module

public import StationaryMFG.Theorems.SimplePower.Coercivity
public import StationaryMFG.Theorems.SimplePower.Banach.AssemblyContext

@[expose] public section

/-!
# Integrability residues for the coercivity combined bound (paper `prop:coercAepsi`)

This module provides the **easy half** of the per-`v` `IntegrableOn`
residues consumed by `coercivity_combined_from_paperHypotheses`
(`StationaryMFG/Theorems/SimplePower/Coercivity.lean`, paper §8
combination of `prop:coercAepsi`'s Eulerian + Laplacian halves, line
947 / 967 / 974).

## What this file delivers

`coercivity_combined_integrability_partial_of_paperHypotheses` — a
**3-of-6** helper that supplies the three "easy" `IntegrableOn`
residues from `(hpow, v ∈ K_Aepsi)` plus the `MemLpPer` data on the Lp
components of `v`:

1. `hm_pos` — a.e.-positivity of `mOf v` (definitional from
   `v ∈ K_Aepsi`).
2. `hRpow_m_int` — `IntegrableOn (m^{β+1}) (UnitCube d)`, via
   `MemLp.integrable_norm_rpow` on `MemLpPer (ofReal (β+1)) (mOf v)`
   (which is `q.1.toMemLp` after the paper-exponent identification
   `βBar = β + 1`), then `‖m x‖ = m x` a.e. using positivity from `hv`.
3. `hRpow_p_int` — `IntegrableOn (‖fun i => Du i x‖^α) (UnitCube d)`,
   via the vector-valued `memLpPer_pi_of_coord` pattern (see
   `Hamiltonian.Estimates`, line 1190): build `MemLpPer α (vector
   function)` from per-coordinate `MemLpPer γBar (DuOf v i)` (via
   `MemLpPer.mono_exponent_finite` using `α ≤ γBar`), then
   `MemLp.integrable_norm_rpow` gives `Integrable (‖·‖^α)`.

The harder three residues `hInt_mu`, `hInt_10`, `hHam_int` — which
require routing through `paperSection8_auxHypsK0_of_paperHypotheses` to
obtain an `MFGOpEpsAuxHyps` certificate at `(DuOf v, mOf v, uOf v)`
and invoking `integrable_mfgPair_integrand` — are deferred to a
sibling task (child of `paperSolFor-coercivity-final-cobounded-integrability`,
key `paperSolFor-coercivity-final-cobounded-integrability-mfgPair`).

## Paper reference

`Source/FGU-monotone_revised.tex`, eq. `prop:coercAepsi` (line 947 and
following). The partial helper here closes the structural
test-pair-independent half (`hm_pos`, `m^{β+1}`-int, `‖Du‖^α`-int) of
the 6-conjunct shape requested by
`paperSolFor-coercivity-final-cobounded`.
-/

noncomputable section

namespace StationaryMFG
namespace Theorems
namespace SimplePower

open MeasureTheory Set
open StationaryMFG.Periodic
open StationaryMFG.Hamiltonian
open StationaryMFG.Solutions.MFG
open StationaryMFG.Theorems.SimplePower.Banach
open scoped ENNReal NNReal

variable {d : ℕ}

/-! ## A small adaptor: the vector-valued `MemLpPer` builder

The next private helper repackages the closure
`memLpPer_pi_of_coord` (proved in `Hamiltonian/Estimates.lean`,
line 1190) but at a different name to avoid privacy issues. The
implementation mirrors the original verbatim: bound the sup-norm of
the vector-valued function by the sum of absolute values, then close
under `MemLp.of_le_mul`.

-- Adapted from `Hamiltonian.Estimates.memLpPer_pi_of_coord`. -/
private theorem coercivityIntegrability.memLpPer_pi_of_coord
    {p : ℝ≥0∞} (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (hDυ : ∀ i, Periodic.MemLpPer p (Dυ i)) :
    Periodic.MemLpPer p (fun x : (Fin d → ℝ) => fun i : Fin d => Dυ i x) := by
  haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  set Dom : (Fin d → ℝ) → ℝ := fun x => ∑ i : Fin d, |Dυ i x| with hDom_def
  have habs_memLp : ∀ i, Periodic.MemLpPer p (fun x => |Dυ i x|) := by
    intro i
    have h := (hDυ i).toMemLp
    have h2 := h.norm
    have heq : (fun x => ‖Dυ i x‖) = fun x => |Dυ i x| := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at h2
    exact MemLp.toMemLpPer h2
  have hDom_memLp : Periodic.MemLpPer p Dom := by
    have hsum :
        MemLp (fun x => ∑ i : Fin d, (fun x => |Dυ i x|) x) p
          (Measure.restrict volume (UnitCube d)) :=
      memLp_finset_sum (Finset.univ : Finset (Fin d))
        (fun i _ => (habs_memLp i).toMemLp)
    exact MemLp.toMemLpPer hsum
  have hbound :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ‖(fun i : Fin d => Dυ i x)‖ ≤ (1 : ℝ) * ‖Dom x‖ := by
    refine Filter.Eventually.of_forall ?_
    intro x
    have hsum_nn : 0 ≤ ∑ i, |Dυ i x| :=
      Finset.sum_nonneg (fun i _ => abs_nonneg _)
    have hpi : ‖(fun i : Fin d => Dυ i x)‖ ≤ ∑ i, |Dυ i x| := by
      rw [pi_norm_le_iff_of_nonneg hsum_nn]
      intro i
      have h1 : ‖Dυ i x‖ = |Dυ i x| := Real.norm_eq_abs _
      rw [h1]
      exact Finset.single_le_sum (f := fun j => |Dυ j x|)
        (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    rw [Real.norm_eq_abs, abs_of_nonneg hsum_nn, one_mul]
    exact hpi
  have hmeas :
      AEStronglyMeasurable
        (fun x : (Fin d → ℝ) => fun i : Fin d => Dυ i x)
        (Measure.restrict volume (UnitCube d)) := by
    have hAEm : AEMeasurable
        (fun x : (Fin d → ℝ) => fun i : Fin d => Dυ i x)
        (Measure.restrict volume (UnitCube d)) :=
      aemeasurable_pi_iff.mpr fun i => (hDυ i).aestronglyMeasurable.aemeasurable
    exact hAEm.aestronglyMeasurable
  exact MemLp.toMemLpPer (MemLp.of_le_mul hDom_memLp.toMemLp hmeas hbound)

/-! ## The partial (3-of-6) integrability helper -/

/-- **Partial (3-of-6) integrability residues for the coercivity
combined bound** at a Banach pair `v ∈ K_Aepsi` (paper `prop:coercAepsi`
combined-bound prerequisite at line 947 / 967 / 974).

Delivers the **easy half** of the 6 `IntegrableOn` premises of
`coercivity_combined_from_paperHypotheses`:

1. `hm_pos` — `mOf v > 0` a.e. on the cube (from `v ∈ K_Aepsi`);
2. `hRpow_m_int` — `(mOf v)^{β+1}` is integrable on the cube;
3. `hRpow_p_int` — `‖(DuOf v ·)‖^α` is integrable on the cube.

The harder three (`hInt_mu`, `hInt_10`, `hHam_int`) require an
`MFGOpEpsAuxHyps` certificate at `v` and are deferred to a sibling
task (child key
`paperSolFor-coercivity-final-cobounded-integrability-mfgPair`). The
combined wrapper assembles both halves into the 6-conjunct shape
consumed by `coercivity_combined_from_paperHypotheses`. -/
theorem coercivity_combined_integrability_partial_of_paperHypotheses
    {γBarReal βBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (hβBar_eq : βBarReal = hpow.β + 1)
    (hγBar_eq : γBarReal = hpow.α * (hpow.β + 1) / hpow.β)
    (v : XBanach d βBarReal γBarReal)
    (hv : v ∈ K_Aepsi d βBarReal γBarReal) :
    (∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < mOf v x) ∧
    IntegrableOn (fun x => mOf v x ^ (hpow.β + 1)) (UnitCube d) ∧
    IntegrableOn
      (fun x => ‖fun i => DuOf v i x‖ ^ hpow.α) (UnitCube d) := by
  -- Standing positivity facts.
  have hα_pos : 0 < hpow.α := lt_trans Real.zero_lt_one hpow.hα
  have hβ_pos : 0 < hpow.β := hpow.hβ
  have hβ1_pos : 0 < hpow.β + 1 := by linarith
  have hγBarReal_pos : 0 < γBarReal := by
    rw [hγBar_eq]; exact div_pos (mul_pos hα_pos hβ1_pos) hβ_pos
  -- `α ≤ γBar` (in fact `<`): `γBar = α + α/β > α`.
  have hα_le_γBar : hpow.α ≤ γBarReal := by
    rw [hγBar_eq]
    -- `γBar = α(β+1)/β ≥ α` ⇔ `α·β ≤ α·(β+1)`, immediate since `0 ≤ α`.
    rw [le_div_iff₀ hβ_pos]
    have : hpow.α * (hpow.β + 1) = hpow.α * hpow.β + hpow.α := by ring
    rw [this]
    linarith
  -- ENNReal lift of `α ≤ γBar`.
  have hα_le_γBar_enn : ENNReal.ofReal hpow.α ≤ ENNReal.ofReal γBarReal :=
    ENNReal.ofReal_le_ofReal hα_le_γBar
  have hγBar_ne_top : ENNReal.ofReal γBarReal ≠ ⊤ := ENNReal.ofReal_ne_top
  -- (1) `hm_pos` — direct from `hv : v ∈ K_Aepsi`.
  have hm_pos : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < mOf v x := hv
  -- `MemLpPer` certificates on the Lp components of `v`.
  have hmLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal) (mOf v) :=
    memLpPer_of_lpPer (d := d) v.1
  have hDuLp : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (DuOf v i) := by
    intro i; exact memLpPer_of_lpPer (d := d) (v.2.2 i)
  -- (2) `(mOf v)^{β+1}` is integrable on the cube.
  --     Pattern adapted from `aClass_hLB_int`
  --     (`Banach/AprioriUniform.lean`, line 523).
  have hRpow_m_int : IntegrableOn (fun x => mOf v x ^ (hpow.β + 1)) (UnitCube d) := by
    -- Lift `hmLp` to the paper exponent.
    have hmLp_paper : MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1)) (mOf v) := by
      rw [← hβBar_eq]; exact hmLp
    have hmemLp : MemLp (mOf v) (ENNReal.ofReal (hpow.β + 1))
        (volume.restrict (UnitCube d)) := hmLp_paper.toMemLp
    have hp_ne_zero : ENNReal.ofReal (hpow.β + 1) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr hβ1_pos).ne'
    have hp_ne_top : ENNReal.ofReal (hpow.β + 1) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hint_norm : Integrable
        (fun x => ‖mOf v x‖ ^ (ENNReal.ofReal (hpow.β + 1)).toReal)
        (volume.restrict (UnitCube d)) :=
      hmemLp.integrable_norm_rpow hp_ne_zero hp_ne_top
    have hp_toReal : (ENNReal.ofReal (hpow.β + 1)).toReal = hpow.β + 1 :=
      ENNReal.toReal_ofReal hβ1_pos.le
    rw [hp_toReal] at hint_norm
    -- Reconcile `‖m x‖^{β+1}` with `m x ^ (β+1)` via `m > 0` a.e.
    refine hint_norm.congr ?_
    filter_upwards [hm_pos] with x hx
    rw [Real.norm_eq_abs, abs_of_pos hx]
  -- (3) `‖fun i => DuOf v i x‖^α` is integrable on the cube.
  --     Build `MemLpPer α (vector function)` via per-coordinate
  --     `MemLpPer.mono_exponent_finite` (γBar → α) and the
  --     adapted vector-builder, then apply `integrable_norm_rpow`.
  have hRpow_p_int :
      IntegrableOn (fun x => ‖fun i => DuOf v i x‖ ^ hpow.α) (UnitCube d) := by
    -- Per-coordinate descent to exponent `α`.
    have hDuLp_α : ∀ i, MemLpPer (d := d) (ENNReal.ofReal hpow.α) (DuOf v i) := by
      intro i
      exact (hDuLp i).mono_exponent_finite hα_le_γBar_enn hγBar_ne_top
    -- Vector-valued `MemLpPer α`.
    have hVecLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal hpow.α)
        (fun x : (Fin d → ℝ) => fun i : Fin d => DuOf v i x) :=
      coercivityIntegrability.memLpPer_pi_of_coord (DuOf v) hDuLp_α
    -- `Integrable (‖·‖^α)` via `MemLp.integrable_norm_rpow`.
    have hα_ne_zero : ENNReal.ofReal hpow.α ≠ 0 :=
      (ENNReal.ofReal_pos.mpr hα_pos).ne'
    have hα_ne_top : ENNReal.ofReal hpow.α ≠ ⊤ := ENNReal.ofReal_ne_top
    have hmemLp : MemLp (fun x : (Fin d → ℝ) => fun i : Fin d => DuOf v i x)
        (ENNReal.ofReal hpow.α) (volume.restrict (UnitCube d)) :=
      hVecLp.toMemLp
    have hint_norm : Integrable
        (fun x => ‖(fun i : Fin d => DuOf v i x)‖ ^
                   (ENNReal.ofReal hpow.α).toReal)
        (volume.restrict (UnitCube d)) :=
      hmemLp.integrable_norm_rpow hα_ne_zero hα_ne_top
    have hα_toReal : (ENNReal.ofReal hpow.α).toReal = hpow.α :=
      ENNReal.toReal_ofReal hα_pos.le
    rw [hα_toReal] at hint_norm
    exact hint_norm
  exact ⟨hm_pos, hRpow_m_int, hRpow_p_int⟩

/-! ## The 3-of-6 mfgPair-based integrability helper -/

/-- **The hard half of the integrability residues** (`hInt_mu`, `hInt_10`,
`hHam_int`) for the coercivity combined bound at a Banach pair
`v ∈ K_Aepsi`.

The plan, following the task spec:

1. `hInt_mu`: route through `paperSection8_auxHypsK0_of_paperHypotheses`
   → `K_Aepsi_subset_K0_Aepsi` → `integrable_mfgPair_integrand` at the
   primal triple `(DuOf v, mOf v, uOf v)` and test triple
   `(η = mOf v - 1, ν = uOf v, Dν = DuOf v)`.
2. `hInt_10`: build a separate `MFGOpEpsAuxHyps … 0 1 0` directly,
   using `H_abs_bound_nonneg_of_hHat0` at `(0, 1)` for the F_HJB
   dominator and `hpow.DpH_upper` at `(0, 1)` for the F_flux
   dominator; the remaining fields (F_mass, G_grad i, G_val) are
   identically zero. Then apply `integrable_mfgPair_integrand`.
3. `hHam_int`: from `mfgOperatorPair_integrand_diff_eq` pointwise +
   `Integrable.sub hInt_mu hInt_10`, then `Integrable.congr`. -/
theorem coercivity_combined_integrability_mfgPair_of_paperHypotheses
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
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
    (hF_HJB_meas : ∀ q : XBanach d βBarReal γBarReal,
      AEStronglyMeasurable
        (fun x => -(uOf q x) - H x (fun i => DuOf q i x) (mOf q x) + V x)
        (volume.restrict (UnitCube d)))
    (hF_flux_meas : ∀ q : XBanach d βBarReal γBarReal, ∀ i,
      AEStronglyMeasurable
        (fun x => mOf q x * DpH x (fun j => DuOf q j x) (mOf q x) i)
        (volume.restrict (UnitCube d)))
    (v : XBanach d βBarReal γBarReal)
    (hv : v ∈ K_Aepsi d βBarReal γBarReal) :
    IntegrableOn
      (fun x => (-(uOf v x) - H x (fun i => DuOf v i x) (mOf v x) + V x)
                  * (mOf v x - 1)
                + mOf v x * (DpH x (fun i => DuOf v i x) (mOf v x)
                              ⬝ (fun i => DuOf v i x))
                + (mOf v x - 1) * uOf v x) (UnitCube d) ∧
    IntegrableOn
      (fun x => (-(0 : ℝ) - H x (0 : Fin d → ℝ) 1 + V x) * (mOf v x - 1)
                + 1 * (DpH x (0 : Fin d → ℝ) 1 ⬝ (fun i => DuOf v i x))
                + (1 - 1) * uOf v x) (UnitCube d) ∧
    IntegrableOn
      (fun x => coerciveHamIntegrand H DpH (DuOf v) (mOf v) x) (UnitCube d) := by
  -- Standard finite-measure instance on the unit cube.
  haveI : IsFiniteMeasure (volume.restrict (UnitCube (d := d))) :=
    Periodic.Saturator.instIsFiniteMeasureRestrictUnitCube
  -- Standing positivity facts.
  have hα_pos : 0 < hpow.α := lt_trans Real.zero_lt_one hpow.hα
  have hβ_pos : 0 < hpow.β := hpow.hβ
  have hβ1_pos : 0 < hpow.β + 1 := by linarith
  -- ENNReal positivity of `β̄`, `γ̄`, `β̄'`, `γ̄'`.
  have hβBar_pos : 0 < βBarReal := by rw [hβBar_eq]; exact hβ1_pos
  have hγBarReal_pos : 0 < γBarReal := by
    rw [hγBar_eq]; exact div_pos (mul_pos hα_pos hβ1_pos) hβ_pos
  have hβ'_pos : 0 < βBarReal' := hβ.symm.pos
  have hγ'_pos : 0 < γBarReal' := hγ.symm.pos
  -- ENNReal-of-real positivity / non-top.
  have hβ_ne_zero : ENNReal.ofReal βBarReal ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hβBar_pos).ne'
  have hβ_ne_top : ENNReal.ofReal βBarReal ≠ ⊤ := ENNReal.ofReal_ne_top
  have hγ_ne_zero : ENNReal.ofReal γBarReal ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hγBarReal_pos).ne'
  have hγ_ne_top : ENNReal.ofReal γBarReal ≠ ⊤ := ENNReal.ofReal_ne_top
  have hβ'_ne_zero : ENNReal.ofReal βBarReal' ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hβ'_pos).ne'
  have hβ'_ne_top : ENNReal.ofReal βBarReal' ≠ ⊤ := ENNReal.ofReal_ne_top
  have hγ'_ne_zero : ENNReal.ofReal γBarReal' ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hγ'_pos).ne'
  have hγ'_ne_top : ENNReal.ofReal γBarReal' ≠ ⊤ := ENNReal.ofReal_ne_top
  -- `MemLpPer` certificates from the Lp components of `v`.
  have hmLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal) (mOf v) :=
    memLpPer_of_lpPer (d := d) v.1
  have huLp : MemLpPer (d := d) (ENNReal.ofReal γBarReal) (uOf v) :=
    memLpPer_of_lpPer (d := d) v.2.1
  have hDuLp : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (DuOf v i) := by
    intro i; exact memLpPer_of_lpPer (d := d) (v.2.2 i)
  -- Build `MemLpPer βBar (mOf v - 1)`.
  have hOneLp_β : MemLpPer (d := d) (ENNReal.ofReal βBarReal)
        (fun _ : (Fin d → ℝ) => (1 : ℝ)) :=
    MemLp.toMemLpPer (memLp_const (1 : ℝ))
  have hOneLp_γ : MemLpPer (d := d) (ENNReal.ofReal γBarReal)
        (fun _ : (Fin d → ℝ) => (1 : ℝ)) :=
    MemLp.toMemLpPer (memLp_const (1 : ℝ))
  have hmSub1_Lp : MemLpPer (d := d) (ENNReal.ofReal βBarReal)
        (fun x : (Fin d → ℝ) => mOf v x - 1) := by
    have hsub : MemLp ((mOf v) - (fun _ => (1 : ℝ))) (ENNReal.ofReal βBarReal)
        (volume.restrict (UnitCube d)) :=
      MeasureTheory.MemLp.sub hmLp.toMemLp hOneLp_β.toMemLp
    -- The pointwise function `x ↦ mOf v x - 1` is the same as `mOf v - 1`.
    have heq : ((mOf v) - (fun _ : (Fin d → ℝ) => (1 : ℝ)))
              = (fun x : (Fin d → ℝ) => mOf v x - 1) := by
      funext x; rfl
    rw [heq] at hsub
    exact MemLp.toMemLpPer hsub
  -- ---------------------------------------------------------------------
  -- (1) `hInt_mu`: route through `paperSection8_auxHypsK0_of_paperHypotheses`.
  -- ---------------------------------------------------------------------
  have hauxHypsK0 :
      ∀ q ∈ K0_Aepsi d βBarReal γBarReal,
        MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
          V H DpH (DuOf q) (mOf q) (uOf q) :=
    paperSection8_auxHypsK0_of_paperHypotheses
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      hmon hpow hHat0 hAgree hV hExp
      hβBar_eq hγBar_eq hβBar'_eq hγBar'_eq
      hβ hγ hβTop hγ'_le_β hF_HJB_meas hF_flux_meas
  have hv_K0 : v ∈ K0_Aepsi d βBarReal γBarReal :=
    K_Aepsi_subset_K0_Aepsi d βBarReal γBarReal hv
  have hauxV : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                  V H DpH (DuOf v) (mOf v) (uOf v) := hauxHypsK0 v hv_K0
  have hInt_mu : IntegrableOn
      (fun x => (-(uOf v x) - H x (fun i => DuOf v i x) (mOf v x) + V x)
                  * (mOf v x - 1)
                + mOf v x * (DpH x (fun i => DuOf v i x) (mOf v x)
                              ⬝ (fun i => DuOf v i x))
                + (mOf v x - 1) * uOf v x) (UnitCube d) :=
    integrable_mfgPair_integrand
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      hauxV hmSub1_Lp huLp hDuLp
  -- ---------------------------------------------------------------------
  -- (2) `hInt_10`: build `MFGOpEpsAuxHyps … 0 1 0` directly.
  -- ---------------------------------------------------------------------
  -- We construct a Banach element `q_one` whose `mOf` is the constant 1
  -- (as an Lp class), `uOf` is the zero class, `DuOf i` is the zero class.
  -- Then `hF_HJB_meas q_one` gives `AEStronglyMeasurable (fun x => -(0 : ℝ)
  --   - H x 0 1 + V x)` (since the representatives of `q_one` equal
  -- `0, 1, 0` *almost everywhere*, not literally, we need an
  -- ae-rewrite via `AEStronglyMeasurable.congr`).
  -- Build the Lp classes via `MemLpPer.toLp`.
  set mLp1 : Periodic.LpPer (ENNReal.ofReal βBarReal) d := hOneLp_β.toLp
  set uLp0 : MeasureTheory.Lp ℝ (ENNReal.ofReal γBarReal)
                (volume.restrict (UnitCube d)) :=
    (MemLp.toMemLpPer (memLp_const (E := ℝ) (μ := volume.restrict (UnitCube d))
        (p := ENNReal.ofReal γBarReal) (0 : ℝ))).toLp
  set q_one : XBanach d βBarReal γBarReal :=
    (mLp1, uLp0, fun _ => uLp0) with hq_one_def
  -- Coercion a.e.-equalities for q_one.
  have hmOf_q_one_ae : mOf q_one =ᵐ[volume.restrict (UnitCube d)]
                        (fun _ : (Fin d → ℝ) => (1 : ℝ)) := by
    -- `mOf q_one = ⇑mLp1`; `⇑mLp1 =ᵐ fun _ => 1` since `mLp1 = hOneLp_β.toLp`.
    have h := MeasureTheory.MemLp.coeFn_toLp (μ := volume.restrict (UnitCube d))
                (p := ENNReal.ofReal βBarReal) hOneLp_β.toMemLp
    exact h
  have huOf_q_one_ae : uOf q_one =ᵐ[volume.restrict (UnitCube d)]
                        (fun _ : (Fin d → ℝ) => (0 : ℝ)) := by
    have h := MeasureTheory.MemLp.coeFn_toLp (μ := volume.restrict (UnitCube d))
                (p := ENNReal.ofReal γBarReal)
                (MemLp.toMemLpPer (memLp_const (E := ℝ)
                  (μ := volume.restrict (UnitCube d))
                  (p := ENNReal.ofReal γBarReal) (0 : ℝ))).toMemLp
    exact h
  have hDuOf_q_one_ae : ∀ i,
      DuOf q_one i =ᵐ[volume.restrict (UnitCube d)]
        (fun _ : (Fin d → ℝ) => (0 : ℝ)) := by
    intro i
    have h := MeasureTheory.MemLp.coeFn_toLp (μ := volume.restrict (UnitCube d))
                (p := ENNReal.ofReal γBarReal)
                (MemLp.toMemLpPer (memLp_const (E := ℝ)
                  (μ := volume.restrict (UnitCube d))
                  (p := ENNReal.ofReal γBarReal) (0 : ℝ))).toMemLp
    exact h
  -- Ae-strong-measurability of `x ↦ -0 - H x 0 1 + V x`.
  have hAEm_HJB10 : AEStronglyMeasurable
        (fun x => -(0 : ℝ) - H x (0 : Fin d → ℝ) 1 + V x)
        (volume.restrict (UnitCube d)) := by
    have h0 := hF_HJB_meas q_one
    -- `(fun x => -(uOf q_one x) - H x (DuOf q_one) (mOf q_one x) + V x)`
    --  =ᵐ `(fun x => -0 - H x 0 1 + V x)`.
    have hpt : (fun x => -(uOf q_one x)
                  - H x (fun i => DuOf q_one i x) (mOf q_one x) + V x)
              =ᵐ[volume.restrict (UnitCube d)]
                (fun x => -(0 : ℝ) - H x (0 : Fin d → ℝ) 1 + V x) := by
      have hDu_all : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
            ∀ i, DuOf q_one i x = (0 : ℝ) := by
        rw [MeasureTheory.ae_all_iff]; intro i; exact hDuOf_q_one_ae i
      filter_upwards [hmOf_q_one_ae, huOf_q_one_ae, hDu_all]
        with x hmx hux hDx
      have h_arg : (fun i => DuOf q_one i x) = (0 : Fin d → ℝ) := by
        funext i; exact hDx i
      rw [hmx, hux, h_arg]
    exact h0.congr hpt
  -- Ae-strong-measurability of `x ↦ 1 * (DpH x 0 1) i`.
  have hAEm_flux10 : ∀ i, AEStronglyMeasurable
        (fun x => (1 : ℝ) * (DpH x (0 : Fin d → ℝ) 1 i))
        (volume.restrict (UnitCube d)) := by
    intro i
    have h0 := hF_flux_meas q_one i
    have hpt : (fun x => mOf q_one x * DpH x (fun j => DuOf q_one j x)
                          (mOf q_one x) i)
              =ᵐ[volume.restrict (UnitCube d)]
                (fun x => (1 : ℝ) * (DpH x (0 : Fin d → ℝ) 1 i)) := by
      have hDu_all : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
            ∀ j, DuOf q_one j x = (0 : ℝ) := by
        rw [MeasureTheory.ae_all_iff]; intro j; exact hDuOf_q_one_ae j
      filter_upwards [hmOf_q_one_ae, hDu_all] with x hmx hDx
      have h_arg : (fun j => DuOf q_one j x) = (0 : Fin d → ℝ) := by
        funext j; exact hDx j
      rw [hmx, h_arg]
    exact h0.congr hpt
  -- Phase-H5d absolute-value bound at `(p, m) = (0, 1)`.
  have hFin : Hamiltonian.Hext_finite_at_zero (d := d) H :=
    Hamiltonian.Hext_finite_at_zero_of_powerGrowth (d := d) hpow hHat0
  have habs := Hamiltonian.H_abs_bound_nonneg_of_hHat0
                  (d := d) hpow hHat0 hFin hAgree
  -- Constant bound `|H(x, 0, 1)| ≤ 3 · hpow.C`.
  have hH01_bound : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      |H x (0 : Fin d → ℝ) 1| ≤ 3 * hpow.C := by
    filter_upwards [habs] with x hxAbs
    have h1 : |H x (0 : Fin d → ℝ) 1|
              ≤ hpow.C * (‖(0 : Fin d → ℝ)‖ ^ hpow.α + 1)
                  + hpow.C * ((1 : ℝ) ^ hpow.β + 1) :=
      hxAbs (0 : Fin d → ℝ) 1 (by norm_num)
    -- Simplify: `‖0‖^α = 0`, `1^β = 1`.
    have h0_norm : ‖(0 : Fin d → ℝ)‖ = 0 := norm_zero
    have h0_pow : (0 : ℝ) ^ hpow.α = 0 := Real.zero_rpow (ne_of_gt hα_pos)
    have h1_pow : (1 : ℝ) ^ hpow.β = 1 := Real.one_rpow _
    rw [h0_norm, h0_pow] at h1
    rw [h1_pow] at h1
    linarith
  -- Build `MemLpPer β' (x ↦ -(0 : ℝ) - H x 0 1 + V x)` via `of_le_mul`.
  have hF_HJB_10 : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x => -(0 : ℝ) - H x (0 : Fin d → ℝ) 1 + V x) := by
    -- Dominator: `Dom x := 3 * hpow.C + |V x|`. In `L^β'`.
    set Dom : (Fin d → ℝ) → ℝ := fun x => 3 * hpow.C + |V x| with hDom
    have hDom_memLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal') Dom := by
      -- `Dom = const + |V|`. Constants ∈ L^β'.
      have hconst : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
            (fun _ : (Fin d → ℝ) => 3 * hpow.C) :=
        MemLp.toMemLpPer (memLp_const _)
      have hAbsV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') (fun x => |V x|) := by
        have hVnorm := hV.toMemLp.norm
        have heq : (fun x => ‖V x‖) = (fun x => |V x|) := by
          funext x; exact Real.norm_eq_abs _
        rw [heq] at hVnorm
        exact MemLp.toMemLpPer hVnorm
      exact hconst.add hAbsV
    -- Pointwise bound: `‖-0 - H x 0 1 + V x‖ ≤ 1 * ‖Dom x‖`.
    have hbd : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖-(0 : ℝ) - H x (0 : Fin d → ℝ) 1 + V x‖ ≤ (1 : ℝ) * ‖Dom x‖ := by
      filter_upwards [hH01_bound] with x hxH
      have hDom_nn : 0 ≤ Dom x := by
        have h1 : 0 ≤ 3 * hpow.C := by linarith [hpow.hC]
        linarith [abs_nonneg (V x)]
      have htri : |-(0 : ℝ) - H x (0 : Fin d → ℝ) 1 + V x|
                    ≤ |H x (0 : Fin d → ℝ) 1| + |V x| := by
        have h1 : -(0 : ℝ) - H x (0 : Fin d → ℝ) 1 + V x
                  = -(H x (0 : Fin d → ℝ) 1) + V x := by ring
        rw [h1]
        have h2 := abs_add_le (-(H x (0 : Fin d → ℝ) 1)) (V x)
        rw [abs_neg] at h2
        exact h2
      have : |-(0 : ℝ) - H x (0 : Fin d → ℝ) 1 + V x| ≤ Dom x := by
        have h := add_le_add hxH (le_refl (|V x|))
        calc |-(0 : ℝ) - H x (0 : Fin d → ℝ) 1 + V x|
            ≤ |H x (0 : Fin d → ℝ) 1| + |V x| := htri
          _ ≤ 3 * hpow.C + |V x| := h
          _ = Dom x := rfl
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hDom_nn, one_mul]
      exact this
    exact MemLp.toMemLpPer (MemLp.of_le_mul hDom_memLp.toMemLp hAEm_HJB10 hbd)
  -- Build `MemLpPer γ' (x ↦ 1 * (DpH x 0 1) i)` per i.
  have hF_flux_10 : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => (1 : ℝ) * (DpH x (0 : Fin d → ℝ) 1 i)) := by
    intro i
    -- Dominator: constant `2 * hpow.C` (constant function on finite measure).
    -- `C*(0 + 1 + 1) = 2*C`.
    set Dom : (Fin d → ℝ) → ℝ := fun _ => 2 * hpow.C with hDom_def
    have hDom_memLp : MemLpPer (d := d) (ENNReal.ofReal γBarReal') Dom :=
      MemLp.toMemLpPer (memLp_const _)
    have hDpH01_bound : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖DpH x (0 : Fin d → ℝ) 1‖ ≤ 2 * hpow.C := by
      filter_upwards [hpow.DpH_upper] with x hxU
      have h1 := hxU (0 : Fin d → ℝ) 1 (by norm_num : (0 : ℝ) < 1)
      -- `‖0‖^{α-1} = 0`, `1^{β-β/α} = 1`.
      have h0_norm : ‖(0 : Fin d → ℝ)‖ = 0 := norm_zero
      have hα1_pos : 0 < hpow.α - 1 := by linarith [hpow.hα]
      have h0_pow : (0 : ℝ) ^ (hpow.α - 1) = 0 :=
        Real.zero_rpow (ne_of_gt hα1_pos)
      have h1_pow : (1 : ℝ) ^ (hpow.β - hpow.β / hpow.α) = 1 := Real.one_rpow _
      rw [h0_norm, h0_pow] at h1
      rw [h1_pow] at h1
      linarith
    have hbd : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖(1 : ℝ) * (DpH x (0 : Fin d → ℝ) 1 i)‖ ≤ (1 : ℝ) * ‖Dom x‖ := by
      filter_upwards [hDpH01_bound] with x hxD
      have hC_nn : 0 ≤ 2 * hpow.C := by linarith [hpow.hC]
      have hcoord : |DpH x (0 : Fin d → ℝ) 1 i| ≤ ‖DpH x (0 : Fin d → ℝ) 1‖ := by
        have := norm_le_pi_norm (DpH x (0 : Fin d → ℝ) 1) i
        simpa [Real.norm_eq_abs] using this
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hC_nn]
      rw [one_mul, one_mul]
      calc |DpH x (0 : Fin d → ℝ) 1 i|
          ≤ ‖DpH x (0 : Fin d → ℝ) 1‖ := hcoord
        _ ≤ 2 * hpow.C := hxD
    exact MemLp.toMemLpPer
      (MemLp.of_le_mul hDom_memLp.toMemLp (hAEm_flux10 i) hbd)
  -- Build `MemLpPer γ' (F_mass 1) = MemLpPer γ' (fun _ => 1 - 1) = const 0`.
  have hF_mass_10 : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (F_mass (fun _ : (Fin d → ℝ) => (1 : ℝ))) := by
    have hpt : F_mass (fun _ : (Fin d → ℝ) => (1 : ℝ))
              = (fun _ : (Fin d → ℝ) => (0 : ℝ)) := by
      funext x; unfold F_mass; ring
    rw [hpt]
    exact MemLp.toMemLpPer (memLp_const _)
  -- `MemLpPer γ' (G_grad γBar 0 i)` = MemLpPer of 0.
  have hG_grad_10 : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (G_grad γBarReal (fun (_ : Fin d) (_ : (Fin d → ℝ)) => (0 : ℝ)) i) := by
    intro i
    have hpt : G_grad γBarReal (fun (_ : Fin d) (_ : (Fin d → ℝ)) => (0 : ℝ)) i
              = (fun _ : (Fin d → ℝ) => (0 : ℝ)) := by
      funext x; unfold G_grad
      have h0 : (fun j : Fin d => (fun (_ : Fin d) (_ : Fin d → ℝ) => (0 : ℝ)) j x)
                = (0 : Fin d → ℝ) := by
        funext j; rfl
      simp [h0, mul_zero]
    rw [hpt]
    exact MemLp.toMemLpPer (memLp_const _)
  -- `MemLpPer γ' (G_val γBar 0)` = MemLpPer of 0.
  have hG_val_10 : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (G_val γBarReal (fun _ : (Fin d → ℝ) => (0 : ℝ))) := by
    have hpt : G_val γBarReal (fun _ : (Fin d → ℝ) => (0 : ℝ))
              = (fun _ : (Fin d → ℝ) => (0 : ℝ)) := by
      funext x; unfold G_val; simp
    rw [hpt]
    exact MemLp.toMemLpPer (memLp_const _)
  -- Assemble the `MFGOpEpsAuxHyps` at primal `(0, 1, 0)`.
  -- Note: the `F_HJB`, `F_flux` definitions of `MFGOpEpsAuxHyps` use
  -- specific shapes that may need unfold; check both.
  have hF_HJB_10' : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (F_HJB V H (fun (_ : Fin d) (_ : (Fin d → ℝ)) => (0 : ℝ))
                  (fun _ : (Fin d → ℝ) => (1 : ℝ))
                  (fun _ : (Fin d → ℝ) => (0 : ℝ))) := by
    have hpt : F_HJB V H (fun (_ : Fin d) (_ : (Fin d → ℝ)) => (0 : ℝ))
                  (fun _ : (Fin d → ℝ) => (1 : ℝ))
                  (fun _ : (Fin d → ℝ) => (0 : ℝ))
              = (fun x => -(0 : ℝ) - H x (0 : Fin d → ℝ) 1 + V x) := by
      funext x; unfold F_HJB
      have h0 : (fun i : Fin d => (fun (_ : Fin d) (_ : (Fin d → ℝ)) => (0 : ℝ)) i x)
                = (0 : Fin d → ℝ) := by funext i; rfl
      rw [h0]
    rw [hpt]; exact hF_HJB_10
  have hF_flux_10' : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (F_flux DpH (fun (_ : Fin d) (_ : (Fin d → ℝ)) => (0 : ℝ))
                  (fun _ : (Fin d → ℝ) => (1 : ℝ)) i) := by
    intro i
    have hpt : F_flux DpH (fun (_ : Fin d) (_ : (Fin d → ℝ)) => (0 : ℝ))
                  (fun _ : (Fin d → ℝ) => (1 : ℝ)) i
              = (fun x => (1 : ℝ) * (DpH x (0 : Fin d → ℝ) 1 i)) := by
      funext x; unfold F_flux
      have h0 : (fun j : Fin d => (fun (_ : Fin d) (_ : (Fin d → ℝ)) => (0 : ℝ)) j x)
                = (0 : Fin d → ℝ) := by funext j; rfl
      rw [h0]
    rw [hpt]; exact hF_flux_10 i
  have haux10 : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                  V H DpH (fun (_ : Fin d) (_ : (Fin d → ℝ)) => (0 : ℝ))
                  (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ)) :=
    { hβ := hβ, hγ := hγ
      hF_HJB := hF_HJB_10', hF_flux := hF_flux_10'
      hF_mass := hF_mass_10
      hG_grad := hG_grad_10, hG_val := hG_val_10
      hβTop := hβTop }
  -- Now apply `integrable_mfgPair_integrand` at primal `(0, 1, 0)` with
  -- test triple `(η = mOf v - 1, ν = uOf v, Dν = DuOf v)`.
  have hInt_10 : IntegrableOn
      (fun x => (-(0 : ℝ) - H x (0 : Fin d → ℝ) 1 + V x) * (mOf v x - 1)
                + 1 * (DpH x (0 : Fin d → ℝ) 1 ⬝ (fun i => DuOf v i x))
                + (1 - 1) * uOf v x) (UnitCube d) :=
    integrable_mfgPair_integrand
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      haux10 hmSub1_Lp huLp hDuLp
  -- ---------------------------------------------------------------------
  -- (3) `hHam_int`: from `hInt_mu - hInt_10 = coerciveHamIntegrand`.
  -- ---------------------------------------------------------------------
  have hHam_int : IntegrableOn
      (fun x => coerciveHamIntegrand H DpH (DuOf v) (mOf v) x) (UnitCube d) := by
    have hsub : IntegrableOn
        (fun x =>
          ((-(uOf v x) - H x (fun i => DuOf v i x) (mOf v x) + V x) * (mOf v x - 1)
            + mOf v x * (DpH x (fun i => DuOf v i x) (mOf v x)
                            ⬝ (fun i => DuOf v i x))
            + (mOf v x - 1) * uOf v x)
          - ((-(0 : ℝ) - H x (0 : Fin d → ℝ) 1 + V x) * (mOf v x - 1)
              + 1 * (DpH x (0 : Fin d → ℝ) 1 ⬝ (fun i => DuOf v i x))
              + (1 - 1) * uOf v x))
        (UnitCube d) := hInt_mu.sub hInt_10
    refine hsub.congr ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    -- Identity is pure algebra (`ring`); mirrors the `private`
    -- `mfgOperatorPair_integrand_diff_eq` from `Coercivity.lean`.
    unfold coerciveHamIntegrand
    ring
  exact ⟨hInt_mu, hInt_10, hHam_int⟩

/-! ## The full 6-conjunct merged integrability helper -/

/-- **Full (6-of-6) integrability residues for the coercivity combined bound**
at a Banach pair `v ∈ K_Aepsi` (paper `prop:coercAepsi`, line 947 / 967 /
974).

This is the pure-assembly wrapper that combines
`coercivity_combined_integrability_partial_of_paperHypotheses` (the easy
half: `hm_pos`, `m^{β+1}`-int, `‖Du‖^α`-int) with
`coercivity_combined_integrability_mfgPair_of_paperHypotheses` (the hard
half: `hInt_mu`, `hInt_10`, `hHam_int`) into the **exact 6-conjunct
shape** consumed by `coercivity_combined_from_paperHypotheses`. -/
theorem coercivity_combined_integrability_residues
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
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
    (hF_HJB_meas : ∀ q : XBanach d βBarReal γBarReal,
      AEStronglyMeasurable
        (fun x => -(uOf q x) - H x (fun i => DuOf q i x) (mOf q x) + V x)
        (volume.restrict (UnitCube d)))
    (hF_flux_meas : ∀ q : XBanach d βBarReal γBarReal, ∀ i,
      AEStronglyMeasurable
        (fun x => mOf q x * DpH x (fun j => DuOf q j x) (mOf q x) i)
        (volume.restrict (UnitCube d)))
    (v : XBanach d βBarReal γBarReal)
    (hv : v ∈ K_Aepsi d βBarReal γBarReal) :
    (∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < mOf v x) ∧
    IntegrableOn
      (fun x => (-(uOf v x) - H x (fun i => DuOf v i x) (mOf v x) + V x)
                  * (mOf v x - 1)
                + mOf v x * (DpH x (fun i => DuOf v i x) (mOf v x)
                              ⬝ (fun i => DuOf v i x))
                + (mOf v x - 1) * uOf v x) (UnitCube d) ∧
    IntegrableOn
      (fun x => (-(0 : ℝ) - H x (0 : Fin d → ℝ) 1 + V x) * (mOf v x - 1)
                + 1 * (DpH x (0 : Fin d → ℝ) 1 ⬝ (fun i => DuOf v i x))
                + (1 - 1) * uOf v x) (UnitCube d) ∧
    IntegrableOn
      (fun x => coerciveHamIntegrand H DpH (DuOf v) (mOf v) x) (UnitCube d) ∧
    IntegrableOn (fun x => mOf v x ^ (hpow.β + 1)) (UnitCube d) ∧
    IntegrableOn
      (fun x => ‖fun i => DuOf v i x‖ ^ hpow.α) (UnitCube d) := by
  obtain ⟨hm_pos, hRpow_m_int, hRpow_p_int⟩ :=
    coercivity_combined_integrability_partial_of_paperHypotheses
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      hpow hβBar_eq hγBar_eq v hv
  obtain ⟨hInt_mu, hInt_10, hHam_int⟩ :=
    coercivity_combined_integrability_mfgPair_of_paperHypotheses
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      hmon hpow hHat0 hAgree hV hExp
      hβBar_eq hγBar_eq hβBar'_eq hγBar'_eq
      hβ hγ hβTop hγ'_le_β hF_HJB_meas hF_flux_meas v hv
  exact ⟨hm_pos, hInt_mu, hInt_10, hHam_int, hRpow_m_int, hRpow_p_int⟩

/-! ## Sanity check: the residues plug into `coercivity_combined_from_paperHypotheses` -/

/-- **API sanity check** for `coercivity_combined_integrability_residues`:
the 6-conjunct output is consumable verbatim by
`coercivity_combined_from_paperHypotheses`, so that the cobounded
packaging downstream only needs the merged residues. -/
example
    {γBar ε γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (V : (Fin d → ℝ) → ℝ)
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
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
    (hF_HJB_meas : ∀ q : XBanach d βBarReal γBarReal,
      AEStronglyMeasurable
        (fun x => -(uOf q x) - H x (fun i => DuOf q i x) (mOf q x) + V x)
        (volume.restrict (UnitCube d)))
    (hF_flux_meas : ∀ q : XBanach d βBarReal γBarReal, ∀ i,
      AEStronglyMeasurable
        (fun x => mOf q x * DpH x (fun j => DuOf q j x) (mOf q x) i)
        (volume.restrict (UnitCube d)))
    (v : XBanach d βBarReal γBarReal)
    (hv : v ∈ K_Aepsi d βBarReal γBarReal) :
    ∃ C_eul : ℝ, 0 < C_eul ∧
      (1 / C_eul) * (∫ x in UnitCube d, mOf v x ^ (hpow.β + 1))
          + (1 / C_eul) * (∫ x in UnitCube d, ‖fun i => DuOf v i x‖ ^ hpow.α)
          + ε * (∫ x in UnitCube d,
              vecAbsPowMinusTwo γBar (fun i => DuOf v i x)
                  * ((fun i => DuOf v i x) ⬝ (fun i => DuOf v i x))
                + absPowMinusTwo γBar (uOf v x) * (uOf v x * uOf v x))
          - C_eul
        ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBar ε (DuOf v) (mOf v) (uOf v) (DuOf v) (mOf v - 1) (uOf v)
          - mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBar ε (fun _ _ => 0) (fun _ => 1) (fun _ => 0)
              (DuOf v) (mOf v - 1) (uOf v) := by
  obtain ⟨hm_pos, hInt_mu, hInt_10, hHam_int, hRpow_m_int, hRpow_p_int⟩ :=
    coercivity_combined_integrability_residues
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      hmon hpow hHat0 hAgree hV hExp
      hβBar_eq hγBar_eq hβBar'_eq hγBar'_eq
      hβ hγ hβTop hγ'_le_β hF_HJB_meas hF_flux_meas v hv
  exact coercivity_combined_from_paperHypotheses (d := d)
    (γBar := γBar) (ε := ε) V hpow (DuOf v) (mOf v) (uOf v)
    hm_pos hInt_mu hInt_10 hHam_int hRpow_m_int hRpow_p_int

/-! ## Signature bridge for `paperSection8_coercivity_of_paperHypotheses_full`

(Child 2a of the iter 0600 cobounded wrap split — task
`paperSolFor-coercivity-final-cobounded-wrap-signature-bridge`.)

The combined algebraic bound `coercivity_combined_from_paperHypotheses`
delivers, per `v ∈ K_Aepsi`, an inequality of the form
```
(1/C_eul)·∫ m^{β+1} + (1/C_eul)·∫ ‖Du‖^α + ε·∫ <gateaux> - C_eul
  ≤ op-diff(v)
```
The conclusion of paper `prop:coercAepsi` (line 982) requires the
**gauge-form** comparison
```
aepsiCoerciveGauge γBarReal v - Ccoerc ≤ op-diff(v)
```
on the filter `cobounded ⊓ 𝓟 K_Aepsi`. Bridging the eulerian RHS
(involving `∫ m^{β+1}`, `∫ ‖Du‖^α`, and the Gateaux integral) to the
Banach-pair gauge `‖v‖^γ̄ / γ̄` is the **norm-bridge** step (paper
line 982's algebraic translation through `MemLpPer.norm_pair_rpow_le`
and `MemSobolevPer.norm_toLpSobolev_rpow_le`).

`paperSection8_coercivity_of_paperHypotheses_full` exposes the full
13-hypothesis signature requested by the cobounded wrap so that
downstream consumers (e.g. `PaperSection8AnalyticResidues`) can thread
the paper hypotheses cleanly, while leaving the norm-bridge step
factored out as a separate residue `hNormBridge`. The sibling task
`paperSolFor-coercivity-final-cobounded-wrap-norm-bridge` closes
`hNormBridge` honestly.

* Target file: relocated from `AssemblyContext.lean` (would induce an
  import cycle — `Coercivity/Integrability.lean` already imports
  `AssemblyContext.lean`, so the wrap must live downstream) to the
  present file.
-/

/-- **Signature bridge for `prop:coercAepsi`** (paper line 982, full
13-hypothesis form, child 2a of the cobounded wrap split).

Threads the 13 paper hypotheses required to discharge
`coercivity_combined_integrability_residues` and
`coercivity_combined_from_paperHypotheses`, plus a final
`hNormBridge` residue carrying the gauge-form inequality. The norm
bridge is the **algebraic translation** of the eulerian-RHS into the
Banach-pair gauge `‖v‖^γBarReal / γBarReal` and is the subject of
the sibling task
`paperSolFor-coercivity-final-cobounded-wrap-norm-bridge`.

The substantive content of this wrap is the **signature** itself: it
authorises all 13 paper hypotheses in scope so that downstream
consumers (chiefly `Aepsi_coercive_of_paperHypotheses` in
`AssemblyContext.lean`) can be invoked with the paper-hypothesis
bundle. The body is the trivial forwarding of `hNormBridge`. -/
theorem paperSection8_coercivity_of_paperHypotheses_full
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
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
    (hF_HJB_meas : ∀ q : XBanach d βBarReal γBarReal,
      AEStronglyMeasurable
        (fun x => -(uOf q x) - H x (fun i => DuOf q i x) (mOf q x) + V x)
        (volume.restrict (UnitCube d)))
    (hF_flux_meas : ∀ q : XBanach d βBarReal γBarReal, ∀ i,
      AEStronglyMeasurable
        (fun x => mOf q x * DpH x (fun j => DuOf q j x) (mOf q x) i)
        (volume.restrict (UnitCube d)))
    (hNormBridge : ∃ Ccoerc : ℝ,
      ∀ᶠ v in (Bornology.cobounded (XBanach d βBarReal γBarReal)
                  ⊓ Filter.principal (K_Aepsi d βBarReal γBarReal)),
        aepsiCoerciveGauge (βBarReal := βBarReal) (γBarReal := γBarReal)
            (coercivityGaugeExponent βBarReal γBarReal) v - Ccoerc ≤
          mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε (fun i => ⇑(v.2.2 i)) (⇑v.1) (⇑v.2.1)
              (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1)
            - mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                γBarReal ε (fun _ _ => 0) (fun _ => 1) (fun _ => 0)
                (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1)) :
    ∃ Ccoerc : ℝ,
      ∀ᶠ v in (Bornology.cobounded (XBanach d βBarReal γBarReal)
                  ⊓ Filter.principal (K_Aepsi d βBarReal γBarReal)),
        aepsiCoerciveGauge (βBarReal := βBarReal) (γBarReal := γBarReal)
            (coercivityGaugeExponent βBarReal γBarReal) v - Ccoerc ≤
          mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε (fun i => ⇑(v.2.2 i)) (⇑v.1) (⇑v.2.1)
              (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1)
            - mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                γBarReal ε (fun _ _ => 0) (fun _ => 1) (fun _ => 0)
                (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1) := by
  -- The 13 hypotheses are authorised in scope precisely so that the
  -- norm-bridge sibling task can build `hNormBridge` from
  -- `coercivity_combined_integrability_residues` (which requires
  -- `hmon, hpow, hHat0, hAgree, hV, hExp, hβBar_eq, hγBar_eq,
  -- hβBar'_eq, hγBar'_eq, hβ, hγ, hβTop, hγ'_le_β, hF_HJB_meas,
  -- hF_flux_meas`) and `coercivity_combined_from_paperHypotheses`.
  -- Acknowledge the threaded hypotheses to keep them in scope (and
  -- to suppress any unused-variable lints).
  let _ := hmon; let _ := hHat0; let _ := hAgree; let _ := hV;
  let _ := hExp; let _ := hβBar_eq; let _ := hγBar_eq;
  let _ := hβBar'_eq; let _ := hγBar'_eq; let _ := hβ; let _ := hγ;
  let _ := hβTop; let _ := hγ'_le_β; let _ := hF_HJB_meas;
  let _ := hF_flux_meas; let _ := hpow
  exact hNormBridge

/-- **API sanity check** for `paperSection8_coercivity_of_paperHypotheses_full`:
the wrap's conclusion plugs verbatim into the
`hbound_residue` slot of `Aepsi_coercive_of_paperHypotheses` (in
`AssemblyContext.lean`, paper-line-982 composition). -/
example
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
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
    (hF_HJB_meas : ∀ q : XBanach d βBarReal γBarReal,
      AEStronglyMeasurable
        (fun x => -(uOf q x) - H x (fun i => DuOf q i x) (mOf q x) + V x)
        (volume.restrict (UnitCube d)))
    (hF_flux_meas : ∀ q : XBanach d βBarReal γBarReal, ∀ i,
      AEStronglyMeasurable
        (fun x => mOf q x * DpH x (fun j => DuOf q j x) (mOf q x) i)
        (volume.restrict (UnitCube d)))
    (hNormBridge : ∃ Ccoerc : ℝ,
      ∀ᶠ v in (Bornology.cobounded (XBanach d βBarReal γBarReal)
                  ⊓ Filter.principal (K_Aepsi d βBarReal γBarReal)),
        aepsiCoerciveGauge (βBarReal := βBarReal) (γBarReal := γBarReal)
            (coercivityGaugeExponent βBarReal γBarReal) v - Ccoerc ≤
          mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε (fun i => ⇑(v.2.2 i)) (⇑v.1) (⇑v.2.1)
              (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1)
            - mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                γBarReal ε (fun _ _ => 0) (fun _ => 1) (fun _ => 0)
                (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1)) :
    ∃ Ccoerc : ℝ,
      ∀ᶠ v in (Bornology.cobounded (XBanach d βBarReal γBarReal)
                  ⊓ Filter.principal (K_Aepsi d βBarReal γBarReal)),
        aepsiCoerciveGauge (βBarReal := βBarReal) (γBarReal := γBarReal)
            (coercivityGaugeExponent βBarReal γBarReal) v - Ccoerc ≤
          mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε (fun i => ⇑(v.2.2 i)) (⇑v.1) (⇑v.2.1)
              (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1)
            - mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                γBarReal ε (fun _ _ => 0) (fun _ => 1) (fun _ => 0)
                (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1) :=
  paperSection8_coercivity_of_paperHypotheses_full
    (γBarReal := γBarReal) (βBarReal := βBarReal)
    (βBarReal' := βBarReal') (γBarReal' := γBarReal') (ε := ε)
    hmon hpow hHat0 hAgree hV hExp
    hβBar_eq hγBar_eq hβBar'_eq hγBar'_eq
    hβ hγ hβTop hγ'_le_β hF_HJB_meas hF_flux_meas hNormBridge

/-! ### Norm-bridge child A: real-analytic gauge ≤ Banach-pair upper bound

The next lemma `coercivity_gauge_le_norm_pair_of_paperHypotheses` is the
**real-analytic gauge step** of the paper-line-982 norm bridge
(`hNormBridge` residue of `paperSection8_coercivity_of_paperHypotheses_full`,
this file's `lemma` above at line ~877). It is the child A of the
iter-0642 split (sibling: `paperSolFor-coercivity-norm-bridge-B-operator-difference`,
which composes this gauge step with the operator-difference lower bound).

The key algebraic step is:
```
‖v‖ ^ (min βBar.toReal γBar.toReal)
  ≤ 1 + ‖v.1‖ ^ βBar.toReal + ‖v.2‖ ^ γBar.toReal
```
(via `MemLpPer.norm_pair_rpow_min_le`), instantiated under the polarity
`γBar ≤ βBar` so that `min βBar γBar = γBar`. Dividing by `γBarReal > 0`
produces the gauge form `aepsiCoerciveGauge γBarReal v ≤ …`.

This is the Banach-norm form of the gauge bridge; the further
unfolding of `‖v.1‖ ^ βBarReal` and `‖v.2‖ ^ γBarReal` to integrated
quantities (via `MemLpPer.norm_toLp_rpow_eq` and the Sobolev analogue)
is deferred to the integrated-form sibling (sub-child A2 / consumed in
child B). -/

/-- **Norm-bridge child A** (paper line 982, real-analytic gauge step).

⚠️ **NON-LOAD-BEARING INTERMEDIATE** (post iter 0644 expert audit,
2026-05-17). This lemma assumes `hγ_le_β : γBarReal ≤ βBarReal`,
which for paper exponents `β̄ = β + 1`, `γ̄ = α(β+1)/β` is equivalent
to `α ≤ β` — **NOT** a paper hypothesis. The load-bearing coercivity
path has been retyped to use
`coercivityGaugeExponent βBarReal γBarReal = min βBarReal γBarReal`
as the gauge exponent (see `paperSection8_coercivity_of_paperHypotheses_full`
above), which avoids the polarity assumption entirely via
`MemLpPer.norm_pair_rpow_min_le`. This lemma remains as a historical
intermediate but is **not** on the paper-exact closure path.

Bridges the abstract Banach gauge `aepsiCoerciveGauge γBarReal v
= ‖v‖^γBarReal / γBarReal` to the Banach-pair-norm upper bound
`(1 + ‖v.1‖^βBarReal + ‖v.2‖^γBarReal) / γBarReal`, via
`MemLpPer.norm_pair_rpow_min_le` at the polarity-correct
instantiation `min βBar γBar = γBar` (requires `γBar ≤ βBar`). -/
theorem coercivity_gauge_le_norm_pair_of_paperHypotheses
    {βBarReal γBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (hβTop : ENNReal.ofReal βBarReal ≠ ⊤)
    (hγTop : ENNReal.ofReal γBarReal ≠ ⊤)
    (hγ_le_β : γBarReal ≤ βBarReal)
    (hγPos : 0 < γBarReal)
    (v : XBanach d βBarReal γBarReal) :
    aepsiCoerciveGauge (βBarReal := βBarReal) (γBarReal := γBarReal)
        γBarReal v
      ≤ (1 + ‖v.1‖ ^ βBarReal + ‖v.2‖ ^ γBarReal) / γBarReal := by
  -- Unfold the gauge `‖v‖^γBarReal / γBarReal`.
  unfold aepsiCoerciveGauge
  -- Apply `MemLpPer.norm_pair_rpow_min_le` to the pair `(v.1, v.2) = v`.
  have h_pair :
      ‖((v.1, v.2))‖
          ^ min (ENNReal.ofReal βBarReal).toReal
                (ENNReal.ofReal γBarReal).toReal
        ≤ 1 + ‖v.1‖ ^ (ENNReal.ofReal βBarReal).toReal
            + ‖v.2‖ ^ (ENNReal.ofReal γBarReal).toReal :=
    MemLpPer.norm_pair_rpow_min_le hβTop hγTop v.1 v.2
  -- `(v.1, v.2) = v` definitionally (since `XBanach = Lp × SobolevPerLp`).
  -- Translate the `ENNReal.toReal`-wrapped exponents back to bare reals.
  have hγReal : (ENNReal.ofReal γBarReal).toReal = γBarReal :=
    ENNReal.toReal_ofReal hγPos.le
  have hβPos : 0 ≤ βBarReal := le_trans hγPos.le hγ_le_β
  have hβReal : (ENNReal.ofReal βBarReal).toReal = βBarReal :=
    ENNReal.toReal_ofReal hβPos
  rw [hβReal, hγReal] at h_pair
  have h_min_real : min βBarReal γBarReal = γBarReal := min_eq_right hγ_le_β
  rw [h_min_real] at h_pair
  -- `(v.1, v.2)` is definitionally `v`.
  have h_v_norm : ‖((v.1, v.2) : XBanach d βBarReal γBarReal)‖ = ‖v‖ := rfl
  rw [h_v_norm] at h_pair
  -- Divide both sides by `γBarReal > 0`.
  exact div_le_div_of_nonneg_right h_pair hγPos.le

/-- **Norm-bridge child A, paper-valid (min-gauge) replacement**
(iter 0645, post-expert-audit 2026-05-17).

This is the paper-line-982 gauge bridge **without** the non-paper
polarity assumption `γBarReal ≤ βBarReal`. It uses
`coercivityGaugeExponent βBarReal γBarReal = min βBarReal γBarReal`
as the LHS gauge exponent, which matches
`Periodic.MemLpPer.norm_pair_rpow_min_le` directly and handles both
polarities uniformly. This is the load-bearing form consumed by the
paper-exact closure path (replaces the iter-0643
`coercivity_gauge_le_norm_pair_of_paperHypotheses` above, which remains
as a historical intermediate). -/
theorem coercivity_gauge_min_le_norm_pair_of_paperHypotheses
    {βBarReal γBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (hβTop : ENNReal.ofReal βBarReal ≠ ⊤)
    (hγTop : ENNReal.ofReal γBarReal ≠ ⊤)
    (hβ : 1 < βBarReal) (hγ : 1 < γBarReal)
    (v : XBanach d βBarReal γBarReal) :
    aepsiCoerciveGauge (βBarReal := βBarReal) (γBarReal := γBarReal)
        (coercivityGaugeExponent βBarReal γBarReal) v
      ≤ (1 + ‖v.1‖ ^ βBarReal + ‖v.2‖ ^ γBarReal)
          / coercivityGaugeExponent βBarReal γBarReal := by
  -- Unfold both the gauge and the coercivity exponent.
  unfold aepsiCoerciveGauge coercivityGaugeExponent
  -- Apply the periodic primitive on the pair `(v.1, v.2) = v`.
  have h_pair :
      ‖((v.1, v.2))‖
          ^ min (ENNReal.ofReal βBarReal).toReal
                (ENNReal.ofReal γBarReal).toReal
        ≤ 1 + ‖v.1‖ ^ (ENNReal.ofReal βBarReal).toReal
            + ‖v.2‖ ^ (ENNReal.ofReal γBarReal).toReal :=
    MemLpPer.norm_pair_rpow_min_le hβTop hγTop v.1 v.2
  -- Translate the `ENNReal.toReal`-wrapped exponents back to bare reals.
  have hβPos : 0 ≤ βBarReal := le_of_lt (lt_trans zero_lt_one hβ)
  have hγPos : 0 ≤ γBarReal := le_of_lt (lt_trans zero_lt_one hγ)
  have hβReal : (ENNReal.ofReal βBarReal).toReal = βBarReal :=
    ENNReal.toReal_ofReal hβPos
  have hγReal : (ENNReal.ofReal γBarReal).toReal = γBarReal :=
    ENNReal.toReal_ofReal hγPos
  rw [hβReal, hγReal] at h_pair
  -- `(v.1, v.2)` is definitionally `v`.
  have h_v_norm : ‖((v.1, v.2) : XBanach d βBarReal γBarReal)‖ = ‖v‖ := rfl
  rw [h_v_norm] at h_pair
  -- Divide both sides by `min βBarReal γBarReal > 0` (strictly, since both > 1).
  have h_min_pos : 0 < min βBarReal γBarReal :=
    lt_of_lt_of_le zero_lt_one (le_min hβ.le hγ.le)
  exact div_le_div_of_nonneg_right h_pair h_min_pos.le

/-- **API sanity check** for `coercivity_gauge_le_norm_pair_of_paperHypotheses`:
the conclusion is a real-valued inequality witnessing the gauge bridge
at the Banach-norm level. The next composition step (child B) will
combine this with the operator-difference lower bound. -/
example
    {βBarReal γBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (hβTop : ENNReal.ofReal βBarReal ≠ ⊤)
    (hγTop : ENNReal.ofReal γBarReal ≠ ⊤)
    (hγ_le_β : γBarReal ≤ βBarReal)
    (hγPos : 0 < γBarReal)
    (v : XBanach d βBarReal γBarReal) :
    aepsiCoerciveGauge (βBarReal := βBarReal) (γBarReal := γBarReal)
        γBarReal v
      ≤ (1 + ‖v.1‖ ^ βBarReal + ‖v.2‖ ^ γBarReal) / γBarReal :=
  coercivity_gauge_le_norm_pair_of_paperHypotheses
    hβTop hγTop hγ_le_β hγPos v

/-! ### Norm-bridge child B1: translate Banach norms to integrated quantities

The next two lemmas connect the Banach-pair RHS produced by child A
(`coercivity_gauge_min_le_norm_pair_of_paperHypotheses`) to the
integrated form `∫ |·|^{β̄}` / `∫ |·|^{γ̄} + ∑ ∫ |∇·|^{γ̄}` consumed by
`coercivity_combined_from_paperHypotheses` downstream. They are the
abstract-Banach-pair-shaped versions of `MemLpPer.norm_toLp_rpow_eq`
(for `v.1`) and `MemSobolevPer.norm_toLpSobolev_rpow_le` (for `v.2`),
re-proven directly for arbitrary `v : XBanach d βBarReal γBarReal`
(rather than for `(MemLpPer.toLp, MemSobolevPer.toLpSobolev)` pairs).

Together they implement the iter-0644 expert-redecomposed B1 step
"norm-pair ≤ integrated" of the norm-bridge chain. -/

/-- **Norm-bridge child B1, `m`-factor (exact equality)**
(paper line 982, integrated form of `‖v.1‖^{β̄}`).

For `v : XBanach d βBarReal γBarReal` (a Banach pair whose first factor
is a `LpPer (ofReal βBarReal) d` class), the `βBarReal`-th power of the
abstract `Lp`-norm of `v.1` equals the unit-cube integral of `|mOf v|^{β̄}`.

This is the direct application of `MemLpPer.norm_toLp_rpow_eq` to the
canonical `MemLpPer` certificate `memLpPer_of_lpPer v.1`, combined with
the identity `v.1 = (memLpPer_of_lpPer v.1).toLp ⇑v.1` (from
`MeasureTheory.Lp.toLp_coeFn`). -/
theorem coercivity_norm_m_eq_integrated
    {βBarReal γBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (hβPos : 0 < βBarReal)
    (v : XBanach d βBarReal γBarReal) :
    ‖v.1‖ ^ βBarReal = ∫ x in UnitCube d, |mOf v x| ^ βBarReal := by
  -- `v.1` has a canonical `MemLpPer` certificate.
  have hm : Periodic.MemLpPer (ENNReal.ofReal βBarReal) (⇑v.1) :=
    StationaryMFG.Theorems.SimplePower.Banach.memLpPer_of_lpPer
      (d := d) v.1
  -- `v.1 = hm.toLp ⇑v.1` via `MeasureTheory.Lp.toLp_coeFn`.
  have hv1_eq : v.1 = hm.toLp := by
    -- `MeasureTheory.Lp.toLp_coeFn` returns `hf.toLp f = f` for `f : Lp`.
    -- Here `f = v.1` and `hf = hm`.
    exact (MeasureTheory.Lp.toLp_coeFn v.1 hm).symm
  -- Apply the periodic primitive `MemLpPer.norm_toLp_rpow_eq`.
  have hβ_ne_zero : (ENNReal.ofReal βBarReal) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hβPos).ne'
  have hβ_ne_top : (ENNReal.ofReal βBarReal) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hβ_toReal : (ENNReal.ofReal βBarReal).toReal = βBarReal :=
    ENNReal.toReal_ofReal hβPos.le
  have h_eq := Periodic.MemLpPer.norm_toLp_rpow_eq
                  (d := d) hβ_ne_zero hβ_ne_top hm
  rw [hβ_toReal] at h_eq
  -- `mOf v x = ⇑v.1 x` definitionally.
  -- `‖hm.toLp‖ = ‖v.1‖` from `hv1_eq` (symmetric).
  calc ‖v.1‖ ^ βBarReal
      = ‖hm.toLp‖ ^ βBarReal := by rw [← hv1_eq]
    _ = ∫ x in UnitCube d, |⇑v.1 x| ^ βBarReal := h_eq
    _ = ∫ x in UnitCube d, |mOf v x| ^ βBarReal := by
        rfl

/-- **Norm-bridge child B1, `u`-factor (Sobolev pair bound)**
(paper line 982, integrated form of `‖v.2‖^{γ̄}`).

For `v : XBanach d βBarReal γBarReal` (whose second factor is a
`SobolevPerLp 1 (ofReal γBarReal) d = Lp × (Fin d → Lp)`), the
`γBarReal`-th power of the abstract Sobolev-pair norm of `v.2` is
bounded by the dimension-weighted integrated sum of `|uOf v|^{γ̄}` and
`|DuOf v i|^{γ̄}`.

Proof outline (re-proof of `Periodic.MemSobolevPer.norm_toLpSobolev_rpow_le`
adapted to the abstract pair, since we have no `MemSobolevPer`
certificate at the abstract level — `SobolevPerLp` does not constrain
the function class and the derivative classes):

1. `Prod.norm_def` splits `‖v.2‖ = max ‖v.2.1‖ ‖v.2.2‖`.
2. `max ≤ sum` and `Pi.norm` bounded by sum of coords.
3. Raise to `γBarReal`-th power, then `sum_succ_rpow_le` introduces
   the `(d+1)^{γ̄}` slack.
4. Each per-factor `‖·‖^{γ̄}` equals an integrated `∫ |·|^{γ̄}` via
   `MemLpPer.norm_toLp_rpow_eq` and `Lp.toLp_coeFn`. -/
theorem coercivity_norm_u_le_integrated
    {βBarReal γBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (hγPos : 0 < γBarReal)
    (v : XBanach d βBarReal γBarReal) :
    ‖v.2‖ ^ γBarReal
      ≤ ((d : ℝ) + 1) ^ γBarReal *
          ((∫ x in UnitCube d, |uOf v x| ^ γBarReal) +
            ∑ i, ∫ x in UnitCube d, |DuOf v i x| ^ γBarReal) := by
  -- Canonical `MemLpPer` certificates for the Lp components of `v.2`.
  have hu : Periodic.MemLpPer (ENNReal.ofReal γBarReal) (⇑v.2.1) :=
    StationaryMFG.Theorems.SimplePower.Banach.memLpPer_of_lpPer
      (d := d) v.2.1
  have hDu : ∀ i, Periodic.MemLpPer (ENNReal.ofReal γBarReal) (⇑(v.2.2 i)) :=
    fun i =>
      StationaryMFG.Theorems.SimplePower.Banach.memLpPer_of_lpPer
        (d := d) (v.2.2 i)
  -- Per-factor `Lp = MemLp.toLp` identities.
  have hv2_1_eq : v.2.1 = hu.toLp :=
    (MeasureTheory.Lp.toLp_coeFn v.2.1 hu).symm
  have hv2_2_eq : ∀ i, v.2.2 i = (hDu i).toLp :=
    fun i => (MeasureTheory.Lp.toLp_coeFn (v.2.2 i) (hDu i)).symm
  -- Step 1: `‖v.2‖ = max ‖v.2.1‖ ‖v.2.2‖` by `Prod.norm_def`.
  have h_norm_split : ‖v.2‖ = max ‖v.2.1‖ ‖v.2.2‖ := Prod.norm_def _
  -- Per-coord nonneg.
  have h_normLp_nn : ∀ i, 0 ≤ ‖v.2.2 i‖ := fun i => norm_nonneg _
  have h_normTo_nn : 0 ≤ ‖v.2.1‖ := norm_nonneg _
  -- `Pi` norm bound: `‖v.2.2‖ ≤ ∑ i, ‖v.2.2 i‖`.
  have h_pi_le : ‖v.2.2‖ ≤ ∑ i, ‖v.2.2 i‖ := by
    have hsum_nn : 0 ≤ ∑ i, ‖v.2.2 i‖ :=
      Finset.sum_nonneg (fun i _ => norm_nonneg _)
    rw [pi_norm_le_iff_of_nonneg hsum_nn]
    intro i
    exact Finset.single_le_sum
      (f := fun j => ‖v.2.2 j‖)
      (fun j _ => norm_nonneg _)
      (Finset.mem_univ i)
  -- Combine: `‖v.2‖ ≤ ‖v.2.1‖ + ∑ i, ‖v.2.2 i‖`.
  have h_norm_le : ‖v.2‖ ≤ ‖v.2.1‖ + ∑ i, ‖v.2.2 i‖ := by
    have hpi_nn : 0 ≤ ‖v.2.2‖ := norm_nonneg _
    rw [h_norm_split]
    calc max ‖v.2.1‖ ‖v.2.2‖
        ≤ ‖v.2.1‖ + ‖v.2.2‖ :=
          max_le (by linarith) (by linarith)
      _ ≤ ‖v.2.1‖ + ∑ i, ‖v.2.2 i‖ := by linarith
  -- Step 2: take the `γBarReal`-th power.
  have hs_nn : 0 ≤ ‖v.2‖ := norm_nonneg _
  have hγ_nn : 0 ≤ γBarReal := hγPos.le
  have h_normp_le :
      ‖v.2‖ ^ γBarReal
        ≤ (‖v.2.1‖ + ∑ i, ‖v.2.2 i‖) ^ γBarReal :=
    Real.rpow_le_rpow hs_nn h_norm_le hγ_nn
  -- Step 3: `sum_succ_rpow_le` for the sum-rpow bound.
  have h_sum_bound :
      (‖v.2.1‖ + ∑ i, ‖v.2.2 i‖) ^ γBarReal
        ≤ ((d : ℝ) + 1) ^ γBarReal *
          ((‖v.2.1‖ ^ γBarReal) +
            ∑ i, ‖v.2.2 i‖ ^ γBarReal) :=
    StationaryMFG.Periodic.sum_succ_rpow_le
      ‖v.2.1‖ (fun i => ‖v.2.2 i‖) h_normTo_nn h_normLp_nn
      γBarReal hγ_nn
  -- Step 4: translate each `‖·‖^γ` to `∫ |·|^γ` via the periodic primitive.
  have hγ_ne_zero : (ENNReal.ofReal γBarReal) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hγPos).ne'
  have hγ_ne_top : (ENNReal.ofReal γBarReal) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hγ_toReal : (ENNReal.ofReal γBarReal).toReal = γBarReal :=
    ENNReal.toReal_ofReal hγPos.le
  have hu_eq : ‖v.2.1‖ ^ γBarReal = ∫ x in UnitCube d, |uOf v x| ^ γBarReal := by
    have h_eq := Periodic.MemLpPer.norm_toLp_rpow_eq
                    (d := d) hγ_ne_zero hγ_ne_top hu
    rw [hγ_toReal] at h_eq
    calc ‖v.2.1‖ ^ γBarReal
        = ‖hu.toLp‖ ^ γBarReal := by rw [← hv2_1_eq]
      _ = ∫ x in UnitCube d, |⇑v.2.1 x| ^ γBarReal := h_eq
      _ = ∫ x in UnitCube d, |uOf v x| ^ γBarReal := by rfl
  have hDu_eq : ∀ i, ‖v.2.2 i‖ ^ γBarReal
                      = ∫ x in UnitCube d, |DuOf v i x| ^ γBarReal := by
    intro i
    have h_eq := Periodic.MemLpPer.norm_toLp_rpow_eq
                    (d := d) hγ_ne_zero hγ_ne_top (hDu i)
    rw [hγ_toReal] at h_eq
    calc ‖v.2.2 i‖ ^ γBarReal
        = ‖(hDu i).toLp‖ ^ γBarReal := by rw [← hv2_2_eq i]
      _ = ∫ x in UnitCube d, |⇑(v.2.2 i) x| ^ γBarReal := h_eq
      _ = ∫ x in UnitCube d, |DuOf v i x| ^ γBarReal := by rfl
  -- Combine.
  calc ‖v.2‖ ^ γBarReal
      ≤ (‖v.2.1‖ + ∑ i, ‖v.2.2 i‖) ^ γBarReal := h_normp_le
    _ ≤ ((d : ℝ) + 1) ^ γBarReal *
          ((‖v.2.1‖ ^ γBarReal) +
            ∑ i, ‖v.2.2 i‖ ^ γBarReal) := h_sum_bound
    _ = ((d : ℝ) + 1) ^ γBarReal *
          ((∫ x in UnitCube d, |uOf v x| ^ γBarReal) +
            ∑ i, ∫ x in UnitCube d, |DuOf v i x| ^ γBarReal) := by
          rw [hu_eq]
          congr 2
          exact Finset.sum_congr rfl (fun i _ => hDu_eq i)

/-! ### Norm-bridge child B2 (pointwise integrated form, iter 0648)

Composition of child A (min-gauge ≤ Banach-pair-norm RHS,
`coercivity_gauge_min_le_norm_pair_of_paperHypotheses`) with B1's
m-factor (`coercivity_norm_m_eq_integrated`) and u-factor
(`coercivity_norm_u_le_integrated`). Result: a **pointwise** (per-`v`)
upper bound on `aepsiCoerciveGauge κ v` (`κ := min βBarReal γBarReal`)
in terms of `∫|mOf v|^β̄`, `∫|uOf v|^γ̄`, and `∑∫|DuOf v i|^γ̄`.

This is the 2026-05-17 STRICT-decomposed B2a (sibling of the deferred
B2b Young-absorption step which will couple this RHS to the actual
operator-difference lower bound from
`coercivity_combined_from_paperHypotheses`). -/

/-- **Norm-bridge child B2a** (pointwise min-gauge ≤ integrated form).

For `v : XBanach d βBarReal γBarReal` (with both exponents > 1), the
min-gauge `aepsiCoerciveGauge (min βBar γBar) v = ‖v‖^min / min` is
bounded by an integrated expression in `(mOf v, uOf v, DuOf v)`:
```
aepsiCoerciveGauge κ v
  ≤ (1 + ∫|mOf v|^β̄
        + (d+1)^γ̄ * (∫|uOf v|^γ̄ + ∑ i, ∫|DuOf v i|^γ̄)) / κ
```
where `κ := coercivityGaugeExponent βBarReal γBarReal = min βBar γBar`.

Proof: assemble child A (gauge ≤ Banach-pair-norms RHS), then rewrite
the `‖v.1‖^β̄` and `‖v.2‖^γ̄` summands by B1's per-factor equalities. -/
theorem coercivity_min_gauge_le_integrated_of_paperHypotheses
    {βBarReal γBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (hβTop : ENNReal.ofReal βBarReal ≠ ⊤)
    (hγTop : ENNReal.ofReal γBarReal ≠ ⊤)
    (hβ : 1 < βBarReal) (hγ : 1 < γBarReal)
    (v : XBanach d βBarReal γBarReal) :
    aepsiCoerciveGauge (βBarReal := βBarReal) (γBarReal := γBarReal)
        (coercivityGaugeExponent βBarReal γBarReal) v
      ≤ (1
          + (∫ x in UnitCube d, |mOf v x| ^ βBarReal)
          + ((d : ℝ) + 1) ^ γBarReal *
              ((∫ x in UnitCube d, |uOf v x| ^ γBarReal)
                + ∑ i, ∫ x in UnitCube d, |DuOf v i x| ^ γBarReal))
        / coercivityGaugeExponent βBarReal γBarReal := by
  -- Positivity of `κ := min βBar γBar` (both `> 1`).
  have hκ_pos : 0 < coercivityGaugeExponent βBarReal γBarReal := by
    unfold coercivityGaugeExponent
    exact lt_of_lt_of_le zero_lt_one (le_min hβ.le hγ.le)
  have hβPos : 0 < βBarReal := lt_trans zero_lt_one hβ
  have hγPos : 0 < γBarReal := lt_trans zero_lt_one hγ
  -- Child A: `aepsiCoerciveGauge κ v ≤ (1 + ‖v.1‖^β̄ + ‖v.2‖^γ̄) / κ`.
  have hA :
      aepsiCoerciveGauge (βBarReal := βBarReal) (γBarReal := γBarReal)
          (coercivityGaugeExponent βBarReal γBarReal) v
        ≤ (1 + ‖v.1‖ ^ βBarReal + ‖v.2‖ ^ γBarReal)
            / coercivityGaugeExponent βBarReal γBarReal :=
    coercivity_gauge_min_le_norm_pair_of_paperHypotheses
      hβTop hγTop hβ hγ v
  -- B1 m-factor: equality `‖v.1‖^β̄ = ∫ |mOf v|^β̄`.
  have hB1m : ‖v.1‖ ^ βBarReal = ∫ x in UnitCube d, |mOf v x| ^ βBarReal :=
    coercivity_norm_m_eq_integrated hβPos v
  -- B1 u-factor: inequality
  --   `‖v.2‖^γ̄ ≤ (d+1)^γ̄ * (∫|uOf|^γ̄ + ∑∫|DuOf i|^γ̄)`.
  have hB1u :
      ‖v.2‖ ^ γBarReal
        ≤ ((d : ℝ) + 1) ^ γBarReal *
            ((∫ x in UnitCube d, |uOf v x| ^ γBarReal) +
              ∑ i, ∫ x in UnitCube d, |DuOf v i x| ^ γBarReal) :=
    coercivity_norm_u_le_integrated hγPos v
  -- Combine: rewrite `‖v.1‖^β̄` to integral and bound `‖v.2‖^γ̄`
  -- by integrals.
  have h_num_le :
      1 + ‖v.1‖ ^ βBarReal + ‖v.2‖ ^ γBarReal
        ≤ 1
          + (∫ x in UnitCube d, |mOf v x| ^ βBarReal)
          + ((d : ℝ) + 1) ^ γBarReal *
              ((∫ x in UnitCube d, |uOf v x| ^ γBarReal)
                + ∑ i, ∫ x in UnitCube d, |DuOf v i x| ^ γBarReal) := by
    rw [hB1m]
    linarith [hB1u]
  -- Divide both sides of `h_num_le` by `κ > 0`, then chain with `hA`.
  have h_div :
      (1 + ‖v.1‖ ^ βBarReal + ‖v.2‖ ^ γBarReal)
          / coercivityGaugeExponent βBarReal γBarReal
        ≤ (1
            + (∫ x in UnitCube d, |mOf v x| ^ βBarReal)
            + ((d : ℝ) + 1) ^ γBarReal *
                ((∫ x in UnitCube d, |uOf v x| ^ γBarReal)
                  + ∑ i, ∫ x in UnitCube d, |DuOf v i x| ^ γBarReal))
          / coercivityGaugeExponent βBarReal γBarReal :=
    div_le_div_of_nonneg_right h_num_le hκ_pos.le
  exact le_trans hA h_div

/-- **API sanity check** for
`coercivity_min_gauge_le_integrated_of_paperHypotheses`: the RHS is
a real-valued expression in `(mOf v, uOf v, DuOf v)` integrals,
suitable for B2b (Young absorption) to couple with the
`coercivity_combined_from_paperHypotheses` integrated lower bound. -/
example
    {βBarReal γBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (hβTop : ENNReal.ofReal βBarReal ≠ ⊤)
    (hγTop : ENNReal.ofReal γBarReal ≠ ⊤)
    (hβ : 1 < βBarReal) (hγ : 1 < γBarReal)
    (v : XBanach d βBarReal γBarReal) :
    aepsiCoerciveGauge (βBarReal := βBarReal) (γBarReal := γBarReal)
        (coercivityGaugeExponent βBarReal γBarReal) v
      ≤ (1
          + (∫ x in UnitCube d, |mOf v x| ^ βBarReal)
          + ((d : ℝ) + 1) ^ γBarReal *
              ((∫ x in UnitCube d, |uOf v x| ^ γBarReal)
                + ∑ i, ∫ x in UnitCube d, |DuOf v i x| ^ γBarReal))
        / coercivityGaugeExponent βBarReal γBarReal :=
  coercivity_min_gauge_le_integrated_of_paperHypotheses
    hβTop hγTop hβ hγ v

/-! ### Scaled-gauge λ-witness (2026-05-17 expert pivot, STRICT split
child A of `paperSolFor-coercivity-norm-bridge-scaled-gauge-bound`)

The scaled-gauge bound `λ · gauge(v) − C ≤ op-diff(v)` requires a
positive multiplier `λ` chosen small enough that the coefficient
mismatch between B2a's
`(1 + ∫|m|^β̄ + (d+1)^γ̄ (∫|u|^γ̄ + ∑∫|Du_i|^γ̄)) / κ` RHS and the
combined-bound LHS `(1/C_eul) · ∫m^β̄ + (1/C_eul) · ∫‖Du‖^α
+ ε · ∫gateaux − C_eul` absorbs by construction. The concrete witness

```
λ := min (κ / C_eul) (ε · κ / (d · (d+1)^γ̄))
```

makes the three required coefficient comparisons
* `λ / κ ≤ 1 / C_eul` — absorbs the `m`-summand and the `‖Du‖^α`-summand;
* `λ · d · (d+1)^γ̄ / κ ≤ ε` — absorbs the `(d+1)^γ̄ · ∑ ∫|Du i|^γ̄`
  summand (after the per-coord vs Euclidean bridge from B2b-1 brings
  in the dimensional factor `d`);

true by construction. The sibling task
`paperSolFor-coercivity-norm-bridge-scaled-gauge-absorption-assembly`
consumes these inequalities to land the scaled-gauge bound on
`K_Aepsi`. -/

/-- **λ-witness for the scaled-gauge bound** (paper line 982 algebraic
translation; 2026-05-17 expert scaled-gauge pivot).

Concrete choice that absorbs the coefficient mismatch between the
B2a integrated upper bound on `gauge(v)` (RHS scaled `1/κ`) and the
combined-bound LHS of `coercivity_combined_from_paperHypotheses`
(coefficients `(1/C_eul) , (1/C_eul) , ε`). -/
noncomputable def coercivityScaledGaugeLambda
    (κ C_eul ε : ℝ) (d : ℕ) (γBar : ℝ) : ℝ :=
  min (κ / C_eul)
      (ε * κ / ((d : ℝ) * (((d : ℝ) + 1) ^ γBar)))

/-- **Positivity of the scaled-gauge λ-witness.** Both branches of
the `min` are positive under the paper hypotheses (`κ, C_eul, ε > 0`,
`d ≥ 1`, `γBar ≥ 0`). -/
lemma coercivityScaledGaugeLambda_pos
    {κ C_eul ε γBar : ℝ} {d : ℕ}
    (hκ : 0 < κ) (hC : 0 < C_eul) (hε : 0 < ε)
    (hd : 0 < (d : ℝ)) (hγ : 0 ≤ γBar) :
    0 < coercivityScaledGaugeLambda κ C_eul ε d γBar := by
  unfold coercivityScaledGaugeLambda
  refine lt_min ?_ ?_
  · -- `κ / C_eul > 0`.
    exact div_pos hκ hC
  · -- `ε · κ / (d · (d+1)^γBar) > 0`.
    have hd1_pos : 0 < ((d : ℝ) + 1) := by linarith
    have hd1pow_pos : 0 < ((d : ℝ) + 1) ^ γBar :=
      Real.rpow_pos_of_pos hd1_pos _
    have hden_pos : 0 < (d : ℝ) * (((d : ℝ) + 1) ^ γBar) :=
      mul_pos hd hd1pow_pos
    have hnum_pos : 0 < ε * κ := mul_pos hε hκ
    exact div_pos hnum_pos hden_pos

/-- **First coefficient bound**: `λ / κ ≤ 1 / C_eul`. This is the
inequality that absorbs the `(λ / κ) · ∫m^β̄` and `(λ / κ) · ∫‖Du‖^α`
summands from `λ · B2a-RHS` into the combined-bound LHS coefficients
`(1/C_eul) · ∫m^β̄` and `(1/C_eul) · ∫‖Du‖^α`. -/
lemma coercivityScaledGaugeLambda_div_le_inv_Ceul
    {κ C_eul ε γBar : ℝ} {d : ℕ}
    (hκ : 0 < κ) (hC : 0 < C_eul) (hε : 0 < ε)
    (hd : 0 < (d : ℝ)) (hγ : 0 ≤ γBar) :
    coercivityScaledGaugeLambda κ C_eul ε d γBar / κ ≤ 1 / C_eul := by
  -- `λ ≤ κ / C_eul` from `min_le_left`.
  have hlam_le : coercivityScaledGaugeLambda κ C_eul ε d γBar ≤ κ / C_eul := by
    unfold coercivityScaledGaugeLambda
    exact min_le_left _ _
  -- Divide both sides by `κ > 0`.
  have hstep : coercivityScaledGaugeLambda κ C_eul ε d γBar / κ
      ≤ (κ / C_eul) / κ :=
    div_le_div_of_nonneg_right hlam_le hκ.le
  -- `(κ / C_eul) / κ = 1 / C_eul` since `κ ≠ 0`.
  have hsimp : (κ / C_eul) / κ = 1 / C_eul := by
    rw [div_div, mul_comm, ← div_div, div_self hκ.ne']
  -- Chain: `λ/κ ≤ (κ/C_eul)/κ = 1/C_eul`.
  linarith [hstep, hsimp.le, hsimp.ge]

/-- **Second coefficient bound**: `λ · d · (d+1)^γ̄ / κ ≤ ε`.
This is the inequality that absorbs the `(λ / κ) · (d+1)^γ̄ · ∑ ∫|Du i|^γ̄`
summand from `λ · B2a-RHS`, after the per-coord vs Euclidean bridge from
B2b-1 (`sum_integral_per_coord_pow_le_dim_mul_integral_euclideanDot_pow`)
brings in the dimensional factor `d`, into the combined-bound LHS
coefficient `ε · ∫(Du⬝Du)^{γ̄/2}`. -/
lemma coercivityScaledGaugeLambda_dim_full_mul_le_eps
    {κ C_eul ε γBar : ℝ} {d : ℕ}
    (hκ : 0 < κ) (hC : 0 < C_eul) (hε : 0 < ε)
    (hd : 0 < (d : ℝ)) (hγ : 0 ≤ γBar) :
    coercivityScaledGaugeLambda κ C_eul ε d γBar
        * ((d : ℝ) * (((d : ℝ) + 1) ^ γBar)) / κ
      ≤ ε := by
  -- Positivity facts.
  have hd1_pos : 0 < ((d : ℝ) + 1) := by linarith
  have hd1pow_pos : 0 < ((d : ℝ) + 1) ^ γBar :=
    Real.rpow_pos_of_pos hd1_pos _
  have hden_pos : 0 < (d : ℝ) * (((d : ℝ) + 1) ^ γBar) :=
    mul_pos hd hd1pow_pos
  -- `λ ≤ ε · κ / (d · (d+1)^γ̄)` from `min_le_right`.
  have hlam_le : coercivityScaledGaugeLambda κ C_eul ε d γBar
      ≤ ε * κ / ((d : ℝ) * (((d : ℝ) + 1) ^ γBar)) := by
    unfold coercivityScaledGaugeLambda
    exact min_le_right _ _
  -- Multiply both sides by `d · (d+1)^γ̄ ≥ 0` (preserves `≤`).
  have hmul :
      coercivityScaledGaugeLambda κ C_eul ε d γBar
            * ((d : ℝ) * (((d : ℝ) + 1) ^ γBar))
        ≤ (ε * κ / ((d : ℝ) * (((d : ℝ) + 1) ^ γBar)))
            * ((d : ℝ) * (((d : ℝ) + 1) ^ γBar)) :=
    mul_le_mul_of_nonneg_right hlam_le hden_pos.le
  -- The RHS simplifies to `ε · κ`.
  have hRHS_eq :
      (ε * κ / ((d : ℝ) * (((d : ℝ) + 1) ^ γBar)))
          * ((d : ℝ) * (((d : ℝ) + 1) ^ γBar))
        = ε * κ := by
    rw [div_mul_cancel₀]
    exact hden_pos.ne'
  have hmul' :
      coercivityScaledGaugeLambda κ C_eul ε d γBar
            * ((d : ℝ) * (((d : ℝ) + 1) ^ γBar))
        ≤ ε * κ := by linarith [hmul, hRHS_eq.le, hRHS_eq.ge]
  -- Divide both sides by `κ > 0`.
  have hdiv :
      coercivityScaledGaugeLambda κ C_eul ε d γBar
            * ((d : ℝ) * (((d : ℝ) + 1) ^ γBar)) / κ
        ≤ (ε * κ) / κ :=
    div_le_div_of_nonneg_right hmul' hκ.le
  -- `(ε · κ) / κ = ε`.
  have hsimp : (ε * κ) / κ = ε := by
    rw [mul_div_assoc, div_self hκ.ne', mul_one]
  linarith [hdiv, hsimp.le, hsimp.ge]

/-- **u-term coefficient bound** (no factor `d`): `λ · (d+1)^γ̄ / κ ≤ ε`.
This is the inequality that absorbs the `(λ / κ) · (d+1)^γ̄ · ∫|u|^…`
summand from `λ · B2a-RHS` (no per-coord vs Euclidean bridge applies
here, so no dimensional factor `d`). Derived from the dim-full lemma
using `1 ≤ d` and positivity of `(d+1)^γ̄`. -/
lemma coercivityScaledGaugeLambda_u_le_eps
    {κ C_eul ε γBar : ℝ} {d : ℕ}
    (hκ : 0 < κ) (hC : 0 < C_eul) (hε : 0 < ε)
    (hd : 1 ≤ (d : ℝ)) (hγ : 0 ≤ γBar) :
    coercivityScaledGaugeLambda κ C_eul ε d γBar
        * (((d : ℝ) + 1) ^ γBar) / κ
      ≤ ε := by
  have hd_pos : 0 < (d : ℝ) := lt_of_lt_of_le one_pos hd
  have hd1_pos : 0 < ((d : ℝ) + 1) := by linarith
  have hd1pow_pos : 0 < ((d : ℝ) + 1) ^ γBar :=
    Real.rpow_pos_of_pos hd1_pos _
  have hlam_pos : 0 < coercivityScaledGaugeLambda κ C_eul ε d γBar :=
    coercivityScaledGaugeLambda_pos hκ hC hε hd_pos hγ
  -- `(d+1)^γ̄ ≤ d · (d+1)^γ̄` since `1 ≤ d` and `(d+1)^γ̄ ≥ 0`.
  have hfac_le : ((d : ℝ) + 1) ^ γBar ≤ (d : ℝ) * (((d : ℝ) + 1) ^ γBar) := by
    have := mul_le_mul_of_nonneg_right hd hd1pow_pos.le
    simpa [one_mul] using this
  -- Multiply by `λ ≥ 0`.
  have hmul_le :
      coercivityScaledGaugeLambda κ C_eul ε d γBar * (((d : ℝ) + 1) ^ γBar)
        ≤ coercivityScaledGaugeLambda κ C_eul ε d γBar
            * ((d : ℝ) * (((d : ℝ) + 1) ^ γBar)) :=
    mul_le_mul_of_nonneg_left hfac_le hlam_pos.le
  -- Divide by `κ > 0`.
  have hdiv_le :
      coercivityScaledGaugeLambda κ C_eul ε d γBar * (((d : ℝ) + 1) ^ γBar) / κ
        ≤ coercivityScaledGaugeLambda κ C_eul ε d γBar
            * ((d : ℝ) * (((d : ℝ) + 1) ^ γBar)) / κ :=
    div_le_div_of_nonneg_right hmul_le hκ.le
  exact hdiv_le.trans
    (coercivityScaledGaugeLambda_dim_full_mul_le_eps hκ hC hε hd_pos hγ)

/-! ## Integral form of the Gateaux integrand positive-form equality

(Child of `paperSolFor-coercivity-norm-bridge-scaled-gauge-absorption-assembly`,
iter 0650.)

The pointwise equality `gateauxWpIntegrand_eq_positive_form`
(`Coercivity.lean`, line 2241) reads, for `γBar > 0`:

```
vecAbsPowMinusTwo γBar v * (v⬝v) + absPowMinusTwo γBar s * (s*s)
  = (v⬝v)^(γBar/2) + |s|^γBar.
```

The downstream absorption assembly (paper `prop:coercAepsi` reduction
to the positive-form gauge) needs the **lifted** equality on the
torus integral. Since the identity is *everywhere* (no exceptional
set), the integral version is direct from `integral_congr_ae` applied
to `Filter.Eventually.of_forall`. -/

/-- **Integral form of the Gateaux integrand positive-form equality**.
For `γBar > 0`, vector field `Du : Fin d → ((Fin d → ℝ) → ℝ)`, and
scalar field `u : (Fin d → ℝ) → ℝ`,

```
∫ x in UnitCube d, vecAbsPowMinusTwo γBar (fun i => Du i x)
                      * ((fun i => Du i x) ⬝ (fun i => Du i x))
                + absPowMinusTwo γBar (u x) * (u x * u x)
  = ∫ x in UnitCube d, ((fun i => Du i x) ⬝ (fun i => Du i x))
                          ^ (γBar / 2)
                      + |u x| ^ γBar.
```

Lifted from `gateauxWpIntegrand_eq_positive_form` (pointwise, paper
`prop:coercAepsi` Gateaux positive-form collapse) via
`MeasureTheory.integral_congr_ae` on the universally-true a.e.
equality `Filter.Eventually.of_forall …`. -/
lemma gateauxWpIntegrand_integral_eq_positive_form
    (γBar : ℝ) (hγ : 0 < γBar)
    (Du : Fin d → ((Fin d → ℝ) → ℝ)) (u : (Fin d → ℝ) → ℝ) :
    (∫ x in UnitCube d,
        vecAbsPowMinusTwo γBar (fun i => Du i x)
            * ((fun i => Du i x) ⬝ (fun i => Du i x))
        + absPowMinusTwo γBar (u x) * (u x * u x))
      = ∫ x in UnitCube d,
          ((fun i => Du i x) ⬝ (fun i => Du i x)) ^ (γBar / 2)
            + |u x| ^ γBar := by
  refine MeasureTheory.integral_congr_ae ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  exact gateauxWpIntegrand_eq_positive_form
    (d := d) γBar hγ (fun i => Du i x) (u x)

/-! ### Scaled-gauge absorption core (2026-05-18 split child 1)

Pure real-algebra step abstracting the assembly of:
* the **combined-bound** output of `coercivity_combined_from_paperHypotheses`
  (an integrated lower bound on `op-diff(v)` involving `∫m^(β+1)`,
  `∫‖Du‖^α`, and the Gateaux integral);
* the **scaled-B2a** upper bound `λ · gauge(v) ≤ λ/κ · (1 + Im + (d+1)^γ̄
  · (Iu + IDu_sum))` (from `coercivity_min_gauge_le_integrated_of_paperHypotheses`
  multiplied by `λ ≥ 0`);
* the **per-coord → Euclidean bridge**
  `IDu_sum ≤ d · IDuDot` (from
  `sum_integral_per_coord_pow_le_dim_mul_integral_euclideanDot_pow`);
* the **three λ-coefficient bounds**
  `λ/κ ≤ 1/C_eul`, `λ·d·(d+1)^γ̄/κ ≤ ε`, `λ·(d+1)^γ̄/κ ≤ ε`
  (from `coercivityScaledGaugeLambda_div_le_inv_Ceul`,
  `…_dim_full_mul_le_eps`, `…_u_le_eps`).

The conclusion is the scaled-gauge inequality
`λ · gauge − (C_eul + λ/κ) ≤ opDiff` with the leftover `(1/C_eul)·IpAlpha`
term dropped as nonneg.

Sibling task `paperSolFor-coercivity-scaled-gauge-absorption-xbanach-wrap`
threads this core lemma through the 13-paper-hypothesis XBanach interface
and identifies `Im = ∫m^(β+1) = ∫|m|^β̄` via strict positivity of `m`. -/

/-- **Scaled-gauge absorption core** (pure real algebra).

From the combined-bound lower estimate on `opDiff`, the scaled B2a upper
estimate on `λ · gauge`, the per-coord → Euclidean bridge, and the three
λ-coefficient bounds, derive `λ · gauge − (C_eul + λ/κ) ≤ opDiff`.

The leftover `(1/C_eul) · IpAlpha` term (corresponding to `∫‖Du‖^α` in
the wrapper) is nonneg and dropped, **not** absorbed; no Young inequality
is invoked. -/
lemma coercivity_scaled_min_gauge_absorption_core
    {κ C_eul ε lam Im Iu IDu_sum IDuDot IpAlpha gauge opDiff : ℝ}
    {γBar : ℝ} {d : ℕ}
    (hκ : 0 < κ) (hC_eul : 0 < C_eul)
    (hlam_pos : 0 < lam)
    (hlam_inv : lam / κ ≤ 1 / C_eul)
    (hlam_dim : lam * ((d : ℝ) * (((d : ℝ) + 1) ^ γBar)) / κ ≤ ε)
    (hlam_u : lam * (((d : ℝ) + 1) ^ γBar) / κ ≤ ε)
    (hd1_pos : 0 < ((d : ℝ) + 1) ^ γBar)
    (hIm_nn : 0 ≤ Im) (hIu_nn : 0 ≤ Iu)
    (hIDu_sum_nn : 0 ≤ IDu_sum)
    (hIDuDot_nn : 0 ≤ IDuDot)
    (hIpAlpha_nn : 0 ≤ IpAlpha)
    (hGauge_le : lam * gauge ≤
      lam * (1 + Im + (((d : ℝ) + 1) ^ γBar) * (Iu + IDu_sum)) / κ)
    (hComb : (1 / C_eul) * Im + (1 / C_eul) * IpAlpha
              + ε * (IDuDot + Iu) - C_eul ≤ opDiff)
    (hBridge : IDu_sum ≤ (d : ℝ) * IDuDot) :
    lam * gauge - (C_eul + lam / κ) ≤ opDiff := by
  -- Positivity facts derived from inputs.
  have hC_inv_pos : 0 < 1 / C_eul := one_div_pos.mpr hC_eul
  have hlam_div_κ_nn : 0 ≤ lam / κ := div_nonneg hlam_pos.le hκ.le
  -- Step A: expand the scaled-B2a RHS to a sum of four terms,
  --   λ * (1 + Im + (d+1)^γ̄ * (Iu + IDu_sum)) / κ
  --     = λ/κ + (λ/κ) * Im + (λ * (d+1)^γ̄ / κ) * Iu
  --       + (λ * (d+1)^γ̄ / κ) * IDu_sum.
  have _hκ_ne : κ ≠ 0 := hκ.ne'  -- needed by `field_simp` below
  have hRHS_eq :
      lam * (1 + Im + (((d : ℝ) + 1) ^ γBar) * (Iu + IDu_sum)) / κ
        = lam / κ + (lam / κ) * Im
            + (lam * (((d : ℝ) + 1) ^ γBar) / κ) * Iu
            + (lam * (((d : ℝ) + 1) ^ γBar) / κ) * IDu_sum := by
    field_simp
    ring
  -- Step B: bound each scaled-B2a summand by combined-bound coefficients.
  -- B.1: (λ/κ) * Im ≤ (1/C_eul) * Im.
  have hB1 : (lam / κ) * Im ≤ (1 / C_eul) * Im :=
    mul_le_mul_of_nonneg_right hlam_inv hIm_nn
  -- B.2: (λ * (d+1)^γ̄ / κ) * Iu ≤ ε * Iu.
  have hB2 : (lam * (((d : ℝ) + 1) ^ γBar) / κ) * Iu ≤ ε * Iu :=
    mul_le_mul_of_nonneg_right hlam_u hIu_nn
  -- B.3: (λ * (d+1)^γ̄ / κ) * IDu_sum ≤ (λ * (d+1)^γ̄ / κ) * (d * IDuDot)
  --      = (λ * d * (d+1)^γ̄ / κ) * IDuDot ≤ ε * IDuDot.
  have hlamd1_nn : 0 ≤ lam * (((d : ℝ) + 1) ^ γBar) / κ := by
    have : 0 ≤ lam * (((d : ℝ) + 1) ^ γBar) := mul_nonneg hlam_pos.le hd1_pos.le
    exact div_nonneg this hκ.le
  have hB3a : (lam * (((d : ℝ) + 1) ^ γBar) / κ) * IDu_sum
        ≤ (lam * (((d : ℝ) + 1) ^ γBar) / κ) * ((d : ℝ) * IDuDot) :=
    mul_le_mul_of_nonneg_left hBridge hlamd1_nn
  have hB3_rearrange :
      (lam * (((d : ℝ) + 1) ^ γBar) / κ) * ((d : ℝ) * IDuDot)
        = (lam * ((d : ℝ) * (((d : ℝ) + 1) ^ γBar)) / κ) * IDuDot := by
    ring
  have hB3b : (lam * ((d : ℝ) * (((d : ℝ) + 1) ^ γBar)) / κ) * IDuDot
        ≤ ε * IDuDot :=
    mul_le_mul_of_nonneg_right hlam_dim hIDuDot_nn
  have hB3 : (lam * (((d : ℝ) + 1) ^ γBar) / κ) * IDu_sum ≤ ε * IDuDot := by
    have := hB3a
    rw [hB3_rearrange] at this
    exact this.trans hB3b
  -- Step C: assemble the four-term bound:
  --   λ * gauge ≤ λ/κ + (1/C_eul)*Im + ε*Iu + ε*IDuDot.
  have hCombined_bd :
      lam * gauge
        ≤ lam / κ + (1 / C_eul) * Im + ε * Iu + ε * IDuDot := by
    have hsum_le :
        lam / κ + (lam / κ) * Im
            + (lam * (((d : ℝ) + 1) ^ γBar) / κ) * Iu
            + (lam * (((d : ℝ) + 1) ^ γBar) / κ) * IDu_sum
          ≤ lam / κ + (1 / C_eul) * Im + ε * Iu + ε * IDuDot := by
      linarith [hB1, hB2, hB3]
    have hGauge_le' : lam * gauge
        ≤ lam / κ + (lam / κ) * Im
            + (lam * (((d : ℝ) + 1) ^ γBar) / κ) * Iu
            + (lam * (((d : ℝ) + 1) ^ γBar) / κ) * IDu_sum := by
      have := hGauge_le
      rw [hRHS_eq] at this
      exact this
    exact hGauge_le'.trans hsum_le
  -- Step D: drop the nonneg `(1/C_eul) * IpAlpha` term from `hComb`:
  --   (1/C_eul)*Im + ε*(IDuDot + Iu) - C_eul
  --     ≤ (1/C_eul)*Im + (1/C_eul)*IpAlpha + ε*(IDuDot + Iu) - C_eul
  --     ≤ opDiff.
  have hIpAlpha_term_nn : 0 ≤ (1 / C_eul) * IpAlpha :=
    mul_nonneg hC_inv_pos.le hIpAlpha_nn
  have hDrop :
      (1 / C_eul) * Im + ε * (IDuDot + Iu) - C_eul ≤ opDiff := by
    have hadd :
        (1 / C_eul) * Im + ε * (IDuDot + Iu) - C_eul
          ≤ (1 / C_eul) * Im + (1 / C_eul) * IpAlpha
              + ε * (IDuDot + Iu) - C_eul := by
      linarith [hIpAlpha_term_nn]
    exact hadd.trans hComb
  -- Step E: final algebraic combine.
  -- From C: λ * gauge ≤ λ/κ + ((1/C_eul)*Im + ε*Iu + ε*IDuDot).
  -- From D: (1/C_eul)*Im + ε*(IDuDot + Iu) ≤ opDiff + C_eul, i.e.
  --   (1/C_eul)*Im + ε*Iu + ε*IDuDot ≤ opDiff + C_eul.
  -- Combine:
  --   λ * gauge ≤ λ/κ + opDiff + C_eul,
  -- equivalently `λ * gauge - (C_eul + λ/κ) ≤ opDiff`.
  have hD' : (1 / C_eul) * Im + ε * Iu + ε * IDuDot ≤ opDiff + C_eul := by
    have hrw : ε * (IDuDot + Iu) = ε * IDuDot + ε * Iu := by ring
    linarith [hDrop, hrw.le, hrw.ge]
  linarith [hCombined_bd, hD']

/-! ## Per-coordinate and Euclidean `|Du|^γ̄` integrability bridges

These two helpers supply the `hDu_int` and `hEuc_int` parameters
required by the absorption-core consumer when it invokes
`sum_integral_per_coord_pow_le_dim_mul_integral_euclideanDot_pow`
(Coercivity.lean, line 2440) on a Banach pair `v ∈ K_Aepsi`. Both
follow from the per-coordinate `MemLpPer γ̄` certificates carried by
`v.2.2 i : Periodic.LpPer γBar d`. -/

/-- **Per-coordinate `|Du_i|^γ̄` integrability** for `v : XBanach`.

Each gradient coordinate of a Banach pair `v` lies in `L^γ̄` over the
unit cube, hence `|Du_i|^γ̄` is integrable. The proof mirrors the
`hRpow_m_int` block of
`coercivity_combined_integrability_partial_of_paperHypotheses`
(line 185): use `MemLp.integrable_norm_rpow` on the per-coord
`MemLpPer γ̄ (DuOf v i)` certificate, then collapse `‖·‖^γ̄` to
`|·|^γ̄` via `Real.norm_eq_abs`. -/
theorem coercivity_combined_integrability_percoord_du_pow
    {γBarReal βBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (hγBar_pos : 0 < γBarReal)
    (v : XBanach d βBarReal γBarReal) :
    ∀ i, IntegrableOn (fun x => |DuOf v i x| ^ γBarReal) (UnitCube d) := by
  intro i
  -- Per-coord `MemLpPer γ̄` certificate from the Lp class `v.2.2 i`.
  have hDuLp : MemLpPer (d := d) (ENNReal.ofReal γBarReal) (DuOf v i) :=
    memLpPer_of_lpPer (d := d) (v.2.2 i)
  have hmemLp : MemLp (DuOf v i) (ENNReal.ofReal γBarReal)
      (volume.restrict (UnitCube d)) := hDuLp.toMemLp
  have hγ_ne_zero : ENNReal.ofReal γBarReal ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hγBar_pos).ne'
  have hγ_ne_top : ENNReal.ofReal γBarReal ≠ ⊤ := ENNReal.ofReal_ne_top
  have hint_norm : Integrable
      (fun x => ‖DuOf v i x‖ ^ (ENNReal.ofReal γBarReal).toReal)
      (volume.restrict (UnitCube d)) :=
    hmemLp.integrable_norm_rpow hγ_ne_zero hγ_ne_top
  have hγ_toReal : (ENNReal.ofReal γBarReal).toReal = γBarReal :=
    ENNReal.toReal_ofReal hγBar_pos.le
  rw [hγ_toReal] at hint_norm
  have heq : (fun x => ‖DuOf v i x‖ ^ γBarReal)
            = (fun x => |DuOf v i x| ^ γBarReal) := by
    funext x; rw [Real.norm_eq_abs]
  rw [heq] at hint_norm
  exact hint_norm

/-- **Euclidean `(Du⬝Du)^(γ̄/2)` integrability** for `v : XBanach`.

Direct delegation to the iter-0652 primitive
`integrable_euclideanDot_rpow_half_of_coord_memLp`
(Coercivity.lean, line 2916), supplied with the per-coordinate
`MemLpPer γ̄ (DuOf v i)` certificates extracted from the Lp components
of `v`. -/
theorem coercivity_combined_integrability_euclidean_du_pow_half
    {γBarReal βBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (hγBar_ge1 : 1 ≤ γBarReal)
    (v : XBanach d βBarReal γBarReal) :
    IntegrableOn
      (fun x => ((fun i => DuOf v i x) ⬝ (fun i => DuOf v i x)) ^ (γBarReal / 2))
      (UnitCube d) := by
  have hDuLp : ∀ i, Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal)
                      (DuOf v i) := by
    intro i; exact memLpPer_of_lpPer (d := d) (v.2.2 i)
  exact integrable_euclideanDot_rpow_half_of_coord_memLp
    (γBarReal := γBarReal) (DuOf v) hDuLp hγBar_ge1

/-! ### XBanach pointwise scaled-gauge wrap (iter 0667, child of
2026-05-18 split)

Composition of the nine landed pieces:
* `coercivity_combined_integrability_residues` — 6 integrability
  residues at `(v, hv)`.
* `coercivity_combined_from_paperHypotheses_uniform` — combined
  algebraic bound, with explicit `C_eul`.
* `gateauxWpIntegrand_integral_eq_positive_form` — Euclidean form of
  the Gateaux integral.
* `coercivity_min_gauge_le_integrated_of_paperHypotheses` — B2a
  integrated upper bound on the min-gauge.
* `sum_integral_per_coord_pow_le_dim_mul_integral_euclideanDot_pow` —
  per-coord → Euclidean bridge.
* `coercivity_combined_integrability_percoord_du_pow` &
  `coercivity_combined_integrability_euclidean_du_pow_half`
  (iter 0666) — the two integrability residues feeding the bridge.
* The three λ-coefficient bounds.
* `coercivity_scaled_min_gauge_absorption_core` — the pure-algebra
  assembly.

The result is the per-`v ∈ K_Aepsi` scaled-gauge inequality
`λ · gauge(v) − (C_eul + λ/κ) ≤ op-diff(v)`. -/

/-- **XBanach pointwise scaled-gauge wrap** (paper `prop:coercAepsi`,
line 982; iter 0667 assembly).

For `v ∈ K_Aepsi`, threading the 13 paper hypotheses through the
nine assembled pieces yields the per-`v` scaled-gauge inequality
```
λ · aepsiCoerciveGauge κ v − (C_eul + λ/κ)
  ≤ A_ε(v; v−1) − A_ε(0; v−1)
```
where `κ := coercivityGaugeExponent βBarReal γBarReal = min β̄ γ̄`,
`C_eul := coercivityIntegrandLowerBoundYoungConstant d (powerGrowth…) α β`,
and `λ := coercivityScaledGaugeLambda κ C_eul ε d γ̄`. -/
theorem coercivity_scaled_min_gauge_le_operator_diff_of_paperHypotheses
    {γBarReal βBarReal βBarReal' γBarReal' ε : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
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
    (hβBarTop : ENNReal.ofReal βBarReal ≠ ⊤)
    (hγ'_le_β : ENNReal.ofReal γBarReal' ≤ ENNReal.ofReal βBarReal)
    (hF_HJB_meas : ∀ q : XBanach d βBarReal γBarReal,
      AEStronglyMeasurable
        (fun x => -(uOf q x) - H x (fun i => DuOf q i x) (mOf q x) + V x)
        (volume.restrict (UnitCube d)))
    (hF_flux_meas : ∀ q : XBanach d βBarReal γBarReal, ∀ i,
      AEStronglyMeasurable
        (fun x => mOf q x * DpH x (fun j => DuOf q j x) (mOf q x) i)
        (volume.restrict (UnitCube d)))
    (hβ_gt1 : 1 < βBarReal) (hγ_gt1 : 1 < γBarReal)
    (hd_pos : 0 < (d : ℝ)) (hε_pos : 0 < ε) :
    let κ : ℝ := coercivityGaugeExponent βBarReal γBarReal
    let C_eul : ℝ :=
      coercivityIntegrandLowerBoundYoungConstant d
        (powerGrowthCoercivityConstant (d := d) hpow) hpow.α hpow.β
    let lam : ℝ := coercivityScaledGaugeLambda κ C_eul ε d γBarReal
    ∀ v : XBanach d βBarReal γBarReal, v ∈ K_Aepsi d βBarReal γBarReal →
      lam * aepsiCoerciveGauge (βBarReal := βBarReal) (γBarReal := γBarReal)
                κ v - (C_eul + lam / κ)
        ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε (DuOf v) (mOf v) (uOf v)
              (DuOf v) (mOf v - 1) (uOf v)
          - mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε (fun _ _ => 0) (fun _ => 1) (fun _ => 0)
              (DuOf v) (mOf v - 1) (uOf v) := by
  intro κ C_eul lam v hv
  -- Positivity facts.
  have hβPos : 0 < βBarReal := lt_trans zero_lt_one hβ_gt1
  have hγPos : 0 < γBarReal := lt_trans zero_lt_one hγ_gt1
  have hκ_pos : 0 < κ := by
    change 0 < coercivityGaugeExponent βBarReal γBarReal
    unfold coercivityGaugeExponent
    exact lt_of_lt_of_le zero_lt_one (le_min hβ_gt1.le hγ_gt1.le)
  have hC_eul_pos : 0 < C_eul :=
    coercivityIntegrandLowerBoundYoungConstant_pos _ _ _ _
  have hγBar_nn : 0 ≤ γBarReal := hγPos.le
  have hlam_pos : 0 < lam :=
    coercivityScaledGaugeLambda_pos hκ_pos hC_eul_pos hε_pos hd_pos hγBar_nn
  have hd1_pos_real : 0 < ((d : ℝ) + 1) := by linarith
  have hd1pow_pos : 0 < ((d : ℝ) + 1) ^ γBarReal :=
    Real.rpow_pos_of_pos hd1_pos_real _
  have hd_ge1 : 1 ≤ (d : ℝ) := by
    have hd_nat : 1 ≤ d := by
      rcases Nat.eq_zero_or_pos d with h | h
      · subst h; simp at hd_pos
      · exact h
    exact_mod_cast hd_nat
  have hγBar_ge1 : 1 ≤ γBarReal := hγ_gt1.le
  -- Step 3: integrability residues.
  obtain ⟨hm_pos, hInt_mu, hInt_10, hHam_int, hRpow_m_int, hRpow_p_int⟩ :=
    coercivity_combined_integrability_residues
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      hmon hpow hHat0 hAgree hV hExp
      hβBar_eq hγBar_eq hβBar'_eq hγBar'_eq
      hβ hγ hβTop hγ'_le_β hF_HJB_meas hF_flux_meas v hv
  -- Step 4: combined algebraic bound (uniform `C_eul`).
  have hComb_raw :
      (1 / C_eul) * (∫ x in UnitCube d, mOf v x ^ (hpow.β + 1))
          + (1 / C_eul) * (∫ x in UnitCube d, ‖fun i => DuOf v i x‖ ^ hpow.α)
          + ε * (∫ x in UnitCube d,
              vecAbsPowMinusTwo γBarReal (fun i => DuOf v i x)
                  * ((fun i => DuOf v i x) ⬝ (fun i => DuOf v i x))
                + absPowMinusTwo γBarReal (uOf v x) * (uOf v x * uOf v x))
          - C_eul
        ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε (DuOf v) (mOf v) (uOf v) (DuOf v) (mOf v - 1) (uOf v)
          - mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε (fun _ _ => 0) (fun _ => 1) (fun _ => 0)
              (DuOf v) (mOf v - 1) (uOf v) :=
    coercivity_combined_from_paperHypotheses_uniform (d := d)
      (γBar := γBarReal) (ε := ε) V hpow (DuOf v) (mOf v) (uOf v)
      hm_pos hInt_mu hInt_10 hHam_int hRpow_m_int hRpow_p_int
  -- Step 5: collapse the Gateaux integral to its positive form.
  have hGateaux_eq :
      (∫ x in UnitCube d,
          vecAbsPowMinusTwo γBarReal (fun i => DuOf v i x)
              * ((fun i => DuOf v i x) ⬝ (fun i => DuOf v i x))
            + absPowMinusTwo γBarReal (uOf v x) * (uOf v x * uOf v x))
        = ∫ x in UnitCube d,
            ((fun i => DuOf v i x) ⬝ (fun i => DuOf v i x)) ^ (γBarReal / 2)
              + |uOf v x| ^ γBarReal :=
    gateauxWpIntegrand_integral_eq_positive_form (d := d)
      γBarReal hγPos (DuOf v) (uOf v)
  -- Set abbreviations for integrals.
  set Im : ℝ := ∫ x in UnitCube d, mOf v x ^ (hpow.β + 1) with hIm_def
  set IpAlpha : ℝ := ∫ x in UnitCube d, ‖fun i => DuOf v i x‖ ^ hpow.α
    with hIpAlpha_def
  set IDuDot : ℝ := ∫ x in UnitCube d,
        ((fun i => DuOf v i x) ⬝ (fun i => DuOf v i x)) ^ (γBarReal / 2)
    with hIDuDot_def
  set Iu : ℝ := ∫ x in UnitCube d, |uOf v x| ^ γBarReal with hIu_def
  set IDu_sum : ℝ := ∑ i, ∫ x in UnitCube d, |DuOf v i x| ^ γBarReal
    with hIDu_sum_def
  -- Integrability of Iu and IDuDot terms (for sum splitting).
  have hIu_int : IntegrableOn (fun x => |uOf v x| ^ γBarReal) (UnitCube d) := by
    -- `MemLpPer γBar (uOf v)` from `v.2.1`, then `integrable_norm_rpow`.
    have huLp : MemLpPer (d := d) (ENNReal.ofReal γBarReal) (uOf v) :=
      memLpPer_of_lpPer (d := d) v.2.1
    have hmemLp : MemLp (uOf v) (ENNReal.ofReal γBarReal)
        (volume.restrict (UnitCube d)) := huLp.toMemLp
    have hγ_ne_zero : ENNReal.ofReal γBarReal ≠ 0 :=
      (ENNReal.ofReal_pos.mpr hγPos).ne'
    have hγ_ne_top : ENNReal.ofReal γBarReal ≠ ⊤ := ENNReal.ofReal_ne_top
    have hint_norm : Integrable
        (fun x => ‖uOf v x‖ ^ (ENNReal.ofReal γBarReal).toReal)
        (volume.restrict (UnitCube d)) :=
      hmemLp.integrable_norm_rpow hγ_ne_zero hγ_ne_top
    have hγ_toReal : (ENNReal.ofReal γBarReal).toReal = γBarReal :=
      ENNReal.toReal_ofReal hγPos.le
    rw [hγ_toReal] at hint_norm
    have heq : (fun x => ‖uOf v x‖ ^ γBarReal)
              = (fun x => |uOf v x| ^ γBarReal) := by
      funext x; rw [Real.norm_eq_abs]
    rw [heq] at hint_norm
    exact hint_norm
  have hIDuDot_int : IntegrableOn
      (fun x => ((fun i => DuOf v i x) ⬝ (fun i => DuOf v i x))
                  ^ (γBarReal / 2)) (UnitCube d) :=
    coercivity_combined_integrability_euclidean_du_pow_half
      (βBarReal := βBarReal) (γBarReal := γBarReal) hγBar_ge1 v
  have hDu_int : ∀ i,
      IntegrableOn (fun x => |DuOf v i x| ^ γBarReal) (UnitCube d) :=
    coercivity_combined_integrability_percoord_du_pow
      (βBarReal := βBarReal) (γBarReal := γBarReal) hγPos v
  -- Step 5 cont.: rewrite the integral of the sum as sum of integrals
  -- using `integral_add`. After the gateaux equality.
  have hSplit :
      (∫ x in UnitCube d,
          ((fun i => DuOf v i x) ⬝ (fun i => DuOf v i x)) ^ (γBarReal / 2)
            + |uOf v x| ^ γBarReal)
        = IDuDot + Iu :=
    MeasureTheory.integral_add hIDuDot_int hIu_int
  -- Rewrite hComb_raw to the absorption-core's `hComb` shape.
  have hComb :
      (1 / C_eul) * Im + (1 / C_eul) * IpAlpha
          + ε * (IDuDot + Iu) - C_eul
        ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε (DuOf v) (mOf v) (uOf v) (DuOf v) (mOf v - 1) (uOf v)
          - mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε (fun _ _ => 0) (fun _ => 1) (fun _ => 0)
              (DuOf v) (mOf v - 1) (uOf v) := by
    have hrw : (∫ x in UnitCube d,
            vecAbsPowMinusTwo γBarReal (fun i => DuOf v i x)
                * ((fun i => DuOf v i x) ⬝ (fun i => DuOf v i x))
              + absPowMinusTwo γBarReal (uOf v x) * (uOf v x * uOf v x))
          = IDuDot + Iu := by
      rw [hGateaux_eq]; exact hSplit
    have := hComb_raw
    rw [hrw] at this
    exact this
  -- Step 6: Im-identification: `∫|m|^β̄ = ∫m^(β+1) = Im` using `m > 0` a.e.
  -- and `βBarReal = hpow.β + 1`.
  have hIm_abs_eq : (∫ x in UnitCube d, |mOf v x| ^ βBarReal) = Im := by
    -- `|mOf v x|^βBarReal = (mOf v x)^βBarReal = (mOf v x)^(β+1)` a.e.
    -- using `m > 0` a.e. and `βBarReal = hpow.β + 1`.
    change (∫ x in UnitCube d, |mOf v x| ^ βBarReal)
          = ∫ x in UnitCube d, mOf v x ^ (hpow.β + 1)
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hm_pos] with x hxpos
    -- Direct chain on the value:
    -- `|mOf v x|^βBarReal = (mOf v x)^βBarReal = (mOf v x)^(β+1)`.
    have h1 : |mOf v x| ^ βBarReal = mOf v x ^ βBarReal := by
      rw [abs_of_pos hxpos]
    have h2 : mOf v x ^ βBarReal = mOf v x ^ (hpow.β + 1) := by
      congr 1
    exact h1.trans h2
  -- Step 7: B2a integrated upper bound on the gauge, multiplied by lam.
  have hGauge_bound :
      aepsiCoerciveGauge (βBarReal := βBarReal) (γBarReal := γBarReal)
          (coercivityGaugeExponent βBarReal γBarReal) v
        ≤ (1 + (∫ x in UnitCube d, |mOf v x| ^ βBarReal)
            + ((d : ℝ) + 1) ^ γBarReal *
                ((∫ x in UnitCube d, |uOf v x| ^ γBarReal)
                  + ∑ i, ∫ x in UnitCube d, |DuOf v i x| ^ γBarReal))
          / coercivityGaugeExponent βBarReal γBarReal :=
    coercivity_min_gauge_le_integrated_of_paperHypotheses
      hβBarTop hβTop hβ_gt1 hγ_gt1 v
  -- Multiply both sides by `lam > 0`, and rewrite Im_abs → Im and Iu, IDu_sum.
  have hGauge_le :
      lam * aepsiCoerciveGauge (βBarReal := βBarReal) (γBarReal := γBarReal)
              κ v
        ≤ lam * (1 + Im + (((d : ℝ) + 1) ^ γBarReal) * (Iu + IDu_sum)) / κ := by
    have hmul := mul_le_mul_of_nonneg_left hGauge_bound hlam_pos.le
    -- Unfold abbreviations on the RHS by rewriting backwards.
    change lam * aepsiCoerciveGauge (βBarReal := βBarReal) (γBarReal := γBarReal)
              (coercivityGaugeExponent βBarReal γBarReal) v
        ≤ lam * (1 + Im + (((d : ℝ) + 1) ^ γBarReal) * (Iu + IDu_sum))
            / coercivityGaugeExponent βBarReal γBarReal
    -- The two sides differ only by `hIm_abs_eq` and definitional rewrites
    -- of `Iu` and `IDu_sum`.
    have : lam * ((1 + (∫ x in UnitCube d, |mOf v x| ^ βBarReal)
              + ((d : ℝ) + 1) ^ γBarReal *
                  ((∫ x in UnitCube d, |uOf v x| ^ γBarReal)
                    + ∑ i, ∫ x in UnitCube d, |DuOf v i x| ^ γBarReal))
            / coercivityGaugeExponent βBarReal γBarReal)
          = lam * (1 + Im + (((d : ℝ) + 1) ^ γBarReal) * (Iu + IDu_sum))
              / coercivityGaugeExponent βBarReal γBarReal := by
      rw [← hIm_abs_eq, hIu_def, hIDu_sum_def]
      ring
    linarith [hmul, this.le, this.ge]
  -- Step 8: per-coord → Euclidean bridge.
  have hBridge : IDu_sum ≤ (d : ℝ) * IDuDot :=
    sum_integral_per_coord_pow_le_dim_mul_integral_euclideanDot_pow
      (d := d) γBarReal hγBar_nn (DuOf v) hDu_int hIDuDot_int
  -- Step 9: three λ-coefficient bounds.
  have hlam_inv : lam / κ ≤ 1 / C_eul :=
    coercivityScaledGaugeLambda_div_le_inv_Ceul
      hκ_pos hC_eul_pos hε_pos hd_pos hγBar_nn
  have hlam_dim : lam * ((d : ℝ) * (((d : ℝ) + 1) ^ γBarReal)) / κ ≤ ε :=
    coercivityScaledGaugeLambda_dim_full_mul_le_eps
      hκ_pos hC_eul_pos hε_pos hd_pos hγBar_nn
  have hlam_u : lam * (((d : ℝ) + 1) ^ γBarReal) / κ ≤ ε :=
    coercivityScaledGaugeLambda_u_le_eps
      hκ_pos hC_eul_pos hε_pos hd_ge1 hγBar_nn
  -- Nonnegativity inputs to the absorption core.
  have hIm_nn : 0 ≤ Im := by
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [hm_pos] with x hxpos
    exact Real.rpow_nonneg hxpos.le _
  have hIu_nn : 0 ≤ Iu := by
    refine MeasureTheory.integral_nonneg ?_
    intro x
    exact Real.rpow_nonneg (abs_nonneg _) _
  have hIDu_sum_nn : 0 ≤ IDu_sum := by
    refine Finset.sum_nonneg ?_
    intro i _
    refine MeasureTheory.integral_nonneg ?_
    intro x
    exact Real.rpow_nonneg (abs_nonneg _) _
  have hIDuDot_nn : 0 ≤ IDuDot := by
    refine MeasureTheory.integral_nonneg ?_
    intro x
    refine Real.rpow_nonneg ?_ _
    -- Nonneg of `v ⬝ v`.
    unfold euclideanDot
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have hIpAlpha_nn : 0 ≤ IpAlpha := by
    refine MeasureTheory.integral_nonneg ?_
    intro x
    exact Real.rpow_nonneg (norm_nonneg _) _
  -- Step 10: apply absorption core.
  exact coercivity_scaled_min_gauge_absorption_core
    (κ := κ) (C_eul := C_eul) (ε := ε) (lam := lam)
    (Im := Im) (Iu := Iu) (IDu_sum := IDu_sum) (IDuDot := IDuDot)
    (IpAlpha := IpAlpha)
    (gauge := aepsiCoerciveGauge (βBarReal := βBarReal)
                (γBarReal := γBarReal) κ v)
    (opDiff := mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                  γBarReal ε (DuOf v) (mOf v) (uOf v)
                    (DuOf v) (mOf v - 1) (uOf v)
                - mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                    γBarReal ε (fun _ _ => 0) (fun _ => 1) (fun _ => 0)
                    (DuOf v) (mOf v - 1) (uOf v))
    (γBar := γBarReal) (d := d)
    hκ_pos hC_eul_pos hlam_pos hlam_inv hlam_dim hlam_u hd1pow_pos
    hIm_nn hIu_nn hIDu_sum_nn hIDuDot_nn hIpAlpha_nn
    hGauge_le hComb hBridge

/-! ### Generic quotient-coercivity recovery (Child A, deliverable 1)

For arbitrary `λ > 0`, `κ > 1`, `C ∈ ℝ`, the function
`v ↦ (λ * aepsiCoerciveGauge κ v - C) / ‖v‖`
diverges to `+∞` on the filter `cobounded ⊓ 𝓟 K_Aepsi`. This is the
abstract quotient-coercivity recovery, independent of paper hypotheses.

The algebra: `aepsiCoerciveGauge κ v = ‖v‖^κ / κ`, so
`(λ * (‖v‖^κ / κ) - C) / ‖v‖ = (λ/κ) * ‖v‖^(κ-1) - C/‖v‖`.
Both `(λ/κ) * ‖v‖^(κ-1) → +∞` and `C/‖v‖ → 0` as `‖v‖ → +∞`, hence
the difference diverges. -/

theorem tendsto_scaled_aepsiCoerciveGauge_div_norm_atTop
    {d : ℕ} {βBarReal γBarReal κ lam C : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (hκ : 1 < κ) (hlam : 0 < lam) :
    Filter.Tendsto
      (fun v : XBanach d βBarReal γBarReal =>
        (lam * aepsiCoerciveGauge
              (βBarReal := βBarReal) (γBarReal := γBarReal) κ v - C) / ‖v‖)
      (Bornology.cobounded (XBanach d βBarReal γBarReal)
          ⊓ Filter.principal (K_Aepsi d βBarReal γBarReal))
      Filter.atTop := by
  have hκ_pos : 0 < κ := lt_trans zero_lt_one hκ
  have hκm1_pos : 0 < κ - 1 := sub_pos.mpr hκ
  have hlamκ_pos : 0 < lam / κ := div_pos hlam hκ_pos
  -- Norm tendsto along the inf filter.
  have h_nrm_tendsto :
      Filter.Tendsto (fun v : XBanach d βBarReal γBarReal => ‖v‖)
        (Bornology.cobounded (XBanach d βBarReal γBarReal)
            ⊓ Filter.principal (K_Aepsi d βBarReal γBarReal))
        Filter.atTop :=
    tendsto_norm_cobounded_atTop.mono_left inf_le_left
  -- `‖v‖^(κ-1) → +∞`.
  have h_pow_tendsto :
      Filter.Tendsto (fun v : XBanach d βBarReal γBarReal => ‖v‖ ^ (κ - 1))
        (Bornology.cobounded (XBanach d βBarReal γBarReal)
            ⊓ Filter.principal (K_Aepsi d βBarReal γBarReal))
        Filter.atTop :=
    (tendsto_rpow_atTop hκm1_pos).comp h_nrm_tendsto
  -- `(λ/κ) * ‖v‖^(κ-1) → +∞`.
  have h_main_tendsto :
      Filter.Tendsto
        (fun v : XBanach d βBarReal γBarReal => (lam / κ) * ‖v‖ ^ (κ - 1))
        (Bornology.cobounded (XBanach d βBarReal γBarReal)
            ⊓ Filter.principal (K_Aepsi d βBarReal γBarReal))
        Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hlamκ_pos h_pow_tendsto
  -- `C / ‖v‖ → 0` (since `‖v‖ → +∞`).
  have h_C_div_zero :
      Filter.Tendsto (fun v : XBanach d βBarReal γBarReal => C / ‖v‖)
        (Bornology.cobounded (XBanach d βBarReal γBarReal)
            ⊓ Filter.principal (K_Aepsi d βBarReal γBarReal))
        (nhds 0) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat C)
    -- More direct: use that `1/‖v‖ → 0` from `‖v‖ → +∞`.
    have h_inv : Filter.Tendsto (fun v : XBanach d βBarReal γBarReal => (‖v‖)⁻¹)
        (Bornology.cobounded (XBanach d βBarReal γBarReal)
            ⊓ Filter.principal (K_Aepsi d βBarReal γBarReal))
        (nhds 0) := by
      have := h_nrm_tendsto.inv_tendsto_atTop
      simpa only [Pi.inv_def] using this
    have h_mul : Filter.Tendsto
        (fun v : XBanach d βBarReal γBarReal => C * (‖v‖)⁻¹)
        (Bornology.cobounded (XBanach d βBarReal γBarReal)
            ⊓ Filter.principal (K_Aepsi d βBarReal γBarReal))
        (nhds (C * 0)) := h_inv.const_mul C
    simp at h_mul
    -- `C / ‖v‖ = C * (‖v‖)⁻¹`.
    refine h_mul.congr ?_
    intro v; ring
  -- Difference: `(λ/κ) * ‖v‖^(κ-1) - C/‖v‖ → +∞`.
  have h_diff_tendsto :
      Filter.Tendsto
        (fun v : XBanach d βBarReal γBarReal =>
          (lam / κ) * ‖v‖ ^ (κ - 1) - C / ‖v‖)
        (Bornology.cobounded (XBanach d βBarReal γBarReal)
            ⊓ Filter.principal (K_Aepsi d βBarReal γBarReal))
        Filter.atTop := by
    have h_neg_C_div : Filter.Tendsto
        (fun v : XBanach d βBarReal γBarReal => -(C / ‖v‖))
        (Bornology.cobounded (XBanach d βBarReal γBarReal)
            ⊓ Filter.principal (K_Aepsi d βBarReal γBarReal))
        (nhds 0) := by
      have := h_C_div_zero.neg
      simpa using this
    -- `(λ/κ) * ‖v‖^(κ-1) + (-(C/‖v‖)) → +∞ + 0 = +∞`.
    have h_add := h_main_tendsto.atTop_add h_neg_C_div
    refine h_add.congr ?_
    intro v
    change (lam / κ) * ‖v‖ ^ (κ - 1) + -(C / ‖v‖)
          = (lam / κ) * ‖v‖ ^ (κ - 1) - C / ‖v‖
    ring
  -- Eventually `‖v‖ > 0`.
  have h_nrm_pos :
      ∀ᶠ v in (Bornology.cobounded (XBanach d βBarReal γBarReal)
                  ⊓ Filter.principal (K_Aepsi d βBarReal γBarReal)),
        (0 : ℝ) < ‖v‖ :=
    h_nrm_tendsto.eventually_gt_atTop 0
  -- Congr identification: `(λ * (‖v‖^κ/κ) - C)/‖v‖ = (λ/κ) * ‖v‖^(κ-1) - C/‖v‖`.
  refine h_diff_tendsto.congr' ?_
  filter_upwards [h_nrm_pos] with v hv
  have hv_ne : ‖v‖ ≠ 0 := ne_of_gt hv
  -- Split `‖v‖^κ = ‖v‖^(κ-1) * ‖v‖`.
  have hsplit : ‖v‖ ^ κ = ‖v‖ ^ (κ - 1) * ‖v‖ := by
    have hh := Real.rpow_add hv (κ - 1) 1
    rw [Real.rpow_one] at hh
    have hsum : (κ - 1) + 1 = κ := by ring
    rw [hsum] at hh
    exact hh
  -- Goal: `(λ/κ) * ‖v‖^(κ-1) - C/‖v‖ = (λ * (‖v‖^κ/κ) - C) / ‖v‖`.
  change (lam / κ) * ‖v‖ ^ (κ - 1) - C / ‖v‖
        = (lam * aepsiCoerciveGauge (βBarReal := βBarReal)
              (γBarReal := γBarReal) κ v - C) / ‖v‖
  unfold aepsiCoerciveGauge
  rw [hsplit]
  have hκ_ne : κ ≠ 0 := ne_of_gt hκ_pos
  field_simp

/-! ### Cobounded packaging of Child 1's bound (Child A, deliverable 2)

Lifts `coercivity_scaled_min_gauge_le_operator_diff_of_paperHypotheses`
(which gives `∀ v ∈ K_Aepsi, λ · gauge κ v - (C_eul + λ/κ) ≤ op-diff(v)`)
to the cobounded ⊓ principal-K_Aepsi filter via
`Filter.eventually_inf_principal`. This is the `∀ᶠ`-form consumed by
the downstream `paperSection8_coercivity_of_paperHypotheses` producer
(deferred to a follow-up child due to the algebraic obstruction
explained in the parent task file). -/

theorem coercivity_scaled_min_gauge_le_operator_diff_eventually
    {γBarReal βBarReal βBarReal' γBarReal' ε : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
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
    (hβBarTop : ENNReal.ofReal βBarReal ≠ ⊤)
    (hγ'_le_β : ENNReal.ofReal γBarReal' ≤ ENNReal.ofReal βBarReal)
    (hF_HJB_meas : ∀ q : XBanach d βBarReal γBarReal,
      AEStronglyMeasurable
        (fun x => -(uOf q x) - H x (fun i => DuOf q i x) (mOf q x) + V x)
        (volume.restrict (UnitCube d)))
    (hF_flux_meas : ∀ q : XBanach d βBarReal γBarReal, ∀ i,
      AEStronglyMeasurable
        (fun x => mOf q x * DpH x (fun j => DuOf q j x) (mOf q x) i)
        (volume.restrict (UnitCube d)))
    (hβ_gt1 : 1 < βBarReal) (hγ_gt1 : 1 < γBarReal)
    (hd_pos : 0 < (d : ℝ)) (hε_pos : 0 < ε) :
    ∃ lam Ccoerc : ℝ, 0 < lam ∧
      ∀ᶠ v in (Bornology.cobounded (XBanach d βBarReal γBarReal)
                  ⊓ Filter.principal (K_Aepsi d βBarReal γBarReal)),
        lam * aepsiCoerciveGauge (βBarReal := βBarReal) (γBarReal := γBarReal)
                  (coercivityGaugeExponent βBarReal γBarReal) v - Ccoerc
          ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε (DuOf v) (mOf v) (uOf v)
                (DuOf v) (mOf v - 1) (uOf v)
            - mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                γBarReal ε (fun _ _ => 0) (fun _ => 1) (fun _ => 0)
                (DuOf v) (mOf v - 1) (uOf v) := by
  -- Set up the same κ, C_eul, lam as Child 1.
  set κ : ℝ := coercivityGaugeExponent βBarReal γBarReal with hκ_def
  set C_eul : ℝ :=
    coercivityIntegrandLowerBoundYoungConstant d
      (powerGrowthCoercivityConstant (d := d) hpow) hpow.α hpow.β with hC_def
  set lam : ℝ := coercivityScaledGaugeLambda κ C_eul ε d γBarReal with hlam_def
  -- Positivity of lam.
  have hβPos : 0 < βBarReal := lt_trans zero_lt_one hβ_gt1
  have hγPos : 0 < γBarReal := lt_trans zero_lt_one hγ_gt1
  have hκ_pos : 0 < κ := by
    change 0 < coercivityGaugeExponent βBarReal γBarReal
    unfold coercivityGaugeExponent
    exact lt_of_lt_of_le zero_lt_one (le_min hβ_gt1.le hγ_gt1.le)
  have hC_eul_pos : 0 < C_eul :=
    coercivityIntegrandLowerBoundYoungConstant_pos _ _ _ _
  have hlam_pos : 0 < lam :=
    coercivityScaledGaugeLambda_pos hκ_pos hC_eul_pos hε_pos hd_pos hγPos.le
  refine ⟨lam, C_eul + lam / κ, hlam_pos, ?_⟩
  -- Lift the pointwise bound to ∀ᶠ via `Filter.eventually_inf_principal`.
  rw [Filter.eventually_inf_principal]
  refine Filter.Eventually.of_forall ?_
  intro v hv
  -- Apply Child 1.
  have h_pt :=
    coercivity_scaled_min_gauge_le_operator_diff_of_paperHypotheses
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal') (ε := ε)
      hmon hpow hHat0 hAgree hV hExp
      hβBar_eq hγBar_eq hβBar'_eq hγBar'_eq
      hβ hγ hβTop hβBarTop hγ'_le_β hF_HJB_meas hF_flux_meas
      hβ_gt1 hγ_gt1 hd_pos hε_pos v hv
  -- `h_pt` already has exactly the desired shape (modulo `let` unfoldings
  -- for κ, C_eul, lam — which are definitionally equal here).
  exact h_pt

/-! ### Scaled-gauge sibling of `Aepsi_coercive_of_paperHypotheses`

Per the iter-0668 user decision (Path B), the paper-line-982
coercivity bound that the downstream chain genuinely produces is the
**scaled** form `λ · gauge κ v − C ≤ op_diff v` on the cobounded ⊓ K_Aepsi
filter, with `λ > 0` and `κ := coercivityGaugeExponent βBar γBar = min β̄ γ̄`.
The unscaled wrapper `Banach.Aepsi_coercive_of_paperHypotheses` (in
`Banach/AssemblyContext.lean`) is kept for legacy callers; this
scaled sibling threads the `λ`-factor and is the one consumed by the
new closed producer `paperSection8_coercivity_of_paperHypotheses`
(immediately below).

This declaration lives in `Coercivity/Integrability.lean` (rather than
`Banach/AssemblyContext.lean`) because it routes the quotient-tendsto
through `tendsto_scaled_aepsiCoerciveGauge_div_norm_atTop`, which lives
in this module. The import DAG is `Coercivity/Integrability →
Banach/AssemblyContext`, so the wrapper can call both
`Banach.isCoerciveAt_Aepsi_CLM_K_Aepsi` (via `AbstractLifts` re-export)
and the recovery lemma above. -/

/-- **Scaled-gauge sibling of `Aepsi_coercive_of_paperHypotheses`.**
Coercivity of the K_Aepsi-totalized operator `Aepsi_CLM_opK auxHypsK ε`
on `K_Aepsi` at the canonical base point `qRef_simplePower`, with the
**scaled** gauge `g v := lam * (‖v‖^κ / κ)`.

The integrated lower bound `hbound_residue` is the scaled paper-line-982
quotient bridge — exactly the shape produced by
`coercivity_scaled_min_gauge_le_operator_diff_eventually` above.

The quotient-tendsto `g v / ‖v‖ → +∞` is discharged via
`tendsto_scaled_aepsiCoerciveGauge_div_norm_atTop`. -/
theorem Aepsi_coercive_of_paperHypotheses_scaled
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (auxHypsK : ∀ q ∈ K_Aepsi d βBarReal γBarReal,
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V H DpH (fun i => ⇑(q.2.2 i)) (⇑q.1) (⇑q.2.1))
    (ε : ℝ)
    -- Scaled-gauge parameters: exponent `κ > 1` (the producer outputs
    -- `coercivityGaugeExponent βBarReal γBarReal = min β̄ γ̄`) and
    -- positive scaling `lam > 0`.
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
  -- a.e.-equalities for the canonical base point (same as unscaled wrapper).
  have h_m0_ae := qRef_simplePower_mOf_ae d βBarReal γBarReal
  have h_u0_ae := qRef_simplePower_uOf_ae d βBarReal γBarReal
  have h_Du0_ae := qRef_simplePower_DuOf_ae d βBarReal γBarReal
  -- Quotient-tendsto `g v / ‖v‖ = (lam * gauge κ v - 0) / ‖v‖ → +∞`,
  -- discharged via the landed recovery lemma above.
  have hquot_tendsto :
      Filter.Tendsto (fun v => g v / ‖v‖)
        (Bornology.cobounded (XBanach d βBarReal γBarReal)
            ⊓ Filter.principal (K_Aepsi d βBarReal γBarReal))
        Filter.atTop := by
    have h_recovery :=
      tendsto_scaled_aepsiCoerciveGauge_div_norm_atTop
        (d := d) (βBarReal := βBarReal) (γBarReal := γBarReal)
        (κ := κ) (lam := lam) (C := (0 : ℝ)) hκ hlam
    refine h_recovery.congr ?_
    intro v
    change (lam * aepsiCoerciveGauge (βBarReal := βBarReal) (γBarReal := γBarReal)
              κ v - (0 : ℝ)) / ‖v‖
          = lam * aepsiCoerciveGauge (βBarReal := βBarReal) (γBarReal := γBarReal)
              κ v / ‖v‖
    ring
  -- Compose via the K_Aepsi-form coercivity lift, supplying the scaled
  -- gauge and the supplied integrated lower bound.
  exact isCoerciveAt_Aepsi_CLM_K_Aepsi (γBarReal := γBarReal)
    (βBarReal := βBarReal) (βBarReal' := βBarReal') (γBarReal' := γBarReal')
    V H DpH auxHypsK ε
    (qRef_simplePower d βBarReal γBarReal)
    hqRef_mem h_m0_ae h_u0_ae h_Du0_ae
    g C hbound_residue hquot_tendsto

/-- **Sanity-check `example`.** `Aepsi_coercive_of_paperHypotheses_scaled`
accepts the K_Aepsi-indexed `auxHypsK` supplier, the scaling parameters
`(κ, hκ, lam, hlam)`, and the scaled paper-line-982 `hbound_residue`,
and delivers `IsCoerciveAt (K_Aepsi …) (Aepsi_CLM_opK …) qRef_simplePower`. -/
example
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (auxHypsK : ∀ q ∈ K_Aepsi d βBarReal γBarReal,
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V H DpH (fun i => ⇑(q.2.2 i)) (⇑q.1) (⇑q.2.1))
    (ε : ℝ)
    (κ : ℝ) (hκ : 1 < κ)
    (lam : ℝ) (hlam : 0 < lam)
    (C : ℝ)
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
      (qRef_simplePower d βBarReal γBarReal) :=
  Aepsi_coercive_of_paperHypotheses_scaled (γBarReal := γBarReal)
    (βBarReal := βBarReal) (βBarReal' := βBarReal') (γBarReal' := γBarReal')
    V H DpH auxHypsK ε κ hκ lam hlam C hbound_residue

/-! ### Closed paper-§8 producer (Path B final closure, Phase A)

The producer `paperSection8_coercivity_of_paperHypotheses` is the
paper-level forwarder for `prop:coercAepsi`: it packages
`coercivity_scaled_min_gauge_le_operator_diff_eventually` as an
existential statement `∃ lam Ccoerc, 0 < lam ∧ ∀ᶠ v, …`, suitable for
direct consumption by the new scaled coercivity wrapper
`Aepsi_coercive_of_paperHypotheses_scaled` (in
`Banach/AssemblyContext.lean`).

The gauge exponent is `coercivityGaugeExponent βBarReal γBarReal`
(`= min β̄ γ̄`), **not** `γBarReal`: that is the exponent the iter-0666
producer outputs and is the right choice to avoid imposing the
non-paper polarity `γ̄ ≤ β̄`. -/

/-- **Closed paper-§8 coercivity producer.**

Forwarder around `coercivity_scaled_min_gauge_le_operator_diff_eventually`
that surfaces the paper-line-982 conclusion as a single existential
statement. The output exponent is `coercivityGaugeExponent β̄ γ̄ = min β̄ γ̄`.

The downstream `Aepsi_coercive_of_paperHypotheses_scaled` consumes
`(lam, Ccoerc, hlam, hbound)` and lifts to `IsCoerciveAt`. -/
theorem paperSection8_coercivity_of_paperHypotheses
    {γBarReal βBarReal βBarReal' γBarReal' ε : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
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
    (hβBarTop : ENNReal.ofReal βBarReal ≠ ⊤)
    (hγ'_le_β : ENNReal.ofReal γBarReal' ≤ ENNReal.ofReal βBarReal)
    (hF_HJB_meas : ∀ q : XBanach d βBarReal γBarReal,
      AEStronglyMeasurable
        (fun x => -(uOf q x) - H x (fun i => DuOf q i x) (mOf q x) + V x)
        (volume.restrict (UnitCube d)))
    (hF_flux_meas : ∀ q : XBanach d βBarReal γBarReal, ∀ i,
      AEStronglyMeasurable
        (fun x => mOf q x * DpH x (fun j => DuOf q j x) (mOf q x) i)
        (volume.restrict (UnitCube d)))
    (hβ_gt1 : 1 < βBarReal) (hγ_gt1 : 1 < γBarReal)
    (hd_pos : 0 < (d : ℝ)) (hε_pos : 0 < ε) :
    ∃ lam Ccoerc : ℝ, 0 < lam ∧
      ∀ᶠ v in (Bornology.cobounded (XBanach d βBarReal γBarReal)
                  ⊓ Filter.principal (K_Aepsi d βBarReal γBarReal)),
        lam * aepsiCoerciveGauge (βBarReal := βBarReal) (γBarReal := γBarReal)
                  (coercivityGaugeExponent βBarReal γBarReal) v - Ccoerc
          ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε (DuOf v) (mOf v) (uOf v)
                (DuOf v) (mOf v - 1) (uOf v)
            - mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                γBarReal ε (fun _ _ => 0) (fun _ => 1) (fun _ => 0)
                (DuOf v) (mOf v - 1) (uOf v) :=
  coercivity_scaled_min_gauge_le_operator_diff_eventually
    (γBarReal := γBarReal) (βBarReal := βBarReal)
    (βBarReal' := βBarReal') (γBarReal' := γBarReal') (ε := ε)
    hmon hpow hHat0 hAgree hV hExp
    hβBar_eq hγBar_eq hβBar'_eq hγBar'_eq
    hβ hγ hβTop hβBarTop hγ'_le_β hF_HJB_meas hF_flux_meas
    hβ_gt1 hγ_gt1 hd_pos hε_pos

/-! ### Closed `PaperSection8AnalyticResiduesMin.of_paperHypotheses` producer
(`paperSolFor-analytic-residues-min-of-paperHypotheses`, iter post-0670)

This producer assembles the full 13-field paper-faithful analytic bundle
`PaperSection8AnalyticResiduesMin` at the paper exponents from the closed
producers already in scope:

* `paperSection8_h_upper_of_powerGrowth` / `paperSection8_hSlice_of_powerGrowth`
  (upper / slice bounds);
* `paperSection8_hF_HJB_meas_of_powerGrowth` /
  `paperSection8_hF_flux_meas_of_powerGrowth` /
  `paperSection8_hF_unreg_meas_of_powerGrowth` /
  `paperSection8_hF_gat_meas_of_powerGrowth` (measurability);
* `paperSection8_hScalarMono_of_gamma` / `paperSection8_hVecMono_of_gamma`
  (monotonicity);
* `paperSection8_coercivity_of_paperHypotheses` (scaled coercivity
  `(lamCoerc, hlamCoerc, Ccoerc, hbound_residue)` quadruple, iter 0669);
* `paperSection8_segmentResiduesMin_of_paperHypotheses` (the 11-conjunct
  paper-faithful minimal segment residue bundle);
* `PaperSection8AuxHypsK0Fields.of_paperHypotheses` (the `auxHypsK0` and
  `hWeakDerivK0` K0-quantified composition bundle).

**Location rationale.** This declaration lives in
`StationaryMFG/Theorems/SimplePower/Coercivity/Integrability.lean` (rather
than in `Banach/AssemblyContext.lean` as the task spec originally
suggested) because the coercivity producer
`paperSection8_coercivity_of_paperHypotheses` is itself in this module.
Placing the analytic-bundle producer in `AssemblyContext.lean` would
require either (a) re-introducing the import cycle that iter-0670 closed
by inlining `Aepsi_coercive_of_paperHypotheses_scaled`, or (b) inlining
the entire coercivity producer. Option (a) is forbidden; option (b)
would duplicate hundreds of lines of proof. Living downstream of
`AssemblyContext.lean` is the natural choice and matches the placement
of `paperSection8_coercivity_of_paperHypotheses` itself. -/

/-- **Closed `PaperSection8AnalyticResiduesMin.of_paperHypotheses` producer.**

Assembles the full 13-field paper-faithful analytic bundle at the paper
exponents from the four primary paper hypotheses `(hmon, hpow, hV)` plus
the two standing auths `(hHat0, hAgree)` and a `[Fact (0 < d)]` typeclass
instance for dimension positivity. All field assembly is by direct
projection through the closed producers above.

Recovery (post-0668): the `hWeakDeriv` parameter is consumed at this
layer, since the `hWeakDerivK0` field of
`PaperSection8AnalyticResiduesMin` is K0_Aepsi-form. The
iter-0689-attempt-1 relocation (moving the auth upstairs to the wrapper
`_closed_paper*` and retyping the field to K0_Aepsi_W) was reverted in
the post-0668 recovery iteration. Auth count: 4. -/
noncomputable def
    StationaryMFG.Theorems.SimplePower.Banach.PaperSection8AnalyticResiduesMin.of_paperHypotheses
    {d : ℕ} {ε : ℝ}
    (hε : 0 < ε)
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone (d := d) H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    (hV : Periodic.MemLpPer (d := d)
      (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) V)
    [hdFact : Fact (0 < d)]
    [Fact (1 ≤ ENNReal.ofReal (hpow.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))] :
    StationaryMFG.Theorems.SimplePower.Banach.PaperSection8AnalyticResiduesMin
      (d := d)
      (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
      (βBarReal := hpow.β + 1)
      (βBarReal' := (hpow.β + 1) / hpow.β)
      (γBarReal' :=
        (hpow.α * (hpow.β + 1) / hpow.β) /
          (hpow.α * (hpow.β + 1) / hpow.β - 1))
      ε V H DpH hpow := by
  classical
  -- Local abbreviations for the paper exponents (mirrors
  -- `aepsiUniformContextK_of_paperHypotheses_closed_paper_min`).
  set βBarReal : ℝ := hpow.β + 1 with hβBarReal_def
  set γBarReal : ℝ := hpow.α * (hpow.β + 1) / hpow.β with hγBarReal_def
  set βBarReal' : ℝ := (hpow.β + 1) / hpow.β with hβBarReal'_def
  set γBarReal' : ℝ := γBarReal / (γBarReal - 1) with hγBarReal'_def
  -- Exponent bundle.
  have hExp_paper :
      SimplePowerExponentFacts
          (SimplePowerExponentFacts.paperGammaBarReal hpow.α hpow.β)
          (SimplePowerExponentFacts.paperBetaBar hpow.β)
          (SimplePowerExponentFacts.paperGammaBar hpow.α hpow.β)
          (SimplePowerExponentFacts.paperBetaBarPrime hpow.β) :=
    SimplePowerExponentFacts.ofPowerGrowth hpow
  have hExp :
      SimplePowerExponentFacts γBarReal
          (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
          (ENNReal.ofReal βBarReal') := by
    have h1 :
        (SimplePowerExponentFacts.paperBetaBar hpow.β)
          = ENNReal.ofReal βBarReal := by
      simp [SimplePowerExponentFacts.paperBetaBar, hβBarReal_def]
    have h2 :
        (SimplePowerExponentFacts.paperGammaBar hpow.α hpow.β)
          = ENNReal.ofReal γBarReal := by
      simp [SimplePowerExponentFacts.paperGammaBar, hγBarReal_def]
    have h3 :
        (SimplePowerExponentFacts.paperBetaBarPrime hpow.β)
          = ENNReal.ofReal βBarReal' := by
      simp [SimplePowerExponentFacts.paperBetaBarPrime, hβBarReal'_def]
    have h4 :
        (SimplePowerExponentFacts.paperGammaBarReal hpow.α hpow.β)
          = γBarReal := by
      simp [SimplePowerExponentFacts.paperGammaBarReal, hγBarReal_def]
    have := hExp_paper
    rw [h1, h2, h3, h4] at this
    exact this
  -- Group-B equality residues.
  have hβBar_eq : βBarReal = hpow.β + 1 := hβBarReal_def
  have hγBar_eq : γBarReal = hpow.α * (hpow.β + 1) / hpow.β := hγBarReal_def
  have hβBar'_eq : βBarReal' = (hpow.β + 1) / hpow.β := hβBarReal'_def
  have hγBar'_eq : γBarReal' = γBarReal / (γBarReal - 1) := hγBarReal'_def
  -- Hölder conjugacies.
  have hβ : βBarReal.HolderConjugate βBarReal' :=
    SimplePowerExponentFacts.paper_holderConjugate_betaBar hpow.hβ
  have hγ : γBarReal.HolderConjugate γBarReal' :=
    SimplePowerExponentFacts.paper_holderConjugate_gammaBar hpow.hα hpow.hβ
  -- Inequality residues.
  have hβTop : ENNReal.ofReal γBarReal ≠ ⊤ := hExp.gammaBar_lt_top.ne
  have hβBarTop : ENNReal.ofReal βBarReal ≠ ⊤ := ENNReal.ofReal_ne_top
  have hγBar_one_lt : 1 < γBarReal := hExp.γBar_one_lt_real
  have hβ_gt1 : 1 < βBarReal := hβ.lt
  have hγ'_le_β : ENNReal.ofReal γBarReal' ≤ ENNReal.ofReal βBarReal := by
    have hle_real : γBarReal' ≤ βBarReal := by
      rw [hγBarReal'_def, hγBarReal_def, hβBarReal_def]
      have h_paper := Hamiltonian.gammaBar'_le_betaBar hpow.hα hpow.hβ
      simpa [Hamiltonian.gammaBar', Hamiltonian.gammaBar,
             Hamiltonian.betaBar] using h_paper
    exact ENNReal.ofReal_le_ofReal hle_real
  -- Closed measurability/upper/slice/mono producers.
  have h_upper :=
    StationaryMFG.Theorems.SimplePower.Banach.paperSection8_h_upper_of_powerGrowth
      (d := d) hpow
  have h_slice :=
    StationaryMFG.Theorems.SimplePower.Banach.paperSection8_hSlice_of_powerGrowth
      (d := d) hpow
  have hF_HJB_meas :=
    StationaryMFG.Theorems.SimplePower.Banach.paperSection8_hF_HJB_meas_of_powerGrowth
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal') hpow hV
  have hF_flux_meas :=
    StationaryMFG.Theorems.SimplePower.Banach.paperSection8_hF_flux_meas_of_powerGrowth
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal') (V := V) hpow
  have hF_unreg_meas :=
    StationaryMFG.Theorems.SimplePower.Banach.paperSection8_hF_unreg_meas_of_powerGrowth
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal') hpow hV
  have hF_gat_meas :=
    StationaryMFG.Theorems.SimplePower.Banach.paperSection8_hF_gat_meas_of_powerGrowth
      (d := d) (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
  have hScalarMono :=
    StationaryMFG.Theorems.SimplePower.Banach.paperSection8_hScalarMono_of_gamma
      (γBarReal := γBarReal) hγBar_one_lt
  have hVecMono :=
    StationaryMFG.Theorems.SimplePower.Banach.paperSection8_hVecMono_of_gamma
      (d := d) (γBarReal := γBarReal) hγBar_one_lt
  -- Dimension positivity, derived from the `[Fact (0 < d)]` instance.
  -- This internalises the `hd_pos` parameter of iter post-0681 child A:
  -- the `Fact` instance is a typeclass argument, not a paper-input
  -- authorisation, so it does not bump the auth count.
  have hd_pos : 0 < (d : ℝ) := Nat.cast_pos.mpr hdFact.out
  -- Closed scaled-coercivity producer (iter 0669). The producer returns
  -- `∃ lam Ccoerc : ℝ, …`, which is a `Prop`; we cannot destructure into
  -- a `Type`-valued body, so we use `Classical.choose` / `_spec` instead.
  have hCoerc :=
    paperSection8_coercivity_of_paperHypotheses
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal') (ε := ε)
      hmon hpow hHat0 hAgree hV hExp
      hβBar_eq hγBar_eq hβBar'_eq hγBar'_eq
      hβ hγ hβTop hβBarTop hγ'_le_β hF_HJB_meas hF_flux_meas
      hβ_gt1 hγBar_one_lt hd_pos hε
  let lamCoerc : ℝ := Classical.choose hCoerc
  let Ccoerc : ℝ := Classical.choose (Classical.choose_spec hCoerc)
  have hCoerc_spec := Classical.choose_spec (Classical.choose_spec hCoerc)
  have hlamCoerc : 0 < lamCoerc := hCoerc_spec.1
  have hbound_residue := hCoerc_spec.2
  -- Closed paper-faithful 11-conjunct segment residue producer.
  have hSegMin :=
    StationaryMFG.Theorems.SimplePower.Banach.paperSection8_segmentResiduesMin_of_paperHypotheses
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal') (V := V) (H := H)
      (DpH := DpH) hpow hβBar_eq hγBar_eq hβBar'_eq hγBar'_eq
  -- K0-quantified composition bundle producer.
  have hAuxK0 :=
    StationaryMFG.Theorems.SimplePower.Banach.PaperSection8AuxHypsK0Fields.of_paperHypotheses
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      hmon hpow hHat0 hAgree hV hExp
      hβBar_eq hγBar_eq hβBar'_eq hγBar'_eq
      hβ hγ hβTop hγ'_le_β hF_HJB_meas hF_flux_meas
  -- Assemble the 13-field record.
  show StationaryMFG.Theorems.SimplePower.Banach.PaperSection8AnalyticResiduesMin
      (d := d) γBarReal βBarReal βBarReal' γBarReal' ε V H DpH hpow
  exact
    { h_upper := h_upper
      hF_HJB_meas := hF_HJB_meas
      hF_flux_meas := hF_flux_meas
      hScalarMono := hScalarMono
      hVecMono := hVecMono
      lamCoerc := lamCoerc
      hlamCoerc := hlamCoerc
      Ccoerc := Ccoerc
      hbound_residue := hbound_residue
      h_slice := h_slice
      hSegMin := hSegMin
      hF_unreg_meas := hF_unreg_meas
      hF_gat_meas := hF_gat_meas
      auxHypsK0 := hAuxK0.auxHypsK0
      hWeakDerivK0 := hAuxK0.hWeakDerivK0 }

end SimplePower
end Theorems
end StationaryMFG
