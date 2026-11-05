module

public import StationaryMFG.Theorems.SimplePower.Coercivity.Integrability
public import StationaryMFG.Theorems.InfimalConvolution.Properties

@[expose] public section

/-!
# AE-keyed coercivity Eulerian/combined bound (paper `prop:coercAepsi`)

This module is the **AE sibling** of the `hpow`-keyed coercivity Eulerian and
combined-algebraic bounds in `Coercivity.lean`
(`coercivity_eulerian_from_paperHypotheses_uniform`,
`coercivity_combined_from_paperHypotheses_uniform`). It re-derives the same
integrated lower bound off the a.e. estimate carrier
`HdeltaAEPowerEpsData hweak qε` (fields `lagr_ae`, `lower_ae`, `upper_ae`,
`DpH_upper_ae`) on the raw `Hdelta hweak ε` / `DpHepsilonFam hweak qε ε`, at the
paper exponents `hweak.α` / `hweak.β` and the per-`ε` constant
`CdeltaEps hweak ε`.

## Why a separate AE chain (T3 sig-fix discipline)

The T3 public theorem `thm_main_weak_power_growth` must not carry a
`HypothesisPowerGrowth (HdeltaPos …)` (`powData`) input. The strict coercivity
chain serves T1/T2 byte-for-byte and is kept intact. This module is an
**additive sibling**: it depends ONLY on `(hweak, qε, hAE)` plus the same
`IntegrableOn` residues the strict `_uniform` lemmas take. None of `powData`,
`HypothesisPowerGrowth (HdeltaPos …)`, `hqE_per`, `hFormPos`, `hInj`, `hSurj`,
`qEofMinv` appears in any signature here.

## Layer audit (recorded in the task file)

The genuine pointwise consumers in the strict path are the four
`paperHypotheses_*_at_uniform` lemmas (Coercivity.lean), which inflate
`hpow.C` to `2·hpow.C+1` so the `(0,1)` bounds fit. Their AE siblings here
inflate `CdeltaEps` to `2·CdeltaEps+1` and feed the **generic** `hpow`-free
core `coercivity_integrand_lower_bound_young` / `coercivity_integral_lower_bound`
/ `coercive_test_pair_identity`.

-- Adapted from `coercivity_*_from_paperHypotheses*` (the `hpow`-keyed siblings).
-/

noncomputable section

namespace StationaryMFG
namespace Theorems
namespace SimplePower

open MeasureTheory Set
open StationaryMFG.Periodic
open StationaryMFG.Hamiltonian
open StationaryMFG.Solutions.MFG
open StationaryMFG.InfimalConvolution
open Banach
open scoped ENNReal NNReal

variable {d : ℕ}
variable {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
variable {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}

/-! ## The inflated AE coercivity constant -/

/-- The inflated per-`ε` coercivity constant `C̃_ε := 2·C_ε + 1`, the AE sibling
of `powerGrowthCoercivityConstant hpow = 2·hpow.C+1`. The inflation makes the
`(p,m) = (0,1)` bounds (`|H|`, `‖DpH‖`) fit under a single constant. -/
def coercivityCdeltaEpsUniform
    (hweak : HypothesisWeakGrowth (d := d) H DpH) (ε : ℝ) : ℝ :=
  2 * CdeltaEps (H := H) (DpH := DpH) hweak ε + 1

lemma coercivityCdeltaEpsUniform_pos
    (hweak : HypothesisWeakGrowth (d := d) H DpH) {ε : ℝ} (hε : 0 < ε) :
    0 < coercivityCdeltaEpsUniform (H := H) (DpH := DpH) hweak ε := by
  unfold coercivityCdeltaEpsUniform
  have := (cdeltaEps_facts_upper (H := H) (DpH := DpH) hweak hε).1
  linarith

lemma coercivityCdeltaEpsUniform_ge_cdeltaEps
    (hweak : HypothesisWeakGrowth (d := d) H DpH) {ε : ℝ} (hε : 0 < ε) :
    CdeltaEps (H := H) (DpH := DpH) hweak ε
      ≤ coercivityCdeltaEpsUniform (H := H) (DpH := DpH) hweak ε := by
  unfold coercivityCdeltaEpsUniform
  have := (cdeltaEps_facts_upper (H := H) (DpH := DpH) hweak hε).1
  linarith

/-! ## The four AE bridges at the inflated constant -/

/-- **AE `h_lagr` at the inflated constant `C̃_ε`** — sibling of
`paperHypotheses_lagr_at_uniform`, derived from `hAE.lagr_ae`. -/
lemma aeData_lagr_at_uniform
    {hweak : HypothesisWeakGrowth (d := d) H DpH} {qε : QEpsFamily d}
    (hAE : HdeltaAEPowerEpsData (H := H) (DpH := DpH) hweak qε)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p mx, 0 < mx →
        (mx ^ hweak.β) / coercivityCdeltaEpsUniform (H := H) (DpH := DpH) hweak ε
            - coercivityCdeltaEpsUniform (H := H) (DpH := DpH) hweak ε
          ≤ (DpHepsilonFam hweak qε ε x p mx) ⬝ p - Hdelta hweak ε x p mx := by
  set Ctil : ℝ := coercivityCdeltaEpsUniform (H := H) (DpH := DpH) hweak ε
    with hCtil
  have hCtil_pos : 0 < Ctil :=
    coercivityCdeltaEpsUniform_pos (H := H) (DpH := DpH) hweak hε
  have hC_le : CdeltaEps (H := H) (DpH := DpH) hweak ε ≤ Ctil :=
    coercivityCdeltaEpsUniform_ge_cdeltaEps (H := H) (DpH := DpH) hweak hε
  have hC_pos : 0 < CdeltaEps (H := H) (DpH := DpH) hweak ε :=
    (cdeltaEps_facts_upper (H := H) (DpH := DpH) hweak hε).1
  filter_upwards [hAE.lagr_ae ε hε hε1] with x hLagr p mx hmx
  have hraw := hLagr p mx hmx
  have hmβ_nn : 0 ≤ mx ^ hweak.β := Real.rpow_nonneg hmx.le _
  have hinv : 1 / Ctil ≤ 1 / CdeltaEps (H := H) (DpH := DpH) hweak ε := by
    rw [one_div, one_div]; exact inv_anti₀ hC_pos hC_le
  have hdivLe : mx ^ hweak.β / Ctil
      ≤ mx ^ hweak.β / CdeltaEps (H := H) (DpH := DpH) hweak ε := by
    rw [div_eq_mul_one_div, div_eq_mul_one_div (mx ^ hweak.β)]
    exact mul_le_mul_of_nonneg_left hinv hmβ_nn
  have hnegLe : -Ctil ≤ -CdeltaEps (H := H) (DpH := DpH) hweak ε :=
    neg_le_neg hC_le
  linarith

/-- **AE `h_lower` at the inflated constant `C̃_ε`** — sibling of
`paperHypotheses_lower_at_uniform`, derived from `hAE.lower_ae`. -/
lemma aeData_lower_at_uniform
    {hweak : HypothesisWeakGrowth (d := d) H DpH} {qε : QEpsFamily d}
    (hAE : HdeltaAEPowerEpsData (H := H) (DpH := DpH) hweak qε)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p mx, 0 < mx →
        (‖p‖ ^ hweak.α)
            / coercivityCdeltaEpsUniform (H := H) (DpH := DpH) hweak ε
            - coercivityCdeltaEpsUniform (H := H) (DpH := DpH) hweak ε
              * (mx ^ hweak.β + 1)
          ≤ Hdelta hweak ε x p mx := by
  set Ctil : ℝ := coercivityCdeltaEpsUniform (H := H) (DpH := DpH) hweak ε
    with hCtil
  have hCtil_pos : 0 < Ctil :=
    coercivityCdeltaEpsUniform_pos (H := H) (DpH := DpH) hweak hε
  have hC_le : CdeltaEps (H := H) (DpH := DpH) hweak ε ≤ Ctil :=
    coercivityCdeltaEpsUniform_ge_cdeltaEps (H := H) (DpH := DpH) hweak hε
  have hC_pos : 0 < CdeltaEps (H := H) (DpH := DpH) hweak ε :=
    (cdeltaEps_facts_upper (H := H) (DpH := DpH) hweak hε).1
  filter_upwards [hAE.lower_ae ε hε hε1] with x hLow p mx hmx
  have hraw := hLow p mx hmx
  have hmβ_nn : 0 ≤ mx ^ hweak.β := Real.rpow_nonneg hmx.le _
  have hpα_nn : 0 ≤ ‖p‖ ^ hweak.α := Real.rpow_nonneg (norm_nonneg _) _
  have hinv : 1 / Ctil ≤ 1 / CdeltaEps (H := H) (DpH := DpH) hweak ε := by
    rw [one_div, one_div]; exact inv_anti₀ hC_pos hC_le
  have hdivLe : ‖p‖ ^ hweak.α / Ctil
      ≤ ‖p‖ ^ hweak.α / CdeltaEps (H := H) (DpH := DpH) hweak ε := by
    rw [div_eq_mul_one_div, div_eq_mul_one_div (‖p‖ ^ hweak.α)]
    exact mul_le_mul_of_nonneg_left hinv hpα_nn
  have hsum_nn : 0 ≤ mx ^ hweak.β + 1 := by linarith
  have hmulLe : CdeltaEps (H := H) (DpH := DpH) hweak ε * (mx ^ hweak.β + 1)
      ≤ Ctil * (mx ^ hweak.β + 1) :=
    mul_le_mul_of_nonneg_right hC_le hsum_nn
  linarith [hraw, hdivLe, hmulLe]

/-- **AE `h_H01_le` at the inflated constant `C̃_ε`** — sibling of
`paperHypotheses_H01_le_uniform`. Upper from `hAE.upper_ae` at `m = 1`
(`Hdelta(x,0,1) ≤ -1/C_ε + C_ε ≤ C_ε`); lower from `hAE.lower_ae` at
`(p,m)=(0,1)` (`Hdelta(x,0,1) ≥ -2·C_ε`). Hence `|Hdelta(x,0,1)| ≤ 2·C_ε ≤
C̃_ε`. -/
lemma aeData_H01_le_at_uniform
    {hweak : HypothesisWeakGrowth (d := d) H DpH} {qε : QEpsFamily d}
    (hAE : HdeltaAEPowerEpsData (H := H) (DpH := DpH) hweak qε)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      |Hdelta hweak ε x (0 : Fin d → ℝ) 1|
        ≤ coercivityCdeltaEpsUniform (H := H) (DpH := DpH) hweak ε := by
  set Cε : ℝ := CdeltaEps (H := H) (DpH := DpH) hweak ε with hCε
  set Ctil : ℝ := coercivityCdeltaEpsUniform (H := H) (DpH := DpH) hweak ε
    with hCtil
  have hC_pos : 0 < Cε := (cdeltaEps_facts_upper (H := H) (DpH := DpH) hweak hε).1
  have hCtil_eq : Ctil = 2 * Cε + 1 := rfl
  filter_upwards [hAE.upper_ae ε hε hε1, hAE.lower_ae ε hε hε1] with x hUp hLow
  -- Upper at m = 1: `Hdelta(x,0,1) ≤ -1^β/Cε + Cε`.
  have hup := hUp 1 one_pos
  have hone : (1 : ℝ) ^ hweak.β = 1 := Real.one_rpow _
  rw [hone] at hup
  -- `hup : Hdelta x 0 1 ≤ -1/Cε + Cε`.
  -- Lower at (0,1): `0^α/Cε - Cε·(1+1) ≤ Hdelta(x,0,1)`.
  have hlow := hLow (0 : Fin d → ℝ) 1 one_pos
  have hα_pos : 0 < hweak.α := lt_trans one_pos hweak.hα
  have hα_ne : hweak.α ≠ 0 := ne_of_gt hα_pos
  have hzero_α : ‖(0 : Fin d → ℝ)‖ ^ hweak.α = 0 := by
    rw [norm_zero, Real.zero_rpow hα_ne]
  rw [hzero_α, hone] at hlow
  -- `hlow : 0/Cε - Cε*(1+1) ≤ Hdelta x 0 1`.
  have hUpCtil : Hdelta hweak ε x (0 : Fin d → ℝ) 1 ≤ Ctil := by
    have hnorm : (-1 : ℝ) / Cε = -(1 / Cε) := by ring
    have hup' : Hdelta hweak ε x (0 : Fin d → ℝ) 1 ≤ -(1 / Cε) + Cε := by
      have := hup; rw [hnorm] at this; exact this
    have h1 : -(1 / Cε) + Cε ≤ Cε := by
      have : 0 ≤ 1 / Cε := le_of_lt (by positivity)
      linarith
    have h2 : Cε ≤ Ctil := by rw [hCtil_eq]; linarith
    linarith
  have hLowCtil : -Ctil ≤ Hdelta hweak ε x (0 : Fin d → ℝ) 1 := by
    have h1 : (0 : ℝ) / Cε - Cε * (1 + 1) = -(2 * Cε) := by
      rw [zero_div]; ring
    have hlow' : -(2 * Cε) ≤ Hdelta hweak ε x (0 : Fin d → ℝ) 1 := by
      have := hlow; rw [h1] at this; exact this
    have h2 : -Ctil ≤ -(2 * Cε) := by rw [hCtil_eq]; linarith
    linarith
  rw [abs_le]
  exact ⟨hLowCtil, hUpCtil⟩

/-- **AE `h_DpH01_le` at the inflated constant `C̃_ε`** — sibling of
`paperHypotheses_DpH01_le_uniform`, derived from `hAE.DpH_upper_ae` at
`(p,m)=(0,1)`: `‖DpH(x,0,1)‖ ≤ C_ε(0^{α-1}+1^{β-β/α}+1) = 2·C_ε ≤ C̃_ε`. -/
lemma aeData_DpH01_le_at_uniform
    {hweak : HypothesisWeakGrowth (d := d) H DpH} {qε : QEpsFamily d}
    (hAE : HdeltaAEPowerEpsData (H := H) (DpH := DpH) hweak qε)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ‖DpHepsilonFam hweak qε ε x (0 : Fin d → ℝ) 1‖
        ≤ coercivityCdeltaEpsUniform (H := H) (DpH := DpH) hweak ε := by
  set Cε : ℝ := CdeltaEps (H := H) (DpH := DpH) hweak ε with hCε
  set Ctil : ℝ := coercivityCdeltaEpsUniform (H := H) (DpH := DpH) hweak ε
    with hCtil
  have hC_pos : 0 < Cε := (cdeltaEps_facts_upper (H := H) (DpH := DpH) hweak hε).1
  have hCtil_eq : Ctil = 2 * Cε + 1 := rfl
  have hα_m1_pos : 0 < hweak.α - 1 := sub_pos.mpr hweak.hα
  have hα_m1_ne : hweak.α - 1 ≠ 0 := ne_of_gt hα_m1_pos
  filter_upwards [hAE.DpH_upper_ae ε hε hε1] with x hDU
  have h := hDU (0 : Fin d → ℝ) 1 one_pos
  have hzero_α1 : ‖(0 : Fin d → ℝ)‖ ^ (hweak.α - 1) = 0 := by
    rw [norm_zero, Real.zero_rpow hα_m1_ne]
  have hone_q : (1 : ℝ) ^ (hweak.β - hweak.β / hweak.α) = 1 := Real.one_rpow _
  rw [hzero_α1, hone_q] at h
  have heq : Cε * (0 + 1 + 1) = 2 * Cε := by ring
  rw [heq] at h
  have h2 : 2 * Cε ≤ Ctil := by rw [hCtil_eq]; linarith
  linarith

/-! ## The AE Eulerian and combined bounds -/

/-- **AE Eulerian half (uniform explicit constant)** — sibling of
`coercivity_eulerian_from_paperHypotheses_uniform`. The constant is
`coercivityIntegrandLowerBoundYoungConstant d (2·C_ε+1) hweak.α hweak.β`. -/
lemma coercivity_eulerian_of_AEData_uniform
    {hweak : HypothesisWeakGrowth (d := d) H DpH} {qε : QEpsFamily d}
    (hAE : HdeltaAEPowerEpsData (H := H) (DpH := DpH) hweak qε)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (Du : Fin d → (Fin d → ℝ) → ℝ) (m : (Fin d → ℝ) → ℝ)
    (hm_pos : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hHam_int : IntegrableOn
        (fun x => coerciveHamIntegrand (Hdelta hweak ε)
                    (DpHepsilonFam hweak qε ε) Du m x) (UnitCube d))
    (hRpow_m_int : IntegrableOn (fun x => m x ^ (hweak.β + 1)) (UnitCube d))
    (hRpow_p_int : IntegrableOn
        (fun x => ‖fun i => Du i x‖ ^ hweak.α) (UnitCube d)) :
    let C_eul : ℝ :=
      coercivityIntegrandLowerBoundYoungConstant d
        (coercivityCdeltaEpsUniform (H := H) (DpH := DpH) hweak ε)
        hweak.α hweak.β
    (1 / C_eul) * (∫ x in UnitCube d, m x ^ (hweak.β + 1))
        + (1 / C_eul) * (∫ x in UnitCube d, ‖fun i => Du i x‖ ^ hweak.α)
        - C_eul
      ≤ ∫ x in UnitCube d, coerciveHamIntegrand (Hdelta hweak ε)
          (DpHepsilonFam hweak qε ε) Du m x := by
  intro C_eul
  have hCtil_pos : 0 < coercivityCdeltaEpsUniform (H := H) (DpH := DpH) hweak ε :=
    coercivityCdeltaEpsUniform_pos (H := H) (DpH := DpH) hweak hε
  have hC_eul_pos : 0 < C_eul :=
    coercivityIntegrandLowerBoundYoungConstant_pos _ _ _ _
  -- Pointwise post-Young bound at the explicit constant.
  have hPointAE :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        0 < m x →
          (1 / C_eul) *
              (m x ^ (hweak.β + 1) + ‖fun i => Du i x‖ ^ hweak.α)
              - C_eul
            ≤ coerciveHamIntegrand (Hdelta hweak ε)
                (DpHepsilonFam hweak qε ε) Du m x := by
    have := coercivity_integrand_lower_bound_young_explicit
      (Hdelta hweak ε) (DpHepsilonFam hweak qε ε)
      hCtil_pos hweak.hα hweak.hβ
      (aeData_lagr_at_uniform hAE hε hε1)
      (aeData_lower_at_uniform hAE hε hε1)
      (aeData_H01_le_at_uniform hAE hε hε1)
      (aeData_DpH01_le_at_uniform hAE hε hε1)
      Du m
    exact this
  -- Drop the `0 < m x` premise using `hm_pos`.
  have hPointAE' :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        (1 / C_eul) *
            (m x ^ (hweak.β + 1) + ‖fun i => Du i x‖ ^ hweak.α)
            - C_eul
          ≤ coerciveHamIntegrand (Hdelta hweak ε)
              (DpHepsilonFam hweak qε ε) Du m x := by
    filter_upwards [hPointAE, hm_pos] with x hx hpos
    exact hx hpos
  -- Integrability of the LHS family.
  have hSum_int : IntegrableOn
      (fun x => m x ^ (hweak.β + 1) + ‖fun i => Du i x‖ ^ hweak.α)
      (UnitCube d) := hRpow_m_int.add hRpow_p_int
  have hSum_smul_int : IntegrableOn
      (fun x =>
        (1 / C_eul) * (m x ^ (hweak.β + 1) + ‖fun i => Du i x‖ ^ hweak.α))
      (UnitCube d) := hSum_int.const_mul _
  have hμ_ne : volume (UnitCube (d := d)) ≠ ⊤ := by
    rw [volume_unitCube]; exact ENNReal.one_ne_top
  have h_const_int : IntegrableOn (fun _ : Fin d → ℝ => (C_eul : ℝ))
      (UnitCube d) := integrableOn_const hμ_ne
  have hLB_int : IntegrableOn
      (fun x =>
        (1 / C_eul) *
            (m x ^ (hweak.β + 1) + ‖fun i => Du i x‖ ^ hweak.α)
            - C_eul)
      (UnitCube d) := hSum_smul_int.sub h_const_int
  exact
    coercivity_integral_lower_bound (C'' := C_eul) (β := hweak.β) (α := hweak.α)
      (Hdelta hweak ε) (DpHepsilonFam hweak qε ε) hC_eul_pos Du m
      hPointAE' hHam_int hLB_int hRpow_m_int hRpow_p_int

/-- **AE combined algebraic bound (uniform explicit constant)** — sibling of
`coercivity_combined_from_paperHypotheses_uniform`. Combines the AE Eulerian
half with the test-pair identity at the same explicit constant `C_eul`. -/
lemma coercivity_combined_of_AEData_uniform
    {γBar ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {hweak : HypothesisWeakGrowth (d := d) H DpH} {qε : QEpsFamily d}
    (hAE : HdeltaAEPowerEpsData (H := H) (DpH := DpH) hweak qε)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (Du : Fin d → (Fin d → ℝ) → ℝ) (m u : (Fin d → ℝ) → ℝ)
    (hm_pos : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hInt_mu : IntegrableOn (fun x =>
        (-(u x) - Hdelta hweak ε x (fun i => Du i x) (m x) + V x) * (m x - 1)
          + m x * (DpHepsilonFam hweak qε ε x (fun i => Du i x) (m x)
                    ⬝ (fun i => Du i x))
          + (m x - 1) * u x) (UnitCube d))
    (hInt_10 : IntegrableOn (fun x =>
        (-(0 : ℝ) - Hdelta hweak ε x (0 : Fin d → ℝ) 1 + V x) * (m x - 1)
          + 1 * (DpHepsilonFam hweak qε ε x (0 : Fin d → ℝ) 1
                  ⬝ (fun i => Du i x))
          + (1 - 1) * u x) (UnitCube d))
    (hHam_int : IntegrableOn
        (fun x => coerciveHamIntegrand (Hdelta hweak ε)
                    (DpHepsilonFam hweak qε ε) Du m x) (UnitCube d))
    (hRpow_m_int : IntegrableOn (fun x => m x ^ (hweak.β + 1)) (UnitCube d))
    (hRpow_p_int : IntegrableOn
        (fun x => ‖fun i => Du i x‖ ^ hweak.α) (UnitCube d)) :
    let C_eul : ℝ :=
      coercivityIntegrandLowerBoundYoungConstant d
        (coercivityCdeltaEpsUniform (H := H) (DpH := DpH) hweak ε)
        hweak.α hweak.β
    (1 / C_eul) * (∫ x in UnitCube d, m x ^ (hweak.β + 1))
        + (1 / C_eul) * (∫ x in UnitCube d, ‖fun i => Du i x‖ ^ hweak.α)
        + ε * (∫ x in UnitCube d,
            vecAbsPowMinusTwo γBar (fun i => Du i x)
                * ((fun i => Du i x) ⬝ (fun i => Du i x))
              + absPowMinusTwo γBar (u x) * (u x * u x))
        - C_eul
      ≤ mfgOperatorEpsPair (V := V) (H := Hdelta hweak ε)
          (DpH := DpHepsilonFam hweak qε ε)
          γBar ε Du m u Du (m - 1) u
        - mfgOperatorEpsPair (V := V) (H := Hdelta hweak ε)
            (DpH := DpHepsilonFam hweak qε ε)
            γBar ε (fun _ _ => 0) (fun _ => 1) (fun _ => 0) Du (m - 1) u := by
  intro C_eul
  -- Step 1: test-pair identity (paper line 947).
  have hTestPair :
      mfgOperatorEpsPair (V := V) (H := Hdelta hweak ε)
          (DpH := DpHepsilonFam hweak qε ε)
          γBar ε Du m u Du (m - 1) u
        - mfgOperatorEpsPair (V := V) (H := Hdelta hweak ε)
            (DpH := DpHepsilonFam hweak qε ε)
            γBar ε (fun _ _ => 0) (fun _ => 1) (fun _ => 0) Du (m - 1) u
      = (∫ x in UnitCube d, coerciveHamIntegrand (Hdelta hweak ε)
            (DpHepsilonFam hweak qε ε) Du m x
          ∂(volume : Measure (Fin d → ℝ)))
        + ε * (∫ x in UnitCube d,
            vecAbsPowMinusTwo γBar (fun i => Du i x)
                * ((fun i => Du i x) ⬝ (fun i => Du i x))
              + absPowMinusTwo γBar (u x) * (u x * u x)
            ∂(volume : Measure (Fin d → ℝ))) :=
    coercive_test_pair_identity V (Hdelta hweak ε) (DpHepsilonFam hweak qε ε)
      γBar ε Du m u hInt_mu hInt_10
  -- Step 2: AE Eulerian half at the explicit constant.
  have hEul :
      (1 / C_eul) * (∫ x in UnitCube d, m x ^ (hweak.β + 1))
          + (1 / C_eul) * (∫ x in UnitCube d, ‖fun i => Du i x‖ ^ hweak.α)
          - C_eul
        ≤ ∫ x in UnitCube d, coerciveHamIntegrand (Hdelta hweak ε)
            (DpHepsilonFam hweak qε ε) Du m x :=
    coercivity_eulerian_of_AEData_uniform hAE hε hε1 Du m
      hm_pos hHam_int hRpow_m_int hRpow_p_int
  -- Step 3: combine.
  linarith [hTestPair, hEul]

/-! ## AE-keyed coercivity integrability residues (D2c-2b-2-i)

The AE siblings of `coercivity_combined_integrability_residues`
(`Coercivity/Integrability.lean:667`) and its `_partial`/`_mfgPair` halves.
They produce the six `IntegrableOn` residues consumed by
`coercivity_combined_of_AEData_uniform` at the paper exponents
`hweak.α` / `hweak.β`, on the `Hdelta hweak ε` / `DpHepsilonFam hweak qε ε`
carrier.

The **easy half** (`_partial_ae`) is exponent-only: it only uses the
`K_Aepsi` Lp memberships of `v`, retyped at `hweak.α`/`hweak.β`. The
**hard half** (`_mfgPair_ae`) takes the two `MFGOpEpsAuxHyps` certificates
(primal at `(DuOf v, mOf v, uOf v)` and the `0 1 0` triple) as INPUTS —
exactly the auxHypsK0 riders the BanachBridge context already supplies via
`mfgOpEpsAuxHyps_HdeltaPos_of_AEData` / `mfgOpEpsAuxHyps_HdeltaK0_of_AEData`
(NOT through `paperSection8_auxHypsK0_of_paperHypotheses`).

-- Adapted from `coercivity_combined_integrability_{partial,mfgPair}_of_paperHypotheses`. -/

/-- Vector-valued `MemLpPer` builder (self-contained inline copy of the
private `coercivityIntegrability.memLpPer_pi_of_coord`): bound the sup-norm
of a vector-valued function by the sum of absolute values, then close under
`MemLp.of_le_mul`. -/
private theorem coercivityAE_memLpPer_pi_of_coord
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

/-- **Partial (3-of-6) AE integrability residues** — sibling of
`coercivity_combined_integrability_partial_of_paperHypotheses`
(`Coercivity/Integrability.lean:142`) at `hweak.α`/`hweak.β`.

Delivers the easy half (`hm_pos`, `(mOf v)^{β+1}`-int, `‖Du‖^α`-int) from the
`K_Aepsi` Lp memberships of `v` only. Carrier-independent — no `H`/`DpH`. -/
theorem coercivity_combined_integrability_partial_ae
    {γBarReal βBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {hweak : HypothesisWeakGrowth (d := d) H DpH}
    (hβBar_eq : βBarReal = hweak.β + 1)
    (hγBar_eq : γBarReal = hweak.α * (hweak.β + 1) / hweak.β)
    (v : XBanach d βBarReal γBarReal)
    (hv : v ∈ K_Aepsi d βBarReal γBarReal) :
    (∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < mOf v x) ∧
    IntegrableOn (fun x => mOf v x ^ (hweak.β + 1)) (UnitCube d) ∧
    IntegrableOn
      (fun x => ‖fun i => DuOf v i x‖ ^ hweak.α) (UnitCube d) := by
  -- Standing positivity facts.
  have hα_pos : 0 < hweak.α := lt_trans Real.zero_lt_one hweak.hα
  have hβ_pos : 0 < hweak.β := hweak.hβ
  have hβ1_pos : 0 < hweak.β + 1 := by linarith
  have hγBarReal_pos : 0 < γBarReal := by
    rw [hγBar_eq]; exact div_pos (mul_pos hα_pos hβ1_pos) hβ_pos
  -- `α ≤ γBar` (in fact `<`): `γBar = α + α/β > α`.
  have hα_le_γBar : hweak.α ≤ γBarReal := by
    rw [hγBar_eq]
    rw [le_div_iff₀ hβ_pos]
    have : hweak.α * (hweak.β + 1) = hweak.α * hweak.β + hweak.α := by ring
    rw [this]
    linarith
  have hα_le_γBar_enn : ENNReal.ofReal hweak.α ≤ ENNReal.ofReal γBarReal :=
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
  have hRpow_m_int : IntegrableOn (fun x => mOf v x ^ (hweak.β + 1)) (UnitCube d) := by
    have hmLp_paper : MemLpPer (d := d) (ENNReal.ofReal (hweak.β + 1)) (mOf v) := by
      rw [← hβBar_eq]; exact hmLp
    have hmemLp : MemLp (mOf v) (ENNReal.ofReal (hweak.β + 1))
        (volume.restrict (UnitCube d)) := hmLp_paper.toMemLp
    have hp_ne_zero : ENNReal.ofReal (hweak.β + 1) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr hβ1_pos).ne'
    have hp_ne_top : ENNReal.ofReal (hweak.β + 1) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hint_norm : Integrable
        (fun x => ‖mOf v x‖ ^ (ENNReal.ofReal (hweak.β + 1)).toReal)
        (volume.restrict (UnitCube d)) :=
      hmemLp.integrable_norm_rpow hp_ne_zero hp_ne_top
    have hp_toReal : (ENNReal.ofReal (hweak.β + 1)).toReal = hweak.β + 1 :=
      ENNReal.toReal_ofReal hβ1_pos.le
    rw [hp_toReal] at hint_norm
    refine hint_norm.congr ?_
    filter_upwards [hm_pos] with x hx
    rw [Real.norm_eq_abs, abs_of_pos hx]
  -- (3) `‖fun i => DuOf v i x‖^α` is integrable on the cube.
  have hRpow_p_int :
      IntegrableOn (fun x => ‖fun i => DuOf v i x‖ ^ hweak.α) (UnitCube d) := by
    have hDuLp_α : ∀ i, MemLpPer (d := d) (ENNReal.ofReal hweak.α) (DuOf v i) := by
      intro i
      exact (hDuLp i).mono_exponent_finite hα_le_γBar_enn hγBar_ne_top
    have hVecLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal hweak.α)
        (fun x : (Fin d → ℝ) => fun i : Fin d => DuOf v i x) :=
      coercivityAE_memLpPer_pi_of_coord (DuOf v) hDuLp_α
    have hα_ne_zero : ENNReal.ofReal hweak.α ≠ 0 :=
      (ENNReal.ofReal_pos.mpr hα_pos).ne'
    have hα_ne_top : ENNReal.ofReal hweak.α ≠ ⊤ := ENNReal.ofReal_ne_top
    have hmemLp : MemLp (fun x : (Fin d → ℝ) => fun i : Fin d => DuOf v i x)
        (ENNReal.ofReal hweak.α) (volume.restrict (UnitCube d)) :=
      hVecLp.toMemLp
    have hint_norm : Integrable
        (fun x => ‖(fun i : Fin d => DuOf v i x)‖ ^
                   (ENNReal.ofReal hweak.α).toReal)
        (volume.restrict (UnitCube d)) :=
      hmemLp.integrable_norm_rpow hα_ne_zero hα_ne_top
    have hα_toReal : (ENNReal.ofReal hweak.α).toReal = hweak.α :=
      ENNReal.toReal_ofReal hα_pos.le
    rw [hα_toReal] at hint_norm
    exact hint_norm
  exact ⟨hm_pos, hRpow_m_int, hRpow_p_int⟩

/-- **The hard half of the AE integrability residues** (`hInt_mu`, `hInt_10`,
`hHam_int`) — sibling of
`coercivity_combined_integrability_mfgPair_of_paperHypotheses`
(`Coercivity/Integrability.lean:256`).

Carrier `Hdelta hweak ε` / `DpHepsilonFam hweak qε ε`. The two
`MFGOpEpsAuxHyps` certificates are taken as INPUTS (the `auxV` at the primal
triple `(DuOf v, mOf v, uOf v)` and `aux10` at `(0, 1, 0)`), so this lemma
never calls `paperSection8_auxHypsK0_of_paperHypotheses`. The three residues
come from `integrable_mfgPair_integrand` plus the `coerciveHamIntegrand`
algebraic congruence, exactly as in the strict mfgPair lemma's final steps. -/
theorem coercivity_combined_integrability_mfgPair_ae
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {hweak : HypothesisWeakGrowth (d := d) H DpH} {qε : QEpsFamily d}
    {ε : ℝ}
    (v : XBanach d βBarReal γBarReal)
    (auxV : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
              V (Hdelta hweak ε) (DpHepsilonFam hweak qε ε)
              (DuOf v) (mOf v) (uOf v))
    (aux10 : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
              V (Hdelta hweak ε) (DpHepsilonFam hweak qε ε)
              (fun (_ : Fin d) (_ : (Fin d → ℝ)) => (0 : ℝ))
              (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ))) :
    IntegrableOn
      (fun x => (-(uOf v x)
                  - Hdelta hweak ε x (fun i => DuOf v i x) (mOf v x) + V x)
                  * (mOf v x - 1)
                + mOf v x * (DpHepsilonFam hweak qε ε x (fun i => DuOf v i x)
                              (mOf v x) ⬝ (fun i => DuOf v i x))
                + (mOf v x - 1) * uOf v x) (UnitCube d) ∧
    IntegrableOn
      (fun x => (-(0 : ℝ) - Hdelta hweak ε x (0 : Fin d → ℝ) 1 + V x)
                  * (mOf v x - 1)
                + 1 * (DpHepsilonFam hweak qε ε x (0 : Fin d → ℝ) 1
                        ⬝ (fun i => DuOf v i x))
                + (1 - 1) * uOf v x) (UnitCube d) ∧
    IntegrableOn
      (fun x => coerciveHamIntegrand (Hdelta hweak ε)
                  (DpHepsilonFam hweak qε ε) (DuOf v) (mOf v) x) (UnitCube d) := by
  -- `MemLpPer` certificates from the Lp components of `v`.
  have huLp : MemLpPer (d := d) (ENNReal.ofReal γBarReal) (uOf v) :=
    memLpPer_of_lpPer (d := d) v.2.1
  have hDuLp : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (DuOf v i) := by
    intro i; exact memLpPer_of_lpPer (d := d) (v.2.2 i)
  -- `MemLpPer βBar (mOf v - 1)`.
  have hmLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal) (mOf v) :=
    memLpPer_of_lpPer (d := d) v.1
  have hOneLp_β : MemLpPer (d := d) (ENNReal.ofReal βBarReal)
        (fun _ : (Fin d → ℝ) => (1 : ℝ)) :=
    MemLp.toMemLpPer (memLp_const (1 : ℝ))
  have hmSub1_Lp : MemLpPer (d := d) (ENNReal.ofReal βBarReal)
        (fun x : (Fin d → ℝ) => mOf v x - 1) := by
    have hsub : MemLp ((mOf v) - (fun _ => (1 : ℝ))) (ENNReal.ofReal βBarReal)
        (volume.restrict (UnitCube d)) :=
      MeasureTheory.MemLp.sub hmLp.toMemLp hOneLp_β.toMemLp
    have heq : ((mOf v) - (fun _ : (Fin d → ℝ) => (1 : ℝ)))
              = (fun x : (Fin d → ℝ) => mOf v x - 1) := by
      funext x; rfl
    rw [heq] at hsub
    exact MemLp.toMemLpPer hsub
  -- (1) `hInt_mu` from `auxV` at the primal triple, test `(m-1, u, Du)`.
  have hInt_mu : IntegrableOn
      (fun x => (-(uOf v x)
                  - Hdelta hweak ε x (fun i => DuOf v i x) (mOf v x) + V x)
                  * (mOf v x - 1)
                + mOf v x * (DpHepsilonFam hweak qε ε x (fun i => DuOf v i x)
                              (mOf v x) ⬝ (fun i => DuOf v i x))
                + (mOf v x - 1) * uOf v x) (UnitCube d) :=
    integrable_mfgPair_integrand
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      auxV hmSub1_Lp huLp hDuLp
  -- (2) `hInt_10` from `aux10` at `(0, 1, 0)`, test `(m-1, u, Du)`.
  have hInt_10 : IntegrableOn
      (fun x => (-(0 : ℝ) - Hdelta hweak ε x (0 : Fin d → ℝ) 1 + V x)
                  * (mOf v x - 1)
                + 1 * (DpHepsilonFam hweak qε ε x (0 : Fin d → ℝ) 1
                        ⬝ (fun i => DuOf v i x))
                + (1 - 1) * uOf v x) (UnitCube d) :=
    integrable_mfgPair_integrand
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      aux10 hmSub1_Lp huLp hDuLp
  -- (3) `hHam_int`: from `hInt_mu - hInt_10 = coerciveHamIntegrand` pointwise.
  have hHam_int : IntegrableOn
      (fun x => coerciveHamIntegrand (Hdelta hweak ε)
                  (DpHepsilonFam hweak qε ε) (DuOf v) (mOf v) x) (UnitCube d) := by
    have hsub : IntegrableOn
        (fun x =>
          ((-(uOf v x)
              - Hdelta hweak ε x (fun i => DuOf v i x) (mOf v x) + V x)
              * (mOf v x - 1)
            + mOf v x * (DpHepsilonFam hweak qε ε x (fun i => DuOf v i x)
                            (mOf v x) ⬝ (fun i => DuOf v i x))
            + (mOf v x - 1) * uOf v x)
          - ((-(0 : ℝ) - Hdelta hweak ε x (0 : Fin d → ℝ) 1 + V x)
              * (mOf v x - 1)
              + 1 * (DpHepsilonFam hweak qε ε x (0 : Fin d → ℝ) 1
                      ⬝ (fun i => DuOf v i x))
              + (1 - 1) * uOf v x))
        (UnitCube d) := hInt_mu.sub hInt_10
    refine hsub.congr ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    unfold coerciveHamIntegrand
    ring
  exact ⟨hInt_mu, hInt_10, hHam_int⟩

/-- **Full (6-of-6) AE integrability residues** — sibling of
`coercivity_combined_integrability_residues`
(`Coercivity/Integrability.lean:667`).

Pure-assembly wrapper merging the easy half
(`coercivity_combined_integrability_partial_ae`) with the hard half
(`coercivity_combined_integrability_mfgPair_ae`) into the exact 6-conjunct
shape consumed by `coercivity_combined_of_AEData_uniform`, on the
`Hdelta hweak ε` / `DpHepsilonFam hweak qε ε` carrier at `hweak.α`/`hweak.β`. -/
theorem coercivity_combined_integrability_residues_ae
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {hweak : HypothesisWeakGrowth (d := d) H DpH} {qε : QEpsFamily d}
    {ε : ℝ}
    (hβBar_eq : βBarReal = hweak.β + 1)
    (hγBar_eq : γBarReal = hweak.α * (hweak.β + 1) / hweak.β)
    (v : XBanach d βBarReal γBarReal)
    (hv : v ∈ K_Aepsi d βBarReal γBarReal)
    (auxV : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
              V (Hdelta hweak ε) (DpHepsilonFam hweak qε ε)
              (DuOf v) (mOf v) (uOf v))
    (aux10 : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
              V (Hdelta hweak ε) (DpHepsilonFam hweak qε ε)
              (fun (_ : Fin d) (_ : (Fin d → ℝ)) => (0 : ℝ))
              (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ))) :
    (∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < mOf v x) ∧
    IntegrableOn
      (fun x => (-(uOf v x)
                  - Hdelta hweak ε x (fun i => DuOf v i x) (mOf v x) + V x)
                  * (mOf v x - 1)
                + mOf v x * (DpHepsilonFam hweak qε ε x (fun i => DuOf v i x)
                              (mOf v x) ⬝ (fun i => DuOf v i x))
                + (mOf v x - 1) * uOf v x) (UnitCube d) ∧
    IntegrableOn
      (fun x => (-(0 : ℝ) - Hdelta hweak ε x (0 : Fin d → ℝ) 1 + V x)
                  * (mOf v x - 1)
                + 1 * (DpHepsilonFam hweak qε ε x (0 : Fin d → ℝ) 1
                        ⬝ (fun i => DuOf v i x))
                + (1 - 1) * uOf v x) (UnitCube d) ∧
    IntegrableOn
      (fun x => coerciveHamIntegrand (Hdelta hweak ε)
                  (DpHepsilonFam hweak qε ε) (DuOf v) (mOf v) x) (UnitCube d) ∧
    IntegrableOn (fun x => mOf v x ^ (hweak.β + 1)) (UnitCube d) ∧
    IntegrableOn
      (fun x => ‖fun i => DuOf v i x‖ ^ hweak.α) (UnitCube d) := by
  obtain ⟨hm_pos, hRpow_m_int, hRpow_p_int⟩ :=
    coercivity_combined_integrability_partial_ae
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      hβBar_eq hγBar_eq v hv
  obtain ⟨hInt_mu, hInt_10, hHam_int⟩ :=
    coercivity_combined_integrability_mfgPair_ae
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      (V := V) v auxV aux10
  exact ⟨hm_pos, hInt_mu, hInt_10, hHam_int, hRpow_m_int, hRpow_p_int⟩

/-! ## AE cobounded gauge wrap (D2c-2b-2-ii)

The AE siblings of the strict `hpow`-keyed XBanach scaled-gauge wrap
(`coercivity_scaled_min_gauge_le_operator_diff_of_paperHypotheses`,
`Coercivity/Integrability.lean:1888`), its cobounded `_eventually`
packaging, and the top-level `paperSection8_coercivity_of_paperHypotheses`
producer (`Coercivity/Integrability.lean:2547`).

The gauge-absorption algebra (Steps 5-10 of the strict lemma) is
`hpow`-FREE and reused verbatim: the four helpers
`coercivity_min_gauge_le_integrated_of_paperHypotheses`,
`gateauxWpIntegrand_integral_eq_positive_form`,
`coercivity_combined_integrability_{percoord_du_pow,euclidean_du_pow_half}`,
and the pure-algebra assembly `coercivity_scaled_min_gauge_absorption_core`
depend only on the Banach pair `v` and the exponents, never on the
Hamiltonian carrier. Only Step 3 (residues) and Step 4 (combined algebraic
bound) are carrier-specific; those route through the AE Layer-2 residues
(`coercivity_combined_integrability_residues_ae`) and the AE Layer-1 combined
bound (`coercivity_combined_of_AEData_uniform`), at the AE constant
`C_eul := coercivityIntegrandLowerBoundYoungConstant d
(coercivityCdeltaEpsUniform hweak ε) hweak.α hweak.β`.

-- Adapted from the `hpow`-keyed wrap in `Coercivity/Integrability.lean`. -/

/-- **AE XBanach pointwise scaled-gauge wrap** (paper `prop:coercAepsi`,
line 982) — sibling of
`coercivity_scaled_min_gauge_le_operator_diff_of_paperHypotheses`
(`Coercivity/Integrability.lean:1888`), on the `Hdelta hweak ε` /
`DpHepsilonFam hweak qε ε` carrier.

The two `MFGOpEpsAuxHyps` certificates (`auxV` at the primal triple, `aux10`
at the `(0,1,0)` reference) are taken as INPUTS, threaded to the AE Layer-2
residues. `C_eul` uses the AE constant `coercivityCdeltaEpsUniform hweak ε`. -/
theorem coercivity_scaled_min_gauge_le_operator_diff_of_AEData
    {γBarReal βBarReal βBarReal' γBarReal' ε : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {hweak : HypothesisWeakGrowth (d := d) H DpH} {qε : QEpsFamily d}
    (hAE : HdeltaAEPowerEpsData (H := H) (DpH := DpH) hweak qε)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hβBar_eq : βBarReal = hweak.β + 1)
    (hγBar_eq : γBarReal = hweak.α * (hweak.β + 1) / hweak.β)
    (hβTop : ENNReal.ofReal γBarReal ≠ ⊤)
    (hβBarTop : ENNReal.ofReal βBarReal ≠ ⊤)
    (hβ_gt1 : 1 < βBarReal) (hγ_gt1 : 1 < γBarReal)
    (hd_pos : 0 < (d : ℝ))
    (v : XBanach d βBarReal γBarReal) (hv : v ∈ K_Aepsi d βBarReal γBarReal)
    (auxV : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
              V (Hdelta hweak ε) (DpHepsilonFam hweak qε ε)
              (DuOf v) (mOf v) (uOf v))
    (aux10 : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
              V (Hdelta hweak ε) (DpHepsilonFam hweak qε ε)
              (fun (_ : Fin d) (_ : (Fin d → ℝ)) => (0 : ℝ))
              (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ))) :
    let κ : ℝ := coercivityGaugeExponent βBarReal γBarReal
    let C_eul : ℝ :=
      coercivityIntegrandLowerBoundYoungConstant d
        (coercivityCdeltaEpsUniform (H := H) (DpH := DpH) hweak ε)
        hweak.α hweak.β
    let lam : ℝ := coercivityScaledGaugeLambda κ C_eul ε d γBarReal
    lam * aepsiCoerciveGauge (βBarReal := βBarReal) (γBarReal := γBarReal)
              κ v - (C_eul + lam / κ)
      ≤ mfgOperatorEpsPair (V := V) (H := Hdelta hweak ε)
          (DpH := DpHepsilonFam hweak qε ε)
          γBarReal ε (DuOf v) (mOf v) (uOf v)
            (DuOf v) (mOf v - 1) (uOf v)
        - mfgOperatorEpsPair (V := V) (H := Hdelta hweak ε)
            (DpH := DpHepsilonFam hweak qε ε)
            γBarReal ε (fun _ _ => 0) (fun _ => 1) (fun _ => 0)
            (DuOf v) (mOf v - 1) (uOf v) := by
  intro κ C_eul lam
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
    coercivityScaledGaugeLambda_pos hκ_pos hC_eul_pos hε hd_pos hγBar_nn
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
  -- Step 3: integrability residues (AE Layer-2).
  obtain ⟨hm_pos, hInt_mu, hInt_10, hHam_int, hRpow_m_int, hRpow_p_int⟩ :=
    coercivity_combined_integrability_residues_ae
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      (V := V) hβBar_eq hγBar_eq v hv auxV aux10
  -- Step 4: combined algebraic bound at the AE constant (AE Layer-1).
  have hComb_raw :
      (1 / C_eul) * (∫ x in UnitCube d, mOf v x ^ (hweak.β + 1))
          + (1 / C_eul) * (∫ x in UnitCube d, ‖fun i => DuOf v i x‖ ^ hweak.α)
          + ε * (∫ x in UnitCube d,
              vecAbsPowMinusTwo γBarReal (fun i => DuOf v i x)
                  * ((fun i => DuOf v i x) ⬝ (fun i => DuOf v i x))
                + absPowMinusTwo γBarReal (uOf v x) * (uOf v x * uOf v x))
          - C_eul
        ≤ mfgOperatorEpsPair (V := V) (H := Hdelta hweak ε)
            (DpH := DpHepsilonFam hweak qε ε)
            γBarReal ε (DuOf v) (mOf v) (uOf v) (DuOf v) (mOf v - 1) (uOf v)
          - mfgOperatorEpsPair (V := V) (H := Hdelta hweak ε)
              (DpH := DpHepsilonFam hweak qε ε)
              γBarReal ε (fun _ _ => 0) (fun _ => 1) (fun _ => 0)
              (DuOf v) (mOf v - 1) (uOf v) :=
    coercivity_combined_of_AEData_uniform (d := d)
      (γBar := γBarReal) (ε := ε) (V := V)
      hAE hε hε1 (DuOf v) (mOf v) (uOf v)
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
  set Im : ℝ := ∫ x in UnitCube d, mOf v x ^ (hweak.β + 1) with hIm_def
  set IpAlpha : ℝ := ∫ x in UnitCube d, ‖fun i => DuOf v i x‖ ^ hweak.α
    with hIpAlpha_def
  set IDuDot : ℝ := ∫ x in UnitCube d,
        ((fun i => DuOf v i x) ⬝ (fun i => DuOf v i x)) ^ (γBarReal / 2)
    with hIDuDot_def
  set Iu : ℝ := ∫ x in UnitCube d, |uOf v x| ^ γBarReal with hIu_def
  set IDu_sum : ℝ := ∑ i, ∫ x in UnitCube d, |DuOf v i x| ^ γBarReal
    with hIDu_sum_def
  -- Integrability of Iu and IDuDot terms (for sum splitting).
  have hIu_int : IntegrableOn (fun x => |uOf v x| ^ γBarReal) (UnitCube d) := by
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
  -- Step 5 cont.: rewrite the integral of the sum as sum of integrals.
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
        ≤ mfgOperatorEpsPair (V := V) (H := Hdelta hweak ε)
            (DpH := DpHepsilonFam hweak qε ε)
            γBarReal ε (DuOf v) (mOf v) (uOf v) (DuOf v) (mOf v - 1) (uOf v)
          - mfgOperatorEpsPair (V := V) (H := Hdelta hweak ε)
              (DpH := DpHepsilonFam hweak qε ε)
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
  have hIm_abs_eq : (∫ x in UnitCube d, |mOf v x| ^ βBarReal) = Im := by
    change (∫ x in UnitCube d, |mOf v x| ^ βBarReal)
          = ∫ x in UnitCube d, mOf v x ^ (hweak.β + 1)
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hm_pos] with x hxpos
    have h1 : |mOf v x| ^ βBarReal = mOf v x ^ βBarReal := by
      rw [abs_of_pos hxpos]
    have h2 : mOf v x ^ βBarReal = mOf v x ^ (hweak.β + 1) := by
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
  have hGauge_le :
      lam * aepsiCoerciveGauge (βBarReal := βBarReal) (γBarReal := γBarReal)
              κ v
        ≤ lam * (1 + Im + (((d : ℝ) + 1) ^ γBarReal) * (Iu + IDu_sum)) / κ := by
    have hmul := mul_le_mul_of_nonneg_left hGauge_bound hlam_pos.le
    change lam * aepsiCoerciveGauge (βBarReal := βBarReal) (γBarReal := γBarReal)
              (coercivityGaugeExponent βBarReal γBarReal) v
        ≤ lam * (1 + Im + (((d : ℝ) + 1) ^ γBarReal) * (Iu + IDu_sum))
            / coercivityGaugeExponent βBarReal γBarReal
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
      hκ_pos hC_eul_pos hε hd_pos hγBar_nn
  have hlam_dim : lam * ((d : ℝ) * (((d : ℝ) + 1) ^ γBarReal)) / κ ≤ ε :=
    coercivityScaledGaugeLambda_dim_full_mul_le_eps
      hκ_pos hC_eul_pos hε hd_pos hγBar_nn
  have hlam_u : lam * (((d : ℝ) + 1) ^ γBarReal) / κ ≤ ε :=
    coercivityScaledGaugeLambda_u_le_eps
      hκ_pos hC_eul_pos hε hd_ge1 hγBar_nn
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
    (opDiff := mfgOperatorEpsPair (V := V) (H := Hdelta hweak ε)
                  (DpH := DpHepsilonFam hweak qε ε)
                  γBarReal ε (DuOf v) (mOf v) (uOf v)
                    (DuOf v) (mOf v - 1) (uOf v)
                - mfgOperatorEpsPair (V := V) (H := Hdelta hweak ε)
                    (DpH := DpHepsilonFam hweak qε ε)
                    γBarReal ε (fun _ _ => 0) (fun _ => 1) (fun _ => 0)
                    (DuOf v) (mOf v - 1) (uOf v))
    (γBar := γBarReal) (d := d)
    hκ_pos hC_eul_pos hlam_pos hlam_inv hlam_dim hlam_u hd1pow_pos
    hIm_nn hIu_nn hIDu_sum_nn hIDuDot_nn hIpAlpha_nn
    hGauge_le hComb hBridge

/-- **AE cobounded packaging** — sibling of
`coercivity_scaled_min_gauge_le_operator_diff_eventually`
(`Coercivity/Integrability.lean:2300`). Lifts the per-`v` AE wrap to the
cobounded ⊓ principal-`K_Aepsi` filter. The K_Aepsi-indexed `auxHypsK`
rider supplies the primal `auxV` per `v`; the single `aux10` certificate at
the `(0,1,0)` reference is taken as a separate input. -/
theorem coercivity_scaled_min_gauge_le_operator_diff_eventually_ae
    {γBarReal βBarReal βBarReal' γBarReal' ε : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {hweak : HypothesisWeakGrowth (d := d) H DpH} {qε : QEpsFamily d}
    (hAE : HdeltaAEPowerEpsData (H := H) (DpH := DpH) hweak qε)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hβBar_eq : βBarReal = hweak.β + 1)
    (hγBar_eq : γBarReal = hweak.α * (hweak.β + 1) / hweak.β)
    (hβTop : ENNReal.ofReal γBarReal ≠ ⊤)
    (hβBarTop : ENNReal.ofReal βBarReal ≠ ⊤)
    (hβ_gt1 : 1 < βBarReal) (hγ_gt1 : 1 < γBarReal)
    (hd_pos : 0 < (d : ℝ))
    (auxHypsK : ∀ q ∈ K_Aepsi d βBarReal γBarReal,
      MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
        V (Hdelta hweak ε) (DpHepsilonFam hweak qε ε)
        (DuOf q) (mOf q) (uOf q))
    (aux10 : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
              V (Hdelta hweak ε) (DpHepsilonFam hweak qε ε)
              (fun (_ : Fin d) (_ : (Fin d → ℝ)) => (0 : ℝ))
              (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ))) :
    ∃ lam Ccoerc : ℝ, 0 < lam ∧
      ∀ᶠ v in (Bornology.cobounded (XBanach d βBarReal γBarReal)
                  ⊓ Filter.principal (K_Aepsi d βBarReal γBarReal)),
        lam * aepsiCoerciveGauge (βBarReal := βBarReal) (γBarReal := γBarReal)
                  (coercivityGaugeExponent βBarReal γBarReal) v - Ccoerc
          ≤ mfgOperatorEpsPair (V := V) (H := Hdelta hweak ε)
              (DpH := DpHepsilonFam hweak qε ε)
              γBarReal ε (DuOf v) (mOf v) (uOf v)
                (DuOf v) (mOf v - 1) (uOf v)
            - mfgOperatorEpsPair (V := V) (H := Hdelta hweak ε)
                (DpH := DpHepsilonFam hweak qε ε)
                γBarReal ε (fun _ _ => 0) (fun _ => 1) (fun _ => 0)
                (DuOf v) (mOf v - 1) (uOf v) := by
  set κ : ℝ := coercivityGaugeExponent βBarReal γBarReal with hκ_def
  set C_eul : ℝ :=
    coercivityIntegrandLowerBoundYoungConstant d
      (coercivityCdeltaEpsUniform (H := H) (DpH := DpH) hweak ε)
      hweak.α hweak.β with hC_def
  set lam : ℝ := coercivityScaledGaugeLambda κ C_eul ε d γBarReal with hlam_def
  have hβPos : 0 < βBarReal := lt_trans zero_lt_one hβ_gt1
  have hγPos : 0 < γBarReal := lt_trans zero_lt_one hγ_gt1
  have hκ_pos : 0 < κ := by
    change 0 < coercivityGaugeExponent βBarReal γBarReal
    unfold coercivityGaugeExponent
    exact lt_of_lt_of_le zero_lt_one (le_min hβ_gt1.le hγ_gt1.le)
  have hC_eul_pos : 0 < C_eul :=
    coercivityIntegrandLowerBoundYoungConstant_pos _ _ _ _
  have hlam_pos : 0 < lam :=
    coercivityScaledGaugeLambda_pos hκ_pos hC_eul_pos hε hd_pos hγPos.le
  refine ⟨lam, C_eul + lam / κ, hlam_pos, ?_⟩
  rw [Filter.eventually_inf_principal]
  refine Filter.Eventually.of_forall ?_
  intro v hv
  have h_pt :=
    coercivity_scaled_min_gauge_le_operator_diff_of_AEData
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal') (ε := ε)
      (V := V) hAE hε hε1 hβBar_eq hγBar_eq hβTop hβBarTop
      hβ_gt1 hγ_gt1 hd_pos v hv (auxHypsK v hv) aux10
  exact h_pt

/-- **Top-level AE coercivity producer** — sibling of
`paperSection8_coercivity_of_paperHypotheses`
(`Coercivity/Integrability.lean:2547`). Surfaces the paper-line-982
conclusion on the `Hdelta hweak ε` / `DpHepsilonFam hweak qε ε` carrier as a
single existential `∃ lam Ccoerc, 0 < lam ∧ ∀ᶠ v, …`, the shape the BanachBridge
context builder's `hbound_residue` field consumes. Output gauge exponent is
`coercivityGaugeExponent βBarReal γBarReal = min β̄ γ̄`. -/
theorem paperSection8_coercivity_of_AEData
    {γBarReal βBarReal βBarReal' γBarReal' ε : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {hweak : HypothesisWeakGrowth (d := d) H DpH} {qε : QEpsFamily d}
    (hAE : HdeltaAEPowerEpsData (H := H) (DpH := DpH) hweak qε)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hβBar_eq : βBarReal = hweak.β + 1)
    (hγBar_eq : γBarReal = hweak.α * (hweak.β + 1) / hweak.β)
    (hβTop : ENNReal.ofReal γBarReal ≠ ⊤)
    (hβBarTop : ENNReal.ofReal βBarReal ≠ ⊤)
    (hβ_gt1 : 1 < βBarReal) (hγ_gt1 : 1 < γBarReal)
    (hd_pos : 0 < (d : ℝ))
    (auxHypsK : ∀ q ∈ K_Aepsi d βBarReal γBarReal,
      MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
        V (Hdelta hweak ε) (DpHepsilonFam hweak qε ε)
        (DuOf q) (mOf q) (uOf q))
    (aux10 : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
              V (Hdelta hweak ε) (DpHepsilonFam hweak qε ε)
              (fun (_ : Fin d) (_ : (Fin d → ℝ)) => (0 : ℝ))
              (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ))) :
    ∃ lam Ccoerc : ℝ, 0 < lam ∧
      ∀ᶠ v in (Bornology.cobounded (XBanach d βBarReal γBarReal)
                  ⊓ Filter.principal (K_Aepsi d βBarReal γBarReal)),
        lam * aepsiCoerciveGauge (βBarReal := βBarReal) (γBarReal := γBarReal)
                  (coercivityGaugeExponent βBarReal γBarReal) v - Ccoerc
          ≤ mfgOperatorEpsPair (V := V) (H := Hdelta hweak ε)
              (DpH := DpHepsilonFam hweak qε ε)
              γBarReal ε (DuOf v) (mOf v) (uOf v)
                (DuOf v) (mOf v - 1) (uOf v)
            - mfgOperatorEpsPair (V := V) (H := Hdelta hweak ε)
                (DpH := DpHepsilonFam hweak qε ε)
                γBarReal ε (fun _ _ => 0) (fun _ => 1) (fun _ => 0)
                (DuOf v) (mOf v - 1) (uOf v) :=
  coercivity_scaled_min_gauge_le_operator_diff_eventually_ae
    (γBarReal := γBarReal) (βBarReal := βBarReal)
    (βBarReal' := βBarReal') (γBarReal' := γBarReal') (ε := ε)
    (V := V) hAE hε hε1 hβBar_eq hγBar_eq hβTop hβBarTop
    hβ_gt1 hγ_gt1 hd_pos auxHypsK aux10

end SimplePower
end Theorems
end StationaryMFG
