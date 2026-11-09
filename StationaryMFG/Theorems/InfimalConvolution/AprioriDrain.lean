module

/-
Copyright (c) 2026 Stationary MFG project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import StationaryMFG.Theorems.InfimalConvolution.StrongIsStrong
public import StationaryMFG.Theorems.InfimalConvolution.Existence
public import StationaryMFG.Theorems.InfimalConvolution.Apriori
public import StationaryMFG.Theorems.SimplePower.Banach.Operator
public import StationaryMFG.Hamiltonian.Estimates
public import StationaryMFG.Periodic.DensityApprox

@[expose] public section

/-!
# T3 a-priori drain (A2a): HJB-clause producer from the strong-VI family

This module is part of the Phase-7 public-signature drain of the
weak-growth theorem `paper:thm:main-weak.power.growth`. It supplies the
`hHJB` input to the a-priori estimate `apriori_weak_power_growth`
(`InfimalConvolution/Apriori.lean`, line 102) from the bare-function
strong-VI predicate `IsStrongVI_Aepsi` produced by the A1d family
producer (`InfimalConvolution/Existence.lean`, line 126).

## Paper content

Paper `lem:strong.is.strong.delta`, item (a)
(`Source/FGU-monotone_revised.tex`, line 1858–1866):

> Let `0 < ε ≤ 1` and `(m, u) ∈ L^{β̄}(𝕋^d; ℝ⁺₀) × W^{1,γ̄}(𝕋^d)`
> satisfy the strong variational inequality
> `⟨A_ε[m,u], (μ−m, υ−u)⟩ ≥ 0` for all `(μ, υ)` in the same space. Then
> `u + H^ε(x, Du, m) − V(x) ≤ 0` a.e. in `𝕋^d`.

## Bridge architecture

The A1d predicate `IsStrongVI_Aepsi` records the inequality in its
**Minty / operator-at-test** form: the regularised pairing
`mfgOperatorEpsPair γBar ε Dυ μ υ (Dυ−Du) (μ−m) (υ−u)` is non-negative,
i.e. the operator `A_ε` is probed at the *test point* `(Dυ, μ, υ)` with
direction `(μ−m, υ−u, Dυ−Du)`. The Phase-6 HJB wrapper
`Hdelta_strong_HJB_le` (`InfimalConvolution/StrongIsStrong.lean`)
instead consumes the **strong / operator-at-solution** set-form
`StrongVI_setForm`, where `A_ε` is probed at the *solution* `(Du, m, u)`
against the set-indicator test `(1_S, 0, 0)`.

The Minty→strong upgrade is the strict-positive perturbation
`μ_n := m + (1/(n+1)) · 1_S`, `n → ∞` argument: instantiate the Minty
inequality at the strictly-positive density `μ_n`, factor the scalar
`1/(n+1) > 0` out of the test triple, and pass to the limit. This is the
exact argument already formalised for the simple-power (T2) theorem in
`StationaryMFG.Theorems.SimplePower.Banach.strongVI_setForm_of_hVIeps_set`
(`Banach/RegularizedSequence.lean`, line 26353), whose `RegularizedBareSolution.hVIeps_set`
field is the same Minty predicate as `IsStrongVI_Aepsi`. We re-derive the
bridge here directly against `IsStrongVI_Aepsi`, then chain
`Hdelta_strong_HJB_le`.

The operator-continuity input `hCont` (continuity of the pairing along
`μ_n → m`) and the indicator-`Lᵝ` input `hIndicMemLp` are the same
authorised CONVENTIONS §8 / finite-measure inputs consumed by the T2
producer; they are NOT new oracles. The residual integrability `hRes`
is the §1b standing-regularity input already required by
`Hdelta_strong_HJB_le`.

## Deliverables

* `strongVI_setForm_of_IsStrongVI_Aepsi` — Minty→strong-set bridge for
  `IsStrongVI_Aepsi`.
* `hHJB_of_IsStrongVI_Aepsi` — single-triple HJB clause, chaining the
  bridge with `Hdelta_strong_HJB_le`.
* `hHJB_of_strongVI_family` — family-level (`∀ ε`) HJB-clause producer.

## Paper reference

`Source/FGU-monotone_revised.tex`, line 1858 (`lem:strong.is.strong.delta`)
and line 1881 (`thm:apriori-weak.power.growth`).
-/

noncomputable section

namespace StationaryMFG
namespace Theorems
namespace InfimalConvolution

open MeasureTheory Set Filter
open StationaryMFG.Periodic
open StationaryMFG.Hamiltonian
open StationaryMFG.InfimalConvolution
open StationaryMFG.Solutions.MFG
open StationaryMFG.Theorems.SimplePower
open StationaryMFG.Theorems.SimplePower.Banach
open scoped ENNReal NNReal Topology

variable {d : ℕ}

/-! ## Minty → strong-set-form bridge for `IsStrongVI_Aepsi` -/

/-- **Minty→strong bridge** for the bare predicate `IsStrongVI_Aepsi`.

From the Minty-form strong VI `IsStrongVI_Aepsi` (operator probed at the
test point), the membership data of the base pair `(m, u, Du)`, the
indicator-`Lᵝ` input `hIndicMemLp`, and the authorised CONVENTIONS §8
operator-continuity input `hCont` along the strict-positive perturbation
`μ_n := m + (1/(n+1)) · 1_S`, derive the strong/operator-at-solution
set-form `StrongVI_setForm V H DpH γBar ε Du m u`.

The proof mirrors
`StationaryMFG.Theorems.SimplePower.Banach.strongVI_setForm_of_hVIeps_set`
line-for-line, substituting `IsStrongVI_Aepsi` (invoked at `μ := ρ_n`)
for the `RegularizedBareSolution.hVIeps_set` field.

-- Adapted from
-- `SimplePower.Banach.strongVI_setForm_of_hVIeps_set`
-- (the simple-power / T2 Minty bridge), re-derived against the
-- formula-package-independent T3 predicate `IsStrongVI_Aepsi`. -/
theorem strongVI_setForm_of_IsStrongVI_Aepsi
    {bb gb : ℝ≥0∞}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBar ε : ℝ}
    {m u : (Fin d → ℝ) → ℝ} {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hVI : IsStrongVI_Aepsi bb gb V H DpH γBar ε m u Du)
    (hmNonneg : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hmLp : MemLpPer bb m)
    (huSob : MemSobolevPer gb u)
    (hDuLp : ∀ i, MemLpPer gb (Du i))
    (hWeak : ∀ i, HasWeakDerivPer i u (Du i))
    (hIndicMemLp :
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (volume.restrict (UnitCube d)) S < ∞ →
        MemLpPer bb (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ))))
    (hCont :
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (volume.restrict (UnitCube d)) S < ∞ →
        Filter.Tendsto
          (fun n : ℕ =>
            mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBar ε
              Du
              (fun x => m x + (1 / ((n : ℝ) + 1)) *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              u
              (fun _ _ => (0 : ℝ))
              (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)))
              (fun _ => (0 : ℝ)))
          Filter.atTop
          (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                γBar ε
                Du m u
                (fun _ _ => (0 : ℝ))
                (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)))
                (fun _ => (0 : ℝ))))) :
    StrongVI_setForm V H DpH γBar ε Du m u := by
  classical
  intro S hS_meas hS_fin
  set f : (Fin d → ℝ) → ℝ :=
    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) with hf_def
  -- Per-`n` step: nonnegativity of the pairing at the perturbed density.
  have hStep :
      ∀ n : ℕ,
        0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBar ε
              Du
              (fun x => m x + (1 / ((n : ℝ) + 1)) * f x)
              u
              (fun _ _ => (0 : ℝ))
              f
              (fun _ => (0 : ℝ)) := by
    intro n
    set tn : ℝ := 1 / ((n : ℝ) + 1) with htn_def
    have htn_pos : (0 : ℝ) < tn := by
      have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      exact div_pos one_pos hpos
    have hf_nn : ∀ x, 0 ≤ f x := by
      intro x
      by_cases hxS : x ∈ S
      · simp [hf_def, Set.indicator_of_mem hxS]
      · simp [hf_def, Set.indicator_of_notMem hxS]
    set ρ : (Fin d → ℝ) → ℝ := fun x => m x + tn * f x with hρ_def
    -- `0 ≤ ρ` a.e. on the cube.
    have hρ_nn :
        ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ ρ x := by
      filter_upwards [hmNonneg] with x hxm
      have hsmul_nn : 0 ≤ tn * f x := mul_nonneg htn_pos.le (hf_nn x)
      change 0 ≤ m x + tn * f x
      linarith
    -- `MemLpPer bb ρ`.
    have hf_memLp : MemLpPer bb f := hIndicMemLp S hS_meas hS_fin
    have htn_f_memLp : MemLpPer bb (fun x => tn * f x) := by
      have h := MemLpPer.const_smul (c := tn) hf_memLp
      have heq : (tn • f : (Fin d → ℝ) → ℝ) = fun x => tn * f x := by
        funext x
        change tn • f x = tn * f x
        simp [smul_eq_mul]
      rw [heq] at h
      exact h
    have hρ_memLp : MemLpPer bb ρ := by
      have h := MemLpPer.add hmLp htn_f_memLp
      have heq : (m + (fun x => tn * f x) : (Fin d → ℝ) → ℝ) = ρ := by
        funext x; simp [hρ_def]
      rw [heq] at h
      exact h
    -- The Minty-VI field invocation at `μ := ρ`, `υ := u`, `Dυ := Du`.
    have hVIρ := hVI ρ u Du hρ_nn hρ_memLp huSob hDuLp hWeak
    -- `hVIρ : 0 ≤ mfgOperatorEpsPair γBar ε Du ρ u (fun i x => Du i x - Du i x)
    --              (fun x => ρ x - m x) (fun x => u x - u x)`.
    -- Step 1: rewrite the test triple `(0, ρ - m, 0)` via `_congr_ae`.
    have hDν_ae : ∀ i,
        (fun x => Du i x - Du i x)
          =ᵐ[volume.restrict (UnitCube d)]
        (fun _ : Fin d → ℝ => (0 : ℝ)) := by
      intro i
      refine Filter.Eventually.of_forall ?_
      intro x; simp
    have hη_ae :
        (fun x => ρ x - m x)
          =ᵐ[volume.restrict (UnitCube d)]
        (fun x => tn * f x) := by
      refine Filter.Eventually.of_forall ?_
      intro x
      change ρ x - m x = tn * f x
      simp [hρ_def]
    have hν_ae :
        (fun x => u x - u x)
          =ᵐ[volume.restrict (UnitCube d)]
        (fun _ : Fin d → ℝ => (0 : ℝ)) := by
      refine Filter.Eventually.of_forall ?_
      intro x; simp
    have hcongr := mfgOperatorEpsPair_congr_ae
      (V := V) (H := H) (DpH := DpH)
      γBar ε
      Du ρ u
      (fun i x => Du i x - Du i x)
      (fun (_ : Fin d) (_ : Fin d → ℝ) => (0 : ℝ))
      (fun x => ρ x - m x)
      (fun x => tn * f x)
      (fun x => u x - u x)
      (fun _ : Fin d → ℝ => (0 : ℝ))
      hDν_ae hη_ae hν_ae
    rw [hcongr] at hVIρ
    -- Step 2: factor `tn` out of the test triple via `_test_smul`.
    have hsmul := mfgOperatorEpsPair_test_smul
      (V := V) (H := H) (DpH := DpH)
      γBar ε
      Du ρ u
      tn
      (fun (_ : Fin d) (_ : Fin d → ℝ) => (0 : ℝ))
      f
      (fun _ : Fin d → ℝ => (0 : ℝ))
    have hDν_smul_eq :
        (fun i : Fin d => tn • ((fun (_ : Fin d) (_ : Fin d → ℝ) => (0 : ℝ)) i))
          = (fun (_ : Fin d) (_ : Fin d → ℝ) => (0 : ℝ)) := by
      funext i; funext x
      change tn • (0 : ℝ) = (0 : ℝ)
      simp
    have hη_smul_eq :
        (tn • f : (Fin d → ℝ) → ℝ) = fun x => tn * f x := by
      funext x
      change tn • f x = tn * f x
      simp [smul_eq_mul]
    have hν_smul_eq :
        (tn • (fun _ : Fin d → ℝ => (0 : ℝ)) : (Fin d → ℝ) → ℝ)
          = (fun _ : Fin d → ℝ => (0 : ℝ)) := by
      funext x
      change tn • (0 : ℝ) = (0 : ℝ)
      simp
    rw [hDν_smul_eq, hη_smul_eq, hν_smul_eq] at hsmul
    rw [hsmul] at hVIρ
    -- `hVIρ : 0 ≤ tn * mfgOperatorEpsPair … Du ρ u 0 f 0`, with `tn > 0`.
    have hVI' :
        0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBar ε
              Du ρ u
              (fun _ _ => (0 : ℝ))
              f
              (fun _ => (0 : ℝ)) :=
      (mul_nonneg_iff_of_pos_left htn_pos).mp hVIρ
    -- `ρ` is exactly `fun x => m x + tn * f x`.
    exact hVI'
  -- Pass `n → ∞` via `hCont`.
  exact ge_of_tendsto' (hCont S hS_meas hS_fin) hStep

/-! ## Signed Minty→strong bridge (D6c-1)

The signed companion of `strongVI_setForm_of_IsStrongVI_Aepsi`. It supplies
the `StrongVI_setForm_signed` input consumed by the part-(b) HJB-on-positivity
wrapper `Hdelta_strong_HJB_eq_on_pos` (`InfimalConvolution/StrongIsStrong.lean`,
line 133), which in turn yields the pointwise a.e. equality
`(u + H^ε − V) · m = 0`. Integrating that equality (D6c-1) gives the integrated
HJB-on-positivity half of the §1b identity `eq:appositiveum`.

The bridge is the **signed multiplicative** Minty perturbation
`ρ_n := m · (1 + (1/(n+1)) · σ · 1_S)` (in place of the additive
`m + (1/(n+1)) · 1_S` used for the unsigned set form): for `σ = ±1` and
`1/(n+1) ≤ 1`, the density `ρ_n ≥ 0` a.e. (`m ≥ 0`, `0 ≤ 1_S ≤ 1`), so it is an
admissible Minty test density. Instantiate the Minty inequality at `μ := ρ_n`,
factor the scalar `1/(n+1) > 0`, and pass to the limit via the operator-continuity
input `hCont` (the signed companion of the unsigned `hCont`). -/
theorem strongVI_setFormSigned_of_IsStrongVI_Aepsi
    {bb gb : ℝ≥0∞}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBar ε : ℝ}
    {m u : (Fin d → ℝ) → ℝ} {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hVI : IsStrongVI_Aepsi bb gb V H DpH γBar ε m u Du)
    (hmNonneg : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hmLp : MemLpPer bb m)
    (huSob : MemSobolevPer gb u)
    (hDuLp : ∀ i, MemLpPer gb (Du i))
    (hWeak : ∀ i, HasWeakDerivPer i u (Du i))
    (hCont :
      ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (volume.restrict (UnitCube d)) S < ∞ →
        Filter.Tendsto
          (fun n : ℕ =>
            mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBar ε
              Du
              (fun x => m x + (1 / ((n : ℝ) + 1)) *
                          (σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
              u
              (fun _ _ => (0 : ℝ))
              (fun x => σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              (fun _ => (0 : ℝ)))
          Filter.atTop
          (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                γBar ε
                Du m u
                (fun _ _ => (0 : ℝ))
                (fun x => σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                (fun _ => (0 : ℝ))))) :
    StrongVI_setForm_signed V H DpH γBar ε Du m u := by
  classical
  intro σ hσ S hS_meas hS_fin
  -- The signed test direction `f := σ · m · 1_S`.
  set ind : (Fin d → ℝ) → ℝ :=
    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) with hind_def
  set f : (Fin d → ℝ) → ℝ := fun x => σ * m x * ind x with hf_def
  -- `0 ≤ 1_S ≤ 1` and `|σ| = 1`.
  have hσ' : σ = 1 ∨ σ = -1 := hσ
  have hind_le : ∀ x, ind x ≤ 1 := by
    intro x
    by_cases hxS : x ∈ S
    · simp [hind_def, Set.indicator_of_mem hxS]
    · simp [hind_def, Set.indicator_of_notMem hxS]
  have hind_nn : ∀ x, 0 ≤ ind x := by
    intro x
    by_cases hxS : x ∈ S
    · simp [hind_def, Set.indicator_of_mem hxS]
    · simp [hind_def, Set.indicator_of_notMem hxS]
  -- `MemLpPer bb f`.
  have hf_memLp : MemLpPer bb f := by
    have hσm : MemLpPer bb (fun x => σ * m x) := by
      have h := MemLpPer.const_smul (c := σ) hmLp
      have heq : (σ • m : (Fin d → ℝ) → ℝ) = fun x => σ * m x := by
        funext x; change σ • m x = σ * m x; simp [smul_eq_mul]
      rwa [heq] at h
    -- `S.indicator (σ·m) =ᵐ f`.
    have hindic : MemLpPer bb (S.indicator (fun x => σ * m x)) :=
      MemLp.toMemLpPer (MemLp.indicator (μ := volume.restrict (UnitCube d)) hS_meas.nullMeasurableSet hσm.toMemLp)
    apply MemLp.toMemLpPer
    refine MemLp.ae_eq (μ := volume.restrict (UnitCube d)) ?_ hindic.toMemLp
    refine Filter.Eventually.of_forall ?_
    intro x
    by_cases hxS : x ∈ S
    · simp [hf_def, hind_def, Set.indicator_of_mem hxS]
    · simp [hf_def, hind_def, Set.indicator_of_notMem hxS]
  -- Per-`n` non-negativity at the perturbed density.
  have hStep :
      ∀ n : ℕ,
        0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBar ε
              Du
              (fun x => m x + (1 / ((n : ℝ) + 1)) * f x)
              u
              (fun _ _ => (0 : ℝ))
              f
              (fun _ => (0 : ℝ)) := by
    intro n
    set tn : ℝ := 1 / ((n : ℝ) + 1) with htn_def
    have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have htn_pos : (0 : ℝ) < tn := div_pos one_pos hn1_pos
    have htn_le_one : tn ≤ 1 := by
      rw [htn_def, div_le_one hn1_pos]
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    set ρ : (Fin d → ℝ) → ℝ := fun x => m x + tn * f x with hρ_def
    -- `0 ≤ ρ` a.e. on the cube: `ρ = m · (1 + tn·σ·1_S) ≥ 0`.
    have hρ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ ρ x := by
      filter_upwards [hmNonneg] with x hxm
      change 0 ≤ m x + tn * f x
      have hfactor : m x + tn * f x = m x * (1 + tn * σ * ind x) := by
        rw [hf_def]; ring
      rw [hfactor]
      refine mul_nonneg hxm ?_
      -- `1 + tn·σ·1_S ≥ 0`.
      rcases hσ' with rfl | rfl
      · have : 0 ≤ tn * 1 * ind x :=
          mul_nonneg (mul_nonneg htn_pos.le (by norm_num)) (hind_nn x)
        linarith
      · -- `1 - tn·1_S ≥ 0` since `tn ≤ 1` and `1_S ≤ 1`.
        have hle : tn * ind x ≤ 1 :=
          le_trans (by nlinarith [hind_le x, hind_nn x, htn_pos.le, htn_le_one])
            (le_refl (1 : ℝ))
        have : tn * (-1 : ℝ) * ind x = -(tn * ind x) := by ring
        rw [this]; linarith
    -- `MemLpPer bb ρ`.
    have htn_f_memLp : MemLpPer bb (fun x => tn * f x) := by
      have h := MemLpPer.const_smul (c := tn) hf_memLp
      have heq : (tn • f : (Fin d → ℝ) → ℝ) = fun x => tn * f x := by
        funext x; change tn • f x = tn * f x; simp [smul_eq_mul]
      rwa [heq] at h
    have hρ_memLp : MemLpPer bb ρ := by
      have h := MemLpPer.add hmLp htn_f_memLp
      have heq : (m + (fun x => tn * f x) : (Fin d → ℝ) → ℝ) = ρ := by
        funext x; simp [hρ_def]
      rwa [heq] at h
    -- Minty-VI field at `μ := ρ`, `υ := u`, `Dυ := Du`.
    have hVIρ := hVI ρ u Du hρ_nn hρ_memLp huSob hDuLp hWeak
    -- Rewrite the test triple `(Du - Du, ρ - m, u - u)` as `(0, tn·f, 0)`.
    have hDν_ae : ∀ i,
        (fun x => Du i x - Du i x)
          =ᵐ[volume.restrict (UnitCube d)]
        (fun _ : Fin d → ℝ => (0 : ℝ)) :=
      fun i => Filter.Eventually.of_forall (by intro x; simp)
    have hη_ae :
        (fun x => ρ x - m x)
          =ᵐ[volume.restrict (UnitCube d)]
        (fun x => tn * f x) :=
      Filter.Eventually.of_forall (by intro x; change ρ x - m x = tn * f x; simp [hρ_def])
    have hν_ae :
        (fun x => u x - u x)
          =ᵐ[volume.restrict (UnitCube d)]
        (fun _ : Fin d → ℝ => (0 : ℝ)) :=
      Filter.Eventually.of_forall (by intro x; simp)
    have hcongr := mfgOperatorEpsPair_congr_ae
      (V := V) (H := H) (DpH := DpH)
      γBar ε
      Du ρ u
      (fun i x => Du i x - Du i x)
      (fun (_ : Fin d) (_ : Fin d → ℝ) => (0 : ℝ))
      (fun x => ρ x - m x)
      (fun x => tn * f x)
      (fun x => u x - u x)
      (fun _ : Fin d → ℝ => (0 : ℝ))
      hDν_ae hη_ae hν_ae
    rw [hcongr] at hVIρ
    -- Factor `tn` out of the test triple.
    have hsmul := mfgOperatorEpsPair_test_smul
      (V := V) (H := H) (DpH := DpH)
      γBar ε
      Du ρ u
      tn
      (fun (_ : Fin d) (_ : Fin d → ℝ) => (0 : ℝ))
      f
      (fun _ : Fin d → ℝ => (0 : ℝ))
    have hDν_smul_eq :
        (fun i : Fin d => tn • ((fun (_ : Fin d) (_ : Fin d → ℝ) => (0 : ℝ)) i))
          = (fun (_ : Fin d) (_ : Fin d → ℝ) => (0 : ℝ)) := by
      funext i; funext x; change tn • (0 : ℝ) = (0 : ℝ); simp
    have hη_smul_eq :
        (tn • f : (Fin d → ℝ) → ℝ) = fun x => tn * f x := by
      funext x; change tn • f x = tn * f x; simp [smul_eq_mul]
    have hν_smul_eq :
        (tn • (fun _ : Fin d → ℝ => (0 : ℝ)) : (Fin d → ℝ) → ℝ)
          = (fun _ : Fin d → ℝ => (0 : ℝ)) := by
      funext x; change tn • (0 : ℝ) = (0 : ℝ); simp
    rw [hDν_smul_eq, hη_smul_eq, hν_smul_eq] at hsmul
    rw [hsmul] at hVIρ
    have hVI' :
        0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBar ε
              Du ρ u
              (fun _ _ => (0 : ℝ))
              f
              (fun _ => (0 : ℝ)) :=
      (mul_nonneg_iff_of_pos_left htn_pos).mp hVIρ
    exact hVI'
  -- Pass `n → ∞` via the signed `hCont`.
  exact ge_of_tendsto' (hCont σ hσ S hS_meas hS_fin) hStep

/-! ## D6c-2a: transport-form bridge (ε-regularised Gateaux base-point collapse)

The transport-form analogue of `strongVI_setForm_of_IsStrongVI_Aepsi`. Where the
set form perturbs only the density `μ_n := m + t_n · 1_S` (leaving `υ = u`), the
transport form perturbs the **value/gradient pair** along the smooth direction:
`υ_t := u + t · σ · φ`, `Dυ_t := Du + t · σ · ∂φ` (with `μ = m` unchanged). The
test triple delivered to `IsStrongVI_Aepsi` at the segment point is then
`(Dυ_t − Du, μ − m, υ_t − u) = (t σ ∂φ, 0, t σ φ) = t · (σ ∂φ, 0, σ φ)`.

The Minty/Gateaux base-point collapse is then identical to the set form:
factor `t_n = 1/(n+1) > 0` out of the test triple via
`mfgOperatorEpsPair_test_smul`, divide, and pass `n → ∞` via the authorised
CONVENTIONS §8 operator-continuity carrier `hCont` (the transport-direction
companion of the set-form `hCont`). The genuine p-Laplacian Gateaux
differentiability that powers `hCont` is the analyst's input, exactly as for
the set form; it is NOT a forbidden rider. -/

/-- Smooth-perturbation weak-derivative closure: `σ · φ` has weak `i`-derivative
`σ · ∂_i φ`. Re-derived locally (the `Banach.RegularizedSequence` version is
`private`). -/
private lemma hasWeakDerivPer_smul_smoothRight_T3
    (i : Fin d) (σ : ℝ) (φ : SmoothPeriodic d) :
    HasWeakDerivPer i
      (fun x => σ * (φ : (Fin d → ℝ) → ℝ) x)
      (fun x => σ *
        ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) x) := by
  have h := HasWeakDerivPer.of_contDiff i φ
  refine ⟨?_, ?_⟩
  · have hL : MemLpPer (d := d) 1
        ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) := h.1
    have hsmul := MemLpPer.const_smul (𝕜 := ℝ) hL σ
    have heq :
        (σ • ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ))
          = fun x => σ *
            ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x := by
      funext x; simp [Pi.smul_apply, smul_eq_mul]
    rw [← heq]; exact hsmul
  · intro ψ
    have hLHS_eq :
        (fun x => σ *
            ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x *
            (ψ : (Fin d → ℝ) → ℝ) x)
          = fun x => σ •
            (((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x *
              (ψ : (Fin d → ℝ) → ℝ) x) := by
      funext x; simp [smul_eq_mul]; ring
    have hRHS_eq :
        (fun x => σ * (φ : (Fin d → ℝ) → ℝ) x *
            ((SmoothPeriodic.partialDeriv i ψ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x)
          = fun x => σ •
            ((φ : (Fin d → ℝ) → ℝ) x *
              ((SmoothPeriodic.partialDeriv i ψ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x) := by
      funext x; simp [smul_eq_mul]; ring
    rw [hLHS_eq, hRHS_eq]
    rw [Periodic.periodicIntegral_smul (𝕜 := ℝ) σ
          (fun x => ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x *
            (ψ : (Fin d → ℝ) → ℝ) x)]
    rw [Periodic.periodicIntegral_smul (𝕜 := ℝ) σ
          (fun x => (φ : (Fin d → ℝ) → ℝ) x *
            ((SmoothPeriodic.partialDeriv i ψ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x)]
    rw [h.2 ψ]
    simp [smul_eq_mul]

/-- Smooth-perturbation weak-derivative closure: `u + σ · φ` has weak
`i`-derivative `Du + σ · ∂_i φ`, given `u ∈ L¹_per` and `HasWeakDerivPer i u Du`.
Re-derived locally. -/
private lemma hasWeakDerivPer_add_smoothRight_T3
    (i : Fin d) (σ : ℝ) (φ : SmoothPeriodic d)
    {u : (Fin d → ℝ) → ℝ} {Du : (Fin d → ℝ) → ℝ}
    (hu_memLp : MemLpPer (d := d) 1 u)
    (hWD : HasWeakDerivPer i u Du) :
    HasWeakDerivPer i
      (fun x => u x + σ * (φ : (Fin d → ℝ) → ℝ) x)
      (fun x => Du x +
        σ * ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) x) := by
  have hPart := hasWeakDerivPer_smul_smoothRight_T3 i σ φ
  refine ⟨?_, ?_⟩
  · have h1 : MemLpPer (d := d) 1 Du := hWD.1
    have h2 := hPart.1
    have hsum := MemLpPer.add h1 h2
    have heq :
        (Du + (fun x => σ *
          ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) x))
          = fun x => Du x +
            σ * ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x := rfl
    rw [← heq]; exact hsum
  · intro ψ
    -- Notation shortcuts (mirror the proven private version).
    set Diφ : (Fin d → ℝ) → ℝ :=
      ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
          (Fin d → ℝ) → ℝ) with hDiφ
    set σDiφ : (Fin d → ℝ) → ℝ := fun x => σ * Diφ x with hσDiφ
    set ψcoe : (Fin d → ℝ) → ℝ := ((ψ : (Fin d → ℝ) → ℝ)) with hψcoe
    set Diψ : (Fin d → ℝ) → ℝ :=
      ((SmoothPeriodic.partialDeriv i ψ : SmoothPeriodic d) :
          (Fin d → ℝ) → ℝ) with hDiψ
    set σφ : (Fin d → ℝ) → ℝ :=
      fun x => σ * (φ : (Fin d → ℝ) → ℝ) x with hσφ
    have hLHS_eq :
        (fun x => (Du x + σDiφ x) * ψcoe x)
          = (fun x => Du x * ψcoe x) + (fun x => σDiφ x * ψcoe x) := by
      funext x; simp [hσDiφ]; ring
    have hRHS_eq :
        (fun x => (u x + σφ x) * Diψ x)
          = (fun x => u x * Diψ x) + (fun x => σφ x * Diψ x) := by
      funext x; simp [hσφ]; ring
    have hcompact :
        IsCompact (Set.pi Set.univ
          (fun _ : Fin d => Set.Icc (0 : ℝ) 1)) :=
      isCompact_univ_pi (fun _ => isCompact_Icc)
    have hsub : Periodic.UnitCube d ⊆
        Set.pi Set.univ (fun _ : Fin d => Set.Icc (0 : ℝ) 1) := by
      intro x hx j _
      exact Set.Ico_subset_Icc_self ((Periodic.mem_unitCube_iff.mp hx) j)
    have hψ_cont : Continuous ψcoe := ψ.smooth.continuous
    have hDiψ_cont : Continuous Diψ :=
      (SmoothPeriodic.partialDeriv i ψ).smooth.continuous
    have hφ_cont : Continuous ((φ : (Fin d → ℝ) → ℝ)) := φ.smooth.continuous
    have hDiφ_cont : Continuous Diφ :=
      (SmoothPeriodic.partialDeriv i φ).smooth.continuous
    have hσφ_cont : Continuous σφ := by
      simpa only [hσφ, Pi.mul_def] using (continuous_const.mul hφ_cont)
    have hσDiφ_cont : Continuous σDiφ := by
      simpa only [hσDiφ, Pi.mul_def] using (continuous_const.mul hDiφ_cont)
    obtain ⟨Cψ, hCψ⟩ := hcompact.bddAbove_image hψ_cont.norm.continuousOn
    obtain ⟨CDiψ, hCDiψ⟩ := hcompact.bddAbove_image hDiψ_cont.norm.continuousOn
    have h_bdd_ψ :
        ∀ᵐ x ∂(volume.restrict (Periodic.UnitCube d)), ‖ψcoe x‖ ≤ Cψ := by
      refine (MeasureTheory.ae_restrict_iff' Periodic.measurableSet_unitCube).2 ?_
      refine Filter.Eventually.of_forall ?_
      intro x hx; exact hCψ ⟨x, hsub hx, rfl⟩
    have h_bdd_Diψ :
        ∀ᵐ x ∂(volume.restrict (Periodic.UnitCube d)), ‖Diψ x‖ ≤ CDiψ := by
      refine (MeasureTheory.ae_restrict_iff' Periodic.measurableSet_unitCube).2 ?_
      refine Filter.Eventually.of_forall ?_
      intro x hx; exact hCDiψ ⟨x, hsub hx, rfl⟩
    have hDu_int : IntegrableOn Du (Periodic.UnitCube d) := hWD.integrableOn
    have hu_int : IntegrableOn u (Periodic.UnitCube d) :=
      (MeasureTheory.memLp_one_iff_integrable).1 hu_memLp
    have hDuψ_int : IntegrableOn (fun x => Du x * ψcoe x) (Periodic.UnitCube d) :=
      Integrable.mul_bdd hDu_int hψ_cont.aestronglyMeasurable h_bdd_ψ
    have hσDiφ_int : IntegrableOn σDiφ (Periodic.UnitCube d) :=
      (hσDiφ_cont.locallyIntegrable.integrableOn_isCompact hcompact).mono_set hsub
    have hσDiφψ_int :
        IntegrableOn (fun x => σDiφ x * ψcoe x) (Periodic.UnitCube d) :=
      Integrable.mul_bdd hσDiφ_int hψ_cont.aestronglyMeasurable h_bdd_ψ
    have huDiψ_int : IntegrableOn (fun x => u x * Diψ x) (Periodic.UnitCube d) :=
      Integrable.mul_bdd hu_int hDiψ_cont.aestronglyMeasurable h_bdd_Diψ
    have hσφ_int : IntegrableOn σφ (Periodic.UnitCube d) :=
      (hσφ_cont.locallyIntegrable.integrableOn_isCompact hcompact).mono_set hsub
    have hσφDiψ_int :
        IntegrableOn (fun x => σφ x * Diψ x) (Periodic.UnitCube d) :=
      Integrable.mul_bdd hσφ_int hDiψ_cont.aestronglyMeasurable h_bdd_Diψ
    rw [hLHS_eq, hRHS_eq]
    rw [Periodic.periodicIntegral_add hDuψ_int hσDiφψ_int]
    rw [Periodic.periodicIntegral_add huDiψ_int hσφDiψ_int]
    have hWD_eq :
        Periodic.periodicIntegral (fun x => Du x * ψcoe x) =
          - Periodic.periodicIntegral (fun x => u x * Diψ x) := hWD.2 ψ
    have hPart_eq :
        Periodic.periodicIntegral (fun x => σDiφ x * ψcoe x) =
          - Periodic.periodicIntegral (fun x => σφ x * Diψ x) := by
      have := hPart.2 ψ
      simpa [hσDiφ, hσφ, hDiψ, hDiφ, mul_comm, mul_left_comm, mul_assoc]
        using this
    rw [hWD_eq, hPart_eq]
    ring

/-- **Transport-form Minty→strong bridge for `IsStrongVI_Aepsi`** (D6c-2a).

The transport-direction analogue of `strongVI_setForm_of_IsStrongVI_Aepsi`.
From the Minty-form strong VI `IsStrongVI_Aepsi` (operator `A_ε` probed at the
*test* base `(Dυ, μ, υ)`), the membership data of the base pair `(m, u, Du)`,
and the authorised CONVENTIONS §8 operator-continuity carrier `hCont` along the
smooth segment `t ↦ (Du + t σ ∂φ, m, u + t σ φ)`, derive the
**operator-at-solution** transport form `StrongVI_transportForm V H DpH γBar ε
Du m u` (operator probed at the solution base `(Du, m, u)` against the smooth
test direction `(σ ∂φ, 0, σ φ)`).

Proof skeleton (the ε-regularised Gateaux base-point collapse): per smooth `φ`
and sign `σ ∈ {±1}`, set `t_n := 1/(n+1) > 0`. The perturbed pair
`(υ_n, Dυ_n) := (u + t_n σ φ, Du + t_n σ ∂φ)` is admissible (its `MemSobolevPer`
witness comes from `huSob` + smooth closure; its specific gradient family has a
weak derivative by `hasWeakDerivPer_add_smoothRight_T3`). Invoke `hVI` at
`(μ, υ, Dυ) := (m, υ_n, Dυ_n)`. The delivered test triple
`(Dυ_n − Du, μ − m, υ_n − u) = (t_n σ ∂φ, 0, t_n σ φ)` factors as
`t_n · (σ ∂φ, 0, σ φ)` via `mfgOperatorEpsPair_test_smul`; divide by `t_n > 0`
and pass `n → ∞` via `hCont`, landing the nonnegativity at the solution base.

The genuine γ̄-Laplacian Gateaux differentiability powering `hCont` is the
analyst's input — exactly as for the set form, where the strict-positive
perturbation continuity is likewise an `hCont` hypothesis — and is NOT a
forbidden rider. -/
theorem strongVI_transportForm_of_IsStrongVI_Aepsi
    {bb gb : ℝ≥0∞}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBar ε : ℝ}
    {m u : (Fin d → ℝ) → ℝ} {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hVI : IsStrongVI_Aepsi bb gb V H DpH γBar ε m u Du)
    (hmNonneg : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hmLp : MemLpPer bb m)
    (huSob : MemSobolevPer gb u)
    (hu1 : MemLpPer (d := d) 1 u)
    (hDuLp : ∀ i, MemLpPer gb (Du i))
    (hWeak : ∀ i, HasWeakDerivPer i u (Du i))
    (hSmoothLp :
      ∀ (ψ : SmoothPeriodic d), MemLpPer gb ((ψ : (Fin d → ℝ) → ℝ)))
    (hCont :
      ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
      ∀ (φ : SmoothPeriodic d),
        Filter.Tendsto
          (fun n : ℕ =>
            mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBar ε
              (fun i x => Du i x + (1 / ((n : ℝ) + 1)) * σ *
                ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x)
              m
              (fun x => u x + (1 / ((n : ℝ) + 1)) * σ *
                (φ : (Fin d → ℝ) → ℝ) x)
              (fun i x => σ *
                ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x)
              (fun _ => (0 : ℝ))
              (fun x => σ * (φ : (Fin d → ℝ) → ℝ) x))
          Filter.atTop
          (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                γBar ε
                Du m u
                (fun i x => σ *
                  ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                    (Fin d → ℝ) → ℝ) x)
                (fun _ => (0 : ℝ))
                (fun x => σ * (φ : (Fin d → ℝ) → ℝ) x)))) :
    StrongVI_transportForm V H DpH γBar ε Du m u := by
  intro σ hσ φ
  -- Per-`n` step: nonnegativity of the pairing at the perturbed pair.
  have hStep :
      ∀ n : ℕ,
        0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBar ε
              (fun i x => Du i x + (1 / ((n : ℝ) + 1)) * σ *
                ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x)
              m
              (fun x => u x + (1 / ((n : ℝ) + 1)) * σ *
                (φ : (Fin d → ℝ) → ℝ) x)
              (fun i x => σ *
                ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x)
              (fun _ => (0 : ℝ))
              (fun x => σ * (φ : (Fin d → ℝ) → ℝ) x) := by
    intro n
    set tn : ℝ := 1 / ((n : ℝ) + 1) with htn_def
    have htn_pos : (0 : ℝ) < tn := by
      have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      exact div_pos one_pos hpos
    -- The perturbed value `υ_n := u + (tn σ)·φ` and gradient family
    -- `Dυ_n := Du + (tn σ)·∂φ`. Write the scalar `tn σ` together.
    set c : ℝ := tn * σ with hc_def
    set υn : (Fin d → ℝ) → ℝ :=
      fun x => u x + c * (φ : (Fin d → ℝ) → ℝ) x with hυn_def
    set Dυn : Fin d → (Fin d → ℝ) → ℝ :=
      fun i x => Du i x + c *
        ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
          (Fin d → ℝ) → ℝ) x with hDυn_def
    -- Admissibility of `(m, υn, Dυn)`.
    -- 1. `MemSobolevPer gb υn`.
    have hφ_smoothLp : MemLpPer gb ((φ : (Fin d → ℝ) → ℝ)) := hSmoothLp φ
    have hcφ_lp : MemLpPer gb (fun x => c * (φ : (Fin d → ℝ) → ℝ) x) := by
      have := MemLpPer.const_smul (𝕜 := ℝ) hφ_smoothLp c
      have heq : (c • (φ : (Fin d → ℝ) → ℝ))
          = fun x => c * (φ : (Fin d → ℝ) → ℝ) x := by
        funext x; simp [Pi.smul_apply, smul_eq_mul]
      rwa [heq] at this
    have hυn_lp : MemLpPer gb υn := by
      have := MemLpPer.add huSob.1 hcφ_lp
      have heq : (u + (fun x => c * (φ : (Fin d → ℝ) → ℝ) x)) = υn := by
        funext x; simp [hυn_def]
      rwa [heq] at this
    have hWD_υn : ∀ i, HasWeakDerivPer i υn (Dυn i) := by
      intro i
      have h := hasWeakDerivPer_add_smoothRight_T3 i c φ hu1 (hWeak i)
      -- match `Dυn i` shape: `Du i x + c * ∂φ x`.
      have heq1 : (fun x => u x + c * (φ : (Fin d → ℝ) → ℝ) x) = υn := by
        funext x; simp [hυn_def]
      have heq2 :
          (fun x => Du i x +
            c * ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x) = Dυn i := by
        funext x; simp [hDυn_def]
      rw [heq1, heq2] at h
      exact h
    have hυn_sob : MemSobolevPer gb υn := ⟨hυn_lp, ⟨Dυn, hWD_υn⟩⟩
    have hDυn_lp : ∀ i, MemLpPer gb (Dυn i) := by
      intro i
      have hDiφ_lp : MemLpPer gb
          ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) := hSmoothLp (SmoothPeriodic.partialDeriv i φ)
      have hcDiφ_lp : MemLpPer gb
          (fun x => c *
            ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) x) := by
        have := MemLpPer.const_smul (𝕜 := ℝ) hDiφ_lp c
        have heq : (c • ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ))
            = fun x => c *
              ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x := by
          funext x; simp [Pi.smul_apply, smul_eq_mul]
        rwa [heq] at this
      have hsum := MemLpPer.add (hDuLp i) hcDiφ_lp
      have heq : (Du i + (fun x => c *
          ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) x)) = Dυn i := by
        funext x; simp [hDυn_def]
      rwa [heq] at hsum
    -- Invoke the Minty VI at `(μ, υ, Dυ) := (m, υn, Dυn)`.
    have hVIn := hVI m υn Dυn hmNonneg hmLp hυn_sob hDυn_lp hWD_υn
    -- `hVIn : 0 ≤ mfgOperatorEpsPair … Dυn m υn (Dυn − Du) (m − m) (υn − u)`.
    -- Rewrite the test triple `(c·∂φ, 0, c·φ)` via `_congr_ae`, identifying
    -- `Dυn i − Du i = c·∂φ`, `m − m = 0`, `υn − u = c·φ` pointwise.
    have hDν_ae : ∀ i,
        (fun x => Dυn i x - Du i x)
          =ᵐ[volume.restrict (UnitCube d)]
        (fun x => c *
          ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) x) := by
      intro i
      refine Filter.Eventually.of_forall ?_
      intro x; simp [hDυn_def]
    have hη_ae :
        (fun x => m x - m x)
          =ᵐ[volume.restrict (UnitCube d)]
        (fun _ : Fin d → ℝ => (0 : ℝ)) := by
      refine Filter.Eventually.of_forall ?_
      intro x; simp
    have hν_ae :
        (fun x => υn x - u x)
          =ᵐ[volume.restrict (UnitCube d)]
        (fun x => c * (φ : (Fin d → ℝ) → ℝ) x) := by
      refine Filter.Eventually.of_forall ?_
      intro x; simp [hυn_def]
    have hcongr := mfgOperatorEpsPair_congr_ae
      (V := V) (H := H) (DpH := DpH)
      γBar ε
      Dυn m υn
      (fun i x => Dυn i x - Du i x)
      (fun i x => c *
        ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
          (Fin d → ℝ) → ℝ) x)
      (fun x => m x - m x)
      (fun _ : Fin d → ℝ => (0 : ℝ))
      (fun x => υn x - u x)
      (fun x => c * (φ : (Fin d → ℝ) → ℝ) x)
      hDν_ae hη_ae hν_ae
    rw [hcongr] at hVIn
    -- Factor `c = tn * σ` out of the test triple. Write the test triple as
    -- `c • (σ⁻¹ ∂φ-shape)` — instead factor `tn` directly via `_test_smul`
    -- with base direction `(σ ∂φ, 0, σ φ)`.
    have hsmul := mfgOperatorEpsPair_test_smul
      (V := V) (H := H) (DpH := DpH)
      γBar ε
      Dυn m υn
      tn
      (fun i x => σ *
        ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
          (Fin d → ℝ) → ℝ) x)
      (fun _ : Fin d → ℝ => (0 : ℝ))
      (fun x => σ * (φ : (Fin d → ℝ) → ℝ) x)
    have hDν_smul_eq :
        (fun i : Fin d => tn • ((fun i x => σ *
            ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) x) i))
          = (fun i x => c *
              ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x) := by
      funext i; funext x
      change tn • (σ *
        ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
          (Fin d → ℝ) → ℝ) x) = _
      simp [smul_eq_mul, hc_def]; ring
    have hη_smul_eq :
        (tn • (fun _ : Fin d → ℝ => (0 : ℝ)) : (Fin d → ℝ) → ℝ)
          = (fun _ : Fin d → ℝ => (0 : ℝ)) := by
      funext x; change tn • (0 : ℝ) = (0 : ℝ); simp
    have hν_smul_eq :
        (tn • (fun x => σ * (φ : (Fin d → ℝ) → ℝ) x) : (Fin d → ℝ) → ℝ)
          = (fun x => c * (φ : (Fin d → ℝ) → ℝ) x) := by
      funext x
      change tn • (σ * (φ : (Fin d → ℝ) → ℝ) x) = c * (φ : (Fin d → ℝ) → ℝ) x
      simp [smul_eq_mul, hc_def]; ring
    rw [hDν_smul_eq, hη_smul_eq, hν_smul_eq] at hsmul
    rw [hsmul] at hVIn
    -- `hVIn : 0 ≤ tn * mfgOperatorEpsPair … Dυn m υn (σ∂φ) 0 (σφ)`, `tn > 0`.
    have hVI' :
        0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBar ε Dυn m υn
              (fun i x => σ *
                ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x)
              (fun _ => (0 : ℝ))
              (fun x => σ * (φ : (Fin d → ℝ) → ℝ) x) :=
      (mul_nonneg_iff_of_pos_left htn_pos).mp hVIn
    -- `Dυn`, `υn` are exactly the segment base at parameter `tn`.
    -- Rewrite `c·∂φ = tn·σ·∂φ` and `c·φ = tn·σ·φ` in the base to match `hStep`.
    have hbase_eq :
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBar ε Dυn m υn
              (fun i x => σ *
                ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x)
              (fun _ => (0 : ℝ))
              (fun x => σ * (φ : (Fin d → ℝ) → ℝ) x)
          = mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBar ε
              (fun i x => Du i x + (1 / ((n : ℝ) + 1)) * σ *
                ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x)
              m
              (fun x => u x + (1 / ((n : ℝ) + 1)) * σ *
                (φ : (Fin d → ℝ) → ℝ) x)
              (fun i x => σ *
                ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x)
              (fun _ => (0 : ℝ))
              (fun x => σ * (φ : (Fin d → ℝ) → ℝ) x) := by
      have hDυn_rw :
          Dυn = (fun i x => Du i x + (1 / ((n : ℝ) + 1)) * σ *
            ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) x) := by
        funext i x; simp only [hDυn_def, hc_def, htn_def, mul_assoc]
      have hυn_rw :
          υn = (fun x => u x + (1 / ((n : ℝ) + 1)) * σ *
            (φ : (Fin d → ℝ) → ℝ) x) := by
        funext x; simp only [hυn_def, hc_def, htn_def, mul_assoc]
      rw [hDυn_rw, hυn_rw]
    rw [hbase_eq] at hVI'
    exact hVI'
  -- Pass `n → ∞` via `hCont`.
  exact ge_of_tendsto' (hCont σ hσ φ) hStep

/-- **K0 transport-form Minty→strong bridge for `IsStrongVI_Aepsi`** (D6c2a2c).

Closed-cone (`K₀`) variant of `strongVI_transportForm_of_IsStrongVI_Aepsi`:
the same ε-regularised transport-direction Gateaux base-point collapse, but
with the operator-continuity `hCont` certificate **discharged internally**
through the K0 hemicontinuity machinery, so it is no longer a binder.

* The starting Minty VI `hVI` is for the **genuine** carrier
  `HdeltaK0 hweak ε` with regularised gradient `DpHepsilonFam hweak qε ε`
  — exactly the carrier `T3RegularizedStrongFamily.hVI` produces, so the
  bridge wires directly at the D6c2a2d call site with no reverse
  `IsStrongVI_Aepsi` conversion.
* The continuity certificate is built per `(σ, φ)` from
  `Aepsi_hemicontinuous_transportSegment_K0` (Hemicontinuity.lean), which
  needs only `0 ≤ m` on the density side (the transport segment fixes the
  density `cxComb m m t = m`) plus the **closed-cone** regularity `hRegK0`
  on the genuine `HdeltaK0` carrier (from `regularityHK0_Hdelta_of_selector`,
  the reviewer-Option-A producer parallel to
  `regularityHK0_HdeltaK0_DpHepsilon_of_selector`, D6c2a2b: the
  `continuous_Hext_pm` field transfers from the `HdeltaK0` instance by
  `ContinuousOn.congr` since the canonical zero-mass trace, and the flux
  field is verbatim identical) and the per-segment
  dominator/measurability bundle (the §1b standing-regularity inputs
  `g_unreg`/`g_gat` and AE-strong-measurability, quantified over the test
  data `(σ, φ)`).
* The transport segment is realised at endpoints `Dῡ := Du`,
  `Dυ := Du + σ ∂φ`, `ῡ := u`, `υ := u + σ φ`, density `μ = m̄ = m`, and the
  test triple `(σ ∂φ, 0, σ φ)`; the continuity at `t = 0` converts to the
  `n → ∞` `Tendsto` along `t_n := 1/(n+1)` consumed by the landed bridge.

No `hCont` binder, no strict positivity (`0 < m`, `hPosSeg`, `mε_pos`), no
`HdeltaPos`, and no Pack/Inputs/Oracle binders. -/
theorem strongVI_transportForm_K0_of_IsStrongVI_Aepsi
    {bb gb : ℝ≥0∞}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    {V : (Fin d → ℝ) → ℝ}
    (qε : QEpsFamily d)
    {γBar ε : ℝ} (hγ : 1 < γBar)
    {m u : (Fin d → ℝ) → ℝ} {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hRegK0 :
      StationaryMFG.Theorems.SimplePower.RegularityHK0 (d := d)
        (HdeltaK0 hweak ε) (DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε))
    (hVI : IsStrongVI_Aepsi bb gb V (HdeltaK0 hweak ε)
            (DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε) γBar ε m u Du)
    (hmNonneg : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hmLp : MemLpPer bb m)
    (huSob : MemSobolevPer gb u)
    (hu1 : MemLpPer (d := d) 1 u)
    (hDuLp : ∀ i, MemLpPer gb (Du i))
    (hWeak : ∀ i, HasWeakDerivPer i u (Du i))
    (hSmoothLp :
      ∀ (ψ : SmoothPeriodic d), MemLpPer gb ((ψ : (Fin d → ℝ) → ℝ)))
    -- Per-`(σ, φ)` transport-segment dominator/measurability bundle (§1b
    -- standing-regularity inputs feeding the closed-cone DCT continuity).
    (g_unreg g_gat :
      (σ : ℝ) → (φ : SmoothPeriodic d) → (Fin d → ℝ) → ℝ)
    (hg_unreg_int :
      ∀ (σ : ℝ) (φ : SmoothPeriodic d),
        IntegrableOn (g_unreg σ φ) (UnitCube d))
    (hg_gat_int :
      ∀ (σ : ℝ) (φ : SmoothPeriodic d),
        IntegrableOn (g_gat σ φ) (UnitCube d))
    (hF_unreg_meas :
      ∀ (σ : ℝ) (φ : SmoothPeriodic d), ∀ t ∈ Set.Icc (0 : ℝ) 1,
        AEStronglyMeasurable
          (fun x =>
            aepsiIntegrandAt_unreg_K0 (d := d) V (HdeltaK0 hweak ε)
              (DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε)
              (fun i x => Du i x + σ *
                ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x)
              Du m m
              (fun x => u x + σ * (φ : (Fin d → ℝ) → ℝ) x) u
              (fun i x => σ *
                ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x)
              (fun _ => (0 : ℝ))
              (fun x => σ * (φ : (Fin d → ℝ) → ℝ) x) x t)
          (volume.restrict (UnitCube d)))
    (hF_unreg_bound :
      ∀ (σ : ℝ) (φ : SmoothPeriodic d), ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          ‖aepsiIntegrandAt_unreg_K0 (d := d) V (HdeltaK0 hweak ε)
              (DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε)
              (fun i x => Du i x + σ *
                ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x)
              Du m m
              (fun x => u x + σ * (φ : (Fin d → ℝ) → ℝ) x) u
              (fun i x => σ *
                ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x)
              (fun _ => (0 : ℝ))
              (fun x => σ * (φ : (Fin d → ℝ) → ℝ) x) x t‖
            ≤ g_unreg σ φ x)
    (hF_gat_meas :
      ∀ (σ : ℝ) (φ : SmoothPeriodic d), ∀ t ∈ Set.Icc (0 : ℝ) 1,
        AEStronglyMeasurable
          (fun x =>
            aepsiIntegrandAt_gateaux (d := d) γBar
              (fun i x => Du i x + σ *
                ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x)
              Du
              (fun x => u x + σ * (φ : (Fin d → ℝ) → ℝ) x) u
              (fun i x => σ *
                ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x)
              (fun x => σ * (φ : (Fin d → ℝ) → ℝ) x) x t)
          (volume.restrict (UnitCube d)))
    (hF_gat_bound :
      ∀ (σ : ℝ) (φ : SmoothPeriodic d), ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          ‖aepsiIntegrandAt_gateaux (d := d) γBar
              (fun i x => Du i x + σ *
                ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x)
              Du
              (fun x => u x + σ * (φ : (Fin d → ℝ) → ℝ) x) u
              (fun i x => σ *
                ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x)
              (fun x => σ * (φ : (Fin d → ℝ) → ℝ) x) x t‖
            ≤ g_gat σ φ x) :
    StrongVI_transportForm V (HdeltaK0 hweak ε)
      (DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε) γBar ε Du m u := by
  -- Build the transport-form result directly on the genuine `HdeltaK0` carrier
  -- by invoking the landed open-cone bridge with `hCont` supplied internally
  -- through the K0 (closed-cone) hemicontinuity machinery. The `hRegK0`
  -- closed-cone regularity certificate is on the genuine `HdeltaK0` carrier
  -- (`regularityHK0_Hdelta_of_selector`).
  refine strongVI_transportForm_of_IsStrongVI_Aepsi
    hVI hmNonneg hmLp huSob hu1 hDuLp hWeak hSmoothLp ?_
  -- Discharge `hCont` per `(σ, φ)` from the K0 transport-segment continuity.
  intro σ _hσ φ
  -- The transport segment continuity (closed-cone DCT) at the chosen
  -- endpoints, with density fixed at `m`.
  have hcts :
      ContinuousOn (fun t : ℝ =>
          mfgOperatorEpsPair (V := V) (H := HdeltaK0 hweak ε)
            (DpH := DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε) γBar ε
            (fun i x => cxCombGrad
              (fun i x => Du i x + σ *
                ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x) Du t i x)
            (fun x => cxComb m m t x)
            (fun x => cxComb
              (fun x => u x + σ * (φ : (Fin d → ℝ) → ℝ) x) u t x)
            (fun i x => σ *
              ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x)
            (fun _ => (0 : ℝ))
            (fun x => σ * (φ : (Fin d → ℝ) → ℝ) x)) (Set.Icc 0 1) :=
    Aepsi_hemicontinuous_transportSegment_K0 (d := d)
      V (HdeltaK0 hweak ε)
      (DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε) hRegK0 γBar ε hγ
      (fun i x => Du i x + σ *
        ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
          (Fin d → ℝ) → ℝ) x) Du
      m
      (fun x => u x + σ * (φ : (Fin d → ℝ) → ℝ) x) u
      (fun i x => σ *
        ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
          (Fin d → ℝ) → ℝ) x)
      (fun _ => (0 : ℝ))
      (fun x => σ * (φ : (Fin d → ℝ) → ℝ) x)
      hmNonneg (g_unreg σ φ) (g_gat σ φ)
      (hg_unreg_int σ φ) (hg_gat_int σ φ)
      (hF_unreg_meas σ φ) (hF_unreg_bound σ φ)
      (hF_gat_meas σ φ) (hF_gat_bound σ φ)
  -- `t_n := 1/(n+1)` lies in `[0,1]` and tends to `0`.
  set F : ℝ → ℝ := fun t =>
      mfgOperatorEpsPair (V := V) (H := HdeltaK0 hweak ε)
        (DpH := DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε) γBar ε
        (fun i x => cxCombGrad
          (fun i x => Du i x + σ *
            ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) x) Du t i x)
        (fun x => cxComb m m t x)
        (fun x => cxComb
          (fun x => u x + σ * (φ : (Fin d → ℝ) → ℝ) x) u t x)
        (fun i x => σ *
          ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) x)
        (fun _ => (0 : ℝ))
        (fun x => σ * (φ : (Fin d → ℝ) → ℝ) x) with hF_def
  -- `F` continuous within `[0,1]` at `0`.
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_refl _, zero_le_one⟩
  have hcwa : ContinuousWithinAt F (Set.Icc 0 1) 0 := hcts.continuousWithinAt h0mem
  -- `t_n → 0` within `[0,1]`.
  have htn_tendsto :
      Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        Filter.atTop (𝓝[Set.Icc 0 1] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · -- `1/(n+1) → 0`.
      exact tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    · refine Filter.Eventually.of_forall ?_
      intro n
      have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      refine ⟨le_of_lt (div_pos one_pos hpos), ?_⟩
      rw [div_le_one hpos]
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
  -- Compose: `F (t_n) → F 0`.
  have hcomp :
      Filter.Tendsto (fun n : ℕ => F ((1 : ℝ) / ((n : ℝ) + 1)))
        Filter.atTop (𝓝 (F 0)) :=
    hcwa.tendsto.comp htn_tendsto
  -- Rewrite `F (t_n)` to the perturbed pairing, and `F 0` to the base.
  have hFn_eq : ∀ n : ℕ,
      F ((1 : ℝ) / ((n : ℝ) + 1))
        = mfgOperatorEpsPair (V := V) (H := HdeltaK0 hweak ε)
            (DpH := DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε) γBar ε
            (fun i x => Du i x + (1 / ((n : ℝ) + 1)) * σ *
              ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x)
            m
            (fun x => u x + (1 / ((n : ℝ) + 1)) * σ *
              (φ : (Fin d → ℝ) → ℝ) x)
            (fun i x => σ *
              ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x)
            (fun _ => (0 : ℝ))
            (fun x => σ * (φ : (Fin d → ℝ) → ℝ) x) := by
    intro n
    simp only [hF_def]
    congr 1
    · funext i x; simp only [cxCombGrad]; ring
    · funext x; simp only [cxComb]; ring
    · funext x; simp only [cxComb]; ring
  have hF0_eq :
      F 0 = mfgOperatorEpsPair (V := V) (H := HdeltaK0 hweak ε)
              (DpH := DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε) γBar ε
              Du m u
              (fun i x => σ *
                ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x)
              (fun _ => (0 : ℝ))
              (fun x => σ * (φ : (Fin d → ℝ) → ℝ) x) := by
    simp only [hF_def]
    congr 1
    · funext i x; simp only [cxCombGrad]; ring
    · funext x; simp only [cxComb]; ring
    · funext x; simp only [cxComb]; ring
  rw [hF0_eq] at hcomp
  refine hcomp.congr ?_
  intro n; exact hFn_eq n

/-- **HJB clause `lem:strong.is.strong.delta` (a) from `IsStrongVI_Aepsi`.**

Chains the Minty→strong bridge `strongVI_setForm_of_IsStrongVI_Aepsi`
with the Phase-6 HJB wrapper `Hdelta_strong_HJB_le` at the regularised
Hamiltonian `H := HdeltaK0 hweak ε`. The conclusion is exactly the `hHJB`
input of `apriori_weak_power_growth` (`InfimalConvolution/Apriori.lean`,
line 102).

The residual integrability `hRes` is the §1b standing-regularity input
required by `Hdelta_strong_HJB_le`; `hIndicMemLp` and `hCont` are the
authorised §8 / finite-measure Minty-bridge inputs. -/
theorem hHJB_of_IsStrongVI_Aepsi
    {bb gb : ℝ≥0∞}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (DpHε : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (γBar ε : ℝ)
    {m u : (Fin d → ℝ) → ℝ} {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hVI : IsStrongVI_Aepsi bb gb V (HdeltaK0 hweak ε) DpHε γBar ε m u Du)
    (hmNonneg : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hmLp : MemLpPer bb m)
    (huSob : MemSobolevPer gb u)
    (hDuLp : ∀ i, MemLpPer gb (Du i))
    (hWeak : ∀ i, HasWeakDerivPer i u (Du i))
    (hIndicMemLp :
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (volume.restrict (UnitCube d)) S < ∞ →
        MemLpPer bb (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ))))
    (hCont :
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (volume.restrict (UnitCube d)) S < ∞ →
        Filter.Tendsto
          (fun n : ℕ =>
            mfgOperatorEpsPair (V := V) (H := HdeltaK0 hweak ε) (DpH := DpHε)
              γBar ε
              Du
              (fun x => m x + (1 / ((n : ℝ) + 1)) *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              u
              (fun _ _ => (0 : ℝ))
              (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)))
              (fun _ => (0 : ℝ)))
          Filter.atTop
          (𝓝 (mfgOperatorEpsPair (V := V) (H := HdeltaK0 hweak ε) (DpH := DpHε)
                γBar ε
                Du m u
                (fun _ _ => (0 : ℝ))
                (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)))
                (fun _ => (0 : ℝ)))))
    (hRes : Integrable (hjbResidual V (HdeltaK0 hweak ε) Du m u)
              (volume.restrict (UnitCube d))) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      u x + HdeltaK0 hweak ε x (fun i => Du i x) (m x) - V x ≤ 0 :=
  Hdelta_strong_HJB_le hweak V DpHε γBar ε Du m u hRes
    (strongVI_setForm_of_IsStrongVI_Aepsi hVI hmNonneg hmLp huSob hDuLp
      hWeak hIndicMemLp hCont)

/-! ## Family-level HJB-clause producer -/

/-- **Family-level HJB-clause producer** (A2a headline).

For every `ε > 0`, given the A1d strong-VI datum `IsStrongVI_Aepsi` at
the substituted regularised pair `(HdeltaK0 hweak ε, DpHε ε)`, the base
membership data, and the authorised Minty-bridge / residual inputs,
deliver the a.e. HJB inequality

```
u_ε(x) + H^ε(x, Du_ε(x), m_ε(x)) − V(x) ≤ 0   a.e. x ∈ 𝕋^d
```

required as the `hHJB` input to `apriori_weak_power_growth`. The
producer is a per-`ε` application of `hHJB_of_IsStrongVI_Aepsi`. -/
theorem hHJB_of_strongVI_family
    {bb gb : ℝ≥0∞}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (DpHε : ℝ → (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (γBar : ℝ)
    (m u : ℝ → (Fin d → ℝ) → ℝ) (Du : ℝ → Fin d → (Fin d → ℝ) → ℝ)
    (hVI : ∀ ε, 0 < ε → ε ≤ 1 →
      IsStrongVI_Aepsi bb gb V (HdeltaK0 hweak ε) (DpHε ε) γBar ε
        (m ε) (u ε) (Du ε))
    (hmNonneg : ∀ ε, 0 < ε → ε ≤ 1 →
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m ε x)
    (hmLp : ∀ ε, 0 < ε → ε ≤ 1 → MemLpPer bb (m ε))
    (huSob : ∀ ε, 0 < ε → ε ≤ 1 → MemSobolevPer gb (u ε))
    (hDuLp : ∀ ε, 0 < ε → ε ≤ 1 → ∀ i, MemLpPer gb (Du ε i))
    (hWeak : ∀ ε, 0 < ε → ε ≤ 1 → ∀ i, HasWeakDerivPer i (u ε) (Du ε i))
    (hIndicMemLp :
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (volume.restrict (UnitCube d)) S < ∞ →
        MemLpPer bb (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ))))
    (hCont : ∀ ε, 0 < ε → ε ≤ 1 →
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (volume.restrict (UnitCube d)) S < ∞ →
        Filter.Tendsto
          (fun n : ℕ =>
            mfgOperatorEpsPair (V := V) (H := HdeltaK0 hweak ε) (DpH := DpHε ε)
              γBar ε
              (Du ε)
              (fun x => m ε x + (1 / ((n : ℝ) + 1)) *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              (u ε)
              (fun _ _ => (0 : ℝ))
              (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)))
              (fun _ => (0 : ℝ)))
          Filter.atTop
          (𝓝 (mfgOperatorEpsPair (V := V) (H := HdeltaK0 hweak ε) (DpH := DpHε ε)
                γBar ε
                (Du ε) (m ε) (u ε)
                (fun _ _ => (0 : ℝ))
                (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)))
                (fun _ => (0 : ℝ)))))
    (hRes : ∀ ε, 0 < ε → ε ≤ 1 →
      Integrable (hjbResidual V (HdeltaK0 hweak ε) (Du ε) (m ε) (u ε))
        (volume.restrict (UnitCube d))) :
    ∀ ε, 0 < ε → ε ≤ 1 →
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        (u ε) x + HdeltaK0 hweak ε x (fun i => (Du ε) i x) ((m ε) x) - V x ≤ 0 :=
  fun ε hε hε1ε =>
    hHJB_of_IsStrongVI_Aepsi hweak V (DpHε ε) γBar ε
      (hVI ε hε hε1ε) (hmNonneg ε hε hε1ε) (hmLp ε hε hε1ε) (huSob ε hε hε1ε)
      (hDuLp ε hε hε1ε)
      (hWeak ε hε hε1ε) hIndicMemLp (hCont ε hε hε1ε) (hRes ε hε hε1ε)

/-! ## D6c-1: integrated HJB-on-positivity half for the strong-VI family

This is the *first* of the two genuine halves of the integrated §1b identity
`eq:appositiveum` (paper line 1212), derived as a NAMED theorem (not an input)
from the produced family `fam : T3RegularizedStrongFamily`.

`Hdelta_strong_HJB_eq_on_pos` (part (b), `InfimalConvolution/StrongIsStrong.lean`,
line 133) gives the pointwise a.e. equality
`(u_ε + H^ε(x, Du_ε, m_ε) − V) · m_ε = 0`. The signed set-form VI it consumes is
produced from `fam.hVI` (`IsStrongVI_Aepsi`) by the signed Minty bridge
`strongVI_setFormSigned_of_IsStrongVI_Aepsi`. Integrating the a.e. zero over the
unit cube (`integral_eq_zero_of_ae`) yields the integrated HJB-on-positivity
identity. The companion *transport* half (testing the transport equation at
`φ = u_ε`) is D6c-2; the two are assembled into `hIdentityRaw` by D6c-3. -/

namespace T3

/-- **D6c-1: integrated HJB-on-positivity half.**

For the produced strong-VI family `fam` and `ε > 0`, the integrated identity
```
∫_{[0,1]^d} (u_ε + H^ε(x, Du_ε, m_ε) − V) · m_ε dx = 0,
```
where `H^ε = HdeltaK0 hweak ε` is the genuine regularised carrier. The proof
integrates the pointwise a.e. equality delivered by `Hdelta_strong_HJB_eq_on_pos`,
fed by the signed Minty bridge from `fam.hVI`.

`fam` IS a binder (this lemma is about a given family). `hResM` is the §1b
standing-regularity input required by part (b), and `hCont` is the authorised
operator-continuity (Minty-bridge) input, both with the same status as the
inputs to `hHJB_of_strongVI_family`. -/
theorem hHJBIntegrated_of_T3RegularizedStrongFamily
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d) {βBarReal γBarReal : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    (fam : T3RegularizedStrongFamily V hweak qε βBarReal γBarReal)
    (ε : ℝ) (hεpos : 0 < ε) (hε1 : ε ≤ 1)
    (hResM : Integrable
              (fun x => hjbResidual V (HdeltaK0 hweak ε) (fam.Du ε)
                          (fam.m ε) (fam.u ε) x * fam.m ε x)
              (volume.restrict (UnitCube d)))
    (hCont :
      ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (volume.restrict (UnitCube d)) S < ∞ →
        Filter.Tendsto
          (fun n : ℕ =>
            mfgOperatorEpsPair (V := V) (H := HdeltaK0 hweak ε)
              (DpH := DpHepsilonFam hweak qε ε)
              γBarReal ε
              (fam.Du ε)
              (fun x => fam.m ε x + (1 / ((n : ℝ) + 1)) *
                          (σ * fam.m ε x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
              (fam.u ε)
              (fun _ _ => (0 : ℝ))
              (fun x => σ * fam.m ε x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              (fun _ => (0 : ℝ)))
          Filter.atTop
          (𝓝 (mfgOperatorEpsPair (V := V) (H := HdeltaK0 hweak ε)
                (DpH := DpHepsilonFam hweak qε ε)
                γBarReal ε
                (fam.Du ε) (fam.m ε) (fam.u ε)
                (fun _ _ => (0 : ℝ))
                (fun x => σ * fam.m ε x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                (fun _ => (0 : ℝ))))) :
    ∫ x in UnitCube d,
        (fam.u ε x + HdeltaK0 hweak ε x (fun i => fam.Du ε i x) (fam.m ε x)
            - V x) * fam.m ε x
        ∂(volume : Measure (Fin d → ℝ)) = 0 := by
  -- Signed set-form VI from the family's `IsStrongVI_Aepsi` via the signed
  -- Minty bridge.
  have hSigned :
      StrongVI_setForm_signed V (HdeltaK0 hweak ε) (DpHepsilonFam hweak qε ε)
        γBarReal ε (fam.Du ε) (fam.m ε) (fam.u ε) :=
    strongVI_setFormSigned_of_IsStrongVI_Aepsi
      (hVI := fam.hVI ε hεpos hε1)
      (hmNonneg := fam.hmNonneg ε hεpos hε1)
      (hmLp := fam.hmLp ε hεpos hε1)
      (huSob := fam.huSob ε hεpos hε1)
      (hDuLp := fam.hDuLp ε hεpos hε1)
      (hWeak := fam.hDuWeak ε hεpos hε1)
      hCont
  -- Pointwise a.e. equality `(u + H^ε − V) · m = 0` from part (b).
  have hPt :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        (fam.u ε x + HdeltaK0 hweak ε x (fun i => fam.Du ε i x) (fam.m ε x)
            - V x) * fam.m ε x = 0 :=
    Hdelta_strong_HJB_eq_on_pos hweak V (DpHepsilonFam hweak qε ε) γBarReal ε
      (fam.Du ε) (fam.m ε) (fam.u ε) hResM hSigned
  -- Integrate the a.e. zero.
  have hzero :
      (fun x =>
        (fam.u ε x + HdeltaK0 hweak ε x (fun i => fam.Du ε i x) (fam.m ε x)
            - V x) * fam.m ε x)
        =ᵐ[volume.restrict (UnitCube d)] (0 : (Fin d → ℝ) → ℝ) := by
    filter_upwards [hPt] with x hx
    simpa using hx
  exact MeasureTheory.integral_eq_zero_of_ae hzero

/-! ## D6c-2: transport half tested at `φ = u_ε` (density / limit passage)

This section delivers the *second* genuine half of the integrated §1b identity
`eq:appositiveum` (paper line 1212): the regularised transport equation tested
at the **non-smooth** solution `φ = u_ε` itself.

`Hdelta_strong_transport_eq` (`InfimalConvolution/StrongIsStrong.lean`, line 202)
gives the transport equality only for *smooth periodic* test functions
`φ : SmoothPeriodic d`:
```
∫ transportFluxIntegrand DpHε Du m φ + ε · ∫ transportGateauxIntegrand γ̄ Du u φ = 0.
```
The paper, however, tests this at `φ = u_ε ∈ W^{1,γ̄}_per`, which is not smooth.
The extension is a genuine `W^{1,γ̄}`-density / limit-passage argument: approximate
`u_ε` by smooth periodics in the Sobolev seminorm, test at each, and pass to the
limit using Hölder-continuity of the transport functional. This is exactly the
content packaged by the torus-layer keystone
`Periodic.integralIdentity_extend_to_W1gamma_via_smooth_density`
(`Periodic/DensityApprox.lean`, line 367), which we route through here.

The transport flux + ε·Gateaux integrand, when paired with a test pair `(f, g)`,
equals the Hölder pairing `transportFunctional a b f g = ∫ a·f + ∑ᵢ ∫ bᵢ·gᵢ` with
the canonical coefficients
```
a x  := (m x − 1) + ε · (|u x|^{γ̄−2} · u x),
b i x := m x · D_pH^ε(x, Du, m)_i + ε · (|Du x|^{γ̄−2} · Du i x).
```
These are the §1b standing-regularity coefficients; their `L^{γ̄'}_per`
membership (the Hölder-conjugate side) is supplied as an authorised input
exactly as `hRes`/`hResM` are in the HJB half. -/

/-- **Flux coefficient on the test function** `f`: `aFlux x = m x − 1`. -/
noncomputable def fluxCoeffA (m : (Fin d → ℝ) → ℝ) : (Fin d → ℝ) → ℝ :=
  fun x => m x - 1

/-- **Flux coefficient on the gradient** `g`:
`bFlux i x = m x · D_pH^ε(x, Du, m)_i`. -/
noncomputable def fluxCoeffB
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (m : (Fin d → ℝ) → ℝ) (Du : Fin d → (Fin d → ℝ) → ℝ) :
    Fin d → ((Fin d → ℝ) → ℝ) :=
  fun i x => m x * (DpH x (fun j => Du j x) (m x)) i

/-- **Gateaux coefficient on the test function** `f`:
`aGat x = |u x|^{γ̄−2} · u x`. -/
noncomputable def gatCoeffA
    (γBar : ℝ) (u : (Fin d → ℝ) → ℝ) : (Fin d → ℝ) → ℝ :=
  fun x => absPowMinusTwo γBar (u x) * u x

/-- **Gateaux coefficient on the gradient** `g`:
`bGat i x = |Du x|^{γ̄−2} · Du i x`. -/
noncomputable def gatCoeffB
    (γBar : ℝ) (Du : Fin d → (Fin d → ℝ) → ℝ) :
    Fin d → ((Fin d → ℝ) → ℝ) :=
  fun i x => vecAbsPowMinusTwo γBar (fun j => Du j x) * Du i x

/-- **Flux integrand = Hölder pairing.** Pointwise, `transportFluxIntegrand`
equals the pairing integrand `aFlux·f + ∑ᵢ bFluxᵢ·gᵢ` for a smooth test pair
`(φ, ∂φ)`. The proof expands the `dotProduct` sum and distributes. -/
theorem fluxIntegrand_eq_pairing
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (m : (Fin d → ℝ) → ℝ) (Du : Fin d → (Fin d → ℝ) → ℝ)
    (φ : SmoothPeriodic d) (x : Fin d → ℝ) :
    transportFluxIntegrand DpH Du m φ x
      = fluxCoeffA m x * (φ : (Fin d → ℝ) → ℝ) x
        + ∑ i : Fin d, fluxCoeffB DpH m Du i x *
            ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) x := by
  classical
  unfold transportFluxIntegrand fluxCoeffA fluxCoeffB
  simp only [dotProduct, Finset.mul_sum]
  ring

/-- **Gateaux integrand = Hölder pairing.** Pointwise, `transportGateauxIntegrand`
equals the pairing integrand `aGat·f + ∑ᵢ bGatᵢ·gᵢ`. -/
theorem gatIntegrand_eq_pairing
    (γBar : ℝ) (u : (Fin d → ℝ) → ℝ) (Du : Fin d → (Fin d → ℝ) → ℝ)
    (φ : SmoothPeriodic d) (x : Fin d → ℝ) :
    transportGateauxIntegrand γBar Du u φ x
      = gatCoeffA γBar u x * (φ : (Fin d → ℝ) → ℝ) x
        + ∑ i : Fin d, gatCoeffB γBar Du i x *
            ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) x := by
  classical
  unfold transportGateauxIntegrand gatCoeffA gatCoeffB
  simp only [dotProduct, Finset.mul_sum]
  ring

/-- **Flux integral = `transportFunctional`.** Under Hölder membership of the
flux coefficients (`q`) and the smooth test pair (`q'`), the flux integral
equals `transportFunctional aFlux bFlux φ ∂φ` (and the integrand is integrable on
the cube). -/
theorem fluxIntegral_eq_transportFunctional
    {p q : ℝ≥0∞} [ENNReal.HolderTriple p q 1]
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (m : (Fin d → ℝ) → ℝ) (Du : Fin d → (Fin d → ℝ) → ℝ)
    (haF : MemLpPer q (fluxCoeffA m))
    (hbF : ∀ i, MemLpPer q (fluxCoeffB DpH m Du i))
    (φ : SmoothPeriodic d) :
    (∫ x in UnitCube d, transportFluxIntegrand DpH Du m φ x
        ∂(volume : Measure (Fin d → ℝ)))
      = Periodic.transportFunctional (fluxCoeffA m) (fluxCoeffB DpH m Du)
          (φ : (Fin d → ℝ) → ℝ)
          (fun i => ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ)) := by
  have hφ_lp : MemLpPer p (φ : (Fin d → ℝ) → ℝ) :=
    (MemSobolevPer.of_smoothPeriodic p φ).1
  have hφ_partial_lp : ∀ i, MemLpPer p
      ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
        (Fin d → ℝ) → ℝ) := fun i =>
    (MemSobolevPer.of_smoothPeriodic p (SmoothPeriodic.partialDeriv i φ)).1
  rw [← Periodic.periodicIntegral_combined_eq_transportFunctional
        (p := p) (q := q) haF hbF hφ_lp hφ_partial_lp]
  refine setIntegral_congr_fun measurableSet_unitCube ?_
  intro x _
  exact fluxIntegrand_eq_pairing DpH m Du φ x

/-- **Gateaux integral = `transportFunctional`.** Under Hölder membership of the
Gateaux coefficients (`q`) and the smooth test pair (`q'`), the Gateaux integral
equals `transportFunctional aGat bGat φ ∂φ`. -/
theorem gatIntegral_eq_transportFunctional
    {p q : ℝ≥0∞} [ENNReal.HolderTriple p q 1]
    (γBar : ℝ) (u : (Fin d → ℝ) → ℝ) (Du : Fin d → (Fin d → ℝ) → ℝ)
    (haG : MemLpPer q (gatCoeffA γBar u))
    (hbG : ∀ i, MemLpPer q (gatCoeffB γBar Du i))
    (φ : SmoothPeriodic d) :
    (∫ x in UnitCube d, transportGateauxIntegrand γBar Du u φ x
        ∂(volume : Measure (Fin d → ℝ)))
      = Periodic.transportFunctional (gatCoeffA γBar u) (gatCoeffB γBar Du)
          (φ : (Fin d → ℝ) → ℝ)
          (fun i => ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ)) := by
  have hφ_lp : MemLpPer p (φ : (Fin d → ℝ) → ℝ) :=
    (MemSobolevPer.of_smoothPeriodic p φ).1
  have hφ_partial_lp : ∀ i, MemLpPer p
      ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
        (Fin d → ℝ) → ℝ) := fun i =>
    (MemSobolevPer.of_smoothPeriodic p (SmoothPeriodic.partialDeriv i φ)).1
  rw [← Periodic.periodicIntegral_combined_eq_transportFunctional
        (p := p) (q := q) haG hbG hφ_lp hφ_partial_lp]
  refine setIntegral_congr_fun measurableSet_unitCube ?_
  intro x _
  exact gatIntegrand_eq_pairing γBar u Du φ x

/-- **`transportFunctional` is additive in its coefficients.**
`Λ(a₁+a₂, b₁+b₂; f, g) = Λ(a₁, b₁; f, g) + Λ(a₂, b₂; f, g)`, provided each
coefficient pairing is integrable on the cube (Hölder). -/
theorem transportFunctional_coeff_add
    {p q : ℝ≥0∞} [ENNReal.HolderTriple p q 1]
    {a₁ a₂ : (Fin d → ℝ) → ℝ} {b₁ b₂ : Fin d → ((Fin d → ℝ) → ℝ)}
    (ha₁ : MemLpPer q a₁) (ha₂ : MemLpPer q a₂)
    (hb₁ : ∀ i, MemLpPer q (b₁ i)) (hb₂ : ∀ i, MemLpPer q (b₂ i))
    {f : (Fin d → ℝ) → ℝ} {g : Fin d → ((Fin d → ℝ) → ℝ)}
    (hf : MemLpPer p f) (hg : ∀ i, MemLpPer p (g i)) :
    Periodic.transportFunctional (fun x => a₁ x + a₂ x)
        (fun i x => b₁ i x + b₂ i x) f g
      = Periodic.transportFunctional a₁ b₁ f g
        + Periodic.transportFunctional a₂ b₂ f g := by
  classical
  unfold Periodic.transportFunctional Periodic.periodicIntegral
  -- Each pairing integrable on the cube.
  have hint_a₁f : IntegrableOn (fun x => a₁ x * f x) (UnitCube d)
      (volume : Measure (Fin d → ℝ)) :=
    MeasureTheory.MemLp.integrable_mul ha₁.toMemLp hf.toMemLp
  have hint_a₂f : IntegrableOn (fun x => a₂ x * f x) (UnitCube d)
      (volume : Measure (Fin d → ℝ)) :=
    MeasureTheory.MemLp.integrable_mul ha₂.toMemLp hf.toMemLp
  have hint_b₁g : ∀ i, IntegrableOn (fun x => b₁ i x * g i x) (UnitCube d)
      (volume : Measure (Fin d → ℝ)) := fun i =>
    MeasureTheory.MemLp.integrable_mul (hb₁ i).toMemLp (hg i).toMemLp
  have hint_b₂g : ∀ i, IntegrableOn (fun x => b₂ i x * g i x) (UnitCube d)
      (volume : Measure (Fin d → ℝ)) := fun i =>
    MeasureTheory.MemLp.integrable_mul (hb₂ i).toMemLp (hg i).toMemLp
  -- Function pairing: `(a₁+a₂)·f = a₁·f + a₂·f`, split by `integral_add`.
  have hAf :
      (∫ x in UnitCube d, (a₁ x + a₂ x) * f x
          ∂(volume : Measure (Fin d → ℝ)))
        = (∫ x in UnitCube d, a₁ x * f x ∂(volume : Measure (Fin d → ℝ)))
          + ∫ x in UnitCube d, a₂ x * f x ∂(volume : Measure (Fin d → ℝ)) := by
    rw [← MeasureTheory.integral_add hint_a₁f hint_a₂f]
    refine setIntegral_congr_fun measurableSet_unitCube ?_
    intro x _; ring
  -- Each gradient pairing splits likewise.
  have hBg : ∀ i,
      (∫ x in UnitCube d, (b₁ i x + b₂ i x) * g i x
          ∂(volume : Measure (Fin d → ℝ)))
        = (∫ x in UnitCube d, b₁ i x * g i x ∂(volume : Measure (Fin d → ℝ)))
          + ∫ x in UnitCube d, b₂ i x * g i x
              ∂(volume : Measure (Fin d → ℝ)) := by
    intro i
    rw [← MeasureTheory.integral_add (hint_b₁g i) (hint_b₂g i)]
    refine setIntegral_congr_fun measurableSet_unitCube ?_
    intro x _; ring
  rw [hAf]
  rw [Finset.sum_congr rfl (fun i _ => hBg i), Finset.sum_add_distrib]
  ring

/-- **Transport functional at smooth test functions vanishes.** Repackages the
smooth-test transport equality (the conclusion of `Hdelta_strong_transport_eq`)
as the vanishing of `transportFunctional a b φ ∂φ` for every smooth periodic `φ`,
where `a = aFlux + ε·aGat`, `b = bFlux + ε·bGat` are the canonical §1b
coefficients. Ready to feed the `W^{1,γ̄}`-density keystone. -/
theorem transportFunctional_smooth_zero_of_transport_eq
    {p q : ℝ≥0∞} [ENNReal.HolderTriple p q 1]
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (γBar ε : ℝ) (m u : (Fin d → ℝ) → ℝ) (Du : Fin d → (Fin d → ℝ) → ℝ)
    (hTransport : ∀ φ : SmoothPeriodic d,
      (∫ x in UnitCube d, transportFluxIntegrand DpH Du m φ x
          ∂(volume : Measure (Fin d → ℝ))) +
        ε * ∫ x in UnitCube d, transportGateauxIntegrand γBar Du u φ x
              ∂(volume : Measure (Fin d → ℝ)) = 0)
    (haF : MemLpPer q (fluxCoeffA m))
    (hbF : ∀ i, MemLpPer q (fluxCoeffB DpH m Du i))
    (haG : MemLpPer q (gatCoeffA γBar u))
    (hbG : ∀ i, MemLpPer q (gatCoeffB γBar Du i)) :
    ∀ φ : SmoothPeriodic d,
      Periodic.transportFunctional
        (fun x => fluxCoeffA m x + ε * gatCoeffA γBar u x)
        (fun i x => fluxCoeffB DpH m Du i x + ε * gatCoeffB γBar Du i x)
        (φ : (Fin d → ℝ) → ℝ)
        (fun i => ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
          (Fin d → ℝ) → ℝ)) = 0 := by
  classical
  intro φ
  have hφ_lp : MemLpPer p (φ : (Fin d → ℝ) → ℝ) :=
    (MemSobolevPer.of_smoothPeriodic p φ).1
  have hφ_partial_lp : ∀ i, MemLpPer p
      ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
        (Fin d → ℝ) → ℝ) := fun i =>
    (MemSobolevPer.of_smoothPeriodic p (SmoothPeriodic.partialDeriv i φ)).1
  -- `ε·aGat`, `ε·bGat` memberships.
  have haGε : MemLpPer q (fun x => ε * gatCoeffA γBar u x) := by
    have h := MemLpPer.const_smul (c := ε) haG
    have heq : (ε • gatCoeffA γBar u : (Fin d → ℝ) → ℝ)
        = fun x => ε * gatCoeffA γBar u x := by
      funext x; change ε • _ = ε * _; simp [smul_eq_mul]
    rwa [heq] at h
  have hbGε : ∀ i, MemLpPer q (fun x => ε * gatCoeffB γBar Du i x) := by
    intro i
    have h := MemLpPer.const_smul (c := ε) (hbG i)
    have heq : (ε • gatCoeffB γBar Du i : (Fin d → ℝ) → ℝ)
        = fun x => ε * gatCoeffB γBar Du i x := by
      funext x; change ε • _ = ε * _; simp [smul_eq_mul]
    rwa [heq] at h
  -- Additivity: `Λ(aFlux + ε·aGat, …) = Λ(aFlux, bFlux) + Λ(ε·aGat, ε·bGat)`.
  rw [transportFunctional_coeff_add (p := p) (q := q)
        haF haGε hbF hbGε hφ_lp hφ_partial_lp]
  -- `Λ(ε·aGat, ε·bGat; φ, ∂φ) = ε · Λ(aGat, bGat; φ, ∂φ)`.
  have hScale :
      Periodic.transportFunctional (fun x => ε * gatCoeffA γBar u x)
          (fun i x => ε * gatCoeffB γBar Du i x)
          (φ : (Fin d → ℝ) → ℝ)
          (fun i => ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ))
        = ε * Periodic.transportFunctional (gatCoeffA γBar u) (gatCoeffB γBar Du)
            (φ : (Fin d → ℝ) → ℝ)
            (fun i => ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ)) := by
    unfold Periodic.transportFunctional Periodic.periodicIntegral
    rw [mul_add, Finset.mul_sum]
    congr 1
    · rw [← MeasureTheory.integral_const_mul]
      refine setIntegral_congr_fun measurableSet_unitCube ?_
      intro x _; ring
    · refine Finset.sum_congr rfl ?_
      intro i _
      rw [← MeasureTheory.integral_const_mul]
      refine setIntegral_congr_fun measurableSet_unitCube ?_
      intro x _; ring
  rw [hScale]
  -- Bridge each integral to a `transportFunctional` and apply `hTransport`.
  have hFlux := fluxIntegral_eq_transportFunctional (p := p) (q := q)
    DpH m Du haF hbF φ
  have hGat := gatIntegral_eq_transportFunctional (p := p) (q := q)
    γBar u Du haG hbG φ
  rw [← hFlux, ← hGat]
  exact hTransport φ

/-- **D6c-2 transport half tested at `φ = u_ε` (`AEPeriodicRep` form).**

Testing the regularised transport equation at the **non-smooth** solution
`u_ε ∈ W^{1,γ̄}_per`: the §1b periodicity /
local-integrability / measurability of the (non-smooth) test pair `(u, Du)` is
supplied through the `AEPeriodicRep` layer (`hu_rep`, `hDu_rep`) rather than
literal pointwise `IsPeriodic`. This is the entry point used by the T3
strong-VI family, whose `u`/`Du` are `Lp.coeFn` representatives carrying only
`AEPeriodicRep` (sourced from `MemLpPer` via
`Periodic.aePeriodicRepOfMemLpPer`).

The density / limit passage routes through
`Periodic.integralIdentity_extend_to_W1gamma_via_smooth_density_AEPeriodicRep`,
which builds the periodic representatives internally and transports the
`transportFunctional` conclusion back to `(u, Du)` by `integral_congr_ae`. -/
theorem transportAtU_of_smoothTransport_AEPeriodicRep
    {p q : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    [ENNReal.HolderTriple p q 1]
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (γBar ε : ℝ) (m u : (Fin d → ℝ) → ℝ) (Du : Fin d → (Fin d → ℝ) → ℝ)
    (hTransport : ∀ φ : SmoothPeriodic d,
      (∫ x in UnitCube d, transportFluxIntegrand DpH Du m φ x
          ∂(volume : Measure (Fin d → ℝ))) +
        ε * ∫ x in UnitCube d, transportGateauxIntegrand γBar Du u φ x
              ∂(volume : Measure (Fin d → ℝ)) = 0)
    (haF : MemLpPer q (fluxCoeffA m))
    (hbF : ∀ i, MemLpPer q (fluxCoeffB DpH m Du i))
    (haG : MemLpPer q (gatCoeffA γBar u))
    (hbG : ∀ i, MemLpPer q (gatCoeffB γBar Du i))
    -- §1b regularity of `(u, Du)` via the `AEPeriodicRep` layer.
    (hu_lp : MemLpPer p u)
    (hu_rep : Periodic.AEPeriodicRep u)
    (hDu_weak : ∀ i, HasWeakDerivPer i u (Du i))
    (hDu_lp : ∀ i, MemLpPer p (Du i))
    (hDu_rep : ∀ i, Periodic.AEPeriodicRep (Du i)) :
    Periodic.transportFunctional
        (fun x => fluxCoeffA m x + ε * gatCoeffA γBar u x)
        (fun i x => fluxCoeffB DpH m Du i x + ε * gatCoeffB γBar Du i x)
        u Du = 0 := by
  -- Combined coefficient memberships for the density keystone.
  have haGε : MemLpPer q (fun x => ε * gatCoeffA γBar u x) := by
    have h := MemLpPer.const_smul (c := ε) haG
    have heq : (ε • gatCoeffA γBar u : (Fin d → ℝ) → ℝ)
        = fun x => ε * gatCoeffA γBar u x := by
      funext x; change ε • _ = ε * _; simp [smul_eq_mul]
    rwa [heq] at h
  have hbGε : ∀ i, MemLpPer q (fun x => ε * gatCoeffB γBar Du i x) := by
    intro i
    have h := MemLpPer.const_smul (c := ε) (hbG i)
    have heq : (ε • gatCoeffB γBar Du i : (Fin d → ℝ) → ℝ)
        = fun x => ε * gatCoeffB γBar Du i x := by
      funext x; change ε • _ = ε * _; simp [smul_eq_mul]
    rwa [heq] at h
  have haSum : MemLpPer q (fun x => fluxCoeffA m x + ε * gatCoeffA γBar u x) := by
    have h := MemLpPer.add haF haGε
    have heq : (fluxCoeffA m + fun x => ε * gatCoeffA γBar u x
                  : (Fin d → ℝ) → ℝ)
        = fun x => fluxCoeffA m x + ε * gatCoeffA γBar u x := rfl
    rwa [← heq];
  have hbSum : ∀ i, MemLpPer q
      (fun x => fluxCoeffB DpH m Du i x + ε * gatCoeffB γBar Du i x) := by
    intro i
    have h := MemLpPer.add (hbF i) (hbGε i)
    have heq : (fluxCoeffB DpH m Du i + fun x => ε * gatCoeffB γBar Du i x
                  : (Fin d → ℝ) → ℝ)
        = fun x => fluxCoeffB DpH m Du i x + ε * gatCoeffB γBar Du i x := rfl
    rwa [← heq]
  -- Smooth-test vanishing of the combined transport functional.
  have hSmooth := transportFunctional_smooth_zero_of_transport_eq
    (p := p) (q := q) DpH γBar ε m u Du hTransport haF hbF haG hbG
  -- Density / limit passage to `(u, Du)` via the `AEPeriodicRep` route.
  exact Periodic.integralIdentity_extend_to_W1gamma_via_smooth_density_AEPeriodicRep
    (p := p) (q := q) hp hp_top haSum hbSum
    hu_lp hu_rep hDu_weak hDu_lp hDu_rep hSmooth

/-! ## D6d: operator-continuity (`hContRaw`) for the strong-VI family

This producer derives the operator-continuity `Tendsto` along the Minty
INDICATOR perturbation — the `hContRaw` loose binder of
`T3RegularizedSideData.of_family` — **internally** from `fam` and the
closed-cone (`K₀`) hemicontinuity machinery, so `hContRaw` need no longer be
a public binder.

The perturbation direction here is the SET / density direction: the density
moves as `μ_n := fam.m ε + (1/(n+1))·1_S → fam.m ε` with the gradient and
value slots fixed. This is exactly the closed-cone density segment
`cxComb (fam.m ε + 1_S) (fam.m ε) t` at `t_n := 1/(n+1) → 0`
(`cxComb (m+1_S) m t = (1-t)·m + t·(m+1_S) = m + t·1_S`). Continuity of
`t ↦ ⟨A_ε[μ_t, u_ε], (1_S, 0, 0)⟩` on `[0,1]` is supplied by the
density-direction sibling `Aepsi_hemicontinuous_setSegment_K0`
(Hemicontinuity.lean), which needs only segment-nonnegativity
`0 ≤ cxComb (m+1_S) m t` (discharged from `fam.hmNonneg` and `1_S ≥ 0`) plus
the **closed-cone** regularity `hRegK0` on the genuine `HdeltaK0` carrier (from
`regularityHK0_Hdelta_of_selector`) and the per-`S` §1b standing-regularity
dominator/measurability bundle.

Crucially, this is where the D4b1 obstruction is lifted: the former D4b1
operator-continuity pass-through could not derive this because the open-cone
`RegularityH.continuous_H_pm` is `{0 < m}`-only, but on the positive-measure
set `{m ε = 0}` the limit density sits on the `m = 0` boundary. The
closed-cone `RegularityHK0` (which is continuous *across* `m = 0` via the
`JsimpleExt` flux and the canonical zero-mass trace) removes exactly that
obstruction, so the K0 DCT gives the Tendsto from `0 ≤ m ε` alone.

`fam` IS the only structure binder. The remaining binders are accepted §1b
standing-regularity / measurability carriers (`hRegK0`, the per-`S`
dominator/measurability bundle). No `hCont` (it is *produced*, not an input),
no `hPosSeg`, no `mε_pos`, no `HdeltaPos`, no Pack/Inputs/Oracle binder. -/
theorem hContRaw_of_T3RegularizedStrongFamily
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d) {βBarReal γBarReal : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    (fam : T3RegularizedStrongFamily V hweak qε βBarReal γBarReal)
    (hγ : 1 < γBarReal)
    -- Closed-cone regularity of the genuine `HdeltaK0` carrier (per `ε`).
    (hRegK0 : ∀ ε, 0 < ε → ε ≤ 1 →
      StationaryMFG.Theorems.SimplePower.RegularityHK0 (d := d)
        (HdeltaK0 hweak ε) (DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε))
    -- Per-`(ε, S)` set-segment dominator/measurability bundle (§1b
    -- standing-regularity inputs feeding the closed-cone DCT continuity).
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
            ≤ g_gat ε S x) :
    ∀ ε, 0 < ε → ε ≤ 1 →
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (volume.restrict (UnitCube d)) S < ∞ →
        Filter.Tendsto
          (fun n : ℕ =>
            mfgOperatorEpsPair (V := V) (H := HdeltaK0 hweak ε)
              (DpH := DpHepsilonFam hweak qε ε)
              γBarReal ε (fam.Du ε)
              (fun x => fam.m ε x + (1 / ((n : ℝ) + 1)) *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              (fam.u ε)
              (fun _ _ => (0 : ℝ))
              (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)))
              (fun _ => (0 : ℝ)))
          Filter.atTop
          (𝓝 (mfgOperatorEpsPair (V := V) (H := HdeltaK0 hweak ε)
                (DpH := DpHepsilonFam hweak qε ε)
                γBarReal ε (fam.Du ε) (fam.m ε) (fam.u ε)
                (fun _ _ => (0 : ℝ))
                (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)))
                (fun _ => (0 : ℝ)))) := by
  intro ε hε hε1ε S _hSmeas _hSfin
  -- Closed-cone density-segment continuity on `[0,1]`. The density endpoints
  -- are `μ := fam.m ε + 1_S` and `mBar := fam.m ε`; the gradient/value slots
  -- are constant (`Dυ = Dῡ = fam.Du ε`, `υ = ῡ = fam.u ε`).
  have hcts :
      ContinuousOn (fun t : ℝ =>
          mfgOperatorEpsPair (V := V) (H := HdeltaK0 hweak ε)
            (DpH := DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε) γBarReal ε
            (fun i x => cxCombGrad (fam.Du ε) (fam.Du ε) t i x)
            (fun x => cxComb
              (fun x => fam.m ε x +
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              (fam.m ε) t x)
            (fun x => cxComb (fam.u ε) (fam.u ε) t x)
            (fun _ _ => (0 : ℝ))
            (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)))
            (fun _ => (0 : ℝ))) (Set.Icc 0 1) :=
    Aepsi_hemicontinuous_setSegment_K0 (d := d)
      V (HdeltaK0 hweak ε)
      (DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε) (hRegK0 ε hε hε1ε)
      γBarReal ε hγ
      (fam.Du ε) (fam.Du ε)
      (fun x => fam.m ε x + S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
      (fam.m ε) (fam.u ε) (fam.u ε)
      (fun _ _ => (0 : ℝ))
      (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)))
      (fun _ => (0 : ℝ))
      (by
        -- Segment nonnegativity: `cxComb (m+1_S) m t x = m + t·1_S ≥ 0`.
        filter_upwards [fam.hmNonneg ε hε hε1ε] with x hx t ht
        have hindic : (0 : ℝ) ≤
            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x :=
          Set.indicator_nonneg (fun _ _ => zero_le_one) x
        have ht0 : (0 : ℝ) ≤ t := ht.1
        -- `cxComb (m+1_S) m t x = (1 - t)·m + t·(m + 1_S)`.
        simp only [cxComb]
        have hexpand :
            (1 - t) * fam.m ε x
              + t * (fam.m ε x +
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              = fam.m ε x
                + t * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
          ring
        rw [hexpand]
        have : (0 : ℝ) ≤
            t * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x :=
          mul_nonneg ht0 hindic
        linarith)
      (g_unreg ε S) (g_gat ε S)
      (hg_unreg_int ε hε hε1ε S) (hg_gat_int ε hε hε1ε S)
      (hF_unreg_meas ε hε hε1ε S _hSmeas) (hF_unreg_bound ε hε hε1ε S)
      (hF_gat_meas ε hε hε1ε S) (hF_gat_bound ε hε hε1ε S)
  -- Convert the `[0,1]`-continuity to the `n → ∞` Tendsto along `t_n`.
  set F : ℝ → ℝ := fun t =>
      mfgOperatorEpsPair (V := V) (H := HdeltaK0 hweak ε)
        (DpH := DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε) γBarReal ε
        (fun i x => cxCombGrad (fam.Du ε) (fam.Du ε) t i x)
        (fun x => cxComb
          (fun x => fam.m ε x +
            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          (fam.m ε) t x)
        (fun x => cxComb (fam.u ε) (fam.u ε) t x)
        (fun _ _ => (0 : ℝ))
        (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)))
        (fun _ => (0 : ℝ)) with hF_def
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_refl _, zero_le_one⟩
  have hcwa : ContinuousWithinAt F (Set.Icc 0 1) 0 := hcts.continuousWithinAt h0mem
  have htn_tendsto :
      Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        Filter.atTop (𝓝[Set.Icc 0 1] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    · refine Filter.Eventually.of_forall ?_
      intro n
      have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      refine ⟨le_of_lt (div_pos one_pos hpos), ?_⟩
      rw [div_le_one hpos]
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
  have hcomp :
      Filter.Tendsto (fun n : ℕ => F ((1 : ℝ) / ((n : ℝ) + 1)))
        Filter.atTop (𝓝 (F 0)) :=
    hcwa.tendsto.comp htn_tendsto
  -- Rewrite `F (t_n)` to the perturbed pairing and `F 0` to the base.
  have hFn_eq : ∀ n : ℕ,
      F ((1 : ℝ) / ((n : ℝ) + 1))
        = mfgOperatorEpsPair (V := V) (H := HdeltaK0 hweak ε)
            (DpH := DpHepsilonFam hweak qε ε) γBarReal ε (fam.Du ε)
            (fun x => fam.m ε x + (1 / ((n : ℝ) + 1)) *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
            (fam.u ε)
            (fun _ _ => (0 : ℝ))
            (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)))
            (fun _ => (0 : ℝ)) := by
    intro n
    simp only [hF_def]
    congr 1
    · funext i x; simp only [cxCombGrad]; ring
    · funext x; simp only [cxComb]; ring
    · funext x; simp only [cxComb]; ring
  have hF0_eq :
      F 0 = mfgOperatorEpsPair (V := V) (H := HdeltaK0 hweak ε)
              (DpH := DpHepsilonFam hweak qε ε) γBarReal ε (fam.Du ε)
              (fam.m ε) (fam.u ε)
              (fun _ _ => (0 : ℝ))
              (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)))
              (fun _ => (0 : ℝ)) := by
    simp only [hF_def]
    congr 1
    · funext i x; simp only [cxCombGrad]; ring
    · funext x; simp only [cxComb]; ring
    · funext x; simp only [cxComb]; ring
  rw [hF0_eq] at hcomp
  refine hcomp.congr ?_
  intro n; exact hFn_eq n

/-! ## D6c-2a-2d: transport capstone for the strong-VI family

This capstone assembles the *transport half* of the §1b identity
`eq:appositiveum` (paper line 1212) at the **family members**
`(fam.m ε, fam.u ε, fam.Du ε)`, as the vanishing of the canonical transport
functional
```
transportFunctional (aFlux + ε·aGat) (bFlux + ε·bGat) (fam.u ε) (fam.Du ε) = 0.
```

It is the trivial three-step composition required by D6c3:

1. `strongVI_transportForm_K0_of_IsStrongVI_Aepsi` (D6c2a2c) builds the
   transport-form strong VI on the **genuine** `HdeltaK0 hweak ε` carrier from
   `fam.hVI ε hεpos`, with the operator-continuity certificate discharged
   internally through the closed-cone (`K₀`) hemicontinuity machinery — so no
   `hCont` binder and no strict positivity.
2. `Hdelta_strong_transport_eq` (StrongIsStrong.lean) turns the transport-form
   VI into the smooth-test transport equality, valid for every
   `φ : SmoothPeriodic d`.
3. `transportAtU_of_smoothTransport_AEPeriodicRep` (the D6c2 density capstone)
   passes the smooth-test identity to the limit `φ → u_ε` and delivers
   `transportFunctional … (fam.u ε) (fam.Du ε) = 0`.

`fam` IS the only structure binder. The remaining binders are accepted §1b
standing-regularity / measurability carriers (`hRegK0`, the per-`(σ, φ)`
dominator/measurability bundle of step 1, the Hölder-conjugate coefficient
memberships of step 3, and the standing regularity of the test pair
`(fam.u ε, fam.Du ε)`). No `hCont`, no `hPosSeg`, no `mε_pos`, no `HdeltaPos`,
no Pack/Inputs/Oracle binder. -/
theorem hTransportAtU_of_T3RegularizedStrongFamily
    {bb gb : ℝ≥0∞}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d) {βBarReal γBarReal : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    (fam : T3RegularizedStrongFamily V hweak qε βBarReal γBarReal)
    (ε : ℝ) (hεpos : 0 < ε) (hε1 : ε ≤ 1) (hγ : 1 < γBarReal)
    {p q : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    [ENNReal.HolderTriple p q 1]
    -- bb / gb pin the `IsStrongVI_Aepsi` exponents of `fam.hVI`.
    (hbb : bb = ENNReal.ofReal βBarReal) (hgb : gb = ENNReal.ofReal γBarReal)
    -- Closed-cone regularity of the genuine `HdeltaK0` carrier (D6c2a2b/c).
    (hRegK0 :
      StationaryMFG.Theorems.SimplePower.RegularityHK0 (d := d)
        (HdeltaK0 hweak ε) (DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε))
    -- `1`-integrability of `u ε` (needed by the K0 transport-form bridge).
    (hu1 : MemLpPer (d := d) 1 (fam.u ε))
    -- Smooth periodics are γ̄-integrable (test-data regularity for step 1).
    (hSmoothLp :
      ∀ (ψ : SmoothPeriodic d),
        MemLpPer (ENNReal.ofReal γBarReal) ((ψ : (Fin d → ℝ) → ℝ)))
    -- Per-`(σ, φ)` transport-segment dominator/measurability bundle (§1b
    -- standing-regularity inputs feeding the closed-cone DCT continuity).
    (g_unreg g_gat :
      (σ : ℝ) → (φ : SmoothPeriodic d) → (Fin d → ℝ) → ℝ)
    (hg_unreg_int :
      ∀ (σ : ℝ) (φ : SmoothPeriodic d),
        IntegrableOn (g_unreg σ φ) (UnitCube d))
    (hg_gat_int :
      ∀ (σ : ℝ) (φ : SmoothPeriodic d),
        IntegrableOn (g_gat σ φ) (UnitCube d))
    (hF_unreg_meas :
      ∀ (σ : ℝ) (φ : SmoothPeriodic d), ∀ t ∈ Set.Icc (0 : ℝ) 1,
        AEStronglyMeasurable
          (fun x =>
            aepsiIntegrandAt_unreg_K0 (d := d) V (HdeltaK0 hweak ε)
              (DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε)
              (fun i x => fam.Du ε i x + σ *
                ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x)
              (fam.Du ε) (fam.m ε) (fam.m ε)
              (fun x => fam.u ε x + σ * (φ : (Fin d → ℝ) → ℝ) x) (fam.u ε)
              (fun i x => σ *
                ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x)
              (fun _ => (0 : ℝ))
              (fun x => σ * (φ : (Fin d → ℝ) → ℝ) x) x t)
          (volume.restrict (UnitCube d)))
    (hF_unreg_bound :
      ∀ (σ : ℝ) (φ : SmoothPeriodic d), ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          ‖aepsiIntegrandAt_unreg_K0 (d := d) V (HdeltaK0 hweak ε)
              (DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε)
              (fun i x => fam.Du ε i x + σ *
                ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x)
              (fam.Du ε) (fam.m ε) (fam.m ε)
              (fun x => fam.u ε x + σ * (φ : (Fin d → ℝ) → ℝ) x) (fam.u ε)
              (fun i x => σ *
                ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x)
              (fun _ => (0 : ℝ))
              (fun x => σ * (φ : (Fin d → ℝ) → ℝ) x) x t‖
            ≤ g_unreg σ φ x)
    (hF_gat_meas :
      ∀ (σ : ℝ) (φ : SmoothPeriodic d), ∀ t ∈ Set.Icc (0 : ℝ) 1,
        AEStronglyMeasurable
          (fun x =>
            aepsiIntegrandAt_gateaux (d := d) γBarReal
              (fun i x => fam.Du ε i x + σ *
                ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x)
              (fam.Du ε)
              (fun x => fam.u ε x + σ * (φ : (Fin d → ℝ) → ℝ) x) (fam.u ε)
              (fun i x => σ *
                ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x)
              (fun x => σ * (φ : (Fin d → ℝ) → ℝ) x) x t)
          (volume.restrict (UnitCube d)))
    (hF_gat_bound :
      ∀ (σ : ℝ) (φ : SmoothPeriodic d), ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          ‖aepsiIntegrandAt_gateaux (d := d) γBarReal
              (fun i x => fam.Du ε i x + σ *
                ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x)
              (fam.Du ε)
              (fun x => fam.u ε x + σ * (φ : (Fin d → ℝ) → ℝ) x) (fam.u ε)
              (fun i x => σ *
                ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x)
              (fun x => σ * (φ : (Fin d → ℝ) → ℝ) x) x t‖
            ≤ g_gat σ φ x)
    -- Canonical Hölder-conjugate coefficient memberships (step 3, §1b).
    (haF : MemLpPer q (fluxCoeffA (fam.m ε)))
    (hbF : ∀ i, MemLpPer q
            (fluxCoeffB (DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε)
              (fam.m ε) (fam.Du ε) i))
    (haG : MemLpPer q (gatCoeffA γBarReal (fam.u ε)))
    (hbG : ∀ i, MemLpPer q (gatCoeffB γBarReal (fam.Du ε) i))
    -- Standing regularity of the (non-smooth) test pair `φ = u_ε`.
    -- Periodicity flows through the `AEPeriodicRep` layer (sourced from
    -- `MemLpPer` via `Periodic.aePeriodicRepOfMemLpPer`), NOT literal
    -- pointwise `IsPeriodic` of the `Lp.coeFn` representatives `fam.u`/`fam.Du`.
    (hu_lp : MemLpPer p (fam.u ε))
    (hDu_lp : ∀ i, MemLpPer p (fam.Du ε i)) :
    Periodic.transportFunctional
        (fun x => fluxCoeffA (fam.m ε) x + ε * gatCoeffA γBarReal (fam.u ε) x)
        (fun i x =>
          fluxCoeffB (DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε)
            (fam.m ε) (fam.Du ε) i x
            + ε * gatCoeffB γBarReal (fam.Du ε) i x)
        (fam.u ε) (fam.Du ε) = 0 := by
  -- Step 1: transport-form strong VI on the genuine `HdeltaK0` carrier, with
  -- the operator continuity discharged internally (K0 hemicontinuity).
  have hSob := fam.huSob ε hεpos hε1
  have hTF :
      StrongVI_transportForm V (HdeltaK0 hweak ε)
        (DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε)
        γBarReal ε (fam.Du ε) (fam.m ε) (fam.u ε) :=
    strongVI_transportForm_K0_of_IsStrongVI_Aepsi
      (bb := bb) (gb := gb) hweak qε hγ hRegK0
      (by
        -- `fam.hVI` carries the `(ofReal βBarReal, ofReal γBarReal)` exponents.
        have h := fam.hVI ε hεpos hε1
        rw [hbb, hgb]; exact h)
      (fam.hmNonneg ε hεpos hε1) (by rw [hbb]; exact fam.hmLp ε hεpos hε1)
      (by rw [hgb]; exact hSob) hu1
      (fun i => by rw [hgb]; exact fam.hDuLp ε hεpos hε1 i)
      (fam.hDuWeak ε hεpos hε1) (fun ψ => by rw [hgb]; exact hSmoothLp ψ)
      g_unreg g_gat hg_unreg_int hg_gat_int
      hF_unreg_meas hF_unreg_bound hF_gat_meas hF_gat_bound
  -- Step 2: smooth-test transport equality for every smooth periodic `φ`.
  have hTransport :=
    Hdelta_strong_transport_eq hweak V
      (DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε)
      γBarReal ε (fam.Du ε) (fam.m ε) (fam.u ε) hTF
  -- Step 3: density / limit passage to `φ = u_ε`, with periodicity sourced
  -- from `MemLpPer` via the `AEPeriodicRep` layer (no literal `IsPeriodic`).
  exact transportAtU_of_smoothTransport_AEPeriodicRep
    (p := p) (q := q) hp hp_top
    (DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε)
    γBarReal ε (fam.m ε) (fam.u ε) (fam.Du ε)
    hTransport haF hbF haG hbG
    hu_lp (Periodic.aePeriodicRepOfMemLpPer (d := d) hu_lp)
    (fam.hDuWeak ε hεpos hε1) hDu_lp
    (fun i => Periodic.aePeriodicRepOfMemLpPer (d := d) (hDu_lp i))

/-! ## D6c-3: the integrated §1b identity from the two halves

This section assembles the integrated §1b identity `eq:appositiveum`
(paper line 1212) from the two genuine halves produced above:

* the **HJB half** (D6c-1, `hHJBIntegrated_of_T3RegularizedStrongFamily`):
  `∫ (u_ε + H^ε(x, Du_ε, m_ε) − V) · m_ε = 0`;
* the **transport half** (D6c-2a-2d, `hTransportAtU_of_T3RegularizedStrongFamily`):
  `transportFunctional (aFlux + ε·aGat) (bFlux + ε·bGat) u_ε Du_ε = 0`.

The actual canonical ε-perturbation remainder produced by the transport
Gateaux term is the *Euclidean*-norm form
`ε · ((Du_ε ⬝ Du_ε)^{γ̄/2} + |u_ε|^{γ̄})` — the dot-product pairing
`vecAbsPowMinusTwo γ̄ Du · (Du ⬝ Du) = (Du ⬝ Du)^{γ̄/2}` is the Euclidean
norm to the `γ̄`-th power, *not* the sup-norm form. Per D6b's note, the
assembly uses this genuine (Euclidean) remainder `weakEpsTermsEucl`. -/

/-- **Canonical (Euclidean) T3 ε-perturbation remainder.**

The genuine additive ε-term delivered by the transport Gateaux pairing of the
integrated §1b identity, in its Euclidean form
`ε · ((Du x ⬝ Du x) ^ (γ̄/2) + |u x| ^ γ̄)`. The first summand is the Euclidean
norm `‖Du x‖₂ ^ γ̄` (via `vecAbsPowMinusTwo γ̄ (Du x) · (Du x ⬝ Du x) =
(Du x ⬝ Du x) ^ (γ̄/2)`), the second `|u x| ^ γ̄`. Both are non-negative for
`ε ≥ 0` (`weakEpsTermsEucl_nonneg`). This is the remainder appearing in
`hIdentityRaw_of_T3RegularizedStrongFamily`. -/
noncomputable def weakEpsTermsEucl (γBar ε : ℝ) (u : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ) : (Fin d → ℝ) → ℝ :=
  fun x => ε * (((fun i => Du i x) ⬝ (fun i => Du i x)) ^ (γBar / 2)
                  + |u x| ^ γBar)

/-- **Non-negativity of the canonical Euclidean ε-perturbation remainder.**
For `0 ≤ ε` the remainder `weakEpsTermsEucl` is pointwise non-negative:
`(Du⬝Du)^{γ̄/2}` is `Real.rpow` of the non-negative `dotProduct`-self, and
`|u|^γ̄` is `Real.rpow` of `|u| ≥ 0`; their sum scaled by `0 ≤ ε` stays
non-negative. Discharges the `hEpsNN`-style slot. -/
theorem weakEpsTermsEucl_nonneg (γBar ε : ℝ) (hε : 0 ≤ ε) (u : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    0 ≤ weakEpsTermsEucl γBar ε u Du x := by
  unfold weakEpsTermsEucl
  have hdot_nn : 0 ≤ (fun i => Du i x) ⬝ (fun i => Du i x) := by
    unfold dotProduct
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  exact mul_nonneg hε
    (add_nonneg
      (Real.rpow_nonneg hdot_nn _)
      (Real.rpow_nonneg (abs_nonneg _) _))

/-- **D6c-3: the integrated §1b identity `eq:appositiveum`** (paper line 1212).

For the produced strong-VI family `fam` and `ε > 0`, the integrated identity
```
∫ u_ε = ∫ (m_ε · (−H^ε(x, Du_ε, m_ε) + D_pH^ε(x, Du_ε, m_ε) ⬝ Du_ε)
            + V · m_ε + weakEpsTermsEucl γ̄ ε u_ε Du_ε)
```
holds, where `H^ε = HdeltaK0 hweak ε`, `D_pH^ε = DpHepsilonFam hweak qε ε`. This
is the `hIdentityRaw` shape consumed by `hIdentityRaw_of_family` /
`hIdentity_of_weakGrowth` (with the loose `epsTerms` slot instantiated to
the canonical Euclidean remainder).

The proof combines the two halves:

1. **Transport half** (`hTransportAtU_of_T3RegularizedStrongFamily`):
   `transportFunctional (aFlux + ε·aGat) (bFlux + ε·bGat) u_ε Du_ε = 0`, which —
   via the combined-integral bridge `periodicIntegral_combined_eq_transportFunctional`
   and the pointwise Gateaux rpow identities — says
   `∫ (m·u − u + m·(D_pH^ε ⬝ Du) + weakEpsTermsEucl) = 0`.
2. **HJB half** (`hHJBIntegrated_of_T3RegularizedStrongFamily`):
   `∫ (u + H^ε − V)·m = 0`, i.e. `∫ (m·u + m·H^ε − V·m) = 0`.

Subtracting (the transport combined integrand minus the HJB integrand equals
`−u + RHS`), and splitting the integral via integrability of `u`, the transport
pieces and the HJB residue, gives `∫ u = ∫ RHS`.

`fam` IS a binder. The remaining binders are the per-half accepted §1b
standing-regularity / measurability carriers threaded into the two halves. -/
theorem hIdentityRaw_of_T3RegularizedStrongFamily
    {bb gb : ℝ≥0∞}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d) {βBarReal γBarReal : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    (fam : T3RegularizedStrongFamily V hweak qε βBarReal γBarReal)
    (ε : ℝ) (hεpos : 0 < ε) (hε1 : ε ≤ 1) (hγ : 1 < γBarReal)
    {p q : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    [ENNReal.HolderTriple p q 1]
    (hbb : bb = ENNReal.ofReal βBarReal) (hgb : gb = ENNReal.ofReal γBarReal)
    -- HJB-half carriers (D6c-1).
    (hResM : Integrable
              (fun x => hjbResidual V (HdeltaK0 hweak ε) (fam.Du ε)
                          (fam.m ε) (fam.u ε) x * fam.m ε x)
              (volume.restrict (UnitCube d)))
    (hCont :
      ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (volume.restrict (UnitCube d)) S < ∞ →
        Filter.Tendsto
          (fun n : ℕ =>
            mfgOperatorEpsPair (V := V) (H := HdeltaK0 hweak ε)
              (DpH := DpHepsilonFam hweak qε ε)
              γBarReal ε
              (fam.Du ε)
              (fun x => fam.m ε x + (1 / ((n : ℝ) + 1)) *
                          (σ * fam.m ε x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
              (fam.u ε)
              (fun _ _ => (0 : ℝ))
              (fun x => σ * fam.m ε x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              (fun _ => (0 : ℝ)))
          Filter.atTop
          (𝓝 (mfgOperatorEpsPair (V := V) (H := HdeltaK0 hweak ε)
                (DpH := DpHepsilonFam hweak qε ε)
                γBarReal ε
                (fam.Du ε) (fam.m ε) (fam.u ε)
                (fun _ _ => (0 : ℝ))
                (fun x => σ * fam.m ε x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                (fun _ => (0 : ℝ)))))
    -- Transport-half carriers (D6c-2a-2d).
    (hRegK0 :
      StationaryMFG.Theorems.SimplePower.RegularityHK0 (d := d)
        (HdeltaK0 hweak ε) (DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε))
    (hu1 : MemLpPer (d := d) 1 (fam.u ε))
    (hSmoothLp :
      ∀ (ψ : SmoothPeriodic d),
        MemLpPer (ENNReal.ofReal γBarReal) ((ψ : (Fin d → ℝ) → ℝ)))
    (g_unreg g_gat :
      (σ : ℝ) → (φ : SmoothPeriodic d) → (Fin d → ℝ) → ℝ)
    (hg_unreg_int :
      ∀ (σ : ℝ) (φ : SmoothPeriodic d),
        IntegrableOn (g_unreg σ φ) (UnitCube d))
    (hg_gat_int :
      ∀ (σ : ℝ) (φ : SmoothPeriodic d),
        IntegrableOn (g_gat σ φ) (UnitCube d))
    (hF_unreg_meas :
      ∀ (σ : ℝ) (φ : SmoothPeriodic d), ∀ t ∈ Set.Icc (0 : ℝ) 1,
        AEStronglyMeasurable
          (fun x =>
            aepsiIntegrandAt_unreg_K0 (d := d) V (HdeltaK0 hweak ε)
              (DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε)
              (fun i x => fam.Du ε i x + σ *
                ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x)
              (fam.Du ε) (fam.m ε) (fam.m ε)
              (fun x => fam.u ε x + σ * (φ : (Fin d → ℝ) → ℝ) x) (fam.u ε)
              (fun i x => σ *
                ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x)
              (fun _ => (0 : ℝ))
              (fun x => σ * (φ : (Fin d → ℝ) → ℝ) x) x t)
          (volume.restrict (UnitCube d)))
    (hF_unreg_bound :
      ∀ (σ : ℝ) (φ : SmoothPeriodic d), ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          ‖aepsiIntegrandAt_unreg_K0 (d := d) V (HdeltaK0 hweak ε)
              (DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε)
              (fun i x => fam.Du ε i x + σ *
                ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x)
              (fam.Du ε) (fam.m ε) (fam.m ε)
              (fun x => fam.u ε x + σ * (φ : (Fin d → ℝ) → ℝ) x) (fam.u ε)
              (fun i x => σ *
                ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x)
              (fun _ => (0 : ℝ))
              (fun x => σ * (φ : (Fin d → ℝ) → ℝ) x) x t‖
            ≤ g_unreg σ φ x)
    (hF_gat_meas :
      ∀ (σ : ℝ) (φ : SmoothPeriodic d), ∀ t ∈ Set.Icc (0 : ℝ) 1,
        AEStronglyMeasurable
          (fun x =>
            aepsiIntegrandAt_gateaux (d := d) γBarReal
              (fun i x => fam.Du ε i x + σ *
                ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x)
              (fam.Du ε)
              (fun x => fam.u ε x + σ * (φ : (Fin d → ℝ) → ℝ) x) (fam.u ε)
              (fun i x => σ *
                ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x)
              (fun x => σ * (φ : (Fin d → ℝ) → ℝ) x) x t)
          (volume.restrict (UnitCube d)))
    (hF_gat_bound :
      ∀ (σ : ℝ) (φ : SmoothPeriodic d), ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          ‖aepsiIntegrandAt_gateaux (d := d) γBarReal
              (fun i x => fam.Du ε i x + σ *
                ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x)
              (fam.Du ε)
              (fun x => fam.u ε x + σ * (φ : (Fin d → ℝ) → ℝ) x) (fam.u ε)
              (fun i x => σ *
                ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x)
              (fun x => σ * (φ : (Fin d → ℝ) → ℝ) x) x t‖
            ≤ g_gat σ φ x)
    (haF : MemLpPer q (fluxCoeffA (fam.m ε)))
    (hbF : ∀ i, MemLpPer q
            (fluxCoeffB (DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε)
              (fam.m ε) (fam.Du ε) i))
    (haG : MemLpPer q (gatCoeffA γBarReal (fam.u ε)))
    (hbG : ∀ i, MemLpPer q (gatCoeffB γBarReal (fam.Du ε) i))
    -- Periodicity of the (non-smooth) test pair `φ = u_ε` flows through the
    -- `AEPeriodicRep` layer (`Periodic.aePeriodicRepOfMemLpPer` from `MemLpPer`),
    -- NOT literal pointwise `IsPeriodic` of the `Lp.coeFn` representatives.
    (hu_lp : MemLpPer p (fam.u ε))
    (hDu_lp : ∀ i, MemLpPer p (fam.Du ε i)) :
    ∫ x in UnitCube d, fam.u ε x ∂(volume : Measure (Fin d → ℝ)) =
      ∫ x in UnitCube d,
        (fam.m ε x * (-HdeltaK0 hweak ε x (fun i => fam.Du ε i x) (fam.m ε x)
                  + (DpHepsilonFam hweak qε ε x (fun i => fam.Du ε i x)
                        (fam.m ε x)) ⬝ (fun i => fam.Du ε i x))
          + V x * fam.m ε x
          + weakEpsTermsEucl γBarReal ε (fam.u ε) (fam.Du ε) x)
        ∂(volume : Measure (Fin d → ℝ)) := by
  classical
  have hγpos : 0 < γBarReal := lt_trans zero_lt_one hγ
  -- Abbreviations.
  set u := fam.u ε with hu_def
  set m := fam.m ε with hm_def
  set Du := fam.Du ε with hDu_def
  set DpHε := DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε with hDpHε_def
  set Hε := HdeltaK0 hweak ε with hHε_def
  -- The canonical transport coefficients.
  set aCoeff : (Fin d → ℝ) → ℝ :=
    (fun x => fluxCoeffA m x + ε * gatCoeffA γBarReal u x) with haCoeff_def
  set bCoeff : Fin d → ((Fin d → ℝ) → ℝ) :=
    (fun i x => fluxCoeffB DpHε m Du i x + ε * gatCoeffB γBarReal Du i x)
    with hbCoeff_def
  -- Coefficient `L^q` memberships for the combined-integral bridge.
  have haGε : MemLpPer q (fun x => ε * gatCoeffA γBarReal u x) := by
    have h := MemLpPer.const_smul (c := ε) haG
    have heq : (ε • gatCoeffA γBarReal u : (Fin d → ℝ) → ℝ)
        = fun x => ε * gatCoeffA γBarReal u x := by
      funext x; change ε • _ = ε * _; simp [smul_eq_mul]
    rwa [heq] at h
  have hbGε : ∀ i, MemLpPer q (fun x => ε * gatCoeffB γBarReal Du i x) := by
    intro i
    have h := MemLpPer.const_smul (c := ε) (hbG i)
    have heq : (ε • gatCoeffB γBarReal Du i : (Fin d → ℝ) → ℝ)
        = fun x => ε * gatCoeffB γBarReal Du i x := by
      funext x; change ε • _ = ε * _; simp [smul_eq_mul]
    rwa [heq] at h
  have haC : MemLpPer q aCoeff := by
    have h := MemLpPer.add haF haGε; rwa [haCoeff_def]
  have hbC : ∀ i, MemLpPer q (bCoeff i) := by
    intro i
    have h := MemLpPer.add (hbF i) (hbGε i); rw [hbCoeff_def]; exact h
  -- Transport half: `transportFunctional aCoeff bCoeff u Du = 0`.
  have hTrans :
      Periodic.transportFunctional aCoeff bCoeff u Du = 0 := by
    rw [haCoeff_def, hbCoeff_def]
    exact hTransportAtU_of_T3RegularizedStrongFamily
      (bb := bb) (gb := gb) hweak qε V fam ε hεpos hε1 hγ hp hp_top hbb hgb
      hRegK0 hu1 hSmoothLp g_unreg g_gat hg_unreg_int hg_gat_int
      hF_unreg_meas hF_unreg_bound hF_gat_meas hF_gat_bound
      haF hbF haG hbG hu_lp hDu_lp
  -- Combined-integral form of the transport functional.
  have hCombined :
      (∫ x in UnitCube d, aCoeff x * u x + ∑ i : Fin d, bCoeff i x * Du i x
          ∂(volume : Measure (Fin d → ℝ)))
        = Periodic.transportFunctional aCoeff bCoeff u Du :=
    Periodic.periodicIntegral_combined_eq_transportFunctional
      (p := p) (q := q) haC hbC hu_lp hDu_lp
  -- HJB half: `∫ (u + H^ε − V)·m = 0`.
  have hHJB :
      ∫ x in UnitCube d,
          (u x + Hε x (fun i => Du i x) (m x) - V x) * m x
          ∂(volume : Measure (Fin d → ℝ)) = 0 := by
    rw [hHε_def, hu_def, hm_def, hDu_def]
    exact hHJBIntegrated_of_T3RegularizedStrongFamily
      hweak qε V fam ε hεpos hε1 hResM hCont
  -- Pointwise: the combined transport integrand equals
  --   `m·u − u + m·(D_pH^ε ⬝ Du) + weakEpsTermsEucl`.
  have hTpt : ∀ x : Fin d → ℝ,
      aCoeff x * u x + ∑ i : Fin d, bCoeff i x * Du i x
        = m x * u x - u x
            + m x * ((DpHε x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + weakEpsTermsEucl γBarReal ε u Du x := by
    intro x
    -- Sum split: `∑ bᵢ·Duᵢ = m·(DpHε⬝Du) + ε·vecAbsPow·(Du⬝Du)`.
    have hsum :
        (∑ i : Fin d, bCoeff i x * Du i x)
          = m x * ((DpHε x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + ε * (vecAbsPowMinusTwo γBarReal (fun i => Du i x)
                    * ((fun i => Du i x) ⬝ (fun i => Du i x))) := by
      rw [hbCoeff_def]
      simp only [fluxCoeffB, gatCoeffB, dotProduct]
      have hrhs :
          (m x * ∑ i, DpHε x (fun j => Du j x) (m x) i * Du i x
            + ε * ((vecAbsPowMinusTwo γBarReal fun j => Du j x)
                    * ∑ i, Du i x * Du i x))
            = (∑ i, m x * (DpHε x (fun j => Du j x) (m x) i * Du i x))
              + ∑ i, ε * ((vecAbsPowMinusTwo γBarReal fun j => Du j x)
                          * (Du i x * Du i x)) := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      rw [hrhs, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _; ring
    -- Gateaux rpow identities (standalone, to feed `linear_combination`).
    have hVec : vecAbsPowMinusTwo γBarReal (fun i => Du i x)
                  * ((fun i => Du i x) ⬝ (fun i => Du i x))
                = ((fun i => Du i x) ⬝ (fun i => Du i x)) ^ (γBarReal / 2) :=
      vecAbsPowMinusTwo_mul_dot_eq_rpow_half γBarReal hγpos (fun i => Du i x)
    have hAbs : absPowMinusTwo γBarReal (u x) * (u x * u x) = |u x| ^ γBarReal :=
      absPowMinusTwo_mul_sq_eq_rpow γBarReal hγpos (u x)
    rw [hsum, haCoeff_def]
    simp only [fluxCoeffA, gatCoeffA, weakEpsTermsEucl]
    linear_combination ε * hVec + ε * hAbs
  -- Integrability of the transport pieces (for the rearrangement).
  have hint_au : IntegrableOn (fun x => aCoeff x * u x) (UnitCube d)
      (volume : Measure (Fin d → ℝ)) :=
    MeasureTheory.MemLp.integrable_mul haC.toMemLp hu_lp.toMemLp
  have hint_bDu : ∀ i, IntegrableOn (fun x => bCoeff i x * Du i x) (UnitCube d)
      (volume : Measure (Fin d → ℝ)) := fun i =>
    MeasureTheory.MemLp.integrable_mul (hbC i).toMemLp (hDu_lp i).toMemLp
  have hint_sum : IntegrableOn (fun x => ∑ i : Fin d, bCoeff i x * Du i x)
      (UnitCube d) (volume : Measure (Fin d → ℝ)) := by
    have := integrable_finset_sum (μ := volume.restrict (UnitCube d))
      (s := (Finset.univ : Finset (Fin d)))
      (f := fun i x => bCoeff i x * Du i x) (fun i _ => hint_bDu i)
    exact this
  -- `T := combined transport integrand` is integrable.
  have hint_T : IntegrableOn
      (fun x => aCoeff x * u x + ∑ i : Fin d, bCoeff i x * Du i x)
      (UnitCube d) (volume : Measure (Fin d → ℝ)) :=
    hint_au.add hint_sum
  -- The HJB residue `H := (u + Hε − V)·m` is integrable (`= −hjbResidual·m`).
  have hint_H : IntegrableOn
      (fun x => (u x + Hε x (fun i => Du i x) (m x) - V x) * m x)
      (UnitCube d) (volume : Measure (Fin d → ℝ)) := by
    have hres : IntegrableOn
        (fun x => hjbResidual V Hε Du m u x * m x) (UnitCube d)
        (volume : Measure (Fin d → ℝ)) := by
      rw [hHε_def, hu_def, hm_def, hDu_def]; exact hResM
    have hneg := hres.neg
    refine hneg.congr ?_
    filter_upwards with x
    simp only [hjbResidual, Pi.neg_apply]; ring
  -- `u` is integrable on the cube (from `hu1 : MemLpPer 1 u`).
  have hint_u : IntegrableOn u (UnitCube d) (volume : Measure (Fin d → ℝ)) :=
    memLp_one_iff_integrable.mp hu1.toMemLp
  -- The target RHS integrand equals `u + (T − H)` pointwise.
  have hRHSpt : ∀ x : Fin d → ℝ,
      (m x * (-Hε x (fun i => Du i x) (m x)
                + (DpHε x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
          + V x * m x
          + weakEpsTermsEucl γBarReal ε u Du x)
        = u x
          + ((aCoeff x * u x + ∑ i : Fin d, bCoeff i x * Du i x)
              - (u x + Hε x (fun i => Du i x) (m x) - V x) * m x) := by
    intro x
    rw [hTpt x]; ring
  -- Assemble: `∫ RHS = ∫ u + (∫ T − ∫ H) = ∫ u + (0 − 0) = ∫ u`.
  -- Combined transport integral vanishes (no rewriting of the integrand).
  have hTransInt' :
      (∫ x in UnitCube d, aCoeff x * u x + ∑ i : Fin d, bCoeff i x * Du i x
          ∂(volume : Measure (Fin d → ℝ))) = 0 := by
    rw [hCombined, hTrans]
  have hsubInt :
      (∫ x in UnitCube d,
          ((aCoeff x * u x + ∑ i : Fin d, bCoeff i x * Du i x)
            - (u x + Hε x (fun i => Du i x) (m x) - V x) * m x)
          ∂(volume : Measure (Fin d → ℝ))) = 0 := by
    rw [MeasureTheory.integral_sub hint_T hint_H, hTransInt', hHJB, sub_zero]
  calc
    ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ))
        = ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ))
          + 0 := by rw [add_zero]
    _ = ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ))
          + ∫ x in UnitCube d,
              ((aCoeff x * u x + ∑ i : Fin d, bCoeff i x * Du i x)
                - (u x + Hε x (fun i => Du i x) (m x) - V x) * m x)
              ∂(volume : Measure (Fin d → ℝ)) := by rw [hsubInt]
    _ = ∫ x in UnitCube d,
          (u x +
            ((aCoeff x * u x + ∑ i : Fin d, bCoeff i x * Du i x)
              - (u x + Hε x (fun i => Du i x) (m x) - V x) * m x))
          ∂(volume : Measure (Fin d → ℝ)) :=
        (MeasureTheory.integral_add hint_u (hint_T.sub hint_H)).symm
    _ = ∫ x in UnitCube d,
          (m x * (-Hε x (fun i => Du i x) (m x)
                    + (DpHε x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + weakEpsTermsEucl γBarReal ε u Du x)
          ∂(volume : Measure (Fin d → ℝ)) := by
        refine setIntegral_congr_fun measurableSet_unitCube ?_
        intro x _; simp only []; rw [← hRHSpt x]

end T3

/-! ## Lagrangian-clause producer (A2b)

This section is the Lagrangian companion of the A2a HJB-clause producer
above. It supplies the `h_lagr` input to `apriori_weak_power_growth`
(`InfimalConvolution/Apriori.lean`, line 104):

```
∀ᵐ x, ∀ p mx, 0 < mx →
  (mx ^ h.β) / h.C - h.C ≤ (DpHε x p mx) ⬝ p - HdeltaK0 h ε x p mx
```

This is paper `prop:boundsHepsilon.d` / `eq:DpHdelta.dotp.minusH`
(`Source/FGU-monotone_revised.tex`, line 1787): the *ε-independent*
Lagrangian lower bound for the regularised Hamiltonian.

### Bridge architecture

Unlike the HJB clause (A2a), the Lagrangian clause is a property of the
regularised Hamiltonian pair `(HdeltaK0 h ε, DpHε)` itself, **not** of the
strong-VI family. Its numerical content is already proved pointwise by
`InfConv.Hdelta_lagrangian_lower_bound` (pure convex algebra: chain the
convex-at-zero inequality for `H^ε` with `Hdelta_le_H_self` and the base
`h.upper` field). The A2b producer lifts that per-point statement to the
a.e.-family `h_lagr` shape, discharging the per-point side conditions:

* `hUp` (the `H(x,0,m) ≤ -(m^β)/C + C` upper bound) from `h.upper`;
* `hBdd` (`BddBelow` of `q ↦ H(x, 0 - q, m)`, needed by
  `Hdelta_le_H_self` at `p = 0`) from the base lower bound `h.lower`,
  which gives the constant lower bound `-h.C * (m^β + 1)`;
* `hCx` (the convex-at-zero inequality for `H^ε`) is passed as an a.e.
  input — exactly the convex-analytic input status of
  `Hamiltonian.lagrangian_lower_bound` and `Hdelta_lagrangian_lower_bound`
  (the convex-at-zero step silently identifies `D_pH^ε` with `∂_p H^ε`;
  it is NOT a proof-output oracle, mirroring the base-pair
  `lagrangian_lower_bound` accepted input).

No new oracle/rider structure is introduced.
-/

/-! ## Identity-clause producer (A2c)

This section is the energy-identity companion of the A2a HJB-clause and
A2b Lagrangian-clause producers above. It supplies the `h_identity`
input to `apriori_weak_power_growth` (`InfimalConvolution/Apriori.lean`,
lines 112–119):

```
∫ x in UnitCube d, u x ∂volume =
  ∫ x in UnitCube d,
    (m x * (-HdeltaK0 hHyp ε x (fun i => Du i x) (m x)
              + (DpHε x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
      + V x * m x + epsTerms x) ∂volume.
```

This is paper `eq:appositiveum` (`Source/FGU-monotone_revised.tex`,
line 1212), the integrated identity inside the proof of
`thm:apriori-simple.power.growth` that survives the `H ↦ H^ε`
substitution prescribed at line 1894 for `thm:apriori-weak.power.growth`.

### Bridge architecture

The integrated identity is, in both the paper (line 1212) and the
already-landed simple-power (T2) theorem, the *genuine-analytic* content
"test the regularized weak transport equation
(`lem:strong.is.strong.(c)`, our Phase-6 wrapper
`Hdelta_strong_transport_eq`) against `φ = u_ε`, combine with the HJB
equality (`lem:strong.is.strong.(b)`,
`Hdelta_strong_HJB_eq_on_pos`) tested against `m_ε`, and subtract". Per
CONVENTIONS §1b, T2 authorizes the *integrated* form as an upstream input
(`hIdentityRaw`) and discharges the `h_identity` consumer field by a
verbatim pass-through pinned against the solution's `(m, u, Du)` shape —
see `SimplePower.Banach.AprioriUniformPerSolHypothesesC.bClass_h_identity`
(`SimplePower/Banach/AprioriUniform.lean`, line 933).

A2c does the identical thing for the *regularized* pair
`(HdeltaK0 hHyp ε, DpHε)`: it accepts the integrated identity at the
regularized Hamiltonian as the same authorised §1b input and pins it to
the `h_identity` shape consumed by `apriori_weak_power_growth`. This
introduces NO new oracle/rider — it carries the exact §1b authorization
status already used by the T2 producer.

The `epsTerms ≥ 0` non-negativity (`hEpsNN`) and the a.e. positivity of
`m_ε` (`hMpos`) are *separate* input slots of `apriori_weak_power_growth`
and are intentionally NOT produced here.

-- Adapted from
-- `SimplePower.Banach.AprioriUniformPerSolHypothesesC.bClass_h_identity`
-- (the simple-power / T2 transport-identity discharge), re-derived for
-- the regularized pair `(HdeltaK0 hHyp ε, DpHε)`.
-/

/-- **Identity-clause producer `eq:appositiveum` (single `ε`).**

From the §1b-authorised integrated transport identity `hIdentityRaw` at
the regularized pair `(HdeltaK0 hHyp ε, DpHε)` and the bare solution
`(m, u, Du)` (sourced upstream from the Phase-6 transport wrapper
`Hdelta_strong_transport_eq` tested at `φ = u_ε`, combined with the HJB
equality `Hdelta_strong_HJB_eq_on_pos` against `m_ε`; paper line 1212),
deliver the `h_identity` input of `apriori_weak_power_growth`
shape-for-shape.

Mirrors `bClass_h_identity` (T2): the identity is consumed verbatim; the
`hHyp, ε, DpHε, V` parameters pin the type-shape of
`(HdeltaK0 hHyp ε, DpHε, m, u, Du, epsTerms)` against the
`apriori_weak_power_growth` `h_identity` slot. -/
theorem hIdentity_of_weakGrowth
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hHyp : HypothesisWeakGrowth (d := d) H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (DpHε : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (ε : ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u epsTerms : (Fin d → ℝ) → ℝ)
    (hIdentityRaw :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (m x * (-HdeltaK0 hHyp ε x (fun i => Du i x) (m x)
                    + (DpHε x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(volume : Measure (Fin d → ℝ))) :
    ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) =
      ∫ x in UnitCube d,
        (m x * (-HdeltaK0 hHyp ε x (fun i => Du i x) (m x)
                  + (DpHε x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
          + V x * m x
          + epsTerms x)
        ∂(volume : Measure (Fin d → ℝ)) :=
  hIdentityRaw

/-! ## Remaining-witness + V-bound cluster producer (A2e)

This section supplies the REMAINING integrability witnesses of
`apriori_weak_power_growth` (`InfimalConvolution/Apriori.lean`, lines
120–165) that A2d deferred:

* `hRHSabove_int` — `|V| + C·(m^β + 1) ∈ L¹` on the cube.
* `hRHSbelow_int` — `m·(-H^ε + DpHε·Du) + V·m + epsTerms ∈ L¹`.
* `hDu_norm_int` — `‖Du‖^{γ̄} ∈ L¹` on the cube.
* `hUbetap_int` — `|u|^{β̄'} ∈ L¹` on the cube.
* The `V`-bound cluster: `hVbnd` (`|V| ≤ Vbound` a.e.),
  `hVint` (`∫|V| ≤ Vint_bound`), `hVβp` (`∫|V|^{β̄'} ≤ Vβp_bound`).

### Provenance / status

* `hRHSabove_int`, `hRHSbelow_int` are taken as the **authorised §1b RAW
  inputs** exactly as in T2
  (`SimplePower.Banach.AprioriUniformPerSolHypothesesC.bClass_hRHSabove_int`
  / `bClass_hRHSbelow_int` are pass-throughs). We mirror that status: the
  integrated/raw integrability is accepted and pinned to the
  regularized-pair shape. NO Hamiltonian algebra is re-derived. This is
  NOT a net-new oracle — it carries the same accepted-rider status as its
  T2 counterpart.
* `hDu_norm_int` is **genuinely derived** from `∀ i, MemLpPer γ̄ (Du i)`
  via per-axis `MemLp.integrable_norm_rpow` and the finite-sum norm bound
  `‖(fun i => Du i x)‖^{γ̄} ≤ ∑ i, ‖Du i x‖^{γ̄}` (sup-norm on `Fin d → ℝ`).
* `hUbetap_int` is **genuinely derived** from `MemLpPer γ̄ u` via the
  exponent inclusion `β̄' ≤ γ̄` (paper `betaBar'_le_gammaBar`, valid since
  `α ≥ 1`) on the finite-measure cube + `MemLp.integrable_norm_rpow`. (In
  T2 this slot is an authorised embedding input; here it is in fact
  derivable from the carried `L^{γ̄}` membership, so we prove it outright —
  this is strictly weaker than the T2 accepted status, not net-new.)
* `hVbnd` is the **accepted paper a.e. bound** `|V| ≤ Vbound` (same C-class
  authorised status as the T2 field `hVbnd`).
* `hVint` is **genuinely derived** from `hVbnd` plus integrability of
  `|V|` on the unit cube: `∫_cube |V| ≤ Vbound · vol(cube) = Vbound`
  (`volume (UnitCube d) = 1`).
* `hVβp` is the **accepted paper §1b bound** `∫|V|^{β̄'} ≤ Vβp_bound`
  (same C-class status as the T2 field `hVβp`).

-- Adapted from
-- `SimplePower.Banach.AprioriUniformPerSolHypothesesC.bClass_hRHSabove_int`
-- / `bClass_hRHSbelow_int` (T2 §1b pass-throughs) and from
-- `Congestion.Existence.hDu_norm_int` / `hUbetap_int` (the genuine
-- norm-power-integrability derivations), re-derived for the bare
-- candidate at the regularized pair `(HdeltaK0 hHyp ε, DpHε)`.
-/

section A2eWitnesses

/-- **A2e (`hVint`, single `ε`).** GENUINELY DERIVED `L¹`-bound on `V`:
from the a.e. pointwise bound `|V| ≤ Vbound` and integrability of `|V|`
on the unit cube, `∫_cube |V| ≤ Vbound · vol(cube) = Vbound`
(`volume (UnitCube d) = 1`). The conclusion uses `Vint_bound := Vbound`. -/
theorem hVint_of_bnd
    {V : (Fin d → ℝ) → ℝ} {Vbound : ℝ}
    (hVint_int : Integrable (fun x => |V x|) (volume.restrict (UnitCube d)))
    (hVbnd : ∀ᵐ x ∂(volume.restrict (UnitCube d)), |V x| ≤ Vbound) :
    ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ)) ≤ Vbound := by
  haveI hcube_fin : MeasureTheory.IsFiniteMeasure
      (volume.restrict (UnitCube d) : Measure (Fin d → ℝ)) :=
    ⟨by
      rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
          volume_unitCube]; exact ENNReal.one_lt_top⟩
  -- `∫_cube |V| ≤ ∫_cube Vbound = Vbound · vol(cube) = Vbound`.
  have hbound : ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ))
      ≤ ∫ _x in UnitCube d, Vbound ∂(volume : Measure (Fin d → ℝ)) := by
    apply MeasureTheory.integral_mono_ae hVint_int (integrable_const _) hVbnd
  rw [MeasureTheory.setIntegral_const] at hbound
  have hvol_real : (volume : Measure (Fin d → ℝ)).real (UnitCube d) = 1 := by
    rw [MeasureTheory.measureReal_def, volume_unitCube, ENNReal.toReal_one]
  rw [hvol_real, one_smul] at hbound
  exact hbound

/-! ### D4b: V-bound integral cluster genuinely derived from `hV`

The `T3RegularizedSideData.of_family` loose binders `Vβp_bound`, `hVβp_nn`
(`0 ≤ Vβp_bound`) and `hVβp` (`∫|V|^{β̄'} ≤ Vβp_bound`) are NOT independent
paper riders: the §1b integral bound is realised by taking the *witness
constant to be the integral itself*, `Vβp_bound := ∫|V|^{β̄'}`. The only
analytic input is `hV : MemLpPer (ofReal (betaBar' β)) V`, which makes the
integrand `|V|^{β̄'}` integrable (via `MemLp.integrable_norm_rpow`), hence the
integral is a well-defined real and `0 ≤ ∫|V|^{β̄'}` is `integral_nonneg`.

This is the one V-cluster item the D4 planner flagged as genuinely
internalisable from `hV`. The remaining V-cluster facts (`Vbound`, `hVbnd`,
`hVintEq`, `hVint_int`) are NOT derivable from a finite-exponent `MemLpPer`:
the a.e. pointwise bound `|V| ≤ Vbound` requires `MemLpPer ⊤ V`
(`MemLpPer.exists_ae_norm_le` is `⊤`-only), so it stays an accepted paper
rider, consumed via the pass-through `hVint_of_bnd`. -/

/-- **D4b `Vβp` constant + bound from `hV`** (family-level `∀ ε > 0`).

The canonical witness is
`Vβp_bound := ∫|V|^{betaBar' hweak.β}`. Both the non-negativity and the §1b
bound are discharged uniformly in `ε` because the witness and the integrand
are `ε`-independent (the regularised Hamiltonians all carry the same `β`,
encoded by the consumer's `hβU`/`hβBar_eq`). This eliminates the
`Vβp_bound`/`hVβp_nn`/`hVβp` loose binders of `T3RegularizedSideData.of_family` in
favour of `hV` alone. -/
theorem hVβp_constant_family_of_memLpPer
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hHyp : HypothesisWeakGrowth (d := d) H DpH)
    {V : (Fin d → ℝ) → ℝ}
    (_hV : MemLpPer (ENNReal.ofReal (betaBar' hHyp.β)) V) :
    let Vβp_bound : ℝ := ∫ x in UnitCube d, |V x| ^ betaBar' hHyp.β
                            ∂(volume : Measure (Fin d → ℝ))
    (0 ≤ Vβp_bound) ∧
      (∀ ε : ℝ, ε > 0 →
        ∫ x in UnitCube d, |V x| ^ betaBar' hHyp.β
            ∂(volume : Measure (Fin d → ℝ)) ≤ Vβp_bound) := by
  intro Vβp_bound
  refine ⟨?_, fun ε _ => le_refl _⟩
  exact MeasureTheory.integral_nonneg
    (fun x => Real.rpow_nonneg (abs_nonneg _) _)

/-! ### D4b: HJB residual integrability from the residual `MemLpPer`

The `T3RegularizedSideData.of_family` loose binder `hRes` (`Integrable
(hjbResidual V (HdeltaK0 hweak ε) (Du ε) (m ε) (u ε))`) is the §1b
standing-regularity input that `Hdelta_strong_HJB_le` consumes. Mirroring
the strict (simple-power) chain's
`SimplePower.Banach.aprioriDischarge_residual_integrable`, the integrability
reduces to a `MemLpPer (ofReal β̄') R_ε` membership of the residual
`R_ε = -u - H^ε(Du, m) + V` (the paper consequence of the HJB inequality
`eq:HJleq0` plus the Hamiltonian upper bound `eq:boundsH` of `lem:ADFGU`).

With `1 ≤ β̄'` (paper `β̄' > 1`), `MemLp.mono_exponent` on the finite-measure
cube reduces `MemLpPer β̄'` to `MemLpPer 1`, which IS `Integrable`. This is
the exact reduction the strict chain uses; the residual `MemLpPer` itself
stays an accepted §1b rider (it is not derivable from `fam.*`+`hV` alone,
since the Hamiltonian's `L^{β̄'}` membership is part of `lem:ADFGU`). -/

-- Adapted from
-- `SimplePower.Banach.aprioriDischarge_residual_integrable`,
-- re-stated for the regularised carrier `HdeltaK0 hweak ε`.
/-- **D4b `hRes` (single `ε`).** HJB residual integrability from the
residual's `L^{β̄'}` membership, via finite-measure exponent monotonicity. -/
theorem hRes_of_residual_memLpPer
    {βBar' : ℝ≥0∞} (hβBar' : 1 ≤ βBar')
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    (hRes_Lp : MemLpPer βBar' (hjbResidual V H Du m u)) :
    Integrable (hjbResidual V H Du m u)
      (volume.restrict (UnitCube d)) := by
  haveI : MeasureTheory.IsFiniteMeasure
      (volume.restrict (UnitCube d) : Measure (Fin d → ℝ)) :=
    ⟨by
      rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
          volume_unitCube]; exact ENNReal.one_lt_top⟩
  exact hRes_Lp.toMemLp.integrable hβBar'

/-! ### D4c: transport-remainder bundle (`epsTerms` / `hEpsNN` /
`hIdentityRaw`) pinned against the strong-VI family

This is the third D4 child of the §1b transport-remainder drain.  The
`T3RegularizedSideData.of_family` loose binders threaded here are the three
regularisation-residue slots of the §1b transport remainder:

* `hIdentityRaw` — the integrated transport identity `eq:appositiveum`
  (paper line 1212),
  ```
  ∫ u ε = ∫ (m ε · (-H^ε + D_pH^ε·Du ε) + V·m ε + epsTerms ε).
  ```
* `epsTerms` — the per-`ε` regularisation residue function;
* `hEpsNN` — its a.e. non-negativity.

**Classification (verified against the strict / T2 chain).** All three
are §1b-authorised paper inputs in *both* the strict and weak chains —
they are NOT derivable from `fam.hVI` alone:

* `hIdentityRaw` is the integrated form derived in the paper by testing
  the regularised weak transport equation (`lem:strong.is.strong.(c)`,
  our `Hdelta_strong_transport_eq`) at `φ = u_ε` and combining with the
  HJB equality (`lem:strong.is.strong.(b)`, our
  `Hdelta_strong_HJB_eq_on_pos`) tested against `m_ε`.  In the *strict*
  (T2) chain this bridge from `(sol k).hVIeps_transport` to the
  integrated identity was deferred (child task
  `infra-P4-h-identity-of-hVIeps-transport`) and the integrated form is
  consumed **verbatim** by
  `SimplePower.Banach.AprioriUniformPerSolHypothesesC.bClass_h_identity`
  (`SimplePower/Banach/AprioriUniform.lean`, line 933).  The genuine
  derivation was never landed even for T2; the integrated identity is an
  authorised §1b/§8-status input in both chains, exactly like the `hCont`
  operator-continuity rider drained in D4b1.
* `epsTerms` / `hEpsNN` are the **C-class genuine residues** of the
  strict chain (`AprioriUniformPerSolHypothesesC.epsTerms` /
  `.hEpsNN`, `SimplePower/Banach/AprioriUniform.lean`, lines 413/415),
  explicitly classified there as "kept as authorised inputs per
  CONVENTIONS §1b".  They have no derivation in either chain.

Hence the genuine-derivation route (combining the transport and HJB
strong-VI consequences into the integrated identity) is **not** available
from the permitted data: the strict chain itself never closed it, and
`epsTerms`/`hEpsNN` are paper-side residues by construction.  The
producers below are therefore documented **verbatim pass-throughs**,
matching the strict-chain
`bClass_h_identity` discharge — they introduce NO new oracle and carry
the identical input status already used by the T2 producers.  Their role
is to pin the three §1b riders' type-shapes against the genuine carrier
`(HdeltaK0 hweak ε, DpHepsilonFam hweak qε ε)` and the produced family
`fam : T3RegularizedStrongFamily`'s `(m, u, Du)`.

-- Adapted from the strict-chain treatment in
-- `SimplePower.Banach.AprioriUniformPerSolHypothesesC.bClass_h_identity`
-- (the §1b transport-identity discharge) and the C-class `epsTerms`/`hEpsNN`
-- residues of `AprioriUniformPerSolHypothesesC`, re-stated as verbatim
-- pass-throughs for the regularised carrier `HdeltaK0 hweak ε`. -/

/-- **D4c `hIdentityRaw` (family, against the strong-VI family).**

Verbatim pass-through of the §1b-authorised integrated transport identity
`eq:appositiveum` (paper line 1212), pinned against the genuine carrier
`(HdeltaK0 hweak ε, DpHepsilonFam hweak qε ε)` and the produced family's
fields `(fam.m, fam.u, fam.Du)`.  This is the `hIdentityRaw` loose binder
shape consumed by `T3RegularizedSideData.of_family`,
specialised to `Du := fam.Du`, `m := fam.m`, `u := fam.u`.

Same authorised input status as the strict-chain `bClass_h_identity`. -/
theorem hIdentityRaw_of_family
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d) {βBarReal γBarReal : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    (fam : T3RegularizedStrongFamily V hweak qε βBarReal γBarReal)
    (epsTerms : ℝ → (Fin d → ℝ) → ℝ)
    (hIdentityRaw : ∀ ε, 0 < ε → ε ≤ 1 →
      ∫ x in UnitCube d, fam.u ε x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (fam.m ε x * (-HdeltaK0 hweak ε x (fun i => fam.Du ε i x) (fam.m ε x)
                    + (DpHepsilonFam hweak qε ε x (fun i => fam.Du ε i x)
                          (fam.m ε x)) ⬝ (fun i => fam.Du ε i x))
            + V x * fam.m ε x
            + epsTerms ε x)
          ∂(volume : Measure (Fin d → ℝ))) :
    ∀ ε, 0 < ε → ε ≤ 1 →
      ∫ x in UnitCube d, fam.u ε x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (fam.m ε x * (-HdeltaK0 hweak ε x (fun i => fam.Du ε i x) (fam.m ε x)
                    + (DpHepsilonFam hweak qε ε x (fun i => fam.Du ε i x)
                          (fam.m ε x)) ⬝ (fun i => fam.Du ε i x))
            + V x * fam.m ε x
            + epsTerms ε x)
          ∂(volume : Measure (Fin d → ℝ)) :=
  -- Verbatim pass-through: the integrated identity is consumed as the
  -- §1b-authorised input, pinned to `(fam.m, fam.u, fam.Du)`.  Mirrors
  -- `bClass_h_identity` (T2).
  fun ε hε hε1ε =>
    hIdentity_of_weakGrowth hweak V (DpHepsilonFam hweak qε ε) ε (fam.Du ε)
      (fam.m ε) (fam.u ε) (epsTerms ε) (hIdentityRaw ε hε hε1ε)

/-- **D4c `hEpsNN` (family, against the strong-VI family).**

Verbatim pass-through of the §1b C-class residue non-negativity
`0 ≤ epsTerms ε` a.e. (the strict-chain
`AprioriUniformPerSolHypothesesC.hEpsNN`), pinned to the `∀ ε > 0` shape
of the `T3RegularizedSideData.of_family` `hEpsNN` loose binder.  `epsTerms` is a
paper-side regularisation residue (C-class per CONVENTIONS §1b), not
derived from `fam`. -/
theorem hEpsNN_of_family
    (epsTerms : ℝ → (Fin d → ℝ) → ℝ)
    (hEpsNNRaw : ∀ ε > 0,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms ε x) :
    ∀ ε > 0, ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms ε x :=
  hEpsNNRaw

/-! ### D4d: integrability-cluster producers wired at the strong-VI family

The `T3RegularizedSideData.of_family` integrability cluster (`Main.lean`, the
`hLB_int` / `hMbeta_int` / `hVbetap_int` / `hRHSabove_int` / `hRHSbelow_int`
/ `hVβp` loose binders) is restated here against the produced
`fam : T3RegularizedStrongFamily` fields (`fam.m`, `fam.u`, `fam.Du`,
`fam.hmLp`, `fam.hmNonneg`) and the analytic input `hV` so the D4e assembly
step can feed them argument-for-argument without re-running each A2d/A2e
producer.

**Classification.**

* `hLB_int`, `hMbeta_int`, `hVbetap_int`, `hVβp` are **genuinely derived**
  from the carried `MemLpPer` memberships (`fam.hmLp` and `hV`) plus a.e.
  non-negativity (`fam.hmNonneg`).  The integrability is inlined via
  `MemLp.integrable_norm_rpow` (+ finite-measure exponent inclusion) and the
  D4b `hVβp_constant_family_of_memLpPer`, with the exponent bridges
  `βBarReal = (hPow ε).β + 1` (`hβBar_eq`), `(hPow ε).β = hweak.β`
  (`hβU`), and the Hölder identity `βBar' = betaBar' hweak.β`.
* `hRHSabove_int` (constant `hUB.C0`) and `hRHSbelow_int` are the §1b RAW
  pass-throughs (same authorised input status as the T2
  `bClass_hRHSabove_int` / `bClass_hRHSbelow_int`); they are threaded as
  hypotheses pinned to the `fam`/`hUB.C0` shape.

No new oracle or hypothesis is introduced; the genuine ones consume
`fam.hmLp`/`fam.hmNonneg`/`hV` only. -/

/-- **D4d Hölder bridge.** From `hpqβ : βBarReal.HolderConjugate βBar'` and
the witness `βBarReal = hweak.β + 1` (supplied by `hβBar_eq` at any `ε > 0`,
composed with `hβU`), the conjugate exponent is exactly
`betaBar' hweak.β = (hweak.β + 1) / hweak.β`. -/
theorem betaBar'_eq_of_holderConjugate
    {βBarReal βBar' β : ℝ}
    (hpqβ : βBarReal.HolderConjugate βBar')
    (hβBarReal : βBarReal = β + 1) :
    βBar' = betaBar' β := by
  have hconj : βBar' = βBarReal / (βBarReal - 1) := hpqβ.conjugate_eq
  rw [hconj, hβBarReal]
  unfold betaBar'
  congr 1
  ring

/-- **D4d `hLB_int` (family).** `m ε ^ (β+1) ∈ L¹(cube)` for all `ε > 0`,
from `fam.hmLp` (`MemLpPer (ofReal βBarReal) (fam.m ε)`) and `fam.hmNonneg`,
pinned to the `T3RegularizedSideData.of_family` binder shape
`(fun x => fam.m ε x ^ (hweak.β + 1))` via the single exponent fact
`βBarReal = hweak.β + 1` (`hβBarReal`).  The integrability argument is inlined
(`integrable_norm_rpow` + `hmNonneg` rewrite), so the producer carries no
`HypothesisPowerGrowth` binder (D4e GATE #4). -/
theorem t3_hLB_int_of_family
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d) {βBarReal γBarReal : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    (fam : T3RegularizedStrongFamily V hweak qε βBarReal γBarReal)
    (hβBarReal : βBarReal = hweak.β + 1) :
    ∀ ε, 0 < ε → ε ≤ 1 → Integrable
      (fun x => fam.m ε x ^ (hweak.β + 1)) (volume.restrict (UnitCube d)) := by
  intro ε hε hε1ε
  have hβ1_pos : 0 < hweak.β + 1 := by linarith [hweak.hβ]
  -- `fam.hmLp` at the regularised exponent `βBarReal = hweak.β + 1`.
  have hmLp : MemLpPer (ENNReal.ofReal (hweak.β + 1)) (fam.m ε) := by
    rw [← hβBarReal]; exact fam.hmLp ε hε (hε1ε)
  have hp_ne_zero : ENNReal.ofReal (hweak.β + 1) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hβ1_pos).ne'
  have hp_ne_top : ENNReal.ofReal (hweak.β + 1) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hint_norm : Integrable
      (fun x => ‖fam.m ε x‖ ^ (ENNReal.ofReal (hweak.β + 1)).toReal)
      (volume.restrict (UnitCube d)) :=
    hmLp.toMemLp.integrable_norm_rpow hp_ne_zero hp_ne_top
  rw [ENNReal.toReal_ofReal hβ1_pos.le] at hint_norm
  refine hint_norm.congr ?_
  filter_upwards [fam.hmNonneg ε hε (hε1ε)] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg hx]

/-- **D4d `hMbeta_int` (family).** `m ε ^ β ∈ L¹(cube)` for all `ε > 0`,
from `fam.hmLp` + `fam.hmNonneg` via the finite-measure exponent inclusion
`L^{β+1} ⊆ L^β`, pinned to the binder shape
`(fun x => fam.m ε x ^ hweak.β)`.  The argument is inlined (`mono_exponent_finite`
+ `integrable_norm_rpow` + `hmNonneg` rewrite), so the producer carries no
`HypothesisPowerGrowth` binder (D4e GATE #4). -/
theorem t3_hMbeta_int_of_family
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d) {βBarReal γBarReal : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    (fam : T3RegularizedStrongFamily V hweak qε βBarReal γBarReal)
    (hβBarReal : βBarReal = hweak.β + 1) :
    ∀ ε, 0 < ε → ε ≤ 1 → Integrable
      (fun x => fam.m ε x ^ hweak.β) (volume.restrict (UnitCube d)) := by
  intro ε hε hε1ε
  have hβ_pos : 0 < hweak.β := hweak.hβ
  have hmLp : MemLpPer (ENNReal.ofReal (hweak.β + 1)) (fam.m ε) := by
    rw [← hβBarReal]; exact fam.hmLp ε hε (hε1ε)
  -- `m ∈ L^β` from `m ∈ L^{β+1}` (finite-measure inclusion, `β ≤ β+1`).
  have hle : ENNReal.ofReal hweak.β ≤ ENNReal.ofReal (hweak.β + 1) := by
    apply ENNReal.ofReal_le_ofReal; linarith
  have hmLpβ : MemLpPer (ENNReal.ofReal hweak.β) (fam.m ε) :=
    Periodic.MemLpPer.mono_exponent_finite hle ENNReal.ofReal_ne_top hmLp
  have hp_ne_zero : ENNReal.ofReal hweak.β ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hβ_pos).ne'
  have hp_ne_top : ENNReal.ofReal hweak.β ≠ ⊤ := ENNReal.ofReal_ne_top
  have hint_norm : Integrable
      (fun x => ‖fam.m ε x‖ ^ (ENNReal.ofReal hweak.β).toReal)
      (volume.restrict (UnitCube d)) :=
    hmLpβ.toMemLp.integrable_norm_rpow hp_ne_zero hp_ne_top
  rw [ENNReal.toReal_ofReal hβ_pos.le] at hint_norm
  refine hint_norm.congr ?_
  filter_upwards [fam.hmNonneg ε hε (hε1ε)] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg hx]

/-- **D4d `hVbetap_int` (family).** `|V| ^ (β̄' = (β+1)/β) ∈ L¹(cube)` for all
`ε > 0`, from `hV : MemLpPer (ofReal βBar') V` and the Hölder identity
`βBar' = betaBar' hweak.β`, pinned to the binder shape
`(fun x => |V x| ^ betaBar' hweak.β)`.  The `∀ ε` is vacuous in the
integrand (it is `ε`-independent); the quantifier matches the binder. -/
theorem t3_hVbetap_int_of_family
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    {βBarReal βBar' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    (hpqβ : βBarReal.HolderConjugate βBar')
    (hβBarReal : βBarReal = hweak.β + 1)
    (hV : MemLpPer (ENNReal.ofReal βBar') V) :
    ∀ ε : ℝ, ε > 0 → Integrable
      (fun x => |V x| ^ betaBar' hweak.β) (volume.restrict (UnitCube d)) := by
  -- `βBar' = betaBar' hweak.β`, so `hV` is at the required exponent.
  have hβBar'_eq : βBar' = betaBar' hweak.β :=
    betaBar'_eq_of_holderConjugate hpqβ hβBarReal
  have hVβ' : MemLpPer (ENNReal.ofReal (betaBar' hweak.β)) V := by
    rw [← hβBar'_eq]; exact hV
  intro ε _hε
  -- Reduce to the raw `|V|^{β̄'}` integrability directly (via
  -- `MemLp.integrable_norm_rpow`), avoiding any per-`ε` `hPow` carrier.
  have hβp_pos : 0 < betaBar' hweak.β :=
    lt_trans zero_lt_one (one_lt_betaBar' hweak.β hweak.hβ)
  have hp_ne_zero : ENNReal.ofReal (betaBar' hweak.β) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hβp_pos).ne'
  have hp_ne_top : ENNReal.ofReal (betaBar' hweak.β) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hint_norm : Integrable
      (fun x => ‖V x‖ ^ (ENNReal.ofReal (betaBar' hweak.β)).toReal)
      (volume.restrict (UnitCube d)) :=
    hVβ'.toMemLp.integrable_norm_rpow hp_ne_zero hp_ne_top
  rw [ENNReal.toReal_ofReal hβp_pos.le] at hint_norm
  have hcong : (fun x => ‖V x‖ ^ betaBar' hweak.β)
      = (fun x => |V x| ^ betaBar' hweak.β) := by
    funext x; rw [Real.norm_eq_abs]
  rw [hcong] at hint_norm
  exact hint_norm

/-- **D4d `hVβp` (family).** `∫|V|^{β̄'} ≤ Vβp_bound` for all `ε > 0`, with the
canonical witness `Vβp_bound := ∫|V|^{betaBar' hweak.β}`, from `hV` alone.
Bundles non-negativity of the witness and the §1b bound.  Reuses
`hVβp_constant_family_of_memLpPer` after rewriting `βBar' = betaBar' hweak.β`. -/
theorem t3_hVβp_constant_of_family
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    {βBarReal βBar' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    (hpqβ : βBarReal.HolderConjugate βBar')
    (hβBarReal : βBarReal = hweak.β + 1)
    (hV : MemLpPer (ENNReal.ofReal βBar') V) :
    let Vβp_bound : ℝ := ∫ x in UnitCube d, |V x| ^ betaBar' hweak.β
                            ∂(volume : Measure (Fin d → ℝ))
    (0 ≤ Vβp_bound) ∧
      (∀ ε : ℝ, ε > 0 →
        ∫ x in UnitCube d, |V x| ^ betaBar' hweak.β
            ∂(volume : Measure (Fin d → ℝ)) ≤ Vβp_bound) := by
  have hβBar'_eq : βBar' = betaBar' hweak.β :=
    betaBar'_eq_of_holderConjugate hpqβ hβBarReal
  have hVβ' : MemLpPer (ENNReal.ofReal (betaBar' hweak.β)) V := by
    rw [← hβBar'_eq]; exact hV
  exact hVβp_constant_family_of_memLpPer hweak hVβ'

/-- **D4d `hRHSbelow_int` (family, pass-through).** §1b RAW pass-through of
the lower-bound RHS integrability
`m ε·(-H^ε + D_pH^ε·Du ε) + V·m ε + epsTerms ε`, pinned to
`(fam.m, fam.u, fam.Du)` and the genuine carrier
`(HdeltaK0 hweak ε, DpHepsilonFam hweak qε ε)`.  Same authorised §1b RAW input
status as the T2 `bClass_hRHSbelow_int` pass-through. -/
theorem t3_hRHSbelow_int_of_family
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d) {βBarReal γBarReal : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    (fam : T3RegularizedStrongFamily V hweak qε βBarReal γBarReal)
    (epsTerms : ℝ → (Fin d → ℝ) → ℝ)
    (hRHSbelowRaw : ∀ ε, 0 < ε → ε ≤ 1 → Integrable
        (fun x =>
          fam.m ε x * (-HdeltaK0 hweak ε x (fun i => fam.Du ε i x) (fam.m ε x)
                    + (DpHepsilonFam hweak qε ε x (fun i => fam.Du ε i x)
                          (fam.m ε x)) ⬝ (fun i => fam.Du ε i x))
            + V x * fam.m ε x
            + epsTerms ε x)
        (volume.restrict (UnitCube d))) :
    ∀ ε, 0 < ε → ε ≤ 1 → Integrable
      (fun x =>
        fam.m ε x * (-HdeltaK0 hweak ε x (fun i => fam.Du ε i x) (fam.m ε x)
                  + (DpHepsilonFam hweak qε ε x (fun i => fam.Du ε i x)
                        (fam.m ε x)) ⬝ (fun i => fam.Du ε i x))
          + V x * fam.m ε x
          + epsTerms ε x)
      (volume.restrict (UnitCube d)) :=
  hRHSbelowRaw

/-- **D4d `hIndicMemLp` (genuinely derived).** For any finite-measure
measurable set `S`, the constant-`1` indicator `1_S` is in `L^{β̄}_per`.
Discharged from Mathlib's `memLp_indicator_const` on the cube-restricted
measure (the `c = 1 ≠ 0` branch needs `μ S ≠ ∞`, exactly the binder
hypothesis), bridged to `MemLpPer` by `MemLp.toMemLpPer`.  This eliminates
the `hIndicMemLp` loose binder of `T3RegularizedSideData.of_family` — it is NOT a
rider. -/
theorem t3_hIndicMemLp_of_family {βBarReal : ℝ} :
    ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
      (volume.restrict (UnitCube d)) S < ∞ →
      MemLpPer (ENNReal.ofReal βBarReal)
        (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ))) := by
  intro S hS hSfin
  exact MemLp.toMemLpPer
    (memLp_indicator_const (ENNReal.ofReal βBarReal) hS.nullMeasurableSet (1 : ℝ)
      (Or.inr hSfin.ne))

/-- **D4d `hVint_int` (genuinely derived).** `|V| ∈ L¹(cube)`, from
`hV : MemLpPer (ofReal βBar') V` with `βBar' = (β+1)/β > 1` via the
finite-measure exponent inclusion `L^{β̄'} ⊆ L¹` and `MemLp.integrable`.
This eliminates the `hVint_int` loose binder of `T3RegularizedSideData.of_family`
— it is NOT a rider. -/
theorem t3_hVint_int_of_family
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    {βBarReal βBar' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    (hpqβ : βBarReal.HolderConjugate βBar')
    (hβBarReal : βBarReal = hweak.β + 1)
    (hV : MemLpPer (ENNReal.ofReal βBar') V) :
    Integrable (fun x => |V x|) (volume.restrict (UnitCube d)) := by
  haveI hcube_fin : MeasureTheory.IsFiniteMeasure
      (volume.restrict (UnitCube d) : Measure (Fin d → ℝ)) :=
    ⟨by
      rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
          volume_unitCube]; exact ENNReal.one_lt_top⟩
  have hβBar'_eq : βBar' = betaBar' hweak.β :=
    betaBar'_eq_of_holderConjugate hpqβ hβBarReal
  have hVβ' : MemLpPer (ENNReal.ofReal (betaBar' hweak.β)) V := by
    rw [← hβBar'_eq]; exact hV
  -- `L^{β̄'} ⊆ L¹` on the finite-measure cube (`β̄' = (β+1)/β > 1`).
  have h1le : (1 : ℝ) ≤ betaBar' hweak.β :=
    (one_lt_betaBar' hweak.β hweak.hβ).le
  have hle : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (betaBar' hweak.β) := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal h1le
  have hV_int : Integrable V (volume.restrict (UnitCube d)) :=
    hVβ'.toMemLp.integrable hle
  exact hV_int.abs

/-- **D4d `hVm_int` (family, genuinely derived — G6c).** The Hölder pairing
`|V|·m ε ∈ L¹(cube)` for all `ε > 0`, derived from `hV : MemLpPer (ofReal βBar') V`
and `fam.hmLp ε : MemLpPer (ofReal βBarReal) (fam.m ε)` at the conjugate pair
`(β̄', β̄)` (`hpqβ.symm`).  This is the integral-V replacement for the L∞ rider:
`Integrable (|V|·m)` follows from `|V| ∈ L^{β̄'}` and `m ε ∈ L^{β̄}` by Hölder,
with NO pointwise `|V| ≤ Vbound`.  Feeds the Young-route engine
`apriori_uniform_bound_of_strongVI_family_coercive_exp_Vlp` (G6b). -/
theorem t3_hVm_int_of_family
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d) {βBarReal γBarReal βBar' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    (fam : T3RegularizedStrongFamily V hweak qε βBarReal γBarReal)
    (hpqβ : βBarReal.HolderConjugate βBar')
    (hV : MemLpPer (ENNReal.ofReal βBar') V) :
    ∀ ε, 0 < ε → ε ≤ 1 → Integrable
      (fun x => |V x| * fam.m ε x) (volume.restrict (UnitCube d)) := by
  intro ε hε hε1ε
  -- `|V| = ‖V‖ ∈ L^{β̄'}` (norm-closure of `MemLp`).
  have hVnorm : MeasureTheory.MemLp (fun x => ‖V x‖) (ENNReal.ofReal βBar')
      (volume.restrict (UnitCube d)) := hV.toMemLp.norm
  -- `m ε ∈ L^{β̄}`.
  have hmMemLp : MeasureTheory.MemLp (fam.m ε) (ENNReal.ofReal βBarReal)
      (volume.restrict (UnitCube d)) := (fam.hmLp ε hε hε1ε).toMemLp
  -- Hölder triple `(β̄', β̄, 1)` from `hpqβ.symm`.
  haveI : ENNReal.HolderTriple (ENNReal.ofReal βBar') (ENNReal.ofReal βBarReal) 1 :=
    hpqβ.symm.ennrealOfReal
  have hmul : Integrable ((fun x => ‖V x‖) * fam.m ε)
      (volume.restrict (UnitCube d)) := hVnorm.integrable_mul hmMemLp
  refine hmul.congr ?_
  refine Filter.Eventually.of_forall ?_
  intro x; simp only [Pi.mul_apply, Real.norm_eq_abs]

/-- **D4d `hV_meas` (family, genuinely derived — G6c).** `V` is
a.e.-strongly-measurable on the cube, from `hV : MemLpPer (ofReal βBar') V`.
Feeds the Young-route engine `_Vlp`. -/
theorem t3_hV_meas_of_family
    {βBar' : ℝ} {V : (Fin d → ℝ) → ℝ}
    (hV : MemLpPer (ENNReal.ofReal βBar') V) :
    AEStronglyMeasurable V (volume.restrict (UnitCube d)) :=
  hV.aestronglyMeasurable

/-- **D6f `hRHSabove_int` (family, genuinely derived).** The upper-bound RHS
`|V x| + C0·(m ε^β + 1)` is `L¹(cube)` for all `ε > 0`, derived from the
already-internalised pieces — NO `hRHSaboveRaw` binder:

* `|V| ∈ L¹` via `t3_hVint_int_of_family` (from `hV : MemLpPer (ofReal βBar') V`
  with `βBar' = (β+1)/β > 1`, finite-measure inclusion `L^{β̄'} ⊆ L¹`);
* `m ε^β ∈ L¹` via `t3_hMbeta_int_of_family` (from `fam.hmLp` + `fam.hmNonneg`,
  finite-measure inclusion `L^{β+1} ⊆ L^β`);
* the constant `1` is `L¹` on the finite cube.

So `|V| + C0·(m^β + 1) = |V| + C0·m^β + C0·1` is a finite sum of integrable
functions, closed by `Integrable.add`/`Integrable.const_mul`.  This is the
genuine (non-pass-through) integrability producer for the upper-bound RHS. -/
theorem t3_hRHSabove_int_of_family_genuine
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d) {βBarReal γBarReal βBar' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    (fam : T3RegularizedStrongFamily V hweak qε βBarReal γBarReal)
    (C0 : ℝ)
    (hpqβ : βBarReal.HolderConjugate βBar')
    (hβBar_eq : βBarReal = hweak.β + 1)
    (hV : MemLpPer (ENNReal.ofReal βBar') V) :
    ∀ ε, 0 < ε → ε ≤ 1 → Integrable
      (fun x => |V x| + C0 * (fam.m ε x ^ hweak.β + 1))
      (volume.restrict (UnitCube d)) := by
  intro ε hε hε1ε
  -- `|V| ∈ L¹` (genuine, from `hV`).
  have hVabs : Integrable (fun x => |V x|) (volume.restrict (UnitCube d)) :=
    t3_hVint_int_of_family hweak hpqβ hβBar_eq hV
  -- `m ε^β ∈ L¹` (genuine, from `fam`).
  have hmβ : Integrable (fun x => fam.m ε x ^ hweak.β)
      (volume.restrict (UnitCube d)) :=
    t3_hMbeta_int_of_family hweak qε V fam hβBar_eq ε hε hε1ε
  -- The constant `1` is `L¹` on the finite cube.
  have hone : Integrable (fun _ : Fin d → ℝ => (1 : ℝ))
      (volume.restrict (UnitCube d)) := integrable_const 1
  -- `C0·(m^β + 1)` is `L¹`.
  have hsum : Integrable (fun x => fam.m ε x ^ hweak.β + 1)
      (volume.restrict (UnitCube d)) := hmβ.add hone
  have hC0sum : Integrable (fun x => C0 * (fam.m ε x ^ hweak.β + 1))
      (volume.restrict (UnitCube d)) := hsum.const_mul C0
  exact hVabs.add hC0sum

/-- **D4d-hH0-boundary `hH0` (genuinely derived).** The
`T3RegularizedSideData.of_family` `hH0` binder demands the lower bound at the
**boundary** mass `m = 0`:
`‖p‖^α / C0 - C0 ≤ HdeltaK0 hweak ε x p 0`.

`HdeltaUniformBounds.lower_uniform` only delivers
`‖p‖^α/C0 - C0·(m^β+1) ≤ HdeltaK0 hweak ε x p m` for `m > 0`; at `m = 0` it gives
the `m → 0⁺` LIMIT `‖p‖^α/C0 - C0`, NOT the literal boundary value. We close
the gap with the genuine boundary right-continuity of `m ↦ HdeltaK0 hweak ε x p m`
at `m = 0⁺` toward the literal value `HdeltaK0 hweak ε x p 0`
(`Hdelta_rc0_of_selectorFamily`, the `m = 0⁺` slice machinery already in
`Properties.lean`/`InfConv.lean`, threading the SAME accepted base riders
`HypothesisHZeroExtension`/`HypothesisHextJointCont`/`InfConvSelectorFamily`,
NOT `Hext_finite_at_zero` as a public oracle):

* the lower bound holds eventually as `m → 0⁺` (`lower_uniform` on `0 < m`);
* `m ↦ ‖p‖^α/C0 - C0·(m^β+1)` tends to `‖p‖^α/C0 - C0` (since `m^β → 0` for
  `β > 0`);
* `m ↦ HdeltaK0 hweak ε x p m` tends to `HdeltaK0 hweak ε x p 0` (rc0);
* `le_of_tendsto_of_tendsto'` passes the inequality to the limit.

This is a REAL producer for the `hH0` binder from `HdeltaUniformBounds`
plus the accepted `m = 0⁺` slice carriers — it is NOT a pass-through and NOT
a new public oracle. -/
theorem t3_hH0_of_bounds
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d)
    (hUB : HdeltaUniformBounds (H := H) (DpH := DpH) hweak qε)
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hdiff : HypothesisHpDifferentiable (d := d) H DpH)
    (sel : StationaryMFG.InfimalConvolution.InfConvSelectorFamily
      (H := H) (DpH := DpH) hweak qε) :
    ∀ ε, 0 < ε → ε ≤ 1 → ∀ᵐ x ∂(volume.restrict (UnitCube d)),
            ∀ p : Fin d → ℝ,
              ‖p‖ ^ hweak.α / hUB.C0 - hUB.C0 ≤ HdeltaK0 hweak ε x p 0 := by
  intro ε hε hε1ε
  exact Hdelta_zero_lower_of_uniformBounds hweak hmon qε sel hUB hε hε1ε

/-! ## D6e-2: two-sided a.e. envelope for the H-composite (`m ≥ 0`)

The §1b residual-`MemLpPer` construction (D6e-3) needs an a.e. pointwise
two-sided envelope of the genuine regularised Hamiltonian composited at the
family's `(Du_ε, m_ε)`:

```
|HdeltaK0 hweak ε x (Du_ε · x) (m_ε x)| ≤ C_ε · (‖Du_ε · x‖^α + m_ε x^β + 1),
```

with `C_ε := CdeltaEps hweak ε`.  The family mass `m_ε` is only `≥ 0`
(`fam.hmNonneg`), so the bound must hold including the boundary `{m = 0}`,
where the `m > 0` a.e. estimates `HdeltaAEPowerEpsData.H_upper_pointwise_ae` /
`HdeltaAEPowerEpsData.lower_ae` are unavailable.

The proof case-splits on `0 < m_ε x` vs `m_ε x = 0` (from `fam.hmNonneg`):

* `0 < m`: upper from `H_upper_pointwise_ae`
  (`HdeltaK0 ≤ C_ε(‖p‖^α+1) − m^β/C_ε ≤ C_ε(‖p‖^α+m^β+1)`), lower from `lower_ae`
  (`‖p‖^α/C_ε − C_ε(m^β+1) ≤ HdeltaK0`, hence
  `−HdeltaK0 ≤ C_ε(m^β+1) − ‖p‖^α/C_ε ≤ C_ε(‖p‖^α+m^β+1)`).
* `m = 0`: upper from `Hdelta_zero_upper_of_selectorFamily`
  (`HdeltaK0(x,p,0) ≤ C_ε(‖p‖^α+1)`), lower from the boundary slice
  `t3_hH0_of_bounds` (`‖p‖^α/C0 − C0 ≤ HdeltaK0(x,p,0)`), so
  `−HdeltaK0(x,p,0) ≤ C0 − ‖p‖^α/C0 ≤ C0 ≤ C_ε` via the reconciliation binder
  `hC0_le : hUB.C0 ≤ C_ε` (discharged by the consumer; e.g. when
  `hUB = hdeltaUniformBounds_of_selector …`, `hUB.C0 = 2^α(C+1) ≤ C_ε` by
  `cdeltaEps_dom_facts`).

GATE #1: binders are `fam` plus the paper-accepted carriers
`hmon`/`hdiff`/`sel`/`hAE`/`hUB` and the constant-reconciliation
`hC0_le`/`hε1`; NO loose `m`/`u`/`Du`. -/
theorem T3.hComposite_envelope_of_family
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d) {βBarReal γBarReal : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    (fam : T3RegularizedStrongFamily V hweak qε βBarReal γBarReal)
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hdiff : HypothesisHpDifferentiable (d := d) H DpH)
    (sel : StationaryMFG.InfimalConvolution.InfConvSelectorFamily
      (H := H) (DpH := DpH) hweak qε)
    (hAE : HdeltaAEPowerEpsData (H := H) (DpH := DpH) hweak qε)
    (hUB : HdeltaUniformBounds (H := H) (DpH := DpH) hweak qε)
    (hC0_le : ∀ ε : ℝ, ε > 0 →
      hUB.C0 ≤ CdeltaEps (H := H) (DpH := DpH) hweak ε)
    :
    ∀ ε, 0 < ε → ε ≤ 1 → ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        |HdeltaK0 hweak ε x (fun i => fam.Du ε i x) (fam.m ε x)|
          ≤ CdeltaEps (H := H) (DpH := DpH) hweak ε
              * (‖(fun i => fam.Du ε i x)‖ ^ hweak.α + fam.m ε x ^ hweak.β + 1) := by
  intro ε hε hε1ε
  -- The per-`ε` constant and its positivity.
  set Cε : ℝ := CdeltaEps (H := H) (DpH := DpH) hweak ε with hCε_def
  have hCε_pos : 0 < Cε := CdeltaEps_pos (H := H) (DpH := DpH) hweak hε
  -- The four AE ingredients.
  have hUp : ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p m, 0 < m →
      HdeltaK0 hweak ε x p m ≤ CdeltaEps hweak ε * (‖p‖ ^ hweak.α + 1) -
        m ^ hweak.β / CdeltaEps hweak ε := by
    filter_upwards [hAE.H_upper_pointwise_ae ε hε hε1ε] with x hx p m hm
    rw [HdeltaK0_eq_Hdelta_of_pos hweak hm]
    exact hx p m hm
  have hLow : ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p m, 0 < m →
      ‖p‖ ^ hweak.α / CdeltaEps hweak ε - CdeltaEps hweak ε * (m ^ hweak.β + 1) ≤
        HdeltaK0 hweak ε x p m := by
    filter_upwards [hAE.lower_ae ε hε hε1ε] with x hx p m hm
    rw [HdeltaK0_eq_Hdelta_of_pos hweak hm]
    exact hx p m hm
  have hZeroUp := Hdelta_zero_upper_of_selectorFamily (H := H) (DpH := DpH)
    hweak hmon qε sel hAE hε hε1ε
  have hZeroLow := t3_hH0_of_bounds hweak qε hUB hmon hdiff sel ε hε hε1ε
  have hC0_le_ε : hUB.C0 ≤ Cε := hC0_le ε hε
  filter_upwards [hUp, hLow, hZeroUp, hZeroLow, fam.hmNonneg ε hε hε1ε]
    with x hxUp hxLow hxZeroUp hxZeroLow hxNonneg
  -- Local abbreviations for the family slot values.
  set p : Fin d → ℝ := fun i => fam.Du ε i x with hp_def
  set m : ℝ := fam.m ε x with hm_def
  set B : ℝ := Cε * (‖p‖ ^ hweak.α + m ^ hweak.β + 1) with hB_def
  -- Nonnegativity of the constituent powers.
  have hpα_nn : (0 : ℝ) ≤ ‖p‖ ^ hweak.α := Real.rpow_nonneg (norm_nonneg _) _
  -- It suffices to show `HdeltaK0 ≤ B` and `−B ≤ HdeltaK0`.
  rw [abs_le]
  rcases lt_or_eq_of_le hxNonneg with hmpos | hmzero
  · -- Case `0 < m`.
    have hmpos' : 0 < m := hmpos
    have hmβ_nn : (0 : ℝ) ≤ m ^ hweak.β := Real.rpow_nonneg (le_of_lt hmpos') _
    have hUpx : HdeltaK0 hweak ε x p m
        ≤ Cε * (‖p‖ ^ hweak.α + 1) - m ^ hweak.β / Cε := hxUp p m hmpos'
    have hLowx : ‖p‖ ^ hweak.α / Cε - Cε * (m ^ hweak.β + 1)
        ≤ HdeltaK0 hweak ε x p m := hxLow p m hmpos'
    have hdiv_nn : (0 : ℝ) ≤ m ^ hweak.β / Cε :=
      div_nonneg hmβ_nn (le_of_lt hCε_pos)
    have hpdiv_nn : (0 : ℝ) ≤ ‖p‖ ^ hweak.α / Cε :=
      div_nonneg hpα_nn (le_of_lt hCε_pos)
    -- `Cε·(‖p‖^α+1) = Cε‖p‖^α + Cε ≤ B = Cε(‖p‖^α+m^β+1)` since `Cε·m^β ≥ 0`.
    have hupper_target : Cε * (‖p‖ ^ hweak.α + 1) ≤ B := by
      have hCεmβ_nn : (0 : ℝ) ≤ Cε * m ^ hweak.β := mul_nonneg (le_of_lt hCε_pos) hmβ_nn
      rw [hB_def]; nlinarith [hCεmβ_nn]
    refine ⟨?_, ?_⟩
    · -- `−B ≤ HdeltaK0`.
      have : -B ≤ ‖p‖ ^ hweak.α / Cε - Cε * (m ^ hweak.β + 1) := by
        rw [hB_def]; nlinarith [hpdiv_nn, hpα_nn]
      linarith [this, hLowx]
    · -- `HdeltaK0 ≤ B`.
      have : HdeltaK0 hweak ε x p m ≤ Cε * (‖p‖ ^ hweak.α + 1) := by
        linarith [hUpx, hdiv_nn]
      linarith [this, hupper_target]
  · -- Case `m = 0`.
    have hm0 : m = 0 := hmzero.symm
    have hmβ0 : m ^ hweak.β = 0 := by
      rw [hm0, Real.zero_rpow (ne_of_gt hweak.hβ)]
    -- Upper at `m = 0`: `HdeltaK0(x,p,0) ≤ Cε(‖p‖^α+1) = B`.
    have hUpx0 : HdeltaK0 hweak ε x p 0 ≤ Cε * (‖p‖ ^ hweak.α + 1) := hxZeroUp p
    -- Lower at `m = 0`: `‖p‖^α/C0 − C0 ≤ HdeltaK0(x,p,0)`.
    have hLowx0 : ‖p‖ ^ hweak.α / hUB.C0 - hUB.C0 ≤ HdeltaK0 hweak ε x p 0 := hxZeroLow p
    have hC0_pos : 0 < hUB.C0 := hUB.hC0
    have hpdiv0_nn : (0 : ℝ) ≤ ‖p‖ ^ hweak.α / hUB.C0 :=
      div_nonneg hpα_nn (le_of_lt hC0_pos)
    -- `B = Cε(‖p‖^α + 1)` at `m = 0`.
    have hB0 : B = Cε * (‖p‖ ^ hweak.α + 1) := by
      rw [hB_def, hmβ0]; ring
    rw [hm0]
    refine ⟨?_, ?_⟩
    · -- `−B ≤ HdeltaK0(x,p,0)`: `−B = −Cε(‖p‖^α+1) ≤ −C0 ≤ ‖p‖^α/C0 − C0 ≤ HdeltaK0`.
      have hneg : -B ≤ -hUB.C0 := by
        rw [hB0]
        have : hUB.C0 ≤ Cε * (‖p‖ ^ hweak.α + 1) := by
          nlinarith [hpα_nn, le_of_lt hCε_pos, hC0_le_ε]
        linarith
      have hchain : -hUB.C0 ≤ ‖p‖ ^ hweak.α / hUB.C0 - hUB.C0 := by linarith [hpdiv0_nn]
      linarith [hneg, hchain, hLowx0]
    · -- `HdeltaK0(x,p,0) ≤ B`.
      rw [hB0]; exact hUpx0

/-! ## D6e-3: `MemLpPer (β̄')` of the H-composite from the D6e-2 envelope

The §1b residual-`MemLpPer` construction packages the genuine regularised
Hamiltonian composited at the family slot `(Du_ε, m_ε)` as a member of
`L^{β̄'}_per`, `β̄' = (β+1)/β`, from the two-sided a.e. envelope
`T3.hComposite_envelope_of_family`:

```
|HdeltaK0 hweak ε x (Du_ε · x) (m_ε x)| ≤ C_ε · (‖Du_ε · x‖^α + m_ε x^β + 1).
```

The dominator `g_ε x := C_ε · (‖Du_ε · x‖^α + m_ε x^β + 1)` is `L^{β̄'}`:

* `‖Du_ε · x‖^α ∈ L^{β̄'}`: each `Du_ε i ∈ L^{γ̄}` (`fam.hDuLp`), so the
  (sup-)norm `x ↦ ‖Du_ε · x‖ ∈ L^{γ̄}` (coordinatewise domination by the
  sum of absolute values, the `memLpPer_pi_of_coord` idea), and `‖·‖^α`
  closes into `L^{γ̄/α} = L^{β̄'}` by `MemLpPer.rpow_closure` (the exponent
  identity `γ̄ = α·β̄'` is `gammaBar_eq_alpha_mul_betaBar'`).
* `m_ε^β ∈ L^{β̄'}`: `m_ε ∈ L^{β̄ = β+1}` (`fam.hmLp`), `β̄'·β = β̄`, and
  `rpow_closure` on `‖m_ε‖^β` transports to `m_ε^β` via `fam.hmNonneg`.
* the constant `1` is `L^{β̄'}` on the finite cube.

The H-composite is `AEStronglyMeasurable` via
`aemeasurable_HdeltaK0_comp_of_rc0` (the closed-cone carrier `HdeltaK0`,
which agrees with `HdeltaK0` on `{0 ≤ m}` a.e. by `fam.hmNonneg` +
the canonical boundary measurability theorem).  `MemLp.mono'` against `g_ε` then closes,
since `‖HdeltaK0 …‖ = |HdeltaK0 …| ≤ g_ε` is exactly the envelope.

GATE #1: binders are `fam` plus the paper-accepted carriers
`hMeas`/`hmon`/`hdiff`/`sel`/`hAE`/`hUB` and the constant
reconciliations `hC0_le`/`hε1`/`hβBar`/`hγBar`; NO loose `m`/`u`/`Du`. -/
theorem T3.hComposite_memLpPer_of_family
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d) {βBarReal γBarReal : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    (fam : T3RegularizedStrongFamily V hweak qε βBarReal γBarReal)
    (hMeas : StationaryMFG.Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hdiff : HypothesisHpDifferentiable (d := d) H DpH)
    (sel : StationaryMFG.InfimalConvolution.InfConvSelectorFamily
      (H := H) (DpH := DpH) hweak qε)
    (hAE : HdeltaAEPowerEpsData (H := H) (DpH := DpH) hweak qε)
    (hUB : HdeltaUniformBounds (H := H) (DpH := DpH) hweak qε)
    (hC0_le : ∀ ε : ℝ, ε > 0 →
      hUB.C0 ≤ CdeltaEps (H := H) (DpH := DpH) hweak ε)
    (hβBar : βBarReal = StationaryMFG.Hamiltonian.betaBar hweak.β)
    (hγBar : γBarReal = StationaryMFG.Hamiltonian.gammaBar hweak.α hweak.β) :
    ∀ ε, 0 < ε → ε ≤ 1 →
      Periodic.MemLpPer (ENNReal.ofReal (StationaryMFG.Hamiltonian.betaBar' hweak.β))
        (fun x => HdeltaK0 hweak ε x (fun i => fam.Du ε i x) (fam.m ε x)) := by
  classical
  -- Substitute the abstract family exponents by their concrete paper values
  -- (this rewrites them inside `fam`'s type, avoiding motive issues later).
  subst hβBar
  subst hγBar
  intro ε hε hε1ε
  -- Exponent constants (kept literal as `hweak.α`/`hweak.β` to avoid
  -- let-binding motive friction in the `fam`-typed memberships).
  have hα1 : (1 : ℝ) < hweak.α := hweak.hα
  have hβ0 : (0 : ℝ) < hweak.β := hweak.hβ
  have hαpos : (0 : ℝ) < hweak.α := lt_trans one_pos hα1
  have hβ1_pos : (0 : ℝ) < hweak.β + 1 := by linarith
  set β' : ℝ := StationaryMFG.Hamiltonian.betaBar' hweak.β with hβ'_def
  have hβ'_pos : 0 < β' := by
    rw [hβ'_def]; unfold StationaryMFG.Hamiltonian.betaBar'; positivity
  -- The per-`ε` constant.
  set Cε : ℝ := CdeltaEps (H := H) (DpH := DpH) hweak ε with hCε_def
  have hCε_pos : 0 < Cε := CdeltaEps_pos (H := H) (DpH := DpH) hweak hε
  -- Family `Lᵖ` regularities at the concrete paper exponents.
  have hmLp : Periodic.MemLpPer (ENNReal.ofReal (hweak.β + 1)) (fam.m ε) := by
    have h := fam.hmLp ε hε hε1ε
    simpa [StationaryMFG.Hamiltonian.betaBar] using h
  have hDuLp : ∀ i, Periodic.MemLpPer
      (ENNReal.ofReal (StationaryMFG.Hamiltonian.gammaBar hweak.α hweak.β))
      (fam.Du ε i) := fun i => fam.hDuLp ε hε hε1ε i
  have hmNonneg := fam.hmNonneg ε hε hε1ε
  -- ===========================================================
  -- Step 1: the vector (sup-)norm `‖Du_ε · x‖ ∈ L^{γ̄}`.
  -- (Inlined `memLpPer_pi_of_coord`: domination by `∑ i, |Du_ε i x|`.)
  -- ===========================================================
  have hγbar_eq : StationaryMFG.Hamiltonian.gammaBar hweak.α hweak.β = hweak.α * β' := by
    rw [hβ'_def]
    exact StationaryMFG.Hamiltonian.gammaBar_eq_alpha_mul_betaBar'
      hweak.α hweak.β (ne_of_gt hβ0)
  haveI hfin : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  have hNormLp : Periodic.MemLpPer
      (ENNReal.ofReal (StationaryMFG.Hamiltonian.gammaBar hweak.α hweak.β))
      (fun x : (Fin d → ℝ) => ‖(fun i : Fin d => fam.Du ε i x)‖) := by
    set p : ℝ≥0∞ := ENNReal.ofReal (StationaryMFG.Hamiltonian.gammaBar hweak.α hweak.β)
      with hp_def
    have habs_memLp : ∀ i, Periodic.MemLpPer (d := d) p (fun x => |fam.Du ε i x|) := by
      intro i
      have h2 := (hDuLp i).toMemLp.norm
      have heq : (fun x => ‖fam.Du ε i x‖) = fun x => |fam.Du ε i x| := by
        funext x; exact Real.norm_eq_abs _
      rw [heq] at h2
      exact MemLp.toMemLpPer h2
    have hDom_memLp : Periodic.MemLpPer (d := d) p
        (fun x => ∑ i : Fin d, |fam.Du ε i x|) := by
      have hsum :
          MemLp (fun x => ∑ i : Fin d, (fun x => |fam.Du ε i x|) x) p
            (Measure.restrict volume (UnitCube d)) :=
        MeasureTheory.memLp_finset_sum (Finset.univ : Finset (Fin d))
          (fun i _ => (habs_memLp i).toMemLp)
      exact MemLp.toMemLpPer hsum
    have hbound :
        ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
          ‖‖(fun i : Fin d => fam.Du ε i x)‖‖ ≤ (1 : ℝ) * ‖∑ i, |fam.Du ε i x|‖ := by
      refine Filter.Eventually.of_forall ?_
      intro x
      have hsum_nn : 0 ≤ ∑ i, |fam.Du ε i x| :=
        Finset.sum_nonneg (fun i _ => abs_nonneg _)
      have hpi : ‖(fun i : Fin d => fam.Du ε i x)‖ ≤ ∑ i, |fam.Du ε i x| := by
        rw [pi_norm_le_iff_of_nonneg hsum_nn]
        intro i
        rw [Real.norm_eq_abs]
        exact Finset.single_le_sum (f := fun j => |fam.Du ε j x|)
          (fun j _ => abs_nonneg _) (Finset.mem_univ i)
      have h1 : ‖‖(fun i : Fin d => fam.Du ε i x)‖‖ = ‖(fun i : Fin d => fam.Du ε i x)‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      have h2 : (1 : ℝ) * ‖∑ i, |fam.Du ε i x|‖ = ∑ i, |fam.Du ε i x| := by
        rw [one_mul, Real.norm_eq_abs, abs_of_nonneg hsum_nn]
      rw [h1, h2]
      exact hpi
    have hmeas :
        AEStronglyMeasurable
          (fun x : (Fin d → ℝ) => ‖(fun i : Fin d => fam.Du ε i x)‖)
          (Measure.restrict volume (UnitCube d)) := by
      have hAEm : AEMeasurable
          (fun x : (Fin d → ℝ) => fun i : Fin d => fam.Du ε i x)
          (Measure.restrict volume (UnitCube d)) :=
        aemeasurable_pi_iff.mpr fun i => (hDuLp i).aestronglyMeasurable.aemeasurable
      exact hAEm.norm.aestronglyMeasurable
    exact MemLp.toMemLpPer (MemLp.of_le_mul hDom_memLp.toMemLp hmeas hbound)
  -- Step 2: `‖Du_ε · x‖^α ∈ L^{β̄'}` via `rpow_closure` (`γ̄ = α·β̄'`).
  have hDuPow : Periodic.MemLpPer (ENNReal.ofReal β')
      (fun x => ‖(fun i : Fin d => fam.Du ε i x)‖ ^ hweak.α) := by
    have hmul : ENNReal.ofReal β' * ENNReal.ofReal hweak.α
        = ENNReal.ofReal (StationaryMFG.Hamiltonian.gammaBar hweak.α hweak.β) := by
      rw [← ENNReal.ofReal_mul (le_of_lt hβ'_pos), hγbar_eq, mul_comm]
    have hrpow := Periodic.MemLpPer.rpow_closure (d := d) (s := ENNReal.ofReal β')
      (r := hweak.α) hαpos
      (f := fun x : (Fin d → ℝ) => ‖(fun i : Fin d => fam.Du ε i x)‖)
      (by rw [hmul]; exact hNormLp)
    -- `‖‖Du‖‖ = ‖Du‖` (the norm of a nonneg real is itself).
    have heq : (fun x => ‖‖(fun i : Fin d => fam.Du ε i x)‖‖ ^ hweak.α)
        = (fun x => ‖(fun i : Fin d => fam.Du ε i x)‖ ^ hweak.α) := by
      funext x; rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    rw [heq] at hrpow
    exact hrpow
  -- Step 3: `m_ε^β ∈ L^{β̄'}` via `rpow_closure` + `hmNonneg` (`β̄'·β = β̄`).
  have hmPow : Periodic.MemLpPer (ENNReal.ofReal β')
      (fun x => fam.m ε x ^ hweak.β) := by
    have hmul : ENNReal.ofReal β' * ENNReal.ofReal hweak.β
        = ENNReal.ofReal (hweak.β + 1) := by
      rw [← ENNReal.ofReal_mul (le_of_lt hβ'_pos), hβ'_def]
      congr 1
      unfold StationaryMFG.Hamiltonian.betaBar'
      field_simp
    have habs : Periodic.MemLpPer (d := d) (ENNReal.ofReal β')
        (fun x => ‖fam.m ε x‖ ^ hweak.β) :=
      Periodic.MemLpPer.rpow_closure (d := d) hβ0 (by rw [hmul]; exact hmLp)
    have hae : (fun x => ‖fam.m ε x‖ ^ hweak.β)
        =ᵐ[Measure.restrict volume (UnitCube d)] (fun x => fam.m ε x ^ hweak.β) := by
      filter_upwards [hmNonneg] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg hx]
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq hae habs.toMemLp)
  -- Step 4: the constant `1 ∈ L^{β̄'}` (finite cube).
  have hOneLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal β')
      (fun _ : (Fin d → ℝ) => (1 : ℝ)) := MemLp.toMemLpPer (memLp_const 1)
  -- Step 5: assemble the dominator `g_ε = Cε · (‖Du‖^α + m^β + 1)`.
  have hSumLp : Periodic.MemLpPer (ENNReal.ofReal β')
      (fun x => ‖(fun i : Fin d => fam.Du ε i x)‖ ^ hweak.α
        + fam.m ε x ^ hweak.β + 1) := by
    have h12 := Periodic.MemLpPer.add hDuPow hmPow
    have h123 := Periodic.MemLpPer.add h12 hOneLp
    -- realign the pointwise function shape.
    have heq :
        ((fun x => ‖(fun i : Fin d => fam.Du ε i x)‖ ^ hweak.α)
            + (fun x => fam.m ε x ^ hweak.β) + (fun _ : (Fin d → ℝ) => (1 : ℝ)))
          = (fun x => ‖(fun i : Fin d => fam.Du ε i x)‖ ^ hweak.α
              + fam.m ε x ^ hweak.β + 1) := by
      funext x; simp [Pi.add_apply]
    rwa [heq] at h123
  have hgLp : Periodic.MemLpPer (ENNReal.ofReal β')
      (fun x => Cε * (‖(fun i : Fin d => fam.Du ε i x)‖ ^ hweak.α
        + fam.m ε x ^ hweak.β + 1)) := by
    have hsmul := hSumLp.const_smul (𝕜 := ℝ) Cε
    have heq :
        (Cε • (fun x => ‖(fun i : Fin d => fam.Du ε i x)‖ ^ hweak.α
            + fam.m ε x ^ hweak.β + 1))
          = (fun x => Cε * (‖(fun i : Fin d => fam.Du ε i x)‖ ^ hweak.α
              + fam.m ε x ^ hweak.β + 1)) := by
      funext x; simp [Pi.smul_apply, smul_eq_mul]
    rwa [heq] at hsmul
  -- Step 6: AE-strong measurability of the H-composite via the closed-cone
  -- carrier `HdeltaK0` (= `HdeltaK0` on `{0 ≤ m}` a.e.).
  have hDu_aem : AEMeasurable (fun x : (Fin d → ℝ) => fun i : Fin d => fam.Du ε i x)
      (volume.restrict (StationaryMFG.Periodic.UnitCube d)) :=
    aemeasurable_pi_iff.mpr fun i => (hDuLp i).aestronglyMeasurable.aemeasurable
  have hm_aem : AEMeasurable (fam.m ε)
      (volume.restrict (StationaryMFG.Periodic.UnitCube d)) :=
    hmLp.aestronglyMeasurable.aemeasurable
  have hK0_aem :
      AEMeasurable
        (fun x => HdeltaK0 hweak ε x (fun i => fam.Du ε i x) (fam.m ε x))
        (volume.restrict (StationaryMFG.Periodic.UnitCube d)) :=
    StationaryMFG.InfimalConvolution.aemeasurable_HdeltaK0_comp_of_rc0
      hweak hMeas hmon qε sel hε hDu_aem hm_aem hmNonneg
  have hHdelta_aem :
      AEMeasurable
        (fun x => HdeltaK0 hweak ε x (fun i => fam.Du ε i x) (fam.m ε x))
        (volume.restrict (StationaryMFG.Periodic.UnitCube d)) := hK0_aem
  have hHdelta_aesm :
      AEStronglyMeasurable
        (fun x => HdeltaK0 hweak ε x (fun i => fam.Du ε i x) (fam.m ε x))
        (volume.restrict (StationaryMFG.Periodic.UnitCube d)) :=
    hHdelta_aem.aestronglyMeasurable
  -- Step 7: close with `MemLp.mono'` against the dominator `g_ε`.
  have hEnv := T3.hComposite_envelope_of_family hweak qε V fam hmon
    hdiff sel hAE hUB hC0_le ε hε hε1ε
  -- The envelope `|HdeltaK0 …| ≤ g_ε` matches `‖HdeltaK0 …‖ ≤ g_ε x`.
  have hdom :
      ∀ᵐ x ∂(volume.restrict (StationaryMFG.Periodic.UnitCube d)),
        ‖HdeltaK0 hweak ε x (fun i => fam.Du ε i x) (fam.m ε x)‖
          ≤ Cε * (‖(fun i : Fin d => fam.Du ε i x)‖ ^ hweak.α
              + fam.m ε x ^ hweak.β + 1) := by
    filter_upwards [hEnv] with x hx
    rw [Real.norm_eq_abs]
    -- `hEnv` uses `CdeltaEps … hweak ε`; align with the local `Cε`.
    simpa [hCε_def] using hx
  exact MemLp.toMemLpPer (MeasureTheory.MemLp.mono' hgLp.toMemLp hHdelta_aesm hdom)

/-! ## D6e-4: the HJB residual `MemLpPer (β̄')` and `hResRaw` from the family

The §1b residual-`MemLpPer` construction (THE ORIGINAL D6e GOAL) packages the
HJB residual `R_ε = −u_ε − H^ε(Du_ε, m_ε) + V` as a member of `L^{β̄'}_per`,
`β̄' = (β+1)/β`, from three summands:

* `−u_ε ∈ L^{β̄'}`: `u_ε ∈ W^{1,γ̄} ⊆ L^{γ̄}` (`fam.huSob`), and `β̄' ≤ γ̄`
  (since `γ̄ = α·β̄'` with `α > 1`), so `MemLpPer.mono_exponent_finite` lands
  `u_ε ∈ L^{β̄'}`; negate via `const_smul (-1)`.
* `−H^ε(Du_ε, m_ε) ∈ L^{β̄'}`: the H-composite `MemLpPer (β̄')` of D6e-3
  (`T3.hComposite_memLpPer_of_family`); negate.
* `V ∈ L^{β̄'}`: `hV` after `betaBar'_eq_of_holderConjugate hpqβ` aligns the
  abstract conjugate `βBar'` with `betaBar' hweak.β`.

The three combine via `MemLpPer.add` after rewriting `hjbResidual` to the sum
`((-1) • u) + ((-1) • Hcomp) + V`.  Threading this per-`ε` `MemLpPer` through
the D4b seam `hRes_of_residual_memLpPer` yields the `Integrable`
`hResRaw` shape, dropping `hResRaw` as a binder of the `of_family` producer.

GATE #1: the seam `hRes_of_residual_memLpPer` IS called.  Binders are
`fam` plus the paper-accepted carriers `hMeas`/`hmon`/`hdiff`/`sel`/
`hAE`/`hUB`/`hV` and the constant/exponent reconciliations
`hC0_le`/`hε1`/`hpqβ`/`hβBar`/`hγBar`; NO loose `m`/`u`/`Du`/`hResRaw`. -/
theorem T3.hResRaw_of_T3RegularizedStrongFamily
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d) {βBarReal γBarReal βBar' : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    (fam : T3RegularizedStrongFamily V hweak qε βBarReal γBarReal)
    (hMeas : StationaryMFG.Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hdiff : HypothesisHpDifferentiable (d := d) H DpH)
    (sel : StationaryMFG.InfimalConvolution.InfConvSelectorFamily
      (H := H) (DpH := DpH) hweak qε)
    (hAE : HdeltaAEPowerEpsData (H := H) (DpH := DpH) hweak qε)
    (hUB : HdeltaUniformBounds (H := H) (DpH := DpH) hweak qε)
    (hC0_le : ∀ ε : ℝ, ε > 0 →
      hUB.C0 ≤ CdeltaEps (H := H) (DpH := DpH) hweak ε)
    (hpqβ : βBarReal.HolderConjugate βBar')
    (hV : Periodic.MemLpPer (ENNReal.ofReal βBar') V)
    (hβBar : βBarReal = StationaryMFG.Hamiltonian.betaBar hweak.β)
    (hγBar : γBarReal = StationaryMFG.Hamiltonian.gammaBar hweak.α hweak.β) :
    ∀ ε, 0 < ε → ε ≤ 1 →
      Integrable
        (hjbResidual V (HdeltaK0 hweak ε) (fam.Du ε) (fam.m ε) (fam.u ε))
        (volume.restrict (UnitCube d)) := by
  classical
  -- Concrete paper exponents.
  have hα1 : (1 : ℝ) < hweak.α := hweak.hα
  have hβ0 : (0 : ℝ) < hweak.β := hweak.hβ
  have hαpos : (0 : ℝ) < hweak.α := lt_trans one_pos hα1
  -- The abstract conjugate exponent is exactly `betaBar' hweak.β`.
  have hβBar'_eq : βBar' = StationaryMFG.Hamiltonian.betaBar' hweak.β :=
    betaBar'_eq_of_holderConjugate hpqβ (by rw [hβBar]; rfl)
  set β' : ℝ := StationaryMFG.Hamiltonian.betaBar' hweak.β with hβ'_def
  have hβ'_pos : 0 < β' := by
    rw [hβ'_def]; unfold StationaryMFG.Hamiltonian.betaBar'; positivity
  -- `β̄' ≤ γ̄` (since `γ̄ = α·β̄'` with `α > 1`).
  have hγbar_eq : StationaryMFG.Hamiltonian.gammaBar hweak.α hweak.β = hweak.α * β' := by
    rw [hβ'_def]
    exact StationaryMFG.Hamiltonian.gammaBar_eq_alpha_mul_betaBar'
      hweak.α hweak.β (ne_of_gt hβ0)
  have hβ'_le_γ : β' ≤ γBarReal := by
    rw [hγBar, hγbar_eq]
    nlinarith [hβ'_pos, hα1]
  -- The per-`ε` residual `MemLpPer (ofReal β')`.
  have hRes_Lp : ∀ ε, 0 < ε → ε ≤ 1 →
      Periodic.MemLpPer (ENNReal.ofReal β')
        (hjbResidual V (HdeltaK0 hweak ε) (fam.Du ε) (fam.m ε) (fam.u ε)) := by
    intro ε hε hε1ε
    -- `−u_ε ∈ L^{β̄'}` from `u_ε ∈ L^{γ̄}` downgraded by Hölder inclusion.
    have huLp_γ : Periodic.MemLpPer (ENNReal.ofReal γBarReal) (fam.u ε) :=
      (fam.huSob ε hε hε1ε).1
    have huLp : Periodic.MemLpPer (ENNReal.ofReal β') (fam.u ε) :=
      Periodic.MemLpPer.mono_exponent_finite
        (ENNReal.ofReal_le_ofReal hβ'_le_γ) ENNReal.ofReal_ne_top huLp_γ
    have hnegU : Periodic.MemLpPer (ENNReal.ofReal β')
        ((-1 : ℝ) • fam.u ε) := huLp.const_smul (-1 : ℝ)
    -- `−H^ε(Du_ε, m_ε) ∈ L^{β̄'}` from D6e-3.
    have hHcomp : Periodic.MemLpPer (ENNReal.ofReal β')
        (fun x => HdeltaK0 hweak ε x (fun i => fam.Du ε i x) (fam.m ε x)) := by
      have h := T3.hComposite_memLpPer_of_family hweak qε V fam hMeas hmon
        hdiff sel hAE hUB hC0_le hβBar hγBar ε hε hε1ε
      rw [hβ'_def]; exact h
    have hnegH : Periodic.MemLpPer (ENNReal.ofReal β')
        ((-1 : ℝ) • (fun x => HdeltaK0 hweak ε x (fun i => fam.Du ε i x) (fam.m ε x))) :=
      hHcomp.const_smul (-1 : ℝ)
    -- `V ∈ L^{β̄'}`.
    have hVLp : Periodic.MemLpPer (ENNReal.ofReal β') V := by
      rw [← hβBar'_eq]; exact hV
    -- Sum the three; rewrite to `hjbResidual`.
    have hsum := (hnegU.add hnegH).add hVLp
    have heq :
        (((-1 : ℝ) • fam.u ε) + ((-1 : ℝ) •
            (fun x => HdeltaK0 hweak ε x (fun i => fam.Du ε i x) (fam.m ε x)))) + V
          = hjbResidual V (HdeltaK0 hweak ε) (fam.Du ε) (fam.m ε) (fam.u ε) := by
      funext x
      simp only [hjbResidual, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [heq] at hsum
    exact hsum
  -- Thread the residual `MemLpPer` through the D4b seam (GATE #1).
  have hβ'_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal β' := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
    exact ENNReal.ofReal_le_ofReal
      (le_of_lt (by rw [hβ'_def]; exact one_lt_betaBar' hweak.β hβ0))
  exact fun ε hε hε1ε =>
    hRes_of_residual_memLpPer hβ'_le (hRes_Lp ε hε hε1ε)

/-- **D6c-1 (`hResM`): the HJB residual times the density is `L¹`.**

For the produced strong-VI family `fam`, the per-`ε` product
`hjbResidual V (HdeltaK0 hweak ε) (fam.Du ε) (fam.m ε) (fam.u ε) · fam.m ε`
is integrable on the cube. This is the HJB-half carrier
(`hResM`) consumed by `T3.hIdentityRaw_of_T3RegularizedStrongFamily`
(D6c-3).

The proof reuses the residual `MemLpPer (β̄')` membership constructed inside
`T3.hResRaw_of_T3RegularizedStrongFamily` (via `hComposite_memLpPer_of_family`
for the H-composite, plus the `u`/`V` summands), pairs it with the density
`fam.m ε ∈ L^{β̄}` (`fam.hmLp`), and applies the Hölder product integrability
`Periodic.MemLpPer.integrable_mul` for the conjugate pair `(β̄', β̄)`.

`fam` IS a binder; the remaining binders are the accepted §1b carriers
(`hMeas`/`hmon`/`hdiff`/`sel`/`hAE`/`hUB`/`hC0_le`/`hε1`) plus the
exponent/Hölder reconciliations (`hpqβ`/`hβBar`/`hγBar`) and `hV`.  NO `hPow`,
NO loose `m`/`u`/`Du`. -/
theorem T3.hResM_of_T3RegularizedStrongFamily
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d) {βBarReal γBarReal βBar' : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    (fam : T3RegularizedStrongFamily V hweak qε βBarReal γBarReal)
    (hMeas : StationaryMFG.Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hdiff : HypothesisHpDifferentiable (d := d) H DpH)
    (sel : StationaryMFG.InfimalConvolution.InfConvSelectorFamily
      (H := H) (DpH := DpH) hweak qε)
    (hAE : HdeltaAEPowerEpsData (H := H) (DpH := DpH) hweak qε)
    (hUB : HdeltaUniformBounds (H := H) (DpH := DpH) hweak qε)
    (hC0_le : ∀ ε : ℝ, ε > 0 →
      hUB.C0 ≤ CdeltaEps (H := H) (DpH := DpH) hweak ε)
    (hpqβ : βBarReal.HolderConjugate βBar')
    (hV : Periodic.MemLpPer (ENNReal.ofReal βBar') V)
    (hβBar : βBarReal = StationaryMFG.Hamiltonian.betaBar hweak.β)
    (hγBar : γBarReal = StationaryMFG.Hamiltonian.gammaBar hweak.α hweak.β) :
    ∀ ε, 0 < ε → ε ≤ 1 →
      Integrable
        (fun x => hjbResidual V (HdeltaK0 hweak ε) (fam.Du ε)
                    (fam.m ε) (fam.u ε) x * fam.m ε x)
        (volume.restrict (UnitCube d)) := by
  classical
  have hβ0 : (0 : ℝ) < hweak.β := hweak.hβ
  -- The abstract conjugate is the concrete paper conjugate `betaBar' hweak.β`.
  have hβBar'_eq : βBar' = StationaryMFG.Hamiltonian.betaBar' hweak.β :=
    betaBar'_eq_of_holderConjugate hpqβ (by rw [hβBar]; rfl)
  -- The per-`ε` residual `MemLpPer (β̄')` — re-derived as in `hResRaw`.
  have hα1 : (1 : ℝ) < hweak.α := hweak.hα
  have hαpos : (0 : ℝ) < hweak.α := lt_trans one_pos hα1
  set β' : ℝ := StationaryMFG.Hamiltonian.betaBar' hweak.β with hβ'_def
  have hβ'_pos : 0 < β' := by
    rw [hβ'_def]; unfold StationaryMFG.Hamiltonian.betaBar'; positivity
  have hγbar_eq : StationaryMFG.Hamiltonian.gammaBar hweak.α hweak.β
      = hweak.α * β' := by
    rw [hβ'_def]
    exact StationaryMFG.Hamiltonian.gammaBar_eq_alpha_mul_betaBar'
      hweak.α hweak.β (ne_of_gt hβ0)
  have hβ'_le_γ : β' ≤ γBarReal := by
    rw [hγBar, hγbar_eq]; nlinarith [hβ'_pos, hα1]
  intro ε hε hε1ε
  -- `−u_ε ∈ L^{β̄'}` from `u_ε ∈ L^{γ̄}` downgraded by Hölder inclusion.
  have huLp_γ : Periodic.MemLpPer (ENNReal.ofReal γBarReal) (fam.u ε) :=
    (fam.huSob ε hε hε1ε).1
  have huLp : Periodic.MemLpPer (ENNReal.ofReal β') (fam.u ε) :=
    Periodic.MemLpPer.mono_exponent_finite
      (ENNReal.ofReal_le_ofReal hβ'_le_γ) ENNReal.ofReal_ne_top huLp_γ
  have hnegU : Periodic.MemLpPer (ENNReal.ofReal β')
      ((-1 : ℝ) • fam.u ε) := huLp.const_smul (-1 : ℝ)
  -- `−H^ε(Du_ε, m_ε) ∈ L^{β̄'}` from D6e-3.
  have hHcomp : Periodic.MemLpPer (ENNReal.ofReal β')
      (fun x => HdeltaK0 hweak ε x (fun i => fam.Du ε i x) (fam.m ε x)) := by
    have h := T3.hComposite_memLpPer_of_family hweak qε V fam hMeas hmon
      hdiff sel hAE hUB hC0_le hβBar hγBar ε hε hε1ε
    rw [hβ'_def]; exact h
  have hnegH : Periodic.MemLpPer (ENNReal.ofReal β')
      ((-1 : ℝ) • (fun x => HdeltaK0 hweak ε x (fun i => fam.Du ε i x)
        (fam.m ε x))) := hHcomp.const_smul (-1 : ℝ)
  -- `V ∈ L^{β̄'}`.
  have hVLp : Periodic.MemLpPer (ENNReal.ofReal β') V := by
    rw [← hβBar'_eq]; exact hV
  -- Sum the three; rewrite to `hjbResidual`.
  have hsum := (hnegU.add hnegH).add hVLp
  have heqRes :
      (((-1 : ℝ) • fam.u ε) + ((-1 : ℝ) •
          (fun x => HdeltaK0 hweak ε x (fun i => fam.Du ε i x) (fam.m ε x)))) + V
        = hjbResidual V (HdeltaK0 hweak ε) (fam.Du ε) (fam.m ε) (fam.u ε) := by
    funext x
    simp only [hjbResidual, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [heqRes] at hsum
  -- The density `m_ε ∈ L^{β̄}` and `β̄' .HolderConjugate β̄`.
  have hmLp : Periodic.MemLpPer (ENNReal.ofReal βBarReal) (fam.m ε) :=
    fam.hmLp ε hε hε1ε
  have hpqβ' : β'.HolderConjugate βBarReal := by
    rw [← hβBar'_eq]; exact hpqβ.symm
  -- Hölder product: `residual · m ∈ L¹`.
  have hres' : Periodic.MemLpPer (ENNReal.ofReal β')
      (hjbResidual V (HdeltaK0 hweak ε) (fam.Du ε) (fam.m ε) (fam.u ε)) := by
    rw [hβ'_def]; rw [hβ'_def] at hsum; exact hsum
  exact Periodic.MemLpPer.integrable_mul hpqβ' hres' hmLp

/-! ## D6i (child A): the SET-form closed-cone K0 segment dominator

`T3.hContRaw_of_T3RegularizedStrongFamily` (D6d) needs, as binders, the DCT
dominator bundle `g_unreg g_gat / hg_*_int / hF_*_meas / hF_*_bound` for the
closed-cone density-segment integrand at the SET test direction
`(Dν, η, ν) = (0, 1_S, 0)`, gradient FIXED `fam.Du ε`, value FIXED `fam.u ε`,
density varying `μt = cxComb (m+1_S) m t = m + t·1_S ∈ [m, m+1_S]`.

**Collapse.** With `Dν = 0`, `ν = 0`, the K0 integrand
`aepsiIntegrandAt_unreg_K0 … = (-υt - HdeltaK0 x Dυt μt + V x)·η x` (the flux term
`JsimpleExt … ⬝ 0` and the value term `(μt-1)·0` both vanish), and the gateaux
integrand `aepsiIntegrandAt_gateaux γ̄ Du Du u u 0 0 x t = 0` identically. So
`g_gat ε S := 0` works, and the unregularised dominator is the t-uniform
`g_unreg ε S x := |u x| + Cε·(‖Du·x‖^α + (m x + 1)^β + 1) + |V x|`, using
`μt ≤ m + 1 ⇒ μt^β ≤ (m+1)^β` (β > 0, m ≥ 0) and `η = 1_S ≤ 1`.

This is the fam-based, `hPow`-free producer the D6h assembly consumes. -/

/-- **Variable-density H-envelope for the set segment.** For a.e. `x`, every
density `μ` with `0 ≤ m(x) ≤ μ ≤ m(x)+1` satisfies
`|HdeltaK0 hweak ε x (Du·x) μ| ≤ Cε·(‖Du·x‖^α + (m x + 1)^β + 1)`.

Mirror of `T3.hComposite_envelope_of_family` but at the **variable** segment
density `μ ∈ [m, m+1]` (gradient still fixed at `fam.Du ε`). Case-split on
`0 < μ` (`hAE.{H_upper_pointwise_ae, lower_ae}`) vs `μ = 0`
(`Hdelta_zero_upper_of_selectorFamily` + `t3_hH0_of_bounds`, with
`hUB.C0 ≤ Cε`), then `μ^β ≤ (m+1)^β` upgrades the envelope to the
t-uniform `(m+1)^β` form. -/
theorem T3.hHdeltaSegEnvelope_of_family
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d) {βBarReal γBarReal : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    (fam : T3RegularizedStrongFamily V hweak qε βBarReal γBarReal)
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hdiff : HypothesisHpDifferentiable (d := d) H DpH)
    (sel : StationaryMFG.InfimalConvolution.InfConvSelectorFamily
      (H := H) (DpH := DpH) hweak qε)
    (hAE : HdeltaAEPowerEpsData (H := H) (DpH := DpH) hweak qε)
    (hUB : HdeltaUniformBounds (H := H) (DpH := DpH) hweak qε)
    (hC0_le : ∀ ε : ℝ, ε > 0 →
      hUB.C0 ≤ CdeltaEps (H := H) (DpH := DpH) hweak ε)
    :
    ∀ ε, 0 < ε → ε ≤ 1 → ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ μ : ℝ, fam.m ε x ≤ μ → μ ≤ fam.m ε x + 1 →
          |HdeltaK0 hweak ε x (fun i => fam.Du ε i x) μ|
            ≤ CdeltaEps (H := H) (DpH := DpH) hweak ε
                * (‖(fun i => fam.Du ε i x)‖ ^ hweak.α
                    + (fam.m ε x + 1) ^ hweak.β + 1) := by
  intro ε hε hε1ε
  set Cε : ℝ := CdeltaEps (H := H) (DpH := DpH) hweak ε with hCε_def
  have hCε_pos : 0 < Cε := CdeltaEps_pos (H := H) (DpH := DpH) hweak hε
  have hUp : ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p m, 0 < m →
      HdeltaK0 hweak ε x p m ≤ CdeltaEps hweak ε * (‖p‖ ^ hweak.α + 1) -
        m ^ hweak.β / CdeltaEps hweak ε := by
    filter_upwards [hAE.H_upper_pointwise_ae ε hε hε1ε] with x hx p m hm
    rw [HdeltaK0_eq_Hdelta_of_pos hweak hm]
    exact hx p m hm
  have hLow : ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p m, 0 < m →
      ‖p‖ ^ hweak.α / CdeltaEps hweak ε - CdeltaEps hweak ε * (m ^ hweak.β + 1) ≤
        HdeltaK0 hweak ε x p m := by
    filter_upwards [hAE.lower_ae ε hε hε1ε] with x hx p m hm
    rw [HdeltaK0_eq_Hdelta_of_pos hweak hm]
    exact hx p m hm
  have hZeroUp := Hdelta_zero_upper_of_selectorFamily (H := H) (DpH := DpH)
    hweak hmon qε sel hAE hε hε1ε
  have hZeroLow := t3_hH0_of_bounds hweak qε hUB hmon hdiff sel ε hε hε1ε
  have hC0_le_ε : hUB.C0 ≤ Cε := hC0_le ε hε
  filter_upwards [hUp, hLow, hZeroUp, hZeroLow, fam.hmNonneg ε hε hε1ε]
    with x hxUp hxLow hxZeroUp hxZeroLow hxNonneg
  intro μ hμlo hμhi
  set p : Fin d → ℝ := fun i => fam.Du ε i x with hp_def
  set m : ℝ := fam.m ε x with hm_def
  set B : ℝ := Cε * (‖p‖ ^ hweak.α + (m + 1) ^ hweak.β + 1) with hB_def
  have hpα_nn : (0 : ℝ) ≤ ‖p‖ ^ hweak.α := Real.rpow_nonneg (norm_nonneg _) _
  have hm1_nn : (0 : ℝ) ≤ m + 1 := by linarith [hxNonneg]
  have hm1β_nn : (0 : ℝ) ≤ (m + 1) ^ hweak.β := Real.rpow_nonneg hm1_nn _
  -- `μ ≥ 0`.
  have hμ_nn : (0 : ℝ) ≤ μ := le_trans hxNonneg hμlo
  rw [abs_le]
  rcases lt_or_eq_of_le hμ_nn with hμpos | hμzero
  · -- Case `0 < μ`.
    have hμpos' : 0 < μ := hμpos
    have hμβ_nn : (0 : ℝ) ≤ μ ^ hweak.β := Real.rpow_nonneg hμ_nn _
    -- `μ^β ≤ (m+1)^β` since `0 ≤ μ ≤ m+1` and `β > 0`.
    have hμβ_le : μ ^ hweak.β ≤ (m + 1) ^ hweak.β :=
      Real.rpow_le_rpow hμ_nn hμhi hweak.hβ.le
    have hUpx : HdeltaK0 hweak ε x p μ
        ≤ Cε * (‖p‖ ^ hweak.α + 1) - μ ^ hweak.β / Cε := hxUp p μ hμpos'
    have hLowx : ‖p‖ ^ hweak.α / Cε - Cε * (μ ^ hweak.β + 1)
        ≤ HdeltaK0 hweak ε x p μ := hxLow p μ hμpos'
    have hdiv_nn : (0 : ℝ) ≤ μ ^ hweak.β / Cε :=
      div_nonneg hμβ_nn (le_of_lt hCε_pos)
    have hpdiv_nn : (0 : ℝ) ≤ ‖p‖ ^ hweak.α / Cε :=
      div_nonneg hpα_nn (le_of_lt hCε_pos)
    refine ⟨?_, ?_⟩
    · -- `−B ≤ HdeltaK0`.
      have hstep : -B ≤ ‖p‖ ^ hweak.α / Cε - Cε * (μ ^ hweak.β + 1) := by
        rw [hB_def]
        nlinarith [hpdiv_nn, hpα_nn, hμβ_le, hm1β_nn, hCε_pos]
      linarith [hstep, hLowx]
    · -- `HdeltaK0 ≤ B`.
      have hstep : HdeltaK0 hweak ε x p μ ≤ Cε * (‖p‖ ^ hweak.α + 1) := by
        linarith [hUpx, hdiv_nn]
      have hupper_target : Cε * (‖p‖ ^ hweak.α + 1) ≤ B := by
        rw [hB_def]
        nlinarith [mul_nonneg (le_of_lt hCε_pos) hm1β_nn]
      linarith [hstep, hupper_target]
  · -- Case `μ = 0`.
    have hμ0 : μ = 0 := hμzero.symm
    have hUpx0 : HdeltaK0 hweak ε x p 0 ≤ Cε * (‖p‖ ^ hweak.α + 1) := hxZeroUp p
    have hLowx0 : ‖p‖ ^ hweak.α / hUB.C0 - hUB.C0 ≤ HdeltaK0 hweak ε x p 0 := hxZeroLow p
    have hC0_pos : 0 < hUB.C0 := hUB.hC0
    have hpdiv0_nn : (0 : ℝ) ≤ ‖p‖ ^ hweak.α / hUB.C0 :=
      div_nonneg hpα_nn (le_of_lt hC0_pos)
    have hupper_target : Cε * (‖p‖ ^ hweak.α + 1) ≤ B := by
      rw [hB_def]
      nlinarith [mul_nonneg (le_of_lt hCε_pos) hm1β_nn]
    rw [hμ0]
    refine ⟨?_, ?_⟩
    · -- `−B ≤ HdeltaK0(x,p,0)`.
      have hneg : -B ≤ -hUB.C0 := by
        have hge : hUB.C0 ≤ Cε * (‖p‖ ^ hweak.α + 1) := by
          nlinarith [hpα_nn, le_of_lt hCε_pos, hC0_le_ε]
        linarith [hge, hupper_target]
      have hchain : -hUB.C0 ≤ ‖p‖ ^ hweak.α / hUB.C0 - hUB.C0 := by linarith [hpdiv0_nn]
      linarith [hneg, hchain, hLowx0]
    · -- `HdeltaK0(x,p,0) ≤ B`.
      linarith [hUpx0, hupper_target]

/-- **D6i child A: the SET-form closed-cone K0 segment dominator (fam-based,
`hPow`-free).**

Produces the DCT dominator/measurability bundle consumed by
`T3.hContRaw_of_T3RegularizedStrongFamily` (D6d): the dominating functions
`g_unreg g_gat`, their `IntegrableOn` certificates, and the `hF_*_meas` /
`hF_*_bound` facts at the SET test direction `(0, 1_S, 0)`.

Binders are `fam` plus the paper-accepted carriers
`hMeas/hmon/hdiff/sel/hAE/hUB` and the constant/exponent
reconciliations `hC0_le/hε1/hβBar/hγ/hpqβ` and `hV`. NO `hPow`, NO loose
`m`/`u`/`Du`, NO T1 weak-limit triple. -/
theorem T3.setSegmentDominator_of_T3RegularizedStrongFamily
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d) {βBarReal γBarReal βBar' : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    (fam : T3RegularizedStrongFamily V hweak qε βBarReal γBarReal)
    (hMeas : StationaryMFG.Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hdiff : HypothesisHpDifferentiable (d := d) H DpH)
    (sel : StationaryMFG.InfimalConvolution.InfConvSelectorFamily
      (H := H) (DpH := DpH) hweak qε)
    (hAE : HdeltaAEPowerEpsData (H := H) (DpH := DpH) hweak qε)
    (hUB : HdeltaUniformBounds (H := H) (DpH := DpH) hweak qε)
    (hC0_le : ∀ ε : ℝ, ε > 0 →
      hUB.C0 ≤ CdeltaEps (H := H) (DpH := DpH) hweak ε)
    (hβBar : βBarReal = hweak.β + 1)
    (hγ : 1 < γBarReal)
    (hαγ : hweak.α ≤ γBarReal)
    (hpqβ : βBarReal.HolderConjugate βBar')
    (hV : Periodic.MemLpPer (ENNReal.ofReal βBar') V) :
    ∃ g_unreg g_gat :
        (ε : ℝ) → (S : Set (Fin d → ℝ)) → (Fin d → ℝ) → ℝ,
      (∀ ε, 0 < ε → ε ≤ 1 → ∀ (S : Set (Fin d → ℝ)),
          IntegrableOn (g_unreg ε S) (UnitCube d)) ∧
      (∀ ε, 0 < ε → ε ≤ 1 → ∀ (S : Set (Fin d → ℝ)),
          IntegrableOn (g_gat ε S) (UnitCube d)) ∧
      (∀ ε, 0 < ε → ε ≤ 1 → ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
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
            (volume.restrict (UnitCube d))) ∧
      (∀ ε, 0 < ε → ε ≤ 1 → ∀ (S : Set (Fin d → ℝ)), ∀ t ∈ Set.Icc (0 : ℝ) 1,
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
              ≤ g_unreg ε S x) ∧
      (∀ ε, 0 < ε → ε ≤ 1 → ∀ (S : Set (Fin d → ℝ)), ∀ t ∈ Set.Icc (0 : ℝ) 1,
          AEStronglyMeasurable
            (fun x =>
              aepsiIntegrandAt_gateaux (d := d) γBarReal
                (fam.Du ε) (fam.Du ε) (fam.u ε) (fam.u ε)
                (fun _ _ => (0 : ℝ)) (fun _ => (0 : ℝ)) x t)
            (volume.restrict (UnitCube d))) ∧
      (∀ ε, 0 < ε → ε ≤ 1 → ∀ (S : Set (Fin d → ℝ)), ∀ t ∈ Set.Icc (0 : ℝ) 1,
          ∀ᵐ x ∂(volume.restrict (UnitCube d)),
            ‖aepsiIntegrandAt_gateaux (d := d) γBarReal
                (fam.Du ε) (fam.Du ε) (fam.u ε) (fam.u ε)
                (fun _ _ => (0 : ℝ)) (fun _ => (0 : ℝ)) x t‖
              ≤ g_gat ε S x) := by
  classical
  haveI hcube_fin : MeasureTheory.IsFiniteMeasure
      (volume.restrict (UnitCube d) : Measure (Fin d → ℝ)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
          volume_unitCube]; exact ENNReal.one_lt_top⟩
  have hβ0 : (0 : ℝ) < hweak.β := hweak.hβ
  have hα1 : (1 : ℝ) < hweak.α := hweak.hα
  -- The variable-density H-envelope (reused for the bound half).
  have hEnv := T3.hHdeltaSegEnvelope_of_family hweak qε V fam hmon
    hdiff sel hAE hUB hC0_le
  -- The set-form dominators: `g_gat = 0`, and
  -- `g_unreg ε S x = |u| + Cε·(‖Du‖^α + (m+1)^β + 1) + |V|`.
  refine ⟨fun ε _S x =>
      |fam.u ε x|
        + CdeltaEps (H := H) (DpH := DpH) hweak ε
            * (‖(fun i => fam.Du ε i x)‖ ^ hweak.α
                + (fam.m ε x + 1) ^ hweak.β + 1)
        + |V x|,
    fun _ε _S _x => (0 : ℝ), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `hg_unreg_int`: integrability of the dominator.
    intro ε hε hε1ε S
    set Cε : ℝ := CdeltaEps (H := H) (DpH := DpH) hweak ε with hCε_def
    -- `|u| ∈ L¹`.
    have hu_int : Integrable (fun x => |fam.u ε x|) (volume.restrict (UnitCube d)) := by
      have huLp_γ : MemLpPer (ENNReal.ofReal γBarReal) (fam.u ε) :=
        (fam.huSob ε hε hε1ε).1
      have h1le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal γBarReal := by
        rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
        exact ENNReal.ofReal_le_ofReal hγ.le
      exact (huLp_γ.toMemLp.integrable h1le).abs
    -- `|V| ∈ L¹` via the existing producer.
    have hV_int : Integrable (fun x => |V x|) (volume.restrict (UnitCube d)) :=
      t3_hVint_int_of_family hweak hpqβ hβBar hV
    -- `‖Du·x‖^α ∈ L¹`: each `Du ε i ∈ L^{γ̄}` and `‖·‖^α ∈ L^{γ̄/α} ⊆ L¹`.
    have hDuLp : ∀ i, MemLpPer (ENNReal.ofReal γBarReal) (fam.Du ε i) :=
      fun i => fam.hDuLp ε hε hε1ε i
    -- `‖Du·x‖ ∈ L^{γ̄}` (coordinate domination by `∑ i |Du i x|`).
    have hNormLp : MemLpPer (ENNReal.ofReal γBarReal)
        (fun x : (Fin d → ℝ) => ‖(fun i : Fin d => fam.Du ε i x)‖) := by
      set q : ℝ≥0∞ := ENNReal.ofReal γBarReal with hq_def
      have habs_memLp : ∀ i, MemLpPer (d := d) q (fun x => |fam.Du ε i x|) := by
        intro i
        have h2 := (hDuLp i).toMemLp.norm
        have heq : (fun x => ‖fam.Du ε i x‖) = fun x => |fam.Du ε i x| := by
          funext x; exact Real.norm_eq_abs _
        rw [heq] at h2
        exact MemLp.toMemLpPer h2
      have hDom_memLp : MemLpPer (d := d) q
          (fun x => ∑ i : Fin d, |fam.Du ε i x|) :=
        MemLp.toMemLpPer
          (MeasureTheory.memLp_finset_sum (Finset.univ : Finset (Fin d))
            (fun i _ => (habs_memLp i).toMemLp))
      have hbound :
          ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
            ‖‖(fun i : Fin d => fam.Du ε i x)‖‖
              ≤ (1 : ℝ) * ‖∑ i, |fam.Du ε i x|‖ := by
        refine Filter.Eventually.of_forall ?_
        intro x
        have hsum_nn : 0 ≤ ∑ i, |fam.Du ε i x| :=
          Finset.sum_nonneg (fun i _ => abs_nonneg _)
        have hpi : ‖(fun i : Fin d => fam.Du ε i x)‖ ≤ ∑ i, |fam.Du ε i x| := by
          rw [pi_norm_le_iff_of_nonneg hsum_nn]
          intro i
          rw [Real.norm_eq_abs]
          exact Finset.single_le_sum (f := fun j => |fam.Du ε j x|)
            (fun j _ => abs_nonneg _) (Finset.mem_univ i)
        have h1 : ‖‖(fun i : Fin d => fam.Du ε i x)‖‖
            = ‖(fun i : Fin d => fam.Du ε i x)‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        have h2 : (1 : ℝ) * ‖∑ i, |fam.Du ε i x|‖ = ∑ i, |fam.Du ε i x| := by
          rw [one_mul, Real.norm_eq_abs, abs_of_nonneg hsum_nn]
        rw [h1, h2]; exact hpi
      have hmeas :
          AEStronglyMeasurable
            (fun x : (Fin d → ℝ) => ‖(fun i : Fin d => fam.Du ε i x)‖)
            (Measure.restrict volume (UnitCube d)) := by
        have hAEm : AEMeasurable
            (fun x : (Fin d → ℝ) => fun i : Fin d => fam.Du ε i x)
            (Measure.restrict volume (UnitCube d)) :=
          aemeasurable_pi_iff.mpr fun i => (hDuLp i).aestronglyMeasurable.aemeasurable
        exact hAEm.norm.aestronglyMeasurable
      exact MemLp.toMemLpPer (MemLp.of_le_mul hDom_memLp.toMemLp hmeas hbound)
    -- `‖Du·x‖^α ∈ L¹` (γ̄ = α·β̄' > α > 1 ⇒ ‖Du‖^α ∈ L^{γ̄/α} with γ̄/α ≥ 1).
    have hDuPow_int : Integrable
        (fun x => ‖(fun i : Fin d => fam.Du ε i x)‖ ^ hweak.α)
        (volume.restrict (UnitCube d)) := by
      have hγ_ne_zero : ENNReal.ofReal γBarReal ≠ 0 :=
        (ENNReal.ofReal_pos.mpr (lt_trans zero_lt_one hγ)).ne'
      have hγ_ne_top : ENNReal.ofReal γBarReal ≠ ⊤ := ENNReal.ofReal_ne_top
      -- `‖Du‖^γ̄ ∈ L¹`.
      have hpow_int : Integrable
          (fun x => ‖(fun i : Fin d => fam.Du ε i x)‖ ^ γBarReal)
          (volume.restrict (UnitCube d)) := by
        have h := hNormLp.toMemLp.integrable_norm_rpow hγ_ne_zero hγ_ne_top
        rw [ENNReal.toReal_ofReal (lt_trans zero_lt_one hγ).le] at h
        refine h.congr ?_
        refine Filter.Eventually.of_forall ?_
        intro x
        simp only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      -- `‖Du‖^α` is dominated by `‖Du‖^γ̄ + 1` (since for s ≥ 0, s^α ≤ s^γ̄ + 1
      -- when α ≤ γ̄): actually use L^{γ̄/α} ⊆ L¹ via rpow_le_rpow split.
      -- Simpler: `s^α ≤ 1 + s^γ̄` for `s ≥ 0, 1 ≤ α ≤ γ̄`.
      have hα_le_γ : hweak.α ≤ γBarReal := hαγ
      have hdom : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          ‖‖(fun i : Fin d => fam.Du ε i x)‖ ^ hweak.α‖
            ≤ (1 : ℝ) + ‖(fun i : Fin d => fam.Du ε i x)‖ ^ γBarReal := by
        refine Filter.Eventually.of_forall ?_
        intro x
        set s : ℝ := ‖(fun i : Fin d => fam.Du ε i x)‖ with hs_def
        have hs_nn : 0 ≤ s := norm_nonneg _
        have hsα_nn : 0 ≤ s ^ hweak.α := Real.rpow_nonneg hs_nn _
        rw [Real.norm_eq_abs, abs_of_nonneg hsα_nn]
        rcases le_or_gt s 1 with hs1 | hs1
        · -- `s ≤ 1 ⇒ s^α ≤ 1`.
          have : s ^ hweak.α ≤ 1 := by
            calc s ^ hweak.α ≤ (1 : ℝ) ^ hweak.α :=
                  Real.rpow_le_rpow hs_nn hs1 (lt_trans zero_lt_one hα1).le
              _ = 1 := Real.one_rpow _
          have hsγ_nn : 0 ≤ s ^ γBarReal := Real.rpow_nonneg hs_nn _
          linarith
        · -- `s > 1 ⇒ s^α ≤ s^γ̄`.
          have : s ^ hweak.α ≤ s ^ γBarReal :=
            Real.rpow_le_rpow_of_exponent_le hs1.le hα_le_γ
          linarith
      have hmeas : AEStronglyMeasurable
          (fun x => ‖(fun i : Fin d => fam.Du ε i x)‖ ^ hweak.α)
          (volume.restrict (UnitCube d)) := by
        have h := hNormLp.aestronglyMeasurable
        exact (h.aemeasurable.pow_const hweak.α).aestronglyMeasurable
      exact Integrable.mono' ((integrable_const (1 : ℝ)).add hpow_int) hmeas hdom
    -- `(m+1)^β ∈ L¹`: `m ∈ L^{β+1} ⊆ L^β`, plus constant ⇒ `(m+1) ∈ L^β`,
    -- then `integrable_norm_rpow`.
    have hm1β_int : Integrable
        (fun x => (fam.m ε x + 1) ^ hweak.β) (volume.restrict (UnitCube d)) := by
      have hmLpβ1 : MemLpPer (ENNReal.ofReal (hweak.β + 1)) (fam.m ε) := by
        rw [← hβBar]; exact fam.hmLp ε hε hε1ε
      have hle : ENNReal.ofReal hweak.β ≤ ENNReal.ofReal (hweak.β + 1) :=
        ENNReal.ofReal_le_ofReal (by linarith)
      have hmLpβ : MemLpPer (ENNReal.ofReal hweak.β) (fam.m ε) :=
        Periodic.MemLpPer.mono_exponent_finite hle ENNReal.ofReal_ne_top hmLpβ1
      have honeLpβ : MemLpPer (d := d) (ENNReal.ofReal hweak.β)
          (fun _ : (Fin d → ℝ) => (1 : ℝ)) := MemLp.toMemLpPer (memLp_const 1)
      have hsumLpβ : MemLpPer (ENNReal.ofReal hweak.β)
          (fun x => fam.m ε x + 1) := by
        have h := hmLpβ.add honeLpβ
        have heq : (fam.m ε + (fun _ : (Fin d → ℝ) => (1 : ℝ)))
            = (fun x => fam.m ε x + 1) := by funext x; simp [Pi.add_apply]
        rwa [heq] at h
      have hβ_ne_zero : ENNReal.ofReal hweak.β ≠ 0 :=
        (ENNReal.ofReal_pos.mpr hβ0).ne'
      have hβ_ne_top : ENNReal.ofReal hweak.β ≠ ⊤ := ENNReal.ofReal_ne_top
      have hnorm_int := hsumLpβ.toMemLp.integrable_norm_rpow hβ_ne_zero hβ_ne_top
      rw [ENNReal.toReal_ofReal hβ0.le] at hnorm_int
      refine hnorm_int.congr ?_
      filter_upwards [fam.hmNonneg ε hε hε1ε] with x hx
      have : (0 : ℝ) ≤ fam.m ε x + 1 := by linarith
      rw [Real.norm_eq_abs, abs_of_nonneg this]
    -- Assemble.
    have hsumPow : Integrable
        (fun x => ‖(fun i : Fin d => fam.Du ε i x)‖ ^ hweak.α
          + (fam.m ε x + 1) ^ hweak.β + 1) (volume.restrict (UnitCube d)) :=
      (hDuPow_int.add hm1β_int).add (integrable_const (1 : ℝ))
    have hCsum : Integrable
        (fun x => Cε * (‖(fun i : Fin d => fam.Du ε i x)‖ ^ hweak.α
          + (fam.m ε x + 1) ^ hweak.β + 1)) (volume.restrict (UnitCube d)) :=
      hsumPow.const_mul Cε
    exact (hu_int.add hCsum).add hV_int
  · -- `hg_gat_int`: the zero dominator is integrable.
    intro ε hε hε1ε S
    exact (integrable_zero _ _ _ : IntegrableOn (fun _ => (0 : ℝ)) (UnitCube d))
  · -- `hF_unreg_meas`: AE-strong measurability of the K0 set integrand
    -- (for measurable `S`). We rewrite the K0 integrand to the collapsed
    -- value `(-u - HdeltaK0(x,Du,μt) + V)·1_S` and assemble measurability of
    -- each piece. The H-composite is measurable via the closed-cone carrier
    -- `aemeasurable_HdeltaK0_comp_of_rc0` transferred to `HdeltaK0` on `{μt≥0}`.
    intro ε hε hε1ε S hS t ht
    have hu_aesm : AEStronglyMeasurable (fam.u ε)
        (volume.restrict (UnitCube d)) := (fam.huSob ε hε hε1ε).1.aestronglyMeasurable
    have hm_aesm : AEStronglyMeasurable (fam.m ε)
        (volume.restrict (UnitCube d)) := (fam.hmLp ε hε hε1ε).aestronglyMeasurable
    have hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)) :=
      hV.aestronglyMeasurable
    have hind_aem : AEMeasurable
        (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)))
        (volume.restrict (UnitCube d)) :=
      (measurable_const.indicator hS).aemeasurable
    -- Segment density `μt = m + t·1_S`.
    set μt : (Fin d → ℝ) → ℝ := fun x =>
        cxComb (fun x => fam.m ε x +
          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) (fam.m ε) t x with hμt_def
    have hμt_nonneg : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ μt x := by
      filter_upwards [fam.hmNonneg ε hε hε1ε] with x hx
      have hindic : (0 : ℝ) ≤ S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x :=
        Set.indicator_nonneg (fun _ _ => zero_le_one) x
      simp only [hμt_def, cxComb]
      have ht0 : (0 : ℝ) ≤ t := ht.1
      have ht1 : t ≤ 1 := ht.2
      nlinarith [hx, hindic, ht0, ht1]
    have hm_aem : AEMeasurable (fam.m ε) (volume.restrict (UnitCube d)) :=
      hm_aesm.aemeasurable
    have hμt_aem : AEMeasurable μt (volume.restrict (UnitCube d)) := by
      simp only [hμt_def, cxComb]
      exact (aemeasurable_const.mul hm_aem).add
        (aemeasurable_const.mul (hm_aem.add hind_aem))
    -- Gradient slot AEMeasurable as a vector.
    have hDu_aem : AEMeasurable (fun x : (Fin d → ℝ) => fun i : Fin d => fam.Du ε i x)
        (volume.restrict (UnitCube d)) :=
      aemeasurable_pi_iff.mpr
        fun i => (fam.hDuLp ε hε hε1ε i).aestronglyMeasurable.aemeasurable
    -- H-composite at `(Du, μt)` AEMeasurable via the closed-cone carrier.
    have hK0_aem :
        AEMeasurable
          (fun x => HdeltaK0 hweak ε x (fun i => fam.Du ε i x) (μt x))
          (volume.restrict (UnitCube d)) :=
      StationaryMFG.InfimalConvolution.aemeasurable_HdeltaK0_comp_of_rc0
        hweak hMeas hmon qε sel hε hDu_aem hμt_aem hμt_nonneg
    have hHdelta_aem :
        AEMeasurable
          (fun x => HdeltaK0 hweak ε x (fun i => fam.Du ε i x) (μt x))
          (volume.restrict (UnitCube d)) := hK0_aem
    have hHdelta_aesm : AEStronglyMeasurable
        (fun x => HdeltaK0 hweak ε x (fun i => fam.Du ε i x) (μt x))
        (volume.restrict (UnitCube d)) := hHdelta_aem.aestronglyMeasurable
    -- The collapsed integrand is measurable: rewrite and assemble.
    have hcollapse :
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
          = (fun x =>
              (-(cxComb (fam.u ε) (fam.u ε) t x)
                  - HdeltaK0 hweak ε x (fun i => fam.Du ε i x) (μt x) + V x)
                * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
      funext x
      have hgrad : (fun i => cxCombGrad (fam.Du ε) (fam.Du ε) t i x)
          = (fun i => fam.Du ε i x) := by
        funext i; simp only [cxCombGrad]; ring
      have hμtx : cxComb (fun x => fam.m ε x +
            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) (fam.m ε) t x = μt x := by
        simp only [hμt_def]
      simp only [aepsiIntegrandAt_unreg_K0, dotProduct,
        mul_zero, Finset.sum_const_zero, hgrad, hμtx, add_zero]
    rw [hcollapse]
    -- `cxComb u u t = u`.
    have hcxu : AEStronglyMeasurable
        (fun x => cxComb (fam.u ε) (fam.u ε) t x)
        (volume.restrict (UnitCube d)) := by
      have heq : (fun x => cxComb (fam.u ε) (fam.u ε) t x) = fam.u ε := by
        funext x; simp only [cxComb]; ring
      rw [heq]; exact hu_aesm
    have hind_aesm : AEStronglyMeasurable
        (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)))
        (volume.restrict (UnitCube d)) := hind_aem.aestronglyMeasurable
    exact (((hcxu.neg.sub hHdelta_aesm).add hVmeas).mul hind_aesm)
  · -- `hF_unreg_bound`: the t-uniform majorant (holds for ALL `S`).
    intro ε hε hε1ε S t ht
    set Cε : ℝ := CdeltaEps (H := H) (DpH := DpH) hweak ε with hCε_def
    filter_upwards [hEnv ε hε hε1ε, fam.hmNonneg ε hε hε1ε] with x hxEnv hxNonneg
    -- The K0 integrand collapses to `(-u - HdeltaK0(x,Du,μt) + V)·1_S`.
    set ind : ℝ := S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x with hind_def
    have hind_nn : (0 : ℝ) ≤ ind := Set.indicator_nonneg (fun _ _ => zero_le_one) x
    have hind_le1 : ind ≤ 1 := by
      rw [hind_def]
      by_cases hx : x ∈ S
      · rw [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx]; exact zero_le_one
    set μt : ℝ := fam.m ε x + t * ind with hμt_def
    have ht0 : (0 : ℝ) ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2
    -- `m ≤ μt ≤ m + 1`.
    have hμt_eq : μt = fam.m ε x + t * ind := hμt_def
    have hμt_lo : fam.m ε x ≤ μt := by
      rw [hμt_eq]; nlinarith [hind_nn, ht0]
    have hμt_hi : μt ≤ fam.m ε x + 1 := by
      rw [hμt_eq]; nlinarith [hind_le1, ht0, ht1, hind_nn]
    -- Envelope at `μt`.
    have henv : |HdeltaK0 hweak ε x (fun i => fam.Du ε i x) μt|
        ≤ Cε * (‖(fun i => fam.Du ε i x)‖ ^ hweak.α
            + (fam.m ε x + 1) ^ hweak.β + 1) := by
      rw [hCε_def]; exact hxEnv μt hμt_lo hμt_hi
    -- The integrand value.
    have hgrad : (fun i => cxCombGrad (fam.Du ε) (fam.Du ε) t i x)
        = (fun i => fam.Du ε i x) := by
      funext i; simp only [cxCombGrad]; ring
    have hval :
        aepsiIntegrandAt_unreg_K0 (d := d) V (HdeltaK0 hweak ε)
          (DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε)
          (fam.Du ε) (fam.Du ε)
          (fun x => fam.m ε x +
            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          (fam.m ε) (fam.u ε) (fam.u ε)
          (fun _ _ => (0 : ℝ))
          (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)))
          (fun _ => (0 : ℝ)) x t
        = (-(fam.u ε x) - HdeltaK0 hweak ε x (fun i => fam.Du ε i x) μt + V x) * ind := by
      have hμtx : cxComb (fun x => fam.m ε x +
            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) (fam.m ε) t x = μt := by
        simp only [cxComb, hμt_def, hind_def]; ring
      have hυt : cxComb (fam.u ε) (fam.u ε) t x = fam.u ε x := by
        simp only [cxComb]; ring
      simp only [aepsiIntegrandAt_unreg_K0, dotProduct,
        mul_zero, Finset.sum_const_zero, hgrad, hμtx, hυt, add_zero]
      ring
    rw [hval, Real.norm_eq_abs, abs_mul]
    -- `|(-u - H + V)| ≤ |u| + |H| + |V|`, and `|ind| ≤ 1`.
    -- Rewrite `-u - H + V = (-u) + (-H) + V` and triangle-bound.
    set uu : ℝ := fam.u ε x
    set HH : ℝ := HdeltaK0 hweak ε x (fun i => fam.Du ε i x) μt
    set VV : ℝ := V x
    have hrw : -uu - HH + VV = (-uu) + (-HH) + VV := by ring
    have htri : |(-uu) + (-HH) + VV| ≤ |(-uu)| + |(-HH)| + |VV| := by
      calc |(-uu) + (-HH) + VV| ≤ |(-uu) + (-HH)| + |VV| := abs_add_le _ _
        _ ≤ (|(-uu)| + |(-HH)|) + |VV| := by
            have := abs_add_le (-uu) (-HH); linarith
        _ = |(-uu)| + |(-HH)| + |VV| := by ring
    have h1 : |(-uu - HH + VV)|
        ≤ |uu|
          + Cε * (‖(fun i => fam.Du ε i x)‖ ^ hweak.α
              + (fam.m ε x + 1) ^ hweak.β + 1)
          + |VV| := by
      rw [hrw]
      have habs_u : |(-uu)| = |uu| := abs_neg _
      have habs_H : |(-HH)| = |HH| := abs_neg _
      rw [habs_u, habs_H] at htri
      have henv' : |HH| ≤ Cε * (‖(fun i => fam.Du ε i x)‖ ^ hweak.α
          + (fam.m ε x + 1) ^ hweak.β + 1) := henv
      linarith [htri, henv']
    have habs_ind : |ind| ≤ 1 := by rw [abs_of_nonneg hind_nn]; exact hind_le1
    set g : ℝ := |uu|
        + Cε * (‖(fun i => fam.Du ε i x)‖ ^ hweak.α
            + (fam.m ε x + 1) ^ hweak.β + 1)
        + |VV| with hg_def
    have hg_nn : (0 : ℝ) ≤ g := le_trans (abs_nonneg _) h1
    calc |(-uu - HH + VV)| * |ind|
        ≤ g * |ind| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ ≤ g * 1 := mul_le_mul_of_nonneg_left habs_ind hg_nn
      _ = g := mul_one _
  · -- `hF_gat_meas`: the gateaux integrand is `0`, measurable.
    intro ε hε _hε1ε _S t ht
    have heq :
        (fun x => aepsiIntegrandAt_gateaux (d := d) γBarReal
          (fam.Du ε) (fam.Du ε) (fam.u ε) (fam.u ε)
          (fun _ _ => (0 : ℝ)) (fun _ => (0 : ℝ)) x t)
          = (fun _ => (0 : ℝ)) := by
      funext x
      simp only [aepsiIntegrandAt_gateaux, dotProduct]
      simp
    rw [heq]
    exact aestronglyMeasurable_const
  · -- `hF_gat_bound`: `‖0‖ ≤ 0`.
    intro ε hε _hε1ε _S t ht
    refine Filter.Eventually.of_forall ?_
    intro x
    have heq : aepsiIntegrandAt_gateaux (d := d) γBarReal
          (fam.Du ε) (fam.Du ε) (fam.u ε) (fam.u ε)
          (fun _ _ => (0 : ℝ)) (fun _ => (0 : ℝ)) x t = 0 := by
      simp only [aepsiIntegrandAt_gateaux, dotProduct]
      simp
    rw [heq, norm_zero]

/-! ## D6c-1b (child): the SIGNED density-segment `hCont` operator-continuity

`T3.hIdentityRaw_of_T3RegularizedStrongFamily` (D6c-3) consumes a SECOND
HJB-half carrier `hCont`: the **signed** density-segment operator continuity
along `ρ_n := m + (1/(n+1))·(σ·m·1_S)`, with gradient/value FIXED at the fam
members, value-test `η = σ·m·1_S`, `ν = 0`, `Dν = 0`. Structurally this mirrors
the SET-form `hContRaw` (D6d) but the density segment is the **multiplicative**
`μt = m·(1 + t·σ·1_S) ∈ [0, 2m]` (σ=+1) or `[0, m]` (σ=−1), and the test slot
`η` now carries the extra factor `m`.

The H-envelope along this segment uses the `(2m)^β = 2^β·m^β` majorant (since
`μt ≤ 2m`), and the dominator carries the extra factor `m·1_S`, so the
integrability is a Hölder pairing `m ∈ L^{β̄}` against the envelope `∈ L^{β̄'}`
(mirroring D6c-1's `hResM`). -/

/-- **Signed variable-density H-envelope.** For a.e. `x`, every density
`μ` with `0 ≤ μ ≤ 2·m(x)` satisfies
`|HdeltaK0 hweak ε x (Du·x) μ| ≤ Cε·(‖Du·x‖^α + 2^β·(m x)^β + 1)`.

Signed companion of `T3.hHdeltaSegEnvelope_of_family` at the **multiplicative**
segment density `μ ∈ [0, 2m]` (gradient still fixed at `fam.Du ε`). Same
case-split on `0 < μ` vs `μ = 0`, then `μ^β ≤ (2m)^β = 2^β·m^β` upgrades the
envelope to the t-uniform `2^β·m^β` form. -/
theorem T3.hHdeltaSegEnvelopeSigned_of_family
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d) {βBarReal γBarReal : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    (fam : T3RegularizedStrongFamily V hweak qε βBarReal γBarReal)
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hdiff : HypothesisHpDifferentiable (d := d) H DpH)
    (sel : StationaryMFG.InfimalConvolution.InfConvSelectorFamily
      (H := H) (DpH := DpH) hweak qε)
    (hAE : HdeltaAEPowerEpsData (H := H) (DpH := DpH) hweak qε)
    (hUB : HdeltaUniformBounds (H := H) (DpH := DpH) hweak qε)
    (hC0_le : ∀ ε : ℝ, ε > 0 →
      hUB.C0 ≤ CdeltaEps (H := H) (DpH := DpH) hweak ε)
    :
    ∀ ε, 0 < ε → ε ≤ 1 → ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ μ : ℝ, (0 : ℝ) ≤ μ → μ ≤ 2 * fam.m ε x →
          |HdeltaK0 hweak ε x (fun i => fam.Du ε i x) μ|
            ≤ CdeltaEps (H := H) (DpH := DpH) hweak ε
                * (‖(fun i => fam.Du ε i x)‖ ^ hweak.α
                    + 2 ^ hweak.β * (fam.m ε x) ^ hweak.β + 1) := by
  intro ε hε hε1ε
  set Cε : ℝ := CdeltaEps (H := H) (DpH := DpH) hweak ε with hCε_def
  have hCε_pos : 0 < Cε := CdeltaEps_pos (H := H) (DpH := DpH) hweak hε
  have hUp : ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p m, 0 < m →
      HdeltaK0 hweak ε x p m ≤ CdeltaEps hweak ε * (‖p‖ ^ hweak.α + 1) -
        m ^ hweak.β / CdeltaEps hweak ε := by
    filter_upwards [hAE.H_upper_pointwise_ae ε hε hε1ε] with x hx p m hm
    rw [HdeltaK0_eq_Hdelta_of_pos hweak hm]
    exact hx p m hm
  have hLow : ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p m, 0 < m →
      ‖p‖ ^ hweak.α / CdeltaEps hweak ε - CdeltaEps hweak ε * (m ^ hweak.β + 1) ≤
        HdeltaK0 hweak ε x p m := by
    filter_upwards [hAE.lower_ae ε hε hε1ε] with x hx p m hm
    rw [HdeltaK0_eq_Hdelta_of_pos hweak hm]
    exact hx p m hm
  have hZeroUp := Hdelta_zero_upper_of_selectorFamily (H := H) (DpH := DpH)
    hweak hmon qε sel hAE hε hε1ε
  have hZeroLow := t3_hH0_of_bounds hweak qε hUB hmon hdiff sel ε hε hε1ε
  have hC0_le_ε : hUB.C0 ≤ Cε := hC0_le ε hε
  filter_upwards [hUp, hLow, hZeroUp, hZeroLow, fam.hmNonneg ε hε hε1ε]
    with x hxUp hxLow hxZeroUp hxZeroLow hxNonneg
  intro μ hμlo hμhi
  set p : Fin d → ℝ := fun i => fam.Du ε i x with hp_def
  set m : ℝ := fam.m ε x with hm_def
  -- The `2^β·m^β` majorant.
  set Mβ : ℝ := 2 ^ hweak.β * m ^ hweak.β with hMβ_def
  set B : ℝ := Cε * (‖p‖ ^ hweak.α + Mβ + 1) with hB_def
  have hpα_nn : (0 : ℝ) ≤ ‖p‖ ^ hweak.α := Real.rpow_nonneg (norm_nonneg _) _
  have h2β_nn : (0 : ℝ) ≤ (2 : ℝ) ^ hweak.β := Real.rpow_nonneg (by norm_num) _
  have hmβ_nn : (0 : ℝ) ≤ m ^ hweak.β := Real.rpow_nonneg hxNonneg _
  have hMβ_nn : (0 : ℝ) ≤ Mβ := by rw [hMβ_def]; positivity
  -- `μ^β ≤ (2m)^β = 2^β·m^β`.
  have h2m_nn : (0 : ℝ) ≤ 2 * m := by linarith [hxNonneg]
  rw [abs_le]
  rcases lt_or_eq_of_le hμlo with hμpos | hμzero
  · -- Case `0 < μ`.
    have hμpos' : 0 < μ := hμpos
    have hμβ_nn : (0 : ℝ) ≤ μ ^ hweak.β := Real.rpow_nonneg hμlo _
    have hμβ_le : μ ^ hweak.β ≤ Mβ := by
      rw [hMβ_def]
      have h1 : μ ^ hweak.β ≤ (2 * m) ^ hweak.β :=
        Real.rpow_le_rpow hμlo hμhi hweak.hβ.le
      have h2 : (2 * m) ^ hweak.β = 2 ^ hweak.β * m ^ hweak.β :=
        Real.mul_rpow (by norm_num) hxNonneg
      rw [h2] at h1; exact h1
    have hUpx : HdeltaK0 hweak ε x p μ
        ≤ Cε * (‖p‖ ^ hweak.α + 1) - μ ^ hweak.β / Cε := hxUp p μ hμpos'
    have hLowx : ‖p‖ ^ hweak.α / Cε - Cε * (μ ^ hweak.β + 1)
        ≤ HdeltaK0 hweak ε x p μ := hxLow p μ hμpos'
    have hdiv_nn : (0 : ℝ) ≤ μ ^ hweak.β / Cε :=
      div_nonneg hμβ_nn (le_of_lt hCε_pos)
    have hpdiv_nn : (0 : ℝ) ≤ ‖p‖ ^ hweak.α / Cε :=
      div_nonneg hpα_nn (le_of_lt hCε_pos)
    refine ⟨?_, ?_⟩
    · -- `−B ≤ HdeltaK0`.
      have hstep : -B ≤ ‖p‖ ^ hweak.α / Cε - Cε * (μ ^ hweak.β + 1) := by
        rw [hB_def]
        nlinarith [hpdiv_nn, hpα_nn, hμβ_le, hMβ_nn, hCε_pos]
      linarith [hstep, hLowx]
    · -- `HdeltaK0 ≤ B`.
      have hstep : HdeltaK0 hweak ε x p μ ≤ Cε * (‖p‖ ^ hweak.α + 1) := by
        linarith [hUpx, hdiv_nn]
      have hupper_target : Cε * (‖p‖ ^ hweak.α + 1) ≤ B := by
        rw [hB_def]
        nlinarith [mul_nonneg (le_of_lt hCε_pos) hMβ_nn]
      linarith [hstep, hupper_target]
  · -- Case `μ = 0`.
    have hμ0 : μ = 0 := hμzero.symm
    have hUpx0 : HdeltaK0 hweak ε x p 0 ≤ Cε * (‖p‖ ^ hweak.α + 1) := hxZeroUp p
    have hLowx0 : ‖p‖ ^ hweak.α / hUB.C0 - hUB.C0 ≤ HdeltaK0 hweak ε x p 0 := hxZeroLow p
    have hC0_pos : 0 < hUB.C0 := hUB.hC0
    have hpdiv0_nn : (0 : ℝ) ≤ ‖p‖ ^ hweak.α / hUB.C0 :=
      div_nonneg hpα_nn (le_of_lt hC0_pos)
    have hupper_target : Cε * (‖p‖ ^ hweak.α + 1) ≤ B := by
      rw [hB_def]
      nlinarith [mul_nonneg (le_of_lt hCε_pos) hMβ_nn]
    rw [hμ0]
    refine ⟨?_, ?_⟩
    · -- `−B ≤ HdeltaK0(x,p,0)`.
      have hneg : -B ≤ -hUB.C0 := by
        have hge : hUB.C0 ≤ Cε * (‖p‖ ^ hweak.α + 1) := by
          nlinarith [hpα_nn, le_of_lt hCε_pos, hC0_le_ε]
        linarith [hge, hupper_target]
      have hchain : -hUB.C0 ≤ ‖p‖ ^ hweak.α / hUB.C0 - hUB.C0 := by linarith [hpdiv0_nn]
      linarith [hneg, hchain, hLowx0]
    · -- `HdeltaK0(x,p,0) ≤ B`.
      linarith [hUpx0, hupper_target]

/-- **D6c-1b: the SIGNED density-segment `hCont` operator-continuity producer
(fam-based, `hPow`-free).**

Produces the signed-segment continuity carrier consumed by the `hCont` binder
of `T3.hIdentityRaw_of_T3RegularizedStrongFamily` (D6c-3): for `σ = ±1` and a
finite-measure measurable `S`, the operator pairing along the multiplicative
density segment `ρ_n = m + (1/(n+1))·(σ·m·1_S)` converges to the endpoint
pairing at `μ = m`.

The proof routes through `Aepsi_hemicontinuous_setSegment_K0` at the signed
data `μ := m + σ·m·1_S`, `mBar := m`, `η := σ·m·1_S`, then converts the
`ContinuousOn [0,1]` to the `n → ∞` Tendsto along `t_n = 1/(n+1)` EXACTLY as
`hContRaw_of_T3RegularizedStrongFamily`. With `Dν = 0`, `ν = 0`, the gateaux
half vanishes (`g_gat := 0`); the unregularised half collapses to
`(-u - HdeltaK0(x, Du, μt) + V)·η` with `η = σ·m·1_S`. The dominator is
`g_unreg σ S x := (|u| + Cε·(‖Du·x‖^α + 2^β·m^β + 1) + |V|)·(m·1_S)`, integrable
via the Hölder pairing `(envelope ∈ L^{β̄'}) · (m ∈ L^{β̄})`.

Binders are `fam` plus the paper-accepted carriers
`hMeas/hmon/hdiff/sel/hAE/hUB`, the regularity carrier `hRegK0`,
and the constant/exponent reconciliations `hC0_le/hε1/hβBar/hγBar/hγ/hpqβ`
and `hV`. NO `hPow`, NO loose `m`/`u`/`Du`. -/
theorem T3.hContSigned_of_T3RegularizedStrongFamily
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d) {βBarReal γBarReal βBar' : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    (fam : T3RegularizedStrongFamily V hweak qε βBarReal γBarReal)
    (hMeas : StationaryMFG.Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hdiff : HypothesisHpDifferentiable (d := d) H DpH)
    (sel : StationaryMFG.InfimalConvolution.InfConvSelectorFamily
      (H := H) (DpH := DpH) hweak qε)
    (hAE : HdeltaAEPowerEpsData (H := H) (DpH := DpH) hweak qε)
    (hUB : HdeltaUniformBounds (H := H) (DpH := DpH) hweak qε)
    (hRegK0 : ∀ ε, 0 < ε → ε ≤ 1 →
      StationaryMFG.Theorems.SimplePower.RegularityHK0 (d := d)
        (HdeltaK0 hweak ε) (DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε))
    (hC0_le : ∀ ε : ℝ, ε > 0 →
      hUB.C0 ≤ CdeltaEps (H := H) (DpH := DpH) hweak ε)
    (hβBar : βBarReal = StationaryMFG.Hamiltonian.betaBar hweak.β)
    (hγBar : γBarReal = StationaryMFG.Hamiltonian.gammaBar hweak.α hweak.β)
    (hγ : 1 < γBarReal)
    (hpqβ : βBarReal.HolderConjugate βBar')
    (hV : Periodic.MemLpPer (ENNReal.ofReal βBar') V) :
    ∀ ε, 0 < ε → ε ≤ 1 →
      ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (volume.restrict (UnitCube d)) S < ∞ →
        Filter.Tendsto
          (fun n : ℕ =>
            mfgOperatorEpsPair (V := V) (H := HdeltaK0 hweak ε)
              (DpH := DpHepsilonFam hweak qε ε)
              γBarReal ε
              (fam.Du ε)
              (fun x => fam.m ε x + (1 / ((n : ℝ) + 1)) *
                          (σ * fam.m ε x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
              (fam.u ε)
              (fun _ _ => (0 : ℝ))
              (fun x => σ * fam.m ε x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              (fun _ => (0 : ℝ)))
          Filter.atTop
          (𝓝 (mfgOperatorEpsPair (V := V) (H := HdeltaK0 hweak ε)
                (DpH := DpHepsilonFam hweak qε ε)
                γBarReal ε
                (fam.Du ε) (fam.m ε) (fam.u ε)
                (fun _ _ => (0 : ℝ))
                (fun x => σ * fam.m ε x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                (fun _ => (0 : ℝ)))) := by
  classical
  haveI hcube_fin : MeasureTheory.IsFiniteMeasure
      (volume.restrict (UnitCube d) : Measure (Fin d → ℝ)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
          volume_unitCube]; exact ENNReal.one_lt_top⟩
  have hβ0 : (0 : ℝ) < hweak.β := hweak.hβ
  have hα1 : (1 : ℝ) < hweak.α := hweak.hα
  -- Exponent reconciliations (mirror of `hResM`).
  have hβBar'_eq : βBar' = StationaryMFG.Hamiltonian.betaBar' hweak.β :=
    betaBar'_eq_of_holderConjugate hpqβ (by rw [hβBar]; rfl)
  set β' : ℝ := StationaryMFG.Hamiltonian.betaBar' hweak.β with hβ'_def
  have hβ'_pos : 0 < β' := by
    rw [hβ'_def]; unfold StationaryMFG.Hamiltonian.betaBar'; positivity
  have hγbar_eq : StationaryMFG.Hamiltonian.gammaBar hweak.α hweak.β
      = hweak.α * β' := by
    rw [hβ'_def]
    exact StationaryMFG.Hamiltonian.gammaBar_eq_alpha_mul_betaBar'
      hweak.α hweak.β (ne_of_gt hβ0)
  have hβ'_le_γ : β' ≤ γBarReal := by
    rw [hγBar, hγbar_eq]; nlinarith [hβ'_pos, hα1]
  -- The signed variable-density envelope (reused for the bound half).
  have hEnv := T3.hHdeltaSegEnvelopeSigned_of_family hweak qε V fam hmon
    hdiff sel hAE hUB hC0_le
  intro ε hε hε1ε σ hσ S hSmeas hSfin
  -- `|σ| = 1`.
  have hσabs : |σ| = 1 := by
    rcases hσ with h | h <;> rw [h] <;> norm_num
  set Cε : ℝ := CdeltaEps (H := H) (DpH := DpH) hweak ε with hCε_def
  have hCε_pos : 0 < Cε := CdeltaEps_pos (H := H) (DpH := DpH) hweak hε
  -- The envelope function `e x = |u| + Cε·(‖Du‖^α + 2^β·m^β + 1) + |V|`.
  set envF : (Fin d → ℝ) → ℝ := fun x =>
      |fam.u ε x|
        + Cε * (‖(fun i => fam.Du ε i x)‖ ^ hweak.α
                  + 2 ^ hweak.β * (fam.m ε x) ^ hweak.β + 1)
        + |V x| with henvF_def
  -- The dominator `g_unreg σ S x = envF x · (m x · 1_S x)`.
  set ind : (Fin d → ℝ) → ℝ :=
    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) with hind_def
  set g_unreg : (Fin d → ℝ) → ℝ := fun x => envF x * (fam.m ε x * ind x)
    with hg_unreg_def
  -- ===== Integrability of the dominator: envF·m ∈ L¹, dominate g_unreg. =====
  -- envF ∈ L^{β̄'}.
  have henvLp : Periodic.MemLpPer (ENNReal.ofReal β') envF := by
    -- `|u| ∈ L^{β̄'}`.
    have huLp_γ : Periodic.MemLpPer (ENNReal.ofReal γBarReal) (fam.u ε) :=
      (fam.huSob ε hε hε1ε).1
    have huLp : Periodic.MemLpPer (ENNReal.ofReal β') (fam.u ε) :=
      Periodic.MemLpPer.mono_exponent_finite
        (ENNReal.ofReal_le_ofReal hβ'_le_γ) ENNReal.ofReal_ne_top huLp_γ
    have huAbsLp : Periodic.MemLpPer (ENNReal.ofReal β')
        (fun x => |fam.u ε x|) := by
      have h := huLp.toMemLp.norm
      have heq : (fun x => ‖fam.u ε x‖) = fun x => |fam.u ε x| := by
        funext x; exact Real.norm_eq_abs _
      rw [heq] at h; exact MemLp.toMemLpPer h
    -- `‖Du‖^α ∈ L^{β̄'}` (reuse the `hComposite`-style derivation).
    have hDuLp : ∀ i, Periodic.MemLpPer
        (ENNReal.ofReal γBarReal) (fam.Du ε i) := fun i => fam.hDuLp ε hε hε1ε i
    have hNormLp : Periodic.MemLpPer (ENNReal.ofReal γBarReal)
        (fun x : (Fin d → ℝ) => ‖(fun i : Fin d => fam.Du ε i x)‖) := by
      set q : ℝ≥0∞ := ENNReal.ofReal γBarReal with hq_def
      have habs_memLp : ∀ i, Periodic.MemLpPer (d := d) q
          (fun x => |fam.Du ε i x|) := by
        intro i
        have h2 := (hDuLp i).toMemLp.norm
        have heq : (fun x => ‖fam.Du ε i x‖) = fun x => |fam.Du ε i x| := by
          funext x; exact Real.norm_eq_abs _
        rw [heq] at h2
        exact MemLp.toMemLpPer h2
      have hDom_memLp : Periodic.MemLpPer (d := d) q
          (fun x => ∑ i : Fin d, |fam.Du ε i x|) :=
        MemLp.toMemLpPer
          (MeasureTheory.memLp_finset_sum (Finset.univ : Finset (Fin d))
            (fun i _ => (habs_memLp i).toMemLp))
      have hbound :
          ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
            ‖‖(fun i : Fin d => fam.Du ε i x)‖‖
              ≤ (1 : ℝ) * ‖∑ i, |fam.Du ε i x|‖ := by
        refine Filter.Eventually.of_forall ?_
        intro x
        have hsum_nn : 0 ≤ ∑ i, |fam.Du ε i x| :=
          Finset.sum_nonneg (fun i _ => abs_nonneg _)
        have hpi : ‖(fun i : Fin d => fam.Du ε i x)‖ ≤ ∑ i, |fam.Du ε i x| := by
          rw [pi_norm_le_iff_of_nonneg hsum_nn]
          intro i
          rw [Real.norm_eq_abs]
          exact Finset.single_le_sum (f := fun j => |fam.Du ε j x|)
            (fun j _ => abs_nonneg _) (Finset.mem_univ i)
        have h1 : ‖‖(fun i : Fin d => fam.Du ε i x)‖‖
            = ‖(fun i : Fin d => fam.Du ε i x)‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        have h2 : (1 : ℝ) * ‖∑ i, |fam.Du ε i x|‖ = ∑ i, |fam.Du ε i x| := by
          rw [one_mul, Real.norm_eq_abs, abs_of_nonneg hsum_nn]
        rw [h1, h2]; exact hpi
      have hmeas :
          AEStronglyMeasurable
            (fun x : (Fin d → ℝ) => ‖(fun i : Fin d => fam.Du ε i x)‖)
            (Measure.restrict volume (UnitCube d)) := by
        have hAEm : AEMeasurable
            (fun x : (Fin d → ℝ) => fun i : Fin d => fam.Du ε i x)
            (Measure.restrict volume (UnitCube d)) :=
          aemeasurable_pi_iff.mpr fun i => (hDuLp i).aestronglyMeasurable.aemeasurable
        exact hAEm.norm.aestronglyMeasurable
      exact MemLp.toMemLpPer (MemLp.of_le_mul hDom_memLp.toMemLp hmeas hbound)
    have hDuPow : Periodic.MemLpPer (ENNReal.ofReal β')
        (fun x => ‖(fun i : Fin d => fam.Du ε i x)‖ ^ hweak.α) := by
      have hmul : ENNReal.ofReal β' * ENNReal.ofReal hweak.α
          = ENNReal.ofReal γBarReal := by
        rw [← ENNReal.ofReal_mul (le_of_lt hβ'_pos), hγBar, hγbar_eq, mul_comm]
      have hαpos : (0 : ℝ) < hweak.α := lt_trans one_pos hα1
      have hrpow := Periodic.MemLpPer.rpow_closure (d := d) (s := ENNReal.ofReal β')
        (r := hweak.α) hαpos
        (f := fun x : (Fin d → ℝ) => ‖(fun i : Fin d => fam.Du ε i x)‖)
        (by rw [hmul]; exact hNormLp)
      have heq : (fun x => ‖‖(fun i : Fin d => fam.Du ε i x)‖‖ ^ hweak.α)
          = (fun x => ‖(fun i : Fin d => fam.Du ε i x)‖ ^ hweak.α) := by
        funext x; rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      rw [heq] at hrpow; exact hrpow
    -- `m^β ∈ L^{β̄'}`.
    have hβBarEq : βBarReal = hweak.β + 1 := by
      rw [hβBar]; rfl
    have hmPow : Periodic.MemLpPer (ENNReal.ofReal β')
        (fun x => (fam.m ε x) ^ hweak.β) := by
      have hmul : ENNReal.ofReal β' * ENNReal.ofReal hweak.β
          = ENNReal.ofReal βBarReal := by
        rw [← ENNReal.ofReal_mul (le_of_lt hβ'_pos), hβ'_def, hβBarEq]
        congr 1
        unfold StationaryMFG.Hamiltonian.betaBar'
        field_simp
      have habs : Periodic.MemLpPer (d := d) (ENNReal.ofReal β')
          (fun x => ‖fam.m ε x‖ ^ hweak.β) :=
        Periodic.MemLpPer.rpow_closure (d := d) hβ0 (by rw [hmul]; exact fam.hmLp ε hε hε1ε)
      have hae : (fun x => ‖fam.m ε x‖ ^ hweak.β)
          =ᵐ[Measure.restrict volume (UnitCube d)]
            (fun x => (fam.m ε x) ^ hweak.β) := by
        filter_upwards [fam.hmNonneg ε hε hε1ε] with x hx
        rw [Real.norm_eq_abs, abs_of_nonneg hx]
      exact MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq hae habs.toMemLp)
    have h2mPow : Periodic.MemLpPer (ENNReal.ofReal β')
        (fun x => 2 ^ hweak.β * (fam.m ε x) ^ hweak.β) := by
      have h := hmPow.const_smul (𝕜 := ℝ) (2 ^ hweak.β)
      have heq : ((2 ^ hweak.β : ℝ) • (fun x => (fam.m ε x) ^ hweak.β))
          = (fun x => 2 ^ hweak.β * (fam.m ε x) ^ hweak.β) := by
        funext x; simp [Pi.smul_apply, smul_eq_mul]
      rwa [heq] at h
    have hOneLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal β')
        (fun _ : (Fin d → ℝ) => (1 : ℝ)) := MemLp.toMemLpPer (memLp_const 1)
    -- The inner sum `‖Du‖^α + 2^β·m^β + 1 ∈ L^{β̄'}`.
    have hSumLp : Periodic.MemLpPer (ENNReal.ofReal β')
        (fun x => ‖(fun i : Fin d => fam.Du ε i x)‖ ^ hweak.α
          + 2 ^ hweak.β * (fam.m ε x) ^ hweak.β + 1) := by
      have h12 := Periodic.MemLpPer.add hDuPow h2mPow
      have h123 := Periodic.MemLpPer.add h12 hOneLp
      have heq :
          ((fun x => ‖(fun i : Fin d => fam.Du ε i x)‖ ^ hweak.α)
              + (fun x => 2 ^ hweak.β * (fam.m ε x) ^ hweak.β)
              + (fun _ : (Fin d → ℝ) => (1 : ℝ)))
            = (fun x => ‖(fun i : Fin d => fam.Du ε i x)‖ ^ hweak.α
                + 2 ^ hweak.β * (fam.m ε x) ^ hweak.β + 1) := by
        funext x; simp [Pi.add_apply]
      rwa [heq] at h123
    have hCsum : Periodic.MemLpPer (ENNReal.ofReal β')
        (fun x => Cε * (‖(fun i : Fin d => fam.Du ε i x)‖ ^ hweak.α
          + 2 ^ hweak.β * (fam.m ε x) ^ hweak.β + 1)) := by
      have h := hSumLp.const_smul (𝕜 := ℝ) Cε
      have heq :
          (Cε • (fun x => ‖(fun i : Fin d => fam.Du ε i x)‖ ^ hweak.α
              + 2 ^ hweak.β * (fam.m ε x) ^ hweak.β + 1))
            = (fun x => Cε * (‖(fun i : Fin d => fam.Du ε i x)‖ ^ hweak.α
                + 2 ^ hweak.β * (fam.m ε x) ^ hweak.β + 1)) := by
        funext x; simp [Pi.smul_apply, smul_eq_mul]
      rwa [heq] at h
    -- `|V| ∈ L^{β̄'}`.
    have hVabsLp : Periodic.MemLpPer (ENNReal.ofReal β') (fun x => |V x|) := by
      have hVLp : Periodic.MemLpPer (ENNReal.ofReal β') V := by
        have hββ : β' = βBar' := by rw [hβ'_def, hβBar'_eq]
        rw [hββ]; exact hV
      have h := hVLp.toMemLp.norm
      have heq : (fun x => ‖V x‖) = fun x => |V x| := by
        funext x; exact Real.norm_eq_abs _
      rw [heq] at h; exact MemLp.toMemLpPer h
    -- Assemble envF.
    have hadd := (huAbsLp.add hCsum).add hVabsLp
    have heqF :
        (((fun x => |fam.u ε x|) + (fun x => Cε *
            (‖(fun i : Fin d => fam.Du ε i x)‖ ^ hweak.α
              + 2 ^ hweak.β * (fam.m ε x) ^ hweak.β + 1)))
          + (fun x => |V x|)) = envF := by
      funext x; simp only [henvF_def, Pi.add_apply]
    rwa [heqF] at hadd
  -- m ∈ L^{β̄}, with `β̄'.HolderConjugate β̄`.
  have hmLp : Periodic.MemLpPer (ENNReal.ofReal βBarReal) (fam.m ε) :=
    fam.hmLp ε hε hε1ε
  have hpqβ' : β'.HolderConjugate βBarReal := by
    have hββ : β' = βBar' := by rw [hβ'_def, hβBar'_eq]
    rw [hββ]; exact hpqβ.symm
  -- `envF · m ∈ L¹`.
  have henvm_int : IntegrableOn (fun x => envF x * fam.m ε x) (UnitCube d)
      (volume : Measure (Fin d → ℝ)) :=
    Periodic.MemLpPer.integrable_mul hpqβ' henvLp hmLp
  -- envF ≥ 0, m ≥ 0 (a.e.), |ind| ≤ 1.
  have hindle1 : ∀ x, ind x ≤ 1 := by
    intro x; rw [hind_def]
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]; exact zero_le_one
  have hind_nn : ∀ x, (0 : ℝ) ≤ ind x := by
    intro x; rw [hind_def]; exact Set.indicator_nonneg (fun _ _ => zero_le_one) x
  have henvF_nn : ∀ x, (0 : ℝ) ≤ fam.m ε x → (0 : ℝ) ≤ envF x := by
    intro x hmx
    have h1 : (0 : ℝ) ≤ ‖(fun i => fam.Du ε i x)‖ ^ hweak.α :=
      Real.rpow_nonneg (norm_nonneg _) _
    have h2β : (0 : ℝ) ≤ (2 : ℝ) ^ hweak.β := Real.rpow_nonneg (by norm_num) _
    have hmβ : (0 : ℝ) ≤ (fam.m ε x) ^ hweak.β := Real.rpow_nonneg hmx _
    have hCprod : (0 : ℝ) ≤ Cε * (‖(fun i => fam.Du ε i x)‖ ^ hweak.α
        + 2 ^ hweak.β * (fam.m ε x) ^ hweak.β + 1) := by positivity
    have := add_nonneg (add_nonneg (abs_nonneg (fam.u ε x)) hCprod) (abs_nonneg (V x))
    rw [henvF_def]; exact this
  -- Dominator integrability.
  have hg_int : IntegrableOn g_unreg (UnitCube d) := by
    refine Integrable.mono' (g := fun x => |envF x * fam.m ε x|)
      henvm_int.abs ?_ ?_
    · -- measurability of g_unreg
      have hu_aem : AEMeasurable (fam.u ε) (volume.restrict (UnitCube d)) :=
        (fam.huSob ε hε hε1ε).1.aestronglyMeasurable.aemeasurable
      have hm_aem : AEMeasurable (fam.m ε) (volume.restrict (UnitCube d)) :=
        (fam.hmLp ε hε hε1ε).aestronglyMeasurable.aemeasurable
      have hV_aem : AEMeasurable V (volume.restrict (UnitCube d)) :=
        hV.aestronglyMeasurable.aemeasurable
      have hDu_aem : AEMeasurable
          (fun x : (Fin d → ℝ) => ‖(fun i : Fin d => fam.Du ε i x)‖)
          (volume.restrict (UnitCube d)) := by
        have hAEm : AEMeasurable
            (fun x : (Fin d → ℝ) => fun i : Fin d => fam.Du ε i x)
            (volume.restrict (UnitCube d)) :=
          aemeasurable_pi_iff.mpr
            fun i => (fam.hDuLp ε hε hε1ε i).aestronglyMeasurable.aemeasurable
        exact hAEm.norm
      have henvF_aem : AEMeasurable envF (volume.restrict (UnitCube d)) := by
        rw [henvF_def]
        exact (hu_aem.abs.add ((((hDu_aem.pow_const _).add
          (aemeasurable_const.mul (hm_aem.pow_const _))).add aemeasurable_const).const_mul Cε)).add hV_aem.abs
      have hind_aem : AEMeasurable ind (volume.restrict (UnitCube d)) := by
        rw [hind_def]; exact (measurable_const.indicator hSmeas).aemeasurable
      rw [hg_unreg_def]
      exact (henvF_aem.mul (hm_aem.mul hind_aem)).aestronglyMeasurable
    · -- pointwise bound `‖g_unreg x‖ ≤ |envF·m|`
      filter_upwards [fam.hmNonneg ε hε hε1ε] with x hx
      rw [hg_unreg_def, Real.norm_eq_abs]
      have henvFx_nn := henvF_nn x hx
      have habs_eq : |envF x * (fam.m ε x * ind x)|
          = envF x * fam.m ε x * ind x := by
        rw [abs_of_nonneg]
        · ring
        · exact mul_nonneg henvFx_nn (mul_nonneg hx (hind_nn x))
      rw [habs_eq]
      have habs_em : |envF x * fam.m ε x| = envF x * fam.m ε x := by
        rw [abs_of_nonneg (mul_nonneg henvFx_nn hx)]
      rw [habs_em]
      calc envF x * fam.m ε x * ind x
          ≤ envF x * fam.m ε x * 1 :=
            mul_le_mul_of_nonneg_left (hindle1 x) (mul_nonneg henvFx_nn hx)
        _ = envF x * fam.m ε x := mul_one _
  -- ===== Route through the K0 hemicontinuity lemma. =====
  have hcts :
      ContinuousOn (fun t : ℝ =>
          mfgOperatorEpsPair (V := V) (H := HdeltaK0 hweak ε)
            (DpH := DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε) γBarReal ε
            (fun i x => cxCombGrad (fam.Du ε) (fam.Du ε) t i x)
            (fun x => cxComb
              (fun x => fam.m ε x + σ * fam.m ε x * ind x)
              (fam.m ε) t x)
            (fun x => cxComb (fam.u ε) (fam.u ε) t x)
            (fun _ _ => (0 : ℝ))
            (fun x => σ * fam.m ε x * ind x)
            (fun _ => (0 : ℝ))) (Set.Icc 0 1) :=
    Aepsi_hemicontinuous_setSegment_K0 (d := d)
      V (HdeltaK0 hweak ε)
      (DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε) (hRegK0 ε hε hε1ε)
      γBarReal ε hγ
      (fam.Du ε) (fam.Du ε)
      (fun x => fam.m ε x + σ * fam.m ε x * ind x)
      (fam.m ε) (fam.u ε) (fam.u ε)
      (fun _ _ => (0 : ℝ))
      (fun x => σ * fam.m ε x * ind x)
      (fun _ => (0 : ℝ))
      (by
        -- Segment nonnegativity: `cxComb μ m t x = m·(1 + t·σ·1_S) ≥ 0`.
        filter_upwards [fam.hmNonneg ε hε hε1ε] with x hx t ht
        have hindnn : (0 : ℝ) ≤ ind x := hind_nn x
        have hindle : ind x ≤ 1 := hindle1 x
        have ht0 : (0 : ℝ) ≤ t := ht.1
        have ht1 : t ≤ 1 := ht.2
        simp only [cxComb]
        -- `(1-t)·m + t·(m + σ·m·1_S) = m·(1 + t·σ·1_S)`.
        have hexpand :
            (1 - t) * fam.m ε x + t * (fam.m ε x + σ * fam.m ε x * ind x)
              = fam.m ε x * (1 + t * σ * ind x) := by ring
        rw [hexpand]
        -- `1 + t·σ·1_S ≥ 0` for `σ = ±1`, `t,1_S ∈ [0,1]`.
        have hfac_nn : (0 : ℝ) ≤ 1 + t * σ * ind x := by
          rcases hσ with hσ1 | hσm
          · rw [hσ1]; nlinarith [ht0, hindnn]
          · rw [hσm]; nlinarith [ht0, ht1, hindnn, hindle]
        exact mul_nonneg hx hfac_nn)
      g_unreg (fun _ => (0 : ℝ))
      hg_int (integrable_zero _ _ _)
      -- `hF_unreg_meas`
      (by
        intro t ht
        have hu_aesm : AEStronglyMeasurable (fam.u ε)
            (volume.restrict (UnitCube d)) := (fam.huSob ε hε hε1ε).1.aestronglyMeasurable
        have hm_aesm : AEStronglyMeasurable (fam.m ε)
            (volume.restrict (UnitCube d)) := (fam.hmLp ε hε hε1ε).aestronglyMeasurable
        have hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)) :=
          hV.aestronglyMeasurable
        have hind_aem : AEMeasurable ind (volume.restrict (UnitCube d)) := by
          rw [hind_def]; exact (measurable_const.indicator hSmeas).aemeasurable
        set μt : (Fin d → ℝ) → ℝ := fun x =>
            cxComb (fun x => fam.m ε x + σ * fam.m ε x * ind x) (fam.m ε) t x
            with hμt_def
        have hμt_nonneg : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ μt x := by
          filter_upwards [fam.hmNonneg ε hε hε1ε] with x hx
          have hindnn : (0 : ℝ) ≤ ind x := hind_nn x
          have hindle : ind x ≤ 1 := hindle1 x
          have ht0 : (0 : ℝ) ≤ t := ht.1
          have ht1 : t ≤ 1 := ht.2
          simp only [hμt_def, cxComb]
          have hexpand :
              (1 - t) * fam.m ε x + t * (fam.m ε x + σ * fam.m ε x * ind x)
                = fam.m ε x * (1 + t * σ * ind x) := by ring
          rw [hexpand]
          have hfac_nn : (0 : ℝ) ≤ 1 + t * σ * ind x := by
            rcases hσ with hσ1 | hσm
            · rw [hσ1]; nlinarith [ht0, hindnn]
            · rw [hσm]; nlinarith [ht0, ht1, hindnn, hindle]
          exact mul_nonneg hx hfac_nn
        have hm_aem : AEMeasurable (fam.m ε) (volume.restrict (UnitCube d)) :=
          hm_aesm.aemeasurable
        have hμt_aem : AEMeasurable μt (volume.restrict (UnitCube d)) := by
          simp only [hμt_def, cxComb]
          exact (aemeasurable_const.mul hm_aem).add
            (aemeasurable_const.mul (hm_aem.add
              ((aemeasurable_const.mul hm_aem).mul hind_aem)))
        have hDu_aem : AEMeasurable
            (fun x : (Fin d → ℝ) => fun i : Fin d => fam.Du ε i x)
            (volume.restrict (UnitCube d)) :=
          aemeasurable_pi_iff.mpr
            fun i => (fam.hDuLp ε hε hε1ε i).aestronglyMeasurable.aemeasurable
        have hK0_aem :
            AEMeasurable
              (fun x => HdeltaK0 hweak ε x (fun i => fam.Du ε i x) (μt x))
              (volume.restrict (UnitCube d)) :=
          StationaryMFG.InfimalConvolution.aemeasurable_HdeltaK0_comp_of_rc0
            hweak hMeas hmon qε sel hε hDu_aem hμt_aem hμt_nonneg
        have hHdelta_aem :
            AEMeasurable
              (fun x => HdeltaK0 hweak ε x (fun i => fam.Du ε i x) (μt x))
              (volume.restrict (UnitCube d)) := hK0_aem
        have hHdelta_aesm := hHdelta_aem.aestronglyMeasurable
        -- Collapse the K0 integrand to `(-u - HdeltaK0(x,Du,μt) + V)·(σ·m·1_S)`.
        have hcollapse :
            (fun x =>
                aepsiIntegrandAt_unreg_K0 (d := d) V (HdeltaK0 hweak ε)
                  (DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε)
                  (fam.Du ε) (fam.Du ε)
                  (fun x => fam.m ε x + σ * fam.m ε x * ind x)
                  (fam.m ε) (fam.u ε) (fam.u ε)
                  (fun _ _ => (0 : ℝ))
                  (fun x => σ * fam.m ε x * ind x)
                  (fun _ => (0 : ℝ)) x t)
              = (fun x =>
                  (-(fam.u ε x) - HdeltaK0 hweak ε x (fun i => fam.Du ε i x) (μt x)
                      + V x) * (σ * fam.m ε x * ind x)) := by
          funext x
          have hgrad : (fun i => cxCombGrad (fam.Du ε) (fam.Du ε) t i x)
              = (fun i => fam.Du ε i x) := by
            funext i; simp only [cxCombGrad]; ring
          have hμtx : cxComb (fun x => fam.m ε x + σ * fam.m ε x * ind x)
              (fam.m ε) t x = μt x := by simp only [hμt_def]
          have hυt : cxComb (fam.u ε) (fam.u ε) t x = fam.u ε x := by
            simp only [cxComb]; ring
          simp only [aepsiIntegrandAt_unreg_K0, dotProduct,
            mul_zero, Finset.sum_const_zero, hgrad, hμtx, hυt, add_zero]
        rw [hcollapse]
        have hσm_ind_aesm : AEStronglyMeasurable
            (fun x => σ * fam.m ε x * ind x) (volume.restrict (UnitCube d)) :=
          ((aemeasurable_const.mul hm_aem).mul hind_aem).aestronglyMeasurable
        exact (((hu_aesm.neg.sub hHdelta_aesm).add hVmeas).mul hσm_ind_aesm))
      -- `hF_unreg_bound`
      (by
        intro t ht
        filter_upwards [hEnv ε hε hε1ε, fam.hmNonneg ε hε hε1ε] with x hxEnv hxNonneg
        have hindnn : (0 : ℝ) ≤ ind x := hind_nn x
        have hindle1' : ind x ≤ 1 := hindle1 x
        have ht0 : (0 : ℝ) ≤ t := ht.1
        have ht1 : t ≤ 1 := ht.2
        set μt : ℝ := cxComb (fun x => fam.m ε x + σ * fam.m ε x * ind x)
            (fam.m ε) t x with hμt_def
        -- `0 ≤ μt ≤ 2·m`.
        have hμt_eq : μt = fam.m ε x * (1 + t * σ * ind x) := by
          rw [hμt_def]; simp only [cxComb]; ring
        have hμt_lo : (0 : ℝ) ≤ μt := by
          rw [hμt_eq]
          have hfac_nn : (0 : ℝ) ≤ 1 + t * σ * ind x := by
            rcases hσ with hσ1 | hσm
            · rw [hσ1]; nlinarith [ht0, hindnn]
            · rw [hσm]; nlinarith [ht0, ht1, hindnn, hindle1']
          exact mul_nonneg hxNonneg hfac_nn
        have hμt_hi : μt ≤ 2 * fam.m ε x := by
          rw [hμt_eq]
          have hfac_le : 1 + t * σ * ind x ≤ 2 := by
            rcases hσ with hσ1 | hσm
            · rw [hσ1]; nlinarith [ht0, ht1, hindnn, hindle1']
            · rw [hσm]; nlinarith [ht0, ht1, hindnn, hindle1']
          have : fam.m ε x * (1 + t * σ * ind x) ≤ fam.m ε x * 2 :=
            mul_le_mul_of_nonneg_left hfac_le hxNonneg
          linarith [this]
        -- Envelope at `μt`.
        have henv : |HdeltaK0 hweak ε x (fun i => fam.Du ε i x) μt|
            ≤ Cε * (‖(fun i => fam.Du ε i x)‖ ^ hweak.α
                + 2 ^ hweak.β * (fam.m ε x) ^ hweak.β + 1) := by
          rw [hCε_def]; exact hxEnv μt hμt_lo hμt_hi
        -- The integrand value.
        have hgrad : (fun i => cxCombGrad (fam.Du ε) (fam.Du ε) t i x)
            = (fun i => fam.Du ε i x) := by
          funext i; simp only [cxCombGrad]; ring
        have hval :
            aepsiIntegrandAt_unreg_K0 (d := d) V (HdeltaK0 hweak ε)
              (DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε)
              (fam.Du ε) (fam.Du ε)
              (fun x => fam.m ε x + σ * fam.m ε x * ind x)
              (fam.m ε) (fam.u ε) (fam.u ε)
              (fun _ _ => (0 : ℝ))
              (fun x => σ * fam.m ε x * ind x)
              (fun _ => (0 : ℝ)) x t
            = (-(fam.u ε x) - HdeltaK0 hweak ε x (fun i => fam.Du ε i x) μt + V x)
                * (σ * fam.m ε x * ind x) := by
          have hμtx : cxComb (fun x => fam.m ε x + σ * fam.m ε x * ind x)
              (fam.m ε) t x = μt := by rw [hμt_def]
          have hυt : cxComb (fam.u ε) (fam.u ε) t x = fam.u ε x := by
            simp only [cxComb]; ring
          simp only [aepsiIntegrandAt_unreg_K0, dotProduct,
            mul_zero, Finset.sum_const_zero, hgrad, hμtx, hυt, add_zero]
        rw [hval, Real.norm_eq_abs, abs_mul]
        -- `|(-u - H + V)| ≤ |u| + |H| + |V| ≤ envF`, `|σ·m·1_S| = m·1_S`.
        set uu : ℝ := fam.u ε x
        set HH : ℝ := HdeltaK0 hweak ε x (fun i => fam.Du ε i x) μt
        set VV : ℝ := V x
        have htri : |(-uu) + (-HH) + VV| ≤ |(-uu)| + |(-HH)| + |VV| := by
          calc |(-uu) + (-HH) + VV| ≤ |(-uu) + (-HH)| + |VV| := abs_add_le _ _
            _ ≤ (|(-uu)| + |(-HH)|) + |VV| := by
                have := abs_add_le (-uu) (-HH); linarith
            _ = |(-uu)| + |(-HH)| + |VV| := by ring
        have hrw : -uu - HH + VV = (-uu) + (-HH) + VV := by ring
        have h1 : |(-uu - HH + VV)| ≤ envF x := by
          rw [hrw]
          have habs_u : |(-uu)| = |uu| := abs_neg _
          have habs_H : |(-HH)| = |HH| := abs_neg _
          rw [habs_u, habs_H] at htri
          rw [henvF_def]
          have : |HH| ≤ Cε * (‖(fun i => fam.Du ε i x)‖ ^ hweak.α
              + 2 ^ hweak.β * (fam.m ε x) ^ hweak.β + 1) := henv
          linarith [htri, this]
        -- `|σ·m·1_S| = m·1_S` (m ≥ 0, |σ| = 1, 1_S ≥ 0).
        have habs_factor : |σ * fam.m ε x * ind x| = fam.m ε x * ind x := by
          rw [abs_mul, abs_mul, hσabs, one_mul, abs_of_nonneg hxNonneg,
            abs_of_nonneg hindnn]
        rw [habs_factor]
        have henvFx_nn : (0 : ℝ) ≤ envF x := henvF_nn x hxNonneg
        have hmind_nn : (0 : ℝ) ≤ fam.m ε x * ind x := mul_nonneg hxNonneg hindnn
        calc |(-uu - HH + VV)| * (fam.m ε x * ind x)
            ≤ envF x * (fam.m ε x * ind x) :=
              mul_le_mul_of_nonneg_right h1 hmind_nn
          _ = g_unreg x := by rw [hg_unreg_def])
      -- `hF_gat_meas`: gateaux integrand is `0`.
      (by
        intro t ht
        have heq :
            (fun x => aepsiIntegrandAt_gateaux (d := d) γBarReal
              (fam.Du ε) (fam.Du ε) (fam.u ε) (fam.u ε)
              (fun _ _ => (0 : ℝ)) (fun _ => (0 : ℝ)) x t)
              = (fun _ => (0 : ℝ)) := by
          funext x; simp only [aepsiIntegrandAt_gateaux, dotProduct]; simp
        rw [heq]; exact aestronglyMeasurable_const)
      -- `hF_gat_bound`: `‖0‖ ≤ 0`.
      (by
        intro t ht
        refine Filter.Eventually.of_forall ?_
        intro x
        have heq : aepsiIntegrandAt_gateaux (d := d) γBarReal
              (fam.Du ε) (fam.Du ε) (fam.u ε) (fam.u ε)
              (fun _ _ => (0 : ℝ)) (fun _ => (0 : ℝ)) x t = 0 := by
          simp only [aepsiIntegrandAt_gateaux, dotProduct]; simp
        rw [heq, norm_zero])
  -- ===== Convert the `[0,1]`-continuity to the `n → ∞` Tendsto. =====
  set F : ℝ → ℝ := fun t =>
      mfgOperatorEpsPair (V := V) (H := HdeltaK0 hweak ε)
        (DpH := DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε) γBarReal ε
        (fun i x => cxCombGrad (fam.Du ε) (fam.Du ε) t i x)
        (fun x => cxComb
          (fun x => fam.m ε x + σ * fam.m ε x * ind x)
          (fam.m ε) t x)
        (fun x => cxComb (fam.u ε) (fam.u ε) t x)
        (fun _ _ => (0 : ℝ))
        (fun x => σ * fam.m ε x * ind x)
        (fun _ => (0 : ℝ)) with hF_def
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_refl _, zero_le_one⟩
  have hcwa : ContinuousWithinAt F (Set.Icc 0 1) 0 := hcts.continuousWithinAt h0mem
  have htn_tendsto :
      Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        Filter.atTop (𝓝[Set.Icc 0 1] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    · refine Filter.Eventually.of_forall ?_
      intro n
      have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      refine ⟨le_of_lt (div_pos one_pos hpos), ?_⟩
      rw [div_le_one hpos]
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
  have hcomp :
      Filter.Tendsto (fun n : ℕ => F ((1 : ℝ) / ((n : ℝ) + 1)))
        Filter.atTop (𝓝 (F 0)) :=
    hcwa.tendsto.comp htn_tendsto
  have hFn_eq : ∀ n : ℕ,
      F ((1 : ℝ) / ((n : ℝ) + 1))
        = mfgOperatorEpsPair (V := V) (H := HdeltaK0 hweak ε)
            (DpH := DpHepsilonFam hweak qε ε) γBarReal ε (fam.Du ε)
            (fun x => fam.m ε x + (1 / ((n : ℝ) + 1)) *
              (σ * fam.m ε x * ind x))
            (fam.u ε)
            (fun _ _ => (0 : ℝ))
            (fun x => σ * fam.m ε x * ind x)
            (fun _ => (0 : ℝ)) := by
    intro n
    simp only [hF_def]
    congr 1
    · funext i x; simp only [cxCombGrad]; ring
    · funext x; simp only [cxComb]; ring
    · funext x; simp only [cxComb]; ring
  have hF0_eq :
      F 0 = mfgOperatorEpsPair (V := V) (H := HdeltaK0 hweak ε)
              (DpH := DpHepsilonFam hweak qε ε) γBarReal ε (fam.Du ε)
              (fam.m ε) (fam.u ε)
              (fun _ _ => (0 : ℝ))
              (fun x => σ * fam.m ε x * ind x)
              (fun _ => (0 : ℝ)) := by
    simp only [hF_def]
    congr 1
    · funext i x; simp only [cxCombGrad]; ring
    · funext x; simp only [cxComb]; ring
    · funext x; simp only [cxComb]; ring
  rw [hF0_eq] at hcomp
  -- `hcomp` (with `ind = S.indicator …` defeq) matches the target.
  refine hcomp.congr ?_
  intro n; exact hFn_eq n

/-- **D6i child B1: transport-segment endpoint `Lᵖ` facts (fam-based).**

The foundational `MemLpPer` regularity for the SmoothPeriodic transport
segment endpoints consumed by the D6i-B2 dominator assembly: for any
test `φ : SmoothPeriodic d` and shift `σ : ℝ`,

* each shifted gradient component `x ↦ Du_ε i x + σ·∂_iφ x ∈ L^γ̄_per`
  (`Du_ε i ∈ L^γ̄` from `fam.hDuLp`, plus the smooth `∂_iφ ∈ L^γ̄` since a
  continuous periodic function is bounded on the finite cube);
* the shifted value `x ↦ u_ε x + σ·φ x ∈ L^γ̄_per`
  (`u_ε ∈ W^{1,γ̄} ⊆ L^γ̄` from `fam.huSob`, plus `σφ ∈ L^γ̄`).

Both reduce to: a `SmoothPeriodic` test function (and its `partialDeriv`)
is in every `L^p_per` on the finite cube (it is continuous and periodic,
hence bounded — `SmoothPeriodic.exists_bound_on_unitCube`), so the
`const_smul` and `add` closure of `MemLpPer` lands the sum.

Binders are `fam` plus the exponent reconciliation `hγ : 1 < γBarReal`
(used to land the `MemLp` from a bounded function on the finite cube).
NO `hPow`, NO loose `m`/`u`/`Du`. This is the prerequisite layer for the
D6i-B2 rpow-cert bundle and the K0 dominator assembly. -/
theorem T3.transportSegmentEndpointLp_of_T3RegularizedStrongFamily
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d) {βBarReal γBarReal : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    (fam : T3RegularizedStrongFamily V hweak qε βBarReal γBarReal)
    (hγ : 1 < γBarReal)
    (ε : ℝ) (hεpos : 0 < ε) (hε1 : ε ≤ 1) :
    (∀ (σ : ℝ) (φ : SmoothPeriodic d) (i : Fin d),
        Periodic.MemLpPer (ENNReal.ofReal γBarReal)
          (fun x => fam.Du ε i x + σ *
            ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) x)) ∧
    (∀ (σ : ℝ) (φ : SmoothPeriodic d),
        Periodic.MemLpPer (ENNReal.ofReal γBarReal)
          (fun x => fam.u ε x + σ * (φ : (Fin d → ℝ) → ℝ) x)) ∧
    (∀ (ψ : SmoothPeriodic d),
        Periodic.MemLpPer (ENNReal.ofReal γBarReal)
          ((ψ : (Fin d → ℝ) → ℝ))) := by
  classical
  haveI hfin : MeasureTheory.IsFiniteMeasure
      (volume.restrict (UnitCube d) : Measure (Fin d → ℝ)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
          volume_unitCube]; exact ENNReal.one_lt_top⟩
  have hγ0 : (0 : ℝ) < γBarReal := lt_trans zero_lt_one hγ
  -- A `SmoothPeriodic` test function is in every `L^γ̄_per` on the finite cube:
  -- it is bounded (continuous + cube compact), hence `MemLp` of any exponent.
  have hSmoothLp : ∀ (ψ : SmoothPeriodic d),
      Periodic.MemLpPer (ENNReal.ofReal γBarReal) ((ψ : (Fin d → ℝ) → ℝ)) := by
    intro ψ
    -- A continuous periodic function is bounded on the compact closed cube
    -- `Icc 0 1 ⊇ UnitCube`; this gives the a.e. norm bound on the restricted
    -- measure, hence `MemLp` of any exponent on the finite cube.
    have hcompact : IsCompact (Set.Icc (0 : Fin d → ℝ) 1) := isCompact_Icc
    have hcont : ContinuousOn (ψ : (Fin d → ℝ) → ℝ) (Set.Icc (0 : Fin d → ℝ) 1) :=
      ψ.smooth.continuous.continuousOn
    obtain ⟨M, hMbound⟩ := hcompact.exists_bound_of_continuousOn hcont
    have hmeas : AEStronglyMeasurable (ψ : (Fin d → ℝ) → ℝ)
        (volume.restrict (UnitCube d)) :=
      ψ.smooth.continuous.aestronglyMeasurable
    have hbnd : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖(ψ : (Fin d → ℝ) → ℝ) x‖ ≤ M := by
      refine (ae_restrict_iff' measurableSet_unitCube).2 ?_
      filter_upwards with x hx
      have hxIcc : x ∈ Set.Icc (0 : Fin d → ℝ) 1 := by
        rw [Set.mem_Icc]
        have hx' := (mem_unitCube_iff (d := d)).1 hx
        exact ⟨fun i => (hx' i).1, fun i => le_of_lt (hx' i).2⟩
      exact hMbound x hxIcc
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.of_bound hmeas M hbnd)
  refine ⟨?_, ?_, hSmoothLp⟩
  · -- Shifted gradient component.
    intro σ φ i
    have hDu : Periodic.MemLpPer (ENNReal.ofReal γBarReal) (fam.Du ε i) :=
      fam.hDuLp ε hεpos hε1 i
    have hdphi : Periodic.MemLpPer (ENNReal.ofReal γBarReal)
        ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
          (Fin d → ℝ) → ℝ) :=
      hSmoothLp (SmoothPeriodic.partialDeriv i φ)
    have hsdphi : Periodic.MemLpPer (ENNReal.ofReal γBarReal)
        (fun x => σ *
          ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) x) := by
      have h := Periodic.MemLpPer.const_smul (c := σ) hdphi
      have heq : (σ • ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ))
          = fun x => σ *
            ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) x := by
        funext x; simp [Pi.smul_apply, smul_eq_mul]
      rwa [heq] at h
    have hadd := Periodic.MemLpPer.add hDu hsdphi
    have heq : (fam.Du ε i + fun x => σ *
          ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) x)
        = fun x => fam.Du ε i x + σ *
          ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) x := by
      funext x; simp [Pi.add_apply]
    rwa [heq] at hadd
  · -- Shifted value.
    intro σ φ
    have hu : Periodic.MemLpPer (ENNReal.ofReal γBarReal) (fam.u ε) :=
      (fam.huSob ε hεpos hε1).1
    have hφ : Periodic.MemLpPer (ENNReal.ofReal γBarReal)
        ((φ : (Fin d → ℝ) → ℝ)) := hSmoothLp φ
    have hσφ : Periodic.MemLpPer (ENNReal.ofReal γBarReal)
        (fun x => σ * (φ : (Fin d → ℝ) → ℝ) x) := by
      have h := Periodic.MemLpPer.const_smul (c := σ) hφ
      have heq : (σ • ((φ : (Fin d → ℝ) → ℝ)))
          = fun x => σ * (φ : (Fin d → ℝ) → ℝ) x := by
        funext x; simp [Pi.smul_apply, smul_eq_mul]
      rwa [heq] at h
    have hadd := Periodic.MemLpPer.add hu hσφ
    have heq : (fam.u ε + fun x => σ * (φ : (Fin d → ℝ) → ℝ) x)
        = fun x => fam.u ε x + σ * (φ : (Fin d → ℝ) → ℝ) x := by
      funext x; simp [Pi.add_apply]
    rwa [heq] at hadd

/-- **D6i child B2: the TRANSPORT-form closed-cone K0 segment dominator
(fam-based, `hPow`-free).**

Produces the DCT dominator/measurability bundle consumed by
`T3.hIdentityRaw_of_T3RegularizedStrongFamily` (D6c-3) at the TRANSPORT
test direction `(σ∂φ, 0, σφ)` with density FIXED `fam.m ε`: the dominating
functions `g_unreg g_gat`, their `IntegrableOn` certificates, and the
`hF_*_meas` / `hF_*_bound` facts (ε FIXED).

The construction REUSES the natural-form dominators
`Banach.g_unreg_natural`/`Banach.g_gat_natural` with `η = 0` (so the first
three `·|η|` terms vanish), `μ = mBar = fam.m ε`, `Dυ = Du+σ∂φ`, `Dῡ = Du`,
`ν = σφ`, `Dν = σ∂φ`, and `C = C' = Cε = CdeltaEps hweak ε`. The integrability
is discharged by `g_unreg_natural_integrableOn_min` (which drops the β≥1
`hΔm1` rider, splitting Term 5 via the `(γ̄',γ̄)` Hölder pair) and
`g_gat_natural_integrableOn`. The eleven/seven `MemLpPer`-of-power certificates
are re-derived for the fam endpoints via the
`hComposite_memLpPer_of_family` `rpow_closure` / `mono_exponent_finite`
pattern. The η=0 K0 flux pointwise bound is re-derived from
`hAE.DpH_upper_ae` + `JsimpleExt`/`JsimpleExt_zero` +
`euclideanDot_smul_left` + `cxCombGrad_norm_le`, NOT the forbidden
`aepsiIntegrandAt_unreg_pointwise_bound_K0`.

Binders are `fam` plus the paper-accepted carriers `hMeas/sel/hAE` (the
H-term is killed by `η = 0`, so no `hmon`/`hdiff`/`hUB`/`hC0_le`
are needed for the bound) and the constant/exponent reconciliations
`hε1/hβBar/hγBar/hpqβ/hpqγ/hγ` and `hV`, plus B1's endpoint Lp bundle.
NO `hPow`, NO loose `m`/`u`/`Du`, NO `bΔm1`-style β≥1 rider. -/
theorem T3.transportSegmentDominator_of_T3RegularizedStrongFamily
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d) {βBarReal γBarReal βBar' γBar' : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    (fam : T3RegularizedStrongFamily V hweak qε βBarReal γBarReal)
    (hMeas : StationaryMFG.Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (sel : StationaryMFG.InfimalConvolution.InfConvSelectorFamily
      (H := H) (DpH := DpH) hweak qε)
    (hAE : HdeltaAEPowerEpsData (H := H) (DpH := DpH) hweak qε)
    (hβBar : βBarReal = StationaryMFG.Hamiltonian.betaBar hweak.β)
    (hγBar : γBarReal = StationaryMFG.Hamiltonian.gammaBar hweak.α hweak.β)
    (hpqβ : βBarReal.HolderConjugate βBar')
    (hpqγ : γBar'.HolderConjugate γBarReal)
    (hγ : 1 < γBarReal)
    (hV : Periodic.MemLpPer (ENNReal.ofReal βBar') V)
    (ε : ℝ) (hεpos : 0 < ε) (hε1ε : ε ≤ 1)
    (hB1 :
      (∀ (σ : ℝ) (φ : SmoothPeriodic d) (i : Fin d),
          Periodic.MemLpPer (ENNReal.ofReal γBarReal)
            (fun x => fam.Du ε i x + σ *
              ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x)) ∧
      (∀ (σ : ℝ) (φ : SmoothPeriodic d),
          Periodic.MemLpPer (ENNReal.ofReal γBarReal)
            (fun x => fam.u ε x + σ * (φ : (Fin d → ℝ) → ℝ) x)) ∧
      (∀ (ψ : SmoothPeriodic d),
          Periodic.MemLpPer (ENNReal.ofReal γBarReal)
            ((ψ : (Fin d → ℝ) → ℝ)))) :
    ∃ g_unreg g_gat :
        (σ : ℝ) → (φ : SmoothPeriodic d) → (Fin d → ℝ) → ℝ,
      (∀ (σ : ℝ) (φ : SmoothPeriodic d),
          IntegrableOn (g_unreg σ φ) (UnitCube d)) ∧
      (∀ (σ : ℝ) (φ : SmoothPeriodic d),
          IntegrableOn (g_gat σ φ) (UnitCube d)) ∧
      (∀ (σ : ℝ) (φ : SmoothPeriodic d), ∀ t ∈ Set.Icc (0 : ℝ) 1,
          AEStronglyMeasurable
            (fun x =>
              aepsiIntegrandAt_unreg_K0 (d := d) V (HdeltaK0 hweak ε)
                (DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε)
                (fun i x => fam.Du ε i x + σ *
                  ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                    (Fin d → ℝ) → ℝ) x)
                (fam.Du ε) (fam.m ε) (fam.m ε)
                (fun x => fam.u ε x + σ * (φ : (Fin d → ℝ) → ℝ) x) (fam.u ε)
                (fun i x => σ *
                  ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                    (Fin d → ℝ) → ℝ) x)
                (fun _ => (0 : ℝ))
                (fun x => σ * (φ : (Fin d → ℝ) → ℝ) x) x t)
            (volume.restrict (UnitCube d))) ∧
      (∀ (σ : ℝ) (φ : SmoothPeriodic d), ∀ t ∈ Set.Icc (0 : ℝ) 1,
          ∀ᵐ x ∂(volume.restrict (UnitCube d)),
            ‖aepsiIntegrandAt_unreg_K0 (d := d) V (HdeltaK0 hweak ε)
                (DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε)
                (fun i x => fam.Du ε i x + σ *
                  ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                    (Fin d → ℝ) → ℝ) x)
                (fam.Du ε) (fam.m ε) (fam.m ε)
                (fun x => fam.u ε x + σ * (φ : (Fin d → ℝ) → ℝ) x) (fam.u ε)
                (fun i x => σ *
                  ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                    (Fin d → ℝ) → ℝ) x)
                (fun _ => (0 : ℝ))
                (fun x => σ * (φ : (Fin d → ℝ) → ℝ) x) x t‖
              ≤ g_unreg σ φ x) ∧
      (∀ (σ : ℝ) (φ : SmoothPeriodic d), ∀ t ∈ Set.Icc (0 : ℝ) 1,
          AEStronglyMeasurable
            (fun x =>
              aepsiIntegrandAt_gateaux (d := d) γBarReal
                (fun i x => fam.Du ε i x + σ *
                  ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                    (Fin d → ℝ) → ℝ) x)
                (fam.Du ε)
                (fun x => fam.u ε x + σ * (φ : (Fin d → ℝ) → ℝ) x) (fam.u ε)
                (fun i x => σ *
                  ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                    (Fin d → ℝ) → ℝ) x)
                (fun x => σ * (φ : (Fin d → ℝ) → ℝ) x) x t)
            (volume.restrict (UnitCube d))) ∧
      (∀ (σ : ℝ) (φ : SmoothPeriodic d), ∀ t ∈ Set.Icc (0 : ℝ) 1,
          ∀ᵐ x ∂(volume.restrict (UnitCube d)),
            ‖aepsiIntegrandAt_gateaux (d := d) γBarReal
                (fun i x => fam.Du ε i x + σ *
                  ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                    (Fin d → ℝ) → ℝ) x)
                (fam.Du ε)
                (fun x => fam.u ε x + σ * (φ : (Fin d → ℝ) → ℝ) x) (fam.u ε)
                (fun i x => σ *
                  ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                    (Fin d → ℝ) → ℝ) x)
                (fun x => σ * (φ : (Fin d → ℝ) → ℝ) x) x t‖
              ≤ g_gat σ φ x) := by
  classical
  haveI hcube_fin : MeasureTheory.IsFiniteMeasure
      (volume.restrict (UnitCube d) : Measure (Fin d → ℝ)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
          volume_unitCube]; exact ENNReal.one_lt_top⟩
  obtain ⟨hB1_grad, hB1_val, hB1_smooth⟩ := hB1
  -- Positivity facts on the exponents.
  have hα1 : (1 : ℝ) < hweak.α := hweak.hα
  have hβ0 : (0 : ℝ) < hweak.β := hweak.hβ
  have hαpos : (0 : ℝ) < hweak.α := lt_trans one_pos hα1
  have hβ1_pos : (0 : ℝ) < hweak.β + 1 := by linarith
  have hαm1_pos : (0 : ℝ) < hweak.α - 1 := by linarith
  -- The per-`ε` constant.
  set Cε : ℝ := CdeltaEps (H := H) (DpH := DpH) hweak ε with hCε_def
  have hCε_pos : 0 < Cε := CdeltaEps_pos (H := H) (DpH := DpH) hweak hεpos
  -- Concrete real exponents.
  set β' : ℝ := StationaryMFG.Hamiltonian.betaBar' hweak.β with hβ'_def
  have hβ'_pos : 0 < β' := by
    rw [hβ'_def]; unfold StationaryMFG.Hamiltonian.betaBar'; positivity
  -- The abstract `βBar'`/`γBar'` equal the concrete paper conjugates.
  have hβBar_eq' : βBarReal = hweak.β + 1 := by
    rw [hβBar]; rfl
  have hβBar'_eq : βBar' = StationaryMFG.Hamiltonian.betaBar' hweak.β :=
    betaBar'_eq_of_holderConjugate hpqβ hβBar_eq'
  have hγr_pos : 0 < γBarReal := lt_trans zero_lt_one hγ
  have hg_id : StationaryMFG.Hamiltonian.gammaBar hweak.α hweak.β = γBarReal :=
    hγBar.symm
  have hγm1_pos : (0 : ℝ) < γBarReal - 1 := by linarith [hγ]
  have hγBar'_eq : γBar' = StationaryMFG.Hamiltonian.gammaBar' hweak.α hweak.β := by
    have hconj : γBar' = γBarReal / (γBarReal - 1) := hpqγ.symm.conjugate_eq
    rw [hconj, hγBar]
    unfold StationaryMFG.Hamiltonian.gammaBar'
    rfl
  set γ'r : ℝ := StationaryMFG.Hamiltonian.gammaBar' hweak.α hweak.β with hγ'r_def
  have hγ'r_pos : 0 < γ'r := by
    rw [hγ'r_def]; unfold StationaryMFG.Hamiltonian.gammaBar'
    rw [hγBar] at hγr_pos
    have hγgt1 : 1 < StationaryMFG.Hamiltonian.gammaBar hweak.α hweak.β := by
      rw [← hγBar]; exact hγ
    exact div_pos hγr_pos (by linarith [hγgt1])
  -- Hölder-conjugate facts in concrete-exponent form.
  have hβconj : β'.HolderConjugate (StationaryMFG.Hamiltonian.betaBar hweak.β) := by
    rw [hβ'_def]
    -- `betaBar' β` and `betaBar β = β+1` are Hölder conjugates.
    have h := hpqβ
    rw [hβBar, hβBar'_eq] at h
    exact h.symm
  have hγconj : γ'r.HolderConjugate γBarReal := by
    rw [← hγBar'_eq]; exact hpqγ
  -- `γ̄ = α · β̄'`.
  have hγbar_eq : StationaryMFG.Hamiltonian.gammaBar hweak.α hweak.β
      = hweak.α * β' := by
    rw [hβ'_def]
    exact StationaryMFG.Hamiltonian.gammaBar_eq_alpha_mul_betaBar'
      hweak.α hweak.β (ne_of_gt hβ0)
  -- Family `Lᵖ` regularities at the concrete exponents.
  have hmLp_β : Periodic.MemLpPer (ENNReal.ofReal (hweak.β + 1)) (fam.m ε) := by
    have h := fam.hmLp ε hεpos hε1ε
    have heq : ENNReal.ofReal βBarReal = ENNReal.ofReal (hweak.β + 1) := by
      rw [hβBar_eq']
    rwa [heq] at h
  have hmNonneg := fam.hmNonneg ε hεpos hε1ε
  have hu_γ : Periodic.MemLpPer (ENNReal.ofReal γBarReal) (fam.u ε) :=
    (fam.huSob ε hεpos hε1ε).1
  have hDu_γ : ∀ i, Periodic.MemLpPer (ENNReal.ofReal γBarReal) (fam.Du ε i) :=
    fun i => fam.hDuLp ε hεpos hε1ε i
  -- The constant `1 ∈ L^{β̄'}` (finite cube).
  have hOneβ' : Periodic.MemLpPer (d := d) (ENNReal.ofReal β')
      (fun _ : (Fin d → ℝ) => (1 : ℝ)) := MemLp.toMemLpPer (memLp_const 1)
  -- `γ̄ = α · β̄'` in ENNReal-of-real form: `ofReal β' * ofReal α = ofReal γ̄`.
  have hmulαβ' : ENNReal.ofReal β' * ENNReal.ofReal hweak.α
      = ENNReal.ofReal γBarReal := by
    rw [← ENNReal.ofReal_mul (le_of_lt hβ'_pos), mul_comm, ← hγbar_eq, hγBar]
  -- `β̄' · β = β̄` in ENNReal-of-real form.
  have hmulβ'β : ENNReal.ofReal β' * ENNReal.ofReal hweak.β
      = ENNReal.ofReal (hweak.β + 1) := by
    rw [← ENNReal.ofReal_mul (le_of_lt hβ'_pos), hβ'_def]
    congr 1
    unfold StationaryMFG.Hamiltonian.betaBar'
    field_simp
  -- ===========================================================
  -- Shared certificate producer for the natural-form dominators.
  -- For each `(σ, φ)`, build the eleven/seven `MemLpPer`-of-power
  -- certificates consumed by `g_unreg_natural_integrableOn_min` and
  -- `g_gat_natural_integrableOn`, at the transport endpoints
  -- `Dυ = Du+σ∂φ`, `Dῡ = Du`, `υ = u+σφ`, `ῡ = u`, `Dν = σ∂φ`, `ν = σφ`.
  -- ===========================================================
  -- Abbreviation for the smoothed gradient endpoint.
  set Dυ : ℝ → SmoothPeriodic d → Fin d → (Fin d → ℝ) → ℝ :=
    fun σ φ i x => fam.Du ε i x + σ *
      ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
        (Fin d → ℝ) → ℝ) x with hDυ_def
  set υ : ℝ → SmoothPeriodic d → (Fin d → ℝ) → ℝ :=
    fun σ φ x => fam.u ε x + σ * (φ : (Fin d → ℝ) → ℝ) x with hυ_def
  set Dν : ℝ → SmoothPeriodic d → Fin d → (Fin d → ℝ) → ℝ :=
    fun σ φ i x => σ *
      ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
        (Fin d → ℝ) → ℝ) x with hDν_def
  set ν : ℝ → SmoothPeriodic d → (Fin d → ℝ) → ℝ :=
    fun σ φ x => σ * (φ : (Fin d → ℝ) → ℝ) x with hν_def
  -- `Dυ σ φ i ∈ L^{γ̄}` (from B1) and `Du ∈ L^{γ̄}`; `υ σ φ ∈ L^{γ̄}`.
  have hDυLp : ∀ σ φ i, Periodic.MemLpPer (ENNReal.ofReal γBarReal) (Dυ σ φ i) :=
    fun σ φ i => hB1_grad σ φ i
  have hυLp : ∀ (σ : ℝ) (φ : SmoothPeriodic d), Periodic.MemLpPer (ENNReal.ofReal γBarReal) (υ σ φ) :=
    fun σ φ => hB1_val σ φ
  have hDνLp : ∀ σ φ i, Periodic.MemLpPer (ENNReal.ofReal γBarReal) (Dν σ φ i) := by
    intro σ φ i
    have h := (hB1_smooth (SmoothPeriodic.partialDeriv i φ)).const_smul (c := σ)
    have heq : (σ • ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
          (Fin d → ℝ) → ℝ)) = Dν σ φ i := by
      funext x; simp [hDν_def, Pi.smul_apply, smul_eq_mul]
    rwa [heq] at h
  have hνLp : ∀ (σ : ℝ) (φ : SmoothPeriodic d), Periodic.MemLpPer (ENNReal.ofReal γBarReal) (ν σ φ) := by
    intro σ φ
    have h := (hB1_smooth φ).const_smul (c := σ)
    have heq : (σ • ((φ : SmoothPeriodic d) : (Fin d → ℝ) → ℝ)) = ν σ φ := by
      funext x; simp [hν_def, Pi.smul_apply, smul_eq_mul]
    rwa [heq] at h
  -- The summed-abs gradient `‖Δp‖`-base function, in `L^{γ̄}`.
  -- `Δp σ φ i x := |Dῡ i x| + |Dυ i x| = |Du i x| + |Du i x + σ∂φ i x|`.
  have hNormΔpLp : ∀ (σ : ℝ) (φ : SmoothPeriodic d), Periodic.MemLpPer (ENNReal.ofReal γBarReal)
      (fun x : (Fin d → ℝ) =>
        ‖fun i => |fam.Du ε i x| + |Dυ σ φ i x|‖) := by
    intro σ φ
    set q : ℝ≥0∞ := ENNReal.ofReal γBarReal with hq_def
    -- Each summed-abs coordinate is in `L^{γ̄}`.
    have hcoord : ∀ i, Periodic.MemLpPer (d := d) q
        (fun x => |fam.Du ε i x| + |Dυ σ φ i x|) := by
      intro i
      have h1 := (hDu_γ i).toMemLp.abs
      have h2 := (hDυLp σ φ i).toMemLp.abs
      exact MemLp.toMemLpPer (h1.add h2)
    have hDom : Periodic.MemLpPer (d := d) q
        (fun x => ∑ i : Fin d, (|fam.Du ε i x| + |Dυ σ φ i x|)) :=
      MemLp.toMemLpPer
        (MeasureTheory.memLp_finset_sum (Finset.univ : Finset (Fin d))
          (fun i _ => (hcoord i).toMemLp))
    have hbound :
        ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
          ‖‖(fun i : Fin d => |fam.Du ε i x| + |Dυ σ φ i x|)‖‖
            ≤ (1 : ℝ) * ‖∑ i, (|fam.Du ε i x| + |Dυ σ φ i x|)‖ := by
      refine Filter.Eventually.of_forall ?_
      intro x
      have hsum_nn : 0 ≤ ∑ i, (|fam.Du ε i x| + |Dυ σ φ i x|) :=
        Finset.sum_nonneg (fun i _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
      have hpi : ‖(fun i : Fin d => |fam.Du ε i x| + |Dυ σ φ i x|)‖
          ≤ ∑ i, (|fam.Du ε i x| + |Dυ σ φ i x|) := by
        rw [pi_norm_le_iff_of_nonneg hsum_nn]
        intro i
        rw [Real.norm_eq_abs,
          abs_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))]
        exact Finset.single_le_sum
          (f := fun j => |fam.Du ε j x| + |Dυ σ φ j x|)
          (fun j _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ i)
      have h1 : ‖‖(fun i : Fin d => |fam.Du ε i x| + |Dυ σ φ i x|)‖‖
          = ‖(fun i : Fin d => |fam.Du ε i x| + |Dυ σ φ i x|)‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      have h2 : (1 : ℝ) * ‖∑ i, (|fam.Du ε i x| + |Dυ σ φ i x|)‖
          = ∑ i, (|fam.Du ε i x| + |Dυ σ φ i x|) := by
        rw [one_mul, Real.norm_eq_abs, abs_of_nonneg hsum_nn]
      rw [h1, h2]; exact hpi
    have hmeas : AEStronglyMeasurable
        (fun x : (Fin d → ℝ) =>
          ‖(fun i : Fin d => |fam.Du ε i x| + |Dυ σ φ i x|)‖)
        (Measure.restrict volume (UnitCube d)) := by
      have hAEm : AEMeasurable
          (fun x : (Fin d → ℝ) => fun i : Fin d => |fam.Du ε i x| + |Dυ σ φ i x|)
          (Measure.restrict volume (UnitCube d)) :=
        aemeasurable_pi_iff.mpr fun i =>
          (((hDu_γ i).aestronglyMeasurable.aemeasurable.abs).add
            ((hDυLp σ φ i).aestronglyMeasurable.aemeasurable.abs))
      exact hAEm.norm.aestronglyMeasurable
    exact MemLp.toMemLpPer (MemLp.of_le_mul hDom.toMemLp hmeas hbound)
  -- `Δm := |m| + |m| ∈ L^{β̄}` (= `|mBar|+|μ|` with `mBar = μ = m`).
  have hΔmβ : Periodic.MemLpPer (d := d) (ENNReal.ofReal (hweak.β + 1))
      (fun x => |fam.m ε x| + |fam.m ε x|) :=
    MemLp.toMemLpPer (hmLp_β.toMemLp.abs.add hmLp_β.toMemLp.abs)
  -- standing exponent facts.
  have hβ'_le_β : ENNReal.ofReal γ'r ≤ ENNReal.ofReal (hweak.β + 1) := by
    apply ENNReal.ofReal_le_ofReal
    -- γ̄' ≤ β̄ (paper inequality).
    rw [hγ'r_def]
    have h := StationaryMFG.Hamiltonian.gammaBar'_le_betaBar hweak.hα hβ0
    unfold StationaryMFG.Hamiltonian.gammaBar' StationaryMFG.Hamiltonian.gammaBar
    exact h
  have hβ'_le_γ : ENNReal.ofReal β' ≤ ENNReal.ofReal γBarReal := by
    apply ENNReal.ofReal_le_ofReal
    rw [hβ'_def, hγBar]
    have h := StationaryMFG.Hamiltonian.betaBar'_le_gammaBar hweak.hα.le hβ0
    simpa [StationaryMFG.Hamiltonian.betaBar', StationaryMFG.Hamiltonian.gammaBar]
      using h
  -- Cert `hΔm`: `Δm ∈ L^{γ̄'}` via mono from `β̄`.
  have hΔm_cert : ∀ (σ : ℝ) (φ : SmoothPeriodic d), Periodic.MemLpPer (d := d) (ENNReal.ofReal γ'r)
      (fun x => |fam.m ε x| + |fam.m ε x|) := fun σ φ =>
    Periodic.MemLpPer.mono_exponent_finite hβ'_le_β ENNReal.ofReal_ne_top hΔmβ
  have hexp_endpoint_pos : 0 < 1 + hweak.β - hweak.β / hweak.α := by
    have hdiv_le : hweak.β / hweak.α ≤ hweak.β := by
      rw [div_le_iff₀ hαpos]; nlinarith [hweak.hα, hβ0]
    linarith
  -- Exponent identity `γ̄' · (1+β-β/α) = β̄`.
  have hmulγ'endpoint : ENNReal.ofReal γ'r
      * ENNReal.ofReal (1 + hweak.β - hweak.β / hweak.α)
      = ENNReal.ofReal (hweak.β + 1) := by
    rw [← ENNReal.ofReal_mul (le_of_lt hγ'r_pos)]
    congr 1
    rw [hγ'r_def]
    unfold StationaryMFG.Hamiltonian.gammaBar'
    rw [hg_id]
    have hβne : hweak.β ≠ 0 := hβ0.ne'
    have hαne : hweak.α ≠ 0 := hαpos.ne'
    have hγne : γBarReal ≠ 0 := hγr_pos.ne'
    have hγm1_ne : γBarReal - 1 ≠ 0 := hγm1_pos.ne'
    -- `γBarReal = α(β+1)/β`, so `γBarReal · β = α(β+1)`.
    have hγβ : γBarReal * hweak.β = hweak.α * (hweak.β + 1) := by
      rw [← hg_id]; unfold StationaryMFG.Hamiltonian.gammaBar; field_simp
    -- `γBarReal/(γBarReal-1) · (1+β-β/α) = β+1`.
    field_simp
    nlinarith [hγβ, hαpos, hβ0, hγr_pos, mul_pos hαpos hβ0]
  -- Cert `hΔm_endpoint`: `Δm^{1+β-β/α} ∈ L^{γ̄'}`.
  have hΔm_endpoint_cert : ∀ (σ : ℝ) (φ : SmoothPeriodic d), Periodic.MemLpPer (d := d) (ENNReal.ofReal γ'r)
      (fun x => (|fam.m ε x| + |fam.m ε x|) ^ (1 + hweak.β - hweak.β / hweak.α)) := by
    intro σ φ
    have hrpow := Periodic.MemLpPer.rpow_closure (d := d) (s := ENNReal.ofReal γ'r)
      (r := 1 + hweak.β - hweak.β / hweak.α) hexp_endpoint_pos
      (f := fun x : (Fin d → ℝ) => |fam.m ε x| + |fam.m ε x|)
      (by rw [hmulγ'endpoint]; exact hΔmβ)
    have hΔm_nn : ∀ x, 0 ≤ |fam.m ε x| + |fam.m ε x| :=
      fun x => add_nonneg (abs_nonneg _) (abs_nonneg _)
    have heq : (fun x => ‖|fam.m ε x| + |fam.m ε x|‖ ^ (1 + hweak.β - hweak.β / hweak.α))
        = (fun x => (|fam.m ε x| + |fam.m ε x|) ^ (1 + hweak.β - hweak.β / hweak.α)) := by
      funext x; rw [Real.norm_eq_abs, abs_of_nonneg (hΔm_nn x)]
    rwa [heq] at hrpow
  -- `‖Δp‖^{α-1} ∈ L^{γ̄/(α-1)}` (from `‖Δp‖ ∈ L^{γ̄}`).
  have hΔpPowLp : ∀ (σ : ℝ) (φ : SmoothPeriodic d),
      Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (γBarReal / (hweak.α - 1)))
        (fun x => ‖fun i => |fam.Du ε i x| + |Dυ σ φ i x|‖ ^ (hweak.α - 1)) := by
    intro σ φ
    have hmul : ENNReal.ofReal (γBarReal / (hweak.α - 1))
        * ENNReal.ofReal (hweak.α - 1) = ENNReal.ofReal γBarReal := by
      rw [← ENNReal.ofReal_mul (le_of_lt (div_pos hγr_pos hαm1_pos))]
      congr 1
      field_simp
    have hrpow := Periodic.MemLpPer.rpow_closure (d := d)
      (s := ENNReal.ofReal (γBarReal / (hweak.α - 1))) (r := hweak.α - 1) hαm1_pos
      (f := fun x : (Fin d → ℝ) => ‖fun i => |fam.Du ε i x| + |Dυ σ φ i x|‖)
      (by rw [hmul]; exact hNormΔpLp σ φ)
    have heq : (fun x => ‖‖(fun i : Fin d => |fam.Du ε i x| + |Dυ σ φ i x|)‖‖ ^ (hweak.α - 1))
        = (fun x => ‖fun i => |fam.Du ε i x| + |Dυ σ φ i x|‖ ^ (hweak.α - 1)) := by
      funext x; rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    rwa [heq] at hrpow
  -- Cert `hΔm_grad`: `Δm · ‖Δp‖^{α-1} ∈ L^{γ̄'}` via the `(β̄, γ̄/(α-1))` HolderTriple.
  have hΔm_grad_cert : ∀ (σ : ℝ) (φ : SmoothPeriodic d), Periodic.MemLpPer (d := d) (ENNReal.ofReal γ'r)
      (fun x => (|fam.m ε x| + |fam.m ε x|)
          * ‖fun i => |fam.Du ε i x| + |Dυ σ φ i x|‖ ^ (hweak.α - 1)) := by
    intro σ φ
    -- The real HolderTriple `(β̄, γ̄/(α-1), γ̄')`: `1/β̄ + (α-1)/γ̄ = 1/γ̄'`.
    have hHT_real : Real.HolderTriple (hweak.β + 1)
        (γBarReal / (hweak.α - 1)) γ'r := by
      refine ⟨?_, hβ1_pos, div_pos hγr_pos hαm1_pos⟩
      rw [hγ'r_def]
      unfold StationaryMFG.Hamiltonian.gammaBar'
      rw [hg_id]
      have hβne : hweak.β ≠ 0 := hβ0.ne'
      have hbb_ne : hweak.β + 1 ≠ 0 := hβ1_pos.ne'
      have hαm1_ne : hweak.α - 1 ≠ 0 := hαm1_pos.ne'
      have hγne : γBarReal ≠ 0 := hγr_pos.ne'
      have hγm1_ne : γBarReal - 1 ≠ 0 := hγm1_pos.ne'
      have hγβ : γBarReal * hweak.β = hweak.α * (hweak.β + 1) := by
        rw [← hg_id]; unfold StationaryMFG.Hamiltonian.gammaBar; field_simp
      field_simp
      nlinarith [hγβ, hαpos, hβ0, hγr_pos]
    haveI hHT : ENNReal.HolderTriple (ENNReal.ofReal (hweak.β + 1))
        (ENNReal.ofReal (γBarReal / (hweak.α - 1))) (ENNReal.ofReal γ'r) :=
      hHT_real.ennrealOfReal
    have hmul := Periodic.MemLpPer.mul_holderTriple
      (p := ENNReal.ofReal (hweak.β + 1))
      (q := ENNReal.ofReal (γBarReal / (hweak.α - 1)))
      (s := ENNReal.ofReal γ'r)
      hΔmβ (hΔpPowLp σ φ)
    exact hmul
  -- Cert `hΔp_pow`: `‖Δp‖^α + 1 ∈ L^{β̄'}`.
  have hΔp_pow_cert : ∀ (σ : ℝ) (φ : SmoothPeriodic d), Periodic.MemLpPer (d := d) (ENNReal.ofReal β')
      (fun x => ‖fun i => |fam.Du ε i x| + |Dυ σ φ i x|‖ ^ hweak.α + 1) := by
    intro σ φ
    have hrpow := Periodic.MemLpPer.rpow_closure (d := d) (s := ENNReal.ofReal β')
      (r := hweak.α) hαpos
      (f := fun x : (Fin d → ℝ) => ‖fun i => |fam.Du ε i x| + |Dυ σ φ i x|‖)
      (by rw [hmulαβ']; exact hNormΔpLp σ φ)
    have heq : (fun x => ‖‖(fun i : Fin d => |fam.Du ε i x| + |Dυ σ φ i x|)‖‖ ^ hweak.α)
        = (fun x => ‖(fun i : Fin d => |fam.Du ε i x| + |Dυ σ φ i x|)‖ ^ hweak.α) := by
      funext x; rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    rw [heq] at hrpow
    have hsum := hrpow.add hOneβ'
    have heqf :
        ((fun x => ‖(fun i : Fin d => |fam.Du ε i x| + |Dυ σ φ i x|)‖ ^ hweak.α)
          + (fun _ : (Fin d → ℝ) => (1 : ℝ)))
        = (fun x => ‖fun i => |fam.Du ε i x| + |Dυ σ φ i x|‖ ^ hweak.α + 1) := by
      funext x; simp [Pi.add_apply]
    rwa [heqf] at hsum
  -- Cert `hΔm_pow`: `Δm^β + 1 ∈ L^{β̄'}`.
  have hΔm_pow_cert : ∀ (σ : ℝ) (φ : SmoothPeriodic d), Periodic.MemLpPer (d := d) (ENNReal.ofReal β')
      (fun x => (|fam.m ε x| + |fam.m ε x|) ^ hweak.β + 1) := by
    intro σ φ
    have hrpow := Periodic.MemLpPer.rpow_closure (d := d) (s := ENNReal.ofReal β')
      (r := hweak.β) hβ0
      (f := fun x : (Fin d → ℝ) => |fam.m ε x| + |fam.m ε x|)
      (by rw [hmulβ'β]; exact hΔmβ)
    have hΔm_nn : ∀ x, 0 ≤ |fam.m ε x| + |fam.m ε x| :=
      fun x => add_nonneg (abs_nonneg _) (abs_nonneg _)
    have heq : (fun x => ‖|fam.m ε x| + |fam.m ε x|‖ ^ hweak.β)
        = (fun x => (|fam.m ε x| + |fam.m ε x|) ^ hweak.β) := by
      funext x; rw [Real.norm_eq_abs, abs_of_nonneg (hΔm_nn x)]
    rw [heq] at hrpow
    have hsum := hrpow.add hOneβ'
    have heqf :
        ((fun x => (|fam.m ε x| + |fam.m ε x|) ^ hweak.β)
          + (fun _ : (Fin d → ℝ) => (1 : ℝ)))
        = (fun x => (|fam.m ε x| + |fam.m ε x|) ^ hweak.β + 1) := by
      funext x; simp [Pi.add_apply]
    rwa [heqf] at hsum
  -- Cert `hΔυ`: `|ῡ| + |υ| = |u| + |u+σφ| ∈ L^{β̄'}`.
  have hΔυ_cert : ∀ (σ : ℝ) (φ : SmoothPeriodic d), Periodic.MemLpPer (d := d) (ENNReal.ofReal β')
      (fun x => |fam.u ε x| + |υ σ φ x|) := by
    intro σ φ
    have hu_β' : Periodic.MemLpPer (d := d) (ENNReal.ofReal β') (fam.u ε) :=
      Periodic.MemLpPer.mono_exponent_finite hβ'_le_γ ENNReal.ofReal_ne_top hu_γ
    have hυ_β' : Periodic.MemLpPer (d := d) (ENNReal.ofReal β') (υ σ φ) :=
      Periodic.MemLpPer.mono_exponent_finite hβ'_le_γ ENNReal.ofReal_ne_top (hυLp σ φ)
    exact MemLp.toMemLpPer (hu_β'.toMemLp.abs.add hυ_β'.toMemLp.abs)
  -- Exponent identity: `γ̄' · (γ̄ - 1) = γ̄`.
  have hmulγ'γm1 : ENNReal.ofReal γ'r * ENNReal.ofReal (γBarReal - 1)
      = ENNReal.ofReal γBarReal := by
    rw [← ENNReal.ofReal_mul (le_of_lt hγ'r_pos)]
    congr 1
    rw [hγ'r_def]
    unfold StationaryMFG.Hamiltonian.gammaBar' StationaryMFG.Hamiltonian.gammaBar
    have hγne : γBarReal ≠ 0 := hγr_pos.ne'
    have hγm1ne : γBarReal - 1 ≠ 0 := hγm1_pos.ne'
    rw [show (hweak.α * (hweak.β + 1) / hweak.β : ℝ)
          = StationaryMFG.Hamiltonian.gammaBar hweak.α hweak.β from rfl, hg_id]
    field_simp
  -- `υSum := |ῡ| + |υ| ∈ L^{γ̄}`.
  have hυSumLp : ∀ (σ : ℝ) (φ : SmoothPeriodic d),
      Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal)
        (fun x => |fam.u ε x| + |υ σ φ x|) := fun σ φ =>
    MemLp.toMemLpPer (hu_γ.toMemLp.abs.add (hυLp σ φ).toMemLp.abs)
  -- Gateaux cert `bG_val`: `(|ῡ|+|υ|)^{γ̄-1} ∈ L^{γ̄'}`.
  have hG_val_cert : ∀ (σ : ℝ) (φ : SmoothPeriodic d), Periodic.MemLpPer (d := d) (ENNReal.ofReal γ'r)
      (fun x => (|fam.u ε x| + |υ σ φ x|) ^ (γBarReal - 1)) := by
    intro σ φ
    have hrpow := Periodic.MemLpPer.rpow_closure (d := d) (s := ENNReal.ofReal γ'r)
      (r := γBarReal - 1) hγm1_pos
      (f := fun x : (Fin d → ℝ) => |fam.u ε x| + |υ σ φ x|)
      (by rw [hmulγ'γm1]; exact hυSumLp σ φ)
    have hυSum_nn : ∀ x, 0 ≤ |fam.u ε x| + |υ σ φ x| :=
      fun x => add_nonneg (abs_nonneg _) (abs_nonneg _)
    have heq : (fun x => ‖|fam.u ε x| + |υ σ φ x|‖ ^ (γBarReal - 1))
        = (fun x => (|fam.u ε x| + |υ σ φ x|) ^ (γBarReal - 1)) := by
      funext x; rw [Real.norm_eq_abs, abs_of_nonneg (hυSum_nn x)]
    rwa [heq] at hrpow
  -- Gateaux cert `bG_grad`: `(∑ (|ῡ i|+|υ i|)^2)^{(γ̄-1)/2} ∈ L^{γ̄'}`.
  have hG_grad_cert : ∀ (σ : ℝ) (φ : SmoothPeriodic d), Periodic.MemLpPer (d := d) (ENNReal.ofReal γ'r)
      (fun x =>
        (∑ i, (|fam.Du ε i x| + |Dυ σ φ i x|) ^ (2 : ℕ)) ^ ((γBarReal - 1) / 2)) := by
    intro σ φ
    -- `∑ (Δp i)^2 ∈ L^{γ̄/2}` (each `(Δp i)^2 = ‖Δp i‖^2 ∈ L^{γ̄/2}`).
    have hexp12_pos : (0 : ℝ) < (γBarReal - 1) / 2 := by positivity
    set q2 : ℝ≥0∞ := ENNReal.ofReal 2 with hq2_def
    have hSqEach : ∀ i, Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal / q2)
        (fun x : (Fin d → ℝ) => (|fam.Du ε i x| + |Dυ σ φ i x|) ^ (2 : ℕ)) := by
      intro i
      have hcoordLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal)
          (fun x => |fam.Du ε i x| + |Dυ σ φ i x|) :=
        MemLp.toMemLpPer ((hDu_γ i).toMemLp.abs.add (hDυLp σ φ i).toMemLp.abs)
      have h := MeasureTheory.MemLp.norm_rpow_div hcoordLp.toMemLp q2
      have hq2tr : q2.toReal = 2 := by rw [hq2_def]; simp
      have heq : (fun x : (Fin d → ℝ) =>
            ‖|fam.Du ε i x| + |Dυ σ φ i x|‖ ^ q2.toReal)
          = (fun x => (|fam.Du ε i x| + |Dυ σ φ i x|) ^ (2 : ℕ)) := by
        funext x
        rw [hq2tr, Real.norm_eq_abs,
          abs_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)),
          show ((2 : ℝ) = ((2 : ℕ) : ℝ)) from by norm_num, Real.rpow_natCast]
      rw [heq] at h
      exact MemLp.toMemLpPer h
    have hSumSq : Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal / q2)
        (fun x : (Fin d → ℝ) => ∑ i, (|fam.Du ε i x| + |Dυ σ φ i x|) ^ (2 : ℕ)) :=
      MemLp.toMemLpPer
        (MeasureTheory.memLp_finset_sum (Finset.univ : Finset (Fin d))
          (fun i _ => (hSqEach i).toMemLp))
    -- rpow at exponent `(γ̄-1)/2` lands in `L^{(γ̄/2)/((γ̄-1)/2)} = L^{γ̄'}`.
    have hγ'half : γ'r * ((γBarReal - 1) / 2) = γBarReal / 2 := by
      rw [hγ'r_def]
      unfold StationaryMFG.Hamiltonian.gammaBar'
      rw [hg_id]
      have hγne : γBarReal ≠ 0 := hγr_pos.ne'
      have hγm1ne : γBarReal - 1 ≠ 0 := hγm1_pos.ne'
      field_simp
    have hq2eq : q2 = ENNReal.ofReal 2 := hq2_def
    have hexpmul : ENNReal.ofReal γ'r * ENNReal.ofReal ((γBarReal - 1) / 2)
        = ENNReal.ofReal γBarReal / q2 := by
      rw [← ENNReal.ofReal_mul (le_of_lt hγ'r_pos), hγ'half, hq2eq,
        ← ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2)]
    have hrpow := Periodic.MemLpPer.rpow_closure (d := d)
      (s := ENNReal.ofReal γ'r) (r := (γBarReal - 1) / 2) hexp12_pos
      (f := fun x : (Fin d → ℝ) => ∑ i, (|fam.Du ε i x| + |Dυ σ φ i x|) ^ (2 : ℕ))
      (by rw [hexpmul]; exact hSumSq)
    have hSumSq_nn : ∀ x, 0 ≤ ∑ i, (|fam.Du ε i x| + |Dυ σ φ i x|) ^ (2 : ℕ) :=
      fun x => Finset.sum_nonneg (fun i _ => pow_nonneg
        (add_nonneg (abs_nonneg _) (abs_nonneg _)) 2)
    have heq : (fun x : (Fin d → ℝ) =>
          ‖∑ i, (|fam.Du ε i x| + |Dυ σ φ i x|) ^ (2 : ℕ)‖ ^ ((γBarReal - 1) / 2))
        = (fun x => (∑ i, (|fam.Du ε i x| + |Dυ σ φ i x|) ^ (2 : ℕ))
              ^ ((γBarReal - 1) / 2)) := by
      funext x; rw [Real.norm_eq_abs, abs_of_nonneg (hSumSq_nn x)]
    rwa [heq] at hrpow
  -- Choose the dominators in the natural form with `η = 0`.
  refine ⟨fun σ φ =>
      Banach.g_unreg_natural hweak.α hweak.β Cε Cε V
        (fun i x => fam.Du ε i x + σ *
          ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) x)
        (fam.Du ε) (fam.m ε) (fam.m ε)
        (fun x => fam.u ε x + σ * (φ : (Fin d → ℝ) → ℝ) x) (fam.u ε)
        (fun i x => σ *
          ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) x)
        (fun _ => (0 : ℝ)) (fun x => σ * (φ : (Fin d → ℝ) → ℝ) x),
    fun σ φ =>
      Banach.g_gat_natural γBarReal
        (fun i x => fam.Du ε i x + σ *
          ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) x)
        (fam.Du ε)
        (fun x => fam.u ε x + σ * (φ : (Fin d → ℝ) → ℝ) x) (fam.u ε)
        (fun i x => σ *
          ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) x)
        (fun x => σ * (φ : (Fin d → ℝ) → ℝ) x),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `hg_unreg_int`: integrability of the natural-form unreg dominator.
    intro σ φ
    have hηLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (StationaryMFG.Hamiltonian.betaBar hweak.β))
        (fun _ : (Fin d → ℝ) => (0 : ℝ)) := MemLp.toMemLpPer (memLp_const 0)
    have hV' : Periodic.MemLpPer (d := d) (ENNReal.ofReal β') V := by
      have heqp : ENNReal.ofReal βBar' = ENNReal.ofReal β' := by rw [hβBar'_eq]
      rw [← heqp]; exact hV
    have hγ_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal γBarReal := by
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
      exact ENNReal.ofReal_le_ofReal hγ.le
    exact Banach.g_unreg_natural_integrableOn_min
      (α := hweak.α) (β := hweak.β) (C := Cε) (C' := Cε) (V := V)
      (Dυ := Dυ σ φ) (Dῡ := fam.Du ε) (μ := fam.m ε) (mBar := fam.m ε)
      (υ := υ σ φ) (ῡ := fam.u ε) (Dν := Dν σ φ)
      (η := fun _ => (0 : ℝ)) (ν := ν σ φ)
      hβconj hγconj hγ_one_le hηLp (hDνLp σ φ) (hνLp σ φ) hV'
      (hΔυ_cert σ φ) (hΔp_pow_cert σ φ) (hΔm_pow_cert σ φ)
      (hΔm_grad_cert σ φ) (hΔm_endpoint_cert σ φ) (hΔm_cert σ φ)
  · -- `hg_gat_int`: integrability of the natural-form gateaux dominator.
    intro σ φ
    exact Banach.g_gat_natural_integrableOn
      (γBar := γBarReal)
      (Dυ := Dυ σ φ) (Dῡ := fam.Du ε) (υ := υ σ φ) (ῡ := fam.u ε)
      (Dν := Dν σ φ) (ν := ν σ φ)
      hγconj (hDνLp σ φ) (hνLp σ φ) (hG_grad_cert σ φ) (hG_val_cert σ φ)
  · -- `hF_unreg_meas`: with `η = 0` the H-term is killed, so only the flux
    -- `JsimpleExt`-composite and the `(m-1)·ν` value piece remain.
    intro σ φ t ht
    have hsmoothDφ : ∀ i, AEMeasurable
        ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) : (Fin d → ℝ) → ℝ)
        (volume.restrict (UnitCube d)) :=
      fun i => (SmoothPeriodic.partialDeriv i φ).smooth.continuous.aemeasurable
    have hsmoothφ : AEMeasurable ((φ : SmoothPeriodic d) : (Fin d → ℝ) → ℝ)
        (volume.restrict (UnitCube d)) := φ.smooth.continuous.aemeasurable
    have hDu_aem : ∀ i, AEMeasurable (fam.Du ε i) (volume.restrict (UnitCube d)) :=
      fun i => (hDu_γ i).aestronglyMeasurable.aemeasurable
    have hm_aem : AEMeasurable (fam.m ε) (volume.restrict (UnitCube d)) :=
      hmLp_β.aestronglyMeasurable.aemeasurable
    -- Collapsed integrand value (η = 0), pointwise for all x.
    have hcollapse :
        (fun x =>
            aepsiIntegrandAt_unreg_K0 (d := d) V (HdeltaK0 hweak ε)
              (DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε)
              (Dυ σ φ) (fam.Du ε) (fam.m ε) (fam.m ε) (υ σ φ) (fam.u ε)
              (Dν σ φ) (fun _ => (0 : ℝ)) (ν σ φ) x t)
          = (fun x =>
              (JsimpleExt (DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε) x
                  (fun i => cxCombGrad (Dυ σ φ) (fam.Du ε) t i x) (fam.m ε x)
                  ⬝ (fun i => Dν σ φ i x))
              + (fam.m ε x - 1) * ν σ φ x) := by
      funext x
      have hμtx : cxComb (fam.m ε) (fam.m ε) t x = fam.m ε x := by
        simp only [cxComb]; ring
      simp only [aepsiIntegrandAt_unreg_K0, mul_zero, zero_add, hμtx]
    rw [hcollapse]
    -- AEMeasurability of the gradient slot `x ↦ (fun i => cxCombGrad …)`.
    have hgrad_aem : AEMeasurable
        (fun x : (Fin d → ℝ) =>
          (fun i : Fin d => cxCombGrad (Dυ σ φ) (fam.Du ε) t i x))
        (volume.restrict (UnitCube d)) := by
      refine aemeasurable_pi_iff.mpr fun i => ?_
      simp only [cxCombGrad, hDυ_def]
      exact (aemeasurable_const.mul (hDu_aem i)).add
        (aemeasurable_const.mul ((hDu_aem i).add
          (aemeasurable_const.mul (hsmoothDφ i))))
    -- The DpH composite is AEMeasurable (global measurable ∘ AEMeas map).
    have hDpH_meas := measurable_DpHepsilonFam_of_selector hweak qε sel hMeas ε
    have hmap_aem : AEMeasurable
        (fun x : (Fin d → ℝ) =>
          (x, (fun i : Fin d => cxCombGrad (Dυ σ φ) (fam.Du ε) t i x), fam.m ε x))
        (volume.restrict (UnitCube d)) :=
      aemeasurable_id.prodMk (hgrad_aem.prodMk hm_aem)
    have hDpHcomp_aem : AEMeasurable
        (fun x : (Fin d → ℝ) =>
          DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε x
            (fun i => cxCombGrad (Dυ σ φ) (fam.Du ε) t i x) (fam.m ε x))
        (volume.restrict (UnitCube d)) :=
      hDpH_meas.comp_aemeasurable hmap_aem
    -- The flux `JsimpleExt = m • DpHε`, dotted with smooth `Dν`.
    have hflux_aem : AEStronglyMeasurable
        (fun x : (Fin d → ℝ) =>
          JsimpleExt (DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε) x
              (fun i => cxCombGrad (Dυ σ φ) (fam.Du ε) t i x) (fam.m ε x)
            ⬝ (fun i => Dν σ φ i x))
        (volume.restrict (UnitCube d)) := by
      unfold JsimpleExt dotProduct
      refine AEMeasurable.aestronglyMeasurable ?_
      refine Finset.aemeasurable_fun_sum (s := Finset.univ) (fun i _ => ?_)
      have hJi : AEMeasurable
          (fun x : (Fin d → ℝ) =>
            (fam.m ε x • DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε x
              (fun i => cxCombGrad (Dυ σ φ) (fam.Du ε) t i x) (fam.m ε x)) i)
          (volume.restrict (UnitCube d)) := by
        simp only [Pi.smul_apply, smul_eq_mul]
        exact hm_aem.mul (hDpHcomp_aem.eval i)
      exact hJi.mul (aemeasurable_const.mul (hsmoothDφ i))
    -- The value piece `(m-1)·ν`.
    have hval_aem : AEStronglyMeasurable
        (fun x : (Fin d → ℝ) => (fam.m ε x - 1) * ν σ φ x)
        (volume.restrict (UnitCube d)) := by
      simp only [hν_def]
      exact ((hm_aem.sub aemeasurable_const).mul
        (aemeasurable_const.mul hsmoothφ)).aestronglyMeasurable
    exact hflux_aem.add hval_aem
  · -- `hF_unreg_bound`: the η=0 K0 flux pointwise bound, re-derived
    -- hPow-free from `hAE.DpH_upper_ae` + `JsimpleExt`/`JsimpleExt_zero`.
    intro σ φ t ht
    have ht0 : (0 : ℝ) ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2
    filter_upwards [hAE.DpH_upper_ae ε hεpos hε1ε, hmNonneg]
      with x hxDpH hxNonneg
    -- Abbreviations.
    set Dυt : Fin d → ℝ := fun i => cxCombGrad (Dυ σ φ) (fam.Du ε) t i x with hDυt_def
    set m0 : ℝ := fam.m ε x with hm0_def
    have hm0_nn : 0 ≤ m0 := hxNonneg
    -- `μt = cxComb m m t x = m`.
    have hμtx : cxComb (fam.m ε) (fam.m ε) t x = m0 := by
      simp only [cxComb, hm0_def]; ring
    -- The K0 integrand collapses (η = 0) to `flux + (m-1)·ν`.
    have hval :
        aepsiIntegrandAt_unreg_K0 (d := d) V (HdeltaK0 hweak ε)
          (DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε)
          (Dυ σ φ) (fam.Du ε) (fam.m ε) (fam.m ε) (υ σ φ) (fam.u ε)
          (Dν σ φ) (fun _ => (0 : ℝ)) (ν σ φ) x t
        = (JsimpleExt (DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε) x Dυt m0
              ⬝ (fun i => Dν σ φ i x))
          + (m0 - 1) * ν σ φ x := by
      simp only [aepsiIntegrandAt_unreg_K0, mul_zero, zero_add, hμtx, ← hDυt_def]
    rw [hval, Real.norm_eq_abs]
    -- Flux = `m0 · (DpHε ⬝ Dν)` via `JsimpleExt = m0 • DpHε`.
    set DpHv : Fin d → ℝ := DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε x Dυt m0
      with hDpHv_def
    have hflux : (JsimpleExt (DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε) x Dυt m0
          ⬝ (fun i => Dν σ φ i x))
        = m0 * (DpHv ⬝ (fun i => Dν σ φ i x)) := by
      unfold JsimpleExt
      rw [hDpHv_def]
      exact euclideanDot_smul_left m0 DpHv (fun i => Dν σ φ i x)
    rw [hflux]
    -- Norm splitting.
    set Δm : ℝ := |fam.m ε x| + |fam.m ε x| with hΔm_def
    set Δp : Fin d → ℝ := fun i => |fam.Du ε i x| + |Dυ σ φ i x| with hΔp_def
    set sν : ℝ := ∑ i, |Dν σ φ i x| with hsν_def
    have hsν_nn : 0 ≤ sν := Finset.sum_nonneg (fun i _ => abs_nonneg _)
    -- `g_unreg_natural` value at `x` (η = 0 ⇒ terms 1-3 vanish).
    have hg :
        Banach.g_unreg_natural hweak.α hweak.β Cε Cε V (Dυ σ φ) (fam.Du ε)
          (fam.m ε) (fam.m ε) (υ σ φ) (fam.u ε) (Dν σ φ) (fun _ => (0 : ℝ))
          (ν σ φ) x
        = Cε * (Δm * ‖Δp‖ ^ (hweak.α - 1)
                  + Δm ^ (1 + hweak.β - hweak.β / hweak.α) + Δm) * sν
          + (Δm + 1) * |ν σ φ x| := by
      simp only [Banach.g_unreg_natural, abs_zero, mul_zero, add_zero, zero_add,
        hΔm_def, hΔp_def, hsν_def]
    rw [hg]
    -- `Δm = 2·|m0|`, `|m0| = m0` (m0 ≥ 0).
    have hΔm_eq : Δm = m0 + m0 := by
      rw [hΔm_def, hm0_def, abs_of_nonneg hm0_nn]
    -- Bound the flux: case split on `m0 = 0` or `m0 > 0`.
    have hCε_nn : 0 ≤ Cε := hCε_pos.le
    have hΔp_nn : 0 ≤ ‖Δp‖ := norm_nonneg _
    have hΔppow_nn : 0 ≤ ‖Δp‖ ^ (hweak.α - 1) := Real.rpow_nonneg hΔp_nn _
    have hΔmend_nn : 0 ≤ Δm ^ (1 + hweak.β - hweak.β / hweak.α) :=
      Real.rpow_nonneg (by rw [hΔm_eq]; linarith [hm0_nn]) _
    have hΔm_nn : 0 ≤ Δm := by rw [hΔm_eq]; linarith [hm0_nn]
    have hbracket_nn : 0 ≤ Cε * (Δm * ‖Δp‖ ^ (hweak.α - 1)
        + Δm ^ (1 + hweak.β - hweak.β / hweak.α) + Δm) * sν := by
      apply mul_nonneg (mul_nonneg hCε_nn _) hsν_nn
      exact add_nonneg (add_nonneg (mul_nonneg hΔm_nn hΔppow_nn) hΔmend_nn) hΔm_nn
    -- Flux bound.
    have hfluxbd : |m0 * (DpHv ⬝ (fun i => Dν σ φ i x))|
        ≤ Cε * (Δm * ‖Δp‖ ^ (hweak.α - 1)
                  + Δm ^ (1 + hweak.β - hweak.β / hweak.α) + Δm) * sν := by
      rcases eq_or_lt_of_le hm0_nn with hm0eq | hm0pos
      · -- `m0 = 0`: flux is `0`.
        rw [← hm0eq, zero_mul, abs_zero]
        exact hbracket_nn
      · -- `m0 > 0`: use the `DpH_upper_ae` bound.
        have hDpHbd : ‖DpHv‖ ≤ Cε * (‖Dυt‖ ^ (hweak.α - 1)
            + m0 ^ (hweak.β - hweak.β / hweak.α) + 1) := by
          rw [hDpHv_def, hCε_def]; exact hxDpH Dυt m0 hm0pos
        -- `‖Dυt‖ ≤ ‖Δp‖`.
        have hnorm_pt : ‖Dυt‖ ≤ ‖Δp‖ := by
          rw [hDυt_def, hΔp_def]
          exact cxCombGrad_norm_le (Dυ σ φ) (fam.Du ε) x ht
        -- `|DpHv ⬝ Dν| ≤ ‖DpHv‖ · sν`  (coordinate-wise `L^∞ × L^1`).
        have hdot : |DpHv ⬝ (fun i => Dν σ φ i x)| ≤ ‖DpHv‖ * sν := by
          rw [hsν_def]
          unfold dotProduct
          calc |∑ i, DpHv i * Dν σ φ i x|
              ≤ ∑ i, |DpHv i * Dν σ φ i x| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ i, ‖DpHv‖ * |Dν σ φ i x| := by
                apply Finset.sum_le_sum
                intro i _
                rw [abs_mul]
                exact mul_le_mul_of_nonneg_right
                  (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm DpHv i)
                  (abs_nonneg _)
            _ = ‖DpHv‖ * ∑ i, |Dν σ φ i x| := by rw [Finset.mul_sum]
        -- Chain.
        have hm0_abs : |m0| = m0 := abs_of_nonneg hm0_nn
        rw [abs_mul, hm0_abs]
        have hstep1 : m0 * |DpHv ⬝ (fun i => Dν σ φ i x)|
            ≤ m0 * (‖DpHv‖ * sν) :=
          mul_le_mul_of_nonneg_left hdot hm0_nn
        have hstep2 : m0 * (‖DpHv‖ * sν)
            ≤ m0 * (Cε * (‖Δp‖ ^ (hweak.α - 1)
                + m0 ^ (hweak.β - hweak.β / hweak.α) + 1) * sν) := by
          apply mul_le_mul_of_nonneg_left _ hm0_nn
          apply mul_le_mul_of_nonneg_right _ hsν_nn
          -- `‖DpHv‖ ≤ Cε·(‖Δp‖^{α-1} + m0^{β-β/α} + 1)` (mono in `‖Dυt‖ ≤ ‖Δp‖`).
          have hmono : ‖Dυt‖ ^ (hweak.α - 1) ≤ ‖Δp‖ ^ (hweak.α - 1) :=
            Real.rpow_le_rpow (norm_nonneg _) hnorm_pt hαm1_pos.le
          calc ‖DpHv‖ ≤ Cε * (‖Dυt‖ ^ (hweak.α - 1)
                + m0 ^ (hweak.β - hweak.β / hweak.α) + 1) := hDpHbd
            _ ≤ Cε * (‖Δp‖ ^ (hweak.α - 1)
                + m0 ^ (hweak.β - hweak.β / hweak.α) + 1) := by
                apply mul_le_mul_of_nonneg_left _ hCε_nn; linarith [hmono]
        -- Now `m0·(Cε·(...)·sν) ≤ Cε·(Δm·‖Δp‖^{α-1} + Δm^{1+β-β/α} + Δm)·sν`.
        have hfinal : m0 * (Cε * (‖Δp‖ ^ (hweak.α - 1)
                + m0 ^ (hweak.β - hweak.β / hweak.α) + 1) * sν)
            ≤ Cε * (Δm * ‖Δp‖ ^ (hweak.α - 1)
                  + Δm ^ (1 + hweak.β - hweak.β / hweak.α) + Δm) * sν := by
          -- `m0 ≤ Δm`, `m0·m0^{β-β/α} = m0^{1+β-β/α} ≤ Δm^{1+β-β/α}`.
          have hm0_le_Δm : m0 ≤ Δm := by rw [hΔm_eq]; linarith [hm0_nn]
          have hm0_ne : m0 ≠ 0 := hm0pos.ne'
          have hmpow_id : m0 * m0 ^ (hweak.β - hweak.β / hweak.α)
              = m0 ^ (1 + hweak.β - hweak.β / hweak.α) := by
            rw [show (1 + hweak.β - hweak.β / hweak.α)
                  = (hweak.β - hweak.β / hweak.α) + 1 by ring,
              Real.rpow_add_one hm0_ne]
            ring
          have hmpow_le : m0 ^ (1 + hweak.β - hweak.β / hweak.α)
              ≤ Δm ^ (1 + hweak.β - hweak.β / hweak.α) :=
            Real.rpow_le_rpow hm0_nn hm0_le_Δm
              (by linarith [hexp_endpoint_pos])
          -- Expand and compare term-by-term.
          rw [show m0 * (Cε * (‖Δp‖ ^ (hweak.α - 1)
                + m0 ^ (hweak.β - hweak.β / hweak.α) + 1) * sν)
              = Cε * (m0 * ‖Δp‖ ^ (hweak.α - 1)
                + m0 * m0 ^ (hweak.β - hweak.β / hweak.α) + m0) * sν by ring,
            hmpow_id]
          apply mul_le_mul_of_nonneg_right _ hsν_nn
          apply mul_le_mul_of_nonneg_left _ hCε_nn
          have h1 : m0 * ‖Δp‖ ^ (hweak.α - 1) ≤ Δm * ‖Δp‖ ^ (hweak.α - 1) :=
            mul_le_mul_of_nonneg_right hm0_le_Δm hΔppow_nn
          linarith [h1, hmpow_le, hm0_le_Δm]
        exact le_trans hstep1 (le_trans hstep2 hfinal)
    -- Value bound: `|(m0-1)·ν| ≤ (Δm+1)·|ν|`.
    have hvalbd : |(m0 - 1) * ν σ φ x| ≤ (Δm + 1) * |ν σ φ x| := by
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      have : |m0 - 1| ≤ m0 + 1 := by
        rw [abs_le]; constructor <;> linarith [hm0_nn]
      rw [hΔm_eq]; linarith [this, hm0_nn]
    -- Combine via triangle inequality.
    calc |m0 * (DpHv ⬝ (fun i => Dν σ φ i x)) + (m0 - 1) * ν σ φ x|
        ≤ |m0 * (DpHv ⬝ (fun i => Dν σ φ i x))| + |(m0 - 1) * ν σ φ x| :=
          abs_add_le _ _
      _ ≤ Cε * (Δm * ‖Δp‖ ^ (hweak.α - 1)
                  + Δm ^ (1 + hweak.β - hweak.β / hweak.α) + Δm) * sν
            + (Δm + 1) * |ν σ φ x| := add_le_add hfluxbd hvalbd
  · -- `hF_gat_meas`: reuse the dedicated gateaux measurability lemma.
    intro σ φ t ht
    have hsmoothDφ : ∀ i, AEStronglyMeasurable
        ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) : (Fin d → ℝ) → ℝ)
        (volume.restrict (UnitCube d)) :=
      fun i => (SmoothPeriodic.partialDeriv i φ).smooth.continuous.aestronglyMeasurable
    have hsmoothφ : AEStronglyMeasurable
        ((φ : SmoothPeriodic d) : (Fin d → ℝ) → ℝ)
        (volume.restrict (UnitCube d)) :=
      φ.smooth.continuous.aestronglyMeasurable
    have hDu_asm : ∀ i, AEStronglyMeasurable (fam.Du ε i)
        (volume.restrict (UnitCube d)) := fun i => (hDu_γ i).aestronglyMeasurable
    have hu_asm : AEStronglyMeasurable (fam.u ε)
        (volume.restrict (UnitCube d)) := hu_γ.aestronglyMeasurable
    exact aestronglyMeasurable_aepsiIntegrandAt_gateaux (d := d) γBarReal
      (Dυ := Dυ σ φ) (Dῡ := fam.Du ε) (υ := υ σ φ) (ῡ := fam.u ε)
      (Dν := Dν σ φ) (ν := ν σ φ)
      (hυLp σ φ).aestronglyMeasurable hu_asm
      (fun i => (hDυLp σ φ i).aestronglyMeasurable) hDu_asm
      (fun i => (hDνLp σ φ i).aestronglyMeasurable)
      (hνLp σ φ).aestronglyMeasurable t
  · -- `hF_gat_bound`: product-form gateaux pointwise bound, t-uniform.
    intro σ φ t ht
    refine Filter.Eventually.of_forall ?_
    intro x
    have hgat := aepsiIntegrandAt_gateaux_pointwise_bound_product (d := d)
      (γBar := γBarReal) hγ
      (Dυ σ φ) (fam.Du ε) (υ σ φ) (fam.u ε) (Dν σ φ) (ν σ φ) x t ht
    -- The RHS equals `g_gat_natural`.
    have heqg : (∑ i, (|fam.Du ε i x| + |Dυ σ φ i x|) ^ (2 : ℕ)) ^ ((γBarReal - 1) / 2)
            * (∑ i, |Dν σ φ i x|)
          + (|fam.u ε x| + |υ σ φ x|) ^ (γBarReal - 1) * |ν σ φ x|
        = Banach.g_gat_natural γBarReal (Dυ σ φ) (fam.Du ε) (υ σ φ) (fam.u ε)
            (Dν σ φ) (ν σ φ) x := by
      unfold Banach.g_gat_natural; rfl
    rw [heqg] at hgat
    exact hgat

/-! ### D6c3b: the four `hPow`-free conjugate-exponent coefficient memberships

The producer `T3.fluxGatCoeffMemberships_of_family` supplies, per `ε > 0`, the
four `MemLpPer (ofReal γ̄')`-memberships consumed by
`hIdentityRaw_of_T3RegularizedStrongFamily` at `q = ofReal γ̄'`,
`p = ofReal γ̄`, `[HolderTriple p q 1]`:

* `haF`  : `fluxCoeffA (fam.m ε) = m − 1`, via `fam.hmLp` + `gammaBar'_le_betaBar`
  (`mono_exponent_finite`) plus the constant `−1`.
* `hbF i` : `fluxCoeffB DpHε (fam.m ε) (fam.Du ε) i = m·D_pH^ε_i`, via the
  dominator keystone `flux_dominator_memLpPer_explicit` + the η=0 AE flux bound
  (`hAE.DpH_upper_ae` + `JsimpleExt`, m=0/m>0 case split) packaged by
  `mDpH_mem_Lp_gammaBar'`, then a coordinate projection.
* `haG`  : `gatCoeffA γ̄ (fam.u ε) = |u|^{γ̄−2}·u`, via `abs_absPowMinusTwo_mul_self`
  (`|·| = |u|^{γ̄−1}`) + `rpow_closure` (`γ̄'(γ̄−1) = γ̄`) on `(fam.huSob ε).1`.
* `hbG i` : `gatCoeffB γ̄ (fam.Du ε) i = |Du|^{γ̄−2}·Du_i`, via
  `abs_vecAbsPowMinusTwo_mul_coord_le` (`|·| ≤ ‖Du‖^{γ̄−1}`) + `rpow_closure`
  on the vector norm `‖Du·‖ ∈ L^{γ̄}`.

Binders: `fam` plus the paper-accepted carriers `hMeas`/`sel`/`hAE` (the H-term
is killed by `η = 0`, so no `hmon`/`hdiff`/`hUB`/`hC0_le`), the
exponent reconciliations `hε1`/`hβBar`/`hγBar`, and `hγ : 1 < γ̄`. NO `hPow`,
NO loose `m`/`u`/`Du`, NO `*Pack`/`*Inputs`/`*Oracle`. -/
theorem T3.fluxGatCoeffMemberships_of_family
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d) {βBarReal γBarReal : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    (fam : T3RegularizedStrongFamily V hweak qε βBarReal γBarReal)
    (hMeas : StationaryMFG.Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (sel : StationaryMFG.InfimalConvolution.InfConvSelectorFamily
      (H := H) (DpH := DpH) hweak qε)
    (hAE : HdeltaAEPowerEpsData (H := H) (DpH := DpH) hweak qε)
    (hβBar : βBarReal = StationaryMFG.Hamiltonian.betaBar hweak.β)
    (hγBar : γBarReal = StationaryMFG.Hamiltonian.gammaBar hweak.α hweak.β)
    (hγ : 1 < γBarReal) :
    ∀ ε, 0 < ε → ε ≤ 1 →
      (Periodic.MemLpPer
          (ENNReal.ofReal
            (StationaryMFG.Hamiltonian.gammaBar' hweak.α hweak.β))
          (fluxCoeffA (fam.m ε))) ∧
      (∀ i, Periodic.MemLpPer
          (ENNReal.ofReal
            (StationaryMFG.Hamiltonian.gammaBar' hweak.α hweak.β))
          (fluxCoeffB (DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε)
            (fam.m ε) (fam.Du ε) i)) ∧
      (Periodic.MemLpPer
          (ENNReal.ofReal
            (StationaryMFG.Hamiltonian.gammaBar' hweak.α hweak.β))
          (gatCoeffA γBarReal (fam.u ε))) ∧
      (∀ i, Periodic.MemLpPer
          (ENNReal.ofReal
            (StationaryMFG.Hamiltonian.gammaBar' hweak.α hweak.β))
          (gatCoeffB γBarReal (fam.Du ε) i)) := by
  classical
  intro ε hε hε1ε
  -- Positivity facts on the exponents.
  have hα1 : (1 : ℝ) < hweak.α := hweak.hα
  have hβ0 : (0 : ℝ) < hweak.β := hweak.hβ
  have hαpos : (0 : ℝ) < hweak.α := lt_trans one_pos hα1
  have hαm1_pos : (0 : ℝ) < hweak.α - 1 := by linarith
  have hγr_pos : 0 < γBarReal := lt_trans zero_lt_one hγ
  have hγm1_pos : (0 : ℝ) < γBarReal - 1 := by linarith
  -- The per-`ε` constant.
  set Cε : ℝ := CdeltaEps (H := H) (DpH := DpH) hweak ε with hCε_def
  have hCε_pos : 0 < Cε := CdeltaEps_pos (H := H) (DpH := DpH) hweak hε
  -- The reconciled conjugate exponent `γ̄'` and its ENNReal form.
  set γ' : ℝ := StationaryMFG.Hamiltonian.gammaBar' hweak.α hweak.β with hγ'_def
  set q : ℝ≥0∞ := ENNReal.ofReal γ' with hq_def
  -- `γ̄ = γBarReal` (from `hγBar`).
  have hγbar_id : StationaryMFG.Hamiltonian.gammaBar hweak.α hweak.β = γBarReal :=
    hγBar.symm
  -- The cube has finite measure.
  haveI hfin : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  -- Family `Lᵖ` regularities at the concrete paper exponents.
  have hmLp_β : Periodic.MemLpPer (ENNReal.ofReal (hweak.β + 1)) (fam.m ε) := by
    have h := fam.hmLp ε hε hε1ε
    have hβeq : ENNReal.ofReal βBarReal = ENNReal.ofReal (hweak.β + 1) := by
      rw [hβBar]; rfl
    rwa [hβeq] at h
  have hDuLp_γ : ∀ i, Periodic.MemLpPer (ENNReal.ofReal γBarReal) (fam.Du ε i) :=
    fun i => fam.hDuLp ε hε hε1ε i
  have hu_γ : Periodic.MemLpPer (ENNReal.ofReal γBarReal) (fam.u ε) :=
    (fam.huSob ε hε hε1ε).1
  have hmNonneg := fam.hmNonneg ε hε hε1ε
  -- ===========================================================
  -- `haF`: `fluxCoeffA (fam.m ε) = m − 1 ∈ L^{γ̄'}`.
  -- ===========================================================
  have hγ'_le_β : q ≤ ENNReal.ofReal (hweak.β + 1) := by
    rw [hq_def, hγ'_def]
    apply ENNReal.ofReal_le_ofReal
    have := StationaryMFG.Hamiltonian.gammaBar'_le_betaBar hα1 hβ0
    -- `gammaBar' = γ̄/(γ̄-1)` and `γ̄ = α(β+1)/β` so this matches the lemma.
    unfold StationaryMFG.Hamiltonian.gammaBar' StationaryMFG.Hamiltonian.gammaBar
    exact this
  have hβTop : ENNReal.ofReal (hweak.β + 1) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hm_q : Periodic.MemLpPer q (fam.m ε) :=
    Periodic.MemLpPer.mono_exponent_finite hγ'_le_β hβTop hmLp_β
  have hOneq : Periodic.MemLpPer (d := d) q (fun _ : (Fin d → ℝ) => (1 : ℝ)) :=
    MemLp.toMemLpPer (memLp_const 1)
  have haF : Periodic.MemLpPer q (fluxCoeffA (fam.m ε)) := by
    -- `fluxCoeffA m = m + (-1)·1`.
    have hneg : Periodic.MemLpPer (d := d) q
        (fun x : (Fin d → ℝ) => (-1 : ℝ) * (1 : ℝ)) := by
      have := hOneq.const_smul (𝕜 := ℝ) (-1 : ℝ)
      simpa [Pi.smul_apply, smul_eq_mul, Pi.neg_def] using this
    have hsum := hm_q.add hneg
    have heq : ((fam.m ε) + fun _ : (Fin d → ℝ) => (-1 : ℝ) * (1 : ℝ))
        = fluxCoeffA (fam.m ε) := by
      funext x; simp only [fluxCoeffA, Pi.add_apply]; ring
    rwa [heq] at hsum
  -- ===========================================================
  -- `hbF`: `fluxCoeffB DpHε m Du i = m·D_pH^ε_i ∈ L^{γ̄'}`.
  -- ===========================================================
  set DpHε := DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε with hDpHε_def
  -- The flux vector field `F = m • DpHε`.
  set Fvec : (Fin d → ℝ) → (Fin d → ℝ) :=
    fun x => fam.m ε x • DpHε x (fun j => fam.Du ε j x) (fam.m ε x) with hFvec_def
  -- AE strong measurability of `F`.
  have hm_aem : AEMeasurable (fam.m ε)
      (volume.restrict (UnitCube d)) :=
    hmLp_β.aestronglyMeasurable.aemeasurable
  have hDu_aem : AEMeasurable
      (fun x : (Fin d → ℝ) => fun i : Fin d => fam.Du ε i x)
      (volume.restrict (UnitCube d)) :=
    aemeasurable_pi_iff.mpr fun i => (hDuLp_γ i).aestronglyMeasurable.aemeasurable
  have hmap_aem : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        (x, (fun j : Fin d => fam.Du ε j x), fam.m ε x))
      (volume.restrict (UnitCube d)) :=
    aemeasurable_id.prodMk (hDu_aem.prodMk hm_aem)
  have hDpHcomp_aem : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        DpHε x (fun j => fam.Du ε j x) (fam.m ε x))
      (volume.restrict (UnitCube d)) := by
    have hDpH_meas :=
      StationaryMFG.InfimalConvolution.measurable_DpHepsilonFam_of_selector
        (H := H) (DpH := DpH) hweak qε sel hMeas ε
    exact hDpH_meas.comp_aemeasurable hmap_aem
  have hFvec_aesm : AEStronglyMeasurable Fvec
      (volume.restrict (UnitCube d)) := by
    rw [hFvec_def]
    refine AEMeasurable.aestronglyMeasurable ?_
    refine aemeasurable_pi_iff.mpr (fun i => ?_)
    simp only [Pi.smul_apply, smul_eq_mul]
    exact hm_aem.mul (hDpHcomp_aem.eval i)
  -- The AE vector dominator bound `‖F x‖ ≤ Cε·(m·‖Du‖^{α-1} + m^{1+β-β/α} + m)`.
  have hF_le :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖Fvec x‖ ≤ Cε * (fam.m ε x * ‖fun j => fam.Du ε j x‖ ^ (hweak.α - 1)
                  + fam.m ε x ^ (1 + hweak.β - hweak.β / hweak.α) + fam.m ε x) := by
    filter_upwards [hAE.DpH_upper_ae ε hε hε1ε, hmNonneg] with x hxDpH hxNonneg
    set m0 : ℝ := fam.m ε x with hm0_def
    have hm0_nn : 0 ≤ m0 := hxNonneg
    set Dux : Fin d → ℝ := fun j => fam.Du ε j x with hDux_def
    set DpHv : Fin d → ℝ := DpHε x Dux m0 with hDpHv_def
    -- `F x = m0 • DpHv`.
    have hFx : Fvec x = m0 • DpHv := by
      rw [hFvec_def, hDpHv_def, hDux_def, hm0_def]
    rw [hFx, norm_smul, Real.norm_eq_abs, abs_of_nonneg hm0_nn]
    have hRHS_nn : 0 ≤ Cε * (m0 * ‖fun j => fam.Du ε j x‖ ^ (hweak.α - 1)
              + m0 ^ (1 + hweak.β - hweak.β / hweak.α) + m0) := by
      have hpow_nn : 0 ≤ ‖fun j => fam.Du ε j x‖ ^ (hweak.α - 1) :=
        Real.rpow_nonneg (norm_nonneg _) _
      have hpow2_nn : 0 ≤ m0 ^ (1 + hweak.β - hweak.β / hweak.α) :=
        Real.rpow_nonneg hm0_nn _
      apply mul_nonneg hCε_pos.le
      exact add_nonneg (add_nonneg (mul_nonneg hm0_nn hpow_nn) hpow2_nn) hm0_nn
    rcases eq_or_lt_of_le hm0_nn with hm0eq | hm0pos
    · -- `m0 = 0`: LHS is `0`.
      have hLHS0 : m0 * ‖DpHv‖ = 0 := by rw [← hm0eq, zero_mul]
      rw [hLHS0]; exact hRHS_nn
    · -- `m0 > 0`: use `DpH_upper_ae`.
      have hDpHbd : ‖DpHv‖ ≤ Cε * (‖Dux‖ ^ (hweak.α - 1)
          + m0 ^ (hweak.β - hweak.β / hweak.α) + 1) := by
        rw [hDpHv_def, hCε_def, hDpHε_def]; exact hxDpH Dux m0 hm0pos
      -- Multiply by `m0`, then expand `m0·m0^{β-β/α} = m0^{1+β-β/α}`.
      have hm0_ne : m0 ≠ 0 := hm0pos.ne'
      have hmpow_id : m0 * m0 ^ (hweak.β - hweak.β / hweak.α)
          = m0 ^ (1 + hweak.β - hweak.β / hweak.α) := by
        rw [show (1 + hweak.β - hweak.β / hweak.α)
              = (hweak.β - hweak.β / hweak.α) + 1 by ring,
          Real.rpow_add_one hm0_ne]
        ring
      calc m0 * ‖DpHv‖
          ≤ m0 * (Cε * (‖Dux‖ ^ (hweak.α - 1)
              + m0 ^ (hweak.β - hweak.β / hweak.α) + 1)) :=
            mul_le_mul_of_nonneg_left hDpHbd hm0_nn
        _ = Cε * (m0 * ‖Dux‖ ^ (hweak.α - 1)
              + m0 * m0 ^ (hweak.β - hweak.β / hweak.α) + m0) := by ring
        _ = Cε * (m0 * ‖Dux‖ ^ (hweak.α - 1)
              + m0 ^ (1 + hweak.β - hweak.β / hweak.α) + m0) := by rw [hmpow_id]
  -- The dominator membership at `q = ofReal γ̄'` from the keystone.
  have hG_mem : Periodic.MemLpPer q
      (fun x : (Fin d → ℝ) =>
        Cε * (fam.m ε x * ‖fun j => fam.Du ε j x‖ ^ (hweak.α - 1)
                  + fam.m ε x ^ (1 + hweak.β - hweak.β / hweak.α) + fam.m ε x)) := by
    have hkey := StationaryMFG.Hamiltonian.flux_dominator_memLpPer_explicit
      (d := d) (α := hweak.α) (β := hweak.β) (C := Cε) hα1 hβ0
      (μ := fam.m ε) (Dυ := fun i => fam.Du ε i)
      hmLp_β (fun i => by
        have h := hDuLp_γ i
        -- `gammaBar α β = α(β+1)/β = γBarReal`.
        have hid : hweak.α * (hweak.β + 1) / hweak.β = γBarReal := by
          rw [← hγbar_id]; rfl
        rw [hid]; exact h)
    -- Reconcile the keystone's exponent with `q = ofReal γ̄'`.
    have hexp : ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β /
        (hweak.α * (hweak.β + 1) / hweak.β - 1)) = q := by
      rw [hq_def, hγ'_def]
      congr 1
    rw [hexp] at hkey
    exact hkey
  -- The vector membership `F ∈ L^{γ̄'}`.
  have hFvec_mem : Periodic.MemLpPer q Fvec := by
    -- `mDpH_mem_Lp_gammaBar'` with `F = Fvec`, `m`, `Du = fun x => fun j => Du j x`.
    have := StationaryMFG.Hamiltonian.mDpH_mem_Lp_gammaBar' (d := d) (q := q)
      (m := fam.m ε) (Du := fun x => fun j => fam.Du ε j x) (F := Fvec)
      (C := Cε) (α := hweak.α) (β := hweak.β)
      hFvec_aesm hF_le hG_mem
    exact this
  -- Coordinate projection: `|fluxCoeffB i x| ≤ ‖F x‖`.
  have hbF : ∀ i, Periodic.MemLpPer q
      (fluxCoeffB DpHε (fam.m ε) (fam.Du ε) i) := by
    intro i
    have hcoord_meas : AEStronglyMeasurable
        (fluxCoeffB DpHε (fam.m ε) (fam.Du ε) i)
        (volume.restrict (UnitCube d)) := by
      unfold fluxCoeffB
      exact (hm_aem.mul (hDpHcomp_aem.eval i)).aestronglyMeasurable
    have hbound : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖fluxCoeffB DpHε (fam.m ε) (fam.Du ε) i x‖ ≤ (1 : ℝ) * ‖Fvec x‖ := by
      refine Filter.Eventually.of_forall (fun x => ?_)
      rw [one_mul]
      -- `fluxCoeffB i x = (F x) i`, and `|(F x) i| ≤ ‖F x‖`.
      have heq : fluxCoeffB DpHε (fam.m ε) (fam.Du ε) i x = Fvec x i := by
        simp [fluxCoeffB, hFvec_def, Pi.smul_apply, smul_eq_mul]
      rw [heq, Real.norm_eq_abs, ← Real.norm_eq_abs]
      exact norm_le_pi_norm (Fvec x) i
    exact MemLp.toMemLpPer (MemLp.of_le_mul hFvec_mem.toMemLp hcoord_meas hbound)
  -- ===========================================================
  -- `haG`: `gatCoeffA γ̄ u = |u|^{γ̄−2}·u ∈ L^{γ̄'}`.
  -- ===========================================================
  -- `‖u‖^{γ̄−1} ∈ L^{γ̄'}` via `rpow_closure` (`γ̄'(γ̄−1) = γ̄`).
  have hmulγ' : q * ENNReal.ofReal (γBarReal - 1) = ENNReal.ofReal γBarReal := by
    rw [hq_def, hγ'_def, ← ENNReal.ofReal_mul ?_]
    · congr 1
      unfold StationaryMFG.Hamiltonian.gammaBar'
      rw [hγbar_id]
      field_simp
    · unfold StationaryMFG.Hamiltonian.gammaBar'
      rw [hγbar_id]
      positivity
  have hu_pow : Periodic.MemLpPer q
      (fun x => ‖fam.u ε x‖ ^ (γBarReal - 1)) :=
    Periodic.MemLpPer.rpow_closure (d := d) (s := q) (r := γBarReal - 1)
      hγm1_pos (f := fam.u ε) (by rw [hmulγ']; exact hu_γ)
  have haG : Periodic.MemLpPer q (gatCoeffA γBarReal (fam.u ε)) := by
    have hmeas : AEStronglyMeasurable (gatCoeffA γBarReal (fam.u ε))
        (volume.restrict (UnitCube d)) := by
      unfold gatCoeffA absPowMinusTwo
      have hu_aem : AEMeasurable (fam.u ε) (volume.restrict (UnitCube d)) :=
        hu_γ.aestronglyMeasurable.aemeasurable
      exact (((hu_aem.abs.pow_const _)).mul hu_aem).aestronglyMeasurable
    have hbound : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖gatCoeffA γBarReal (fam.u ε) x‖ ≤ (1 : ℝ) * ‖‖fam.u ε x‖ ^ (γBarReal - 1)‖ := by
      refine Filter.Eventually.of_forall (fun x => ?_)
      rw [one_mul, Real.norm_eq_abs, gatCoeffA]
      have hkey := abs_absPowMinusTwo_mul_self (γBar := γBarReal) hγ (fam.u ε x)
      rw [hkey]
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact MemLp.toMemLpPer (MemLp.of_le_mul hu_pow.toMemLp hmeas hbound)
  -- ===========================================================
  -- `hbG`: `gatCoeffB γ̄ Du i = |Du|^{γ̄−2}·Du_i ∈ L^{γ̄'}`.
  -- ===========================================================
  -- The summed-abs base `D(x) = ∑ i, |Du_i x| ∈ L^{γ̄}`.
  have hSumAbsLp : Periodic.MemLpPer (ENNReal.ofReal γBarReal)
      (fun x : (Fin d → ℝ) => ∑ i : Fin d, |fam.Du ε i x|) := by
    set p : ℝ≥0∞ := ENNReal.ofReal γBarReal with hp_def
    have habs_memLp : ∀ i, Periodic.MemLpPer (d := d) p (fun x => |fam.Du ε i x|) := by
      intro i
      have h2 := (hDuLp_γ i).toMemLp.norm
      have heq : (fun x => ‖fam.Du ε i x‖) = fun x => |fam.Du ε i x| := by
        funext x; exact Real.norm_eq_abs _
      rw [heq] at h2
      exact MemLp.toMemLpPer h2
    exact MemLp.toMemLpPer (MeasureTheory.memLp_finset_sum (Finset.univ : Finset (Fin d))
      (fun i _ => (habs_memLp i).toMemLp))
  -- `‖D·‖^{γ̄−1} = D^{γ̄−1} ∈ L^{γ̄'}` via `rpow_closure`.
  have hDu_pow : Periodic.MemLpPer q
      (fun x => (∑ i : Fin d, |fam.Du ε i x|) ^ (γBarReal - 1)) := by
    have hrpow := Periodic.MemLpPer.rpow_closure (d := d) (s := q) (r := γBarReal - 1)
      hγm1_pos (f := fun x : (Fin d → ℝ) => ∑ i : Fin d, |fam.Du ε i x|)
      (by rw [hmulγ']; exact hSumAbsLp)
    have heq : (fun x => ‖∑ i : Fin d, |fam.Du ε i x|‖ ^ (γBarReal - 1))
        = (fun x => (∑ i : Fin d, |fam.Du ε i x|) ^ (γBarReal - 1)) := by
      funext x
      rw [Real.norm_eq_abs,
        abs_of_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg _))]
    rwa [heq] at hrpow
  have hbG : ∀ i, Periodic.MemLpPer q (gatCoeffB γBarReal (fam.Du ε) i) := by
    intro i
    have hmeas : AEStronglyMeasurable (gatCoeffB γBarReal (fam.Du ε) i)
        (volume.restrict (UnitCube d)) := by
      unfold gatCoeffB vecAbsPowMinusTwo
      have hdot_aem : AEMeasurable
          (fun x : (Fin d → ℝ) => (fun j => fam.Du ε j x) ⬝ (fun j => fam.Du ε j x))
          (volume.restrict (UnitCube d)) := by
        unfold dotProduct
        exact Finset.aemeasurable_fun_sum (s := Finset.univ)
          (fun j _ => (hDu_aem.eval j).mul (hDu_aem.eval j))
      exact ((hdot_aem.pow_const _).mul (hDu_aem.eval i)).aestronglyMeasurable
    have hbound : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖gatCoeffB γBarReal (fam.Du ε) i x‖
          ≤ (1 : ℝ) * ‖(∑ j : Fin d, |fam.Du ε j x|) ^ (γBarReal - 1)‖ := by
      refine Filter.Eventually.of_forall (fun x => ?_)
      rw [one_mul, Real.norm_eq_abs, gatCoeffB]
      -- `|gatCoeffB i x| ≤ (v⬝v)^((γ̄-1)/2) ≤ (∑|Du_j|)^{γ̄-1}`.
      have hkey := abs_vecAbsPowMinusTwo_mul_coord_le (γBar := γBarReal) hγ
        (fun j => fam.Du ε j x) i
      set v : Fin d → ℝ := fun j => fam.Du ε j x with hv_def
      set S : ℝ := ∑ j : Fin d, |v j| with hS_def
      have hS_nn : 0 ≤ S := Finset.sum_nonneg (fun j _ => abs_nonneg _)
      have hvv_nn : 0 ≤ v ⬝ v :=
        Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)
      -- `v⬝v ≤ S^2` (the `c2`-style bound).
      have hvv_le : v ⬝ v ≤ S ^ 2 := by
        have hself : v ⬝ v = ∑ j, |v j| ^ 2 := by
          simp only [dotProduct, sq_abs]
          exact Finset.sum_congr rfl (fun j _ => by ring)
        rw [hself, hS_def, sq, Finset.sum_mul_sum]
        refine Finset.sum_le_sum (fun j _ => ?_)
        rw [show |v j| ^ 2 = |v j| * |v j| from sq _,
          show |v j| * |v j| = ∑ k ∈ ({j} : Finset (Fin d)), |v j| * |v k| by simp]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          simp only [Finset.mem_singleton] at hk
          subst hk; exact Finset.mem_univ _
        · intro k _ _; exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
      -- `(v⬝v)^((γ̄-1)/2) ≤ (S^2)^((γ̄-1)/2) = S^{γ̄-1}`.
      have hpow : (v ⬝ v) ^ ((γBarReal - 1) / 2) ≤ S ^ (γBarReal - 1) := by
        have h1 : (v ⬝ v) ^ ((γBarReal - 1) / 2) ≤ (S ^ 2) ^ ((γBarReal - 1) / 2) :=
          Real.rpow_le_rpow hvv_nn hvv_le (by linarith)
        have h2 : (S ^ 2) ^ ((γBarReal - 1) / 2) = S ^ (γBarReal - 1) := by
          rw [show (S ^ 2 : ℝ) = S ^ (2 : ℝ) from (Real.rpow_two _).symm,
            ← Real.rpow_mul hS_nn]
          congr 1; ring
        rw [h2] at h1; exact h1
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hS_nn _)]
      exact le_trans hkey hpow
    exact MemLp.toMemLpPer (MemLp.of_le_mul hDu_pow.toMemLp hmeas hbound)
  exact ⟨haF, hbF, haG, hbG⟩

/-- **D6f2 `hRHSbelow_int` (family, genuinely derived).** The lower-bound RHS
integrand
`m·(-Hδ + DpHε·Du) + V·m + weakEpsTermsEucl γ̄ ε u Du`
is `L¹(cube)` for all `0 < ε ≤ 1`, derived from `fam` + the accepted §1b
carriers — **NO `hRHSbelowRaw` binder**.  The three summands are handled
by Hölder-exponent-balance (paper `eq:gamma`):

* `m·(-Hδ)`: `Hδ(·) ∈ L^{β̄'}` (`T3.hComposite_memLpPer_of_family`) paired with
  `m ∈ L^{β̄}` (`fam.hmLp`) by the conjugate pair `(β̄', β̄)` (`hpqβ`);
* `m·(DpHε·Du) = ∑ᵢ (m·DpHε_i)·Du_i = ∑ᵢ fluxCoeffB_i·Du_i`: each
  `fluxCoeffB_i ∈ L^{γ̄'}` (`T3.fluxGatCoeffMemberships_of_family`) paired with
  `Du_i ∈ L^{γ̄}` (`fam.hDuLp`) by the conjugate pair `(γ̄', γ̄)`
  (`paper_holderConjugate_gammaBar`);
* `V·m`: `V ∈ L^{β̄'}` (`hV`) paired with `m ∈ L^{β̄}` by `(β̄', β̄)`;
* `weakEpsTermsEucl = ε·((Du⬝Du)^{γ̄/2} + |u|^γ̄)`: directly from the `γ̄`-`Lp`
  data (`fam.hDuLp` via `integrable_euclideanDot_rpow_half_of_coord_memLp`,
  `fam.huSob` via `integrable_norm_rpow`).

This supersedes the §1b RAW pass-through `t3_hRHSbelow_int_of_family` for the
canonical `epsTerms = weakEpsTermsEucl γ̄`.  `fam` IS a binder; the remaining
binders are `fam` + the accepted §1b carriers and exponent reconciliations. -/
theorem T3.hRHSbelow_int_of_family_genuine
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d) {βBarReal γBarReal βBar' : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    (fam : T3RegularizedStrongFamily V hweak qε βBarReal γBarReal)
    (hMeas : StationaryMFG.Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hdiff : HypothesisHpDifferentiable (d := d) H DpH)
    (sel : StationaryMFG.InfimalConvolution.InfConvSelectorFamily
      (H := H) (DpH := DpH) hweak qε)
    (hAE : HdeltaAEPowerEpsData (H := H) (DpH := DpH) hweak qε)
    (hUB : HdeltaUniformBounds (H := H) (DpH := DpH) hweak qε)
    (hC0_le : ∀ ε : ℝ, ε > 0 →
      hUB.C0 ≤ CdeltaEps (H := H) (DpH := DpH) hweak ε)
    (hpqβ : βBarReal.HolderConjugate βBar')
    (hβBar_eq : βBarReal = hweak.β + 1)
    (hγBar_eq : γBarReal = StationaryMFG.Hamiltonian.gammaBar hweak.α hweak.β)
    (hV : Periodic.MemLpPer (ENNReal.ofReal βBar') V)
    (hγ : 1 < γBarReal) :
    ∀ ε, 0 < ε → ε ≤ 1 → Integrable
      (fun x =>
        fam.m ε x * (-HdeltaK0 hweak ε x (fun i => fam.Du ε i x) (fam.m ε x)
                  + (DpHepsilonFam hweak qε ε x (fun i => fam.Du ε i x)
                        (fam.m ε x)) ⬝ (fun i => fam.Du ε i x))
          + V x * fam.m ε x
          + weakEpsTermsEucl γBarReal ε (fam.u ε) (fam.Du ε) x)
      (volume.restrict (UnitCube d)) := by
  classical
  intro ε hε hε1ε
  have hα1 : (1 : ℝ) < hweak.α := hweak.hα
  have hβ0 : (0 : ℝ) < hweak.β := hweak.hβ
  have hγr_pos : 0 < γBarReal := lt_trans zero_lt_one hγ
  -- `betaBar hweak.β = hweak.β + 1`, so the abstract exponent facts feed the
  -- `betaBar`-flavoured producers.
  have hβBar_eq' : βBarReal = StationaryMFG.Hamiltonian.betaBar hweak.β := by
    rw [hβBar_eq]; rfl
  -- The §1b density / gradient regularities at the paper exponents.
  have hmLp : Periodic.MemLpPer (ENNReal.ofReal βBarReal) (fam.m ε) :=
    fam.hmLp ε hε hε1ε
  have hDuLp : ∀ i, Periodic.MemLpPer (ENNReal.ofReal γBarReal) (fam.Du ε i) :=
    fun i => fam.hDuLp ε hε hε1ε i
  have huLp : Periodic.MemLpPer (ENNReal.ofReal γBarReal) (fam.u ε) :=
    (fam.huSob ε hε hε1ε).1
  -- ===========================================================
  -- Summand A : `m·(-Hδ)` integrable.
  -- ===========================================================
  -- `Hδ ∈ L^{β̄'}` via the D6e-3 composite producer.
  have hHcomp : Periodic.MemLpPer
      (ENNReal.ofReal (StationaryMFG.Hamiltonian.betaBar' hweak.β))
      (fun x => HdeltaK0 hweak ε x (fun i => fam.Du ε i x) (fam.m ε x)) :=
    T3.hComposite_memLpPer_of_family hweak qε V fam hMeas hmon
      hdiff sel hAE hUB hC0_le hβBar_eq' hγBar_eq ε hε hε1ε
  -- The abstract conjugate `βBar'` IS the concrete `betaBar' hweak.β`.
  have hβBar'_eq : βBar' = StationaryMFG.Hamiltonian.betaBar' hweak.β :=
    betaBar'_eq_of_holderConjugate hpqβ hβBar_eq
  -- Pair `(β̄', β̄)`: `(betaBar' β).HolderConjugate (β+1)`.
  have hpqβ' : (StationaryMFG.Hamiltonian.betaBar' hweak.β).HolderConjugate
      βBarReal := by
    rw [← hβBar'_eq]; exact hpqβ.symm
  -- `Hδ·m ∈ L¹`.
  have hHm_int : Integrable
      (fun x => HdeltaK0 hweak ε x (fun i => fam.Du ε i x) (fam.m ε x)
                  * fam.m ε x)
      (volume.restrict (UnitCube d)) :=
    Periodic.MemLpPer.integrable_mul hpqβ' hHcomp hmLp
  -- `m·(-Hδ) = -(Hδ·m)`.
  have hmH_int : Integrable
      (fun x => fam.m ε x * (-HdeltaK0 hweak ε x (fun i => fam.Du ε i x)
                  (fam.m ε x)))
      (volume.restrict (UnitCube d)) := by
    refine (hHm_int.neg).congr ?_
    filter_upwards with x; simp only [Pi.neg_apply]; ring
  -- ===========================================================
  -- Summand B : `m·(DpHε·Du) = ∑ᵢ fluxCoeffB_i·Du_i` integrable.
  -- ===========================================================
  -- The four `L^{γ̄'}` coefficient memberships (we only need `hbF`).
  obtain ⟨_haF, hbF, _haG, _hbG⟩ :=
    T3.fluxGatCoeffMemberships_of_family hweak qε V fam hMeas sel hAE
      hβBar_eq' hγBar_eq hγ ε hε hε1ε
  -- `(γ̄).HolderConjugate (γ̄')`, hence `(γ̄').HolderConjugate (γ̄)`.
  have hpqγ : (StationaryMFG.Hamiltonian.gammaBar hweak.α hweak.β).HolderConjugate
      (StationaryMFG.Hamiltonian.gammaBar' hweak.α hweak.β) := by
    have h := SimplePowerExponentFacts.paper_holderConjugate_gammaBar hα1 hβ0
    -- `gammaBar = α(β+1)/β`, `gammaBar' = γ̄/(γ̄-1)`.
    simpa [StationaryMFG.Hamiltonian.gammaBar,
      StationaryMFG.Hamiltonian.gammaBar'] using h
  have hpqγ' : (StationaryMFG.Hamiltonian.gammaBar' hweak.α hweak.β).HolderConjugate
      γBarReal := by
    rw [hγBar_eq]; exact hpqγ.symm
  -- Each `fluxCoeffB_i·Du_i ∈ L¹`.
  have hbDu_int : ∀ i, Integrable
      (fun x =>
        fluxCoeffB (DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε)
          (fam.m ε) (fam.Du ε) i x * fam.Du ε i x)
      (volume.restrict (UnitCube d)) := by
    intro i
    have hDuLp_i : Periodic.MemLpPer (ENNReal.ofReal γBarReal) (fam.Du ε i) :=
      hDuLp i
    -- align the `Du` index shape `(fam.Du ε i)`.
    exact Periodic.MemLpPer.integrable_mul hpqγ' (hbF i) hDuLp_i
  -- Sum over `i`.
  have hbsum_int : Integrable
      (fun x => ∑ i : Fin d,
        fluxCoeffB (DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε)
          (fam.m ε) (fam.Du ε) i x * fam.Du ε i x)
      (volume.restrict (UnitCube d)) := by
    have := integrable_finset_sum (μ := volume.restrict (UnitCube d))
      (s := (Finset.univ : Finset (Fin d)))
      (f := fun i x =>
        fluxCoeffB (DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε)
          (fam.m ε) (fam.Du ε) i x * fam.Du ε i x)
      (fun i _ => hbDu_int i)
    simpa using this
  -- `m·(DpHε·Du) = ∑ᵢ fluxCoeffB_i·Du_i` pointwise.
  have hmDpH_int : Integrable
      (fun x => fam.m ε x *
        ((DpHepsilonFam hweak qε ε x (fun i => fam.Du ε i x) (fam.m ε x))
          ⬝ (fun i => fam.Du ε i x)))
      (volume.restrict (UnitCube d)) := by
    refine hbsum_int.congr ?_
    filter_upwards with x
    simp only [fluxCoeffB, dotProduct]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _; ring
  -- ===========================================================
  -- Summand C : `V·m` integrable.
  -- ===========================================================
  have hVLp : Periodic.MemLpPer
      (ENNReal.ofReal (StationaryMFG.Hamiltonian.betaBar' hweak.β)) V := by
    rw [← hβBar'_eq]; exact hV
  have hVm_int : Integrable (fun x => V x * fam.m ε x)
      (volume.restrict (UnitCube d)) :=
    Periodic.MemLpPer.integrable_mul hpqβ' hVLp hmLp
  -- ===========================================================
  -- Summand D : `weakEpsTermsEucl γ̄ ε u Du` integrable.
  -- ===========================================================
  -- `(Du⬝Du)^{γ̄/2} ∈ L¹` from the coordinate `γ̄`-`Lp` data.
  have hDot_int : Integrable
      (fun x => ((fun i => fam.Du ε i x) ⬝ (fun i => fam.Du ε i x))
                  ^ (γBarReal / 2))
      (volume.restrict (UnitCube d)) :=
    integrable_euclideanDot_rpow_half_of_coord_memLp (fam.Du ε) hDuLp hγ.le
  -- `|u|^γ̄ ∈ L¹` from `u ∈ L^{γ̄}`.
  have hAbsU_int : Integrable (fun x => |fam.u ε x| ^ γBarReal)
      (volume.restrict (UnitCube d)) := by
    have hp_ne_zero : ENNReal.ofReal γBarReal ≠ 0 :=
      (ENNReal.ofReal_pos.mpr hγr_pos).ne'
    have hp_ne_top : ENNReal.ofReal γBarReal ≠ ⊤ := ENNReal.ofReal_ne_top
    have hint_norm : Integrable
        (fun x => ‖fam.u ε x‖ ^ (ENNReal.ofReal γBarReal).toReal)
        (volume.restrict (UnitCube d)) :=
      huLp.toMemLp.integrable_norm_rpow hp_ne_zero hp_ne_top
    rw [ENNReal.toReal_ofReal hγr_pos.le] at hint_norm
    refine hint_norm.congr ?_
    filter_upwards with x; rw [Real.norm_eq_abs]
  -- Sum, scale by `ε`, and rewrite to `weakEpsTermsEucl`.
  have hEps_int : Integrable
      (fun x => weakEpsTermsEucl γBarReal ε (fam.u ε) (fam.Du ε) x)
      (volume.restrict (UnitCube d)) := by
    have hsum := (hDot_int.add hAbsU_int).const_mul ε
    refine hsum.congr ?_
    filter_upwards with x
    simp only [weakEpsTermsEucl, Pi.add_apply]
  -- ===========================================================
  -- Assemble: `(A + B) + C + D`.
  -- ===========================================================
  have hAB : Integrable
      (fun x => fam.m ε x * (-HdeltaK0 hweak ε x (fun i => fam.Du ε i x)
                  (fam.m ε x)
                + (DpHepsilonFam hweak qε ε x (fun i => fam.Du ε i x)
                      (fam.m ε x)) ⬝ (fun i => fam.Du ε i x)))
      (volume.restrict (UnitCube d)) := by
    refine (hmH_int.add hmDpH_int).congr ?_
    filter_upwards with x; simp only [Pi.add_apply]; ring
  exact (hAB.add hVm_int).add hEps_int

/-- **D6c3d: the fam-based, `hPow`-free wrapper of the integrated §1b identity.**

Assembles `T3.hIdentityRaw_of_T3RegularizedStrongFamily` with ALL of its
per-half carrier classes discharged internally from `fam` plus the
paper-accepted carriers:

* the four conjugate-exponent coefficient memberships from D6c3b
  (`T3.fluxGatCoeffMemberships_of_family`), reconciled at
  `q := ofReal γ̄'` via `hγBar'_eq`;
* the HJB-half residual `hResM` from D6c1
  (`T3.hResM_of_T3RegularizedStrongFamily`);
* the signed density-segment `hCont` from D6c1b
  (`T3.hContSigned_of_T3RegularizedStrongFamily`);
* the transport DCT dominator bundle from D6i-B2
  (`T3.transportSegmentDominator_of_T3RegularizedStrongFamily`) on top of the
  D6i-B endpoint-`Lp` bundle
  (`T3.transportSegmentEndpointLp_of_T3RegularizedStrongFamily`);
* the K0 standing-regularity `hRegK0` from `regularityHK0_Hdelta_of_selector`.

Periodicity flows through the `AEPeriodicRep`/`MemLpPer` layer inside the
consumer (post-D6c3c), so NO literal `IsPeriodic` carrier appears. The
HolderTriple `(ofReal γ̄, ofReal γ̄', 1)` instance is built from
`hpqγ.symm.ennrealOfReal`.

`fam` IS a binder; the remaining binders are exactly the paper-accepted
carriers (`hMeas`/`hmon`/`hdiff`/`sel`/`hAE`/`hUB`/`hC0_le`/`hε1`)
and the exponent/Hölder reconciliations (`hβBar`/`hγBar`/`hγ`/`hpqβ`/`hpqγ`)
plus `hV`. NO `hPow`, NO loose `m`/`u`/`Du`, NO `*Pack`/`*Inputs`/`*Oracle`,
NO literal-`IsPeriodic` public binder. This is the shape the D6h assembly
consumes. -/
theorem T3.hIdentityRaw_of_T3RegularizedStrongFamily_fam
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d) {βBarReal γBarReal βBar' γBar' : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    (fam : T3RegularizedStrongFamily V hweak qε βBarReal γBarReal)
    (hMeas : StationaryMFG.Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hdiff : HypothesisHpDifferentiable (d := d) H DpH)
    (sel : StationaryMFG.InfimalConvolution.InfConvSelectorFamily
      (H := H) (DpH := DpH) hweak qε)
    (hAE : HdeltaAEPowerEpsData (H := H) (DpH := DpH) hweak qε)
    (hUB : HdeltaUniformBounds (H := H) (DpH := DpH) hweak qε)
    (hC0_le : ∀ ε : ℝ, ε > 0 →
      hUB.C0 ≤ CdeltaEps (H := H) (DpH := DpH) hweak ε)
    (hβBar : βBarReal = StationaryMFG.Hamiltonian.betaBar hweak.β)
    (hγBar : γBarReal = StationaryMFG.Hamiltonian.gammaBar hweak.α hweak.β)
    (hγ : 1 < γBarReal)
    (hpqβ : βBarReal.HolderConjugate βBar')
    (hpqγ : γBar'.HolderConjugate γBarReal)
    (hV : Periodic.MemLpPer (ENNReal.ofReal βBar') V) :
    ∀ ε, 0 < ε → ε ≤ 1 →
      ∫ x in UnitCube d, fam.u ε x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          (fam.m ε x * (-HdeltaK0 hweak ε x (fun i => fam.Du ε i x) (fam.m ε x)
                    + (DpHepsilonFam hweak qε ε x (fun i => fam.Du ε i x)
                          (fam.m ε x)) ⬝ (fun i => fam.Du ε i x))
            + V x * fam.m ε x
            + weakEpsTermsEucl γBarReal ε (fam.u ε) (fam.Du ε) x)
          ∂(volume : Measure (Fin d → ℝ)) := by
  classical
  have hγr_pos : 0 < γBarReal := lt_trans zero_lt_one hγ
  have hα1 : (1 : ℝ) < hweak.α := hweak.hα
  have hβ0 : (0 : ℝ) < hweak.β := hweak.hβ
  -- The reconciled conjugate exponent `γ̄' = gammaBar' α β`.
  have hγBar'_eq : γBar' = StationaryMFG.Hamiltonian.gammaBar' hweak.α hweak.β := by
    have hconj : γBar' = γBarReal / (γBarReal - 1) := hpqγ.symm.conjugate_eq
    rw [hconj, hγBar]
    unfold StationaryMFG.Hamiltonian.gammaBar'
    rfl
  -- The HolderTriple instance `(ofReal γ̄, ofReal γ̄', 1)`.
  haveI hHolder : ENNReal.HolderTriple (ENNReal.ofReal γBarReal)
      (ENNReal.ofReal γBar') 1 := hpqγ.symm.ennrealOfReal
  -- The K0 standing-regularity carrier (per `ε`).
  have hRegK0fam : ∀ ε, 0 < ε → ε ≤ 1 →
      StationaryMFG.Theorems.SimplePower.RegularityHK0 (d := d)
        (HdeltaK0 hweak ε) (DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε) :=
    fun ε hε hε1ε => regularityHK0_Hdelta_of_selector hweak hmon hdiff qε sel
      hMeas hAE hε hε1ε
  -- The HJB-half residual carrier (per `ε`).
  have hResMfam := T3.hResM_of_T3RegularizedStrongFamily hweak qε V fam
    hMeas hmon hdiff sel hAE hUB hC0_le hpqβ hV hβBar hγBar
  -- The signed density-segment `hCont` carrier (per `ε`).
  have hContfam := T3.hContSigned_of_T3RegularizedStrongFamily hweak qε V fam
    hMeas hmon hdiff sel hAE hUB hRegK0fam hC0_le hβBar hγBar
    hγ hpqβ hV
  -- The four conjugate-exponent coefficient memberships (per `ε`).
  have hCoeff := T3.fluxGatCoeffMemberships_of_family hweak qε V fam
    hMeas sel hAE hβBar hγBar hγ
  intro ε hε hε1ε
  -- Endpoint-`Lp` bundle (B1) and transport DCT dominator bundle (B2).
  have hB1 := T3.transportSegmentEndpointLp_of_T3RegularizedStrongFamily
    hweak qε V fam hγ ε hε hε1ε
  obtain ⟨g_unreg, g_gat, hg_unreg_int, hg_gat_int,
      hF_unreg_meas, hF_unreg_bound, hF_gat_meas, hF_gat_bound⟩ :=
    T3.transportSegmentDominator_of_T3RegularizedStrongFamily
      hweak qε V fam hMeas sel hAE hβBar hγBar hpqβ hpqγ hγ hV ε hε hε1ε hB1
  -- The four memberships at the reconciled `q = ofReal γ̄'`.
  obtain ⟨haF, hbF, haG, hbG⟩ := hCoeff ε hε hε1ε
  rw [← hγBar'_eq] at haF hbF haG hbG
  -- `u_ε ∈ L¹` (downgrade `MemLpPer (ofReal γ̄)` to exponent `1`).
  have huLp_γ : Periodic.MemLpPer (ENNReal.ofReal γBarReal) (fam.u ε) :=
    (fam.huSob ε hε hε1ε).1
  have h1_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal γBarReal := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
    exact ENNReal.ofReal_le_ofReal (le_of_lt hγ)
  have hu1 : Periodic.MemLpPer (d := d) 1 (fam.u ε) :=
    Periodic.MemLpPer.mono_exponent_finite h1_le ENNReal.ofReal_ne_top huLp_γ
  exact hIdentityRaw_of_T3RegularizedStrongFamily
    (bb := ENNReal.ofReal βBarReal) (gb := ENNReal.ofReal γBarReal)
    hweak qε V fam ε hε hε1ε hγ
    (p := ENNReal.ofReal γBarReal) (q := ENNReal.ofReal γBar')
    h1_le ENNReal.ofReal_ne_top rfl rfl
    (hResMfam ε hε hε1ε)
    (hContfam ε hε hε1ε)
    (hRegK0fam ε hε hε1ε)
    hu1 hB1.2.2
    g_unreg g_gat hg_unreg_int hg_gat_int
    hF_unreg_meas hF_unreg_bound hF_gat_meas hF_gat_bound
    haF hbF haG hbG
    huLp_γ (fun i => fam.hDuLp ε hε hε1ε i)

/-! ### G6a: T3-local Young-route a-priori below-bound (no L∞ on `V`)

Paper `thm:apriori-weak.power.growth`, eq. `eq:uepsibelow` (lines 1218–1224):
multiplying the transport equation by `u_ε` and subtracting the HJ identity, the
`∫ V·m` term is absorbed by **Young's inequality** at the conjugate pair
`(β̄, β̄') = (β+1, (β+1)/β)`, NOT by a pointwise `L^∞` bound on `V`.  Only the
finite constant `∫|V|^{β̄'}` (well-defined since `V ∈ L^{β̄'}`) enters.

This `_young_Vlp_raw` lemma is the pure-real-keyed, T3-local re-derivation of the
below-bound (`(1/C')·∫ m^{β̄} − C' ≤ ∫ u`) that the L∞-using shared engine
`apriori_uepsi_below_closed_nonneg_raw` (SimplePower/Apriori.lean) does NOT
provide L∞-free at the `_raw` keying T3 needs.  The shared bundle-keyed sibling
`apriori_uepsi_below_closed_int` exists but is keyed on
`CongestionAprioriPowerData` and is consumed upward through the forbidden T3
riders `Hext_finite_at_zero`/`HypothesisHat0`/`H_zero_eq_Hext`; here we clone its
analytic content (which uses only `β, C0, hβ, hC0, h_lagr` + the public Hölder
helper `holder_Vm_betaBar`) at the pure-real keying, targeting the public raw
constant `aprioriUepsiBelowConst_intRaw β C0 Vint_bound Vβp_bound`.

-- Adapted from `SimplePower.apriori_uepsi_below_closed_int` (bundle-keyed),
-- re-derived pure-real for the regularized pair `(HdeltaK0 hHyp ε, DpHε)`.
-/

/-- Local copy of the (private) Lagrangian×m lower bound
`SimplePower.mul_lagrangian_lower_bound_ae_nonneg` (`mx ≥ 0` form). -/
private theorem t3_mul_lagrangian_lower_bound_ae_nonneg
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {β C : ℝ} (hβ : 0 < β) (_hC : 0 < C)
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
  · have hL := hx p mx hmx_pos
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
  · subst hmx_eq
    have hβp1_pos : 0 < β + 1 := by linarith
    have hβp1_ne : (β + 1 : ℝ) ≠ 0 := ne_of_gt hβp1_pos
    have h0pow : (0 : ℝ) ^ (β + 1) = 0 := Real.zero_rpow hβp1_ne
    rw [h0pow]; simp

/-- Local copy of the (private) scaled Young absorption
`SimplePower.young_absorb_lin_into_betaPlusOne`:
`K·mx ≤ mx^{β+1}/(β+1) + K^{(β+1)/β}·β/(β+1)` for `K, mx ≥ 0`. -/
private theorem t3_young_absorb_lin_into_betaPlusOne
    {β : ℝ} (hβ : 0 < β) (K : ℝ) (hK : 0 ≤ K) (mx : ℝ) (hmx : 0 ≤ mx) :
    K * mx ≤ mx ^ (β + 1) / (β + 1) + K ^ ((β + 1) / β) * (β / (β + 1)) := by
  have hβp1_pos : 0 < β + 1 := by linarith
  have hHC : Real.HolderConjugate (β + 1) ((β + 1) / β) := by
    rw [Real.holderConjugate_iff]
    refine ⟨by linarith, ?_⟩
    have hβne : β ≠ 0 := ne_of_gt hβ
    have hβp1ne : β + 1 ≠ 0 := ne_of_gt hβp1_pos
    field_simp; ring
  have hY : mx * K ≤ mx ^ (β + 1) / (β + 1) + K ^ ((β + 1) / β) / ((β + 1) / β) :=
    Real.young_inequality_of_nonneg hmx hK hHC
  have hdiv : K ^ ((β + 1) / β) / ((β + 1) / β)
      = K ^ ((β + 1) / β) * (β / (β + 1)) := by
    field_simp
  rw [hdiv] at hY
  rw [mul_comm K mx]
  exact hY

/-- **G6a — T3-local Young/Hölder below-bound (no `L^∞` on `V`).**

`(1/C')·∫ m^{β̄} − C' ≤ ∫ u` with `C' = aprioriUepsiBelowConst_intRaw β C0
Vint_bound Vβp_bound`, derived from the residue identity + Lagrangian +
`hmNonneg` + the **integral** V-data `hVβp : ∫|V|^{β̄'} ≤ Vβp_bound` (with
`hVβp_int`, `hVm_int`, measurability), via the paper's Young absorption of
`∫ V·m`.  NO pointwise `hVbnd : |V| ≤ Vbound` rider. -/
theorem apriori_uepsi_below_young_Vlp_raw
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (β C0 : ℝ) (hβ : 0 < β) (hC0 : 0 < C0)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (epsTerms : (Fin d → ℝ) → ℝ)
    (Vint_bound Vβp_bound : ℝ)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ β) / C0 - C0 ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hmNonneg : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hVβp :
      ∫ x in UnitCube d, |V x| ^ ((β + 1) / β)
          ∂(volume : Measure (Fin d → ℝ))
        ≤ Vβp_bound)
    (hVβp_nn : 0 ≤ Vβp_bound)
    (hVβp_int : Integrable (fun x => |V x| ^ ((β + 1) / β))
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
                (fun x => m x ^ (β + 1)) (volume.restrict (UnitCube d)))
    (hM_int : Integrable m (volume.restrict (UnitCube d)))
    (hRHS_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d))) :
    (1 / aprioriUepsiBelowConst_intRaw β C0 Vint_bound Vβp_bound)
        * (∫ x in UnitCube d, m x ^ (β + 1)
              ∂(volume : Measure (Fin d → ℝ)))
      - aprioriUepsiBelowConst_intRaw β C0 Vint_bound Vβp_bound
        ≤ ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) := by
  have hC_pos : 0 < C0 := hC0
  have hβ_pos : 0 < β := hβ
  have hβp1_pos : 0 < β + 1 := by linarith
  have h2C_pos : 0 < 2 * C0 := by linarith
  -- Young scale.
  set lam : ℝ := ((β + 1) / (2 * C0)) ^ ((1 : ℝ) / (β + 1)) with hlamdef
  have hbasis_pos : 0 < (β + 1) / (2 * C0) := div_pos hβp1_pos h2C_pos
  have hlam_pos : 0 < lam := Real.rpow_pos_of_pos hbasis_pos _
  have hlam_pow_p : lam ^ (β + 1) = (β + 1) / (2 * C0) := by
    rw [hlamdef, ← Real.rpow_mul hbasis_pos.le]
    have heq : (1 : ℝ) / (β + 1) * (β + 1) = 1 := by field_simp
    rw [heq, Real.rpow_one]
  -- Effective coefficient `K_eff = C0 + Vβp_bound^{β/(β+1)}`.
  set K_eff : ℝ := C0 + Vβp_bound ^ (β / (β + 1)) with hK_eff_def
  have hVβp_pow_nn : 0 ≤ Vβp_bound ^ (β / (β + 1)) := Real.rpow_nonneg hVβp_nn _
  have hK_eff_nn : 0 ≤ K_eff := by have : 0 ≤ C0 := hC_pos.le; linarith
  -- The Young residual.
  set K_Y_int : ℝ := (K_eff / lam) ^ ((β + 1) / β) * (β / (β + 1))
    with hK_Y_int_def
  have hK_Y_int_nn : 0 ≤ K_Y_int := by
    have h1 : 0 ≤ K_eff / lam := div_nonneg hK_eff_nn hlam_pos.le
    have h2 : 0 ≤ (K_eff / lam) ^ ((β + 1) / β) := Real.rpow_nonneg h1 _
    have h3 : 0 ≤ β / (β + 1) := div_nonneg hβ_pos.le hβp1_pos.le
    exact mul_nonneg h2 h3
  -- Step A: pointwise `m^{β+1}/C0 - C0·m ≤ m·(-H + DpH·Du)` from Lagrangian × m.
  have hlagr_mul := t3_mul_lagrangian_lower_bound_ae_nonneg (β := β) (C := C0)
    hβ_pos hC_pos h_lagr
  have hcube_finite : (volume.restrict (UnitCube (d := d))) Set.univ < ∞ := by
    rw [Measure.restrict_apply MeasurableSet.univ]; simp
  have : IsFiniteMeasure (volume.restrict (UnitCube (d := d))) := ⟨hcube_finite⟩
  have hLB_int_div :
      Integrable (fun x => m x ^ (β + 1) / C0)
        (volume.restrict (UnitCube d)) := by
    have h := hLB_int.const_mul (1 / C0)
    refine h.congr ?_
    refine Filter.Eventually.of_forall ?_
    intro x; ring
  have hM_int_const :
      Integrable (fun x => C0 * m x) (volume.restrict (UnitCube d)) :=
    hM_int.const_mul _
  have hLHS_A_int :
      Integrable (fun x => m x ^ (β + 1) / C0 - C0 * m x)
        (volume.restrict (UnitCube d)) := hLB_int_div.sub hM_int_const
  -- Step B: integrate the combined inequality.
  have hpointAfull :
      (fun x => m x ^ (β + 1) / C0 - C0 * m x + V x * m x)
        ≤ᵐ[volume.restrict (UnitCube d)]
        (fun x => m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x) := by
    filter_upwards [hlagr_mul, hmNonneg, hEpsNN] with x hLag hxm hxe
    have hL := hLag (fun i => Du i x) (m x) hxm
    linarith
  -- `V·m` integrable (from `|V|·m` integrable and `m ≥ 0`).
  have hVm_int_signed : Integrable (fun x => V x * m x)
      (volume.restrict (UnitCube d)) := by
    have hVm_meas : AEStronglyMeasurable (fun x => V x * m x)
        (volume.restrict (UnitCube d)) := hV_meas.mul hm_meas
    have hbound : (fun x => |V x * m x|)
        ≤ᵐ[volume.restrict (UnitCube d)] (fun x => |V x| * m x) := by
      filter_upwards [hmNonneg] with x hxm
      rw [abs_mul, abs_of_nonneg hxm]
    refine Integrable.mono' hVm_int hVm_meas ?_
    filter_upwards [hbound] with x hb using hb
  have hLHS_full_int :
      Integrable (fun x => m x ^ (β + 1) / C0 - C0 * m x + V x * m x)
        (volume.restrict (UnitCube d)) :=
    hLHS_A_int.add hVm_int_signed
  have hIntStep :
      ∫ x in UnitCube d,
          (m x ^ (β + 1) / C0 - C0 * m x + V x * m x)
        ∂(volume : Measure (Fin d → ℝ)) ≤
      ∫ x in UnitCube d,
          (m x * (-H x (fun i => Du i x) (m x)
                    + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
        ∂(volume : Measure (Fin d → ℝ)) :=
    setIntegral_mono_ae_restrict hLHS_full_int hRHS_int hpointAfull
  rw [← h_identity] at hIntStep
  -- LHS integral splits.
  set X : ℝ := ∫ x in UnitCube d, m x ^ (β + 1)
                ∂(volume : Measure (Fin d → ℝ)) with hX_def
  have hX_nn : 0 ≤ X := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [hmNonneg] with x hxm
    exact Real.rpow_nonneg hxm _
  set Im : ℝ := ∫ x in UnitCube d, m x ∂(volume : Measure (Fin d → ℝ)) with hIm_def
  have hIm_nn : 0 ≤ Im := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [hmNonneg] with x hxm using hxm
  set IVm : ℝ := ∫ x in UnitCube d, V x * m x
                  ∂(volume : Measure (Fin d → ℝ)) with hIVm_def
  set IabsVm : ℝ := ∫ x in UnitCube d, |V x| * m x
                      ∂(volume : Measure (Fin d → ℝ)) with hIabsVm_def
  have hLHS_split :
      ∫ x in UnitCube d,
          (m x ^ (β + 1) / C0 - C0 * m x + V x * m x)
        ∂(volume : Measure (Fin d → ℝ))
      = (1 / C0) * X - C0 * Im + IVm := by
    have h1 : ∫ x in UnitCube d, m x ^ (β + 1) / C0
                ∂(volume : Measure (Fin d → ℝ)) = (1 / C0) * X := by
      have hcongr : ∀ x, m x ^ (β + 1) / C0 = (1 / C0) * m x ^ (β + 1) := by
        intro x; ring
      simp only [hcongr]; rw [integral_const_mul]
    have h2 : ∫ x in UnitCube d, C0 * m x
                ∂(volume : Measure (Fin d → ℝ)) = C0 * Im := by
      rw [integral_const_mul]
    have hadd :
        ∫ x in UnitCube d,
            (m x ^ (β + 1) / C0 - C0 * m x + V x * m x)
          ∂(volume : Measure (Fin d → ℝ))
        = ∫ x in UnitCube d, (m x ^ (β + 1) / C0 - C0 * m x)
            ∂(volume : Measure (Fin d → ℝ))
          + ∫ x in UnitCube d, V x * m x
            ∂(volume : Measure (Fin d → ℝ)) :=
      integral_add hLHS_A_int hVm_int_signed
    have hsub :
        ∫ x in UnitCube d, (m x ^ (β + 1) / C0 - C0 * m x)
          ∂(volume : Measure (Fin d → ℝ))
        = ∫ x in UnitCube d, m x ^ (β + 1) / C0
              ∂(volume : Measure (Fin d → ℝ))
          - ∫ x in UnitCube d, C0 * m x
              ∂(volume : Measure (Fin d → ℝ)) :=
      integral_sub hLB_int_div hM_int_const
    rw [hadd, hsub, h1, h2]
  rw [hLHS_split] at hIntStep
  -- IVm ≥ -IabsVm.
  have hIVm_lb : -IabsVm ≤ IVm := by
    have hae : (fun x => -(V x * m x))
        ≤ᵐ[volume.restrict (UnitCube d)] (fun x => |V x| * m x) := by
      filter_upwards [hmNonneg] with x hxm
      have hVneg : -V x ≤ |V x| := neg_le_abs _
      have := mul_le_mul_of_nonneg_right hVneg hxm
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
      IabsVm ≤ Vβp_bound ^ (β / (β + 1)) * X ^ (1 / (β + 1)) := by
    have h_holder := holder_Vm_betaBar (d := d) (β := β) hβ_pos
        V m hmNonneg hV_meas hm_meas hVβp_int hLB_int
    have hVβp_int_nn :
        0 ≤ ∫ x in UnitCube d, |V x| ^ ((β + 1) / β)
              ∂(volume : Measure (Fin d → ℝ)) := by
      refine integral_nonneg_of_ae ?_
      refine Filter.Eventually.of_forall ?_
      intro x; exact Real.rpow_nonneg (abs_nonneg _) _
    have hMono : (∫ x in UnitCube d, |V x| ^ ((β + 1) / β)
                    ∂(volume : Measure (Fin d → ℝ))) ^ (β / (β + 1))
                  ≤ Vβp_bound ^ (β / (β + 1)) :=
      Real.rpow_le_rpow hVβp_int_nn hVβp ((div_pos hβ_pos hβp1_pos).le)
    have hX_pow_nn : 0 ≤ X ^ (1 / (β + 1)) := Real.rpow_nonneg hX_nn _
    have hMul := mul_le_mul_of_nonneg_right hMono hX_pow_nn
    exact h_holder.trans hMul
  -- Hölder for ∫ m: Im ≤ X^{1/(β+1)}.
  have hHolder_m : Im ≤ X ^ (1 / (β + 1)) := by
    have h1_meas : AEStronglyMeasurable (fun _ : Fin d → ℝ => (1 : ℝ))
        (volume.restrict (UnitCube d)) := aestronglyMeasurable_const
    have h1_int : Integrable
        (fun x : Fin d → ℝ => |(1 : ℝ)| ^ ((β + 1) / β))
        (volume.restrict (UnitCube d)) := by
      have hconst : Integrable (fun _ : Fin d → ℝ => (1 : ℝ))
                      (volume.restrict (UnitCube d)) := integrable_const _
      refine hconst.congr ?_
      filter_upwards with x using by rw [abs_one, Real.one_rpow]
    have h_holder := holder_Vm_betaBar (d := d) (β := β) hβ_pos
        (fun _ => (1 : ℝ)) m hmNonneg h1_meas hm_meas h1_int hLB_int
    have hLHS_eq :
        ∫ x in UnitCube d, |(1 : ℝ)| * m x
            ∂(volume : Measure (Fin d → ℝ)) = Im := by
      simp only [abs_one, one_mul, hIm_def]
    have hRHS_first :
        (∫ x in UnitCube d, |(1 : ℝ)| ^ ((β + 1) / β)
            ∂(volume : Measure (Fin d → ℝ))) ^ (β / (β + 1)) = 1 := by
      have hint_eq :
          ∫ x in UnitCube d, |(1 : ℝ)| ^ ((β + 1) / β)
              ∂(volume : Measure (Fin d → ℝ)) = 1 := by
        have hone : ∫ _x in UnitCube d, (1 : ℝ) ∂(volume : Measure (Fin d → ℝ))
              = 1 := by
          rw [MeasureTheory.integral_const]
          simp [MeasureTheory.Measure.real, MeasureTheory.Measure.restrict_apply,
            Set.univ_inter, volume_unitCube]
        calc ∫ x in UnitCube d, |(1 : ℝ)| ^ ((β + 1) / β)
                ∂(volume : Measure (Fin d → ℝ))
            = ∫ _x in UnitCube d, (1 : ℝ)
                ∂(volume : Measure (Fin d → ℝ)) := by
              refine integral_congr_ae ?_
              refine Filter.Eventually.of_forall ?_
              intro x; rw [abs_one, Real.one_rpow]
          _ = 1 := hone
      rw [hint_eq, Real.one_rpow]
    rw [hLHS_eq, hRHS_first, one_mul] at h_holder
    exact h_holder
  -- Combine: -C0·Im + IVm ≥ -K_eff·X^{1/(β+1)}.
  have hX_pow_nn : 0 ≤ X ^ (1 / (β + 1)) := Real.rpow_nonneg hX_nn _
  have hCm_ub : C0 * Im ≤ C0 * X ^ (1 / (β + 1)) :=
    mul_le_mul_of_nonneg_left hHolder_m hC_pos.le
  have hVm_lb_X : -(Vβp_bound ^ (β / (β + 1)) * X ^ (1 / (β + 1))) ≤ IVm := by
    have := neg_le_neg hHolder
    linarith [hIVm_lb]
  have hCombined :
      -(K_eff * X ^ (1 / (β + 1))) ≤ -C0 * Im + IVm := by
    have hsplit : K_eff * X ^ (1 / (β + 1))
                    = C0 * X ^ (1 / (β + 1))
                      + Vβp_bound ^ (β / (β + 1)) * X ^ (1 / (β + 1)) := by
      rw [hK_eff_def]; ring
    have h1 : -C0 * Im ≥ -C0 * X ^ (1 / (β + 1)) := by
      have := hCm_ub; linarith
    linarith [hVm_lb_X, hsplit]
  -- Scaled Young absorption.
  have hY_X : (X ^ (1 / (β + 1))) ^ (β + 1) = X := by
    rw [← Real.rpow_mul hX_nn]
    have heq : (1 : ℝ) / (β + 1) * (β + 1) = 1 := by field_simp
    rw [heq, Real.rpow_one]
  have hY_pt :
      K_eff * X ^ (1 / (β + 1)) ≤ (1 / (2 * C0)) * X + K_Y_int := by
    have hylam_nn : 0 ≤ lam * X ^ (1 / (β + 1)) :=
      mul_nonneg hlam_pos.le hX_pow_nn
    have hKlam_nn : 0 ≤ K_eff / lam := div_nonneg hK_eff_nn hlam_pos.le
    have hY := t3_young_absorb_lin_into_betaPlusOne hβ_pos
                  (K_eff / lam) hKlam_nn (lam * X ^ (1 / (β + 1))) hylam_nn
    have hLHS : (K_eff / lam) * (lam * X ^ (1 / (β + 1)))
        = K_eff * X ^ (1 / (β + 1)) := by
      have hlamne : lam ≠ 0 := ne_of_gt hlam_pos
      field_simp
    have hpow_mul :
        (lam * X ^ (1 / (β + 1))) ^ (β + 1)
          = lam ^ (β + 1) * (X ^ (1 / (β + 1))) ^ (β + 1) :=
      Real.mul_rpow hlam_pos.le hX_pow_nn
    have hR1 :
        (lam * X ^ (1 / (β + 1))) ^ (β + 1) / (β + 1)
          = (1 / (2 * C0)) * X := by
      rw [hpow_mul, hlam_pow_p, hY_X]
      have hβp1ne : (β + 1) ≠ 0 := ne_of_gt hβp1_pos
      have h2Cne : (2 * C0) ≠ 0 := ne_of_gt h2C_pos
      field_simp
    rw [hLHS, hR1] at hY
    have hRY : (K_eff / lam) ^ ((β + 1) / β) * (β / (β + 1)) = K_Y_int := by
      rw [hK_Y_int_def]
    rw [hRY] at hY
    exact hY
  -- Chain to `(1/(2C0))·X - K_Y_int ≤ ∫ u`.
  have hChain :
      (1 / (2 * C0)) * X - K_Y_int
        ≤ ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) := by
    have hinequalities : (1 / C0) * X - K_eff * X ^ (1 / (β + 1))
                ≤ ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) := by
      linarith [hIntStep, hCombined]
    have h_split : (1 / C0) * X = (1 / (2 * C0)) * X + (1 / (2 * C0)) * X := by
      have h2Cne : (2 * C0) ≠ 0 := ne_of_gt h2C_pos
      have hCne : C0 ≠ 0 := ne_of_gt hC_pos
      field_simp; ring
    linarith [hY_pt]
  -- Enlarge the residual to `C'`.
  set C' : ℝ := aprioriUepsiBelowConst_intRaw β C0 Vint_bound Vβp_bound with hC'_def
  have hC'_unfold : C' = max (2 * C0) (K_Y_int + 1) := by
    show aprioriUepsiBelowConst_intRaw β C0 Vint_bound Vβp_bound = _
    rfl
  have hC'_pos : 0 < C' :=
    aprioriUepsiBelowConst_intRaw_pos β C0 Vint_bound Vβp_bound hC0
  have hC'_ge_2C : 2 * C0 ≤ C' := by rw [hC'_unfold]; exact le_max_left _ _
  have hC'_ge_resid : K_Y_int ≤ C' := by
    rw [hC'_unfold]
    exact (by linarith : K_Y_int ≤ K_Y_int + 1).trans (le_max_right _ _)
  have h_coeff : (1 / C') ≤ (1 / (2 * C0)) :=
    one_div_le_one_div_of_le h2C_pos hC'_ge_2C
  have h_lhs_term : (1 / C') * X ≤ (1 / (2 * C0)) * X :=
    mul_le_mul_of_nonneg_right h_coeff hX_nn
  have h_rhs_const : -C' ≤ -K_Y_int := by linarith
  linarith [h_lhs_term, h_rhs_const, hChain]

end A2eWitnesses

section A2fUniform

/-! ### D4e-pre: exponent-parameterized helpers and coercive engine

These drop the `HypothesisPowerGrowth (HdeltaK0 hweak ε) DpHε` binder `hPow`
(and the loose `DpHε`) entirely.  A power-growth-bundle coercive engine
consumes `hPow` ONLY through its exponent fields `(hPow ε).α`/`.β`/`.hα`/`.hβ`
(collapsed to `hweak.α`/`hweak.β` via `hαU`/`hβU`), and `DpHε` only as the
Lagrangian-clause carrier (pinned to `DpHepsilonFam hweak qε ε` via `hDpHε_eq`).
The exponent-parameterized siblings below take the bare exponents instead, with
`DpHε := DpHepsilonFam hweak qε` fixed internally.  This is the producer the
D4e assembly (`T3RegularizedSideData.of_family`) calls so that neither `hPow`
nor `DpHε` appears as a binder of the assembly (D4e GATE #4). -/

/-- **D4e-pre `hDu_norm_int` (exponent-parameterized).** The
`‖(fun i => Du i ·)‖^{γ̄}`-integrability bridge at the FIXED exponent
`gammaBar α₀ β₀`, taking the bare exponents `(α₀, β₀)` with `1 < α₀`,
`0 < β₀` instead of a `HypothesisPowerGrowth` bundle.  Body is the
exponent-only `‖·‖^{γ̄}`-integrability reduction (the sup-norm is dominated
termwise by `∑ i, ‖Du i x‖^{γ̄}`, each summand integrable via
`MemLp.integrable_norm_rpow`). -/
theorem hDu_norm_int_of_exp
    {α₀ β₀ : ℝ} (hα₀ : 1 < α₀) (hβ₀ : 0 < β₀)
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hDuLp : ∀ i, MemLpPer (ENNReal.ofReal (gammaBar α₀ β₀)) (Du i)) :
    Integrable
      (fun x => ‖(fun i => Du i x)‖ ^ gammaBar α₀ β₀)
      (volume.restrict (UnitCube d)) := by
  classical
  set γBar : ℝ := gammaBar α₀ β₀ with hγBar_def
  have hγBar_pos : 0 < γBar :=
    gammaBar_pos α₀ β₀ (lt_trans zero_lt_one hα₀) hβ₀
  have hp_ne_zero : ENNReal.ofReal γBar ≠ 0 := by simp [hγBar_pos]
  have hp_top : ENNReal.ofReal γBar ≠ ⊤ := ENNReal.ofReal_ne_top
  have hp_toReal : (ENNReal.ofReal γBar).toReal = γBar :=
    ENNReal.toReal_ofReal hγBar_pos.le
  have h_each_int : ∀ i, Integrable
      (fun x => ‖Du i x‖ ^ γBar) (volume.restrict (UnitCube d)) := by
    intro i
    have hmemLp : MeasureTheory.MemLp (Du i) (ENNReal.ofReal γBar)
        (volume.restrict (UnitCube d)) := hDuLp i
    have h := MeasureTheory.MemLp.integrable_norm_rpow hmemLp hp_ne_zero hp_top
    rw [hp_toReal] at h; exact h
  have h_sum_int : Integrable
      (fun x => ∑ i, ‖Du i x‖ ^ γBar) (volume.restrict (UnitCube d)) :=
    MeasureTheory.integrable_finset_sum _ (fun i _ => h_each_int i)
  have hDu_aem : ∀ i, AEMeasurable (Du i) (volume.restrict (UnitCube d)) :=
    fun i => (hDuLp i).aestronglyMeasurable.aemeasurable
  have hPi_meas : MeasureTheory.AEStronglyMeasurable
      (fun x : Fin d → ℝ => (fun i => Du i x)) (volume.restrict (UnitCube d)) :=
    aestronglyMeasurable_iff_aemeasurable.mpr (AEMeasurable.of_eval hDu_aem)
  have h_rpow_meas : MeasureTheory.AEStronglyMeasurable
      (fun x => ‖(fun i => Du i x)‖ ^ γBar) (volume.restrict (UnitCube d)) :=
    (Real.continuous_rpow_const hγBar_pos.le).comp_aestronglyMeasurable hPi_meas.norm
  have h_pointwise : ∀ x : Fin d → ℝ,
      ‖fun i => Du i x‖ ^ γBar ≤ ∑ i, ‖Du i x‖ ^ γBar := by
    intro x
    have h_nn_sum : 0 ≤ ∑ i, ‖Du i x‖ ^ γBar :=
      Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg _) γBar)
    by_cases hd : d = 0
    · subst hd
      have hf_norm : ‖fun i : Fin 0 => Du i x‖ = 0 := by
        rw [Pi.norm_def]; simp [Finset.univ_eq_empty]
      rw [hf_norm, Real.zero_rpow hγBar_pos.ne']
      exact h_nn_sum
    · haveI : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero hd⟩⟩
      obtain ⟨j, _, hj_eq⟩ :=
        Finset.exists_mem_eq_sup (s := (Finset.univ : Finset (Fin d)))
          ⟨⟨0, Nat.pos_of_ne_zero hd⟩, Finset.mem_univ _⟩
          (fun i => ‖Du i x‖₊)
      have hf_norm_eq : ‖fun i => Du i x‖ = ‖Du j x‖ := by
        rw [Pi.norm_def, hj_eq]; rfl
      rw [hf_norm_eq]
      have h_each_nn : ∀ i, 0 ≤ ‖Du i x‖ ^ γBar :=
        fun i => Real.rpow_nonneg (norm_nonneg _) γBar
      calc ‖Du j x‖ ^ γBar
          = ∑ i ∈ ({j} : Finset (Fin d)), ‖Du i x‖ ^ γBar := by simp
        _ ≤ ∑ i, ‖Du i x‖ ^ γBar := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro i hi; exact Finset.mem_univ _
              · intro i _ _; exact h_each_nn i
  have h_abs_bound :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖‖fun i => Du i x‖ ^ γBar‖ ≤ ∑ i, ‖Du i x‖ ^ γBar := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    have hnn : 0 ≤ ‖fun i => Du i x‖ ^ γBar :=
      Real.rpow_nonneg (norm_nonneg _) γBar
    rw [Real.norm_of_nonneg hnn]
    exact h_pointwise x
  exact h_sum_int.mono' h_rpow_meas h_abs_bound

/-- **D4e-pre `hUbetap_int` (exponent-parameterized).** `|u|^{β̄'}`-integrability
from `MemLpPer (gammaBar α₀ β₀) u` via the exponent inclusion
`betaBar' β₀ ≤ gammaBar α₀ β₀` (valid since `α₀ ≥ 1`), taking the bare
exponents instead of a `HypothesisPowerGrowth` bundle.  Body is the
exponent-only reduction via `MemLp.mono_exponent` + `integrable_norm_rpow`. -/
theorem hUbetap_int_of_exp
    {α₀ β₀ : ℝ} (hα₀ : 1 < α₀) (hβ₀ : 0 < β₀)
    {u : (Fin d → ℝ) → ℝ}
    (hu : MemLpPer (ENNReal.ofReal (gammaBar α₀ β₀)) u) :
    Integrable
      (fun x => |u x| ^ betaBar' β₀) (volume.restrict (UnitCube d)) := by
  haveI hcube_fin : MeasureTheory.IsFiniteMeasure
      (volume.restrict (UnitCube d) : Measure (Fin d → ℝ)) :=
    ⟨by
      rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
          volume_unitCube]; exact ENNReal.one_lt_top⟩
  have hβp_pos : 0 < betaBar' β₀ :=
    lt_trans zero_lt_one (one_lt_betaBar' β₀ hβ₀)
  have hle : betaBar' β₀ ≤ gammaBar α₀ β₀ :=
    StationaryMFG.Hamiltonian.betaBar'_le_gammaBar (le_of_lt hα₀) hβ₀
  have hp_le_q : ENNReal.ofReal (betaBar' β₀)
      ≤ ENNReal.ofReal (gammaBar α₀ β₀) :=
    ENNReal.ofReal_le_ofReal hle
  have hu_memLpγ : MeasureTheory.MemLp u
      (ENNReal.ofReal (gammaBar α₀ β₀)) (volume.restrict (UnitCube d)) := hu
  have hu_memLpβ' : MeasureTheory.MemLp u
      (ENNReal.ofReal (betaBar' β₀)) (volume.restrict (UnitCube d)) :=
    hu_memLpγ.mono_exponent hp_le_q
  have hp_ne_zero : ENNReal.ofReal (betaBar' β₀) ≠ 0 := by simp [hβp_pos]
  have hp_top : ENNReal.ofReal (betaBar' β₀) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hp_toReal : (ENNReal.ofReal (betaBar' β₀)).toReal = betaBar' β₀ :=
    ENNReal.toReal_ofReal hβp_pos.le
  have h_norm_int : Integrable
      (fun x => ‖u x‖ ^ betaBar' β₀) (volume.restrict (UnitCube d)) := by
    have := MeasureTheory.MemLp.integrable_norm_rpow hu_memLpβ' hp_ne_zero hp_top
    rw [hp_toReal] at this; exact this
  have h_eq : (fun x => ‖u x‖ ^ betaBar' β₀)
      = (fun x => |u x| ^ betaBar' β₀) := by
    funext x; rw [Real.norm_eq_abs]
  rw [h_eq] at h_norm_int
  exact h_norm_int

/-! ### G6b — T3-local Young-route a-priori chain (no `L^∞` on `V`)

Raw-real (`β, C0`)-keyed `_intRaw` siblings of the closed-form mean/U/Du/uniform
constants, plus the m-bound → mean → Lp → Du → aggregate chain re-threaded on
top of G6a's `apriori_uepsi_below_young_Vlp_raw`.  Every V-input is integral
data (`hVβp`/`hVβp_int`/`hVm_int`/`hVbetap_int` + measurability); NO pointwise
`hVbnd : |V| ≤ Vbound` rider appears anywhere.  The m^β̄/Du^γ̄ coercive terms are
V-independent, so the rethread swaps only the below + m legs (the unique V·m
pairing consumers).  Conclusions match the shared L∞-keyed chain in shape so
that the engine sibling below feeds the compactness producer unchanged. -/

/-- Local copy of the (private) `SimplePower.holderConjugate_betaPlusOne_apriori`. -/
private lemma t3_holderConjugate_betaPlusOne {β : ℝ} (hβ : 0 < β) :
    Real.HolderConjugate (β + 1) ((β + 1) / β) := by
  rw [Real.holderConjugate_iff]
  refine ⟨by linarith, ?_⟩
  have hβp1_pos : 0 < β + 1 := by linarith
  have hβne : β ≠ 0 := ne_of_gt hβ
  have hβp1ne : β + 1 ≠ 0 := ne_of_gt hβp1_pos
  field_simp
  ring

/-- Local copy of the (private) `SimplePower.young_absorb_pow_into_betaPlusOne`. -/
private theorem t3_young_absorb_pow_into_betaPlusOne {β : ℝ} (hβ : 0 < β)
    (K : ℝ) (hK : 0 ≤ K) (mx : ℝ) (hmx : 0 ≤ mx)
    (lam : ℝ) (hlam : 0 < lam) :
    K * mx ^ β ≤
      (lam ^ ((β + 1) / β)) * (β / (β + 1)) * mx ^ (β + 1)
        + (K / lam) ^ (β + 1) / (β + 1) := by
  have hβp1_pos : 0 < β + 1 := by linarith
  have hβne : β ≠ 0 := ne_of_gt hβ
  have hβp1ne : β + 1 ≠ 0 := ne_of_gt hβp1_pos
  have hHC : Real.HolderConjugate ((β + 1) / β) (β + 1) :=
    (t3_holderConjugate_betaPlusOne hβ).symm
  have ha_nn : 0 ≤ lam * mx ^ β :=
    mul_nonneg hlam.le (Real.rpow_nonneg hmx _)
  have hb_nn : 0 ≤ K / lam := div_nonneg hK hlam.le
  have hY : (lam * mx ^ β) * (K / lam) ≤
      (lam * mx ^ β) ^ ((β + 1) / β) / ((β + 1) / β)
        + (K / lam) ^ (β + 1) / (β + 1) :=
    Real.young_inequality_of_nonneg ha_nn hb_nn hHC
  have hLHS : (lam * mx ^ β) * (K / lam) = K * mx ^ β := by
    have hlamne : lam ≠ 0 := ne_of_gt hlam
    field_simp
  have hpow_lammx :
      (lam * mx ^ β) ^ ((β + 1) / β)
        = lam ^ ((β + 1) / β) * (mx ^ β) ^ ((β + 1) / β) :=
    Real.mul_rpow hlam.le (Real.rpow_nonneg hmx _)
  have hpow_mx :
      (mx ^ β) ^ ((β + 1) / β) = mx ^ (β + 1) := by
    rw [← Real.rpow_mul hmx]
    have : β * ((β + 1) / β) = β + 1 := by field_simp
    rw [this]
  have hdiv : ((β + 1) / β)⁻¹ = β / (β + 1) := by field_simp
  have hR1 :
      (lam * mx ^ β) ^ ((β + 1) / β) / ((β + 1) / β)
        = (lam ^ ((β + 1) / β)) * (β / (β + 1)) * mx ^ (β + 1) := by
    rw [hpow_lammx, hpow_mx, div_eq_mul_inv, hdiv]; ring
  rw [hLHS, hR1] at hY
  exact hY

/-- Local copy of the (private) `SimplePower.rpow_beta_le_rpow_betaPlusOne_add_one`. -/
private lemma t3_rpow_beta_le_rpow_betaPlusOne_add_one
    {β : ℝ} (hβ : 0 < β) {m : ℝ} (hm : 0 ≤ m) :
    m ^ β ≤ m ^ (β + 1) + 1 := by
  rcases le_or_gt m 1 with hm1 | hm1
  · have hpow_le_one : m ^ β ≤ 1 := Real.rpow_le_one hm hm1 hβ.le
    have hpow_nn : 0 ≤ m ^ (β + 1) := Real.rpow_nonneg hm _
    linarith
  · have hm_pos : 0 < m := lt_trans zero_lt_one hm1
    have hpow_le : m ^ β ≤ m ^ (β + 1) :=
      Real.rpow_le_rpow_of_exponent_le hm1.le (by linarith)
    linarith

/-- Local copy of the (private) `SimplePower.lpNormPer_const_unitCube`. -/
private lemma t3_lpNormPer_const_unitCube
    (p : ℝ≥0∞) (hp : p ≠ 0) (c : ℝ) :
    lpNormPer (d := d) p (fun _ : Fin d → ℝ => c) = |c| := by
  unfold lpNormPer eLpNormPer
  have hμuniv :
      (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) Set.univ = 1 := by
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, volume_unitCube]
  have hμ_ne : (Measure.restrict (volume : Measure (Fin d → ℝ))
      (UnitCube d)) ≠ 0 := by
    intro h; rw [h] at hμuniv; simp at hμuniv
  rw [MeasureTheory.eLpNorm_const c hp hμ_ne, hμuniv]
  rw [ENNReal.one_rpow, mul_one]
  rw [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg _)]

/-- Local copy of the (private) `SimplePower.add_rpow_le_two_rpow_mul`. -/
private lemma t3_add_rpow_le_two_rpow_mul {a b q : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hq : 0 ≤ q) :
    (a + b) ^ q ≤ (2 : ℝ) ^ q * (a ^ q + b ^ q) := by
  have hab : 0 ≤ a + b := add_nonneg ha hb
  have hmax_nn : 0 ≤ max a b := le_max_of_le_left ha
  have h1 : a + b ≤ 2 * max a b := by
    have ha' : a ≤ max a b := le_max_left a b
    have hb' : b ≤ max a b := le_max_right a b
    linarith
  have h2 : (a + b) ^ q ≤ (2 * max a b) ^ q := Real.rpow_le_rpow hab h1 hq
  have h3 : (2 * max a b) ^ q = (2 : ℝ) ^ q * (max a b) ^ q :=
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hmax_nn
  have h4 : (max a b) ^ q ≤ a ^ q + b ^ q := by
    rcases le_total a b with hab' | hab'
    · rw [max_eq_right hab']
      have : 0 ≤ a ^ q := Real.rpow_nonneg ha q
      linarith
    · rw [max_eq_left hab']
      have : 0 ≤ b ^ q := Real.rpow_nonneg hb q
      linarith
  have h2pow_nn : 0 ≤ (2 : ℝ) ^ q := Real.rpow_nonneg (by norm_num) _
  calc (a + b) ^ q ≤ (2 * max a b) ^ q := h2
    _ = (2 : ℝ) ^ q * (max a b) ^ q := h3
    _ ≤ (2 : ℝ) ^ q * (a ^ q + b ^ q) := mul_le_mul_of_nonneg_left h4 h2pow_nn

/-- Raw-real form of `aprioriUepsiMeanClosed_int` (keyed by `β, C0`). -/
noncomputable def aprioriUepsiMeanClosed_intRaw (β C0 Vint_bound Vβp_bound : ℝ) : ℝ :=
  max (aprioriUepsiBelowConst_intRaw β C0 Vint_bound Vβp_bound)
      (Vint_bound + C0 * (aprioriMBoundClosed_intRaw β C0 Vint_bound Vβp_bound + 2))

/-- Raw-real form of `aprioriUBoundClosed_int` (keyed by `β, C0`). -/
noncomputable def aprioriUBoundClosed_intRaw
    (d : ℕ) (β C0 Vint_bound Vβp_bound : ℝ) : ℝ :=
  max (poincareWirtingerConstant d)
      (aprioriUepsiMeanClosed_intRaw β C0 Vint_bound Vβp_bound)

/-- Raw-real form of `aprioriDuBoundClosed_int` (keyed by `α, β, C0`). -/
noncomputable def aprioriDuBoundClosed_intRaw
    (d : ℕ) (α β C0 Vint_bound Vβp_bound : ℝ) : ℝ :=
  let C₁ : ℝ := aprioriDuPointwiseConstRaw β C0
  let M  : ℝ := aprioriMBoundClosed_intRaw β C0 Vint_bound Vβp_bound
  let Cu : ℝ := aprioriUBoundClosed_intRaw d β C0 Vint_bound Vβp_bound
  let βp : ℝ := betaBar' β
  let γ  : ℝ := gammaBar α β
  let A  : ℝ := C₁ * (Cu ^ βp * (2 : ℝ) ^ βp * (d : ℝ) ^ βp)
  let B  : ℝ := C₁ * (M + Cu ^ βp * (2 : ℝ) ^ βp + Vβp_bound + 1)
  let r  : ℝ := γ⁻¹ * βp
  (2 * A) ^ (1 / (1 - r)) + (2 * B)

/-- Raw-real form of `aprioriUniformConstantClosed_int` (keyed by `α, β, C0`). -/
noncomputable def aprioriUniformConstantClosed_intRaw
    (d : ℕ) (α β C0 Vint_bound Vβp_bound : ℝ) : ℝ :=
  let M : ℝ := aprioriMBoundClosed_intRaw β C0 Vint_bound Vβp_bound
  let Cu : ℝ := aprioriUBoundClosed_intRaw d β C0 Vint_bound Vβp_bound
  let Cd : ℝ := aprioriDuBoundClosed_intRaw d α β C0 Vint_bound Vβp_bound
  let γ : ℝ := gammaBar α β
  let U : ℝ := Cu * ((d : ℝ) * Cd ^ γ⁻¹ + 1)
  M + U ^ γ + (d : ℝ) * Cd

/-- Non-negativity of `aprioriMBoundClosed_intRaw` (needs `Vint_bound ≥ 0`). -/
theorem aprioriMBoundClosed_intRaw_nn_of_Vint_nn
    (β C0 Vint_bound Vβp_bound : ℝ) (hβ : 0 < β) (hC0 : 0 < C0)
    (hVint_nn : 0 ≤ Vint_bound) :
    0 ≤ aprioriMBoundClosed_intRaw β C0 Vint_bound Vβp_bound := by
  unfold aprioriMBoundClosed_intRaw
  have hβp1_pos : 0 < β + 1 := by linarith
  have hC'_pos : 0 < aprioriUepsiBelowConst_intRaw β C0 Vint_bound Vβp_bound :=
    aprioriUepsiBelowConst_intRaw_pos β C0 Vint_bound Vβp_bound hC0
  have h2C'_nn : 0 ≤ 2 * aprioriUepsiBelowConst_intRaw β C0 Vint_bound Vβp_bound := by
    linarith
  have hR_nn : 0 ≤ aprioriMBoundResidual_intRaw β C0 Vint_bound Vβp_bound := by
    unfold aprioriMBoundResidual_intRaw
    set C' : ℝ := aprioriUepsiBelowConst_intRaw β C0 Vint_bound Vβp_bound with hC'_def
    have h2C'_pos : 0 < 2 * C' := by linarith
    set δ : ℝ := 1 / (2 * C') with hδ_def
    have hδ_pos : 0 < δ := by rw [hδ_def]; exact div_pos (by norm_num) h2C'_pos
    set lam_pow : ℝ := (β + 1) * δ / β with hlam_pow_def
    have hlam_pow_pos : 0 < lam_pow := by
      rw [hlam_pow_def]; exact div_pos (mul_pos hβp1_pos hδ_pos) hβ
    set lam : ℝ := lam_pow ^ (β / (β + 1)) with hlam_def
    have hlam_pos : 0 < lam := Real.rpow_pos_of_pos hlam_pow_pos _
    have hCnn : 0 ≤ C0 / lam := div_nonneg hC0.le hlam_pos.le
    have hpow_nn : 0 ≤ (C0 / lam) ^ (β + 1) := Real.rpow_nonneg hCnn _
    exact div_nonneg hpow_nn hβp1_pos.le
  have hsum_nn :
      0 ≤ aprioriUepsiBelowConst_intRaw β C0 Vint_bound Vβp_bound + Vint_bound +
            aprioriMBoundResidual_intRaw β C0 Vint_bound Vβp_bound + C0 := by
    linarith [hC'_pos, hC0, hR_nn]
  exact mul_nonneg h2C'_nn hsum_nn

/-- Non-negativity of `aprioriUepsiMeanClosed_intRaw`. -/
theorem aprioriUepsiMeanClosed_intRaw_nn
    (β C0 Vint_bound Vβp_bound : ℝ) (hC0 : 0 < C0) :
    0 ≤ aprioriUepsiMeanClosed_intRaw β C0 Vint_bound Vβp_bound := by
  unfold aprioriUepsiMeanClosed_intRaw
  exact le_trans (aprioriUepsiBelowConst_intRaw_nn β C0 Vint_bound Vβp_bound hC0)
        (le_max_left _ _)

/-- Non-negativity of `aprioriUBoundClosed_intRaw`. -/
theorem aprioriUBoundClosed_intRaw_nn
    (β C0 Vint_bound Vβp_bound : ℝ) (hC0 : 0 < C0) :
    0 ≤ aprioriUBoundClosed_intRaw d β C0 Vint_bound Vβp_bound := by
  unfold aprioriUBoundClosed_intRaw
  have hd_nn : (0 : ℝ) ≤ poincareWirtingerConstant d := by
    rw [poincareWirtingerConstant_def]; exact_mod_cast Nat.zero_le d
  exact le_trans hd_nn (le_max_left _ _)

/-- Non-negativity of `aprioriDuBoundClosed_intRaw`. -/
theorem aprioriDuBoundClosed_intRaw_nn
    (α β C0 Vint_bound Vβp_bound : ℝ) (hβ : 0 < β) (hC0 : 0 < C0)
    (hVint_nn : 0 ≤ Vint_bound) (hVβp_nn : 0 ≤ Vβp_bound) :
    0 ≤ aprioriDuBoundClosed_intRaw d α β C0 Vint_bound Vβp_bound := by
  unfold aprioriDuBoundClosed_intRaw
  set C₁ : ℝ := aprioriDuPointwiseConstRaw β C0 with hC₁_def
  set M  : ℝ := aprioriMBoundClosed_intRaw β C0 Vint_bound Vβp_bound with hM_def
  set Cu : ℝ := aprioriUBoundClosed_intRaw d β C0 Vint_bound Vβp_bound with hCu_def
  set βp : ℝ := betaBar' β with hβp_def
  set γ  : ℝ := gammaBar α β with hγ_def
  set A  : ℝ := C₁ * (Cu ^ βp * (2 : ℝ) ^ βp * (d : ℝ) ^ βp) with hA_def
  set B  : ℝ := C₁ * (M + Cu ^ βp * (2 : ℝ) ^ βp + Vβp_bound + 1) with hB_def
  set r  : ℝ := γ⁻¹ * βp with hr_def
  have hC₁_nn : 0 ≤ C₁ := aprioriDuPointwiseConstRaw_nn β C0 hC0
  have hM_nn : 0 ≤ M :=
    aprioriMBoundClosed_intRaw_nn_of_Vint_nn β C0 Vint_bound Vβp_bound hβ hC0 hVint_nn
  have hCu_nn : 0 ≤ Cu := aprioriUBoundClosed_intRaw_nn β C0 Vint_bound Vβp_bound hC0
  have hβp_nn : 0 ≤ βp := by
    rw [hβp_def]; exact (lt_trans zero_lt_one (one_lt_betaBar' β hβ)).le
  have hd_nn : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have hCu_pow_nn : 0 ≤ Cu ^ βp := Real.rpow_nonneg hCu_nn _
  have h2pow_nn : 0 ≤ (2 : ℝ) ^ βp := Real.rpow_nonneg (by norm_num) _
  have hd_pow_nn : 0 ≤ (d : ℝ) ^ βp := Real.rpow_nonneg hd_nn _
  have hA_nn : 0 ≤ A := by
    rw [hA_def]
    exact mul_nonneg hC₁_nn (mul_nonneg (mul_nonneg hCu_pow_nn h2pow_nn) hd_pow_nn)
  have hB_nn : 0 ≤ B := by
    rw [hB_def]
    refine mul_nonneg hC₁_nn ?_
    have h2 : 0 ≤ Cu ^ βp * (2 : ℝ) ^ βp := mul_nonneg hCu_pow_nn h2pow_nn
    linarith
  have h2A_nn : 0 ≤ 2 * A := by linarith
  have h2A_pow_nn : 0 ≤ (2 * A) ^ (1 / (1 - r)) := Real.rpow_nonneg h2A_nn _
  linarith

/-- Non-negativity of `aprioriUniformConstantClosed_intRaw`. -/
theorem aprioriUniformConstantClosed_intRaw_nn
    (α β C0 Vint_bound Vβp_bound : ℝ) (hα : 1 < α) (hβ : 0 < β) (hC0 : 0 < C0)
    (hVint_nn : 0 ≤ Vint_bound) (hVβp_nn : 0 ≤ Vβp_bound) :
    0 ≤ aprioriUniformConstantClosed_intRaw d α β C0 Vint_bound Vβp_bound := by
  unfold aprioriUniformConstantClosed_intRaw
  set M : ℝ := aprioriMBoundClosed_intRaw β C0 Vint_bound Vβp_bound with hM_def
  set Cu : ℝ := aprioriUBoundClosed_intRaw d β C0 Vint_bound Vβp_bound with hCu_def
  set Cd : ℝ := aprioriDuBoundClosed_intRaw d α β C0 Vint_bound Vβp_bound with hCd_def
  set γ : ℝ := gammaBar α β with hγ_def
  set U : ℝ := Cu * ((d : ℝ) * Cd ^ γ⁻¹ + 1) with hU_def
  have hα_pos : 0 < α := lt_trans zero_lt_one hα
  have hγ_pos : 0 < γ := by rw [hγ_def]; exact gammaBar_pos α β hα_pos hβ
  have hM_nn : 0 ≤ M :=
    aprioriMBoundClosed_intRaw_nn_of_Vint_nn β C0 Vint_bound Vβp_bound hβ hC0 hVint_nn
  have hCu_nn : 0 ≤ Cu := aprioriUBoundClosed_intRaw_nn β C0 Vint_bound Vβp_bound hC0
  have hCd_nn : 0 ≤ Cd :=
    aprioriDuBoundClosed_intRaw_nn α β C0 Vint_bound Vβp_bound hβ hC0 hVint_nn hVβp_nn
  have hd_nn : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have hCd_inv_nn : 0 ≤ Cd ^ γ⁻¹ := Real.rpow_nonneg hCd_nn _
  have hU_nn : 0 ≤ U := by
    rw [hU_def]
    exact mul_nonneg hCu_nn (by positivity)
  have hU_pow_nn : 0 ≤ U ^ γ := Real.rpow_nonneg hU_nn _
  have hdCd_nn : 0 ≤ (d : ℝ) * Cd := mul_nonneg hd_nn hCd_nn
  linarith

/-- **G6b m-bound (Young, no `L^∞`).** Same conclusion shape as
`apriori_m_bound_closed_riderNN_raw` but the below leg is G6a's
`apriori_uepsi_below_young_Vlp_raw`, so NO `hVbnd`; keyed on
`aprioriMBoundClosed_intRaw`. -/
theorem apriori_m_bound_young_Vlp_raw
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (α β C0 : ℝ) (hα : 1 < α) (hβ : 0 < β) (hC0 : 0 < C0)
    (hLower :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m → H x p m ≥ (‖p‖ ^ α) / C0 - C0 * (m ^ β + 1))
    (hH0 : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
            ∀ p : Fin d → ℝ, ‖p‖ ^ α / C0 - C0 ≤ H x p 0)
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
          (mx ^ β) / C0 - C0 ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hMnonneg : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hVβp :
      ∫ x in UnitCube d, |V x| ^ ((β + 1) / β)
          ∂(volume : Measure (Fin d → ℝ)) ≤ Vβp_bound)
    (hVβp_nn : 0 ≤ Vβp_bound)
    (hVβp_int : Integrable (fun x => |V x| ^ ((β + 1) / β))
                  (volume.restrict (UnitCube d)))
    (hVm_int : Integrable (fun x => |V x| * m x)
                  (volume.restrict (UnitCube d)))
    (hV_meas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hm_meas : AEStronglyMeasurable m (volume.restrict (UnitCube d)))
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ)) ≤ Vint_bound)
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
              (fun x => |V x| + C0 * (m x ^ β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (β + 1)) (volume.restrict (UnitCube d)))
    (hM_int : Integrable m (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d))) :
    ∫ x in UnitCube d, m x ^ (β + 1) ∂(volume : Measure (Fin d → ℝ))
      ≤ aprioriMBoundClosed_intRaw β C0 Vint_bound Vβp_bound := by
  have hC_pos : 0 < C0 := hC0
  have hβ_pos : 0 < β := hβ
  have hβp1_pos : 0 < β + 1 := by linarith
  have hcube_vol_lt : (volume.restrict (UnitCube (d := d))) Set.univ < ∞ := by
    rw [Measure.restrict_apply MeasurableSet.univ]; simp
  have : IsFiniteMeasure (volume.restrict (UnitCube (d := d))) := ⟨hcube_vol_lt⟩
  set vol : ℝ := (volume (UnitCube (d := d))).toReal with hvol_def
  have hvol_nn : 0 ≤ vol := ENNReal.toReal_nonneg
  have hvol_eq_one : vol = 1 := by simp [hvol_def]
  set C' : ℝ := aprioriUepsiBelowConst_intRaw β C0 Vint_bound Vβp_bound with hC'_def
  have hC'_pos : 0 < C' :=
    aprioriUepsiBelowConst_intRaw_pos β C0 Vint_bound Vβp_bound hC0
  have hbelow :
      (1 / C') * (∫ x in UnitCube d, m x ^ (β + 1)
                    ∂(volume : Measure (Fin d → ℝ))) - C'
        ≤ ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) :=
    apriori_uepsi_below_young_Vlp_raw (d := d) (H := H) (DpH := DpH)
      β C0 hβ hC0 V Du m u epsTerms Vint_bound Vβp_bound
      h_lagr hMnonneg hVβp hVβp_nn hVβp_int hVm_int hV_meas hm_meas hEpsNN
      h_identity hLB_int hM_int hRHSbelow_int
  have habove :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) ≤
        ∫ x in UnitCube d, (|V x| + C0 * (m x ^ β + 1))
          ∂(volume : Measure (Fin d → ℝ)) :=
    apriori_uepsi_above_riderNN_raw (d := d) α β C0 hβ hC0 hLower hH0
      V Du m u hHJB hMnonneg hu_int hRHSabove_int
  set X : ℝ := ∫ x in UnitCube d, m x ^ (β + 1)
                  ∂(volume : Measure (Fin d → ℝ)) with hX_def
  have hX_nn : 0 ≤ X := by
    apply integral_nonneg_of_ae
    filter_upwards [hMnonneg] with x hxm
    exact Real.rpow_nonneg hxm _
  set Y : ℝ := ∫ x in UnitCube d, m x ^ β
                  ∂(volume : Measure (Fin d → ℝ)) with hY_def
  have hY_nn : 0 ≤ Y := by
    apply integral_nonneg_of_ae
    filter_upwards [hMnonneg] with x hxm
    exact Real.rpow_nonneg hxm _
  set Vint : ℝ := ∫ x in UnitCube d, |V x|
                    ∂(volume : Measure (Fin d → ℝ)) with hVint_def
  have habove_eq :
      (∫ x in UnitCube d, (|V x| + C0 * (m x ^ β + 1))
          ∂(volume : Measure (Fin d → ℝ)))
        = Vint + C0 * (Y + vol) := by
    have habs_int : Integrable (fun x => |V x|)
                      (volume.restrict (UnitCube d)) := by
      have hpow_int : Integrable (fun x => C0 * (m x ^ β + 1))
                        (volume.restrict (UnitCube d)) := by
        have hone : Integrable (fun _ : Fin d → ℝ => (1 : ℝ))
                      (volume.restrict (UnitCube d)) := integrable_const _
        exact (hMbeta_int.add hone).const_mul C0
      have : Integrable (fun x => (|V x| + C0 * (m x ^ β + 1))
                                    - C0 * (m x ^ β + 1))
                (volume.restrict (UnitCube d)) :=
        hRHSabove_int.sub hpow_int
      exact this.congr (Filter.Eventually.of_forall (fun x => by ring))
    have hpow_int : Integrable (fun x => C0 * (m x ^ β + 1))
                      (volume.restrict (UnitCube d)) := by
      have hone : Integrable (fun _ : Fin d → ℝ => (1 : ℝ))
                    (volume.restrict (UnitCube d)) := integrable_const _
      exact (hMbeta_int.add hone).const_mul C0
    rw [integral_add habs_int hpow_int]
    have hsplit :
        ∫ x in UnitCube d, C0 * (m x ^ β + 1)
            ∂(volume : Measure (Fin d → ℝ))
          = C0 * (Y + vol) := by
      rw [integral_const_mul]
      have hsub :
          ∫ x in UnitCube d, (m x ^ β + 1)
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
  have hcomb : (1 / C') * X - C' ≤ Vint + C0 * (Y + vol) := by
    calc (1 / C') * X - C' ≤ ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) := hbelow
      _ ≤ _ := habove
      _ = Vint + C0 * (Y + vol) := habove_eq
  set δ : ℝ := 1 / (2 * C') with hδ_def
  have h2C'_pos : 0 < 2 * C' := by linarith
  have hδ_pos : 0 < δ := by
    rw [hδ_def]; exact div_pos (by norm_num) h2C'_pos
  set lam_pow : ℝ := (β + 1) * δ / β with hlam_pow_def
  have hlam_pow_pos : 0 < lam_pow := by
    rw [hlam_pow_def]
    exact div_pos (mul_pos hβp1_pos hδ_pos) hβ_pos
  have hlam_pow_eq_δ : lam_pow * (β / (β + 1)) = δ := by
    rw [hlam_pow_def]; field_simp
  set lam : ℝ := lam_pow ^ (β / (β + 1)) with hlam_def
  have hlam_pos : 0 < lam := Real.rpow_pos_of_pos hlam_pow_pos _
  have hlam_pow_id : lam ^ ((β + 1) / β) = lam_pow := by
    rw [hlam_def, ← Real.rpow_mul hlam_pow_pos.le]
    have heq : β / (β + 1) * ((β + 1) / β) = 1 := by
      have hβne : β ≠ 0 := ne_of_gt hβ_pos
      have hβp1ne : β + 1 ≠ 0 := ne_of_gt hβp1_pos
      field_simp
    rw [heq, Real.rpow_one]
  set R : ℝ := aprioriMBoundResidual_intRaw β C0 Vint_bound Vβp_bound with hR_def
  have hR_unfold : R = (C0 / lam) ^ (β + 1) / (β + 1) := by
    show aprioriMBoundResidual_intRaw β C0 Vint_bound Vβp_bound = _
    rfl
  have hR_nn : 0 ≤ R := by
    rw [hR_unfold]
    have hCnn : 0 ≤ C0 / lam := div_nonneg hC_pos.le hlam_pos.le
    have hpow_nn : 0 ≤ (C0 / lam) ^ (β + 1) := Real.rpow_nonneg hCnn _
    exact div_nonneg hpow_nn hβp1_pos.le
  have hYoung_pt : ∀ mx : ℝ, 0 ≤ mx →
      C0 * mx ^ β ≤ δ * mx ^ (β + 1) + R := by
    intro mx hmx
    have hY := t3_young_absorb_pow_into_betaPlusOne (β := β) hβ_pos
                  C0 hC_pos.le mx hmx lam hlam_pos
    rw [hlam_pow_id] at hY
    rw [hlam_pow_eq_δ] at hY
    rw [hR_unfold]
    exact hY
  have hY_int :
      Integrable (fun x => C0 * m x ^ β) (volume.restrict (UnitCube d)) :=
    hMbeta_int.const_mul C0
  have hRHS_int :
      Integrable (fun x => δ * m x ^ (β + 1) + R)
        (volume.restrict (UnitCube d)) :=
    (hLB_int.const_mul δ).add (integrable_const _)
  have hpoint_ae :
      (fun x => C0 * m x ^ β)
        ≤ᵐ[volume.restrict (UnitCube d)]
        (fun x => δ * m x ^ (β + 1) + R) := by
    filter_upwards [hMnonneg] with x hxm
    exact hYoung_pt (m x) hxm
  have hYint_le :
      ∫ x in UnitCube d, C0 * m x ^ β
          ∂(volume : Measure (Fin d → ℝ)) ≤
      ∫ x in UnitCube d, (δ * m x ^ (β + 1) + R)
          ∂(volume : Measure (Fin d → ℝ)) :=
    setIntegral_mono_ae_restrict hY_int hRHS_int hpoint_ae
  have hYint_LHS :
      ∫ x in UnitCube d, C0 * m x ^ β
          ∂(volume : Measure (Fin d → ℝ))
        = C0 * Y := by
    rw [integral_const_mul]
  have hYint_RHS :
      ∫ x in UnitCube d, (δ * m x ^ (β + 1) + R)
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
      (1 / C') * X - C' ≤ Vint + δ * X + R * vol + C0 * vol := by
    have : C0 * (Y + vol) = C0 * Y + C0 * vol := by ring
    have h1 : Vint + C0 * (Y + vol) ≤ Vint + (δ * X + R * vol) + C0 * vol := by
      linarith [hYint_le]
    linarith [hcomb, h1]
  have hcoeff_id : (1 / C') - δ = 1 / (2 * C') := by
    rw [hδ_def]
    have hC'ne : C' ≠ 0 := ne_of_gt hC'_pos
    have h2C'ne : 2 * C' ≠ 0 := ne_of_gt h2C'_pos
    field_simp
    ring
  have habs : (1 / (2 * C')) * X ≤ C' + Vint + R * vol + C0 * vol := by
    have hsub : (1 / C') * X - δ * X = (1 / (2 * C')) * X := by
      have : (1 / C') * X - δ * X = ((1 / C') - δ) * X := by ring
      rw [this, hcoeff_id]
    linarith [hcomb', hsub]
  have hVint_le : Vint ≤ Vint_bound := hVint
  have habs2 : (1 / (2 * C')) * X ≤ C' + Vint_bound + R * vol + C0 * vol := by
    linarith [habs, hVint_le]
  have hM_unfold :
      aprioriMBoundClosed_intRaw β C0 Vint_bound Vβp_bound
        = 2 * C' * (C' + Vint_bound + R + C0) := by
    show aprioriMBoundClosed_intRaw β C0 Vint_bound Vβp_bound = _
    rfl
  have h2C'_pos' : 0 < 2 * C' := h2C'_pos
  have hmul : 2 * C' * ((1 / (2 * C')) * X) ≤
                2 * C' * (C' + Vint_bound + R * vol + C0 * vol) := by
    exact mul_le_mul_of_nonneg_left habs2 h2C'_pos'.le
  have hLHS_eq : 2 * C' * ((1 / (2 * C')) * X) = X := by
    have h2C'ne : 2 * C' ≠ 0 := ne_of_gt h2C'_pos
    field_simp
  rw [hLHS_eq] at hmul
  rw [hvol_eq_one, mul_one, mul_one] at hmul
  rw [hM_unfold]
  exact hmul

/-- **G6b mean-bound (Young, no `L^∞`).** Mirror of
`apriori_uepsi_mean_closed_riderNN_raw`; below + m legs swapped to the Young
route; keyed on `aprioriUepsiMeanClosed_intRaw`. -/
theorem apriori_uepsi_mean_young_Vlp_raw
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (α β C0 : ℝ) (hα : 1 < α) (hβ : 0 < β) (hC0 : 0 < C0)
    (hLower :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m → H x p m ≥ (‖p‖ ^ α) / C0 - C0 * (m ^ β + 1))
    (hH0 : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
            ∀ p : Fin d → ℝ, ‖p‖ ^ α / C0 - C0 ≤ H x p 0)
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
          (mx ^ β) / C0 - C0 ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hMnonneg : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hVβp :
      ∫ x in UnitCube d, |V x| ^ ((β + 1) / β)
          ∂(volume : Measure (Fin d → ℝ)) ≤ Vβp_bound)
    (hVβp_nn : 0 ≤ Vβp_bound)
    (hVβp_int : Integrable (fun x => |V x| ^ ((β + 1) / β))
                  (volume.restrict (UnitCube d)))
    (hVm_int : Integrable (fun x => |V x| * m x)
                  (volume.restrict (UnitCube d)))
    (hV_meas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hm_meas : AEStronglyMeasurable m (volume.restrict (UnitCube d)))
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ)) ≤ Vint_bound)
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
              (fun x => |V x| + C0 * (m x ^ β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (β + 1)) (volume.restrict (UnitCube d)))
    (hM_int : Integrable m (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d))) :
    |∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ))|
      ≤ aprioriUepsiMeanClosed_intRaw β C0 Vint_bound Vβp_bound := by
  have hC_pos : 0 < C0 := hC0
  have hβ_pos : 0 < β := hβ
  have hcube_vol_lt : (volume.restrict (UnitCube (d := d))) Set.univ < ∞ := by
    rw [Measure.restrict_apply MeasurableSet.univ]; simp
  have : IsFiniteMeasure (volume.restrict (UnitCube (d := d))) := ⟨hcube_vol_lt⟩
  set vol : ℝ := (volume (UnitCube (d := d))).toReal with hvol_def
  have hvol_nn : 0 ≤ vol := ENNReal.toReal_nonneg
  have hvol_eq_one : vol = 1 := by simp [hvol_def]
  set M : ℝ := aprioriMBoundClosed_intRaw β C0 Vint_bound Vβp_bound with hM_def
  have hM_le :
      ∫ x in UnitCube d, m x ^ (β + 1)
          ∂(volume : Measure (Fin d → ℝ)) ≤ M :=
    apriori_m_bound_young_Vlp_raw (d := d) (H := H) (DpH := DpH)
      α β C0 hα hβ hC0 hLower hH0 V Du m u epsTerms Vint_bound Vβp_bound
      hHJB h_lagr hMnonneg hVβp hVβp_nn hVβp_int hVm_int hV_meas hm_meas hVint hEpsNN
      h_identity hu_int hRHSabove_int hLB_int hM_int hMbeta_int hRHSbelow_int
  set C' : ℝ := aprioriUepsiBelowConst_intRaw β C0 Vint_bound Vβp_bound with hC'_def
  have hC'_pos : 0 < C' :=
    aprioriUepsiBelowConst_intRaw_pos β C0 Vint_bound Vβp_bound hC0
  have hbelow :
      (1 / C') * (∫ x in UnitCube d, m x ^ (β + 1)
                    ∂(volume : Measure (Fin d → ℝ))) - C'
        ≤ ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) :=
    apriori_uepsi_below_young_Vlp_raw (d := d) (H := H) (DpH := DpH)
      β C0 hβ hC0 V Du m u epsTerms Vint_bound Vβp_bound
      h_lagr hMnonneg hVβp hVβp_nn hVβp_int hVm_int hV_meas hm_meas hEpsNN
      h_identity hLB_int hM_int hRHSbelow_int
  have habove :
      ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) ≤
        ∫ x in UnitCube d, (|V x| + C0 * (m x ^ β + 1))
          ∂(volume : Measure (Fin d → ℝ)) :=
    apriori_uepsi_above_riderNN_raw (d := d) α β C0 hβ hC0 hLower hH0
      V Du m u hHJB hMnonneg hu_int hRHSabove_int
  set X : ℝ := ∫ x in UnitCube d, m x ^ (β + 1)
                  ∂(volume : Measure (Fin d → ℝ)) with hX_def
  have hX_nn : 0 ≤ X := by
    apply integral_nonneg_of_ae
    filter_upwards [hMnonneg] with x hxm
    exact Real.rpow_nonneg hxm _
  set Y : ℝ := ∫ x in UnitCube d, m x ^ β
                  ∂(volume : Measure (Fin d → ℝ)) with hY_def
  have hY_nn : 0 ≤ Y := by
    apply integral_nonneg_of_ae
    filter_upwards [hMnonneg] with x hxm
    exact Real.rpow_nonneg hxm _
  set Vint : ℝ := ∫ x in UnitCube d, |V x|
                    ∂(volume : Measure (Fin d → ℝ)) with hVint_def
  have habs_int : Integrable (fun x => |V x|)
                      (volume.restrict (UnitCube d)) := by
    have hpow_int : Integrable (fun x => C0 * (m x ^ β + 1))
                      (volume.restrict (UnitCube d)) := by
      have hone : Integrable (fun _ : Fin d → ℝ => (1 : ℝ))
                    (volume.restrict (UnitCube d)) := integrable_const _
      exact (hMbeta_int.add hone).const_mul C0
    have : Integrable (fun x => (|V x| + C0 * (m x ^ β + 1))
                                  - C0 * (m x ^ β + 1))
              (volume.restrict (UnitCube d)) :=
      hRHSabove_int.sub hpow_int
    exact this.congr (Filter.Eventually.of_forall (fun x => by ring))
  have habove_eq :
      (∫ x in UnitCube d, (|V x| + C0 * (m x ^ β + 1))
          ∂(volume : Measure (Fin d → ℝ)))
        = Vint + C0 * (Y + vol) := by
    have hpow_int : Integrable (fun x => C0 * (m x ^ β + 1))
                      (volume.restrict (UnitCube d)) := by
      have hone : Integrable (fun _ : Fin d → ℝ => (1 : ℝ))
                    (volume.restrict (UnitCube d)) := integrable_const _
      exact (hMbeta_int.add hone).const_mul C0
    rw [integral_add habs_int hpow_int]
    have hsplit :
        ∫ x in UnitCube d, C0 * (m x ^ β + 1)
            ∂(volume : Measure (Fin d → ℝ))
          = C0 * (Y + vol) := by
      rw [integral_const_mul]
      have hsub :
          ∫ x in UnitCube d, (m x ^ β + 1)
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
        (fun x => m x ^ β)
          ≤ᵐ[volume.restrict (UnitCube d)]
          (fun x => m x ^ (β + 1) + 1) := by
      filter_upwards [hMnonneg] with x hxm
      exact t3_rpow_beta_le_rpow_betaPlusOne_add_one hβ_pos hxm
    have hone_int' : Integrable (fun _ : Fin d → ℝ => (1 : ℝ))
                      (volume.restrict (UnitCube d)) := integrable_const _
    have hRHS_int : Integrable (fun x => m x ^ (β + 1) + 1)
                      (volume.restrict (UnitCube d)) :=
      hLB_int.add hone_int'
    have hint_le :
        ∫ x in UnitCube d, m x ^ β
            ∂(volume : Measure (Fin d → ℝ)) ≤
        ∫ x in UnitCube d, (m x ^ (β + 1) + 1)
            ∂(volume : Measure (Fin d → ℝ)) :=
      setIntegral_mono_ae_restrict hMbeta_int hRHS_int hpoint
    have hRHS_eq :
        ∫ x in UnitCube d, (m x ^ (β + 1) + 1)
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
  have hUint_ub : Uint ≤ Vint_bound + C0 * (M + 2 * vol) := by
    have h_step : Uint ≤ Vint + C0 * (Y + vol) := by
      calc Uint ≤ _ := habove
        _ = _ := habove_eq
    have hY_step : C0 * (Y + vol) ≤ C0 * ((M + vol) + vol) :=
      mul_le_mul_of_nonneg_left (by linarith) hC_pos.le
    have h_combine : Vint + C0 * (Y + vol) ≤ Vint_bound + C0 * (M + 2 * vol) := by
      have : C0 * ((M + vol) + vol) = C0 * (M + 2 * vol) := by ring
      linarith [hY_step, hVint_le, this]
    linarith
  have hUint_lb : -C' ≤ Uint := by
    have hcoeff_nn : 0 ≤ (1 / C') := by positivity
    have hLHS_nn : 0 ≤ (1 / C') * X := mul_nonneg hcoeff_nn hX_nn
    have hbelow' : (1 / C') * X - C' ≤ Uint := by
      simpa [hX_def, hUint_def] using hbelow
    linarith
  have hCmean_unfold :
      aprioriUepsiMeanClosed_intRaw β C0 Vint_bound Vβp_bound
        = max C' (Vint_bound + C0 * (M + 2)) := by
    show aprioriUepsiMeanClosed_intRaw β C0 Vint_bound Vβp_bound = _
    rfl
  have hCmean_ge_C' : C' ≤ aprioriUepsiMeanClosed_intRaw β C0 Vint_bound Vβp_bound := by
    rw [hCmean_unfold]; exact le_max_left _ _
  have hUint_ub' : Uint ≤ Vint_bound + C0 * (M + 2) := by
    have : (M + 2 * vol) = M + 2 := by rw [hvol_eq_one]; ring
    rw [this] at hUint_ub
    exact hUint_ub
  have hCmean_ge_ub :
      Vint_bound + C0 * (M + 2)
        ≤ aprioriUepsiMeanClosed_intRaw β C0 Vint_bound Vβp_bound := by
    rw [hCmean_unfold]; exact le_max_right _ _
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have hneg :
        -aprioriUepsiMeanClosed_intRaw β C0 Vint_bound Vβp_bound ≤ -C' := by
      linarith [hCmean_ge_C']
    linarith [hUint_lb]
  · linarith [hUint_ub', hCmean_ge_ub]

/-- **G6b Lᵖ-bound (Young, no `L^∞`).** Mirror of
`apriori_uepsi_Lp_closed_riderNN_aePeriodic_raw`; the mean leg is swapped to
the Young route; keyed on `aprioriUBoundClosed_intRaw`. -/
theorem apriori_uepsi_Lp_young_Vlp_raw
    [AxisMixMeasureHypothesis]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (α β C0 : ℝ) (hα : 1 < α) (hβ : 0 < β) (hC0 : 0 < C0)
    (hLower :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m → H x p m ≥ (‖p‖ ^ α) / C0 - C0 * (m ^ β + 1))
    (hH0 : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
            ∀ p : Fin d → ℝ, ‖p‖ ^ α / C0 - C0 ≤ H x p 0)
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
          (mx ^ β) / C0 - C0 ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hMnonneg : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hVβp :
      ∫ x in UnitCube d, |V x| ^ ((β + 1) / β)
          ∂(volume : Measure (Fin d → ℝ)) ≤ Vβp_bound)
    (hVβp_nn : 0 ≤ Vβp_bound)
    (hVβp_int : Integrable (fun x => |V x| ^ ((β + 1) / β))
                  (volume.restrict (UnitCube d)))
    (hVm_int : Integrable (fun x => |V x| * m x)
                  (volume.restrict (UnitCube d)))
    (hV_meas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hm_meas : AEStronglyMeasurable m (volume.restrict (UnitCube d)))
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ)) ≤ Vint_bound)
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
              (fun x => |V x| + C0 * (m x ^ β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (β + 1)) (volume.restrict (UnitCube d)))
    (hM_int : Integrable m (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d)))
    (hγ_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (gammaBar α β))
    (hγ_top : ENNReal.ofReal (gammaBar α β) ≠ ⊤)
    (hu_per : Periodic.AEPeriodic (d := d) u)
    (hu_sob : MemSobolevPer (ENNReal.ofReal (gammaBar α β)) u)
    (hDu_weak : ∀ i, HasWeakDerivPer i u (Du i))
    (hDu_per : ∀ i, Periodic.AEPeriodic (d := d) (Du i))
    (hDu_lp : ∀ i, MemLpPer (ENNReal.ofReal (gammaBar α β)) (Du i)) :
    lpNormPer (ENNReal.ofReal (gammaBar α β)) u ≤
      aprioriUBoundClosed_intRaw d β C0 Vint_bound Vβp_bound *
        ((∑ i : Fin d, lpNormPer
            (ENNReal.ofReal (gammaBar α β)) (Du i)) + 1) := by
  classical
  set p : ℝ≥0∞ := ENNReal.ofReal (gammaBar α β) with hp_def
  set Cmean : ℝ := aprioriUepsiMeanClosed_intRaw β C0 Vint_bound Vβp_bound
    with hCmean_def
  have hCmean_nn : 0 ≤ Cmean :=
    aprioriUepsiMeanClosed_intRaw_nn β C0 Vint_bound Vβp_bound hC0
  have hCmean_le :
      |∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ))| ≤ Cmean :=
    apriori_uepsi_mean_young_Vlp_raw (d := d) (H := H) (DpH := DpH)
      α β C0 hα hβ hC0 hLower hH0 V Du m u epsTerms Vint_bound Vβp_bound
      hHJB h_lagr hMnonneg hVβp hVβp_nn hVβp_int hVm_int hV_meas hm_meas hVint hEpsNN
      h_identity hu_int hRHSabove_int hLB_int hM_int hMbeta_int hRHSbelow_int
  have hmean_eq :
      periodicMean u = ∫ x in UnitCube d, u x ∂(volume : Measure (Fin d → ℝ)) := rfl
  have h_abs_mean_le_Cmean : |periodicMean u| ≤ Cmean := by
    rw [hmean_eq]; exact hCmean_le
  let hu_rep : Periodic.AEPeriodicRep (d := d) u := Classical.choice hu_per
  let hDu_rep : ∀ i, Periodic.AEPeriodicRep (d := d) (Du i) :=
    fun i => Classical.choice (hDu_per i)
  have h_poincare :
      lpNormPer (d := d) p (u - (fun _ : Fin d → ℝ => periodicMean u))
        ≤ poincareWirtingerConstant d *
            ∑ i : Fin d, lpNormPer (d := d) p (Du i) :=
    Periodic.poincareWirtinger_AEPeriodicRep (d := d) (p := p) hγ_one_le hγ_top
      hu_rep hu_sob hDu_weak hDu_rep hDu_lp
  have hu_lp : MemLpPer p u := hu_sob.1
  have hcube_finite : MeasureTheory.IsFiniteMeasure
      (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  have hconst_lp : MemLpPer p (fun _ : Fin d → ℝ => periodicMean u) :=
    MemLp.toMemLpPer (MeasureTheory.memLp_const _)
  have hneg_const_lp :
      MemLpPer p (fun _ : Fin d → ℝ => -periodicMean u) :=
    MemLp.toMemLpPer (MeasureTheory.memLp_const _)
  have hdiff_lp : MemLpPer p (u - (fun _ : Fin d → ℝ => periodicMean u)) := by
    have hrew :
        u - (fun _ : Fin d → ℝ => periodicMean u) =
          u + (fun _ : Fin d → ℝ => -periodicMean u) := by
      funext x; simp [sub_eq_add_neg]
    rw [hrew]; exact hu_lp.add hneg_const_lp
  have hp_one_le : (1 : ℝ≥0∞) ≤ p := hγ_one_le
  have htri :
      lpNormPer (d := d) p u ≤
        lpNormPer (d := d) p (u - (fun _ : Fin d → ℝ => periodicMean u)) +
          lpNormPer (d := d) p (fun _ : Fin d → ℝ => periodicMean u) := by
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
    intro hp0; rw [hp0] at hp_one_le; exact absurd hp_one_le (by norm_num)
  have h_const_norm :
      lpNormPer (d := d) p (fun _ : Fin d → ℝ => periodicMean u)
        = |periodicMean u| :=
    t3_lpNormPer_const_unitCube p hp_ne_zero (periodicMean u)
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
          rw [h_const_norm]; exact add_le_add h_poincare le_rfl
      _ ≤ poincareWirtingerConstant d * S + Cmean :=
          add_le_add le_rfl h_abs_mean_le_Cmean
  set C : ℝ := aprioriUBoundClosed_intRaw d β C0 Vint_bound Vβp_bound with hC_def
  have hC_unfold : C = max (poincareWirtingerConstant d) Cmean := by
    show aprioriUBoundClosed_intRaw d β C0 Vint_bound Vβp_bound = _
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

/-- **G6b Du-bound (Young, no `L^∞`).** Mirror of
`apriori_Du_bound_closed_form_riderNN_aePeriodic_raw`; m + Lp legs swapped to the
Young route; the V·m pairing is gone; `Vβp_bound` enters via the integral `hVβp`.
Keyed on `aprioriDuBoundClosed_intRaw`. -/
theorem apriori_Du_bound_young_Vlp_raw
    [AxisMixMeasureHypothesis]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (α β C0 : ℝ) (hα : 1 < α) (hβ : 0 < β) (hC0 : 0 < C0)
    (hLower :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m → H x p m ≥ (‖p‖ ^ α) / C0 - C0 * (m ^ β + 1))
    (hH0 : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
            ∀ p : Fin d → ℝ, ‖p‖ ^ α / C0 - C0 ≤ H x p 0)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u epsTerms : (Fin d → ℝ) → ℝ)
    (Vint_bound Vβp_bound : ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ β) / C0 - C0 ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hMnonneg : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hVβp :
      ∫ x in UnitCube d, |V x| ^ ((β + 1) / β)
          ∂(volume : Measure (Fin d → ℝ)) ≤ Vβp_bound)
    (hVβp_nn : 0 ≤ Vβp_bound)
    (hVβp_int : Integrable (fun x => |V x| ^ ((β + 1) / β))
                  (volume.restrict (UnitCube d)))
    (hVm_int : Integrable (fun x => |V x| * m x)
                  (volume.restrict (UnitCube d)))
    (hV_meas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hm_meas : AEStronglyMeasurable m (volume.restrict (UnitCube d)))
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ)) ≤ Vint_bound)
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
              (fun x => |V x| + C0 * (m x ^ β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (β + 1)) (volume.restrict (UnitCube d)))
    (hM_int : Integrable m (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d)))
    (hγ_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (gammaBar α β))
    (hγ_top : ENNReal.ofReal (gammaBar α β) ≠ ⊤)
    (hu_per : Periodic.AEPeriodic (d := d) u)
    (hu_sob : MemSobolevPer (ENNReal.ofReal (gammaBar α β)) u)
    (hDu_weak : ∀ i, HasWeakDerivPer i u (Du i))
    (hDu_per : ∀ i, Periodic.AEPeriodic (d := d) (Du i))
    (hDu_lp : ∀ i, MemLpPer (ENNReal.ofReal (gammaBar α β)) (Du i))
    (hDu_norm_int : Integrable
        (fun x => ‖(fun i => Du i x)‖ ^ gammaBar α β)
        (volume.restrict (UnitCube d)))
    (hUbetap_int : Integrable
        (fun x => |u x| ^ betaBar' β)
        (volume.restrict (UnitCube d)))
    (hVbetap_int : Integrable
        (fun x => |V x| ^ betaBar' β)
        (volume.restrict (UnitCube d)))
    (hu_lp_γ : MemLpPer (ENNReal.ofReal (gammaBar α β)) u) :
    ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ gammaBar α β
        ∂(volume : Measure (Fin d → ℝ)) ≤
      aprioriDuBoundClosed_intRaw d α β C0 Vint_bound Vβp_bound := by
  classical
  set γ : ℝ := gammaBar α β with hγ_def
  set βp : ℝ := betaBar' β with hβp_def
  set p : ℝ≥0∞ := ENNReal.ofReal γ with hp_def
  set q : ℝ≥0∞ := ENNReal.ofReal βp with hq_def
  have hβ_pos : 0 < β := hβ
  have hα_one_lt : 1 < α := hα
  have hα_pos : 0 < α := lt_trans zero_lt_one hα_one_lt
  have hβp_pos : 0 < βp := by
    rw [hβp_def]; exact lt_trans zero_lt_one (one_lt_betaBar' β hβ_pos)
  have hβp_one_lt : 1 < βp := by rw [hβp_def]; exact one_lt_betaBar' β hβ_pos
  have hβp_nn : 0 ≤ βp := hβp_pos.le
  have hγ_pos : 0 < γ := by rw [hγ_def]; exact gammaBar_pos α β hα_pos hβ_pos
  have hγ_nn : 0 ≤ γ := hγ_pos.le
  have hγ_ne : γ ≠ 0 := ne_of_gt hγ_pos
  have hγ_eq : γ = α * βp := by
    rw [hγ_def, hβp_def]
    exact gammaBar_eq_alpha_mul_betaBar' α β (ne_of_gt hβ_pos)
  have hβp_lt_γ : βp < γ := by
    rw [hγ_eq]
    have : 1 * βp < α * βp :=
      (mul_lt_mul_iff_of_pos_right hβp_pos).mpr hα_one_lt
    simpa using this
  have hβp_le_γ : βp ≤ γ := hβp_lt_γ.le
  have hcube_vol_lt : (volume.restrict (UnitCube (d := d))) Set.univ < ∞ := by
    rw [Measure.restrict_apply MeasurableSet.univ]; simp
  haveI : IsFiniteMeasure (volume.restrict (UnitCube (d := d))) := ⟨hcube_vol_lt⟩
  set vol : ℝ := (volume (UnitCube (d := d))).toReal with hvol_def
  have hvol_eq_one : vol = 1 := by simp [hvol_def]
  set C₁ : ℝ := aprioriDuPointwiseConstRaw β C0 with hC₁_def
  have hC₁_nn : 0 ≤ C₁ := aprioriDuPointwiseConstRaw_nn β C0 hC0
  have hMbetaBar_int : Integrable (fun x => m x ^ betaBar β)
      (volume.restrict (UnitCube d)) := by
    show Integrable (fun x => m x ^ (β + 1)) _; exact hLB_int
  have hint_bound :=
    apriori_Du_integrated_bound_closed_riderNN_raw
      (d := d) α β C0 hα hβ hC0 hLower hH0 V Du m u hHJB hMnonneg
      hDu_norm_int hMbetaBar_int hUbetap_int hVbetap_int
  set M : ℝ := aprioriMBoundClosed_intRaw β C0 Vint_bound Vβp_bound with hM_def
  have hM_bound :
      ∫ x in UnitCube d, m x ^ (β + 1)
          ∂(volume : Measure (Fin d → ℝ)) ≤ M :=
    apriori_m_bound_young_Vlp_raw (d := d) (H := H) (DpH := DpH)
      α β C0 hα hβ hC0 hLower hH0 V Du m u epsTerms Vint_bound Vβp_bound
      hHJB h_lagr hMnonneg hVβp hVβp_nn hVβp_int hVm_int hV_meas hm_meas hVint hEpsNN
      h_identity hu_int hRHSabove_int hLB_int hM_int hMbeta_int hRHSbelow_int
  set Cu : ℝ := aprioriUBoundClosed_intRaw d β C0 Vint_bound Vβp_bound with hCu_def
  have hCu_nn : 0 ≤ Cu := aprioriUBoundClosed_intRaw_nn β C0 Vint_bound Vβp_bound hC0
  have hu_pw :
      lpNormPer (ENNReal.ofReal (gammaBar α β)) u ≤
        Cu * ((∑ i : Fin d, lpNormPer
              (ENNReal.ofReal (gammaBar α β)) (Du i)) + 1) :=
    apriori_uepsi_Lp_young_Vlp_raw (d := d) (H := H) (DpH := DpH)
      α β C0 hα hβ hC0 hLower hH0 V Du m u epsTerms Vint_bound Vβp_bound
      hHJB h_lagr hMnonneg hVβp hVβp_nn hVβp_int hVm_int hV_meas hm_meas hVint hEpsNN
      h_identity hu_int hRHSabove_int hLB_int hM_int hMbeta_int hRHSbelow_int
      hγ_one_le hγ_top hu_per hu_sob hDu_weak hDu_per hDu_lp
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
    rw [heq, ← Real.rpow_mul hint_nn, inv_mul_cancel₀ hγ_ne, Real.rpow_one]
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
    have : MemLp u q (volume.restrict (UnitCube d)) := hmemL.mono_exponent hq_le_p
    exact MemLp.toMemLpPer this
  have h_int_u_βp :
      ∫ x in UnitCube d, |u x| ^ βp ∂(volume : Measure (Fin d → ℝ))
        = lpNormPer q u ^ βp := by
    have hbridge :=
      StationaryMFG.Solutions.MFG.lpNormPer_eq_integral_rpow
        (p := q) (f := u) hq_ne_zero hq_top hu_lp_q
    rw [hq_toReal] at hbridge
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
    rw [heq2, ← Real.rpow_mul hint_nn', inv_mul_cancel₀ hβp_ne, Real.rpow_one]
  have h_inclusion : lpNormPer q u ≤ lpNormPer p u :=
    lpNormPer_mono_exponent u hu_lp_γ hq_le_p
  have hLpq_nn : 0 ≤ lpNormPer q u := lpNormPer_nonneg q u
  have hLpp_nn : 0 ≤ lpNormPer p u := lpNormPer_nonneg p u
  have h_inclusion_pow :
      lpNormPer q u ^ βp ≤ lpNormPer p u ^ βp :=
    Real.rpow_le_rpow hLpq_nn h_inclusion hβp_nn
  have hu_lpp_le_CuS :
      lpNormPer p u ^ βp ≤ (Cu * (S + 1)) ^ βp :=
    Real.rpow_le_rpow hLpp_nn hu_pw hβp_nn
  have h_int_u_βp_le :
      ∫ x in UnitCube d, |u x| ^ βp ∂(volume : Measure (Fin d → ℝ))
        ≤ (Cu * (S + 1)) ^ βp := by
    rw [h_int_u_βp]; exact le_trans h_inclusion_pow hu_lpp_le_CuS
  have hSp1_nn : 0 ≤ S + 1 := by linarith
  have hCu_pow : (Cu * (S + 1)) ^ βp = Cu ^ βp * (S + 1) ^ βp :=
    Real.mul_rpow hCu_nn hSp1_nn
  have hSplus1_pow_le :
      (S + 1) ^ βp ≤ (2 : ℝ) ^ βp * (S ^ βp + 1 ^ βp) :=
    t3_add_rpow_le_two_rpow_mul hS_nn (by norm_num : (0 : ℝ) ≤ 1) hβp_nn
  have h1pow : (1 : ℝ) ^ βp = 1 := Real.one_rpow _
  have hCu_pow_nn : 0 ≤ Cu ^ βp := Real.rpow_nonneg hCu_nn _
  have h2pow_nn : 0 ≤ (2 : ℝ) ^ βp :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hbetaBar_eq : betaBar β = β + 1 := rfl
  have hM_bound' : ∫ x in UnitCube d, m x ^ betaBar β
      ∂(volume : Measure (Fin d → ℝ)) ≤ M := by
    rw [hbetaBar_eq]; exact hM_bound
  set Im : ℝ := ∫ x in UnitCube d, m x ^ betaBar β
                  ∂(volume : Measure (Fin d → ℝ)) with hIm_def
  set Iu : ℝ := ∫ x in UnitCube d, |u x| ^ betaBar' β
                  ∂(volume : Measure (Fin d → ℝ)) with hIu_def
  set Iv : ℝ := ∫ x in UnitCube d, |V x| ^ betaBar' β
                  ∂(volume : Measure (Fin d → ℝ)) with hIv_def
  have hIu_eq : Iu = ∫ x in UnitCube d, |u x| ^ βp
                  ∂(volume : Measure (Fin d → ℝ)) := rfl
  have hint_bound' :
      T ≤ C₁ * (Im + Iu + Iv + vol) := by
    show ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ γ
            ∂(volume : Measure (Fin d → ℝ)) ≤
          C₁ * (Im + Iu + Iv + vol)
    convert hint_bound using 2
  have hIm_le : Im ≤ M := hM_bound'
  have hIu_le : Iu ≤ (Cu * (S + 1)) ^ βp := h_int_u_βp_le
  have hIv_le : Iv ≤ Vβp_bound := by
    have hIv_eq : Iv = ∫ x in UnitCube d, |V x| ^ ((β + 1) / β)
        ∂(volume : Measure (Fin d → ℝ)) := by
      rw [hIv_def]; rfl
    rw [hIv_eq]; exact hVβp
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
  have hdTinv_nn : (0 : ℝ) ≤ (d : ℝ) * T ^ γ⁻¹ := mul_nonneg hd_nn hT_inv_nn
  have hSpow_le :
      S ^ βp ≤ ((d : ℝ) * T ^ γ⁻¹) ^ βp :=
    Real.rpow_le_rpow hS_nn hS_le hβp_nn
  have hd_T_pow :
      ((d : ℝ) * T ^ γ⁻¹) ^ βp =
        (d : ℝ) ^ βp * (T ^ γ⁻¹) ^ βp :=
    Real.mul_rpow hd_nn hT_inv_nn
  have hT_pow_iter :
      (T ^ γ⁻¹) ^ βp = T ^ (γ⁻¹ * βp) := by rw [← Real.rpow_mul hT_nn]
  set r : ℝ := γ⁻¹ * βp with hr_def
  have hr_pos : 0 < r := by
    rw [hr_def]
    exact mul_pos (inv_pos.mpr hγ_pos) hβp_pos
  have hr_nn : 0 ≤ r := hr_pos.le
  have hr_lt_one : r < 1 := by
    rw [hr_def]
    have hinv_pos : 0 < γ⁻¹ := inv_pos.mpr hγ_pos
    rw [show (1 : ℝ) = γ⁻¹ * γ from by rw [inv_mul_cancel₀ hγ_ne]]
    exact (mul_lt_mul_iff_of_pos_left hinv_pos).mpr hβp_lt_γ
  set A : ℝ := C₁ * (Cu ^ βp * (2 : ℝ) ^ βp * (d : ℝ) ^ βp) with hA_def
  set B : ℝ := C₁ * (M + Cu ^ βp * (2 : ℝ) ^ βp + Vβp_bound + 1) with hB_def
  have hd_pow_nn : 0 ≤ (d : ℝ) ^ βp := Real.rpow_nonneg hd_nn _
  have hA_nn : 0 ≤ A := by
    apply mul_nonneg hC₁_nn
    exact mul_nonneg (mul_nonneg hCu_pow_nn h2pow_nn) hd_pow_nn
  have hB_nn : 0 ≤ B := by
    apply mul_nonneg hC₁_nn
    have hM_nn : 0 ≤ M :=
      aprioriMBoundClosed_intRaw_nn_of_Vint_nn β C0 Vint_bound Vβp_bound hβ_pos hC0
        (by
          have hVint_nn : 0 ≤ ∫ x in UnitCube d, |V x|
              ∂(volume : Measure (Fin d → ℝ)) := by
            apply integral_nonneg_of_ae
            refine Filter.Eventually.of_forall ?_
            intro x; exact abs_nonneg _
          linarith [le_trans hVint_nn hVint])
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
  have hAR_T' : T ^ (1 : ℝ) ≤ A * T ^ r + B := by
    rw [Real.rpow_one]; exact hAR_T
  have hT_le_closed :
      T ≤ (2 * A) ^ (1 / (1 - r)) + (2 * B) ^ (1 / (1 : ℝ)) :=
    apriori_Du_bound_closed T A B 1 r hT_nn hA_nn hB_nn hr_nn hr_lt_one hAR_T'
  have h_2B_pow : (2 * B) ^ (1 / (1 : ℝ)) = 2 * B := by
    rw [show (1 / (1 : ℝ)) = 1 by norm_num, Real.rpow_one]
  have hclosed_eq :
      aprioriDuBoundClosed_intRaw d α β C0 Vint_bound Vβp_bound
        = (2 * A) ^ (1 / (1 - r)) + (2 * B) := by
    show aprioriDuBoundClosed_intRaw d α β C0 Vint_bound Vβp_bound = _
    rfl
  rw [hclosed_eq, ← h_2B_pow]
  exact hT_le_closed

/-- **G6b aggregate (Young, no `L^∞`).** Mirror of
`apriori_aggregate_bound_residue_form_riderNN_aePeriodic_raw`; the three
sub-lemma calls (m-bound, Du-bound, Lp) are the Young-route siblings, so NO
`hVbnd`/L∞; keyed on `aprioriUniformConstantClosed_intRaw`.  The proof skeleton
after the three calls is byte-identical to the shared aggregate. -/
theorem apriori_aggregate_bound_residue_form_young_Vlp_raw
    [AxisMixMeasureHypothesis]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (α β C0 : ℝ) (hα : 1 < α) (hβ : 0 < β) (hC0 : 0 < C0)
    (hLower :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m → H x p m ≥ (‖p‖ ^ α) / C0 - C0 * (m ^ β + 1))
    (hH0 : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
            ∀ p : Fin d → ℝ, ‖p‖ ^ α / C0 - C0 ≤ H x p 0)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u epsTerms : (Fin d → ℝ) → ℝ)
    (Vint_bound Vβp_bound : ℝ)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ β) / C0 - C0 ≤ (DpH x p mx) ⬝ p - H x p mx)
    (hMnonneg : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hVβp :
      ∫ x in UnitCube d, |V x| ^ ((β + 1) / β)
          ∂(volume : Measure (Fin d → ℝ)) ≤ Vβp_bound)
    (hVβp_nn : 0 ≤ Vβp_bound)
    (hVβp_int : Integrable (fun x => |V x| ^ ((β + 1) / β))
                  (volume.restrict (UnitCube d)))
    (hVm_int : Integrable (fun x => |V x| * m x)
                  (volume.restrict (UnitCube d)))
    (hV_meas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hm_meas : AEStronglyMeasurable m (volume.restrict (UnitCube d)))
    (hVint :
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ)) ≤ Vint_bound)
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
              (fun x => |V x| + C0 * (m x ^ β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : Integrable
                (fun x => m x ^ (β + 1)) (volume.restrict (UnitCube d)))
    (hM_int : Integrable m (volume.restrict (UnitCube d)))
    (hMbeta_int : Integrable
                (fun x => m x ^ β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : Integrable
                (fun x =>
                  m x * (-H x (fun i => Du i x) (m x)
                            + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                    + V x * m x
                    + epsTerms x)
                (volume.restrict (UnitCube d)))
    (hγ_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (gammaBar α β))
    (hγ_top : ENNReal.ofReal (gammaBar α β) ≠ ⊤)
    (hu_per : Periodic.AEPeriodic (d := d) u)
    (hu_sob : MemSobolevPer (ENNReal.ofReal (gammaBar α β)) u)
    (hDu_weak : ∀ i, HasWeakDerivPer i u (Du i))
    (hDu_per : ∀ i, Periodic.AEPeriodic (d := d) (Du i))
    (hDu_lp : ∀ i, MemLpPer (ENNReal.ofReal (gammaBar α β)) (Du i))
    (hDu_norm_int : Integrable
        (fun x => ‖(fun i => Du i x)‖ ^ gammaBar α β)
        (volume.restrict (UnitCube d)))
    (hUbetap_int : Integrable
        (fun x => |u x| ^ betaBar' β)
        (volume.restrict (UnitCube d)))
    (hVbetap_int : Integrable
        (fun x => |V x| ^ betaBar' β)
        (volume.restrict (UnitCube d)))
    (hu_lp_γ : MemLpPer (ENNReal.ofReal (gammaBar α β)) u) :
    (∫ x in UnitCube d, |m x| ^ (β + 1)
        ∂(volume : Measure (Fin d → ℝ)))
      + (∫ x in UnitCube d, |u x| ^ gammaBar α β
          ∂(volume : Measure (Fin d → ℝ)))
      + (∑ i : Fin d, ∫ x in UnitCube d, |Du i x| ^ gammaBar α β
          ∂(volume : Measure (Fin d → ℝ)))
        ≤ aprioriUniformConstantClosed_intRaw d α β C0 Vint_bound Vβp_bound := by
  classical
  set γ : ℝ := gammaBar α β with hγ_def
  set p : ℝ≥0∞ := ENNReal.ofReal γ with hp_def
  have hβ_pos : 0 < β := hβ
  have hα_one_lt : 1 < α := hα
  have hα_pos : 0 < α := lt_trans zero_lt_one hα_one_lt
  have hγ_pos : 0 < γ := by rw [hγ_def]; exact gammaBar_pos α β hα_pos hβ_pos
  have hγ_nn : 0 ≤ γ := hγ_pos.le
  have hγ_ne : γ ≠ 0 := ne_of_gt hγ_pos
  have hp_ne_zero : p ≠ 0 := by
    rw [hp_def]; simp [ENNReal.ofReal_eq_zero, not_le.mpr hγ_pos]
  have hp_top : p ≠ ⊤ := by rw [hp_def]; exact ENNReal.ofReal_ne_top
  have hp_toReal : p.toReal = γ := by rw [hp_def]; exact ENNReal.toReal_ofReal hγ_nn
  set M : ℝ := aprioriMBoundClosed_intRaw β C0 Vint_bound Vβp_bound with hM_def
  have hM_bound :
      ∫ x in UnitCube d, m x ^ (β + 1)
          ∂(volume : Measure (Fin d → ℝ)) ≤ M :=
    apriori_m_bound_young_Vlp_raw (d := d) (H := H) (DpH := DpH)
      α β C0 hα hβ hC0 hLower hH0 V Du m u epsTerms Vint_bound Vβp_bound
      hHJB h_lagr hMnonneg hVβp hVβp_nn hVβp_int hVm_int hV_meas hm_meas hVint hEpsNN
      h_identity hu_int hRHSabove_int hLB_int hM_int hMbeta_int hRHSbelow_int
  have hM_abs_eq :
      ∫ x in UnitCube d, |m x| ^ (β + 1)
          ∂(volume : Measure (Fin d → ℝ)) =
      ∫ x in UnitCube d, m x ^ (β + 1)
          ∂(volume : Measure (Fin d → ℝ)) := by
    apply integral_congr_ae
    filter_upwards [hMnonneg] with x hxm
    rw [abs_of_nonneg hxm]
  have hM_abs_le :
      ∫ x in UnitCube d, |m x| ^ (β + 1)
          ∂(volume : Measure (Fin d → ℝ)) ≤ M := by
    rw [hM_abs_eq]; exact hM_bound
  set Cd : ℝ := aprioriDuBoundClosed_intRaw d α β C0 Vint_bound Vβp_bound
    with hCd_def
  have hCd_bound :
      ∫ x in UnitCube d, ‖(fun i => Du i x)‖ ^ γ
          ∂(volume : Measure (Fin d → ℝ)) ≤ Cd :=
    apriori_Du_bound_young_Vlp_raw (d := d) (H := H) (DpH := DpH)
      α β C0 hα hβ hC0 hLower hH0 V Du m u epsTerms Vint_bound Vβp_bound
      hHJB h_lagr hMnonneg hVβp hVβp_nn hVβp_int hVm_int hV_meas hm_meas hVint hEpsNN
      h_identity hu_int hRHSabove_int hLB_int hM_int hMbeta_int hRHSbelow_int
      hγ_one_le hγ_top hu_per hu_sob hDu_weak hDu_per hDu_lp
      hDu_norm_int hUbetap_int hVbetap_int hu_lp_γ
  set Cu : ℝ := aprioriUBoundClosed_intRaw d β C0 Vint_bound Vβp_bound with hCu_def
  have hCu_nn : 0 ≤ Cu := aprioriUBoundClosed_intRaw_nn β C0 Vint_bound Vβp_bound hC0
  have hu_pw :
      lpNormPer p u ≤
        Cu * ((∑ i : Fin d, lpNormPer p (Du i)) + 1) :=
    apriori_uepsi_Lp_young_Vlp_raw (d := d) (H := H) (DpH := DpH)
      α β C0 hα hβ hC0 hLower hH0 V Du m u epsTerms Vint_bound Vβp_bound
      hHJB h_lagr hMnonneg hVβp hVβp_nn hVβp_int hVm_int hV_meas hm_meas hVint hEpsNN
      h_identity hu_int hRHSabove_int hLB_int hM_int hMbeta_int hRHSbelow_int
      hγ_one_le hγ_top hu_per hu_sob hDu_weak hDu_per hDu_lp
  -- From here the skeleton is byte-identical to the shared aggregate.
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
    rw [heq, ← Real.rpow_mul hint_nn, inv_mul_cancel₀ hγ_ne, Real.rpow_one]
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
      rw [hDu_lp_γ i]; exact hDu_i_le_Cd i
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
    rw [heq, ← Real.rpow_mul hint_nn, inv_mul_cancel₀ hγ_ne, Real.rpow_one]
    have hcong :
        (fun x => ‖u x‖ ^ γ) = (fun x => |u x| ^ γ) := by
      funext x; rw [Real.norm_eq_abs]
    rw [show (fun x => ‖u x‖ ^ γ) = (fun x => |u x| ^ γ) from hcong]
  have hu_int_le : ∫ x in UnitCube d, |u x| ^ γ
      ∂(volume : Measure (Fin d → ℝ)) ≤ U ^ γ := by
    rw [← hu_lp_eq]; exact hLpu_γ_le
  unfold aprioriUniformConstantClosed_intRaw
  show (∫ x in UnitCube d, |m x| ^ (β + 1)
        ∂(volume : Measure (Fin d → ℝ)))
      + (∫ x in UnitCube d, |u x| ^ γ
          ∂(volume : Measure (Fin d → ℝ)))
      + (∑ i : Fin d, ∫ x in UnitCube d, |Du i x| ^ γ
          ∂(volume : Measure (Fin d → ℝ)))
        ≤ M + U ^ γ + (d : ℝ) * Cd
  linarith [hM_abs_le, hu_int_le, hSum_Du_le]

/-- **A2g (coercive, exponent-parameterized, Young V-route) — T3 a-priori engine.**

The sole T3 coercive a-priori engine (the former L∞ sibling
`apriori_uniform_bound_of_strongVI_family_coercive_exp` was deleted in G6c once
this Young-route variant superseded it).  V-inputs are ONLY integral data:
`hVint` (∫|V| ≤ Vint_bound), `hVβp` (∫|V|^β̄' ≤ Vβp_bound), `hVbetap_int`,
`hVm_int`, `hV_meas`.  NO pointwise `hVbnd : |V| ≤ Vbound`, NO
`Vbound`/`hVint_int`/`hVintEq` — the m·V pairing is absorbed by the paper's
Young/Hölder argument at `(β̄, β̄')`.  The closed constant is
`aprioriUniformConstantClosed_intRaw`.  Consumed by
`T3RegularizedSideData.of_family`; internally feeds
`apriori_aggregate_bound_residue_form_young_Vlp_raw`. -/
theorem apriori_uniform_bound_of_strongVI_family_coercive_exp_Vlp
    [AxisMixMeasureHypothesis]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {βBarReal γBarReal : ℝ}
    (hHyp : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d)
    (hUB : HdeltaUniformBounds (H := H) (DpH := DpH) hHyp qε)
    (hβBar_eq : βBarReal = hHyp.β + 1)
    (hγBar_eq : γBarReal = gammaBar hHyp.α hHyp.β)
    (V : (Fin d → ℝ) → ℝ)
    (Du : ℝ → Fin d → (Fin d → ℝ) → ℝ)
    (m u epsTerms : ℝ → (Fin d → ℝ) → ℝ)
    (Vint_bound Vβp_bound : ℝ)
    (hVint_nn : 0 ≤ Vint_bound) (hVβp_nn : 0 ≤ Vβp_bound)
    (hmLp : ∀ ε, 0 < ε → ε ≤ 1 → MemLpPer (ENNReal.ofReal βBarReal) (m ε))
    (huSob : ∀ ε, 0 < ε → ε ≤ 1 → MemSobolevPer (ENNReal.ofReal γBarReal) (u ε))
    (hDu_lp : ∀ ε, 0 < ε → ε ≤ 1 → ∀ i, MemLpPer (ENNReal.ofReal γBarReal) (Du ε i))
    (hDu_weak : ∀ ε, 0 < ε → ε ≤ 1 → ∀ i, HasWeakDerivPer i (u ε) (Du ε i))
    (hVI : ∀ ε, 0 < ε → ε ≤ 1 →
      IsStrongVI_Aepsi (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
        V (HdeltaK0 hHyp ε) (DpHepsilonFam hHyp qε ε) γBarReal ε (m ε) (u ε) (Du ε))
    (hmNonneg : ∀ ε, 0 < ε → ε ≤ 1 →
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m ε x)
    (hIndicMemLp :
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (volume.restrict (UnitCube d)) S < ∞ →
        MemLpPer (ENNReal.ofReal βBarReal)
          (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ))))
    (hCont : ∀ ε, 0 < ε → ε ≤ 1 →
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (volume.restrict (UnitCube d)) S < ∞ →
        Filter.Tendsto
          (fun n : ℕ =>
            mfgOperatorEpsPair (V := V) (H := HdeltaK0 hHyp ε)
              (DpH := DpHepsilonFam hHyp qε ε)
              γBarReal ε (Du ε)
              (fun x => m ε x + (1 / ((n : ℝ) + 1)) *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              (u ε)
              (fun _ _ => (0 : ℝ))
              (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)))
              (fun _ => (0 : ℝ)))
          Filter.atTop
          (𝓝 (mfgOperatorEpsPair (V := V) (H := HdeltaK0 hHyp ε)
                (DpH := DpHepsilonFam hHyp qε ε)
                γBarReal ε (Du ε) (m ε) (u ε)
                (fun _ _ => (0 : ℝ))
                (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)))
                (fun _ => (0 : ℝ)))))
    (hRes : ∀ ε, 0 < ε → ε ≤ 1 →
      Integrable (hjbResidual V (HdeltaK0 hHyp ε) (Du ε) (m ε) (u ε))
        (volume.restrict (UnitCube d)))
    (hIdentityRaw : ∀ ε, 0 < ε → ε ≤ 1 →
      ∫ x in UnitCube d, u ε x ∂(volume : Measure (Fin d → ℝ)) =
        ∫ x in UnitCube d,
          ((m ε) x * (-HdeltaK0 hHyp ε x (fun i => (Du ε) i x) ((m ε) x)
                    + (DpHepsilonFam hHyp qε ε x (fun i => (Du ε) i x) ((m ε) x))
                        ⬝ (fun i => (Du ε) i x))
            + V x * (m ε) x
            + epsTerms ε x)
          ∂(volume : Measure (Fin d → ℝ)))
    (hH0 : ∀ ε, 0 < ε → ε ≤ 1 → ∀ᵐ x ∂(volume.restrict (UnitCube d)),
            ∀ p : Fin d → ℝ,
              ‖p‖ ^ hHyp.α / hUB.C0 - hUB.C0
                ≤ HdeltaK0 hHyp ε x p 0)
    (hEpsNN : ∀ ε > 0, ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ epsTerms ε x)
    (hRHSabove_int : ∀ ε, 0 < ε → ε ≤ 1 → Integrable
              (fun x => |V x| + hUB.C0 * ((m ε) x ^ hHyp.β + 1))
              (volume.restrict (UnitCube d)))
    (hLB_int : ∀ ε, 0 < ε → ε ≤ 1 → Integrable
                (fun x => (m ε) x ^ (hHyp.β + 1)) (volume.restrict (UnitCube d)))
    (hMbeta_int : ∀ ε, 0 < ε → ε ≤ 1 → Integrable
                (fun x => (m ε) x ^ hHyp.β) (volume.restrict (UnitCube d)))
    (hRHSbelow_int : ∀ ε, 0 < ε → ε ≤ 1 → Integrable
                (fun x =>
                  m ε x * (-HdeltaK0 hHyp ε x (fun i => (Du ε) i x) ((m ε) x)
                            + (DpHepsilonFam hHyp qε ε x (fun i => (Du ε) i x)
                                  ((m ε) x))
                                ⬝ (fun i => (Du ε) i x))
                    + V x * (m ε) x
                    + epsTerms ε x)
                (volume.restrict (UnitCube d)))
    (hVbetap_int : ∀ ε : ℝ, ε > 0 → Integrable
        (fun x => |V x| ^ betaBar' hHyp.β)
        (volume.restrict (UnitCube d)))
    (hVm_int : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → Integrable (fun x => |V x| * m ε x)
                (volume.restrict (UnitCube d)))
    (hV_meas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hVint : ∀ ε : ℝ, ε > 0 →
      ∫ x in UnitCube d, |V x| ∂(volume : Measure (Fin d → ℝ)) ≤ Vint_bound)
    (hVβp : ∀ ε : ℝ, ε > 0 →
      ∫ x in UnitCube d, |V x| ^ betaBar' hHyp.β
          ∂(volume : Measure (Fin d → ℝ)) ≤ Vβp_bound) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε, 0 < ε → ε ≤ 1 →
      (∫ x in UnitCube d, |m ε x| ^ (ENNReal.ofReal βBarReal).toReal
          ∂(volume : Measure (Fin d → ℝ)))
        + (∫ x in UnitCube d, |u ε x| ^ (ENNReal.ofReal γBarReal).toReal
            ∂(volume : Measure (Fin d → ℝ)))
        + (∑ i : Fin d, ∫ x in UnitCube d,
              |Du ε i x| ^ (ENNReal.ofReal γBarReal).toReal
            ∂(volume : Measure (Fin d → ℝ)))
          ≤ C := by
  classical
  set C0 : ℝ := hUB.C0 with hC0_def
  have hC0_pos : 0 < C0 := hUB.hC0
  have hα₀ : 1 < hHyp.α := hHyp.hα
  have hβ₀ : 0 < hHyp.β := hHyp.hβ
  have hβBar_pos : 0 < βBarReal := by rw [hβBar_eq]; linarith
  have hγBar_pos : 0 < γBarReal := by
    rw [hγBar_eq, gammaBar]
    exact div_pos (mul_pos (lt_trans zero_lt_one hα₀) (by linarith)) hβ₀
  have hγBar_eq_g : γBarReal = gammaBar hHyp.α hHyp.β := hγBar_eq
  have hu_lp_γ : ∀ ε, 0 < ε → ε ≤ 1 →
      MemLpPer (ENNReal.ofReal (gammaBar hHyp.α hHyp.β)) (u ε) := by
    intro ε hε hε1ε; rw [← hγBar_eq_g]; exact (huSob ε hε hε1ε).1
  have hu_sob : ∀ ε, 0 < ε → ε ≤ 1 →
      MemSobolevPer (ENNReal.ofReal (gammaBar hHyp.α hHyp.β)) (u ε) := by
    intro ε hε hε1ε; rw [← hγBar_eq_g]; exact huSob ε hε hε1ε
  have hDu_lp' : ∀ ε, 0 < ε → ε ≤ 1 → ∀ i,
      MemLpPer (ENNReal.ofReal (gammaBar hHyp.α hHyp.β)) (Du ε i) := by
    intro ε hε hε1ε i; rw [← hγBar_eq_g]; exact hDu_lp ε hε hε1ε i
  have hu_per : ∀ ε, 0 < ε → ε ≤ 1 → Periodic.AEPeriodic (d := d) (u ε) :=
    fun ε hε hε1ε => ⟨Periodic.aePeriodicRepOfMemLpPer (d := d) (huSob ε hε hε1ε).1⟩
  have hDu_per : ∀ ε, 0 < ε → ε ≤ 1 → ∀ i, Periodic.AEPeriodic (d := d) (Du ε i) :=
    fun ε hε hε1ε i => ⟨Periodic.aePeriodicRepOfMemLpPer (d := d) (hDu_lp ε hε hε1ε i)⟩
  have hHJB := hHJB_of_strongVI_family hHyp V (DpHepsilonFam hHyp qε) γBarReal
    m u Du hVI hmNonneg hmLp huSob hDu_lp hDu_weak hIndicMemLp hCont hRes
  have hγ_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (gammaBar hHyp.α hHyp.β) := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal (by
      rw [gammaBar]; rw [le_div_iff₀ hβ₀]
      nlinarith [mul_pos (lt_trans zero_lt_one hα₀)
        (show (0:ℝ) < hHyp.β + 1 by linarith)])
  have hγ_top : ENNReal.ofReal (gammaBar hHyp.α hHyp.β) ≠ ⊤ := ENNReal.ofReal_ne_top
  -- The ε-INDEPENDENT closed-form constant.
  refine ⟨aprioriUniformConstantClosed_intRaw d hHyp.α hHyp.β C0 Vint_bound Vβp_bound,
    aprioriUniformConstantClosed_intRaw_nn (d := d) hHyp.α hHyp.β C0 Vint_bound Vβp_bound
      hα₀ hβ₀ hC0_pos hVint_nn hVβp_nn, ?_⟩
  intro ε hε hε1ε
  have h_identity_ε :=
    hIdentity_of_weakGrowth hHyp V (DpHepsilonFam hHyp qε ε) ε (Du ε) (m ε) (u ε)
      (epsTerms ε) (hIdentityRaw ε hε hε1ε)
  have hLower :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mm, 0 < mm →
          HdeltaK0 hHyp ε x p mm
            ≥ (‖p‖ ^ hHyp.α) / C0 - C0 * (mm ^ hHyp.β + 1) := by
    filter_upwards [hUB.lower_uniform ε hε hε1ε] with x hx
    intro p mm hmm
    rw [HdeltaK0_eq_Hdelta_of_pos hHyp hmm]
    exact hx p mm hmm
  have h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ hHyp.β) / C0 - C0
            ≤ (DpHepsilonFam hHyp qε ε x p mx) ⬝ p - HdeltaK0 hHyp ε x p mx := by
    filter_upwards [hUB.lagr_uniform ε hε hε1ε] with x hx
    intro p mx hmx
    rw [HdeltaK0_eq_Hdelta_of_pos hHyp hmx]
    exact hx p mx hmx
  have hDu_norm_int' :
      Integrable (fun x => ‖(fun i => Du ε i x)‖ ^ gammaBar hHyp.α hHyp.β)
        (volume.restrict (UnitCube d)) :=
    hDu_norm_int_of_exp hα₀ hβ₀ (hDu_lp' ε hε hε1ε)
  have hUbetap_int' :
      Integrable (fun x => |u ε x| ^ betaBar' hHyp.β)
        (volume.restrict (UnitCube d)) :=
    hUbetap_int_of_exp hα₀ hβ₀ (hu_lp_γ ε hε hε1ε)
  have hu_int : Integrable (u ε) (volume.restrict (UnitCube d)) :=
    MemLp.integrable hγ_one_le (hu_lp_γ ε hε hε1ε)
  have hm_meas : AEStronglyMeasurable (m ε) (volume.restrict (UnitCube d)) :=
    (hmLp ε hε hε1ε).aestronglyMeasurable
  have hβBar_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal βBarReal := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal (by rw [hβBar_eq]; linarith)
  have hM_int : Integrable (m ε) (volume.restrict (UnitCube d)) :=
    MemLp.integrable hβBar_one_le (hmLp ε hε hε1ε)
  -- `hVβp_int` (aggregate exponent `(β+1)/β`) IS `hVbetap_int` (at `betaBar'`).
  have hVβp_int' : Integrable (fun x => |V x| ^ ((hHyp.β + 1) / hHyp.β))
      (volume.restrict (UnitCube d)) := hVbetap_int ε hε
  have hVβp' :
      ∫ x in UnitCube d, |V x| ^ ((hHyp.β + 1) / hHyp.β)
          ∂(volume : Measure (Fin d → ℝ)) ≤ Vβp_bound := hVβp ε hε
  -- Feed the Young-route raw aggregate.
  have hbound :=
    apriori_aggregate_bound_residue_form_young_Vlp_raw (d := d)
      (H := HdeltaK0 hHyp ε) (DpH := DpHepsilonFam hHyp qε ε)
      hHyp.α hHyp.β C0 hα₀ hβ₀ hC0_pos hLower (hH0 ε hε hε1ε)
      V (Du ε) (m ε) (u ε) (epsTerms ε) Vint_bound Vβp_bound
      (hHJB ε hε hε1ε) h_lagr (hmNonneg ε hε hε1ε)
      hVβp' hVβp_nn hVβp_int' (hVm_int ε hε hε1ε) hV_meas hm_meas (hVint ε hε) (hEpsNN ε hε)
      h_identity_ε hu_int (hRHSabove_int ε hε hε1ε)
      (hLB_int ε hε hε1ε) hM_int (hMbeta_int ε hε hε1ε) (hRHSbelow_int ε hε hε1ε)
      hγ_one_le hγ_top (hu_per ε hε hε1ε) (hu_sob ε hε hε1ε) (hDu_weak ε hε hε1ε)
      (hDu_per ε hε hε1ε) (hDu_lp' ε hε hε1ε) hDu_norm_int' hUbetap_int'
      (hVbetap_int ε hε) (hu_lp_γ ε hε hε1ε)
  have hβtoReal : (ENNReal.ofReal βBarReal).toReal = hHyp.β + 1 := by
    rw [ENNReal.toReal_ofReal hβBar_pos.le, hβBar_eq]
  have hγtoReal : (ENNReal.ofReal γBarReal).toReal = gammaBar hHyp.α hHyp.β := by
    rw [ENNReal.toReal_ofReal hγBar_pos.le, hγBar_eq_g]
  rw [hβtoReal, hγtoReal]
  exact hbound

/-- **Anti-sham composability witness (A2g).**

The `∃ C` uniform bound produced by `apriori_uniform_bound_of_strongVI_family`
is in *exactly* the fixed-exponent closed-real shape that the compactness
producer `t3WeakCompactnessUpstreamPack_of_uniformBound_pinned_full`
consumes as its `hbound` field (`Compactness.lean:1725`): for the pack
exponents `betaBar := ENNReal.ofReal βBarReal`,
`gammaBar := ENNReal.ofReal γBarReal`, and a regularising sequence
`ε : ℕ → ℝ` of positive parameters, the per-`n` realisations
`m' n := m (ε n)`, `u' n := u (ε n)`, `Du' n := Du (ε n)` satisfy

```
∀ n, (∫|m' n|^betaBar.toReal) + (∫|u' n|^gammaBar.toReal)
       + (∑ i, ∫|Du' n i|^gammaBar.toReal) ≤ C
```

This lemma derives that `hbound`-shaped statement from the A2g aggregator
output, with no further analytic content — confirming the wiring is
literally type-compatible with the compactness consumer (which itself
lives in the sibling `Compactness` module; we reproduce the field's exact
type here to avoid an import edge). -/
theorem hbound_seq_of_apriori_uniform_bound_of_strongVI_family
    {βBarReal γBarReal C : ℝ} (hC_nn : 0 ≤ C)
    {m u : ℝ → (Fin d → ℝ) → ℝ} {Du : ℝ → Fin d → (Fin d → ℝ) → ℝ}
    (hbound : ∀ ε, 0 < ε → ε ≤ 1 →
      (∫ x in UnitCube d, |m ε x| ^ (ENNReal.ofReal βBarReal).toReal
          ∂(volume : Measure (Fin d → ℝ)))
        + (∫ x in UnitCube d, |u ε x| ^ (ENNReal.ofReal γBarReal).toReal
            ∂(volume : Measure (Fin d → ℝ)))
        + (∑ i : Fin d, ∫ x in UnitCube d,
              |Du ε i x| ^ (ENNReal.ofReal γBarReal).toReal
            ∂(volume : Measure (Fin d → ℝ)))
          ≤ C)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hε1 : ∀ n, ε n ≤ 1) :
    ∀ n : ℕ,
      (∫ x in UnitCube d, |m (ε n) x| ^ (ENNReal.ofReal βBarReal).toReal)
        + (∫ x in UnitCube d, |u (ε n) x| ^ (ENNReal.ofReal γBarReal).toReal)
        + (∑ i, ∫ x in UnitCube d,
              |Du (ε n) i x| ^ (ENNReal.ofReal γBarReal).toReal)
          ≤ C :=
  fun n => hbound (ε n) (hε n) (hε1 n)

end A2fUniform

end InfimalConvolution
end Theorems
end StationaryMFG

end
