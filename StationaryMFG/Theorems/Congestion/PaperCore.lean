module

public import StationaryMFG.Hamiltonian.Assumptions

@[expose] public section

/-!
# Internal congestion interface without a zero-flux restriction

This interface preserves the implementation's convenient globally measurable
representatives while allowing the paper's general continuous limiting flux.
The paper-facing bundle is constructed separately from positive-mass data.
Old restricted bundles have a forgetful coercion, preserving their callers.
-/

namespace StationaryMFG.Hamiltonian

open MeasureTheory Filter Set Topology StationaryMFG.Periodic
open scoped StationaryMFG.Hamiltonian

variable {d : ℕ}

/-- The implementation flux interface, without a zero-at-vacuum premise. -/
structure CongestionFluxCore
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)) : Prop where
  /-- For `m > 0`, the extension `J` agrees with `m · D_pH`. -/
  J_of_pos : ∀ x p m, 0 < m → J x p m = m • DpH x p m
  /-- For a.e. `x ∈ 𝕋^d` and every `p ∈ ℝ^d`, `m · D_pH(x, p, m) → J(x, p, 0)`
  as `m → 0⁺`. -/
  tendsto_at_zero :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p : Fin d → ℝ,
      Tendsto (fun m : ℝ => m • DpH x p m)
        (𝓝[>] (0 : ℝ)) (𝓝 (J x p 0))
  /-- For a.e. `x`, `(p, m) ↦ J(x, p, m)` is jointly continuous on
  the closed half-line `{(p, m) | m ≥ 0}`. -/
  continuous_J :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ContinuousOn (fun (pm : (Fin d → ℝ) × ℝ) => J x pm.1 pm.2)
        {pm | 0 ≤ pm.2}
  /-- Joint `x`-measurability of the extension `J`. This is a
  paper-faithful regularity clause (mirrors `RegularityH.measurable_DpH`):
  `J` is continuous in `(p, m)` a.e. `x` and is integrated against test
  functions, so the paper implicitly requires `x`-measurability. -/
  measurable_J : Measurable (fun (xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ) =>
    J xpm.1 xpm.2.1 xpm.2.2)

/-- Growth and representative data used internally by the congestion proof. -/
structure CongestionGrowthCore
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    extends RegularityH H DpH where
  /-- The growth constant `C > 0` from the paper. -/
  C : ℝ
  /-- The momentum growth exponent `α > 1` from the paper. -/
  α : ℝ
  /-- The mass growth exponent `β > 0` from the paper. -/
  β : ℝ
  /-- The congestion exponent `τ ∈ [0, 1]` from the paper. -/
  τ : ℝ
  /-- Strict positivity of the growth constant `C`. -/
  hC : 0 < C
  /-- Strict super-linearity of the momentum exponent `α`. -/
  hα : 1 < α
  /-- Strict positivity of the mass exponent `β`. -/
  hβ : 0 < β
  /-- Bounds on the congestion exponent `τ ∈ [0, 1]`. -/
  hτ : 0 ≤ τ ∧ τ ≤ 1
  /-- The bundled `(a:mDpHat0)` hypothesis: the extension `J` of
  `m · D_pH` to `m = 0` is well-formed (limit exists and matches `J`
  on `m > 0`, and `J` is jointly continuous on `{(p, m) | m ≥ 0}`). -/
  mDpHat0 : CongestionFluxCore DpH J
  /-- (eq:assH.upper.congestion) `H(x, 0, m) ≤ -m^β / C + C` for `m > 0`. -/
  upper :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ m, 0 < m → H x (0 : Fin d → ℝ) m ≤ -(m ^ β) / C + C
  /-- (eq:assH.DpH.upper.congestion)
  `‖D_pH(x, p, m)‖ ≤ C (1/m + 1/m^τ) ‖p‖^{α(1+τ/β) − 1}
                    + C (m^{β − β/α} + 1/m)` for `m > 0`. -/
  DpH_upper :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p m, 0 < m →
        ‖DpH x p m‖
          ≤ C * ((1 / m) + (1 / m ^ τ)) * (‖p‖ ^ (α * (1 + τ / β) - 1))
            + C * ((m ^ (β - β / α)) + 1 / m)
  /-- (eq:assH.lower.congestion)
  `H(x, p, m) ≥ (1/C) (1/(m^τ + 1)) ‖p‖^{α(1+τ/β)}
              − C (m^β + 1)` for `m > 0`. -/
  lower :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p m, 0 < m →
        H x p m
          ≥ (1 / C) * (1 / (m ^ τ + 1)) * (‖p‖ ^ (α * (1 + τ / β)))
            - C * (m ^ β + 1)


/-- Forget the checkpoint's global zero-flux restriction. -/
abbrev HypothesismDpHat0.toCongestionFluxCore
    {DpH J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesismDpHat0 DpH J) : CongestionFluxCore DpH J where
  J_of_pos := h.J_of_pos
  tendsto_at_zero := h.tendsto_at_zero
  continuous_J := h.continuous_J
  measurable_J := h.measurable_J

instance {DpH J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)} :
    Coe (HypothesismDpHat0 DpH J) (CongestionFluxCore DpH J) :=
  ⟨HypothesismDpHat0.toCongestionFluxCore⟩

/-- Forget the checkpoint's global zero-flux restriction, preserving constants. -/
abbrev HypothesisCongestionGrowth.toCongestionGrowthCore
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisCongestionGrowth H DpH J) : CongestionGrowthCore H DpH J where
  toRegularityH := h.toRegularityH
  C := h.C
  α := h.α
  β := h.β
  τ := h.τ
  hC := h.hC
  hα := h.hα
  hβ := h.hβ
  hτ := h.hτ
  mDpHat0 := h.mDpHat0
  upper := h.upper
  DpH_upper := h.DpH_upper
  lower := h.lower

instance {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)} :
    Coe (HypothesisCongestionGrowth H DpH J) (CongestionGrowthCore H DpH J) :=
  ⟨HypothesisCongestionGrowth.toCongestionGrowthCore⟩

lemma CongestionFluxCore.aemeasurable_J_comp
    {DpH J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hJ : CongestionFluxCore (d := d) DpH J)
    {p : (Fin d → ℝ) → (Fin d → ℝ)} {m : (Fin d → ℝ) → ℝ}
    (hp : AEMeasurable p (volume.restrict (UnitCube d)))
    (hm : AEMeasurable m (volume.restrict (UnitCube d))) :
    AEMeasurable (fun x => J x (p x) (m x)) (volume.restrict (UnitCube d)) :=
  hJ.measurable_J.comp_aemeasurable (aemeasurable_id.prodMk (hp.prodMk hm))


private lemma two_mul_rpow_pow_add_one_ge
    {m β τ : ℝ} (hm : 0 < m) (hβ : 0 < β) (hτ : 0 ≤ τ) :
    m ^ τ + 1 ≤ 2 * (m ^ β + 1) ^ (τ / β) := by
  have hβ_ne : β ≠ 0 := ne_of_gt hβ
  have hmβ_nonneg : (0 : ℝ) ≤ m ^ β := Real.rpow_nonneg hm.le _
  have hsum_pos : (0 : ℝ) < m ^ β + 1 := by linarith
  have hsum_nonneg : (0 : ℝ) ≤ m ^ β + 1 := hsum_pos.le
  have htbβ_nonneg : (0 : ℝ) ≤ τ / β := div_nonneg hτ (le_of_lt hβ)
  rcases le_or_gt m 1 with hm1 | hm1
  · -- `m ≤ 1`: then `m^τ ≤ 1`, so `m^τ + 1 ≤ 2 ≤ 2 (m^β+1)^(τ/β)`
    -- (using `(m^β+1)^(τ/β) ≥ 1` since `m^β+1 ≥ 1`).
    have hmτ_le_one : m ^ τ ≤ 1 := Real.rpow_le_one hm.le hm1 hτ
    have hbase_ge_one : (1 : ℝ) ≤ m ^ β + 1 := by linarith
    have hpow_ge_one : (1 : ℝ) ≤ (m ^ β + 1) ^ (τ / β) :=
      Real.one_le_rpow hbase_ge_one htbβ_nonneg
    linarith
  · -- `m ≥ 1`: then `m^β ≥ 1`, hence `(m^β + 1)^(τ/β) ≥ (m^β)^(τ/β) = m^τ`,
    -- and we use `m^τ ≥ 1` to conclude `m^τ + 1 ≤ 2 m^τ ≤ 2 (m^β+1)^(τ/β)`.
    have hm_ge_one : (1 : ℝ) ≤ m := hm1.le
    have hmβ_ge_one : (1 : ℝ) ≤ m ^ β := Real.one_le_rpow hm_ge_one hβ.le
    have hmτ_ge_one : (1 : ℝ) ≤ m ^ τ := Real.one_le_rpow hm_ge_one hτ
    -- Bound `(m^β + 1)^(τ/β) ≥ (m^β)^(τ/β) = m^(β·(τ/β)) = m^τ`.
    have hmono :
        (m ^ β) ^ (τ / β) ≤ (m ^ β + 1) ^ (τ / β) :=
      Real.rpow_le_rpow hmβ_nonneg (by linarith) htbβ_nonneg
    have hexp_eq : β * (τ / β) = τ := by
      field_simp
    have hpow_compose : (m ^ β) ^ (τ / β) = m ^ τ := by
      rw [← Real.rpow_mul hm.le β (τ / β), hexp_eq]
    have hge : m ^ τ ≤ (m ^ β + 1) ^ (τ / β) := by
      rw [← hpow_compose]; exact hmono
    linarith

lemma paperCore_young_congestion_to_weak
    {a m α β τ : ℝ} (ha : 0 ≤ a) (hm : 0 < m)
    (hα : 0 < α) (hβ : 0 < β) (hτ : 0 ≤ τ) :
    a ^ α / 2 ^ (β / (β + τ))
      ≤ a ^ (α * (1 + τ / β)) / (m ^ τ + 1) + (m ^ β + 1) := by
  -- Set up basic positivity facts.
  have hβτ_pos : 0 < β + τ := by linarith
  have hβτ_ne : β + τ ≠ 0 := ne_of_gt hβτ_pos
  have hβ_ne : β ≠ 0 := ne_of_gt hβ
  have hβτ_β_nonneg : (0 : ℝ) ≤ β / (β + τ) := div_nonneg hβ.le hβτ_pos.le
  have hβτ_τ_nonneg : (0 : ℝ) ≤ τ / (β + τ) := div_nonneg hτ hβτ_pos.le
  have hweights : β / (β + τ) + τ / (β + τ) = 1 := by
    field_simp
  have hmβ_nonneg : (0 : ℝ) ≤ m ^ β := Real.rpow_nonneg hm.le _
  have hmτ_nonneg : (0 : ℝ) ≤ m ^ τ := Real.rpow_nonneg hm.le _
  have hmτ1_pos : (0 : ℝ) < m ^ τ + 1 := by linarith
  have hmβ1_pos : (0 : ℝ) < m ^ β + 1 := by linarith
  have hmτ1_nonneg : (0 : ℝ) ≤ m ^ τ + 1 := hmτ1_pos.le
  have hmβ1_nonneg : (0 : ℝ) ≤ m ^ β + 1 := hmβ1_pos.le
  -- Define the abbreviations `A`, `B` from the paper's argument.
  set A : ℝ := a ^ (α * (1 + τ / β)) / (m ^ τ + 1) with hA
  set B : ℝ := m ^ β + 1 with hB
  have hA_nonneg : 0 ≤ A := by
    apply div_nonneg
    · exact Real.rpow_nonneg ha _
    · exact hmτ1_nonneg
  have hB_nonneg : 0 ≤ B := hmβ1_nonneg
  -- Weighted AM-GM: `A^(β/(β+τ)) * B^(τ/(β+τ)) ≤ (β/(β+τ))·A + (τ/(β+τ))·B`.
  have hamgm : A ^ (β / (β + τ)) * B ^ (τ / (β + τ))
      ≤ β / (β + τ) * A + τ / (β + τ) * B :=
    Real.geom_mean_le_arith_mean2_weighted hβτ_β_nonneg hβτ_τ_nonneg
      hA_nonneg hB_nonneg hweights
  -- Compute `A^(β/(β+τ)) = a^α / (m^τ+1)^(β/(β+τ))`.
  have hA_pow : A ^ (β / (β + τ)) = a ^ α / (m ^ τ + 1) ^ (β / (β + τ)) := by
    have hnum_nonneg : (0 : ℝ) ≤ a ^ (α * (1 + τ / β)) := Real.rpow_nonneg ha _
    rw [hA, Real.div_rpow hnum_nonneg hmτ1_nonneg]
    congr 1
    -- `(a^(α(1+τ/β)))^(β/(β+τ)) = a^(α(1+τ/β) · β/(β+τ)) = a^α`.
    rw [← Real.rpow_mul ha]
    congr 1
    -- Show `α(1+τ/β) · β/(β+τ) = α`.
    have hkey : (1 + τ / β) * (β / (β + τ)) = 1 := by
      field_simp
    have : α * (1 + τ / β) * (β / (β + τ)) = α * ((1 + τ / β) * (β / (β + τ))) := by
      ring
    rw [this, hkey, mul_one]
  -- Bound `β/(β+τ) * A + τ/(β+τ) * B ≤ A + B`, since both weights are `≤ 1`
  -- and `A, B ≥ 0`.
  have hweight_le : β / (β + τ) * A + τ / (β + τ) * B ≤ A + B := by
    have h1 : β / (β + τ) * A ≤ A := by
      have hβτ_β_le : β / (β + τ) ≤ 1 := by
        rw [div_le_one hβτ_pos]; linarith
      nlinarith
    have h2 : τ / (β + τ) * B ≤ B := by
      have hβτ_τ_le : τ / (β + τ) ≤ 1 := by
        rw [div_le_one hβτ_pos]; linarith
      nlinarith
    linarith
  -- So we have: `A^(β/(β+τ)) * B^(τ/(β+τ)) ≤ A + B`,
  -- i.e. `a^α * B^(τ/(β+τ)) / (m^τ+1)^(β/(β+τ)) ≤ A + B`.
  have hcombined : a ^ α / (m ^ τ + 1) ^ (β / (β + τ)) * B ^ (τ / (β + τ))
      ≤ A + B := by
    rw [← hA_pow]
    linarith
  -- Now we want to bound `a^α / 2^(β/(β+τ)) ≤ a^α * B^(τ/(β+τ)) / (m^τ+1)^(β/(β+τ))`.
  -- Use the auxiliary inequality `(m^τ+1) ≤ 2·(m^β+1)^(τ/β)`, raised to `β/(β+τ)`:
  --   `(m^τ+1)^(β/(β+τ)) ≤ 2^(β/(β+τ)) · (m^β+1)^(τ/(β+τ))`.
  have hkey_aux : m ^ τ + 1 ≤ 2 * (m ^ β + 1) ^ (τ / β) :=
    two_mul_rpow_pow_add_one_ge hm hβ hτ
  -- Raise to the power `β/(β+τ) ≥ 0`:
  have hpow_aux :
      (m ^ τ + 1) ^ (β / (β + τ))
        ≤ (2 * (m ^ β + 1) ^ (τ / β)) ^ (β / (β + τ)) :=
    Real.rpow_le_rpow hmτ1_nonneg hkey_aux hβτ_β_nonneg
  -- Expand the RHS: `(2 · (m^β+1)^(τ/β))^(β/(β+τ))
  --     = 2^(β/(β+τ)) · ((m^β+1)^(τ/β))^(β/(β+τ))
  --     = 2^(β/(β+τ)) · (m^β+1)^(τ/β · β/(β+τ))
  --     = 2^(β/(β+τ)) · (m^β+1)^(τ/(β+τ))`.
  have hpow_expand : (2 * (m ^ β + 1) ^ (τ / β)) ^ (β / (β + τ))
      = 2 ^ (β / (β + τ)) * (m ^ β + 1) ^ (τ / (β + τ)) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
          (Real.rpow_nonneg hmβ1_nonneg _)]
    congr 1
    rw [← Real.rpow_mul hmβ1_nonneg]
    congr 1
    field_simp
  -- So `(m^τ+1)^(β/(β+τ)) ≤ 2^(β/(β+τ)) · (m^β+1)^(τ/(β+τ))`.
  have hpow_aux' :
      (m ^ τ + 1) ^ (β / (β + τ))
        ≤ 2 ^ (β / (β + τ)) * (m ^ β + 1) ^ (τ / (β + τ)) := by
    rw [← hpow_expand]; exact hpow_aux
  -- Strict positivity facts for the divisions.
  have hmτ1pow_pos : (0 : ℝ) < (m ^ τ + 1) ^ (β / (β + τ)) :=
    Real.rpow_pos_of_pos hmτ1_pos _
  have h2pow_pos : (0 : ℝ) < (2 : ℝ) ^ (β / (β + τ)) :=
    Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
  have hBpow_nonneg : (0 : ℝ) ≤ B ^ (τ / (β + τ)) := Real.rpow_nonneg hB_nonneg _
  have hBpow_pos : (0 : ℝ) < B ^ (τ / (β + τ)) :=
    Real.rpow_pos_of_pos (by linarith) _
  -- Now: `a^α / 2^(β/(β+τ)) ≤ a^α · (m^β+1)^(τ/(β+τ)) / (m^τ+1)^(β/(β+τ))`.
  -- Equivalently: `a^α · (m^τ+1)^(β/(β+τ)) ≤ a^α · 2^(β/(β+τ)) · (m^β+1)^(τ/(β+τ))`,
  -- which follows from `hpow_aux'` multiplied by `a^α ≥ 0`.
  have ha_α_nonneg : (0 : ℝ) ≤ a ^ α := Real.rpow_nonneg ha _
  have hmul_aux : a ^ α * (m ^ τ + 1) ^ (β / (β + τ))
      ≤ a ^ α * (2 ^ (β / (β + τ)) * (m ^ β + 1) ^ (τ / (β + τ))) :=
    mul_le_mul_of_nonneg_left hpow_aux' ha_α_nonneg
  -- Divide both sides by `2^(β/(β+τ)) · (m^τ+1)^(β/(β+τ)) > 0`.
  have hdenom_pos : 0 < 2 ^ (β / (β + τ)) * (m ^ τ + 1) ^ (β / (β + τ)) :=
    mul_pos h2pow_pos hmτ1pow_pos
  -- Equivalent rearrangement:
  -- `a^α / 2^(β/(β+τ)) ≤ a^α · (m^β+1)^(τ/(β+τ)) / (m^τ+1)^(β/(β+τ))`.
  have hstep1 :
      a ^ α / 2 ^ (β / (β + τ))
        ≤ a ^ α * (m ^ β + 1) ^ (τ / (β + τ)) / (m ^ τ + 1) ^ (β / (β + τ)) := by
    rw [div_le_div_iff₀ h2pow_pos hmτ1pow_pos]
    nlinarith [hmul_aux, ha_α_nonneg, h2pow_pos.le, hmτ1pow_pos.le, hBpow_nonneg]
  -- Combine with `hcombined`:
  -- `a^α · (m^β+1)^(τ/(β+τ)) / (m^τ+1)^(β/(β+τ)) ≤ A + B`.
  have hstep2 :
      a ^ α * (m ^ β + 1) ^ (τ / (β + τ)) / (m ^ τ + 1) ^ (β / (β + τ))
        ≤ A + B := by
    -- `B = m^β + 1` (definitional via `set`), so the LHS coincides with
    -- `a^α / (m^τ+1)^(β/(β+τ)) * B^(τ/(β+τ))`.
    have heq : a ^ α / (m ^ τ + 1) ^ (β / (β + τ)) * B ^ (τ / (β + τ))
        = a ^ α * (m ^ β + 1) ^ (τ / (β + τ))
            / (m ^ τ + 1) ^ (β / (β + τ)) := by
      show a ^ α / (m ^ τ + 1) ^ (β / (β + τ)) * (m ^ β + 1) ^ (τ / (β + τ))
        = a ^ α * (m ^ β + 1) ^ (τ / (β + τ))
            / (m ^ τ + 1) ^ (β / (β + τ))
      ring
    linarith [heq ▸ hcombined]
  linarith


noncomputable def CongestionGrowthCore.toWeakGrowth
    {d : ℕ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionGrowthCore (d := d) H DpH J) :
    HypothesisWeakGrowth (d := d) H DpH := by
  -- Abbreviations to keep the proof readable.
  set C' : ℝ := h.C * 2 ^ (h.β / (h.β + h.τ)) + h.C + 1 / h.C with hC'_def
  have hC_pos := h.hC
  have hβ_pos := h.hβ
  have hτ_nonneg : 0 ≤ h.τ := h.hτ.1
  have hβτ_pos : 0 < h.β + h.τ := by linarith
  have h2pow_pos : (0 : ℝ) < (2 : ℝ) ^ (h.β / (h.β + h.τ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have h2pow_ge_one : (1 : ℝ) ≤ (2 : ℝ) ^ (h.β / (h.β + h.τ)) := by
    have hexp_nonneg : (0 : ℝ) ≤ h.β / (h.β + h.τ) :=
      div_nonneg hβ_pos.le hβτ_pos.le
    exact Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2) hexp_nonneg
  have hC'_pos : 0 < C' := by
    have h1 : 0 < h.C * 2 ^ (h.β / (h.β + h.τ)) := mul_pos hC_pos h2pow_pos
    have h2 : 0 < 1 / h.C := by positivity
    linarith
  -- The dominance facts we need:
  have hC_le_C' : h.C ≤ C' := by
    have hpos1 : 0 ≤ h.C * 2 ^ (h.β / (h.β + h.τ)) - h.C := by
      have : h.C ≤ h.C * 2 ^ (h.β / (h.β + h.τ)) := by
        have := mul_le_mul_of_nonneg_left h2pow_ge_one hC_pos.le
        linarith
      linarith
    have hpos2 : 0 ≤ 1 / h.C := by positivity
    linarith
  -- Bound function for `D_pH` (continuous on `{m > 0}`).
  -- `f(p, m) = h.C · (1/m + 1/m^τ) · ‖p‖^(α(1+τ/β)−1)
  --           + h.C · (m^(β−β/α) + 1/m)`.
  let f : (Fin d → ℝ) → ℝ → ℝ := fun p m =>
    h.C * (1 / m + 1 / m ^ h.τ) * ‖p‖ ^ (h.α * (1 + h.τ / h.β) - 1)
      + h.C * (m ^ (h.β - h.β / h.α) + 1 / m)
  have hα_pos : 0 < h.α := lt_trans zero_lt_one h.hα
  have hf_continuous :
      ContinuousOn (fun pm : (Fin d → ℝ) × ℝ => f pm.1 pm.2)
        {pm | 0 < pm.2} := by
    -- Positive-exponent facts.
    have hexp_p_nonneg : (0 : ℝ) ≤ h.α * (1 + h.τ / h.β) - 1 := by
      have hτβ_nonneg : (0 : ℝ) ≤ h.τ / h.β := div_nonneg hτ_nonneg hβ_pos.le
      have h1τβ_ge_one : (1 : ℝ) ≤ 1 + h.τ / h.β := by linarith
      have hα_ge_one : (1 : ℝ) ≤ h.α := h.hα.le
      have : (1 : ℝ) ≤ h.α * (1 + h.τ / h.β) := by
        have := mul_le_mul hα_ge_one h1τβ_ge_one (by norm_num) (by linarith)
        linarith
      linarith
    have hexp_m_nonneg : (0 : ℝ) ≤ h.β - h.β / h.α := by
      have hα_gt_one := h.hα
      have : h.β / h.α < h.β := by
        rw [div_lt_iff₀ hα_pos]
        nlinarith [hβ_pos, hα_gt_one]
      linarith
    -- The ingredients, all continuous on the relevant domain:
    -- `m ↦ 1/m`, continuous on `{m > 0} ⊆ {m ≠ 0}`.
    have h_inv_m : ContinuousOn (fun pm : (Fin d → ℝ) × ℝ => 1 / pm.2)
        {pm | 0 < pm.2} := by
      refine ContinuousOn.div continuousOn_const continuous_snd.continuousOn ?_
      intro pm hpm; exact ne_of_gt hpm
    -- `m ↦ m^τ`, continuous on all of ℝ since `τ ≥ 0`.
    have h_pow_τ : Continuous (fun pm : (Fin d → ℝ) × ℝ => pm.2 ^ h.τ) :=
      (Real.continuous_rpow_const hτ_nonneg).comp continuous_snd
    -- `m ↦ 1/m^τ`, continuous on `{m > 0}` since `m^τ > 0` for `m > 0`.
    have h_inv_powτ : ContinuousOn
        (fun pm : (Fin d → ℝ) × ℝ => 1 / pm.2 ^ h.τ)
        {pm | 0 < pm.2} := by
      refine ContinuousOn.div continuousOn_const h_pow_τ.continuousOn ?_
      intro pm hpm
      have hm : 0 < pm.2 := hpm
      exact ne_of_gt (Real.rpow_pos_of_pos hm _)
    -- `1/m + 1/m^τ`.
    have h_invsum : ContinuousOn
        (fun pm : (Fin d → ℝ) × ℝ => 1 / pm.2 + 1 / pm.2 ^ h.τ)
        {pm | 0 < pm.2} := h_inv_m.add h_inv_powτ
    -- `‖p‖^(α(1+τ/β)−1)`, continuous on all of ℝ^d × ℝ since the exponent ≥ 0.
    have h_p_pow : Continuous
        (fun pm : (Fin d → ℝ) × ℝ =>
          ‖pm.1‖ ^ (h.α * (1 + h.τ / h.β) - 1)) :=
      (Real.continuous_rpow_const hexp_p_nonneg).comp
        ((continuous_norm).comp continuous_fst)
    -- `m^(β−β/α)`, continuous on all of ℝ since the exponent ≥ 0.
    have h_m_pow : Continuous
        (fun pm : (Fin d → ℝ) × ℝ => pm.2 ^ (h.β - h.β / h.α)) :=
      (Real.continuous_rpow_const hexp_m_nonneg).comp continuous_snd
    -- Term 1: `h.C · (1/m + 1/m^τ) · ‖p‖^(α(1+τ/β)−1)`.
    have h_term1 : ContinuousOn
        (fun pm : (Fin d → ℝ) × ℝ =>
          h.C * (1 / pm.2 + 1 / pm.2 ^ h.τ)
            * ‖pm.1‖ ^ (h.α * (1 + h.τ / h.β) - 1))
        {pm | 0 < pm.2} :=
      (continuousOn_const.mul h_invsum).mul h_p_pow.continuousOn
    -- Term 2: `h.C · (m^(β−β/α) + 1/m)`.
    have h_term2 : ContinuousOn
        (fun pm : (Fin d → ℝ) × ℝ =>
          h.C * (pm.2 ^ (h.β - h.β / h.α) + 1 / pm.2))
        {pm | 0 < pm.2} :=
      continuousOn_const.mul (h_m_pow.continuousOn.add h_inv_m)
    exact h_term1.add h_term2
  -- Now construct the weak-growth bundle.
  refine
    { periodic_H := h.periodic_H
      periodic_DpH := h.periodic_DpH
      measurable_H := h.measurable_H
      measurable_DpH := h.measurable_DpH
      continuous_H_pm := h.continuous_H_pm
      continuous_DpH_pm := h.continuous_DpH_pm
      C := C'
      α := h.α
      β := h.β
      hC := hC'_pos
      hα := h.hα
      hβ := h.hβ
      f := f
      hf_continuous := hf_continuous
      upper := ?_
      DpH_upper := ?_
      lower := ?_ }
  · -- Upper: `H(x, 0, m) ≤ -m^β/h.C + h.C ≤ -m^β/C' + C'`,
    -- using `h.C ≤ C'` and `m^β ≥ 0`, `0 < h.C`.
    filter_upwards [h.upper] with x hx m hm
    have hupper := hx m hm
    have hpow_nonneg : (0 : ℝ) ≤ m ^ h.β := Real.rpow_nonneg hm.le _
    have hdiv_le : m ^ h.β / C' ≤ m ^ h.β / h.C :=
      div_le_div_of_nonneg_left hpow_nonneg hC_pos hC_le_C'
    have hslack : -(m ^ h.β) / h.C + h.C ≤ -(m ^ h.β) / C' + C' := by
      have hneg1 : -(m ^ h.β) / h.C = -(m ^ h.β / h.C) := by ring
      have hneg2 : -(m ^ h.β) / C' = -(m ^ h.β / C') := by ring
      rw [hneg1, hneg2]; linarith
    linarith
  · -- DpH bound: just unfold `f` to match the congestion bound exactly.
    filter_upwards [h.DpH_upper] with x hx p m hm
    exact hx p m hm
  · -- Lower: combine the congestion lower bound with the Young-type inequality
    -- to obtain the weak lower bound.
    filter_upwards [h.lower] with x hx p m hm
    have hlow := hx p m hm
    have hp_nonneg : (0 : ℝ) ≤ ‖p‖ := norm_nonneg _
    have hα_pos : 0 < h.α := lt_trans zero_lt_one h.hα
    -- Apply the Young-type inequality at `a = ‖p‖`, `(m, α, β, τ) = (m, h.α, h.β, h.τ)`.
    have hyoung := paperCore_young_congestion_to_weak (a := ‖p‖) (m := m) (α := h.α)
      (β := h.β) (τ := h.τ) hp_nonneg hm hα_pos hβ_pos hτ_nonneg
    -- Multiply by `1/h.C > 0`:
    have hC_inv_pos : 0 < 1 / h.C := by positivity
    have hyoung_scaled :
        (1 / h.C) * (‖p‖ ^ h.α / 2 ^ (h.β / (h.β + h.τ)))
          ≤ (1 / h.C) * (‖p‖ ^ (h.α * (1 + h.τ / h.β)) / (m ^ h.τ + 1)
                          + (m ^ h.β + 1)) :=
      mul_le_mul_of_nonneg_left hyoung hC_inv_pos.le
    -- Rewrite the LHS: `(1/C) · ‖p‖^α / 2^(β/(β+τ)) = ‖p‖^α / (C · 2^(β/(β+τ)))`.
    have hLHS_eq :
        (1 / h.C) * (‖p‖ ^ h.α / 2 ^ (h.β / (h.β + h.τ)))
          = ‖p‖ ^ h.α / (h.C * 2 ^ (h.β / (h.β + h.τ))) := by
      field_simp
    -- Rewrite the RHS:
    --  `(1/C) · (X + (m^β+1)) = (1/C)·X + (1/C)·(m^β+1)`,
    -- and `(1/C)·X = (1/C)·‖p‖^(α(1+τ/β))/(m^τ+1)`.
    have hRHS_eq :
        (1 / h.C) * (‖p‖ ^ (h.α * (1 + h.τ / h.β)) / (m ^ h.τ + 1)
                      + (m ^ h.β + 1))
          = (1 / h.C) * (1 / (m ^ h.τ + 1)) * ‖p‖ ^ (h.α * (1 + h.τ / h.β))
            + (1 / h.C) * (m ^ h.β + 1) := by
      ring
    rw [hLHS_eq, hRHS_eq] at hyoung_scaled
    -- The congestion lower bound gives:
    --   `H ≥ (1/C)·(1/(m^τ+1))·‖p‖^(α(1+τ/β)) − C·(m^β+1)`.
    -- Rearrange to `(1/C)·(1/(m^τ+1))·‖p‖^(α(1+τ/β)) ≤ H + C·(m^β+1)`.
    have hlow' :
        (1 / h.C) * (1 / (m ^ h.τ + 1)) * ‖p‖ ^ (h.α * (1 + h.τ / h.β))
          ≤ H x p m + h.C * (m ^ h.β + 1) := by
      linarith
    -- Combine with `hyoung_scaled` to get
    --   `‖p‖^α / (C · 2^(β/(β+τ))) ≤ (1/C)·(m^β+1) + H + C·(m^β+1)
    --                              = H + (C + 1/C)·(m^β+1)`.
    have hcombined :
        ‖p‖ ^ h.α / (h.C * 2 ^ (h.β / (h.β + h.τ)))
          ≤ H x p m + h.C * (m ^ h.β + 1) + (1 / h.C) * (m ^ h.β + 1) :=
      le_trans hyoung_scaled (by linarith)
    -- Now: `‖p‖^α / C' ≤ ‖p‖^α / (C · 2^(β/(β+τ)))`, since
    -- `C · 2^(β/(β+τ)) ≤ C'` and `‖p‖^α ≥ 0`.
    have hp_α_nonneg : (0 : ℝ) ≤ ‖p‖ ^ h.α := Real.rpow_nonneg hp_nonneg _
    have hCprod_pos : 0 < h.C * 2 ^ (h.β / (h.β + h.τ)) := mul_pos hC_pos h2pow_pos
    have hCprod_le_C' : h.C * 2 ^ (h.β / (h.β + h.τ)) ≤ C' := by
      have h2 : 0 ≤ 1 / h.C := by positivity
      linarith
    have hdiv_C' : ‖p‖ ^ h.α / C' ≤ ‖p‖ ^ h.α / (h.C * 2 ^ (h.β / (h.β + h.τ))) :=
      div_le_div_of_nonneg_left hp_α_nonneg hCprod_pos hCprod_le_C'
    -- And `(C + 1/C)·(m^β+1) ≤ C'·(m^β+1)`, since `C + 1/C ≤ C'`.
    have hC_inv_C : h.C + 1 / h.C ≤ C' := by
      have h1 : 0 ≤ h.C * 2 ^ (h.β / (h.β + h.τ)) - h.C := by
        have := mul_le_mul_of_nonneg_left h2pow_ge_one hC_pos.le
        linarith
      linarith
    have hmβ_nonneg : (0 : ℝ) ≤ m ^ h.β := Real.rpow_nonneg hm.le _
    have hmβ1_nonneg : (0 : ℝ) ≤ m ^ h.β + 1 := by linarith
    have hsumC : h.C * (m ^ h.β + 1) + (1 / h.C) * (m ^ h.β + 1)
                  ≤ C' * (m ^ h.β + 1) := by
      have hexpand : h.C * (m ^ h.β + 1) + (1 / h.C) * (m ^ h.β + 1)
          = (h.C + 1 / h.C) * (m ^ h.β + 1) := by ring
      rw [hexpand]
      exact mul_le_mul_of_nonneg_right hC_inv_C hmβ1_nonneg
    -- Conclude.
    have : ‖p‖ ^ h.α / C' - C' * (m ^ h.β + 1) ≤ H x p m := by linarith
    exact this

-- Sanity-check `noncomputable example` of `HypothesisWeakGrowth`
-- inhabitedness moved to after `HypothesisPowerGrowth.toMDpHat0` is
-- available (search for `simpleHypothesisWeakGrowth_example`).


lemma CongestionGrowthCore.lagr_rider_of_convex_at_zero
    {d : ℕ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    (h_convex_at_zero :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          H x p m - (DpH x p m) ⬝ p ≤ H x (0 : Fin d → ℝ) m) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p m, 0 < m →
        (m ^ hcong.toWeakGrowth.β) / hcong.toWeakGrowth.C
          - hcong.toWeakGrowth.C
          ≤ (DpH x p m) ⬝ p - H x p m := by
  -- Constants from `hcong.toWeakGrowth`.
  have hC_pos : 0 < hcong.C := hcong.hC
  have hβ_pos : 0 < hcong.β := hcong.hβ
  have hτ_nonneg : 0 ≤ hcong.τ := hcong.hτ.1
  have hβτ_pos : 0 < hcong.β + hcong.τ := by linarith
  have h2pow_pos : (0 : ℝ) < (2 : ℝ) ^ (hcong.β / (hcong.β + hcong.τ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have h2pow_ge_one : (1 : ℝ) ≤ (2 : ℝ) ^ (hcong.β / (hcong.β + hcong.τ)) := by
    have hexp_nonneg : (0 : ℝ) ≤ hcong.β / (hcong.β + hcong.τ) :=
      div_nonneg hβ_pos.le hβτ_pos.le
    exact Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2) hexp_nonneg
  -- `toWeakGrowth.C = hcong.C * 2^(β/(β+τ)) + hcong.C + 1/hcong.C` and
  -- `toWeakGrowth.β = hcong.β` (definitionally; see `toWeakGrowth` body).
  have hC'_eq :
      hcong.toWeakGrowth.C
        = hcong.C * 2 ^ (hcong.β / (hcong.β + hcong.τ))
            + hcong.C + 1 / hcong.C := rfl
  have hβ'_eq : hcong.toWeakGrowth.β = hcong.β := rfl
  have hC'_pos : 0 < hcong.toWeakGrowth.C := by
    rw [hC'_eq]
    have h1 : 0 < hcong.C * 2 ^ (hcong.β / (hcong.β + hcong.τ)) :=
      mul_pos hC_pos h2pow_pos
    have h2 : 0 < 1 / hcong.C := by positivity
    linarith
  have hC_le_C' : hcong.C ≤ hcong.toWeakGrowth.C := by
    rw [hC'_eq]
    have hpos1 : 0 ≤ hcong.C * 2 ^ (hcong.β / (hcong.β + hcong.τ)) - hcong.C := by
      have : hcong.C ≤ hcong.C * 2 ^ (hcong.β / (hcong.β + hcong.τ)) := by
        have := mul_le_mul_of_nonneg_left h2pow_ge_one hC_pos.le
        linarith
      linarith
    have hpos2 : 0 ≤ 1 / hcong.C := by positivity
    linarith
  -- Now derive the lagr inequality at `hcong.{C, β}` first, then weaken.
  filter_upwards [hcong.upper, h_convex_at_zero] with x hUp hCx p m hm
  -- Step 1: `H x p m - DpH·p ≤ H x 0 m ≤ -(m^β)/hcong.C + hcong.C`.
  have h1 : H x p m - (DpH x p m) ⬝ p ≤ H x (0 : Fin d → ℝ) m := hCx p m hm
  have h2 : H x (0 : Fin d → ℝ) m ≤ -(m ^ hcong.β) / hcong.C + hcong.C := hUp m hm
  have h3 : H x p m - (DpH x p m) ⬝ p ≤ -(m ^ hcong.β) / hcong.C + hcong.C := h1.trans h2
  -- Rearrange: `(m^β)/hcong.C - hcong.C ≤ (DpH·p) - H x p m`.
  have h_lagr_at_hcong :
      (m ^ hcong.β) / hcong.C - hcong.C ≤ (DpH x p m) ⬝ p - H x p m := by
    have hneg : -(m ^ hcong.β) / hcong.C = -((m ^ hcong.β) / hcong.C) := by ring
    linarith
  -- Step 2: weaken from `hcong.{C, β}` to `toWeakGrowth.{C, β}`.
  -- `(m^β)/toWeakGrowth.C ≤ (m^β)/hcong.C` since `hcong.C ≤ toWeakGrowth.C` and `m^β ≥ 0`.
  -- `-toWeakGrowth.C ≤ -hcong.C` since `hcong.C ≤ toWeakGrowth.C`.
  have hmβ_nonneg : (0 : ℝ) ≤ m ^ hcong.β := Real.rpow_nonneg hm.le _
  have hdiv_le : (m ^ hcong.β) / hcong.toWeakGrowth.C ≤ (m ^ hcong.β) / hcong.C :=
    div_le_div_of_nonneg_left hmβ_nonneg hC_pos hC_le_C'
  have hC_le_C'_neg : -hcong.toWeakGrowth.C ≤ -hcong.C := by linarith
  -- Conclude.
  have hβ_subst : (m ^ hcong.toWeakGrowth.β) / hcong.toWeakGrowth.C
                    - hcong.toWeakGrowth.C
                  ≤ (m ^ hcong.β) / hcong.C - hcong.C := by
    rw [hβ'_eq]; linarith
  exact hβ_subst.trans h_lagr_at_hcong


noncomputable def CongestionGrowthCore.toCongestionAprioriPowerData
    {d : ℕ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    (h_convex_at_zero :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          H x p m - (DpH x p m) ⬝ p ≤ H x (0 : Fin d → ℝ) m) :
    CongestionAprioriPowerData (d := d) H DpH := by
  set hweak : HypothesisWeakGrowth (d := d) H DpH := hcong.toWeakGrowth
  have hLagr := hcong.lagr_rider_of_convex_at_zero
                  (DpH := DpH) (J := J) h_convex_at_zero
  refine
    { periodic_H := hweak.periodic_H
      periodic_DpH := hweak.periodic_DpH
      measurable_H := hweak.measurable_H
      measurable_DpH := hweak.measurable_DpH
      continuous_H_pm := hweak.continuous_H_pm
      continuous_DpH_pm := hweak.continuous_DpH_pm
      C := hweak.C
      α := hweak.α
      β := hweak.β
      hC := hweak.hC
      hα := hweak.hα
      hβ := hweak.hβ
      lower := hweak.lower
      lagr := hLagr }


theorem CongestionGrowthCore.mDpH_extended_bound
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionGrowthCore (d := d) H DpH J) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p m, 0 ≤ m →
        ‖J x p m‖
          ≤ h.C * (1 + m ^ (1 - h.τ)) * (‖p‖ ^ (h.α * (1 + h.τ / h.β) - 1))
            + h.C * (m ^ (h.β + 1 - h.β / h.α) + 1) := by
  -- Useful sign / order facts on the exponents.
  have hC := h.hC
  have hα := h.hα
  have hβ := h.hβ
  have hτ := h.hτ
  have hα_pos : 0 < h.α := lt_trans zero_lt_one hα
  have hτ_nonneg : 0 ≤ h.τ := hτ.1
  have hτ_le_one : h.τ ≤ 1 := hτ.2
  have h_one_sub_τ_nonneg : 0 ≤ 1 - h.τ := by linarith
  have h_div_lt : h.β / h.α < h.β := by
    rw [div_lt_iff₀ hα_pos]; nlinarith
  have h_β_sub_div_nonneg : 0 ≤ h.β - h.β / h.α := by linarith
  have h_β1_sub_div_nonneg : 0 ≤ h.β + 1 - h.β / h.α := by linarith
  -- Pull the relevant a.e. hypotheses on `x`.
  filter_upwards [h.DpH_upper, h.mDpHat0.tendsto_at_zero] with x hxB hxT
  intro p m hm
  -- A reusable abbreviation for the RHS as a function of `m`.
  set R : ℝ → ℝ := fun m =>
        h.C * (1 + m ^ (1 - h.τ)) * (‖p‖ ^ (h.α * (1 + h.τ / h.β) - 1))
        + h.C * (m ^ (h.β + 1 - h.β / h.α) + 1) with hR_def
  -- Continuity of `R` (as a function of `m`) on all of `ℝ`, since both
  -- exponents `1 - τ ≥ 0` and `β + 1 - β/α ≥ 0` are non-negative.
  have hR_cont : Continuous R := by
    have h1 : Continuous (fun m : ℝ => m ^ (1 - h.τ)) :=
      Real.continuous_rpow_const h_one_sub_τ_nonneg
    have h2 : Continuous (fun m : ℝ => m ^ (h.β + 1 - h.β / h.α)) :=
      Real.continuous_rpow_const h_β1_sub_div_nonneg
    have hA : Continuous (fun m : ℝ =>
        h.C * (1 + m ^ (1 - h.τ)) *
          (‖p‖ ^ (h.α * (1 + h.τ / h.β) - 1))) :=
      ((continuous_const.mul (continuous_const.add h1)).mul continuous_const)
    have hB : Continuous (fun m : ℝ =>
        h.C * (m ^ (h.β + 1 - h.β / h.α) + 1)) :=
      continuous_const.mul (h2.add continuous_const)
    exact hA.add hB
  -- Establish the bound first for `m > 0`, then extend to `m ≥ 0` by
  -- continuity / the limit hypothesis at `0`.
  -- Helper: bound for strictly positive `m`.
  have hbound_pos : ∀ m, 0 < m → ‖J x p m‖ ≤ R m := by
    intro m hmpos
    -- `J = m • DpH` for `m > 0`.
    have hJ_eq : J x p m = m • DpH x p m :=
      h.mDpHat0.J_of_pos x p m hmpos
    rw [hJ_eq]
    -- `‖m • DpH x p m‖ = m * ‖DpH x p m‖`.
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hmpos]
    -- Multiply `DpH_upper` by `m ≥ 0`.
    have hDpH := hxB p m hmpos
    have hmle :
        m * ‖DpH x p m‖
          ≤ m * (h.C * ((1 / m) + (1 / m ^ h.τ)) *
                  (‖p‖ ^ (h.α * (1 + h.τ / h.β) - 1))
                + h.C * ((m ^ (h.β - h.β / h.α)) + 1 / m)) :=
      mul_le_mul_of_nonneg_left hDpH hmpos.le
    -- Now simplify the rpow arithmetic to recover `R m`.
    have hm_ne : m ≠ 0 := ne_of_gt hmpos
    have hmτ_pos : 0 < m ^ h.τ := Real.rpow_pos_of_pos hmpos _
    have hmβdiv_pos : 0 < m ^ (h.β - h.β / h.α) :=
      Real.rpow_pos_of_pos hmpos _
    -- `m * (1/m^τ) = m^{1-τ}`.
    have h_m_inv_τ : m * (1 / m ^ h.τ) = m ^ (1 - h.τ) := by
      have hmτ_ne : m ^ h.τ ≠ 0 := ne_of_gt hmτ_pos
      have : m ^ (1 - h.τ) = m ^ (1 : ℝ) / m ^ h.τ :=
        Real.rpow_sub hmpos 1 h.τ
      rw [this, Real.rpow_one]
      field_simp
    -- `m * m^{β-β/α} = m^{β+1-β/α}`.
    have h_m_β : m * m ^ (h.β - h.β / h.α) = m ^ (h.β + 1 - h.β / h.α) := by
      have : m * m ^ (h.β - h.β / h.α)
          = m ^ (1 : ℝ) * m ^ (h.β - h.β / h.α) := by
        rw [Real.rpow_one]
      rw [this, ← Real.rpow_add hmpos]
      ring_nf
    -- Combine: rewrite the dominator to match `R m`.
    have hrhs_eq :
        m * (h.C * ((1 / m) + (1 / m ^ h.τ)) *
                (‖p‖ ^ (h.α * (1 + h.τ / h.β) - 1))
              + h.C * ((m ^ (h.β - h.β / h.α)) + 1 / m))
          = R m := by
      have hm_inv : m * (1 / m) = 1 := by field_simp
      simp only [hR_def]
      have step1 :
          m * (h.C * (1 / m + 1 / m ^ h.τ) *
                ‖p‖ ^ (h.α * (1 + h.τ / h.β) - 1))
            = h.C * (m * (1 / m) + m * (1 / m ^ h.τ)) *
                ‖p‖ ^ (h.α * (1 + h.τ / h.β) - 1) := by ring
      have step2 :
          m * (h.C * (m ^ (h.β - h.β / h.α) + 1 / m))
            = h.C * (m * m ^ (h.β - h.β / h.α) + m * (1 / m)) := by ring
      have step1' :
          h.C * (m * (1 / m) + m * (1 / m ^ h.τ)) *
              ‖p‖ ^ (h.α * (1 + h.τ / h.β) - 1)
            = h.C * (1 + m ^ (1 - h.τ)) *
              ‖p‖ ^ (h.α * (1 + h.τ / h.β) - 1) := by
        rw [hm_inv, h_m_inv_τ]
      have step2' :
          h.C * (m * m ^ (h.β - h.β / h.α) + m * (1 / m))
            = h.C * (m ^ (h.β + 1 - h.β / h.α) + 1) := by
        rw [hm_inv, h_m_β]
      calc m * (h.C * ((1 / m) + (1 / m ^ h.τ)) *
                  (‖p‖ ^ (h.α * (1 + h.τ / h.β) - 1))
                + h.C * ((m ^ (h.β - h.β / h.α)) + 1 / m))
          = m * (h.C * (1 / m + 1 / m ^ h.τ) *
                  ‖p‖ ^ (h.α * (1 + h.τ / h.β) - 1))
              + m * (h.C * (m ^ (h.β - h.β / h.α) + 1 / m)) := by ring
        _ = h.C * (m * (1 / m) + m * (1 / m ^ h.τ)) *
              ‖p‖ ^ (h.α * (1 + h.τ / h.β) - 1)
              + h.C * (m * m ^ (h.β - h.β / h.α) + m * (1 / m)) := by
              rw [step1, step2]
        _ = h.C * (1 + m ^ (1 - h.τ)) *
              ‖p‖ ^ (h.α * (1 + h.τ / h.β) - 1)
              + h.C * (m ^ (h.β + 1 - h.β / h.α) + 1) := by
              rw [step1', step2']
    linarith [hmle, hrhs_eq.le, hrhs_eq.ge]
  -- Now treat `m ≥ 0` by case analysis on `m = 0` vs `m > 0`.
  rcases lt_or_eq_of_le hm with hmpos | hmzero
  · exact hbound_pos m hmpos
  · -- `m = 0`: pass to the limit `m → 0⁺` of the bound for `m > 0`.
    subst hmzero
    -- `tendsto_at_zero` gives `m • DpH x p m → J x p 0` along `𝓝[>] 0`.
    have hLHS : Filter.Tendsto (fun m : ℝ => ‖m • DpH x p m‖)
        (𝓝[>] (0 : ℝ)) (𝓝 ‖J x p 0‖) :=
      (continuous_norm.continuousAt).tendsto.comp (hxT p)
    -- The RHS is continuous at `0`.
    have hRHS : Filter.Tendsto R (𝓝[>] (0 : ℝ)) (𝓝 (R 0)) :=
      (hR_cont.continuousAt).tendsto.mono_left nhdsWithin_le_nhds
    -- The bound holds eventually on `𝓝[>] 0` via `hbound_pos`,
    -- with the LHS rewritten as `‖m • DpH x p m‖` using `J_of_pos`.
    have hev : ∀ᶠ m in 𝓝[>] (0 : ℝ),
        ‖m • DpH x p m‖ ≤ R m := by
      filter_upwards [self_mem_nhdsWithin] with m hmpos
      have hmpos' : 0 < m := hmpos
      have hJeq : J x p m = m • DpH x p m :=
        h.mDpHat0.J_of_pos x p m hmpos'
      have := hbound_pos m hmpos'
      rwa [hJeq] at this
    -- Standard limit-of-inequality: limit of LHS ≤ limit of RHS.
    exact le_of_tendsto_of_tendsto hLHS hRHS hev


theorem CongestionGrowthCore.upper_extends_to_zero
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionGrowthCore (d := d) H DpH J)
    (hHat0 : HypothesisHat0 (d := d) H) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      Hext H x (0 : Fin d → ℝ) 0 ≤ ((h.C : ℝ) : WithTop ℝ) := by
  have hC := h.hC
  have hβ := h.hβ
  filter_upwards [h.upper, hHat0.exists_limit_at_zero] with x hxU hxL
  have hLim := tendsto_Hext_zero_of_exists (hxL (0 : Fin d → ℝ))
  have hRHS : Filter.Tendsto (fun _ : ℝ => ((h.C : ℝ) : WithTop ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 ((h.C : ℝ) : WithTop ℝ)) := tendsto_const_nhds
  have hev : ∀ᶠ m in 𝓝[>] (0 : ℝ),
      ((H x (0 : Fin d → ℝ) m : ℝ) : WithTop ℝ) ≤ ((h.C : ℝ) : WithTop ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with m hmpos
    have hmpos' : 0 < m := hmpos
    have hUbound := hxU m hmpos'
    have hmβ_pos : 0 < m ^ h.β := Real.rpow_pos_of_pos hmpos' _
    have hdivnn : 0 ≤ (m ^ h.β) / h.C := div_nonneg hmβ_pos.le hC.le
    have hreal : H x (0 : Fin d → ℝ) m ≤ h.C := by
      have hub : H x (0 : Fin d → ℝ) m ≤ -(m ^ h.β) / h.C + h.C := hUbound
      have hneg : -(m ^ h.β) / h.C ≤ 0 := by
        rw [neg_div]; linarith
      linarith
    exact_mod_cast hreal
  exact le_of_tendsto_of_tendsto hLim hRHS hev


theorem CongestionGrowthCore.lower_extends_to_zero
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : CongestionGrowthCore (d := d) H DpH J)
    (hHat0 : HypothesisHat0 (d := d) H) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p : Fin d → ℝ,
        (((1 / h.C) * (1 / ((0 : ℝ) ^ h.τ + 1)) *
            (‖p‖ ^ (h.α * (1 + h.τ / h.β))) - h.C : ℝ) : WithTop ℝ)
          ≤ Hext H x p 0 := by
  have hC := h.hC
  have hα := h.hα
  have hβ := h.hβ
  have hτ := h.hτ
  have hτ_nonneg : 0 ≤ h.τ := hτ.1
  filter_upwards [h.lower, hHat0.exists_limit_at_zero] with x hxL hxLim
  intro p
  have hLim := tendsto_Hext_zero_of_exists (hxLim p)
  -- Real-valued RHS as a function of `m`.
  set R : ℝ → ℝ := fun m =>
        (1 / h.C) * (1 / (m ^ h.τ + 1)) *
          (‖p‖ ^ (h.α * (1 + h.τ / h.β))) - h.C * (m ^ h.β + 1) with hR_def
  -- Continuity of `R` on `ℝ`. The factor `1/(m^τ + 1)` is continuous
  -- because `m^τ + 1 ≥ 1 > 0` for `m ≥ 0`; we use the simpler fact that
  -- `m^τ` is continuous (since `τ ≥ 0`) and `m^τ + 1 ≠ 0` everywhere on ℝ.
  -- However, `m^τ` may take negative-base values; we only need continuity
  -- on a neighborhood of `0` from the right, where `m > 0`, but it's easier
  -- to prove `Tendsto R (𝓝[>] 0) (𝓝 (R 0))` directly.
  -- Build `Tendsto R (𝓝[>] 0) (𝓝 (R 0))` directly from continuity of `R` at `0`.
  have hR_tendsto : Filter.Tendsto R (𝓝[>] (0 : ℝ)) (𝓝 (R 0)) := by
    have hτpos : ContinuousAt (fun m : ℝ => m ^ h.τ) 0 :=
      (Real.continuous_rpow_const hτ_nonneg).continuousAt
    have hβpos : ContinuousAt (fun m : ℝ => m ^ h.β) 0 :=
      (Real.continuous_rpow_const hβ.le).continuousAt
    -- Denominator `m^τ + 1` is positive at `0`.
    have h_denom_pos : 0 < (0 : ℝ) ^ h.τ + 1 := by
      have h0τ : 0 ≤ (0 : ℝ) ^ h.τ := Real.rpow_nonneg le_rfl _
      linarith
    have h_denom_cont : Continuous (fun m : ℝ => m ^ h.τ + 1) :=
      (Real.continuous_rpow_const hτ_nonneg).add continuous_const
    have h_inv_cont : ContinuousAt (fun m : ℝ => 1 / (m ^ h.τ + 1)) 0 := by
      refine ContinuousAt.div continuousAt_const h_denom_cont.continuousAt ?_
      exact ne_of_gt h_denom_pos
    have hR_contAt : ContinuousAt R 0 := by
      simp only [hR_def]
      have hA : ContinuousAt
          (fun m : ℝ => (1 / h.C) * (1 / (m ^ h.τ + 1)) *
            (‖p‖ ^ (h.α * (1 + h.τ / h.β)))) 0 :=
        ((continuousAt_const.mul h_inv_cont)).mul continuousAt_const
      have hB : ContinuousAt
          (fun m : ℝ => h.C * (m ^ h.β + 1)) 0 :=
        continuousAt_const.mul (hβpos.add continuousAt_const)
      exact hA.sub hB
    exact (hR_contAt.tendsto).mono_left nhdsWithin_le_nhds
  -- Tendsto of the cast of `R` to `WithTop ℝ`.
  have hRHS : Filter.Tendsto (fun m : ℝ => ((R m : ℝ) : WithTop ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 ((R 0 : ℝ) : WithTop ℝ)) :=
    (WithTop.continuous_coe.continuousAt.tendsto).comp hR_tendsto
  -- Eventually for `m > 0`: `R m ≤ H x p m` (lifted to `WithTop ℝ`).
  have hev : ∀ᶠ m in 𝓝[>] (0 : ℝ),
      ((R m : ℝ) : WithTop ℝ) ≤ ((H x p m : ℝ) : WithTop ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with m hmpos
    have hmpos' : 0 < m := hmpos
    have hLB := hxL p m hmpos'
    have hreal : R m ≤ H x p m := by
      simp only [hR_def]
      exact hLB
    exact_mod_cast hreal
  -- Identify `R 0` with the explicit form in the goal.
  have hR0 : R 0 = (1 / h.C) * (1 / ((0 : ℝ) ^ h.τ + 1)) *
        (‖p‖ ^ (h.α * (1 + h.τ / h.β))) - h.C := by
    simp only [hR_def, Real.zero_rpow hβ.ne', zero_add, mul_one]
  have hgoal := le_of_tendsto_of_tendsto hRHS hLim hev
  rw [hR0] at hgoal
  exact hgoal


end StationaryMFG.Hamiltonian
