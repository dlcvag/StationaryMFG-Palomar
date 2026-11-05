module

public import StationaryMFG.Periodic.LpDualityRN
public import StationaryMFG.Periodic.Reflexive
public import StationaryMFG.Periodic.Sobolev

@[expose] public section

/-!
# Reflexivity of `L^p_per`, `W^{1,p}_per` and the paper's product space (general `1 < p < ∞`)

This module lifts the `p = 2` reflexivity instances delivered in
`StationaryMFG.Periodic.Reflexive` to the full classical range
`1 < p < ∞`, using the unit-cube Riesz representation theorem
`StationaryMFG.Periodic.exists_representer_norm_eq` from
`LpDualityRN.lean`.

## Strategy

The classical proof: `(L^p)** ≃ (L^q)* ≃ L^p`. Two applications of
the Riesz representation theorem identify `(L^p_per)**` with
`L^p_per`, and the composite agrees with the canonical embedding
`NormedSpace.inclusionInDoubleDual ℝ (LpPer p d)`.

Concretely, given `Φ : (LpPer p d) →L[ℝ] ℝ →L[ℝ] ℝ`:
1. The map `LpPer.toDual p q : LpPer q d →L[ℝ] (LpPer p d →L[ℝ] ℝ)`,
   `g ↦ (f ↦ ∫ g · f)`, is the Hölder pairing — continuous by Mathlib's
   `ContinuousLinearMap.lpPairing`.
2. Compose with `Φ` to get a continuous functional `LpPer q d →L[ℝ] ℝ`.
3. Riesz produces `f ∈ LpPer p d` with `Φ (toDual g) = ∫ f · g`.
4. For any `ψ : LpPer p d →L[ℝ] ℝ`, Riesz produces `g_ψ ∈ LpPer q d`
   with `ψ = toDual g_ψ`. Then `Φ ψ = Φ (toDual g_ψ) = ∫ f · g_ψ
   = ∫ g_ψ · f = ψ f`, i.e. `Φ` is the canonical image of `f`.

Closure of reflexivity under finite products and `Pi`-types
(`IsReflexiveNormedSpace.prod` and `IsReflexiveNormedSpace.pi` in
`Reflexive.lean`) then delivers reflexivity of
`SobolevPerLp 1 p d = LpPer p d × (Fin d → LpPer p d)` and of the
paper's product `LpPer β̄ d × SobolevPerLp 1 γ̄ d`.

## Reference

Adapted from `LpSpaces.LpReflexive.LpOn.isReflexive` (whole-space
finite-measure version), specialised to the unit-cube measure.
-/

noncomputable section

namespace StationaryMFG
namespace Periodic

open MeasureTheory NormedSpace
open scoped ENNReal NNReal Topology

variable {d : ℕ}

/-! ## The `L^q → (L^p)*` natural map -/

/-- The **Hölder pairing** `LpPer q d →L[ℝ] LpPer p d →L[ℝ] ℝ`,
`(g, f) ↦ ∫ x, g x * f x`, for Hölder-conjugate exponents `p q`.
This is `ContinuousLinearMap.lpPairing` specialised to real
multiplication and the unit-cube measure. -/
def LpPer.toDual (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate q p] (d : ℕ) :
    LpPer q d →L[ℝ] (LpPer p d →L[ℝ] ℝ) :=
  (ContinuousLinearMap.mul ℝ ℝ).lpPairing
    (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) q p

/-- The `LpPer.toDual` pairing is given by the integral `∫ g · f`. -/
theorem LpPer.toDual_apply_apply {p q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate q p]
    (g : LpPer q d) (f : LpPer p d) :
    LpPer.toDual p q d g f =
      ∫ x, g x * f x
        ∂(Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) := by
  simp [LpPer.toDual, ContinuousLinearMap.lpPairing_eq_integral]

/-! ## Reflexivity of `LpPer p d` for `1 < p < ∞` -/

/-- **Reflexivity of `LpPer p d` for `1 < p < ∞`.** The canonical
isometric embedding `LpPer p d → (LpPer p d)**` is surjective, by two
applications of the unit-cube Riesz representation theorem.

Adapted from `LpSpaces.LpReflexive.LpOn.isReflexive`. -/
theorem lpPer_isReflexive (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (hp_gt_one : 1 < p) (hp_ne_top : p ≠ ∞) :
    IsReflexiveNormedSpace (LpPer p d) := by
  -- Conjugate exponents: `q` is between `1` and `∞`.
  haveI hqp : ENNReal.HolderConjugate q p :=
    (inferInstance : ENNReal.HolderConjugate p q).symm
  have hp_lt_top : p < ∞ := lt_top_iff_ne_top.mpr hp_ne_top
  have hq_gt_one : 1 < q := by
    rw [← ENNReal.HolderConjugate.lt_top_iff_one_lt p q]
    exact hp_lt_top
  have hq_lt_top : q < ∞ := by
    rw [ENNReal.HolderConjugate.lt_top_iff_one_lt q p]
    exact hp_gt_one
  have hq_ne_top : q ≠ ∞ := hq_lt_top.ne
  -- Take Φ in the double dual.
  intro Φ
  -- ΦTilde : LpPer q d →L[ℝ] ℝ.
  set ΦTilde : LpPer q d →L[ℝ] ℝ :=
    Φ.comp (LpPer.toDual p q d) with hΦT_def
  -- Apply Riesz to ΦTilde (exponents q, p) to extract a representer
  -- `f₀ : (Fin d → ℝ) → ℝ` in `MemLp _ p μPer`.
  obtain ⟨f₀, hf₀_memLp, hf₀_eq, _⟩ :=
    exists_representer_norm_eq (p := q) (q := p) hq_gt_one hq_ne_top ΦTilde
  -- Package `f₀` as an element of `LpPer p d`.
  set f : LpPer p d := MemLp.toLp f₀ hf₀_memLp with hf_def
  have hf_ae : (⇑f : (Fin d → ℝ) → ℝ) =ᵐ[Measure.restrict
      (volume : Measure (Fin d → ℝ)) (UnitCube d)] f₀ :=
    MemLp.coeFn_toLp hf₀_memLp
  refine ⟨f, ?_⟩
  -- Show: `inclusionInDoubleDual ℝ (LpPer p d) f = Φ`.
  apply ContinuousLinearMap.ext
  intro ψ
  -- Apply Riesz to ψ (exponents p, q): get `g_ψ ∈ LpPer q d` with
  -- `ψ h = ∫ h · g_ψ`.
  obtain ⟨g₀, hg₀_memLp, hψ_eq, _⟩ :=
    exists_representer_norm_eq (p := p) (q := q) hp_gt_one hp_ne_top ψ
  set g_ψ : LpPer q d := MemLp.toLp g₀ hg₀_memLp with hg_def
  have hg_ae : (⇑g_ψ : (Fin d → ℝ) → ℝ) =ᵐ[Measure.restrict
      (volume : Measure (Fin d → ℝ)) (UnitCube d)] g₀ :=
    MemLp.coeFn_toLp hg₀_memLp
  -- Identify ψ with `LpPer.toDual p q d g_ψ`.
  have h_ψ_clm : ψ = LpPer.toDual p q d g_ψ := by
    apply ContinuousLinearMap.ext
    intro h
    rw [LpPer.toDual_apply_apply, hψ_eq h]
    apply integral_congr_ae
    filter_upwards [hg_ae] with x hx
    rw [hx, mul_comm]
  -- Show: `f` represents `Φ` in the double dual sense.
  change ψ f = Φ ψ
  -- Chain: ψ f = (toDual g_ψ) f = ∫ g_ψ · f = ∫ f₀ · g₀ = ΦTilde g_ψ
  --        = Φ (toDual g_ψ) = Φ ψ.
  calc ψ f
      = LpPer.toDual p q d g_ψ f := by rw [h_ψ_clm]
    _ = ∫ x, g_ψ x * f x
          ∂(Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) :=
          LpPer.toDual_apply_apply g_ψ f
    _ = ∫ x, f₀ x * g₀ x
          ∂(Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) := by
          apply integral_congr_ae
          filter_upwards [hf_ae, hg_ae] with x hx hy
          rw [hx, hy]; ring
    _ = ΦTilde g_ψ := by
          rw [hf₀_eq g_ψ]
          apply integral_congr_ae
          filter_upwards [hg_ae] with x hx
          rw [hx]; ring
    _ = Φ (LpPer.toDual p q d g_ψ) := rfl
    _ = Φ ψ := by rw [← h_ψ_clm]

/-! ## Reflexivity of `SobolevPerLp 1 p d` for `1 < p < ∞`

`SobolevPerLp 1 p d = LpPer p d × (Fin d → LpPer p d)`, so the result
follows from `lpPer_isReflexive` together with the closure lemmas
`IsReflexiveNormedSpace.prod` and `IsReflexiveNormedSpace.pi`. -/

/-- **Reflexivity of `SobolevPerLp 1 p d` for `1 < p < ∞`.** -/
theorem sobolevPer_isReflexive (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (hp_gt_one : 1 < p) (hp_ne_top : p ≠ ∞) :
    IsReflexiveNormedSpace (SobolevPerLp 1 p d) := by
  refine IsReflexiveNormedSpace.prod
    (lpPer_isReflexive (d := d) p q hp_gt_one hp_ne_top) ?_
  exact IsReflexiveNormedSpace.pi
    (fun _ => lpPer_isReflexive (d := d) p q hp_gt_one hp_ne_top)

/-- **Reflexivity of the paper's product space `L^β_per × W^{1,γ}_per`
for general `1 < β, γ < ∞`** (corresponding to the paper's
`β̄` and `γ̄`). This is the compactness target invoked in
`Source/FGU-monotone_revised.tex` lines 1296, 1601, and 1982. -/
theorem lpSobolev_product_isReflexive
    (pβ qβ pγ qγ : ℝ≥0∞)
    [Fact (1 ≤ pβ)] [Fact (1 ≤ qβ)] [ENNReal.HolderConjugate pβ qβ]
    [Fact (1 ≤ pγ)] [Fact (1 ≤ qγ)] [ENNReal.HolderConjugate pγ qγ]
    (hβ_gt_one : 1 < pβ) (hβ_ne_top : pβ ≠ ∞)
    (hγ_gt_one : 1 < pγ) (hγ_ne_top : pγ ≠ ∞) :
    IsReflexiveNormedSpace (LpPer pβ d × SobolevPerLp 1 pγ d) :=
  IsReflexiveNormedSpace.prod
    (lpPer_isReflexive (d := d) pβ qβ hβ_gt_one hβ_ne_top)
    (sobolevPer_isReflexive (d := d) pγ qγ hγ_gt_one hγ_ne_top)

/-! ### Sample exercise: extracting the canonical equivalence -/

/-- Sample: at general exponents `1 < β, γ < ∞`, the canonical embedding
of the paper's product space into its double dual is a linear isometric
equivalence, supplying the abstract data underlying weakly convergent
subsequence extraction. -/
example
    (pβ qβ pγ qγ : ℝ≥0∞)
    [Fact (1 ≤ pβ)] [Fact (1 ≤ qβ)] [ENNReal.HolderConjugate pβ qβ]
    [Fact (1 ≤ pγ)] [Fact (1 ≤ qγ)] [ENNReal.HolderConjugate pγ qγ]
    (hβ_gt_one : 1 < pβ) (hβ_ne_top : pβ ≠ ∞)
    (hγ_gt_one : 1 < pγ) (hγ_ne_top : pγ ≠ ∞) :
    (LpPer pβ d × SobolevPerLp 1 pγ d) ≃ₗᵢ[ℝ]
      StrongDual ℝ (StrongDual ℝ (LpPer pβ d × SobolevPerLp 1 pγ d)) :=
  (lpSobolev_product_isReflexive (d := d)
      pβ qβ pγ qγ hβ_gt_one hβ_ne_top hγ_gt_one hγ_ne_top).equiv

end Periodic
end StationaryMFG
