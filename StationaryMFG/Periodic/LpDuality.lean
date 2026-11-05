module

public import StationaryMFG.Periodic.Lp
public import StationaryMFG.Periodic.Reflexive
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

/-!
# Riesz representation on the unit cube — `L²` warm-up

This module ships the **`p = 2` Riesz representation theorem** on the
periodic unit cube `[0,1)^d`, the first iteration of the `Lp` duality
infrastructure scheduled by task `infra:P1-Lp-duality`.

For every continuous linear functional `φ` on
`Lp ℝ 2 (volume.restrict (UnitCube d))`, there is a unique representer
`g ∈ Lp ℝ 2 (volume.restrict (UnitCube d))` with

```
φ f = ∫ x, f x * g x ∂(volume.restrict (UnitCube d))
```

for all `f`, and `‖g‖ = ‖φ‖`.

## Mathlib search (documented in the task file)

The toolchain copy of Mathlib *does not* expose a finite-measure Riesz
representation theorem `(Lp)* ≃ Lq`. It does provide:

- `MeasureTheory.L2.innerProductSpace`: `Lp ℝ 2 μ` is a real
  inner-product space with `⟪f, g⟫ = ∫ a, ⟪f a, g a⟫ ∂μ`.
- `InnerProductSpace.toDual`: for any complete inner-product space `E`,
  the Fréchet–Riesz isometric equivalence `E ≃ₗᵢ⋆ StrongDual 𝕜 E`.
- `ContinuousLinearMap.lpPairing` (Hölder pairing) — the easy direction
  `Lq ↪ (Lp)*`, but **without** surjectivity.

For the Hilbert case we therefore reduce directly to
`InnerProductSpace.toDual` applied to `Lp ℝ 2 (volume.restrict
(UnitCube d))`. The general `1 < p < ∞` case requires the saturator
argument from `LpSpaces.LpDualityFinitePQ` and is parked as a
follow-up subtask.

## References

- Adapted from `LpSpaces.LpDualityFinite.exists_unique_representer_L2`
  (whole-space version); rewritten here for the cube-restricted measure
  with the explicit real `f * g` integrand demanded by the paper.
-/

noncomputable section

namespace StationaryMFG
namespace Periodic

open MeasureTheory
open scoped ENNReal NNReal InnerProductSpace

variable {d : ℕ}

/-- The Mathlib `Lp` space on the unit cube, parameterised by an
extended exponent. This is the project-local abbreviation through which
all Riesz / reflexivity results are phrased. -/
abbrev LpPer (p : ℝ≥0∞) (d : ℕ) : Type :=
  Lp ℝ p (Measure.restrict (volume) (UnitCube d))

/-! ## `p = 2` Riesz representation on the unit cube -/

/-- **Existence and uniqueness of the `L²` representer on the unit
cube.** Every continuous real-linear functional `φ : LpPer 2 d →L[ℝ] ℝ`
is given by integration against a unique `g ∈ LpPer 2 d`, with matching
norms.

This is the Hilbert (`p = 2`) instance of the finite-measure Riesz
representation theorem. The general `1 < p < ∞` case is parked as a
follow-up child task. -/
theorem exists_unique_representer_L2
    (φ : LpPer 2 d →L[ℝ] ℝ) :
    ∃! g : LpPer 2 d,
      (∀ f : LpPer 2 d,
        φ f = ∫ x, (f x) * (g x)
          ∂(Measure.restrict (volume) (UnitCube d))) ∧
      ‖g‖ = ‖φ‖ := by
  -- Fréchet–Riesz on the real Hilbert space `LpPer 2 d`.
  set R : LpPer 2 d ≃ₗᵢ⋆[ℝ] StrongDual ℝ (LpPer 2 d) :=
    InnerProductSpace.toDual ℝ (LpPer 2 d) with hR
  -- The candidate representer.
  refine ⟨R.symm φ, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro f
      -- `φ f = R (R.symm φ) f = ⟪R.symm φ, f⟫ = ∫ x, ⟪(R.symm φ) x, f x⟫`.
      have hRapp : R (R.symm φ) = φ := R.apply_symm_apply φ
      have hpair : (R (R.symm φ)) f = @inner ℝ _ _ (R.symm φ) f :=
        InnerProductSpace.toDual_apply_apply
      have hphi : φ f = @inner ℝ _ _ (R.symm φ) f := by
        have := congrArg (fun ψ : StrongDual ℝ (LpPer 2 d) => ψ f) hRapp
        simpa using this.symm.trans hpair
      -- Unfold the L² inner product to an integral.
      rw [hphi, MeasureTheory.L2.inner_def]
      -- Real inner product on ℝ is plain multiplication; reorder to match
      -- the statement `f x * g x`.
      apply integral_congr_ae
      filter_upwards with x
      -- `⟪a, b⟫_ℝ = b * a` definitionally (`RCLike.inner_apply`).
      change (f x) * (R.symm φ) x = (f x) * (R.symm φ) x
      rfl
    · -- Norm matching: `R.symm` is an isometry.
      simp [R.symm.norm_map φ]
  · -- Uniqueness: any other `g` satisfying the integral equation must
    -- equal `R.symm φ` because `R` is injective.
    rintro g ⟨hg_int, _hg_norm⟩
    apply R.injective
    apply ContinuousLinearMap.ext
    intro f
    -- LHS: `R g f = ⟪g, f⟫ = ∫ f * g`.
    have hRg : R g f = @inner ℝ _ _ g f :=
      InnerProductSpace.toDual_apply_apply
    have hRgInt : R g f =
        ∫ x, (f x) * (g x) ∂(Measure.restrict (volume) (UnitCube d)) := by
      rw [hRg, MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards with x
      change (f x) * g x = (f x) * g x
      rfl
    -- RHS: `R (R.symm φ) f = φ f`.
    have hRsymm : R (R.symm φ) f = φ f := by
      have hRapp : R (R.symm φ) = φ := R.apply_symm_apply φ
      exact congrArg (fun ψ : StrongDual ℝ (LpPer 2 d) => ψ f) hRapp
    -- The integral equation supplies `R g f = R (R.symm φ) f`.
    rw [hRsymm, hRgInt]
    exact (hg_int f).symm

/-! ### Sanity-check example

Apply the representer theorem to the `Lq → (Lp)*` natural pairing for
the constant function `1` on the unit cube: it must produce a unique
representer in `LpPer 2 d`, and our theorem indeed provides one. -/

/-- Example consumer of `exists_unique_representer_L2`: any continuous
linear functional on `LpPer 2 d` admits a unique `L²` representer. The
particular functional below is the "evaluation against a fixed `g₀`"
pairing realised through `InnerProductSpace.toDual`. -/
example (g₀ : LpPer 2 d) :
    ∃! g : LpPer 2 d,
      (∀ f : LpPer 2 d,
        (InnerProductSpace.toDual ℝ (LpPer 2 d) g₀) f =
          ∫ x, (f x) * (g x)
            ∂(Measure.restrict (volume) (UnitCube d))) ∧
      ‖g‖ = ‖InnerProductSpace.toDual ℝ (LpPer 2 d) g₀‖ :=
  exists_unique_representer_L2
    (φ := InnerProductSpace.toDual ℝ (LpPer 2 d) g₀)

/-! ## Saturator construction for the general-`p` Riesz port

Adapted from `LpSpaces.LpDualityRN` (lines 223–423 of the reference
file `docs/references/LpSpaces/LpSpaces/LpDualityRN.lean`). The
saturator is the building block needed for the general
`1 < p < ∞` Riesz representation theorem on the unit cube.

We zero out the function on `{g = 0}` to make it manifestly measurable
for any real `q` (the issue is that `t ↦ t^(q-2)` is discontinuous at
`0` when `q < 2`). The truncated variant additionally zeros on
`{|g| > n}`, which makes it uniformly bounded and hence in every
`Lᵖ` on the finite-measure unit cube. -/

namespace Saturator

/-- The unit-cube measure is finite (it has total mass `1`). This
instance is needed by `MemLp.of_bound` below. -/
instance instIsFiniteMeasureRestrictUnitCube :
    IsFiniteMeasure (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, volume_unitCube]
  exact ENNReal.one_lt_top

/-- **RN saturator.** Zero on `{g = 0}`, equal to `g x · |g x|^(q-2)`
elsewhere. Adapted from `LpSpaces.LpDualityRN.saturatorRN`. -/
def satRN (q : ℝ) (g : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  if g x = 0 then 0 else g x * |g x| ^ (q - 2)

/-- **Truncated RN saturator.** Zero on `{g = 0} ∪ {|g| > n}`, and
`g x · |g x|^(q-2)` elsewhere. Adapted from
`LpSpaces.LpDualityRN.saturatorRNTruncated`. -/
def satRNTruncated (q : ℝ) (g : (Fin d → ℝ) → ℝ) (n : ℕ) (x : Fin d → ℝ) : ℝ :=
  if g x = 0 ∨ (n : ℝ) < |g x| then 0 else g x * |g x| ^ (q - 2)

/-- Measurability tunnel: `t ↦ ((ENNReal.ofReal |t|)^r).toReal` is
measurable for every real `r`, avoiding the `0^(q-2)` discontinuity at
`q < 2`. Adapted from `LpSpaces.LpDualityRN.measurable_abs_rpow`. -/
private lemma measurable_abs_rpow (r : ℝ) :
    Measurable (fun t : ℝ => ((ENNReal.ofReal |t|) ^ r).toReal) := by
  apply ENNReal.measurable_toReal.comp
  apply (ENNReal.continuous_rpow_const).measurable.comp
  exact ENNReal.measurable_ofReal.comp _root_.continuous_abs.measurable

/-- Pointwise equivalence of the tunnel with `|t|^r`.
Adapted from `LpSpaces.LpDualityRN.abs_rpow_eq_ennreal_toReal`. -/
private lemma abs_rpow_eq_ennreal_toReal (t r : ℝ) :
    ((ENNReal.ofReal |t|) ^ r).toReal = |t| ^ r := by
  rw [← ENNReal.toReal_rpow]
  rw [ENNReal.toReal_ofReal (abs_nonneg t)]

/-- AE-strong-measurability of the saturator. Works for any real `q`
because we have explicitly zeroed `{g = 0}`. Adapted from
`LpSpaces.LpDualityRN.aestronglyMeasurable_saturatorRN`. -/
theorem aestronglyMeasurable_satRN
    {g : (Fin d → ℝ) → ℝ}
    (hg : AEStronglyMeasurable g
      (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)))
    (q : ℝ) :
    AEStronglyMeasurable (satRN q g)
      (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) := by
  set g' := hg.mk g with hg'_def
  have hg'_meas : StronglyMeasurable g' := hg.stronglyMeasurable_mk
  have hg'_ae : g =ᵐ[Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)] g' :=
    hg.ae_eq_mk
  have h_ae : satRN q g =ᵐ[Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)]
      satRN q g' := by
    filter_upwards [hg'_ae] with x hx
    unfold satRN
    simp [hx]
  refine AEStronglyMeasurable.congr ?_ h_ae.symm
  have h_set : MeasurableSet {x : (Fin d → ℝ) | g' x = 0} :=
    measurableSet_eq_fun hg'_meas.measurable measurable_const
  have h_rpow_meas : Measurable
      (fun x => ((ENNReal.ofReal |g' x|) ^ (q - 2)).toReal) :=
    (measurable_abs_rpow (q - 2)).comp hg'_meas.measurable
  have h_prod_meas : Measurable
      (fun x => g' x * ((ENNReal.ofReal |g' x|) ^ (q - 2)).toReal) :=
    hg'_meas.measurable.mul h_rpow_meas
  have h_ite : Measurable (fun x => if g' x = 0 then (0 : ℝ)
      else g' x * ((ENNReal.ofReal |g' x|) ^ (q - 2)).toReal) :=
    Measurable.ite h_set measurable_const h_prod_meas
  have h_eq : (fun x => if g' x = 0 then (0 : ℝ)
      else g' x * ((ENNReal.ofReal |g' x|) ^ (q - 2)).toReal)
      = satRN q g' := by
    funext x
    unfold satRN
    split_ifs with h
    · rfl
    · rw [abs_rpow_eq_ennreal_toReal]
  rw [← h_eq]
  exact h_ite.stronglyMeasurable.aestronglyMeasurable

/-- AE-strong-measurability of the truncated saturator. Adapted from
`LpSpaces.LpDualityRN.aestronglyMeasurable_saturatorRNTruncated`. -/
theorem aestronglyMeasurable_satRNTruncated
    {g : (Fin d → ℝ) → ℝ}
    (hg : AEStronglyMeasurable g
      (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)))
    (q : ℝ) (n : ℕ) :
    AEStronglyMeasurable (satRNTruncated q g n)
      (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) := by
  set g' := hg.mk g with hg'_def
  have hg'_meas : StronglyMeasurable g' := hg.stronglyMeasurable_mk
  have hg'_ae : g =ᵐ[Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)] g' :=
    hg.ae_eq_mk
  have h_ae : satRNTruncated q g n
      =ᵐ[Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)]
      satRNTruncated q g' n := by
    filter_upwards [hg'_ae] with x hx
    unfold satRNTruncated
    simp [hx]
  refine AEStronglyMeasurable.congr ?_ h_ae.symm
  have h_zero : MeasurableSet {x : (Fin d → ℝ) | g' x = 0} :=
    measurableSet_eq_fun hg'_meas.measurable measurable_const
  have h_abs : Measurable fun x => |g' x| :=
    _root_.continuous_abs.measurable.comp hg'_meas.measurable
  have h_big : MeasurableSet {x : (Fin d → ℝ) | (n : ℝ) < |g' x|} :=
    measurableSet_lt measurable_const h_abs
  have h_or : MeasurableSet {x : (Fin d → ℝ) | g' x = 0 ∨ (n : ℝ) < |g' x|} := by
    have hset : {x : (Fin d → ℝ) | g' x = 0 ∨ (n : ℝ) < |g' x|}
        = {x | g' x = 0} ∪ {x | (n : ℝ) < |g' x|} := by
      ext x; simp [Set.mem_union]
    rw [hset]
    exact h_zero.union h_big
  have h_rpow_meas : Measurable
      (fun x => ((ENNReal.ofReal |g' x|) ^ (q - 2)).toReal) :=
    (measurable_abs_rpow (q - 2)).comp hg'_meas.measurable
  have h_prod_meas : Measurable
      (fun x => g' x * ((ENNReal.ofReal |g' x|) ^ (q - 2)).toReal) :=
    hg'_meas.measurable.mul h_rpow_meas
  have h_ite : Measurable (fun x => if g' x = 0 ∨ (n : ℝ) < |g' x|
      then (0 : ℝ) else g' x * ((ENNReal.ofReal |g' x|) ^ (q - 2)).toReal) :=
    Measurable.ite h_or measurable_const h_prod_meas
  have h_eq : (fun x => if g' x = 0 ∨ (n : ℝ) < |g' x|
      then (0 : ℝ) else g' x * ((ENNReal.ofReal |g' x|) ^ (q - 2)).toReal)
      = satRNTruncated q g' n := by
    funext x
    unfold satRNTruncated
    split_ifs with h
    · rfl
    · rw [abs_rpow_eq_ennreal_toReal]
  rw [← h_eq]
  exact h_ite.stronglyMeasurable.aestronglyMeasurable

/-- Pointwise bound for the truncated saturator. Adapted from
`LpSpaces.LpDualityRN.abs_saturatorRNTruncated_le`. -/
theorem abs_satRNTruncated_le (q : ℝ) (hq : 1 ≤ q)
    (g : (Fin d → ℝ) → ℝ) (n : ℕ) (x : Fin d → ℝ) :
    |satRNTruncated q g n x| ≤ (n : ℝ) ^ (q - 1) := by
  unfold satRNTruncated
  split_ifs with hx
  · simp; positivity
  · push_neg at hx
    obtain ⟨hg0, hle⟩ := hx
    have h_abs_pos : 0 < |g x| := abs_pos.mpr hg0
    rw [abs_mul]
    have h_pow_abs : |(|g x| ^ (q - 2))| = |g x| ^ (q - 2) :=
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
    rw [h_pow_abs]
    have h_eq : |g x| * |g x| ^ (q - 2) = |g x| ^ (q - 1) := by
      rw [show (q - 1 : ℝ) = 1 + (q - 2) by ring,
          Real.rpow_add h_abs_pos, Real.rpow_one]
    rw [h_eq]
    exact Real.rpow_le_rpow (abs_nonneg _) hle (by linarith)

/-- `Lᵖ` membership of the truncated saturator on the unit cube.
Adapted from `LpSpaces.LpDualityRN.memLpOn_saturatorRNTruncated`. -/
theorem memLp_satRNTruncated
    {g : (Fin d → ℝ) → ℝ}
    (hg : AEStronglyMeasurable g
      (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)))
    (q : ℝ) (hq : 1 ≤ q) (n : ℕ) (p : ℝ≥0∞) :
    MemLp (satRNTruncated q g n) p
      (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) := by
  refine MemLp.of_bound (aestronglyMeasurable_satRNTruncated hg q n)
    ((n : ℝ) ^ (q - 1)) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs]
  exact abs_satRNTruncated_le q hq g n x

/-- First key identity. Adapted from
`LpSpaces.LpDualityRN.saturatorRNTruncated_mul_self`. -/
theorem satRNTruncated_mul_self
    {q : ℝ} (hq : 0 < q) (g : (Fin d → ℝ) → ℝ) (n : ℕ) (x : Fin d → ℝ) :
    satRNTruncated q g n x * g x =
      (if g x = 0 ∨ (n : ℝ) < |g x| then 0 else |g x| ^ q) := by
  unfold satRNTruncated
  split_ifs with hx
  · rw [zero_mul]
  · push_neg at hx
    obtain ⟨hg0, _⟩ := hx
    have h_abs_pos : 0 < |g x| := abs_pos.mpr hg0
    have h_sq : g x * g x = |g x| ^ (2 : ℝ) := by
      rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [sq_abs, sq]
    calc g x * |g x| ^ (q - 2) * g x
        = g x * g x * |g x| ^ (q - 2) := by ring
      _ = |g x| ^ (2 : ℝ) * |g x| ^ (q - 2) := by rw [h_sq]
      _ = |g x| ^ ((2 : ℝ) + (q - 2)) := by rw [← Real.rpow_add h_abs_pos]
      _ = |g x| ^ q := by ring_nf

/-- Second key identity, using the conjugacy relation `p (q - 1) = q`.
Adapted from `LpSpaces.LpDualityRN.abs_saturatorRNTruncated_rpow`. -/
theorem abs_satRNTruncated_rpow
    {p q : ℝ} (hp : 1 < p) (hq : 1 < q) (hpq : p * (q - 1) = q)
    (g : (Fin d → ℝ) → ℝ) (n : ℕ) (x : Fin d → ℝ) :
    |satRNTruncated q g n x| ^ p =
      (if g x = 0 ∨ (n : ℝ) < |g x| then 0 else |g x| ^ q) := by
  unfold satRNTruncated
  have hp_pos : 0 < p := by linarith
  split_ifs with hx
  · rw [abs_zero]
    exact Real.zero_rpow hp_pos.ne'
  · push_neg at hx
    obtain ⟨hg0, _⟩ := hx
    have h_abs_pos : 0 < |g x| := abs_pos.mpr hg0
    rw [abs_mul]
    have h_pow_abs : |(|g x| ^ (q - 2))| = |g x| ^ (q - 2) :=
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
    rw [h_pow_abs]
    have h_eq : |g x| * |g x| ^ (q - 2) = |g x| ^ (q - 1) := by
      rw [show (q - 1 : ℝ) = 1 + (q - 2) by ring,
          Real.rpow_add h_abs_pos, Real.rpow_one]
    rw [h_eq, ← Real.rpow_mul h_abs_pos.le]
    congr 1
    linarith

end Saturator

/-! ## `Lq` membership and norm bound for the representer (Step 1)

Adapted from `LpSpaces.LpDualityRN.representer_memLq_and_norm_le` (lines
448-771 of the reference file). Given a candidate representer `g`
on `LpPer p d` for which the duality identity already holds for every
**bounded** `h ∈ Lᵖ`, we conclude `g ∈ Lᵠ` with
`eLpNorm g q μ ≤ ENNReal.ofReal ‖φ‖`. This is Step 1 of
`infra:P1-Lp-duality-norm`. -/

open Saturator

/-- **`Lq` membership and norm bound for the representer.** Given an
`L¹`-style candidate representer `g` for a continuous linear functional
`φ : LpPer p d →L[ℝ] ℝ` with `1 < p < ∞`, if `φ` is represented by `g`
against every bounded `h ∈ Lᵖ`, then `g ∈ Lᵠ` and
`eLpNorm g q μ ≤ ENNReal.ofReal ‖φ‖`.

The proof's only nontrivial inputs are `1 < pr` and the conjugacy
identity `pr * (qr - 1) = qr`, both of which follow from `1 < p` and
`HolderConjugate p q` alone. The earlier `2 ≤ p` hypothesis was
inert and has been removed so the lemma applies symmetrically in the
two ranges `1 < p ≤ 2` and `2 ≤ p < ∞`.

Adapted from `LpSpaces.LpDualityRN.representer_memLq_and_norm_le`. -/
theorem representer_memLq_and_norm_le {p q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (hp_gt_one : 1 < p) (hp_ne_top : p ≠ ∞)
    (φ : LpPer p d →L[ℝ] ℝ)
    (g : (Fin d → ℝ) → ℝ)
    (hg_aesm : AEStronglyMeasurable g
      (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)))
    (hrepr_bdd : ∀ (h : LpPer p d) (M : ℝ),
      (∀ᵐ x ∂(Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)),
          ‖h x‖ ≤ M) →
      φ h = ∫ x, h x * g x
        ∂(Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d))) :
    MemLp g q (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) ∧
    eLpNorm g q (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d))
      ≤ ENNReal.ofReal ‖φ‖ := by
  set μ : Measure (Fin d → ℝ) := Measure.restrict volume (UnitCube d) with hμ_def
  -- Real exponents and basic comparisons.
  have hp_ne_zero : p ≠ 0 := by
    intro h; rw [h] at hp_gt_one; exact absurd hp_gt_one (by norm_num)
  have hq_lt_top : q < ∞ := by
    rw [ENNReal.HolderConjugate.lt_top_iff_one_lt q p]; exact hp_gt_one
  have hq_ne_top : q ≠ ∞ := hq_lt_top.ne
  have hq_ne_zero : q ≠ 0 := ENNReal.HolderConjugate.ne_zero q p
  set pr : ℝ := p.toReal with hpr_def
  set qr : ℝ := q.toReal with hqr_def
  have hp_pos : 0 < pr := ENNReal.toReal_pos hp_ne_zero hp_ne_top
  have hq_pos : 0 < qr := ENNReal.toReal_pos hq_ne_zero hq_ne_top
  have hpr_gt_one : 1 < pr := by
    have : (1 : ℝ≥0∞).toReal < p.toReal :=
      (ENNReal.toReal_lt_toReal (by norm_num) hp_ne_top).mpr hp_gt_one
    simpa using this
  -- Hölder identity at the real level.
  have h_inv_sum : 1 / pr + 1 / qr = 1 := by
    have h_inv : p⁻¹ + q⁻¹ = 1 := ENNReal.HolderConjugate.inv_add_inv_eq_one p q
    have h1 := congrArg ENNReal.toReal h_inv
    have h2 : (p⁻¹).toReal = p.toReal⁻¹ := ENNReal.toReal_inv _
    have h3 : (q⁻¹).toReal = q.toReal⁻¹ := ENNReal.toReal_inv _
    have h4 : (p⁻¹ + q⁻¹).toReal = (p⁻¹).toReal + (q⁻¹).toReal := by
      apply ENNReal.toReal_add
      · simp [hp_ne_zero]
      · simp [hq_ne_zero]
    rw [h4, h2, h3] at h1
    have h_inv_sum' : pr⁻¹ + qr⁻¹ = 1 := by simpa using h1
    rw [one_div, one_div]; exact h_inv_sum'
  have hconj : pr * (qr - 1) = qr := by
    -- From `1/pr + 1/qr = 1` derive `pr (qr - 1) = qr`.
    have hpr_ne : pr ≠ 0 := hp_pos.ne'
    have hqr_ne : qr ≠ 0 := hq_pos.ne'
    have h := h_inv_sum
    field_simp at h
    linarith
  have hqr_gt_one : 1 < qr := by
    have h1 : qr = pr / (pr - 1) := by
      have hpr1 : 0 < pr - 1 := by linarith
      field_simp at hconj ⊢
      linarith
    rw [h1, lt_div_iff₀ (by linarith : (0 : ℝ) < pr - 1)]
    linarith
  have hqr_ge_one : 1 ≤ qr := le_of_lt hqr_gt_one
  -- For each `n`, the truncated saturator is in `Lᵖ`. Lift to `LpPer p d`.
  have h_mem_p : ∀ n : ℕ, MemLp (satRNTruncated qr g n) p μ :=
    fun n => memLp_satRNTruncated hg_aesm qr hqr_ge_one n p
  set hn_p : ℕ → LpPer p d := fun n => (h_mem_p n).toLp _ with hn_p_def
  -- Truncated lintegral.
  set I : ℕ → ℝ≥0∞ := fun n =>
    ∫⁻ x, ENNReal.ofReal
      (if g x = 0 ∨ (n : ℝ) < |g x| then 0 else |g x| ^ qr) ∂μ with hI_def
  -- AEMeasurability of the integrand of `I n`.
  have h_aemeas_enn : ∀ n : ℕ, AEMeasurable
      (fun x => ENNReal.ofReal
        (if g x = 0 ∨ (n : ℝ) < |g x| then 0 else |g x| ^ qr)) μ := by
    intro n
    set g' := hg_aesm.mk g with hg'_def
    have hg'_meas : StronglyMeasurable g' := hg_aesm.stronglyMeasurable_mk
    have hg'_ae : g =ᵐ[μ] g' := hg_aesm.ae_eq_mk
    have h_ae :
        (fun x => ENNReal.ofReal
          (if g x = 0 ∨ (n : ℝ) < |g x| then 0 else |g x| ^ qr))
        =ᵐ[μ] (fun x => ENNReal.ofReal
          (if g' x = 0 ∨ (n : ℝ) < |g' x| then 0 else |g' x| ^ qr)) := by
      filter_upwards [hg'_ae] with x hx
      simp [hx]
    refine AEMeasurable.congr ?_ h_ae.symm
    have h_zero : MeasurableSet {x : (Fin d → ℝ) | g' x = 0} :=
      measurableSet_eq_fun hg'_meas.measurable measurable_const
    have h_abs : Measurable fun x => |g' x| :=
      _root_.continuous_abs.measurable.comp hg'_meas.measurable
    have h_big : MeasurableSet {x : (Fin d → ℝ) | (n : ℝ) < |g' x|} :=
      measurableSet_lt measurable_const h_abs
    have h_or : MeasurableSet {x : (Fin d → ℝ) | g' x = 0 ∨ (n : ℝ) < |g' x|} := by
      have hset : {x : (Fin d → ℝ) | g' x = 0 ∨ (n : ℝ) < |g' x|}
          = {x | g' x = 0} ∪ {x | (n : ℝ) < |g' x|} := by
        ext x; simp [Set.mem_union]
      rw [hset]; exact h_zero.union h_big
    -- We use the same measurability tunnel as in the saturator file.
    have h_rpow : Measurable (fun x => ((ENNReal.ofReal |g' x|) ^ qr).toReal) := by
      have : Measurable (fun t : ℝ => ((ENNReal.ofReal |t|) ^ qr).toReal) := by
        apply ENNReal.measurable_toReal.comp
        apply (ENNReal.continuous_rpow_const).measurable.comp
        exact ENNReal.measurable_ofReal.comp _root_.continuous_abs.measurable
      exact this.comp hg'_meas.measurable
    have h_ite : Measurable (fun x => if g' x = 0 ∨ (n : ℝ) < |g' x|
        then (0 : ℝ) else ((ENNReal.ofReal |g' x|) ^ qr).toReal) :=
      Measurable.ite h_or measurable_const h_rpow
    have h_eq : (fun x => ENNReal.ofReal
        (if g' x = 0 ∨ (n : ℝ) < |g' x| then 0 else |g' x| ^ qr))
        = (fun x => ENNReal.ofReal
            (if g' x = 0 ∨ (n : ℝ) < |g' x| then 0
             else ((ENNReal.ofReal |g' x|) ^ qr).toReal)) := by
      funext x
      split_ifs <;> [rfl;
        rw [show ((ENNReal.ofReal |g' x|) ^ qr).toReal = |g' x| ^ qr from by
          rw [← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (abs_nonneg _)]]]
    rw [h_eq]
    exact (ENNReal.measurable_ofReal.comp h_ite).aemeasurable
  -- Finiteness of `I n`.
  have h_I_ne_top : ∀ n : ℕ, I n ≠ ∞ := by
    intro n
    refine ne_of_lt ?_
    have h_le : ∀ x, ENNReal.ofReal
        (if g x = 0 ∨ (n : ℝ) < |g x| then 0 else |g x| ^ qr) ≤
        ENNReal.ofReal ((n : ℝ) ^ qr) := by
      intro x
      apply ENNReal.ofReal_le_ofReal
      split_ifs with h
      · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
      · push_neg at h
        exact Real.rpow_le_rpow (abs_nonneg _) h.2 hq_pos.le
    show (∫⁻ x, ENNReal.ofReal
              (if g x = 0 ∨ (n : ℝ) < |g x| then 0 else |g x| ^ qr) ∂μ) < ∞
    calc ∫⁻ x, ENNReal.ofReal
            (if g x = 0 ∨ (n : ℝ) < |g x| then 0 else |g x| ^ qr) ∂μ
        ≤ ∫⁻ _, ENNReal.ofReal ((n : ℝ) ^ qr) ∂μ := lintegral_mono h_le
      _ = ENNReal.ofReal ((n : ℝ) ^ qr) * μ Set.univ := by rw [lintegral_const]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  -- `(I n).toReal` as a Bochner integral.
  have h_Inn : ∀ n : ℕ, (I n).toReal = ∫ x,
      (if g x = 0 ∨ (n : ℝ) < |g x| then 0 else |g x| ^ qr) ∂μ := by
    intro n
    have := integral_toReal (f := fun x => ENNReal.ofReal
        (if g x = 0 ∨ (n : ℝ) < |g x| then 0 else |g x| ^ qr))
      (h_aemeas_enn n)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)
    show (I n).toReal = _
    rw [show I n = (∫⁻ x, ENNReal.ofReal
            (if g x = 0 ∨ (n : ℝ) < |g x| then 0 else |g x| ^ qr) ∂μ) from rfl]
    rw [← this]
    apply integral_congr_ae
    filter_upwards with x
    rw [ENNReal.toReal_ofReal]
    split_ifs with h
    · linarith
    · exact Real.rpow_nonneg (abs_nonneg _) _
  -- Representer equation evaluated at `hn_p n`.
  have h_repr : ∀ n : ℕ, φ (hn_p n) = (I n).toReal := by
    intro n
    have h_ae : ⇑(hn_p n) =ᵐ[μ] satRNTruncated qr g n :=
      MemLp.coeFn_toLp (h_mem_p n)
    have h_bnd : ∀ᵐ x ∂μ, ‖(hn_p n) x‖ ≤ (n : ℝ) ^ (qr - 1) := by
      filter_upwards [h_ae] with x hx
      rw [hx, Real.norm_eq_abs]
      exact abs_satRNTruncated_le qr hqr_ge_one g n x
    rw [hrepr_bdd (hn_p n) ((n : ℝ) ^ (qr - 1)) h_bnd]
    rw [h_Inn n]
    apply integral_congr_ae
    filter_upwards [h_ae] with x hx
    rw [hx]
    exact satRNTruncated_mul_self hq_pos g n x
  -- `Lᵖ` norm of `hn_p n` equals `(I n)^(1/pr)`.
  have h_eLpNorm_p : ∀ n : ℕ,
      eLpNorm (⇑(hn_p n)) p μ = (I n) ^ (1 / pr) := by
    intro n
    have h_ae : ⇑(hn_p n) =ᵐ[μ] satRNTruncated qr g n :=
      MemLp.coeFn_toLp (h_mem_p n)
    rw [eLpNorm_congr_ae h_ae]
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_ne_top (h_mem_p n).aestronglyMeasurable]
    show (∫⁻ x, ‖satRNTruncated qr g n x‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal) = _
    change (∫⁻ x, ‖satRNTruncated qr g n x‖ₑ ^ pr ∂μ) ^ (1 / pr) = _
    congr 1
    apply lintegral_congr_ae
    filter_upwards with x
    have h_key : |satRNTruncated qr g n x| ^ pr
        = (if g x = 0 ∨ (n : ℝ) < |g x| then 0 else |g x| ^ qr) :=
      abs_satRNTruncated_rpow hpr_gt_one hqr_gt_one hconj g n x
    rw [Real.enorm_eq_ofReal_abs]
    rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp_pos.le]
    rw [h_key]
  -- Key inequality: `(I n).toReal ≤ ‖φ‖ · (I n).toReal^(1/pr)`.
  have h_key_ineq : ∀ n : ℕ,
      (I n).toReal ≤ ‖φ‖ * (I n).toReal ^ (1 / pr) := by
    intro n
    have h1 : |φ (hn_p n)| ≤ ‖φ‖ * ‖hn_p n‖ := by
      have := φ.le_opNorm (hn_p n)
      simpa [Real.norm_eq_abs] using this
    rw [h_repr n] at h1
    have h_In_nn : 0 ≤ (I n).toReal := ENNReal.toReal_nonneg
    rw [abs_of_nonneg h_In_nn] at h1
    have h_norm_eq : ‖hn_p n‖ = (I n).toReal ^ (1 / pr) := by
      rw [Lp.norm_def, h_eLpNorm_p n, ENNReal.toReal_rpow]
    rw [h_norm_eq] at h1
    exact h1
  -- `(I n)^(1/qr) ≤ ‖φ‖`.
  have h_bound_n : ∀ n : ℕ, (I n).toReal ^ (1 / qr) ≤ ‖φ‖ := by
    intro n
    have h_In_nn : 0 ≤ (I n).toReal := ENNReal.toReal_nonneg
    rcases eq_or_lt_of_le h_In_nn with hI0 | hI_pos
    · rw [← hI0]
      rw [Real.zero_rpow (by simp [one_div, hq_pos.ne'] : (1 / qr) ≠ 0)]
      exact norm_nonneg _
    · have h := h_key_ineq n
      have h_pos : 0 < (I n).toReal ^ (1 / pr) := Real.rpow_pos_of_pos hI_pos _
      have h_split : (I n).toReal
          = (I n).toReal ^ (1 / pr) * (I n).toReal ^ (1 / qr) := by
        rw [← Real.rpow_add hI_pos, h_inv_sum, Real.rpow_one]
      have h' : (I n).toReal ^ (1 / pr) * (I n).toReal ^ (1 / qr) ≤
          ‖φ‖ * (I n).toReal ^ (1 / pr) := by
        rw [← h_split]; exact h
      rw [mul_comm ‖φ‖ _] at h'
      exact le_of_mul_le_mul_left h' h_pos
  -- `J := ∫⁻ |g|^qr` and monotone convergence `I n ↑ J`.
  set J : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (|g x| ^ qr) ∂μ with hJ_def
  have h_tendsto_I : Filter.Tendsto I Filter.atTop (nhds J) := by
    apply lintegral_tendsto_of_tendsto_of_monotone
    · intro n; exact h_aemeas_enn n
    · filter_upwards with x
      intro n m hnm
      apply ENNReal.ofReal_le_ofReal
      split_ifs with h1 h2 h2
      · exact le_refl _
      · exact Real.rpow_nonneg (abs_nonneg _) _
      · exfalso
        push_neg at h1
        rcases h2 with hg0 | hbig
        · exact h1.1 hg0
        · have h_cast : (n : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hnm
          linarith [h1.2]
      · exact le_refl _
    · filter_upwards with x
      rcases eq_or_ne (g x) 0 with hg0 | hg0
      · have h_g0 : |g x| ^ qr = 0 := by
          rw [hg0, abs_zero]; exact Real.zero_rpow hq_pos.ne'
        have h_eq_const : ∀ n : ℕ, ENNReal.ofReal
            (if g x = 0 ∨ (n : ℝ) < |g x| then 0 else |g x| ^ qr) = 0 := by
          intro n; simp [hg0]
        simp_rw [h_eq_const]
        rw [h_g0]; simp
      · obtain ⟨N, hN⟩ := exists_nat_ge (|g x|)
        apply Filter.Tendsto.congr' (f₁ := fun _ => ENNReal.ofReal (|g x| ^ qr))
        · refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
          have h_le : |g x| ≤ (n : ℝ) := hN.trans (Nat.cast_le.mpr hn)
          have h_not : ¬ (g x = 0 ∨ (n : ℝ) < |g x|) := by
            push_neg; exact ⟨hg0, h_le⟩
          simp [h_not]
        · exact tendsto_const_nhds
  -- `J ≤ (ENNReal.ofReal ‖φ‖) ^ qr`.
  have h_phi_nn : 0 ≤ ‖φ‖ := norm_nonneg _
  have h_J_le : J ≤ (ENNReal.ofReal ‖φ‖) ^ qr := by
    have h_I_le_phi : ∀ n : ℕ, I n ≤ (ENNReal.ofReal ‖φ‖) ^ qr := by
      intro n
      have h_In_ne_top : I n ≠ ∞ := h_I_ne_top n
      have h_bn := h_bound_n n
      have h_In_nn : 0 ≤ (I n).toReal := ENNReal.toReal_nonneg
      have h_bn' : (I n).toReal ≤ ‖φ‖ ^ qr := by
        have h2 : ((I n).toReal ^ (1 / qr)) ^ qr ≤ ‖φ‖ ^ qr :=
          Real.rpow_le_rpow (Real.rpow_nonneg h_In_nn _) h_bn hq_pos.le
        rw [← Real.rpow_mul h_In_nn, one_div, inv_mul_cancel₀ hq_pos.ne',
            Real.rpow_one] at h2
        exact h2
      have h_eq_ofReal : ENNReal.ofReal ((I n).toReal) = I n := by
        rw [ENNReal.ofReal_toReal h_In_ne_top]
      have h_ofReal_le :
          ENNReal.ofReal ((I n).toReal) ≤ ENNReal.ofReal (‖φ‖ ^ qr) :=
        ENNReal.ofReal_le_ofReal h_bn'
      rw [h_eq_ofReal] at h_ofReal_le
      have h_rpow : ENNReal.ofReal (‖φ‖ ^ qr) = (ENNReal.ofReal ‖φ‖) ^ qr := by
        rw [ENNReal.ofReal_rpow_of_nonneg h_phi_nn hq_pos.le]
      rw [h_rpow] at h_ofReal_le
      exact h_ofReal_le
    exact le_of_tendsto' h_tendsto_I h_I_le_phi
  -- Convert to `eLpNorm g q μ ≤ ENNReal.ofReal ‖φ‖`.
  have h_eLp_eq : eLpNorm g q μ = J ^ (1 / qr) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq_ne_zero hq_ne_top hg_aesm]
    show (∫⁻ x, ‖g x‖ₑ ^ q.toReal ∂μ) ^ (1 / q.toReal) = J ^ (1 / qr)
    change (∫⁻ x, ‖g x‖ₑ ^ qr ∂μ) ^ (1 / qr) = J ^ (1 / qr)
    congr 1
    apply lintegral_congr_ae
    filter_upwards with x
    rw [Real.enorm_eq_ofReal_abs]
    rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hq_pos.le]
  have h_norm_final : eLpNorm g q μ ≤ ENNReal.ofReal ‖φ‖ := by
    rw [h_eLp_eq]
    have h1 : J ^ (1 / qr) ≤ ((ENNReal.ofReal ‖φ‖) ^ qr) ^ (1 / qr) := by
      apply ENNReal.rpow_le_rpow h_J_le; positivity
    rw [← ENNReal.rpow_mul, mul_one_div, div_self hq_pos.ne',
        ENNReal.rpow_one] at h1
    exact h1
  refine ⟨?_, h_norm_final⟩
  show eLpNorm g q μ < ∞
  calc eLpNorm g q μ ≤ ENNReal.ofReal ‖φ‖ := h_norm_final
    _ < ∞ := ENNReal.ofReal_lt_top

/-! ## Bounded-`Lp` extension of a simple-function representation (Step 2)

Adapted from `LpSpaces.LpDualityFinitePQ.phi_eq_integral_of_bounded_simple_hyp`
(lines 70-199 of the reference file). Given that the integral identity
`φ s = ∫ s · g` holds for every `Lp.simpleFunc`, this extends the
identity to every bounded `h ∈ Lp` via `MeasureTheory.SimpleFunc.approxOn`
plus the dominated convergence theorem (dominator `M · |g|`, integrable
since `g ∈ L¹`). -/

/-- **Bounded-`Lp` extension of the simple-function identity.**
If `φ s = ∫ s · g` for every `s : Lp.simpleFunc`, the identity extends
to every bounded `h ∈ LpPer p d` on the unit cube. Adapted from
`LpSpaces.LpDualityFinitePQ.phi_eq_integral_of_bounded_simple_hyp`. -/
theorem phi_eq_integral_of_bounded_simple_hyp
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp_ne_top : p ≠ ∞)
    (φ : LpPer p d →L[ℝ] ℝ)
    (g : (Fin d → ℝ) → ℝ)
    (hg_int : Integrable g
      (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)))
    (hsimple : ∀ s : Lp.simpleFunc ℝ p
        (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)),
      φ ((s : LpPer p d)) =
        ∫ x, ((s : LpPer p d)) x * g x
          ∂(Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)))
    (h : LpPer p d) (M : ℝ) (hM_nn : 0 ≤ M)
    (hM_bd : ∀ᵐ x ∂(Measure.restrict
        (volume : Measure (Fin d → ℝ)) (UnitCube d)), ‖h x‖ ≤ M) :
    φ h = ∫ x, h x * g x
      ∂(Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) := by
  set μ : Measure (Fin d → ℝ) := Measure.restrict volume (UnitCube d) with hμ_def
  -- Measurable representative of `h`.
  set h_meas : (Fin d → ℝ) → ℝ := (Lp.aestronglyMeasurable h).mk h with hhm_def
  have hh_meas_meas : StronglyMeasurable h_meas :=
    (Lp.aestronglyMeasurable h).stronglyMeasurable_mk
  have hh_meas_ae : (h : (Fin d → ℝ) → ℝ) =ᵐ[μ] h_meas :=
    (Lp.aestronglyMeasurable h).ae_eq_mk
  have hh_meas_memLp : MemLp h_meas p μ := (Lp.memLp h).ae_eq hh_meas_ae
  have hh_meas_bd : ∀ᵐ x ∂μ, ‖h_meas x‖ ≤ M := by
    filter_upwards [hM_bd, hh_meas_ae] with x hx hae
    rw [← hae]; exact hx
  -- Target set: `closedBall 0 M`. `0 ∈ s` since `0 ≤ M`.
  set s : Set ℝ := Metric.closedBall 0 M
  have h0_mem : (0 : ℝ) ∈ s := by
    show ‖(0 : ℝ) - 0‖ ≤ M
    simp [hM_nn]
  -- Simple-function approximation `sn` with range in `s`.
  set sn : ℕ → MeasureTheory.SimpleFunc (Fin d → ℝ) ℝ := fun n =>
    SimpleFunc.approxOn h_meas hh_meas_meas.measurable s 0 h0_mem n
  -- Each `sn n x ∈ s`, hence `‖sn n x‖ ≤ M`.
  have hsn_bd : ∀ n x, ‖sn n x‖ ≤ M := by
    intro n x
    have hin : sn n x ∈ s :=
      SimpleFunc.approxOn_mem hh_meas_meas.measurable h0_mem n x
    have hin' : sn n x ∈ Metric.closedBall (0 : ℝ) M := hin
    rw [Metric.mem_closedBall, dist_zero_right] at hin'
    exact hin'
  -- `MemLp` of each `sn`.
  have h0_memLp : MemLp (fun _ : (Fin d → ℝ) => (0 : ℝ)) p μ := memLp_const _
  have hsn_memLp : ∀ n, MemLp (⇑(sn n)) p μ := fun n =>
    SimpleFunc.memLp_approxOn hh_meas_meas.measurable
      hh_meas_memLp h0_mem h0_memLp n
  -- Lp.simpleFunc lifts.
  set sn_Lp : ℕ → Lp.simpleFunc ℝ p μ := fun n =>
    SimpleFunc.toLp (sn n) (hsn_memLp n)
  -- a.e.-convergence: `h_meas x ∈ closure s = s` a.e. by `hh_meas_bd`.
  have h_closure : closure s = s := Metric.isClosed_closedBall.closure_eq
  have hh_meas_in_s : ∀ᵐ x ∂μ, h_meas x ∈ s := by
    filter_upwards [hh_meas_bd] with x hx
    show h_meas x ∈ Metric.closedBall 0 M
    rw [Metric.mem_closedBall, dist_zero_right]; exact hx
  have hsn_ae_conv : ∀ᵐ x ∂μ,
      Filter.Tendsto (fun n => sn n x) Filter.atTop (nhds (h_meas x)) := by
    filter_upwards [hh_meas_in_s] with x hx
    apply SimpleFunc.tendsto_approxOn hh_meas_meas.measurable h0_mem
    rw [h_closure]; exact hx
  -- Lp convergence: `sn → h_meas` in Lp via Mathlib's lemma.
  have hh_meas_in_closure : ∀ᵐ x ∂μ, h_meas x ∈ closure s := by
    filter_upwards [hh_meas_in_s] with x hx; rw [h_closure]; exact hx
  have h_eLp_sub : eLpNorm (fun x => h_meas x - (0 : ℝ)) p μ < ∞ := by
    simp only [sub_zero]; exact hh_meas_memLp
  have hsn_Lp_conv : Filter.Tendsto
      (fun n => eLpNorm (⇑(sn n) - h_meas) p μ) Filter.atTop (nhds 0) :=
    SimpleFunc.tendsto_approxOn_Lp_eLpNorm hh_meas_meas.measurable
      h0_mem hp_ne_top hh_meas_in_closure h_eLp_sub
  -- Lp convergence of sn_Lp to h.
  have h_Lp : Filter.Tendsto (fun n => (sn_Lp n : LpPer p d))
      Filter.atTop (nhds h) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    apply Filter.Tendsto.congr
      (f₁ := fun n => eLpNorm (⇑(sn n) - h_meas) p μ) ?_ hsn_Lp_conv
    intro n
    apply eLpNorm_congr_ae
    have h_coe : ((sn_Lp n : Lp.simpleFunc ℝ p μ) : LpPer p d) =
        (hsn_memLp n).toLp (⇑(sn n)) :=
      Lp.simpleFunc.toLp_eq_toLp _ _
    have h1 : ⇑((sn_Lp n : Lp.simpleFunc ℝ p μ) : LpPer p d) =ᵐ[μ] ⇑(sn n) := by
      rw [h_coe]; exact MemLp.coeFn_toLp _
    have h2 := Lp.coeFn_sub ((sn_Lp n : Lp.simpleFunc ℝ p μ) : LpPer p d) h
    filter_upwards [h1, h2, hh_meas_ae] with x hx1 hx2 hx3
    simp only [Pi.sub_apply] at hx2 ⊢
    rw [hx1, hx3]
  -- φ continuous: φ (sn_Lp n) → φ h.
  have h_phi_lim : Filter.Tendsto (fun n => φ (sn_Lp n : LpPer p d))
      Filter.atTop (nhds (φ h)) :=
    (φ.continuous.tendsto h).comp h_Lp
  -- ∫ sn · g → ∫ h · g via DCT.
  have h_dct : Filter.Tendsto (fun n => ∫ x, sn n x * g x ∂μ)
      Filter.atTop (nhds (∫ x, h x * g x ∂μ)) := by
    set bound : (Fin d → ℝ) → ℝ := fun x => M * |g x|
    have hbound_int : Integrable bound μ := hg_int.abs.const_mul M
    have h_pointwise_ae : ∀ᵐ x ∂μ,
        Filter.Tendsto (fun n => sn n x * g x) Filter.atTop
          (nhds (h x * g x)) := by
      filter_upwards [hsn_ae_conv, hh_meas_ae] with x hx hxh_meas
      have : Filter.Tendsto (fun n => sn n x * g x) Filter.atTop
          (nhds (h_meas x * g x)) :=
        hx.mul_const (g x)
      simpa [hxh_meas] using this
    have h_aesm : ∀ n, AEStronglyMeasurable (fun x => sn n x * g x) μ :=
      fun n => ((sn n).aestronglyMeasurable).mul hg_int.aestronglyMeasurable
    have h_bd_ae : ∀ n, ∀ᵐ x ∂μ, ‖sn n x * g x‖ ≤ bound x := by
      intro n
      filter_upwards with x
      show ‖sn n x * g x‖ ≤ M * |g x|
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right
        (by simpa [Real.norm_eq_abs] using hsn_bd n x) (abs_nonneg _)
    exact MeasureTheory.tendsto_integral_of_dominated_convergence bound h_aesm
      hbound_int h_bd_ae h_pointwise_ae
  -- Combine: φ sn_Lp = ∫ sn · g, take limits.
  have h_eq_each : ∀ n, φ (sn_Lp n : LpPer p d) =
      ∫ x, sn n x * g x ∂μ := by
    intro n
    rw [hsimple (sn_Lp n)]
    apply integral_congr_ae
    have h_coe : ((sn_Lp n : Lp.simpleFunc ℝ p μ) : LpPer p d) =
        (hsn_memLp n).toLp (sn n) :=
      Lp.simpleFunc.toLp_eq_toLp _ _
    have h1 : ⇑((sn_Lp n : Lp.simpleFunc ℝ p μ) : LpPer p d) =ᵐ[μ] sn n := by
      rw [h_coe]; exact MemLp.coeFn_toLp _
    filter_upwards [h1] with x hx
    rw [hx]
  -- Take limits on both sides.
  have h_rhs : Filter.Tendsto (fun n => φ (sn_Lp n : LpPer p d))
      Filter.atTop (nhds (∫ x, h x * g x ∂μ)) := by
    apply h_dct.congr'
    filter_upwards with n
    exact (h_eq_each n).symm
  exact tendsto_nhds_unique h_phi_lim h_rhs

/-! ## a.e. uniqueness of the representer (Step 5)

Adapted from the uniqueness clause of `LpSpaces.LpDualityFinitePQ`'s
`exists_unique_representer`. The argument is independent of the
existence half: given two `Lᵠ` representers of the same functional
the difference satisfies `∫ h · (g₁ - g₂) = 0` for every bounded
`h ∈ Lᵖ`, and the conjugate saturator drives this to `‖g₁ - g₂‖_q = 0`.
-/

/-- **Uniqueness from vanishing integral against bounded `Lᵖ`.**
If `g ∈ Lᵠ` and `∫ h · g = 0` for every bounded `h ∈ Lᵖ`, then
`g =ᵐ 0` on the unit cube. The conjugate saturator on `g` itself is
the universal test function. -/
theorem ae_eq_zero_of_integral_bounded_zero
    {p q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (hp_gt_one : 1 < p) (hp_ne_top : p ≠ ∞)
    (g : (Fin d → ℝ) → ℝ)
    (hg_memLp : MemLp g q
      (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)))
    (hzero : ∀ (h : LpPer p d) (M : ℝ),
      (∀ᵐ x ∂(Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)),
          ‖h x‖ ≤ M) →
      ∫ x, h x * g x
        ∂(Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) = 0) :
    g =ᵐ[Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)] 0 := by
  set μ : Measure (Fin d → ℝ) := Measure.restrict volume (UnitCube d) with hμ_def
  -- Real exponents and their basic comparisons (mirrors
  -- `representer_memLq_and_norm_le`).
  have hp_ne_zero : p ≠ 0 := by
    intro h; rw [h] at hp_gt_one; exact absurd hp_gt_one (by norm_num)
  have hq_lt_top : q < ∞ := by
    rw [ENNReal.HolderConjugate.lt_top_iff_one_lt q p]; exact hp_gt_one
  have hq_ne_top : q ≠ ∞ := hq_lt_top.ne
  have hq_ne_zero : q ≠ 0 := ENNReal.HolderConjugate.ne_zero q p
  set pr : ℝ := p.toReal with hpr_def
  set qr : ℝ := q.toReal with hqr_def
  have hp_pos : 0 < pr := ENNReal.toReal_pos hp_ne_zero hp_ne_top
  have hq_pos : 0 < qr := ENNReal.toReal_pos hq_ne_zero hq_ne_top
  have hpr_gt_one : 1 < pr := by
    have : (1 : ℝ≥0∞).toReal < p.toReal :=
      (ENNReal.toReal_lt_toReal (by norm_num) hp_ne_top).mpr hp_gt_one
    simpa using this
  have hqr_gt_one : 1 < qr := by
    have : (1 : ℝ≥0∞).toReal < q.toReal :=
      (ENNReal.toReal_lt_toReal (by norm_num) hq_ne_top).mpr
        ((ENNReal.HolderConjugate.lt_top_iff_one_lt p q).mp
          (lt_of_le_of_ne le_top hp_ne_top))
    simpa using this
  have hqr_ge_one : 1 ≤ qr := le_of_lt hqr_gt_one
  -- Hölder identity at the real level.
  have h_inv_sum : 1 / pr + 1 / qr = 1 := by
    have h_inv : p⁻¹ + q⁻¹ = 1 := ENNReal.HolderConjugate.inv_add_inv_eq_one p q
    have h1 := congrArg ENNReal.toReal h_inv
    have h2 : (p⁻¹).toReal = p.toReal⁻¹ := ENNReal.toReal_inv _
    have h3 : (q⁻¹).toReal = q.toReal⁻¹ := ENNReal.toReal_inv _
    have h4 : (p⁻¹ + q⁻¹).toReal = (p⁻¹).toReal + (q⁻¹).toReal := by
      apply ENNReal.toReal_add
      · simp [hp_ne_zero]
      · simp [hq_ne_zero]
    rw [h4, h2, h3] at h1
    have h_inv_sum' : pr⁻¹ + qr⁻¹ = 1 := by simpa using h1
    rw [one_div, one_div]; exact h_inv_sum'
  have hconj : pr * (qr - 1) = qr := by
    have h := h_inv_sum
    field_simp at h
    linarith
  -- Strong measurability of `g`.
  have hg_aesm : AEStronglyMeasurable g μ := hg_memLp.aestronglyMeasurable
  -- Truncated saturator is in `Lᵖ` for every `n`.
  have h_mem_p : ∀ n : ℕ, MemLp (satRNTruncated qr g n) p μ :=
    fun n => memLp_satRNTruncated hg_aesm qr hqr_ge_one n p
  set hn_p : ℕ → LpPer p d := fun n => (h_mem_p n).toLp _ with hn_p_def
  -- Truncated lintegral and its toReal.
  set I : ℕ → ℝ≥0∞ := fun n =>
    ∫⁻ x, ENNReal.ofReal
      (if g x = 0 ∨ (n : ℝ) < |g x| then 0 else |g x| ^ qr) ∂μ with hI_def
  -- AEMeasurability of the integrand.
  have h_aemeas_enn : ∀ n : ℕ, AEMeasurable
      (fun x => ENNReal.ofReal
        (if g x = 0 ∨ (n : ℝ) < |g x| then 0 else |g x| ^ qr)) μ := by
    intro n
    set g' := hg_aesm.mk g with hg'_def
    have hg'_meas : StronglyMeasurable g' := hg_aesm.stronglyMeasurable_mk
    have hg'_ae : g =ᵐ[μ] g' := hg_aesm.ae_eq_mk
    have h_ae :
        (fun x => ENNReal.ofReal
          (if g x = 0 ∨ (n : ℝ) < |g x| then 0 else |g x| ^ qr))
        =ᵐ[μ] (fun x => ENNReal.ofReal
          (if g' x = 0 ∨ (n : ℝ) < |g' x| then 0 else |g' x| ^ qr)) := by
      filter_upwards [hg'_ae] with x hx
      simp [hx]
    refine AEMeasurable.congr ?_ h_ae.symm
    have h_zero : MeasurableSet {x : (Fin d → ℝ) | g' x = 0} :=
      measurableSet_eq_fun hg'_meas.measurable measurable_const
    have h_abs : Measurable fun x => |g' x| :=
      _root_.continuous_abs.measurable.comp hg'_meas.measurable
    have h_big : MeasurableSet {x : (Fin d → ℝ) | (n : ℝ) < |g' x|} :=
      measurableSet_lt measurable_const h_abs
    have h_or : MeasurableSet {x : (Fin d → ℝ) | g' x = 0 ∨ (n : ℝ) < |g' x|} := by
      have hset : {x : (Fin d → ℝ) | g' x = 0 ∨ (n : ℝ) < |g' x|}
          = {x | g' x = 0} ∪ {x | (n : ℝ) < |g' x|} := by
        ext x; simp [Set.mem_union]
      rw [hset]; exact h_zero.union h_big
    have h_rpow : Measurable (fun x => ((ENNReal.ofReal |g' x|) ^ qr).toReal) := by
      have : Measurable (fun t : ℝ => ((ENNReal.ofReal |t|) ^ qr).toReal) := by
        apply ENNReal.measurable_toReal.comp
        apply (ENNReal.continuous_rpow_const).measurable.comp
        exact ENNReal.measurable_ofReal.comp _root_.continuous_abs.measurable
      exact this.comp hg'_meas.measurable
    have h_ite : Measurable (fun x => if g' x = 0 ∨ (n : ℝ) < |g' x|
        then (0 : ℝ) else ((ENNReal.ofReal |g' x|) ^ qr).toReal) :=
      Measurable.ite h_or measurable_const h_rpow
    have h_eq : (fun x => ENNReal.ofReal
        (if g' x = 0 ∨ (n : ℝ) < |g' x| then 0 else |g' x| ^ qr))
        = (fun x => ENNReal.ofReal
            (if g' x = 0 ∨ (n : ℝ) < |g' x| then 0
             else ((ENNReal.ofReal |g' x|) ^ qr).toReal)) := by
      funext x
      split_ifs <;> [rfl;
        rw [show ((ENNReal.ofReal |g' x|) ^ qr).toReal = |g' x| ^ qr from by
          rw [← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (abs_nonneg _)]]]
    rw [h_eq]
    exact (ENNReal.measurable_ofReal.comp h_ite).aemeasurable
  -- Each `I n` is finite.
  have h_I_ne_top : ∀ n : ℕ, I n ≠ ∞ := by
    intro n
    refine ne_of_lt ?_
    have h_le : ∀ x, ENNReal.ofReal
        (if g x = 0 ∨ (n : ℝ) < |g x| then 0 else |g x| ^ qr) ≤
        ENNReal.ofReal ((n : ℝ) ^ qr) := by
      intro x
      apply ENNReal.ofReal_le_ofReal
      split_ifs with h
      · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
      · push_neg at h
        exact Real.rpow_le_rpow (abs_nonneg _) h.2 hq_pos.le
    show (∫⁻ x, ENNReal.ofReal
              (if g x = 0 ∨ (n : ℝ) < |g x| then 0 else |g x| ^ qr) ∂μ) < ∞
    calc ∫⁻ x, ENNReal.ofReal
            (if g x = 0 ∨ (n : ℝ) < |g x| then 0 else |g x| ^ qr) ∂μ
        ≤ ∫⁻ _, ENNReal.ofReal ((n : ℝ) ^ qr) ∂μ := lintegral_mono h_le
      _ = ENNReal.ofReal ((n : ℝ) ^ qr) * μ Set.univ := by rw [lintegral_const]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  -- `(I n).toReal` as a Bochner integral (mirror of the same step
  -- in `representer_memLq_and_norm_le`).
  have h_Inn : ∀ n : ℕ, (I n).toReal = ∫ x,
      (if g x = 0 ∨ (n : ℝ) < |g x| then 0 else |g x| ^ qr) ∂μ := by
    intro n
    have := integral_toReal (f := fun x => ENNReal.ofReal
        (if g x = 0 ∨ (n : ℝ) < |g x| then 0 else |g x| ^ qr))
      (h_aemeas_enn n)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)
    show (I n).toReal = _
    rw [show I n = (∫⁻ x, ENNReal.ofReal
            (if g x = 0 ∨ (n : ℝ) < |g x| then 0 else |g x| ^ qr) ∂μ) from rfl]
    rw [← this]
    apply integral_congr_ae
    filter_upwards with x
    rw [ENNReal.toReal_ofReal]
    split_ifs with h
    · linarith
    · exact Real.rpow_nonneg (abs_nonneg _) _
  -- Hypothesis evaluated at `hn_p n` gives `(I n).toReal = 0`.
  have h_zero_each : ∀ n : ℕ, (I n).toReal = 0 := by
    intro n
    have h_ae : ⇑(hn_p n) =ᵐ[μ] satRNTruncated qr g n :=
      MemLp.coeFn_toLp (h_mem_p n)
    have h_bnd : ∀ᵐ x ∂μ, ‖(hn_p n) x‖ ≤ (n : ℝ) ^ (qr - 1) := by
      filter_upwards [h_ae] with x hx
      rw [hx, Real.norm_eq_abs]
      exact abs_satRNTruncated_le qr hqr_ge_one g n x
    have hint_eq_zero := hzero (hn_p n) ((n : ℝ) ^ (qr - 1)) h_bnd
    have h_int_eq : ∫ x, (hn_p n) x * g x ∂μ =
        ∫ x, (if g x = 0 ∨ (n : ℝ) < |g x| then 0 else |g x| ^ qr) ∂μ := by
      apply integral_congr_ae
      filter_upwards [h_ae] with x hx
      rw [hx]
      exact satRNTruncated_mul_self hq_pos g n x
    rw [h_Inn n, ← h_int_eq, hint_eq_zero]
  -- Hence each `I n = 0`.
  have h_I_eq_zero : ∀ n : ℕ, I n = 0 := by
    intro n
    have h_ne_top : I n ≠ ∞ := h_I_ne_top n
    rw [← ENNReal.ofReal_toReal h_ne_top, h_zero_each n, ENNReal.ofReal_zero]
  -- `J := ∫⁻ |g|^qr` and monotone convergence `I n ↑ J`.
  set J : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (|g x| ^ qr) ∂μ with hJ_def
  have h_tendsto_I : Filter.Tendsto I Filter.atTop (nhds J) := by
    apply lintegral_tendsto_of_tendsto_of_monotone
    · intro n; exact h_aemeas_enn n
    · filter_upwards with x
      intro n m hnm
      apply ENNReal.ofReal_le_ofReal
      split_ifs with h1 h2 h2
      · exact le_refl _
      · exact Real.rpow_nonneg (abs_nonneg _) _
      · exfalso
        push_neg at h1
        rcases h2 with hg0 | hbig
        · exact h1.1 hg0
        · have h_cast : (n : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hnm
          linarith [h1.2]
      · exact le_refl _
    · filter_upwards with x
      rcases eq_or_ne (g x) 0 with hg0 | hg0
      · have h_g0 : |g x| ^ qr = 0 := by
          rw [hg0, abs_zero]; exact Real.zero_rpow hq_pos.ne'
        have h_eq_const : ∀ n : ℕ, ENNReal.ofReal
            (if g x = 0 ∨ (n : ℝ) < |g x| then 0 else |g x| ^ qr) = 0 := by
          intro n; simp [hg0]
        simp_rw [h_eq_const]
        rw [h_g0]; simp
      · obtain ⟨N, hN⟩ := exists_nat_ge (|g x|)
        apply Filter.Tendsto.congr' (f₁ := fun _ => ENNReal.ofReal (|g x| ^ qr))
        · refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
          have h_le : |g x| ≤ (n : ℝ) := hN.trans (Nat.cast_le.mpr hn)
          have h_not : ¬ (g x = 0 ∨ (n : ℝ) < |g x|) := by
            push_neg; exact ⟨hg0, h_le⟩
          simp [h_not]
        · exact tendsto_const_nhds
  -- From `I n = 0` for all `n` and `I n → J`, conclude `J = 0`.
  have h_J_zero : J = 0 := by
    have h_const : (fun _ : ℕ => (0 : ℝ≥0∞)) = I := by
      funext n; exact (h_I_eq_zero n).symm
    have : Filter.Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) Filter.atTop (nhds J) := by
      rw [h_const]; exact h_tendsto_I
    exact tendsto_nhds_unique this tendsto_const_nhds
  -- Convert to `eLpNorm g q μ = 0`.
  have h_eLp_eq : eLpNorm g q μ = J ^ (1 / qr) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq_ne_zero hq_ne_top hg_aesm]
    show (∫⁻ x, ‖g x‖ₑ ^ q.toReal ∂μ) ^ (1 / q.toReal) = J ^ (1 / qr)
    change (∫⁻ x, ‖g x‖ₑ ^ qr ∂μ) ^ (1 / qr) = J ^ (1 / qr)
    congr 1
    apply lintegral_congr_ae
    filter_upwards with x
    rw [Real.enorm_eq_ofReal_abs]
    rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hq_pos.le]
  have h_eLp_zero : eLpNorm g q μ = 0 := by
    rw [h_eLp_eq, h_J_zero]
    exact ENNReal.zero_rpow_of_pos (by positivity)
  -- Conclude `g =ᵐ 0` via `eLpNorm_eq_zero_iff`.
  exact (eLpNorm_eq_zero_iff hq_ne_zero).mp h_eLp_zero

/-- **Uniqueness of the `Lᵠ` representer (a.e.).** Two `Lᵠ`
candidate representers of the same continuous linear functional on
`LpPer p d` agree almost everywhere. The hypothesis
`heq` only needs to hold on bounded `Lᵖ` test functions; this is the
shape supplied by `representer_memLq_and_norm_le` and friends.

Subtracting the two integrals and applying
`ae_eq_zero_of_integral_bounded_zero` to `g₁ - g₂` finishes the
proof. -/
theorem unique_representer_ae
    {p q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (hp_gt_one : 1 < p) (hp_ne_top : p ≠ ∞)
    (g₁ g₂ : (Fin d → ℝ) → ℝ)
    (hg₁ : MemLp g₁ q
      (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)))
    (hg₂ : MemLp g₂ q
      (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)))
    (heq : ∀ (h : LpPer p d) (M : ℝ),
      (∀ᵐ x ∂(Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)),
          ‖h x‖ ≤ M) →
      ∫ x, h x * g₁ x
        ∂(Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) =
      ∫ x, h x * g₂ x
        ∂(Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d))) :
    g₁ =ᵐ[Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)] g₂ := by
  set μ : Measure (Fin d → ℝ) := Measure.restrict volume (UnitCube d) with hμ_def
  -- Apply the vanishing-integral lemma to `g₁ - g₂`.
  have h_diff_memLp : MemLp (fun x => g₁ x - g₂ x) q μ := hg₁.sub hg₂
  -- Hypothesis on the difference.
  have h_zero_diff : ∀ (h : LpPer p d) (M : ℝ),
      (∀ᵐ x ∂μ, ‖h x‖ ≤ M) →
      ∫ x, h x * (g₁ x - g₂ x) ∂μ = 0 := by
    intro h M hM
    -- Hölder's inequality / direct integrability: bounded `h` times
    -- `Lᵠ` function is integrable.
    have hh_aesm : AEStronglyMeasurable h μ := Lp.aestronglyMeasurable h
    -- bounded * Lq, and μ finite ⇒ Lq ⊆ L¹. So this is integrable.
    have hq_lt_top : q < ∞ := by
      rw [ENNReal.HolderConjugate.lt_top_iff_one_lt q p]; exact hp_gt_one
    have h_one_le_q : (1 : ℝ≥0∞) ≤ q := (Fact.out : (1 : ℝ≥0∞) ≤ q)
    have hg₁_int : Integrable g₁ μ :=
      (hg₁.mono_exponent h_one_le_q).integrable le_rfl
    have hg₂_int : Integrable g₂ μ :=
      (hg₂.mono_exponent h_one_le_q).integrable le_rfl
    have h_bound : ∀ (g : (Fin d → ℝ) → ℝ),
        ∀ᵐ x ∂μ, ‖h x * g x‖ ≤ ‖M * ‖g x‖‖ := by
      intro g
      filter_upwards [hM] with x hx
      have hM_nn : 0 ≤ M := (norm_nonneg _).trans hx
      have h_nn : 0 ≤ M * ‖g x‖ := mul_nonneg hM_nn (norm_nonneg _)
      have h1 : ‖h x * g x‖ = ‖h x‖ * ‖g x‖ := norm_mul _ _
      have h2 : ‖M * ‖g x‖‖ = M * ‖g x‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg h_nn]
      rw [h1, h2]
      exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
    have hint₁ : Integrable (fun x => h x * g₁ x) μ := by
      refine ⟨hh_aesm.mul hg₁.aestronglyMeasurable, ?_⟩
      exact ((hg₁_int.norm.const_mul M).2).mono (h_bound g₁)
    have hint₂ : Integrable (fun x => h x * g₂ x) μ := by
      refine ⟨hh_aesm.mul hg₂.aestronglyMeasurable, ?_⟩
      exact ((hg₂_int.norm.const_mul M).2).mono (h_bound g₂)
    -- Distribute the integral.
    have h_split : ∫ x, h x * (g₁ x - g₂ x) ∂μ
        = (∫ x, h x * g₁ x ∂μ) - (∫ x, h x * g₂ x ∂μ) := by
      have : ∀ x, h x * (g₁ x - g₂ x) = h x * g₁ x - h x * g₂ x := by
        intro x; ring
      simp_rw [this]
      exact integral_sub hint₁ hint₂
    rw [h_split, heq h M hM, sub_self]
  -- Apply `ae_eq_zero_of_integral_bounded_zero`.
  have h_diff_zero : (fun x => g₁ x - g₂ x) =ᵐ[μ] 0 :=
    ae_eq_zero_of_integral_bounded_zero hp_gt_one hp_ne_top
      (fun x => g₁ x - g₂ x) h_diff_memLp h_zero_diff
  filter_upwards [h_diff_zero] with x hx
  have : g₁ x - g₂ x = 0 := hx
  linarith

/-! ## L² ↪ Lᵖ inclusion on the unit cube (Part A foundation)

Adapted from `LpSpaces.LpDualityFinite.L2On.inclusionLp` (whole-space
version). On the unit cube `[0, 1)^d`, which has total measure `1`, the
finite-measure Hölder inclusion `L²(μ) ⊂ Lᵖ(μ)` for `1 ≤ p ≤ 2`
collapses the prefactor `μ(univ) ^ (1/p - 1/2)` to `1`. We package
the resulting map as a continuous linear map. -/

/-- **Inclusion `L² ↪ Lᵖ` on the unit cube** for `1 ≤ p ≤ 2`. The
underlying function is preserved a.e.; the operator norm is `≤ 1`
because `volume (UnitCube d) = 1`. -/
def inclusionL2ToLp {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp_le_two : p ≤ 2) :
    LpPer 2 d →L[ℝ] LpPer p d := by
  -- Underlying function builder.
  set μ : Measure (Fin d → ℝ) := Measure.restrict volume (UnitCube d) with hμ_def
  haveI : IsFiniteMeasure μ := Saturator.instIsFiniteMeasureRestrictUnitCube
  refine LinearMap.mkContinuous
    { toFun := fun f => (MemLp.mono_exponent (Lp.memLp f) hp_le_two).toLp ⇑f
      map_add' := ?_
      map_smul' := ?_ }
    1 ?_
  · -- additivity
    intro f g
    apply Lp.ext
    have h1 : ⇑((MemLp.mono_exponent (Lp.memLp (f + g)) hp_le_two).toLp ⇑(f + g))
        =ᵐ[μ] ⇑(f + g) := MemLp.coeFn_toLp _
    have h2 : ⇑((MemLp.mono_exponent (Lp.memLp f) hp_le_two).toLp ⇑f)
        =ᵐ[μ] ⇑f := MemLp.coeFn_toLp _
    have h3 : ⇑((MemLp.mono_exponent (Lp.memLp g) hp_le_two).toLp ⇑g)
        =ᵐ[μ] ⇑g := MemLp.coeFn_toLp _
    have hfg := Lp.coeFn_add f g
    have hadd := Lp.coeFn_add
      ((MemLp.mono_exponent (Lp.memLp f) hp_le_two).toLp ⇑f)
      ((MemLp.mono_exponent (Lp.memLp g) hp_le_two).toLp ⇑g)
    filter_upwards [h1, h2, h3, hfg, hadd] with x hx1 hx2 hx3 hxfg hxadd
    rw [hx1, hxfg, hxadd]
    simp [Pi.add_apply, hx2, hx3]
  · -- ℝ-linearity
    intro c f
    apply Lp.ext
    have h1 : ⇑((MemLp.mono_exponent (Lp.memLp (c • f)) hp_le_two).toLp ⇑(c • f))
        =ᵐ[μ] ⇑(c • f) := MemLp.coeFn_toLp _
    have h2 : ⇑((MemLp.mono_exponent (Lp.memLp f) hp_le_two).toLp ⇑f)
        =ᵐ[μ] ⇑f := MemLp.coeFn_toLp _
    have hcf := Lp.coeFn_smul c f
    have hsmul := Lp.coeFn_smul (E := ℝ) (μ := μ) (p := p) c
      ((MemLp.mono_exponent (Lp.memLp f) hp_le_two).toLp ⇑f)
    filter_upwards [h1, h2, hcf, hsmul] with x hx1 hx2 hxcf hxsmul
    simp only [RingHom.id_apply]
    rw [hx1, hxcf, hxsmul]
    simp [Pi.smul_apply, hx2]
  · -- norm bound: ‖inclusionL2ToLp f‖ ≤ 1 · ‖f‖.
    intro f
    show ‖(MemLp.mono_exponent (Lp.memLp f) hp_le_two).toLp ⇑f‖ ≤ 1 * ‖f‖
    rw [Lp.norm_def, Lp.norm_def, one_mul]
    have h_ae : ⇑((MemLp.mono_exponent (Lp.memLp f) hp_le_two).toLp ⇑f)
        =ᵐ[μ] ⇑f := MemLp.coeFn_toLp _
    rw [eLpNorm_congr_ae h_ae]
    have haesm : AEStronglyMeasurable (⇑f) μ := Lp.aestronglyMeasurable f
    have h_le := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp_le_two haesm
    -- μ univ = 1 ⇒ the prefactor is 1.
    have h_mu : μ Set.univ = 1 := by
      rw [hμ_def, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
          volume_unitCube]
    rw [h_mu, ENNReal.one_rpow, mul_one] at h_le
    have hf_top : eLpNorm (⇑f) 2 μ ≠ ∞ := (Lp.memLp f).eLpNorm_ne_top
    exact ENNReal.toReal_mono hf_top h_le

/-- The inclusion's underlying function is a.e. equal to the L² function. -/
theorem inclusionL2ToLp_coeFn {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp_le_two : p ≤ 2) (f : LpPer 2 d) :
    (inclusionL2ToLp (d := d) (p := p) hp_le_two f
        : (Fin d → ℝ) → ℝ)
      =ᵐ[Measure.restrict volume (UnitCube d)] ⇑f := by
  haveI : IsFiniteMeasure (Measure.restrict (volume : Measure (Fin d → ℝ))
      (UnitCube d)) := Saturator.instIsFiniteMeasureRestrictUnitCube
  exact MemLp.coeFn_toLp (MemLp.mono_exponent (Lp.memLp f) hp_le_two)

/-- **L²-restriction of a continuous linear functional on `Lᵖ`.** For
`1 ≤ p ≤ 2`, every `φ : LpPer p d →L[ℝ] ℝ` restricts to a continuous
linear functional on `LpPer 2 d` by precomposition with the Hölder
inclusion. The Riesz representer of this restriction is the candidate
`g₀` for the general-`p` representer of `φ`. -/
def l2RestrictFunctional {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp_le_two : p ≤ 2)
    (φ : LpPer p d →L[ℝ] ℝ) :
    LpPer 2 d →L[ℝ] ℝ :=
  φ.comp (inclusionL2ToLp (d := d) (p := p) hp_le_two)

@[simp]
theorem l2RestrictFunctional_apply {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp_le_two : p ≤ 2) (φ : LpPer p d →L[ℝ] ℝ) (f : LpPer 2 d) :
    l2RestrictFunctional (d := d) (p := p) hp_le_two φ f =
      φ (inclusionL2ToLp (d := d) (p := p) hp_le_two f) := rfl

/-! ## Existence of the `Lᵠ` representer for `1 < p ≤ 2` (Part A finish)

Combining the building blocks above:
* `exists_unique_representer_L2` provides an L² representer `g₀` for the
  L²-restriction `φ ∘ inclusionL2ToLp`.
* `representer_memLq_and_norm_le` upgrades the L² function to `Lᵠ` and
  bounds `‖g₀‖_q ≤ ‖φ‖`.
* `Lp.induction` extends the integral identity from bounded functions to
  the entire `LpPer p d`.
* Hölder's inequality supplies the matching lower bound `‖φ‖ ≤ ‖g₀‖_q`.

Adapted from `LpSpaces.LpDualityFinite.exists_representer_norm_eq_of_p_le_two`.
-/

/-- **Existence of the `Lᵠ` representer with norm equality** for
`1 < p ≤ 2` on the unit cube. Every continuous linear functional
`φ : LpPer p d →L[ℝ] ℝ` is represented by integration against a
function `g ∈ Lᵠ(μ)`, and the matching `Lᵠ` norm equals `‖φ‖`. -/
theorem exists_representer_norm_eq_of_p_le_two
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (hp_gt_one : 1 < p) (hp_le_two : p ≤ 2) (hp_ne_top : p ≠ ∞)
    (φ : LpPer p d →L[ℝ] ℝ) :
    ∃ g : (Fin d → ℝ) → ℝ,
      MemLp g q (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d))
      ∧ (∀ f : LpPer p d,
          φ f = ∫ x, f x * g x
            ∂(Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)))
      ∧ eLpNorm g q
          (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d))
        = ENNReal.ofReal ‖φ‖ := by
  set μ : Measure (Fin d → ℝ) := Measure.restrict volume (UnitCube d) with hμ_def
  haveI : IsFiniteMeasure μ := Saturator.instIsFiniteMeasureRestrictUnitCube
  -- Real exponent and basic comparisons.
  have hp_ne_zero : p ≠ 0 := by
    intro h; rw [h] at hp_gt_one; exact absurd hp_gt_one (by norm_num)
  have hq_lt_top : q < ∞ := by
    rw [ENNReal.HolderConjugate.lt_top_iff_one_lt q p]; exact hp_gt_one
  have hq_ne_top : q ≠ ∞ := hq_lt_top.ne
  have hq_ne_zero : q ≠ 0 := ENNReal.HolderConjugate.ne_zero q p
  -- Step 1. L² representer of the restricted functional.
  set ψ : LpPer 2 d →L[ℝ] ℝ :=
    l2RestrictFunctional (d := d) (p := p) hp_le_two φ with hψ_def
  obtain ⟨g₀, ⟨hg₀_int, hg₀_norm⟩, _hg₀_uniq⟩ :=
    exists_unique_representer_L2 (d := d) ψ
  set g : (Fin d → ℝ) → ℝ := ⇑g₀ with hg_def
  have hg_aesm : AEStronglyMeasurable g μ := Lp.aestronglyMeasurable g₀
  have hg_memLp_two : MemLp g 2 μ := Lp.memLp g₀
  -- Step 2. Integral identity for **bounded** `h ∈ LpPer p d`.
  have h_bdd_id : ∀ (h : LpPer p d) (M : ℝ),
      (∀ᵐ x ∂μ, ‖h x‖ ≤ M) →
      φ h = ∫ x, h x * g x ∂μ := by
    intro h M hbd
    -- Bounded h ∈ Lp on a finite measure space ⇒ MemLp h 2 μ.
    have hh_aesm : AEStronglyMeasurable (⇑h) μ := Lp.aestronglyMeasurable h
    have hh_memLp_two : MemLp (⇑h) 2 μ := MemLp.of_bound hh_aesm M hbd
    -- Lift to LpPer 2 d.
    set h2 : LpPer 2 d := hh_memLp_two.toLp ⇑h with hh2_def
    have hh2_ae : ⇑h2 =ᵐ[μ] ⇑h := MemLp.coeFn_toLp hh_memLp_two
    -- inclusionL2ToLp h2 = h as elements of LpPer p d (via ext).
    have h_incl_eq : inclusionL2ToLp (d := d) (p := p) hp_le_two h2 = h := by
      apply Lp.ext
      have h1 : ⇑(inclusionL2ToLp (d := d) (p := p) hp_le_two h2) =ᵐ[μ] ⇑h2 :=
        inclusionL2ToLp_coeFn (d := d) (p := p) hp_le_two h2
      filter_upwards [h1, hh2_ae] with x hx1 hx2
      rw [hx1, hx2]
    -- Apply L² identity through the restriction.
    have hψh2 : ψ h2 = ∫ x, h2 x * g x ∂μ := hg₀_int h2
    have hψh2_eq : ψ h2 = φ h := by
      rw [hψ_def, l2RestrictFunctional_apply, h_incl_eq]
    have h_int_eq : ∫ x, h2 x * g x ∂μ = ∫ x, h x * g x ∂μ := by
      apply integral_congr_ae
      filter_upwards [hh2_ae] with x hx
      rw [hx]
    rw [← hψh2_eq, hψh2, h_int_eq]
  -- Step 3. Apply `representer_memLq_and_norm_le`.
  have h_repr_memLq :=
    representer_memLq_and_norm_le (d := d) (p := p) (q := q)
      hp_gt_one hp_ne_top φ g hg_aesm h_bdd_id
  obtain ⟨hg_memLp_q, hg_norm_le⟩ := h_repr_memLq
  -- Step 4. Extend the integral identity to all `f ∈ LpPer p d` via Lp.induction.
  -- The motive: φ f = ∫ f * g.
  -- Since `g ∈ Lᵠ`, the map `f ↦ ∫ f * g` is continuous on `LpPer p d`.
  have h_holder_bound : ∀ f : LpPer p d,
      ‖∫ x, f x * g x ∂μ‖ ≤
        (eLpNorm (⇑f) p μ).toReal * (eLpNorm g q μ).toReal := by
    intro f
    have hf_aesm : AEStronglyMeasurable (⇑f) μ := Lp.aestronglyMeasurable f
    have hf_memLp : MemLp (⇑f) p μ := Lp.memLp f
    -- |∫ f * g| ≤ ∫ |f * g|.
    have h1 : ‖∫ x, f x * g x ∂μ‖ ≤ ∫ x, ‖f x * g x‖ ∂μ :=
      norm_integral_le_integral_norm _
    -- Hölder triple p q 1: f * g ∈ L¹.
    haveI : ENNReal.HolderTriple p q 1 := inferInstance
    have hmemL1 : MemLp (fun x => f x * g x) 1 μ := by
      exact MemLp.fun_mul (μ := μ) (p := p) (q := q) (r := 1)
        hf_memLp hg_memLp_q
    have h_int : Integrable (fun x => ‖f x * g x‖) μ :=
      (memLp_one_iff_integrable.mp hmemL1).norm
    -- ∫ ‖f * g‖ as eLpNorm 1 toReal.
    have h_toReal : ∫ x, ‖f x * g x‖ ∂μ
        = (eLpNorm (fun x => f x * g x) 1 μ).toReal := by
      have h_aesm_mul : AEStronglyMeasurable
          (fun x : (Fin d → ℝ) => f x * g x) μ := hf_aesm.mul hg_aesm
      rw [eLpNorm_one_eq_lintegral_enorm h_aesm_mul]
      have h1 : ∫ x, ‖f x * g x‖ ∂μ
          = (∫⁻ x, ENNReal.ofReal ‖f x * g x‖ ∂μ).toReal :=
        integral_eq_lintegral_of_nonneg_ae
          (Filter.Eventually.of_forall (fun x => norm_nonneg _))
          h_aesm_mul.norm
      rw [h1]
      congr 1
      apply lintegral_congr_ae
      filter_upwards with x
      rw [ofReal_norm_eq_enorm]
    -- Hölder for eLpNorm using HolderTriple p q 1.
    have h_holder :
        eLpNorm (fun x => f x * g x) 1 μ ≤ eLpNorm (⇑f) p μ * eLpNorm g q μ := by
      have :=
        MeasureTheory.eLpNorm_smul_le_mul_eLpNorm
          (μ := μ) (𝕜 := ℝ) (p := p) (q := q) (r := 1)
          (f := g) (φ := (⇑f : (Fin d → ℝ) → ℝ))
          hf_aesm hg_aesm
      simpa only [Pi.smul_apply', smul_eq_mul] using! this
    have hf_top : eLpNorm (⇑f) p μ ≠ ∞ := hf_memLp.eLpNorm_ne_top
    have hg_top : eLpNorm g q μ ≠ ∞ := hg_memLp_q.eLpNorm_ne_top
    have h_mul_top : eLpNorm (⇑f) p μ * eLpNorm g q μ ≠ ∞ :=
      ENNReal.mul_ne_top hf_top hg_top
    have h_holder_real :
        (eLpNorm (fun x => f x * g x) 1 μ).toReal ≤
          (eLpNorm (⇑f) p μ).toReal * (eLpNorm g q μ).toReal := by
      have := ENNReal.toReal_mono h_mul_top h_holder
      simpa [ENNReal.toReal_mul] using this
    calc ‖∫ x, f x * g x ∂μ‖
        ≤ ∫ x, ‖f x * g x‖ ∂μ := h1
      _ = (eLpNorm (fun x => f x * g x) 1 μ).toReal := h_toReal
      _ ≤ (eLpNorm (⇑f) p μ).toReal * (eLpNorm g q μ).toReal := h_holder_real
  -- The integral functional `f ↦ ∫ f * g` as a continuous linear map.
  haveI hpq1 : ENNReal.HolderTriple p q 1 := inferInstance
  -- Integrability lemma: for every `f' ∈ Lp`, `f' * g` is integrable.
  have hi : ∀ f' : LpPer p d, Integrable (fun x => f' x * g x) μ := by
    intro f'
    have hf'_memLp : MemLp (⇑f') p μ := Lp.memLp f'
    have hL1 : MemLp (fun x => f' x * g x) 1 μ :=
      MemLp.fun_mul (μ := μ) (p := p) (q := q) (r := 1) hf'_memLp hg_memLp_q
    exact memLp_one_iff_integrable.mp hL1
  -- Linear map skeleton.
  let ψgL : LpPer p d →ₗ[ℝ] ℝ :=
    { toFun := fun f' => ∫ x, f' x * g x ∂μ
      map_add' := by
        intro f₁ f₂
        have hadd := Lp.coeFn_add f₁ f₂
        have h_ae : (fun x => (f₁ + f₂) x * g x)
            =ᵐ[μ] fun x => f₁ x * g x + f₂ x * g x := by
          filter_upwards [hadd] with x hx
          rw [hx]
          simp [Pi.add_apply, add_mul]
        rw [integral_congr_ae h_ae, integral_add (hi f₁) (hi f₂)]
      map_smul' := by
        intro c f'
        have hcf := Lp.coeFn_smul c f'
        have h_ae : (fun x => (c • f') x * g x)
            =ᵐ[μ] fun x => c * (f' x * g x) := by
          filter_upwards [hcf] with x hx
          rw [hx]; simp [Pi.smul_apply, smul_eq_mul, mul_assoc]
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [integral_congr_ae h_ae, integral_const_mul] }
  -- Continuous version via the Hölder bound.
  let ψg : LpPer p d →L[ℝ] ℝ :=
    ψgL.mkContinuous ((eLpNorm g q μ).toReal) (fun f => by
      change ‖∫ x, f x * g x ∂μ‖ ≤ (eLpNorm g q μ).toReal * ‖f‖
      have h := h_holder_bound f
      rw [Lp.norm_def, mul_comm]
      exact h)
  have hψg_apply : ∀ f : LpPer p d, ψg f = ∫ x, f x * g x ∂μ := by
    intro f; rfl
  -- The "agreement" set is the kernel of `φ - ψg`. Show it's all of LpPer p d.
  have h_diff_zero : φ - ψg = 0 := by
    apply ContinuousLinearMap.ext
    intro f'
    change φ f' - ψg f' = 0
    revert f'
    apply Lp.induction (E := ℝ) (p := p) (μ := μ) hp_ne_top
      (motive := fun f' => φ f' - ψg f' = 0)
    · -- Indicator step. The simple-function indicator is bounded by ‖c‖.
      intro c s hs hμs
      set f_ind : LpPer p d :=
        (Lp.simpleFunc.indicatorConst p hs hμs.ne c : LpPer p d)
        with hf_ind_def
      -- a.e. function is `s.indicator (fun _ => c)`, bounded by ‖c‖.
      have h_ae_f : ⇑f_ind =ᵐ[μ] s.indicator (fun _ => c) := by
        show ⇑((Lp.simpleFunc.indicatorConst p hs hμs.ne c :
            Lp.simpleFunc ℝ p μ) : LpPer p d) =ᵐ[μ] s.indicator (fun _ => c)
        rw [Lp.simpleFunc.coe_indicatorConst]
        exact indicatorConstLp_coeFn
      have h_bound : ∀ᵐ x ∂μ, ‖f_ind x‖ ≤ ‖c‖ := by
        filter_upwards [h_ae_f] with x hx
        rw [hx]
        by_cases hxs : x ∈ s
        · rw [Set.indicator_of_mem hxs]
        · rw [Set.indicator_of_notMem hxs]; simp
      have hφf := h_bdd_id f_ind ‖c‖ h_bound
      rw [hψg_apply f_ind, hφf, sub_self]
    · -- Additivity step.
      intro f₁ f₂ hf₁ hf₂ _ hf₁_eq hf₂_eq
      rw [map_add, map_add]
      linarith [hf₁_eq, hf₂_eq]
    · -- Closedness.
      have h_cont : Continuous fun f' : LpPer p d => φ f' - ψg f' :=
        Continuous.sub φ.continuous ψg.continuous
      exact isClosed_eq h_cont continuous_const
  -- Step 4 (concluded): integral identity holds for every `f ∈ LpPer p d`.
  have h_full_id : ∀ f : LpPer p d, φ f = ∫ x, f x * g x ∂μ := by
    intro f
    have hcong := congrArg (fun T : LpPer p d →L[ℝ] ℝ => T f) h_diff_zero
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.zero_apply] at hcong
    have h_eq : φ f - ψg f = 0 := hcong
    have h_ψg : ψg f = ∫ x, f x * g x ∂μ := hψg_apply f
    linarith [h_ψg, h_eq]
  -- Step 5. Lower bound: ‖φ‖ ≤ ‖g‖_q via Hölder.
  have h_phi_nn : 0 ≤ ‖φ‖ := norm_nonneg _
  have h_gnorm_nn : 0 ≤ (eLpNorm g q μ).toReal := ENNReal.toReal_nonneg
  have h_lower : ‖φ‖ ≤ (eLpNorm g q μ).toReal := by
    refine ContinuousLinearMap.opNorm_le_bound _ h_gnorm_nn ?_
    intro f
    rw [h_full_id f, Real.norm_eq_abs]
    have h := h_holder_bound f
    rw [Real.norm_eq_abs] at h
    rw [Lp.norm_def, mul_comm]
    exact h
  -- Step 6. Norm equality `eLpNorm g q μ = ENNReal.ofReal ‖φ‖`.
  have h_eLp_top : eLpNorm g q μ ≠ ∞ := hg_memLp_q.eLpNorm_ne_top
  have h_eLp_eq_ofReal : eLpNorm g q μ = ENNReal.ofReal (eLpNorm g q μ).toReal :=
    (ENNReal.ofReal_toReal h_eLp_top).symm
  have h_norm_eq : eLpNorm g q μ = ENNReal.ofReal ‖φ‖ := by
    -- Both real values are equal: combine `≤` from Step 3 with `≥` from Step 5.
    have h_le_real : (eLpNorm g q μ).toReal ≤ ‖φ‖ := by
      have := ENNReal.toReal_mono (by simp) hg_norm_le
      simpa [ENNReal.toReal_ofReal h_phi_nn] using this
    have h_real_eq : (eLpNorm g q μ).toReal = ‖φ‖ :=
      le_antisymm h_le_real h_lower
    rw [h_eLp_eq_ofReal, h_real_eq]
  exact ⟨g, hg_memLp_q, h_full_id, h_norm_eq⟩

end Periodic
end StationaryMFG
