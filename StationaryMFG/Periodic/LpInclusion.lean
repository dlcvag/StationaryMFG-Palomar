module

public import StationaryMFG.Periodic.Lp

@[expose] public section

/-!
# Finite-measure `Lᵖ` inclusion on the torus

For exponents `q' ≤ q`, the half-open unit cube has volume `1`, so the
prefactor in Mathlib's
`MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ` collapses to `1` and
we recover the clean Hölder inclusion `‖f‖_{L^{q'}_per} ≤ ‖f‖_{L^{q}_per}`.

This is the embedding the paper invokes near
`Source/FGU-monotone_revised.tex` line 1256, with `q = γ̄`, `q' = β̄'`.

Adapted from `LpSpaces.LpOnSet.eLpNormOn_mono_exponent` (whole-space version).
-/

namespace StationaryMFG
namespace Periodic

open MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-- Finite-measure Hölder inclusion at the extended-seminorm level: on the
unit cube (volume `1`), `eLpNormPer q' f ≤ eLpNormPer q f` whenever
`q' ≤ q`. -/
theorem eLpNormPer_mono_exponent {q' q : ℝ≥0∞}
    (f : (Fin d → ℝ) → ℝ)
    (hf : AEStronglyMeasurable f (Measure.restrict volume (UnitCube d)))
    (hq : q' ≤ q) :
    eLpNormPer q' f ≤ eLpNormPer q f := by
  have hbase :
      eLpNormPer q' f ≤ eLpNormPer q f *
        (Measure.restrict volume (UnitCube d)) Set.univ ^
          (1 / q'.toReal - 1 / q.toReal) :=
    eLpNorm_le_eLpNorm_mul_rpow_measure_univ hq hf
  have hμ : (Measure.restrict volume (UnitCube d)) Set.univ = 1 := by
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, volume_unitCube]
  simpa [hμ] using hbase

/-- Real-valued analogue of `eLpNormPer_mono_exponent`: under `MemLpPer q f`,
`lpNormPer q' f ≤ lpNormPer q f` whenever `q' ≤ q`. -/
theorem lpNormPer_mono_exponent {q' q : ℝ≥0∞}
    (f : (Fin d → ℝ) → ℝ)
    (hf : MemLpPer q f) (hq : q' ≤ q) :
    lpNormPer q' f ≤ lpNormPer q f :=
  ENNReal.toReal_mono hf.eLpNormPer_ne_top
    (eLpNormPer_mono_exponent f hf.aestronglyMeasurable hq)

/-- Specialisation to the paper's invocation: with `q = gammaBar` and
`q' = betaBar'` two extended-real exponents satisfying `betaBar' ≤ gammaBar`,
we obtain the inclusion `L^{gammaBar}_per ↪ L^{betaBar'}_per`. The paper's
`betaBar' = gammaBar / alpha` with `alpha ≥ 1` is one such pair. -/
example (gammaBar betaBar' : ℝ≥0∞) (hpq : betaBar' ≤ gammaBar) :
    eLpNormPer betaBar' (fun _ : Fin d → ℝ => (0 : ℝ)) ≤
      eLpNormPer gammaBar (fun _ : Fin d → ℝ => (0 : ℝ)) :=
  eLpNormPer_mono_exponent _ aestronglyMeasurable_const hpq

/-! ### Predicate-level `MemLpPer` inclusion -/

set_option linter.unusedVariables false in
/-- Predicate-level Hölder inclusion on the finite-measure unit cube: if
`f ∈ L^p_per` and `q ≤ p` (with `p ≠ ⊤`), then `f ∈ L^q_per`. This is the
predicate analogue of `lpNormPer_mono_exponent`. -/
theorem MemLpPer.mono_exponent_finite {p q : ℝ≥0∞} (hpq : q ≤ p) (hp : p ≠ ⊤)
    {f : (Fin d → ℝ) → ℝ}
    (hf : MemLpPer p f) :
    MemLpPer q f := by
  -- The unit cube has volume 1, hence the restricted measure is finite.
  haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    ⟨by
      rw [Measure.restrict_apply MeasurableSet.univ]
      simp⟩
  -- Route through Mathlib's `MemLp.mono_exponent` via the
  -- `MemLpPer = MemLp …` defeq. The argument `hp : p ≠ ⊤` is not actually
  -- consumed here — Mathlib's `mono_exponent` only needs `q ≤ p` and a
  -- finite measure — but we keep it in the API for the natural use case
  -- where `p` is finite.
  exact MemLp.toMemLpPer (hf.toMemLp.mono_exponent hpq)

set_option linter.unusedVariables false in
/-- `L^∞_per ⊆ L^q_per` on the finite-measure unit cube, for every finite
exponent `q`.  This is the special case `p = ⊤` of the Hölder inclusion.
The `q ≠ ⊤` argument is kept in the API for the natural use case (it is
not consumed: `q ≤ ⊤` holds unconditionally). -/
theorem MemLpPer.of_top_finite {q : ℝ≥0∞} (hq : q ≠ ⊤)
    {f : (Fin d → ℝ) → ℝ}
    (hf : MemLpPer (d := d) ⊤ f) :
    MemLpPer (d := d) q f := by
  haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    ⟨by
      rw [Measure.restrict_apply MeasurableSet.univ]
      simp⟩
  exact MemLp.toMemLpPer (hf.toMemLp.mono_exponent le_top)

/-- Vector-valued `L^∞` bound: from coordinatewise `L^∞_per` membership of
a test gradient family `Dυ`, the Euclidean norm of the vector
`x ↦ (fun j => Dυ j x)` is a.e. bounded by a single nonnegative constant
on the cube (concretely `∑ⱼ Cⱼ`, where `Cⱼ` bounds `|Dυ j|`). -/
theorem exists_ae_vector_norm_bound
    {Dυ : Fin d → (Fin d → ℝ) → ℝ}
    (hDυ : ∀ i, MemLpPer (d := d) ⊤ (Dυ i)) :
    ∃ R : ℝ, 0 ≤ R ∧
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ‖fun j => Dυ j x‖ ≤ R := by
  classical
  -- Per-coordinate a.e. bounds.
  choose C hC_nn hC using fun i => (hDυ i).exists_ae_norm_le
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => hC_nn i), ?_⟩
  -- a.e. all coordinate bounds hold simultaneously.
  have hall : ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
      ∀ i, ‖Dυ i x‖ ≤ C i :=
    (ae_all_iff).mpr hC
  filter_upwards [hall] with x hx
  -- `‖v‖ = sup ‖vⱼ‖ ≤ ∑ ‖vⱼ‖ ≤ ∑ Cⱼ` (sup-norm `≤` ℓ¹-norm).
  rw [pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun i _ => hC_nn i))]
  intro j
  calc ‖Dυ j x‖ ≤ C j := hx j
    _ ≤ ∑ i, C i := Finset.single_le_sum (fun i _ => hC_nn i) (Finset.mem_univ j)

/-- Unit test: a constant function lies in every `L^q_per`, hence it
satisfies the Hölder inclusion for any pair `q ≤ p < ⊤`. -/
example (c : ℝ) (p q : ℝ≥0∞) (hpq : q ≤ p) (hp : p ≠ ⊤) :
    MemLpPer (d := d) q (fun _ => c) := by
  haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    ⟨by
      rw [Measure.restrict_apply MeasurableSet.univ]
      simp⟩
  have hf : MemLpPer (d := d) p (fun _ => c) := MemLp.toMemLpPer (memLp_const c)
  exact MemLpPer.mono_exponent_finite hpq hp hf

end Periodic
end StationaryMFG
