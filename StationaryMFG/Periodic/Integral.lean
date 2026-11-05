module

public import StationaryMFG.Periodic.UnitCube
public import Mathlib.Algebra.Module.ZLattice.Basic

@[expose] public section

/-!
# The periodic integral and translation invariance

Per `docs/CONVENTIONS.md` §1, integration on the torus `𝕋^d` is realised as
integration over the half-open unit cube `UnitCube d ⊆ Fin d → ℝ`. This file
defines

`periodicIntegral f := ∫ x in UnitCube d, f x`   (Bochner integral)

and proves the basic linearity lemmas (`periodicIntegral_add`,
`periodicIntegral_smul`, `periodicIntegral_const`) together with the main
structural fact used throughout Phase 1: **translation invariance**

`periodicIntegral (fun x => f (x + y)) = periodicIntegral f`

for any `y : Fin d → ℝ` and any periodic `f`.

The proof of translation invariance uses
`MeasureTheory.IsAddFundamentalDomain.setIntegral_eq` between the two additive
fundamental domains `UnitCube d` and `(fun x => x + y) '' UnitCube d`, both of
which are fundamental domains for the integer lattice
`(Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin d)))).toAddSubgroup` acting on
`Fin d → ℝ`. The identification
`UnitCube d = ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin d))` comes from
`Mathlib.Algebra.Module.ZLattice.Basic`.
-/

namespace StationaryMFG
namespace Periodic

open Set MeasureTheory
open scoped Pointwise ENNReal

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

/-- The integral of `f : (Fin d → ℝ) → E` over the unit cube, i.e. over the
torus `𝕋^d`. -/
noncomputable def periodicIntegral (f : (Fin d → ℝ) → E) : E :=
  ∫ x in UnitCube d, f x

omit [CompleteSpace E] in
@[simp]
lemma periodicIntegral_zero : periodicIntegral (0 : (Fin d → ℝ) → E) = 0 := by
  simp [periodicIntegral]

lemma periodicIntegral_const (c : E) :
    periodicIntegral (fun _ : Fin d → ℝ => c) = c := by
  unfold periodicIntegral
  rw [setIntegral_const, measureReal_def, volume_unitCube]
  simp

omit [CompleteSpace E] in
lemma periodicIntegral_add {f g : (Fin d → ℝ) → E}
    (hf : IntegrableOn f (UnitCube d)) (hg : IntegrableOn g (UnitCube d)) :
    periodicIntegral (f + g) = periodicIntegral f + periodicIntegral g := by
  simp only [periodicIntegral, Pi.add_apply]
  exact integral_add hf hg

omit [CompleteSpace E] in
lemma periodicIntegral_smul {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]
    [SMulCommClass ℝ 𝕜 E] (c : 𝕜) (f : (Fin d → ℝ) → E) :
    periodicIntegral (fun x => c • f x) = c • periodicIntegral f := by
  simp only [periodicIntegral]
  exact integral_smul c f

/-! ### Translation invariance -/

section Translate

open Submodule (span)

/-- The integer lattice inside `Fin d → ℝ`, as an `AddSubgroup` (which is what
the fundamental-domain machinery expects for group actions). -/
abbrev ZLatGroup (d : ℕ) : AddSubgroup (Fin d → ℝ) :=
  (span ℤ (Set.range (Pi.basisFun ℝ (Fin d)))).toAddSubgroup

/-- The integer lattice is countable: the ambient `Fin d → ℝ` is second
countable, hence separable, and combined with the discreteness of the integer
lattice this gives countability. -/
instance : Countable (ZLatGroup d) := by
  -- `ZLatGroup d` shares its carrier with the `Submodule` `span ℤ ...`.
  -- `DiscreteTopology` of the latter is a global instance from `ZLattice.Basic`.
  have : DiscreteTopology (ZLatGroup d) := by
    -- The `AddSubgroup` carrier and `Submodule` carrier coincide as subtypes.
    exact inferInstanceAs
      (DiscreteTopology (span ℤ (Set.range (Pi.basisFun ℝ (Fin d)))).toAddSubgroup)
  exact (TopologicalSpace.separableSpace_iff_countable (α := ZLatGroup d)).mp
    inferInstance

/-- The fundamental domain of `Pi.basisFun ℝ (Fin d)` in the sense of `ZSpan`
coincides with our `UnitCube d`. -/
private lemma unitCube_eq_zspan_fundamentalDomain :
    (UnitCube d : Set (Fin d → ℝ)) =
      ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin d)) := by
  rw [show (UnitCube d : Set (Fin d → ℝ)) =
        Set.pi Set.univ fun _ : Fin d => Set.Ico (0 : ℝ) 1 from rfl,
      ← ZSpan.fundamentalDomain_pi_basisFun (ι := Fin d)]

/-- `UnitCube d` is an additive fundamental domain for the integer lattice
`ZLatGroup d` acting on `Fin d → ℝ`. -/
lemma unitCube_isAddFundamentalDomain :
    IsAddFundamentalDomain (ZLatGroup d) (UnitCube d) (volume : Measure (Fin d → ℝ)) := by
  rw [unitCube_eq_zspan_fundamentalDomain]
  exact ZSpan.isAddFundamentalDomain' (Pi.basisFun ℝ (Fin d)) volume

/-- The translate `(· + y) '' UnitCube d` is also an additive fundamental domain
for `ZLatGroup d`: existence/uniqueness of a lattice vector sending a point into
this translate follows from the unshifted case applied to `x - y`. -/
private lemma unitCubeTranslate_isAddFundamentalDomain (y : Fin d → ℝ) :
    IsAddFundamentalDomain (ZLatGroup d) ((fun x => x + y) '' UnitCube d)
      (volume : Measure (Fin d → ℝ)) := by
  -- Measurability of the image.
  have hmeas : MeasurableSet ((fun x : Fin d → ℝ => x + y) '' UnitCube d) := by
    have hembed : MeasurableEmbedding (fun x : Fin d → ℝ => x + y) :=
      (MeasurableEquiv.addRight y).measurableEmbedding
    exact hembed.measurableSet_image.mpr measurableSet_unitCube
  refine IsAddFundamentalDomain.mk' hmeas.nullMeasurableSet ?_
  intro x
  -- Unique lattice point `v` with `v +ᵥ (x - y) ∈ UnitCube d`.
  obtain ⟨v, hv, huniq⟩ : ∃! v : ZLatGroup d, v +ᵥ (x - y) ∈ UnitCube d := by
    rw [unitCube_eq_zspan_fundamentalDomain]
    -- `ZSpan.exist_unique_vadd_mem_fundamentalDomain` gives a unique lattice
    -- point as a `Submodule` element; `ZLatGroup d` is its `toAddSubgroup`,
    -- which shares the same underlying type.
    exact ZSpan.exist_unique_vadd_mem_fundamentalDomain
      (Pi.basisFun ℝ (Fin d)) (x - y)
  refine ⟨v, ?_, ?_⟩
  · -- Show `v +ᵥ x ∈ (· + y) '' UnitCube d`.
    refine ⟨v +ᵥ (x - y), hv, ?_⟩
    change (v : Fin d → ℝ) + (x - y) + y = (v : Fin d → ℝ) + x
    abel
  · rintro w ⟨u, hu, hwu⟩
    apply huniq
    -- `hwu : (fun x => x + y) u = w +ᵥ x`, i.e. `u + y = w + x`.
    have hwux : (u : Fin d → ℝ) + y = (w : Fin d → ℝ) + x := hwu
    have key : (w : Fin d → ℝ) + (x - y) = u := by linear_combination -hwux
    change w +ᵥ (x - y) ∈ UnitCube d
    rw [show (w +ᵥ (x - y) : Fin d → ℝ) = (w : Fin d → ℝ) + (x - y) from rfl, key]
    exact hu

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] in
/-- If `f` is periodic in our sense, then it is invariant under the action of
every element of the integer lattice `ZLatGroup d`. -/
lemma isPeriodic_toZLatGroup_invariant {f : (Fin d → ℝ) → E}
    (hf : IsPeriodic f) : ∀ (v : ZLatGroup d) (x : Fin d → ℝ), f (v +ᵥ x) = f x := by
  intro v x
  -- An element of `span ℤ (range (Pi.basisFun ℝ (Fin d)))` has integer
  -- coordinates in the standard basis.
  have hmem : (v : Fin d → ℝ) ∈
      (span ℤ (Set.range (Pi.basisFun ℝ (Fin d))) : Submodule ℤ (Fin d → ℝ)) :=
    v.2
  have hcoord : ∀ i, ∃ k : ℤ, (v : Fin d → ℝ) i = (k : ℝ) := by
    intro i
    have hrepr :=
      ((Pi.basisFun ℝ (Fin d)).mem_span_iff_repr_mem ℤ (v : Fin d → ℝ)).mp hmem i
    rcases hrepr with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have : (Pi.basisFun ℝ (Fin d)).repr (v : Fin d → ℝ) i = (v : Fin d → ℝ) i := by
      simp
    rw [← this, ← hk]
    simp [algebraMap_int_eq, eq_intCast]
  choose k hk using hcoord
  have hv_eq : (v : Fin d → ℝ) = fun i => (k i : ℝ) := funext hk
  change f ((v : Fin d → ℝ) + x) = f x
  rw [hv_eq, add_comm]
  exact hf k x

omit [CompleteSpace E] in
/-- Change of variables: the set integral over `UnitCube d` of the shifted
function `f ∘ (· + y)` equals the set integral of `f` over `UnitCube d + y`. -/
private lemma setIntegral_translate (f : (Fin d → ℝ) → E) (y : Fin d → ℝ) :
    ∫ x in UnitCube d, f (x + y) = ∫ u in (fun x => x + y) '' UnitCube d, f u := by
  have hmp : MeasurePreserving (fun x : Fin d → ℝ => x + y) volume volume :=
    measurePreserving_add_right volume y
  have hembed : MeasurableEmbedding (fun x : Fin d → ℝ => x + y) :=
    (MeasurableEquiv.addRight y).measurableEmbedding
  exact (hmp.setIntegral_image_emb hembed f (UnitCube d)).symm

omit [CompleteSpace E] in
/-- **Main translation-invariance result.** For any periodic integrable
`f : (Fin d → ℝ) → E` and any `y : Fin d → ℝ`, the integral of `f(· + y)` over
the unit cube equals the integral of `f` over the unit cube. -/
theorem periodicIntegral_translate {f : (Fin d → ℝ) → E}
    (hf : IsPeriodic f) (_hfint : IntegrableOn f (UnitCube d))
    (y : Fin d → ℝ) :
    periodicIntegral (fun x => f (x + y)) = periodicIntegral f := by
  -- Step 1: convert LHS to an integral over the translated cube.
  unfold periodicIntegral
  rw [setIntegral_translate f y]
  -- Step 2: use `IsAddFundamentalDomain.setIntegral_eq` between the two
  -- fundamental domains `(· + y) '' UnitCube d` and `UnitCube d`.
  exact IsAddFundamentalDomain.setIntegral_eq
    (unitCubeTranslate_isAddFundamentalDomain y)
    (unitCube_isAddFundamentalDomain)
    (isPeriodic_toZLatGroup_invariant hf)

/-! ### Translation invariance for `ℝ≥0∞`-valued lintegral -/

/-- Lattice invariance for `ℝ≥0∞`-valued periodic functions. Same content
as `isPeriodic_toZLatGroup_invariant` with `E = ℝ≥0∞`. -/
private lemma isPeriodic_toZLatGroup_invariant_ennreal
    {g : (Fin d → ℝ) → ℝ≥0∞} (hg : IsPeriodic g) :
    ∀ (v : ZLatGroup d) (x : Fin d → ℝ), g (v +ᵥ x) = g x := by
  intro v x
  have hmem : (v : Fin d → ℝ) ∈
      (span ℤ (Set.range (Pi.basisFun ℝ (Fin d))) : Submodule ℤ (Fin d → ℝ)) :=
    v.2
  have hcoord : ∀ i, ∃ k : ℤ, (v : Fin d → ℝ) i = (k : ℝ) := by
    intro i
    have hrepr :=
      ((Pi.basisFun ℝ (Fin d)).mem_span_iff_repr_mem ℤ (v : Fin d → ℝ)).mp hmem i
    rcases hrepr with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have : (Pi.basisFun ℝ (Fin d)).repr (v : Fin d → ℝ) i = (v : Fin d → ℝ) i := by
      simp
    rw [← this, ← hk]
    simp [algebraMap_int_eq, eq_intCast]
  choose k hk using hcoord
  have hv_eq : (v : Fin d → ℝ) = fun i => (k i : ℝ) := funext hk
  change g ((v : Fin d → ℝ) + x) = g x
  rw [hv_eq, add_comm]
  exact hg k x

/-- Change of variables for the `lintegral` of a `ℝ≥0∞`-valued function: the
set lintegral over `UnitCube d` of `g ∘ (· + y)` equals the set lintegral of `g`
over the translated cube. -/
private lemma setLIntegral_translate_ennreal (g : (Fin d → ℝ) → ℝ≥0∞)
    (y : Fin d → ℝ) :
    ∫⁻ x in UnitCube d, g (x + y) ∂(volume : Measure (Fin d → ℝ))
      = ∫⁻ u in (fun x => x + y) '' UnitCube d, g u
          ∂(volume : Measure (Fin d → ℝ)) := by
  have hmp : MeasurePreserving (fun x : Fin d → ℝ => x + y) volume volume :=
    measurePreserving_add_right volume y
  have hembed : MeasurableEmbedding (fun x : Fin d → ℝ => x + y) :=
    (MeasurableEquiv.addRight y).measurableEmbedding
  exact (hmp.setLIntegral_comp_emb hembed g (UnitCube d))

/-- **Translation invariance of the periodic `lintegral`.** For any
periodic `g : (Fin d → ℝ) → ℝ≥0∞` and any `y : Fin d → ℝ`, the lintegral of
`g(· + y)` over the unit cube equals the lintegral of `g` over the unit
cube. The `ℝ≥0∞`-valued analogue of `periodicIntegral_translate`. -/
theorem lintegral_unitCube_translate_eq_add
    {g : (Fin d → ℝ) → ℝ≥0∞} (hg : IsPeriodic g) (y : Fin d → ℝ) :
    ∫⁻ x in UnitCube d, g (x + y) ∂(volume : Measure (Fin d → ℝ))
      = ∫⁻ x in UnitCube d, g x ∂(volume : Measure (Fin d → ℝ)) := by
  rw [setLIntegral_translate_ennreal g y]
  exact IsAddFundamentalDomain.setLIntegral_eq
    (unitCubeTranslate_isAddFundamentalDomain y)
    (unitCube_isAddFundamentalDomain)
    g
    (isPeriodic_toZLatGroup_invariant_ennreal hg)

/-- Subtraction form: for periodic `g`, the lintegral of `g(· - y)` over
the unit cube equals the lintegral of `g`. Follows from
`lintegral_unitCube_translate_eq_add` applied with `-y`. -/
theorem lintegral_unitCube_translate_eq_sub
    {g : (Fin d → ℝ) → ℝ≥0∞} (hg : IsPeriodic g) (y : Fin d → ℝ) :
    ∫⁻ x in UnitCube d, g (x - y) ∂(volume : Measure (Fin d → ℝ))
      = ∫⁻ x in UnitCube d, g x ∂(volume : Measure (Fin d → ℝ)) := by
  have h := lintegral_unitCube_translate_eq_add (g := g) hg (-y)
  simpa [sub_eq_add_neg] using h

end Translate

end Periodic
end StationaryMFG
