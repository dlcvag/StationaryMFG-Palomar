module

public import StationaryMFG.Periodic.LpReflexive
public import StationaryMFG.Periodic.Sobolev
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

@[expose] public section

/-!
# Separability of strong duals of `L^p_per` and the paper's product space

This module discharges separability of the strong dual
`StrongDual ℝ (LpPer p d)` for `1 < p < ∞`, of `SobolevPerLp 1 p d` and
its strong dual, and of the paper's compactness target
`LpPer βBar d × SobolevPerLp 1 γBar d` and its strong dual.

The strategy:

* `LpPer p d = Lp ℝ p (volume.restrict (UnitCube d))`. Mathlib's
  `Lp.SecondCountableTopology` instance shows this is second countable
  whenever the measure is `IsSeparable` and the codomain `SeparableSpace`.
  Both hypotheses hold automatically for our finite cube measure on
  `Fin d → ℝ`. Hence `SeparableSpace (LpPer p d)`.
* The strong dual `(LpPer p d)*` is a continuous-linear-image of
  `LpPer q d` (the conjugate exponent), via the surjective Riesz map
  `LpPer.toDual p q d`. Hence its dual is separable.
* Products and finite Pi-types of separable spaces are separable.
* Same for strong duals: `(X × Y)* ≃ X* × Y*`, `(Π i, X i)* ≃ Π i, (X i)*`.
  Rather than identify them, we directly use surjective continuous linear
  maps from `LpPer q × (LpPer q × (Fin d → LpPer q))` onto the strong
  duals.

-- Adapted from `LpSpaces.WeakConvergence.LpOn.separableSpace_LqOn`,
-- specialised to the unit-cube measure.
-/

noncomputable section

namespace StationaryMFG
namespace Periodic

open MeasureTheory NormedSpace
open scoped ENNReal NNReal Topology

variable {d : ℕ}

/-! ## Auxiliary measure-theoretic instances -/

/-- The cube-restricted volume on `Fin d → ℝ` is separable
(`MeasureTheory.IsSeparable`), automatically because the underlying
measurable space is countably generated and the measure is `SFinite`
(it is finite). -/
instance instIsSeparableRestrictUnitCube :
    MeasureTheory.IsSeparable
      (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) :=
  inferInstance

/-! ## Separability of `LpPer p d`

When `p ≠ ∞`, Mathlib's `Lp.SecondCountableTopology` together with
`SeparableSpace ℝ` and the separability of the cube-restricted volume
yield second countability — hence separability — of `LpPer p d`.
-/

/-- `LpPer p d` is second countable for `p ≠ ∞`. -/
instance lpPer_secondCountable (p : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (p ≠ ∞)] :
    SecondCountableTopology (LpPer p d) :=
  Lp.SecondCountableTopology

/-- `LpPer p d` is a separable space for `p ≠ ∞`. -/
instance lpPer_separable (p : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (p ≠ ∞)] :
    TopologicalSpace.SeparableSpace (LpPer p d) :=
  inferInstance

/-! ## Separability of `SobolevPerLp 1 p d`

`SobolevPerLp 1 p d = LpPer p d × (Fin d → LpPer p d)` (a finite product),
so separability follows from `lpPer_separable` and the standard product
/ Pi closure of separability.
-/

/-- A finite Pi-type of separable spaces is separable.
(Provided here in the form `(Fin d → X)` since that is what we need.) -/
instance pi_fin_separable {α : Type*} [TopologicalSpace α]
    [TopologicalSpace.SeparableSpace α] :
    TopologicalSpace.SeparableSpace (Fin d → α) :=
  inferInstance

/-- `SobolevPerLp 1 p d` is separable for `p ≠ ∞`. -/
instance sobolevPerLp_separable (p : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (p ≠ ∞)] :
    TopologicalSpace.SeparableSpace (SobolevPerLp 1 p d) := by
  unfold SobolevPerLp
  infer_instance

/-! ## Separability of the strong dual via Riesz surjection

The map `LpPer.toDual p q d : LpPer q d →L[ℝ] (LpPer p d →L[ℝ] ℝ)`
is surjective by the Riesz representation theorem
(`exists_representer_norm_eq`). Combined with separability of the
domain, this gives separability of the strong dual.
-/

/-- The map `LpPer.toDual p q d` is surjective for `1 < p < ∞`.

Adapted from `LpSpaces.LpReflexive`'s use of `exists_representer_norm_eq`. -/
theorem lpPer_toDual_surjective {p q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (hp_gt_one : 1 < p) (hp_ne_top : p ≠ ∞) :
    Function.Surjective (LpPer.toDual (d := d) p q) := by
  intro φ
  -- `exists_representer_norm_eq` produces a `MemLp` representer; lift to `LpPer q d`.
  obtain ⟨g₀, hg₀_memLp, hφ_eq, _⟩ :=
    exists_representer_norm_eq (p := p) (q := q) hp_gt_one hp_ne_top φ
  set g : LpPer q d := MemLp.toLp g₀ hg₀_memLp with hg_def
  refine ⟨g, ?_⟩
  -- `LpPer.toDual p q d g = φ`.
  apply ContinuousLinearMap.ext
  intro f
  rw [LpPer.toDual_apply_apply, hφ_eq f]
  -- Both sides are integrals of `f x * g x`-like expressions.
  -- `g =ᵐ g₀` ⇒ rewrite the LHS integral.
  have hg_ae : (⇑g : (Fin d → ℝ) → ℝ)
      =ᵐ[Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)] g₀ :=
    MemLp.coeFn_toLp hg₀_memLp
  apply integral_congr_ae
  filter_upwards [hg_ae] with x hx
  rw [hx, mul_comm]

/-- **Strong dual of `LpPer p d` is separable for `1 < p < ∞`.**

By the Riesz representation theorem, the map `LpPer.toDual p q d` is
a continuous linear surjection from `LpPer q d` onto
`StrongDual ℝ (LpPer p d)`. Separability of `LpPer q d` (which holds
because `q ≠ ∞`, the conjugate of `p` being finite when `p > 1`)
transports through `Continuous.surjective.denseRange.separableSpace`. -/
theorem lpPer_strongDual_separable (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (hp_gt_one : 1 < p) (hp_ne_top : p ≠ ∞) :
    TopologicalSpace.SeparableSpace (StrongDual ℝ (LpPer p d)) := by
  -- Conjugate exponents: `q ≠ ∞` is equivalent to `1 < p`, which we have.
  haveI hqp : ENNReal.HolderConjugate q p :=
    (inferInstance : ENNReal.HolderConjugate p q).symm
  have hq_lt_top : q < ∞ := by
    rw [ENNReal.HolderConjugate.lt_top_iff_one_lt q p]
    exact hp_gt_one
  have hq_ne_top : q ≠ ∞ := hq_lt_top.ne
  haveI : Fact (q ≠ ∞) := ⟨hq_ne_top⟩
  -- Separability of `LpPer q d` (auto-instance).
  haveI : TopologicalSpace.SeparableSpace (LpPer q d) := inferInstance
  -- Surjectivity of `LpPer.toDual p q d`.
  have hsurj : Function.Surjective (LpPer.toDual (d := d) p q) :=
    lpPer_toDual_surjective hp_gt_one hp_ne_top
  -- Continuity of `LpPer.toDual p q d` (it is a CLM).
  have hcont : Continuous (LpPer.toDual (d := d) p q) :=
    (LpPer.toDual (d := d) p q).continuous
  exact hsurj.denseRange.separableSpace hcont

/-! ## Separability of the strong dual of `SobolevPerLp 1 p d`

`SobolevPerLp 1 p d = LpPer p d × (Fin d → LpPer p d)`.
Mathlib's CLM library does not give us a direct CLE
`(X × Y)* ≃ X* × Y*`, but we do have the *coordinate inclusions*
`inl, inr` (and their `single`-style analogues for Pi-types) that, when
postcomposed with a functional on the larger space, yield the
component-wise dual elements. Reversing this construction (linear
combinations along the canonical decomposition of `f`) gives a
continuous linear surjection
```
StrongDual ℝ X × StrongDual ℝ Y → StrongDual ℝ (X × Y),
(f, g) ↦ f ∘ fst + g ∘ snd
```
and similarly for finite Pi-types. We use these to transport
separability from the product of strong duals onto the strong dual of
the product.
-/

/-- Continuous linear surjection
`X* × Y* → (X × Y)*, (f, g) ↦ f ∘ fst + g ∘ snd`. -/
def prodStrongDualSurj (X Y : Type*)
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] :
    StrongDual ℝ X × StrongDual ℝ Y →L[ℝ] StrongDual ℝ (X × Y) :=
  ((ContinuousLinearMap.fst ℝ X Y).precomp ℝ).coprod
    ((ContinuousLinearMap.snd ℝ X Y).precomp ℝ)

/-- The above map is surjective: any `f : (X × Y) →L[ℝ] ℝ` decomposes
as `f = (f ∘ inl) ∘ fst + (f ∘ inr) ∘ snd`. -/
theorem prodStrongDualSurj_surjective (X Y : Type*)
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] :
    Function.Surjective (prodStrongDualSurj X Y) := by
  intro f
  refine ⟨(f.comp (ContinuousLinearMap.inl ℝ X Y),
           f.comp (ContinuousLinearMap.inr ℝ X Y)), ?_⟩
  -- `prodStrongDualSurj` applied to `(f∘inl, f∘inr)` is
  -- `(f∘inl)∘fst + (f∘inr)∘snd`. Show this equals `f`.
  apply ContinuousLinearMap.ext
  intro v
  -- Use Mathlib's `comp_inl_add_comp_inr`.
  have := ContinuousLinearMap.comp_inl_add_comp_inr f v
  -- Need to relate `prodStrongDualSurj` evaluated to the LHS form.
  -- `(g.coprod h) (a, b) = g a + h b`.
  change (f.comp (ContinuousLinearMap.inl ℝ X Y)).comp
            (ContinuousLinearMap.fst ℝ X Y) v +
          (f.comp (ContinuousLinearMap.inr ℝ X Y)).comp
            (ContinuousLinearMap.snd ℝ X Y) v
      = f v
  -- The first summand is `f (inl v.1) = f (v.1, 0)`; second is `f (0, v.2) = f (inr v.2)`.
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  -- Now LHS is `f (v.1, 0) + f (0, v.2) = f (v.1, v.2) = f v`.
  exact this

/-- Strong-dual separability is closed under finite products. -/
theorem strongDual_prod_separable (X Y : Type*)
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [TopologicalSpace.SeparableSpace (StrongDual ℝ X)]
    [TopologicalSpace.SeparableSpace (StrongDual ℝ Y)] :
    TopologicalSpace.SeparableSpace (StrongDual ℝ (X × Y)) := by
  -- `StrongDual ℝ X × StrongDual ℝ Y` is separable (product of separable
  -- spaces); `prodStrongDualSurj` is a continuous surjection onto
  -- `StrongDual ℝ (X × Y)`.
  haveI : TopologicalSpace.SeparableSpace
            (StrongDual ℝ X × StrongDual ℝ Y) := inferInstance
  exact (prodStrongDualSurj_surjective X Y).denseRange.separableSpace
    (prodStrongDualSurj X Y).continuous

/-- Continuous linear surjection
`(Π i, (φ i)*) → (Π i, φ i)*, g ↦ ∑ i, (g i) ∘ proj i`. -/
def piStrongDualSurj
    {ι : Type*} [Fintype ι] (φ : ι → Type*)
    [∀ i, NormedAddCommGroup (φ i)] [∀ i, NormedSpace ℝ (φ i)] :
    (∀ i, StrongDual ℝ (φ i)) →L[ℝ] StrongDual ℝ (∀ i, φ i) := by
  classical
  exact ∑ i,
    ((ContinuousLinearMap.proj (R := ℝ) (φ := φ) i).precomp ℝ).comp
      (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun i => StrongDual ℝ (φ i)) i)

/-- The Pi-strong-dual map is surjective: any
`f : (Π i, φ i) →L[ℝ] ℝ` decomposes as
`f = ∑ i, (f ∘ single i) ∘ proj i`. -/
theorem piStrongDualSurj_surjective
    {ι : Type*} [Fintype ι] (φ : ι → Type*)
    [∀ i, NormedAddCommGroup (φ i)] [∀ i, NormedSpace ℝ (φ i)] :
    Function.Surjective (piStrongDualSurj φ) := by
  classical
  intro f
  refine ⟨fun i => f.comp (ContinuousLinearMap.single ℝ φ i), ?_⟩
  apply ContinuousLinearMap.ext
  intro v
  -- `piStrongDualSurj` is a sum of CLM compositions; evaluating at `v`
  -- gives `∑ i, (f ∘ single i) (proj i v) = ∑ i, (f ∘ single i) (v i)`.
  -- Mathlib's `sum_comp_single` says
  -- `∑ i, f.comp (single ℝ φ i) (v i) = f v`.
  have := ContinuousLinearMap.sum_comp_single (R := ℝ) (φ := φ) f v
  -- Reduce LHS to ∑ i, (f ∘ single i) (v i).
  simp only [piStrongDualSurj, ContinuousLinearMap.coe_sum',
    ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.proj_apply, Finset.sum_apply]
  simpa [Finset.sum_apply] using this

/-- Strong-dual separability is closed under finite Pi-types. -/
theorem strongDual_pi_separable
    {ι : Type*} [Fintype ι] (φ : ι → Type*)
    [∀ i, NormedAddCommGroup (φ i)] [∀ i, NormedSpace ℝ (φ i)]
    [∀ i, TopologicalSpace.SeparableSpace (StrongDual ℝ (φ i))] :
    TopologicalSpace.SeparableSpace (StrongDual ℝ (∀ i, φ i)) := by
  classical
  haveI : TopologicalSpace.SeparableSpace
            (∀ i, StrongDual ℝ (φ i)) := inferInstance
  exact (piStrongDualSurj_surjective φ).denseRange.separableSpace
    (piStrongDualSurj φ).continuous

/-! ## Concrete instances at the paper's product space -/

/-- **Strong dual of `SobolevPerLp 1 p d` is separable for `1 < p < ∞`.**

`SobolevPerLp 1 p d = LpPer p d × (Fin d → LpPer p d)`; the strong dual
is separable by `strongDual_prod_separable` and `strongDual_pi_separable`,
each component using `lpPer_strongDual_separable`. -/
theorem sobolevPerLp_strongDual_separable (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (hp_gt_one : 1 < p) (hp_ne_top : p ≠ ∞) :
    TopologicalSpace.SeparableSpace (StrongDual ℝ (SobolevPerLp 1 p d)) := by
  haveI hLp : TopologicalSpace.SeparableSpace
                (StrongDual ℝ (LpPer p d)) :=
    lpPer_strongDual_separable p q hp_gt_one hp_ne_top
  haveI hPi : TopologicalSpace.SeparableSpace
                (StrongDual ℝ (Fin d → LpPer p d)) :=
    strongDual_pi_separable (fun _ : Fin d => LpPer p d)
  unfold SobolevPerLp
  exact strongDual_prod_separable (LpPer p d) (Fin d → LpPer p d)

/-- **Strong dual of the paper's product space is separable.**

This is the compactness target invoked in the F.5 weak-extraction
chain: `LpPer βBar d × SobolevPerLp 1 γBar d` for `1 < βBar, γBar < ∞`. -/
theorem lpSobolev_product_strongDual_separable
    (pβ qβ pγ qγ : ℝ≥0∞)
    [Fact (1 ≤ pβ)] [Fact (1 ≤ qβ)] [ENNReal.HolderConjugate pβ qβ]
    [Fact (1 ≤ pγ)] [Fact (1 ≤ qγ)] [ENNReal.HolderConjugate pγ qγ]
    (hβ_gt_one : 1 < pβ) (hβ_ne_top : pβ ≠ ∞)
    (hγ_gt_one : 1 < pγ) (hγ_ne_top : pγ ≠ ∞) :
    TopologicalSpace.SeparableSpace
      (StrongDual ℝ (LpPer pβ d × SobolevPerLp 1 pγ d)) := by
  haveI hLp : TopologicalSpace.SeparableSpace
                (StrongDual ℝ (LpPer pβ d)) :=
    lpPer_strongDual_separable pβ qβ hβ_gt_one hβ_ne_top
  haveI hSob : TopologicalSpace.SeparableSpace
                (StrongDual ℝ (SobolevPerLp 1 pγ d)) :=
    sobolevPerLp_strongDual_separable pγ qγ hγ_gt_one hγ_ne_top
  exact strongDual_prod_separable (LpPer pβ d) (SobolevPerLp 1 pγ d)

end Periodic
end StationaryMFG
