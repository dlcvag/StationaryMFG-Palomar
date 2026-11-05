module

public import StationaryMFG.Periodic.Lp
public import StationaryMFG.Periodic.Sobolev
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

/-!
# Reflexivity infrastructure for `L^p_per` and `W^{1,p}_per` (paper-only product)

This file introduces a project-local notion of reflexivity for real normed
spaces and discharges the **`p = 2` (Hilbert) instance** of weak compactness
on the paper's product space `L^β̄_per × W^{1,γ̄}_per`.

## Why this scope

Mathlib (as of 2026-04) does not expose a `Reflexive`-style typeclass for
Banach spaces, nor does it provide a Riesz duality theorem on finite-measure
sets that would yield `L^p` reflexivity for `1 < p < ∞`. The classical
non-Hilbert routes (Milman–Pettis, Clarkson) are also absent.

The fully general `1 < β̄, γ̄ < ∞` reflexivity is parked as a follow-up task
(`infra:P1-reflexive-general-p`), depending on a torus-adapted Riesz
representation theorem. Until then, this file lands the infrastructure that
the paper's compactness arguments need at the `p = 2` calibration:

* `IsReflexiveNormedSpace X` — surjectivity of the canonical embedding
  `X → X**` (Mathlib's `NormedSpace.inclusionInDoubleDual`).
* `Hilbert.isReflexive` — every real Hilbert space is reflexive, by two
  applications of Fréchet–Riesz (`InnerProductSpace.toDual`).
* `IsReflexiveNormedSpace.prod` and `IsReflexiveNormedSpace.pi` — closure of
  reflexivity under finite products, by direct dualisation of the canonical
  decompositions `comp_inl_add_comp_inr` / `sum_comp_single`.
* `lpPer_isReflexive_two` — periodic `L²` is reflexive.
* `sobolevPer_isReflexive_two` — periodic `W^{1,2}` is reflexive (uses the
  `prod` and `pi` lemmas above).
* `lpSobolev_product_isReflexive_two` — the paper's product space at
  `β̄ = γ̄ = 2`.

## Reference

Adapted from `LpSpaces.LpReflexive` (whole-space version), specialised to
the bare `Lp ℝ 2 μ` Hilbert structure on the unit cube and recombined with
hand-derived product/Pi closure lemmas.
-/

noncomputable section

namespace StationaryMFG
namespace Periodic

open MeasureTheory NormedSpace
open scoped ENNReal NNReal Topology

variable {d : ℕ}

/-! ## Project-local reflexivity predicate -/

/-- A real normed space `X` is **reflexive** when the canonical isometric
embedding `X → StrongDual ℝ (StrongDual ℝ X)` is surjective. -/
def IsReflexiveNormedSpace (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop :=
  Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ X)

namespace IsReflexiveNormedSpace

/-- If `X` is reflexive, package the canonical embedding as a linear
isometric equivalence `X ≃ₗᵢ[ℝ] StrongDual ℝ (StrongDual ℝ X)`. -/
def equiv {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (h : IsReflexiveNormedSpace X) :
    X ≃ₗᵢ[ℝ] StrongDual ℝ (StrongDual ℝ X) :=
  LinearIsometryEquiv.ofSurjective (NormedSpace.inclusionInDoubleDualLi ℝ) h

end IsReflexiveNormedSpace

/-! ## Hilbert spaces are reflexive

The proof is the classical two-step Fréchet–Riesz argument. Adapted from
`LpSpaces.LpReflexive.Hilbert.isReflexive`. -/

/-- **Every real Hilbert space is reflexive.** Two applications of the
Fréchet–Riesz representation theorem (`InnerProductSpace.toDual`). -/
theorem Hilbert.isReflexive
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] :
    IsReflexiveNormedSpace H := by
  intro Φ
  -- Riesz isomorphism `T : H ≃ StrongDual ℝ H`.
  let T : H ≃ₗᵢ⋆[ℝ] StrongDual ℝ H := InnerProductSpace.toDual ℝ H
  -- The composition `Φ ∘ T` as a continuous ℝ-linear functional on `H`.
  let Tcl : H →L[ℝ] StrongDual ℝ H := T.toContinuousLinearEquiv.toContinuousLinearMap
  let ℓ : H →L[ℝ] ℝ := Φ.comp Tcl
  refine ⟨T.symm ℓ, ?_⟩
  set y : H := T.symm ℓ with hy_def
  have hTy : T y = ℓ := by simp [y]
  apply ContinuousLinearMap.ext
  intro f
  change f y = Φ f
  set z : H := T.symm f with hz_def
  have hTz : T z = f := by simp [z]
  have hstep1 : Φ f = ℓ z := by
    rw [← hTz]; rfl
  have hstep2 : ℓ z = T y z := by
    have := congr_arg (fun g : StrongDual ℝ H => g z) hTy
    simpa using this.symm
  have hstep3 : T y z = @inner ℝ _ _ y z := InnerProductSpace.toDual_apply_apply
  have hstep4 : f y = T z y := by rw [← hTz]
  have hstep5 : T z y = @inner ℝ _ _ z y := InnerProductSpace.toDual_apply_apply
  have hstep6 : @inner ℝ _ _ z y = @inner ℝ _ _ y z := real_inner_comm _ _
  rw [hstep4, hstep5, hstep6, ← hstep3, ← hstep2, ← hstep1]

/-! ## Closure under finite products

These two lemmas are pure functional-analytic plumbing: we decompose any
`f ∈ (X × Y)*` as `(f ∘ inl) ∘ fst + (f ∘ inr) ∘ snd`, and similarly for
the Pi case. -/

/-- The product of two reflexive real normed spaces is reflexive. -/
theorem IsReflexiveNormedSpace.prod
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (hX : IsReflexiveNormedSpace X) (hY : IsReflexiveNormedSpace Y) :
    IsReflexiveNormedSpace (X × Y) := by
  intro Φ
  -- Build `Φ_X : X**` from `Φ` by precomposing with `f ↦ f ∘ fst`.
  let precompFst : StrongDual ℝ X →L[ℝ] StrongDual ℝ (X × Y) :=
    (ContinuousLinearMap.fst ℝ X Y).precomp ℝ
  let precompSnd : StrongDual ℝ Y →L[ℝ] StrongDual ℝ (X × Y) :=
    (ContinuousLinearMap.snd ℝ X Y).precomp ℝ
  let ΦX : StrongDual ℝ (StrongDual ℝ X) := Φ.comp precompFst
  let ΦY : StrongDual ℝ (StrongDual ℝ Y) := Φ.comp precompSnd
  obtain ⟨x, hx⟩ := hX ΦX
  obtain ⟨y, hy⟩ := hY ΦY
  refine ⟨(x, y), ?_⟩
  apply ContinuousLinearMap.ext
  intro f
  -- `inclusionInDoubleDual ℝ (X × Y) (x, y) f = f (x, y)` definitionally.
  change f (x, y) = Φ f
  -- Local abbreviations for the inl/inr-precomposed components.
  set fl : StrongDual ℝ X := f.comp (ContinuousLinearMap.inl ℝ X Y)
  set fr : StrongDual ℝ Y := f.comp (ContinuousLinearMap.inr ℝ X Y)
  -- Decompose `(x, y) = inl x + inr y`, hence `f (x, y) = fl x + fr y`.
  have hdecompPt : f (x, y) = fl x + fr y :=
    (ContinuousLinearMap.comp_inl_add_comp_inr f (x, y)).symm
  -- Now compute `Φ f` via the two reflexivity witnesses.
  have hxf : fl x = Φ (precompFst fl) := by
    have := congr_arg (fun g : StrongDual ℝ (StrongDual ℝ X) => g fl) hx
    simpa [ΦX, NormedSpace.inclusionInDoubleDual] using this
  have hyf : fr y = Φ (precompSnd fr) := by
    have := congr_arg (fun g : StrongDual ℝ (StrongDual ℝ Y) => g fr) hy
    simpa [ΦY, NormedSpace.inclusionInDoubleDual] using this
  -- `precompFst fl = fl ∘ fst` and `precompSnd fr = fr ∘ snd` by definition.
  have hfst : precompFst fl = fl.comp (ContinuousLinearMap.fst ℝ X Y) := rfl
  have hsnd : precompSnd fr = fr.comp (ContinuousLinearMap.snd ℝ X Y) := rfl
  -- The decomposition of `f` itself as `fl ∘ fst + fr ∘ snd`.
  have hdecompMap :
      f = fl.comp (ContinuousLinearMap.fst ℝ X Y) +
          fr.comp (ContinuousLinearMap.snd ℝ X Y) := by
    apply ContinuousLinearMap.ext
    intro v
    exact (ContinuousLinearMap.comp_inl_add_comp_inr f v).symm
  -- Chain via calc to avoid global pattern matching by `rw [Φ f = ...]`.
  calc f (x, y)
      = fl x + fr y := hdecompPt
    _ = Φ (precompFst fl) + Φ (precompSnd fr) := by rw [hxf, hyf]
    _ = Φ (fl.comp (ContinuousLinearMap.fst ℝ X Y)) +
          Φ (fr.comp (ContinuousLinearMap.snd ℝ X Y)) := by rw [hfst, hsnd]
    _ = Φ (fl.comp (ContinuousLinearMap.fst ℝ X Y) +
            fr.comp (ContinuousLinearMap.snd ℝ X Y)) := (map_add Φ _ _).symm
    _ = Φ f := by rw [← hdecompMap]

/-- A finite product of reflexive real normed spaces is reflexive. -/
theorem IsReflexiveNormedSpace.pi
    {ι : Type*} [Fintype ι]
    {φ : ι → Type*}
    [∀ i, NormedAddCommGroup (φ i)] [∀ i, NormedSpace ℝ (φ i)]
    (h : ∀ i, IsReflexiveNormedSpace (φ i)) :
    IsReflexiveNormedSpace (∀ i, φ i) := by
  classical
  intro Φ
  -- For each coordinate `i`, lift `Φ` to a double-dual element on `φ i`.
  let precompProj : ∀ i, StrongDual ℝ (φ i) →L[ℝ] StrongDual ℝ (∀ j, φ j) :=
    fun i => (ContinuousLinearMap.proj (R := ℝ) (φ := φ) i).precomp ℝ
  let Φi : ∀ i, StrongDual ℝ (StrongDual ℝ (φ i)) :=
    fun i => Φ.comp (precompProj i)
  -- Reflexivity at each coordinate produces a representer `x i`.
  choose x hx using fun i => h i (Φi i)
  refine ⟨x, ?_⟩
  apply ContinuousLinearMap.ext
  intro f
  -- Decompose `f` and `f x` along the `single` injections.
  change f x = Φ f
  have hdecompPt : f x = ∑ i, f.comp (ContinuousLinearMap.single ℝ φ i) (x i) := by
    simpa [Finset.sum_apply] using
      (ContinuousLinearMap.sum_comp_single (R := ℝ) (φ := φ) f x).symm
  have hcoord : ∀ i,
      f.comp (ContinuousLinearMap.single ℝ φ i) (x i) =
        Φ ((f.comp (ContinuousLinearMap.single ℝ φ i)).comp
            (ContinuousLinearMap.proj (R := ℝ) (φ := φ) i)) := by
    intro i
    have hxi := hx i
    have := congr_arg
      (fun g : StrongDual ℝ (StrongDual ℝ (φ i)) =>
        g (f.comp (ContinuousLinearMap.single ℝ φ i))) hxi
    -- LHS: `inclusionInDoubleDual ℝ (φ i) (x i) (...) = (f ∘ single i) (x i)`.
    -- RHS: `Φ (precompProj i (f ∘ single i)) = Φ ((f ∘ single i) ∘ proj i)`.
    simpa [Φi, precompProj, NormedSpace.inclusionInDoubleDual] using this
  -- Decomposition of `f` itself as `∑ i, (f ∘ single i) ∘ proj i`.
  have hdecompMap :
      f = ∑ i, (f.comp (ContinuousLinearMap.single ℝ φ i)).comp
              (ContinuousLinearMap.proj (R := ℝ) (φ := φ) i) := by
    apply ContinuousLinearMap.ext
    intro v
    have := (ContinuousLinearMap.sum_comp_single (R := ℝ) (φ := φ) f v).symm
    simpa [Finset.sum_apply] using this
  calc f x
      = ∑ i, f.comp (ContinuousLinearMap.single ℝ φ i) (x i) := hdecompPt
    _ = ∑ i, Φ ((f.comp (ContinuousLinearMap.single ℝ φ i)).comp
              (ContinuousLinearMap.proj (R := ℝ) (φ := φ) i)) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          exact hcoord i
    _ = Φ (∑ i, (f.comp (ContinuousLinearMap.single ℝ φ i)).comp
              (ContinuousLinearMap.proj (R := ℝ) (φ := φ) i)) := (map_sum Φ _ _).symm
    _ = Φ f := by rw [← hdecompMap]

/-! ## Concrete instances at `p = 2`

`Lp ℝ 2 μ` is a Hilbert space (Mathlib's `MeasureTheory.L2.innerProductSpace`),
so reflexivity follows from `Hilbert.isReflexive`. The Sobolev product
`SobolevPerLp 1 2 d = Lp ℝ 2 μ × (Fin d → Lp ℝ 2 μ)` is reflexive by the
product/Pi closure lemmas. -/

/-- **Periodic `L²` is reflexive.** -/
theorem lpPer_isReflexive_two :
    IsReflexiveNormedSpace
      (MeasureTheory.Lp ℝ 2
        (MeasureTheory.Measure.restrict (volume) (UnitCube d))) :=
  Hilbert.isReflexive _

/-- **Periodic `W^{1,2}` is reflexive** (paper's product space, derivative
factor). -/
theorem sobolevPer_isReflexive_two :
    IsReflexiveNormedSpace (SobolevPerLp 1 2 d) := by
  -- `SobolevPerLp 1 2 d = Lp × (Fin d → Lp)`; both factors are reflexive.
  refine IsReflexiveNormedSpace.prod (lpPer_isReflexive_two (d := d)) ?_
  exact IsReflexiveNormedSpace.pi (fun _ => lpPer_isReflexive_two (d := d))

/-- **The paper's compactness target at `β̄ = γ̄ = 2`.** Reflexivity of the
product `L^2_per × W^{1,2}_per`, the exact space from which the paper
extracts weakly convergent subsequences in `eq:compactness`,
`eq:compactness.delta`, and `paper:thm:main-congestion.growth`. -/
theorem lpSobolev_product_isReflexive_two :
    IsReflexiveNormedSpace
      ((MeasureTheory.Lp ℝ 2
        (MeasureTheory.Measure.restrict (volume) (UnitCube d))) ×
        SobolevPerLp 1 2 d) :=
  IsReflexiveNormedSpace.prod
    (lpPer_isReflexive_two (d := d)) (sobolevPer_isReflexive_two (d := d))

/-- Sample exercise: the canonical embedding into the double dual is a
linear isometric equivalence on the paper's compactness target. -/
example :
    ((MeasureTheory.Lp ℝ 2
        (MeasureTheory.Measure.restrict (volume) (UnitCube d))) ×
        SobolevPerLp 1 2 d) ≃ₗᵢ[ℝ]
      StrongDual ℝ (StrongDual ℝ
        ((MeasureTheory.Lp ℝ 2
          (MeasureTheory.Measure.restrict (volume) (UnitCube d))) ×
          SobolevPerLp 1 2 d)) :=
  (lpSobolev_product_isReflexive_two (d := d)).equiv

end Periodic
end StationaryMFG
