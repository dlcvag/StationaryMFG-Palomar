module

public import StationaryMFG.Basic
public import StationaryMFG.Monotone.Operator
public import StationaryMFG.Monotone.FiniteVI

@[expose] public section

/-!
# Finite-dimensional convex-hull variational inequality — Sion discharge

This module discharges the typeclass
`StationaryMFG.Monotone.FiniteConvexHullWeakVI` introduced in
`StationaryMFG/Monotone/FiniteVI.lean`. The classical statement is
the Hartman–Stampacchia / Debrunner–Flor finite-dim variational
inequality on a polytope `C = convexHull ℝ F` with `F : Finset X`
nonempty: for every monotone operator `A : X → StrongDual ℝ X`
defined on `C`, there exists `u ∈ C` such that
`0 ≤ A v (v - u)` for every `v ∈ C`.

Rather than vendor KKM / Brouwer / Debrunner–Flor, we prove the
result via Mathlib's `Sion.exists_isSaddlePointOn` plus a compact
finite-intersection-property argument, following
`docs/MONOTONE_PLAN.md` §2.

## Strategy

1. **Sample payoff.** For an indexed finite family `p : ι → X` with
   image in `C`, define the bilinear payoff
   `samplePayoff p A λ u := ∑ i, λ i • (A (p i)) (p i - u)`.
   It is linear in `λ` (hence convex and concave in `λ`) and affine
   in `u` (hence convex and concave in `u`). In particular it is
   l.s.c./quasiconvex in `λ` and u.s.c./quasiconcave in `u`.
2. **Sion saddle.** Apply `Sion.exists_isSaddlePointOn` to the game
   `samplePayoff p A : stdSimplex ℝ ι × C → ℝ` to extract a saddle
   pair `(λ₀, u₀)`. The saddle inequality
   `f λ₀ u ≤ f λ u₀` for all `λ ∈ stdSimplex`, `u ∈ C`.
3. **Vertex collapse.** At `λ = stdSimplex.vertex i`, the right-hand
   side collapses to the single constraint
   `A (p i) (p i - u₀)`.
4. **Monotonicity bound.** At `u = ∑ (λ₀)ᵢ • p i`, monotonicity
   collapses the left-hand side to `0`. Hence `0 ≤ A (p i) (p i - u₀)`
   for every `i`.
5. **Compact FIP upgrade.** With `C` compact (`Set.Finite.isCompact_convexHull`),
   the closed half-spaces `{u ∈ C | 0 ≤ A v (v - u)}` (closed by
   continuity of `A v` as a continuous linear functional) have the
   finite intersection property — each finite subfamily is nonempty
   by step (4) applied to the corresponding finite index set —
   and `IsCompact.inter_iInter_nonempty` produces the universal `u₀`.

## Main declarations

* `StationaryMFG.Monotone.finiteConstraintVI` — the Sion-based
  statement: for any nonempty `F : Finset X` and any `A` monotone
  on `convexHull ℝ F`, there exists `u ∈ convexHull ℝ F` such that
  `0 ≤ A v (v - u)` for every `v ∈ F` (the finite vertex set).
* `StationaryMFG.Monotone.finiteConvexHullWeakVI` — the universal
  upgrade: same `u` works for every `v ∈ convexHull ℝ F`.
* `StationaryMFG.Monotone.instFiniteConvexHullWeakVI` — the resulting
  typeclass instance, dropping the `FiniteConvexHullWeakVI X`
  hypothesis from `monotone_abstract_weak`.
-/

noncomputable section

namespace StationaryMFG
namespace Monotone

open NormedSpace Set
open scoped BigOperators

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ## Sample payoff and its convexity / continuity properties -/

/-- The sample payoff of an operator `A` on a finite family of points
`p : ι → X` is `samplePayoff p A λ u := ∑ i, λ i • A (p i) (p i - u)`.
It is linear in `λ` (so convex and concave in `λ`), and affine in `u`
(so convex and concave in `u`). -/
def samplePayoff {ι : Type*} [Fintype ι]
    (p : ι → X) (A : X → StrongDual ℝ X) (lam : ι → ℝ) (u : X) : ℝ :=
  ∑ i, lam i • (A (p i)) (p i - u)

/-- The sample payoff `samplePayoff p A` viewed as a map of `λ` for fixed
`u`, packaged as a real-valued linear map `(ι → ℝ) →ₗ[ℝ] ℝ`. -/
def samplePayoffLeftLM {ι : Type*} [Fintype ι]
    (p : ι → X) (A : X → StrongDual ℝ X) (u : X) : (ι → ℝ) →ₗ[ℝ] ℝ where
  toFun lam := ∑ i, lam i * (A (p i)) (p i - u)
  map_add' lam μ := by
    simp [Finset.sum_add_distrib, add_mul]
  map_smul' c lam := by
    simp [Finset.mul_sum, mul_assoc]

@[simp] lemma samplePayoffLeftLM_apply {ι : Type*} [Fintype ι]
    (p : ι → X) (A : X → StrongDual ℝ X) (u : X) (lam : ι → ℝ) :
    samplePayoffLeftLM p A u lam = ∑ i, lam i * (A (p i)) (p i - u) := rfl

lemma samplePayoff_eq_left_lm {ι : Type*} [Fintype ι]
    (p : ι → X) (A : X → StrongDual ℝ X) (lam : ι → ℝ) (u : X) :
    samplePayoff p A lam u = samplePayoffLeftLM p A u lam := by
  simp [samplePayoff, samplePayoffLeftLM, smul_eq_mul]

/-- Linearity of `samplePayoff` in `λ`. -/
lemma samplePayoff_add_left {ι : Type*} [Fintype ι]
    (p : ι → X) (A : X → StrongDual ℝ X) (lam μ : ι → ℝ) (u : X) :
    samplePayoff p A (lam + μ) u
      = samplePayoff p A lam u + samplePayoff p A μ u := by
  simp [samplePayoff_eq_left_lm, map_add]

lemma samplePayoff_smul_left {ι : Type*} [Fintype ι]
    (p : ι → X) (A : X → StrongDual ℝ X) (c : ℝ) (lam : ι → ℝ) (u : X) :
    samplePayoff p A (c • lam) u = c • samplePayoff p A lam u := by
  simp [samplePayoff_eq_left_lm, map_smul]

/-- The sample payoff `samplePayoff p A` viewed as a map of `u` for fixed
`λ`. The expression
`samplePayoff p A λ u = (∑ i, λ i * A (p i) (p i)) - (∑ i, λ i • A (p i)) u`
shows it is affine in `u`; we record the constant and linear parts. -/
lemma samplePayoff_eq_const_sub {ι : Type*} [Fintype ι]
    (p : ι → X) (A : X → StrongDual ℝ X) (lam : ι → ℝ) (u : X) :
    samplePayoff p A lam u
      = (∑ i, lam i • (A (p i)) (p i)) - (∑ i, lam i • (A (p i)) u) := by
  simp only [samplePayoff, map_sub, smul_sub, Finset.sum_sub_distrib]

/-- Continuity of `samplePayoff` in `λ` (jointly with `u` fixed): the map
`λ ↦ samplePayoff p A λ u` is continuous. -/
lemma continuous_samplePayoff_left {ι : Type*} [Fintype ι]
    (p : ι → X) (A : X → StrongDual ℝ X) (u : X) :
    Continuous (fun lam : ι → ℝ => samplePayoff p A lam u) := by
  unfold samplePayoff
  refine continuous_finset_sum _ ?_
  intro i _
  exact (continuous_apply i).smul continuous_const

/-- Continuity of `samplePayoff` in `u` for fixed `λ`. -/
lemma continuous_samplePayoff_right {ι : Type*} [Fintype ι]
    (p : ι → X) (A : X → StrongDual ℝ X) (lam : ι → ℝ) :
    Continuous (fun u : X => samplePayoff p A lam u) := by
  simp only [samplePayoff_eq_const_sub]
  refine Continuous.sub continuous_const ?_
  refine continuous_finset_sum _ ?_
  intro i _
  exact (continuous_const.mul ((A (p i)).continuous))

/-! ## Convexity slices -/

/-- Affine identity used to prove both convexity and concavity in `λ`:
the sample payoff is **linear** in `λ`, so for any convex combination,
both inequalities reduce to equality. -/
lemma samplePayoff_left_affine {ι : Type*} [Fintype ι]
    (p : ι → X) (A : X → StrongDual ℝ X) (u : X)
    (lam μ : ι → ℝ) (a b : ℝ) :
    samplePayoff p A (a • lam + b • μ) u
      = a • samplePayoff p A lam u + b • samplePayoff p A μ u := by
  rw [samplePayoff_add_left, samplePayoff_smul_left, samplePayoff_smul_left]

/-- The `λ`-slice of `samplePayoff` is convex (it is linear). -/
lemma convexOn_samplePayoff_left {ι : Type*} [Fintype ι]
    (p : ι → X) (A : X → StrongDual ℝ X) (u : X) :
    ConvexOn ℝ (stdSimplex ℝ ι) (fun lam => samplePayoff p A lam u) := by
  refine ⟨convex_stdSimplex ℝ ι, ?_⟩
  intro lam _ μ _ a b _ _ _
  change samplePayoff p A (a • lam + b • μ) u
      ≤ a • samplePayoff p A lam u + b • samplePayoff p A μ u
  rw [samplePayoff_left_affine]

/-- The `λ`-slice of `samplePayoff` is concave (it is linear). -/
lemma concaveOn_samplePayoff_left {ι : Type*} [Fintype ι]
    (p : ι → X) (A : X → StrongDual ℝ X) (u : X) :
    ConcaveOn ℝ (stdSimplex ℝ ι) (fun lam => samplePayoff p A lam u) := by
  refine ⟨convex_stdSimplex ℝ ι, ?_⟩
  intro lam _ μ _ a b _ _ _
  change a • samplePayoff p A lam u + b • samplePayoff p A μ u
      ≤ samplePayoff p A (a • lam + b • μ) u
  rw [samplePayoff_left_affine]

/-- Affine identity used to prove both convexity and concavity in `u`:
the sample payoff is **affine** (constant minus linear) in `u`,
so for any convex combination both inequalities reduce to equality.

Concretely:
`f(a • u + b • v) = c - L(a • u + b • v) = a (c - L u) + b (c - L v)`
when `a + b = 1`. -/
lemma samplePayoff_right_affine {ι : Type*} [Fintype ι]
    (p : ι → X) (A : X → StrongDual ℝ X) (lam : ι → ℝ) (u v : X)
    {a b : ℝ} (hab : a + b = 1) :
    samplePayoff p A lam (a • u + b • v)
      = a • samplePayoff p A lam u + b • samplePayoff p A lam v := by
  rw [samplePayoff_eq_const_sub, samplePayoff_eq_const_sub p A lam u,
      samplePayoff_eq_const_sub p A lam v]
  set c : ℝ := ∑ i, lam i • (A (p i)) (p i)
  have hL : (∑ i, lam i • (A (p i)) (a • u + b • v))
      = a * (∑ i, lam i • (A (p i)) u) + b * (∑ i, lam i • (A (p i)) v) := by
    have : ∀ i, lam i • (A (p i)) (a • u + b • v)
          = a * (lam i • (A (p i)) u) + b * (lam i • (A (p i)) v) := by
      intro i
      simp [map_add, map_smul, smul_eq_mul]
      ring
    simp only [this]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hL]
  have habc : a * c + b * c = c := by
    have : (a + b) * c = c := by rw [hab]; ring
    linarith
  simp only [smul_eq_mul]
  linarith

/-- The `u`-slice of `samplePayoff` is convex (it is affine). -/
lemma convexOn_samplePayoff_right {ι : Type*} [Fintype ι]
    {C : Set X} (hC : Convex ℝ C)
    (p : ι → X) (A : X → StrongDual ℝ X) (lam : ι → ℝ) :
    ConvexOn ℝ C (fun u => samplePayoff p A lam u) := by
  refine ⟨hC, ?_⟩
  intro u _ v _ a b _ _ hab
  change samplePayoff p A lam (a • u + b • v)
      ≤ a • samplePayoff p A lam u + b • samplePayoff p A lam v
  rw [samplePayoff_right_affine p A lam u v hab]

/-- The `u`-slice of `samplePayoff` is concave (it is affine). -/
lemma concaveOn_samplePayoff_right {ι : Type*} [Fintype ι]
    {C : Set X} (hC : Convex ℝ C)
    (p : ι → X) (A : X → StrongDual ℝ X) (lam : ι → ℝ) :
    ConcaveOn ℝ C (fun u => samplePayoff p A lam u) := by
  refine ⟨hC, ?_⟩
  intro u _ v _ a b _ _ hab
  change a • samplePayoff p A lam u + b • samplePayoff p A lam v
      ≤ samplePayoff p A lam (a • u + b • v)
  rw [samplePayoff_right_affine p A lam u v hab]

/-! ## Vertex collapse and barycenter identity -/

/-- At a vertex of the standard simplex, the sample payoff collapses to
the single-vertex evaluation. -/
lemma samplePayoff_vertex {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → X) (A : X → StrongDual ℝ X) (i : ι) (u : X) :
    samplePayoff p A (Pi.single i 1) u = (A (p i)) (p i - u) := by
  unfold samplePayoff
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- The "barycenter" `y_λ := ∑ λ i • p i` is in the convex hull of
the points whenever `λ ∈ stdSimplex`. -/
lemma barycenter_mem_convexHull {ι : Type*} [Fintype ι]
    [Nonempty ι]
    {p : ι → X} {C : Set X} (hp : ∀ i, p i ∈ C) (hC : Convex ℝ C)
    (lam : ι → ℝ) (hlam : lam ∈ stdSimplex ℝ ι) :
    (∑ i, lam i • p i) ∈ C := by
  -- Use Convex.sum_mem with weights `lam i`.
  refine hC.sum_mem (t := Finset.univ) ?_ ?_ ?_
  · intro i _; exact hlam.1 i
  · exact hlam.2
  · intro i _; exact hp i

/-- **Key positivity lemma.** For `y := ∑ i, λ i • p i` (the barycenter),
monotonicity collapses `samplePayoff p A λ y ≥ 0`.

Proof: by monotonicity, `(A (p i) - A y)(p i - y) ≥ 0`, hence
`A y (p i - y) ≤ A (p i) (p i - y)` for each `i`. Weighted-summing:
`∑ λᵢ • A (p i) (p i - y) ≥ ∑ λᵢ • A y (p i - y) = A y (∑ λᵢ • (p i - y))`.
And `∑ λᵢ • (p i - y) = (∑ λᵢ • p i) - (∑ λᵢ) • y = y - 1 • y = 0`. -/
lemma samplePayoff_nonneg_at_barycenter
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {C : Set X} (hC : Convex ℝ C)
    (p : ι → X) (hp : ∀ i, p i ∈ C)
    (A : X → StrongDual ℝ X) (hA : IsMonotone C A)
    (lam : ι → ℝ) (hlam : lam ∈ stdSimplex ℝ ι) :
    0 ≤ samplePayoff p A lam (∑ i, lam i • p i) := by
  set y := ∑ i, lam i • p i with hy
  have hy_mem : y ∈ C := barycenter_mem_convexHull hp hC lam hlam
  -- Monotonicity gives `A y (p i - y) ≤ A (p i) (p i - y)`.
  have hmono : ∀ i, (A y) (p i - y) ≤ (A (p i)) (p i - y) := by
    intro i
    have h := hA hy_mem (hp i)
    -- `0 ≤ (A y - A (p i)) (y - p i)`.
    have hexp : (A y - A (p i)) (y - p i)
        = (A (p i)) (p i - y) - (A y) (p i - y) := by
      simp only [ContinuousLinearMap.sub_apply, map_sub]
      ring
    linarith [hexp ▸ h]
  -- Weighted sum: 0 ≤ ∑ λᵢ • (A (p i) - A y)(p i - y),
  -- equivalently ∑ λᵢ • A y (p i - y) ≤ ∑ λᵢ • A (p i) (p i - y).
  have hsum_le : ∑ i, lam i • (A y) (p i - y)
      ≤ ∑ i, lam i • (A (p i)) (p i - y) := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (hmono i) (hlam.1 i)
  -- The LHS equals `A y (∑ λᵢ • (p i - y)) = A y 0 = 0`.
  have hzero : ∑ i, lam i • (p i - y) = (0 : X) := by
    have : ∑ i, lam i • (p i - y)
        = (∑ i, lam i • p i) - (∑ i, lam i) • y := by
      simp [smul_sub, Finset.sum_sub_distrib, Finset.sum_smul]
    rw [this, ← hy, hlam.2, one_smul, sub_self]
  have hLHS : ∑ i, lam i • (A y) (p i - y) = 0 := by
    have hlin : (∑ i, lam i • (A y) (p i - y))
        = (A y) (∑ i, lam i • (p i - y)) := by
      simp only [map_sum, map_smul, smul_eq_mul]
    rw [hlin, hzero, map_zero]
  -- Conclude.
  calc (0 : ℝ) = ∑ i, lam i • (A y) (p i - y) := hLHS.symm
    _ ≤ ∑ i, lam i • (A (p i)) (p i - y) := hsum_le
    _ = samplePayoff p A lam y := by rfl

/-! ## Sion application: indexed finite-constraint VI -/

section
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-- **Indexed finite-constraint VI** (Sion). Given a finite family
`p : ι → C` (with `C := convexHull ℝ F` compact convex nonempty), and
`A` monotone on `C`, there exists `u₀ ∈ C` such that
`0 ≤ A (p i) (p i - u₀)` for every `i : ι`.

The `[Fintype ι]` and `[DecidableEq ι]` instances are used inside the
proof (to invoke `Pi.single`, `Sion.exists_isSaddlePointOn`, and
`stdSimplex.vertex`), even though they don't appear in the final
statement. The linter is suppressed accordingly. -/
lemma finiteConstraintVI_indexed
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {C : Set X} (hC_cvx : Convex ℝ C) (hC_cpt : IsCompact C)
    (hC_ne : C.Nonempty)
    (p : ι → X) (hp : ∀ i, p i ∈ C)
    (A : X → StrongDual ℝ X) (hA : IsMonotone C A) :
    ∃ u₀ ∈ C, ∀ i : ι, 0 ≤ (A (p i)) (p i - u₀) := by
  -- Set up the Sion game.
  -- `X_S := stdSimplex ℝ ι`, `Y_S := C`, payoff `f λ u := samplePayoff p A λ u`.
  set f : (ι → ℝ) → X → ℝ := samplePayoff p A with hf_def
  set XS : Set (ι → ℝ) := stdSimplex ℝ ι with hXS
  -- Hypotheses for Sion.
  have ne_X : XS.Nonempty := by
    refine ⟨Pi.single (Classical.arbitrary ι) 1, ?_⟩
    exact single_mem_stdSimplex ℝ _
  have cX : Convex ℝ XS := convex_stdSimplex ℝ ι
  have kX : IsCompact XS := isCompact_stdSimplex ℝ ι
  have cY : Convex ℝ C := hC_cvx
  have ne_Y : C.Nonempty := hC_ne
  have kY : IsCompact C := hC_cpt
  -- LSC of `λ ↦ f λ u` and quasiconvexity in `λ`.
  have hfy : ∀ u ∈ C, LowerSemicontinuousOn (fun lam : ι → ℝ => f lam u) XS := by
    intro u _
    exact (continuous_samplePayoff_left p A u).continuousOn.lowerSemicontinuousOn
  have hfy' : ∀ u ∈ C, QuasiconvexOn ℝ XS (fun lam : ι → ℝ => f lam u) := by
    intro u _
    exact (convexOn_samplePayoff_left p A u).quasiconvexOn
  -- USC of `u ↦ f λ u` and quasiconcavity in `u`.
  have hfx : ∀ lam ∈ XS, UpperSemicontinuousOn (fun u : X => f lam u) C := by
    intro lam _
    exact (continuous_samplePayoff_right p A lam).continuousOn.upperSemicontinuousOn
  have hfx' : ∀ lam ∈ XS, QuasiconcaveOn ℝ C (fun u : X => f lam u) := by
    intro lam _
    exact (concaveOn_samplePayoff_right hC_cvx p A lam).quasiconcaveOn
  -- Apply Sion.
  obtain ⟨lam₀, hlam₀, u₀, hu₀, hsaddle⟩ :=
    Sion.exists_isSaddlePointOn (X := XS) (Y := C) (f := f)
      ne_X cX kX hfy hfy' cY ne_Y kY hfx hfx'
  refine ⟨u₀, hu₀, ?_⟩
  intro i
  -- Saddle: ∀ x ∈ X, ∀ y ∈ Y, f lam₀ y ≤ f x u₀.
  -- Plug `x := vertex i` and `y := y_{lam₀} := ∑ lam₀ j • p j`.
  set y_lam : X := ∑ j, lam₀ j • p j with hy_lam
  have hy_lam_mem : y_lam ∈ C :=
    barycenter_mem_convexHull hp hC_cvx lam₀ hlam₀
  -- LHS bound: 0 ≤ f lam₀ y_lam (positivity at barycenter).
  have hLHS : 0 ≤ f lam₀ y_lam :=
    samplePayoff_nonneg_at_barycenter hC_cvx p hp A hA lam₀ hlam₀
  -- Saddle inequality at (vertex i, y_lam).
  have hvertex_mem : (Pi.single i 1 : ι → ℝ) ∈ XS := single_mem_stdSimplex ℝ i
  have hsad := hsaddle (Pi.single i 1) hvertex_mem y_lam hy_lam_mem
  -- `f lam₀ y_lam ≤ f (vertex i) u₀ = A (p i) (p i - u₀)`.
  have hcollapse : f (Pi.single i 1) u₀ = (A (p i)) (p i - u₀) :=
    samplePayoff_vertex p A i u₀
  linarith [hcollapse ▸ hsad]

end

/-! ## Finite-constraint VI (Finset version) -/

/-- **Finite-constraint VI** (Finset version). Given `F : Finset X`
nonempty with `C := convexHull ℝ (F : Set X)`, and `A` monotone on `C`,
there exists `u ∈ C` such that `0 ≤ A v (v - u)` for every `v ∈ F`. -/
lemma finiteConstraintVI
    {F : Finset X} (hF : F.Nonempty)
    (A : X → StrongDual ℝ X)
    (hA : IsMonotone (convexHull ℝ (F : Set X)) A) :
    ∃ u ∈ convexHull ℝ (F : Set X),
      ∀ v ∈ F, 0 ≤ (A v) (v - u) := by
  classical
  -- Translate to the indexed version with `ι := ↥F`.
  set C := convexHull ℝ ((F : Set X)) with hC_def
  have hC_cvx : Convex ℝ C := convex_convexHull _ _
  have hF_finite : (F : Set X).Finite := F.finite_toSet
  have hC_cpt : IsCompact C := hF_finite.isCompact_convexHull (𝕜 := ℝ)
  have hC_ne : C.Nonempty := by
    obtain ⟨x, hx⟩ := hF
    exact ⟨x, subset_convexHull ℝ _ hx⟩
  let ι := {x // x ∈ F}
  haveI : Fintype ι := FinsetCoe.fintype F
  haveI : Nonempty ι := by
    obtain ⟨x, hx⟩ := hF; exact ⟨⟨x, hx⟩⟩
  haveI : DecidableEq ι := Subtype.instDecidableEq
  let p : ι → X := fun v => v.val
  have hp : ∀ i : ι, p i ∈ C := by
    intro v
    exact subset_convexHull ℝ _ v.property
  obtain ⟨u₀, hu₀_mem, hu₀_VI⟩ :=
    finiteConstraintVI_indexed hC_cvx hC_cpt hC_ne p hp A hA
  refine ⟨u₀, hu₀_mem, ?_⟩
  intro v hv
  exact hu₀_VI ⟨v, hv⟩

/-! ## Compact FIP upgrade -/

/-- The half-space `{u | 0 ≤ A v (v - u)}` is closed in `X` (continuity
of `A v` as a continuous linear functional). -/
lemma isClosed_viHalfspace (A : X → StrongDual ℝ X) (v : X) :
    IsClosed {u : X | 0 ≤ (A v) (v - u)} := by
  -- `u ↦ A v (v - u)` is continuous.
  have hcont : Continuous (fun u : X => (A v) (v - u)) :=
    (A v).continuous.comp (continuous_const.sub continuous_id)
  exact isClosed_le continuous_const hcont

/-- **Compact FIP upgrade.** Given a compact convex nonempty set `C` and
`A` monotone on `C`, suppose every finite subset `G ⊂ C` admits a
`u ∈ C` with `∀ v ∈ G, 0 ≤ A v (v - u)`. Then there exists a
universal `u ∈ C` with `∀ v ∈ C, 0 ≤ A v (v - u)`. -/
lemma compactFIP_upgrade
    {C : Set X} (hC_cpt : IsCompact C) (_hC_ne : C.Nonempty)
    (A : X → StrongDual ℝ X)
    (h_finite : ∀ G : Finset C, ∃ u ∈ C,
      ∀ v ∈ G, 0 ≤ (A v.val) (v.val - u)) :
    ∃ u ∈ C, ∀ v ∈ C, 0 ≤ (A v) (v - u) := by
  classical
  -- Index half-spaces by `↥C`.
  let S : C → Set X := fun v => {u : X | 0 ≤ (A v.val) (v.val - u)}
  have hS_closed : ∀ v : C, IsClosed (S v) := fun v => isClosed_viHalfspace A v.val
  -- Finite-subfamily nonemptiness:
  -- For any Finset G ⊂ ↥C, the intersection `C ∩ ⋂ v ∈ G, S v` is nonempty.
  have h_finset : ∀ G : Finset C, (C ∩ ⋂ v ∈ G, S v).Nonempty := by
    intro G
    obtain ⟨u, hu_C, hu_G⟩ := h_finite G
    refine ⟨u, hu_C, ?_⟩
    simp only [Set.mem_iInter]
    intro v hv
    exact hu_G v hv
  -- Apply IsCompact.inter_iInter_nonempty.
  have hbig : (C ∩ ⋂ v : C, S v).Nonempty :=
    hC_cpt.inter_iInter_nonempty S hS_closed h_finset
  obtain ⟨u, hu_C, hu_inter⟩ := hbig
  refine ⟨u, hu_C, ?_⟩
  intro v hv
  have : u ∈ S ⟨v, hv⟩ := by
    simp only [Set.mem_iInter] at hu_inter
    exact hu_inter ⟨v, hv⟩
  exact this

/-! ## Headline theorem and instance -/

/-- **Finite convex-hull weak VI** (headline theorem). For any nonempty
`F : Finset X` and any `A` monotone on `convexHull ℝ F`, there exists
`u ∈ convexHull ℝ F` such that `0 ≤ A v (v - u)` for every
`v ∈ convexHull ℝ F`.

This discharges the typeclass `FiniteConvexHullWeakVI X` for every
real normed space `X`, removing the typeclass argument from
`monotone_abstract_weak`. -/
theorem finiteConvexHullWeakVI
    {F : Finset X} (hF : F.Nonempty)
    (A : X → StrongDual ℝ X)
    (hA : IsMonotone (convexHull ℝ (F : Set X)) A) :
    ∃ u ∈ convexHull ℝ (F : Set X),
      ∀ v ∈ convexHull ℝ (F : Set X), 0 ≤ (A v) (v - u) := by
  classical
  set C := convexHull ℝ ((F : Set X)) with hC_def
  have hC_cvx : Convex ℝ C := convex_convexHull _ _
  have hF_finite : (F : Set X).Finite := F.finite_toSet
  have hC_cpt : IsCompact C := hF_finite.isCompact_convexHull (𝕜 := ℝ)
  have hC_ne : C.Nonempty := by
    obtain ⟨x, hx⟩ := hF
    exact ⟨x, subset_convexHull ℝ _ hx⟩
  -- For any finite subfamily `G ⊂ C`, build a Finset `F'` extending `F`
  -- by adjoining the values, then use `finiteConstraintVI_indexed` over
  -- `F ∪ G.image Subtype.val` so the indexed family covers both `F`
  -- (giving the half-space constraint) and `G` (giving the points).
  apply compactFIP_upgrade hC_cpt hC_ne A
  intro G
  -- Build Finset of `X` containing all chosen sample points + F.
  let G' : Finset X := F ∪ G.image Subtype.val
  have hG'_ne : G'.Nonempty := hF.mono Finset.subset_union_left
  -- All points of `G'` are in `C` — `F ⊂ C` (vertices) and `G.image Val ⊂ C`.
  have hG'_subset_C : (G' : Set X) ⊆ C := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxF | hxG
    · exact subset_convexHull ℝ _ hxF
    · obtain ⟨⟨y, hy_mem⟩, _, rfl⟩ := Finset.mem_image.mp hxG
      exact hy_mem
  -- Hull of `G'` is contained in `C` (since `C` is convex containing `G'`).
  have hHull_G'_subset : convexHull ℝ ((G' : Set X)) ⊆ C :=
    convexHull_min hG'_subset_C hC_cvx
  -- A monotone on `C` — restrict to the hull of `G'`.
  have hA' : IsMonotone (convexHull ℝ ((G' : Set X))) A := by
    intro v₁ hv₁ v₂ hv₂
    exact hA (hHull_G'_subset hv₁) (hHull_G'_subset hv₂)
  -- Apply the indexed finite-constraint VI.
  let ι := {x // x ∈ G'}
  haveI : Fintype ι := FinsetCoe.fintype G'
  haveI : Nonempty ι := by
    obtain ⟨x, hx⟩ := hG'_ne; exact ⟨⟨x, hx⟩⟩
  haveI : DecidableEq ι := Subtype.instDecidableEq
  let p : ι → X := fun v => v.val
  have hp : ∀ i : ι, p i ∈ convexHull ℝ ((G' : Set X)) := by
    intro v
    exact subset_convexHull ℝ _ v.property
  -- Compactness etc. for the inner Sion game on the hull of `G'`.
  have hG'_finite : (G' : Set X).Finite := G'.finite_toSet
  have hHull_G'_cvx : Convex ℝ (convexHull ℝ ((G' : Set X))) :=
    convex_convexHull _ _
  have hHull_G'_cpt : IsCompact (convexHull ℝ ((G' : Set X))) :=
    hG'_finite.isCompact_convexHull (𝕜 := ℝ)
  have hHull_G'_ne : (convexHull ℝ ((G' : Set X))).Nonempty := by
    obtain ⟨x, hx⟩ := hG'_ne
    exact ⟨x, subset_convexHull ℝ _ hx⟩
  obtain ⟨u₀, hu₀_hull, hu₀_VI⟩ :=
    finiteConstraintVI_indexed hHull_G'_cvx hHull_G'_cpt hHull_G'_ne p hp A hA'
  refine ⟨u₀, hHull_G'_subset hu₀_hull, ?_⟩
  intro v hv
  -- `v ∈ G ⊂ G'` (image), so `⟨v.val, _⟩ : ι` exists.
  have hv_in_G' : v.val ∈ G' := by
    apply Finset.mem_union.mpr; right
    exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
  exact hu₀_VI ⟨v.val, hv_in_G'⟩

/-- The typeclass instance discharging `FiniteConvexHullWeakVI X`. -/
instance instFiniteConvexHullWeakVI
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] :
    FiniteConvexHullWeakVI X where
  exists_vi := by
    intro A F hF hA
    exact finiteConvexHullWeakVI (X := X) hF A hA

/-! ## Sanity check -/

/-- **Sanity-check `example`.** Apply the unconditional instance to a 2D
simplex: take `F := {(0,0), (1,0), (0,1)} ⊂ ℝ²` and the zero operator;
the hull is the closed triangle and the trivial VI holds for any `u`
in it. -/
example :
    ∃ u ∈ convexHull ℝ
        (({![0, 0], ![1, 0], ![0, 1]} : Finset (Fin 2 → ℝ)) : Set (Fin 2 → ℝ)),
      ∀ v ∈ convexHull ℝ
          (({![0, 0], ![1, 0], ![0, 1]} : Finset (Fin 2 → ℝ)) : Set (Fin 2 → ℝ)),
        0 ≤ (fun _ : (Fin 2 → ℝ) =>
          (0 : StrongDual ℝ (Fin 2 → ℝ))) v (v - u) := by
  classical
  apply FiniteConvexHullWeakVI.exists_vi
    (X := (Fin 2 → ℝ))
    ({![0, 0], ![1, 0], ![0, 1]} : Finset (Fin 2 → ℝ))
  · -- Nonempty: contains `![0, 0]`.
    exact ⟨![0, 0], by simp⟩
  · -- Monotone: zero operator.
    exact isMonotone_zero _

end Monotone
end StationaryMFG
