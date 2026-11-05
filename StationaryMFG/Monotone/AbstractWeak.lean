module

public import StationaryMFG.Basic
public import StationaryMFG.Monotone.Operator
public import StationaryMFG.Monotone.Coercive
public import StationaryMFG.Monotone.CoerciveBound
public import StationaryMFG.Monotone.FiniteVI
public import StationaryMFG.Monotone.WeakTopology
public import StationaryMFG.Periodic.Reflexive
public import Mathlib.Topology.Compactness.Compact

@[expose] public section

/-!
# Browder–Minty abstract weak variational inequality theorem

This file proves `paper:thm:monotone.abstract-weak`, the headline existence
theorem for weak variational inequalities associated with monotone and
coercive operators on a reflexive Banach space:

> Let `X` be a reflexive Banach space, `K ⊂ X` a nonempty convex subset,
> and `A : X → X' = StrongDual ℝ X` an operator that is monotone on `K`
> and coercive on `K` at some base point `v₀ ∈ K`. Then there exists
> `u ∈ closure K` such that `0 ≤ ⟨A v, v - u⟩` for every `v ∈ K`.

See `Source/FGU-monotone_revised.tex`, line 801, eq. `eq:weakIneqA`.

## Strategy

We follow the proof outlined in the paper (lines 810–830) and in
`docs/MONOTONE_PLAN.md` §1, with the five steps:

* **(A) Coercive radius (refined).** A *single-midpoint* version of
  the radius bound: if `u ∈ K` and the VI holds *just at the midpoint*
  `m := (u + v₀)/2`, then `‖u‖ ≤ R(A, v₀)` for an `R` depending only on
  `(A, v₀)` and the coercivity data. This is precisely what the proof
  of `IsCoerciveAt.exists_radius_for_midpoint_vi` actually establishes,
  but the present file only needs the VI at the midpoint. We re-derive
  the bound inline.
* **(B) Compact weak core.** `B := Metric.closedBall (0 : X) R ∩ closure K`
  has weakly compact image — Banach–Alaoglu via reflexivity
  (`isCompact_closure_weak_of_isBounded_reflexive`).
* **(C) Closed half-spaces.** `S(v) := {u | 0 ≤ A v (v - u)}` is weakly
  closed (`isClosed_viHalfspaceW'`).
* **(D) Finite intersection nonemptiness.** Build `G := insert v₀ {vᵢ}`,
  apply `FiniteConvexHullWeakVI.exists_vi`, the midpoint `(u+v₀)/2` is
  in the hull, so the single-midpoint radius bound applies.
* **(E) Conclusion.** `IsCompact.inter_iInter_nonempty`.

## Main declarations

* `monotone_abstract_weak` — the theorem.
-/

noncomputable section

namespace StationaryMFG
namespace Monotone

open NormedSpace Set Filter
open scoped Topology

open StationaryMFG.Periodic (IsReflexiveNormedSpace)

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ## Auxiliary: single-midpoint radius bound -/

/-- **Single-midpoint radius bound.** Let `K ⊂ X` be convex, and let `A`
be coercive on `K` at `v₀`. Then there exists `R` such that whenever
`u ∈ K` and the variational inequality holds at the midpoint
`m := (u + v₀)/2`, namely `0 ≤ A m (m - u)` (which forces `m ∈ K` to be
meaningful — we package the membership as a hypothesis), we have `‖u‖ ≤ R`.

The radius depends only on the coercivity data and `v₀`. This is the
midpoint argument used inside `exists_radius_for_midpoint_vi`, but here
we only require the VI at the single midpoint `m`. -/
lemma IsCoerciveAt.exists_radius_for_single_midpoint
    {K : Set X} {A : X → StrongDual ℝ X} {v₀ : X}
    (h : IsCoerciveAt K A v₀) (_hK : Convex ℝ K) :
    ∃ R : ℝ, ∀ u ∈ K,
      ((1/2 : ℝ) • u + (1/2 : ℝ) • v₀ ∈ K) →
      (0 ≤ A ((1/2 : ℝ) • u + (1/2 : ℝ) • v₀)
            (((1/2 : ℝ) • u + (1/2 : ℝ) • v₀) - u)) →
      ‖u‖ ≤ R := by
  -- Threshold from coercivity.
  obtain ⟨R₀, hR₀⟩ := h.exists_radius_quotient_ge (‖A v₀‖ + 1)
  set M : ℝ := max (max R₀ (‖A v₀‖ * ‖v₀‖)) 0 with hM_def
  refine ⟨2 * M + ‖v₀‖, ?_⟩
  intro u hu_K hm_K hVIm
  set m : X := (1/2 : ℝ) • u + (1/2 : ℝ) • v₀ with hm_def
  -- Algebraic identities `m - u = -(m - v₀)` and `u = 2 • m - v₀`.
  have hid : m - u = -(m - v₀) := by
    change ((1/2 : ℝ) • u + (1/2 : ℝ) • v₀) - u
        = -(((1/2 : ℝ) • u + (1/2 : ℝ) • v₀) - v₀)
    module
  have hid_u : u = (2 : ℝ) • m - v₀ := by
    change u = (2 : ℝ) • ((1/2 : ℝ) • u + (1/2 : ℝ) • v₀) - v₀
    module
  have hAm_eq : A m (m - u) = - A m (m - v₀) := by
    rw [hid]; simp
  have hAm_le : A m (m - v₀) ≤ 0 := by
    have := hVIm
    rw [hAm_eq] at this; linarith
  have hpair : (A m - A v₀) (m - v₀) ≤ ‖A v₀‖ * ‖m - v₀‖ := by
    have hsplit :
        (A m - A v₀) (m - v₀) = A m (m - v₀) - A v₀ (m - v₀) := by
      simp [ContinuousLinearMap.sub_apply]
    have hop : ‖A v₀ (m - v₀)‖ ≤ ‖A v₀‖ * ‖m - v₀‖ :=
      (A v₀).le_opNorm (m - v₀)
    have habs : |A v₀ (m - v₀)| ≤ ‖A v₀‖ * ‖m - v₀‖ := by
      have := hop; rwa [Real.norm_eq_abs] at this
    have hop' : -(A v₀ (m - v₀)) ≤ ‖A v₀‖ * ‖m - v₀‖ := by
      have := abs_le.mp habs; linarith [this.1]
    rw [hsplit]; linarith
  have hM_R₀ : R₀ ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
  have hM_prod : ‖A v₀‖ * ‖v₀‖ ≤ M :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hM_nonneg : 0 ≤ M := le_max_right _ _
  have hAv0nn : 0 ≤ ‖A v₀‖ := norm_nonneg _
  have hm_norm_le_M : ‖m‖ ≤ M := by
    by_cases hcase : R₀ ≤ ‖m‖
    · have hquot := hR₀ m hm_K hcase
      have hmnn : 0 ≤ ‖m‖ := norm_nonneg _
      have hlhs : (‖A v₀‖ + 1) * ‖m‖ ≤ (A m - A v₀) (m - v₀) := by
        rcases lt_or_ge 0 ‖m‖ with hpos | hzero
        · rw [le_div_iff₀ hpos] at hquot; linarith
        · exfalso
          have hmz : ‖m‖ = 0 := le_antisymm hzero hmnn
          rw [hmz, div_zero] at hquot; linarith
      have hrhs : (A m - A v₀) (m - v₀) ≤ ‖A v₀‖ * (‖m‖ + ‖v₀‖) := by
        have hnsub : ‖m - v₀‖ ≤ ‖m‖ + ‖v₀‖ := norm_sub_le m v₀
        have hmul : ‖A v₀‖ * ‖m - v₀‖ ≤ ‖A v₀‖ * (‖m‖ + ‖v₀‖) :=
          mul_le_mul_of_nonneg_left hnsub hAv0nn
        linarith
      have habs : (‖A v₀‖ + 1) * ‖m‖ ≤ ‖A v₀‖ * (‖m‖ + ‖v₀‖) :=
        le_trans hlhs hrhs
      have habs' : ‖m‖ ≤ ‖A v₀‖ * ‖v₀‖ := by
        have e1 : (‖A v₀‖ + 1) * ‖m‖ = ‖A v₀‖ * ‖m‖ + ‖m‖ := by ring
        have e2 : ‖A v₀‖ * (‖m‖ + ‖v₀‖) = ‖A v₀‖ * ‖m‖ + ‖A v₀‖ * ‖v₀‖ := by
          ring
        linarith
      exact le_trans habs' hM_prod
    · have hlt : ‖m‖ < R₀ := lt_of_not_ge hcase
      exact le_trans hlt.le hM_R₀
  have hu_norm : ‖u‖ ≤ 2 * ‖m‖ + ‖v₀‖ := by
    rw [hid_u]
    calc ‖(2 : ℝ) • m - v₀‖
        ≤ ‖(2 : ℝ) • m‖ + ‖v₀‖ := norm_sub_le _ _
      _ = 2 * ‖m‖ + ‖v₀‖ := by rw [norm_smul]; simp
  linarith

/-! ## Headline theorem -/

/-- **Browder–Minty abstract weak variational inequality theorem**
(`paper:thm:monotone.abstract-weak`, eq. `eq:weakIneqA`).

Let `X` be a reflexive Banach space (encoded via
`IsReflexiveNormedSpace X`) admitting the finite-dimensional convex-hull
variational inequality (typeclass `FiniteConvexHullWeakVI X`). Let
`K ⊂ X` be convex, and let `A : X → StrongDual ℝ X` be monotone on `K`
and coercive on `K` at some base point `v₀ ∈ K`. Then there exists
`u ∈ closure K` satisfying `0 ≤ A v (v - u)` for every `v ∈ K`. -/
theorem monotone_abstract_weak
    [FiniteConvexHullWeakVI X]
    (hX : IsReflexiveNormedSpace X)
    {K : Set X} (hK_cvx : Convex ℝ K)
    {A : X → StrongDual ℝ X} (hA_mono : IsMonotone K A)
    {v₀ : X} (hA_coerc : IsCoerciveAt K A v₀) :
    ∃ u ∈ closure K, ∀ v ∈ K, 0 ≤ A v (v - u) := by
  -- (A) Single-midpoint radius bound.
  obtain ⟨R, hR⟩ := hA_coerc.exists_radius_for_single_midpoint hK_cvx
  set Rball : ℝ := max R ‖v₀‖ with hRball_def
  have hRball_R : R ≤ Rball := le_max_left _ _
  have hRball_v₀ : ‖v₀‖ ≤ Rball := le_max_right _ _
  have hv₀_K : v₀ ∈ K := hA_coerc.mem
  -- (B) Compact weak core: image in `WeakSpace ℝ X` of
  -- `B := closedBall 0 Rball ∩ closure K`. Since `toWeakSpace` is
  -- `LinearEquiv.refl` on the underlying type, set-theoretically this
  -- image *equals* `B` itself; we may work in `X` viewed with the weak
  -- topology and avoid the image entirely. We use the closure form
  -- supplied by `isCompact_compactCoreW`.
  set Tw : Set (WeakSpace ℝ X) :=
    closure ((toWeakSpace ℝ X) ''
      (Metric.closedBall (0 : X) Rball ∩ closure K)) with hTw_def
  have hTw_compact : IsCompact Tw :=
    isCompact_compactCoreW (X := X) hX Rball K
  -- (C) For each `v ∈ K`, the half-space is weakly closed.
  have hSw_closed :
      ∀ v : ↥K,
        IsClosed
          ((toWeakSpace ℝ X) '' {u : X | 0 ≤ A v.val (v.val - u)}) := by
    intro v
    exact isClosed_viHalfspaceW' (X := X) (A v.val) v.val
  -- (D) Finite intersection. We index over the subtype `↥K`.
  have hFI : ∀ F : Finset (↥K),
      (Tw ∩ ⋂ i ∈ F,
        (toWeakSpace ℝ X) '' {u : X | 0 ≤ A i.val (i.val - u)}).Nonempty := by
    intro F
    classical
    -- Build `G := insert v₀ (F.image Subtype.val)`.
    let G : Finset X := insert v₀ (F.image Subtype.val)
    have hG_ne : G.Nonempty := ⟨v₀, Finset.mem_insert_self _ _⟩
    have hG_subset_K : (G : Set X) ⊆ K := by
      intro x hx
      rcases Finset.mem_insert.mp hx with hx0 | hxF
      · exact hx0 ▸ hv₀_K
      · obtain ⟨⟨y, hy⟩, _, rfl⟩ := Finset.mem_image.mp hxF
        exact hy
    have hHull_subset_K : convexHull ℝ (G : Set X) ⊆ K :=
      convexHull_min hG_subset_K hK_cvx
    have hA_mono_hull : IsMonotone (convexHull ℝ (G : Set X)) A := by
      intro v₁ hv₁ v₂ hv₂
      exact hA_mono (hHull_subset_K hv₁) (hHull_subset_K hv₂)
    obtain ⟨u, hu_mem, hu_VI⟩ :=
      FiniteConvexHullWeakVI.exists_vi (X := X) (A := A) G hG_ne hA_mono_hull
    have hHull_cvx : Convex ℝ (convexHull ℝ (G : Set X)) := convex_convexHull _ _
    have hv₀_hull : v₀ ∈ convexHull ℝ (G : Set X) :=
      subset_convexHull ℝ _ (Finset.mem_insert_self _ _)
    have hu_K : u ∈ K := hHull_subset_K hu_mem
    -- Midpoint membership and VI at the midpoint.
    set m : X := (1/2 : ℝ) • u + (1/2 : ℝ) • v₀ with hm_def
    have hm_hull : m ∈ convexHull ℝ (G : Set X) := by
      have h12nn : (0 : ℝ) ≤ 1/2 := by norm_num
      have h12sum : (1 : ℝ)/2 + 1/2 = 1 := by norm_num
      exact hHull_cvx hu_mem hv₀_hull h12nn h12nn h12sum
    have hm_K : m ∈ K := hHull_subset_K hm_hull
    have hVIm : 0 ≤ A m (m - u) := hu_VI m hm_hull
    -- Apply the single-midpoint radius bound.
    have hu_norm_R : ‖u‖ ≤ R := hR u hu_K hm_K hVIm
    have hu_norm_Rball : ‖u‖ ≤ Rball := le_trans hu_norm_R hRball_R
    -- `u ∈ closedBall 0 Rball`.
    have hu_ball : u ∈ Metric.closedBall (0 : X) Rball := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hu_norm_Rball
    -- `u ∈ closure K`.
    have hu_closure : u ∈ closure K := subset_closure hu_K
    have hu_B : u ∈ Metric.closedBall (0 : X) Rball ∩ closure K :=
      ⟨hu_ball, hu_closure⟩
    -- Witness: `u` (viewed via `toWeakSpace`) lies in `Tw ∩ ⋂_{i ∈ F} Sw`.
    refine ⟨(toWeakSpace ℝ X) u, ?_, ?_⟩
    · -- `(toWeakSpace ℝ X) u ∈ Tw = closure (toWeakSpace ℝ X '' B)`.
      have hmem : (toWeakSpace ℝ X) u ∈
          (toWeakSpace ℝ X) ''
            (Metric.closedBall (0 : X) Rball ∩ closure K) :=
        ⟨u, hu_B, rfl⟩
      exact subset_closure hmem
    · -- For each `i ∈ F`, `(toWeakSpace ℝ X) u ∈ image of {x | 0 ≤ A i.val (i.val - x)}`.
      simp only [mem_iInter]
      intro i hi
      refine ⟨u, ?_, rfl⟩
      -- `0 ≤ A i.val (i.val - u)` since `i.val ∈ G ⊆ convexHull G` and we
      -- have the universal VI on the hull.
      have hi_hull : i.val ∈ convexHull ℝ (G : Set X) := by
        apply subset_convexHull
        apply Finset.mem_insert.mpr
        right
        exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
      exact hu_VI i.val hi_hull
  -- (E) Apply `IsCompact.inter_iInter_nonempty`.
  have hnonempty :
      (Tw ∩ ⋂ v : ↥K,
        (toWeakSpace ℝ X) '' {u : X | 0 ≤ A v.val (v.val - u)}).Nonempty :=
    hTw_compact.inter_iInter_nonempty
      (fun v : ↥K =>
        (toWeakSpace ℝ X) '' {u : X | 0 ≤ A v.val (v.val - u)})
      hSw_closed hFI
  -- Pull back: extract `x : WeakSpace ℝ X`, transport to `u : X`.
  obtain ⟨x, hxTw, hxInter⟩ := hnonempty
  -- The underlying set of `WeakSpace ℝ X` is `X`. The element `x` thus
  -- gives us a point in `X` directly via `(toWeakSpace ℝ X).symm x`.
  refine ⟨(toWeakSpace ℝ X).symm x, ?_, ?_⟩
  · -- Membership in `closure K`. From `x ∈ Tw = closure (toWeakSpace '' B)`,
    -- and the fact that `toWeakSpace = LinearEquiv.refl` so the image
    -- coincides set-theoretically with the source, we get
    -- `(toWeakSpace).symm x ∈ closure (B)` in `X`. Since closure in
    -- `WeakSpace ℝ X` is finer-or-equal to closure in `X`, and the
    -- *target set* for the closure is in fact already closed in the
    -- weak topology (being weakly compact and Hausdorff)…
    -- Cleaner: by Mazur, `closure (toWeakSpace '' B) = toWeakSpace '' closure B`
    -- when `B` is convex. But `B` is convex (intersection of two convex
    -- sets), and *closed* (intersection of two closed sets in `X`), so
    -- `closure B = B`. Hence `Tw = toWeakSpace '' B`, and
    -- `(toWeakSpace).symm x ∈ B ⊆ closure K`.
    have hB_conv : Convex ℝ
        (Metric.closedBall (0 : X) Rball ∩ closure K) := by
      exact (convex_closedBall (0 : X) Rball).inter (hK_cvx.closure)
    have hB_closed : IsClosed
        (Metric.closedBall (0 : X) Rball ∩ closure K) :=
      Metric.isClosed_closedBall.inter isClosed_closure
    have hMazur :
        (toWeakSpace ℝ X) ''
            closure (Metric.closedBall (0 : X) Rball ∩ closure K)
          = closure ((toWeakSpace ℝ X) ''
              (Metric.closedBall (0 : X) Rball ∩ closure K)) :=
      hB_conv.toWeakSpace_closure ℝ
    have hclos_eq :
        closure (Metric.closedBall (0 : X) Rball ∩ closure K)
          = Metric.closedBall (0 : X) Rball ∩ closure K :=
      hB_closed.closure_eq
    rw [hclos_eq] at hMazur
    -- So `Tw = toWeakSpace '' B`. Hence `x ∈ toWeakSpace '' B`.
    have hxB : x ∈ (toWeakSpace ℝ X) ''
        (Metric.closedBall (0 : X) Rball ∩ closure K) := by
      rw [show Tw = (toWeakSpace ℝ X) ''
          (Metric.closedBall (0 : X) Rball ∩ closure K) from hMazur.symm] at hxTw
      exact hxTw
    obtain ⟨u₀, hu₀B, hu₀_eq⟩ := hxB
    -- `(toWeakSpace).symm x = u₀ ∈ closure K`.
    have : (toWeakSpace ℝ X).symm x = u₀ := by
      rw [← hu₀_eq]; simp
    rw [this]
    exact hu₀B.2
  · -- Universal VI: for each `v ∈ K`, `0 ≤ A v (v - (toWeakSpace).symm x)`.
    intro v hv
    have hxv : x ∈ (toWeakSpace ℝ X) ''
        {u : X | 0 ≤ A v (v - u)} := by
      have := hxInter
      simp only [mem_iInter] at this
      exact this ⟨v, hv⟩
    obtain ⟨u₁, hu₁_VI, hu₁_eq⟩ := hxv
    have hsymm : (toWeakSpace ℝ X).symm x = u₁ := by
      rw [← hu₁_eq]; simp
    rw [hsymm]
    exact hu₁_VI

/-! ## Sanity-check `example` -/

/-- **Sanity-check `example` for `monotone_abstract_weak`.**

For a 1D operator (`X := ℝ`) and `K := {0}` (singleton, hence convex,
nonempty, bounded — coercivity is vacuous), the zero operator is monotone
and coercive on `{0}` at `0`. The theorem produces a `u ∈ closure {0} = {0}`,
i.e. `u = 0`, satisfying the trivial VI. -/
example
    [FiniteConvexHullWeakVI ℝ]
    (hℝ : IsReflexiveNormedSpace ℝ) :
    ∃ u ∈ closure ({0} : Set ℝ), ∀ v ∈ ({0} : Set ℝ),
      0 ≤ (fun _ => (0 : StrongDual ℝ ℝ)) v (v - u) := by
  refine monotone_abstract_weak (X := ℝ) hℝ
    (K := ({0} : Set ℝ))
    (convex_singleton 0)
    (A := fun _ => (0 : StrongDual ℝ ℝ))
    (isMonotone_zero _)
    (v₀ := 0)
    (isCoerciveAt_of_bounded_domain Bornology.isBounded_singleton _ rfl)

end Monotone
end StationaryMFG
