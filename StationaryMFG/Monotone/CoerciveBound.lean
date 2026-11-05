module

public import StationaryMFG.Basic
public import StationaryMFG.Monotone.Coercive

@[expose] public section

/-!
# Coercivity radius for half-space VIs (midpoint argument)

This file delivers the *uniform norm bound* lemma underlying the
finite-intersection step of `paper:thm:monotone.abstract-weak`
(`Source/FGU-monotone_revised.tex`, line 801, eq. `eq:weakIneqA`),
following `MONOTONE_PLAN.md` §1 step (A) and `PHASES.md` Phase 3
bullet `infra:P3-monotone-coercive-radius`.

## Statement (informal)

Let `K ⊂ X` be convex and `A : X → X' = StrongDual ℝ X` coercive on `K`
at a base point `v₀ ∈ K`. Then there is a radius `R = R(A, v₀)` such
that every `u ∈ K` satisfying the half-space variational inequality
```
∀ v ∈ K,  ⟨A v, v - u⟩_{X', X} ≥ 0
```
admits the uniform norm bound `‖u‖ ≤ R`.

## Strategy (paper's "midpoint trick")

Set `m := (u + v₀) / 2`. Convexity of `K` gives `m ∈ K`. Two algebraic
identities — `m - u = -(m - v₀)` and `u = 2 • m - v₀` — drive the proof:

* **Test the VI at `v = m`.** This yields `0 ≤ A m (m - u)`. Combined
  with `m - u = -(m - v₀)` and linearity of `A m`, we get
  `A m (m - v₀) ≤ 0`.
* **Subtract `A v₀ (m - v₀)`.** Hence
  `(A m - A v₀)(m - v₀) ≤ -A v₀ (m - v₀) ≤ ‖A v₀‖ · ‖m - v₀‖`.
* **Apply coercivity.** Whenever `‖m‖` exceeds the eventual radius `R₀`
  produced by coercivity, the LHS divided by `‖m‖` exceeds `‖A v₀‖ + 1`,
  hence `(‖A v₀‖ + 1) · ‖m‖ ≤ ‖A v₀‖ · (‖m‖ + ‖v₀‖)` and `‖m‖ ≤
  ‖A v₀‖ · ‖v₀‖`.
* **Bound `‖u‖`.** From `u = 2 • m - v₀` we get
  `‖u‖ ≤ 2‖m‖ + ‖v₀‖ ≤ 2 max(R₀, ‖A v₀‖ · ‖v₀‖) + ‖v₀‖`.

The auxiliary lemma `eventually_coerciveFilter_iff_exists_norm_bound`
isolates the cobounded-filter step and is independently useful for
downstream consumers.

## Main declarations

* `eventually_coerciveFilter_iff_exists_norm_bound` — characterise the
  cobounded-restricted-to-`D` filter via a uniform norm threshold.
* `IsCoerciveAt.exists_radius_for_midpoint_vi` — the headline radius
  bound (signature in `MONOTONE_PLAN.md` lines 70–82 and Phase 3 bullet).
-/

noncomputable section

namespace StationaryMFG
namespace Monotone

open NormedSpace Filter Bornology Set

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

set_option linter.unusedSectionVars false in
/-- Eventual statements on the coercive filter `cobounded ⊓ 𝓟 D` are
exactly statements that hold for every `v ∈ D` once `‖v‖` exceeds some
threshold. This is a convenience reformulation of
`Filter.eventually_inf_principal` paired with the cobounded basis
`{x | r ≤ ‖x‖}_{r : ℝ}`. -/
theorem eventually_coerciveFilter_iff_exists_norm_bound
    (D : Set X) (P : X → Prop) :
    (∀ᶠ v in coerciveFilter (X := X) D, P v)
      ↔ ∃ R : ℝ, ∀ v ∈ D, R ≤ ‖v‖ → P v := by
  unfold coerciveFilter
  rw [eventually_inf_principal]
  rw [Filter.hasBasis_cobounded_norm.eventually_iff]
  constructor
  · rintro ⟨R, _, hR⟩
    refine ⟨R, fun v hv hnorm => ?_⟩
    exact hR hnorm hv
  · rintro ⟨R, hR⟩
    refine ⟨R, trivial, fun v (hnorm : R ≤ ‖v‖) (hv : v ∈ D) => hR v hv hnorm⟩

namespace IsCoerciveAt

variable {K : Set X} {A : X → StrongDual ℝ X} {v₀ : X}

/-- The coercive limit `(A v - A v₀)(v - v₀) / ‖v‖ → +∞` along
`v ∈ K, ‖v‖ → ∞` packaged as the existence of a radius beyond which the
quotient stays above any prescribed threshold `M`. -/
lemma exists_radius_quotient_ge (h : IsCoerciveAt K A v₀) (M : ℝ) :
    ∃ R : ℝ, ∀ v ∈ K, R ≤ ‖v‖ → M ≤ (A v - A v₀) (v - v₀) / ‖v‖ := by
  have hev : ∀ᶠ v in coerciveFilter K,
      M ≤ (A v - A v₀) (v - v₀) / ‖v‖ :=
    h.tendsto.eventually_ge_atTop M
  exact (eventually_coerciveFilter_iff_exists_norm_bound _ _).1 hev

/-- **Uniform norm bound for solutions of the half-space VI.**

Let `K` be convex and `A` coercive on `K` at `v₀`. Every `u ∈ K`
satisfying `0 ≤ A v (v - u)` for all `v ∈ K` admits the uniform bound
`‖u‖ ≤ R(A, v₀)`. The radius depends only on the coercivity data and
`v₀`. -/
theorem exists_radius_for_midpoint_vi
    (h : IsCoerciveAt K A v₀) (hK : Convex ℝ K) :
    ∃ R : ℝ, ∀ u ∈ K, (∀ v ∈ K, 0 ≤ A v (v - u)) → ‖u‖ ≤ R := by
  -- Coercivity supplies a threshold `R₀` such that for every `v ∈ K`
  -- with `‖v‖ ≥ R₀`, the coercive quotient exceeds `‖A v₀‖ + 1`.
  obtain ⟨R₀, hR₀⟩ := h.exists_radius_quotient_ge (‖A v₀‖ + 1)
  -- The candidate radius. Take `2 * max(R₀, ‖A v₀‖ * ‖v₀‖) + ‖v₀‖`,
  -- guaranteed nonnegative by the explicit `max … 0` clamp.
  set M : ℝ := max (max R₀ (‖A v₀‖ * ‖v₀‖)) 0 with hM_def
  refine ⟨2 * M + ‖v₀‖, ?_⟩
  intro u huK hVI
  -- Midpoint between `u` and the base point. Convexity puts `m ∈ K`.
  set m : X := (1/2 : ℝ) • u + (1/2 : ℝ) • v₀ with hm_def
  have hm_mem : m ∈ K := by
    have h12 : (1 : ℝ) / 2 + 1 / 2 = 1 := by norm_num
    have h12nn : (0 : ℝ) ≤ 1 / 2 := by norm_num
    exact hK huK h.mem h12nn h12nn h12
  -- Test VI at `v = m`: `0 ≤ A m (m - u)`.
  have hVIm : 0 ≤ A m (m - u) := hVI m hm_mem
  -- Identity `m - u = -(m - v₀)` (both equal `(v₀ - u)/2`, with opposite
  -- signs to `(u - v₀)/2 = m - v₀`).
  have hid : m - u = -(m - v₀) := by
    change ((1/2 : ℝ) • u + (1/2 : ℝ) • v₀) - u
        = -(((1/2 : ℝ) • u + (1/2 : ℝ) • v₀) - v₀)
    module
  -- Identity `u = 2 • m - v₀` (real scalar).
  have hid_u : u = (2 : ℝ) • m - v₀ := by
    change u = (2 : ℝ) • ((1/2 : ℝ) • u + (1/2 : ℝ) • v₀) - v₀
    module
  -- Push the negation through `A m`: `A m (m - u) = - A m (m - v₀)`.
  have hAm : A m (m - u) = - A m (m - v₀) := by
    rw [hid]; simp
  -- Hence `A m (m - v₀) ≤ 0`.
  have hAm_neg : A m (m - v₀) ≤ 0 := by
    have := hVIm
    rw [hAm] at this
    linarith
  -- Bound `(A m - A v₀)(m - v₀) ≤ ‖A v₀‖ · ‖m - v₀‖`.
  have hpair : (A m - A v₀) (m - v₀) ≤ ‖A v₀‖ * ‖m - v₀‖ := by
    have hsplit : (A m - A v₀) (m - v₀) = A m (m - v₀) - A v₀ (m - v₀) := by
      simp [ContinuousLinearMap.sub_apply]
    have hop : |A v₀ (m - v₀)| ≤ ‖A v₀‖ * ‖m - v₀‖ := by
      have := (A v₀).le_opNorm (m - v₀)
      have habs : ‖A v₀ (m - v₀)‖ = |A v₀ (m - v₀)| := Real.norm_eq_abs _
      rw [habs] at this
      exact this
    have hop' : -(A v₀ (m - v₀)) ≤ ‖A v₀‖ * ‖m - v₀‖ := by
      have := abs_le.mp hop
      linarith [this.1]
    rw [hsplit]
    linarith
  -- We now split on whether `‖m‖` is small (`< R₀`) or large.
  -- The bound on `‖u‖` is the same in both branches since
  -- `M ≥ max(R₀, ‖A v₀‖ · ‖v₀‖) ≥ 0`.
  have hM_R₀ : R₀ ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
  have hM_prod : ‖A v₀‖ * ‖v₀‖ ≤ M :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hM_nonneg : 0 ≤ M := le_max_right _ _
  have hm_norm_le_M : ‖m‖ ≤ M := by
    by_cases hcase : R₀ ≤ ‖m‖
    · -- Large case: use coercivity directly to bound `‖m‖`.
      -- From `(A m - A v₀)(m - v₀) ≥ (‖A v₀‖ + 1) · ‖m‖` and the
      -- algebraic upper bound `≤ ‖A v₀‖ · (‖m‖ + ‖v₀‖)`, conclude
      -- `‖m‖ ≤ ‖A v₀‖ · ‖v₀‖`.
      have hquot := hR₀ m hm_mem hcase
      have hmnn : 0 ≤ ‖m‖ := norm_nonneg _
      have hAv0nn : 0 ≤ ‖A v₀‖ := norm_nonneg _
      -- Multiply the quotient inequality by `‖m‖ ≥ 0`.
      have hlhs : (‖A v₀‖ + 1) * ‖m‖ ≤ (A m - A v₀) (m - v₀) := by
        rcases lt_or_ge 0 ‖m‖ with hpos | hzero
        · rw [le_div_iff₀ hpos] at hquot
          linarith
        · -- `‖m‖ = 0` is impossible: the coercive quotient at `‖m‖ = 0`
          -- would force `‖A v₀‖ + 1 ≤ 0` (Lean's `x/0 = 0` convention),
          -- contradicting the non-negativity of `‖A v₀‖`.
          exfalso
          have hmz : ‖m‖ = 0 := le_antisymm hzero hmnn
          rw [hmz, div_zero] at hquot
          linarith
      have hrhs : (A m - A v₀) (m - v₀) ≤ ‖A v₀‖ * (‖m‖ + ‖v₀‖) := by
        have hnsub : ‖m - v₀‖ ≤ ‖m‖ + ‖v₀‖ := norm_sub_le m v₀
        have hmul : ‖A v₀‖ * ‖m - v₀‖ ≤ ‖A v₀‖ * (‖m‖ + ‖v₀‖) :=
          mul_le_mul_of_nonneg_left hnsub hAv0nn
        linarith
      have habs : (‖A v₀‖ + 1) * ‖m‖ ≤ ‖A v₀‖ * (‖m‖ + ‖v₀‖) :=
        le_trans hlhs hrhs
      have habs' : ‖m‖ ≤ ‖A v₀‖ * ‖v₀‖ := by
        have hexpand1 : (‖A v₀‖ + 1) * ‖m‖ = ‖A v₀‖ * ‖m‖ + ‖m‖ := by ring
        have hexpand2 : ‖A v₀‖ * (‖m‖ + ‖v₀‖) = ‖A v₀‖ * ‖m‖ + ‖A v₀‖ * ‖v₀‖ := by ring
        linarith
      exact le_trans habs' hM_prod
    · -- Small case: `‖m‖ < R₀ ≤ M`.
      have hlt : ‖m‖ < R₀ := lt_of_not_ge hcase
      exact le_trans hlt.le hM_R₀
  -- Finally, `‖u‖ = ‖2 • m - v₀‖ ≤ 2 ‖m‖ + ‖v₀‖ ≤ 2 M + ‖v₀‖`.
  have hu_norm : ‖u‖ ≤ 2 * ‖m‖ + ‖v₀‖ := by
    rw [hid_u]
    calc ‖(2 : ℝ) • m - v₀‖
        ≤ ‖(2 : ℝ) • m‖ + ‖v₀‖ := norm_sub_le _ _
      _ = 2 * ‖m‖ + ‖v₀‖ := by
            rw [norm_smul]; simp
  linarith

end IsCoerciveAt

/-- **Sanity-check `example`.**

The zero operator is coercive on the singleton `{v₀}` (vacuously), and
the half-space VI `0 ≤ 0 (v - u)` is satisfied trivially. The radius
lemma therefore produces a uniform bound for any `u ∈ {v₀}`, which can
only be `u = v₀` itself. -/
example (v₀ : X) :
    ∃ R : ℝ, ∀ u ∈ ({v₀} : Set X),
      (∀ v ∈ ({v₀} : Set X), 0 ≤ (0 : StrongDual ℝ X) (v - u)) →
        ‖u‖ ≤ R := by
  have hcoerc : IsCoerciveAt ({v₀} : Set X) (fun _ => (0 : StrongDual ℝ X)) v₀ :=
    isCoerciveAt_of_bounded_domain isBounded_singleton _ rfl
  have hconv : Convex ℝ ({v₀} : Set X) := convex_singleton v₀
  exact hcoerc.exists_radius_for_midpoint_vi hconv

end Monotone
end StationaryMFG
