module

public import StationaryMFG.Basic

@[expose] public section

/-!
# Monotone operators on Banach spaces — basic predicate

This file introduces the abstract notion of a **monotone operator**
`A : D(A) ⊂ X → X'` from a (reflexive) Banach space `X` to its continuous
dual `X' = StrongDual ℝ X`, with a convex domain `D(A) ⊂ X`.

This is item (a) of Definition `def:prelim` (label `defitem:monotone`) in
Section `subs:monotone` of the paper:

> `A` is monotone if for all `v₁, v₂ ∈ D(A)`,
> `⟨A[v₁] - A[v₂], v₁ - v₂⟩_{X', X} ≥ 0`.

See `Source/FGU-monotone_revised.tex` line 788.

The full notion of "monotone operator" used by the paper additionally
involves coercivity (`defitem:coercive`) and hemicontinuity
(`defitem:hemicont`); those land in dedicated follow-up tasks. The
existence theorem `thm:monotone.abstract-weak` consumes all three
predicates together.

## Convention

We follow `StationaryMFG/Periodic/Reflexive.lean` and identify `X'` with
`StrongDual ℝ X = X →L[ℝ] ℝ`. The duality pairing is then plain function
application:
```
⟨φ, x⟩_{X',X}  ≡  φ x.
```
Reflexivity of `X` is *not* needed to *state* monotonicity, so we keep it
out of the definition's hypotheses; the existence-theorem statements that
require it will impose `IsReflexiveNormedSpace X` separately.

## Main declarations

* `StationaryMFG.Monotone.IsMonotone D A` — the predicate.
* `IsMonotone.swap_pairing` — symmetry under exchanging `v₁` and `v₂`.
* `isMonotone_zero` — the zero operator is monotone on any domain.
-/

noncomputable section

namespace StationaryMFG
namespace Monotone

open NormedSpace

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- An operator `A : X → X'` is **monotone on the set `D ⊂ X`** when
`⟨A v₁ - A v₂, v₁ - v₂⟩_{X', X} ≥ 0` for every pair of points
`v₁, v₂ ∈ D`. With `X' = StrongDual ℝ X`, the pairing is plain function
application.

This is `defitem:monotone` in `def:prelim` of the paper
(Section `subs:monotone`, line 788).

The predicate makes sense for an arbitrary set `D`; the paper additionally
assumes `D` is convex when it appears in the existence theorem. We do not
bake convexity in here, so the predicate composes cleanly with whatever
hypothesis the caller wants. -/
def IsMonotone (D : Set X) (A : X → StrongDual ℝ X) : Prop :=
  ∀ ⦃v₁⦄, v₁ ∈ D → ∀ ⦃v₂⦄, v₂ ∈ D → 0 ≤ (A v₁ - A v₂) (v₁ - v₂)

namespace IsMonotone

variable {D : Set X} {A : X → StrongDual ℝ X}

/-- The duality pairing in the definition is symmetric in `(v₁, v₂)`:
`⟨A v₁ - A v₂, v₁ - v₂⟩ = ⟨A v₂ - A v₁, v₂ - v₁⟩`. -/
lemma pairing_swap (v₁ v₂ : X) :
    (A v₁ - A v₂) (v₁ - v₂) = (A v₂ - A v₁) (v₂ - v₁) := by
  -- Expand both sides via `ContinuousLinearMap.sub_apply` and
  -- `ContinuousLinearMap.map_sub`; the two equal real expressions then
  -- match by `ring`.
  simp only [ContinuousLinearMap.sub_apply, map_sub]
  ring

/-- Equivalent form of monotonicity obtained by swapping the two arguments
of the pairing. -/
lemma swap_pairing (h : IsMonotone D A) :
    ∀ ⦃v₁⦄, v₁ ∈ D → ∀ ⦃v₂⦄, v₂ ∈ D → 0 ≤ (A v₂ - A v₁) (v₂ - v₁) := by
  intro v₁ hv₁ v₂ hv₂
  have := h hv₁ hv₂
  rwa [pairing_swap] at this

/-- Symmetric reformulation: monotonicity holds iff the swapped form
holds. -/
lemma iff_swap_pairing :
    IsMonotone D A ↔
      ∀ ⦃v₁⦄, v₁ ∈ D → ∀ ⦃v₂⦄, v₂ ∈ D → 0 ≤ (A v₂ - A v₁) (v₂ - v₁) := by
  refine ⟨swap_pairing, ?_⟩
  intro h v₁ hv₁ v₂ hv₂
  -- Rewrite the original pairing into its swapped form using `pairing_swap`,
  -- then apply the swapped hypothesis with arguments in matching order.
  rw [pairing_swap]
  exact h hv₁ hv₂

/-- The pairing of any operator with itself on the diagonal vanishes:
`⟨A v - A v, v - v⟩ = 0`. -/
lemma pairing_self (v : X) : (A v - A v) (v - v) = 0 := by
  simp

end IsMonotone

/-- **Sum of two monotone operators is monotone.**

If `A` and `B` are both monotone on `D`, then the pointwise sum
`fun v => A v + B v : X → StrongDual ℝ X` is monotone on `D`. The
difference pairing of the sum is the sum of the two (nonnegative)
difference pairings.

This is the abstract glue used by the regularised MFG operator
`A_ε^δ = A_0 + (ε-regularisation)` of `paper:eq:defAepsi`: both summands are
monotone (the MFG part by `paper:lem:H.delta.monotone`, the ε-part as the
Gâteaux derivative of a convex functional), so the sum is monotone. -/
theorem isMonotone_add {D : Set X} {A B : X → StrongDual ℝ X}
    (hA : IsMonotone D A) (hB : IsMonotone D B) :
    IsMonotone D (fun v => A v + B v) := by
  intro v₁ hv₁ v₂ hv₂
  have hAterm : 0 ≤ (A v₁ - A v₂) (v₁ - v₂) := hA hv₁ hv₂
  have hBterm : 0 ≤ (B v₁ - B v₂) (v₁ - v₂) := hB hv₁ hv₂
  have hsplit :
      ((fun v => A v + B v) v₁ - (fun v => A v + B v) v₂) (v₁ - v₂)
        = (A v₁ - A v₂) (v₁ - v₂) + (B v₁ - B v₂) (v₁ - v₂) := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply]
    ring
  rw [hsplit]
  exact add_nonneg hAterm hBterm

/-- The zero operator is monotone on every domain. The pairing
`⟨0 - 0, v₁ - v₂⟩ = 0 ≥ 0`. -/
theorem isMonotone_zero (D : Set X) :
    IsMonotone (X := X) D (fun _ => (0 : StrongDual ℝ X)) := by
  intro v₁ _ v₂ _
  simp

/-- Sanity-check `example`: the zero operator is monotone on `Set.univ`. -/
example : IsMonotone (X := X) (Set.univ) (fun _ => (0 : StrongDual ℝ X)) :=
  isMonotone_zero _

/-- Sanity-check `example`: the zero operator is monotone on the empty
domain (vacuously). -/
example : IsMonotone (X := X) (∅ : Set X) (fun _ => (0 : StrongDual ℝ X)) :=
  isMonotone_zero _

end Monotone
end StationaryMFG
