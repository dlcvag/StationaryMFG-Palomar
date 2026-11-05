module

public import StationaryMFG.Basic
public import StationaryMFG.Monotone.Operator

@[expose] public section

/-!
# Finite-dimensional convex-hull variational inequality — typeclass shell

This module introduces the typeclass `FiniteConvexHullWeakVI X` packaging
the finite-dimensional **Hartman–Stampacchia / Debrunner–Flor / Ky Fan**
variational inequality on a convex hull of finitely many points: for any
monotone operator `A : X → StrongDual ℝ X` defined on
`convexHull ℝ (F : Set X)` for some nonempty `F : Finset X`, there exists
`u ∈ convexHull ℝ F` satisfying

```
∀ v ∈ convexHull ℝ F, 0 ≤ A v (v - u).
```

This is **pure plumbing**: no proofs, no axioms. Downstream consumers in
the proof of the abstract-weak existence theorem
`monotone_abstract_weak` (Phase 3, Section `subs:monotone` of the paper)
take this typeclass as a hypothesis. The actual instance — once the
upstream Mathlib gap (Brouwer fixed-point / KKM / Debrunner–Flor) is
filled in — will be produced in a separate Stage-B task
(`infra:P3-monotone-finiteVI-sion`) via Sion's minimax.

See `docs/MONOTONE_PLAN.md` lines 53–64 for the design rationale, and
`docs/PHASES.md` Phase 3, Stage A bullet
`infra:P3-monotone-finiteVI-class`.

## Main declarations

* `StationaryMFG.Monotone.FiniteConvexHullWeakVI X` — the typeclass.
-/

noncomputable section

namespace StationaryMFG
namespace Monotone

open NormedSpace

/-- **Finite-dimensional convex-hull variational inequality** packaged as
a typeclass on a normed space `X` over `ℝ`.

For every nonempty `F : Finset X` and every operator
`A : X → StrongDual ℝ X` that is monotone on the convex hull of `F`, this
class asserts the existence of a point `u ∈ convexHull ℝ F` satisfying

```
∀ v ∈ convexHull ℝ F, 0 ≤ A v (v - u).
```

This is the finite-dimensional VI conclusion entering the proof of the
abstract-weak existence theorem `thm:monotone.abstract-weak` (paper
Section `subs:monotone`). It is the only ingredient missing from current
Mathlib — Brouwer fixed-point / KKM / Debrunner–Flor under any obvious
name — so we expose it here as a typeclass; a downstream task supplies
the instance.

Because the proof of `monotone_abstract_weak` uses the unknown solution
`u` to form midpoints with arbitrary points of the hull, the conclusion
must hold **for every `v` in the hull**, not just for the finite list of
generators of `F`. -/
class FiniteConvexHullWeakVI
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop where
  /-- The finite-dimensional convex-hull VI: for every nonempty
  `F : Finset X` and every operator `A : X → StrongDual ℝ X` monotone on
  `convexHull ℝ (F : Set X)`, there exists `u ∈ convexHull ℝ F` such that
  `0 ≤ A v (v - u)` for all `v ∈ convexHull ℝ F`. -/
  exists_vi :
    ∀ {A : X → StrongDual ℝ X} (F : Finset X),
      F.Nonempty →
      IsMonotone (convexHull ℝ (F : Set X)) A →
      ∃ u ∈ convexHull ℝ (F : Set X),
        ∀ v ∈ convexHull ℝ (F : Set X),
          0 ≤ A v (v - u)

/-- Sanity-check `#check`: the typeclass field is well-formed and visible
to elaboration in any normed real space `X`. -/
example (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteConvexHullWeakVI X] (F : Finset X) (hF : F.Nonempty)
    (A : X → StrongDual ℝ X)
    (hA : IsMonotone (convexHull ℝ (F : Set X)) A) :
    ∃ u ∈ convexHull ℝ (F : Set X),
      ∀ v ∈ convexHull ℝ (F : Set X), 0 ≤ A v (v - u) :=
  FiniteConvexHullWeakVI.exists_vi F hF hA

end Monotone
end StationaryMFG
