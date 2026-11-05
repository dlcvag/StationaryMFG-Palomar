module

public import StationaryMFG.Basic
public import StationaryMFG.Monotone.Operator

@[expose] public section

/-!
# Hemicontinuous operators on Banach spaces — basic predicate

This file introduces the abstract notion of a **hemicontinuous operator**
`A : D(A) ⊂ X → X'` from a (reflexive) Banach space `X` to its continuous
dual `X' = StrongDual ℝ X`, with a convex domain `D(A) ⊂ X`.

This is item (c) of Definition `def:prelim` (label `defitem:hemicont`) in
Section `subs:monotone` of the paper:

> `A` is hemicontinuous if for all `u, v ∈ D(A)` and `w ∈ X`, the
> real-valued map `t ↦ ⟨A[(1 - t) u + t v], w⟩_{X', X}` is continuous on
> the interval `[0, 1]`.

See `Source/FGU-monotone_revised.tex` line 793.

## Convention

Following `StationaryMFG/Monotone/Operator.lean`, the dual `X'` is
`StrongDual ℝ X = X →L[ℝ] ℝ` and the duality pairing is plain function
application. The "test direction" `w` ranges over the predual `X`.

We do not bake convexity of `D` into the predicate (the convex combination
`(1 - t) u + t v` is meaningful for any pair `u, v` even when `D` is not
convex; the operator is simply evaluated wherever the segment lands).

## Main declarations

* `StationaryMFG.Monotone.IsHemicontinuous D A` — the predicate.
* `IsHemicontinuous.comp_segment_continuousOn` — restatement at fixed
  `u, v, w`.
* `isHemicontinuous_of_continuous` — operator-norm continuity implies
  hemicontinuity.
* `isHemicontinuous_zero` — the zero operator is hemicontinuous.
-/

noncomputable section

namespace StationaryMFG
namespace Monotone

open NormedSpace

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- An operator `A : X → X'` is **hemicontinuous on the set `D ⊂ X`** when
for every pair `u, v ∈ D` and every test direction `w ∈ X`, the real-valued
function
```
t ↦ ⟨A ((1 - t) • u + t • v), w⟩_{X', X}
```
is continuous on `[0, 1]`. With `X' = StrongDual ℝ X`, the pairing is plain
function application.

This is `defitem:hemicont` in `def:prelim` of the paper
(Section `subs:monotone`, line 793). -/
def IsHemicontinuous (D : Set X) (A : X → StrongDual ℝ X) : Prop :=
  ∀ ⦃u⦄, u ∈ D → ∀ ⦃v⦄, v ∈ D → ∀ w : X,
    ContinuousOn (fun t : ℝ => A ((1 - t) • u + t • v) w) (Set.Icc 0 1)

namespace IsHemicontinuous

variable {D : Set X} {A : X → StrongDual ℝ X}

/-- Restatement of hemicontinuity at a fixed pair `(u, v)` and test
direction `w`: the segment composition is continuous on `[0, 1]`. This is
the form used in the upgrade remark `rmk:hemicontinuous-upgrade`. -/
lemma comp_segment_continuousOn (h : IsHemicontinuous D A)
    {u : X} (hu : u ∈ D) {v : X} (hv : v ∈ D) (w : X) :
    ContinuousOn (fun t : ℝ => A ((1 - t) • u + t • v) w) (Set.Icc 0 1) :=
  h hu hv w

end IsHemicontinuous

/-- **Continuity in the operator norm implies hemicontinuity.**

If `A : X → StrongDual ℝ X` is continuous (with `StrongDual ℝ X` carrying
its usual operator-norm topology), then for every `u, v` the map
`t ↦ A ((1 - t) • u + t • v) w` is continuous on all of `ℝ`, hence
continuous on `[0, 1]`. The hypothesis `Continuous A` subsumes the special
cases of bounded-linear and Lipschitz operators that arise in the paper's
applications. -/
theorem isHemicontinuous_of_continuous {D : Set X} {A : X → StrongDual ℝ X}
    (hA : Continuous A) : IsHemicontinuous D A := by
  intro u _ v _ w
  -- Build continuity of `t ↦ A ((1 - t) • u + t • v) w` on all of ℝ.
  have hseg : Continuous (fun t : ℝ => (1 - t) • u + t • v) := by
    -- `(1 - t) • u` is continuous in `t`; so is `t • v`; their sum is too.
    refine Continuous.add ?_ ?_
    · exact ((continuous_const.sub continuous_id).smul continuous_const)
    · exact (continuous_id.smul continuous_const)
  have hAseg : Continuous (fun t : ℝ => A ((1 - t) • u + t • v)) :=
    hA.comp hseg
  -- Evaluation `φ ↦ φ w` is continuous on `StrongDual ℝ X`.
  have hEval : Continuous (fun φ : StrongDual ℝ X => φ w) :=
    (ContinuousLinearMap.apply ℝ ℝ w).continuous
  exact (hEval.comp hAseg).continuousOn

/-- **Sum of two hemicontinuous operators is hemicontinuous.**

If `A` and `B` are both hemicontinuous on `D`, then so is the pointwise sum
`fun v => A v + B v`. At fixed `u, v ∈ D` and test direction `w`, the
segment map of the sum is the sum of the two segment maps, each continuous
on `[0,1]`, hence continuous on `[0,1]`.

This is the abstract glue used by the regularised MFG operator
`A_ε^δ = A_0 + (ε-regularisation)` of `paper:eq:defAepsi` when bridging
`paper:lem:hemicont`: each summand is hemicontinuous, so the sum is. -/
theorem isHemicontinuous_add {D : Set X} {A B : X → StrongDual ℝ X}
    (hA : IsHemicontinuous D A) (hB : IsHemicontinuous D B) :
    IsHemicontinuous D (fun v => A v + B v) := by
  intro u hu v hv w
  have hAseg := hA hu hv w
  have hBseg := hB hu hv w
  have hsum := hAseg.add hBseg
  refine hsum.congr ?_
  intro t _
  simp [ContinuousLinearMap.add_apply]

/-- The zero operator is hemicontinuous on every domain: the segment map
`t ↦ ⟨0, w⟩ = 0` is constant, hence continuous. -/
theorem isHemicontinuous_zero (D : Set X) :
    IsHemicontinuous (X := X) D (fun _ => (0 : StrongDual ℝ X)) :=
  isHemicontinuous_of_continuous continuous_const

/-- Sanity-check `example`: the zero operator is hemicontinuous on
`Set.univ`. -/
example : IsHemicontinuous (X := X) (Set.univ) (fun _ => (0 : StrongDual ℝ X)) :=
  isHemicontinuous_zero _

/-- Sanity-check `example`: a bounded linear operator (viewed as a
constant-valued map into the dual at each point — here we use the simplest
such instance, the zero map) is hemicontinuous. The general "Lipschitz
implies hemicontinuous" statement promised by the task acceptance criterion
is recovered by `isHemicontinuous_of_continuous`, since Lipschitz functions
are continuous: see the next example. -/
example {A : X → StrongDual ℝ X} {K : NNReal} (hA : LipschitzWith K A) :
    IsHemicontinuous (X := X) Set.univ A :=
  isHemicontinuous_of_continuous hA.continuous

end Monotone
end StationaryMFG
