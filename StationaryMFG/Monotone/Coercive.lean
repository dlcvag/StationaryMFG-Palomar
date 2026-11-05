module

public import StationaryMFG.Basic
public import StationaryMFG.Monotone.Operator

@[expose] public section

/-!
# Coercive operators on Banach spaces — basic predicate

This file introduces the abstract notion of a **coercive operator**
`A : D(A) ⊂ X → X'` from a (reflexive) Banach space `X` to its continuous
dual `X' = StrongDual ℝ X`, with respect to a base point `v0 ∈ D(A)`.

This is item (b) of Definition `def:prelim` (label `defitem:coercive`) in
Section `subs:monotone` of the paper:

> `A` is coercive if there exists `v0 ∈ D(A)` such that
> `lim_{v ∈ D(A), ‖v‖_X → ∞} ⟨A v - A v0, v - v0⟩_{X', X} / ‖v‖_X = +∞`.

See `Source/FGU-monotone_revised.tex` line 790.

## Filter formulation

The paper writes `lim_{v ∈ D(A), ‖v‖_X → ∞}`, a directed limit along the
*restriction to `D(A)` of the cobounded filter on `X`*. In Lean we encode
this as
```
Filter.Tendsto (fun v => (A v - A v0) (v - v0) / ‖v‖)
               (Filter.cobounded X ⊓ Filter.principal D)
               Filter.atTop
```
where `Filter.cobounded X` is the filter of complements of bounded sets;
on a normed space this is the filter "`‖v‖ → ∞`"
(see `Mathlib.Analysis.Normed.Group.Bounded`,
`tendsto_norm_atTop_iff_cobounded`).

We follow the paper verbatim and divide by `‖v‖`, not `‖v - v0‖` — the two
denominators are asymptotically equivalent (their ratio tends to `1`), but
matching the source keeps citations of `prop:coercAepsi` direct.

## Convention

As in `StationaryMFG/Monotone/Operator.lean`, the dual `X'` is
`StrongDual ℝ X = X →L[ℝ] ℝ`, and the duality pairing is plain function
application. Reflexivity of `X` is *not* needed to *state* coercivity, so
we keep it out of the definition's hypotheses.

## Main declarations

* `StationaryMFG.Monotone.IsCoerciveAt D A v0` — coercivity of `A` on `D`
  with base point `v0`.
* `StationaryMFG.Monotone.IsCoercive D A` — existence of a base point at
  which `A` is coercive.
* `IsCoerciveAt.mem`, `IsCoerciveAt.tendsto` — projection lemmas.
* `isCoerciveAt_mono` — domination implies coercivity is preserved.
* `isCoerciveAt_of_bounded_domain` — coercivity is automatic on a bounded
  domain (the limit filter is `⊥`).
-/

noncomputable section

namespace StationaryMFG
namespace Monotone

open NormedSpace Filter Bornology

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The "directed limit on `D(A)` as `‖v‖ → ∞`" filter: the cobounded filter
on `X` restricted to the subset `D ⊂ X`. We package this so the coercivity
predicate has a clean filter argument. -/
def coerciveFilter (D : Set X) : Filter X :=
  Bornology.cobounded X ⊓ Filter.principal D

/-- An operator `A : X → X'` is **coercive on the set `D ⊂ X` at the base
point `v0`** if `v0 ∈ D` and the real-valued map
`v ↦ ⟨A v - A v0, v - v0⟩_{X',X} / ‖v‖`
tends to `+∞` as `v` ranges through `D` with `‖v‖ → ∞`.

This is `defitem:coercive` in `def:prelim` of the paper
(Section `subs:monotone`, line 790). With `X' = StrongDual ℝ X` the
pairing is plain function application. -/
def IsCoerciveAt (D : Set X) (A : X → StrongDual ℝ X) (v0 : X) : Prop :=
  v0 ∈ D ∧
    Tendsto (fun v : X => (A v - A v0) (v - v0) / ‖v‖)
      (coerciveFilter D) atTop

/-- An operator `A : X → X'` is **coercive on `D`** if there exists some
base point `v0 ∈ D` at which it is coercive in the sense of
`IsCoerciveAt`. This matches the paper's existential phrasing of
`defitem:coercive`. -/
def IsCoercive (D : Set X) (A : X → StrongDual ℝ X) : Prop :=
  ∃ v0 : X, IsCoerciveAt D A v0

namespace IsCoerciveAt

variable {D : Set X} {A : X → StrongDual ℝ X} {v0 : X}

/-- The base point `v0` of a coercive operator lies in its domain `D`. -/
lemma mem (h : IsCoerciveAt D A v0) : v0 ∈ D := h.1

/-- Coercivity unfolds to the asserted `Tendsto` statement on the
restricted cobounded filter. -/
lemma tendsto (h : IsCoerciveAt D A v0) :
    Tendsto (fun v : X => (A v - A v0) (v - v0) / ‖v‖)
      (coerciveFilter D) atTop := h.2

end IsCoerciveAt

/-- **Domination implies coercivity is preserved.**

If `A` is coercive at `v0` on `D`, and `B : X → X'` satisfies
`(A v - A v0) (v - v0) ≤ (B v - B v0) (v - v0)` for every `v ∈ D`, then `B`
is coercive at the same `v0`. -/
theorem isCoerciveAt_mono {D : Set X} {A B : X → StrongDual ℝ X} {v0 : X}
    (hA : IsCoerciveAt D A v0)
    (hAB : ∀ v ∈ D, (A v - A v0) (v - v0) ≤ (B v - B v0) (v - v0)) :
    IsCoerciveAt D B v0 := by
  refine ⟨hA.mem, ?_⟩
  -- We squeeze using `tendsto_atTop_mono'`. Eventually on the
  -- restricted cobounded filter we have `v ∈ D` (from `principal D`),
  -- and division by `‖v‖ ≥ 0` preserves the pointwise inequality.
  refine tendsto_atTop_mono' _ ?_ hA.tendsto
  have hD : ∀ᶠ v in coerciveFilter D, v ∈ D :=
    (eventually_inf_principal.mpr) (Eventually.of_forall (fun _ hv => hv))
  filter_upwards [hD] with v hv
  exact div_le_div_of_nonneg_right (hAB v hv) (norm_nonneg _)

/-- **Coercive + monotone is coercive.**

If `A` is coercive at `v0` on `D` and `B` is monotone on `D` (with
`v0 ∈ D`), then the pointwise sum `fun v => A v + B v` is coercive at the
same base point `v0`. The monotone summand contributes a nonnegative term
`(B v - B v0)(v - v0) ≥ 0` to the difference pairing, so the sum dominates
`A`'s difference pairing; `isCoerciveAt_mono` then concludes.

This is the abstract form of the paper's coercivity argument
(`paper:prop:coercAepsi`): in `A_ε^δ = A_0 + (ε-regularisation)`, the
ε-regularisation term is coercive for `ε > 0`, while the MFG part `A_0` is
monotone (`paper:lem:H.delta.monotone`); hence `A_ε^δ` is coercive. -/
theorem isCoerciveAt_add_of_monotone {D : Set X} {A B : X → StrongDual ℝ X}
    {v0 : X} (hA : IsCoerciveAt D A v0) (hB : IsMonotone D B) :
    IsCoerciveAt D (fun v => A v + B v) v0 := by
  refine isCoerciveAt_mono hA ?_
  intro v hv
  -- The summand difference pairing splits; the `B` part is `≥ 0`.
  have hBterm : 0 ≤ (B v - B v0) (v - v0) := hB hv hA.mem
  have hsplit :
      ((fun v => A v + B v) v - (fun v => A v + B v) v0) (v - v0)
        = (A v - A v0) (v - v0) + (B v - B v0) (v - v0) := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply]
    ring
  rw [hsplit]
  linarith

set_option linter.unusedSectionVars false in
/-- A bounded domain trivialises the coercivity filter: `coerciveFilter D = ⊥`
when `D` is bounded. -/
lemma coerciveFilter_eq_bot_of_isBounded {D : Set X} (hD : IsBounded D) :
    coerciveFilter D = ⊥ := by
  rw [coerciveFilter, inf_principal_eq_bot]
  -- `isBounded_def : IsBounded s ↔ sᶜ ∈ cobounded α` matches the goal exactly.
  exact isBounded_def.mp hD

/-- If `D` is bounded, then any operator `A` is coercive at any base
point `v0 ∈ D`: the limit filter degenerates to `⊥`, on which every
`Tendsto` statement is vacuous. -/
theorem isCoerciveAt_of_bounded_domain {D : Set X} (hD : IsBounded D)
    (A : X → StrongDual ℝ X) {v0 : X} (hv0 : v0 ∈ D) :
    IsCoerciveAt D A v0 := by
  refine ⟨hv0, ?_⟩
  rw [coerciveFilter_eq_bot_of_isBounded hD]
  exact tendsto_bot

/-- **Sanity-check `example`** (vacuous coercivity on a singleton).

The zero operator is coercive at any base point of a singleton domain,
since the singleton is bounded and the coercivity filter degenerates to
`⊥`. -/
example (v0 : X) :
    IsCoerciveAt ({v0} : Set X) (fun _ => (0 : StrongDual ℝ X)) v0 :=
  isCoerciveAt_of_bounded_domain isBounded_singleton _ rfl

/-- **Sanity-check `example`** (existence form on a bounded domain).

Any operator is coercive on a bounded nonempty domain. -/
example (A : X → StrongDual ℝ X) (v0 : X) :
    IsCoercive ({v0} : Set X) A :=
  ⟨v0, isCoerciveAt_of_bounded_domain isBounded_singleton _ rfl⟩

end Monotone
end StationaryMFG
