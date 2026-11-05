module

public import StationaryMFG.Basic
public import StationaryMFG.Monotone.Operator
public import StationaryMFG.Monotone.Hemicontinuous
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.Order.DenselyOrdered

@[expose] public section

/-!
# Hemicontinuous upgrade — weak VI implies strong VI

This file formalises Remark `rmk:hemicontinuous-upgrade` of the paper
(`Source/FGU-monotone_revised.tex`, line 832).

## Paper restatement

Let `K ⊂ X` be a convex set and let `A : X → X'` be hemicontinuous on `K`
(predicate `IsHemicontinuous K A` from
`StationaryMFG/Monotone/Hemicontinuous.lean`). Suppose `u ∈ K` satisfies
the **weak** variational inequality
```
∀ v ∈ K,  ⟨A v, v - u⟩_{X', X} ≥ 0.
```
Then `u` also satisfies the **strong** variational inequality
```
∀ v ∈ K,  ⟨A u, v - u⟩_{X', X} ≥ 0.
```

## Proof strategy (Minty-style trick)

Fix `v ∈ K` and set `seg t := (1 - t) • u + t • v = u + t • (v - u)`.

* By convexity of `K`, `seg t ∈ K` for every `t ∈ [0, 1]`.
* Apply the weak VI at the point `seg t`. Using
  `seg t - u = t • (v - u)` and the linearity of `A (seg t)` we obtain
  ```
  0 ≤ A (seg t) (seg t - u) = t * A (seg t) (v - u).
  ```
* For `0 < t ≤ 1` we may divide by `t` to get
  `0 ≤ A (seg t) (v - u)`.
* Send `t → 0⁺`. Hemicontinuity gives `ContinuousOn` on `Icc 0 1` of the
  map `t ↦ A (seg t) (v - u)`, which restricts to a `ContinuousWithinAt`
  at `0` with respect to `Set.Ioc 0 1 ⊆ Set.Ioi 0 ⊆ Set.Icc 0 1`. The
  value at `0` is `A u (v - u)`, and the limit of a non-negative function
  is non-negative.

## Independence note

This remark is logically *independent* of the Browder–Minty existence
theorem `paper:thm:monotone.abstract-weak`: we take the weak VI as a
hypothesis. The lemma is therefore usable now even though the existence
theorem itself is still in progress.
-/

noncomputable section

namespace StationaryMFG
namespace Monotone

open NormedSpace Set Filter Topology

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

section UpgradeHelpers

/-- Algebraic identity used inside `hemicont_upgrade`:
`((1 - t) • u + t • v) - u = t • (v - u)`. -/
private lemma seg_sub_self (u v : X) (t : ℝ) :
    ((1 - t) • u + t • v) - u = t • (v - u) := by
  -- Expand both sides as linear combinations of `u` and `v`.
  match_scalars <;> ring

end UpgradeHelpers

/-- **Hemicontinuous upgrade (Remark `rmk:hemicontinuous-upgrade`).**

Let `K ⊆ X` be convex and `A : X → X'` hemicontinuous on `K`. If `u ∈ K`
satisfies the *weak* variational inequality
`∀ v ∈ K, 0 ≤ A v (v - u)`, then `u` satisfies the *strong* variational
inequality `∀ v ∈ K, 0 ≤ A u (v - u)`.

This is the Minty-trick `t → 0⁺` step inside the proof of the abstract
existence result; it is split off as a stand-alone lemma so that it can
be used (and proved) independently of the existence theorem itself. -/
theorem hemicont_upgrade
    {K : Set X} (hKconv : Convex ℝ K)
    {A : X → StrongDual ℝ X} (hAhc : IsHemicontinuous K A)
    {u : X} (hu : u ∈ K)
    (hweak : ∀ ⦃v⦄, v ∈ K → 0 ≤ A v (v - u)) :
    ∀ ⦃v⦄, v ∈ K → 0 ≤ A u (v - u) := by
  intro v hv
  -- Segment endpoint and the parametrised path through `u` toward `v`.
  set seg : ℝ → X := fun t => (1 - t) • u + t • v with hseg_def
  -- For each `t ∈ Icc 0 1`, `seg t ∈ K` by convexity.
  have hseg_mem : ∀ ⦃t : ℝ⦄, t ∈ Icc (0 : ℝ) 1 → seg t ∈ K := by
    intro t ht
    -- Rewrite `seg t = u + t • (v - u)` to apply `Convex.add_smul_sub_mem`.
    have hrewrite : seg t = u + t • (v - u) := by
      simp only [hseg_def]
      match_scalars <;> ring
    rw [hrewrite]
    exact hKconv.add_smul_sub_mem hu hv ht
  -- Define the scalar path `g t := A (seg t) (v - u)`.
  set g : ℝ → ℝ := fun t => A (seg t) (v - u) with hg_def
  -- Step 1. For every `t ∈ Ioc 0 1`, `0 ≤ g t`.
  have hg_pos : ∀ ⦃t : ℝ⦄, t ∈ Ioc (0 : ℝ) 1 → 0 ≤ g t := by
    intro t ht
    rcases ht with ⟨ht_pos, ht_le⟩
    have ht_mem : t ∈ Icc (0 : ℝ) 1 := ⟨ht_pos.le, ht_le⟩
    -- Apply the weak VI at `seg t ∈ K`.
    have hwk : 0 ≤ A (seg t) ((seg t) - u) := hweak (hseg_mem ht_mem)
    -- Rewrite the right-hand side using `seg t - u = t • (v - u)`.
    have hsub : (seg t) - u = t • (v - u) := seg_sub_self u v t
    have hsmul : A (seg t) ((seg t) - u) = t * g t := by
      rw [hsub, ContinuousLinearMap.map_smul, smul_eq_mul]
    rw [hsmul] at hwk
    -- Divide by `t > 0`.
    exact (mul_nonneg_iff_of_pos_left ht_pos).1 hwk
  -- Step 2. The map `g` is continuous on `[0, 1]` (hemicontinuity).
  have hg_cont : ContinuousOn g (Icc (0 : ℝ) 1) := by
    -- This is hemicontinuity at `(u, v)` in the test direction `v - u`.
    have := hAhc hu hv (v - u)
    -- Match the lambda: `g t = A ((1 - t) • u + t • v) (v - u)` by definition.
    simpa [hg_def, hseg_def] using this
  -- Step 3. The value at `0` is `A u (v - u)`.
  have hg_zero : g 0 = A u (v - u) := by
    simp [hg_def, hseg_def]
  -- Step 4. Take the limit `t → 0⁺` along `Ioc 0 1`. The filter
  -- `𝓝[Ioc 0 1] 0` is non-trivial because `(0, 1]` accumulates at `0`.
  have h_subset : Ioc (0 : ℝ) 1 ⊆ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self
  have hcwa : ContinuousWithinAt g (Ioc (0 : ℝ) 1) 0 := by
    have hcwa_Icc : ContinuousWithinAt g (Icc (0 : ℝ) 1) 0 :=
      hg_cont 0 ⟨le_rfl, by norm_num⟩
    exact hcwa_Icc.mono h_subset
  -- Non-emptiness / `NeBot` of `𝓝[Ioc 0 1] 0`.
  have hNeBot : (𝓝[Ioc (0 : ℝ) 1] 0).NeBot :=
    left_nhdsWithin_Ioc_neBot (by norm_num : (0 : ℝ) < 1)
  -- Step 5. Pass the inequality `0 ≤ g t` to the limit.
  have htendsto : Tendsto g (𝓝[Ioc (0 : ℝ) 1] 0) (𝓝 (g 0)) := hcwa
  have : 0 ≤ g 0 := by
    refine ge_of_tendsto htendsto ?_
    exact Filter.eventually_of_mem self_mem_nhdsWithin (fun t ht => hg_pos ht)
  -- Conclude.
  rw [hg_zero] at this
  exact this

/-- Sanity-check `example`: the zero operator trivially upgrades on
`Set.univ` (every weak VI for the zero operator gives `0 ≥ 0`, and so
does the strong one). -/
example {u : X} :
    ∀ v : X, (0 : ℝ) ≤ (fun _ : X => (0 : StrongDual ℝ X)) u (v - u) := by
  intro v
  simp

/-- Sanity-check `example`: the upgrade theorem applied to the zero
operator on the whole space gives the trivial conclusion `0 ≤ 0`. -/
example {u : X} (hu : u ∈ (Set.univ : Set X)) :
    ∀ ⦃v : X⦄, v ∈ (Set.univ : Set X) →
      (0 : ℝ) ≤ (fun _ : X => (0 : StrongDual ℝ X)) u (v - u) :=
  hemicont_upgrade (K := (Set.univ : Set X))
    convex_univ
    (isHemicontinuous_zero _)
    hu
    (by intro v _; simp)

end Monotone
end StationaryMFG
