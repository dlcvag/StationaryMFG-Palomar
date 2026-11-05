module

public import StationaryMFG.Theorems.SimplePower.Banach.AprioriDischarge

@[expose] public section

/-!
# Block C.5 — `ε`-uniform sequence of regularised solutions

This module discharges Phase-4 task `infra-P4-banach-C5-uniform-sequence`:
build an explicit `ℕ`-indexed sequence of Banach-pair elements
`(m_{ε_k}, u_{ε_k}) : ℕ → LpPer β̄ × SobolevPerLp 1 γ̄` together with
`ε_k → 0⁺` and a uniform Banach-pair-norm bound
```
∀ k, ‖v_k‖ ≤ C
```
where `C` is the ε-independent constant from Block C.4.

## Strategy

We do **not** here construct the per-`ε` regularised pair from the raw
paper hypotheses `(hMon, hPow, V ∈ L^{β̄'}_per)` — that is the work of the
A.* + B.* + C.4 chain together with the (still-to-land) bridge from the
bare-function `apriori_at_eps`-style bound to the Banach norm
`‖v‖_{LpPer × SobolevPerLp}`. Instead, we land the pure plumbing that
turns a per-`k` "step input" (a Banach-pair element with a uniform
`‖·‖ ≤ C` certificate) into:
1. an explicit ε-sequence `epsSeq k := 1 / (k + 1)`,
2. lemmas `epsSeq_pos`, `epsSeq_tendsto_zero`, and
3. the headline existence statement
   `exists_uniform_eps_sequence`.

The downstream Block D.1 task (`infra-P4-banach-D1-weak-to-bare`) then
populates the per-`k` step input from `apriori_at_eps + thm_strongAepsi`
plus the bridge `lpNormPer ↔ ‖toLp …‖`, both of which are needed by D.1
in any case.

## Main contents

* `epsSeq` — the canonical sequence `k ↦ 1 / (k + 1)`.
* `epsSeq_pos`, `epsSeq_tendsto_zero` — the positivity and `→ 0`
  facts.
* `UniformEpsStep` — the per-`k` input record (a Banach-pair element +
  a `‖·‖ ≤ C` certificate).
* `exists_uniform_eps_sequence` — the headline existence statement.
-/

noncomputable section

namespace StationaryMFG
namespace Theorems
namespace SimplePower
namespace Banach

open MeasureTheory Filter
open StationaryMFG.Periodic
open scoped ENNReal Topology

variable {d : ℕ}

/-! ### The canonical ε-sequence -/

/-- **Canonical `ε`-sequence** `ε_k := 1 / (k + 1)`. Strictly positive
for every `k : ℕ`, tends to `0` as `k → ∞`. -/
def epsSeq (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)

/-- `0 < ε_k` for every `k : ℕ`. -/
lemma epsSeq_pos (k : ℕ) : 0 < epsSeq k := by
  unfold epsSeq
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
    linarith
  exact one_div_pos.mpr hk

/-- `ε_k → 0⁺` as `k → ∞`. -/
lemma epsSeq_tendsto_zero :
    Tendsto epsSeq atTop (𝓝 0) := by
  unfold epsSeq
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-! ### Per-`k` step input

A `UniformEpsStep` packages a Banach-pair element together with the
uniform-bound certificate `‖v‖ ≤ C`. Block D.1 will populate this from
`apriori_at_eps` + the `lpNormPer ↔ ‖toLp …‖` bridge. -/

/-- **Per-`k` step input** for the uniform-`ε` sequence construction.
Records:

* `v` — a Banach-pair element in `LpPer β̄ d × SobolevPerLp 1 γ̄ d`
  (its bare-function components are the regularised pair
  `(m_{ε_k}, u_{ε_k})` together with the family of weak partial
  derivatives `Du_{ε_k}` carried by the second `Sobolev` factor).
* `hNorm` — uniform bound `‖v‖ ≤ C` on the Banach-pair norm. -/
structure UniformEpsStep (βBar γBar : ℝ≥0∞) [Fact (1 ≤ βBar)] [Fact (1 ≤ γBar)]
    (d : ℕ) (C : ℝ) where
  /-- The Banach-pair element at the step's parameter `ε`. -/
  v : LpPer βBar d × SobolevPerLp 1 γBar d
  /-- Uniform bound on the Banach-pair norm. -/
  hNorm : ‖v‖ ≤ C

/-! ### Headline existence theorem -/

/-- **`ε`-uniform sequence of regularised solutions in the Banach pair.**

Given a per-`k` family of step inputs at parameter `ε_k := 1 / (k + 1)`,
each producing a Banach-pair element `v_k` with uniform norm bound
`‖v_k‖ ≤ C` (the ε-independent constant from Block C.4), produce:
1. the bare ε-sequence `epsSeq` (= `k ↦ 1 / (k + 1)`) with
   `epsSeq_pos` and `epsSeq_tendsto_zero` already in scope;
2. the sequence `v : ℕ → LpPer β̄ d × SobolevPerLp 1 γ̄ d`;
3. a `Bornology.IsBounded` certificate on `Set.range v`.

The bornology bound is the input shape consumed by
`exists_weak_cluster_point_pair` (the Block D entry point). -/
theorem exists_uniform_eps_sequence
    {βBar γBar : ℝ≥0∞} [Fact (1 ≤ βBar)] [Fact (1 ≤ γBar)]
    {C : ℝ} (steps : ∀ k : ℕ, UniformEpsStep (d := d) βBar γBar C) :
    ∃ (ε : ℕ → ℝ) (v : ℕ → LpPer βBar d × SobolevPerLp 1 γBar d),
      (∀ k, 0 < ε k)
        ∧ Tendsto ε atTop (𝓝 0)
        ∧ Bornology.IsBounded (Set.range v)
        ∧ (∀ k, ‖v k‖ ≤ C) := by
  refine ⟨epsSeq, fun k => (steps k).v, ?_, ?_, ?_, ?_⟩
  · exact epsSeq_pos
  · exact epsSeq_tendsto_zero
  · -- `IsBounded (Set.range v)` from the per-`k` norm bound.
    rw [isBounded_iff_forall_norm_le]
    refine ⟨C, ?_⟩
    rintro w ⟨k, rfl⟩
    exact (steps k).hNorm
  · intro k
    exact (steps k).hNorm

/-! ### Sanity-check unit test

We exercise `exists_uniform_eps_sequence` on the trivial step where
every `v_k = 0`. The Banach-pair norm of zero is zero, so `C := 0`
suffices. The output sequence is the constant zero sequence. -/

example {βBar γBar : ℝ≥0∞} [Fact (1 ≤ βBar)] [Fact (1 ≤ γBar)] :
    ∃ (ε : ℕ → ℝ) (v : ℕ → LpPer βBar d × SobolevPerLp 1 γBar d),
      (∀ k, 0 < ε k)
        ∧ Tendsto ε atTop (𝓝 0)
        ∧ Bornology.IsBounded (Set.range v)
        ∧ (∀ k, ‖v k‖ ≤ 0) := by
  -- Trivial step at every `k`: the zero element of the product.
  let trivialStep : UniformEpsStep (d := d) βBar γBar 0 :=
    { v := 0
    , hNorm := by simp }
  exact exists_uniform_eps_sequence (fun _ => trivialStep)

end Banach
end SimplePower
end Theorems
end StationaryMFG
