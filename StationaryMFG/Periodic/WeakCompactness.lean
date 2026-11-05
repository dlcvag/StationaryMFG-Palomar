module

public import StationaryMFG.Periodic.Reflexive
public import StationaryMFG.Monotone.WeakTopology
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.Normed.Module.WeakDual

@[expose] public section

/-!
# Sequential weak compactness of bounded sets in a reflexive normed space

This file proves the **sequential Banach–Alaoglu / Eberlein–Smulian-style**
statement consumed by the existence theory in Phase 4: every bounded sequence
in a reflexive real normed space whose strong dual is separable has a weakly
convergent subsequence.

## Why the separability hypothesis

Mathlib's only sequential weak-* compactness statement
(`WeakDual.isSeqCompact_closedBall`) requires the normed space whose dual is
being topologised to be separable. For a reflexive `X`, the relevant predual
is `StrongDual ℝ X`, so the hypothesis we carry is
`[SeparableSpace (StrongDual ℝ X)]`.

The full Eberlein–Smulian theorem (no separability needed) is not yet in
Mathlib; landing it here is parked as a follow-up. The separable form already
covers every concrete instance the paper uses (the product space
`L^β̄_per × W^{1,γ̄}_per`, separable as a finite product of separable
`L^p`-on-finite-measure factors).

## Main result

* `weakSeqCompact_of_bounded_reflexive` — every bounded sequence in a
  reflexive real normed space with separable strong dual has a subsequence
  converging in `WeakSpace ℝ X`.

## Reference

The proof transports the sequence into the weak-* bidual via
`NormedSpace.inclusionInDoubleDualWeak`, applies sequential Banach–Alaoglu
there, and pulls the limit back through the topological embedding (using
reflexivity to ensure the limit is in the range of the embedding).
-/

noncomputable section

namespace StationaryMFG
namespace Periodic

open MeasureTheory NormedSpace
open Bornology Filter Topology Metric
open StationaryMFG.Periodic (IsReflexiveNormedSpace)
open StationaryMFG.Monotone (inclusionInDoubleDualWeak_surjective_of_reflexive)

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ## Bound transfer through `inclusionInDoubleDualLi` -/

/-- A norm bound `‖x‖ ≤ R` transfers to a norm bound on the
double-dual image in `StrongDual ℝ (StrongDual ℝ X)`. -/
lemma norm_inclusionInDoubleDual_le {x : X} {R : ℝ} (hx : ‖x‖ ≤ R) :
    ‖NormedSpace.inclusionInDoubleDual ℝ X x‖ ≤ R := by
  -- `inclusionInDoubleDualLi` is an isometry, so `‖inclusion x‖ = ‖x‖`.
  have hnorm : ‖NormedSpace.inclusionInDoubleDual ℝ X x‖ = ‖x‖ :=
    (NormedSpace.inclusionInDoubleDualLi (𝕜 := ℝ) (E := X)).norm_map x
  rw [hnorm]
  exact hx

/-! ## Main theorem -/

/-- **Sequential weak compactness of bounded sets in a reflexive real normed
space with separable strong dual.**

Every norm-bounded sequence `x_n : ℕ → X` admits a strictly increasing
subsequence whose images under `toWeakSpace ℝ X` converge in the weak
topology of `X`.

The hypothesis `IsReflexiveNormedSpace X` is the project-local predicate
(surjectivity of the canonical inclusion `X → StrongDual ℝ (StrongDual ℝ X)`).
The typeclass `[SeparableSpace (StrongDual ℝ X)]` is required to use the
sequential Banach–Alaoglu theorem in the bidual.

Adapted from the strategy in Mathlib's
`NormedSpace.isCompact_closure_of_isBounded` (which proves the *non-sequential*
Banach–Alaoglu transfer): we replace the compactness step with sequential
Banach–Alaoglu (`WeakDual.isSeqCompact_closedBall`). -/
theorem weakSeqCompact_of_bounded_reflexive
    [TopologicalSpace.SeparableSpace (StrongDual ℝ X)]
    (hX : IsReflexiveNormedSpace X)
    (x_n : ℕ → X) (hb : IsBounded (Set.range x_n)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ x : WeakSpace ℝ X,
      Tendsto (fun n => (toWeakSpace ℝ X) (x_n (φ n))) atTop (𝓝 x) := by
  -- Step 1: Extract a uniform norm bound `R` on the sequence.
  obtain ⟨R, hR⟩ : ∃ R, ∀ n, ‖x_n n‖ ≤ R := by
    rcases (Metric.isBounded_range_iff).1 hb with ⟨C, hC⟩
    -- `dist (x_n m) (x_n 0) ≤ C` for all m, hence `‖x_n m‖ ≤ ‖x_n 0‖ + C`.
    refine ⟨‖x_n 0‖ + C, fun n => ?_⟩
    have h1 : ‖x_n n - x_n 0‖ ≤ C := by
      have := hC n 0
      simpa [dist_eq_norm] using this
    have h2 : ‖x_n n‖ ≤ ‖x_n 0‖ + ‖x_n n - x_n 0‖ := by
      have := norm_add_le (x_n 0) (x_n n - x_n 0)
      simpa using this
    linarith
  -- Step 2: Define the weak-* bidual sequence `Y_n`.
  set Y_n : ℕ → WeakDual ℝ (StrongDual ℝ X) :=
    fun n => NormedSpace.inclusionInDoubleDualWeak ℝ X
              ((toWeakSpace ℝ X) (x_n n)) with hY_def
  -- Step 3: Each `Y_n` lies in the preimage of the closed ball of radius `R`
  -- in `StrongDual ℝ (StrongDual ℝ X)` under `WeakDual.toStrongDual`.
  --
  -- Setwise: `WeakDual.toStrongDual Y_n = inclusionInDoubleDual ℝ X (x_n n)`,
  -- and the latter has norm at most `R`.
  set B : Set (WeakDual ℝ (StrongDual ℝ X)) :=
    WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 R with hB_def
  have hY_mem : ∀ n, Y_n n ∈ B := by
    intro n
    -- Goal: `WeakDual.toStrongDual (Y_n n) ∈ Metric.closedBall 0 R`,
    -- i.e. `‖WeakDual.toStrongDual (Y_n n)‖ ≤ R`.
    -- The function `WeakDual.toStrongDual ∘ inclusionInDoubleDualWeak ℝ X
    --   ∘ toWeakSpace ℝ X` agrees with `inclusionInDoubleDual ℝ X` on `X`.
    -- Pointwise check: for any `f`, both sides evaluate to `f (x_n n)`.
    have hcoincide :
        WeakDual.toStrongDual (Y_n n) =
          NormedSpace.inclusionInDoubleDual ℝ X (x_n n) := by
      apply ContinuousLinearMap.ext
      intro f
      -- Both sides evaluate to `f (x_n n)`: the RHS by definition of
      -- `inclusionInDoubleDual` (`dual_def`), the LHS by unfolding the
      -- `arrowCongr` through identity-on-type linear equivs `toWeakSpace`
      -- and `StrongDual.toWeakDual`.
      change ((NormedSpace.inclusionInDoubleDualWeak ℝ X)
              ((toWeakSpace ℝ X) (x_n n))) f = f (x_n n)
      rfl
    -- Conclude: ‖Y_n n‖ in the StrongDual sense equals ‖inclusion x_n n‖ ≤ R.
    have hnorm_le : ‖WeakDual.toStrongDual (Y_n n)‖ ≤ R := by
      rw [hcoincide]
      exact norm_inclusionInDoubleDual_le (hR n)
    change WeakDual.toStrongDual (Y_n n) ∈ Metric.closedBall (0 : StrongDual ℝ (StrongDual ℝ X)) R
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm_le
  -- Step 4: Apply sequential Banach–Alaoglu in `WeakDual`.
  have hSeqCompact : IsSeqCompact B :=
    WeakDual.isSeqCompact_closedBall ℝ (StrongDual ℝ X)
      (0 : StrongDual ℝ (StrongDual ℝ X)) R
  obtain ⟨Y, hY_inB, φ, hφ_mono, hY_tendsto⟩ := hSeqCompact hY_mem
  -- Step 5: Use reflexivity to pull `Y` back to a point `x : WeakSpace ℝ X`.
  obtain ⟨x, hx_eq⟩ :=
    inclusionInDoubleDualWeak_surjective_of_reflexive (X := X) hX Y
  refine ⟨φ, hφ_mono, x, ?_⟩
  -- Step 6: Transfer the convergence `Y_(φ k) → Y` back to
  -- `toWeakSpace ℝ X (x_n (φ k)) → x` using the topological embedding
  -- `inclusionInDoubleDualWeak ℝ X`.
  have hEmbed : IsEmbedding (NormedSpace.inclusionInDoubleDualWeak ℝ X) :=
    NormedSpace.isEmbedding_inclusionInDoubleDualWeak ℝ X
  -- The sequence `(fun k => toWeakSpace ℝ X (x_n (φ k)))` is
  -- mapped by `inclusionInDoubleDualWeak ℝ X` to `Y ∘ φ`, which tends to `Y`.
  -- And `Y = inclusionInDoubleDualWeak ℝ X x`, so by `IsEmbedding.tendsto_nhds_iff`
  -- the original sequence tends to `x`.
  rw [hEmbed.tendsto_nhds_iff]
  -- Now the goal is `Tendsto (inclusionInDoubleDualWeak ℝ X ∘
  --   fun k => toWeakSpace ℝ X (x_n (φ k))) atTop (𝓝 (inclusionInDoubleDualWeak ℝ X x))`.
  -- This is exactly `hY_tendsto` after rewriting through `hx_eq` and unfolding `Y_n`.
  have hgoal : (fun k => NormedSpace.inclusionInDoubleDualWeak ℝ X
        ((toWeakSpace ℝ X) (x_n (φ k)))) = (fun k => Y_n (φ k)) := by
    funext k; rfl
  rw [Function.comp_def, hgoal, hx_eq]
  exact hY_tendsto

/-! ## Sanity-check examples -/

/-- **Application to the paper's compactness target.** Given separability of
the strong dual of the product space `Lp ℝ 2 × SobolevPerLp 1 2 d`, every
bounded sequence in this Hilbert product space admits a weakly convergent
subsequence.

The separability hypothesis is supplied as a typeclass instance; it is true
under standard separability of the underlying `Lp ℝ 2 (volume.restrict ...)`
factors, but proving the instance globally is parked as a follow-up. The
example below verifies that the type of the witness-extracting theorem matches
the paper's compactness use case at the `β̄ = γ̄ = 2` calibration. -/
example (d : ℕ)
    [TopologicalSpace.SeparableSpace
      (StrongDual ℝ
        ((MeasureTheory.Lp ℝ 2
            (MeasureTheory.Measure.restrict (volume) (UnitCube d))) ×
          SobolevPerLp 1 2 d))]
    (z_n : ℕ →
      ((MeasureTheory.Lp ℝ 2
          (MeasureTheory.Measure.restrict (volume) (UnitCube d))) ×
        SobolevPerLp 1 2 d))
    (hb : IsBounded (Set.range z_n)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ z : WeakSpace ℝ
      ((MeasureTheory.Lp ℝ 2
          (MeasureTheory.Measure.restrict (volume) (UnitCube d))) ×
        SobolevPerLp 1 2 d),
      Tendsto (fun n => (toWeakSpace ℝ _) (z_n (φ n))) atTop (𝓝 z) :=
  weakSeqCompact_of_bounded_reflexive
    (lpSobolev_product_isReflexive_two (d := d)) z_n hb

/-- A bounded sequence in any reflexive real normed space whose strong dual
is separable has a weakly convergent subsequence — generic restatement. -/
example {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [TopologicalSpace.SeparableSpace (StrongDual ℝ X)]
    (hX : IsReflexiveNormedSpace X)
    (x_n : ℕ → X) (hb : IsBounded (Set.range x_n)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ x : WeakSpace ℝ X,
      Tendsto (fun n => (toWeakSpace ℝ X) (x_n (φ n))) atTop (𝓝 x) :=
  weakSeqCompact_of_bounded_reflexive hX x_n hb

end Periodic
end StationaryMFG
