module

public import StationaryMFG.Periodic.Basic

@[expose] public section

/-!
# The unit cube as a fundamental domain for ℤ^d acting on ℝ^d

Per `docs/CONVENTIONS.md` §1, the "torus" `𝕋^d` is modelled by the unit cube
`UnitCube d := {x : Fin d → ℝ | ∀ i, 0 ≤ x i ∧ x i < 1}`. This file records
the three structural facts about `UnitCube d` that the rest of Phase 1 relies
on:

1. It is a measurable set.
2. Its Lebesgue volume is `1`.
3. It is a fundamental domain for the ℤ^d-action on `ℝ^d` by translation:
   every `x : Fin d → ℝ` admits a (unique) integer translate lying in
   `UnitCube d`.

Integration over `UnitCube d` and the periodic `Lᵖ`/`Wᵏ,ᵖ` machinery live in
sibling modules (`Integral.lean`, `Lp.lean`, …).
-/

namespace StationaryMFG
namespace Periodic

open Set MeasureTheory

variable {d : ℕ}

/-- The (half-open) unit cube `[0,1)^d ⊆ ℝ^d`, viewed as a subset of
`Fin d → ℝ`. The half-open choice makes every `x : Fin d → ℝ` have a *unique*
integer translate inside the cube, which is what we need for a fundamental
domain. -/
def UnitCube (d : ℕ) : Set (Fin d → ℝ) :=
  Set.pi Set.univ fun _ : Fin d => Set.Ico (0 : ℝ) 1

lemma mem_unitCube_iff {x : Fin d → ℝ} :
    x ∈ UnitCube d ↔ ∀ i, 0 ≤ x i ∧ x i < 1 := by
  unfold UnitCube
  simp [Set.mem_pi, Set.mem_Ico]

/-- The unit cube is a measurable set. -/
lemma measurableSet_unitCube : MeasurableSet (UnitCube d) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ico

/-- The Lebesgue volume of the unit cube equals `1`. -/
@[simp]
lemma volume_unitCube : MeasureTheory.volume (UnitCube d) = 1 := by
  unfold UnitCube
  rw [Real.volume_pi_Ico]
  simp

/-- Existence part of the fundamental-domain property: for every
`x : Fin d → ℝ`, subtracting the coordinatewise floor lands in the unit cube.
The integer translate is `k i := ⌊x i⌋`. -/
lemma exists_int_translate_mem_unitCube (x : Fin d → ℝ) :
    ∃ k : Fin d → ℤ, (x - fun i => (k i : ℝ)) ∈ UnitCube d := by
  refine ⟨fun i => ⌊x i⌋, ?_⟩
  rw [mem_unitCube_iff]
  intro i
  -- `x i - ⌊x i⌋ = Int.fract (x i) ∈ [0, 1)`.
  have hfract : x i - (⌊x i⌋ : ℝ) = Int.fract (x i) := by
    rw [Int.fract]
  refine ⟨?_, ?_⟩
  · simp only [Pi.sub_apply, hfract]
    exact Int.fract_nonneg _
  · simp only [Pi.sub_apply, hfract]
    exact Int.fract_lt_one _

/-- Uniqueness part of the fundamental-domain property: at most one integer
translate of `x` lies in the half-open unit cube. If two integer translates
`x - k` and `x - k'` both lie in `UnitCube d`, then `k = k'`. -/
lemma unique_int_translate_of_mem_unitCube {x : Fin d → ℝ} {k k' : Fin d → ℤ}
    (hk : (x - fun i => (k i : ℝ)) ∈ UnitCube d)
    (hk' : (x - fun i => (k' i : ℝ)) ∈ UnitCube d) :
    k = k' := by
  rw [mem_unitCube_iff] at hk hk'
  funext i
  have h1 := hk i
  have h2 := hk' i
  -- `0 ≤ x i - k i < 1` and `0 ≤ x i - k' i < 1`.
  have h1a : (0 : ℝ) ≤ x i - (k i : ℝ) := by simpa using h1.1
  have h1b : x i - (k i : ℝ) < 1 := by simpa using h1.2
  have h2a : (0 : ℝ) ≤ x i - (k' i : ℝ) := by simpa using h2.1
  have h2b : x i - (k' i : ℝ) < 1 := by simpa using h2.2
  -- The difference `(k' i - k i : ℝ)` lies in the open interval `(-1, 1)`.
  have hdiff_lt : ((k' i : ℝ) - (k i : ℝ)) < 1 := by linarith
  have hdiff_gt : (-1 : ℝ) < ((k' i : ℝ) - (k i : ℝ)) := by linarith
  -- Passing through the integer cast: the integer `k' i - k i` is strictly
  -- between `-1` and `1`, hence zero.
  have hcast : ((k' i - k i : ℤ) : ℝ) = (k' i : ℝ) - (k i : ℝ) := by
    push_cast; ring
  have hlt : (k' i - k i : ℤ) < 1 := by
    have : ((k' i - k i : ℤ) : ℝ) < ((1 : ℤ) : ℝ) := by
      rw [hcast]; exact_mod_cast hdiff_lt
    exact_mod_cast this
  have hgt : (-1 : ℤ) < (k' i - k i : ℤ) := by
    have : (((-1) : ℤ) : ℝ) < ((k' i - k i : ℤ) : ℝ) := by
      rw [hcast]; exact_mod_cast hdiff_gt
    exact_mod_cast this
  have hzero : k' i - k i = 0 := by omega
  linarith [hzero]

end Periodic
end StationaryMFG
