module

public import StationaryMFG.Basic
public import StationaryMFG.Periodic.Basic
public import StationaryMFG.Periodic.UnitCube
public import Mathlib.Data.ENNReal.Basic
public import Mathlib.Data.ENNReal.Real

@[expose] public section

/-!
# Hamiltonian — basic data carriers

This module introduces the basic types used to talk about a Hamiltonian
`H : 𝕋^d × ℝ^d × ℝ^+ → ℝ` and its `p`-gradient `D_pH` in our periodic
setting. It is the first file in Phase 2 (§2.3 of
Ferreira–Gomes–Üçer) and contains no analytical content; the
hypotheses `(a:regularityH)`, `(a:Hat0)`, `(a:mDpHat0)`, etc., are stated
in `StationaryMFG/Hamiltonian/Assumptions.lean`.

Per `docs/CONVENTIONS.md` §1, the torus `𝕋^d` is modelled by
periodic functions on `Fin d → ℝ` with fundamental domain `UnitCube d`,
not by a quotient space. A "Hamiltonian" is therefore just a function
`H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ` whose `x`-component is
periodic; periodicity is not built into the type, it is asserted in the
regularity hypotheses.
-/

namespace StationaryMFG
namespace Hamiltonian

open scoped ENNReal

/-- A point of the phase space `𝕋^d × ℝ^d × ℝ` on which a Hamiltonian
acts: position `x` (modelled as a point of `ℝ^d` via the periodic
convention), momentum `p ∈ ℝ^d`, and density `m ∈ ℝ` (with `m > 0`
in the body of the paper, but the type itself does not enforce that). -/
abbrev MfgPoint (d : ℕ) : Type :=
  (Fin d → ℝ) × (Fin d → ℝ) × ℝ

/-! ### Auxiliary exponents `β̄` and `γ̄`

These come from the unlabelled equation `eq:gamma` at line 489 of
`Source/FGU-monotone_revised.tex`:
```
β̄ = β + 1,    γ̄ = α (β + 1) / β.
```
The Hölder conjugates `β̄'` and `γ̄'` satisfy `1/β̄ + 1/β̄' = 1` and
`1/γ̄ + 1/γ̄' = 1`. The dual identity `γ̄ = α · β̄'` is invoked in
every a priori estimate of §3 onward. -/

/-- The auxiliary exponent `β̄ := β + 1` from the paper's eq. `eq:gamma`. -/
noncomputable def betaBar (β : ℝ) : ℝ := β + 1

/-- The auxiliary exponent `γ̄ := α (β + 1) / β` from the paper's
eq. `eq:gamma`. -/
noncomputable def gammaBar (α β : ℝ) : ℝ := α * (β + 1) / β

/-- Hölder conjugate of `β̄`: explicitly `β̄' = (β + 1) / β`, since
`1/(β+1) + β/(β+1) = 1`. -/
noncomputable def betaBar' (β : ℝ) : ℝ := (β + 1) / β

/-- Hölder conjugate of `γ̄`, defined by the standard formula
`q' = q / (q - 1)`. -/
noncomputable def gammaBar' (α β : ℝ) : ℝ :=
  gammaBar α β / (gammaBar α β - 1)

/-- The dual identity `γ̄ = α · β̄'`, by direct calculation. -/
theorem gammaBar_eq_alpha_mul_betaBar' (α β : ℝ) (hβ : β ≠ 0) :
    gammaBar α β = α * betaBar' β := by
  unfold gammaBar betaBar'
  field_simp

/-- The Hölder identity for `β̄`: `1/β̄ + 1/β̄' = 1`. -/
theorem inv_betaBar_add_inv_betaBar' (β : ℝ) (hβ : 0 < β) :
    1 / betaBar β + 1 / betaBar' β = 1 := by
  unfold betaBar betaBar'
  have hβ1 : β + 1 ≠ 0 := by linarith
  have hβne : β ≠ 0 := ne_of_gt hβ
  field_simp
  ring

/-- `β̄ > 1` whenever `β > 0`. -/
theorem one_lt_betaBar (β : ℝ) (hβ : 0 < β) : 1 < betaBar β := by
  unfold betaBar; linarith

/-- `β̄ > 0` whenever `β > -1`. -/
theorem betaBar_pos (β : ℝ) (hβ : -1 < β) : 0 < betaBar β := by
  unfold betaBar; linarith

/-- `β̄' > 1` whenever `β > 0`, since `(β+1)/β = 1 + 1/β > 1`. -/
theorem one_lt_betaBar' (β : ℝ) (hβ : 0 < β) : 1 < betaBar' β := by
  unfold betaBar'
  rw [lt_div_iff₀ hβ]
  linarith

/-- `γ̄ > 1` whenever `α > 1` and `β > 0`. -/
theorem one_lt_gammaBar (α β : ℝ) (hα : 1 < α) (hβ : 0 < β) :
    1 < gammaBar α β := by
  rw [gammaBar_eq_alpha_mul_betaBar' α β (ne_of_gt hβ)]
  have hb' : 1 < betaBar' β := one_lt_betaBar' β hβ
  have hb'_pos : 0 < betaBar' β := lt_trans zero_lt_one hb'
  calc 1 = 1 * 1 := by ring
    _ < α * betaBar' β := by
        exact mul_lt_mul' (le_of_lt hα) hb' (le_of_lt zero_lt_one) (lt_trans zero_lt_one hα)

/-- `γ̄ > 0` whenever `α > 0` and `β > 0`. -/
theorem gammaBar_pos (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    0 < gammaBar α β := by
  unfold gammaBar
  positivity

/-- Sanity check of the dual identity at concrete values: with `α = 2`
and `β = 1`, we have `β̄ = 2`, `β̄' = 2`, and `γ̄ = 4 = α · β̄'`. -/
example : gammaBar 2 1 = 2 * betaBar' 1 := by
  unfold gammaBar betaBar'; norm_num

example : betaBar 1 = 2 := by unfold betaBar; norm_num

example : gammaBar 2 1 = 4 := by unfold gammaBar; norm_num

/-! ### `Fact` introductions for the ENNReal projections of `β̄` and `γ̄`

The Phase 4 / Phase 5 producer chain in
`StationaryMFG/Theorems/SimplePower/Banach/*` consumes `Fact (1 ≤ p)`
instances for the exponent `p := ENNReal.ofReal (β̄ β)` and likewise
for `γ̄`. The lemmas below let the caller introduce those `Fact`s
once-and-for-all from the underlying `0 < β` / `1 < α`-style data
fields of `HypothesisPowerGrowth`. They are not registered as
typeclass `instance`s because they depend on a hypothesis (`0 < β`,
etc.) that is not part of the static context — callers should bind
them with `haveI := ...` at the call-site. -/

/-- `1 ≤ ENNReal.ofReal (β̄ β)` whenever `0 < β`, since `β̄ β = β + 1 ≥ 1`. -/
lemma fact_one_le_ofReal_betaBar {β : ℝ} (hβ : 0 < β) :
    Fact (1 ≤ ENNReal.ofReal (betaBar β)) := by
  refine ⟨?_⟩
  unfold betaBar
  rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
  exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).mpr (by linarith)

/-- `1 ≤ ENNReal.ofReal (γ̄ α β)` whenever `1 < α` and `0 < β`. -/
lemma fact_one_le_ofReal_gammaBar {α β : ℝ} (hα : 1 < α) (hβ : 0 < β) :
    Fact (1 ≤ ENNReal.ofReal (gammaBar α β)) := by
  refine ⟨?_⟩
  have hα0 : 0 < α := lt_trans zero_lt_one hα
  have hβ1 : 0 < β + 1 := by linarith
  have hpos : 0 < gammaBar α β := by
    unfold gammaBar
    exact div_pos (mul_pos hα0 hβ1) hβ
  have h1 : 1 ≤ gammaBar α β := le_of_lt (one_lt_gammaBar α β hα hβ)
  rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
  exact (ENNReal.ofReal_le_ofReal_iff (le_of_lt hpos)).mpr h1

end Hamiltonian
end StationaryMFG
