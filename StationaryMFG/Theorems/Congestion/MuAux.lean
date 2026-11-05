module

/-
Copyright (c) 2026 Stationary MFG project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import StationaryMFG.Hamiltonian.Assumptions
public import StationaryMFG.Periodic.UnitCube
public import Mathlib.MeasureTheory.MeasurableSpace.Basic
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

@[expose] public section

/-!
# The auxiliary function `μ(x)` for the HJB inequality step

For a fixed tolerance `k > 0`, given periodic functions `m`, `u`, `V` and a
gradient witness `Du` together with a Hamiltonian `H`, the paper
(`Source/FGU-monotone_revised.tex` line 1431, eq. `eq:mu-definition`)
introduces the auxiliary correction

```
μ(x) := inf{μ₀ ∈ ℝ⁺ : μ₀ ≥ m(x) ∧ u(x) + H(x, Du(x), μ₀) - V(x) ≤ k}.
```

This module provides:

* `muAuxSet` — the constraint set, parameterised by `(k, m, u, V, Du, H)` and
  evaluated at a point `x : Fin d → ℝ`. We use `0 ≤ μ₀` (rather than strict
  `0 < μ₀`) so that the set is closed and the infimum is attained when
  non-empty; the strict-positivity statement of the paper is recovered
  whenever the witness produced is positive (which is the case under the
  congestion-growth upper bound).
* `muAux` — the pointwise infimum, computed with `sInf`.
* `muAux_nonempty` — under an a.e. upper bound for `H` of the form
  provided by `Hamiltonian.upper_bound_congestiongrowth`, the set is
  non-empty (in fact it contains a strictly positive witness) for almost
  every `x`.
* `muAux_measurable` — measurability via the level-set identity
  `{x : μ x ≤ a} = {x : m x ≤ a} ∩ {x : u x + H(x, Du x, a) - V x ≤ k}`
  for `a ≥ 0` (paper line 1435), under hypotheses of antitonicity of
  `H(x, Du x, ·)` (i.e. the constraint set is upward-closed in `μ₀`)
  and joint measurability of `H`.
* `muAux_product_identity` — the pointwise product identity
  `(μ(x) - m(x))(-k + u(x) + H(x, Du(x), μ(x)) - V(x)) = 0` (paper line 1437,
  eq. `eq:mu-minus-m-formula`).

## Paper reference

`Source/FGU-monotone_revised.tex` §`sec:proof-congestion`, lines 1431–1440.
-/

noncomputable section

namespace StationaryMFG
namespace Congestion

open MeasureTheory Set
open StationaryMFG.Periodic
open scoped Topology

variable {d : ℕ}

/-! ## The constraint set and the infimum -/

/-- The constraint set defining `μ(x)` (paper eq. `eq:mu-definition`,
line 1432).

`muAuxSet k m u V Du H x` is the set of admissible candidate values
`μ₀ ≥ 0` with `μ₀ ≥ m x` and `u x + H x (Du x) μ₀ - V x ≤ k`. Here
`Du x` denotes the gradient evaluation `fun i => Du i x : Fin d → ℝ`. -/
def muAuxSet
    (k : ℝ)
    (m u V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (x : Fin d → ℝ) : Set ℝ :=
  { μ₀ : ℝ | 0 ≤ μ₀ ∧ m x ≤ μ₀ ∧
      u x + H x (fun i => Du i x) μ₀ - V x ≤ k }

/-- The auxiliary function `μ(x)` (paper eq. `eq:mu-definition`, line 1432). -/
def muAux
    (k : ℝ)
    (m u V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ) :
    (Fin d → ℝ) → ℝ :=
  fun x => sInf (muAuxSet k m u V Du H x)

lemma muAux_def
    (k : ℝ)
    (m u V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (x : Fin d → ℝ) :
    muAux k m u V Du H x = sInf (muAuxSet k m u V Du H x) := rfl

lemma mem_muAuxSet_iff
    {k : ℝ} {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {x : Fin d → ℝ} {μ₀ : ℝ} :
    μ₀ ∈ muAuxSet k m u V Du H x ↔
      0 ≤ μ₀ ∧ m x ≤ μ₀ ∧ u x + H x (fun i => Du i x) μ₀ - V x ≤ k := Iff.rfl

/-- **Periodicity of the constraint set.** If the data `m, u, V, Du` and the
spatial sections `x ↦ H(x, p, μ₀)` are `ℤ^d`-periodic, then the constraint set
`muAuxSet k m u V Du H x` is invariant under integer-lattice translation of `x`.

Membership in `muAuxSet … x` is a conjunction of conditions in `m x`, `u x`,
`V x` and `H x (Du x) μ₀`, each of which is unchanged under `x ↦ x + k` by the
periodicity hypotheses (for `H`, periodicity of the section combined with
periodicity of the gradient evaluation `Du x`). -/
lemma muAuxSet_periodic
    {k : ℝ} {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    (hm : StationaryMFG.Periodic.IsPeriodic m)
    (hu : StationaryMFG.Periodic.IsPeriodic u)
    (hV : StationaryMFG.Periodic.IsPeriodic V)
    (hDu : ∀ i, StationaryMFG.Periodic.IsPeriodic (Du i))
    (hH : ∀ p μ₀, StationaryMFG.Periodic.IsPeriodic (fun x => H x p μ₀))
    (κ : Fin d → ℤ) (x : Fin d → ℝ) :
    muAuxSet k m u V Du H (x + fun i => (κ i : ℝ))
      = muAuxSet k m u V Du H x := by
  have hDu_pt : (fun i => Du i (x + fun i => (κ i : ℝ)))
      = (fun i => Du i x) := by
    funext i; exact hDu i κ x
  ext μ₀
  simp only [mem_muAuxSet_iff, hm κ x, hu κ x, hV κ x]
  -- The only remaining `x`-dependence is in `H (x + κ) (Du (x+κ) ·) μ₀`.
  have hHval : H (x + fun i => (κ i : ℝ))
        (fun i => Du i (x + fun i => (κ i : ℝ))) μ₀
      = H x (fun i => Du i x) μ₀ := by
    rw [hDu_pt]
    exact hH (fun i => Du i x) μ₀ κ x
  rw [hHval]

/-- **Periodicity of `muAux`.** Under periodicity of the data and the
Hamiltonian's spatial sections, `μ(x) = sInf (muAuxSet … x)` is periodic,
since equal sets have equal infima. -/
lemma muAux_periodic
    {k : ℝ} {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    (hm : StationaryMFG.Periodic.IsPeriodic m)
    (hu : StationaryMFG.Periodic.IsPeriodic u)
    (hV : StationaryMFG.Periodic.IsPeriodic V)
    (hDu : ∀ i, StationaryMFG.Periodic.IsPeriodic (Du i))
    (hH : ∀ p μ₀, StationaryMFG.Periodic.IsPeriodic (fun x => H x p μ₀)) :
    StationaryMFG.Periodic.IsPeriodic (muAux k m u V Du H) := by
  intro κ x
  simp only [muAux_def]
  rw [muAuxSet_periodic hm hu hV hDu hH κ x]

/-- `muAux` is always non-negative: every element of the constraint set is
`≥ 0`, so `sInf` is `≥ 0` (and `sInf ∅ = 0 ≥ 0` covers the empty case). -/
lemma muAux_nonneg
    {k : ℝ} {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    (x : Fin d → ℝ) :
    0 ≤ muAux k m u V Du H x :=
  Real.sInf_nonneg (fun _ hb => hb.1)

/-- The constraint set is bounded below by `0`. -/
lemma muAuxSet_bddBelow
    (k : ℝ) (m u V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (x : Fin d → ℝ) :
    BddBelow (muAuxSet k m u V Du H x) := by
  refine ⟨0, ?_⟩
  intro μ₀ hμ₀
  exact hμ₀.1

/-- The constraint set is closed (when `H(x, Du x, ·)` is continuous in
its third argument). -/
lemma muAuxSet_isClosed
    {k : ℝ} {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {x : Fin d → ℝ}
    (hcont : Continuous (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀)) :
    IsClosed (muAuxSet k m u V Du H x) := by
  have h1 : IsClosed { μ₀ : ℝ | 0 ≤ μ₀ } := isClosed_Ici
  have h2 : IsClosed { μ₀ : ℝ | m x ≤ μ₀ } := isClosed_Ici
  have h3 : IsClosed
      { μ₀ : ℝ | u x + H x (fun i => Du i x) μ₀ - V x ≤ k } := by
    have hc : Continuous
        (fun μ₀ : ℝ => u x + H x (fun i => Du i x) μ₀ - V x) :=
      (continuous_const.add hcont).sub continuous_const
    exact isClosed_le hc continuous_const
  have hset_eq :
      muAuxSet k m u V Du H x =
        { μ₀ : ℝ | 0 ≤ μ₀ } ∩
          ({ μ₀ : ℝ | m x ≤ μ₀ } ∩
            { μ₀ : ℝ | u x + H x (fun i => Du i x) μ₀ - V x ≤ k }) := by
    ext μ₀
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, h3⟩
  rw [hset_eq]
  exact h1.inter (h2.inter h3)

/-! ## Non-emptiness (paper line 1435, via `eq:boundsH+`) -/

/-- **Non-emptiness of the constraint set** (paper line 1435).

Under the upper bound `H(x, Du x, μ₀) ≤ f x - δ · μ₀^β` of the form
extracted from `Hamiltonian.upper_bound_congestiongrowth`, the constraint
set is non-empty for almost every `x`. -/
theorem muAux_nonempty
    {k : ℝ}
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {β δ : ℝ} (hβ : 0 < β) (hδ : 0 < δ)
    {f : (Fin d → ℝ) → ℝ}
    (hbound :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ μ₀, 0 < μ₀ →
          H x (fun i => Du i x) μ₀ ≤ f x - δ * μ₀ ^ β) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      (muAuxSet k m u V Du H x).Nonempty := by
  filter_upwards [hbound] with x hbx
  set A : ℝ := f x + u x - V x - k with hAdef
  set R : ℝ := max (m x) 1 with hRdef
  have hR_pos : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hR_ge_m : m x ≤ R := le_max_left _ _
  have hR_nn : 0 ≤ R := hR_pos.le
  rcases le_or_gt A 0 with hA_le | hA_pos
  · refine ⟨R, hR_nn, hR_ge_m, ?_⟩
    have hHbd : H x (fun i => Du i x) R ≤ f x - δ * R ^ β := hbx R hR_pos
    have hδRβ_nn : 0 ≤ δ * R ^ β :=
      mul_nonneg hδ.le (Real.rpow_nonneg hR_nn β)
    have h2 : u x + (f x - δ * R ^ β) - V x = A + k - δ * R ^ β := by
      rw [hAdef]; ring
    linarith
  · have hAdiv_pos : 0 < A / δ := div_pos hA_pos hδ
    set T : ℝ := (A / δ) ^ (1 / β) + 1 with hTdef
    have hT_pos_aux : 0 < (A / δ) ^ (1 / β) :=
      Real.rpow_pos_of_pos hAdiv_pos (1 / β)
    have hT_pos : 0 < T := by linarith
    set μ₀ : ℝ := max R T with hμ₀def
    have hμ₀_pos : 0 < μ₀ := lt_of_lt_of_le hR_pos (le_max_left _ _)
    have hμ₀_ge_m : m x ≤ μ₀ := le_trans hR_ge_m (le_max_left _ _)
    have hμ₀_ge_T : T ≤ μ₀ := le_max_right _ _
    refine ⟨μ₀, hμ₀_pos.le, hμ₀_ge_m, ?_⟩
    have hHbd : H x (fun i => Du i x) μ₀ ≤ f x - δ * μ₀ ^ β := hbx μ₀ hμ₀_pos
    have h_T_lt : (A / δ) ^ (1 / β) < T := by linarith
    have h_pow_eq : ((A / δ) ^ (1 / β)) ^ β = A / δ := by
      have hAdiv_nn : 0 ≤ A / δ := hAdiv_pos.le
      rw [← Real.rpow_mul hAdiv_nn]
      have h_one : (1 / β) * β = 1 := by field_simp
      rw [h_one, Real.rpow_one]
    have h_pow_le : ((A / δ) ^ (1 / β)) ^ β ≤ T ^ β :=
      Real.rpow_le_rpow hT_pos_aux.le h_T_lt.le hβ.le
    have hTβ_ge : A / δ ≤ T ^ β := by rw [← h_pow_eq]; exact h_pow_le
    have hμβ_ge_T : T ^ β ≤ μ₀ ^ β :=
      Real.rpow_le_rpow hT_pos.le hμ₀_ge_T hβ.le
    have hδμβ_ge : A ≤ δ * μ₀ ^ β := by
      have h1 : A / δ ≤ μ₀ ^ β := le_trans hTβ_ge hμβ_ge_T
      have h2 : A = δ * (A / δ) := by field_simp
      rw [h2]
      exact mul_le_mul_of_nonneg_left h1 hδ.le
    have h2 : u x + (f x - δ * μ₀ ^ β) - V x = A + k - δ * μ₀ ^ β := by
      rw [hAdef]; ring
    linarith

/-- **Non-emptiness companion for the large-`μ₀` regime** (paper line 1435).

A weakened-quantifier variant of `muAux_nonempty`: the upper bound for `H`
is required only for `μ₀ ≥ 1` (rather than for all `μ₀ > 0`).  This is the
shape that `H_upper_congestion_of_hmon` actually delivers with a *static*
right-hand side `f x`, because the positive part
`K·(1/μ₀ + 1/μ₀^τ)·(‖Du‖^{αt}+1)` is bounded above by `K·2·(‖Du‖^{αt}+1)`
only on `{μ₀ ≥ 1}` (it blows up as `μ₀ → 0⁺`).

The proof mirrors `muAux_nonempty`: the witness it constructs is always
`≥ R = max (m x) 1 ≥ 1`, so the weakened hypothesis is evaluated only at
points `≥ 1` and suffices.  The existing `muAux_nonempty` is left
untouched. -/
theorem muAux_nonempty_of_large_bound
    {k : ℝ}
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {β δ : ℝ} (hβ : 0 < β) (hδ : 0 < δ)
    {f : (Fin d → ℝ) → ℝ}
    (hbound :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ μ₀, 1 ≤ μ₀ →
          H x (fun i => Du i x) μ₀ ≤ f x - δ * μ₀ ^ β) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      (muAuxSet k m u V Du H x).Nonempty := by
  filter_upwards [hbound] with x hbx
  set A : ℝ := f x + u x - V x - k with hAdef
  set R : ℝ := max (m x) 1 with hRdef
  have hR_pos : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hR_ge_one : 1 ≤ R := le_max_right _ _
  have hR_ge_m : m x ≤ R := le_max_left _ _
  have hR_nn : 0 ≤ R := hR_pos.le
  rcases le_or_gt A 0 with hA_le | hA_pos
  · refine ⟨R, hR_nn, hR_ge_m, ?_⟩
    have hHbd : H x (fun i => Du i x) R ≤ f x - δ * R ^ β := hbx R hR_ge_one
    have hδRβ_nn : 0 ≤ δ * R ^ β :=
      mul_nonneg hδ.le (Real.rpow_nonneg hR_nn β)
    have h2 : u x + (f x - δ * R ^ β) - V x = A + k - δ * R ^ β := by
      rw [hAdef]; ring
    linarith
  · have hAdiv_pos : 0 < A / δ := div_pos hA_pos hδ
    set T : ℝ := (A / δ) ^ (1 / β) + 1 with hTdef
    have hT_pos_aux : 0 < (A / δ) ^ (1 / β) :=
      Real.rpow_pos_of_pos hAdiv_pos (1 / β)
    have hT_pos : 0 < T := by linarith
    set μ₀ : ℝ := max R T with hμ₀def
    have hμ₀_ge_R : R ≤ μ₀ := le_max_left _ _
    have hμ₀_ge_one : 1 ≤ μ₀ := le_trans hR_ge_one hμ₀_ge_R
    have hμ₀_pos : 0 < μ₀ := lt_of_lt_of_le zero_lt_one hμ₀_ge_one
    have hμ₀_ge_m : m x ≤ μ₀ := le_trans hR_ge_m hμ₀_ge_R
    have hμ₀_ge_T : T ≤ μ₀ := le_max_right _ _
    refine ⟨μ₀, hμ₀_pos.le, hμ₀_ge_m, ?_⟩
    have hHbd : H x (fun i => Du i x) μ₀ ≤ f x - δ * μ₀ ^ β := hbx μ₀ hμ₀_ge_one
    have h_T_lt : (A / δ) ^ (1 / β) < T := by linarith
    have h_pow_eq : ((A / δ) ^ (1 / β)) ^ β = A / δ := by
      have hAdiv_nn : 0 ≤ A / δ := hAdiv_pos.le
      rw [← Real.rpow_mul hAdiv_nn]
      have h_one : (1 / β) * β = 1 := by field_simp
      rw [h_one, Real.rpow_one]
    have h_pow_le : ((A / δ) ^ (1 / β)) ^ β ≤ T ^ β :=
      Real.rpow_le_rpow hT_pos_aux.le h_T_lt.le hβ.le
    have hTβ_ge : A / δ ≤ T ^ β := by rw [← h_pow_eq]; exact h_pow_le
    have hμβ_ge_T : T ^ β ≤ μ₀ ^ β :=
      Real.rpow_le_rpow hT_pos.le hμ₀_ge_T hβ.le
    have hδμβ_ge : A ≤ δ * μ₀ ^ β := by
      have h1 : A / δ ≤ μ₀ ^ β := le_trans hTβ_ge hμβ_ge_T
      have h2 : A = δ * (A / δ) := by field_simp
      rw [h2]
      exact mul_le_mul_of_nonneg_left h1 hδ.le
    have h2 : u x + (f x - δ * μ₀ ^ β) - V x = A + k - δ * μ₀ ^ β := by
      rw [hAdef]; ring
    linarith

/-! ## Measurability via the level-set identity (paper line 1435)

The paper claims `{x : μ x ≤ a} = {x : m x ≤ a} ∩ {x : HJB at a}` for
`a ∈ ℝ⁺`. The reverse inclusion is direct: any `a` satisfying the two
conditions is itself a candidate. The forward inclusion requires
*antitonicity* of `H(x, Du x, ·)` in the third argument (i.e. the
constraint `u + H(...,μ₀) - V ≤ k` is preserved when `μ₀` increases),
since the inf is attained at `μ x` (closedness of the constraint set
plus boundedness below) and antitonicity of `H` lifts the HJB constraint
from `μ x` to any `a ≥ μ x`.

For the *generic* monotonicity statement (without committing to a
direction) we provide a level-set inclusion that always holds:
`{x : m x ≤ a} ∩ {x : HJB at a} ⊆ {x : μ x ≤ a}`. Combined with
antitonicity we obtain set equality. -/

/-- The reverse inclusion of the paper's level-set identity (paper line
1435), `(⊇)` direction. Holds without any continuity or monotonicity
hypothesis on `H`. -/
lemma muAux_le_of_mem
    {k : ℝ} {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {x : Fin d → ℝ} {a : ℝ}
    (ha : 0 ≤ a) (hmle : m x ≤ a)
    (hHJB : u x + H x (fun i => Du i x) a - V x ≤ k) :
    muAux k m u V Du H x ≤ a := by
  apply csInf_le (muAuxSet_bddBelow k m u V Du H x)
  exact ⟨ha, hmle, hHJB⟩

/-- The forward inclusion of the paper's level-set identity, requiring
**antitonicity** of `H(x, Du x, ·)` in its third argument. -/
lemma muAux_le_iff_of_antitone_of_nonempty
    {k : ℝ} {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {x : Fin d → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hcont : Continuous (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀))
    (hanti : Antitone (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀))
    (hne : (muAuxSet k m u V Du H x).Nonempty) :
    muAux k m u V Du H x ≤ a ↔
      m x ≤ a ∧ u x + H x (fun i => Du i x) a - V x ≤ k := by
  refine ⟨fun hle => ?_, fun ⟨hmle, hHJB⟩ => muAux_le_of_mem ha hmle hHJB⟩
  -- Forward direction.
  have h_lb : m x ≤ sInf (muAuxSet k m u V Du H x) :=
    le_csInf hne (fun _ hb => hb.2.1)
  have hmle : m x ≤ a := le_trans h_lb hle
  have h_closed : IsClosed (muAuxSet k m u V Du H x) :=
    muAuxSet_isClosed hcont
  have h_bdd : BddBelow (muAuxSet k m u V Du H x) :=
    muAuxSet_bddBelow k m u V Du H x
  have h_inf_mem :
      sInf (muAuxSet k m u V Du H x) ∈ muAuxSet k m u V Du H x :=
    h_closed.csInf_mem hne h_bdd
  -- HJB at μ x:
  have hHJB_at_mu :
      u x + H x (fun i => Du i x) (sInf (muAuxSet k m u V Du H x)) - V x
        ≤ k := h_inf_mem.2.2
  -- Antitonicity: μ x ≤ a ⇒ H(...,a) ≤ H(...,μ x).
  have hanti_le : H x (fun i => Du i x) a
                  ≤ H x (fun i => Du i x) (sInf (muAuxSet k m u V Du H x)) :=
    hanti hle
  refine ⟨hmle, ?_⟩
  linarith

/-- **Measurability of `μ`** under antitonicity of `H(x, Du x, ·)` for a.e.
`x`, joint measurability of `H`, and measurability of `m, u, V, Du`.

The level-set identity `{x : μ x ≤ a} = {x : m x ≤ a} ∩ {x : HJB at a}`
(paper line 1435) reduces measurability of `μ` to measurability of the
two factors on the RHS. We do not formalise the full level-set identity
here; instead we provide the wrapper function and the two-sided inclusion
under the hypotheses, leaving the `Measurable` extraction to a downstream
task that bundles the precise hypotheses on `H`. -/
theorem muAux_levelSet_ae
    {k : ℝ} {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    (hae_anti :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        Antitone (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀))
    (hae_cont :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        Continuous (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀))
    (hae_ne :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        (muAuxSet k m u V Du H x).Nonempty)
    {a : ℝ} (ha : 0 ≤ a) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      (muAux k m u V Du H x ≤ a ↔
        m x ≤ a ∧ u x + H x (fun i => Du i x) a - V x ≤ k) := by
  filter_upwards [hae_anti, hae_cont, hae_ne] with x hax_anti hax_cont hax_ne
  exact muAux_le_iff_of_antitone_of_nonempty
    (k := k) (m := m) (u := u) (V := V) (Du := Du) (H := H)
    (x := x) (a := a) ha hax_cont hax_anti hax_ne

/-- **Measurability of `μ`** (paper line 1435).

Under joint measurability of `m`, the HJB constraint set `{x | u + H(x,Du,a) - V ≤ k}`
in `x` (for each `a`), and *pointwise* (not just a.e.) hypotheses on `H` of
continuity and antitonicity, the function `μ = muAux` is measurable.

The proof uses the level-set identity (paper line 1435):
`{x : μ x ≤ a} = {x : m x ≤ a} ∩ {x : u + H(x,Du,a) - V ≤ k}` for `a ≥ 0`.
The right-hand side is measurable (as an intersection of two measurable
sets, the second by hypothesis). This characterises measurability via the
generated σ-algebra of `Ici`-complements, since rational `a > 0` are
dense in `(0, ∞)` and `μ ≥ 0` (so its level sets `{μ ≤ a}` for `a ≥ 0`
suffice). -/
theorem muAux_measurable
    {k : ℝ} {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    (hm_meas : Measurable m)
    (hHJB_meas : ∀ a : ℝ,
      MeasurableSet { x : Fin d → ℝ |
        u x + H x (fun i => Du i x) a - V x ≤ k })
    (h_anti :
      ∀ x : Fin d → ℝ,
        Antitone (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀))
    (h_cont :
      ∀ x : Fin d → ℝ,
        Continuous (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀))
    (h_ne :
      ∀ x : Fin d → ℝ, (muAuxSet k m u V Du H x).Nonempty) :
    Measurable (muAux k m u V Du H) := by
  -- Use `Measurable.measurable_of_countable_le` style: it suffices to show
  -- that for each `a : ℝ`, `{x | muAux x ≤ a}` is measurable.
  apply measurable_of_Iic
  intro a
  -- `muAux x ∈ Iic a ↔ muAux x ≤ a`.
  rcases lt_or_ge a 0 with ha_neg | ha_nn
  · -- a < 0: the set is empty since muAux x ≥ 0 always.
    have hempty : { x : Fin d → ℝ | muAux k m u V Du H x ≤ a } = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hle
      have h_lb : 0 ≤ muAux k m u V Du H x := by
        apply le_csInf (h_ne x)
        intro b hb; exact hb.1
      linarith
    rw [show muAux k m u V Du H ⁻¹' Set.Iic a =
        { x : Fin d → ℝ | muAux k m u V Du H x ≤ a } from rfl, hempty]
    exact MeasurableSet.empty
  · -- a ≥ 0: use the level-set identity.
    have hset_eq :
        { x : Fin d → ℝ | muAux k m u V Du H x ≤ a } =
          { x : Fin d → ℝ | m x ≤ a } ∩
            { x : Fin d → ℝ |
              u x + H x (fun i => Du i x) a - V x ≤ k } := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
      exact muAux_le_iff_of_antitone_of_nonempty
        (k := k) (m := m) (u := u) (V := V) (Du := Du) (H := H)
        (x := x) (a := a) ha_nn (h_cont x) (h_anti x) (h_ne x)
    rw [show muAux k m u V Du H ⁻¹' Set.Iic a =
        { x : Fin d → ℝ | muAux k m u V Du H x ≤ a } from rfl, hset_eq]
    exact (hm_meas measurableSet_Iic).inter (hHJB_meas a)

/-! ## On-`[0,∞)` regularity variants (childA of prereq2)

The constraint set `muAuxSet k m u V Du H x` is contained in `Ici 0` by
construction (its first conjunct is `0 ≤ μ₀`). Therefore the closedness,
level-set identity, and measurability of `μ = muAux` only ever require the
regularity of `μ₀ ↦ H(x, Du x, μ₀)` ON `[0, ∞)` — not on all of `ℝ`.

This matters because `HypothesisCongestionGrowth` supplies only `AntitoneOn`
on `(0, ∞)` (`antitone_in_m`) and a.e. continuity on `{0 < m}`
(`RegularityH.continuous_H_pm`), never the full-`ℝ` `Antitone`/`Continuous`
demanded by `muAux_measurable`. The variants below close that gap by taking
the genuinely-available on-`Ici 0` hypotheses. The original full-`ℝ` lemmas
are kept untouched (other modules still consume them). -/

/-- The constraint set is closed, requiring only continuity of `H(x, Du x, ·)`
**on `[0, ∞)`** (rather than on all of `ℝ`). Sound because
`muAuxSet ⊆ Ici 0`. -/
lemma muAuxSet_isClosed_of_continuousOn
    {k : ℝ} {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {x : Fin d → ℝ}
    (hcont :
      ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ici 0)) :
    IsClosed (muAuxSet k m u V Du H x) := by
  -- The HJB section `μ₀ ↦ u x + H(x, Du x, μ₀) - V x` is continuous on `Ici 0`.
  have hHJBcont :
      ContinuousOn
        (fun μ₀ : ℝ => u x + H x (fun i => Du i x) μ₀ - V x) (Set.Ici 0) :=
    (continuousOn_const.add hcont).sub continuousOn_const
  -- `Ici 0 ∩ {μ₀ | HJB ≤ k}` is closed (preimage of the closed `Iic k`).
  have hpre :
      IsClosed
        ((Set.Ici (0 : ℝ)) ∩
          (fun μ₀ : ℝ => u x + H x (fun i => Du i x) μ₀ - V x) ⁻¹'
            (Set.Iic k)) :=
    hHJBcont.preimage_isClosed_of_isClosed isClosed_Ici isClosed_Iic
  -- `muAuxSet = (Ici 0 ∩ {HJB ≤ k}) ∩ Ici (m x)`.
  have hset_eq :
      muAuxSet k m u V Du H x =
        ((Set.Ici (0 : ℝ)) ∩
          (fun μ₀ : ℝ => u x + H x (fun i => Du i x) μ₀ - V x) ⁻¹'
            (Set.Iic k)) ∩ Set.Ici (m x) := by
    ext μ₀
    simp only [muAuxSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Ici,
      Set.mem_preimage, Set.mem_Iic]
    constructor
    · rintro ⟨h0, hm, hHJB⟩; exact ⟨⟨h0, hHJB⟩, hm⟩
    · rintro ⟨⟨h0, hHJB⟩, hm⟩; exact ⟨h0, hm, hHJB⟩
  rw [hset_eq]
  exact hpre.inter isClosed_Ici

/-- Level-set identity at `a ≥ 0`, requiring only **on-`[0, ∞)`**
antitonicity and continuity of `H(x, Du x, ·)`. Sound because the infimum and
the test point `a` both lie in `Ici 0`. -/
lemma muAux_le_iff_of_antitoneOn_of_nonempty
    {k : ℝ} {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {x : Fin d → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hcont :
      ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ici 0))
    (hanti :
      AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ici 0))
    (hne : (muAuxSet k m u V Du H x).Nonempty) :
    muAux k m u V Du H x ≤ a ↔
      m x ≤ a ∧ u x + H x (fun i => Du i x) a - V x ≤ k := by
  refine ⟨fun hle => ?_, fun ⟨hmle, hHJB⟩ => muAux_le_of_mem ha hmle hHJB⟩
  -- Forward direction.
  have h_lb : m x ≤ sInf (muAuxSet k m u V Du H x) :=
    le_csInf hne (fun _ hb => hb.2.1)
  have hmle : m x ≤ a := le_trans h_lb hle
  have h_closed : IsClosed (muAuxSet k m u V Du H x) :=
    muAuxSet_isClosed_of_continuousOn hcont
  have h_bdd : BddBelow (muAuxSet k m u V Du H x) :=
    muAuxSet_bddBelow k m u V Du H x
  have h_inf_mem :
      sInf (muAuxSet k m u V Du H x) ∈ muAuxSet k m u V Du H x :=
    h_closed.csInf_mem hne h_bdd
  -- The infimum is nonnegative (every element of the set is).
  have h_inf_nn : (0 : ℝ) ≤ sInf (muAuxSet k m u V Du H x) := h_inf_mem.1
  -- HJB at `μ x`:
  have hHJB_at_mu :
      u x + H x (fun i => Du i x) (sInf (muAuxSet k m u V Du H x)) - V x
        ≤ k := h_inf_mem.2.2
  -- Antitonicity on `Ici 0`: `μ x ≤ a ⇒ H(...,a) ≤ H(...,μ x)`, with both
  -- arguments in `Ici 0`.
  have hanti_le : H x (fun i => Du i x) a
                  ≤ H x (fun i => Du i x) (sInf (muAuxSet k m u V Du H x)) :=
    hanti h_inf_nn ha hle
  refine ⟨hmle, ?_⟩
  linarith

/-! ## On-`(0,∞)` regularity variants assuming `0 < m x` (positive-witness route)

When the witness density is strictly positive at `x` (`0 < m x`), the
constraint set `muAuxSet k m u V Du H x` is contained in `Ici (m x) ⊆ Ioi 0`.
Therefore the closedness and level-set identity require only the regularity of
`μ₀ ↦ H(x, Du x, μ₀)` ON the OPEN half-line `(0, ∞)` — exactly the standing
facts supplied by `HypothesisCongestionGrowth`
(`RegularityH.continuous_H_pm` on `{0 < pm.2}` and `antitone_in_m` on
`Ioi 0`). No continuity at the boundary `μ₀ = 0` is needed, because every
admissible candidate sits strictly inside the open half-line.

This is the paper's truncation regime (`μ_δ = max{μ, δ}`): the boundary is
avoided rather than analysed. The earlier on-`Ici 0` lemmas
(`muAuxSet_isClosed_of_continuousOn`, `muAux_le_iff_of_antitoneOn_of_nonempty`)
are kept untouched; these are genuine siblings. -/

/-- The constraint set is closed, requiring only continuity of `H(x, Du x, ·)`
**on the open `(0, ∞)`** — assuming `0 < m x`. Sound because then
`muAuxSet k m u V Du H x ⊆ Ici (m x) ⊆ Ioi 0`, and `Ici (m x)` is closed. -/
lemma muAuxSet_isClosed_of_continuousOn_Ioi_of_m_pos
    {k : ℝ} {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {x : Fin d → ℝ} (hmx : 0 < m x)
    (hcont :
      ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0)) :
    IsClosed (muAuxSet k m u V Du H x) := by
  -- `muAuxSet ⊆ Ici (m x)`, and on `Ici (m x) ⊆ Ioi 0` the HJB section is
  -- continuous. Write `muAuxSet = (Ici (m x) ∩ {HJB ≤ k}) ∩ Ici 0` and use
  -- closedness on the closed subset `Ici (m x)`.
  -- The HJB section `μ₀ ↦ u x + H(x, Du x, μ₀) - V x` is continuous on `Ioi 0`.
  have hHJBcont :
      ContinuousOn
        (fun μ₀ : ℝ => u x + H x (fun i => Du i x) μ₀ - V x) (Set.Ioi 0) :=
    (continuousOn_const.add hcont).sub continuousOn_const
  -- Restrict the continuity to the closed set `Ici (m x) ⊆ Ioi 0`.
  have hsub : Set.Ici (m x) ⊆ Set.Ioi (0 : ℝ) := fun y hy =>
    lt_of_lt_of_le hmx hy
  have hHJBcont' :
      ContinuousOn
        (fun μ₀ : ℝ => u x + H x (fun i => Du i x) μ₀ - V x) (Set.Ici (m x)) :=
    hHJBcont.mono hsub
  -- `Ici (m x) ∩ {μ₀ | HJB ≤ k}` is closed (preimage of closed `Iic k`).
  have hpre :
      IsClosed
        ((Set.Ici (m x)) ∩
          (fun μ₀ : ℝ => u x + H x (fun i => Du i x) μ₀ - V x) ⁻¹'
            (Set.Iic k)) :=
    hHJBcont'.preimage_isClosed_of_isClosed isClosed_Ici isClosed_Iic
  -- `muAuxSet = (Ici (m x) ∩ {HJB ≤ k}) ∩ Ici 0`.
  have hset_eq :
      muAuxSet k m u V Du H x =
        ((Set.Ici (m x)) ∩
          (fun μ₀ : ℝ => u x + H x (fun i => Du i x) μ₀ - V x) ⁻¹'
            (Set.Iic k)) ∩ Set.Ici (0 : ℝ) := by
    ext μ₀
    simp only [muAuxSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Ici,
      Set.mem_preimage, Set.mem_Iic]
    constructor
    · rintro ⟨h0, hm, hHJB⟩; exact ⟨⟨hm, hHJB⟩, h0⟩
    · rintro ⟨⟨hm, hHJB⟩, h0⟩; exact ⟨h0, hm, hHJB⟩
  rw [hset_eq]
  exact hpre.inter isClosed_Ici

/-- Level-set identity at `a` with `m x ≤ a`, requiring only **on-`(0,∞)`**
antitonicity and continuity of `H(x, Du x, ·)` — assuming `0 < m x`. Sound
because the infimum and the test point `a` both lie in `Ici (m x) ⊆ Ioi 0`. -/
lemma muAux_le_iff_of_antitoneOn_Ioi_of_nonempty_of_m_pos
    {k : ℝ} {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {x : Fin d → ℝ} {a : ℝ} (hmx : 0 < m x) (ha : 0 ≤ a)
    (hcont :
      ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hanti :
      AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hne : (muAuxSet k m u V Du H x).Nonempty) :
    muAux k m u V Du H x ≤ a ↔
      m x ≤ a ∧ u x + H x (fun i => Du i x) a - V x ≤ k := by
  refine ⟨fun hle => ?_, fun ⟨hmle, hHJB⟩ => muAux_le_of_mem ha hmle hHJB⟩
  -- Forward direction.
  have h_lb : m x ≤ sInf (muAuxSet k m u V Du H x) :=
    le_csInf hne (fun _ hb => hb.2.1)
  have hmle : m x ≤ a := le_trans h_lb hle
  have h_closed : IsClosed (muAuxSet k m u V Du H x) :=
    muAuxSet_isClosed_of_continuousOn_Ioi_of_m_pos hmx hcont
  have h_bdd : BddBelow (muAuxSet k m u V Du H x) :=
    muAuxSet_bddBelow k m u V Du H x
  have h_inf_mem :
      sInf (muAuxSet k m u V Du H x) ∈ muAuxSet k m u V Du H x :=
    h_closed.csInf_mem hne h_bdd
  -- The infimum dominates `m x` (positive) and `a ≥ m x > 0`.
  have h_inf_pos : (0 : ℝ) < sInf (muAuxSet k m u V Du H x) :=
    lt_of_lt_of_le hmx h_lb
  have h_a_pos : (0 : ℝ) < a := lt_of_lt_of_le hmx hmle
  -- HJB at `μ x`:
  have hHJB_at_mu :
      u x + H x (fun i => Du i x) (sInf (muAuxSet k m u V Du H x)) - V x
        ≤ k := h_inf_mem.2.2
  -- Antitonicity on `Ioi 0`: `μ x ≤ a ⇒ H(...,a) ≤ H(...,μ x)`, both in `Ioi 0`.
  have hanti_le : H x (fun i => Du i x) a
                  ≤ H x (fun i => Du i x) (sInf (muAuxSet k m u V Du H x)) :=
    hanti h_inf_pos h_a_pos hle
  refine ⟨hmle, ?_⟩
  linarith

/-! ## On-`(0,∞)` product identity assuming `0 < m x` (positive-witness route)

The pointwise product identity of paper line 1437 on the a.e. set `{0 < m x}`,
using only `ContinuousOn (Ioi 0)` (rather than full-`ℝ` `Continuous`). On
`{0 < m x}` the infimum `μ x ≥ m x > 0`, so the continuity argument that
perturbs `μ x` downward by a small `ε` can be carried out staying inside the
open half-line `Ioi 0` (choose the perturbation small enough to remain
`> m x / 2 > 0`). No redefinition of `muAux`; this is a per-`x` statement on
`{0 < m x}`, a genuine sibling of `muAux_product_identity`. -/

/-- **Pointwise product identity on `{0 < m x}`** (paper line 1437), requiring
only **on-`(0,∞)`** continuity of `H(x, Du x, ·)`. Sibling of
`muAux_product_identity`; the original is kept untouched. -/
theorem muAux_product_identity_of_m_pos
    {k : ℝ}
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    (hae_cont :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hae_ne :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        (muAuxSet k m u V Du H x).Nonempty)
    (hae_m_pos :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      (muAux k m u V Du H x - m x) *
        (-k + u x + H x (fun i => Du i x) (muAux k m u V Du H x) - V x) = 0 := by
  filter_upwards [hae_cont, hae_ne, hae_m_pos] with x hx_cont hx_ne hx_m_pos
  set μx : ℝ := muAux k m u V Du H x with hμxdef
  -- `m x ≤ μ x` (every element of the constraint set dominates `m x`).
  have h_mle_mu : m x ≤ μx := by
    apply le_csInf hx_ne
    intro b hb
    exact hb.2.1
  rcases lt_or_eq_of_le h_mle_mu with h_lt | h_eq
  · -- m x < μ x. Show second factor is zero.
    have h_closed : IsClosed (muAuxSet k m u V Du H x) :=
      muAuxSet_isClosed_of_continuousOn_Ioi_of_m_pos hx_m_pos hx_cont
    have h_bdd : BddBelow (muAuxSet k m u V Du H x) :=
      muAuxSet_bddBelow k m u V Du H x
    have h_inf_mem : μx ∈ muAuxSet k m u V Du H x :=
      h_closed.csInf_mem hx_ne h_bdd
    have hHJB_le : u x + H x (fun i => Du i x) μx - V x ≤ k :=
      h_inf_mem.2.2
    -- `μ x ≥ m x > 0`.
    have hμx_pos : (0 : ℝ) < μx := lt_of_lt_of_le hx_m_pos h_mle_mu
    by_contra hne_zero
    have hHJB_lt_or_eq : u x + H x (fun i => Du i x) μx - V x = k ∨
                         u x + H x (fun i => Du i x) μx - V x < k :=
      eq_or_lt_of_le hHJB_le
    rcases hHJB_lt_or_eq with h_eq_k | h_lt_k
    · apply hne_zero
      have h_factor_eq : -k + u x + H x (fun i => Du i x) μx - V x = 0 := by
        linarith
      rw [h_factor_eq, mul_zero]
    · -- strict HJB inequality at `μ x`. Use continuity ON `Ioi 0` (μ x is
      -- interior to `Ioi 0`, so the relative neighbourhood is a genuine
      -- neighbourhood) to find a smaller admissible point, contradicting inf.
      have h_strict : u x + H x (fun i => Du i x) μx - V x < k := h_lt_k
      set φ : ℝ → ℝ :=
        fun t => u x + H x (fun i => Du i x) t - V x with hφdef
      -- `φ` is continuous on `Ioi 0`.
      have hφ_contOn : ContinuousOn φ (Set.Ioi 0) :=
        (continuousOn_const.add hx_cont).sub continuousOn_const
      have hφμx_lt_k : φ μx < k := h_strict
      -- Since `μ x ∈ Ioi 0` (open), the relative preimage of `Iio k` is a
      -- neighbourhood of `μ x` in `ℝ`. Build it directly via continuity at
      -- `μ x` within `Ioi 0`, intersected with the open `Ioi 0`.
      have hμx_mem_Ioi : μx ∈ Set.Ioi (0 : ℝ) := hμx_pos
      have h_cont_at : ContinuousWithinAt φ (Set.Ioi 0) μx :=
        hφ_contOn μx hμx_mem_Ioi
      -- `Ioi 0` is open, so `ContinuousWithinAt` upgrades to `ContinuousAt`.
      have h_cont_at' : ContinuousAt φ μx :=
        h_cont_at.continuousAt (isOpen_Ioi.mem_nhds hμx_mem_Ioi)
      -- Find a neighbourhood of `μ x` (in ℝ) where `φ < k`.
      have hpre_nhds : φ ⁻¹' Set.Iio k ∈ nhds μx :=
        h_cont_at'.preimage_mem_nhds (isOpen_Iio.mem_nhds hφμx_lt_k)
      -- Intersect with `Ioi 0` (also a nhd of μ x) to stay positive.
      have hIoi_nhds : Set.Ioi (0 : ℝ) ∈ nhds μx :=
        isOpen_Ioi.mem_nhds hμx_mem_Ioi
      have hball_nhds : (φ ⁻¹' Set.Iio k) ∩ Set.Ioi 0 ∈ nhds μx :=
        Filter.inter_mem hpre_nhds hIoi_nhds
      obtain ⟨ε, hε_pos, hε_subset⟩ :=
        Metric.mem_nhds_iff.mp hball_nhds
      -- Choose `μ' := max (m x) (μx - ε/2)`. Then `m x ≤ μ' < μ x` and
      -- `μ' ∈ ball μx ε`, so `μ' ∈ {φ < k} ∩ Ioi 0`, hence admissible.
      have hε_half_pos : 0 < ε / 2 := by linarith
      set μ' : ℝ := max (m x) (μx - ε / 2) with hμ'def
      have h_μ'_ge_m : m x ≤ μ' := le_max_left _ _
      have h_μ'_lt_μx : μ' < μx := by
        rcases le_or_gt (μx - ε / 2) (m x) with h | h
        · have : μ' = m x := by simp [hμ'def, max_eq_left h]
          rw [this]; exact h_lt
        · have : μ' = μx - ε / 2 := by simp [hμ'def, max_eq_right h.le]
          rw [this]; linarith
      have h_μ'_dist : dist μ' μx < ε := by
        have h_μ'_le_μx : μ' ≤ μx := h_μ'_lt_μx.le
        have h_μ'_gt : μx - ε < μ' := by
          have h1 : μx - ε < μx - ε / 2 := by linarith
          have h2 : μx - ε / 2 ≤ μ' := le_max_right _ _
          linarith
        have hdiff : μx - μ' < ε := by linarith
        have hdist_eq : dist μ' μx = μx - μ' := by
          rw [Real.dist_eq, abs_of_nonpos (by linarith : μ' - μx ≤ 0)]
          ring
        rw [hdist_eq]; exact hdiff
      have h_μ'_in : μ' ∈ (φ ⁻¹' Set.Iio k) ∩ Set.Ioi 0 :=
        hε_subset (by simp [Metric.ball, Set.mem_setOf_eq, h_μ'_dist])
      have hφμ'_lt_k : φ μ' < k := h_μ'_in.1
      have hμ'_pos : (0 : ℝ) < μ' := h_μ'_in.2
      have hHJB_at_μ' : u x + H x (fun i => Du i x) μ' - V x ≤ k := by
        have h1 : φ μ' = u x + H x (fun i => Du i x) μ' - V x := rfl
        rw [h1] at hφμ'_lt_k
        exact hφμ'_lt_k.le
      have h_μ'_mem : μ' ∈ muAuxSet k m u V Du H x :=
        ⟨hμ'_pos.le, h_μ'_ge_m, hHJB_at_μ'⟩
      have h_inf_le_μ' : μx ≤ μ' :=
        csInf_le (muAuxSet_bddBelow k m u V Du H x) h_μ'_mem
      linarith
  · -- m x = μ x. First factor is zero.
    have hzero : μx - m x = 0 := by linarith
    rw [hzero, zero_mul]

/-! ## On-`(0,∞)` product identity assuming only `0 ≤ m x` (δ-truncation route)

The paper's actual argument (`Source/FGU-monotone_revised.tex` lines 1417–1506)
never assumes the solution density is strictly positive — it can vanish on
positive-measure sets (paper lines 375, 1459, 1495). The product identity is
therefore needed assuming only `0 ≤ m x`, with the regularity of
`μ₀ ↦ H(x, Du x, μ₀)` available solely on the **open** half-line `Ioi 0`.

The key observation: in the case `m x < μ x` we automatically have
`0 ≤ m x < μ x`, hence `0 < μ x`, so the continuity/antitonicity argument that
perturbs `μ x` downward stays strictly inside `Ioi 0` (the perturbation is
chosen small enough to remain `> max (m x) 0`, which is `≥ 0`; the perturbed
point lands in `(m x, μ x) ⊆ Ioi 0` because every value strictly above
`m x ≥ 0` is positive). No continuity at the boundary `μ₀ = 0` is required and
`0 < m x` is never assumed. This replaces the abandoned positive-witness route. -/

/-- **Inf-membership of `μ x` when `m x < μ x`**, requiring only **on-`(0,∞)`**
continuity of `H(x, Du x, ·)` and `0 ≤ m x`.

When `m x < μ x = sInf (muAuxSet …)`, the infimum is `> 0`, and the part of the
constraint set near `μ x` lies in `Ioi (m x) ⊆ Ioi 0`. We show `μ x` is itself
a member: it is the limit (from above) of admissible points, all of which lie
in the closed-on-`Ici (m x)` portion of the set; closedness of that portion
(continuity on `Ici (m x) ⊆ Ioi 0`) and `csInf_mem` of the set
`muAuxSet ∩ Ici (m x) = muAuxSet` give membership. -/
lemma muAux_mem_of_m_lt_muAux_of_continuousOn_Ioi
    {k : ℝ} {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {x : Fin d → ℝ} (hmx_nonneg : 0 ≤ m x)
    (hcont :
      ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hne : (muAuxSet k m u V Du H x).Nonempty)
    (hlt : m x < muAux k m u V Du H x) :
    muAux k m u V Du H x ∈ muAuxSet k m u V Du H x := by
  -- The infimum dominates `m x` (every element does), hence is `> m x ≥ 0`.
  have h_lb : m x ≤ muAux k m u V Du H x :=
    le_csInf hne (fun _ hb => hb.2.1)
  have hμx_pos : (0 : ℝ) < muAux k m u V Du H x :=
    lt_of_le_of_lt hmx_nonneg hlt
  -- Every element of `muAuxSet` is `≥ m x ≥ 0`, so the set sits inside
  -- `Ici (m x)`, on which `H(x, Du x, ·)` is continuous (because
  -- `Ici (m x) ⊆ Ioi 0` once `m x` is positive — but here `m x` may be `0`).
  -- The relevant closed envelope: `Ici (m x) ∩ {HJB ≤ k}` is closed on the
  -- portion `≥ μ x`; we use that the inf is positive so the constraint
  -- `0 ≤ μ₀` is automatically inactive near the inf. We rewrite `muAuxSet`
  -- as the intersection with `Ici (m x)` and prove closedness there.
  -- Continuity of the HJB section on `Ioi 0`.
  set φ : ℝ → ℝ := fun t => u x + H x (fun i => Du i x) t - V x with hφdef
  have hφ_contOn : ContinuousOn φ (Set.Ioi 0) :=
    (continuousOn_const.add hcont).sub continuousOn_const
  -- `csInf_mem` route: it suffices to find admissible points converging to
  -- the inf from above, and continuity of `φ` at `μ x ∈ Ioi 0` then forces
  -- `φ (μ x) ≤ k`.  We build it by contradiction exactly as in the
  -- product-identity proof, but only need the membership conclusion here.
  -- First, `μ x` satisfies `0 ≤ μ x` and `m x ≤ μ x`; remaining is HJB.
  refine ⟨hμx_pos.le, h_lb, ?_⟩
  -- Suppose `φ (μ x) > k`. By continuity at `μ x` (interior to `Ioi 0`), `φ`
  -- stays `> k` on a neighbourhood, so no admissible point lies just above
  -- `μ x`, contradicting `μ x = sInf` and `m x < μ x` (which guarantees
  -- admissible points arbitrarily close above the inf).
  by_contra hHJB
  have hHJB' : k < u x + H x (fun i => Du i x) (muAux k m u V Du H x) - V x :=
    lt_of_not_ge hHJB
  have hφμx_gt : k < φ (muAux k m u V Du H x) := by
    simp only [hφdef]; linarith [hHJB']
  -- Continuity of `φ` at `μ x` within `Ioi 0`, upgraded to `ContinuousAt`.
  have hμx_mem_Ioi : muAux k m u V Du H x ∈ Set.Ioi (0 : ℝ) := hμx_pos
  have h_cont_at : ContinuousAt φ (muAux k m u V Du H x) :=
    (hφ_contOn _ hμx_mem_Ioi).continuousAt (isOpen_Ioi.mem_nhds hμx_mem_Ioi)
  have hpre_nhds : φ ⁻¹' Set.Ioi k ∈ nhds (muAux k m u V Du H x) :=
    h_cont_at.preimage_mem_nhds (isOpen_Ioi.mem_nhds hφμx_gt)
  obtain ⟨ε, hε_pos, hε_subset⟩ := Metric.mem_nhds_iff.mp hpre_nhds
  -- `sInf + ε/2` is `> sInf`, so it is not a lower bound: there is an
  -- admissible `b` with `sInf ≤ b < sInf + ε/2`. That `b` lies in the
  -- ε-ball, so `φ b > k`, but admissibility gives `φ b ≤ k`. Contradiction.
  have hbdd : BddBelow (muAuxSet k m u V Du H x) := muAuxSet_bddBelow k m u V Du H x
  have hhalf : 0 < ε / 2 := by linarith
  obtain ⟨b, hb_mem, hb_lt⟩ :=
    Real.lt_sInf_add_pos hne hhalf
  -- `b ≥ sInf = μ x`.
  have hb_ge : muAux k m u V Du H x ≤ b := csInf_le hbdd hb_mem
  -- `dist b (μ x) < ε`.
  have hdist : dist b (muAux k m u V Du H x) < ε := by
    have h1 : b - muAux k m u V Du H x < ε / 2 := by
      have : b < muAux k m u V Du H x + ε / 2 := hb_lt
      linarith
    rw [Real.dist_eq, abs_of_nonneg (by linarith)]
    linarith
  have hb_in : b ∈ φ ⁻¹' Set.Ioi k :=
    hε_subset (by simp only [Metric.mem_ball]; exact hdist)
  have hφb_gt : k < φ b := hb_in
  have hφb_le : φ b ≤ k := by
    have : u x + H x (fun i => Du i x) b - V x ≤ k := hb_mem.2.2
    simpa [hφdef] using this
  linarith

/-! ## On-`(0,∞)` level-set identity assuming only `0 ≤ m x` (δ-truncation route)

The boundary-free level-set identity for the nonnegative-witness route. At a
threshold `a ≥ 0` the equivalence reads

    μ(x) ≤ a ↔ m x ≤ a ∧ (HJB(a) ≤ k ∨ μ(x) ≤ 0)

— the extra disjunct `μ(x) ≤ 0` absorbs the boundary case (`m x = 0` with the
infimum sitting at `0`) without ever evaluating `H(x, Du x, ·)` at the boundary
`μ₀ = 0`. The forward direction uses `muAux_mem_of_m_lt_muAux_of_continuousOn_Ioi`
(membership of the infimum when `m x < μ x`, so `μ x ∈ Ioi 0`) and antitonicity
on `Ioi 0`; the reverse uses `muAux_le_of_mem` (or `μ x ≤ 0 ≤ a`). No boundary
continuity, no `0 < m x`. This is a genuine sibling of the `_of_m_pos` identity. -/
lemma muAux_le_iff_of_antitoneOn_Ioi_of_nonempty_of_m_nonneg
    {k : ℝ} {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {x : Fin d → ℝ} {a : ℝ} (hmx : 0 ≤ m x) (ha : 0 ≤ a)
    (hcont :
      ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hanti :
      AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hne : (muAuxSet k m u V Du H x).Nonempty) :
    muAux k m u V Du H x ≤ a ↔
      m x ≤ a ∧
        (u x + H x (fun i => Du i x) a - V x ≤ k ∨
          muAux k m u V Du H x ≤ 0) := by
  set μx : ℝ := muAux k m u V Du H x with hμxdef
  have h_lb : m x ≤ μx := le_csInf hne (fun _ hb => hb.2.1)
  constructor
  · -- Forward.
    intro hle
    have hmle : m x ≤ a := le_trans h_lb hle
    refine ⟨hmle, ?_⟩
    rcases le_or_gt μx 0 with hμ0 | hμpos
    · exact Or.inr hμ0
    · -- `μ x > 0`. Show `HJB(a) ≤ k`.
      refine Or.inl ?_
      rcases lt_or_eq_of_le h_lb with hlt | heq
      · -- `m x < μ x`: `μ x ∈ muAuxSet`, so HJB(μ x) ≤ k; antitone lifts to a.
        have h_inf_mem : μx ∈ muAuxSet k m u V Du H x :=
          muAux_mem_of_m_lt_muAux_of_continuousOn_Ioi hmx hcont hne hlt
        have hHJB_at_mu :
            u x + H x (fun i => Du i x) μx - V x ≤ k := h_inf_mem.2.2
        have ha_pos : (0 : ℝ) < a := lt_of_lt_of_le hμpos hle
        have hanti_le : H x (fun i => Du i x) a ≤ H x (fun i => Du i x) μx :=
          hanti hμpos ha_pos hle
        linarith
      · -- `m x = μ x > 0`: admissible points lie in `(0, a]` near the inf.
        -- Use `csInf_lt`-style witness when `μ x < a`, and continuity at `a`
        -- when `μ x = a`.
        rcases lt_or_eq_of_le hle with hμlt_a | hμeq_a
        · -- `μ x < a`: choose admissible `b` with `μ x ≤ b < a`, `b > 0`.
          obtain ⟨b, hb_mem, hb_lt⟩ :=
            Real.lt_sInf_add_pos hne
              (show (0 : ℝ) < a - μx by linarith)
          have hb_ge : μx ≤ b := csInf_le (muAuxSet_bddBelow k m u V Du H x) hb_mem
          have hb_lt_a : b < a := by
            have : b < μx + (a - μx) := hb_lt
            linarith
          have hb_pos : (0 : ℝ) < b := lt_of_lt_of_le hμpos hb_ge
          have hHJB_b : u x + H x (fun i => Du i x) b - V x ≤ k := hb_mem.2.2
          have hanti_le : H x (fun i => Du i x) a ≤ H x (fun i => Du i x) b :=
            hanti hb_pos (lt_trans hb_pos hb_lt_a) hb_lt_a.le
          linarith
        · -- `μ x = a`: admissible points `b ↓ μ x` from above; continuity at
          -- `a = μ x > 0` gives `HJB(a) ≤ k`.
          subst hμeq_a
          set φ : ℝ → ℝ := fun t => u x + H x (fun i => Du i x) t - V x with hφdef
          have hφ_contOn : ContinuousOn φ (Set.Ioi 0) :=
            (continuousOn_const.add hcont).sub continuousOn_const
          by_contra hHJB
          have hHJB' : k < φ μx := by
            simp only [hφdef]; linarith [lt_of_not_ge hHJB]
          have hμx_mem_Ioi : μx ∈ Set.Ioi (0 : ℝ) := hμpos
          have h_cont_at : ContinuousAt φ μx :=
            (hφ_contOn _ hμx_mem_Ioi).continuousAt (isOpen_Ioi.mem_nhds hμx_mem_Ioi)
          have hpre_nhds : φ ⁻¹' Set.Ioi k ∈ nhds μx :=
            h_cont_at.preimage_mem_nhds (isOpen_Ioi.mem_nhds hHJB')
          obtain ⟨ε, hε_pos, hε_subset⟩ := Metric.mem_nhds_iff.mp hpre_nhds
          have hhalf : 0 < ε / 2 := by linarith
          obtain ⟨b, hb_mem, hb_lt⟩ := Real.lt_sInf_add_pos hne hhalf
          have hb_ge : μx ≤ b := csInf_le (muAuxSet_bddBelow k m u V Du H x) hb_mem
          have hdist : dist b μx < ε := by
            have h1 : b - μx < ε / 2 := by
              have : b < μx + ε / 2 := hb_lt; linarith
            rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith
          have hb_in : b ∈ φ ⁻¹' Set.Ioi k :=
            hε_subset (by simp only [Metric.mem_ball]; exact hdist)
          have hφb_gt : k < φ b := hb_in
          have hφb_le : φ b ≤ k := by
            have : u x + H x (fun i => Du i x) b - V x ≤ k := hb_mem.2.2
            simpa [hφdef] using this
          linarith
  · -- Reverse.
    rintro ⟨hmle, hdisj⟩
    rcases hdisj with hHJB | hμ0
    · exact muAux_le_of_mem ha hmle hHJB
    · exact le_trans hμ0 ha

/-- **Boundary-free characterization of `{μ ≤ 0}` assuming only `0 ≤ m x`**.

Since `μ ≥ 0`, `μ x ≤ 0 ↔ μ x = 0 ↔ inf = 0`, i.e. admissible points get
arbitrarily close to `0`. Using the up-set structure of `{HJB ≤ k}` (antitone
on `Ioi 0`), a real witness `b` is replaced by a rational `q` in
`[m x, 1/(n+1))` with `HJB(q) ≤ k` — possibly `q = 0` when `m x = 0` and the
infimum is attained at `0`; in that case `HJB(0)` appears, but only as a
*value* (joint measurability of `H` makes the corresponding sublevel set
measurable), never via continuity at the boundary. -/
lemma muAux_le_zero_iff_of_antitoneOn_Ioi_of_m_nonneg
    {k : ℝ} {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {x : Fin d → ℝ} (hmx : 0 ≤ m x)
    (hanti :
      AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hne : (muAuxSet k m u V Du H x).Nonempty) :
    muAux k m u V Du H x ≤ 0 ↔
      ∀ n : ℕ, ∃ q : ℚ,
        m x ≤ (q : ℝ) ∧ 0 ≤ (q : ℝ) ∧ (q : ℝ) < 1 / ((n : ℝ) + 1) ∧
          u x + H x (fun i => Du i x) (q : ℝ) - V x ≤ k := by
  have hpos_denom : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := by
    intro n
    have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    exact div_pos one_pos this
  have hbdd : BddBelow (muAuxSet k m u V Du H x) := muAuxSet_bddBelow k m u V Du H x
  set μx : ℝ := muAux k m u V Du H x with hμxdef
  have hμ_nn : 0 ≤ μx := muAux_nonneg x
  constructor
  · -- `μ x ≤ 0`, hence `μ x = 0 = inf`.
    intro hle
    have hμ0 : μx = 0 := le_antisymm hle hμ_nn
    intro n
    -- `inf = 0 < 1/(n+1)`, so there is an admissible `b < 1/(n+1)`.
    have hlt : sInf (muAuxSet k m u V Du H x) < 1 / ((n : ℝ) + 1) := by
      have : μx < 1 / ((n : ℝ) + 1) := by rw [hμ0]; exact hpos_denom n
      simpa only [hμxdef, muAux] using this
    obtain ⟨b, hb_mem, hb_lt⟩ := exists_lt_of_csInf_lt hne hlt
    -- `b ≥ m x ≥ 0`, `HJB(b) ≤ k`.
    have hb_ge_m : m x ≤ b := hb_mem.2.1
    have hb_nn : 0 ≤ b := hb_mem.1
    have hHJB_b : u x + H x (fun i => Du i x) b - V x ≤ k := hb_mem.2.2
    rcases eq_or_lt_of_le hb_nn with hb0 | hb_pos
    · -- `b = 0`: then `m x ≤ 0`, so `m x = 0`. Use rational `q = 0`.
      refine ⟨(0 : ℚ), ?_, ?_, ?_, ?_⟩
      · push_cast; exact hb_ge_m.trans (le_of_eq hb0.symm)
      · push_cast; exact le_refl (0 : ℝ)
      · push_cast; exact hpos_denom n
      · push_cast; rw [hb0]; exact hHJB_b
    · -- `b > 0`: pick a rational `q ∈ [b, 1/(n+1))` with `HJB(q) ≤ k` (up-set).
      obtain ⟨q, hq_lo, hq_hi⟩ := exists_rat_btwn (show b < 1 / ((n : ℝ) + 1) from hb_lt)
      have hq_pos : (0 : ℝ) < (q : ℝ) := lt_trans hb_pos hq_lo
      have hq_ge_m : m x ≤ (q : ℝ) := le_trans hb_ge_m hq_lo.le
      have hanti_le : H x (fun i => Du i x) (q : ℝ) ≤ H x (fun i => Du i x) b :=
        hanti hb_pos hq_pos hq_lo.le
      refine ⟨q, hq_ge_m, le_of_lt hq_pos, hq_hi, ?_⟩
      linarith
  · -- Conversely: rational admissible points `< 1/(n+1)` force `inf ≤ 0`.
    intro hforall
    have hinf_lt : ∀ n : ℕ, sInf (muAuxSet k m u V Du H x) < 1 / ((n : ℝ) + 1) := by
      intro n
      obtain ⟨q, hq_ge_m, hq_nn, hq_hi, hHJB_q⟩ := hforall n
      have hq_mem : (q : ℝ) ∈ muAuxSet k m u V Du H x := ⟨hq_nn, hq_ge_m, hHJB_q⟩
      exact lt_of_le_of_lt (csInf_le hbdd hq_mem) hq_hi
    have hμ_le : μx ≤ 0 := by
      by_contra hgt
      push_neg at hgt
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hgt
      have hlt := hinf_lt n
      have : μx < 1 / ((n : ℝ) + 1) := by simpa only [hμxdef, muAux] using hlt
      simp only [one_div] at this hn
      linarith
    exact hμ_le

/-- **Pointwise product identity assuming only `0 ≤ m x`** (paper line 1437,
δ-truncation route, lines 1417–1506), requiring only **on-`(0,∞)`** continuity
of `H(x, Du x, ·)`. Never assumes `0 < m x`.

Case split: if `μ x = m x` the first factor is `0`; if `m x < μ x` then
`0 < μ x` and `μ x ∈ muAuxSet`, so HJB holds at `μ x`. If HJB is strict we use
the continuity-on-`Ioi 0` perturbation (staying positive since the perturbed
point is `> m x ≥ 0`) to contradict the infimum, forcing the second factor
to vanish. -/
theorem muAux_product_identity_of_m_nonneg
    {k : ℝ}
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {x : Fin d → ℝ}
    (hmx_nonneg : 0 ≤ m x)
    (hcont :
      ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hne : (muAuxSet k m u V Du H x).Nonempty) :
    (muAux k m u V Du H x - m x) *
      (-k + u x + H x (fun i => Du i x) (muAux k m u V Du H x) - V x) = 0 := by
  set μx : ℝ := muAux k m u V Du H x with hμxdef
  have h_mle_mu : m x ≤ μx := le_csInf hne (fun _ hb => hb.2.1)
  rcases lt_or_eq_of_le h_mle_mu with h_lt | h_eq
  · -- m x < μ x. Then 0 < μ x and `μ x ∈ muAuxSet`. Show second factor is 0.
    have hμx_pos : (0 : ℝ) < μx := lt_of_le_of_lt hmx_nonneg h_lt
    have h_inf_mem : μx ∈ muAuxSet k m u V Du H x :=
      muAux_mem_of_m_lt_muAux_of_continuousOn_Ioi hmx_nonneg hcont hne h_lt
    have hHJB_le : u x + H x (fun i => Du i x) μx - V x ≤ k := h_inf_mem.2.2
    by_contra hne_zero
    have hHJB_lt_or_eq : u x + H x (fun i => Du i x) μx - V x = k ∨
                         u x + H x (fun i => Du i x) μx - V x < k :=
      eq_or_lt_of_le hHJB_le
    rcases hHJB_lt_or_eq with h_eq_k | h_lt_k
    · apply hne_zero
      have h_factor_eq : -k + u x + H x (fun i => Du i x) μx - V x = 0 := by
        linarith
      rw [h_factor_eq, mul_zero]
    · -- strict HJB at `μ x`. Perturb downward staying in `Ioi 0`.
      have h_strict : u x + H x (fun i => Du i x) μx - V x < k := h_lt_k
      set φ : ℝ → ℝ :=
        fun t => u x + H x (fun i => Du i x) t - V x with hφdef
      have hφ_contOn : ContinuousOn φ (Set.Ioi 0) :=
        (continuousOn_const.add hcont).sub continuousOn_const
      have hφμx_lt_k : φ μx < k := h_strict
      have hμx_mem_Ioi : μx ∈ Set.Ioi (0 : ℝ) := hμx_pos
      have h_cont_at' : ContinuousAt φ μx :=
        (hφ_contOn μx hμx_mem_Ioi).continuousAt (isOpen_Ioi.mem_nhds hμx_mem_Ioi)
      have hpre_nhds : φ ⁻¹' Set.Iio k ∈ nhds μx :=
        h_cont_at'.preimage_mem_nhds (isOpen_Iio.mem_nhds hφμx_lt_k)
      have hIoi_nhds : Set.Ioi (0 : ℝ) ∈ nhds μx :=
        isOpen_Ioi.mem_nhds hμx_mem_Ioi
      have hball_nhds : (φ ⁻¹' Set.Iio k) ∩ Set.Ioi 0 ∈ nhds μx :=
        Filter.inter_mem hpre_nhds hIoi_nhds
      obtain ⟨ε, hε_pos, hε_subset⟩ := Metric.mem_nhds_iff.mp hball_nhds
      have hε_half_pos : 0 < ε / 2 := by linarith
      set μ' : ℝ := max (m x) (μx - ε / 2) with hμ'def
      have h_μ'_ge_m : m x ≤ μ' := le_max_left _ _
      have h_μ'_lt_μx : μ' < μx := by
        rcases le_or_gt (μx - ε / 2) (m x) with h | h
        · have : μ' = m x := by simp [hμ'def, max_eq_left h]
          rw [this]; exact h_lt
        · have : μ' = μx - ε / 2 := by simp [hμ'def, max_eq_right h.le]
          rw [this]; linarith
      have h_μ'_dist : dist μ' μx < ε := by
        have h_μ'_le_μx : μ' ≤ μx := h_μ'_lt_μx.le
        have h_μ'_gt : μx - ε < μ' := by
          have h1 : μx - ε < μx - ε / 2 := by linarith
          have h2 : μx - ε / 2 ≤ μ' := le_max_right _ _
          linarith
        have hdiff : μx - μ' < ε := by linarith
        have hdist_eq : dist μ' μx = μx - μ' := by
          rw [Real.dist_eq, abs_of_nonpos (by linarith : μ' - μx ≤ 0)]
          ring
        rw [hdist_eq]; exact hdiff
      have h_μ'_in : μ' ∈ (φ ⁻¹' Set.Iio k) ∩ Set.Ioi 0 :=
        hε_subset (by simp [Metric.ball, Set.mem_setOf_eq, h_μ'_dist])
      have hφμ'_lt_k : φ μ' < k := h_μ'_in.1
      have hμ'_pos : (0 : ℝ) < μ' := h_μ'_in.2
      have hHJB_at_μ' : u x + H x (fun i => Du i x) μ' - V x ≤ k := by
        have h1 : φ μ' = u x + H x (fun i => Du i x) μ' - V x := rfl
        rw [h1] at hφμ'_lt_k
        exact hφμ'_lt_k.le
      have h_μ'_mem : μ' ∈ muAuxSet k m u V Du H x :=
        ⟨hμ'_pos.le, h_μ'_ge_m, hHJB_at_μ'⟩
      have h_inf_le_μ' : μx ≤ μ' :=
        csInf_le (muAuxSet_bddBelow k m u V Du H x) h_μ'_mem
      linarith
  · -- m x = μ x. First factor is zero.
    have hzero : μx - m x = 0 := by linarith
    rw [hzero, zero_mul]

/-- **a.e. version** of `muAux_product_identity_of_m_nonneg` (paper line 1437,
δ-truncation route). Sibling of `muAux_product_identity_of_m_pos`, but with
the strict positivity of `m` replaced by mere nonnegativity. -/
theorem muAux_product_identity_of_m_nonneg_ae
    {k : ℝ}
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    (hae_cont :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hae_ne :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        (muAuxSet k m u V Du H x).Nonempty)
    (hae_m_nn :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      (muAux k m u V Du H x - m x) *
        (-k + u x + H x (fun i => Du i x) (muAux k m u V Du H x) - V x) = 0 := by
  filter_upwards [hae_cont, hae_ne, hae_m_nn] with x hx_cont hx_ne hx_m_nn
  exact muAux_product_identity_of_m_nonneg hx_m_nn hx_cont hx_ne

/-- **Measurability of `μ`** from **on-`[0, ∞)`** pointwise antitonicity and
continuity of `H(x, Du x, ·)` (rather than on all of `ℝ`), plus joint
measurability of `m` and of the HJB constraint set, and pointwise
nonemptiness. Sound because `muAuxSet ⊆ Ici 0`; mirrors `muAux_measurable`. -/
theorem muAux_measurable_of_Ici0
    {k : ℝ} {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    (hm_meas : Measurable m)
    (hHJB_meas : ∀ a : ℝ,
      MeasurableSet { x : Fin d → ℝ |
        u x + H x (fun i => Du i x) a - V x ≤ k })
    (h_anti :
      ∀ x : Fin d → ℝ,
        AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ici 0))
    (h_cont :
      ∀ x : Fin d → ℝ,
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ici 0))
    (h_ne :
      ∀ x : Fin d → ℝ, (muAuxSet k m u V Du H x).Nonempty) :
    Measurable (muAux k m u V Du H) := by
  apply measurable_of_Iic
  intro a
  rcases lt_or_ge a 0 with ha_neg | ha_nn
  · -- a < 0: the set is empty since muAux x ≥ 0 always.
    have hempty : { x : Fin d → ℝ | muAux k m u V Du H x ≤ a } = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hle
      have h_lb : 0 ≤ muAux k m u V Du H x := by
        apply le_csInf (h_ne x)
        intro b hb; exact hb.1
      linarith
    rw [show muAux k m u V Du H ⁻¹' Set.Iic a =
        { x : Fin d → ℝ | muAux k m u V Du H x ≤ a } from rfl, hempty]
    exact MeasurableSet.empty
  · -- a ≥ 0: use the on-`Ici 0` level-set identity.
    have hset_eq :
        { x : Fin d → ℝ | muAux k m u V Du H x ≤ a } =
          { x : Fin d → ℝ | m x ≤ a } ∩
            { x : Fin d → ℝ |
              u x + H x (fun i => Du i x) a - V x ≤ k } := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
      exact muAux_le_iff_of_antitoneOn_of_nonempty
        (k := k) (m := m) (u := u) (V := V) (Du := Du) (H := H)
        (x := x) (a := a) ha_nn (h_cont x) (h_anti x) (h_ne x)
    rw [show muAux k m u V Du H ⁻¹' Set.Iic a =
        { x : Fin d → ℝ | muAux k m u V Du H x ≤ a } from rfl, hset_eq]
    exact (hm_meas measurableSet_Iic).inter (hHJB_meas a)

/-! ## The product identity (paper line 1437, eq. `eq:mu-minus-m-formula`) -/

/-- **Pointwise product identity** (paper line 1437, eq.
`eq:mu-minus-m-formula`).

For almost every `x`, `(μ(x) - m(x))(-k + u(x) + H(x, Du(x), μ(x)) - V(x)) = 0`.

Proof by cases on the first factor:

* If `μ x = m x`, the product is zero. (Always true, no hypothesis used.)
* If `μ x > m x`, then by closedness of the constraint set the inf is
  attained at `μ x`, so HJB at `μ x` holds with `≤ k`. We argue equality
  by contradiction: if `H(x, Du x, μ x) - V x + u x < k`, continuity of
  `H(x, Du x, ·)` gives a smaller value `μ x - ε > m x` still in the
  constraint set, contradicting the infimum.
-/
theorem muAux_product_identity
    {k : ℝ}
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    (hae_cont :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        Continuous (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀))
    (hae_ne :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        (muAuxSet k m u V Du H x).Nonempty)
    (hae_m_nn :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      (muAux k m u V Du H x - m x) *
        (-k + u x + H x (fun i => Du i x) (muAux k m u V Du H x) - V x) = 0 := by
  filter_upwards [hae_cont, hae_ne, hae_m_nn] with x hx_cont hx_ne hx_m_nn
  set μx : ℝ := muAux k m u V Du H x with hμxdef
  -- Case split on m x = μ x vs m x < μ x.
  -- First: m x ≤ μ x (since μ x is in the inf of a set whose elements
  -- are ≥ m x).
  have h_mle_mu : m x ≤ μx := by
    apply le_csInf hx_ne
    intro b hb
    exact hb.2.1
  rcases lt_or_eq_of_le h_mle_mu with h_lt | h_eq
  · -- m x < μ x. Show second factor is zero.
    -- inf is attained: closed + bounded below + non-empty.
    have h_closed : IsClosed (muAuxSet k m u V Du H x) :=
      muAuxSet_isClosed hx_cont
    have h_bdd : BddBelow (muAuxSet k m u V Du H x) :=
      muAuxSet_bddBelow k m u V Du H x
    have h_inf_mem : μx ∈ muAuxSet k m u V Du H x :=
      h_closed.csInf_mem hx_ne h_bdd
    have hHJB_le : u x + H x (fun i => Du i x) μx - V x ≤ k :=
      h_inf_mem.2.2
    -- Show equality (i.e. the second factor `-k + u x + H x ... - V x = 0`)
    -- by contradiction. Suppose strict inequality `< k` (i.e. second factor
    -- < 0). Then by continuity of `H x (Du x) ·` at μ x, there is `ε > 0`
    -- with the constraint still satisfied at `μ x - ε`, contradicting `μ x`
    -- being the infimum.
    by_contra hne_zero
    -- We need: `-k + u x + H x (...) μx - V x = 0`.
    have hHJB_lt_or_eq : u x + H x (fun i => Du i x) μx - V x = k ∨
                         u x + H x (fun i => Du i x) μx - V x < k :=
      eq_or_lt_of_le hHJB_le
    rcases hHJB_lt_or_eq with h_eq_k | h_lt_k
    · -- second factor = 0. So the product is 0, contradicting hne_zero.
      apply hne_zero
      have h_factor_eq : -k + u x + H x (fun i => Du i x) μx - V x = 0 := by
        linarith
      rw [h_factor_eq, mul_zero]
    · -- strict: HJB constraint with strict inequality.
      -- Continuity of H_x at μx ⇒ exists ε > 0 with H stays ≤ k - u + V at μx - ε.
      -- Then μx - ε is in the set, with μx - ε < μx, contradicting inf.
      -- Apply continuity to get an ε.
      have h_strict : u x + H x (fun i => Du i x) μx - V x < k := h_lt_k
      -- Define φ(t) := u x + H x (Du x) t - V x. Continuous in t.
      set φ : ℝ → ℝ :=
        fun t => u x + H x (fun i => Du i x) t - V x with hφdef
      have hφ_cont : Continuous φ :=
        (continuous_const.add hx_cont).sub continuous_const
      have hφμx_lt_k : φ μx < k := h_strict
      -- Find a neighborhood of μx where φ stays < k.
      have h_open : IsOpen (φ ⁻¹' Set.Iio k) :=
        hφ_cont.isOpen_preimage _ isOpen_Iio
      have hμx_in_open : μx ∈ φ ⁻¹' Set.Iio k := hφμx_lt_k
      obtain ⟨ε, hε_pos, hε_subset⟩ :=
        Metric.isOpen_iff.mp h_open μx hμx_in_open
      -- We need a μ' ∈ S strictly less than μx and ≥ m x.
      -- Use μ' := max (μx - ε/2) (m x + ε'/2) for some appropriate ε'.
      -- We need m x ≤ μ' < μx and 0 ≤ μ'.
      -- Choose μ' := max (m x) (μx - ε/2). Then m x ≤ μ' and
      -- if μx - ε/2 ≥ m x then μ' = μx - ε/2 < μx (good). If μx - ε/2 < m x
      -- then μ' = m x < μx (good).
      have hε_half_pos : 0 < ε / 2 := by linarith
      set μ' : ℝ := max (m x) (μx - ε / 2) with hμ'def
      have h_μ'_ge_m : m x ≤ μ' := le_max_left _ _
      have h_μ'_lt_μx : μ' < μx := by
        rcases le_or_gt (μx - ε / 2) (m x) with h | h
        · -- μ' = m x < μx
          have : μ' = m x := by
            simp [hμ'def, max_eq_left h]
          rw [this]; exact h_lt
        · -- μ' = μx - ε/2 < μx
          have : μ' = μx - ε / 2 := by
            simp [hμ'def, max_eq_right h.le]
          rw [this]; linarith
      -- μ' is in the ε-ball around μx (since |μ' - μx| < ε).
      have h_μ'_dist : dist μ' μx < ε := by
        have h_μ'_le_μx : μ' ≤ μx := h_μ'_lt_μx.le
        have h_μ'_gt : μx - ε < μ' := by
          have h1 : μx - ε < μx - ε / 2 := by linarith
          have h2 : μx - ε / 2 ≤ μ' := le_max_right _ _
          linarith
        have hdiff : μx - μ' < ε := by linarith
        have hdiff_nn : 0 ≤ μx - μ' := by linarith
        have hdist_eq : dist μ' μx = μx - μ' := by
          rw [Real.dist_eq, abs_of_nonpos (by linarith : μ' - μx ≤ 0)]
          ring
        rw [hdist_eq]
        exact hdiff
      have h_μ'_in_pre : μ' ∈ φ ⁻¹' Set.Iio k :=
        hε_subset (by simp [Metric.ball, Set.mem_setOf_eq, h_μ'_dist])
      have hφμ'_lt_k : φ μ' < k := h_μ'_in_pre
      have hHJB_at_μ' : u x + H x (fun i => Du i x) μ' - V x ≤ k := by
        have h1 : φ μ' = u x + H x (fun i => Du i x) μ' - V x := rfl
        rw [h1] at hφμ'_lt_k
        exact hφμ'_lt_k.le
      -- 0 ≤ μ': since μ' = max (m x) (μx - ε/2), m x ≥ 0 by hypothesis
      -- gives μ' ≥ m x ≥ 0.
      have h_μ'_nn : 0 ≤ μ' := le_trans hx_m_nn h_μ'_ge_m
      -- Now μ' ∈ muAuxSet and μ' < μx, contradicting μx = sInf.
      have h_μ'_mem : μ' ∈ muAuxSet k m u V Du H x :=
        ⟨h_μ'_nn, h_μ'_ge_m, hHJB_at_μ'⟩
      have h_inf_le_μ' : μx ≤ μ' :=
        csInf_le (muAuxSet_bddBelow k m u V Du H x) h_μ'_mem
      linarith
  · -- m x = μ x (as h_eq : m x = μx). First factor is zero.
    have hzero : μx - m x = 0 := by linarith
    rw [hzero, zero_mul]

end Congestion

end StationaryMFG
