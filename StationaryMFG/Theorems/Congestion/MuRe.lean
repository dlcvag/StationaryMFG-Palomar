module

/-
Copyright (c) 2026 Stationary MFG project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import StationaryMFG.Theorems.Congestion.MuAux
public import StationaryMFG.Theorems.Congestion.MuIntegrability
public import StationaryMFG.Theorems.Congestion.WellDefined
public import StationaryMFG.Theorems.SimplePower.Banach.ExponentFacts

@[expose] public section

/-!
# The redefined auxiliary function `μ_re(x)` (Step 2 of paper Lemma
`lem:weak.is.strong`)

Paper `Source/FGU-monotone_revised.tex`, lines 1480–1497.

After Step 1 (`paper:lem:weak.is.strong.a`, formalised in
`StrongIsStrong.weak_is_strong_HJB_le`) yields
`u + H(·, Du, m) - V ≤ 0` a.e., the proof of the *opposite* inequality
(`eq:congest.HJ0`) builds a *dual* competitor density `μ_re` that is
**smaller** than `m` exactly where `m` fails the lower bound. Concretely,
for a fixed tolerance `k > 0`,

```
μ_re(x) := min{ m(x),
                inf{ μ₀ ∈ ℝ⁺ : u(x) + H(x, Du(x), μ₀) - V(x) ≤ -k }}.
```

This module provides:

* `muReSet` — the constraint set of the *inner* infimum, parameterised by
  `(k, u, V, Du, H)`.
* `muReInner` — the inner infimum `sInf (muReSet …)`.
* `muRe` — the outer minimum with `m`.
* `muRe_le_m` — direct: `μ_re(x) ≤ m(x)`.
* `muRe_nonneg` — under `0 ≤ m`, `0 ≤ μ_re`.
* `muRe_measurable` — measurability under hypotheses mirroring
  `MuAux.muAux_measurable`.
* `muRe_bound_up` — paper eq.~`eq:mu.redef.up` (line 1488):
  `u + H(·, Du, μ_re) - V ≤ 0` a.e., under continuity/antitonicity of
  `H(x, Du x, ·)`, a.e. non-emptiness of the inner set whenever the
  second branch is active, and the Step 1 conclusion
  `u + H(·, Du, m) - V ≤ 0` a.e.

## Paper reference

`Source/FGU-monotone_revised.tex`, eq.~`eq:mu-re.definition`
(line 1483) and eq.~`eq:mu.redef.up` (line 1488).
-/

noncomputable section

namespace StationaryMFG
namespace Congestion

open MeasureTheory Set
open StationaryMFG.Periodic
open scoped Topology

variable {d : ℕ}

/-! ## The inner constraint set and its infimum -/

/-- The constraint set defining the *inner* infimum of `μ_re` (paper
eq.~`eq:mu-re.definition`, line 1483, second branch).

`muReSet k u V Du H x` is the set of admissible `μ₀ ≥ 0` with
`u x + H x (Du x) μ₀ - V x ≤ -k`. Note: unlike `muAuxSet` (Step 1) we
do *not* impose `μ₀ ≥ m x` here — the comparison with `m` is taken
*outside* via `min`. -/
def muReSet
    (k : ℝ)
    (u V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (x : Fin d → ℝ) : Set ℝ :=
  { μ₀ : ℝ | 0 ≤ μ₀ ∧ u x + H x (fun i => Du i x) μ₀ - V x ≤ -k }

lemma mem_muReSet_iff
    {k : ℝ} {u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {x : Fin d → ℝ} {μ₀ : ℝ} :
    μ₀ ∈ muReSet k u V Du H x ↔
      0 ≤ μ₀ ∧ u x + H x (fun i => Du i x) μ₀ - V x ≤ -k := Iff.rfl

/-- The constraint set is bounded below by `0`. -/
lemma muReSet_bddBelow
    (k : ℝ) (u V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (x : Fin d → ℝ) :
    BddBelow (muReSet k u V Du H x) := by
  refine ⟨0, ?_⟩
  intro μ₀ hμ₀
  exact hμ₀.1

/-- The constraint set is closed.

Since `muReSet ⊆ Ici 0`, closedness only requires continuity of
`H(x, Du x, ·)` on `Ici 0` (not all of ℝ): the boundary point `μ₀ = 0`
is the only closure point outside `Ioi 0`, and it lies in `Ici 0`. We
write `muReSet = Ici 0 ∩ {μ₀ | u + H − V ≤ −k}` and show the second
factor is *relatively* closed in `Ici 0`, then intersect with the closed
`Ici 0`. -/
lemma muReSet_isClosed
    {k : ℝ} {u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {x : Fin d → ℝ}
    (hcont : ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀)
      (Set.Ici (0 : ℝ))) :
    IsClosed (muReSet k u V Du H x) := by
  -- `μ₀ ↦ u + H − V` is continuous on `Ici 0`.
  have hc : ContinuousOn
      (fun μ₀ : ℝ => u x + H x (fun i => Du i x) μ₀ - V x) (Set.Ici (0 : ℝ)) :=
    (continuousOn_const.add hcont).sub continuousOn_const
  -- The sublevel set `{u + H − V ≤ −k}` is relatively closed in `Ici 0`,
  -- so its intersection with the closed `Ici 0` is closed in ℝ.
  have h2 : IsClosed
      (Set.Ici (0 : ℝ) ∩ { μ₀ : ℝ | u x + H x (fun i => Du i x) μ₀ - V x ≤ -k }) := by
    have hpre : IsClosed
        (Set.Ici (0 : ℝ) ∩
          (fun μ₀ : ℝ => u x + H x (fun i => Du i x) μ₀ - V x) ⁻¹' Set.Iic (-k)) :=
      hc.preimage_isClosed_of_isClosed isClosed_Ici isClosed_Iic
    have hset :
        (fun μ₀ : ℝ => u x + H x (fun i => Du i x) μ₀ - V x) ⁻¹' Set.Iic (-k)
          = { μ₀ : ℝ | u x + H x (fun i => Du i x) μ₀ - V x ≤ -k } := by
      ext μ₀; simp [Set.mem_preimage, Set.mem_Iic]
    rwa [hset] at hpre
  have hset_eq :
      muReSet k u V Du H x =
        Set.Ici (0 : ℝ) ∩ { μ₀ : ℝ | u x + H x (fun i => Du i x) μ₀ - V x ≤ -k } := by
    ext μ₀; constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2⟩
  rw [hset_eq]
  exact h2

/-- The inner infimum (paper line 1483, inner part of the `min`).

When the inner set is empty, `sInf ∅ = 0` in `ℝ` (the default), but
since the outer `min` with `m x` is taken in `muRe`, the empty case is
benign: `μ_re x = min (m x) 0`, which is still ≤ `m x`. The substantive
analysis only uses `muReInner` when the inner set is non-empty. -/
def muReInner
    (k : ℝ)
    (u V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ) :
    (Fin d → ℝ) → ℝ :=
  fun x => sInf (muReSet k u V Du H x)

lemma muReInner_def
    (k : ℝ) (u V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (x : Fin d → ℝ) :
    muReInner k u V Du H x = sInf (muReSet k u V Du H x) := rfl

/-! ## The redefined auxiliary function `μ_re(x)` -/

/-- The auxiliary function `μ_re(x)` (paper eq.~`eq:mu-re.definition`,
line 1483):

```
μ_re(x) := min{ m(x), inf{ μ₀ ∈ ℝ⁺ : u(x) + H(x, Du(x), μ₀) - V(x) ≤ -k }}.
```
-/
def muRe
    (k : ℝ)
    (m u V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ) :
    (Fin d → ℝ) → ℝ :=
  fun x => min (m x) (muReInner k u V Du H x)

lemma muRe_def
    (k : ℝ) (m u V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (x : Fin d → ℝ) :
    muRe k m u V Du H x = min (m x) (muReInner k u V Du H x) := rfl

/-- `μ_re ≤ m` pointwise (immediate from the outer `min`). -/
lemma muRe_le_m
    (k : ℝ) (m u V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (x : Fin d → ℝ) :
    muRe k m u V Du H x ≤ m x :=
  min_le_left _ _

/-- `μ_re ≤ μ_re_inner` pointwise (the other half of the outer `min`). -/
lemma muRe_le_muReInner
    (k : ℝ) (m u V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (x : Fin d → ℝ) :
    muRe k m u V Du H x ≤ muReInner k u V Du H x :=
  min_le_right _ _

/-- **Periodicity of the `μ_re` constraint set.** If the data `u, V, Du` and the
spatial sections `x ↦ H(x, p, μ₀)` are `ℤ^d`-periodic, then the constraint set
`muReSet k u V Du H x` is invariant under integer-lattice translation of `x`.
Mirrors `MuAux.muAuxSet_periodic` (no `m`-dependence here). -/
lemma muReSet_periodic
    {k : ℝ} {u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    (hu : StationaryMFG.Periodic.IsPeriodic u)
    (hV : StationaryMFG.Periodic.IsPeriodic V)
    (hDu : ∀ i, StationaryMFG.Periodic.IsPeriodic (Du i))
    (hH : ∀ p μ₀, StationaryMFG.Periodic.IsPeriodic (fun x => H x p μ₀))
    (κ : Fin d → ℤ) (x : Fin d → ℝ) :
    muReSet k u V Du H (x + fun i => (κ i : ℝ))
      = muReSet k u V Du H x := by
  have hDu_pt : (fun i => Du i (x + fun i => (κ i : ℝ)))
      = (fun i => Du i x) := by
    funext i; exact hDu i κ x
  ext μ₀
  simp only [mem_muReSet_iff, hu κ x, hV κ x]
  have hHval : H (x + fun i => (κ i : ℝ))
        (fun i => Du i (x + fun i => (κ i : ℝ))) μ₀
      = H x (fun i => Du i x) μ₀ := by
    rw [hDu_pt]
    exact hH (fun i => Du i x) μ₀ κ x
  rw [hHval]

/-- **Periodicity of the inner infimum `μ_re_inner`.** Equal sets have equal
infima. -/
lemma muReInner_periodic
    {k : ℝ} {u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    (hu : StationaryMFG.Periodic.IsPeriodic u)
    (hV : StationaryMFG.Periodic.IsPeriodic V)
    (hDu : ∀ i, StationaryMFG.Periodic.IsPeriodic (Du i))
    (hH : ∀ p μ₀, StationaryMFG.Periodic.IsPeriodic (fun x => H x p μ₀)) :
    StationaryMFG.Periodic.IsPeriodic (muReInner k u V Du H) := by
  intro κ x
  simp only [muReInner_def]
  rw [muReSet_periodic hu hV hDu hH κ x]

/-- **Periodicity of `μ_re = min(m, μ_re_inner)`.** Under periodicity of the data
and the Hamiltonian's spatial sections. -/
lemma muRe_periodic
    {k : ℝ} {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    (hm : StationaryMFG.Periodic.IsPeriodic m)
    (hu : StationaryMFG.Periodic.IsPeriodic u)
    (hV : StationaryMFG.Periodic.IsPeriodic V)
    (hDu : ∀ i, StationaryMFG.Periodic.IsPeriodic (Du i))
    (hH : ∀ p μ₀, StationaryMFG.Periodic.IsPeriodic (fun x => H x p μ₀)) :
    StationaryMFG.Periodic.IsPeriodic (muRe k m u V Du H) := by
  intro κ x
  simp only [muRe_def]
  rw [hm κ x, muReInner_periodic hu hV hDu hH κ x]

/-- Under `0 ≤ m` and non-emptiness of the inner set, the inner infimum
is non-negative (since every member of the set is ≥ 0). -/
lemma muReInner_nonneg_of_nonempty
    {k : ℝ} {u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {x : Fin d → ℝ}
    (hne : (muReSet k u V Du H x).Nonempty) :
    0 ≤ muReInner k u V Du H x := by
  apply le_csInf hne
  intro b hb
  exact hb.1

/-- Under `0 ≤ m x` and a.e. non-emptiness of the inner set, `μ_re ≥ 0`
a.e. -/
lemma muRe_nonneg_ae
    {k : ℝ} {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    (hae_m_nn :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hae_ne :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        (muReSet k u V Du H x).Nonempty) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      0 ≤ muRe k m u V Du H x := by
  filter_upwards [hae_m_nn, hae_ne] with x hx_m_nn hx_ne
  unfold muRe
  exact le_min hx_m_nn (muReInner_nonneg_of_nonempty hx_ne)

/-! ## Non-emptiness of `muReSet` (analog of `muAux_nonempty`)

The `muRe`-side (`≥`-direction) analogue of `MuAux.muAux_nonempty`.  Unlike
`muAuxSet`, `muReSet` imposes **no** `μ₀ ≥ m x` constraint, so its
non-emptiness needs **no** positivity / `m`-comparison: the same large-`μ₀`
construction (driving `H(x, Du x, μ₀) → -∞` via the congestion upper bound
`H ≤ f x - δ·μ₀^β`) lands a feasible witness with `u + H − V ≤ -k`.  The
admissible target shifts from `≤ k` (muAux) to `≤ -k` (muRe), which is
absorbed by enlarging the auxiliary constant `A` by `2k`. -/

/-- **Non-emptiness of the `muRe` constraint set** (paper line 1493, `≥`
direction).  Under the congestion upper bound `H(x, Du x, μ₀) ≤ f x − δ·μ₀^β`
(`δ, β > 0`), the set `muReSet k u V Du H x` is non-empty for a.e. `x`.

Mirrors `MuAux.muAux_nonempty`; no `0 ≤ m x` / positivity hypothesis is
needed because `muReSet` drops the `μ₀ ≥ m x` requirement. -/
theorem muRe_nonempty
    {k : ℝ}
    {u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {β δ : ℝ} (hβ : 0 < β) (hδ : 0 < δ)
    {f : (Fin d → ℝ) → ℝ}
    (hbound :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ μ₀, 0 < μ₀ →
          H x (fun i => Du i x) μ₀ ≤ f x - δ * μ₀ ^ β) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      (muReSet k u V Du H x).Nonempty := by
  filter_upwards [hbound] with x hbx
  -- Auxiliary constant: shifted by `+ k` (vs `- k` in muAux) to hit `≤ -k`.
  set A : ℝ := f x + u x - V x + k with hAdef
  rcases le_or_gt A 0 with hA_le | hA_pos
  · -- `A ≤ 0`: even `μ₀ = 1` works (any positive value gives `≤ -k`).
    refine ⟨1, le_of_lt one_pos, ?_⟩
    have hHbd : H x (fun i => Du i x) 1 ≤ f x - δ * (1 : ℝ) ^ β := hbx 1 one_pos
    have hδ1β_nn : 0 ≤ δ * (1 : ℝ) ^ β :=
      mul_nonneg hδ.le (Real.rpow_nonneg zero_le_one β)
    have h2 : u x + (f x - δ * (1 : ℝ) ^ β) - V x = A - k - δ * (1 : ℝ) ^ β := by
      rw [hAdef]; ring
    -- `u + H − V ≤ u + (f − δ) − V = A − k − δ ≤ -k`.
    have : u x + H x (fun i => Du i x) 1 - V x ≤ -k := by
      have := hHbd; linarith
    exact this
  · -- `A > 0`: take `μ₀` large enough that `δ·μ₀^β ≥ A`.
    have hAdiv_pos : 0 < A / δ := div_pos hA_pos hδ
    set T : ℝ := (A / δ) ^ (1 / β) + 1 with hTdef
    have hT_pos_aux : 0 < (A / δ) ^ (1 / β) :=
      Real.rpow_pos_of_pos hAdiv_pos (1 / β)
    have hT_pos : 0 < T := by linarith
    refine ⟨T, hT_pos.le, ?_⟩
    have hHbd : H x (fun i => Du i x) T ≤ f x - δ * T ^ β := hbx T hT_pos
    have h_T_lt : (A / δ) ^ (1 / β) < T := by linarith
    have h_pow_eq : ((A / δ) ^ (1 / β)) ^ β = A / δ := by
      have hAdiv_nn : 0 ≤ A / δ := hAdiv_pos.le
      rw [← Real.rpow_mul hAdiv_nn]
      have h_one : (1 / β) * β = 1 := by field_simp
      rw [h_one, Real.rpow_one]
    have h_pow_le : ((A / δ) ^ (1 / β)) ^ β ≤ T ^ β :=
      Real.rpow_le_rpow hT_pos_aux.le h_T_lt.le hβ.le
    have hTβ_ge : A / δ ≤ T ^ β := by rw [← h_pow_eq]; exact h_pow_le
    have hδTβ_ge : A ≤ δ * T ^ β := by
      have h2 : A = δ * (A / δ) := by field_simp
      rw [h2]
      exact mul_le_mul_of_nonneg_left hTβ_ge hδ.le
    have h2 : u x + (f x - δ * T ^ β) - V x = A - k - δ * T ^ β := by
      rw [hAdef]; ring
    have : u x + H x (fun i => Du i x) T - V x ≤ -k := by linarith
    exact this

/-- **Non-emptiness companion for the large-`μ₀` regime** (`muRe`-side analog
of `MuAux.muAux_nonempty_of_large_bound`).  The congestion upper bound is
required only for `μ₀ ≥ 1`; the witness constructed is always `≥ 1`. -/
theorem muRe_nonempty_of_large_bound
    {k : ℝ}
    {u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {β δ : ℝ} (hβ : 0 < β) (hδ : 0 < δ)
    {f : (Fin d → ℝ) → ℝ}
    (hbound :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ μ₀, 1 ≤ μ₀ →
          H x (fun i => Du i x) μ₀ ≤ f x - δ * μ₀ ^ β) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      (muReSet k u V Du H x).Nonempty := by
  filter_upwards [hbound] with x hbx
  set A : ℝ := f x + u x - V x + k with hAdef
  rcases le_or_gt A 0 with hA_le | hA_pos
  · refine ⟨1, le_of_lt one_pos, ?_⟩
    have hHbd : H x (fun i => Du i x) 1 ≤ f x - δ * (1 : ℝ) ^ β := hbx 1 le_rfl
    have hδ1β_nn : 0 ≤ δ * (1 : ℝ) ^ β :=
      mul_nonneg hδ.le (Real.rpow_nonneg zero_le_one β)
    have h2 : u x + (f x - δ * (1 : ℝ) ^ β) - V x = A - k - δ * (1 : ℝ) ^ β := by
      rw [hAdef]; ring
    have : u x + H x (fun i => Du i x) 1 - V x ≤ -k := by linarith
    exact this
  · have hAdiv_pos : 0 < A / δ := div_pos hA_pos hδ
    -- The witness is `max 1 ((A/δ)^{1/β} + 1) ≥ 1`.
    set T : ℝ := max 1 ((A / δ) ^ (1 / β) + 1) with hTdef
    have hT_ge_one : 1 ≤ T := le_max_left _ _
    have hT_pos : 0 < T := lt_of_lt_of_le one_pos hT_ge_one
    have hT_ge_aux : (A / δ) ^ (1 / β) + 1 ≤ T := le_max_right _ _
    have hT_pos_aux : 0 < (A / δ) ^ (1 / β) :=
      Real.rpow_pos_of_pos hAdiv_pos (1 / β)
    refine ⟨T, hT_pos.le, ?_⟩
    have hHbd : H x (fun i => Du i x) T ≤ f x - δ * T ^ β := hbx T hT_ge_one
    have h_T_lt : (A / δ) ^ (1 / β) < T := by linarith
    have h_pow_eq : ((A / δ) ^ (1 / β)) ^ β = A / δ := by
      have hAdiv_nn : 0 ≤ A / δ := hAdiv_pos.le
      rw [← Real.rpow_mul hAdiv_nn]
      have h_one : (1 / β) * β = 1 := by field_simp
      rw [h_one, Real.rpow_one]
    have h_pow_le : ((A / δ) ^ (1 / β)) ^ β ≤ T ^ β :=
      Real.rpow_le_rpow hT_pos_aux.le h_T_lt.le hβ.le
    have hTβ_ge : A / δ ≤ T ^ β := by rw [← h_pow_eq]; exact h_pow_le
    have hδTβ_ge : A ≤ δ * T ^ β := by
      have h2 : A = δ * (A / δ) := by field_simp
      rw [h2]
      exact mul_le_mul_of_nonneg_left hTβ_ge hδ.le
    have h2 : u x + (f x - δ * T ^ β) - V x = A - k - δ * T ^ β := by
      rw [hAdef]; ring
    have : u x + H x (fun i => Du i x) T - V x ≤ -k := by linarith
    exact this

/-! ## Measurability of `μ_re` (analog of `muAux_measurable`) -/

/-- Reverse inclusion of the level-set identity for `muReInner`. -/
lemma muReInner_le_of_mem
    {k : ℝ} {u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {x : Fin d → ℝ} {a : ℝ}
    (ha : 0 ≤ a)
    (hHJB : u x + H x (fun i => Du i x) a - V x ≤ -k) :
    muReInner k u V Du H x ≤ a := by
  apply csInf_le (muReSet_bddBelow k u V Du H x)
  exact ⟨ha, hHJB⟩

/-- Forward inclusion under continuity, antitonicity of `H(x, Du x, ·)`,
and non-emptiness. -/
lemma muReInner_le_iff_of_antitone_of_nonempty
    {k : ℝ} {u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {x : Fin d → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hcont :
      ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ici 0))
    (hanti :
      AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ici 0))
    (hne : (muReSet k u V Du H x).Nonempty) :
    muReInner k u V Du H x ≤ a ↔
      u x + H x (fun i => Du i x) a - V x ≤ -k := by
  refine ⟨fun hle => ?_, fun hHJB => muReInner_le_of_mem ha hHJB⟩
  -- Forward direction.
  have h_closed : IsClosed (muReSet k u V Du H x) :=
    muReSet_isClosed hcont
  have h_bdd : BddBelow (muReSet k u V Du H x) :=
    muReSet_bddBelow k u V Du H x
  have h_inf_mem :
      sInf (muReSet k u V Du H x) ∈ muReSet k u V Du H x :=
    h_closed.csInf_mem hne h_bdd
  -- The infimum is nonnegative (every element of the set is).
  have h_inf_nn : (0 : ℝ) ≤ sInf (muReSet k u V Du H x) := h_inf_mem.1
  have hHJB_at_inf :
      u x + H x (fun i => Du i x) (sInf (muReSet k u V Du H x)) - V x
        ≤ -k := h_inf_mem.2
  -- Antitonicity on `Ici 0`: inf ≤ a ⇒ H(...,a) ≤ H(...,inf), with both
  -- arguments in `Ici 0`.
  have hanti_le : H x (fun i => Du i x) a
                  ≤ H x (fun i => Du i x) (sInf (muReSet k u V Du H x)) :=
    hanti h_inf_nn ha hle
  linarith

/-! ## Boundary-free `muReInner`/`muRe` level sets (δ-truncation route)

The `μ_re`-side analogues of the `muAux` boundary-free level-set lemmas
(`MuAux.muAux_le_iff_of_antitoneOn_Ioi_of_nonempty_of_m_nonneg`,
`MuAux.muAux_le_zero_iff_of_antitoneOn_Ioi_of_m_nonneg`). They characterise
the sublevel sets of `muReInner` (and hence of `muRe = min(m, muReInner)`)
using only **on-`(0,∞)`** continuity / antitonicity of `H(x, Du x, ·)`,
never evaluating `H` at the boundary `μ₀ = 0` through continuity — the
boundary enters only through the measurable *value* `H(x, Du x, q)` at
rational `q` (including `q = 0`). These feed the AEMeasurable route
`muRe_measurable_of_Ioi0_of_m_nonneg_aesm`, the `μ_re`-side sibling of
`MuIntegrability.muAux_measurable_of_Ioi0_of_m_nonneg_aesm`. -/

/-- Membership of the inner infimum when it is **strictly positive**, using
only continuity of `H(x, Du x, ·)` on `Ioi 0`. (Mirrors
`MuAux.muAux_mem_of_m_lt_muAux_of_continuousOn_Ioi`.) -/
lemma muReInner_mem_of_pos_of_continuousOn_Ioi
    {k : ℝ} {u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {x : Fin d → ℝ}
    (hcont :
      ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hne : (muReSet k u V Du H x).Nonempty)
    (hpos : 0 < muReInner k u V Du H x) :
    muReInner k u V Du H x ∈ muReSet k u V Du H x := by
  set μx : ℝ := muReInner k u V Du H x with hμxdef
  set φ : ℝ → ℝ := fun t => u x + H x (fun i => Du i x) t - V x with hφdef
  have hφ_contOn : ContinuousOn φ (Set.Ioi 0) :=
    (continuousOn_const.add hcont).sub continuousOn_const
  refine ⟨hpos.le, ?_⟩
  by_contra hHJB
  have hHJB' : -k < u x + H x (fun i => Du i x) μx - V x := lt_of_not_ge hHJB
  have hφμx_gt : -k < φ μx := by simp only [hφdef]; linarith
  have hμx_mem_Ioi : μx ∈ Set.Ioi (0 : ℝ) := hpos
  have h_cont_at : ContinuousAt φ μx :=
    (hφ_contOn _ hμx_mem_Ioi).continuousAt (isOpen_Ioi.mem_nhds hμx_mem_Ioi)
  have hpre_nhds : φ ⁻¹' Set.Ioi (-k) ∈ nhds μx :=
    h_cont_at.preimage_mem_nhds (isOpen_Ioi.mem_nhds hφμx_gt)
  obtain ⟨ε, hε_pos, hε_subset⟩ := Metric.mem_nhds_iff.mp hpre_nhds
  have hbdd : BddBelow (muReSet k u V Du H x) := muReSet_bddBelow k u V Du H x
  have hhalf : 0 < ε / 2 := by linarith
  obtain ⟨b, hb_mem, hb_lt⟩ := Real.lt_sInf_add_pos hne hhalf
  have hb_ge : μx ≤ b := csInf_le hbdd hb_mem
  have hdist : dist b μx < ε := by
    have h1 : b - μx < ε / 2 := by
      have : b < μx + ε / 2 := hb_lt; linarith
    rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith
  have hb_in : b ∈ φ ⁻¹' Set.Ioi (-k) :=
    hε_subset (by simp only [Metric.mem_ball]; exact hdist)
  have hφb_gt : -k < φ b := hb_in
  have hφb_le : φ b ≤ -k := by
    have : u x + H x (fun i => Du i x) b - V x ≤ -k := hb_mem.2
    simpa [hφdef] using this
  linarith

/-- **Boundary-free `{muReInner ≤ 0}` characterization**, using only
antitonicity of `H(x, Du x, ·)` on `Ioi 0`. (Mirrors
`MuAux.muAux_le_zero_iff_of_antitoneOn_Ioi_of_m_nonneg`.) -/
lemma muReInner_le_zero_iff_of_antitoneOn_Ioi
    {k : ℝ} {u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {x : Fin d → ℝ}
    (hanti :
      AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hne : (muReSet k u V Du H x).Nonempty) :
    muReInner k u V Du H x ≤ 0 ↔
      ∀ n : ℕ, ∃ q : ℚ,
        0 ≤ (q : ℝ) ∧ (q : ℝ) < 1 / ((n : ℝ) + 1) ∧
          u x + H x (fun i => Du i x) (q : ℝ) - V x ≤ -k := by
  have hpos_denom : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := by
    intro n
    have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    exact div_pos one_pos this
  have hbdd : BddBelow (muReSet k u V Du H x) := muReSet_bddBelow k u V Du H x
  set μx : ℝ := muReInner k u V Du H x with hμxdef
  have hμ_nn : 0 ≤ μx := muReInner_nonneg_of_nonempty hne
  constructor
  · -- `muReInner ≤ 0`, hence `= 0 = inf`.
    intro hle
    have hμ0 : μx = 0 := le_antisymm hle hμ_nn
    intro n
    have hlt : sInf (muReSet k u V Du H x) < 1 / ((n : ℝ) + 1) := by
      have : μx < 1 / ((n : ℝ) + 1) := by rw [hμ0]; exact hpos_denom n
      simpa only [hμxdef, muReInner] using this
    obtain ⟨b, hb_mem, hb_lt⟩ := exists_lt_of_csInf_lt hne hlt
    have hb_nn : 0 ≤ b := hb_mem.1
    have hHJB_b : u x + H x (fun i => Du i x) b - V x ≤ -k := hb_mem.2
    rcases eq_or_lt_of_le hb_nn with hb0 | hb_pos
    · -- `b = 0`: use rational `q = 0`.
      refine ⟨(0 : ℚ), ?_, ?_, ?_⟩
      · push_cast; exact le_refl (0 : ℝ)
      · push_cast; exact hpos_denom n
      · push_cast; rw [hb0]; exact hHJB_b
    · -- `b > 0`: pick a rational `q ∈ [b, 1/(n+1))`; antitone lifts HJB to `q`.
      obtain ⟨q, hq_lo, hq_hi⟩ :=
        exists_rat_btwn (show b < 1 / ((n : ℝ) + 1) from hb_lt)
      have hq_pos : (0 : ℝ) < (q : ℝ) := lt_trans hb_pos hq_lo
      have hanti_le : H x (fun i => Du i x) (q : ℝ) ≤ H x (fun i => Du i x) b :=
        hanti hb_pos hq_pos hq_lo.le
      refine ⟨q, le_of_lt hq_pos, hq_hi, ?_⟩
      linarith
  · -- Conversely: rational admissible points `< 1/(n+1)` force `inf ≤ 0`.
    intro hforall
    have hinf_lt :
        ∀ n : ℕ, sInf (muReSet k u V Du H x) < 1 / ((n : ℝ) + 1) := by
      intro n
      obtain ⟨q, hq_nn, hq_hi, hHJB_q⟩ := hforall n
      have hq_mem : (q : ℝ) ∈ muReSet k u V Du H x := ⟨hq_nn, hHJB_q⟩
      exact lt_of_le_of_lt (csInf_le hbdd hq_mem) hq_hi
    have hμ_le : μx ≤ 0 := by
      by_contra hgt
      push_neg at hgt
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hgt
      have hlt := hinf_lt n
      have : μx < 1 / ((n : ℝ) + 1) := by simpa only [hμxdef, muReInner] using hlt
      simp only [one_div] at this hn
      linarith
    exact hμ_le

/-- **Boundary-free `muReInner` level-set identity** at a nonnegative
threshold `a`, using only on-`(0,∞)` continuity and antitonicity. (Mirrors
`MuAux.muAux_le_iff_of_antitoneOn_Ioi_of_nonempty_of_m_nonneg`.) -/
lemma muReInner_le_iff_of_antitoneOn_Ioi_of_nonempty
    {k : ℝ} {u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {x : Fin d → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hcont :
      ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hanti :
      AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hne : (muReSet k u V Du H x).Nonempty) :
    muReInner k u V Du H x ≤ a ↔
      u x + H x (fun i => Du i x) a - V x ≤ -k ∨
        muReInner k u V Du H x ≤ 0 := by
  set μx : ℝ := muReInner k u V Du H x with hμxdef
  constructor
  · -- Forward.
    intro hle
    rcases le_or_gt μx 0 with hμ0 | hμpos
    · exact Or.inr hμ0
    · -- `μx > 0`. Show `HJB(a) ≤ -k`.
      refine Or.inl ?_
      -- `μx ∈ muReSet`, so HJB(μx) ≤ -k.
      have h_inf_mem : μx ∈ muReSet k u V Du H x :=
        muReInner_mem_of_pos_of_continuousOn_Ioi hcont hne hμpos
      have hHJB_at_mu : u x + H x (fun i => Du i x) μx - V x ≤ -k := h_inf_mem.2
      have ha_pos : (0 : ℝ) < a := lt_of_lt_of_le hμpos hle
      have hanti_le : H x (fun i => Du i x) a ≤ H x (fun i => Du i x) μx :=
        hanti hμpos ha_pos hle
      linarith
  · -- Reverse.
    rintro (hHJB | hμ0)
    · exact muReInner_le_of_mem ha hHJB
    · exact le_trans hμ0 ha

/-- **Boundary-free `muRe` level-set identity** at a nonnegative threshold
`a`, via the outer `min`: `muRe x ≤ a ↔ m x ≤ a ∨ muReInner x ≤ a`. -/
lemma muRe_le_iff_of_antitoneOn_Ioi_of_nonempty
    {k : ℝ} {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {x : Fin d → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hcont :
      ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hanti :
      AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hne : (muReSet k u V Du H x).Nonempty) :
    muRe k m u V Du H x ≤ a ↔
      m x ≤ a ∨
        (u x + H x (fun i => Du i x) a - V x ≤ -k ∨
          muReInner k u V Du H x ≤ 0) := by
  rw [muRe, min_le_iff,
    muReInner_le_iff_of_antitoneOn_Ioi_of_nonempty ha hcont hanti hne]

/-- **AEMeasurability of `μ_re` from a.e. on-`(0,∞)` data** — the `μ_re`-side
sibling of `MuIntegrability.muAux_measurable_of_Ioi0_of_m_nonneg_aesm`.

Conclusion `AEMeasurable (muRe …)` from a.e. (not pointwise-everywhere)
antitonicity / continuity on `Ioi 0`, a.e. nonemptiness, and a.e.
nonnegativity of `m`. The boundary value `H(x, Du x, 0)` is never assumed
continuous; it enters only as the measurable value through the rational
sublevel sets `hHJB_nmeas q` (incl. `q = 0`). Uses the boundary-free
level-set identity `muRe_le_iff_of_antitoneOn_Ioi_of_nonempty` together with
`muReInner_le_zero_iff_of_antitoneOn_Ioi`, concluding via
`aemeasurable_of_nullMeasurable_Iic_rat`. NO `Set.Ici 0`, NO `Measurable V`,
NO `∀ x` pointwise rider, NO boundary continuity. -/
theorem muRe_measurable_of_Ioi0_of_m_nonneg_aesm
    {k : ℝ} {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    (hm_meas : Measurable m)
    (hHJB_nmeas : ∀ a : ℝ,
      NullMeasurableSet { x : Fin d → ℝ |
        u x + H x (fun i => Du i x) a - V x ≤ -k } (volume.restrict (UnitCube d)))
    (hae_m_nn :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hae_anti :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hae_cont :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hae_ne :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        (muReSet k u V Du H x).Nonempty) :
    AEMeasurable (muRe k m u V Du H) (volume.restrict (UnitCube d)) := by
  classical
  set μm : Measure (Fin d → ℝ) := volume.restrict (UnitCube d) with hμmdef
  -- Bad set: nonnegativity ∩ antitonicity ∩ continuity ∩ nonemptiness fail.
  set B₁ : Set (Fin d → ℝ) := toMeasurable μm { x | ¬ (0 ≤ m x) } with hB₁
  set B₂ : Set (Fin d → ℝ) :=
    toMeasurable μm
      { x | ¬ AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0) }
    with hB₂
  set B₃ : Set (Fin d → ℝ) :=
    toMeasurable μm
      { x | ¬ ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀)
        (Set.Ioi 0) } with hB₃
  set B₄ : Set (Fin d → ℝ) :=
    toMeasurable μm { x | ¬ (muReSet k u V Du H x).Nonempty } with hB₄
  set Bad : Set (Fin d → ℝ) := B₁ ∪ B₂ ∪ B₃ ∪ B₄ with hBad
  have hB₁_meas : MeasurableSet B₁ := measurableSet_toMeasurable _ _
  have hB₂_meas : MeasurableSet B₂ := measurableSet_toMeasurable _ _
  have hB₃_meas : MeasurableSet B₃ := measurableSet_toMeasurable _ _
  have hB₄_meas : MeasurableSet B₄ := measurableSet_toMeasurable _ _
  have hBad_meas : MeasurableSet Bad :=
    ((hB₁_meas.union hB₂_meas).union hB₃_meas).union hB₄_meas
  have hB₁_null : μm B₁ = 0 := by
    rw [hB₁, measure_toMeasurable]; simpa using (ae_iff.mp hae_m_nn)
  have hB₂_null : μm B₂ = 0 := by
    rw [hB₂, measure_toMeasurable]; simpa using (ae_iff.mp hae_anti)
  have hB₃_null : μm B₃ = 0 := by
    rw [hB₃, measure_toMeasurable]; simpa using (ae_iff.mp hae_cont)
  have hB₄_null : μm B₄ = 0 := by
    rw [hB₄, measure_toMeasurable]; simpa using (ae_iff.mp hae_ne)
  have hBad_null : μm Bad = 0 := by
    have h12 : μm (B₁ ∪ B₂) = 0 := measure_union_null hB₁_null hB₂_null
    have h123 : μm (B₁ ∪ B₂ ∪ B₃) = 0 := measure_union_null h12 hB₃_null
    exact measure_union_null h123 hB₄_null
  have hgood : ∀ x ∈ Badᶜ,
      0 ≤ m x ∧
      AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0) ∧
      ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0) ∧
      (muReSet k u V Du H x).Nonempty := by
    intro x hx
    simp only [hBad, Set.mem_compl_iff, Set.mem_union, not_or] at hx
    obtain ⟨⟨⟨hx1, hx2⟩, hx3⟩, hx4⟩ := hx
    refine ⟨?_, ?_, ?_, ?_⟩
    · by_contra h; exact hx1 (subset_toMeasurable _ _ h)
    · by_contra h; exact hx2 (subset_toMeasurable _ _ h)
    · by_contra h; exact hx3 (subset_toMeasurable _ _ h)
    · by_contra h; exact hx4 (subset_toMeasurable _ _ h)
  -- The boundary-free `{muReInner ≤ 0}` set, expressed measurably.
  set Z : Set (Fin d → ℝ) :=
    { x : Fin d → ℝ | ∀ n : ℕ, ∃ q : ℚ,
        0 ≤ (q : ℝ) ∧ (q : ℝ) < 1 / ((n : ℝ) + 1) ∧
          u x + H x (fun i => Du i x) (q : ℝ) - V x ≤ -k } with hZdef
  have hZ_nmeas : NullMeasurableSet Z μm := by
    have hZ_eq : Z =
        ⋂ n : ℕ, ⋃ q : ℚ,
          ({ x : Fin d → ℝ |
              0 ≤ (q : ℝ) ∧ (q : ℝ) < 1 / ((n : ℝ) + 1) } ∩
            { x : Fin d → ℝ |
              u x + H x (fun i => Du i x) (q : ℝ) - V x ≤ -k }) := by
      ext x
      simp only [hZdef, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion,
        Set.mem_inter_iff]
      constructor
      · intro h n
        obtain ⟨q, h1, h2, h3⟩ := h n
        exact ⟨q, ⟨h1, h2⟩, h3⟩
      · intro h n
        obtain ⟨q, ⟨h1, h2⟩, h3⟩ := h n
        exact ⟨q, h1, h2, h3⟩
    rw [hZ_eq]
    refine NullMeasurableSet.iInter (fun n => ?_)
    refine NullMeasurableSet.iUnion (fun q => ?_)
    have hmid : NullMeasurableSet
        { x : Fin d → ℝ | 0 ≤ (q : ℝ) ∧ (q : ℝ) < 1 / ((n : ℝ) + 1) } μm := by
      by_cases hcond : 0 ≤ (q : ℝ) ∧ (q : ℝ) < 1 / ((n : ℝ) + 1)
      · have : { x : Fin d → ℝ | 0 ≤ (q : ℝ) ∧ (q : ℝ) < 1 / ((n : ℝ) + 1) }
            = Set.univ := by
          ext x; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]; exact hcond
        rw [this]; exact MeasurableSet.univ.nullMeasurableSet
      · have : { x : Fin d → ℝ | 0 ≤ (q : ℝ) ∧ (q : ℝ) < 1 / ((n : ℝ) + 1) }
            = (∅ : Set (Fin d → ℝ)) := by
          ext x; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          exact hcond
        rw [this]; exact MeasurableSet.empty.nullMeasurableSet
    exact hmid.inter (hHJB_nmeas (q : ℝ))
  -- On `Badᶜ`, `Z` agrees with `{muReInner ≤ 0}`.
  have hZ_level : ∀ x ∈ Badᶜ,
      (x ∈ Z ↔ muReInner k u V Du H x ≤ 0) := by
    intro x hx
    obtain ⟨_, hx_anti, _, hx_ne⟩ := hgood x hx
    rw [hZdef, Set.mem_setOf_eq,
      muReInner_le_zero_iff_of_antitoneOn_Ioi hx_anti hx_ne]
  -- The `{muReInner ≤ q}` set, sign-guarded so it is genuinely empty at
  -- `q < 0` (where `muReInner ≥ 0 > q`).  `Iq q := {0 ≤ q} ∩ ({HJB(q) ≤ -k} ∪ Z)`.
  set Iq : ℚ → Set (Fin d → ℝ) := fun q =>
    { _x : Fin d → ℝ | (0 : ℝ) ≤ (q : ℝ) } ∩
      (({ y : Fin d → ℝ |
          u y + H y (fun i => Du i y) (q : ℝ) - V y ≤ -k }) ∪ Z) with hIqdef
  have hIq_level : ∀ q : ℚ, ∀ x ∈ Badᶜ,
      (muReInner k u V Du H x ≤ (q : ℝ) ↔ x ∈ Iq q) := by
    intro q x hx
    obtain ⟨_, hx_anti, hx_cont, hx_ne⟩ := hgood x hx
    have hinner_nn : 0 ≤ muReInner k u V Du H x :=
      muReInner_nonneg_of_nonempty hx_ne
    rcases lt_or_ge (q : ℝ) 0 with hq_neg | hq_nn
    · -- `q < 0`: both sides false (inner ≥ 0 > q; `Iq` needs `0 ≤ q`).
      constructor
      · intro hle; exact absurd (le_trans hinner_nn hle) (by linarith)
      · intro hmem
        have : (0 : ℝ) ≤ (q : ℝ) := hmem.1
        linarith
    · -- `q ≥ 0`: boundary-free inner level-set identity.
      rw [muReInner_le_iff_of_antitoneOn_Ioi_of_nonempty hq_nn hx_cont hx_anti hx_ne]
      simp only [hIqdef, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_union]
      constructor
      · rintro (hHJB | hμ0)
        · exact ⟨hq_nn, Or.inl hHJB⟩
        · exact ⟨hq_nn, Or.inr ((hZ_level x hx).2 hμ0)⟩
      · rintro ⟨_, hHJB | hZmem⟩
        · exact Or.inl hHJB
        · exact Or.inr ((hZ_level x hx).1 hZmem)
  -- The level-set identity for `μ_re` on the good set, via the outer `min`.
  have hlevel : ∀ q : ℚ, ∀ x ∈ Badᶜ,
      (muRe k m u V Du H x ≤ (q : ℝ) ↔
        x ∈ ({ y : Fin d → ℝ | m y ≤ (q : ℝ) } ∪ Iq q)) := by
    intro q x hx
    rw [muRe, min_le_iff]
    simp only [Set.mem_union, Set.mem_setOf_eq]
    rw [hIq_level q x hx]
  -- For each rational `q`, the level set `μ_re⁻¹(Iic q)` is null-measurable.
  refine aemeasurable_of_nullMeasurable_Iic_rat (fun q => ?_)
  set Lq : Set (Fin d → ℝ) :=
    ({ y : Fin d → ℝ | m y ≤ (q : ℝ) } ∪ Iq q) with hLq
  have hIq_nmeas : NullMeasurableSet (Iq q) μm := by
    have hguard : NullMeasurableSet
        { _x : Fin d → ℝ | (0 : ℝ) ≤ (q : ℝ) } μm := by
      by_cases hcond : (0 : ℝ) ≤ (q : ℝ)
      · have : { _x : Fin d → ℝ | (0 : ℝ) ≤ (q : ℝ) } = Set.univ := by
          ext x; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]; exact hcond
        rw [this]; exact MeasurableSet.univ.nullMeasurableSet
      · have : { _x : Fin d → ℝ | (0 : ℝ) ≤ (q : ℝ) } = (∅ : Set (Fin d → ℝ)) := by
          ext x; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          exact hcond
        rw [this]; exact MeasurableSet.empty.nullMeasurableSet
    rw [hIqdef]
    exact hguard.inter ((hHJB_nmeas (q : ℝ)).union hZ_nmeas)
  have hLq_nmeas : NullMeasurableSet Lq μm := by
    rw [hLq]
    exact (hm_meas measurableSet_Iic).nullMeasurableSet.union hIq_nmeas
  have hpre_inter :
      (muRe k m u V Du H ⁻¹' Set.Iic (q : ℝ)) ∩ Badᶜ = Lq ∩ Badᶜ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic]
    constructor
    · rintro ⟨hle, hx⟩; exact ⟨(hlevel q x hx).1 hle, hx⟩
    · rintro ⟨hxL, hx⟩; exact ⟨(hlevel q x hx).2 hxL, hx⟩
  have hae_eq :
      (muRe k m u V Du H ⁻¹' Set.Iic (q : ℝ)) =ᵐ[μm]
        ((Lq ∩ Badᶜ : Set (Fin d → ℝ))) := by
    have hsub : (Lq ∩ Badᶜ) ⊆ (muRe k m u V Du H ⁻¹' Set.Iic (q : ℝ)) := by
      rw [← hpre_inter]; exact Set.inter_subset_left
    refine (ae_eq_set.2 ⟨?_, ?_⟩)
    · have : (muRe k m u V Du H ⁻¹' Set.Iic (q : ℝ)) \ (Lq ∩ Badᶜ) ⊆ Bad := by
        intro x hx
        by_contra hxBad
        have hxc : x ∈ Badᶜ := hxBad
        have : x ∈ (muRe k m u V Du H ⁻¹' Set.Iic (q : ℝ)) ∩ Badᶜ := ⟨hx.1, hxc⟩
        rw [hpre_inter] at this
        exact hx.2 this
      exact measure_mono_null this hBad_null
    · have : (Lq ∩ Badᶜ) \ (muRe k m u V Du H ⁻¹' Set.Iic (q : ℝ)) = ∅ := by
        rw [Set.diff_eq_empty]; exact hsub
      rw [this]; simp
  have hRHS_nmeas : NullMeasurableSet (Lq ∩ Badᶜ) μm :=
    hLq_nmeas.inter hBad_meas.compl.nullMeasurableSet
  exact hRHS_nmeas.congr hae_eq.symm

/-- **Measurability of `muReInner`** under joint hypotheses analogous to
`muAux_measurable`. -/
theorem muReInner_measurable
    {k : ℝ} {u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    (hHJB_meas : ∀ a : ℝ,
      MeasurableSet { x : Fin d → ℝ |
        u x + H x (fun i => Du i x) a - V x ≤ -k })
    (h_anti :
      ∀ x : Fin d → ℝ,
        AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ici 0))
    (h_cont :
      ∀ x : Fin d → ℝ,
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ici 0))
    (h_ne :
      ∀ x : Fin d → ℝ, (muReSet k u V Du H x).Nonempty) :
    Measurable (muReInner k u V Du H) := by
  apply measurable_of_Iic
  intro a
  rcases lt_or_ge a 0 with ha_neg | ha_nn
  · -- a < 0: the set is empty since muReInner x ≥ 0 always (by hne).
    have hempty : { x : Fin d → ℝ | muReInner k u V Du H x ≤ a } = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hle
      have h_lb : 0 ≤ muReInner k u V Du H x :=
        muReInner_nonneg_of_nonempty (h_ne x)
      linarith
    rw [show muReInner k u V Du H ⁻¹' Set.Iic a =
        { x : Fin d → ℝ | muReInner k u V Du H x ≤ a } from rfl, hempty]
    exact MeasurableSet.empty
  · -- a ≥ 0: use the level-set identity.
    have hset_eq :
        { x : Fin d → ℝ | muReInner k u V Du H x ≤ a } =
          { x : Fin d → ℝ |
              u x + H x (fun i => Du i x) a - V x ≤ -k } := by
      ext x
      simp only [Set.mem_setOf_eq]
      exact muReInner_le_iff_of_antitone_of_nonempty
        (k := k) (u := u) (V := V) (Du := Du) (H := H)
        (x := x) (a := a) ha_nn (h_cont x) (h_anti x) (h_ne x)
    rw [show muReInner k u V Du H ⁻¹' Set.Iic a =
        { x : Fin d → ℝ | muReInner k u V Du H x ≤ a } from rfl, hset_eq]
    exact hHJB_meas a

/-- **Measurability of `muRe`**: `min` of measurable `m` and measurable
`muReInner`. -/
theorem muRe_measurable
    {k : ℝ} {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    (hm_meas : Measurable m)
    (hHJB_meas : ∀ a : ℝ,
      MeasurableSet { x : Fin d → ℝ |
        u x + H x (fun i => Du i x) a - V x ≤ -k })
    (h_anti :
      ∀ x : Fin d → ℝ,
        AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ici 0))
    (h_cont :
      ∀ x : Fin d → ℝ,
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ici 0))
    (h_ne :
      ∀ x : Fin d → ℝ, (muReSet k u V Du H x).Nonempty) :
    Measurable (muRe k m u V Du H) := by
  unfold muRe
  exact hm_meas.min
    (muReInner_measurable hHJB_meas h_anti h_cont h_ne)

/-! ## Integrability of `μ_re − m` (the `h_diff_int` rider of
`weak_is_strong_HJB_ge_at_k`)

Since `0 ≤ μ_re ≤ m` a.e. (the outer `min` is `≤ m`, and non-emptiness gives
`μ_re ≥ 0`), the difference `μ_re − m` is squeezed: `|μ_re − m| = m − μ_re ≤ m`
a.e.  Hence `μ_re − m` is dominated by the integrable `m`. -/

/-- **`h_diff_int` rider** (paper line ~1499): `μ_re − m ∈ L¹` on the cube.

Dominated by `m`: `|μ_re x − m x| ≤ |m x|` a.e., because `0 ≤ μ_re ≤ m`. -/
theorem muRe_sub_m_integrable
    {k : ℝ} {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    (hμre_aesm :
      AEStronglyMeasurable (muRe k m u V Du H)
        (volume.restrict (UnitCube d)))
    (hm_int : Integrable m (volume.restrict (UnitCube d)))
    (hae_m_nn :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hae_ne :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        (muReSet k u V Du H x).Nonempty) :
    Integrable (fun x => muRe k m u V Du H x - m x)
      (volume.restrict (UnitCube d)) := by
  have hμre_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      0 ≤ muRe k m u V Du H x :=
    muRe_nonneg_ae hae_m_nn hae_ne
  -- The difference is AEStronglyMeasurable.
  have hdiff_aesm :
      AEStronglyMeasurable (fun x => muRe k m u V Du H x - m x)
        (volume.restrict (UnitCube d)) :=
    hμre_aesm.sub hm_int.aestronglyMeasurable
  -- Dominate `|μ_re − m|` by `|m|` a.e.
  refine Integrable.mono' hm_int hdiff_aesm ?_
  filter_upwards [hμre_nn, hae_m_nn] with x hx_nn hx_m_nn
  have hle_m : muRe k m u V Du H x ≤ m x := muRe_le_m k m u V Du H x
  rw [Real.norm_eq_abs,
    abs_of_nonpos (by linarith : muRe k m u V Du H x - m x ≤ 0)]
  linarith

/-! ## The crucial upper bound (paper eq.~`eq:mu.redef.up`, line 1488) -/

/-- **Paper eq.~`eq:mu.redef.up` (line 1488).** Under

* a.e. continuity of `H(x, Du x, ·)`,
* a.e. non-emptiness of the inner set `muReSet`,
* the Step 1 conclusion `u + H(·, Du, m) - V ≤ 0` a.e. (paper
  eq.~`eq:congest.HJleq0`, formalised in
  `weak_is_strong_HJB_le`),

we have

```
u + H(·, Du, μ_re) - V ≤ 0   a.e.
```

The argument splits at `μ_re x` versus `m x`:

* if `μ_re x = m x` (the second branch dominates the `min` from below),
  the bound is `≤ 0` directly from Step 1 (paper line 1491);
* if `μ_re x < m x`, then `μ_re x = muReInner x` (the inner branch is
  active). The inner set is closed and bounded below, so the inf is
  attained, giving `u + H(·, Du, μ_re) - V ≤ -k ≤ 0` (paper line 1491).

For `k > 0` the inequality `≤ -k` is even stronger (`≤ -k < 0`), but the
paper-stated form uses `≤ 0`. -/
theorem muRe_bound_up
    {k : ℝ}
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    (hk : 0 < k)
    (hae_cont :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hae_ne :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        (muReSet k u V Du H x).Nonempty)
    (hae_HJB0 :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        muReInner k u V Du H x ≤ 0 →
          u x + H x (fun i => Du i x) 0 - V x ≤ -k)
    (hae_step1 :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        u x + H x (fun i => Du i x) (m x) - V x ≤ 0) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      u x + H x (fun i => Du i x) (muRe k m u V Du H x) - V x ≤ 0 := by
  filter_upwards [hae_cont, hae_ne, hae_HJB0, hae_step1]
    with x hx_cont hx_ne hx_HJB0 hx_step1
  set μrex : ℝ := muRe k m u V Du H x with hμrexdef
  -- Two cases: μ_re x = m x or μ_re x = muReInner x.
  rcases le_or_gt (m x) (muReInner k u V Du H x) with h_le | h_gt
  · -- m x ≤ muReInner x ⇒ μ_re x = m x. Apply Step 1.
    have hμrex_eq : μrex = m x := by
      simp [hμrexdef, muRe, min_eq_left h_le]
    rw [hμrex_eq]
    exact hx_step1
  · -- m x > muReInner x ⇒ μ_re x = muReInner x. Use the inner constraint
    -- (boundary-aware: membership for `muReInner > 0`, `hx_HJB0` at `= 0`).
    have hμrex_eq : μrex = muReInner k u V Du H x := by
      simp [hμrexdef, muRe, min_eq_right h_gt.le]
    rw [hμrex_eq]
    have hHJB_at_inf :
        u x + H x (fun i => Du i x) (muReInner k u V Du H x) - V x ≤ -k := by
      rcases eq_or_lt_of_le (muReInner_nonneg_of_nonempty hx_ne)
        with hinner0 | hinner_pos
      · rw [← hinner0]; exact hx_HJB0 (le_of_eq hinner0.symm)
      · exact (muReInner_mem_of_pos_of_continuousOn_Ioi hx_cont hx_ne
          hinner_pos).2
    -- `≤ -k ≤ 0` since `k > 0`.
    linarith

/-! ## The product inequality (paper eq.~`eq:mu.redef-minus-m.bound`,
line 1493) -/

/-- **Pointwise product inequality** (paper eq.~`eq:mu.redef-minus-m.bound`,
line 1493).

For almost every `x`, with `μ_re := muRe k m u V Du H`,
```
(μ_re(x) - m(x)) · (k + u(x) + H(x, Du(x), μ_re(x)) - V(x)) ≥ 0.
```

The argument (paper line 1494) splits at `μ_re x` versus `m x`:

* the first factor `μ_re - m ≤ 0` always (since `μ_re = min(m, …) ≤ m`);
* on the set where `μ_re = m`, the first factor is zero, and so is the
  product;
* on the set where `μ_re < m`, the inner branch of the `min` is active,
  so `μ_re x = muReInner k u V Du H x`. The inner set is closed and
  bounded below; non-emptiness gives that the inf is attained, hence
  `u + H(·, Du, μ_re) - V ≤ -k`, i.e. `k + u + H(·, Du, μ_re) - V ≤ 0`.
  The product of two non-positive numbers is non-negative.

Note (paper line 1494): unlike `eq:mu-minus-m-formula`, this is only an
inequality, with possible strict inequality on `{m > μ_re = 0}`.

Hypotheses mirror `muRe_bound_up` (no `0 < k` needed for the inequality
itself: `0 ≤ k` would even be superfluous, since the proof goes through
the `≤ -k` constraint of the inner set). -/
theorem muRe_inequality
    {k : ℝ}
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    (hae_cont :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hae_ne :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        (muReSet k u V Du H x).Nonempty)
    (hae_HJB0 :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        muReInner k u V Du H x ≤ 0 →
          u x + H x (fun i => Du i x) 0 - V x ≤ -k) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      0 ≤ (muRe k m u V Du H x - m x) *
            (k + u x + H x (fun i => Du i x) (muRe k m u V Du H x) - V x) := by
  filter_upwards [hae_cont, hae_ne, hae_HJB0] with x hx_cont hx_ne hx_HJB0
  set μrex : ℝ := muRe k m u V Du H x with hμrexdef
  -- First factor is always ≤ 0 since μ_re ≤ m.
  have h_first_nonpos : μrex - m x ≤ 0 := by
    have h_le : μrex ≤ m x := by
      simpa [hμrexdef] using muRe_le_m k m u V Du H x
    linarith
  -- Case split: either the first factor is zero (μ_re = m) or strictly
  -- negative (μ_re < m).
  rcases lt_or_eq_of_le h_first_nonpos with h_lt | h_eq
  · -- μ_re x < m x. Then μ_re x = muReInner x (the second branch is
    -- active in the `min`).
    have h_lt_m : μrex < m x := by linarith
    have h_inner_lt_m : muReInner k u V Du H x < m x := by
      -- μ_re = min (m x) (muReInner) < m x ⇒ muReInner < m x.
      have h_min : μrex = min (m x) (muReInner k u V Du H x) := by
        simp [hμrexdef, muRe]
      by_contra h_not_lt
      push_neg at h_not_lt
      have : μrex = m x := by
        rw [h_min]; exact min_eq_left h_not_lt
      linarith
    have h_μrex_eq : μrex = muReInner k u V Du H x := by
      simp [hμrexdef, muRe, min_eq_right h_inner_lt_m.le]
    -- Inner constraint (boundary-aware: membership for `muReInner > 0`,
    -- `hx_HJB0` at the boundary `muReInner = 0`).
    have hHJB_at_inf :
        u x + H x (fun i => Du i x) (muReInner k u V Du H x) - V x ≤ -k := by
      rcases eq_or_lt_of_le (muReInner_nonneg_of_nonempty hx_ne)
        with hinner0 | hinner_pos
      · rw [← hinner0]; exact hx_HJB0 (le_of_eq hinner0.symm)
      · exact (muReInner_mem_of_pos_of_continuousOn_Ioi hx_cont hx_ne
          hinner_pos).2
    -- Therefore second factor ≤ 0 at μ_re x.
    have h_second_nonpos :
        k + u x + H x (fun i => Du i x) μrex - V x ≤ 0 := by
      rw [h_μrex_eq]; linarith
    -- Product of two non-positive numbers is non-negative.
    exact mul_nonneg_of_nonpos_of_nonpos h_first_nonpos h_second_nonpos
  · -- μ_re x = m x. First factor is zero ⇒ product is zero ⇒ ≥ 0.
    have h_zero : μrex - m x = 0 := h_eq
    rw [h_zero, zero_mul]

/-! ## Product integrability (the `h_prod_int` rider of
`weak_is_strong_HJB_ge_at_k`)

The witness `weak_is_strong_HJB_ge_at_k` (StrongIsStrong.lean) consumes
```
Integrable ((u + H(·,Du,μ_re) − V)·(μ_re − m))  on the cube.
```
Both factors are non-positive a.e. (`μ_re − m ≤ 0` from the outer `min`,
`u + H − V ≤ 0` on the active inner branch), so the product is non-negative;
we dominate it above by a Hölder product `G·|μ_re − m|` with
`G := |u| + |V| + C·(m^β + 1) ∈ L^{β̄'}` and `μ_re − m ∈ L^{β̄}`.

The crucial lower bound `H(·,Du,μ_re) ≥ −C(μ_re^β + 1)` comes from
`hcong.lower` for `μ_re > 0`, extended to the boundary `μ_re = 0` by the
continuity-at-`0` limit argument of
`MuIntegrability.muAux_quotient_dominator_memLp`.  No `μ_re > 0`,
`Hext_finite_at_zero`, power-growth, or joint-continuity rider is used. -/

open MeasureTheory in
/-- **`h_prod_int` rider** (paper line ~1507) — product integrability of the
HJB test integrand at the `μ_re` competitor.

`G x := |u x| + |V x| + C·(m x ^ β + 1)` dominates `|u + H(·,Du,μ_re) − V|`
on `{μ_re < m}` (the only place the factor `μ_re − m` is nonzero), via the
inner-set upper bound `u + H − V ≤ −k ≤ 0` and the congestion lower bound
`H ≥ −C(μ_re^β + 1) ≥ −C(m^β + 1)` (continuity-extended to `μ_re = 0`).
`G ∈ L^{β̄'}` and `μ_re − m ∈ L^{β̄}` then give Hölder integrability of
`G·(μ_re − m)`, dominating the product. -/
theorem muRe_prod_integrable
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : StationaryMFG.Hamiltonian.HypothesisMonotone (d := d) H DpH)
    (hcong : StationaryMFG.Hamiltonian.CongestionGrowthCore (d := d) H DpH J)
    (hHat0 : StationaryMFG.Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : StationaryMFG.Hamiltonian.H_zero_eq_Hext (d := d) H)
    {k : ℝ} (hk : 0 ≤ k)
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm_meas : Measurable m)
    (hu_meas : Measurable u)
    (hV_aesm : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hDu_meas : ∀ i, Measurable (Du i))
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) m)
    (hu_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) u)
    (hV_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (hae_m_nn :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hae_anti :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hae_cont :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hae_ne :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        (muReSet k u V Du H x).Nonempty) :
    Integrable
      (fun x =>
        (u x + H x (fun i => Du i x) (muRe k m u V Du H x) - V x)
          * (muRe k m u V Du H x - m x))
      (volume.restrict (UnitCube d)) := by
  classical
  set β : ℝ := hcong.β with hβdef
  set τ : ℝ := hcong.τ with hτdef
  set C : ℝ := hcong.C with hCdef
  have hβ : 0 < β := hcong.hβ
  have hτ_nn : 0 ≤ τ := hcong.hτ.1
  have hC_pos : 0 < C := hcong.hC
  have hC_nn : 0 ≤ C := hC_pos.le
  haveI hfin : IsFiniteMeasure
      (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  -- HJB level-set null-measurability (boundary-free `_aesm` route).
  have hHJB_nmeas :
      ∀ a : ℝ,
        NullMeasurableSet { x : Fin d → ℝ |
          u x + H x (fun i => Du i x) a - V x ≤ -k }
          (volume.restrict (UnitCube d)) := by
    intro a
    have hDuvec : Measurable (fun x : Fin d → ℝ => fun i => Du i x) :=
      Measurable.of_eval hDu_meas
    have hprod :
        Measurable (fun x : Fin d → ℝ => (x, (fun i => Du i x), a)) :=
      measurable_id.prodMk (hDuvec.prodMk measurable_const)
    have hHcomp : Measurable (fun x : Fin d → ℝ => H x (fun i => Du i x) a) :=
      hmon.toRegularityH.measurable_H.comp hprod
    -- `V` is only a.e.-strongly-measurable: build the sublevel set as a
    -- `NullMeasurableSet` of the a.e.-strongly-measurable HJB integrand.
    have hF_aesm : AEStronglyMeasurable
        (fun x : Fin d → ℝ => u x + H x (fun i => Du i x) a - V x)
        (volume.restrict (UnitCube d)) :=
      (hu_meas.aestronglyMeasurable.add hHcomp.aestronglyMeasurable).sub hV_aesm
    exact hF_aesm.nullMeasurableSet_le aestronglyMeasurable_const
  -- `μ_re` is `AEMeasurable` (a.e.-on-`Ioi 0` route).
  have hμre_aemeas : AEMeasurable (muRe k m u V Du H)
      (volume.restrict (UnitCube d)) :=
    muRe_measurable_of_Ioi0_of_m_nonneg_aesm hm_meas hHJB_nmeas hae_m_nn
      hae_anti hae_cont hae_ne
  have hμre_aesm : AEStronglyMeasurable (muRe k m u V Du H)
      (volume.restrict (UnitCube d)) := hμre_aemeas.aestronglyMeasurable
  -- `0 ≤ μ_re ≤ m` a.e. (and everywhere `μ_re ≤ m`).
  have hμre_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      0 ≤ muRe k m u V Du H x :=
    muRe_nonneg_ae hae_m_nn hae_ne
  -- AE-strong measurability of `H(·,Du,μ_re)`.
  have hH_comp_meas :
      AEStronglyMeasurable
        (fun x => H x (fun i => Du i x) (muRe k m u V Du H x))
        (volume.restrict (UnitCube d)) := by
    have hDuvec : Measurable (fun x : Fin d → ℝ => fun i => Du i x) :=
      Measurable.of_eval hDu_meas
    have hDuvec_aem : AEMeasurable (fun x : Fin d → ℝ => fun i => Du i x)
        (volume.restrict (UnitCube d)) := hDuvec.aemeasurable
    have hprod :
        AEMeasurable (fun x : Fin d → ℝ =>
          (x, (fun i => Du i x), muRe k m u V Du H x))
          (volume.restrict (UnitCube d)) :=
      aemeasurable_id.prodMk (hDuvec_aem.prodMk hμre_aemeas)
    exact (hmon.toRegularityH.measurable_H.comp_aemeasurable hprod).aestronglyMeasurable
  -- The HJB factor `F x := u + H(·,Du,μ_re) − V`.
  set F : (Fin d → ℝ) → ℝ :=
    fun x => u x + H x (fun i => Du i x) (muRe k m u V Du H x) - V x with hFdef
  have hF_meas : AEStronglyMeasurable F (volume.restrict (UnitCube d)) :=
    (hu_meas.aestronglyMeasurable.add hH_comp_meas).sub hV_aesm
  -- The difference factor `D x := μ_re − m`.
  set D : (Fin d → ℝ) → ℝ := fun x => muRe k m u V Du H x - m x with hDdef
  have hD_meas : AEStronglyMeasurable D (volume.restrict (UnitCube d)) :=
    hμre_aesm.sub hm_meas.aestronglyMeasurable
  -- The dominator `G x := |u x| + |V x| + C·(m x ^ β + 1)`.
  set G : (Fin d → ℝ) → ℝ :=
    fun x => |u x| + |V x| + C * (m x ^ β + 1) with hGdef
  -- `G ∈ L^{β̄'}`.
  set betaBarPrime : ENNReal := ENNReal.ofReal ((β + 1) / β) with hbbp_def
  have huabs : MemLpPer (d := d) betaBarPrime (fun x => |u x|) := by
    have h := hu_mem.toMemLp.norm
    have heq : (fun x => ‖u x‖) = fun x => |u x| := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at h; rw [hbbp_def]; exact MemLp.toMemLpPer h
  have hVabs : MemLpPer (d := d) betaBarPrime (fun x => |V x|) := by
    have h := hV_mem.toMemLp.norm
    have heq : (fun x => ‖V x‖) = fun x => |V x| := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at h; rw [hbbp_def]; exact MemLp.toMemLpPer h
  have hmβ : MemLpPer (d := d) betaBarPrime (fun x => m x ^ β) := by
    rw [hbbp_def]
    exact rpow_beta_memLp_betaBar' hβ hm_mem hae_m_nn
  have hCmβ : MemLpPer (d := d) betaBarPrime
      (fun x => C * (m x ^ β + 1)) := by
    have hone : MemLpPer (d := d) betaBarPrime
        (fun _ : (Fin d → ℝ) => (1 : ℝ)) := MemLp.toMemLpPer (memLp_const 1)
    have := (hmβ.add hone).const_smul (𝕜 := ℝ) C
    have heq : (C • ((fun x => m x ^ β) + fun _ : Fin d → ℝ => (1 : ℝ)))
        = (fun x => C * (m x ^ β + 1)) := by
      funext x; simp [Pi.smul_apply, smul_eq_mul, Pi.add_apply]
    rwa [heq] at this
  have hG_mem : MemLpPer (d := d) betaBarPrime G := by
    have := (huabs.add hVabs).add hCmβ
    have heq : ((fun x => |u x|) + fun x => |V x|) + (fun x => C * (m x ^ β + 1))
        = G := by
      funext x; simp [hGdef, Pi.add_apply]
    rwa [heq] at this
  -- `D = μ_re − m ∈ L^{β̄}` (dominated by `m`).
  set betaBar : ENNReal := ENNReal.ofReal (β + 1) with hbb_def
  have hD_mem : MemLpPer (d := d) betaBar D := by
    rw [hbb_def, memLpPer_iff_memLp]
    refine MemLp.of_le_mul (c := 1) (by rw [← hbb_def]; exact hm_mem.toMemLp)
      hD_meas ?_
    filter_upwards [hμre_nn, hae_m_nn] with x hx_nn hx_m_nn
    have hle_m : muRe k m u V Du H x ≤ m x := muRe_le_m k m u V Du H x
    rw [Real.norm_eq_abs (D x), hDdef,
      abs_of_nonpos (by linarith : muRe k m u V Du H x - m x ≤ 0),
      one_mul, Real.norm_eq_abs, abs_of_nonneg hx_m_nn]
    linarith
  -- Hölder integrability of `G·D`.
  have hconj : Real.HolderConjugate (β + 1) ((β + 1) / β) :=
    StationaryMFG.Theorems.SimplePower.SimplePowerExponentFacts.paper_holderConjugate_betaBar
      hβ
  have hGD_int : IntegrableOn (fun x => G x * D x) (UnitCube d) :=
    -- `hconj.symm : HolderConjugate ((β+1)/β) (β+1)`, so `f := G ∈ L^{β̄'}`,
    -- `g := D ∈ L^{β̄}`.
    MemLpPer.integrable_mul (d := d) hconj.symm
      (f := G) (g := D)
      (by rw [← hbbp_def]; exact hG_mem) (by rw [← hbb_def]; exact hD_mem)
  -- Boundary lower bound at `μ = 0` via the (a:Hat0) extension (paper line
  -- 1435): from `lower_extends_to_zero` we get `g₀ ≤ Hext H x (Du x) 0`, and
  -- `hAgree` transports `Hext H x (Du x) 0 = (H x (Du x) 0 : WithTop ℝ)`.
  have hlow0 :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        -(C * ((0 : ℝ) ^ β + 1)) ≤ H x (fun i => Du i x) 0 := by
    filter_upwards [hcong.lower_extends_to_zero hHat0, hAgree]
      with x hx_ext hx_agree
    have hext := hx_ext (fun i => Du i x)
    -- Transport `Hext → raw` via `hAgree`.
    have hagree_x :
        ((H x (fun i => Du i x) 0 : ℝ) : WithTop ℝ)
          = StationaryMFG.Hamiltonian.Hext H x (fun i => Du i x) 0 :=
      hx_agree (fun i => Du i x)
    rw [← hagree_x] at hext
    -- `hext : ((g₀ : ℝ) : WithTop) ≤ ((H x (Du x) 0 : ℝ) : WithTop)`.
    have hreal :
        (1 / C) * (1 / ((0 : ℝ) ^ hcong.τ + 1)) *
            (‖(fun i => Du i x)‖ ^ (hcong.α * (1 + hcong.τ / hcong.β))) - C
          ≤ H x (fun i => Du i x) 0 := by exact_mod_cast hext
    -- Drop the nonnegative momentum term: `-C ≤ g₀`, and `0^β = 0`.
    have hmom_nn : 0 ≤ (1 / C) * (1 / ((0 : ℝ) ^ hcong.τ + 1)) *
        (‖(fun i => Du i x)‖ ^ (hcong.α * (1 + hcong.τ / hcong.β))) := by
      have hden_pos : 0 < (0 : ℝ) ^ hcong.τ + 1 := by
        have : 0 ≤ (0 : ℝ) ^ hcong.τ := Real.rpow_nonneg le_rfl _
        linarith
      have hnum_nn : 0 ≤ ‖(fun i => Du i x)‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) :=
        Real.rpow_nonneg (norm_nonneg _) _
      positivity
    have h0β : (0 : ℝ) ^ β = 0 := Real.zero_rpow hβ.ne'
    rw [h0β]
    nlinarith [hreal, hmom_nn]
  -- Boundary HJB-upper bound at `μ_re = 0` via the (a:Hat0) limit applied to the
  -- level-set rationals: `muReInner ≤ 0` ⇒ rationals `qₙ ↓ 0` with
  -- `HJB(qₙ) ≤ −k`; the right-limit (`tendsto_Hext_zero_of_exists` + `hAgree`)
  -- pushes this to `u + H(·,0) − V ≤ −k`.
  have hHJB0 :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        muReInner k u V Du H x ≤ 0 →
          u x + H x (fun i => Du i x) 0 - V x ≤ -k := by
    filter_upwards [hae_anti, hae_ne, hHat0.exists_limit_at_zero, hAgree]
      with x hx_anti hx_ne hx_limit hx_agree hμle0
    -- Rationals `qₙ ↓ 0` with HJB ≤ −k.
    have hwit := (muReInner_le_zero_iff_of_antitoneOn_Ioi hx_anti hx_ne).mp hμle0
    -- Right-limit of `H(·,ν)` in `WithTop ℝ`.
    have hTendsto :
        Filter.Tendsto
          (fun ν : ℝ => ((H x (fun i => Du i x) ν : ℝ) : WithTop ℝ))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (StationaryMFG.Hamiltonian.H_at_zero H x (fun i => Du i x))) :=
      StationaryMFG.Hamiltonian.tendsto_Hext_zero_of_exists
        (hx_limit (fun i => Du i x))
    set b : ℝ := -k - u x + V x with hb_def
    -- Case split on whether a `q = 0` witness exists (mirrors the `_le_` side).
    by_cases hzero : ∃ n : ℕ, ∃ q : ℚ,
        (q : ℝ) = 0 ∧ 0 ≤ (q : ℝ) ∧ (q : ℝ) < 1 / ((n : ℝ) + 1) ∧
          u x + H x (fun i => Du i x) (q : ℝ) - V x ≤ -k
    · -- Case A: a `q = 0` witness ⇒ raw `u + H(·,0) − V ≤ −k` directly.
      obtain ⟨_, _, hq_eq0, _, _, hHJB_q⟩ := hzero
      rw [hq_eq0] at hHJB_q; exact hHJB_q
    · -- Case B: every witness is positive ⇒ antitone-lift + (a:Hat0) limit.
      have hPointwise : ∀ ν : ℝ, 0 < ν →
          u x + H x (fun i => Du i x) ν - V x ≤ -k := by
        intro ν hν
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hν
        obtain ⟨q, hq_nn, hq_hi, hHJB_q⟩ := hwit n
        have hq_lt_ν : (q : ℝ) < ν := by
          have h1 : (1 : ℝ) / ((n : ℝ) + 1) < ν := by
            simpa only [one_div] using hn
          exact lt_trans hq_hi h1
        have hq_pos : 0 < (q : ℝ) := by
          rcases eq_or_lt_of_le hq_nn with hq0 | hq_pos
          · exact absurd ⟨n, q, hq0.symm, hq_nn, hq_hi, hHJB_q⟩ hzero
          · exact hq_pos
        have hanti_le :
            H x (fun i => Du i x) ν ≤ H x (fun i => Du i x) (q : ℝ) :=
          hx_anti hq_pos (lt_trans hq_pos hq_lt_ν) hq_lt_ν.le
        linarith [hHJB_q]
      have hEv :
          ∀ᶠ ν in nhdsWithin 0 (Set.Ioi 0),
            ((H x (fun i => Du i x) ν : ℝ) : WithTop ℝ) ≤ ((b : ℝ) : WithTop ℝ) := by
        refine Filter.eventually_iff_exists_mem.mpr ⟨Set.Ioi (0 : ℝ),
          self_mem_nhdsWithin, fun ν hν => ?_⟩
        have := hPointwise ν hν
        have hle : H x (fun i => Du i x) ν ≤ b := by rw [hb_def]; linarith
        exact_mod_cast hle
      have hHext_le :
          StationaryMFG.Hamiltonian.H_at_zero H x (fun i => Du i x)
            ≤ ((b : ℝ) : WithTop ℝ) := le_of_tendsto hTendsto hEv
      have hAgree_x :
          ((H x (fun i => Du i x) 0 : ℝ) : WithTop ℝ)
            = StationaryMFG.Hamiltonian.H_at_zero H x (fun i => Du i x) := by
        rw [StationaryMFG.Hamiltonian.H_at_zero_def]
        exact hx_agree (fun i => Du i x)
      have hraw_le :
          ((H x (fun i => Du i x) 0 : ℝ) : WithTop ℝ) ≤ ((b : ℝ) : WithTop ℝ) := by
        rw [hAgree_x]; exact hHext_le
      have hraw : H x (fun i => Du i x) 0 ≤ b := by exact_mod_cast hraw_le
      rw [hb_def] at hraw; linarith
  -- Pointwise domination `|F·D| ≤ |G·D|` a.e.
  have hdom :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖F x * D x‖ ≤ ‖G x * D x‖ := by
    filter_upwards [hμre_nn, hae_m_nn, hcong.lower, hae_anti, hae_cont, hae_ne,
        hlow0, hHJB0]
      with x hx_nn hx_m_nn hlow_x hx_anti hx_cont hx_ne hx_low0 hx_HJB0
    -- Notation.
    set μ : ℝ := muRe k m u V Du H x with hμ_def
    have hμ_le_m : μ ≤ m x := muRe_le_m k m u V Du H x
    have hμβ_le_mβ : μ ^ β ≤ m x ^ β :=
      Real.rpow_le_rpow hx_nn hμ_le_m hβ.le
    -- The `G x ≥ 0` and the value of `D x`.
    have hG_nn : 0 ≤ G x := by
      have hmβ_nn : 0 ≤ m x ^ β := Real.rpow_nonneg hx_m_nn _
      have : 0 ≤ C * (m x ^ β + 1) := mul_nonneg hC_nn (by linarith)
      have := abs_nonneg (u x); have := abs_nonneg (V x)
      rw [hGdef]; linarith
    -- The lower bound `H(x,Du,μ) ≥ −C(μ^β + 1)` (boundary handled at μ=0).
    have hH_ge : -(C * (μ ^ β + 1)) ≤ H x (fun i => Du i x) μ := by
      rcases eq_or_lt_of_le hx_nn with hμ0 | hμpos
      · -- `μ = 0`: use the (a:Hat0) boundary lower bound `hx_low0`.
        rw [← hμ0]; exact hx_low0
      · -- `μ > 0`: direct.
        have hlb := hlow_x (fun i => Du i x) μ hμpos
        rw [← hCdef, ← hβdef, ← hτdef] at hlb
        have hmom_nn : 0 ≤ (1 / C) * (1 / (μ ^ τ + 1))
            * (‖fun i => Du i x‖ ^ (hcong.α * (1 + τ / β))) := by
          have hden_pos : 0 < μ ^ τ + 1 := by
            have : 0 ≤ μ ^ τ := Real.rpow_nonneg hμpos.le _
            linarith
          have hnum_nn : 0 ≤ ‖fun i => Du i x‖ ^ (hcong.α * (1 + τ / β)) :=
            Real.rpow_nonneg (norm_nonneg _) _
          positivity
        show -(C * (μ ^ β + 1)) ≤ H x (fun i => Du i x) μ
        nlinarith [hlb, hmom_nn]
    -- Upper bound on `F x = u + H − V`:
    --   on `{μ < m}` it is `≤ −k ≤ 0`; on `{μ = m}` the factor `D x = 0`.
    rcases lt_or_eq_of_le hμ_le_m with hμ_lt | hμ_eq
    · -- `μ < m`: inner branch active, `u + H − V ≤ −k`, so `|F| ≤ G`.
      have h_inner_lt_m : muReInner k u V Du H x < m x := by
        by_contra hnot
        push_neg at hnot
        have : μ = m x := by
          rw [hμ_def, muRe, min_eq_left hnot]
        linarith
      have hμ_eq_inner : μ = muReInner k u V Du H x := by
        rw [hμ_def, muRe, min_eq_right h_inner_lt_m.le]
      -- `u + H(·,μ_re) − V ≤ −k`: membership (`muReInner > 0`) or boundary
      -- (`muReInner = 0`, via `hx_HJB0`).
      have hHJB :
          u x + H x (fun i => Du i x) (muReInner k u V Du H x) - V x ≤ -k := by
        rcases eq_or_lt_of_le (muReInner_nonneg_of_nonempty hx_ne)
          with hinner0 | hinner_pos
        · -- `muReInner = 0`: boundary HJB-upper bound.
          rw [← hinner0]; exact hx_HJB0 (le_of_eq hinner0.symm)
        · -- `muReInner > 0`: inner-set membership.
          exact (muReInner_mem_of_pos_of_continuousOn_Ioi hx_cont hx_ne
            hinner_pos).2
      -- `F x ≤ 0` (upper) and `F x ≥ −G x` (lower).
      have hF_val : F x = u x + H x (fun i => Du i x) μ - V x := rfl
      have hG_val : G x = |u x| + |V x| + C * (m x ^ β + 1) := rfl
      have hF_upper : F x ≤ 0 := by
        rw [hF_val, hμ_eq_inner]; linarith
      have hF_lower : -(G x) ≤ F x := by
        have hH_ge' : -(C * (m x ^ β + 1)) ≤ H x (fun i => Du i x) μ := by
          have : -(C * (m x ^ β + 1)) ≤ -(C * (μ ^ β + 1)) := by
            have := mul_le_mul_of_nonneg_left hμβ_le_mβ hC_nn
            linarith
          linarith [hH_ge]
        rw [hF_val, hG_val]
        have h1 : -|u x| ≤ u x := neg_abs_le _
        have h2 : -|V x| ≤ V x := by have := neg_abs_le (V x); linarith
        -- goal: −(|u|+|V|+C(m^β+1)) ≤ u + H − V
        nlinarith [hH_ge', h1, h2, le_abs_self (V x)]
      have hF_abs : |F x| ≤ |G x| := by
        rw [abs_of_nonneg hG_nn]
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right hF_abs (abs_nonneg _)
    · -- `μ = m`: `D x = 0`, so both products vanish.
      have hDx : D x = 0 := by
        simp only [hDdef, ← hμ_def, hμ_eq, sub_self]
      rw [hDx, mul_zero, mul_zero]
  -- Conclude by domination (dominate by `|G·D|`, integrable from `hGD_int`).
  refine Integrable.mono' (g := fun x => |G x * D x|) hGD_int.abs
    (hF_meas.mul hD_meas) ?_
  filter_upwards [hdom] with x hx
  simpa [Real.norm_eq_abs] using hx

/-! ## The quotient dominator Lp certificate for `μ_re`
(the `hQuot_muRe_mem` parameter of `perdelta_vi_integral_le_of_muRe`)

Mirrors `MuIntegrability.muAux_quotient_dominator_memLp` for the `μ_re`
(`≥`-direction) side.  The HJB constraint at `μ_re` is the inner-set
membership `u + H(x, Du, μ_re) − V ≤ −k` (via `muReSet`), which is
*stronger* than the muAux `≤ k`; combined with the congestion lower bound
`H ≥ (1/C)(1/(μ^τ+1))‖Du‖^{αt} − C(μ^β+1)` (continuity-extended to the
boundary `μ_re = 0`), this yields

```
‖Du‖^{αt}/(μ_re^τ+1) ≤ C·(|k| + |u| + |V| + C(m^β + 1) + C) =: G.
```

Using `μ_re ≤ m` (`muRe_le_m`), the envelope is taken over `m^β` (not
`μ_re^β`), so `G ∈ L^{β̄'}` reuses `rpow_beta_memLp_betaBar'`
(`β̄'·β = β + 1`).  Domination is `MemLp.of_le_mul (c := 1)`. -/

open MeasureTheory in
/-- **`hQuot_muRe_mem` cert** (paper eq. `eq:congest.HJ0`, child D1b-i2) —
quotient-dominator Lp membership at the `μ_re` competitor:
```
‖Du‖^{α(1+τ/β)} / (μ_re^τ + 1) ∈ L^{β̄'}_per,   β̄' = ENNReal.ofReal ((β+1)/β).
```
The `μ_re^τ` denominator is essential (dropping it would force
`‖Du‖^{αt} ∈ L^{β̄'}`, which fails for `τ > 0`); the dominator
`G x := C·(|k| + |u x| + |V x| + C·(m x ^ β + 1) + C)` lies in `L^{β̄'}`
via `m ∈ L^{β̄}`. -/
theorem muRe_quotient_dominator_memLp
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : StationaryMFG.Hamiltonian.HypothesisMonotone (d := d) H DpH)
    (hcong : StationaryMFG.Hamiltonian.CongestionGrowthCore (d := d) H DpH J)
    (hHat0 : StationaryMFG.Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : StationaryMFG.Hamiltonian.H_zero_eq_Hext (d := d) H)
    {k : ℝ}
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm_meas : Measurable m)
    (hu_meas : Measurable u)
    (hV_aesm : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hDu_meas : ∀ i, Measurable (Du i))
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) m)
    (hu_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) u)
    (hV_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (hae_m_nn :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hae_anti :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hae_cont :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (h_step1 :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (hae_ne :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        (muReSet k u V Du H x).Nonempty) :
    MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
      (fun x : Fin d → ℝ =>
        ‖fun i => Du i x‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) /
          (muRe k m u V Du H x ^ hcong.τ + 1)) := by
  classical
  set α : ℝ := hcong.α with hαdef
  set β : ℝ := hcong.β with hβdef
  set τ : ℝ := hcong.τ with hτdef
  set C : ℝ := hcong.C with hCdef
  have hβ : 0 < β := hcong.hβ
  have hτ_nn : 0 ≤ τ := hcong.hτ.1
  have hC_pos : 0 < C := hcong.hC
  have hC_nn : 0 ≤ C := hC_pos.le
  set αt : ℝ := α * (1 + τ / β) with hαtdef
  set betaBarPrime : ENNReal := ENNReal.ofReal ((β + 1) / β) with hbbp_def
  -- HJB level-set null-measurability (boundary-free `_aesm` route).
  have hHJB_nmeas :
      ∀ a : ℝ,
        NullMeasurableSet { x : Fin d → ℝ |
          u x + H x (fun i => Du i x) a - V x ≤ -k }
          (volume.restrict (UnitCube d)) := by
    intro a
    have hDuvec : Measurable (fun x : Fin d → ℝ => fun i => Du i x) :=
      Measurable.of_eval hDu_meas
    have hprod :
        Measurable (fun x : Fin d → ℝ => (x, (fun i => Du i x), a)) :=
      measurable_id.prodMk (hDuvec.prodMk measurable_const)
    have hHcomp : Measurable (fun x : Fin d → ℝ => H x (fun i => Du i x) a) :=
      hmon.toRegularityH.measurable_H.comp hprod
    -- `V` is only a.e.-strongly-measurable: build the sublevel set as a
    -- `NullMeasurableSet` of the a.e.-strongly-measurable HJB integrand.
    have hF_aesm : AEStronglyMeasurable
        (fun x : Fin d → ℝ => u x + H x (fun i => Du i x) a - V x)
        (volume.restrict (UnitCube d)) :=
      (hu_meas.aestronglyMeasurable.add hHcomp.aestronglyMeasurable).sub hV_aesm
    exact hF_aesm.nullMeasurableSet_le aestronglyMeasurable_const
  -- `μ_re` is `AEMeasurable` (a.e.-on-`Ioi 0` route).
  have hμre_meas : AEMeasurable (muRe k m u V Du H)
      (volume.restrict (UnitCube d)) :=
    muRe_measurable_of_Ioi0_of_m_nonneg_aesm hm_meas hHJB_nmeas hae_m_nn
      hae_anti hae_cont hae_ne
  -- The dominator `G x := C·(|k| + |u x| + |V x| + C·(m x ^ β + 1) + C)`.
  set G : (Fin d → ℝ) → ℝ :=
    fun x => C * (|k| + |u x| + |V x| + C * (m x ^ β + 1) + C) with hG_def
  -- (a) `m^β ∈ L^{β̄'}_per` via `rpow_beta_memLp_betaBar'` (`β̄'·β = β + 1`).
  have hmβ : MemLpPer (d := d) betaBarPrime (fun x => m x ^ β) := by
    rw [hbbp_def]
    exact rpow_beta_memLp_betaBar' hβ hm_mem hae_m_nn
  -- (b) finite-measure cube for constants.
  haveI hcube_fin :
      IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  -- (c) the absolute-value pieces of `u`, `V`.
  have huabs : MemLpPer (d := d) betaBarPrime (fun x => |u x|) := by
    have h := hu_mem.toMemLp.norm
    have heq : (fun x => ‖u x‖) = fun x => |u x| := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at h; rw [hbbp_def]; exact MemLp.toMemLpPer h
  have hVabs : MemLpPer (d := d) betaBarPrime (fun x => |V x|) := by
    have h := hV_mem.toMemLp.norm
    have heq : (fun x => ‖V x‖) = fun x => |V x| := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at h; rw [hbbp_def]; exact MemLp.toMemLpPer h
  have hconst : ∀ c : ℝ, MemLpPer (d := d) betaBarPrime (fun _ : Fin d → ℝ => c) :=
    fun c => MemLp.toMemLpPer (memLp_const c)
  -- A local `MemLpPer` transport along a pointwise equality of functions.
  have memLpPer_of_eq :
      ∀ {f g : (Fin d → ℝ) → ℝ}, MemLpPer (d := d) betaBarPrime f →
        (∀ x, f x = g x) → MemLpPer (d := d) betaBarPrime g := by
    intro f g hf hfg
    have heq : f = g := funext hfg
    rwa [heq] at hf
  -- (d) `G ∈ L^{β̄'}_per`.
  have hG_mem : MemLpPer (d := d) betaBarPrime G := by
    have h2 : MemLpPer (d := d) betaBarPrime
        (fun x => C * (m x ^ β + 1)) :=
      memLpPer_of_eq ((hmβ.add (hconst (1 : ℝ))).const_smul (𝕜 := ℝ) C)
        (fun x => by simp [Pi.smul_apply, Pi.add_apply, smul_eq_mul])
    have hinner :
        MemLpPer (d := d) betaBarPrime
          (fun x => |k| + |u x| + |V x|
            + C * (m x ^ β + 1) + C) :=
      memLpPer_of_eq
        (((((hconst |k|).add huabs).add hVabs).add h2).add (hconst C))
        (fun x => by simp only [Pi.add_apply])
    exact memLpPer_of_eq (hinner.const_smul (𝕜 := ℝ) C)
      (fun x => by simp only [hG_def, Pi.smul_apply, smul_eq_mul])
  -- (e) `G ≥ 0` a.e.
  have hG_nn : ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)), 0 ≤ G x := by
    filter_upwards [hae_m_nn] with x hx_m_nn
    rw [hG_def]
    have hmβ_nn : 0 ≤ m x ^ β := Real.rpow_nonneg hx_m_nn _
    have hinner_nn :
        0 ≤ |k| + |u x| + |V x| + C * (m x ^ β + 1) + C := by
      have h2 : 0 ≤ C * (m x ^ β + 1) := mul_nonneg hC_nn (by linarith)
      have := abs_nonneg k; have := abs_nonneg (u x); have := abs_nonneg (V x)
      linarith
    exact mul_nonneg hC_nn hinner_nn
  -- (f) measurability of the quotient.
  have h_meas :
      AEStronglyMeasurable
        (fun x : Fin d → ℝ =>
          ‖fun i => Du i x‖ ^ αt /
            (muRe k m u V Du H x ^ τ + 1))
        (Measure.restrict volume (UnitCube d)) := by
    have hDuvec : Measurable (fun x : Fin d → ℝ => fun i => Du i x) :=
      Measurable.of_eval hDu_meas
    have hnum : Measurable
        (fun x : Fin d → ℝ => ‖fun i => Du i x‖ ^ αt) :=
      (hDuvec.norm.pow_const αt)
    have hden : AEMeasurable
        (fun x : Fin d → ℝ => muRe k m u V Du H x ^ τ + 1)
        (Measure.restrict volume (UnitCube d)) :=
      (hμre_meas.pow_const τ).add aemeasurable_const
    exact (hnum.aemeasurable.div hden).aestronglyMeasurable
  -- (g) the quotient is non-negative a.e. (using `0 ≤ μ_re` a.e.).
  have hμre_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      0 ≤ muRe k m u V Du H x :=
    muRe_nonneg_ae hae_m_nn hae_ne
  have h_quotient_nn :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        0 ≤ ‖fun i => Du i x‖ ^ αt /
              (muRe k m u V Du H x ^ τ + 1) := by
    filter_upwards [hμre_nn] with x hx_nn
    have hnum_nn : 0 ≤ ‖fun i => Du i x‖ ^ αt :=
      Real.rpow_nonneg (norm_nonneg _) _
    have hden_pos : 0 < muRe k m u V Du H x ^ τ + 1 := by
      have : 0 ≤ muRe k m u V Du H x ^ τ :=
        Real.rpow_nonneg hx_nn _
      linarith
    exact div_nonneg hnum_nn hden_pos.le
  -- (h) the pointwise domination `Q x ≤ G x` a.e.
  have hlower := hcong.lower
  -- Boundary lower bound `g₀ ≤ H(·,0)` at `μ_re = 0` via (a:Hat0).
  have hlow0 :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        (1 / C) * (1 / ((0 : ℝ) ^ τ + 1)) *
            (‖fun i => Du i x‖ ^ αt) - C * ((0 : ℝ) ^ β + 1)
          ≤ H x (fun i => Du i x) 0 := by
    filter_upwards [hcong.lower_extends_to_zero hHat0, hAgree]
      with x hx_ext hx_agree
    have hext := hx_ext (fun i => Du i x)
    have hagree_x :
        ((H x (fun i => Du i x) 0 : ℝ) : WithTop ℝ)
          = StationaryMFG.Hamiltonian.Hext H x (fun i => Du i x) 0 :=
      hx_agree (fun i => Du i x)
    rw [← hagree_x] at hext
    have hreal :
        (1 / C) * (1 / ((0 : ℝ) ^ τ + 1)) *
            (‖(fun i => Du i x)‖ ^ (α * (1 + τ / β))) - C
          ≤ H x (fun i => Du i x) 0 := by
      have := hext
      rw [← hCdef, ← hαdef, ← hβdef, ← hτdef] at this
      exact_mod_cast this
    have h0β : (0 : ℝ) ^ β = 0 := Real.zero_rpow hβ.ne'
    rw [h0β, hαtdef]; simpa using hreal
  -- Boundary HJB-upper bound at `μ_re = 0` (mirrors `muRe_prod_integrable`).
  have hHJB0 :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        muReInner k u V Du H x ≤ 0 →
          u x + H x (fun i => Du i x) 0 - V x ≤ -k := by
    filter_upwards [hae_anti, hae_ne, hHat0.exists_limit_at_zero, hAgree]
      with x hx_anti hx_ne hx_limit hx_agree hμle0
    have hwit := (muReInner_le_zero_iff_of_antitoneOn_Ioi hx_anti hx_ne).mp hμle0
    have hTendsto :
        Filter.Tendsto
          (fun ν : ℝ => ((H x (fun i => Du i x) ν : ℝ) : WithTop ℝ))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (StationaryMFG.Hamiltonian.H_at_zero H x (fun i => Du i x))) :=
      StationaryMFG.Hamiltonian.tendsto_Hext_zero_of_exists
        (hx_limit (fun i => Du i x))
    set b : ℝ := -k - u x + V x with hb_def
    by_cases hzero : ∃ n : ℕ, ∃ q : ℚ,
        (q : ℝ) = 0 ∧ 0 ≤ (q : ℝ) ∧ (q : ℝ) < 1 / ((n : ℝ) + 1) ∧
          u x + H x (fun i => Du i x) (q : ℝ) - V x ≤ -k
    · obtain ⟨_, _, hq_eq0, _, _, hHJB_q⟩ := hzero
      rw [hq_eq0] at hHJB_q; exact hHJB_q
    · have hPointwise : ∀ ν : ℝ, 0 < ν →
          u x + H x (fun i => Du i x) ν - V x ≤ -k := by
        intro ν hν
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hν
        obtain ⟨q, hq_nn, hq_hi, hHJB_q⟩ := hwit n
        have hq_lt_ν : (q : ℝ) < ν := by
          have h1 : (1 : ℝ) / ((n : ℝ) + 1) < ν := by
            simpa only [one_div] using hn
          exact lt_trans hq_hi h1
        have hq_pos : 0 < (q : ℝ) := by
          rcases eq_or_lt_of_le hq_nn with hq0 | hq_pos
          · exact absurd ⟨n, q, hq0.symm, hq_nn, hq_hi, hHJB_q⟩ hzero
          · exact hq_pos
        have hanti_le :
            H x (fun i => Du i x) ν ≤ H x (fun i => Du i x) (q : ℝ) :=
          hx_anti hq_pos (lt_trans hq_pos hq_lt_ν) hq_lt_ν.le
        linarith [hHJB_q]
      have hEv :
          ∀ᶠ ν in nhdsWithin 0 (Set.Ioi 0),
            ((H x (fun i => Du i x) ν : ℝ) : WithTop ℝ) ≤ ((b : ℝ) : WithTop ℝ) := by
        refine Filter.eventually_iff_exists_mem.mpr ⟨Set.Ioi (0 : ℝ),
          self_mem_nhdsWithin, fun ν hν => ?_⟩
        have := hPointwise ν hν
        have hle : H x (fun i => Du i x) ν ≤ b := by rw [hb_def]; linarith
        exact_mod_cast hle
      have hHext_le :
          StationaryMFG.Hamiltonian.H_at_zero H x (fun i => Du i x)
            ≤ ((b : ℝ) : WithTop ℝ) := le_of_tendsto hTendsto hEv
      have hAgree_x :
          ((H x (fun i => Du i x) 0 : ℝ) : WithTop ℝ)
            = StationaryMFG.Hamiltonian.H_at_zero H x (fun i => Du i x) := by
        rw [StationaryMFG.Hamiltonian.H_at_zero_def]
        exact hx_agree (fun i => Du i x)
      have hraw_le :
          ((H x (fun i => Du i x) 0 : ℝ) : WithTop ℝ) ≤ ((b : ℝ) : WithTop ℝ) := by
        rw [hAgree_x]; exact hHext_le
      have hraw : H x (fun i => Du i x) 0 ≤ b := by exact_mod_cast hraw_le
      rw [hb_def] at hraw; linarith
  have h_envelope :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ‖fun i => Du i x‖ ^ αt /
            (muRe k m u V Du H x ^ τ + 1) ≤ G x := by
    filter_upwards [hμre_nn, hae_m_nn, hlower, h_step1, hae_anti, hae_cont,
        hae_ne, hlow0, hHJB0]
      with x hx_nn hx_m_nn hlow_x hstep1_x hx_anti hx_cont hx_ne hx_low0 hx_HJB0
    set μ : ℝ := muRe k m u V Du H x with hμ_def
    set P : ℝ := ‖fun i => Du i x‖ ^ αt with hP_def
    have hP_nn : 0 ≤ P := Real.rpow_nonneg (norm_nonneg _) _
    have hμ_le_m : μ ≤ m x := muRe_le_m k m u V Du H x
    have hμβ_le_mβ : μ ^ β ≤ m x ^ β := Real.rpow_le_rpow hx_nn hμ_le_m hβ.le
    -- The lower bound at `μ` (boundary handled at `μ = 0` via (a:Hat0)).
    have hH_ge :
        (1 / C) * (1 / (μ ^ τ + 1)) * P - C * (μ ^ β + 1)
          ≤ H x (fun i => Du i x) μ := by
      rcases eq_or_lt_of_le hx_nn with hμ0 | hμpos
      · -- `μ = 0`: use the (a:Hat0) boundary lower bound `hx_low0`.
        show (1 / C) * (1 / (μ ^ τ + 1)) * P - C * (μ ^ β + 1)
          ≤ H x (fun i => Du i x) μ
        rw [← hμ0, hP_def]; exact hx_low0
      · -- `μ > 0`: direct.
        have hlb := hlow_x (fun i => Du i x) μ hμpos
        rw [← hCdef, ← hβdef, ← hτdef, ← hαdef] at hlb
        show (1 / C) * (1 / (μ ^ τ + 1)) * P - C * (μ ^ β + 1)
          ≤ H x (fun i => Du i x) μ
        rw [hP_def, hαtdef]
        exact hlb
    -- HJB membership at `μ_re`: on `{μ_re < m}` the inner branch is active
    -- and `u + H − V ≤ −k`; on `{μ_re = m}` we use the inner-infimum bound
    -- directly only when active.  We obtain `H(x, Du, μ) ≤ −k − u + V` via
    -- the inner-set membership at `μ_re` (when it equals the inner inf).
    -- Either way we derive `H(x, Du, μ) ≤ −k − u x + V x` from membership.
    -- `H(x, Du, μ_re) ≤ |k| − u x + V x`:
    --  • on `{μ_re < m}` the inner branch is active (`μ_re = muReInner ∈
    --    muReSet`), giving `u + H − V ≤ −k`, hence `H ≤ −k − u + V ≤ |k| − u + V`;
    --  • on `{μ_re = m}` the Step-1 bound `u + H(·, m) − V ≤ 0` gives
    --    `H ≤ −u + V ≤ |k| − u + V`.
    have hH_le : H x (fun i => Du i x) μ ≤ |k| - u x + V x := by
      rcases lt_or_eq_of_le hμ_le_m with hμ_lt | hμ_eq
      · -- `μ < m`: inner branch active, `μ = muReInner ∈ muReSet`.
        have h_inner_lt_m : muReInner k u V Du H x < m x := by
          by_contra hnot
          push_neg at hnot
          have : μ = m x := by rw [hμ_def, muRe, min_eq_left hnot]
          linarith
        have hμ_eq_inner : μ = muReInner k u V Du H x := by
          rw [hμ_def, muRe, min_eq_right h_inner_lt_m.le]
        have hHJB :
            u x + H x (fun i => Du i x) (muReInner k u V Du H x) - V x ≤ -k := by
          rcases eq_or_lt_of_le (muReInner_nonneg_of_nonempty hx_ne)
            with hinner0 | hinner_pos
          · rw [← hinner0]; exact hx_HJB0 (le_of_eq hinner0.symm)
          · exact (muReInner_mem_of_pos_of_continuousOn_Ioi hx_cont hx_ne
              hinner_pos).2
        have hk_le : -k ≤ |k| := by have := neg_abs_le k; linarith
        rw [hμ_eq_inner]; linarith
      · -- `μ = m`: use the Step-1 bound `u + H(·, m) − V ≤ 0`.
        have hμ_H : H x (fun i => Du i x) μ = H x (fun i => Du i x) (m x) := by
          rw [hμ_eq]
        have hk_nn : (0 : ℝ) ≤ |k| := abs_nonneg k
        rw [hμ_H]; linarith
    -- Combine the two bounds.
    have hden_pos : 0 < μ ^ τ + 1 := by
      have : 0 ≤ μ ^ τ := Real.rpow_nonneg hx_nn _
      linarith
    have hμβ_nn : 0 ≤ μ ^ β := Real.rpow_nonneg hx_nn _
    have hstep : (1 / C) * (1 / (μ ^ τ + 1)) * P
        ≤ |k| - u x + V x + C * (μ ^ β + 1) := by
      have := le_trans hH_ge hH_le
      linarith
    have hCstep :
        P / (μ ^ τ + 1)
          ≤ C * (|k| - u x + V x + C * (μ ^ β + 1)) := by
      have hmul := mul_le_mul_of_nonneg_left hstep hC_nn
      have hlhs : C * ((1 / C) * (1 / (μ ^ τ + 1)) * P)
          = P / (μ ^ τ + 1) := by field_simp
      rw [hlhs] at hmul
      exact hmul
    -- Replace `μ^β` by `m^β` and bound `|k| − u + V ≤ |k| + |u| + |V|`.
    have hbound2 :
        C * (|k| - u x + V x + C * (μ ^ β + 1))
          ≤ C * (|k| + |u x| + |V x| + C * (m x ^ β + 1) + C) := by
      apply mul_le_mul_of_nonneg_left _ hC_nn
      have hCμβ_le : C * (μ ^ β + 1) ≤ C * (m x ^ β + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) hC_nn
      have h3 : -u x ≤ |u x| := by have := neg_abs_le (u x); linarith
      have h4 : V x ≤ |V x| := le_abs_self (V x)
      linarith [hC_nn]
    show ‖fun i => Du i x‖ ^ αt / (μ ^ τ + 1)
        ≤ C * (|k| + |u x| + |V x| + C * (m x ^ β + 1) + C)
    calc ‖fun i => Du i x‖ ^ αt / (μ ^ τ + 1)
        = P / (μ ^ τ + 1) := by rw [hP_def]
      _ ≤ C * (|k| - u x + V x + C * (μ ^ β + 1)) := hCstep
      _ ≤ C * (|k| + |u x| + |V x| + C * (m x ^ β + 1) + C) := hbound2
  -- Assemble via `MemLp.of_le_mul (c := 1)` against the dominator `G`.
  apply MemLp.toMemLpPer
  apply MemLp.of_le_mul (c := 1) hG_mem.toMemLp h_meas
  filter_upwards [h_quotient_nn, hG_nn, h_envelope] with x hq_nn hg_nn hxle
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hq_nn,
    abs_of_nonneg hg_nn, one_mul]
  exact hxle

end Congestion
end StationaryMFG
