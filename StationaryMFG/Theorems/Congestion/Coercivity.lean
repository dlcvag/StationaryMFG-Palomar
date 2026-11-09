module

/-
Copyright (c) 2026 Stationary MFG project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import StationaryMFG.Theorems.Congestion.Existence
public import StationaryMFG.Theorems.SimplePower.Coercivity
public import StationaryMFG.Theorems.SimplePower.Coercivity.Integrability
public import StationaryMFG.Hamiltonian.Assumptions

@[expose] public section

/-!
# Congestion coercivity, child 1: coercive gauge + hierarchy lower-bound bridge

This file is the first sub-task (`BB1d child1`) of the congestion
coercivity block (paper `prop:coercAepsi` reuse, `thm:weakAepsi.congestion`
proof, `Source/FGU-monotone_revised.tex` lines 1369–1377).

The paper says coercivity of `A_ε` on `𝓚` follows "the same line of
argument as `prop:coercAepsi`", the only adaptation being that the simple
lower bound `H(x,p,m) ≥ ‖p‖^α/C − C(m^β+1)` (`eq:assH.lower.simple`)
comes from the congestion lower bound `eq:assH.lower.congestion`
(`hcong.lower`) **via the hierarchy** (`rem:hierarchy`, tex line 517).

That hierarchy bridge is *already formalised* as
`CongestionGrowthCore.toWeakGrowth` (Assumptions.lean): its `.lower`
field is precisely the simple lower bound at the inflated constant
`hcong.toWeakGrowth.C`. We therefore set the congestion coercivity
constant to be that very constant and read off the bridge in one line.

Deliverables:

* `congestionCoercivityConstant` — the inflated coercivity constant
  `C' := hcong.toWeakGrowth.C` (genuinely derived from the Young hierarchy
  step inside `toWeakGrowth`, not assumed);
* `congestionCoercivityConstant_pos`;
* `congestionCoerciveGauge` — the LHS of `eq:coercive.Aepsi` (paper line
  958) for the congestion operator, at the congestion exponents;
* `congestionCoerciveGauge_nonneg`;
* `congestion_coercivity_h_lower_from_hcong` — the hierarchy bridge
  (cited: `hcong.toWeakGrowth.lower`);
* `congestion_coercivity_h_H01_le`;
* `congestion_coercivity_h_DpH01_le`.
-/

namespace StationaryMFG
namespace Congestion

open MeasureTheory Set
open StationaryMFG.Periodic
open StationaryMFG.Solutions.MFG
open StationaryMFG.Hamiltonian
open scoped ENNReal NNReal

variable {d : ℕ}
variable {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
variable {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
variable {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}

/-! ## The congestion coercivity constant -/

/-- **Congestion coercivity constant** `C' := hcong.toWeakGrowth.C`.

This is the inflated constant produced by the hierarchy bridge
`CongestionGrowthCore.toWeakGrowth` (paper `rem:hierarchy`,
tex line 517). It is *genuinely derived* from `hcong` — the Young-type
absorption that turns `eq:assH.lower.congestion` into the simple lower
bound `eq:assH.lower.simple` happens inside `toWeakGrowth`, and the
resulting constant is exactly this `C'`. Choosing the coercivity
constant to be `toWeakGrowth.C` makes the simple lower bound at this
constant literally the `.lower` field of `hcong.toWeakGrowth`. -/
noncomputable def congestionCoercivityConstant
    (hcong : CongestionGrowthCore (d := d) H DpH J) : ℝ :=
  hcong.toWeakGrowth.C

/-- Positivity of the congestion coercivity constant. -/
lemma congestionCoercivityConstant_pos
    (hcong : CongestionGrowthCore (d := d) H DpH J) :
    0 < congestionCoercivityConstant (d := d) hcong :=
  hcong.toWeakGrowth.hC

/-! ## The congestion coercive gauge -/

/-- **Congestion coercive gauge** — the LHS of `eq:coercive.Aepsi`
(paper line 958) for the congestion operator `A_ε`, at the congestion
exponents `β̄ = β + 1`, `γ̄ = α(β+1)/β`.

It is the same shape as the simple-power coercive gauge, with
`α := hcong.α`, `β := hcong.β`, `γBar := hcong.α*(hcong.β+1)/hcong.β`,
applied to a point `v = (m, u, Du)` of the congestion Banach space:

* `(1/C_eul) · ∫ m^{β+1}` — the mass term;
* `(1/C_eul) · ∫ ‖Du‖^α` — the momentum term;
* `ε · ∫ (|Du|^{γ̄-2}(Du·Du) + |u|^{γ̄-2}(u·u))` — the regularising
  `γ̄`-Laplacian term. -/
noncomputable def congestionCoerciveGauge
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    (C_eul ε : ℝ)
    (v : congestionXBanach d
           (ENNReal.ofReal (hcong.β + 1))
           (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))) : ℝ :=
  (1 / C_eul) * (∫ x in UnitCube d, (⇑v.1 x) ^ (hcong.β + 1))
  + (1 / C_eul) * (∫ x in UnitCube d,
      ‖fun i => (⇑(v.2.2 i) : (Fin d → ℝ) → ℝ) x‖ ^ hcong.α)
  + ε * (∫ x in UnitCube d,
      vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
          (fun i => (⇑(v.2.2 i) : (Fin d → ℝ) → ℝ) x)
        * ((fun i => (⇑(v.2.2 i) : (Fin d → ℝ) → ℝ) x)
            ⬝ (fun i => (⇑(v.2.2 i) : (Fin d → ℝ) → ℝ) x))
      + absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β) (⇑v.2.1 x)
          * (⇑v.2.1 x * ⇑v.2.1 x))

/-- Sanity `example`: the gauge type-checks at concrete arguments. -/
noncomputable example
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    (C_eul ε : ℝ)
    (v : congestionXBanach d
           (ENNReal.ofReal (hcong.β + 1))
           (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))) :
    ℝ :=
  congestionCoerciveGauge (d := d) hcong C_eul ε v

/-! ## Nonnegativity of the gauge

Each integrand is a nonnegative real function:

* `m^{β+1} ≥ 0` whenever `m ≥ 0` a.e. (`Real.rpow_nonneg`) — the density
  `m = ⇑v.1` is nonnegative a.e. on the cube for any `v` in the
  admissible domain `𝓚` (`essinf μ > 0`), so we carry this as an explicit
  a.e.-positivity hypothesis on `v.1`;
* `‖Du‖^α ≥ 0` (`Real.rpow_nonneg`, `norm_nonneg`);
* the `γ̄`-Laplacian integrand is
  `(Du⬝Du)^{(γ̄-2)/2}·(Du⬝Du) + |u|^{γ̄-2}·u² ≥ 0`, since `Du⬝Du ≥ 0`,
  `(Du⬝Du)^{(γ̄-2)/2} ≥ 0` (`Real.rpow_nonneg`), `|u|^{γ̄-2} ≥ 0`
  (`Real.rpow_nonneg`), and `u² ≥ 0`.

With `0 < C_eul` and `0 < ε` the scaling factors are nonnegative, so the
whole gauge is nonnegative. -/
lemma congestionCoerciveGauge_nonneg
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    {C_eul ε : ℝ} (hC : 0 < C_eul) (hε : 0 < ε)
    (v : congestionXBanach d
           (ENNReal.ofReal (hcong.β + 1))
           (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))
    (hv_pos : 0 ≤ᵐ[volume.restrict (UnitCube d)] (⇑v.1 : (Fin d → ℝ) → ℝ)) :
    0 ≤ congestionCoerciveGauge (d := d) hcong C_eul ε v := by
  unfold congestionCoerciveGauge
  have hCinv : 0 ≤ 1 / C_eul := by positivity
  -- Mass integral ≥ 0 (uses a.e. positivity of the density).
  have hmass : 0 ≤ ∫ x in UnitCube d, (⇑v.1 x) ^ (hcong.β + 1) := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [hv_pos] with x hx
    exact Real.rpow_nonneg hx _
  -- Momentum integral ≥ 0.
  have hmom : 0 ≤ ∫ x in UnitCube d,
      ‖fun i => (⇑(v.2.2 i) : (Fin d → ℝ) → ℝ) x‖ ^ hcong.α := by
    refine integral_nonneg ?_
    intro x
    exact Real.rpow_nonneg (norm_nonneg _) _
  -- γ̄-Laplacian integral ≥ 0.
  have hreg : 0 ≤ ∫ x in UnitCube d,
      vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
          (fun i => (⇑(v.2.2 i) : (Fin d → ℝ) → ℝ) x)
        * ((fun i => (⇑(v.2.2 i) : (Fin d → ℝ) → ℝ) x)
            ⬝ (fun i => (⇑(v.2.2 i) : (Fin d → ℝ) → ℝ) x))
      + absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β) (⇑v.2.1 x)
          * (⇑v.2.1 x * ⇑v.2.1 x) := by
    refine integral_nonneg ?_
    intro x
    refine add_nonneg ?_ ?_
    · -- `(Du⬝Du)^{(γ̄-2)/2} · (Du⬝Du) ≥ 0`.
      have hdot_nn : 0 ≤ (fun i => (⇑(v.2.2 i) : (Fin d → ℝ) → ℝ) x)
          ⬝ (fun i => (⇑(v.2.2 i) : (Fin d → ℝ) → ℝ) x) := by
        unfold dotProduct
        exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
      refine mul_nonneg ?_ hdot_nn
      unfold vecAbsPowMinusTwo
      exact Real.rpow_nonneg hdot_nn _
    · -- `|u|^{γ̄-2} · u² ≥ 0`.
      refine mul_nonneg ?_ (mul_self_nonneg _)
      unfold absPowMinusTwo
      exact Real.rpow_nonneg (abs_nonneg _) _
  have h1 : 0 ≤ (1 / C_eul) * (∫ x in UnitCube d, (⇑v.1 x) ^ (hcong.β + 1)) :=
    mul_nonneg hCinv hmass
  have h2 : 0 ≤ (1 / C_eul) * (∫ x in UnitCube d,
      ‖fun i => (⇑(v.2.2 i) : (Fin d → ℝ) → ℝ) x‖ ^ hcong.α) :=
    mul_nonneg hCinv hmom
  have h3 : 0 ≤ ε * (∫ x in UnitCube d,
      vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
          (fun i => (⇑(v.2.2 i) : (Fin d → ℝ) → ℝ) x)
        * ((fun i => (⇑(v.2.2 i) : (Fin d → ℝ) → ℝ) x)
            ⬝ (fun i => (⇑(v.2.2 i) : (Fin d → ℝ) → ℝ) x))
      + absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β) (⇑v.2.1 x)
          * (⇑v.2.1 x * ⇑v.2.1 x)) :=
    mul_nonneg hε.le hreg
  linarith

/-! ## The hierarchy lower-bound bridge (`rem:hierarchy`)

The bridge from the congestion lower bound `eq:assH.lower.congestion`
(`hcong.lower`) to the simple lower bound `eq:assH.lower.simple` is
exactly the `.lower` field of `hcong.toWeakGrowth`, which performs the
Young-type absorption inside `CongestionGrowthCore.toWeakGrowth`
(paper `rem:hierarchy`, tex line 517). Since
`congestionCoercivityConstant hcong = hcong.toWeakGrowth.C` and
`toWeakGrowth.α = hcong.α`, `toWeakGrowth.β = hcong.β` definitionally, the
simple lower bound at the congestion coercivity constant is read off
directly. -/

/-- **Hierarchy bridge (deliverable 3).** From `hcong.lower` (via
`hcong.toWeakGrowth.lower`, the Young absorption of `rem:hierarchy`)
obtain the simple-power lower bound at `C' = congestionCoercivityConstant`:
`H(x,p,m) ≥ ‖p‖^α/C' − C'(m^β+1)` for `m > 0`. -/
lemma congestion_coercivity_h_lower_from_hcong
    (hcong : CongestionGrowthCore (d := d) H DpH J) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p m, 0 < m →
        ‖p‖ ^ hcong.α / congestionCoercivityConstant (d := d) hcong
          - congestionCoercivityConstant (d := d) hcong * (m ^ hcong.β + 1)
          ≤ H x p m := by
  -- `congestionCoercivityConstant = hcong.toWeakGrowth.C`,
  -- `hcong.toWeakGrowth.α = hcong.α`, `hcong.toWeakGrowth.β = hcong.β` (rfl).
  filter_upwards [hcong.toWeakGrowth.lower] with x hx p m hm
  exact (hx p m hm)

/-! ## The `|H(x,0,1)|` and `‖DpH(x,0,1)‖` bounds -/

/-- **`h_H01_le` (deliverable 4)**: `|H(x,0,1)| ≤ C'`.

From the upper bound `hcong.toWeakGrowth.upper` at `m = 1`
(`H(x,0,1) ≤ -1/C' + C' ≤ C'`) and the hierarchy lower bound at
`(p,m) = (0,1)` (`H(x,0,1) ≥ -C'(1+1) = -2C' ≥ -... `). We use the
simple lower bound from `congestion_coercivity_h_lower_from_hcong`.
Mirror of `paperHypotheses_H01_le_uniform`. -/
lemma congestion_coercivity_h_H01_le
    (hcong : CongestionGrowthCore (d := d) H DpH J) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      |H x (0 : Fin d → ℝ) 1|
        ≤ 2 * congestionCoercivityConstant (d := d) hcong := by
  set C' : ℝ := congestionCoercivityConstant (d := d) hcong with hC'
  have hC'_pos : 0 < C' := congestionCoercivityConstant_pos (d := d) hcong
  -- `congestionCoercivityConstant = toWeakGrowth.C`, and the weak upper
  -- bound is stated at `toWeakGrowth.C` and `toWeakGrowth.β = hcong.β`.
  have hCeq : C' = hcong.toWeakGrowth.C := rfl
  filter_upwards [hcong.toWeakGrowth.upper,
    congestion_coercivity_h_lower_from_hcong (d := d) hcong]
    with x hUp hLow
  -- Upper at `m = 1`: `H x 0 1 ≤ -(1^β)/C' + C' = -1/C' + C'`.
  have hup := hUp 1 one_pos
  have hone : (1 : ℝ) ^ hcong.toWeakGrowth.β = 1 := Real.one_rpow _
  rw [hone, ← hCeq] at hup
  -- Lower at `(p,m) = (0,1)`: `0^α/C' - C'*(1^β+1) ≤ H x 0 1`.
  have hlow := hLow (0 : Fin d → ℝ) 1 one_pos
  have hα_pos : 0 < hcong.α := lt_trans one_pos hcong.hα
  have hzero_α : ‖(0 : Fin d → ℝ)‖ ^ hcong.α = 0 := by
    rw [norm_zero, Real.zero_rpow (ne_of_gt hα_pos)]
  have hone_β : (1 : ℝ) ^ hcong.β = 1 := Real.one_rpow _
  rw [hzero_α, hone_β] at hlow
  -- `hlow : 0/C' - C'*(1+1) ≤ H x 0 1`, i.e. `-2C' ≤ H x 0 1`.
  -- Upper side: `H x 0 1 ≤ -1/C' + C' ≤ C' ≤ 2C'`.
  rw [abs_le]
  constructor
  · -- `-2C' ≤ H x 0 1`.
    have hzdiv : (0 : ℝ) / C' = 0 := zero_div _
    rw [hzdiv] at hlow
    nlinarith [hlow, hC'_pos]
  · -- `H x 0 1 ≤ 2C'`.
    -- `hup : H x 0 1 ≤ -1 / C' + C'`. With `-1/C' = -(1/C') ≤ 0`, get `≤ C' ≤ 2C'`.
    have hneg : (-1 : ℝ) / C' = -(1 / C') := by ring
    rw [hneg] at hup
    have hinv_nn : 0 ≤ (1 : ℝ) / C' := by positivity
    nlinarith [hup, hinv_nn, hC'_pos]

/-- **`h_DpH01_le` (deliverable 5)**: `‖DpH(x,0,1)‖ ≤ 2C'`.

From `hcong.DpH_upper` at `(p,m) = (0,1)`:
`‖DpH(x,0,1)‖ ≤ C·(1/1 + 1/1^τ)·‖0‖^{α(1+τ/β)-1} + C·(1^{β-β/α} + 1/1)
            = C·(0) + C·(1 + 1) = 2C ≤ 2C'`,
using `α(1+τ/β) - 1 > 0` (since `α > 1` and `τ/β ≥ 0`) so `‖0‖^{…} = 0`,
`1/1^τ = 1`, `1^{β-β/α} = 1`, and `hcong.C ≤ hcong.toWeakGrowth.C = C'`.
Mirror of `paperHypotheses_DpH01_le_uniform`. -/
lemma congestion_coercivity_h_DpH01_le
    (hcong : CongestionGrowthCore (d := d) H DpH J) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ‖DpH x (0 : Fin d → ℝ) 1‖
        ≤ 2 * congestionCoercivityConstant (d := d) hcong := by
  set C' : ℝ := congestionCoercivityConstant (d := d) hcong with hC'
  have hC'_pos : 0 < C' := congestionCoercivityConstant_pos (d := d) hcong
  have hC_pos : 0 < hcong.C := hcong.hC
  -- `hcong.C ≤ toWeakGrowth.C = C'` (established inside `toWeakGrowth`).
  have hC_le_C' : hcong.C ≤ C' := by
    rw [hC']
    -- `congestionCoercivityConstant = toWeakGrowth.C`; dominance below.
    have hβ_pos : 0 < hcong.β := hcong.hβ
    have hτ_nonneg : 0 ≤ hcong.τ := hcong.hτ.1
    have hβτ_pos : 0 < hcong.β + hcong.τ := by linarith
    have h2pow_ge_one : (1 : ℝ) ≤ (2 : ℝ) ^ (hcong.β / (hcong.β + hcong.τ)) := by
      have hexp_nonneg : (0 : ℝ) ≤ hcong.β / (hcong.β + hcong.τ) :=
        div_nonneg hβ_pos.le hβτ_pos.le
      exact Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2) hexp_nonneg
    -- `toWeakGrowth.C = C·2^(β/(β+τ)) + C + 1/C`.
    change hcong.C ≤ hcong.C * 2 ^ (hcong.β / (hcong.β + hcong.τ)) + hcong.C + 1 / hcong.C
    have hdom : hcong.C ≤ hcong.C * 2 ^ (hcong.β / (hcong.β + hcong.τ)) := by
      have := mul_le_mul_of_nonneg_left h2pow_ge_one hC_pos.le
      linarith
    have hinv_nn : 0 ≤ 1 / hcong.C := by positivity
    linarith
  -- Exponent positivity: `α(1+τ/β) - 1 > 0`.
  have hα_gt_one : 1 < hcong.α := hcong.hα
  have hβ_pos : 0 < hcong.β := hcong.hβ
  have hτ_nonneg : 0 ≤ hcong.τ := hcong.hτ.1
  have hexp_pos : 0 < hcong.α * (1 + hcong.τ / hcong.β) - 1 := by
    have hτβ_nonneg : (0 : ℝ) ≤ hcong.τ / hcong.β := div_nonneg hτ_nonneg hβ_pos.le
    have h1 : (1 : ℝ) ≤ 1 + hcong.τ / hcong.β := by linarith
    have : (1 : ℝ) < hcong.α * (1 + hcong.τ / hcong.β) := by
      calc (1 : ℝ) < hcong.α := hα_gt_one
        _ = hcong.α * 1 := (mul_one _).symm
        _ ≤ hcong.α * (1 + hcong.τ / hcong.β) :=
            mul_le_mul_of_nonneg_left h1 (le_of_lt (lt_trans one_pos hα_gt_one))
    linarith
  filter_upwards [hcong.DpH_upper] with x hDU
  have h := hDU (0 : Fin d → ℝ) 1 one_pos
  -- Simplify the RHS at `(0,1)`.
  have hzero_pow : ‖(0 : Fin d → ℝ)‖ ^ (hcong.α * (1 + hcong.τ / hcong.β) - 1) = 0 := by
    rw [norm_zero, Real.zero_rpow (ne_of_gt hexp_pos)]
  have hone_τ : (1 : ℝ) ^ hcong.τ = 1 := Real.one_rpow _
  have hone_q : (1 : ℝ) ^ (hcong.β - hcong.β / hcong.α) = 1 := Real.one_rpow _
  rw [hzero_pow, hone_τ, hone_q] at h
  -- `h : ‖DpH x 0 1‖ ≤ C*(1/1 + 1/1)*0 + C*(1 + 1/1) = 2C`.
  have hsimp :
      hcong.C * (1 / (1 : ℝ) + 1 / (1 : ℝ)) * 0 + hcong.C * (1 + 1 / (1 : ℝ))
        = 2 * hcong.C := by norm_num; ring
  rw [hsimp] at h
  -- `2C ≤ 2C'`.
  nlinarith [h, hC_le_C']


/-! ## Integrability residues for the congestion coercivity combined bound
(`BB1d child 2a`)

The five `IntegrableOn` residues (plus `hm_pos`) consumed by the
simple-power combined bound `coercivity_combined_from_paperHypotheses_uniform`
are **not** fields of `MFGOpEpsAuxHyps`; they require a dedicated
derivation (mirror of `coercivity_combined_integrability_residues` in
`SimplePower/Coercivity/Integrability.lean`). This section ports that
block to the congestion `v ∈ congestionBanachK`, reusing:

* the **v-side** `MFGOpEpsAuxHyps` certificate from
  `congestion_auxHyps_of_mem_congestionBanachK'` (child B2b);
* child-1's `congestion_coercivity_h_H01_le` /
  `congestion_coercivity_h_DpH01_le` for the `(0,1,0)` base-point
  `F_HJB`/`F_flux` dominators;
* `hV` for the `V` part of the base-point `F_HJB` dominator.

The mass/momentum residues come from the `Lp`-membership of the
`congestionXBanach` components (`v.1 ∈ Lp(β+1)`, `v.2.2 i ∈ Lp(γ̄)`).
-/

open StationaryMFG.Theorems.SimplePower
open StationaryMFG.Theorems.SimplePower.Banach

/-- **Vector-valued `MemLpPer` from per-coordinate `MemLpPer`** (local
copy; adapted from `Hamiltonian.Estimates.memLpPer_pi_of_coord`, which
is `private`). For a family `Dυ i ∈ L^p`, the assembled vector
`x ↦ (Dυ · x)` is also `L^p`, bounded coordinatewise by the sum of
absolute values. -/
private theorem congestion_memLpPer_pi_of_coord
    {p : ℝ≥0∞} (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (hDυ : ∀ i, Periodic.MemLpPer (d := d) p (Dυ i)) :
    Periodic.MemLpPer (d := d) p
      (fun x : (Fin d → ℝ) => fun i : Fin d => Dυ i x) := by
  haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  set Dom : (Fin d → ℝ) → ℝ := fun x => ∑ i : Fin d, |Dυ i x| with hDom_def
  have habs_memLp : ∀ i, Periodic.MemLpPer (d := d) p (fun x => |Dυ i x|) := by
    intro i
    have h2 := (hDυ i).toMemLp.norm
    have heq : (fun x => ‖Dυ i x‖) = fun x => |Dυ i x| := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at h2
    exact MemLp.toMemLpPer h2
  have hDom_memLp : Periodic.MemLpPer (d := d) p Dom := by
    have hsum :
        MemLp (fun x => ∑ i : Fin d, (fun x => |Dυ i x|) x) p
          (Measure.restrict volume (UnitCube d)) :=
      memLp_finset_sum (Finset.univ : Finset (Fin d))
        (fun i _ => (habs_memLp i).toMemLp)
    exact MemLp.toMemLpPer hsum
  have hbound :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ‖(fun i : Fin d => Dυ i x)‖ ≤ (1 : ℝ) * ‖Dom x‖ := by
    refine Filter.Eventually.of_forall ?_
    intro x
    have hsum_nn : 0 ≤ ∑ i, |Dυ i x| :=
      Finset.sum_nonneg (fun i _ => abs_nonneg _)
    have hpi : ‖(fun i : Fin d => Dυ i x)‖ ≤ ∑ i, |Dυ i x| := by
      rw [pi_norm_le_iff_of_nonneg hsum_nn]
      intro i
      have h1 : ‖Dυ i x‖ = |Dυ i x| := Real.norm_eq_abs _
      rw [h1]
      exact Finset.single_le_sum (f := fun j => |Dυ j x|)
        (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    rw [Real.norm_eq_abs, abs_of_nonneg hsum_nn, one_mul]
    exact hpi
  have hmeas :
      AEStronglyMeasurable
        (fun x : (Fin d → ℝ) => fun i : Fin d => Dυ i x)
        (Measure.restrict volume (UnitCube d)) := by
    have hAEm : AEMeasurable
        (fun x : (Fin d → ℝ) => fun i : Fin d => Dυ i x)
        (Measure.restrict volume (UnitCube d)) :=
      aemeasurable_pi_iff.mpr fun i => (hDυ i).aestronglyMeasurable.aemeasurable
    exact hAEm.aestronglyMeasurable
  exact MemLp.toMemLpPer (MemLp.of_le_mul hDom_memLp.toMemLp hmeas hbound)

/-- **Congestion integrability residues (`BB1d child 2a`).**

The 6-conjunct of integrability residues consumed by the simple-power
combined coercivity bound, ported to a congestion Banach pair
`v ∈ congestionBanachK …`. From `(hmon, hcong, hVmeas, hV, ε, hv)`. -/
theorem congestion_coercivity_integrability_residues
    {V : (Fin d → ℝ) → ℝ}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (ε : ℝ)
    {v : congestionXBanach d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))}
    (hv : v ∈ congestionBanachK d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ) :
    (∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < (⇑v.1 : (Fin d → ℝ) → ℝ) x) ∧
    IntegrableOn
      (fun x => (-(⇑v.2.1 x) - H x (fun i => ⇑(v.2.2 i) x) (⇑v.1 x) + V x)
                  * (⇑v.1 x - 1)
                + ⇑v.1 x * (DpH x (fun i => ⇑(v.2.2 i) x) (⇑v.1 x)
                              ⬝ (fun i => ⇑(v.2.2 i) x))
                + (⇑v.1 x - 1) * ⇑v.2.1 x) (UnitCube d) ∧
    IntegrableOn
      (fun x => (-(0 : ℝ) - H x (0 : Fin d → ℝ) 1 + V x) * (⇑v.1 x - 1)
                + 1 * (DpH x (0 : Fin d → ℝ) 1 ⬝ (fun i => ⇑(v.2.2 i) x))
                + (1 - 1) * ⇑v.2.1 x) (UnitCube d) ∧
    IntegrableOn
      (fun x => coerciveHamIntegrand H DpH (fun i => ⇑(v.2.2 i)) (⇑v.1) x)
      (UnitCube d) ∧
    IntegrableOn (fun x => (⇑v.1 x) ^ (hcong.β + 1)) (UnitCube d) ∧
    IntegrableOn
      (fun x => ‖fun i => (⇑(v.2.2 i) : (Fin d → ℝ) → ℝ) x‖ ^ hcong.α)
      (UnitCube d) := by
  classical
  haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  -- The paper exponents are kept *unfolded* (never `set`) so that the
  -- concrete-exponent type of `v` is never rewritten (which would fork
  -- `v` into a fresh `v✝` and break the aux/integrability applications).
  have hα_pos : 0 < hcong.α := lt_trans one_pos hcong.hα
  have hβ_pos : 0 < hcong.β := hcong.hβ
  have hβ1_pos : 0 < hcong.β + 1 := by linarith
  have hα_le_γBar : hcong.α ≤ hcong.α * (hcong.β + 1) / hcong.β := by
    rw [le_div_iff₀ hβ_pos]
    have : hcong.α * (hcong.β + 1) = hcong.α * hcong.β + hcong.α := by ring
    rw [this]; nlinarith
  have hα_le_γBar_enn : ENNReal.ofReal hcong.α
      ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β) :=
    ENNReal.ofReal_le_ofReal hα_le_γBar
  have hγBar_ne_top : ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  -- (1) `hm_pos` from the domain lower bound.
  have hm_pos : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      0 < (⇑v.1 : (Fin d → ℝ) → ℝ) x := by
    obtain ⟨_, _, ⟨c, hc_pos, hc_le⟩, _⟩ := hv.1
    filter_upwards [hc_le] with x hx
    exact lt_of_lt_of_le hc_pos hx
  -- `MemLpPer` certificates from the Lp components of `v`.
  have hmLp : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) (⇑v.1 : (Fin d → ℝ) → ℝ) :=
    Periodic.memLpPer_iff_memLp.mpr (MeasureTheory.Lp.memLp v.1)
  have huLp : MemLpPer (d := d) (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
      (⇑v.2.1 : (Fin d → ℝ) → ℝ) :=
    Periodic.memLpPer_iff_memLp.mpr (MeasureTheory.Lp.memLp v.2.1)
  have hDuLp : ∀ i, MemLpPer (d := d) (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
      (fun x => (⇑(v.2.2 i) : (Fin d → ℝ) → ℝ) x) :=
    fun i => Periodic.memLpPer_iff_memLp.mpr (MeasureTheory.Lp.memLp (v.2.2 i))
  -- (5) `hRpow_m_int`: `m^{β+1}` integrable.
  have hRpow_m_int : IntegrableOn
      (fun x => (⇑v.1 x) ^ (hcong.β + 1)) (UnitCube d) := by
    have hmemLp : MemLp (⇑v.1 : (Fin d → ℝ) → ℝ) (ENNReal.ofReal (hcong.β + 1))
        (volume.restrict (UnitCube d)) := hmLp.toMemLp
    have hp_ne_zero : ENNReal.ofReal (hcong.β + 1) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr hβ1_pos).ne'
    have hp_ne_top : ENNReal.ofReal (hcong.β + 1) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hint_norm : Integrable
        (fun x => ‖(⇑v.1 : (Fin d → ℝ) → ℝ) x‖ ^
            (ENNReal.ofReal (hcong.β + 1)).toReal)
        (volume.restrict (UnitCube d)) :=
      hmemLp.integrable_norm_rpow hp_ne_zero hp_ne_top
    have hp_toReal : (ENNReal.ofReal (hcong.β + 1)).toReal = hcong.β + 1 :=
      ENNReal.toReal_ofReal hβ1_pos.le
    rw [hp_toReal] at hint_norm
    refine hint_norm.congr ?_
    filter_upwards [hm_pos] with x hx
    rw [Real.norm_eq_abs, abs_of_pos hx]
  -- (6) `hRpow_p_int`: `‖Du‖^α` integrable.
  have hRpow_p_int : IntegrableOn
      (fun x => ‖fun i => (⇑(v.2.2 i) : (Fin d → ℝ) → ℝ) x‖ ^ hcong.α)
      (UnitCube d) := by
    have hDuLp_α : ∀ i, MemLpPer (d := d) (ENNReal.ofReal hcong.α)
        (fun x => (⇑(v.2.2 i) : (Fin d → ℝ) → ℝ) x) := by
      intro i
      exact (hDuLp i).mono_exponent_finite hα_le_γBar_enn hγBar_ne_top
    have hVecLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal hcong.α)
        (fun x : (Fin d → ℝ) => fun i : Fin d =>
          (⇑(v.2.2 i) : (Fin d → ℝ) → ℝ) x) :=
      congestion_memLpPer_pi_of_coord
        (fun i x => (⇑(v.2.2 i) : (Fin d → ℝ) → ℝ) x) hDuLp_α
    have hα_ne_zero : ENNReal.ofReal hcong.α ≠ 0 :=
      (ENNReal.ofReal_pos.mpr hα_pos).ne'
    have hα_ne_top : ENNReal.ofReal hcong.α ≠ ⊤ := ENNReal.ofReal_ne_top
    have hmemLp : MemLp
        (fun x : (Fin d → ℝ) => fun i : Fin d =>
          (⇑(v.2.2 i) : (Fin d → ℝ) → ℝ) x)
        (ENNReal.ofReal hcong.α) (volume.restrict (UnitCube d)) :=
      hVecLp.toMemLp
    have hint_norm : Integrable
        (fun x => ‖(fun i : Fin d => (⇑(v.2.2 i) : (Fin d → ℝ) → ℝ) x)‖ ^
            (ENNReal.ofReal hcong.α).toReal)
        (volume.restrict (UnitCube d)) :=
      hmemLp.integrable_norm_rpow hα_ne_zero hα_ne_top
    have hα_toReal : (ENNReal.ofReal hcong.α).toReal = hcong.α :=
      ENNReal.toReal_ofReal hα_pos.le
    rw [hα_toReal] at hint_norm
    exact hint_norm
  -- The v-side `MFGOpEpsAuxHyps` certificate (child B2b).
  have hauxV :
      Theorems.SimplePower.Banach.MFGOpEpsAuxHyps (d := d)
        (hcong.α * (hcong.β + 1) / hcong.β) (hcong.β + 1)
        ((hcong.β + 1) / hcong.β)
        (hcong.α * (hcong.β + 1) / hcong.β
          / (hcong.α * (hcong.β + 1) / hcong.β - 1))
        V H DpH
        (fun i x => (⇑(v.2.2 i) : (Fin d → ℝ) → ℝ) x)
        (⇑v.1 : (Fin d → ℝ) → ℝ)
        (⇑v.2.1 : (Fin d → ℝ) → ℝ) :=
    congestion_auxHyps_of_mem_congestionBanachK' hmon hcong hVmeas hV ε hv
  -- Test triple `MemLpPer`: `m-1 ∈ L^{β̄}`, `u, Du ∈ L^{γ̄}`.
  have hOneLp_β : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1))
      (fun _ : (Fin d → ℝ) => (1 : ℝ)) :=
    MemLp.toMemLpPer (memLp_const (1 : ℝ))
  have hmSub1_Lp : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1))
      (fun x : (Fin d → ℝ) => (⇑v.1 : (Fin d → ℝ) → ℝ) x - 1) := by
    have hsub : MemLp ((⇑v.1 : (Fin d → ℝ) → ℝ) - (fun _ => (1 : ℝ)))
        (ENNReal.ofReal (hcong.β + 1)) (volume.restrict (UnitCube d)) :=
      MeasureTheory.MemLp.sub hmLp.toMemLp hOneLp_β.toMemLp
    have heq : ((⇑v.1 : (Fin d → ℝ) → ℝ) - (fun _ : (Fin d → ℝ) => (1 : ℝ)))
              = (fun x : (Fin d → ℝ) => (⇑v.1 : (Fin d → ℝ) → ℝ) x - 1) := by
      funext x; rfl
    rw [heq] at hsub
    exact MemLp.toMemLpPer hsub
  -- (2) `hInt_mu`: from the v-side aux + test triple.
  have hInt_mu : IntegrableOn
      (fun x => (-(⇑v.2.1 x) - H x (fun i => ⇑(v.2.2 i) x) (⇑v.1 x) + V x)
                  * (⇑v.1 x - 1)
                + ⇑v.1 x * (DpH x (fun i => ⇑(v.2.2 i) x) (⇑v.1 x)
                              ⬝ (fun i => ⇑(v.2.2 i) x))
                + (⇑v.1 x - 1) * ⇑v.2.1 x) (UnitCube d) :=
    Theorems.SimplePower.Banach.integrable_mfgPair_integrand
      (γBarReal := hcong.α * (hcong.β + 1) / hcong.β) (βBarReal := hcong.β + 1)
      (βBarReal' := (hcong.β + 1) / hcong.β)
      (γBarReal' := (hcong.α * (hcong.β + 1) / hcong.β)
          / (hcong.α * (hcong.β + 1) / hcong.β - 1))
      hauxV hmSub1_Lp huLp hDuLp
  -- (3) `hInt_10`: build an `MFGOpEpsAuxHyps … 0 1 0` directly, reusing
  -- the v-side Hölder data and child-1's `(0,1)` bounds.
  -- Measurability of the constant-argument sections.
  have harg_meas : Measurable
      (fun x : (Fin d → ℝ) => (x, ((0 : Fin d → ℝ), (1 : ℝ)))) :=
    measurable_id.prodMk (measurable_const.prodMk measurable_const)
  have hHmeas : Measurable (fun x : (Fin d → ℝ) => H x (0 : Fin d → ℝ) 1) :=
    hcong.measurable_H.comp harg_meas
  have hDpHmeas : Measurable
      (fun x : (Fin d → ℝ) => DpH x (0 : Fin d → ℝ) 1) :=
    hcong.measurable_DpH.comp harg_meas
  have hAEm_HJB10 : AEStronglyMeasurable
      (fun x => -(0 : ℝ) - H x (0 : Fin d → ℝ) 1 + V x)
      (volume.restrict (UnitCube d)) :=
    (((measurable_const.sub hHmeas).aemeasurable).aestronglyMeasurable.add hVmeas)
  have hAEm_flux10 : ∀ i, AEStronglyMeasurable
      (fun x => (1 : ℝ) * (DpH x (0 : Fin d → ℝ) 1 i))
      (volume.restrict (UnitCube d)) := by
    intro i
    have hcoord : Measurable
        (fun x : (Fin d → ℝ) => (1 : ℝ) * (DpH x (0 : Fin d → ℝ) 1 i)) :=
      (measurable_const.mul ((measurable_pi_apply i).comp hDpHmeas))
    exact hcoord.aemeasurable.aestronglyMeasurable
  -- Hölder data + finiteness reused from the v-side aux.
  have hβconj : (hcong.β + 1).HolderConjugate ((hcong.β + 1) / hcong.β) :=
    hauxV.hβ
  have hγconj : (hcong.α * (hcong.β + 1) / hcong.β).HolderConjugate
      (hcong.α * (hcong.β + 1) / hcong.β
        / (hcong.α * (hcong.β + 1) / hcong.β - 1)) := hauxV.hγ
  have hβTop : ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β) ≠ ⊤ := hauxV.hβTop
  -- `MemLpPer β̄' (x ↦ -0 - H x 0 1 + V x)` via a constant + |V| dominator.
  have hF_HJB_10 : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
      (fun x => -(0 : ℝ) - H x (0 : Fin d → ℝ) 1 + V x) := by
    set Dom : (Fin d → ℝ) → ℝ :=
      fun x => 2 * congestionCoercivityConstant (d := d) hcong + |V x| with hDom
    have hC'_pos : 0 < congestionCoercivityConstant (d := d) hcong :=
      congestionCoercivityConstant_pos (d := d) hcong
    have hDom_memLp : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) Dom := by
      have hconst : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
          (fun _ : (Fin d → ℝ) => 2 * congestionCoercivityConstant (d := d) hcong) :=
        MemLp.toMemLpPer (memLp_const _)
      have hAbsV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
          (fun x => |V x|) := by
        have hVnorm := hV.toMemLp.norm
        have heq : (fun x => ‖V x‖) = (fun x => |V x|) := by
          funext x; exact Real.norm_eq_abs _
        rw [heq] at hVnorm
        exact MemLp.toMemLpPer hVnorm
      exact hconst.add hAbsV
    have hbd : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖-(0 : ℝ) - H x (0 : Fin d → ℝ) 1 + V x‖ ≤ (1 : ℝ) * ‖Dom x‖ := by
      filter_upwards [congestion_coercivity_h_H01_le (d := d) hcong] with x hxH
      have hDom_nn : 0 ≤ Dom x := by
        have h1 : 0 ≤ 2 * congestionCoercivityConstant (d := d) hcong := by
          linarith
        linarith [abs_nonneg (V x)]
      have htri : |-(0 : ℝ) - H x (0 : Fin d → ℝ) 1 + V x|
                    ≤ |H x (0 : Fin d → ℝ) 1| + |V x| := by
        have h1 : -(0 : ℝ) - H x (0 : Fin d → ℝ) 1 + V x
                  = -(H x (0 : Fin d → ℝ) 1) + V x := by ring
        rw [h1]
        have h2 := abs_add_le (-(H x (0 : Fin d → ℝ) 1)) (V x)
        rw [abs_neg] at h2
        exact h2
      have hle : |-(0 : ℝ) - H x (0 : Fin d → ℝ) 1 + V x| ≤ Dom x := by
        calc |-(0 : ℝ) - H x (0 : Fin d → ℝ) 1 + V x|
            ≤ |H x (0 : Fin d → ℝ) 1| + |V x| := htri
          _ ≤ 2 * congestionCoercivityConstant (d := d) hcong + |V x| :=
              add_le_add hxH (le_refl _)
          _ = Dom x := rfl
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hDom_nn, one_mul]
      exact hle
    exact MemLp.toMemLpPer (MemLp.of_le_mul hDom_memLp.toMemLp hAEm_HJB10 hbd)
  -- `MemLpPer γ̄' (x ↦ 1 * (DpH x 0 1) i)` via a constant dominator.
  have hF_flux_10 : ∀ i, MemLpPer (d := d)
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β
        / (hcong.α * (hcong.β + 1) / hcong.β - 1)))
      (fun x => (1 : ℝ) * (DpH x (0 : Fin d → ℝ) 1 i)) := by
    intro i
    set Dom : (Fin d → ℝ) → ℝ :=
      fun _ => 2 * congestionCoercivityConstant (d := d) hcong with hDom_def
    have hC'_pos : 0 < congestionCoercivityConstant (d := d) hcong :=
      congestionCoercivityConstant_pos (d := d) hcong
    have hDom_memLp : MemLpPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β
          / (hcong.α * (hcong.β + 1) / hcong.β - 1))) Dom :=
      MemLp.toMemLpPer (memLp_const _)
    have hbd : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖(1 : ℝ) * (DpH x (0 : Fin d → ℝ) 1 i)‖ ≤ (1 : ℝ) * ‖Dom x‖ := by
      filter_upwards [congestion_coercivity_h_DpH01_le (d := d) hcong] with x hxD
      have hC_nn : 0 ≤ 2 * congestionCoercivityConstant (d := d) hcong := by
        linarith
      have hcoord : |DpH x (0 : Fin d → ℝ) 1 i|
          ≤ ‖DpH x (0 : Fin d → ℝ) 1‖ := by
        have := norm_le_pi_norm (DpH x (0 : Fin d → ℝ) 1) i
        simpa [Real.norm_eq_abs] using this
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hC_nn, one_mul, one_mul]
      calc |DpH x (0 : Fin d → ℝ) 1 i|
          ≤ ‖DpH x (0 : Fin d → ℝ) 1‖ := hcoord
        _ ≤ 2 * congestionCoercivityConstant (d := d) hcong := hxD
    exact MemLp.toMemLpPer
      (MemLp.of_le_mul hDom_memLp.toMemLp (hAEm_flux10 i) hbd)
  -- The remaining base-point fields (`F_mass 1`, `G_grad 0 i`, `G_val 0`)
  -- are identically zero.
  have hF_mass_10 : MemLpPer (d := d)
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β
        / (hcong.α * (hcong.β + 1) / hcong.β - 1)))
      (Theorems.SimplePower.Banach.F_mass (fun _ : (Fin d → ℝ) => (1 : ℝ))) := by
    have hpt : Theorems.SimplePower.Banach.F_mass
          (fun _ : (Fin d → ℝ) => (1 : ℝ))
        = (fun _ : (Fin d → ℝ) => (0 : ℝ)) := by
      funext x; unfold Theorems.SimplePower.Banach.F_mass; ring
    rw [hpt]; exact MemLp.toMemLpPer (memLp_const _)
  have hG_grad_10 : ∀ i, MemLpPer (d := d)
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β
        / (hcong.α * (hcong.β + 1) / hcong.β - 1)))
      (Theorems.SimplePower.Banach.G_grad (hcong.α * (hcong.β + 1) / hcong.β)
        (fun (_ : Fin d) (_ : (Fin d → ℝ)) => (0 : ℝ)) i) := by
    intro i
    have hpt : Theorems.SimplePower.Banach.G_grad (hcong.α * (hcong.β + 1) / hcong.β)
          (fun (_ : Fin d) (_ : (Fin d → ℝ)) => (0 : ℝ)) i
        = (fun _ : (Fin d → ℝ) => (0 : ℝ)) := by
      funext x; unfold Theorems.SimplePower.Banach.G_grad
      have h0 : (fun j : Fin d =>
          (fun (_ : Fin d) (_ : Fin d → ℝ) => (0 : ℝ)) j x) = (0 : Fin d → ℝ) := by
        funext j; rfl
      simp [h0, mul_zero]
    rw [hpt]; exact MemLp.toMemLpPer (memLp_const _)
  have hG_val_10 : MemLpPer (d := d)
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β
        / (hcong.α * (hcong.β + 1) / hcong.β - 1)))
      (Theorems.SimplePower.Banach.G_val (hcong.α * (hcong.β + 1) / hcong.β)
        (fun _ : (Fin d → ℝ) => (0 : ℝ))) := by
    have hpt : Theorems.SimplePower.Banach.G_val (hcong.α * (hcong.β + 1) / hcong.β)
          (fun _ : (Fin d → ℝ) => (0 : ℝ))
        = (fun _ : (Fin d → ℝ) => (0 : ℝ)) := by
      funext x; unfold Theorems.SimplePower.Banach.G_val; simp
    rw [hpt]; exact MemLp.toMemLpPer (memLp_const _)
  -- Reconcile the base-point primal functions with the `F_*` shapes.
  have hF_HJB_10' : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
      (Theorems.SimplePower.Banach.F_HJB V H
        (fun (_ : Fin d) (_ : (Fin d → ℝ)) => (0 : ℝ))
        (fun _ : (Fin d → ℝ) => (1 : ℝ))
        (fun _ : (Fin d → ℝ) => (0 : ℝ))) := by
    have hpt : Theorems.SimplePower.Banach.F_HJB V H
          (fun (_ : Fin d) (_ : (Fin d → ℝ)) => (0 : ℝ))
          (fun _ : (Fin d → ℝ) => (1 : ℝ))
          (fun _ : (Fin d → ℝ) => (0 : ℝ))
        = (fun x => -(0 : ℝ) - H x (0 : Fin d → ℝ) 1 + V x) := by
      funext x; unfold Theorems.SimplePower.Banach.F_HJB
      have h0 : (fun i : Fin d =>
          (fun (_ : Fin d) (_ : (Fin d → ℝ)) => (0 : ℝ)) i x) = (0 : Fin d → ℝ) := by
        funext i; rfl
      rw [h0]
    rw [hpt]; exact hF_HJB_10
  have hF_flux_10' : ∀ i, MemLpPer (d := d)
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β
        / (hcong.α * (hcong.β + 1) / hcong.β - 1)))
      (Theorems.SimplePower.Banach.F_flux DpH
        (fun (_ : Fin d) (_ : (Fin d → ℝ)) => (0 : ℝ))
        (fun _ : (Fin d → ℝ) => (1 : ℝ)) i) := by
    intro i
    have hpt : Theorems.SimplePower.Banach.F_flux DpH
          (fun (_ : Fin d) (_ : (Fin d → ℝ)) => (0 : ℝ))
          (fun _ : (Fin d → ℝ) => (1 : ℝ)) i
        = (fun x => (1 : ℝ) * (DpH x (0 : Fin d → ℝ) 1 i)) := by
      funext x; unfold Theorems.SimplePower.Banach.F_flux
      have h0 : (fun j : Fin d =>
          (fun (_ : Fin d) (_ : (Fin d → ℝ)) => (0 : ℝ)) j x) = (0 : Fin d → ℝ) := by
        funext j; rfl
      rw [h0]
    rw [hpt]; exact hF_flux_10 i
  have haux10 :
      Theorems.SimplePower.Banach.MFGOpEpsAuxHyps (d := d)
        (hcong.α * (hcong.β + 1) / hcong.β) (hcong.β + 1)
        ((hcong.β + 1) / hcong.β)
        (hcong.α * (hcong.β + 1) / hcong.β
          / (hcong.α * (hcong.β + 1) / hcong.β - 1))
        V H DpH (fun (_ : Fin d) (_ : (Fin d → ℝ)) => (0 : ℝ))
        (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ)) :=
    { hβ := hβconj, hγ := hγconj
      hF_HJB := hF_HJB_10', hF_flux := hF_flux_10'
      hF_mass := hF_mass_10
      hG_grad := hG_grad_10, hG_val := hG_val_10
      hβTop := hβTop }
  have hInt_10 : IntegrableOn
      (fun x => (-(0 : ℝ) - H x (0 : Fin d → ℝ) 1 + V x) * (⇑v.1 x - 1)
                + 1 * (DpH x (0 : Fin d → ℝ) 1 ⬝ (fun i => ⇑(v.2.2 i) x))
                + (1 - 1) * ⇑v.2.1 x) (UnitCube d) :=
    Theorems.SimplePower.Banach.integrable_mfgPair_integrand
      (γBarReal := hcong.α * (hcong.β + 1) / hcong.β) (βBarReal := hcong.β + 1)
      (βBarReal' := (hcong.β + 1) / hcong.β)
      (γBarReal' := (hcong.α * (hcong.β + 1) / hcong.β)
          / (hcong.α * (hcong.β + 1) / hcong.β - 1))
      haux10 hmSub1_Lp huLp hDuLp
  -- (4) `hHam_int`: `(hInt_mu - hInt_10) = coerciveHamIntegrand` (ring).
  have hHam_int : IntegrableOn
      (fun x => coerciveHamIntegrand H DpH (fun i => ⇑(v.2.2 i)) (⇑v.1) x)
      (UnitCube d) := by
    have hsub := hInt_mu.sub hInt_10
    refine hsub.congr ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    simp only [Pi.sub_apply]
    unfold coerciveHamIntegrand
    ring
  exact ⟨hm_pos, hInt_mu, hInt_10, hHam_int, hRpow_m_int, hRpow_p_int⟩

/-! ## Congestion Eulerian / combined lower bound (`BB1d child 2b`)

Route-B port of `coercivity_eulerian_from_paperHypotheses_uniform` /
`coercivity_combined_from_paperHypotheses_uniform` (paper `prop:coercAepsi`
reuse) to the congestion exponents/constant. The coercivity constant is
fixed at `C := 2 * congestionCoercivityConstant hcong`, so that the four
explicit input bounds of `coercivity_integrand_lower_bound_young_explicit`
align at the same `C`:

* `h_lower` from child-1 `congestion_coercivity_h_lower_from_hcong` at
  `C'`, weakened to `2C'`;
* `h_lagr` from `hcong.lagr_rider_of_convex_at_zero (hmon.convex_at_zero)`
  at `C' = toWeakGrowth.C` (and `toWeakGrowth.β = hcong.β`), weakened to
  `2C'`;
* `h_H01_le`, `h_DpH01_le` from child-1, already at `2C'`.

The post-Young constant is then
`C_eul := coercivityIntegrandLowerBoundYoungConstant d (2C') hcong.α hcong.β`
— fully determined by `hcong`, with no free constant in the signature.
**Route B**: the lower bound is sourced *directly* from `hcong` (via the
hierarchy bridge `toWeakGrowth.lower`) and `hmon.convex_at_zero`; we do
**not** call `hcong.toHypothesisPowerGrowth`. -/

/-- **Congestion Eulerian half (`BB1d child 2b`).** The integrated
Eulerian lower bound at the congestion constant `2C'`, mirror of
`coercivity_eulerian_from_paperHypotheses_uniform`. -/
theorem congestion_coercivity_eulerian
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m : (Fin d → ℝ) → ℝ)
    (hm_pos : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hHam_int : IntegrableOn
        (fun x => coerciveHamIntegrand H DpH Du m x) (UnitCube d))
    (hRpow_m_int : IntegrableOn (fun x => m x ^ (hcong.β + 1)) (UnitCube d))
    (hRpow_p_int : IntegrableOn
        (fun x => ‖fun i => Du i x‖ ^ hcong.α) (UnitCube d)) :
    let C_eul : ℝ :=
      coercivityIntegrandLowerBoundYoungConstant d
        (2 * congestionCoercivityConstant (d := d) hcong) hcong.α hcong.β
    (1 / C_eul) * (∫ x in UnitCube d, m x ^ (hcong.β + 1))
        + (1 / C_eul) * (∫ x in UnitCube d, ‖fun i => Du i x‖ ^ hcong.α)
        - C_eul
      ≤ ∫ x in UnitCube d, coerciveHamIntegrand H DpH Du m x := by
  intro C_eul
  set C' : ℝ := congestionCoercivityConstant (d := d) hcong with hC'_def
  have hC'_pos : 0 < C' := congestionCoercivityConstant_pos (d := d) hcong
  have h2C'_pos : 0 < 2 * C' := by linarith
  have hC_eul_pos : 0 < C_eul :=
    coercivityIntegrandLowerBoundYoungConstant_pos d _ hcong.α hcong.β
  -- Exponent hypotheses inherited from `hcong` via `toWeakGrowth`
  -- (`.hα : 1 < hcong.α`, `.hβ : 0 < hcong.β`, defeq).
  have hα : (1 : ℝ) < hcong.α := hcong.toWeakGrowth.hα
  have hβ : (0 : ℝ) < hcong.β := hcong.toWeakGrowth.hβ
  -- Lagrangian bound at `C'`, weakened to `2C'`. `lagr_rider_*` is stated
  -- at `toWeakGrowth.C = C'` and `toWeakGrowth.β = hcong.β`.
  have h_lagr_2C :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ hcong.β) / (2 * C') - 2 * C' ≤ (DpH x p mx) ⬝ p - H x p mx := by
    filter_upwards
      [hcong.lagr_rider_of_convex_at_zero (hmon.convex_at_zero)] with x hx p mx hmx
    have hbase := hx p mx hmx
    -- `hbase : mx^β / C' - C' ≤ DpH·p - H` (at `toWeakGrowth.{β,C}`, defeq).
    have hmβ_nn : (0 : ℝ) ≤ mx ^ hcong.β := Real.rpow_nonneg hmx.le _
    -- `mx^β/(2C') ≤ mx^β/C'` and `-2C' ≤ -C'`, so the weakened LHS is ≤ base LHS.
    have hdiv : mx ^ hcong.β / (2 * C') ≤ mx ^ hcong.β / C' := by
      apply div_le_div_of_nonneg_left hmβ_nn hC'_pos
      linarith
    have hbase' : mx ^ hcong.β / C' - C'
        ≤ (DpH x p mx) ⬝ p - H x p mx := hbase
    linarith
  -- Simple lower bound at `C'`, weakened to `2C'`.
  have h_lower_2C :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (‖p‖ ^ hcong.α) / (2 * C') - 2 * C' * (mx ^ hcong.β + 1) ≤ H x p mx := by
    filter_upwards
      [congestion_coercivity_h_lower_from_hcong (d := d) hcong] with x hx p mx hmx
    have hbase := hx p mx hmx
    -- `hbase : ‖p‖^α / C' - C'*(mx^β+1) ≤ H`.
    have hp_nn : (0 : ℝ) ≤ ‖p‖ ^ hcong.α := Real.rpow_nonneg (norm_nonneg _) _
    have hmβ1_nn : (0 : ℝ) ≤ mx ^ hcong.β + 1 := by
      have := Real.rpow_nonneg hmx.le (hcong.β); linarith
    have hdiv : ‖p‖ ^ hcong.α / (2 * C') ≤ ‖p‖ ^ hcong.α / C' := by
      apply div_le_div_of_nonneg_left hp_nn hC'_pos; linarith
    have hmul : C' * (mx ^ hcong.β + 1) ≤ 2 * C' * (mx ^ hcong.β + 1) := by
      apply mul_le_mul_of_nonneg_right _ hmβ1_nn; linarith
    linarith
  -- The `(0,1)` bounds, already at `2C'`.
  have h_H01_le :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        |H x (0 : Fin d → ℝ) 1| ≤ 2 * C' :=
    congestion_coercivity_h_H01_le (d := d) hcong
  have h_DpH01_le :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖DpH x (0 : Fin d → ℝ) 1‖ ≤ 2 * C' :=
    congestion_coercivity_h_DpH01_le (d := d) hcong
  -- Step 1: pointwise post-Young bound at the explicit constant.
  have hPointAE :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        0 < m x →
          (1 / C_eul) *
              (m x ^ (hcong.β + 1) + ‖fun i => Du i x‖ ^ hcong.α)
              - C_eul
            ≤ coerciveHamIntegrand H DpH Du m x :=
    coercivity_integrand_lower_bound_young_explicit H DpH
      h2C'_pos hα hβ h_lagr_2C h_lower_2C h_H01_le h_DpH01_le Du m
  -- Step 2: drop the `0 < m x` premise.
  have hPointAE' :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        (1 / C_eul) *
            (m x ^ (hcong.β + 1) + ‖fun i => Du i x‖ ^ hcong.α)
            - C_eul
          ≤ coerciveHamIntegrand H DpH Du m x := by
    filter_upwards [hPointAE, hm_pos] with x hx hpos
    exact hx hpos
  -- Step 3: integrability residue for the LHS family.
  have hSum_int : IntegrableOn
      (fun x => m x ^ (hcong.β + 1) + ‖fun i => Du i x‖ ^ hcong.α)
      (UnitCube d) := hRpow_m_int.add hRpow_p_int
  have hSum_smul_int : IntegrableOn
      (fun x =>
        (1 / C_eul) * (m x ^ (hcong.β + 1) + ‖fun i => Du i x‖ ^ hcong.α))
      (UnitCube d) := hSum_int.const_mul _
  have hμ_ne : volume (UnitCube (d := d)) ≠ ⊤ := by
    rw [volume_unitCube]; exact ENNReal.one_ne_top
  have h_const_int : IntegrableOn (fun _ : Fin d → ℝ => (C_eul : ℝ))
      (UnitCube d) := integrableOn_const hμ_ne
  have hLB_int : IntegrableOn
      (fun x =>
        (1 / C_eul) *
            (m x ^ (hcong.β + 1) + ‖fun i => Du i x‖ ^ hcong.α)
            - C_eul)
      (UnitCube d) := hSum_smul_int.sub h_const_int
  -- Step 4: integrate.
  exact
    coercivity_integral_lower_bound (C'' := C_eul) (β := hcong.β) (α := hcong.α)
      H DpH hC_eul_pos Du m
      hPointAE' hHam_int hLB_int hRpow_m_int hRpow_p_int

/-- **Congestion combined algebraic bound (`BB1d child 2b`).** Mirror of
`coercivity_combined_from_paperHypotheses_uniform` at the congestion
constant `2C'`, with the test-pair identity (paper line 947) stitched on
top of the Eulerian half. The `γ̄`-Laplacian regulariser uses the
congestion exponent `γ̄ = α(β+1)/β`. -/
theorem congestion_coercivity_combined
    {γBar ε : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (hm_pos : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hInt_mu : IntegrableOn (fun x =>
        (-(u x) - H x (fun i => Du i x) (m x) + V x) * (m x - 1)
          + m x * (DpH x (fun i => Du i x) (m x) ⬝ (fun i => Du i x))
          + (m x - 1) * u x) (UnitCube d))
    (hInt_10 : IntegrableOn (fun x =>
        (-(0 : ℝ) - H x (0 : Fin d → ℝ) 1 + V x) * (m x - 1)
          + 1 * (DpH x (0 : Fin d → ℝ) 1 ⬝ (fun i => Du i x))
          + (1 - 1) * u x) (UnitCube d))
    (hHam_int : IntegrableOn
        (fun x => coerciveHamIntegrand H DpH Du m x) (UnitCube d))
    (hRpow_m_int : IntegrableOn (fun x => m x ^ (hcong.β + 1)) (UnitCube d))
    (hRpow_p_int : IntegrableOn
        (fun x => ‖fun i => Du i x‖ ^ hcong.α) (UnitCube d)) :
    let C_eul : ℝ :=
      coercivityIntegrandLowerBoundYoungConstant d
        (2 * congestionCoercivityConstant (d := d) hcong) hcong.α hcong.β
    (1 / C_eul) * (∫ x in UnitCube d, m x ^ (hcong.β + 1))
        + (1 / C_eul) * (∫ x in UnitCube d, ‖fun i => Du i x‖ ^ hcong.α)
        + ε * (∫ x in UnitCube d,
            vecAbsPowMinusTwo γBar (fun i => Du i x)
                * ((fun i => Du i x) ⬝ (fun i => Du i x))
              + absPowMinusTwo γBar (u x) * (u x * u x))
        - C_eul
      ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBar ε Du m u Du (m - 1) u
        - mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBar ε (fun _ _ => 0) (fun _ => 1) (fun _ => 0) Du (m - 1) u := by
  intro C_eul
  -- Step 1: test-pair identity (paper line 947).
  have hTestPair :
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBar ε Du m u Du (m - 1) u
        - mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBar ε (fun _ _ => 0) (fun _ => 1) (fun _ => 0) Du (m - 1) u
      = (∫ x in UnitCube d, coerciveHamIntegrand H DpH Du m x
          ∂(volume : Measure (Fin d → ℝ)))
        + ε * (∫ x in UnitCube d,
            vecAbsPowMinusTwo γBar (fun i => Du i x)
                * ((fun i => Du i x) ⬝ (fun i => Du i x))
              + absPowMinusTwo γBar (u x) * (u x * u x)
            ∂(volume : Measure (Fin d → ℝ))) :=
    coercive_test_pair_identity V H DpH γBar ε Du m u hInt_mu hInt_10
  -- Step 2: congestion Eulerian half at the explicit constant.
  have hEul :
      (1 / C_eul) * (∫ x in UnitCube d, m x ^ (hcong.β + 1))
          + (1 / C_eul) * (∫ x in UnitCube d, ‖fun i => Du i x‖ ^ hcong.α)
          - C_eul
        ≤ ∫ x in UnitCube d, coerciveHamIntegrand H DpH Du m x :=
    congestion_coercivity_eulerian (d := d) hmon hcong Du m
      hm_pos hHam_int hRpow_m_int hRpow_p_int
  -- Step 3: combine.
  linarith [hTestPair, hEul]

/-! ## Congestion coercivity bound, eventual form (`BB1d child 2c`)

The final `∀ᶠ` deliverable of `BB1d`: the eventual lower bound on the
`congestionAepsiOpK`-difference along the coercivity filter
`cobounded ⊓ 𝓟 (congestionBanachK …)`, the input `hbound` of the abstract
coercivity wrap `isCoerciveAt_Aepsi_CLM_K_Aepsi` ported to the congestion
operator.

The bound is *derived* (not assumed) from child-2b's
`congestion_coercivity_combined` at the components `(Du, m, u)` of `v`,
together with the on-domain operator unfolding
`congestionAepsiOpK_apply_of_mem` (mirror of `isCoerciveAt_Aepsi_CLM`'s
`h_subapply` / test- and primal-swap machinery). The coercivity constant
`C_eul` is *fixed* by `hcong` — it is the child-2b Young constant
`coercivityIntegrandLowerBoundYoungConstant d (2C') hcong.α hcong.β`, NOT a
free parameter. -/

/-- **Congestion coercivity bound, eventual form (`BB1d child 2c`).**

For a base point `v₀` lying in `congestionBanachK` with the `(1, 0, 0)`
a.e. profile (`m₀ = 1`, `u₀ = 0`, `Du₀ = 0`), the gauge-minus-`C_eul`
lower bound holds eventually along the coercivity filter, with `C_eul`
the fixed child-2b Young constant. -/
theorem congestion_coercivity_bound_eventually
    {V : (Fin d → ℝ) → ℝ}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (ε : ℝ)
    (v₀ : congestionXBanach d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))
    (hv₀_mem : v₀ ∈ congestionBanachK d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ)
    (hv₀_m : ⇑v₀.1 =ᵐ[Measure.restrict volume (UnitCube d)] (fun _ => (1 : ℝ)))
    (hv₀_u : ⇑v₀.2.1 =ᵐ[Measure.restrict volume (UnitCube d)] (fun _ => (0 : ℝ)))
    (hv₀_Du : ∀ i, ⇑(v₀.2.2 i)
                  =ᵐ[Measure.restrict volume (UnitCube d)] (fun _ => (0 : ℝ))) :
    let C_eul : ℝ :=
      coercivityIntegrandLowerBoundYoungConstant d
        (2 * congestionCoercivityConstant (d := d) hcong) hcong.α hcong.β
    ∀ᶠ v in (Bornology.cobounded
                (congestionXBanach d
                  (ENNReal.ofReal (hcong.β + 1))
                  (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))
              ⊓ Filter.principal
                (congestionBanachK d
                  (ENNReal.ofReal (hcong.β + 1))
                  (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
                  (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
                  hcong.α hcong.β hcong.τ)),
      congestionCoerciveGauge (d := d) hcong C_eul ε v - C_eul
        ≤ (congestionAepsiOpK hmon hcong hVmeas hV ε v
            - congestionAepsiOpK hmon hcong hVmeas hV ε v₀) (v - v₀) := by
  intro C_eul
  -- The principal `congestionBanachK` factor of the coercivity filter makes
  -- membership `v ∈ congestionBanachK` an eventual fact (universal on the
  -- principal piece), the only hypothesis we need on the running `v`.
  have h_eventually_K :
      ∀ᶠ v in (Bornology.cobounded
                  (congestionXBanach d
                    (ENNReal.ofReal (hcong.β + 1))
                    (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))
                ⊓ Filter.principal
                  (congestionBanachK d
                    (ENNReal.ofReal (hcong.β + 1))
                    (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
                    (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
                    hcong.α hcong.β hcong.τ)),
        v ∈ congestionBanachK d
            (ENNReal.ofReal (hcong.β + 1))
            (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
            (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
            hcong.α hcong.β hcong.τ :=
    Filter.eventually_inf_principal.mpr (Filter.Eventually.of_forall (fun _ h => h))
  filter_upwards [h_eventually_K] with v hv
  -- Abbreviations for the primal data of the running point `v`.
  set Du : Fin d → (Fin d → ℝ) → ℝ := fun i => ⇑(v.2.2 i) with hDu_def
  set m : (Fin d → ℝ) → ℝ := ⇑v.1 with hm_def
  set u : (Fin d → ℝ) → ℝ := ⇑v.2.1 with hu_def
  -- Step 1: rewrite the operator difference applied to `(v - v₀)` as the
  -- two `mfgOperatorEpsPair` values, then collapse the `(v - v₀)` test
  -- triple to `(m - 1, u, Du)` and the `v₀` data triple to `(0, 1, 0)`.
  have h_subapply :
      (congestionAepsiOpK hmon hcong hVmeas hV ε v
          - congestionAepsiOpK hmon hcong hVmeas hV ε v₀) (v - v₀)
        = mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            (hcong.α * (hcong.β + 1) / hcong.β) ε
            Du m u
            (fun i => ⇑((v - v₀).2.2 i)) (⇑(v - v₀).1) (⇑(v - v₀).2.1)
          - mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              (hcong.α * (hcong.β + 1) / hcong.β) ε
              (fun i => ⇑(v₀.2.2 i)) (⇑v₀.1) (⇑v₀.2.1)
              (fun i => ⇑((v - v₀).2.2 i)) (⇑(v - v₀).1) (⇑(v - v₀).2.1) := by
    rw [ContinuousLinearMap.sub_apply,
        congestionAepsiOpK_apply_of_mem hmon hcong hVmeas hV ε hv (v - v₀),
        congestionAepsiOpK_apply_of_mem hmon hcong hVmeas hV ε hv₀_mem (v - v₀)]
  -- a.e.-equalities for the `(v - v₀)` test triple, collapsing via the
  -- base-point profile (`m₀ = 1`, `u₀ = 0`, `Du₀ = 0`).
  have h_eta_ae : ⇑((v - v₀).1)
                    =ᵐ[Measure.restrict volume (UnitCube d)] (m - 1) := by
    have h_pair : (v - v₀).1 = v.1 - v₀.1 := rfl
    rw [h_pair]
    filter_upwards [MeasureTheory.Lp.coeFn_sub v.1 v₀.1, hv₀_m] with x hx h0
    rw [hx]
    change (⇑v.1 - ⇑v₀.1) x = (m - 1) x
    rw [Pi.sub_apply, Pi.sub_apply, h0, Pi.one_apply]
  have h_nu_ae : ⇑((v - v₀).2.1)
                    =ᵐ[Measure.restrict volume (UnitCube d)] u := by
    have h_pair : (v - v₀).2.1 = v.2.1 - v₀.2.1 := rfl
    rw [h_pair]
    filter_upwards [MeasureTheory.Lp.coeFn_sub v.2.1 v₀.2.1, hv₀_u] with x hx h0
    rw [hx]
    change (⇑v.2.1 - ⇑v₀.2.1) x = u x
    rw [Pi.sub_apply, h0, sub_zero]
  have h_Dnu_ae : ∀ i, ⇑((v - v₀).2.2 i)
                    =ᵐ[Measure.restrict volume (UnitCube d)]
                      fun x => Du i x := by
    intro i
    have h_pair : (v - v₀).2.2 i = v.2.2 i - v₀.2.2 i := rfl
    rw [h_pair]
    filter_upwards [MeasureTheory.Lp.coeFn_sub (v.2.2 i) (v₀.2.2 i),
      hv₀_Du i] with x hx h0
    rw [hx]
    change (⇑(v.2.2 i) - ⇑(v₀.2.2 i)) x = Du i x
    rw [Pi.sub_apply, h0, sub_zero]
  -- Swap the test triple of both pairings to `(m - 1, u, Du)`.
  have h_test_swap1 :
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          (hcong.α * (hcong.β + 1) / hcong.β) ε
          Du m u
          (fun i => ⇑((v - v₀).2.2 i)) (⇑(v - v₀).1) (⇑(v - v₀).2.1)
        = mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            (hcong.α * (hcong.β + 1) / hcong.β) ε
            Du m u Du (m - 1) u :=
    Theorems.SimplePower.Banach.mfgOperatorEpsPair_test_congr_ae
      V H DpH (hcong.α * (hcong.β + 1) / hcong.β) ε Du m u
      h_eta_ae h_nu_ae h_Dnu_ae
  have h_test_swap2 :
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          (hcong.α * (hcong.β + 1) / hcong.β) ε
          (fun i => ⇑(v₀.2.2 i)) (⇑v₀.1) (⇑v₀.2.1)
          (fun i => ⇑((v - v₀).2.2 i)) (⇑(v - v₀).1) (⇑(v - v₀).2.1)
        = mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            (hcong.α * (hcong.β + 1) / hcong.β) ε
            (fun i => ⇑(v₀.2.2 i)) (⇑v₀.1) (⇑v₀.2.1)
            Du (m - 1) u :=
    Theorems.SimplePower.Banach.mfgOperatorEpsPair_test_congr_ae
      V H DpH (hcong.α * (hcong.β + 1) / hcong.β) ε
      (fun i => ⇑(v₀.2.2 i)) (⇑v₀.1) (⇑v₀.2.1)
      h_eta_ae h_nu_ae h_Dnu_ae
  -- Swap the second pairing's data triple from `v₀` to `(0, 1, 0)`.
  have h_primal_swap :
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          (hcong.α * (hcong.β + 1) / hcong.β) ε
          (fun i => ⇑(v₀.2.2 i)) (⇑v₀.1) (⇑v₀.2.1)
          Du (m - 1) u
        = mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            (hcong.α * (hcong.β + 1) / hcong.β) ε
            (fun _ _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ))
            Du (m - 1) u :=
    Theorems.SimplePower.Banach.mfgOperatorEpsPair_primal_congr_ae
      V H DpH (hcong.α * (hcong.β + 1) / hcong.β) ε Du (m - 1) u
      hv₀_m hv₀_u hv₀_Du
  rw [h_subapply, h_test_swap1, h_test_swap2, h_primal_swap]
  -- Step 2: integrability residues + strict positivity from membership.
  obtain ⟨hm_pos, hInt_mu, hInt_10, hHam_int, hRpow_m_int, hRpow_p_int⟩ :=
    congestion_coercivity_integrability_residues (d := d)
      hmon hcong hVmeas hV ε hv
  -- Step 3: child-2b combined bound at the components `(Du, m, u)` of `v`,
  -- at the regularising exponent `γ̄ = α(β+1)/β`.
  have hCombined :=
    congestion_coercivity_combined (d := d)
      (γBar := hcong.α * (hcong.β + 1) / hcong.β) (ε := ε)
      V hmon hcong Du m u
      hm_pos hInt_mu hInt_10 hHam_int hRpow_m_int hRpow_p_int
  -- Step 4: identify the gauge with the combined LHS by unfolding.
  unfold congestionCoerciveGauge
  -- `hCombined`'s LHS is exactly `gauge - C_eul`; the RHS matches the
  -- post-swap operator difference. Close by `linarith` (the `let`-bound
  -- `C_eul` is shared on both sides).
  simpa only [hDu_def, hm_def, hu_def] using hCombined


/-! ## Congestion coercive-gauge norm bridge (`BB1d child 3a`)

The lower bound on the congestion coercive gauge in terms of the ambient
norm (paper line 982, congestion variant of `eq:coercive.Aepsi`):
```
‖v‖^κ ≤ 1 + Cbig · congestionCoerciveGauge hcong C_eul ε v
```
with `κ = coercivityGaugeExponent (β+1) (α(β+1)/β) = min(β+1, γ̄)` and
`Cbig = C_eul + (d+1)^(γ̄+1)/ε`.

The Sobolev coercivity comes from the gauge's **ε-term** (the
`γ̄`-Laplacian integrand `(√(Du⬝Du))^γ̄ + |u|^γ̄`), NOT the `α`-momentum
term: since `α < γ̄`, the `L^α` momentum term cannot control the
`γ̄`-Sobolev norm. The mass term `(1/C_eul)·∫m^{β+1}` provides the
`‖v.1‖^{β+1}` bound.
-/

/-- **Congestion coercive-gauge norm bridge (`BB1d child 3a`).**

`‖v‖^κ ≤ 1 + Cbig · gauge`, the lower bound on the congestion coercive
gauge in terms of the ambient norm. Derived from the gauge's mass term
(for the `‖v.1‖^{β+1}` factor) and ε-term (for the `‖v.2‖^{γ̄}` Sobolev
factor), via the public simple-power per-component bridges
`coercivity_norm_m_eq_integrated` / `coercivity_norm_u_le_integrated`
and `MemLpPer.norm_pair_rpow_min_le`. -/
theorem congestion_coercivity_norm_bridge
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    {C_eul ε : ℝ} (hC : 0 < C_eul) (hε : 0 < ε)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    (v : congestionXBanach d
           (ENNReal.ofReal (hcong.β + 1))
           (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))
    (hv_pos : 0 ≤ᵐ[volume.restrict (UnitCube d)] (⇑v.1 : (Fin d → ℝ) → ℝ)) :
    ‖v‖ ^ Theorems.SimplePower.Banach.coercivityGaugeExponent
            (hcong.β + 1) (hcong.α * (hcong.β + 1) / hcong.β)
      ≤ 1 + (C_eul + ((d : ℝ) + 1) ^ (hcong.α * (hcong.β + 1) / hcong.β + 1) / ε)
            * congestionCoerciveGauge (d := d) hcong C_eul ε v := by
  classical
  haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  -- Raw exponents (NO `set`): `β̄ = hcong.β + 1`, `γ̄ = hcong.α*(β+1)/β`.
  have hα_pos : 0 < hcong.α := lt_trans one_pos hcong.hα
  have hβ_pos : 0 < hcong.β := hcong.hβ
  have hβ1_pos : 0 < hcong.β + 1 := by linarith
  -- `1 < β̄` and `1 < γ̄`.
  have hβ1_gt_one : 1 < hcong.β + 1 := by linarith
  have hγ_gt_one : 1 < hcong.α * (hcong.β + 1) / hcong.β := by
    rw [lt_div_iff₀ hβ_pos, one_mul]
    nlinarith [hcong.hα, hβ_pos]
  have hγ_pos : 0 < hcong.α * (hcong.β + 1) / hcong.β := lt_trans one_pos hγ_gt_one
  have hγ_ge_one : (1 : ℝ) ≤ hcong.α * (hcong.β + 1) / hcong.β := hγ_gt_one.le
  -- Top-finiteness facts.
  have hβTop : ENNReal.ofReal (hcong.β + 1) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hγTop : ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  -- Per-coordinate `MemLpPer γ̄` certificates for the gradient family.
  have hDuLp : ∀ i, Periodic.MemLpPer (d := d)
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
      (fun x => (⇑(v.2.2 i) : (Fin d → ℝ) → ℝ) x) :=
    fun i => Periodic.memLpPer_iff_memLp.mpr (MeasureTheory.Lp.memLp (v.2.2 i))
  -- ============================================================
  -- Step A: `‖v‖^κ ≤ 1 + ‖v.1‖^β̄ + ‖v.2‖^γ̄`.
  -- ============================================================
  have hmin :
      ‖((v.1, v.2))‖ ^ min (ENNReal.ofReal (hcong.β + 1)).toReal
                           (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)).toReal
        ≤ 1 + ‖v.1‖ ^ (ENNReal.ofReal (hcong.β + 1)).toReal
            + ‖v.2‖ ^ (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)).toReal :=
    Periodic.MemLpPer.norm_pair_rpow_min_le hβTop hγTop v.1 v.2
  rw [ENNReal.toReal_ofReal hβ1_pos.le,
      ENNReal.toReal_ofReal hγ_pos.le] at hmin
  -- `(v.1, v.2) = v` and `min = coercivityGaugeExponent`.
  have hvnorm : ‖((v.1, v.2))‖ = ‖v‖ := rfl
  rw [hvnorm] at hmin
  have hκeq : Theorems.SimplePower.Banach.coercivityGaugeExponent
        (hcong.β + 1) (hcong.α * (hcong.β + 1) / hcong.β)
      = min (hcong.β + 1) (hcong.α * (hcong.β + 1) / hcong.β) := rfl
  rw [hκeq]
  -- ============================================================
  -- Step B: m-factor `‖v.1‖^β̄ = ∫ m^β̄ = C_eul · (mass term)`.
  -- ============================================================
  have hB : ‖v.1‖ ^ (hcong.β + 1)
      = ∫ x in UnitCube d, |(⇑v.1 : (Fin d → ℝ) → ℝ) x| ^ (hcong.β + 1) :=
    Theorems.SimplePower.coercivity_norm_m_eq_integrated (d := d)
      (βBarReal := hcong.β + 1)
      (γBarReal := hcong.α * (hcong.β + 1) / hcong.β) hβ1_pos v
  -- Drop the absolute value using a.e.-nonnegativity of the density.
  have hB_pos : ‖v.1‖ ^ (hcong.β + 1)
      = ∫ x in UnitCube d, ((⇑v.1 : (Fin d → ℝ) → ℝ) x) ^ (hcong.β + 1) := by
    rw [hB]
    refine integral_congr_ae ?_
    filter_upwards [hv_pos] with x hx
    rw [abs_of_nonneg hx]
  -- `∫ m^β̄ = C_eul · (1/C_eul · ∫ m^β̄)`.
  have hmass_eq : ∫ x in UnitCube d, ((⇑v.1 : (Fin d → ℝ) → ℝ) x) ^ (hcong.β + 1)
      = C_eul * ((1 / C_eul) * ∫ x in UnitCube d,
          ((⇑v.1 : (Fin d → ℝ) → ℝ) x) ^ (hcong.β + 1)) := by
    field_simp
  -- ============================================================
  -- Step C: u-factor `‖v.2‖^γ̄ ≤ (d+1)^γ̄·(∫|u|^γ̄ + ∑∫|Du i|^γ̄)`.
  -- ============================================================
  have hC_u : ‖v.2‖ ^ (hcong.α * (hcong.β + 1) / hcong.β)
      ≤ ((d : ℝ) + 1) ^ (hcong.α * (hcong.β + 1) / hcong.β) *
          ((∫ x in UnitCube d,
              |(⇑v.2.1 : (Fin d → ℝ) → ℝ) x| ^ (hcong.α * (hcong.β + 1) / hcong.β))
            + ∑ i, ∫ x in UnitCube d,
              |(⇑(v.2.2 i) : (Fin d → ℝ) → ℝ) x| ^ (hcong.α * (hcong.β + 1) / hcong.β)) :=
    Theorems.SimplePower.coercivity_norm_u_le_integrated (d := d)
      (βBarReal := hcong.β + 1)
      (γBarReal := hcong.α * (hcong.β + 1) / hcong.β) hγ_pos v
  -- ============================================================
  -- Step D: ε-term pointwise identity.
  -- `εint x = (√(Du⬝Du))^γ̄ + |u|^γ̄`.
  -- ============================================================
  -- Notation: the gauge ε-integrand and the "clean" form.
  set Du : Fin d → (Fin d → ℝ) → ℝ := fun i => (⇑(v.2.2 i) : (Fin d → ℝ) → ℝ)
    with hDu_def
  set u : (Fin d → ℝ) → ℝ := (⇑v.2.1 : (Fin d → ℝ) → ℝ) with hu_def
  -- Du-part: `vecAbsPowMinusTwo γ̄ Du · (Du⬝Du) = (√(Du⬝Du))^γ̄ = (Du⬝Du)^(γ̄/2)`.
  have hDu_id : ∀ x,
      vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
          (fun i => Du i x)
        * ((fun i => Du i x) ⬝ (fun i => Du i x))
        = ((fun i => Du i x) ⬝ (fun i => Du i x))
            ^ (hcong.α * (hcong.β + 1) / hcong.β / 2) := by
    intro x
    have hr : 0 ≤ (fun i => Du i x) ⬝ (fun i => Du i x) :=
      Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
    unfold vecAbsPowMinusTwo
    rcases eq_or_lt_of_le hr with hr0 | hrpos
    · -- `r = 0`: both sides zero (γ̄/2 > 0).
      have hexp2 : 0 < hcong.α * (hcong.β + 1) / hcong.β / 2 := by linarith
      rw [← hr0, mul_zero, Real.zero_rpow hexp2.ne']
    · -- `r > 0`: `r^((γ̄-2)/2) · r = r^((γ̄-2)/2 + 1) = r^(γ̄/2)`.
      have hstep : ((fun i => Du i x) ⬝ (fun i => Du i x)) ^ ((hcong.α * (hcong.β + 1) / hcong.β - 2) / 2)
            * ((fun i => Du i x) ⬝ (fun i => Du i x))
          = ((fun i => Du i x) ⬝ (fun i => Du i x))
              ^ ((hcong.α * (hcong.β + 1) / hcong.β - 2) / 2 + 1) := by
        rw [Real.rpow_add_one hrpos.ne']
      rw [hstep]
      congr 1
      ring
  -- u-part: `absPowMinusTwo γ̄ u · (u·u) = |u|^γ̄`.
  have hu_id : ∀ x,
      absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β) (u x) * (u x * u x)
        = |u x| ^ (hcong.α * (hcong.β + 1) / hcong.β) := by
    intro x
    unfold absPowMinusTwo
    have huu : u x * u x = |u x| ^ (2 : ℝ) := by
      rw [Real.rpow_two, sq_abs, sq]
    rw [huu]
    rcases eq_or_lt_of_le (abs_nonneg (u x)) with h0 | hpos
    · -- `|u x| = 0`.
      have hexp2 : (0 : ℝ) < 2 := by norm_num
      rw [← h0, Real.zero_rpow hexp2.ne', mul_zero,
          Real.zero_rpow hγ_pos.ne']
    · rw [← Real.rpow_add hpos]
      congr 1
      ring
  -- ============================================================
  -- Step E: `∫|u|^γ̄ + ∑∫|Du i|^γ̄ ≤ (d+1)·∫εint`.
  -- ============================================================
  -- `εint x = (Du⬝Du)^(γ̄/2) + |u|^γ̄`.
  have hεint_eq : ∀ x,
      vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β) (fun i => Du i x)
          * ((fun i => Du i x) ⬝ (fun i => Du i x))
        + absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β) (u x) * (u x * u x)
      = ((fun i => Du i x) ⬝ (fun i => Du i x))
          ^ (hcong.α * (hcong.β + 1) / hcong.β / 2)
        + |u x| ^ (hcong.α * (hcong.β + 1) / hcong.β) := by
    intro x; rw [hDu_id x, hu_id x]
  -- Integrability of `(Du⬝Du)^(γ̄/2)`.
  have hdot_int : MeasureTheory.Integrable
      (fun x => ((fun i => Du i x) ⬝ (fun i => Du i x))
          ^ (hcong.α * (hcong.β + 1) / hcong.β / 2))
      (volume.restrict (UnitCube d)) :=
    Theorems.SimplePower.integrable_euclideanDot_rpow_half_of_coord_memLp
      (d := d) (γBarReal := hcong.α * (hcong.β + 1) / hcong.β) Du hDuLp hγ_ge_one
  -- Integrability of `|u|^γ̄`.
  have hu_int : MeasureTheory.Integrable
      (fun x => |u x| ^ (hcong.α * (hcong.β + 1) / hcong.β))
      (volume.restrict (UnitCube d)) := by
    have huLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) u :=
      Periodic.memLpPer_iff_memLp.mpr (MeasureTheory.Lp.memLp v.2.1)
    have hraw : MeasureTheory.Integrable
        (fun x => ‖u x‖ ^ (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)).toReal)
        (volume.restrict (UnitCube d)) :=
      huLp.toMemLp.integrable_norm_rpow
        (ENNReal.ofReal_pos.mpr hγ_pos).ne' ENNReal.ofReal_ne_top
    rw [ENNReal.toReal_ofReal hγ_pos.le] at hraw
    refine hraw.congr ?_
    filter_upwards with x
    rw [Real.norm_eq_abs]
  -- Per-coordinate integrability of `|Du i|^γ̄`.
  have hDui_int : ∀ i, MeasureTheory.Integrable
      (fun x => |Du i x| ^ (hcong.α * (hcong.β + 1) / hcong.β))
      (volume.restrict (UnitCube d)) := by
    intro i
    have hraw : MeasureTheory.Integrable
        (fun x => ‖Du i x‖ ^ (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)).toReal)
        (volume.restrict (UnitCube d)) :=
      (hDuLp i).toMemLp.integrable_norm_rpow
        (ENNReal.ofReal_pos.mpr hγ_pos).ne' ENNReal.ofReal_ne_top
    rw [ENNReal.toReal_ofReal hγ_pos.le] at hraw
    refine hraw.congr ?_
    filter_upwards with x
    rw [Real.norm_eq_abs]
  -- εint is integrable.
  have hεint_int : MeasureTheory.Integrable
      (fun x => vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β) (fun i => Du i x)
            * ((fun i => Du i x) ⬝ (fun i => Du i x))
          + absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β) (u x) * (u x * u x))
      (volume.restrict (UnitCube d)) := by
    have hsum := hdot_int.add hu_int
    refine hsum.congr ?_
    filter_upwards with x
    exact (hεint_eq x).symm
  -- Pointwise: `(Du⬝Du)^(γ̄/2) ≤ εint x` and `|u|^γ̄ ≤ εint x`.
  have hdot_le_εint : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ((fun i => Du i x) ⬝ (fun i => Du i x))
          ^ (hcong.α * (hcong.β + 1) / hcong.β / 2)
        ≤ vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β) (fun i => Du i x)
              * ((fun i => Du i x) ⬝ (fun i => Du i x))
            + absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β) (u x) * (u x * u x) := by
    filter_upwards with x
    rw [hεint_eq x]
    have h2 : 0 ≤ |u x| ^ (hcong.α * (hcong.β + 1) / hcong.β) :=
      Real.rpow_nonneg (abs_nonneg _) _
    linarith
  have hu_le_εint : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      |u x| ^ (hcong.α * (hcong.β + 1) / hcong.β)
        ≤ vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β) (fun i => Du i x)
              * ((fun i => Du i x) ⬝ (fun i => Du i x))
            + absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β) (u x) * (u x * u x) := by
    filter_upwards with x
    rw [hεint_eq x]
    have h1 : 0 ≤ ((fun i => Du i x) ⬝ (fun i => Du i x))
        ^ (hcong.α * (hcong.β + 1) / hcong.β / 2) :=
      Real.rpow_nonneg (Finset.sum_nonneg (fun i _ => mul_self_nonneg _)) _
    linarith
  -- Per-coordinate domination `|Du i|^γ̄ ≤ (Du⬝Du)^(γ̄/2)`.
  have hcoord_dom : ∀ i, ∀ x,
      |Du i x| ^ (hcong.α * (hcong.β + 1) / hcong.β)
        ≤ ((fun j => Du j x) ⬝ (fun j => Du j x))
            ^ (hcong.α * (hcong.β + 1) / hcong.β / 2) := by
    intro i x
    -- `(Du i x)^2 ≤ Du⬝Du`, then raise to `γ̄/2`.
    have hsq : Du i x * Du i x ≤ (fun j => Du j x) ⬝ (fun j => Du j x) := by
      unfold dotProduct
      refine Finset.single_le_sum (f := fun j => Du j x * Du j x)
        (fun j _ => mul_self_nonneg _) (Finset.mem_univ i)
    -- `|Du i x|^γ̄ = (|Du i x|^2)^(γ̄/2) = ((Du i x)^2)^(γ̄/2)`.
    have hrewrite : |Du i x| ^ (hcong.α * (hcong.β + 1) / hcong.β)
        = (Du i x * Du i x) ^ (hcong.α * (hcong.β + 1) / hcong.β / 2) := by
      rw [show Du i x * Du i x = |Du i x| ^ (2 : ℝ) from by
            rw [Real.rpow_two, sq_abs, sq],
          ← Real.rpow_mul (abs_nonneg _)]
      congr 1; ring
    rw [hrewrite]
    refine Real.rpow_le_rpow (mul_self_nonneg _) hsq (by positivity)
  -- `∑∫|Du i|^γ̄ ≤ d·∫εint`.
  have hsum_Du_le : ∑ i, ∫ x in UnitCube d,
        |Du i x| ^ (hcong.α * (hcong.β + 1) / hcong.β)
      ≤ (d : ℝ) * ∫ x in UnitCube d,
          (vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β) (fun i => Du i x)
              * ((fun i => Du i x) ⬝ (fun i => Du i x))
            + absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β) (u x) * (u x * u x)) := by
    -- Each `∫|Du i|^γ̄ ≤ ∫(Du⬝Du)^(γ̄/2) ≤ ∫εint`.
    have hstep : ∀ i, ∫ x in UnitCube d,
          |Du i x| ^ (hcong.α * (hcong.β + 1) / hcong.β)
        ≤ ∫ x in UnitCube d,
            (vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β) (fun i => Du i x)
                * ((fun i => Du i x) ⬝ (fun i => Du i x))
              + absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β) (u x) * (u x * u x)) := by
      intro i
      calc ∫ x in UnitCube d, |Du i x| ^ (hcong.α * (hcong.β + 1) / hcong.β)
          ≤ ∫ x in UnitCube d, ((fun j => Du j x) ⬝ (fun j => Du j x))
              ^ (hcong.α * (hcong.β + 1) / hcong.β / 2) :=
            integral_mono (hDui_int i) hdot_int (fun x => hcoord_dom i x)
        _ ≤ ∫ x in UnitCube d,
              (vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β) (fun i => Du i x)
                  * ((fun i => Du i x) ⬝ (fun i => Du i x))
                + absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β) (u x) * (u x * u x)) :=
            integral_mono_ae hdot_int hεint_int hdot_le_εint
    calc ∑ i, ∫ x in UnitCube d, |Du i x| ^ (hcong.α * (hcong.β + 1) / hcong.β)
        ≤ ∑ _i : Fin d, ∫ x in UnitCube d,
            (vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β) (fun i => Du i x)
                * ((fun i => Du i x) ⬝ (fun i => Du i x))
              + absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β) (u x) * (u x * u x)) :=
          Finset.sum_le_sum (fun i _ => hstep i)
      _ = (d : ℝ) * ∫ x in UnitCube d,
            (vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β) (fun i => Du i x)
                * ((fun i => Du i x) ⬝ (fun i => Du i x))
              + absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β) (u x) * (u x * u x)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- `∫|u|^γ̄ ≤ ∫εint`.
  have hu_int_le : ∫ x in UnitCube d, |u x| ^ (hcong.α * (hcong.β + 1) / hcong.β)
      ≤ ∫ x in UnitCube d,
          (vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β) (fun i => Du i x)
              * ((fun i => Du i x) ⬝ (fun i => Du i x))
            + absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β) (u x) * (u x * u x)) :=
    integral_mono_ae hu_int hεint_int hu_le_εint
  -- ============================================================
  -- Step F: assemble `‖v.2‖^γ̄ ≤ (d+1)^(γ̄+1)·∫εint = ((d+1)^(γ̄+1)/ε)·(ε-term)`.
  -- ============================================================
  set Iεint : ℝ := ∫ x in UnitCube d,
      (vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β) (fun i => Du i x)
          * ((fun i => Du i x) ⬝ (fun i => Du i x))
        + absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β) (u x) * (u x * u x))
    with hIεint_def
  have hIεint_nn : 0 ≤ Iεint := by
    rw [hIεint_def]
    refine integral_nonneg ?_
    intro x
    refine add_nonneg ?_ ?_
    · refine mul_nonneg ?_ (Finset.sum_nonneg (fun i _ => mul_self_nonneg _))
      unfold vecAbsPowMinusTwo
      exact Real.rpow_nonneg (Finset.sum_nonneg (fun i _ => mul_self_nonneg _)) _
    · refine mul_nonneg ?_ (mul_self_nonneg _)
      unfold absPowMinusTwo
      exact Real.rpow_nonneg (abs_nonneg _) _
  -- `(d+1)^γ̄ ≥ 0`.
  have hdp1_nn : (0 : ℝ) ≤ ((d : ℝ) + 1) ^ (hcong.α * (hcong.β + 1) / hcong.β) := by
    positivity
  have hv2_le_εint :
      ‖v.2‖ ^ (hcong.α * (hcong.β + 1) / hcong.β)
        ≤ ((d : ℝ) + 1) ^ (hcong.α * (hcong.β + 1) / hcong.β + 1) * Iεint := by
    -- `∫|u|^γ̄ + ∑∫|Du i|^γ̄ ≤ (d+1)·∫εint`.
    have hbracket : (∫ x in UnitCube d, |u x| ^ (hcong.α * (hcong.β + 1) / hcong.β))
          + ∑ i, ∫ x in UnitCube d, |Du i x| ^ (hcong.α * (hcong.β + 1) / hcong.β)
        ≤ ((d : ℝ) + 1) * Iεint := by
      rw [hIεint_def]
      have := add_le_add hu_int_le hsum_Du_le
      -- `Iεint + d·Iεint = (d+1)·Iεint`.
      nlinarith [this, hIεint_nn]
    calc ‖v.2‖ ^ (hcong.α * (hcong.β + 1) / hcong.β)
        ≤ ((d : ℝ) + 1) ^ (hcong.α * (hcong.β + 1) / hcong.β) *
            ((∫ x in UnitCube d, |u x| ^ (hcong.α * (hcong.β + 1) / hcong.β))
              + ∑ i, ∫ x in UnitCube d, |Du i x| ^ (hcong.α * (hcong.β + 1) / hcong.β)) :=
          hC_u
      _ ≤ ((d : ℝ) + 1) ^ (hcong.α * (hcong.β + 1) / hcong.β) * (((d : ℝ) + 1) * Iεint) :=
          mul_le_mul_of_nonneg_left hbracket hdp1_nn
      _ = ((d : ℝ) + 1) ^ (hcong.α * (hcong.β + 1) / hcong.β + 1) * Iεint := by
          rw [Real.rpow_add_one (by positivity : ((d : ℝ) + 1) ≠ 0)]
          ring
  -- ============================================================
  -- Step G: chain everything.
  -- ============================================================
  -- The gauge unfolds to `(1/C_eul)·∫m^β̄ + (1/C_eul)·∫‖Du‖^α + ε·Iεint`.
  -- Nonneg of the momentum term.
  have hmom_nn : 0 ≤ (1 / C_eul) * (∫ x in UnitCube d,
      ‖fun i => (⇑(v.2.2 i) : (Fin d → ℝ) → ℝ) x‖ ^ hcong.α) := by
    refine mul_nonneg (by positivity) ?_
    refine integral_nonneg ?_
    intro x; exact Real.rpow_nonneg (norm_nonneg _) _
  -- Mass term value.
  set Imass : ℝ := (1 / C_eul) * ∫ x in UnitCube d,
      ((⇑v.1 : (Fin d → ℝ) → ℝ) x) ^ (hcong.β + 1) with hImass_def
  have hImass_nn : 0 ≤ Imass := by
    rw [hImass_def]
    refine mul_nonneg (by positivity) ?_
    refine integral_nonneg_of_ae ?_
    filter_upwards [hv_pos] with x hx
    exact Real.rpow_nonneg hx _
  -- `‖v.1‖^β̄ = C_eul · Imass`.
  have hv1_val : ‖v.1‖ ^ (hcong.β + 1) = C_eul * Imass := by
    rw [hB_pos, hImass_def]; field_simp
  -- The gauge equals `Imass + (momentum) + ε·Iεint`.
  have hgauge_eq : congestionCoerciveGauge (d := d) hcong C_eul ε v
      = Imass
        + (1 / C_eul) * (∫ x in UnitCube d,
            ‖fun i => (⇑(v.2.2 i) : (Fin d → ℝ) → ℝ) x‖ ^ hcong.α)
        + ε * Iεint := by
    unfold congestionCoerciveGauge
    rw [hImass_def, hIεint_def]
  -- Final chain.
  -- `‖v‖^κ ≤ 1 + ‖v.1‖^β̄ + ‖v.2‖^γ̄`
  --        ≤ 1 + C_eul·Imass + ((d+1)^(γ̄+1)/ε)·(ε·Iεint)
  --        ≤ 1 + Cbig·gauge.
  rw [hgauge_eq]
  -- Abbreviate the momentum term.
  set Imom : ℝ := (1 / C_eul) * (∫ x in UnitCube d,
      ‖fun i => (⇑(v.2.2 i) : (Fin d → ℝ) → ℝ) x‖ ^ hcong.α) with hImom_def
  -- `Cbig := C_eul + (d+1)^(γ̄+1)/ε`. We show the target via an explicit
  -- lower bound on `Cbig·gauge`.
  set Cbig : ℝ := C_eul + ((d : ℝ) + 1) ^ (hcong.α * (hcong.β + 1) / hcong.β + 1) / ε
    with hCbig_def
  set Dpow : ℝ := ((d : ℝ) + 1) ^ (hcong.α * (hcong.β + 1) / hcong.β + 1) with hDpow_def
  have hDpow_nn : 0 ≤ Dpow := by rw [hDpow_def]; positivity
  have hDpowε_nn : 0 ≤ Dpow / ε := div_nonneg hDpow_nn hε.le
  -- `‖v‖^κ ≤ 1 + ‖v.1‖^β̄ + ‖v.2‖^γ̄ ≤ 1 + C_eul·Imass + Dpow·Iεint`.
  have hupper : ‖v‖ ^ min (hcong.β + 1) (hcong.α * (hcong.β + 1) / hcong.β)
      ≤ 1 + C_eul * Imass + Dpow * Iεint := by
    have h1 : ‖v.1‖ ^ (hcong.β + 1) = C_eul * Imass := hv1_val
    have h2 : ‖v.2‖ ^ (hcong.α * (hcong.β + 1) / hcong.β) ≤ Dpow * Iεint := by
      rw [hDpow_def]; exact hv2_le_εint
    linarith [hmin]
  -- `Cbig·gauge = Cbig·Imass + Cbig·Imom + Cbig·ε·Iεint`
  --            ≥ C_eul·Imass + Dpow·Iεint` (all extra terms ≥ 0).
  have hgauge_lb : C_eul * Imass + Dpow * Iεint ≤ Cbig * (Imass + Imom + ε * Iεint) := by
    rw [hCbig_def]
    -- `(Dpow/ε)·ε·Iεint = Dpow·Iεint`.
    have hcancel : (Dpow / ε) * (ε * Iεint) = Dpow * Iεint := by
      field_simp
    have hImom_nn : 0 ≤ Imom := by rw [hImom_def]; exact hmom_nn
    nlinarith [hcancel, mul_nonneg hC.le hImom_nn,
      mul_nonneg (mul_nonneg hC.le hε.le) hIεint_nn,
      mul_nonneg hDpowε_nn hImass_nn, mul_nonneg hDpowε_nn hImom_nn,
      mul_nonneg hC.le hImass_nn]
  linarith [hupper, hgauge_lb]


/-! ## Congestion coercive-gauge quotient divergence (`BB1d child 3b`)

`gauge / ‖v‖ → +∞` along `cobounded ⊓ 𝓟(congestionBanachK)`. Derived from
the norm bridge `congestion_coercivity_norm_bridge`
(`‖v‖^κ ≤ 1 + Cbig · gauge`) by the same `atTop`-machinery as the
simple-power skeleton `tendsto_scaled_aepsiCoerciveGauge_div_norm_atTop`,
except the final step uses `Filter.tendsto_atTop_mono'` (the bridge is an
*inequality*, not an equality). -/

/-- **Congestion coercive-gauge quotient divergence (`BB1d child 3b`).**

`congestionCoerciveGauge hcong C_eul ε v / ‖v‖ → +∞` along
`cobounded ⊓ 𝓟(congestionBanachK …)`. The eventual lower bound
`gauge/‖v‖ ≥ (1/Cbig)·‖v‖^(κ-1) - 1/(Cbig·‖v‖)` comes from the norm
bridge; the right-hand side diverges because `κ > 1`. -/
theorem congestion_coercivity_quotient_tendsto
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    {C_eul ε : ℝ} (hC : 0 < C_eul) (hε : 0 < ε)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))] :
    Filter.Tendsto
      (fun v : congestionXBanach d
               (ENNReal.ofReal (hcong.β + 1))
               (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) =>
        congestionCoerciveGauge (d := d) hcong C_eul ε v / ‖v‖)
      (Bornology.cobounded (congestionXBanach d
               (ENNReal.ofReal (hcong.β + 1))
               (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))
        ⊓ Filter.principal
            (congestionBanachK d
              (ENNReal.ofReal (hcong.β + 1))
              (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
              (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
              hcong.α hcong.β hcong.τ))
      Filter.atTop := by
  classical
  -- `κ = coercivityGaugeExponent (β+1) γ̄ = min (β+1) γ̄`.
  set κ := Theorems.SimplePower.Banach.coercivityGaugeExponent
              (hcong.β + 1) (hcong.α * (hcong.β + 1) / hcong.β) with hκ_def
  have hβ_pos : 0 < hcong.β := hcong.hβ
  have hκ : 1 < κ :=
    Theorems.SimplePower.Banach.one_lt_coercivityGaugeExponent
      (by linarith [hcong.hβ])
      (by rw [lt_div_iff₀ hβ_pos, one_mul]; nlinarith [hcong.hα, hβ_pos])
  have hκ_pos : 0 < κ := lt_trans one_pos hκ
  have hκm1_pos : 0 < κ - 1 := sub_pos.mpr hκ
  -- `Cbig > 0`.
  have hCbig_pos :
      0 < C_eul + ((d : ℝ) + 1) ^ (hcong.α * (hcong.β + 1) / hcong.β + 1) / ε := by
    positivity
  set Cbig := C_eul + ((d : ℝ) + 1) ^ (hcong.α * (hcong.β + 1) / hcong.β + 1) / ε
    with hCbig_def
  -- Abbreviate the filter.
  set F := Bornology.cobounded (congestionXBanach d
               (ENNReal.ofReal (hcong.β + 1))
               (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))
        ⊓ Filter.principal
            (congestionBanachK d
              (ENNReal.ofReal (hcong.β + 1))
              (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
              (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
              hcong.α hcong.β hcong.τ)
    with hF_def
  -- Step 1: `‖v‖ → +∞` along `F`.
  have h_nrm : Filter.Tendsto
      (fun v : congestionXBanach d
               (ENNReal.ofReal (hcong.β + 1))
               (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) => ‖v‖)
      F Filter.atTop :=
    tendsto_norm_cobounded_atTop.mono_left inf_le_left
  -- Step 2: `‖v‖^(κ-1) → +∞`.
  have h_pow : Filter.Tendsto
      (fun v : congestionXBanach d
               (ENNReal.ofReal (hcong.β + 1))
               (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) =>
        ‖v‖ ^ (κ - 1))
      F Filter.atTop :=
    (tendsto_rpow_atTop hκm1_pos).comp h_nrm
  -- Step 3: `(1/Cbig)·‖v‖^(κ-1) → +∞`.
  have h_main : Filter.Tendsto
      (fun v : congestionXBanach d
               (ENNReal.ofReal (hcong.β + 1))
               (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) =>
        (1 / Cbig) * ‖v‖ ^ (κ - 1))
      F Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity) h_pow
  -- Step 4: `1/(Cbig·‖v‖) → 0`.
  have h_inv_zero : Filter.Tendsto
      (fun v : congestionXBanach d
               (ENNReal.ofReal (hcong.β + 1))
               (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) =>
        1 / (Cbig * ‖v‖))
      F (nhds 0) := by
    have h_inv := h_nrm.inv_tendsto_atTop
    have h_mul := h_inv.const_mul (1 / Cbig)
    simp only [mul_zero] at h_mul
    refine h_mul.congr ?_
    intro v
    simp only [one_div, mul_inv, Pi.inv_apply]
  -- Step 5: difference `→ +∞`.
  have h_diff : Filter.Tendsto
      (fun v : congestionXBanach d
               (ENNReal.ofReal (hcong.β + 1))
               (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) =>
        (1 / Cbig) * ‖v‖ ^ (κ - 1) - 1 / (Cbig * ‖v‖))
      F Filter.atTop := by
    have h_neg := h_inv_zero.neg
    simp only [neg_zero] at h_neg
    have h_add := h_main.atTop_add h_neg
    refine h_add.congr ?_
    intro v
    ring
  -- Step 6: eventual lower bound + `tendsto_atTop_mono'` (bridge is an inequality).
  have h_nrm_pos : ∀ᶠ v in F, (0 : ℝ) < ‖v‖ := h_nrm.eventually_gt_atTop 0
  have h_mem : ∀ᶠ v in F,
      v ∈ congestionBanachK d
            (ENNReal.ofReal (hcong.β + 1))
            (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
            (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
            hcong.α hcong.β hcong.τ := by
    rw [hF_def]
    exact Filter.eventually_inf_principal.mpr (Filter.Eventually.of_forall (fun v hv => hv))
  refine Filter.tendsto_atTop_mono' _ ?_ h_diff
  filter_upwards [h_nrm_pos, h_mem] with v hv_pos hv_mem
  have hv_ne : ‖v‖ ≠ 0 := ne_of_gt hv_pos
  -- a.e. nonnegativity of the `m`-component from `congestionBanachK` membership.
  have hv_pos_ae : 0 ≤ᵐ[volume.restrict (UnitCube d)] (⇑v.1 : (Fin d → ℝ) → ℝ) := by
    obtain ⟨c, hc_pos, hc_le⟩ := hv_mem.1.2.2.1
    filter_upwards [hc_le] with x hx
    simp only [Pi.zero_apply]
    linarith
  -- Apply the bridge: `‖v‖^κ ≤ 1 + Cbig · gauge`.
  have hbridge := congestion_coercivity_norm_bridge (d := d)
    hcong hC hε v hv_pos_ae
  rw [← hκ_def, ← hCbig_def] at hbridge
  -- Rearrange: `gauge ≥ (‖v‖^κ - 1)/Cbig`.
  have hgauge_lb : (‖v‖ ^ κ - 1) / Cbig
      ≤ congestionCoerciveGauge (d := d) hcong C_eul ε v := by
    rw [div_le_iff₀ hCbig_pos]
    nlinarith [hbridge]
  -- Divide by `‖v‖ > 0`.
  have hquot : (‖v‖ ^ κ - 1) / (Cbig * ‖v‖)
      ≤ congestionCoerciveGauge (d := d) hcong C_eul ε v / ‖v‖ := by
    rw [← div_div]
    exact div_le_div_of_nonneg_right hgauge_lb hv_pos.le
  -- `(‖v‖^κ - 1)/(Cbig·‖v‖) = (1/Cbig)·‖v‖^(κ-1) - 1/(Cbig·‖v‖)`.
  have hsplit : ‖v‖ ^ κ = ‖v‖ ^ (κ - 1) * ‖v‖ := by
    have hh := Real.rpow_add hv_pos (κ - 1) 1
    rw [Real.rpow_one] at hh
    rw [show (κ - 1) + 1 = κ from by ring] at hh
    exact hh
  have hsimp : (‖v‖ ^ κ - 1) / (Cbig * ‖v‖)
      = (1 / Cbig) * ‖v‖ ^ (κ - 1) - 1 / (Cbig * ‖v‖) := by
    rw [hsplit]
    field_simp
  rw [hsimp] at hquot
  exact hquot


/-! ## Congestion coercivity assembly (`BB1d child 4`, completes `BB1d`)

Packages the two landed analytic halves
(`congestion_coercivity_bound_eventually`, child 2c, and
`congestion_coercivity_quotient_tendsto`, child 3b) into the
`Monotone.IsCoerciveAt` predicate for the totalized operator
`congestionAepsiOpK` on the strict-positivity cone `congestionBanachK`.

The structure mirrors the simple-power skeleton
`isCoerciveAt_Aepsi_CLM_K_Aepsi` (`SimplePower/Banach/AbstractLifts.lean`):
the abstract `coercAepsi` quotient theorem is fed `hbound`,
`h_nrm_pos`, `h_nrm_tendsto`, `hquot_tendsto`, producing a `Tendsto`
in `mfgOperatorEpsPair`-form, which is bridged back to the abstract
operator-difference form of `IsCoerciveAt` via `Filter.Tendsto.congr'`
on the on-domain identity `congestionAepsiOpK_apply_of_mem`. -/

/-- **Congestion operator coercivity (`BB1d child 4`).**

`congestionAepsiOpK` is coercive at the base point `v₀ ∈ congestionBanachK`
(with the `(1, 0, 0)` a.e. profile). Pure assembly of the two landed
halves; the analytic content is entirely in `congestion_coercivity_bound_eventually`
(child 2c) and `congestion_coercivity_quotient_tendsto` (child 3b). -/
theorem congestionAepsiOpK_coercive
    {V : (Fin d → ℝ) → ℝ}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (ε : ℝ) (hε : 0 < ε)
    (v₀ : congestionXBanach d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))
    (hv₀_mem : v₀ ∈ congestionBanachK d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ)
    (hv₀_m : ⇑v₀.1 =ᵐ[Measure.restrict volume (UnitCube d)] (fun _ => (1 : ℝ)))
    (hv₀_u : ⇑v₀.2.1 =ᵐ[Measure.restrict volume (UnitCube d)] (fun _ => (0 : ℝ)))
    (hv₀_Du : ∀ i, ⇑(v₀.2.2 i)
                   =ᵐ[Measure.restrict volume (UnitCube d)] (fun _ => (0 : ℝ))) :
    Monotone.IsCoerciveAt
      (congestionBanachK d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
          hcong.α hcong.β hcong.τ)
      (congestionAepsiOpK hmon hcong hVmeas hV ε)
      v₀ := by
  classical
  refine ⟨hv₀_mem, ?_⟩
  -- The coercivity filter.
  set F := Bornology.cobounded
              (congestionXBanach d
                (ENNReal.ofReal (hcong.β + 1))
                (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))
            ⊓ Filter.principal
                (congestionBanachK d
                  (ENNReal.ofReal (hcong.β + 1))
                  (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
                  (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
                  hcong.α hcong.β hcong.τ)
    with hF_def
  -- The fixed coercivity constant `C_eul` (child 2b Young constant).
  set C_eul : ℝ :=
    coercivityIntegrandLowerBoundYoungConstant d
      (2 * congestionCoercivityConstant (d := d) hcong) hcong.α hcong.β
    with hC_eul_def
  have hC_eul_pos : 0 < C_eul :=
    coercivityIntegrandLowerBoundYoungConstant_pos d _ hcong.α hcong.β
  -- `coerciveFilter` unfolds to `F`.
  change Filter.Tendsto
      (fun v => (congestionAepsiOpK hmon hcong hVmeas hV ε v
                  - congestionAepsiOpK hmon hcong hVmeas hV ε v₀) (v - v₀) / ‖v‖)
      F Filter.atTop
  -- Membership of the running `v` is eventual along `F`.
  have h_eventually_K :
      ∀ᶠ v in F,
        v ∈ congestionBanachK d
            (ENNReal.ofReal (hcong.β + 1))
            (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
            (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
            hcong.α hcong.β hcong.τ := by
    rw [hF_def]
    exact Filter.eventually_inf_principal.mpr
      (Filter.Eventually.of_forall (fun _ h => h))
  -- The per-`v` identity equating the operator-difference form with the
  -- `coercAepsi` (`mfgOperatorEpsPair`) form. Proved exactly as the
  -- `h_subapply`/test-swap/primal-swap chain inside
  -- `congestion_coercivity_bound_eventually`.
  have h_op_eq :
      ∀ᶠ v in F,
        (congestionAepsiOpK hmon hcong hVmeas hV ε v
            - congestionAepsiOpK hmon hcong hVmeas hV ε v₀) (v - v₀)
          = mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              (hcong.α * (hcong.β + 1) / hcong.β) ε
              (fun i => ⇑(v.2.2 i)) (⇑v.1) (⇑v.2.1)
              (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1)
            - mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                (hcong.α * (hcong.β + 1) / hcong.β) ε
                (fun _ _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ))
                (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1) := by
    filter_upwards [h_eventually_K] with v hv
    set Du : Fin d → (Fin d → ℝ) → ℝ := fun i => ⇑(v.2.2 i) with hDu_def
    set m : (Fin d → ℝ) → ℝ := ⇑v.1 with hm_def
    set u : (Fin d → ℝ) → ℝ := ⇑v.2.1 with hu_def
    have h_subapply :
        (congestionAepsiOpK hmon hcong hVmeas hV ε v
            - congestionAepsiOpK hmon hcong hVmeas hV ε v₀) (v - v₀)
          = mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              (hcong.α * (hcong.β + 1) / hcong.β) ε
              Du m u
              (fun i => ⇑((v - v₀).2.2 i)) (⇑(v - v₀).1) (⇑(v - v₀).2.1)
            - mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                (hcong.α * (hcong.β + 1) / hcong.β) ε
                (fun i => ⇑(v₀.2.2 i)) (⇑v₀.1) (⇑v₀.2.1)
                (fun i => ⇑((v - v₀).2.2 i)) (⇑(v - v₀).1) (⇑(v - v₀).2.1) := by
      rw [ContinuousLinearMap.sub_apply,
          congestionAepsiOpK_apply_of_mem hmon hcong hVmeas hV ε hv (v - v₀),
          congestionAepsiOpK_apply_of_mem hmon hcong hVmeas hV ε hv₀_mem (v - v₀)]
    have h_eta_ae : ⇑((v - v₀).1)
                      =ᵐ[Measure.restrict volume (UnitCube d)] (m - 1) := by
      have h_pair : (v - v₀).1 = v.1 - v₀.1 := rfl
      rw [h_pair]
      filter_upwards [MeasureTheory.Lp.coeFn_sub v.1 v₀.1, hv₀_m] with x hx h0
      rw [hx]
      change (⇑v.1 - ⇑v₀.1) x = (m - 1) x
      rw [Pi.sub_apply, Pi.sub_apply, h0, Pi.one_apply]
    have h_nu_ae : ⇑((v - v₀).2.1)
                      =ᵐ[Measure.restrict volume (UnitCube d)] u := by
      have h_pair : (v - v₀).2.1 = v.2.1 - v₀.2.1 := rfl
      rw [h_pair]
      filter_upwards [MeasureTheory.Lp.coeFn_sub v.2.1 v₀.2.1, hv₀_u] with x hx h0
      rw [hx]
      change (⇑v.2.1 - ⇑v₀.2.1) x = u x
      rw [Pi.sub_apply, h0, sub_zero]
    have h_Dnu_ae : ∀ i, ⇑((v - v₀).2.2 i)
                      =ᵐ[Measure.restrict volume (UnitCube d)]
                        fun x => Du i x := by
      intro i
      have h_pair : (v - v₀).2.2 i = v.2.2 i - v₀.2.2 i := rfl
      rw [h_pair]
      filter_upwards [MeasureTheory.Lp.coeFn_sub (v.2.2 i) (v₀.2.2 i),
        hv₀_Du i] with x hx h0
      rw [hx]
      change (⇑(v.2.2 i) - ⇑(v₀.2.2 i)) x = Du i x
      rw [Pi.sub_apply, h0, sub_zero]
    have h_test_swap1 :
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            (hcong.α * (hcong.β + 1) / hcong.β) ε
            Du m u
            (fun i => ⇑((v - v₀).2.2 i)) (⇑(v - v₀).1) (⇑(v - v₀).2.1)
          = mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              (hcong.α * (hcong.β + 1) / hcong.β) ε
              Du m u Du (m - 1) u :=
      Theorems.SimplePower.Banach.mfgOperatorEpsPair_test_congr_ae
        V H DpH (hcong.α * (hcong.β + 1) / hcong.β) ε Du m u
        h_eta_ae h_nu_ae h_Dnu_ae
    have h_test_swap2 :
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            (hcong.α * (hcong.β + 1) / hcong.β) ε
            (fun i => ⇑(v₀.2.2 i)) (⇑v₀.1) (⇑v₀.2.1)
            (fun i => ⇑((v - v₀).2.2 i)) (⇑(v - v₀).1) (⇑(v - v₀).2.1)
          = mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              (hcong.α * (hcong.β + 1) / hcong.β) ε
              (fun i => ⇑(v₀.2.2 i)) (⇑v₀.1) (⇑v₀.2.1)
              Du (m - 1) u :=
      Theorems.SimplePower.Banach.mfgOperatorEpsPair_test_congr_ae
        V H DpH (hcong.α * (hcong.β + 1) / hcong.β) ε
        (fun i => ⇑(v₀.2.2 i)) (⇑v₀.1) (⇑v₀.2.1)
        h_eta_ae h_nu_ae h_Dnu_ae
    have h_primal_swap :
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            (hcong.α * (hcong.β + 1) / hcong.β) ε
            (fun i => ⇑(v₀.2.2 i)) (⇑v₀.1) (⇑v₀.2.1)
            Du (m - 1) u
          = mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              (hcong.α * (hcong.β + 1) / hcong.β) ε
              (fun _ _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ))
              Du (m - 1) u :=
      Theorems.SimplePower.Banach.mfgOperatorEpsPair_primal_congr_ae
        V H DpH (hcong.α * (hcong.β + 1) / hcong.β) ε Du (m - 1) u
        hv₀_m hv₀_u hv₀_Du
    rw [h_subapply, h_test_swap1, h_test_swap2, h_primal_swap]
  -- `hbound` in `coercAepsi`-form: rewrite the child-2c operator bound
  -- through `h_op_eq`.
  have hbound_op := congestion_coercivity_bound_eventually (d := d)
    hmon hcong hVmeas hV ε v₀ hv₀_mem hv₀_m hv₀_u hv₀_Du
  simp only at hbound_op
  rw [← hF_def, ← hC_eul_def] at hbound_op
  have hbound :
      ∀ᶠ v in F,
        congestionCoerciveGauge (d := d) hcong C_eul ε v - C_eul ≤
          mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              (hcong.α * (hcong.β + 1) / hcong.β) ε
              (fun i => ⇑(v.2.2 i)) (⇑v.1) (⇑v.2.1)
              (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1)
            - mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                (hcong.α * (hcong.β + 1) / hcong.β) ε
                (fun _ _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ))
                (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1) := by
    filter_upwards [hbound_op, h_op_eq] with v hv heq
    rw [← heq]; exact hv
  -- norm machinery.
  have h_nrm_tendsto :
      Filter.Tendsto (fun v : congestionXBanach d
                 (ENNReal.ofReal (hcong.β + 1))
                 (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) => ‖v‖)
        F Filter.atTop := by
    rw [hF_def]; exact tendsto_norm_cobounded_atTop.mono_left inf_le_left
  have h_nrm_pos : ∀ᶠ v in F, (0 : ℝ) < ‖v‖ := h_nrm_tendsto.eventually_gt_atTop 0
  -- the quotient tendsto (child 3b).
  have hquot_tendsto := congestion_coercivity_quotient_tendsto (d := d)
    hcong hC_eul_pos hε
  rw [← hF_def] at hquot_tendsto
  -- assemble via the abstract `coercAepsi` quotient theorem.
  have hCoerc :=
    Theorems.SimplePower.coercAepsi (V := V) (H := H) (DpH := DpH)
      (hcong.α * (hcong.β + 1) / hcong.β) ε
      (l := F)
      (Du_of := fun v => fun i => ⇑(v.2.2 i))
      (m_of := fun v => ⇑v.1)
      (u_of := fun v => ⇑v.2.1)
      (g := fun v => congestionCoerciveGauge (d := d) hcong C_eul ε v)
      (nrm := fun v => ‖v‖) (C := C_eul)
      hbound h_nrm_pos h_nrm_tendsto hquot_tendsto
  -- bridge back to the abstract operator-difference quotient.
  refine hCoerc.congr' ?_
  filter_upwards [h_op_eq] with v heq
  rw [heq]

/-! ## Phase 7 — `CongestionRegularizedSolutionUpstreamPack` producer (BB1e child 2b)

Assemble the seven-field upstream pack from the paper data
`(hmon, hcong, hVmeas, hV, ε, hε)` plus the two exponent `Fact`
instances. Every field is genuinely discharged from the landed
BB1a–d + child1/child2a lemmas — no re-assumption, no oracle.

This producer lives in `Coercivity.lean` (not `Existence.lean`) because
its `A_coerc` field consumes `congestionAepsiOpK_coercive`, which is
defined here downstream of `Existence.lean` (the import goes
`Coercivity → Existence`, so the pack structure and all other lemmas are
in scope). This COMPLETES BB1. -/

/-- **Reflexivity of the congestion Banach realisation, derived from
`hcong`.** Adapted from `congestionOracle_hRefl` (Compactness.lean:1039,
which is `private` and takes `CongestionAprioriPowerData`, hence not
callable here): the conjugate exponents `β̄' = (β+1)/β` and
`γ̄' = γ̄/(γ̄-1)` are computed in-body from `hcong.hα`/`hcong.hβ` and fed
to `Periodic.lpSobolev_product_isReflexive`. -/
lemma coercivity_congestionXBanach_isReflexive_of_hcong
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))] :
    Periodic.IsReflexiveNormedSpace
      (congestionXBanach d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))) := by
  classical
  have hβ : 0 < hcong.β := hcong.hβ
  have hα : 1 < hcong.α := hcong.hα
  -- β-side: βBarReal = β + 1, conjugate βBarReal' = (β+1)/β.
  set βBarReal : ℝ := hcong.β + 1 with hβBar_def
  set βBarReal' : ℝ := (hcong.β + 1) / hcong.β with hβBar'_def
  have h_one_lt_βBarReal : (1 : ℝ) < βBarReal := by rw [hβBar_def]; linarith
  have h_one_lt_βBarReal' : (1 : ℝ) < βBarReal' := by
    rw [hβBar'_def, lt_div_iff₀ hβ, one_mul]; linarith
  have hβConj_real : Real.HolderConjugate βBarReal βBarReal' := by
    rw [hβBar_def, hβBar'_def, Real.holderConjugate_iff]
    refine ⟨by linarith, ?_⟩
    have hβ1 : (0 : ℝ) < hcong.β + 1 := by linarith
    have hβ1ne : hcong.β + 1 ≠ 0 := ne_of_gt hβ1
    have hβne : hcong.β ≠ 0 := ne_of_gt hβ
    have hdiv : ((hcong.β + 1) / hcong.β)⁻¹ = hcong.β / (hcong.β + 1) := by
      field_simp
    rw [hdiv]; field_simp; ring
  haveI : ENNReal.HolderConjugate (ENNReal.ofReal βBarReal)
            (ENNReal.ofReal βBarReal') :=
    Real.HolderConjugate.ennrealOfReal hβConj_real
  haveI : Fact (1 ≤ ENNReal.ofReal βBarReal') :=
    ⟨by
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
      exact ENNReal.ofReal_le_ofReal h_one_lt_βBarReal'.le⟩
  -- γ-side: γBarReal = γ̄ = α(β+1)/β, conjugate γBarReal' = γ̄/(γ̄-1).
  have h_one_lt_γBarReal_g : (1 : ℝ) < Hamiltonian.gammaBar hcong.α hcong.β :=
    Hamiltonian.one_lt_gammaBar hcong.α hcong.β hα hβ
  have h_one_lt_γBarReal : (1 : ℝ) < hcong.α * (hcong.β + 1) / hcong.β := by
    rwa [Hamiltonian.gammaBar] at h_one_lt_γBarReal_g
  set γBarReal : ℝ := hcong.α * (hcong.β + 1) / hcong.β with hγBar_def
  set γBarReal' : ℝ := γBarReal / (γBarReal - 1) with hγBar'_def
  have h_γBar_minus_one_pos : (0 : ℝ) < γBarReal - 1 := by
    rw [hγBar_def]; rw [hγBar_def] at h_one_lt_γBarReal; linarith
  have h_one_lt_γBarReal' : (1 : ℝ) < γBarReal' := by
    rw [hγBar'_def, lt_div_iff₀ h_γBar_minus_one_pos, one_mul]
    rw [hγBar_def] at h_γBar_minus_one_pos ⊢; linarith
  have hγConj_real : Real.HolderConjugate γBarReal γBarReal' := by
    have := Real.HolderConjugate.conjExponent
      (p := γBarReal) (by rw [hγBar_def] at h_one_lt_γBarReal ⊢; exact h_one_lt_γBarReal)
    rwa [Real.conjExponent, ← hγBar'_def] at this
  haveI : ENNReal.HolderConjugate (ENNReal.ofReal γBarReal)
            (ENNReal.ofReal γBarReal') :=
    Real.HolderConjugate.ennrealOfReal hγConj_real
  haveI : Fact (1 ≤ ENNReal.ofReal γBarReal') :=
    ⟨by
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
      exact ENNReal.ofReal_le_ofReal h_one_lt_γBarReal'.le⟩
  -- `1 < ofReal _` for both exponents.
  have h_βBar_one_lt : (1 : ℝ≥0∞) < ENNReal.ofReal βBarReal := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num) |>.mpr h_one_lt_βBarReal
  have h_γBar_one_lt : (1 : ℝ≥0∞) < ENNReal.ofReal γBarReal := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
    refine ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num) |>.mpr ?_
    rw [hγBar_def] at h_one_lt_γBarReal ⊢; exact h_one_lt_γBarReal
  exact Periodic.lpSobolev_product_isReflexive (d := d)
    (ENNReal.ofReal βBarReal) (ENNReal.ofReal βBarReal')
    (ENNReal.ofReal γBarReal) (ENNReal.ofReal γBarReal')
    h_βBar_one_lt ENNReal.ofReal_ne_top h_γBar_one_lt ENNReal.ofReal_ne_top

/-- **Phase 7 producer for the upstream pack** (paper
`thm:weakAepsi.congestion`, line 1363). Assembles all seven fields of
`CongestionRegularizedSolutionUpstreamPack` from the paper hypotheses
`(hmon, hcong, hVmeas, hV, ε, hε)` plus the two exponent `Fact`
instances. This COMPLETES BB1: no free oracle, no re-assumption, no
`sorry`. `hmon` is load-bearing via `A_mono`. -/
noncomputable def congestionRegularizedSolutionUpstreamPack_of_paperHypotheses
    {V : (Fin d → ℝ) → ℝ}
    (hmon  : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV    : MemLpPer (d := d)
               (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (ε : ℝ) (hε : 0 < ε)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))] :
    CongestionRegularizedSolutionUpstreamPack
        (γBar := hcong.α * (hcong.β + 1) / hcong.β)
        (betaBar  := ENNReal.ofReal (hcong.β + 1))
        (betaBar' := ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (gammaBar := ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        V H DpH J ε
        (congestionXBanach d
           (ENNReal.ofReal (hcong.β + 1))
           (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))) :=
  -- `1 ≤ α * (1 + τ/β)` for `bridge_K_convex` (recipe from
  -- `congestionRegularizedSolutionAtEps_of_paperHypotheses`).
  have hτ_nn : (0 : ℝ) ≤ hcong.τ := hcong.hτ.1
  have hβ_pos : (0 : ℝ) < hcong.β := hcong.hβ
  have hα_gt_one : (1 : ℝ) < hcong.α := hcong.hα
  have hα_ge_one : (1 : ℝ) ≤ hcong.α := le_of_lt hα_gt_one
  have hαt_ge_one : (1 : ℝ) ≤ hcong.α * (1 + hcong.τ / hcong.β) := by
    have htdivβ_nn : (0 : ℝ) ≤ hcong.τ / hcong.β :=
      div_nonneg hτ_nn (le_of_lt hβ_pos)
    have hone_plus_ge : (1 : ℝ) ≤ 1 + hcong.τ / hcong.β := by linarith
    have hα_nn : (0 : ℝ) ≤ hcong.α := le_of_lt (lt_trans zero_lt_one hα_gt_one)
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ hcong.α * (1 + hcong.τ / hcong.β) :=
          mul_le_mul hα_ge_one hone_plus_ge (by norm_num) hα_nn
  { hReflexive := coercivity_congestionXBanach_isReflexive_of_hcong (d := d) hcong
    K :=
      congestionBanachK d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ
    bridge_K_convex :=
      convex_congestionBanachK d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ hτ_nn hαt_ge_one
    A := congestionAepsiOpK hmon hcong hVmeas hV ε
    A_mono :=
      congestionAepsiOpK_monotone_of_paperHypotheses
        hmon hcong hVmeas hV ε (le_of_lt hε)
    v₀ :=
      congestionCanonicalBasePoint d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
    A_coerc :=
      congestionAepsiOpK_coercive hmon hcong hVmeas hV ε hε
        (congestionCanonicalBasePoint d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))
        (congestionCanonicalBasePoint_mem_K d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
          hcong.α hcong.β hcong.τ)
        (congestionCanonicalBasePoint_m_ae d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))
        (congestionCanonicalBasePoint_u_ae d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))
        (fun i => congestionCanonicalBasePoint_Du_ae d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) i) }

/-- **Phase 7 T2 (pack-field-concretize, child A)**: a thin re-typing
wrapper around `congestionRegularizedSolutionUpstreamPack_of_paperHypotheses`
whose declared exponents use the project `gammaBar`/`betaBar`/`betaBar'`
notation (rather than the producer's unfolded `α*(β+1)/β`, `(β+1)/β`
forms). The two are *definitionally equal*
(`gammaBar α β = α*(β+1)/β`, `betaBar' β = (β+1)/β`,
`betaBar β = β+1`; see `Hamiltonian/Basic.lean`), so the body is the
producer verbatim and the wrapper type-checks by `rfl`.

This is the form that the `pack` field of
`CongestionRegularizedSequenceBuilderInputs` (Apriori.lean) is typed at
(`gammaBar h.α h.β`, `ENNReal.ofReal (h.β + 1)`,
`ENNReal.ofReal (gammaBar h.α h.β)`, `ENNReal.ofReal (betaBar' h.β)`).
Child B re-parameterizes that structure by `hcong`/`hmon`/`hVmeas` and
plugs this wrapper into the field, draining the `pack` oracle and making
`data.A = congestionAepsiOpK …` / `data.K = congestionBanachK …` hold by
`rfl`. Per the HARD anti-pack-swap rule this is draining via the EXISTING
internal producer, NOT a new oracle. -/
noncomputable def congestionSequenceBuilderPack
    {V : (Fin d → ℝ) → ℝ}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal (betaBar' hcong.β)) V)
    (ε : ℝ) (hε : 0 < ε)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (gammaBar hcong.α hcong.β))] :
    CongestionRegularizedSolutionUpstreamPack
        (γBar := gammaBar hcong.α hcong.β)
        (betaBar  := ENNReal.ofReal (hcong.β + 1))
        (gammaBar := ENNReal.ofReal (gammaBar hcong.α hcong.β))
        (betaBar' := ENNReal.ofReal (betaBar' hcong.β))
        V H DpH J ε
        (Periodic.LpPer (ENNReal.ofReal (hcong.β + 1)) d
          × Periodic.SobolevPerLp 1
              (ENNReal.ofReal (gammaBar hcong.α hcong.β)) d) :=
  -- The producer's required exponent `Fact` is on the unfolded form
  -- `α*(β+1)/β`; instance synthesis does not unfold `gammaBar`, so we
  -- supply it explicitly (it is `rfl`-defeq to the supplied instance).
  haveI : Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) :=
    ‹Fact (1 ≤ ENNReal.ofReal (gammaBar hcong.α hcong.β))›
  congestionRegularizedSolutionUpstreamPack_of_paperHypotheses
    hmon hcong hVmeas hV ε hε

/-- **Phase 7 T2 (pack-field-concretize, child B)**: the child-A wrapper
`congestionSequenceBuilderPack`, transported from its native
`hcong.α`/`hcong.β` exponents to the `h`-exponents
(`h : CongestionAprioriPowerData`) used by the per-ε `pack` slot of
`CongestionRegularizedSequenceBuilderInputs` (Apriori.lean).

The two exponent equalities `hpowα_eq : hcong.α = h.α` and
`hpowβ_eq : hcong.β = h.β` (which hold by `rfl` at the concrete Main
call site, where `h = pack3.hPowerCong` and that pack is built from the
same `hcong`) rewrite the wrapper's return type into the `h`-typed shape
the field demands. This is the term the consumer threads into
`congestionRegularizedSolutionAtEps_of_paperHypotheses`, draining the
former `pack` oracle: with it, `data.A = congestionAepsiOpK …` and
`data.K = congestionBanachK …` hold by `rfl` (the wrapper's `A`/`K`
fields are exactly those, and Phase 2's producer sets `data.A := pack.A`,
`data.K := pack.K`). -/
noncomputable def congestionSequenceBuilderPack_atPowerData
    {V : (Fin d → ℝ) → ℝ}
    (h : CongestionAprioriPowerData (d := d) H DpH)
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal (betaBar' hcong.β)) V)
    (hpowα_eq : hcong.α = h.α)
    (hpowβ_eq : hcong.β = h.β)
    (ε : ℝ) (hε : 0 < ε)
    [Fact (1 ≤ ENNReal.ofReal (h.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (gammaBar h.α h.β))] :
    CongestionRegularizedSolutionUpstreamPack
        (γBar := gammaBar h.α h.β)
        (betaBar  := ENNReal.ofReal (h.β + 1))
        (gammaBar := ENNReal.ofReal (gammaBar h.α h.β))
        (betaBar' := ENNReal.ofReal (betaBar' h.β))
        V H DpH J ε
        (Periodic.LpPer (ENNReal.ofReal (h.β + 1)) d
          × Periodic.SobolevPerLp 1 (ENNReal.ofReal (gammaBar h.α h.β)) d) := by
  -- Transport the wrapper's `hcong`-typed pack to the `h`-typed goal.
  -- A bare goal `rw [← hpowα_eq, ← hpowβ_eq]` produces an ill-typed motive
  -- because the `Lp` normed-group instances baked into the product type `X`
  -- depend on the rewritten exponents. We therefore *revert the
  -- exponent-dependent `Fact` instances first*, so the rewrite motive
  -- abstracts them too and stays type-correct; the two equalities then turn
  -- the whole `h`-typed goal into the wrapper's `hcong`-typed statement.
  revert ‹Fact (1 ≤ ENNReal.ofReal (h.β + 1))›
         ‹Fact (1 ≤ ENNReal.ofReal (gammaBar h.α h.β))›
  rw [← hpowα_eq, ← hpowβ_eq]
  intro _ _
  exact congestionSequenceBuilderPack hmon hcong hVmeas hV ε hε

/-- **Sanity `example`** feeding the upstream-pack producer into the
Phase 2 data producer `congestionRegularizedSolutionAtEps_of_paperHypotheses`,
yielding a `CongestionRegularizedSolutionData`. The two exponent
normalisations `1 ≤ betaBar` / `1 ≤ gammaBar` come from the `Fact`
instances via `Fact.out`. -/
noncomputable example
    {V : (Fin d → ℝ) → ℝ}
    (hmon  : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV    : MemLpPer (d := d)
               (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (ε : ℝ) (hε : 0 < ε)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))] :
    CongestionRegularizedSolutionData (d := d)
        (γBar := hcong.α * (hcong.β + 1) / hcong.β)
        (betaBar := ENNReal.ofReal (hcong.β + 1))
        (betaBarPrime := ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (gammaBar := ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        V H DpH J hcong.α hcong.β hcong.τ ε
        (congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))) :=
  congestionRegularizedSolutionAtEps_of_paperHypotheses
    (γBar := hcong.α * (hcong.β + 1) / hcong.β)
    (betaBar := ENNReal.ofReal (hcong.β + 1))
    (gammaBar := ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
    (betaBar' := ENNReal.ofReal ((hcong.β + 1) / hcong.β))
    V H DpH J ε hε hcong hV Fact.out Fact.out
    (congestionRegularizedSolutionUpstreamPack_of_paperHypotheses
      hmon hcong hVmeas hV ε hε)

/-! ### `rfl`-by-construction of the discharge premises `hAeq`/`hKeq`
(Phase 7 T2 `hcoeHJB_le` discharge prerequisite 1)

The `hcoeHJB_le` discharge needs `data.A = congestionAepsiOpK …` and
`data.K = congestionBanachK …` (where `data := dataAt ε hε` is the
Phase-2 producer applied at the builder-inputs wrapper). The Phase-2
producer sets `data.A := pack.A`, `data.K := pack.K`, and the wrapper
`congestionSequenceBuilderPack_atPowerData` transports its native
`hcong`-typed pack to the `h`-exponents via `revert/rw/intro`. That
`Eq.mpr` collapses *exactly when* the exponent equalities passed to the
wrapper are `rfl`.

The two clinching lemmas below witness this: when the wrapper is fed
`rfl rfl` (the concrete Main call-site situation, where
`h := hcong.toCongestionAprioriPowerData …` so `hcong.{α,β} = h.{α,β}`
definitionally — equivalently, when the wrapper is replaced by the native
`congestionSequenceBuilderPack`), both `.A` and `.K` of the resulting
Phase-2 `data` reduce to the bare `congestionAepsiOpK`/`congestionBanachK`
by `rfl`.

(The Phase-2 producer's `data.A := pack.A`, `data.K := pack.K` are
projection-`rfl`; the load-bearing content is that the wrapper's
`revert/rw/intro` `Eq.mpr` collapses under `rfl rfl`, which the
non-`rfl`-typed forms below establish definitionally.)

Discharge consumers should therefore (a) construct the builder-inputs
with `hpowα_eq := rfl`, `hpowβ_eq := rfl`, and `hcong := <the hcong that
built h>`, and (b) bring the `hcong`-typed `Fact` exponent instances into
scope (so the `congestionAepsiOpK`/`congestionBanachK` RHS typechecks) —
the iter-0940 blocker was the missing (b), which made even the *statement*
of `hAeq` fail to elaborate. -/

/-- **Discharge prerequisite, clinching form (`A`-side).** With the
exponent equalities `rfl` (the concrete Main call-site situation, where
`h := hcong.toCongestionAprioriPowerData …`), the Phase-2 `data.A`
reduces to the bare `congestionAepsiOpK …` typed at `hcong`'s exponents
by `rfl`. This is the equation the `hcoeHJB_le` discharge asserts. -/
theorem congestionSequenceBuilderData_A_eq_bare_of_rfl
    {V : (Fin d → ℝ) → ℝ}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal (betaBar' hcong.β)) V)
    (ε : ℝ) (hε : 0 < ε)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (gammaBar hcong.α hcong.β))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))] :
    (congestionRegularizedSolutionAtEps_of_paperHypotheses
      (γBar := gammaBar hcong.α hcong.β)
      (betaBar := ENNReal.ofReal (hcong.β + 1))
      (gammaBar := ENNReal.ofReal (gammaBar hcong.α hcong.β))
      (betaBar' := ENNReal.ofReal (betaBar' hcong.β))
      V H DpH J ε hε hcong hV
      (fact_one_le_ofReal_betaBar hcong.hβ).out
      (fact_one_le_ofReal_gammaBar hcong.hα hcong.hβ).out
      (congestionSequenceBuilderPack (J := J) hmon hcong hVmeas hV ε hε)).A
      = congestionAepsiOpK hmon hcong hVmeas hV ε := by
  rfl

/-- **Discharge prerequisite, clinching form (`K`-side).** Companion to
`…_A_eq_bare_of_rfl`: with the exponent equalities `rfl`, `data.K`
reduces to the bare `congestionBanachK …` by `rfl`. -/
theorem congestionSequenceBuilderData_K_eq_bare_of_rfl
    {V : (Fin d → ℝ) → ℝ}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal (betaBar' hcong.β)) V)
    (ε : ℝ) (hε : 0 < ε)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (gammaBar hcong.α hcong.β))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))] :
    (congestionRegularizedSolutionAtEps_of_paperHypotheses
      (γBar := gammaBar hcong.α hcong.β)
      (betaBar := ENNReal.ofReal (hcong.β + 1))
      (gammaBar := ENNReal.ofReal (gammaBar hcong.α hcong.β))
      (betaBar' := ENNReal.ofReal (betaBar' hcong.β))
      V H DpH J ε hε hcong hV
      (fact_one_le_ofReal_betaBar hcong.hβ).out
      (fact_one_le_ofReal_gammaBar hcong.hα hcong.hβ).out
      (congestionSequenceBuilderPack (J := J) hmon hcong hVmeas hV ε hε)).K
      = congestionBanachK d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
          hcong.α hcong.β hcong.τ := by
  rfl

/-! ### Cast-form discharge premises for the GENERAL transported case
(`hcoeHJB_le` discharge, child-E)

The `weak_is_strong_HJB_le_of_witnessData_powTransport_pos'` entry point
takes the operator/set identifications in the `cast`-transported shape
`A = cast hAty (congestionAepsiOpK …)`, `K = cast hKty (congestionBanachK …)`,
where the bare operators are typed at `hcong`'s exponents and `hAty`/`hKty`
transport the *type* to the abstract `αh`/`βh` exponents.

The two lemmas below produce exactly those equalities for the transported
upstream pack `congestionSequenceBuilderPack_atPowerData …` built at the
`αh`/`βh` exponents of a power-data record `h`, draining the abstract case
by `subst`-ing the exponent equalities (which collapses the wrapper's
`Eq.mpr` transport and the `cast`s simultaneously). At the consumer the
Phase-2 producer's `data.A := pack.A`, `data.K := pack.K` are
projection-`rfl`, so these pack-level equalities lift to the `data` level. -/

/-- **Operator-type transport equality (`A`-side).** The type equality
`hAty` consumed by `…_A_eq_cast_bare` and by the `_aesm`/`_powTransport`
entry points, produced from the exponent reconciliations `hpowα_eq`/
`hpowβ_eq` by destructuring `h` (so its exponents become free variables)
and `cases`-ing the equalities. This is the *only* sound way to build the
equality at a call site where the exponents are structure projections
(not free variables): `rw`/`▸` fail with a "motive is not type correct"
error because `StrongDual ℝ (congestionXBanach d a b)` carries
`Fact (1 ≤ a)`/`Fact (1 ≤ b)` instances that cannot be synthesized for an
abstracted exponent. -/
theorem congestionXBanach_op_ty_eq_of_powData
    (h : CongestionAprioriPowerData (d := d) H DpH)
    {α β : ℝ}
    (hpowα_eq : α = h.α)
    (hpowβ_eq : β = h.β)
    [Fact (1 ≤ ENNReal.ofReal (β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (α * (β + 1) / β))]
    [Fact (1 ≤ ENNReal.ofReal (h.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (h.α * (h.β + 1) / h.β))] :
    (congestionXBanach d (ENNReal.ofReal (β + 1))
        (ENNReal.ofReal (α * (β + 1) / β)) →
      StrongDual ℝ (congestionXBanach d (ENNReal.ofReal (β + 1))
        (ENNReal.ofReal (α * (β + 1) / β))))
      =
    (congestionXBanach d (ENNReal.ofReal (h.β + 1))
        (ENNReal.ofReal (h.α * (h.β + 1) / h.β)) →
      StrongDual ℝ (congestionXBanach d (ENNReal.ofReal (h.β + 1))
        (ENNReal.ofReal (h.α * (h.β + 1) / h.β)))) := by
  obtain ⟨_, _, αh, βh, _, _, _, _, _⟩ := h
  cases hpowα_eq
  cases hpowβ_eq
  rfl

/-- **Set-type transport equality (`K`-side).** Companion of
`congestionXBanach_op_ty_eq_of_powData` for the `K`/`Set`-side. -/
theorem congestionXBanach_set_ty_eq_of_powData
    (h : CongestionAprioriPowerData (d := d) H DpH)
    {α β : ℝ}
    (hpowα_eq : α = h.α)
    (hpowβ_eq : β = h.β)
    [Fact (1 ≤ ENNReal.ofReal (β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (α * (β + 1) / β))]
    [Fact (1 ≤ ENNReal.ofReal (h.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (h.α * (h.β + 1) / h.β))] :
    Set (congestionXBanach d (ENNReal.ofReal (β + 1))
        (ENNReal.ofReal (α * (β + 1) / β)))
      =
    Set (congestionXBanach d (ENNReal.ofReal (h.β + 1))
        (ENNReal.ofReal (h.α * (h.β + 1) / h.β))) := by
  obtain ⟨_, _, αh, βh, _, _, _, _, _⟩ := h
  cases hpowα_eq
  cases hpowβ_eq
  rfl

/-- **`A`-side cast equality, general transported case.** -/
theorem congestionSequenceBuilderPack_atPowerData_A_eq_cast_bare
    {V : (Fin d → ℝ) → ℝ}
    (h : CongestionAprioriPowerData (d := d) H DpH)
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal (betaBar' hcong.β)) V)
    (hpowα_eq : hcong.α = h.α)
    (hpowβ_eq : hcong.β = h.β)
    (ε : ℝ) (hε : 0 < ε)
    [Fact (1 ≤ ENNReal.ofReal (h.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (gammaBar h.α h.β))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    (hAty :
      (congestionXBanach d (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) →
        StrongDual ℝ (congestionXBanach d (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))))
        =
      (congestionXBanach d (ENNReal.ofReal (h.β + 1))
          (ENNReal.ofReal (gammaBar h.α h.β)) →
        StrongDual ℝ (congestionXBanach d (ENNReal.ofReal (h.β + 1))
          (ENNReal.ofReal (gammaBar h.α h.β))))) :
    (congestionSequenceBuilderPack_atPowerData h hmon hcong hVmeas hV
        hpowα_eq hpowβ_eq ε hε).A
      = cast hAty (congestionAepsiOpK hmon hcong hVmeas hV ε) := by
  -- Generalize the `h`-exponents to free variables so the abstract exponent
  -- equalities can be `subst`-ed; this collapses the wrapper's `Eq.mpr`
  -- transport and the `cast` simultaneously, reducing to the native `rfl`.
  -- The wrapper consumes its own copies of the equalities; generalize those
  -- proof terms so the `subst` of the exponent variables is unobstructed.
  obtain ⟨_, _, αh, βh, _, _, _, _, _⟩ := h
  cases hpowα_eq
  cases hpowβ_eq
  rfl

/-- **`K`-side cast equality, general transported case.** -/
theorem congestionSequenceBuilderPack_atPowerData_K_eq_cast_bare
    {V : (Fin d → ℝ) → ℝ}
    (h : CongestionAprioriPowerData (d := d) H DpH)
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal (betaBar' hcong.β)) V)
    (hpowα_eq : hcong.α = h.α)
    (hpowβ_eq : hcong.β = h.β)
    (ε : ℝ) (hε : 0 < ε)
    [Fact (1 ≤ ENNReal.ofReal (h.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (gammaBar h.α h.β))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    (hKty :
      Set (congestionXBanach d (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))
        =
      Set (congestionXBanach d (ENNReal.ofReal (h.β + 1))
          (ENNReal.ofReal (gammaBar h.α h.β)))) :
    (congestionSequenceBuilderPack_atPowerData h hmon hcong hVmeas hV
        hpowα_eq hpowβ_eq ε hε).K
      = cast hKty (congestionBanachK d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
          hcong.α hcong.β hcong.τ) := by
  obtain ⟨_, _, αh, βh, _, _, _, _, _⟩ := h
  cases hpowα_eq
  cases hpowβ_eq
  rfl

/-- **hKBridge discharge, general transported case (iter-0972).** Sobolev
membership of the value coercion at the chosen weak-VI witness of the
`_atPowerData`-transported Phase-2 data, derived internally from closure
membership.

This is the `_atPowerData` analogue of the `coeMemSob_u_atWitness_of_closure`
(Existence.lean) discharge: it replaces the former `hKBridge` field's sole
live conjunct. Like `…_K_eq_cast_bare`, the transported `data.K` equals
`congestionBanachK …` only across a cast, which obstructs a bare application
at the wrapper exponents; we `subst` the exponent equalities (after
destructuring `h`) to collapse the wrapper's `Eq.mpr` transport, reducing the
goal to the native-pack form where `data.K = congestionBanachK …` holds by
`rfl` and `coeMemSob_u_atWitness_of_closure` applies directly. -/
theorem congestionSequenceBuilderPack_atPowerData_coeMemSob_u
    {V : (Fin d → ℝ) → ℝ}
    (h : CongestionAprioriPowerData (d := d) H DpH)
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hVpack : MemLpPer (d := d) (ENNReal.ofReal (betaBar' hcong.β)) V)
    (hVdir : MemLpPer (d := d) (ENNReal.ofReal (betaBar' h.β)) V)
    (hpowα_eq : hcong.α = h.α)
    (hpowβ_eq : hcong.β = h.β)
    (ε : ℝ) (hε : 0 < ε)
    [Fact (1 ≤ ENNReal.ofReal (h.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (gammaBar h.α h.β))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))] :
    Periodic.MemSobolevPer (ENNReal.ofReal (gammaBar h.α h.β))
      (((congestionRegularizedSolutionAtEps_of_paperHypotheses
          (γBar := gammaBar h.α h.β)
          (betaBar := ENNReal.ofReal (h.β + 1))
          (gammaBar := ENNReal.ofReal (gammaBar h.α h.β))
          (betaBar' := ENNReal.ofReal (betaBar' h.β))
          V H DpH J ε hε hcong hVdir
          (fact_one_le_ofReal_betaBar h.hβ).out
          (fact_one_le_ofReal_gammaBar h.hα h.hβ).out
          (congestionSequenceBuilderPack_atPowerData h hmon hcong hVmeas hVpack
            hpowα_eq hpowβ_eq ε hε)).weakVI.choose.2.1
        : (Fin d → ℝ) → ℝ)) := by
  -- Collapse the wrapper transport by substituting the exponent equalities,
  -- reducing to the native-pack form (`data.K = congestionBanachK …` by `rfl`).
  obtain ⟨_, _, αh, βh, _, _, _, _, _⟩ := h
  cases hpowα_eq
  cases hpowβ_eq
  exact coeMemSob_u_atWitness_of_closure (d := d)
    (congestionRegularizedSolutionAtEps_of_paperHypotheses
      (γBar := gammaBar hcong.α hcong.β)
      (betaBar := ENNReal.ofReal (hcong.β + 1))
      (gammaBar := ENNReal.ofReal (gammaBar hcong.α hcong.β))
      (betaBar' := ENNReal.ofReal (betaBar' hcong.β))
      V H DpH J ε hε hcong hVdir
      (fact_one_le_ofReal_betaBar hcong.hβ).out
      (fact_one_le_ofReal_gammaBar hcong.hα hcong.hβ).out
      (congestionSequenceBuilderPack hmon hcong hVmeas hVpack ε hε))
    rfl

/-- **`hcoeWeak_Du` discharge, general transported case (iter-XXXX
child-hcoeWeak).** The periodic weak-derivative relation at the chosen weak-VI
witness of the `_atPowerData`-transported Phase-2 data, derived internally from
closure membership.

This is the `_atPowerData` analogue of `coeWeakDeriv_atWitness_of_closure`
(Existence.lean) — it replaces the former `hcoeWeak_Du` field. As with
`…_coeMemSob_u`, the transported `data.K` equals `congestionBanachK …` only
across a cast, which obstructs a bare application at the wrapper exponents; we
`subst` the exponent equalities (after destructuring `h`) to collapse the
wrapper's transport, reducing the goal to the native-pack form where
`data.K = congestionBanachK …` holds by `rfl` and
`coeWeakDeriv_atWitness_of_closure` applies directly. -/
theorem congestionSequenceBuilderPack_atPowerData_coeWeakDeriv
    {V : (Fin d → ℝ) → ℝ}
    (h : CongestionAprioriPowerData (d := d) H DpH)
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hVpack : MemLpPer (d := d) (ENNReal.ofReal (betaBar' hcong.β)) V)
    (hVdir : MemLpPer (d := d) (ENNReal.ofReal (betaBar' h.β)) V)
    (hpowα_eq : hcong.α = h.α)
    (hpowβ_eq : hcong.β = h.β)
    (ε : ℝ) (hε : 0 < ε)
    [Fact (1 ≤ ENNReal.ofReal (h.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (gammaBar h.α h.β))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))] :
    ∀ i, Periodic.HasWeakDerivPer (d := d) i
      (((congestionRegularizedSolutionAtEps_of_paperHypotheses
          (γBar := gammaBar h.α h.β)
          (betaBar := ENNReal.ofReal (h.β + 1))
          (gammaBar := ENNReal.ofReal (gammaBar h.α h.β))
          (betaBar' := ENNReal.ofReal (betaBar' h.β))
          V H DpH J ε hε hcong hVdir
          (fact_one_le_ofReal_betaBar h.hβ).out
          (fact_one_le_ofReal_gammaBar h.hα h.hβ).out
          (congestionSequenceBuilderPack_atPowerData h hmon hcong hVmeas hVpack
            hpowα_eq hpowβ_eq ε hε)).weakVI.choose.2.1
        : (Fin d → ℝ) → ℝ))
      (((congestionRegularizedSolutionAtEps_of_paperHypotheses
          (γBar := gammaBar h.α h.β)
          (betaBar := ENNReal.ofReal (h.β + 1))
          (gammaBar := ENNReal.ofReal (gammaBar h.α h.β))
          (betaBar' := ENNReal.ofReal (betaBar' h.β))
          V H DpH J ε hε hcong hVdir
          (fact_one_le_ofReal_betaBar h.hβ).out
          (fact_one_le_ofReal_gammaBar h.hα h.hβ).out
          (congestionSequenceBuilderPack_atPowerData h hmon hcong hVmeas hVpack
            hpowα_eq hpowβ_eq ε hε)).weakVI.choose.2.2 i
        : (Fin d → ℝ) → ℝ)) := by
  -- Collapse the wrapper transport by substituting the exponent equalities,
  -- reducing to the native-pack form (`data.K = congestionBanachK …` by `rfl`).
  obtain ⟨_, _, αh, βh, _, _, _, _, _⟩ := h
  cases hpowα_eq
  cases hpowβ_eq
  exact coeWeakDeriv_atWitness_of_closure (d := d)
    (congestionRegularizedSolutionAtEps_of_paperHypotheses
      (γBar := gammaBar hcong.α hcong.β)
      (betaBar := ENNReal.ofReal (hcong.β + 1))
      (gammaBar := ENNReal.ofReal (gammaBar hcong.α hcong.β))
      (betaBar' := ENNReal.ofReal (betaBar' hcong.β))
      V H DpH J ε hε hcong hVdir
      (fact_one_le_ofReal_betaBar hcong.hβ).out
      (fact_one_le_ofReal_gammaBar hcong.hα hcong.hβ).out
      (congestionSequenceBuilderPack hmon hcong hVmeas hVpack ε hε))
    rfl

/-- **T2 nonneg-track (Phase-3c) — `coeM_nonneg` discharge, general
transported case.** A.e. NONnegativity of the density coercion at the chosen
weak-VI witness of the `_atPowerData`-transported Phase-2 data, derived
internally from nonneg-cone closure membership.

This is the `_atPowerData` analogue of `coeM_nonneg_atWitness_of_closure`
(Existence.lean), parallel to `…_coeMemSob_u` / `…_coeWeakDeriv`. As with those
wrappers, the transported `data.K` equals `congestionBanachK …` only across a
cast, which obstructs a bare application of `coeM_nonneg_atWitness_of_closure`
at the wrapper exponents; we `subst` the exponent equalities (after
destructuring `h`) to collapse the wrapper's `Eq.mpr` transport, reducing the
goal to the native-pack form where `data.K = congestionBanachK …` holds by
`rfl` and `coeM_nonneg_atWitness_of_closure` applies directly. This supplies
the `hcoeNonneg_m` parameter of `BanachBareDecomposition.ofLpProductGap_nonneg`
in the nonneg producer — NO `0 < m_ε` rider. -/
theorem congestionSequenceBuilderPack_atPowerData_coeM_nonneg
    {V : (Fin d → ℝ) → ℝ}
    (h : CongestionAprioriPowerData (d := d) H DpH)
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hVpack : MemLpPer (d := d) (ENNReal.ofReal (betaBar' hcong.β)) V)
    (hVdir : MemLpPer (d := d) (ENNReal.ofReal (betaBar' h.β)) V)
    (hpowα_eq : hcong.α = h.α)
    (hpowβ_eq : hcong.β = h.β)
    (ε : ℝ) (hε : 0 < ε)
    [Fact (1 ≤ ENNReal.ofReal (h.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (gammaBar h.α h.β))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))] :
    0 ≤ᵐ[Measure.restrict volume (UnitCube d)]
      (((congestionRegularizedSolutionAtEps_of_paperHypotheses
          (γBar := gammaBar h.α h.β)
          (betaBar := ENNReal.ofReal (h.β + 1))
          (gammaBar := ENNReal.ofReal (gammaBar h.α h.β))
          (betaBar' := ENNReal.ofReal (betaBar' h.β))
          V H DpH J ε hε hcong hVdir
          (fact_one_le_ofReal_betaBar h.hβ).out
          (fact_one_le_ofReal_gammaBar h.hα h.hβ).out
          (congestionSequenceBuilderPack_atPowerData h hmon hcong hVmeas hVpack
            hpowα_eq hpowβ_eq ε hε)).weakVI.choose.1
        : (Fin d → ℝ) → ℝ)) := by
  -- Collapse the wrapper transport by substituting the exponent equalities,
  -- reducing to the native-pack form (`data.K = congestionBanachK …` by `rfl`).
  obtain ⟨_, _, αh, βh, _, _, _, _, _⟩ := h
  cases hpowα_eq
  cases hpowβ_eq
  exact coeM_nonneg_atWitness_of_closure (d := d)
    (congestionRegularizedSolutionAtEps_of_paperHypotheses
      (γBar := gammaBar hcong.α hcong.β)
      (betaBar := ENNReal.ofReal (hcong.β + 1))
      (gammaBar := ENNReal.ofReal (gammaBar hcong.α hcong.β))
      (betaBar' := ENNReal.ofReal (betaBar' hcong.β))
      V H DpH J ε hε hcong hVdir
      (fact_one_le_ofReal_betaBar hcong.hβ).out
      (fact_one_le_ofReal_gammaBar hcong.hα hcong.hβ).out
      (congestionSequenceBuilderPack hmon hcong hVmeas hVpack ε hε))
    rfl

/-! ### BB2 `_atPowerData` wrappers (iter-XXXX child-BB2): `gap`,
`coeEpsNN`, `coeEpsTerms_int`

These three wrappers transport the unconditional BB2 producers
(`congestionRegularizedBuilderInputs_gap` / `_hcoeEpsNN` /
`_hEpsTerms_int` in Existence.lean) to the `h`-exponents used by the
`CongestionRegularizedSequenceBuilderInputs` bundle. Unlike the
`_coeMemSob_u` / `_coeWeakDeriv` wrappers, NO closure membership and NO
data-record dependence is needed — the gap producer takes the exponents
as *implicit* arguments, so the wrappers simply instantiate them at
`h.β + 1` (β̄) and `gammaBar h.α h.β` (γ̄), with `γBarReal := gammaBar
h.α h.β`. -/

/-- **BB2 `gap` `_atPowerData` wrapper.** The BB4a-i gap bundle at the
`h`-exponents, from the unconditional producer
`congestionRegularizedBuilderInputs_gap`. No exponent transport is
needed: the producer takes `betaBar`/`gammaBar` as implicits and they
unify directly with the `h`-exponents. -/
noncomputable def congestionSequenceBuilderPack_atPowerData_gap
    {V : (Fin d → ℝ) → ℝ}
    (h : CongestionAprioriPowerData (d := d) H DpH)
    [Fact (1 ≤ ENNReal.ofReal (h.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (gammaBar h.α h.β))]
    (ε : ℝ) :
    LpProductBareGap (d := d)
      (ENNReal.ofReal (h.β + 1))
      (ENNReal.ofReal (gammaBar h.α h.β))
      V H DpH ε :=
  congestionRegularizedBuilderInputs_gap (d := d)
    (betaBar := ENNReal.ofReal (h.β + 1))
    (gammaBar := ENNReal.ofReal (gammaBar h.α h.β))
    (V := V) (H := H) (DpH := DpH) ε (gammaBar h.α h.β)

/-- **BB2 `coeEpsNN` `_atPowerData` wrapper.** A.e. nonnegativity of the
gap's `coe_epsTerms` at any pair `z`, from the unconditional producer
`congestionRegularizedBuilderInputs_hcoeEpsNN`. -/
theorem congestionSequenceBuilderPack_atPowerData_coeEpsNN
    {V : (Fin d → ℝ) → ℝ}
    (h : CongestionAprioriPowerData (d := d) H DpH)
    [Fact (1 ≤ ENNReal.ofReal (h.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (gammaBar h.α h.β))]
    {ε : ℝ} (hε : 0 < ε)
    (z : Periodic.LpPer (ENNReal.ofReal (h.β + 1)) d
          × Periodic.SobolevPerLp 1 (ENNReal.ofReal (gammaBar h.α h.β)) d) :
    ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
      0 ≤ (congestionSequenceBuilderPack_atPowerData_gap (d := d)
            (V := V) h ε).coe_epsTerms z x :=
  congestionRegularizedBuilderInputs_hcoeEpsNN (d := d)
    (betaBar := ENNReal.ofReal (h.β + 1))
    (gammaBar := ENNReal.ofReal (gammaBar h.α h.β))
    (V := V) (H := H) (DpH := DpH) hε (gammaBar h.α h.β) z

/-- **BB2 `coeEpsTerms_int` `_atPowerData` wrapper.** Integrability of
the gap's `project_epsTerms` at any pair `z`, from the unconditional
producer `congestionRegularizedBuilderInputs_hEpsTerms_int`. The
`1 ≤ γBarReal` premise is `(one_lt_gammaBar …).le`; the exponent
equality `gammaBar = ENNReal.ofReal γBarReal` is `rfl`. -/
theorem congestionSequenceBuilderPack_atPowerData_coeEpsTerms_int
    {V : (Fin d → ℝ) → ℝ}
    (h : CongestionAprioriPowerData (d := d) H DpH)
    [Fact (1 ≤ ENNReal.ofReal (h.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (gammaBar h.α h.β))]
    (ε : ℝ)
    (z : Periodic.LpPer (ENNReal.ofReal (h.β + 1)) d
          × Periodic.SobolevPerLp 1 (ENNReal.ofReal (gammaBar h.α h.β)) d) :
    MeasureTheory.Integrable
      ((congestionSequenceBuilderPack_atPowerData_gap (d := d)
          (V := V) h ε).project_epsTerms z)
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
  congestionRegularizedBuilderInputs_hEpsTerms_int (d := d)
    (betaBar := ENNReal.ofReal (h.β + 1))
    (gammaBar := ENNReal.ofReal (gammaBar h.α h.β))
    (V := V) (H := H) (DpH := DpH) ε
    (one_lt_gammaBar h.α h.β h.hα h.hβ).le rfl z

/-- **VIid-5c child E1b — the `heps_int` cert at the `_atPowerData` gap.**
Integrability of the gap's `coe_epsTerms` (the Lp-quotient coercion of the
regularisation residual) at any pair `z`. This is the `coe_epsTerms`
counterpart of `congestionSequenceBuilderPack_atPowerData_coeEpsTerms_int`
(which produces the `project_epsTerms` representative): transfer
integrability across the gap's built-in a.e. equality
`project_epsTerms z =ᵐ coe_epsTerms z` (`LpProductBareGap.ae_epsTerms`).

This is the cert consumed by `congestionSequenceBuilderPack_atPowerData_coeVI_identity`
that the circular `CongestionBareRepresentatives`-based producers could not
supply: it depends only on the concrete gap structure, not on the
`hVI_identity_coe` field. -/
theorem congestionSequenceBuilderPack_atPowerData_coe_epsTerms_int
    {V : (Fin d → ℝ) → ℝ}
    (h : CongestionAprioriPowerData (d := d) H DpH)
    [Fact (1 ≤ ENNReal.ofReal (h.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (gammaBar h.α h.β))]
    (ε : ℝ)
    (z : Periodic.LpPer (ENNReal.ofReal (h.β + 1)) d
          × Periodic.SobolevPerLp 1 (ENNReal.ofReal (gammaBar h.α h.β)) d) :
    MeasureTheory.Integrable
      ((congestionSequenceBuilderPack_atPowerData_gap (d := d)
          (V := V) h ε).coe_epsTerms z)
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
  (congestionSequenceBuilderPack_atPowerData_coeEpsTerms_int (d := d)
    (V := V) h ε z).congr
    ((congestionSequenceBuilderPack_atPowerData_gap (d := d) (V := V) h ε).ae_epsTerms z)

/-- **VIid-5c child C — `coeVI_identity` `_atPowerData` wrapper.** The paper
`eq:identity-congestion` integral identity at the chosen weak-VI witness of the
`_atPowerData`-transported Phase-2 data, produced from the witness transport-at-`u`
identity (`hTransport`), the `eq:congest.HJ0` mass identity (`hHJ0`), and the six
per-summand integrability certificates.

This is the `_atPowerData` analogue of `coeVI_identity_atWitness_of_closure`
(Existence.lean). As with `…_coeMemSob_u` / `…_coeWeakDeriv`, the transported
data only matches the native-pack form across a cast; we `subst` the exponent
equalities (after destructuring `h`) to collapse the wrapper transport, reducing
to the native-pack data on which `coeVI_identity_atWitness_of_closure` applies
directly. The analytic inputs are threaded through unchanged: they are phrased
against the wrapper's data record, and the `subst` carries them to the native
form. -/
theorem congestionSequenceBuilderPack_atPowerData_coeVI_identity
    {V : (Fin d → ℝ) → ℝ}
    (h : CongestionAprioriPowerData (d := d) H DpH)
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hVpack : MemLpPer (d := d) (ENNReal.ofReal (betaBar' hcong.β)) V)
    (hVdir : MemLpPer (d := d) (ENNReal.ofReal (betaBar' h.β)) V)
    (hpowα_eq : hcong.α = h.α)
    (hpowβ_eq : hcong.β = h.β)
    (ε : ℝ) (hε : 0 < ε)
    [Fact (1 ≤ ENNReal.ofReal (h.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (gammaBar h.α h.β))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    -- per-summand integrability of child A's pieces, at the witness data
    (hu_int : MeasureTheory.Integrable
      ((congestionRegularizedSolutionAtEps_of_paperHypotheses (γBar := gammaBar h.α h.β) (betaBar := ENNReal.ofReal (h.β + 1)) (gammaBar := ENNReal.ofReal (gammaBar h.α h.β)) (betaBar' := ENNReal.ofReal (betaBar' h.β)) V H DpH J ε hε hcong hVdir (fact_one_le_ofReal_betaBar h.hβ).out (fact_one_le_ofReal_gammaBar h.hα h.hβ).out (congestionSequenceBuilderPack_atPowerData h hmon hcong hVmeas hVpack hpowα_eq hpowβ_eq ε hε)).weakVI.choose.2.1 : (Fin d → ℝ) → ℝ)
      (volume.restrict (UnitCube d)))
    (hmFlux_int : MeasureTheory.Integrable
      (fun x => (((congestionRegularizedSolutionAtEps_of_paperHypotheses (γBar := gammaBar h.α h.β) (betaBar := ENNReal.ofReal (h.β + 1)) (gammaBar := ENNReal.ofReal (gammaBar h.α h.β)) (betaBar' := ENNReal.ofReal (betaBar' h.β)) V H DpH J ε hε hcong hVdir (fact_one_le_ofReal_betaBar h.hβ).out (fact_one_le_ofReal_gammaBar h.hα h.hβ).out (congestionSequenceBuilderPack_atPowerData h hmon hcong hVmeas hVpack hpowα_eq hpowβ_eq ε hε)).weakVI.choose.1 : (Fin d → ℝ) → ℝ) x) * ((DpH x (fun i => (((congestionRegularizedSolutionAtEps_of_paperHypotheses (γBar := gammaBar h.α h.β) (betaBar := ENNReal.ofReal (h.β + 1)) (gammaBar := ENNReal.ofReal (gammaBar h.α h.β)) (betaBar' := ENNReal.ofReal (betaBar' h.β)) V H DpH J ε hε hcong hVdir (fact_one_le_ofReal_betaBar h.hβ).out (fact_one_le_ofReal_gammaBar h.hα h.hβ).out (congestionSequenceBuilderPack_atPowerData h hmon hcong hVmeas hVpack hpowα_eq hpowβ_eq ε hε)).weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)) (((congestionRegularizedSolutionAtEps_of_paperHypotheses (γBar := gammaBar h.α h.β) (betaBar := ENNReal.ofReal (h.β + 1)) (gammaBar := ENNReal.ofReal (gammaBar h.α h.β)) (betaBar' := ENNReal.ofReal (betaBar' h.β)) V H DpH J ε hε hcong hVdir (fact_one_le_ofReal_betaBar h.hβ).out (fact_one_le_ofReal_gammaBar h.hα h.hβ).out (congestionSequenceBuilderPack_atPowerData h hmon hcong hVmeas hVpack hpowα_eq hpowβ_eq ε hε)).weakVI.choose.1 : (Fin d → ℝ) → ℝ) x)) ⬝ (fun i => (((congestionRegularizedSolutionAtEps_of_paperHypotheses (γBar := gammaBar h.α h.β) (betaBar := ENNReal.ofReal (h.β + 1)) (gammaBar := ENNReal.ofReal (gammaBar h.α h.β)) (betaBar' := ENNReal.ofReal (betaBar' h.β)) V H DpH J ε hε hcong hVdir (fact_one_le_ofReal_betaBar h.hβ).out (fact_one_le_ofReal_gammaBar h.hα h.hβ).out (congestionSequenceBuilderPack_atPowerData h hmon hcong hVmeas hVpack hpowα_eq hpowβ_eq ε hε)).weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x))))
      (volume.restrict (UnitCube d)))
    (hVm_int : MeasureTheory.Integrable
      (fun x => V x * (((congestionRegularizedSolutionAtEps_of_paperHypotheses (γBar := gammaBar h.α h.β) (betaBar := ENNReal.ofReal (h.β + 1)) (gammaBar := ENNReal.ofReal (gammaBar h.α h.β)) (betaBar' := ENNReal.ofReal (betaBar' h.β)) V H DpH J ε hε hcong hVdir (fact_one_le_ofReal_betaBar h.hβ).out (fact_one_le_ofReal_gammaBar h.hα h.hβ).out (congestionSequenceBuilderPack_atPowerData h hmon hcong hVmeas hVpack hpowα_eq hpowβ_eq ε hε)).weakVI.choose.1 : (Fin d → ℝ) → ℝ) x))
      (volume.restrict (UnitCube d)))
    (heps_int : MeasureTheory.Integrable
      ((congestionSequenceBuilderPack_atPowerData_gap (d := d) (V := V) h ε).coe_epsTerms (congestionRegularizedSolutionAtEps_of_paperHypotheses (γBar := gammaBar h.α h.β) (betaBar := ENNReal.ofReal (h.β + 1)) (gammaBar := ENNReal.ofReal (gammaBar h.α h.β)) (betaBar' := ENNReal.ofReal (betaBar' h.β)) V H DpH J ε hε hcong hVdir (fact_one_le_ofReal_betaBar h.hβ).out (fact_one_le_ofReal_gammaBar h.hα h.hβ).out (congestionSequenceBuilderPack_atPowerData h hmon hcong hVmeas hVpack hpowα_eq hpowβ_eq ε hε)).weakVI.choose)
      (volume.restrict (UnitCube d)))
    (hmH_int : MeasureTheory.Integrable
      (fun x => (((congestionRegularizedSolutionAtEps_of_paperHypotheses (γBar := gammaBar h.α h.β) (betaBar := ENNReal.ofReal (h.β + 1)) (gammaBar := ENNReal.ofReal (gammaBar h.α h.β)) (betaBar' := ENNReal.ofReal (betaBar' h.β)) V H DpH J ε hε hcong hVdir (fact_one_le_ofReal_betaBar h.hβ).out (fact_one_le_ofReal_gammaBar h.hα h.hβ).out (congestionSequenceBuilderPack_atPowerData h hmon hcong hVmeas hVpack hpowα_eq hpowβ_eq ε hε)).weakVI.choose.1 : (Fin d → ℝ) → ℝ) x) * (H x (fun i => (((congestionRegularizedSolutionAtEps_of_paperHypotheses (γBar := gammaBar h.α h.β) (betaBar := ENNReal.ofReal (h.β + 1)) (gammaBar := ENNReal.ofReal (gammaBar h.α h.β)) (betaBar' := ENNReal.ofReal (betaBar' h.β)) V H DpH J ε hε hcong hVdir (fact_one_le_ofReal_betaBar h.hβ).out (fact_one_le_ofReal_gammaBar h.hα h.hβ).out (congestionSequenceBuilderPack_atPowerData h hmon hcong hVmeas hVpack hpowα_eq hpowβ_eq ε hε)).weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)) (((congestionRegularizedSolutionAtEps_of_paperHypotheses (γBar := gammaBar h.α h.β) (betaBar := ENNReal.ofReal (h.β + 1)) (gammaBar := ENNReal.ofReal (gammaBar h.α h.β)) (betaBar' := ENNReal.ofReal (betaBar' h.β)) V H DpH J ε hε hcong hVdir (fact_one_le_ofReal_betaBar h.hβ).out (fact_one_le_ofReal_gammaBar h.hα h.hβ).out (congestionSequenceBuilderPack_atPowerData h hmon hcong hVmeas hVpack hpowα_eq hpowβ_eq ε hε)).weakVI.choose.1 : (Fin d → ℝ) → ℝ) x)))
      (volume.restrict (UnitCube d)))
    (hmu_int : MeasureTheory.Integrable
      (fun x => (((congestionRegularizedSolutionAtEps_of_paperHypotheses (γBar := gammaBar h.α h.β) (betaBar := ENNReal.ofReal (h.β + 1)) (gammaBar := ENNReal.ofReal (gammaBar h.α h.β)) (betaBar' := ENNReal.ofReal (betaBar' h.β)) V H DpH J ε hε hcong hVdir (fact_one_le_ofReal_betaBar h.hβ).out (fact_one_le_ofReal_gammaBar h.hα h.hβ).out (congestionSequenceBuilderPack_atPowerData h hmon hcong hVmeas hVpack hpowα_eq hpowβ_eq ε hε)).weakVI.choose.1 : (Fin d → ℝ) → ℝ) x) * (((congestionRegularizedSolutionAtEps_of_paperHypotheses (γBar := gammaBar h.α h.β) (betaBar := ENNReal.ofReal (h.β + 1)) (gammaBar := ENNReal.ofReal (gammaBar h.α h.β)) (betaBar' := ENNReal.ofReal (betaBar' h.β)) V H DpH J ε hε hcong hVdir (fact_one_le_ofReal_betaBar h.hβ).out (fact_one_le_ofReal_gammaBar h.hα h.hβ).out (congestionSequenceBuilderPack_atPowerData h hmon hcong hVmeas hVpack hpowα_eq hpowβ_eq ε hε)).weakVI.choose.2.1 : (Fin d → ℝ) → ℝ) x))
      (volume.restrict (UnitCube d)))
    (hTransport :
      ∫ x in UnitCube d, (((((congestionRegularizedSolutionAtEps_of_paperHypotheses (γBar := gammaBar h.α h.β) (betaBar := ENNReal.ofReal (h.β + 1)) (gammaBar := ENNReal.ofReal (gammaBar h.α h.β)) (betaBar' := ENNReal.ofReal (betaBar' h.β)) V H DpH J ε hε hcong hVdir (fact_one_le_ofReal_betaBar h.hβ).out (fact_one_le_ofReal_gammaBar h.hα h.hβ).out (congestionSequenceBuilderPack_atPowerData h hmon hcong hVmeas hVpack hpowα_eq hpowβ_eq ε hε)).weakVI.choose.1 : (Fin d → ℝ) → ℝ) x) - 1) * (((congestionRegularizedSolutionAtEps_of_paperHypotheses (γBar := gammaBar h.α h.β) (betaBar := ENNReal.ofReal (h.β + 1)) (gammaBar := ENNReal.ofReal (gammaBar h.α h.β)) (betaBar' := ENNReal.ofReal (betaBar' h.β)) V H DpH J ε hε hcong hVdir (fact_one_le_ofReal_betaBar h.hβ).out (fact_one_le_ofReal_gammaBar h.hα h.hβ).out (congestionSequenceBuilderPack_atPowerData h hmon hcong hVmeas hVpack hpowα_eq hpowβ_eq ε hε)).weakVI.choose.2.1 : (Fin d → ℝ) → ℝ) x) + (((congestionRegularizedSolutionAtEps_of_paperHypotheses (γBar := gammaBar h.α h.β) (betaBar := ENNReal.ofReal (h.β + 1)) (gammaBar := ENNReal.ofReal (gammaBar h.α h.β)) (betaBar' := ENNReal.ofReal (betaBar' h.β)) V H DpH J ε hε hcong hVdir (fact_one_le_ofReal_betaBar h.hβ).out (fact_one_le_ofReal_gammaBar h.hα h.hβ).out (congestionSequenceBuilderPack_atPowerData h hmon hcong hVmeas hVpack hpowα_eq hpowβ_eq ε hε)).weakVI.choose.1 : (Fin d → ℝ) → ℝ) x) * ((DpH x (fun i => (((congestionRegularizedSolutionAtEps_of_paperHypotheses (γBar := gammaBar h.α h.β) (betaBar := ENNReal.ofReal (h.β + 1)) (gammaBar := ENNReal.ofReal (gammaBar h.α h.β)) (betaBar' := ENNReal.ofReal (betaBar' h.β)) V H DpH J ε hε hcong hVdir (fact_one_le_ofReal_betaBar h.hβ).out (fact_one_le_ofReal_gammaBar h.hα h.hβ).out (congestionSequenceBuilderPack_atPowerData h hmon hcong hVmeas hVpack hpowα_eq hpowβ_eq ε hε)).weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)) (((congestionRegularizedSolutionAtEps_of_paperHypotheses (γBar := gammaBar h.α h.β) (betaBar := ENNReal.ofReal (h.β + 1)) (gammaBar := ENNReal.ofReal (gammaBar h.α h.β)) (betaBar' := ENNReal.ofReal (betaBar' h.β)) V H DpH J ε hε hcong hVdir (fact_one_le_ofReal_betaBar h.hβ).out (fact_one_le_ofReal_gammaBar h.hα h.hβ).out (congestionSequenceBuilderPack_atPowerData h hmon hcong hVmeas hVpack hpowα_eq hpowβ_eq ε hε)).weakVI.choose.1 : (Fin d → ℝ) → ℝ) x)) ⬝ (fun i => (((congestionRegularizedSolutionAtEps_of_paperHypotheses (γBar := gammaBar h.α h.β) (betaBar := ENNReal.ofReal (h.β + 1)) (gammaBar := ENNReal.ofReal (gammaBar h.α h.β)) (betaBar' := ENNReal.ofReal (betaBar' h.β)) V H DpH J ε hε hcong hVdir (fact_one_le_ofReal_betaBar h.hβ).out (fact_one_le_ofReal_gammaBar h.hα h.hβ).out (congestionSequenceBuilderPack_atPowerData h hmon hcong hVmeas hVpack hpowα_eq hpowβ_eq ε hε)).weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)))) ∂(volume : MeasureTheory.Measure (Fin d → ℝ))
        + ∫ x in UnitCube d, (((congestionSequenceBuilderPack_atPowerData_gap (d := d) (V := V) h ε).coe_epsTerms (congestionRegularizedSolutionAtEps_of_paperHypotheses (γBar := gammaBar h.α h.β) (betaBar := ENNReal.ofReal (h.β + 1)) (gammaBar := ENNReal.ofReal (gammaBar h.α h.β)) (betaBar' := ENNReal.ofReal (betaBar' h.β)) V H DpH J ε hε hcong hVdir (fact_one_le_ofReal_betaBar h.hβ).out (fact_one_le_ofReal_gammaBar h.hα h.hβ).out (congestionSequenceBuilderPack_atPowerData h hmon hcong hVmeas hVpack hpowα_eq hpowβ_eq ε hε)).weakVI.choose) x) ∂(volume : MeasureTheory.Measure (Fin d → ℝ)) = 0)
    (hHJ0 :
      ∫ x in UnitCube d, ((((congestionRegularizedSolutionAtEps_of_paperHypotheses (γBar := gammaBar h.α h.β) (betaBar := ENNReal.ofReal (h.β + 1)) (gammaBar := ENNReal.ofReal (gammaBar h.α h.β)) (betaBar' := ENNReal.ofReal (betaBar' h.β)) V H DpH J ε hε hcong hVdir (fact_one_le_ofReal_betaBar h.hβ).out (fact_one_le_ofReal_gammaBar h.hα h.hβ).out (congestionSequenceBuilderPack_atPowerData h hmon hcong hVmeas hVpack hpowα_eq hpowβ_eq ε hε)).weakVI.choose.1 : (Fin d → ℝ) → ℝ) x) * ((((congestionRegularizedSolutionAtEps_of_paperHypotheses (γBar := gammaBar h.α h.β) (betaBar := ENNReal.ofReal (h.β + 1)) (gammaBar := ENNReal.ofReal (gammaBar h.α h.β)) (betaBar' := ENNReal.ofReal (betaBar' h.β)) V H DpH J ε hε hcong hVdir (fact_one_le_ofReal_betaBar h.hβ).out (fact_one_le_ofReal_gammaBar h.hα h.hβ).out (congestionSequenceBuilderPack_atPowerData h hmon hcong hVmeas hVpack hpowα_eq hpowβ_eq ε hε)).weakVI.choose.2.1 : (Fin d → ℝ) → ℝ) x) + (H x (fun i => (((congestionRegularizedSolutionAtEps_of_paperHypotheses (γBar := gammaBar h.α h.β) (betaBar := ENNReal.ofReal (h.β + 1)) (gammaBar := ENNReal.ofReal (gammaBar h.α h.β)) (betaBar' := ENNReal.ofReal (betaBar' h.β)) V H DpH J ε hε hcong hVdir (fact_one_le_ofReal_betaBar h.hβ).out (fact_one_le_ofReal_gammaBar h.hα h.hβ).out (congestionSequenceBuilderPack_atPowerData h hmon hcong hVmeas hVpack hpowα_eq hpowβ_eq ε hε)).weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)) (((congestionRegularizedSolutionAtEps_of_paperHypotheses (γBar := gammaBar h.α h.β) (betaBar := ENNReal.ofReal (h.β + 1)) (gammaBar := ENNReal.ofReal (gammaBar h.α h.β)) (betaBar' := ENNReal.ofReal (betaBar' h.β)) V H DpH J ε hε hcong hVdir (fact_one_le_ofReal_betaBar h.hβ).out (fact_one_le_ofReal_gammaBar h.hα h.hβ).out (congestionSequenceBuilderPack_atPowerData h hmon hcong hVmeas hVpack hpowα_eq hpowβ_eq ε hε)).weakVI.choose.1 : (Fin d → ℝ) → ℝ) x)) - V x)) ∂(volume : MeasureTheory.Measure (Fin d → ℝ)) = 0) :
    ∫ x in UnitCube d, (((congestionRegularizedSolutionAtEps_of_paperHypotheses (γBar := gammaBar h.α h.β) (betaBar := ENNReal.ofReal (h.β + 1)) (gammaBar := ENNReal.ofReal (gammaBar h.α h.β)) (betaBar' := ENNReal.ofReal (betaBar' h.β)) V H DpH J ε hε hcong hVdir (fact_one_le_ofReal_betaBar h.hβ).out (fact_one_le_ofReal_gammaBar h.hα h.hβ).out (congestionSequenceBuilderPack_atPowerData h hmon hcong hVmeas hVpack hpowα_eq hpowβ_eq ε hε)).weakVI.choose.2.1 : (Fin d → ℝ) → ℝ) x) ∂(volume : MeasureTheory.Measure (Fin d → ℝ))
      = ∫ x in UnitCube d, ((((congestionRegularizedSolutionAtEps_of_paperHypotheses (γBar := gammaBar h.α h.β) (betaBar := ENNReal.ofReal (h.β + 1)) (gammaBar := ENNReal.ofReal (gammaBar h.α h.β)) (betaBar' := ENNReal.ofReal (betaBar' h.β)) V H DpH J ε hε hcong hVdir (fact_one_le_ofReal_betaBar h.hβ).out (fact_one_le_ofReal_gammaBar h.hα h.hβ).out (congestionSequenceBuilderPack_atPowerData h hmon hcong hVmeas hVpack hpowα_eq hpowβ_eq ε hε)).weakVI.choose.1 : (Fin d → ℝ) → ℝ) x) * (-(H x (fun i => (((congestionRegularizedSolutionAtEps_of_paperHypotheses (γBar := gammaBar h.α h.β) (betaBar := ENNReal.ofReal (h.β + 1)) (gammaBar := ENNReal.ofReal (gammaBar h.α h.β)) (betaBar' := ENNReal.ofReal (betaBar' h.β)) V H DpH J ε hε hcong hVdir (fact_one_le_ofReal_betaBar h.hβ).out (fact_one_le_ofReal_gammaBar h.hα h.hβ).out (congestionSequenceBuilderPack_atPowerData h hmon hcong hVmeas hVpack hpowα_eq hpowβ_eq ε hε)).weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)) (((congestionRegularizedSolutionAtEps_of_paperHypotheses (γBar := gammaBar h.α h.β) (betaBar := ENNReal.ofReal (h.β + 1)) (gammaBar := ENNReal.ofReal (gammaBar h.α h.β)) (betaBar' := ENNReal.ofReal (betaBar' h.β)) V H DpH J ε hε hcong hVdir (fact_one_le_ofReal_betaBar h.hβ).out (fact_one_le_ofReal_gammaBar h.hα h.hβ).out (congestionSequenceBuilderPack_atPowerData h hmon hcong hVmeas hVpack hpowα_eq hpowβ_eq ε hε)).weakVI.choose.1 : (Fin d → ℝ) → ℝ) x)) + ((DpH x (fun i => (((congestionRegularizedSolutionAtEps_of_paperHypotheses (γBar := gammaBar h.α h.β) (betaBar := ENNReal.ofReal (h.β + 1)) (gammaBar := ENNReal.ofReal (gammaBar h.α h.β)) (betaBar' := ENNReal.ofReal (betaBar' h.β)) V H DpH J ε hε hcong hVdir (fact_one_le_ofReal_betaBar h.hβ).out (fact_one_le_ofReal_gammaBar h.hα h.hβ).out (congestionSequenceBuilderPack_atPowerData h hmon hcong hVmeas hVpack hpowα_eq hpowβ_eq ε hε)).weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)) (((congestionRegularizedSolutionAtEps_of_paperHypotheses (γBar := gammaBar h.α h.β) (betaBar := ENNReal.ofReal (h.β + 1)) (gammaBar := ENNReal.ofReal (gammaBar h.α h.β)) (betaBar' := ENNReal.ofReal (betaBar' h.β)) V H DpH J ε hε hcong hVdir (fact_one_le_ofReal_betaBar h.hβ).out (fact_one_le_ofReal_gammaBar h.hα h.hβ).out (congestionSequenceBuilderPack_atPowerData h hmon hcong hVmeas hVpack hpowα_eq hpowβ_eq ε hε)).weakVI.choose.1 : (Fin d → ℝ) → ℝ) x)) ⬝ (fun i => (((congestionRegularizedSolutionAtEps_of_paperHypotheses (γBar := gammaBar h.α h.β) (betaBar := ENNReal.ofReal (h.β + 1)) (gammaBar := ENNReal.ofReal (gammaBar h.α h.β)) (betaBar' := ENNReal.ofReal (betaBar' h.β)) V H DpH J ε hε hcong hVdir (fact_one_le_ofReal_betaBar h.hβ).out (fact_one_le_ofReal_gammaBar h.hα h.hβ).out (congestionSequenceBuilderPack_atPowerData h hmon hcong hVmeas hVpack hpowα_eq hpowβ_eq ε hε)).weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)))) + V x * (((congestionRegularizedSolutionAtEps_of_paperHypotheses (γBar := gammaBar h.α h.β) (betaBar := ENNReal.ofReal (h.β + 1)) (gammaBar := ENNReal.ofReal (gammaBar h.α h.β)) (betaBar' := ENNReal.ofReal (betaBar' h.β)) V H DpH J ε hε hcong hVdir (fact_one_le_ofReal_betaBar h.hβ).out (fact_one_le_ofReal_gammaBar h.hα h.hβ).out (congestionSequenceBuilderPack_atPowerData h hmon hcong hVmeas hVpack hpowα_eq hpowβ_eq ε hε)).weakVI.choose.1 : (Fin d → ℝ) → ℝ) x) + (((congestionSequenceBuilderPack_atPowerData_gap (d := d) (V := V) h ε).coe_epsTerms (congestionRegularizedSolutionAtEps_of_paperHypotheses (γBar := gammaBar h.α h.β) (betaBar := ENNReal.ofReal (h.β + 1)) (gammaBar := ENNReal.ofReal (gammaBar h.α h.β)) (betaBar' := ENNReal.ofReal (betaBar' h.β)) V H DpH J ε hε hcong hVdir (fact_one_le_ofReal_betaBar h.hβ).out (fact_one_le_ofReal_gammaBar h.hα h.hβ).out (congestionSequenceBuilderPack_atPowerData h hmon hcong hVmeas hVpack hpowα_eq hpowβ_eq ε hε)).weakVI.choose) x)) ∂(volume : MeasureTheory.Measure (Fin d → ℝ)) := by
  -- Collapse the wrapper transport by substituting the exponent equalities,
  -- reducing to the native-pack form on which the producer applies directly.
  obtain ⟨_, _, αh, βh, _, _, _, _, _⟩ := h
  cases hpowα_eq
  cases hpowβ_eq
  exact coeVI_identity_atWitness_of_closure (d := d)
    (congestionRegularizedSolutionAtEps_of_paperHypotheses
      (γBar := gammaBar hcong.α hcong.β)
      (betaBar := ENNReal.ofReal (hcong.β + 1))
      (gammaBar := ENNReal.ofReal (gammaBar hcong.α hcong.β))
      (betaBar' := ENNReal.ofReal (betaBar' hcong.β))
      V H DpH J ε hε hcong hVdir
      (fact_one_le_ofReal_betaBar hcong.hβ).out
      (fact_one_le_ofReal_gammaBar hcong.hα hcong.hβ).out
      (congestionSequenceBuilderPack hmon hcong hVmeas hVpack ε hε))
    (congestionSequenceBuilderPack_atPowerData_gap (d := d) (V := V)
      ⟨_, _, hcong.α, hcong.β, _, _, _, _, _⟩ ε)
    hu_int hmFlux_int hVm_int heps_int hmH_int hmu_int hTransport hHJ0

end Congestion
end StationaryMFG
