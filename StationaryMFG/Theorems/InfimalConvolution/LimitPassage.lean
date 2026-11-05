module

/-
Copyright (c) 2026 Stationary MFG project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import StationaryMFG.Solutions.Weak
public import StationaryMFG.Solutions.Regularized
public import StationaryMFG.Theorems.SimplePower.Banach.WeakPairing
public import StationaryMFG.Hamiltonian.Estimates
public import StationaryMFG.Theorems.InfimalConvolution.Envelope

@[expose] public section

/-!
# Theorem 3 — limit passage to the weak variational inequality
(paper `eq:existweaksol.delta`, lines 1945–1986)

Paper reference: `Source/FGU-monotone_revised.tex`, lines 1945–1986
(proof of `thm:main-weak.power.growth`).

## Paper restatement

From Proposition `thm:strongAepsi.delta`, for `ε_k → 0⁺` there is a
sequence of regularised solutions `(m_{ε_k}, u_{ε_k})` satisfying, for
every admissible test pair `(μ, υ)` with `essinf μ > 0`,

```
0 ≤ ∫ (-υ - H^ε(x,Dυ,μ) + V)(μ - m_{ε_k})
   + ∫ (μ D_pH^ε(x,Dυ,μ)·(Dυ - Du_{ε_k}) + (μ-1)(υ - u_{ε_k}))
   + ε_k ∫ (|Dυ|^{γ̄-2}Dυ·D(υ-u_{ε_k}) + |υ|^{γ̄-2}υ(υ-u_{ε_k})).
```

Since `D_pH(x,Dυ,μ) ∈ L^∞` (`assH.DpH.upper.weak`), Remark
`observation` stabilises `H^ε ↦ H`, `D_pH^ε ↦ D_pH` a.e. for small ε
(arrow A4 / `Stabilization.stabilization_uniform_of_DpH_small`).
Letting `k → ∞`, the first two integrals converge by weak convergence
`(m_{ε_k}, u_{ε_k}) ⇀ (m, u)` against the fixed admissible test factors
(Hölder dualities `L^{β̄'} × L^{β̄}`, `W^{-1,γ̄'} × W^{1,γ̄}`), and the
`ε_k`-prefactored remainder vanishes (uniform `W^{1,γ̄}` boundedness +
`ε_k → 0`). The limit inequality is exactly Definition `def:weak`,
`IsWeakSolution V H DpH Du m u`.

## This file (arrow A5d — assembly keystone)

The target predicate `IsWeakSolution` is a *single* universally
quantified integral inequality over admissible test pairs (unlike
Theorem 2's multi-clause solution pack). This file lands the
**assembly keystone** of the limit passage:

`limit_passage_to_weak_VI_of_seq` takes, for each admissible test
pair, a real sequence `S` (the full per-`ε_k` right-hand side of
`eq:existweaksol.delta`, including the regularisation remainder) that

* is *eventually* `≥ 0` along the subsequence (the per-`ε_k` VI after
  stabilisation `H^ε ↦ H`, `D_pH^ε ↦ D_pH` — arrows A1 + A4), and
* converges to the limit weak integrand `W` (the analytic
  weak-convergence closures — arrows A5a/A5b/A5c),

and concludes `0 ≤ W`, i.e. the weak VI at the limit pair.

The two convergence hypotheses are precisely the deliverables of the
remaining analytic closures (split into follow-up children A5a–A5c, and
the wiring child A5e). The keystone itself is the order-topological
limit-of-nonnegatives fact `ge_of_tendsto'`.
-/

namespace StationaryMFG
namespace InfimalConvolution
namespace LimitPassage

open MeasureTheory Filter Topology
open StationaryMFG.Solutions.Weak
open StationaryMFG.Solutions.MFG
open StationaryMFG.Periodic
open StationaryMFG.Hamiltonian

variable {d : ℕ}

/-- **Limit-of-nonnegatives keystone** (paper `eq:existweaksol.delta`,
arrow A5d).

For a fixed admissible test pair, suppose a real sequence `S`
(the per-`ε_k` right-hand side of `eq:existweaksol.delta`, *after*
stabilising `H^ε ↦ H`, `D_pH^ε ↦ D_pH`) is eventually nonnegative and
converges to a real number `W`. Then `0 ≤ W`.

This is the order-topological core of the `k → ∞` passage: the per-`ε_k`
variational inequality supplies `0 ≤ S k` (eventually, for large `k`),
and the weak-convergence closures supply `S k → W`. -/
theorem nonneg_of_tendsto_of_eventually_nonneg
    {S : ℕ → ℝ} {W : ℝ}
    (htend : Tendsto S atTop (𝓝 W))
    (hnn : ∀ᶠ k in atTop, 0 ≤ S k) :
    0 ≤ W :=
  ge_of_tendsto htend hnn

/-- **Hölder `L^{β̄'} × L^{β̄}` weak-convergence closure of the first
integral of `eq:existweaksol.delta`** (paper `eq:existweaksol.delta`,
arrow A5a).

Given a fixed multiplier `g ∈ L^{βBar'}_per` and test `μ ∈ L^{βBar}_per`
(real Hölder conjugates `βBar'.HolderConjugate βBar`), a running
sequence `m_n ⇀ m` weakly in `L^{βBar}_per` (universal weak-pairing
certificate `WeakConvPairing_universal hpqβ' m_n m`), plus the per-`k`
and limit `L^{βBar}_per` regularities, the paired integral converges:

```
∫ g·(μ - m_n k)  →  ∫ g·(μ - m)   (k → ∞).
```

This is the analytic content of the first summand of the per-`ε_k`
variational inequality passing to the weak limit: only weak convergence
of `m_{ε_k}` and the `L^{βBar'}` regularity of the fixed factor are
used (no pointwise convergence of the sequence fields, no positivity).
The proof mirrors the T2 `congestionPairConv_combine` summand-1 block
(`Congestion/LimitPassage.lean`): weak pairing gives `∫ g·m_n → ∫ g·m`,
then subtract from the constant `∫ g·μ` via `integral_sub`.

-- Adapted from the summand-1 block of
-- `StationaryMFG.Theorems.Congestion.congestionPairConv_combine`. -/
theorem limit_passage_summand1_weakConv
    {βBar βBar' : ℝ}
    (hpqβ : βBar.HolderConjugate βBar')
    {g μ : (Fin d → ℝ) → ℝ}
    {m_n : ℕ → (Fin d → ℝ) → ℝ} {m : (Fin d → ℝ) → ℝ}
    (hg : MemLpPer (d := d) (ENNReal.ofReal βBar') g)
    (hμ : MemLpPer (d := d) (ENNReal.ofReal βBar) μ)
    (hm_n : ∀ k, MemLpPer (d := d) (ENNReal.ofReal βBar) (m_n k))
    (hm : MemLpPer (d := d) (ENNReal.ofReal βBar) m)
    (h_weak_m :
      StationaryMFG.Theorems.SimplePower.Banach.WeakConvPairing_universal
        (d := d) hpqβ m_n m) :
    Filter.Tendsto
      (fun k => ∫ x in UnitCube d, g x * (μ x - m_n k x))
      atTop
      (𝓝 (∫ x in UnitCube d, g x * (μ x - m x))) := by
  have hpqβ' : βBar'.HolderConjugate βBar := hpqβ.symm
  -- Weak pairing gives `∫ m_n·g → ∫ m·g`; rewrite to `∫ g·m_n`.
  have hpair_m :
      Filter.Tendsto (fun k => ∫ x in UnitCube d, g x * m_n k x)
        atTop (𝓝 (∫ x in UnitCube d, g x * m x)) := by
    have h0 :=
      StationaryMFG.Theorems.SimplePower.Banach.tendsto_integral_of_weakConvUniversal_strongTest
        hpqβ hm_n hm hg h_weak_m
    have e1 : (fun k => ∫ x in UnitCube d, m_n k x * g x)
            = (fun k => ∫ x in UnitCube d, g x * m_n k x) := by
      funext k; refine integral_congr_ae ?_
      filter_upwards with x; ring
    have e2 : (∫ x in UnitCube d, m x * g x)
            = (∫ x in UnitCube d, g x * m x) := by
      refine integral_congr_ae ?_; filter_upwards with x; ring
    rw [e1, e2] at h0; exact h0
  -- Subtract from the constant `∫ g·μ` via `integral_sub`.
  have hIgμ : IntegrableOn (fun x => g x * μ x) (UnitCube d) :=
    StationaryMFG.Periodic.MemLpPer.integrable_mul hpqβ' hg hμ
  have hIgm_n : ∀ k, IntegrableOn (fun x => g x * m_n k x) (UnitCube d) :=
    fun k => StationaryMFG.Periodic.MemLpPer.integrable_mul hpqβ' hg (hm_n k)
  have hIgm : IntegrableOn (fun x => g x * m x) (UnitCube d) :=
    StationaryMFG.Periodic.MemLpPer.integrable_mul hpqβ' hg hm
  have hconst :
      Filter.Tendsto (fun _ : ℕ => ∫ x in UnitCube d, g x * μ x)
        atTop (𝓝 (∫ x in UnitCube d, g x * μ x)) :=
    tendsto_const_nhds
  have hdiff := hconst.sub hpair_m
  have efun : (fun k => (∫ x in UnitCube d, g x * μ x)
                        - ∫ x in UnitCube d, g x * m_n k x)
            = (fun k => ∫ x in UnitCube d, g x * (μ x - m_n k x)) := by
    funext k
    rw [← MeasureTheory.integral_sub hIgμ (hIgm_n k)]
    refine integral_congr_ae ?_; filter_upwards with x; ring
  have elim : (∫ x in UnitCube d, g x * μ x)
                - ∫ x in UnitCube d, g x * m x
              = ∫ x in UnitCube d, g x * (μ x - m x) := by
    rw [← MeasureTheory.integral_sub hIgμ hIgm]
    refine integral_congr_ae ?_; filter_upwards with x; ring
  rw [efun, elim] at hdiff; exact hdiff

/-- **A5a closure specialised to the `eq:existweaksol.delta` multiplier**
(paper `eq:existweaksol.delta`, arrow A5a).

The fixed factor is the HJB multiplier
`g := -υ - H(·,Dυ,μ) + V ∈ L^{βBar'}_per`. Under weak convergence
`m_n ⇀ m` in `L^{βBar}_per`, the first integral of
`eq:existweaksol.delta` converges to its limit value:

```
∫ (-υ - H(x,Dυ,μ) + V)·(μ - m_n k)
   →  ∫ (-υ - H(x,Dυ,μ) + V)·(μ - m).
```

The conclusion is the first summand of the keystone
`limit_passage_to_weak_VI_of_seq`'s `htend` target integrand. -/
theorem limit_passage_existweaksol_term1
    {βBar βBar' : ℝ}
    (hpqβ : βBar.HolderConjugate βBar')
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {Dυ : Fin d → (Fin d → ℝ) → ℝ}
    {μ υ : (Fin d → ℝ) → ℝ}
    {m_n : ℕ → (Fin d → ℝ) → ℝ} {m : (Fin d → ℝ) → ℝ}
    (hg : MemLpPer (d := d) (ENNReal.ofReal βBar')
            (fun x => -(υ x) - H x (fun i => Dυ i x) (μ x) + V x))
    (hμ : MemLpPer (d := d) (ENNReal.ofReal βBar) μ)
    (hm_n : ∀ k, MemLpPer (d := d) (ENNReal.ofReal βBar) (m_n k))
    (hm : MemLpPer (d := d) (ENNReal.ofReal βBar) m)
    (h_weak_m :
      StationaryMFG.Theorems.SimplePower.Banach.WeakConvPairing_universal
        (d := d) hpqβ m_n m) :
    Filter.Tendsto
      (fun k => ∫ x in UnitCube d,
        (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (μ x - m_n k x))
      atTop
      (𝓝 (∫ x in UnitCube d,
        (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (μ x - m x))) :=
  limit_passage_summand1_weakConv hpqβ hg hμ hm_n hm h_weak_m

/-! ### A5b — gradient/value weak-convergence closure
(`W^{-1,γ̄'} × W^{1,γ̄}` duality)

The keystone `htend` integrand has, besides the A5a summand-1, a
**gradient summand** `μ·(D_pH(x,Dυ,μ) ⬝ (Dυ - Du_n))` and a **value
summand** `(μ-1)(υ - u_n)`. This block closes both under the Sobolev
weak convergence `(Du_n, u_n) ⇀ (Du, u)` in `W^{1,γ̄}_per` (coordinate
gradients ⇀ in `L^{γ̄}_per`, values ⇀ in `L^{γ̄}_per`), against the
fixed `L^{γ̄'}_per` factors `μ·D_pH_i` and `(μ-1)`. The Hölder duality
is the coordinatewise `L^{γ̄'} × L^{γ̄}` pairing — i.e. exactly the
A5a/`limit_passage_summand1_weakConv` machinery, applied once per
coordinate (gradient) and once for the value. -/

/-- **Value-summand weak-convergence closure** (paper
`eq:existweaksol.delta`, arrow A5b, value term).

With `u_n ⇀ u` weakly in `L^{γBar}_per` and the fixed factor
`(μ-1) ∈ L^{γBar'}_per`, the value integral converges:

```
∫ (μ x - 1)·(υ x - u_n k x)  →  ∫ (μ x - 1)·(υ x - u x).
```

This is the A5a summand-1 pattern with `g := (μ-1)`, the constant
factor `υ`, and the running sequence `u_n`. -/
theorem limit_passage_existweaksol_value
    {γBar γBar' : ℝ}
    (hpqγ : γBar.HolderConjugate γBar')
    {μ υ : (Fin d → ℝ) → ℝ}
    {u_n : ℕ → (Fin d → ℝ) → ℝ} {u : (Fin d → ℝ) → ℝ}
    (hg : MemLpPer (d := d) (ENNReal.ofReal γBar') (fun x => μ x - 1))
    (hυ : MemLpPer (d := d) (ENNReal.ofReal γBar) υ)
    (hu_n : ∀ k, MemLpPer (d := d) (ENNReal.ofReal γBar) (u_n k))
    (hu : MemLpPer (d := d) (ENNReal.ofReal γBar) u)
    (h_weak_u :
      StationaryMFG.Theorems.SimplePower.Banach.WeakConvPairing_universal
        (d := d) hpqγ u_n u) :
    Filter.Tendsto
      (fun k => ∫ x in UnitCube d, (μ x - 1) * (υ x - u_n k x))
      atTop
      (𝓝 (∫ x in UnitCube d, (μ x - 1) * (υ x - u x))) :=
  limit_passage_summand1_weakConv hpqγ hg hυ hu_n hu h_weak_u

/-- **Per-coordinate gradient-summand weak-convergence closure** (paper
`eq:existweaksol.delta`, arrow A5b, gradient term, single coordinate).

For a fixed coordinate `i`, with the `i`-th solution gradient
`(Du_n · i) ⇀ Du i` weakly in `L^{γBar}_per` and the fixed factor
`g_i := μ · D_pH(·,Dυ,μ)_i ∈ L^{γBar'}_per`, the coordinate gradient
pairing converges:

```
∫ g_i x·(Dυ i x - Du_n k i x)  →  ∫ g_i x·(Dυ i x - Du i x).
```

This is the A5a summand-1 pattern with `g := g_i`, the constant factor
`Dυ i`, and the running sequence `fun k => Du_n k i`. -/
theorem limit_passage_existweaksol_grad_coord
    {γBar γBar' : ℝ}
    (hpqγ : γBar.HolderConjugate γBar')
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {Dυ Du : Fin d → (Fin d → ℝ) → ℝ}
    {μ : (Fin d → ℝ) → ℝ}
    {Du_n : ℕ → Fin d → (Fin d → ℝ) → ℝ}
    (i : Fin d)
    (hg : MemLpPer (d := d) (ENNReal.ofReal γBar')
            (fun x => μ x * DpH x (fun j => Dυ j x) (μ x) i))
    (hDυ : MemLpPer (d := d) (ENNReal.ofReal γBar) (Dυ i))
    (hDu_n : ∀ k, MemLpPer (d := d) (ENNReal.ofReal γBar) (Du_n k i))
    (hDu : MemLpPer (d := d) (ENNReal.ofReal γBar) (Du i))
    (h_weak_Du :
      StationaryMFG.Theorems.SimplePower.Banach.WeakConvPairing_universal
        (d := d) hpqγ (fun k => Du_n k i) (Du i)) :
    Filter.Tendsto
      (fun k => ∫ x in UnitCube d,
        (μ x * DpH x (fun j => Dυ j x) (μ x) i) * (Dυ i x - Du_n k i x))
      atTop
      (𝓝 (∫ x in UnitCube d,
        (μ x * DpH x (fun j => Dυ j x) (μ x) i) * (Dυ i x - Du i x))) :=
  limit_passage_summand1_weakConv hpqγ hg hDυ hDu_n hDu h_weak_Du

/-- **Combined gradient + value weak-convergence closure** (paper
`eq:existweaksol.delta`, arrow A5b).

The second and third summands of the keystone `htend` integrand,
```
μ x · (D_pH(x,Dυ,μ) ⬝ (Dυ - Du_n k))  +  (μ x - 1)·(υ x - u_n k x),
```
converge to their limit values under the `W^{1,γ̄}_per` weak
convergence of `(Du_n, u_n) ⇀ (Du, u)` (coordinate gradients ⇀ in
`L^{γBar}_per`, values ⇀ in `L^{γBar}_per`) against the fixed
`L^{γBar'}_per` factors `μ·D_pH_i` and `(μ-1)`.

The gradient `euclideanDot` is expanded coordinatewise
(`euclideanDot = ∑ i, …`, distributing `μ x`) into `d` copies of the
per-coordinate closure `limit_passage_existweaksol_grad_coord`, summed
via `tendsto_finset_sum`; the value summand uses
`limit_passage_existweaksol_value`; the integral of the sum is split by
`MeasureTheory.integral_finset_sum` / `integral_add`. The conclusion
composes with the A5a `limit_passage_existweaksol_term1` via
`Filter.Tendsto.add`. -/
theorem limit_passage_existweaksol_term23
    {γBar γBar' : ℝ}
    (hpqγ : γBar.HolderConjugate γBar')
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {Dυ Du : Fin d → (Fin d → ℝ) → ℝ}
    {μ υ : (Fin d → ℝ) → ℝ}
    {Du_n : ℕ → Fin d → (Fin d → ℝ) → ℝ}
    {u_n : ℕ → (Fin d → ℝ) → ℝ} {u : (Fin d → ℝ) → ℝ}
    -- gradient factors and convergence (per coordinate)
    (hgGrad : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBar')
                (fun x => μ x * DpH x (fun j => Dυ j x) (μ x) i))
    (hDυ : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBar) (Dυ i))
    (hDu_n : ∀ k i, MemLpPer (d := d) (ENNReal.ofReal γBar) (Du_n k i))
    (hDu : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBar) (Du i))
    (h_weak_Du : ∀ i,
      StationaryMFG.Theorems.SimplePower.Banach.WeakConvPairing_universal
        (d := d) hpqγ (fun k => Du_n k i) (Du i))
    -- value factors and convergence
    (hgVal : MemLpPer (d := d) (ENNReal.ofReal γBar') (fun x => μ x - 1))
    (hυ : MemLpPer (d := d) (ENNReal.ofReal γBar) υ)
    (hu_n : ∀ k, MemLpPer (d := d) (ENNReal.ofReal γBar) (u_n k))
    (hu : MemLpPer (d := d) (ENNReal.ofReal γBar) u)
    (h_weak_u :
      StationaryMFG.Theorems.SimplePower.Banach.WeakConvPairing_universal
        (d := d) hpqγ u_n u) :
    Filter.Tendsto
      (fun k => ∫ x in UnitCube d,
        μ x * (DpH x (fun j => Dυ j x) (μ x)
                ⬝ (fun i => Dυ i x - Du_n k i x))
          + (μ x - 1) * (υ x - u_n k x))
      atTop
      (𝓝 (∫ x in UnitCube d,
        μ x * (DpH x (fun j => Dυ j x) (μ x)
                ⬝ (fun i => Dυ i x - Du i x))
          + (μ x - 1) * (υ x - u x))) := by
  have hpqγ' : γBar'.HolderConjugate γBar := hpqγ.symm
  -- Abbreviation: the per-coordinate `L^{γ̄'}` gradient factor.
  set gGrad : Fin d → (Fin d → ℝ) → ℝ :=
    fun i x => μ x * DpH x (fun j => Dυ j x) (μ x) i with hgGrad_def
  -- Integrability facts (Hölder products on the cube).
  have hIgGrad_n : ∀ k i,
      IntegrableOn
        (fun x => gGrad i x * (Dυ i x - Du_n k i x)) (UnitCube d) := by
    intro k i
    have hdiff : MemLpPer (d := d) (ENNReal.ofReal γBar)
        (fun x => Dυ i x - Du_n k i x) := by
      have := StationaryMFG.Periodic.MemLp.toMemLpPer (MeasureTheory.MemLp.sub (hDυ i).toMemLp (hDu_n k i).toMemLp)
      simpa only [Pi.sub_def] using this
    exact StationaryMFG.Periodic.MemLpPer.integrable_mul hpqγ' (hgGrad i) hdiff
  have hIgGrad : ∀ i,
      IntegrableOn
        (fun x => gGrad i x * (Dυ i x - Du i x)) (UnitCube d) := by
    intro i
    have hdiff : MemLpPer (d := d) (ENNReal.ofReal γBar)
        (fun x => Dυ i x - Du i x) := by
      have := StationaryMFG.Periodic.MemLp.toMemLpPer (MeasureTheory.MemLp.sub (hDυ i).toMemLp (hDu i).toMemLp)
      simpa only [Pi.sub_def] using this
    exact StationaryMFG.Periodic.MemLpPer.integrable_mul hpqγ' (hgGrad i) hdiff
  have hIVal_n : ∀ k,
      IntegrableOn (fun x => (μ x - 1) * (υ x - u_n k x)) (UnitCube d) := by
    intro k
    have hdiff : MemLpPer (d := d) (ENNReal.ofReal γBar)
        (fun x => υ x - u_n k x) := by
      have := StationaryMFG.Periodic.MemLp.toMemLpPer (MeasureTheory.MemLp.sub hυ.toMemLp (hu_n k).toMemLp)
      simpa only [Pi.sub_def] using this
    exact StationaryMFG.Periodic.MemLpPer.integrable_mul hpqγ' hgVal hdiff
  have hIVal :
      IntegrableOn (fun x => (μ x - 1) * (υ x - u x)) (UnitCube d) := by
    have hdiff : MemLpPer (d := d) (ENNReal.ofReal γBar)
        (fun x => υ x - u x) := by
      have := StationaryMFG.Periodic.MemLp.toMemLpPer (MeasureTheory.MemLp.sub hυ.toMemLp hu.toMemLp)
      simpa only [Pi.sub_def] using this
    exact StationaryMFG.Periodic.MemLpPer.integrable_mul hpqγ' hgVal hdiff
  -- Rewrite the running integrand as `∑_i (coord) + value`.
  have hsplit_n : ∀ k,
      (∫ x in UnitCube d,
        μ x * (DpH x (fun j => Dυ j x) (μ x)
                ⬝ (fun i => Dυ i x - Du_n k i x))
          + (μ x - 1) * (υ x - u_n k x))
      = (∑ i : Fin d, ∫ x in UnitCube d,
            gGrad i x * (Dυ i x - Du_n k i x))
          + ∫ x in UnitCube d, (μ x - 1) * (υ x - u_n k x) := by
    intro k
    -- pointwise: `μ · (D_pH ⬝ Δ) = ∑_i gGrad i · Δ_i`.
    have hpt : ∀ x,
        μ x * (DpH x (fun j => Dυ j x) (μ x)
                ⬝ (fun i => Dυ i x - Du_n k i x))
          = ∑ i : Fin d, gGrad i x * (Dυ i x - Du_n k i x) := by
      intro x
      simp only [hgGrad_def, euclideanDot, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _; ring
    -- integrate the sum over coordinates and add the value integral.
    rw [MeasureTheory.integral_add ?_ (hIVal_n k)]
    · congr 1
      rw [← MeasureTheory.integral_finset_sum _ (fun i _ => hIgGrad_n k i)]
      refine integral_congr_ae ?_
      filter_upwards with x using hpt x
    · -- integrability of the gradient summand `μ·(D_pH ⬝ Δ)`.
      have hsum_int :
          IntegrableOn
            (fun x => ∑ i : Fin d, gGrad i x * (Dυ i x - Du_n k i x))
            (UnitCube d) :=
        MeasureTheory.integrable_finset_sum _ (fun i _ => hIgGrad_n k i)
      refine hsum_int.congr ?_
      filter_upwards with x using (hpt x).symm
  have hsplit_lim :
      (∫ x in UnitCube d,
        μ x * (DpH x (fun j => Dυ j x) (μ x)
                ⬝ (fun i => Dυ i x - Du i x))
          + (μ x - 1) * (υ x - u x))
      = (∑ i : Fin d, ∫ x in UnitCube d,
            gGrad i x * (Dυ i x - Du i x))
          + ∫ x in UnitCube d, (μ x - 1) * (υ x - u x) := by
    have hpt : ∀ x,
        μ x * (DpH x (fun j => Dυ j x) (μ x)
                ⬝ (fun i => Dυ i x - Du i x))
          = ∑ i : Fin d, gGrad i x * (Dυ i x - Du i x) := by
      intro x
      simp only [hgGrad_def, euclideanDot, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _; ring
    rw [MeasureTheory.integral_add ?_ hIVal]
    · congr 1
      rw [← MeasureTheory.integral_finset_sum _ (fun i _ => hIgGrad i)]
      refine integral_congr_ae ?_
      filter_upwards with x using hpt x
    · have hsum_int :
          IntegrableOn
            (fun x => ∑ i : Fin d, gGrad i x * (Dυ i x - Du i x))
            (UnitCube d) :=
        MeasureTheory.integrable_finset_sum _ (fun i _ => hIgGrad i)
      refine hsum_int.congr ?_
      filter_upwards with x using (hpt x).symm
  -- Coordinate-wise gradient convergence, summed.
  have hgrad_tend :
      Filter.Tendsto
        (fun k => ∑ i : Fin d, ∫ x in UnitCube d,
            gGrad i x * (Dυ i x - Du_n k i x))
        atTop
        (𝓝 (∑ i : Fin d, ∫ x in UnitCube d,
            gGrad i x * (Dυ i x - Du i x))) := by
    refine tendsto_finset_sum _ (fun i _ => ?_)
    exact limit_passage_existweaksol_grad_coord hpqγ i
      (hgGrad i) (hDυ i) (hDu_n · i) (hDu i) (h_weak_Du i)
  -- Value convergence.
  have hval_tend :
      Filter.Tendsto
        (fun k => ∫ x in UnitCube d, (μ x - 1) * (υ x - u_n k x))
        atTop
        (𝓝 (∫ x in UnitCube d, (μ x - 1) * (υ x - u x))) :=
    limit_passage_existweaksol_value hpqγ hgVal hυ hu_n hu h_weak_u
  -- Combine and rewrite back to the unsplit integrand.
  have hcomb := hgrad_tend.add hval_tend
  -- Rewrite the limit value to the unsplit form.
  rw [← hsplit_lim] at hcomb
  -- Rewrite the running sequence to the unsplit form.
  refine hcomb.congr ?_
  intro k
  exact (hsplit_n k).symm

/-! ### A5c — vanishing of the `ε_k` regularisation remainder

The per-`ε_k` pairing of `eq:existweaksol.delta` decomposes (seam
`mfgOperatorEpsPair_pairing_eq`) as `[def:weak integrand] + ε_k · R_k`,
where `R_k = gateauxWpPair γ̄ Dυ υ (Dυ - Du_{ε_k}) (υ - u_{ε_k})` is the
γ̄-Laplacian Gateaux pairing. Since the a-priori bound makes `|R_k|`
uniformly bounded (fixed `υ, Dυ` against a uniformly `W^{1,γ̄}`-bounded
difference) and `ε_k → 0`, the remainder `ε_k · R_k` vanishes. -/

/-- **Abstract vanishing of an `ε`-prefactored, uniformly bounded
remainder** (paper `eq:existweaksol.delta`, arrow A5c, real core).

If `ε_k → 0` and a real sequence `g` is uniformly bounded in absolute
value (`∀ k, |g k| ≤ M`), then the product `ε_k · g_k → 0`.

This is the order-free numeric squeeze underlying the discarding of the
regularisation remainder in the `k → ∞` passage: `|ε_k · g_k| ≤
|ε_k| · M` and `|ε_k| · M → 0`. (Same squeeze as `hres_tendsto` inside
`SimplePower.limit_passage_real`, factored out for the def:weak
single-inequality target.) -/
theorem gateaux_remainder_tendsto_zero
    {ε g : ℕ → ℝ} {M : ℝ}
    (hε_to0 : Tendsto ε atTop (𝓝 0))
    (hbdd : ∀ k, |g k| ≤ M) :
    Tendsto (fun k => ε k * g k) atTop (𝓝 0) := by
  have hM_nonneg : 0 ≤ M := le_trans (abs_nonneg _) (hbdd 0)
  -- `|ε k| → 0`.
  have habs : Tendsto (fun k => |ε k|) atTop (𝓝 0) := by
    have habs_eq : (fun k => |ε k|) = (fun k => ‖ε k‖) := by
      funext k; rw [Real.norm_eq_abs]
    rw [habs_eq]; simpa using hε_to0.norm
  -- `|ε k| · M → 0`.
  have hbnd_tendsto : Tendsto (fun k => |ε k| * M) atTop (𝓝 0) := by
    have : Tendsto (fun k => |ε k| * M) atTop (𝓝 (0 * M)) :=
      habs.mul_const M
    simpa using this
  -- Squeeze `|ε k · g k| ≤ |ε k| · M`.
  refine squeeze_zero_norm (a := fun k => |ε k| * M) ?_ hbnd_tendsto
  intro k
  have h1 : |ε k * g k| ≤ |ε k| * M := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hbdd k) (abs_nonneg _)
  simpa [Real.norm_eq_abs] using h1

/-- **Vanishing of the `eq:existweaksol.delta` regularisation remainder**
(paper `eq:existweaksol.delta`, arrow A5c).

Specialising `gateaux_remainder_tendsto_zero` to the actual remainder
factor `R_k = gateauxWpPair γBar Dυ υ (Dυ - Du_n k) (υ - u_n k)`:
under `ε_k → 0` and the uniform a-priori bound `|R_k| ≤ M` (output of
the `W^{1,γ̄}` a-priori bound, A2/A2f), the remainder
`ε_k · R_k → 0` as `k → ∞`. -/
theorem limit_passage_existweaksol_remainder
    {γBar : ℝ} {ε : ℕ → ℝ}
    {Dυ : Fin d → (Fin d → ℝ) → ℝ} {υ : (Fin d → ℝ) → ℝ}
    {Du_n : ℕ → Fin d → (Fin d → ℝ) → ℝ}
    {u_n : ℕ → (Fin d → ℝ) → ℝ}
    {M : ℝ}
    (hε_to0 : Tendsto ε atTop (𝓝 0))
    (hbdd : ∀ k,
      |gateauxWpPair γBar Dυ υ
          (fun i x => Dυ i x - Du_n k i x) (υ - u_n k)| ≤ M) :
    Tendsto
      (fun k => ε k * gateauxWpPair γBar Dυ υ
          (fun i x => Dυ i x - Du_n k i x) (υ - u_n k))
      atTop (𝓝 0) :=
  gateaux_remainder_tendsto_zero (ε := ε)
    (g := fun k => gateauxWpPair γBar Dυ υ
        (fun i x => Dυ i x - Du_n k i x) (υ - u_n k))
    hε_to0 hbdd

/-- **Composed `htend` for the keystone** (paper `eq:existweaksol.delta`,
arrows A5a + A5b + A5c).

The per-`ε_k` right-hand side of `eq:existweaksol.delta`, written
through the seam `mfgOperatorEpsPair_pairing_eq` as
```
S k = [def:weak integrand at (m_n k, u_n k)]  +  ε_k · R_k,
```
converges to the `def:weak` integrand at the limit pair `(m, u, Du)`.
The convergence of the integrand part is A5a
(`limit_passage_existweaksol_term1`) + A5b
(`limit_passage_existweaksol_term23`) combined via `Tendsto.add`; the
remainder `ε_k · R_k → 0` is A5c
(`limit_passage_existweaksol_remainder`). The whole sum then tends to
`[limit integrand] + 0` via `Tendsto.add`, which is the keystone's
`htend` target. -/
theorem limit_passage_existweaksol_htend
    {βBar βBar' γBar γBar' : ℝ}
    (hpqβ : βBar.HolderConjugate βBar')
    (hpqγ : γBar.HolderConjugate γBar')
    {ε : ℕ → ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {Dυ Du : Fin d → (Fin d → ℝ) → ℝ}
    {μ υ : (Fin d → ℝ) → ℝ}
    {m_n : ℕ → (Fin d → ℝ) → ℝ} {m : (Fin d → ℝ) → ℝ}
    {Du_n : ℕ → Fin d → (Fin d → ℝ) → ℝ}
    {u_n : ℕ → (Fin d → ℝ) → ℝ} {u : (Fin d → ℝ) → ℝ}
    {M : ℝ}
    -- A5a factor and weak convergence (HJB multiplier in `L^{βBar'}`)
    (hg1 : MemLpPer (d := d) (ENNReal.ofReal βBar')
            (fun x => -(υ x) - H x (fun i => Dυ i x) (μ x) + V x))
    (hμβ : MemLpPer (d := d) (ENNReal.ofReal βBar) μ)
    (hm_n : ∀ k, MemLpPer (d := d) (ENNReal.ofReal βBar) (m_n k))
    (hm : MemLpPer (d := d) (ENNReal.ofReal βBar) m)
    (h_weak_m :
      StationaryMFG.Theorems.SimplePower.Banach.WeakConvPairing_universal
        (d := d) hpqβ m_n m)
    -- A5b gradient factors and weak convergence (per coordinate)
    (hgGrad : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBar')
                (fun x => μ x * DpH x (fun j => Dυ j x) (μ x) i))
    (hDυ : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBar) (Dυ i))
    (hDu_n : ∀ k i, MemLpPer (d := d) (ENNReal.ofReal γBar) (Du_n k i))
    (hDu : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBar) (Du i))
    (h_weak_Du : ∀ i,
      StationaryMFG.Theorems.SimplePower.Banach.WeakConvPairing_universal
        (d := d) hpqγ (fun k => Du_n k i) (Du i))
    -- A5b value factors and weak convergence
    (hgVal : MemLpPer (d := d) (ENNReal.ofReal γBar') (fun x => μ x - 1))
    (hυ : MemLpPer (d := d) (ENNReal.ofReal γBar) υ)
    (hu_n : ∀ k, MemLpPer (d := d) (ENNReal.ofReal γBar) (u_n k))
    (hu : MemLpPer (d := d) (ENNReal.ofReal γBar) u)
    (h_weak_u :
      StationaryMFG.Theorems.SimplePower.Banach.WeakConvPairing_universal
        (d := d) hpqγ u_n u)
    -- A5c remainder data
    (hε_to0 : Tendsto ε atTop (𝓝 0))
    (hbdd : ∀ k,
      |gateauxWpPair γBar Dυ υ
          (fun i x => Dυ i x - Du_n k i x) (υ - u_n k)| ≤ M) :
    Tendsto
      (fun k =>
        (∫ x in UnitCube d,
          (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (μ x - m_n k x)
          ∂(volume : Measure (Fin d → ℝ)))
        + (∫ x in UnitCube d,
            μ x * (DpH x (fun j => Dυ j x) (μ x)
                    ⬝ (fun i => Dυ i x - Du_n k i x))
              + (μ x - 1) * (υ x - u_n k x)
          ∂(volume : Measure (Fin d → ℝ)))
        + ε k * gateauxWpPair γBar Dυ υ
            (fun i x => Dυ i x - Du_n k i x) (υ - u_n k))
      atTop
      (𝓝 ((∫ x in UnitCube d,
            (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (μ x - m x)
          ∂(volume : Measure (Fin d → ℝ)))
          + (∫ x in UnitCube d,
              μ x * (DpH x (fun j => Dυ j x) (μ x)
                      ⬝ (fun i => Dυ i x - Du i x))
                + (μ x - 1) * (υ x - u x)
            ∂(volume : Measure (Fin d → ℝ))))) := by
  -- A5a: first summand converges.
  have hterm1 := limit_passage_existweaksol_term1 (d := d)
    hpqβ hg1 hμβ hm_n hm h_weak_m
  -- A5b: gradient + value summands converge.
  have hterm23 := limit_passage_existweaksol_term23 (d := d)
    hpqγ hgGrad hDυ hDu_n hDu h_weak_Du hgVal hυ hu_n hu h_weak_u
  -- A5c: remainder vanishes.
  have hrem := limit_passage_existweaksol_remainder (d := d)
    (γBar := γBar) (ε := ε) hε_to0 hbdd
  -- Compose: (A5a + A5b) + A5c, with the remainder limit `0` absorbed.
  have hsum := (hterm1.add hterm23).add hrem
  simpa using hsum

/-- **Assembly keystone for the weak VI at the limit pair** (paper
`eq:existweaksol.delta`, arrow A5d).

Given the limit data `(m, u, Du)` and, *for every admissible test pair*
`(Dυ, μ, υ)`:

* a real sequence `S Dυ μ υ` — the per-`ε_k` right-hand side of
  `eq:existweaksol.delta` after stabilisation `H^ε ↦ H`,
  `D_pH^ε ↦ D_pH` (arrows A1 + A4) — that is eventually nonnegative
  along the subsequence `k → ∞` (the per-`ε_k` variational
  inequality), and
* convergence of that sequence to the limit weak integrand `W` for the
  test pair (the analytic weak-convergence closures A5a/A5b/A5c),

where `W` is the `def:weak` integrand at the limit pair `(m, u, Du)`,
the pair `(m, u)` is a weak solution `IsWeakSolution V H DpH Du m u`.

This isolates the order-topological core of the `k → ∞` passage; the
two per-test-pair hypotheses are precisely the deliverables of the
remaining analytic-closure children (A5a–A5c) and of the per-`ε_k`
family / stabilisation (A1 + A4). -/
theorem limit_passage_to_weak_VI_of_seq
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    (S : (Fin d → (Fin d → ℝ) → ℝ) → ((Fin d → ℝ) → ℝ) →
          ((Fin d → ℝ) → ℝ) → ℕ → ℝ)
    (hnn : ∀ (Dυ : Fin d → (Fin d → ℝ) → ℝ) (μ υ : (Fin d → ℝ) → ℝ),
      IsWeakSolutionTestPair Dυ μ υ →
        ∀ᶠ k in atTop, 0 ≤ S Dυ μ υ k)
    (htend : ∀ (Dυ : Fin d → (Fin d → ℝ) → ℝ) (μ υ : (Fin d → ℝ) → ℝ),
      IsWeakSolutionTestPair Dυ μ υ →
        Tendsto (S Dυ μ υ) atTop
          (𝓝 (∫ x in UnitCube d,
                (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (μ x - m x)
                  + μ x * (DpH x (fun i => Dυ i x) (μ x)
                            ⬝ (fun i => Dυ i x - Du i x))
                  + (μ x - 1) * (υ x - u x)
              ∂(volume : Measure (Fin d → ℝ))))) :
    IsWeakSolution V H DpH Du m u := by
  intro Dυ μ υ hadm
  exact nonneg_of_tendsto_of_eventually_nonneg
    (htend Dυ μ υ hadm) (hnn Dυ μ υ hadm)

/-! ### A5e — wiring the keystone with A5a/A5b/A5c + A1/A4

The keystone `limit_passage_to_weak_VI_of_seq` consumes, per admissible
test pair, a real sequence `S` that (i) is eventually nonnegative
(the per-`ε_k` VI after stabilisation, arrows A1 + A4) and (ii)
converges to the `def:weak` integrand at the limit pair (arrows
A5a/A5b/A5c). The composed convergence `htend` is delivered by
`limit_passage_existweaksol_htend`, whose target is the *split* form
`(∫ A) + (∫ (B + C))`, whereas the keystone wants the *single*
integral `∫ (A + B + C)`. The two are equal by `integral_add`; the
helper below records that reconciliation. -/

/-- **Single-integral `htend` for the keystone** (paper
`eq:existweaksol.delta`, arrows A5a + A5b + A5c, recombined).

Identical hypotheses to `limit_passage_existweaksol_htend`, plus the
two limit integrabilities needed to merge the split target
`(∫ A) + (∫ (B + C))` into the single integral `∫ (A + B + C)` that the
keystone `limit_passage_to_weak_VI_of_seq` consumes as its `htend`
target. The running sequence is left in the explicit
three-summand form `(∫ A_k) + (∫ (B_k + C_k)) + ε_k · R_k`. -/
theorem limit_passage_existweaksol_htend_combined
    {βBar βBar' γBar γBar' : ℝ}
    (hpqβ : βBar.HolderConjugate βBar')
    (hpqγ : γBar.HolderConjugate γBar')
    {ε : ℕ → ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {Dυ Du : Fin d → (Fin d → ℝ) → ℝ}
    {μ υ : (Fin d → ℝ) → ℝ}
    {m_n : ℕ → (Fin d → ℝ) → ℝ} {m : (Fin d → ℝ) → ℝ}
    {Du_n : ℕ → Fin d → (Fin d → ℝ) → ℝ}
    {u_n : ℕ → (Fin d → ℝ) → ℝ} {u : (Fin d → ℝ) → ℝ}
    {M : ℝ}
    (hg1 : MemLpPer (d := d) (ENNReal.ofReal βBar')
            (fun x => -(υ x) - H x (fun i => Dυ i x) (μ x) + V x))
    (hμβ : MemLpPer (d := d) (ENNReal.ofReal βBar) μ)
    (hm_n : ∀ k, MemLpPer (d := d) (ENNReal.ofReal βBar) (m_n k))
    (hm : MemLpPer (d := d) (ENNReal.ofReal βBar) m)
    (h_weak_m :
      StationaryMFG.Theorems.SimplePower.Banach.WeakConvPairing_universal
        (d := d) hpqβ m_n m)
    (hgGrad : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBar')
                (fun x => μ x * DpH x (fun j => Dυ j x) (μ x) i))
    (hDυ : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBar) (Dυ i))
    (hDu_n : ∀ k i, MemLpPer (d := d) (ENNReal.ofReal γBar) (Du_n k i))
    (hDu : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBar) (Du i))
    (h_weak_Du : ∀ i,
      StationaryMFG.Theorems.SimplePower.Banach.WeakConvPairing_universal
        (d := d) hpqγ (fun k => Du_n k i) (Du i))
    (hgVal : MemLpPer (d := d) (ENNReal.ofReal γBar') (fun x => μ x - 1))
    (hυ : MemLpPer (d := d) (ENNReal.ofReal γBar) υ)
    (hu_n : ∀ k, MemLpPer (d := d) (ENNReal.ofReal γBar) (u_n k))
    (hu : MemLpPer (d := d) (ENNReal.ofReal γBar) u)
    (h_weak_u :
      StationaryMFG.Theorems.SimplePower.Banach.WeakConvPairing_universal
        (d := d) hpqγ u_n u)
    (hε_to0 : Tendsto ε atTop (𝓝 0))
    (hbdd : ∀ k,
      |gateauxWpPair γBar Dυ υ
          (fun i x => Dυ i x - Du_n k i x) (υ - u_n k)| ≤ M) :
    Tendsto
      (fun k =>
        (∫ x in UnitCube d,
          (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (μ x - m_n k x)
          ∂(volume : Measure (Fin d → ℝ)))
        + (∫ x in UnitCube d,
            μ x * (DpH x (fun j => Dυ j x) (μ x)
                    ⬝ (fun i => Dυ i x - Du_n k i x))
              + (μ x - 1) * (υ x - u_n k x)
          ∂(volume : Measure (Fin d → ℝ)))
        + ε k * gateauxWpPair γBar Dυ υ
            (fun i x => Dυ i x - Du_n k i x) (υ - u_n k))
      atTop
      (𝓝 (∫ x in UnitCube d,
            (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (μ x - m x)
              + μ x * (DpH x (fun i => Dυ i x) (μ x)
                        ⬝ (fun i => Dυ i x - Du i x))
              + (μ x - 1) * (υ x - u x)
          ∂(volume : Measure (Fin d → ℝ)))) := by
  have hpqβ' : βBar'.HolderConjugate βBar := hpqβ.symm
  have hpqγ' : γBar'.HolderConjugate γBar := hpqγ.symm
  -- The split-target convergence (A5a + A5b + A5c).
  have hsplit := limit_passage_existweaksol_htend (d := d)
    hpqβ hpqγ hg1 hμβ hm_n hm h_weak_m
    hgGrad hDυ hDu_n hDu h_weak_Du hgVal hυ hu_n hu h_weak_u hε_to0 hbdd
  -- Merge the two limit integrals `(∫ A) + (∫ (B+C)) = ∫ (A+B+C)`.
  -- Term-1 integrability (Hölder `L^{β̄'} × L^{β̄}` on the cube).
  have hIA : IntegrableOn
      (fun x =>
        (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (μ x - m x))
      (UnitCube d) := by
    have hdiff : MemLpPer (d := d) (ENNReal.ofReal βBar)
        (fun x => μ x - m x) := by
      have := StationaryMFG.Periodic.MemLp.toMemLpPer (MeasureTheory.MemLp.sub hμβ.toMemLp hm.toMemLp)
      simpa only [Pi.sub_def] using this
    exact StationaryMFG.Periodic.MemLpPer.integrable_mul hpqβ' hg1 hdiff
  -- Term-(2+3) integrability: split into the `d` gradient summands plus
  -- the value summand, each a Hölder `L^{γ̄'} × L^{γ̄}` product.
  have hIBC : IntegrableOn
      (fun x =>
        μ x * (DpH x (fun i => Dυ i x) (μ x)
                ⬝ (fun i => Dυ i x - Du i x))
          + (μ x - 1) * (υ x - u x))
      (UnitCube d) := by
    -- value-summand integrability
    have hIVal : IntegrableOn
        (fun x => (μ x - 1) * (υ x - u x)) (UnitCube d) := by
      have hdiff : MemLpPer (d := d) (ENNReal.ofReal γBar)
          (fun x => υ x - u x) := by
        have := StationaryMFG.Periodic.MemLp.toMemLpPer (MeasureTheory.MemLp.sub hυ.toMemLp hu.toMemLp)
        simpa only [Pi.sub_def] using this
      exact StationaryMFG.Periodic.MemLpPer.integrable_mul hpqγ' hgVal hdiff
    -- gradient-summand integrability (coordinatewise, then summed)
    have hIgrad : IntegrableOn
        (fun x => μ x * (DpH x (fun i => Dυ i x) (μ x)
                          ⬝ (fun i => Dυ i x - Du i x)))
        (UnitCube d) := by
      have hIcoord : ∀ i, IntegrableOn
          (fun x => (μ x * DpH x (fun j => Dυ j x) (μ x) i)
                      * (Dυ i x - Du i x)) (UnitCube d) := by
        intro i
        have hdiff : MemLpPer (d := d) (ENNReal.ofReal γBar)
            (fun x => Dυ i x - Du i x) := by
          have := StationaryMFG.Periodic.MemLp.toMemLpPer (MeasureTheory.MemLp.sub (hDυ i).toMemLp (hDu i).toMemLp)
          simpa only [Pi.sub_def] using this
        exact StationaryMFG.Periodic.MemLpPer.integrable_mul hpqγ'
          (hgGrad i) hdiff
      have hsum : IntegrableOn
          (fun x => ∑ i : Fin d,
              (μ x * DpH x (fun j => Dυ j x) (μ x) i) * (Dυ i x - Du i x))
          (UnitCube d) :=
        MeasureTheory.integrable_finset_sum _ (fun i _ => hIcoord i)
      refine hsum.congr ?_
      filter_upwards with x
      simp only [euclideanDot, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _; ring
    exact hIgrad.add hIVal
  -- Rewrite the limit value to the single integral.
  have hmerge :
      (∫ x in UnitCube d,
          (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (μ x - m x)
        ∂(volume : Measure (Fin d → ℝ)))
        + (∫ x in UnitCube d,
            μ x * (DpH x (fun i => Dυ i x) (μ x)
                    ⬝ (fun i => Dυ i x - Du i x))
              + (μ x - 1) * (υ x - u x)
          ∂(volume : Measure (Fin d → ℝ)))
      = ∫ x in UnitCube d,
          (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (μ x - m x)
            + μ x * (DpH x (fun i => Dυ i x) (μ x)
                      ⬝ (fun i => Dυ i x - Du i x))
            + (μ x - 1) * (υ x - u x)
        ∂(volume : Measure (Fin d → ℝ)) := by
    rw [← MeasureTheory.integral_add hIA hIBC]
    refine integral_congr_ae ?_
    filter_upwards with x; ring
  rw [hmerge] at hsplit
  exact hsplit

/-! ## A4b — keystone `hnn` from the A1d `∀ ε`-family + A4 stabilisation
(paper `eq:existweaksol.delta`, line 1968; Remark `observation`, lines
1923–1941)

The closed strong-VI family
`Existence.strongAepsi_deltaK0_family_of_selectorData_ae` yields, at
the per-`ε_k` solution triple `(m_n k, u_n k, Du_n k)`, the bare strong VI
`IsStrongVI_Aepsi … (Hdelta hweak (ε k)) (DpHepsilon hweak qE) …`. Unfolded
through `Solutions.Regularized.mfgOperatorEpsPair_pairing_eq`, this is the
non-negativity of the explicit three-summand RHS of `eq:existweaksol.delta`
*with the REGULARISED Hamiltonian* `H^{ε_k}`, `D_pH^{ε_k}`.

The A4 stabilisation producer
`Stabilization.stabilization_uniform_of_DpH_small` provides, for each
admissible test pair and small `ε`, the a.e. identities
`H^{ε_k}(x, Dυ, μ) = H(x, Dυ, μ)`, `D_pH^{ε_k}(x, Dυ, μ) = D_pH(x, Dυ, μ)`
on the cube. Substituting these a.e. identities into the two integrals of
the RHS (they only see `H`/`D_pH` evaluated at the *test* argument
`(x, Dυ(x), μ(x))`) turns the regularised RHS into the *stabilised* RHS
with the limit `H`, `D_pH` — the exact `hnn` shape consumed by
`limit_passage_to_weak_VI_of_paperHypotheses`.

`keystone_hnn_of_perEps_VI_and_stabilization` performs this substitution.
It is stated against an abstract per-`k` regularised Hamiltonian family
`Hε`, `D_pHε` (instantiated at the call site by `Hdelta hweak (ε ·)`,
`DpHepsilon hweak qE`), so it is decoupled from the family's Browder–Minty
context types: it consumes only the per-`k` `mfgOperatorEpsPair`
non-negativity (the unfolded `IsStrongVI_Aepsi`) and the per-`k` eventual
a.e. stabilisation identities. -/
theorem keystone_hnn_of_perEps_VI_and_stabilization
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {Hε : ℕ → (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpHε : ℕ → (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBar : ℝ}
    {ε : ℕ → ℝ}
    {m_n : ℕ → (Fin d → ℝ) → ℝ}
    {Du_n : ℕ → Fin d → (Fin d → ℝ) → ℝ}
    {u_n : ℕ → (Fin d → ℝ) → ℝ}
    {Dυ : Fin d → (Fin d → ℝ) → ℝ} {μ υ : (Fin d → ℝ) → ℝ}
    -- (A1d) per-`k` regularised VI in `mfgOperatorEpsPair` form (the
    -- unfolded `IsStrongVI_Aepsi` at the per-`k` solution triple).
    (hVIeps : ∀ k,
      0 ≤ mfgOperatorEpsPair (V := V) (H := Hε k) (DpH := DpHε k)
            γBar (ε k) Dυ μ υ
            (fun i x => Dυ i x - Du_n k i x)
            (μ - m_n k) (υ - u_n k))
    -- (A4) eventual a.e. stabilisation `H^{ε_k} ↦ H`, `D_pH^{ε_k} ↦ D_pH`.
    (hstabH : ∀ᶠ k in atTop,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        Hε k x (fun i => Dυ i x) (μ x) = H x (fun i => Dυ i x) (μ x))
    (hstabDpH : ∀ᶠ k in atTop,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        DpHε k x (fun i => Dυ i x) (μ x) = DpH x (fun i => Dυ i x) (μ x))
    -- Integrability of the two STABILISED (limit-`H`/`D_pH`) integrands at
    -- the per-`k` solution; at the keystone call site these are discharged
    -- from the test-pair Hölder factors `hg1`/`hgGrad`/`hgVal` and the
    -- per-`k` solution `MemLpPer` certs `hm_n`/`hu_n`/`hDu_n`, exactly as in
    -- `limit_passage_existweaksol_htend_combined`.
    (hIA : ∀ k, IntegrableOn
      (fun x =>
        (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (μ x - m_n k x))
      (UnitCube d))
    (hIBC : ∀ k, IntegrableOn
      (fun x =>
        μ x * (DpH x (fun i => Dυ i x) (μ x)
                ⬝ (fun i => Dυ i x - Du_n k i x))
          + (μ x - 1) * (υ x - u_n k x))
      (UnitCube d)) :
    ∀ᶠ k in atTop, 0 ≤
      (∫ x in UnitCube d,
        (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (μ x - m_n k x)
        ∂(volume : Measure (Fin d → ℝ)))
      + (∫ x in UnitCube d,
          μ x * (DpH x (fun j => Dυ j x) (μ x)
                  ⬝ (fun i => Dυ i x - Du_n k i x))
            + (μ x - 1) * (υ x - u_n k x)
        ∂(volume : Measure (Fin d → ℝ)))
      + ε k * gateauxWpPair γBar Dυ υ
          (fun i x => Dυ i x - Du_n k i x) (υ - u_n k) := by
  -- Work eventually, where both stabilisation identities hold.
  filter_upwards [hstabH, hstabDpH] with k hHk hDpHk
  -- The per-`k` regularised non-negativity, unfolded into the explicit
  -- single merged integral plus the `ε_k`-Gateaux remainder (regularised
  -- `H^{ε_k}`, `D_pH^{ε_k}`).
  have hk := hVIeps k
  rw [mfgOperatorEpsPair_pairing_eq (V := V) (H := Hε k) (DpH := DpHε k)
        γBar (ε k) Dυ (Du_n k) μ υ (m_n k) (u_n k)] at hk
  -- (A4) a.e. identify the merged regularised integrand with the merged
  -- STABILISED (limit-`H`/`D_pH`) integrand on the cube.
  have hmergeStab :
      (∫ x in UnitCube d,
          (-(υ x) - Hε k x (fun i => Dυ i x) (μ x) + V x) * (μ x - m_n k x)
            + μ x * (DpHε k x (fun i => Dυ i x) (μ x)
                      ⬝ (fun i => Dυ i x - Du_n k i x))
            + (μ x - 1) * (υ x - u_n k x)
        ∂(volume : Measure (Fin d → ℝ)))
      = ∫ x in UnitCube d,
          (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (μ x - m_n k x)
            + μ x * (DpH x (fun i => Dυ i x) (μ x)
                      ⬝ (fun i => Dυ i x - Du_n k i x))
            + (μ x - 1) * (υ x - u_n k x)
        ∂(volume : Measure (Fin d → ℝ)) := by
    refine setIntegral_congr_ae measurableSet_unitCube ?_
    filter_upwards [(ae_restrict_iff' measurableSet_unitCube).1 hHk,
      (ae_restrict_iff' measurableSet_unitCube).1 hDpHk] with x hxH hxDpH hxmem
    rw [hxH hxmem, hxDpH hxmem]
  -- The merged STABILISED integral splits into the keystone's two integrals.
  have hsplit :
      (∫ x in UnitCube d,
          (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (μ x - m_n k x)
            + μ x * (DpH x (fun i => Dυ i x) (μ x)
                      ⬝ (fun i => Dυ i x - Du_n k i x))
            + (μ x - 1) * (υ x - u_n k x)
        ∂(volume : Measure (Fin d → ℝ)))
      = (∫ x in UnitCube d,
            (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (μ x - m_n k x)
          ∂(volume : Measure (Fin d → ℝ)))
        + (∫ x in UnitCube d,
            μ x * (DpH x (fun j => Dυ j x) (μ x)
                    ⬝ (fun i => Dυ i x - Du_n k i x))
              + (μ x - 1) * (υ x - u_n k x)
          ∂(volume : Measure (Fin d → ℝ))) := by
    rw [← MeasureTheory.integral_add (hIA k) (hIBC k)]
    refine integral_congr_ae ?_
    filter_upwards with x; ring
  -- Identify the regularised Gateaux remainder with `gateauxWpPair`.
  have hGat :
      (∫ x in UnitCube d,
            vecAbsPowMinusTwo γBar (fun i => Dυ i x)
                  * ((fun i => Dυ i x) ⬝ (fun i => Dυ i x - Du_n k i x))
              + absPowMinusTwo γBar (υ x) * (υ x * (υ x - u_n k x))
          ∂(volume : Measure (Fin d → ℝ)))
        = gateauxWpPair γBar Dυ υ
            (fun i x => Dυ i x - Du_n k i x) (υ - u_n k) := by
    rw [gateauxWpPair_pairing_eq γBar Dυ (Du_n k) υ (u_n k)]
  -- Assemble: rewrite `hk` through the stabilisation identification, the
  -- two-integral split, and the Gateaux identification.
  rw [hmergeStab, hsplit, hGat] at hk
  exact hk

/-- **A5e — limit-passage producer for the weak VI** (paper
`eq:existweaksol.delta`, arrows A5a + A5b + A5c + A1 + A4 wired into the
keystone A5d).

Given the limit data `(m, u, Du)` and a per-`ε_k` family of regularised
solutions `(m_n, u_n, Du_n)` plus a decay sequence `ε_k → 0`, suppose
that *for every admissible test pair* `(Dυ, μ, υ)`:

* (A5a/A5b) the fixed Hölder factors are `L^{β̄'}`/`L^{γ̄'}`-regular and
  the sequence fields converge weakly (`WeakConvPairing_universal`)
  `m_n ⇀ m` in `L^{β̄}`, `Du_n · i ⇀ Du i` and `u_n ⇀ u` in `L^{γ̄}`;
* (A5c) the `ε_k`-prefactored γ̄-Laplacian Gateaux remainder is
  uniformly bounded;
* (A1 + A4) the per-`ε_k` right-hand side of `eq:existweaksol.delta`
  *after stabilisation* `H^ε ↦ H`, `D_pH^ε ↦ D_pH`, written explicitly
  as
  ```
  S k = (∫ A_k) + (∫ (B_k + C_k)) + ε_k · R_k,
  ```
  is eventually nonnegative along `k → ∞` (the per-`ε_k` variational
  inequality).

Then the limit pair is a weak solution `IsWeakSolution V H DpH Du m u`.

The `htend` of the keystone is discharged by
`limit_passage_existweaksol_htend_combined`; the `hnn` is the supplied
A1 + A4 eventual nonnegativity; the conclusion is
`limit_passage_to_weak_VI_of_seq`. The per-test-pair regularity / weak
convergence / nonnegativity hypotheses are exactly the deliverables of
the upstream A1d-final family (A1), the weak compactness (A2/A3), the
stabilisation (A4), and the analytic closures (A5a/A5b/A5c). -/
theorem limit_passage_to_weak_VI_of_paperHypotheses
    {βBar βBar' γBar γBar' : ℝ}
    (hpqβ : βBar.HolderConjugate βBar')
    (hpqγ : γBar.HolderConjugate γBar')
    {ε : ℕ → ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    {m_n : ℕ → (Fin d → ℝ) → ℝ}
    {Du_n : ℕ → Fin d → (Fin d → ℝ) → ℝ}
    {u_n : ℕ → (Fin d → ℝ) → ℝ}
    {M : (Fin d → (Fin d → ℝ) → ℝ) → ((Fin d → ℝ) → ℝ) →
          ((Fin d → ℝ) → ℝ) → ℝ}
    (hε_to0 : Tendsto ε atTop (𝓝 0))
    (hm : MemLpPer (d := d) (ENNReal.ofReal βBar) m)
    (hm_n : ∀ k, MemLpPer (d := d) (ENNReal.ofReal βBar) (m_n k))
    (hu : MemLpPer (d := d) (ENNReal.ofReal γBar) u)
    (hu_n : ∀ k, MemLpPer (d := d) (ENNReal.ofReal γBar) (u_n k))
    (hDu : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBar) (Du i))
    (hDu_n : ∀ k i, MemLpPer (d := d) (ENNReal.ofReal γBar) (Du_n k i))
    -- A5a/A5b: per-test-pair fixed Hölder factors.
    (hg1 : ∀ (Dυ : Fin d → (Fin d → ℝ) → ℝ) (μ υ : (Fin d → ℝ) → ℝ),
      IsWeakSolutionTestPair Dυ μ υ →
        MemLpPer (d := d) (ENNReal.ofReal βBar')
          (fun x => -(υ x) - H x (fun i => Dυ i x) (μ x) + V x))
    (hμβ : ∀ (Dυ : Fin d → (Fin d → ℝ) → ℝ) (μ υ : (Fin d → ℝ) → ℝ),
      IsWeakSolutionTestPair Dυ μ υ →
        MemLpPer (d := d) (ENNReal.ofReal βBar) μ)
    (hgGrad : ∀ (Dυ : Fin d → (Fin d → ℝ) → ℝ) (μ υ : (Fin d → ℝ) → ℝ),
      IsWeakSolutionTestPair Dυ μ υ → ∀ i,
        MemLpPer (d := d) (ENNReal.ofReal γBar')
          (fun x => μ x * DpH x (fun j => Dυ j x) (μ x) i))
    (hDυ : ∀ (Dυ : Fin d → (Fin d → ℝ) → ℝ) (μ υ : (Fin d → ℝ) → ℝ),
      IsWeakSolutionTestPair Dυ μ υ → ∀ i,
        MemLpPer (d := d) (ENNReal.ofReal γBar) (Dυ i))
    (hgVal : ∀ (Dυ : Fin d → (Fin d → ℝ) → ℝ) (μ υ : (Fin d → ℝ) → ℝ),
      IsWeakSolutionTestPair Dυ μ υ →
        MemLpPer (d := d) (ENNReal.ofReal γBar') (fun x => μ x - 1))
    (hυ : ∀ (Dυ : Fin d → (Fin d → ℝ) → ℝ) (μ υ : (Fin d → ℝ) → ℝ),
      IsWeakSolutionTestPair Dυ μ υ →
        MemLpPer (d := d) (ENNReal.ofReal γBar) υ)
    -- A5a/A5b: per-test-pair weak convergence certificates.
    (h_weak_m : ∀ (Dυ : Fin d → (Fin d → ℝ) → ℝ) (μ υ : (Fin d → ℝ) → ℝ),
      IsWeakSolutionTestPair Dυ μ υ →
        StationaryMFG.Theorems.SimplePower.Banach.WeakConvPairing_universal
          (d := d) hpqβ m_n m)
    (h_weak_Du : ∀ (Dυ : Fin d → (Fin d → ℝ) → ℝ) (μ υ : (Fin d → ℝ) → ℝ),
      IsWeakSolutionTestPair Dυ μ υ → ∀ i,
        StationaryMFG.Theorems.SimplePower.Banach.WeakConvPairing_universal
          (d := d) hpqγ (fun k => Du_n k i) (Du i))
    (h_weak_u : ∀ (Dυ : Fin d → (Fin d → ℝ) → ℝ) (μ υ : (Fin d → ℝ) → ℝ),
      IsWeakSolutionTestPair Dυ μ υ →
        StationaryMFG.Theorems.SimplePower.Banach.WeakConvPairing_universal
          (d := d) hpqγ u_n u)
    -- A5c: per-test-pair uniform Gateaux-remainder bound.
    (hbdd : ∀ (Dυ : Fin d → (Fin d → ℝ) → ℝ) (μ υ : (Fin d → ℝ) → ℝ),
      IsWeakSolutionTestPair Dυ μ υ → ∀ k,
        |gateauxWpPair γBar Dυ υ
            (fun i x => Dυ i x - Du_n k i x) (υ - u_n k)| ≤ M Dυ μ υ)
    -- A1 + A4: eventual nonnegativity of the stabilised per-`ε_k` RHS.
    (hnn : ∀ (Dυ : Fin d → (Fin d → ℝ) → ℝ) (μ υ : (Fin d → ℝ) → ℝ),
      IsWeakSolutionTestPair Dυ μ υ →
        ∀ᶠ k in atTop, 0 ≤
          (∫ x in UnitCube d,
            (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (μ x - m_n k x)
            ∂(volume : Measure (Fin d → ℝ)))
          + (∫ x in UnitCube d,
              μ x * (DpH x (fun j => Dυ j x) (μ x)
                      ⬝ (fun i => Dυ i x - Du_n k i x))
                + (μ x - 1) * (υ x - u_n k x)
            ∂(volume : Measure (Fin d → ℝ)))
          + ε k * gateauxWpPair γBar Dυ υ
              (fun i x => Dυ i x - Du_n k i x) (υ - u_n k)) :
    IsWeakSolution V H DpH Du m u := by
  -- The per-`ε_k` right-hand side sequence (explicit three-summand form).
  refine limit_passage_to_weak_VI_of_seq (V := V) (H := H) (DpH := DpH)
    (Du := Du) (m := m) (u := u)
    (S := fun Dυ μ υ k =>
      (∫ x in UnitCube d,
        (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (μ x - m_n k x)
        ∂(volume : Measure (Fin d → ℝ)))
      + (∫ x in UnitCube d,
          μ x * (DpH x (fun j => Dυ j x) (μ x)
                  ⬝ (fun i => Dυ i x - Du_n k i x))
            + (μ x - 1) * (υ x - u_n k x)
        ∂(volume : Measure (Fin d → ℝ)))
      + ε k * gateauxWpPair γBar Dυ υ
          (fun i x => Dυ i x - Du_n k i x) (υ - u_n k))
    ?_ ?_
  · -- `hnn`: the A1 + A4 eventual nonnegativity, verbatim.
    intro Dυ μ υ hadm
    exact hnn Dυ μ υ hadm
  · -- `htend`: the recombined A5a/A5b/A5c convergence.
    intro Dυ μ υ hadm
    exact limit_passage_existweaksol_htend_combined (d := d)
      hpqβ hpqγ
      (hg1 Dυ μ υ hadm) (hμβ Dυ μ υ hadm) hm_n hm (h_weak_m Dυ μ υ hadm)
      (hgGrad Dυ μ υ hadm) (hDυ Dυ μ υ hadm) hDu_n hDu
      (h_weak_Du Dυ μ υ hadm)
      (hgVal Dυ μ υ hadm) (hυ Dυ μ υ hadm) hu_n hu (h_weak_u Dυ μ υ hadm)
      hε_to0 (hbdd Dυ μ υ hadm)

/-! ## B2a — closed producers for the keystone's regularity-derived
    Hölder factors

The keystone `limit_passage_to_weak_VI_of_paperHypotheses` consumes six
per-test-pair Hölder factors. Four of them are *regularity-derived*:
they follow purely from the test-pair `Lᵖ` regularity together with the
exponent ordering `γ̄' ≤ β̄` (paper `eq:gamma`), with no use of the
Hamiltonian growth.  These are produced here as closed lemmas in the
exact shapes consumed by the keystone.

The two remaining factors (`hg1`, the HJB multiplier, and `hgGrad`, the
flux multiplier) and the uniform Gateaux-remainder bound `hbdd` are the
genuinely Hamiltonian-analytic deliverables; they are split off to the
follow-up child (see the task `## Blocker` / split note) because the
weak-growth bundle `HypothesisWeakGrowth` only supplies an upper bound on
`H(x, 0, m)` (paper `eq:assH.upper.weak`), not the polynomial upper bound
on `H(x, p, m)` at general momentum `p` that the dominator route
`g_memLp_betaBar'_at_test` requires. -/

/-- **B2a / factor `hgVal`.** The mass-defect multiplier `μ − 1` lies in
`L^{γ̄'}_per`, via the `L^{β̄} ↪ L^{γ̄'}` inclusion on the finite-measure
torus (paper `eq:gamma`, `γ̄' ≤ β̄`).  This is the per-test-pair wrapper
around `Hamiltonian.μMinusOne_memLp_of_betaBar`. -/
theorem keystone_hgVal_of_regularity
    {βBar γBar' : ℝ}
    {μ : (Fin d → ℝ) → ℝ}
    (hμ_reg : MemLpPer (d := d) (ENNReal.ofReal βBar) μ)
    (hexp : ENNReal.ofReal γBar' ≤ ENNReal.ofReal βBar)
    (hβBar_top : ENNReal.ofReal βBar ≠ ⊤) :
    MemLpPer (d := d) (ENNReal.ofReal γBar') (fun x => μ x - 1) :=
  StationaryMFG.Hamiltonian.μMinusOne_memLp_of_betaBar
    (d := d) μ hμ_reg hexp hβBar_top

/-! ## B2a1 — Hamiltonian-analytic keystone factors

The remaining two of the three B2a1 deliverables that *are* derivable
from the accepted weak-growth set:

* `hgGrad` — the flux multiplier `μ · D_pH(x, Dυ, μ) i` lies in
  `L^{γ̄'}_per`, via the weak-growth `D_pH`-bound `f` (continuous, hence
  bounded on the compact range of `(Dυ(x), μ(x))`) and the test-pair
  `L^∞` data;
* `hbdd` — the uniform-in-`k` Gateaux remainder bound, a thin wrapper of
  `gateauxWpPair_uniform_bound_per_triple`.

The third deliverable `hg1` (the `|H(x, Dυ, μ)|`-side `L^{β̄'}` factor)
is **not** derivable from the accepted set: weak growth supplies an upper
bound on `H` only at `p = 0` (`eq:assH.upper.weak`) and a lower bound at
general `p` (`eq:assH.lower.weak`); the general-`p` upper bound that
controls `H(x, Dυ, μ)` from above is obtained in the paper through the
FTC slice `H(x, p, m) = H(x, 0, m) + ∫₀¹ D_pH(x, t·p, m)·p dt`
(differentiability of `H` in `p` with derivative `D_pH`), which is the
content of the (forbidden) `HypothesisHepsilonFtcSlice` clause — stated
there for the regularised pair, with no accepted base-pair analogue.
`hg1` is therefore split off to a follow-up that must decide on the
minimal paper-faithful rider (a base-pair H-side FTC slice, i.e. an
`onH.regularity`-level differentiability clause). -/

/-- **B2a1 / factor `hgGrad`** (flux multiplier).

The flux coordinate `x ↦ μ(x) · D_pH(x, Dυ(x), μ(x)) i` lies in
`L^{γ̄'}_per`.  Under the weak-growth bound `‖D_pH(x, p, m)‖ ≤ f(p, m)`
(with `f` continuous on `{m > 0}`), the test-pair `L^∞` data
(`‖Dυ(x)‖ ≤ R`, `μ(x) ≤ b` a.e.) together with the test-pair lower bound
`a ≤ μ(x)` for some `a > 0`, the argument `(Dυ(x), μ(x))` ranges in the
compact box `closedBall 0 R × Icc a b ⊆ {m > 0}`, on which `f` is
bounded.  Hence the flux is bounded a.e. by the constant `b · sup_K f`,
so it lies in `L^q_per` for every `q` on the finite-measure cube.

The flux's a.e.-strong measurability is threaded as a hypothesis,
mirroring `Hamiltonian.flux_memLp_gammaBar'_at_test`. -/
theorem keystone_hgGrad_of_weakGrowth
    {γBar' R a b : ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    {μ : (Fin d → ℝ) → ℝ}
    {Dυ : Fin d → (Fin d → ℝ) → ℝ}
    (i : Fin d)
    (ha_pos : 0 < a)
    (hμ_lower : ∀ x, a ≤ μ x)
    (hμ_upper : ∀ᵐ x ∂(volume.restrict (UnitCube d)), μ x ≤ b)
    (hDυ_bdd : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ‖fun j => Dυ j x‖ ≤ R)
    (hF_meas :
      AEStronglyMeasurable
        (fun x => μ x * DpH x (fun j => Dυ j x) (μ x) i)
        (Measure.restrict volume (UnitCube d))) :
    MemLpPer (d := d) (ENNReal.ofReal γBar')
      (fun x => μ x * DpH x (fun j => Dυ j x) (μ x) i) := by
  classical
  -- `R ≥ 0` (it bounds a norm a.e.; and the cube has positive measure so
  -- such an `x` exists — but we only need `R ≥ 0` to build the box, which
  -- holds since `‖·‖ ≥ 0 ≤ R` a.e. forces `R ≥ 0` once the set is
  -- nonempty; to avoid that subtlety we take `max R 0`).
  set R' : ℝ := max R 0 with hR'_def
  have hR'_nn : 0 ≤ R' := le_max_right _ _
  have hR_le_R' : R ≤ R' := le_max_left _ _
  -- The compact box `K = closedBall 0 R' × Icc a b ⊆ {m > 0}`.
  set K : Set ((Fin d → ℝ) × ℝ) :=
    (Metric.closedBall (0 : Fin d → ℝ) R') ×ˢ Set.Icc a b with hK_def
  have hK_compact : IsCompact K := by
    rw [hK_def]
    exact (isCompact_closedBall _ _).prod isCompact_Icc
  have hK_sub : K ⊆ {pm : (Fin d → ℝ) × ℝ | 0 < pm.2} := by
    intro pm hpm
    rw [hK_def] at hpm
    have hm : pm.2 ∈ Set.Icc a b := hpm.2
    exact lt_of_lt_of_le ha_pos hm.1
  -- `f` is bounded above on the compact box `K`.
  have hf_contK : ContinuousOn
      (fun pm : (Fin d → ℝ) × ℝ => hweak.f pm.1 pm.2) K :=
    hweak.hf_continuous.mono hK_sub
  obtain ⟨Cf, hCf⟩ := hK_compact.bddAbove_image hf_contK
  -- The dominator constant `b · max Cf 0` (nonneg).
  set Cf' : ℝ := max Cf 0 with hCf'_def
  have hCf'_nn : 0 ≤ Cf' := le_max_right _ _
  have hCf_le : Cf ≤ Cf' := le_max_left _ _
  -- `b ≥ a > 0` so `b > 0`: there is an `x` with `μ x ≤ b` and `a ≤ μ x`.
  -- We only need `b ≥ 0` for the dominator; derive `0 ≤ b` from
  -- `0 < a ≤ μ x ≤ b` (using that the upper bound holds a.e. and the
  -- lower bound holds everywhere, so on the a.e. set `a ≤ b`).
  -- For the `MemLp.of_bound` constant we use `Dom := b * Cf'` with `b`
  -- replaced by `max b 0` to guarantee nonnegativity unconditionally.
  set b' : ℝ := max b 0 with hb'_def
  have hb'_nn : 0 ≤ b' := le_max_right _ _
  have hb_le : b ≤ b' := le_max_left _ _
  set Dom : ℝ := b' * Cf' with hDom_def
  have hDom_nn : 0 ≤ Dom := mul_nonneg hb'_nn hCf'_nn
  -- Reduce to `MemLp.of_bound` for the cube-restricted measure.
  refine MemLp.toMemLpPer ?_
  refine MeasureTheory.MemLp.of_bound hF_meas Dom ?_
  -- The a.e. pointwise bound `|flux| ≤ Dom`.
  filter_upwards [hweak.DpH_upper, hμ_upper, hDυ_bdd] with x hxDpH hxμ hxDυ
  have hμpos : 0 < μ x := lt_of_lt_of_le ha_pos (hμ_lower x)
  -- `(Dυ x, μ x) ∈ K`.
  have hmemK : ((fun j => Dυ j x), μ x) ∈ K := by
    rw [hK_def]
    refine ⟨?_, ?_⟩
    · -- `Dυ x ∈ closedBall 0 R'`.
      rw [Metric.mem_closedBall, dist_zero_right]
      exact le_trans hxDυ hR_le_R'
    · -- `μ x ∈ Icc a b`.
      exact ⟨hμ_lower x, hxμ⟩
  -- `f (Dυ x) (μ x) ≤ Cf'`.
  have hf_le : hweak.f (fun j => Dυ j x) (μ x) ≤ Cf' :=
    le_trans (hCf ⟨_, hmemK, rfl⟩) hCf_le
  -- `f` is nonneg there since it dominates a norm `‖DpH ...‖ ≥ 0`.
  have hDpH_bound : ‖DpH x (fun j => Dυ j x) (μ x)‖
      ≤ hweak.f (fun j => Dυ j x) (μ x) :=
    hxDpH (fun j => Dυ j x) (μ x) hμpos
  have hf_nn : 0 ≤ hweak.f (fun j => Dυ j x) (μ x) :=
    le_trans (norm_nonneg _) hDpH_bound
  -- Coordinate bound: `|DpH x (Dυ x) (μ x) i| ≤ ‖DpH x (Dυ x) (μ x)‖`.
  have hcoord : |DpH x (fun j => Dυ j x) (μ x) i|
      ≤ ‖DpH x (fun j => Dυ j x) (μ x)‖ := by
    rw [← Real.norm_eq_abs]
    exact norm_le_pi_norm (DpH x (fun j => Dυ j x) (μ x)) i
  -- Combine: `|μ x * DpH .. i| = |μ x| * |DpH .. i| ≤ b' * Cf' = Dom`.
  rw [Real.norm_eq_abs, abs_mul]
  have hμabs : |μ x| = μ x := abs_of_nonneg hμpos.le
  rw [hμabs]
  calc μ x * |DpH x (fun j => Dυ j x) (μ x) i|
      ≤ μ x * ‖DpH x (fun j => Dυ j x) (μ x)‖ :=
        mul_le_mul_of_nonneg_left hcoord hμpos.le
    _ ≤ μ x * hweak.f (fun j => Dυ j x) (μ x) :=
        mul_le_mul_of_nonneg_left hDpH_bound hμpos.le
    _ ≤ b' * Cf' := by
        apply mul_le_mul
        · exact le_trans hxμ hb_le
        · exact hf_le
        · exact hf_nn
        · exact hb'_nn

/-- **B2a2 / factor `hg1`** (HJB multiplier — the `H`-value `L^{β̄'}`
factor), via the **internal base-pair FTC slice** (Path 0, no new rider).

The HJB multiplier `x ↦ -υ(x) - H(x, Dυ(x), μ(x)) + V(x)` lies in
`L^{β̄'}_per`.  The only genuinely Hamiltonian-analytic content is a
two-sided bound on the `H`-value `H(x, Dυ(x), μ(x))`:

* the **lower** bound is the weak-growth `lower` clause
  (`eq:assH.lower.weak`), bounded below on the `L^∞` test slice;
* the **upper** bound is obtained from the FTC slice identity
  `H(x,p,m) = H(x,0,m) + ∫₀¹ D_pH(x,t·p,m)·p dt`, derived *internally*
  from the **already-accepted** rider `HypothesisHpDifferentiable`
  (`hasFDerivAt_H_p`, giving the envelope's `hderiv` input) and the
  `RegularityH` continuity of `p ↦ D_pH(x,p,m)` (the envelope's `hG`
  input), through
  `InfimalConvolution.ftc_slice_of_hasFDerivAt_continuous_gradient`.
  Combined with the `p = 0` upper bound (`eq:assH.upper.weak`) and the
  `D_pH`-bound `f` (continuous, bounded on the compact box
  `closedBall 0 R × Icc a b ⊆ {m > 0}`), this yields
  `H(x,Dυ,μ) ≤ (-(μ^β)/C + C) + (1 + 2d·R)·sup_K f` a.e.

Together with the `L^∞` test/data bounds on `υ` and `V`, the whole
multiplier is bounded a.e. by a constant, hence lies in `L^q_per` for
every `q` on the finite-measure cube.  **No new rider.**

The multiplier's a.e.-strong measurability is threaded as a hypothesis,
mirroring `keystone_hgGrad_of_weakGrowth`. -/
theorem keystone_hg1_of_weakGrowth
    {βBar' R a b Cυ CV : ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {V : (Fin d → ℝ) → ℝ}
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hdiff : HypothesisHpDifferentiable (d := d) H DpH)
    {μ υ : (Fin d → ℝ) → ℝ}
    {Dυ : Fin d → (Fin d → ℝ) → ℝ}
    (ha_pos : 0 < a)
    (hμ_lower : ∀ x, a ≤ μ x)
    (hμ_upper : ∀ᵐ x ∂(volume.restrict (UnitCube d)), μ x ≤ b)
    (hDυ_bdd : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ‖fun j => Dυ j x‖ ≤ R)
    (hυ_bdd : ∀ᵐ x ∂(volume.restrict (UnitCube d)), |υ x| ≤ Cυ)
    (hV_bdd : ∀ᵐ x ∂(volume.restrict (UnitCube d)), |V x| ≤ CV)
    (hG_meas :
      AEStronglyMeasurable
        (fun x => -(υ x) - H x (fun j => Dυ j x) (μ x) + V x)
        (Measure.restrict volume (UnitCube d))) :
    MemLpPer (d := d) (ENNReal.ofReal βBar')
      (fun x => -(υ x) - H x (fun j => Dυ j x) (μ x) + V x) := by
  classical
  -- Normalised nonnegative bounds (mirrors `keystone_hgGrad_of_weakGrowth`).
  set R' : ℝ := max R 0 with hR'_def
  have hR'_nn : 0 ≤ R' := le_max_right _ _
  have hR_le_R' : R ≤ R' := le_max_left _ _
  set b' : ℝ := max b 0 with hb'_def
  have hb'_nn : 0 ≤ b' := le_max_right _ _
  have hb_le : b ≤ b' := le_max_left _ _
  -- Compact box `K = closedBall 0 R' × Icc a b' ⊆ {m > 0}`.
  set K : Set ((Fin d → ℝ) × ℝ) :=
    (Metric.closedBall (0 : Fin d → ℝ) R') ×ˢ Set.Icc a b' with hK_def
  have hK_compact : IsCompact K := by
    rw [hK_def]; exact (isCompact_closedBall _ _).prod isCompact_Icc
  have hK_sub : K ⊆ {pm : (Fin d → ℝ) × ℝ | 0 < pm.2} := by
    intro pm hpm
    rw [hK_def] at hpm
    exact lt_of_lt_of_le ha_pos hpm.2.1
  -- `f` bounded above on `K`.
  have hf_contK : ContinuousOn
      (fun pm : (Fin d → ℝ) × ℝ => hweak.f pm.1 pm.2) K :=
    hweak.hf_continuous.mono hK_sub
  obtain ⟨Cf, hCf⟩ := hK_compact.bddAbove_image hf_contK
  set Cf' : ℝ := max Cf 0 with hCf'_def
  have hCf'_nn : 0 ≤ Cf' := le_max_right _ _
  have hCf_le : Cf ≤ Cf' := le_max_left _ _
  -- The constant dominator for the `H`-value (both sides):
  -- `|H(x,Dυ,μ)| ≤ CH` where `CH` collects the upper and lower bounds.
  -- Upper: `-(μ^β)/C + C + (1 + 2 d R') · Cf'`.
  -- Lower (negated, as upper bound on `-H`): `C·(b'^β + 1) - 0`.
  set CH : ℝ :=
    (hweak.C + 3 * (d : ℝ) * Cf' * R')
      + hweak.C * (b' ^ hweak.β + 1) with hCH_def
  -- The total dominator `Dom = Cυ' + CH + CV'`.
  set Cυ' : ℝ := max Cυ 0 with hCυ'_def
  set CV' : ℝ := max CV 0 with hCV'_def
  set Dom : ℝ := Cυ' + CH + CV' with hDom_def
  refine MemLp.toMemLpPer ?_
  refine MeasureTheory.MemLp.of_bound hG_meas Dom ?_
  -- The a.e. pointwise bound `|(-υ - H + V) x| ≤ Dom`.
  filter_upwards [hweak.upper, hweak.lower, hweak.DpH_upper,
      hdiff.hasFDerivAt_H_p, hweak.continuous_DpH_pm,
      hμ_upper, hDυ_bdd, hυ_bdd, hV_bdd]
    with x hxUpper hxLower hxDpH hxFD hxCont hxμ hxDυ hxυ hxV
  have hμpos : 0 < μ x := lt_of_lt_of_le ha_pos (hμ_lower x)
  -- Set `p := Dυ x`, `m := μ x`.
  set p : Fin d → ℝ := fun j => Dυ j x with hp_def
  -- `‖p‖ ≤ R'`.
  have hp_le : ‖p‖ ≤ R' := le_trans hxDυ hR_le_R'
  have hp_nn : 0 ≤ ‖p‖ := norm_nonneg _
  -- The base-pair gradient field and value section at this `x, μ x`.
  set F : (Fin d → ℝ) → ℝ := fun q => H x q (μ x) with hF_def
  set Gfield : (Fin d → ℝ) → (Fin d → ℝ) :=
    fun q => DpH x q (μ x) with hGfield_def
  -- Envelope input 1: `hderiv` from `HypothesisHpDifferentiable`.
  have hderiv : ∀ q, HasFDerivAt F (dotCLMHam (Gfield q)) q := by
    intro q
    exact hxFD q (μ x) hμpos
  -- Envelope input 2: `hG` continuity of `q ↦ DpH x q (μ x)`.
  have hGcont : Continuous Gfield := by
    have himg : ∀ q : Fin d → ℝ,
        (q, μ x) ∈ {pm : (Fin d → ℝ) × ℝ | 0 < pm.2} := fun q => hμpos
    have hcomp_cont : Continuous (fun q : Fin d → ℝ => (q, μ x)) :=
      continuous_id.prodMk continuous_const
    exact hxCont.comp_continuous hcomp_cont himg
  -- The FTC slice identity at `p`.
  have hftc := ftc_slice_of_hasFDerivAt_continuous_gradient
    (F := F) (G := Gfield) hderiv hGcont p
  -- Rearrange: `F p = F 0 + Gfield p ⬝ p - ∫₀¹ (Gfield p - Gfield (t•p)) ⬝ p`.
  -- `hftc : Gfield p ⬝ p - (F p - F 0) = ∫ t in 0..1, (Gfield p - Gfield (t•p)) ⬝ p`.
  -- Bound on the box-radius for arguments `t • p`, `t ∈ [0,1]`.
  -- `f` bound at `(p, μ x)` and at `(t • p, μ x)`.
  have hf_box : ∀ q : Fin d → ℝ, ‖q‖ ≤ R' →
      hweak.f q (μ x) ≤ Cf' := by
    intro q hq
    have hmem : (q, μ x) ∈ K := by
      rw [hK_def]
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_closedBall, dist_zero_right]; exact hq
      · exact ⟨hμ_lower x, le_trans hxμ hb_le⟩
    exact le_trans (hCf ⟨_, hmem, rfl⟩) hCf_le
  -- `‖DpH x q (μ x)‖ ≤ Cf'` for `‖q‖ ≤ R'`.
  have hDpH_box : ∀ q : Fin d → ℝ, ‖q‖ ≤ R' →
      ‖DpH x q (μ x)‖ ≤ Cf' :=
    fun q hq => le_trans (hxDpH q (μ x) hμpos) (hf_box q hq)
  -- Coordinate Cauchy–Schwarz: `|v ⬝ w| ≤ d · ‖v‖ · ‖w‖`.
  have habs_dot : ∀ v w : Fin d → ℝ, |v ⬝ w| ≤ (d : ℝ) * ‖v‖ * ‖w‖ := by
    intro v w
    have hexpand : |v ⬝ w| ≤ ∑ i : Fin d, |v i * w i| := by
      unfold euclideanDot
      exact Finset.abs_sum_le_sum_abs _ _
    refine hexpand.trans ?_
    have hterm : ∀ i : Fin d, |v i * w i| ≤ ‖v‖ * ‖w‖ := by
      intro i
      rw [abs_mul]
      have hv : |v i| ≤ ‖v‖ := by
        have := norm_le_pi_norm v i; simpa [Real.norm_eq_abs] using this
      have hw : |w i| ≤ ‖w‖ := by
        have := norm_le_pi_norm w i; simpa [Real.norm_eq_abs] using this
      calc |v i| * |w i|
          ≤ ‖v‖ * |w i| := mul_le_mul_of_nonneg_right hv (abs_nonneg _)
        _ ≤ ‖v‖ * ‖w‖ := mul_le_mul_of_nonneg_left hw (norm_nonneg _)
    refine (Finset.sum_le_sum (fun i _ => hterm i)).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact le_of_eq (by ring)
  -- Bound on `|Gfield p ⬝ p|`.
  have hdot1 : |Gfield p ⬝ p| ≤ (d : ℝ) * Cf' * R' := by
    refine (habs_dot (Gfield p) p).trans ?_
    have h1 : ‖Gfield p‖ ≤ Cf' := hDpH_box p hp_le
    have h2 : ‖p‖ ≤ R' := hp_le
    apply mul_le_mul
    · apply mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg d)
    · exact h2
    · exact hp_nn
    · positivity
  -- Bound on the FTC-slice integral.
  have hint_bound :
      |∫ t in (0:ℝ)..1, ((Gfield p - Gfield (t • p)) ⬝ p)|
        ≤ 2 * (d : ℝ) * Cf' * R' := by
    have hconst : ∀ t ∈ Set.uIoc (0:ℝ) 1,
        ‖(Gfield p - Gfield (t • p)) ⬝ p‖ ≤ 2 * (d : ℝ) * Cf' * R' := by
      intro t ht
      rw [Real.norm_eq_abs]
      refine (habs_dot (Gfield p - Gfield (t • p)) p).trans ?_
      -- `‖t • p‖ ≤ R'`.
      have htp_le : ‖t • p‖ ≤ R' := by
        rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
        have ht0 : 0 ≤ t := le_of_lt ht.1
        have ht1 : t ≤ 1 := ht.2
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
        have hstep : t * ‖p‖ ≤ ‖p‖ := by
          calc t * ‖p‖ ≤ 1 * ‖p‖ := mul_le_mul_of_nonneg_right ht1 hp_nn
            _ = ‖p‖ := one_mul _
        exact le_trans hstep hp_le
      have hsub : ‖Gfield p - Gfield (t • p)‖ ≤ 2 * Cf' := by
        calc ‖Gfield p - Gfield (t • p)‖
            ≤ ‖Gfield p‖ + ‖Gfield (t • p)‖ := norm_sub_le _ _
          _ ≤ Cf' + Cf' := add_le_add (hDpH_box p hp_le) (hDpH_box _ htp_le)
          _ = 2 * Cf' := by ring
      have hstep : (d : ℝ) * ‖Gfield p - Gfield (t • p)‖ * ‖p‖
          ≤ (d : ℝ) * (2 * Cf') * R' := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hsub (Nat.cast_nonneg d)
        · exact hp_le
        · exact hp_nn
        · positivity
      have heq : (d : ℝ) * (2 * Cf') * R' = 2 * (d : ℝ) * Cf' * R' := by ring
      rw [← heq]; exact hstep
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0:ℝ)) (b := 1) (C := 2 * (d : ℝ) * Cf' * R')
      (f := fun t => (Gfield p - Gfield (t • p)) ⬝ p) hconst
    rw [Real.norm_eq_abs] at this
    simpa using this
  -- Upper bound on `F p = H x p (μ x)`.
  -- `F p = F 0 + Gfield p ⬝ p - ∫ ...`.
  have hFp_eq : F p = F 0 + Gfield p ⬝ p
      - ∫ t in (0:ℝ)..1, ((Gfield p - Gfield (t • p)) ⬝ p) := by
    have := hftc
    linarith [this]
  -- Upper bound on `F 0 = H x 0 (μ x)`.
  have hF0_le : F 0 ≤ -(μ x ^ hweak.β) / hweak.C + hweak.C := by
    have h := hxUpper (μ x) hμpos
    simpa [hF_def] using h
  -- Now bound `F p` above.
  have hFp_upper :
      F p ≤ (-(μ x ^ hweak.β) / hweak.C + hweak.C)
        + (d : ℝ) * Cf' * R' + 2 * (d : ℝ) * Cf' * R' := by
    rw [hFp_eq]
    have h1 : Gfield p ⬝ p ≤ (d : ℝ) * Cf' * R' :=
      le_trans (le_abs_self _) hdot1
    have h2 : -(∫ t in (0:ℝ)..1, ((Gfield p - Gfield (t • p)) ⬝ p))
        ≤ 2 * (d : ℝ) * Cf' * R' :=
      le_trans (neg_le_abs _) hint_bound
    linarith [hF0_le, h1, h2]
  -- Lower bound on `F p` from weak growth `lower`.
  have hFp_lower : F p ≥ (‖p‖ ^ hweak.α) / hweak.C
      - hweak.C * (μ x ^ hweak.β + 1) := by
    have h := hxLower p (μ x) hμpos
    simpa [hF_def] using h
  -- Convert both bounds into `|H x p (μ x)| ≤ CH`.
  have hμβ_nn : 0 ≤ μ x ^ hweak.β :=
    Real.rpow_nonneg hμpos.le _
  have hμβ_le : μ x ^ hweak.β ≤ b' ^ hweak.β := by
    apply Real.rpow_le_rpow hμpos.le (le_trans hxμ hb_le) hweak.hβ.le
  have hpα_nn : 0 ≤ ‖p‖ ^ hweak.α := Real.rpow_nonneg hp_nn _
  have hCpos := hweak.hC
  -- Nonnegativity of the two summands of `CH`.
  have hgradCH_nn : 0 ≤ 3 * (d : ℝ) * Cf' * R' := by positivity
  have hCC_nn : 0 ≤ hweak.C * (b' ^ hweak.β + 1) := by positivity
  have habsH : |F p| ≤ CH := by
    rw [abs_le]
    constructor
    · -- `-CH ≤ F p`: from the lower bound `F p ≥ -C(b'^β+1)`.
      have hlow : (‖p‖ ^ hweak.α) / hweak.C - hweak.C * (μ x ^ hweak.β + 1)
          ≥ -(hweak.C * (b' ^ hweak.β + 1)) := by
        have hpos : 0 ≤ (‖p‖ ^ hweak.α) / hweak.C :=
          div_nonneg hpα_nn hCpos.le
        have hmono : hweak.C * (μ x ^ hweak.β + 1)
            ≤ hweak.C * (b' ^ hweak.β + 1) := by
          apply mul_le_mul_of_nonneg_left _ hCpos.le
          linarith [hμβ_le]
        linarith
      -- `CH ≥ C(b'^β+1)` since the gradient summand and `C` are nonneg.
      have hCH_ge : CH ≥ hweak.C * (b' ^ hweak.β + 1) := by
        rw [hCH_def]; linarith [hgradCH_nn, hCpos.le]
      linarith [hFp_lower, hlow]
    · -- `F p ≤ CH`: from the upper bound `F p ≤ C + 3 d Cf' R'`.
      have hUB : (-(μ x ^ hweak.β) / hweak.C + hweak.C)
          + (d : ℝ) * Cf' * R' + 2 * (d : ℝ) * Cf' * R' ≤ CH := by
        rw [hCH_def]
        have hnegterm : -(μ x ^ hweak.β) / hweak.C ≤ 0 := by
          apply div_nonpos_of_nonpos_of_nonneg _ hCpos.le
          linarith [hμβ_nn]
        nlinarith [hnegterm, hCC_nn]
      exact le_trans hFp_upper hUB
  -- Assemble `|(-υ - H + V) x| ≤ Cυ' + CH + CV' = Dom`.
  have hCυ_le : Cυ ≤ Cυ' := le_max_left _ _
  have hCV_le : CV ≤ CV' := le_max_left _ _
  have hυ_le : |υ x| ≤ Cυ' := le_trans hxυ hCυ_le
  have hV_le : |V x| ≤ CV' := le_trans hxV hCV_le
  -- Bounds on the three summands, expressed via `abs_le`.
  have hHabs : |H x p (μ x)| ≤ CH := by
    have : |H x p (μ x)| = |F p| := by rw [hF_def]
    rw [this]; exact habsH
  have hυb := abs_le.mp hυ_le
  have hVb := abs_le.mp hV_le
  have hHb := abs_le.mp hHabs
  rw [Real.norm_eq_abs, abs_le]
  refine ⟨?_, ?_⟩
  · -- `-Dom ≤ -(υ x) - H x p (μ x) + V x`.
    rw [hDom_def]; linarith [hυb.1, hυb.2, hVb.1, hVb.2, hHb.1, hHb.2]
  · -- `-(υ x) - H x p (μ x) + V x ≤ Dom`.
    rw [hDom_def]; linarith [hυb.1, hυb.2, hVb.1, hVb.2, hHb.1, hHb.2]

/-- **B2c / factor `hg1` with `V ∈ L^{β̄'}` (paper-faithful potential).**

Variant of `keystone_hg1_of_weakGrowth` that takes the potential in
`L^{β̄'}_per` — exactly the paper hypothesis `V ∈ L^{β̄'}(𝕋^d)` of
`thm:main-weak.power.growth` — instead of an `L^∞` bound on `V`.  The
`H`-value/test-data part `x ↦ -υ(x) - H(x, Dυ(x), μ(x))` is bounded a.e.
by a constant (the content of `keystone_hg1_of_weakGrowth`, applied with
the zero potential), hence lies in `L^∞ ⊆ L^{β̄'}` on the finite-measure
cube; adding `V ∈ L^{β̄'}` keeps the whole multiplier in `L^{β̄'}`.

This removes the spurious `V ∈ L^∞` over-strengthening: the keystone now
consumes the potential at the paper exponent `β̄'`. -/
theorem keystone_hg1_of_weakGrowth_VLp
    {βBar' R a b Cυ : ℝ} (hβBar'_pos : 0 < βBar')
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {V : (Fin d → ℝ) → ℝ}
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hdiff : HypothesisHpDifferentiable (d := d) H DpH)
    {μ υ : (Fin d → ℝ) → ℝ}
    {Dυ : Fin d → (Fin d → ℝ) → ℝ}
    (ha_pos : 0 < a)
    (hμ_lower : ∀ x, a ≤ μ x)
    (hμ_upper : ∀ᵐ x ∂(volume.restrict (UnitCube d)), μ x ≤ b)
    (hDυ_bdd : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ‖fun j => Dυ j x‖ ≤ R)
    (hυ_bdd : ∀ᵐ x ∂(volume.restrict (UnitCube d)), |υ x| ≤ Cυ)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBar') V)
    (hG_meas :
      AEStronglyMeasurable
        (fun x => -(υ x) - H x (fun j => Dυ j x) (μ x))
        (Measure.restrict volume (UnitCube d))) :
    MemLpPer (d := d) (ENNReal.ofReal βBar')
      (fun x => -(υ x) - H x (fun i => Dυ i x) (μ x) + V x) := by
  -- The `υ`/`H` part is bounded a.e. by a constant, via the existing
  -- `keystone_hg1_of_weakGrowth` instantiated at the zero potential.
  have hbase0 : MemLpPer (d := d) (ENNReal.ofReal βBar')
      (fun x => -(υ x) - H x (fun j => Dυ j x) (μ x) + (0 : ℝ)) := by
    refine keystone_hg1_of_weakGrowth (βBar' := βBar') (R := R) (a := a)
      (b := b) (Cυ := Cυ) (CV := 0) hweak hdiff ha_pos hμ_lower hμ_upper
      hDυ_bdd hυ_bdd ?_ ?_
    · filter_upwards with x; simp
    · simpa using hG_meas
  -- Drop the `+ 0`.
  have hbase : MemLpPer (d := d) (ENNReal.ofReal βBar')
      (fun x => -(υ x) - H x (fun j => Dυ j x) (μ x)) := by
    have hfun : (fun x => -(υ x) - H x (fun j => Dυ j x) (μ x) + (0 : ℝ))
        = (fun x => -(υ x) - H x (fun j => Dυ j x) (μ x)) := by
      funext x; ring
    rwa [hfun] at hbase0
  -- Add the paper-exponent potential `V ∈ L^{β̄'}`.
  exact hbase.add hV

/-- **B2a1 / bound `hbdd`** (uniform Gateaux remainder bound).

Thin wrapper of
`SimplePower.Banach.gateauxWpPair_uniform_bound_per_triple`: given the
four integrability certificates for the test/sequence fields and the
four uniform-in-`k` integral upper bounds `Aυ, Au, ADυ, ADu`, the
`γ̄`-Laplacian Gateaux remainder is bounded by their sum.  The sum is the
uniform constant `M Dυ μ υ` consumed by the keystone (the `μ` argument
is carried only to mirror the per-test-triple shape). -/
theorem keystone_hbdd_of_integralBounds
    {γBar : ℝ} (hγ : 1 ≤ γBar)
    {μ υ : (Fin d → ℝ) → ℝ}
    {Dυ Du : Fin d → (Fin d → ℝ) → ℝ}
    {u : (Fin d → ℝ) → ℝ}
    {Aυ Au ADυ ADu : ℝ}
    (hInt_DυDυ : Integrable (fun x : Fin d → ℝ =>
        ((fun i => Dυ i x) ⬝ (fun i => Dυ i x)) ^ (γBar / 2))
        (volume.restrict (UnitCube d)))
    (hInt_DυmDu : Integrable (fun x : Fin d → ℝ =>
        ((fun i => Dυ i x - Du i x) ⬝ (fun i => Dυ i x - Du i x))
          ^ (γBar / 2))
        (volume.restrict (UnitCube d)))
    (hInt_υ : Integrable (fun x : Fin d → ℝ => |υ x| ^ γBar)
        (volume.restrict (UnitCube d)))
    (hInt_υmu : Integrable (fun x : Fin d → ℝ => |υ x - u x| ^ γBar)
        (volume.restrict (UnitCube d)))
    (hAυ : ∫ x in UnitCube d, |υ x| ^ γBar
              ∂(volume : Measure (Fin d → ℝ)) ≤ Aυ)
    (hAu : ∫ x in UnitCube d, |υ x - u x| ^ γBar
              ∂(volume : Measure (Fin d → ℝ)) ≤ Au)
    (hADυ : ∫ x in UnitCube d,
              ((fun i => Dυ i x) ⬝ (fun i => Dυ i x)) ^ (γBar / 2)
              ∂(volume : Measure (Fin d → ℝ)) ≤ ADυ)
    (hADu : ∫ x in UnitCube d,
              ((fun i => Dυ i x - Du i x) ⬝ (fun i => Dυ i x - Du i x))
                ^ (γBar / 2)
              ∂(volume : Measure (Fin d → ℝ)) ≤ ADu) :
    |gateauxWpPair γBar Dυ υ
        (fun i x => Dυ i x - Du i x) (υ - u)|
      ≤ Aυ + Au + ADυ + ADu :=
  StationaryMFG.Theorems.SimplePower.Banach.gateauxWpPair_uniform_bound_per_triple
    (d := d) γBar hγ μ υ Dυ Du u Aυ Au ADυ ADu
    hInt_DυDυ hInt_DυmDu hInt_υ hInt_υmu hAυ hAu hADυ hADu

/-! ## C2 — closed full-quantifier `hbdd` from the A2 uniform control

The keystone's seventh input `hbdd` (consumed by
`hWeakVI_of_sharedExtraction` / `H6WeakGrowthUpstreamPack.of_paperHypotheses`)
is the per-test-pair uniform-in-`k` Gateaux-remainder bound along the
shared extraction's subsequence `ext.φ`.  Unlike the six Hölder/Hamiltonian
factors, it is *sequence-dependent*; it is produced here from
(a) the test pair's `L^∞ × W^{1,∞}` data (giving the `υ`/`Dυ` integrabilities
and the `k`-independent integral bounds `Aυ`, `ADυ`) and (b) the A2 uniform
`W^{1,γ̄}` a-priori control on `uSeq (ext.φ k)`/`DuSeq (ext.φ k)` (the same
`∃C` bound feeding the compactness extraction), which yields the `k`-uniform
difference bounds `Au`, `ADu`.

The single-shot engine is `keystone_hbdd_of_integralBounds`; this section
threads its inputs over the full `∀`-test-pair quantifier with a
`k`-uniform `M Dυ μ υ`.

The arithmetic mirrors
`SimplePower.Banach.gateauxAux_of_paperHypotheses` exactly; the pointwise
power lemmas are re-derived locally (the originals are `private`/downstream
in `RegularizedSequence`).
-- Adapted from SimplePower.Banach.RegularizedSequence (gateauxAux). -/

/-- Scalar `rpow` bound `|a-b|^q ≤ 2^q(|a|^q+|b|^q)` for `q ≥ 0`. -/
private lemma c2_abs_sub_rpow_le_two_rpow_mul
    {q : ℝ} (hq : 0 ≤ q) (a b : ℝ) :
    |a - b| ^ q ≤ (2 : ℝ) ^ q * (|a| ^ q + |b| ^ q) := by
  have ha : 0 ≤ |a| := abs_nonneg a
  have hb : 0 ≤ |b| := abs_nonneg b
  have hab : 0 ≤ |a - b| := abs_nonneg _
  have htriangle : |a - b| ≤ |a| + |b| := abs_sub _ _
  have h1 : |a - b| ^ q ≤ (|a| + |b|) ^ q :=
    Real.rpow_le_rpow hab htriangle hq
  -- `(|a|+|b|)^q ≤ 2^q(|a|^q+|b|^q)` via `max`.
  have hsum_nn : 0 ≤ |a| + |b| := add_nonneg ha hb
  have hmax_nn : 0 ≤ max |a| |b| := le_max_of_le_left ha
  have hle2 : |a| + |b| ≤ 2 * max |a| |b| := by
    have h1' : |a| ≤ max |a| |b| := le_max_left _ _
    have h2' : |b| ≤ max |a| |b| := le_max_right _ _
    linarith
  have h2 : (|a| + |b|) ^ q ≤ (2 * max |a| |b|) ^ q :=
    Real.rpow_le_rpow hsum_nn hle2 hq
  have h3 : (2 * max |a| |b|) ^ q = (2 : ℝ) ^ q * (max |a| |b|) ^ q :=
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hmax_nn
  have h4 : (max |a| |b|) ^ q ≤ |a| ^ q + |b| ^ q := by
    rcases le_total |a| |b| with hab' | hab'
    · rw [max_eq_right hab']
      have : 0 ≤ |a| ^ q := Real.rpow_nonneg ha q
      linarith
    · rw [max_eq_left hab']
      have : 0 ≤ |b| ^ q := Real.rpow_nonneg hb q
      linarith
  have h2pos : (0 : ℝ) ≤ (2 : ℝ) ^ q :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) q
  calc |a - b| ^ q
      ≤ (|a| + |b|) ^ q := h1
    _ ≤ (2 * max |a| |b|) ^ q := h2
    _ = (2 : ℝ) ^ q * (max |a| |b|) ^ q := h3
    _ ≤ (2 : ℝ) ^ q * (|a| ^ q + |b| ^ q) :=
        mul_le_mul_of_nonneg_left h4 h2pos

/-- Vector `rpow` bound
`((a-b)·(a-b))^(q/2) ≤ 2^q((a·a)^(q/2)+(b·b)^(q/2))` for `q ≥ 1`. -/
private lemma c2_euclideanDot_sub_rpow_le_two_rpow_mul
    {q : ℝ} (hq : 1 ≤ q) (a b : Fin d → ℝ) :
    ((fun i => a i - b i) ⬝ (fun i => a i - b i)) ^ (q / 2)
      ≤ (2 : ℝ) ^ q * ((a ⬝ a) ^ (q / 2) + (b ⬝ b) ^ (q / 2)) := by
  have haa_nn : 0 ≤ a ⬝ a :=
    StationaryMFG.Theorems.SimplePower.Banach.euclideanDot_self_nonneg a
  have hbb_nn : 0 ≤ b ⬝ b :=
    StationaryMFG.Theorems.SimplePower.Banach.euclideanDot_self_nonneg b
  have hsubsub_nn : 0 ≤ (fun i => a i - b i) ⬝ (fun i => a i - b i) :=
    StationaryMFG.Theorems.SimplePower.Banach.euclideanDot_self_nonneg _
  have hCS : |a ⬝ b| ≤ Real.sqrt (a ⬝ a) * Real.sqrt (b ⬝ b) :=
    StationaryMFG.Theorems.SimplePower.Banach.abs_euclideanDot_le_sqrt a b
  have hexpand : (fun i => a i - b i) ⬝ (fun i => a i - b i)
      = a ⬝ a - 2 * (a ⬝ b) + b ⬝ b := by
    simp only [euclideanDot]
    have hpoint : ∀ i, (a i - b i) * (a i - b i)
        = a i * a i - 2 * (a i * b i) + b i * b i := by
      intro i; ring
    simp_rw [hpoint]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hsqrt_aa : 0 ≤ Real.sqrt (a ⬝ a) := Real.sqrt_nonneg _
  have hsqrt_bb : 0 ≤ Real.sqrt (b ⬝ b) := Real.sqrt_nonneg _
  have hsqrt_aa_sq : (Real.sqrt (a ⬝ a)) ^ 2 = a ⬝ a := Real.sq_sqrt haa_nn
  have hsqrt_bb_sq : (Real.sqrt (b ⬝ b)) ^ 2 = b ⬝ b := Real.sq_sqrt hbb_nn
  have hsum_sq : (Real.sqrt (a ⬝ a) + Real.sqrt (b ⬝ b))^2
      = a ⬝ a + 2 * (Real.sqrt (a ⬝ a) * Real.sqrt (b ⬝ b)) + b ⬝ b := by
    have h := add_pow_two (Real.sqrt (a ⬝ a)) (Real.sqrt (b ⬝ b))
    rw [h, hsqrt_aa_sq, hsqrt_bb_sq]; ring
  have hbound : (fun i => a i - b i) ⬝ (fun i => a i - b i)
      ≤ (Real.sqrt (a ⬝ a) + Real.sqrt (b ⬝ b))^2 := by
    rw [hexpand, hsum_sq]
    have h2 : 2 * |a ⬝ b|
        ≤ 2 * (Real.sqrt (a ⬝ a) * Real.sqrt (b ⬝ b)) :=
      mul_le_mul_of_nonneg_left hCS (by norm_num : (0:ℝ) ≤ 2)
    nlinarith [neg_le_abs (a ⬝ b), le_abs_self (a ⬝ b)]
  have hγ2_nn : 0 ≤ q / 2 := by linarith
  have hsum_nn : 0 ≤ Real.sqrt (a ⬝ a) + Real.sqrt (b ⬝ b) :=
    add_nonneg hsqrt_aa hsqrt_bb
  have hpow1 : ((fun i => a i - b i) ⬝ (fun i => a i - b i)) ^ (q / 2)
      ≤ ((Real.sqrt (a ⬝ a) + Real.sqrt (b ⬝ b))^2) ^ (q / 2) :=
    Real.rpow_le_rpow hsubsub_nn hbound hγ2_nn
  have hsq_to_rpow : ((Real.sqrt (a ⬝ a) + Real.sqrt (b ⬝ b))^2) ^ (q / 2)
      = (Real.sqrt (a ⬝ a) + Real.sqrt (b ⬝ b))^q := by
    rw [show (((Real.sqrt (a ⬝ a) + Real.sqrt (b ⬝ b))^2 : ℝ))
          = (Real.sqrt (a ⬝ a) + Real.sqrt (b ⬝ b))^(2:ℝ) from
            (Real.rpow_two _).symm]
    rw [← Real.rpow_mul hsum_nn]; congr 1; ring
  rw [hsq_to_rpow] at hpow1
  have hγ_nn : 0 ≤ q := by linarith
  -- `(√(a·a)+√(b·b))^q ≤ 2^q((√(a·a))^q+(√(b·b))^q)`.
  have hAdd : (Real.sqrt (a ⬝ a) + Real.sqrt (b ⬝ b))^q
      ≤ (2 : ℝ) ^ q *
          ((Real.sqrt (a ⬝ a))^q + (Real.sqrt (b ⬝ b))^q) := by
    have hmax_nn : 0 ≤ max (Real.sqrt (a ⬝ a)) (Real.sqrt (b ⬝ b)) :=
      le_max_of_le_left hsqrt_aa
    have hle2 : Real.sqrt (a ⬝ a) + Real.sqrt (b ⬝ b)
        ≤ 2 * max (Real.sqrt (a ⬝ a)) (Real.sqrt (b ⬝ b)) := by
      have h1' : Real.sqrt (a ⬝ a)
          ≤ max (Real.sqrt (a ⬝ a)) (Real.sqrt (b ⬝ b)) := le_max_left _ _
      have h2' : Real.sqrt (b ⬝ b)
          ≤ max (Real.sqrt (a ⬝ a)) (Real.sqrt (b ⬝ b)) := le_max_right _ _
      linarith
    have h2 : (Real.sqrt (a ⬝ a) + Real.sqrt (b ⬝ b)) ^ q
        ≤ (2 * max (Real.sqrt (a ⬝ a)) (Real.sqrt (b ⬝ b))) ^ q :=
      Real.rpow_le_rpow hsum_nn hle2 hγ_nn
    have h3 : (2 * max (Real.sqrt (a ⬝ a)) (Real.sqrt (b ⬝ b))) ^ q
        = (2 : ℝ) ^ q * (max (Real.sqrt (a ⬝ a)) (Real.sqrt (b ⬝ b))) ^ q :=
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hmax_nn
    have h4 : (max (Real.sqrt (a ⬝ a)) (Real.sqrt (b ⬝ b))) ^ q
        ≤ (Real.sqrt (a ⬝ a))^q + (Real.sqrt (b ⬝ b))^q := by
      rcases le_total (Real.sqrt (a ⬝ a)) (Real.sqrt (b ⬝ b)) with hab' | hab'
      · rw [max_eq_right hab']
        have : 0 ≤ (Real.sqrt (a ⬝ a))^q := Real.rpow_nonneg hsqrt_aa q
        linarith
      · rw [max_eq_left hab']
        have : 0 ≤ (Real.sqrt (b ⬝ b))^q := Real.rpow_nonneg hsqrt_bb q
        linarith
    have h2pos : (0 : ℝ) ≤ (2 : ℝ) ^ q :=
      Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) q
    calc (Real.sqrt (a ⬝ a) + Real.sqrt (b ⬝ b))^q
        ≤ (2 * max (Real.sqrt (a ⬝ a)) (Real.sqrt (b ⬝ b))) ^ q := h2
      _ = (2 : ℝ) ^ q * (max (Real.sqrt (a ⬝ a)) (Real.sqrt (b ⬝ b))) ^ q := h3
      _ ≤ (2 : ℝ) ^ q * ((Real.sqrt (a ⬝ a))^q + (Real.sqrt (b ⬝ b))^q) :=
          mul_le_mul_of_nonneg_left h4 h2pos
  have hsqrt_aa_pow : (Real.sqrt (a ⬝ a)) ^ q = (a ⬝ a) ^ (q / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul haa_nn]; congr 1; ring
  have hsqrt_bb_pow : (Real.sqrt (b ⬝ b)) ^ q = (b ⬝ b) ^ (q / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hbb_nn]; congr 1; ring
  rw [hsqrt_aa_pow, hsqrt_bb_pow] at hAdd
  exact le_trans hpow1 hAdd

/-- Jensen dominator `(a·a)^(q/2) ≤ d^(q-1) ∑|aᵢ|^q` for `q ≥ 1`. -/
private lemma c2_euclideanDot_self_rpow_le_sum_rpow
    {q : ℝ} (hq : 1 ≤ q) (a : Fin d → ℝ) :
    (a ⬝ a) ^ (q / 2)
      ≤ ((d : ℝ)) ^ (q - 1) * ∑ i, |a i| ^ q := by
  have haa_nn : 0 ≤ a ⬝ a :=
    StationaryMFG.Theorems.SimplePower.Banach.euclideanDot_self_nonneg a
  have hsum_abs_nn : 0 ≤ ∑ i, |a i| :=
    Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hStep1 : a ⬝ a ≤ (∑ i, |a i|) ^ 2 := by
    have hsq : (∑ i, |a i|) ^ 2 = (∑ i, |a i|) * (∑ i, |a i|) := sq _
    have hself : a ⬝ a = ∑ i, |a i| ^ 2 := by
      simp only [euclideanDot, sq_abs]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [hself, hsq, Finset.sum_mul_sum]
    refine Finset.sum_le_sum ?_
    intro i _
    rw [show |a i| ^ 2 = |a i| * |a i| from sq _]
    have h1 : |a i| * |a i|
        = ∑ j ∈ ({i} : Finset (Fin d)), |a i| * |a j| := by simp
    rw [h1]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro j hj; simp at hj; subst hj; exact Finset.mem_univ _
    · intro j _ _; exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hγ2_nn : 0 ≤ q / 2 := by linarith
  have hpow1 : (a ⬝ a) ^ (q / 2) ≤ ((∑ i, |a i|) ^ 2) ^ (q / 2) :=
    Real.rpow_le_rpow haa_nn hStep1 hγ2_nn
  have hsq_to_rpow : ((∑ i, |a i|) ^ 2) ^ (q / 2) = (∑ i, |a i|) ^ q := by
    rw [show (((∑ i, |a i|) ^ 2 : ℝ))
          = (∑ i, |a i|) ^ (2 : ℝ) from (Real.rpow_two _).symm]
    rw [← Real.rpow_mul hsum_abs_nn]; congr 1; ring
  rw [hsq_to_rpow] at hpow1
  have hJensen : (∑ i, |a i|) ^ q
      ≤ ((Finset.univ : Finset (Fin d)).card : ℝ) ^ (q - 1) *
          ∑ i, |a i| ^ q :=
    Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
      (s := Finset.univ) (f := fun i => |a i|) (p := q) hq
      (fun i _ => abs_nonneg _)
  rw [Finset.card_univ, Fintype.card_fin] at hJensen
  exact le_trans hpow1 hJensen

/-- Integrability of `|f|^q` on the cube from `MemLpPer (ofReal q) f`. -/
private lemma c2_integrable_abs_rpow
    {q : ℝ} (hq : 1 ≤ q) {f : (Fin d → ℝ) → ℝ}
    (hf : MemLpPer (d := d) (ENNReal.ofReal q) f) :
    Integrable (fun x : Fin d → ℝ => |f x| ^ q)
      (volume.restrict (UnitCube d)) := by
  have hq_nn : (0 : ℝ) ≤ q := le_trans zero_le_one hq
  have hpne : (ENNReal.ofReal q) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (lt_of_lt_of_le zero_lt_one hq)).ne'
  have hpne_top : (ENNReal.ofReal q) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hI := hf.toMemLp.integrable_norm_rpow hpne hpne_top
  rw [ENNReal.toReal_ofReal hq_nn] at hI
  have heq : (fun x : Fin d → ℝ => ‖f x‖ ^ q)
              = (fun x => |f x| ^ q) := by
    funext x; rw [Real.norm_eq_abs]
  rwa [heq] at hI

/-- Integrability of `(g·g)^(q/2)` on the cube when each `g i ∈ Lᵠ`. -/
private lemma c2_integrable_dot_rpow
    {q : ℝ} (hq : 1 ≤ q) {g : Fin d → (Fin d → ℝ) → ℝ}
    (hg : ∀ i, MemLpPer (d := d) (ENNReal.ofReal q) (g i)) :
    Integrable (fun x : Fin d → ℝ =>
      ((fun i => g i x) ⬝ (fun i => g i x)) ^ (q / 2))
      (volume.restrict (UnitCube d)) := by
  have hPointwise : ∀ x : Fin d → ℝ,
      ((fun i => g i x) ⬝ (fun i => g i x)) ^ (q / 2)
        ≤ ((d : ℝ)) ^ (q - 1) * ∑ i, |g i x| ^ q :=
    fun x => c2_euclideanDot_self_rpow_le_sum_rpow (d := d) hq _
  have hInt_g_i : ∀ i, Integrable
      (fun x : Fin d → ℝ => |g i x| ^ q)
      (volume.restrict (UnitCube d)) :=
    fun i => c2_integrable_abs_rpow hq (hg i)
  have hInt_sum : Integrable
      (fun x : Fin d → ℝ => ∑ i, |g i x| ^ q)
      (volume.restrict (UnitCube d)) :=
    MeasureTheory.integrable_finset_sum _ (fun i _ => hInt_g_i i)
  have hInt_dom : Integrable
      (fun x : Fin d → ℝ =>
        ((d : ℝ)) ^ (q - 1) * ∑ i, |g i x| ^ q)
      (volume.restrict (UnitCube d)) := hInt_sum.const_mul _
  have hγ2_nn : (0 : ℝ) ≤ q / 2 := by linarith
  have hCont : Continuous (fun y : ℝ => y ^ (q / 2)) :=
    Real.continuous_rpow_const hγ2_nn
  have hDot_aesm : AEStronglyMeasurable
      (fun x : Fin d → ℝ => ((fun i => g i x) ⬝ (fun i => g i x)))
      (volume.restrict (UnitCube d)) := by
    unfold euclideanDot
    refine Finset.aestronglyMeasurable_fun_sum _ ?_
    intro i _
    exact (hg i).aestronglyMeasurable.mul (hg i).aestronglyMeasurable
  apply MeasureTheory.Integrable.mono'
    (g := fun x => ((d : ℝ)) ^ (q - 1) * ∑ i, |g i x| ^ q) hInt_dom
  · exact hCont.comp_aestronglyMeasurable hDot_aesm
  · refine Filter.Eventually.of_forall (fun x => ?_)
    have hnn : (0 : ℝ) ≤
        ((fun i => g i x) ⬝ (fun i => g i x)) ^ (q / 2) :=
      Real.rpow_nonneg
        (StationaryMFG.Theorems.SimplePower.Banach.euclideanDot_self_nonneg _) _
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact hPointwise x

/-- **C2 — closed full-quantifier `hbdd` from the A2 uniform control.**

Produces the keystone's seventh input over *every* admissible test pair:
the per-test-pair uniform-in-`k` Gateaux-remainder bound along the shared
extraction's subsequence `uSeq (φ k)`/`DuSeq (φ k)`, with a `k`-uniform
constant `M Dυ μ υ`.

Inputs:
* `hγ : 1 ≤ γBar`;
* `huSeq`/`hDuSeq` — per-`k` `Lᵞᵇᵃʳ` regularity along the subsequence
  (`fun k => huLpSeq (φ k)`, `fun k i => hDuLpSeq (φ k) i`);
* `Capr`/`hCapr_nn`/`hCapr` — the A2 uniform a-priori control: the `u`/`Du`
  part of the compactness `hbound` restricted along `φ`.

The `υ`/`Dυ` integral data is extracted from the test pair's
`L^∞ × W^{1,∞}` fields via `MemLpPer.of_top_finite`; the per-pair engine is
`keystone_hbdd_of_integralBounds`. -/
theorem keystone_hbdd_full_of_uniformControl
    {γBar : ℝ} (hγ : 1 ≤ γBar)
    {uSeq : ℕ → (Fin d → ℝ) → ℝ}
    {DuSeq : ℕ → Fin d → (Fin d → ℝ) → ℝ}
    {φ : ℕ → ℕ}
    (huSeq : ∀ k, MemLpPer (d := d) (ENNReal.ofReal γBar) (uSeq (φ k)))
    (hDuSeq : ∀ k i, MemLpPer (d := d) (ENNReal.ofReal γBar) (DuSeq (φ k) i))
    (Capr : ℝ) (hCapr_nn : 0 ≤ Capr)
    (hCapr : ∀ k : ℕ,
      (∫ x in UnitCube d, |uSeq (φ k) x| ^ γBar) +
        (∑ i, ∫ x in UnitCube d, |DuSeq (φ k) i x| ^ γBar)
          ≤ Capr) :
    ∃ M : (Fin d → (Fin d → ℝ) → ℝ) → ((Fin d → ℝ) → ℝ) →
          ((Fin d → ℝ) → ℝ) → ℝ,
      ∀ (Dυ : Fin d → (Fin d → ℝ) → ℝ) (μ υ : (Fin d → ℝ) → ℝ),
        IsWeakSolutionTestPair Dυ μ υ → ∀ k,
          |gateauxWpPair γBar Dυ υ
              (fun i x => Dυ i x - DuSeq (φ k) i x) (υ - uSeq (φ k))|
            ≤ M Dυ μ υ := by
  classical
  have hγ_nn : (0 : ℝ) ≤ γBar := le_trans zero_le_one hγ
  have h2γ_nn : (0 : ℝ) ≤ (2 : ℝ) ^ γBar :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hd_rpow_nn : (0 : ℝ) ≤ ((d : ℝ)) ^ (γBar - 1) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  -- The uniform constant: mirrors `gateauxAux_of_paperHypotheses.M`.
  refine ⟨fun Dυ μ υ =>
      (∫ x in UnitCube d, |υ x| ^ γBar)
        + (2 : ℝ) ^ γBar * ((∫ x in UnitCube d, |υ x| ^ γBar) + Capr)
        + (∫ x in UnitCube d,
            ((fun i => Dυ i x) ⬝ (fun i => Dυ i x)) ^ (γBar / 2))
        + (2 : ℝ) ^ γBar *
            ((∫ x in UnitCube d,
                ((fun i => Dυ i x) ⬝ (fun i => Dυ i x)) ^ (γBar / 2))
              + ((d : ℝ)) ^ (γBar - 1) * Capr), ?_⟩
  intro Dυ μ υ htp k
  -- `υ`/`Dυ` ∈ Lᵞᵇᵃʳ from the test pair's `L^∞` data.
  have hυLp : MemLpPer (d := d) (ENNReal.ofReal γBar) υ :=
    MemLpPer.of_top_finite ENNReal.ofReal_ne_top htp.υ_sob_linf.1
  have hDυLp : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBar) (Dυ i) :=
    fun i => MemLpPer.of_top_finite ENNReal.ofReal_ne_top (htp.Dυ_linf i)
  -- The four integrabilities.
  have hInt_υ : Integrable (fun x : Fin d → ℝ => |υ x| ^ γBar)
      (volume.restrict (UnitCube d)) := c2_integrable_abs_rpow hγ hυLp
  have hInt_uk : Integrable (fun x : Fin d → ℝ => |uSeq (φ k) x| ^ γBar)
      (volume.restrict (UnitCube d)) := c2_integrable_abs_rpow hγ (huSeq k)
  have hInt_υmu : Integrable (fun x : Fin d → ℝ => |υ x - uSeq (φ k) x| ^ γBar)
      (volume.restrict (UnitCube d)) := by
    have hsub : MemLpPer (d := d) (ENNReal.ofReal γBar)
        (fun x => υ x - uSeq (φ k) x) := by
      have := (hυLp.toMemLp.sub (huSeq k).toMemLp)
      exact MemLp.toMemLpPer this
    have := c2_integrable_abs_rpow hγ hsub
    simpa using this
  have hInt_DυDυ : Integrable (fun x : Fin d → ℝ =>
      ((fun i => Dυ i x) ⬝ (fun i => Dυ i x)) ^ (γBar / 2))
      (volume.restrict (UnitCube d)) := c2_integrable_dot_rpow hγ hDυLp
  have hInt_DuDu : Integrable (fun x : Fin d → ℝ =>
      ((fun i => DuSeq (φ k) i x) ⬝ (fun i => DuSeq (φ k) i x)) ^ (γBar / 2))
      (volume.restrict (UnitCube d)) :=
    c2_integrable_dot_rpow hγ (fun i => hDuSeq k i)
  have hInt_DυmDu : Integrable (fun x : Fin d → ℝ =>
      ((fun i => Dυ i x - DuSeq (φ k) i x)
        ⬝ (fun i => Dυ i x - DuSeq (φ k) i x)) ^ (γBar / 2))
      (volume.restrict (UnitCube d)) := by
    have hdiff : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBar)
        (fun x => Dυ i x - DuSeq (φ k) i x) := by
      intro i
      have := ((hDυLp i).toMemLp.sub (hDuSeq k i).toMemLp)
      exact MemLp.toMemLpPer this
    have := c2_integrable_dot_rpow hγ hdiff
    simpa using this
  -- Non-negativity helpers for the a-priori bound split.
  have hIu_nn : 0 ≤ ∫ x in UnitCube d, |uSeq (φ k) x| ^ γBar :=
    MeasureTheory.integral_nonneg (fun x => Real.rpow_nonneg (abs_nonneg _) _)
  have hIDu_nn : 0 ≤ ∑ i, ∫ x in UnitCube d, |DuSeq (φ k) i x| ^ γBar :=
    Finset.sum_nonneg (fun i _ => MeasureTheory.integral_nonneg
      (fun x => Real.rpow_nonneg (abs_nonneg _) _))
  have hSum : (∫ x in UnitCube d, |uSeq (φ k) x| ^ γBar)
      + (∑ i, ∫ x in UnitCube d, |DuSeq (φ k) i x| ^ γBar) ≤ Capr := hCapr k
  have hIu_le : (∫ x in UnitCube d, |uSeq (φ k) x| ^ γBar) ≤ Capr := by linarith
  have hIDu_le : (∑ i, ∫ x in UnitCube d, |DuSeq (φ k) i x| ^ γBar) ≤ Capr := by
    linarith
  -- `Au`: `∫|υ - u_k|^γ̄ ≤ 2^γ̄((∫|υ|^γ̄) + Capr)`.
  have hAu : ∫ x in UnitCube d, |υ x - uSeq (φ k) x| ^ γBar
      ≤ (2 : ℝ) ^ γBar * ((∫ x in UnitCube d, |υ x| ^ γBar) + Capr) := by
    have hPointwise : ∀ x : Fin d → ℝ,
        |υ x - uSeq (φ k) x| ^ γBar
          ≤ (2 : ℝ) ^ γBar * (|υ x| ^ γBar + |uSeq (φ k) x| ^ γBar) :=
      fun x => c2_abs_sub_rpow_le_two_rpow_mul hγ_nn (υ x) (uSeq (φ k) x)
    have hInt_RHS : Integrable (fun x : Fin d → ℝ =>
        (2 : ℝ) ^ γBar * (|υ x| ^ γBar + |uSeq (φ k) x| ^ γBar))
        (volume.restrict (UnitCube d)) := (hInt_υ.add hInt_uk).const_mul _
    have hStep1 : ∫ x in UnitCube d, |υ x - uSeq (φ k) x| ^ γBar
        ≤ ∫ x in UnitCube d,
            (2 : ℝ) ^ γBar * (|υ x| ^ γBar + |uSeq (φ k) x| ^ γBar) :=
      MeasureTheory.integral_mono_ae hInt_υmu hInt_RHS
        (Filter.Eventually.of_forall hPointwise)
    have hLin : ∫ x in UnitCube d,
          (2 : ℝ) ^ γBar * (|υ x| ^ γBar + |uSeq (φ k) x| ^ γBar)
        = (2 : ℝ) ^ γBar *
            ((∫ x in UnitCube d, |υ x| ^ γBar)
              + ∫ x in UnitCube d, |uSeq (φ k) x| ^ γBar) := by
      rw [MeasureTheory.integral_const_mul]; congr 1
      rw [MeasureTheory.integral_add hInt_υ hInt_uk]
    rw [hLin] at hStep1
    have hbnd : (2 : ℝ) ^ γBar *
        ((∫ x in UnitCube d, |υ x| ^ γBar)
          + ∫ x in UnitCube d, |uSeq (φ k) x| ^ γBar)
        ≤ (2 : ℝ) ^ γBar * ((∫ x in UnitCube d, |υ x| ^ γBar) + Capr) :=
      mul_le_mul_of_nonneg_left (by linarith) h2γ_nn
    linarith
  -- `ADu`: `∫((Dυ - Du_k)·…)^(γ̄/2) ≤ 2^γ̄((∫(Dυ·Dυ)^…) + d^(γ̄-1)·Capr)`.
  have hADu : ∫ x in UnitCube d,
        ((fun i => Dυ i x - DuSeq (φ k) i x)
          ⬝ (fun i => Dυ i x - DuSeq (φ k) i x)) ^ (γBar / 2)
      ≤ (2 : ℝ) ^ γBar *
          ((∫ x in UnitCube d,
              ((fun i => Dυ i x) ⬝ (fun i => Dυ i x)) ^ (γBar / 2))
            + ((d : ℝ)) ^ (γBar - 1) * Capr) := by
    have hPointwise : ∀ x : Fin d → ℝ,
        ((fun i => Dυ i x - DuSeq (φ k) i x)
            ⬝ (fun i => Dυ i x - DuSeq (φ k) i x)) ^ (γBar / 2)
          ≤ (2 : ℝ) ^ γBar *
              (((fun i => Dυ i x) ⬝ (fun i => Dυ i x)) ^ (γBar / 2)
                + ((fun i => DuSeq (φ k) i x) ⬝ (fun i => DuSeq (φ k) i x))
                    ^ (γBar / 2)) :=
      fun x => c2_euclideanDot_sub_rpow_le_two_rpow_mul (d := d) hγ
        (fun i => Dυ i x) (fun i => DuSeq (φ k) i x)
    have hInt_pair_const : Integrable (fun x : Fin d → ℝ =>
        (2 : ℝ) ^ γBar *
          (((fun i => Dυ i x) ⬝ (fun i => Dυ i x)) ^ (γBar / 2)
            + ((fun i => DuSeq (φ k) i x) ⬝ (fun i => DuSeq (φ k) i x))
                ^ (γBar / 2)))
        (volume.restrict (UnitCube d)) := (hInt_DυDυ.add hInt_DuDu).const_mul _
    -- Step A.
    have hStepA : ∫ x in UnitCube d,
          ((fun i => Dυ i x - DuSeq (φ k) i x)
            ⬝ (fun i => Dυ i x - DuSeq (φ k) i x)) ^ (γBar / 2)
        ≤ (2 : ℝ) ^ γBar *
            ((∫ x in UnitCube d,
                ((fun i => Dυ i x) ⬝ (fun i => Dυ i x)) ^ (γBar / 2))
              + ∫ x in UnitCube d,
                  ((fun i => DuSeq (φ k) i x) ⬝ (fun i => DuSeq (φ k) i x))
                    ^ (γBar / 2)) := by
      have hraw := MeasureTheory.integral_mono_ae hInt_DυmDu hInt_pair_const
        (Filter.Eventually.of_forall hPointwise)
      rw [MeasureTheory.integral_const_mul,
          MeasureTheory.integral_add hInt_DυDυ hInt_DuDu] at hraw
      exact hraw
    -- Step B: `∫(Du_k·Du_k)^(γ̄/2) ≤ d^(γ̄-1)·∑ᵢ∫|Du_k i|^γ̄`.
    have hPointwise_Du : ∀ x : Fin d → ℝ,
        ((fun i => DuSeq (φ k) i x) ⬝ (fun i => DuSeq (φ k) i x)) ^ (γBar / 2)
          ≤ ((d : ℝ)) ^ (γBar - 1) * ∑ i, |DuSeq (φ k) i x| ^ γBar :=
      fun x => c2_euclideanDot_self_rpow_le_sum_rpow (d := d) hγ _
    have hInt_Duk_i : ∀ i, Integrable
        (fun x : Fin d → ℝ => |DuSeq (φ k) i x| ^ γBar)
        (volume.restrict (UnitCube d)) :=
      fun i => c2_integrable_abs_rpow hγ (hDuSeq k i)
    have hInt_d_Duk : Integrable
        (fun x : Fin d → ℝ =>
          ((d : ℝ)) ^ (γBar - 1) * ∑ i, |DuSeq (φ k) i x| ^ γBar)
        (volume.restrict (UnitCube d)) :=
      (MeasureTheory.integrable_finset_sum _
        (fun i _ => hInt_Duk_i i)).const_mul _
    have hStepB : ∫ x in UnitCube d,
          ((fun i => DuSeq (φ k) i x) ⬝ (fun i => DuSeq (φ k) i x)) ^ (γBar / 2)
        ≤ ((d : ℝ)) ^ (γBar - 1) *
            ∑ i, ∫ x in UnitCube d, |DuSeq (φ k) i x| ^ γBar := by
      have h1 := MeasureTheory.integral_mono_ae hInt_DuDu hInt_d_Duk
        (Filter.Eventually.of_forall hPointwise_Du)
      rw [MeasureTheory.integral_const_mul,
          MeasureTheory.integral_finset_sum _ (fun i _ => hInt_Duk_i i)] at h1
      exact h1
    have hStepBC : ∫ x in UnitCube d,
          ((fun i => DuSeq (φ k) i x) ⬝ (fun i => DuSeq (φ k) i x)) ^ (γBar / 2)
        ≤ ((d : ℝ)) ^ (γBar - 1) * Capr := by
      have hb : ((d : ℝ)) ^ (γBar - 1) *
          (∑ i, ∫ x in UnitCube d, |DuSeq (φ k) i x| ^ γBar)
          ≤ ((d : ℝ)) ^ (γBar - 1) * Capr :=
        mul_le_mul_of_nonneg_left hIDu_le hd_rpow_nn
      linarith
    have hCombine : (2 : ℝ) ^ γBar *
          ((∫ x in UnitCube d,
              ((fun i => Dυ i x) ⬝ (fun i => Dυ i x)) ^ (γBar / 2))
            + ∫ x in UnitCube d,
                ((fun i => DuSeq (φ k) i x) ⬝ (fun i => DuSeq (φ k) i x))
                  ^ (γBar / 2))
        ≤ (2 : ℝ) ^ γBar *
            ((∫ x in UnitCube d,
                ((fun i => Dυ i x) ⬝ (fun i => Dυ i x)) ^ (γBar / 2))
              + ((d : ℝ)) ^ (γBar - 1) * Capr) :=
      mul_le_mul_of_nonneg_left (by linarith) h2γ_nn
    exact le_trans hStepA hCombine
  -- Assemble via the per-pair engine.
  have hbound := keystone_hbdd_of_integralBounds (d := d) (γBar := γBar) hγ
    (μ := μ) (υ := υ) (Dυ := Dυ) (Du := fun i => DuSeq (φ k) i)
    (u := uSeq (φ k))
    (Aυ := ∫ x in UnitCube d, |υ x| ^ γBar)
    (Au := (2 : ℝ) ^ γBar * ((∫ x in UnitCube d, |υ x| ^ γBar) + Capr))
    (ADυ := ∫ x in UnitCube d,
        ((fun i => Dυ i x) ⬝ (fun i => Dυ i x)) ^ (γBar / 2))
    (ADu := (2 : ℝ) ^ γBar *
        ((∫ x in UnitCube d,
            ((fun i => Dυ i x) ⬝ (fun i => Dυ i x)) ^ (γBar / 2))
          + ((d : ℝ)) ^ (γBar - 1) * Capr))
    hInt_DυDυ hInt_DυmDu hInt_υ hInt_υmu
    (le_refl _) hAu (le_refl _) hADu
  exact hbound

/-! ## B2c1 — keystone factors over the FULL test-pair quantifier

The keystone `limit_passage_to_weak_VI_of_paperHypotheses` consumes the
per-test-pair Hölder/Hamiltonian factors quantified over *every*
admissible pair `IsWeakSolutionTestPair Dυ μ υ`.  With the B2c0
refinement, `IsWeakSolutionTestPair` now carries the paper `def:weak`
test-space data (`L^∞ × W^{1,∞}` membership plus `essinf μ > 0`), so the
concrete a.e. bounds that the factor producers require can be
*extracted from the predicate itself*, per pair.

This section threads the predicate's `L^∞`/`W^{1,∞}` fields through the
already-closed producers (`keystone_hgVal_of_regularity`,
`keystone_hgGrad_of_weakGrowth`, `keystone_hg1_of_weakGrowth`), yielding
the six per-test-pair factors over the full `∀`-quantifier.  The seventh
keystone input `hbdd` is *sequence-dependent* (it bounds the
`γ̄`-Laplacian Gateaux remainder uniformly in `k` along the extracted
`u_n k`/`Du_n k`); it is not a function of the test pair alone and is
supplied separately by the wiring step (B2c) from the A2 uniform
`W^{1,γ̄}` a-priori control, via `keystone_hbdd_of_integralBounds`. -/

/-- Measurability of the **flux multiplier** at a test pair.

`x ↦ μ(x) · D_pH(x, Dυ(x), μ(x)) i` is a.e.-strongly measurable on the
cube, from the joint measurability of `D_pH` (`RegularityH.measurable_DpH`)
composed with the a.e.-measurable test data `μ`, `Dυ`. -/
theorem flux_multiplier_aestronglyMeasurable
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hreg : RegularityH (d := d) H DpH)
    {μ : (Fin d → ℝ) → ℝ}
    {Dυ : Fin d → (Fin d → ℝ) → ℝ}
    (hμ_meas : AEStronglyMeasurable μ
      (Measure.restrict volume (UnitCube d)))
    (hDυ_meas : ∀ i, AEStronglyMeasurable (Dυ i)
      (Measure.restrict volume (UnitCube d)))
    (i : Fin d) :
    AEStronglyMeasurable
      (fun x => μ x * DpH x (fun j => Dυ j x) (μ x) i)
      (Measure.restrict volume (UnitCube d)) := by
  set m₀ := Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)
  have hμ_ae : AEMeasurable μ m₀ := hμ_meas.aemeasurable
  have hDυ_ae : AEMeasurable (fun x => (fun j => Dυ j x)) m₀ :=
    aemeasurable_pi_iff.mpr (fun j => (hDυ_meas j).aemeasurable)
  have hcomp : AEMeasurable
      (fun x => DpH x (fun j => Dυ j x) (μ x)) m₀ :=
    hreg.measurable_DpH.comp_aemeasurable
      (aemeasurable_id.prodMk (hDυ_ae.prodMk hμ_ae))
  have hcoord : AEMeasurable
      (fun x => DpH x (fun j => Dυ j x) (μ x) i) m₀ :=
    hcomp.eval i
  exact ((hμ_ae.mul hcoord).aestronglyMeasurable)

/-- Measurability of the **HJB multiplier** at a test pair.

`x ↦ -υ(x) - H(x, Dυ(x), μ(x)) + V(x)` is a.e.-strongly measurable on
the cube, from the joint measurability of `H` (`RegularityH.measurable_H`)
composed with the a.e.-measurable test data, plus the a.e.-strong
measurability of `υ` and `V`. -/
theorem hjb_multiplier_aestronglyMeasurable
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {V : (Fin d → ℝ) → ℝ}
    (hreg : RegularityH (d := d) H DpH)
    {μ υ : (Fin d → ℝ) → ℝ}
    {Dυ : Fin d → (Fin d → ℝ) → ℝ}
    (hμ_meas : AEStronglyMeasurable μ
      (Measure.restrict volume (UnitCube d)))
    (hυ_meas : AEStronglyMeasurable υ
      (Measure.restrict volume (UnitCube d)))
    (hV_meas : AEStronglyMeasurable V
      (Measure.restrict volume (UnitCube d)))
    (hDυ_meas : ∀ i, AEStronglyMeasurable (Dυ i)
      (Measure.restrict volume (UnitCube d))) :
    AEStronglyMeasurable
      (fun x => -(υ x) - H x (fun j => Dυ j x) (μ x) + V x)
      (Measure.restrict volume (UnitCube d)) := by
  set m₀ := Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)
  have hμ_ae : AEMeasurable μ m₀ := hμ_meas.aemeasurable
  have hDυ_ae : AEMeasurable (fun x => (fun j => Dυ j x)) m₀ :=
    aemeasurable_pi_iff.mpr (fun j => (hDυ_meas j).aemeasurable)
  have hH_ae : AEMeasurable
      (fun x => H x (fun j => Dυ j x) (μ x)) m₀ :=
    hreg.measurable_H.comp_aemeasurable
      (aemeasurable_id.prodMk (hDυ_ae.prodMk hμ_ae))
  have hH_asm : AEStronglyMeasurable
      (fun x => H x (fun j => Dυ j x) (μ x)) m₀ :=
    hH_ae.aestronglyMeasurable
  exact ((hυ_meas.neg.sub hH_asm).add hV_meas)

/-- **B2c1 — the six per-test-pair keystone factors over the FULL
quantifier.**

From the per-test-pair predicate `IsWeakSolutionTestPair Dυ μ υ` (now
carrying the paper `def:weak` `L^∞ × W^{1,∞}` test data) together with
the Hamiltonian-side hypotheses (`RegularityH`, `HypothesisWeakGrowth`,
`HypothesisHpDifferentiable`), the exponent ordering `γ̄' ≤ β̄`, the
potential's `L^∞` bound, and `V`'s measurability, this derives the six
Hölder/Hamiltonian factors `hg1`, `hμβ`, `hgGrad`, `hDυ`, `hgVal`, `hυ`
in the *exact* shapes the keystone consumes — for every admissible test
pair.

The concrete bounds (`a` from `lower`, `b`/`R`/`Cυ` from the `L^∞`
fields) are extracted internally from the predicate via
`MemLpPer.exists_ae_norm_le`; nothing beyond the predicate's own fields
and the (accepted) Hamiltonian hypotheses is consumed. -/
theorem keystone_sixFactors_of_testPair
    {βBar βBar' γBar γBar' : ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {V : (Fin d → ℝ) → ℝ}
    (hreg : RegularityH (d := d) H DpH)
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hdiff : HypothesisHpDifferentiable (d := d) H DpH)
    (hexp : ENNReal.ofReal γBar' ≤ ENNReal.ofReal βBar)
    (hβBar_top : ENNReal.ofReal βBar ≠ ⊤)
    (hV_linf : MemLpPer (d := d) ⊤ V) :
    -- `hg1`
    (∀ (Dυ : Fin d → (Fin d → ℝ) → ℝ) (μ υ : (Fin d → ℝ) → ℝ),
        IsWeakSolutionTestPair Dυ μ υ →
          MemLpPer (d := d) (ENNReal.ofReal βBar')
            (fun x => -(υ x) - H x (fun i => Dυ i x) (μ x) + V x))
      ∧
    -- `hμβ`
    (∀ (Dυ : Fin d → (Fin d → ℝ) → ℝ) (μ υ : (Fin d → ℝ) → ℝ),
        IsWeakSolutionTestPair Dυ μ υ →
          MemLpPer (d := d) (ENNReal.ofReal βBar) μ)
      ∧
    -- `hgGrad`
    (∀ (Dυ : Fin d → (Fin d → ℝ) → ℝ) (μ υ : (Fin d → ℝ) → ℝ),
        IsWeakSolutionTestPair Dυ μ υ → ∀ i,
          MemLpPer (d := d) (ENNReal.ofReal γBar')
            (fun x => μ x * DpH x (fun j => Dυ j x) (μ x) i))
      ∧
    -- `hDυ`
    (∀ (Dυ : Fin d → (Fin d → ℝ) → ℝ) (μ υ : (Fin d → ℝ) → ℝ),
        IsWeakSolutionTestPair Dυ μ υ → ∀ i,
          MemLpPer (d := d) (ENNReal.ofReal γBar) (Dυ i))
      ∧
    -- `hgVal`
    (∀ (Dυ : Fin d → (Fin d → ℝ) → ℝ) (μ υ : (Fin d → ℝ) → ℝ),
        IsWeakSolutionTestPair Dυ μ υ →
          MemLpPer (d := d) (ENNReal.ofReal γBar') (fun x => μ x - 1))
      ∧
    -- `hυ`
    (∀ (Dυ : Fin d → (Fin d → ℝ) → ℝ) (μ υ : (Fin d → ℝ) → ℝ),
        IsWeakSolutionTestPair Dυ μ υ →
          MemLpPer (d := d) (ENNReal.ofReal γBar) υ) := by
  classical
  -- Potential's a.e. `L^∞` bound (one fixed constant `CV ≥ 0`).
  obtain ⟨CV, _hCV_nn, hV_bdd⟩ := hV_linf.exists_ae_norm_le
  have hV_bdd' : ∀ᵐ x ∂(volume.restrict (UnitCube d)), |V x| ≤ CV := by
    filter_upwards [hV_bdd] with x hx; simpa [Real.norm_eq_abs] using hx
  have hV_meas : AEStronglyMeasurable V
      (Measure.restrict volume (UnitCube d)) := hV_linf.aestronglyMeasurable
  -- For finite `Lᵖ` membership of the regularity-derived factors we need
  -- `Lᵖ_per` (any finite `p`) membership of the `L^∞` test data; on the
  -- finite-measure cube `L^∞ ⊆ Lᵖ`.  We use the explicit constant bound
  -- route through `MemLp.of_bound` instead.
  refine ⟨?hg1, ?hμβ, ?hgGrad, ?hDυ, ?hgVal, ?hυ⟩
  -- The shared per-pair extraction of bounds, used by every factor below.
  -- We re-derive it inside each branch (cheap, keeps the goals decoupled).
  case hg1 =>
    intro Dυ μ υ htp
    obtain ⟨a, ha_pos, hμ_lower⟩ := htp.lower
    obtain ⟨b, _hb_nn, hμ_bdd⟩ := htp.μ_linf.exists_ae_norm_le
    have hμ_upper : ∀ᵐ x ∂(volume.restrict (UnitCube d)), μ x ≤ b := by
      filter_upwards [hμ_bdd] with x hx
      exact le_trans (le_abs_self (μ x)) (by simpa [Real.norm_eq_abs] using hx)
    -- We need `‖fun j => Dυ j x‖ ≤ R'`; build it from the coordinate
    -- `L^∞` bounds `Dυ_linf`.
    obtain ⟨R', hR'_nn, hDυ_bdd⟩ :=
      exists_ae_vector_norm_bound (Dυ := Dυ) htp.Dυ_linf
    obtain ⟨Cυ, _hCυ_nn, hυ_bdd0⟩ := htp.υ_sob_linf.1.exists_ae_norm_le
    have hυ_bdd : ∀ᵐ x ∂(volume.restrict (UnitCube d)), |υ x| ≤ Cυ := by
      filter_upwards [hυ_bdd0] with x hx; simpa [Real.norm_eq_abs] using hx
    have hG_meas := hjb_multiplier_aestronglyMeasurable hreg
      htp.μ_linf.aestronglyMeasurable htp.υ_sob_linf.1.aestronglyMeasurable
      hV_meas (fun i => (htp.Dυ_linf i).aestronglyMeasurable)
    exact keystone_hg1_of_weakGrowth (βBar' := βBar') (R := R') (a := a)
      (b := b) (Cυ := Cυ) (CV := CV) hweak hdiff ha_pos hμ_lower hμ_upper
      hDυ_bdd hυ_bdd hV_bdd' hG_meas
  case hμβ =>
    intro Dυ μ υ htp
    exact MemLpPer.of_top_finite hβBar_top htp.μ_linf
  case hgGrad =>
    intro Dυ μ υ htp i
    obtain ⟨a, ha_pos, hμ_lower⟩ := htp.lower
    obtain ⟨b, _hb_nn, hμ_bdd⟩ := htp.μ_linf.exists_ae_norm_le
    have hμ_upper : ∀ᵐ x ∂(volume.restrict (UnitCube d)), μ x ≤ b := by
      filter_upwards [hμ_bdd] with x hx
      exact le_trans (le_abs_self (μ x)) (by simpa [Real.norm_eq_abs] using hx)
    obtain ⟨R', hR'_nn, hDυ_bdd⟩ :=
      exists_ae_vector_norm_bound (Dυ := Dυ) htp.Dυ_linf
    have hF_meas := flux_multiplier_aestronglyMeasurable hreg
      htp.μ_linf.aestronglyMeasurable
      (fun j => (htp.Dυ_linf j).aestronglyMeasurable) i
    exact keystone_hgGrad_of_weakGrowth (γBar' := γBar') (R := R') (a := a)
      (b := b) hweak i ha_pos hμ_lower hμ_upper hDυ_bdd hF_meas
  case hDυ =>
    intro Dυ μ υ htp i
    exact MemLpPer.of_top_finite ENNReal.ofReal_ne_top (htp.Dυ_linf i)
  case hgVal =>
    intro Dυ μ υ htp
    exact keystone_hgVal_of_regularity
      (MemLpPer.of_top_finite hβBar_top htp.μ_linf) hexp hβBar_top
  case hυ =>
    intro Dυ μ υ htp
    exact MemLpPer.of_top_finite ENNReal.ofReal_ne_top htp.υ_sob_linf.1

/-- **B2c — the six per-test-pair keystone factors with `V ∈ L^{β̄'}`.**

Identical to `keystone_sixFactors_of_testPair`, but the potential is
supplied at the paper exponent `β̄'` (`V ∈ L^{β̄'}(𝕋^d)`) rather than
`L^∞`.  Only the HJB factor `hg1` uses `V`; it is produced via
`keystone_hg1_of_weakGrowth_VLp`, which keeps the whole multiplier in
`L^{β̄'}` by adding `V ∈ L^{β̄'}` to the bounded `υ`/`H` part.  The other
five factors are unchanged. -/
theorem keystone_sixFactors_of_testPair_VLp
    {βBar βBar' γBar γBar' : ℝ} (hβBar'_pos : 0 < βBar')
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {V : (Fin d → ℝ) → ℝ}
    (hreg : RegularityH (d := d) H DpH)
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hdiff : HypothesisHpDifferentiable (d := d) H DpH)
    (hexp : ENNReal.ofReal γBar' ≤ ENNReal.ofReal βBar)
    (hβBar_top : ENNReal.ofReal βBar ≠ ⊤)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBar') V) :
    -- `hg1`
    (∀ (Dυ : Fin d → (Fin d → ℝ) → ℝ) (μ υ : (Fin d → ℝ) → ℝ),
        IsWeakSolutionTestPair Dυ μ υ →
          MemLpPer (d := d) (ENNReal.ofReal βBar')
            (fun x => -(υ x) - H x (fun i => Dυ i x) (μ x) + V x))
      ∧
    -- `hμβ`
    (∀ (Dυ : Fin d → (Fin d → ℝ) → ℝ) (μ υ : (Fin d → ℝ) → ℝ),
        IsWeakSolutionTestPair Dυ μ υ →
          MemLpPer (d := d) (ENNReal.ofReal βBar) μ)
      ∧
    -- `hgGrad`
    (∀ (Dυ : Fin d → (Fin d → ℝ) → ℝ) (μ υ : (Fin d → ℝ) → ℝ),
        IsWeakSolutionTestPair Dυ μ υ → ∀ i,
          MemLpPer (d := d) (ENNReal.ofReal γBar')
            (fun x => μ x * DpH x (fun j => Dυ j x) (μ x) i))
      ∧
    -- `hDυ`
    (∀ (Dυ : Fin d → (Fin d → ℝ) → ℝ) (μ υ : (Fin d → ℝ) → ℝ),
        IsWeakSolutionTestPair Dυ μ υ → ∀ i,
          MemLpPer (d := d) (ENNReal.ofReal γBar) (Dυ i))
      ∧
    -- `hgVal`
    (∀ (Dυ : Fin d → (Fin d → ℝ) → ℝ) (μ υ : (Fin d → ℝ) → ℝ),
        IsWeakSolutionTestPair Dυ μ υ →
          MemLpPer (d := d) (ENNReal.ofReal γBar') (fun x => μ x - 1))
      ∧
    -- `hυ`
    (∀ (Dυ : Fin d → (Fin d → ℝ) → ℝ) (μ υ : (Fin d → ℝ) → ℝ),
        IsWeakSolutionTestPair Dυ μ υ →
          MemLpPer (d := d) (ENNReal.ofReal γBar) υ) := by
  classical
  -- The five non-`hg1` factors come straight from the `L^∞`-V producer
  -- with `V := 0` (it never uses `V` except in `hg1`).  We re-derive each
  -- branch directly rather than threading a dummy `V` through the bundle.
  refine ⟨?hg1, ?hμβ, ?hgGrad, ?hDυ, ?hgVal, ?hυ⟩
  case hg1 =>
    intro Dυ μ υ htp
    obtain ⟨a, ha_pos, hμ_lower⟩ := htp.lower
    obtain ⟨b, _hb_nn, hμ_bdd⟩ := htp.μ_linf.exists_ae_norm_le
    have hμ_upper : ∀ᵐ x ∂(volume.restrict (UnitCube d)), μ x ≤ b := by
      filter_upwards [hμ_bdd] with x hx
      exact le_trans (le_abs_self (μ x)) (by simpa [Real.norm_eq_abs] using hx)
    obtain ⟨R', hR'_nn, hDυ_bdd⟩ :=
      exists_ae_vector_norm_bound (Dυ := Dυ) htp.Dυ_linf
    obtain ⟨Cυ, _hCυ_nn, hυ_bdd0⟩ := htp.υ_sob_linf.1.exists_ae_norm_le
    have hυ_bdd : ∀ᵐ x ∂(volume.restrict (UnitCube d)), |υ x| ≤ Cυ := by
      filter_upwards [hυ_bdd0] with x hx; simpa [Real.norm_eq_abs] using hx
    -- a.e.-strong measurability of the bounded base `-υ - H` (no `V`).
    have hG_meas := hjb_multiplier_aestronglyMeasurable hreg
      htp.μ_linf.aestronglyMeasurable htp.υ_sob_linf.1.aestronglyMeasurable
      (V := fun _ => (0 : ℝ))
      (aestronglyMeasurable_const)
      (fun i => (htp.Dυ_linf i).aestronglyMeasurable)
    have hG_meas' : AEStronglyMeasurable
        (fun x => -(υ x) - H x (fun j => Dυ j x) (μ x))
        (Measure.restrict volume (UnitCube d)) := by
      have hfun : (fun x => -(υ x) - H x (fun j => Dυ j x) (μ x) + (0 : ℝ))
          = (fun x => -(υ x) - H x (fun j => Dυ j x) (μ x)) := by
        funext x; ring
      rwa [hfun] at hG_meas
    exact keystone_hg1_of_weakGrowth_VLp (βBar' := βBar') (R := R') (a := a)
      (b := b) (Cυ := Cυ) hβBar'_pos hweak hdiff ha_pos hμ_lower hμ_upper
      hDυ_bdd hυ_bdd hV hG_meas'
  case hμβ =>
    intro Dυ μ υ htp
    exact MemLpPer.of_top_finite hβBar_top htp.μ_linf
  case hgGrad =>
    intro Dυ μ υ htp i
    obtain ⟨a, ha_pos, hμ_lower⟩ := htp.lower
    obtain ⟨b, _hb_nn, hμ_bdd⟩ := htp.μ_linf.exists_ae_norm_le
    have hμ_upper : ∀ᵐ x ∂(volume.restrict (UnitCube d)), μ x ≤ b := by
      filter_upwards [hμ_bdd] with x hx
      exact le_trans (le_abs_self (μ x)) (by simpa [Real.norm_eq_abs] using hx)
    obtain ⟨R', hR'_nn, hDυ_bdd⟩ :=
      exists_ae_vector_norm_bound (Dυ := Dυ) htp.Dυ_linf
    have hF_meas := flux_multiplier_aestronglyMeasurable hreg
      htp.μ_linf.aestronglyMeasurable
      (fun j => (htp.Dυ_linf j).aestronglyMeasurable) i
    exact keystone_hgGrad_of_weakGrowth (γBar' := γBar') (R := R') (a := a)
      (b := b) hweak i ha_pos hμ_lower hμ_upper hDυ_bdd hF_meas
  case hDυ =>
    intro Dυ μ υ htp i
    exact MemLpPer.of_top_finite ENNReal.ofReal_ne_top (htp.Dυ_linf i)
  case hgVal =>
    intro Dυ μ υ htp
    exact keystone_hgVal_of_regularity
      (MemLpPer.of_top_finite hβBar_top htp.μ_linf) hexp hβBar_top
  case hυ =>
    intro Dυ μ υ htp
    exact MemLpPer.of_top_finite ENNReal.ofReal_ne_top htp.υ_sob_linf.1

end LimitPassage
end InfimalConvolution
end StationaryMFG
