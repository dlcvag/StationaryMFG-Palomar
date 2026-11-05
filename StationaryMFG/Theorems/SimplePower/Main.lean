module

public import StationaryMFG.Solutions.Regularized
public import StationaryMFG.Solutions.MFGOperator
public import StationaryMFG.Solutions.Strong
public import StationaryMFG.Theorems.SimplePower.Compactness
public import StationaryMFG.Theorems.SimplePower.Hemicontinuity
public import StationaryMFG.Theorems.SimplePower.StrongIsStrong
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Order.OrderClosed

@[expose] public section

/-!
# Limit passage `ε → 0` for the regularized weak variational inequality

This module formalizes the limit-passage step of paper
`Source/FGU-monotone_revised.tex`, lines 1276–1292, equation
`eq:existweaksol` (proof of `thm:main-simple.power.growth`).

## Paper restatement

We have a sequence
`(m_{ε_k}, u_{ε_k}) ⊂ L^{β̄}(𝕋^d; ℝ⁺_0) × W^{1,γ̄}(𝕋^d)` with
`ε_k → 0⁺` such that, for every `k ∈ ℕ` and every admissible test pair
`(μ, υ) ∈ 𝓚`,
```
0 ≤ ⟨A_{ε_k}[μ, υ], (μ, υ) − (m_{ε_k}, u_{ε_k})⟩
  = I_{HJB,k}(μ,υ) + I_{TR,k}(μ,υ) + ε_k · I_{Reg,k}(μ,υ).
```
By the apriori bounds + reflexivity, after extraction
`(m_{ε_k}, u_{ε_k}) ⇀ (m, u)`. The paper now passes to the limit
summand-by-summand:

* The `H, D_pH, V` terms (linear in `(m_{ε_k}, u_{ε_k})` and multiplied
  against test factors that lie in `L^{β̄'}`/`L^{γ̄'}` by Hölder) define
  bounded linear functionals on `L^{β̄} × W^{1,γ̄}`; weak convergence
  passes to the limit.
* The `ε_k`-Gateaux term is dominated by the uniformly-bounded
  `(υ - u_{ε_k})` in `W^{1,γ̄}` times `ε_k → 0`, so vanishes.

The conclusion is `0 ≤ ⟨A_0[μ, υ], (μ, υ) − (m, u)⟩` for every
`(μ, υ) ∈ 𝓚`.

## Lean encoding

Following the conventions used elsewhere in this project (cf.
`Compactness.lean` for the abstract weak-extraction theorem), we land
the limit passage as a **hypothesis-shaped** real-numerical theorem:
the consumer supplies the upstream Hölder + weak-convergence
information by asserting

* `Tendsto Aε atTop (𝓝 A0)` — the unregularized pairing converges, i.e.
  the `H, D_pH, V` terms pass to the limit (paper equation
  `eq:existweaksol`, lines 1283–1290 right-hand side).
* `Tendsto ε atTop (𝓝 0)` and `|reg k| ≤ M` — the regularization
  parameter goes to zero with the Gateaux pairing uniformly bounded
  (paper apriori bound on `(υ − u_{ε_k})` in `W^{1,γ̄}`).

The structural inequality to pass to the limit is
`0 ≤ Aε k + ε k * reg k` (this is exactly the regularized VI shape).

The conclusion `0 ≤ A0` is the abstract limit passage; the
`limit_passage_weak_VI_pairing` corollary names the consumer-facing
version where `A0 = mfgOperatorPair (μ, υ; (μ - m, υ - u, Dυ - Du))`.

## Main results

* `limit_passage_real` — the abstract real-numerical limit passage:
  given `0 ≤ Aε k + ε k * reg k`, `Aε → A0`, `ε → 0`, `|reg| ≤ M`,
  conclude `0 ≤ A0`.
* `limit_passage_weak_VI` — packaged form using `mfgOperatorEpsPair` /
  `mfgOperatorPair` and the convergence hypotheses produced by the
  upstream weak-convergence + Hölder steps. This is the consumer-facing
  statement for `infra:P4-main-strong-VI`.
-/

noncomputable section

namespace StationaryMFG
namespace Theorems
namespace SimplePower

open Filter Topology
open MeasureTheory
open StationaryMFG.Periodic
open StationaryMFG.Solutions.MFG
open scoped ENNReal

variable {d : ℕ}

/-! ## Real-numerical kernel of the limit passage

The structural lemma underlying the paper's argument: a sequence of
real numbers of the form `Aε k + ε k * reg k`, all `≥ 0`, with
`Aε k → A0`, `ε k → 0`, and `|reg k|` uniformly bounded, has limit
`A0 ≥ 0`. -/

/-- **Real limit passage.** If `0 ≤ Aε k + ε k * reg k` for every `k`,
`Aε → A0`, `ε → 0`, and `|reg k| ≤ M` for some `M`, then `0 ≤ A0`. -/
theorem limit_passage_real
    {ε Aε reg : ℕ → ℝ} {A0 : ℝ}
    (hineq : ∀ k, 0 ≤ Aε k + ε k * reg k)
    (hAε : Tendsto Aε atTop (𝓝 A0))
    (hε : Tendsto ε atTop (𝓝 0))
    {M : ℝ} (hreg : ∀ k, |reg k| ≤ M) :
    0 ≤ A0 := by
  -- The regularization residual `ε k * reg k` tends to `0`.
  -- We squeeze: `|ε k * reg k| ≤ |ε k| * M`, and `|ε k| * M → 0`.
  have hM_nonneg : 0 ≤ M := le_trans (abs_nonneg _) (hreg 0)
  have hres_tendsto : Tendsto (fun k => ε k * reg k) atTop (𝓝 0) := by
    -- `|ε k| * M → 0` since `ε k → 0`.
    have habs : Tendsto (fun k => |ε k|) atTop (𝓝 0) := by
      have habs_eq : (fun k => |ε k|) = (fun k => ‖ε k‖) := by
        funext k; rw [Real.norm_eq_abs]
      rw [habs_eq]
      simpa using hε.norm
    have hbnd_tendsto : Tendsto (fun k => |ε k| * M) atTop (𝓝 0) := by
      have : Tendsto (fun k => |ε k| * M) atTop (𝓝 (0 * M)) :=
        habs.mul_const M
      simpa using this
    -- Squeeze: `|ε k * reg k| ≤ |ε k| * M`.
    refine squeeze_zero_norm (a := fun k => |ε k| * M) ?_ hbnd_tendsto
    intro k
    have h1 : |ε k * reg k| ≤ |ε k| * M := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hreg k) (abs_nonneg _)
    simpa [Real.norm_eq_abs] using h1
  -- Hence `Aε k + ε k * reg k → A0 + 0 = A0`.
  have hsum : Tendsto (fun k => Aε k + ε k * reg k) atTop (𝓝 (A0 + 0)) :=
    hAε.add hres_tendsto
  rw [add_zero] at hsum
  -- The closed half-space `{x : 0 ≤ x}` is closed; the sequence stays
  -- inside it, so the limit does too.
  exact ge_of_tendsto' hsum hineq

/-! ## Packaged form: limit passage for the MFG variational inequality

The packaged statement re-uses the real-numerical kernel by reading
`Aε k = mfgOperatorPair V H DpH Dυ μ υ (Dυ - D u_{ε_k}) (μ - m_{ε_k}) (υ - u_{ε_k})`
(the unregularized pairing applied to the regularized solutions),
`reg k = gateauxWpPair γBar Dυ υ (Dυ - D u_{ε_k}) (υ - u_{ε_k})`,
`A0 = mfgOperatorPair V H DpH Dυ μ υ (Dυ - Du) (μ - m) (υ - u)`. The
hypothesis `0 ≤ Aε k + ε k * reg k` is exactly the regularized weak VI
`0 ≤ ⟨A_{ε_k}[μ,υ], (μ,υ) - (m_{ε_k}, u_{ε_k})⟩` after expansion via
`mfgOperatorEpsPair_pairing_eq`.

The convergence `Aε → A0` is the content of weak convergence
`(m_{ε_k}, u_{ε_k}) ⇀ (m, u)` against the test functionals
`(-υ - H(x, Dυ, μ) + V)`, `μ D_pH(x, Dυ, μ)`, `(μ - 1)`; producing it
is the job of the upstream Hölder + duality task and is supplied as a
hypothesis here. -/

variable (V : (Fin d → ℝ) → ℝ)
variable (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
variable (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))

/-- **Limit passage for the regularized weak VI** (paper line 1276,
eq. `eq:existweaksol`).

Inputs:

* A regularization sequence `ε k → 0` with `0 ≤ ε k`.
* For each `k`, a regularized solution candidate `(mε k, uε k)` with
  explicit gradient family `Duε k`, satisfying the regularized weak VI
  in expanded form
  `0 ≤ mfgOperatorPair V H DpH Dυ μ υ (Dυ - Duε k) (μ - mε k) (υ - uε k)
       + ε k * gateauxWpPair γBar Dυ υ (Dυ - Duε k) (υ - uε k)`.
* The sequence of *unregularized* pairings converges to the limit
  pairing along the weakly-convergent subsequence (this packages the
  paper's Hölder + weak-convergence argument, lines 1283–1290).
* The Gateaux residuals are uniformly bounded (this packages the paper's
  apriori bound `(υ - uε k)` is bounded in `W^{1,γ̄}`, lines 1290–1291).

Output: the unregularized weak VI at the limit pair `(m, u)`:
`0 ≤ mfgOperatorPair V H DpH Dυ μ υ (Dυ - Du) (μ - m) (υ - u)`. -/
theorem limit_passage_weak_VI
    {γBar : ℝ} {ε : ℕ → ℝ}
    {μ υ : (Fin d → ℝ) → ℝ}
    {Dυ : Fin d → (Fin d → ℝ) → ℝ}
    {mε uε : ℕ → (Fin d → ℝ) → ℝ}
    {Duε : ℕ → Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (_hε_nonneg : ∀ k, 0 ≤ ε k)
    (hε_to0 : Tendsto ε atTop (𝓝 0))
    (hVI : ∀ k,
      0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
              (fun i x => Dυ i x - Duε k i x) (μ - mε k) (υ - uε k)
            + ε k *
              gateauxWpPair γBar Dυ υ
                (fun i x => Dυ i x - Duε k i x) (υ - uε k))
    (hpair_conv :
      Tendsto (fun k =>
        mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
            (fun i x => Dυ i x - Duε k i x) (μ - mε k) (υ - uε k))
        atTop
        (𝓝 (mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
              (fun i x => Dυ i x - Du i x) (μ - m) (υ - u))))
    {M : ℝ}
    (hreg_bdd : ∀ k,
      |gateauxWpPair γBar Dυ υ
          (fun i x => Dυ i x - Duε k i x) (υ - uε k)| ≤ M) :
    0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
          (fun i x => Dυ i x - Du i x) (μ - m) (υ - u) := by
  set Aε : ℕ → ℝ := fun k =>
    mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
      (fun i x => Dυ i x - Duε k i x) (μ - mε k) (υ - uε k) with hAε_def
  set reg : ℕ → ℝ := fun k =>
    gateauxWpPair γBar Dυ υ
      (fun i x => Dυ i x - Duε k i x) (υ - uε k) with hreg_def
  set A0 : ℝ :=
    mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
      (fun i x => Dυ i x - Du i x) (μ - m) (υ - u) with hA0_def
  -- Re-shape `hVI`, `hpair_conv`, `hreg_bdd` against the abbreviations
  -- and apply the real-numerical kernel.
  have hineq : ∀ k, 0 ≤ Aε k + ε k * reg k := hVI
  have hAε_tendsto : Tendsto Aε atTop (𝓝 A0) := hpair_conv
  have hreg_abs : ∀ k, |reg k| ≤ M := hreg_bdd
  exact limit_passage_real (Aε := Aε) (reg := reg) (ε := ε)
    (A0 := A0) hineq hAε_tendsto hε_to0 hreg_abs

/-! ## Equivalent statement on the regularized pairing

It is sometimes more convenient to feed the limit-passage theorem with
the regularized pairing `mfgOperatorEpsPair … (μ - mε k) (υ - uε k)`
directly, as this is the literal output of the upstream
`paper:thm:strongAepsi`. The corollary below repackages
`limit_passage_weak_VI` with the `mfgOperatorEpsPair_pairing_eq`
expansion already applied.

Note: the `mfgOperatorEpsPair_pairing_eq` rewrites the regularized
pairing into the integral form of `defAepsi`. To present the corollary
in a form that lines up with the upstream `paper:thm:strongAepsi`'s
output (which produces `0 ≤ mfgOperatorEpsPair … (μ - mε, υ - uε)`),
the consumer should rewrite via `mfgOperatorEpsPair`'s definition
before applying this lemma; we package that bridge as a separate
helper lemma. -/

/-- **Bridge form of the limit passage**, taking the regularized weak VI
in `mfgOperatorEpsPair` form (the literal output of
`paper:thm:strongAepsi`). The proof reduces to
`limit_passage_weak_VI` after unfolding `mfgOperatorEpsPair` via its
defining sum decomposition. -/
theorem limit_passage_weak_VI_of_eps
    {γBar : ℝ} {ε : ℕ → ℝ}
    {μ υ : (Fin d → ℝ) → ℝ}
    {Dυ : Fin d → (Fin d → ℝ) → ℝ}
    {mε uε : ℕ → (Fin d → ℝ) → ℝ}
    {Duε : ℕ → Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hε_nonneg : ∀ k, 0 ≤ ε k)
    (hε_to0 : Tendsto ε atTop (𝓝 0))
    (hVI_eps : ∀ k,
      0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBar (ε k) Dυ μ υ
            (fun i x => Dυ i x - Duε k i x) (μ - mε k) (υ - uε k))
    (hpair_conv :
      Tendsto (fun k =>
        mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
            (fun i x => Dυ i x - Duε k i x) (μ - mε k) (υ - uε k))
        atTop
        (𝓝 (mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
              (fun i x => Dυ i x - Du i x) (μ - m) (υ - u))))
    {M : ℝ}
    (hreg_bdd : ∀ k,
      |gateauxWpPair γBar Dυ υ
          (fun i x => Dυ i x - Duε k i x) (υ - uε k)| ≤ M) :
    0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
          (fun i x => Dυ i x - Du i x) (μ - m) (υ - u) := by
  -- Rewrite each `hVI_eps k` via the definition of `mfgOperatorEpsPair`
  -- and feed into `limit_passage_weak_VI`.
  have hVI : ∀ k,
      0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
              (fun i x => Dυ i x - Duε k i x) (μ - mε k) (υ - uε k)
            + ε k *
              gateauxWpPair γBar Dυ υ
                (fun i x => Dυ i x - Duε k i x) (υ - uε k) := by
    intro k
    have h := hVI_eps k
    -- Unfold `mfgOperatorEpsPair`.
    unfold mfgOperatorEpsPair at h
    exact h
  exact limit_passage_weak_VI (V := V) (H := H) (DpH := DpH)
    hε_nonneg hε_to0 hVI hpair_conv hreg_bdd

/-! ## Sanity-check examples -/

/-- The real-numerical kernel applied to the toy data `ε k = 0`,
`Aε k = 0`, `reg k = 0`: the trivial instance. -/
example :
    (0 : ℝ) ≤ 0 := by
  refine limit_passage_real
    (ε := fun _ => (0 : ℝ))
    (Aε := fun _ => (0 : ℝ))
    (reg := fun _ => (0 : ℝ)) (A0 := 0) (M := 0)
    ?_ ?_ ?_ ?_
  · intro _; simp
  · exact tendsto_const_nhds
  · exact tendsto_const_nhds
  · intro _; simp

/-- The packaged limit-passage theorem in its statement form, exercised
on a generic instance. The hypotheses are taken as given; the example
just verifies the signature. -/
example
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    {γBar : ℝ} {ε : ℕ → ℝ}
    {μ υ : (Fin d → ℝ) → ℝ}
    {Dυ : Fin d → (Fin d → ℝ) → ℝ}
    {mε uε : ℕ → (Fin d → ℝ) → ℝ}
    {Duε : ℕ → Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hε_nonneg : ∀ k, 0 ≤ ε k)
    (hε_to0 : Tendsto ε atTop (𝓝 0))
    (hVI : ∀ k,
      0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
              (fun i x => Dυ i x - Duε k i x) (μ - mε k) (υ - uε k)
            + ε k *
              gateauxWpPair γBar Dυ υ
                (fun i x => Dυ i x - Duε k i x) (υ - uε k))
    (hpair_conv :
      Tendsto (fun k =>
        mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
            (fun i x => Dυ i x - Duε k i x) (μ - mε k) (υ - uε k))
        atTop
        (𝓝 (mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
              (fun i x => Dυ i x - Du i x) (μ - m) (υ - u))))
    {M : ℝ}
    (hreg_bdd : ∀ k,
      |gateauxWpPair γBar Dυ υ
          (fun i x => Dυ i x - Duε k i x) (υ - uε k)| ≤ M) :
    0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
          (fun i x => Dυ i x - Du i x) (μ - m) (υ - u) :=
  limit_passage_weak_VI (V := V) (H := H) (DpH := DpH)
    hε_nonneg hε_to0 hVI hpair_conv hreg_bdd

/-! ## Strong VI upgrade for `A_0` via hemicontinuity

This section formalises the closing step of paper
`Source/FGU-monotone_revised.tex`, lines 1311–1314: starting from the
**weak** VI for `A_0` at the limit pair `(m, u)` produced by
`limit_passage_weak_VI`, the paper invokes hemicontinuity of `A_0`
(`infra:P4-A0-hemicontinuous`, formalised as `A0_isHemicontinuous`) to
upgrade the inequality to the **strong** form
```
0 ≤ ⟨A_0[m, u], (μ, υ) − (m, u)⟩  for every (μ, υ) ∈ 𝓚.
```

The proof is a Minty-style segment argument adapted to the project's
`IsHemicontinuousMFG` predicate (which packages continuity along the
explicit convex-combination path `cxComb`/`cxCombGrad` over `[0, 1]`).
The argument mirrors `Monotone.hemicont_upgrade` (paper
`rmk:hemicontinuous-upgrade`); we reproduce it concretely here because
our project-local hemicontinuity predicate operates on
`MFGTriple d := (m, u, Du)` triples rather than on a single normed-space
point. -/

open StationaryMFG.Hamiltonian

/-- **Linearity of `mfgOperatorPair` in the test direction** under the
pointwise scaling `(η, ν, Dν) ↦ (t • η, t • ν, fun i => t • Dν i)`.
Used by the Minty-trick `t → 0⁺` step in `main_strong_VI`. -/
lemma mfgOperatorPair_smul_test
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (μ υ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ) (t : ℝ) :
    mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
        (fun i x => t * Dν i x) (fun x => t * η x) (fun x => t * ν x)
      = t * mfgOperatorPair (V := V) (H := H) (DpH := DpH)
              Dυ μ υ Dν η ν := by
  -- Pointwise: the integrand is linear in `(η, ν, Dν)`.
  unfold mfgOperatorPair
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_unitCube ?_
  intro x _
  -- Distribute the scalar through the pointwise euclidean dot product.
  have hdot :
      (DpH x (fun i => Dυ i x) (μ x)) ⬝ (fun i => t * Dν i x)
        = t * ((DpH x (fun i => Dυ i x) (μ x)) ⬝ (fun i => Dν i x)) := by
    unfold euclideanDot
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  -- The integrand on the LHS contains the dot-product expression
  -- `DpH … ⬝ (fun i => t * Dν i x)`; rewrite it via `hdot` and then
  -- close by `ring`.
  change (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (t * η x)
        + μ x * ((DpH x (fun i => Dυ i x) (μ x)) ⬝ (fun i => t * Dν i x))
        + (μ x - 1) * (t * ν x)
      = t * ((-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * η x
                + μ x * ((DpH x (fun i => Dυ i x) (μ x))
                            ⬝ (fun i => Dν i x))
                + (μ x - 1) * ν x)
  rw [hdot]
  ring

/-- **Segment substitution shape** of the weak VI applied along the
homotopy `(μ_t, υ_t, Dυ_t) := (1−t)(m, u, Du) + t(μ, υ, Dυ)`.

The pairing of `A_0[μ_t, υ_t, Dυ_t]` with the test direction
`((μ_t, υ_t, Dυ_t) − (m, u, Du))` equals `t` times the pairing with
`((μ, υ, Dυ) − (m, u, Du))`, by linearity of the pairing in the test
direction.

This is the algebraic step that lets us divide the weak VI by `t > 0`
in the Minty-style upgrade. -/
lemma mfgOperatorPair_segment_test_eq_smul
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (Dυ Du : Fin d → (Fin d → ℝ) → ℝ)
    (μ m υ u : (Fin d → ℝ) → ℝ) (t : ℝ) :
    mfgOperatorPair (V := V) (H := H) (DpH := DpH)
        (fun i x => cxCombGrad Dυ Du t i x)
        (fun x => cxComb μ m t x)
        (fun x => cxComb υ u t x)
        (fun i x => cxCombGrad Dυ Du t i x - Du i x)
        (fun x => cxComb μ m t x - m x)
        (fun x => cxComb υ u t x - u x)
      = t * mfgOperatorPair (V := V) (H := H) (DpH := DpH)
              (fun i x => cxCombGrad Dυ Du t i x)
              (fun x => cxComb μ m t x)
              (fun x => cxComb υ u t x)
              (fun i x => Dυ i x - Du i x)
              (μ - m) (υ - u) := by
  -- Each of the three "test" arguments equals `t • <the corresponding
  -- straight difference>`.
  have h_grad : ∀ i x, cxCombGrad Dυ Du t i x - Du i x
      = t * (Dυ i x - Du i x) := by
    intro i x; unfold cxCombGrad; ring
  have h_μ : ∀ x, cxComb μ m t x - m x = t * (μ x - m x) := by
    intro x; unfold cxComb; ring
  have h_υ : ∀ x, cxComb υ u t x - u x = t * (υ x - u x) := by
    intro x; unfold cxComb; ring
  -- Rewrite the LHS pointwise so it matches the `t * Dν`, `t * η`,
  -- `t * ν` shape, then apply linearity.
  have hLHS_eq :
      mfgOperatorPair (V := V) (H := H) (DpH := DpH)
          (fun i x => cxCombGrad Dυ Du t i x)
          (fun x => cxComb μ m t x)
          (fun x => cxComb υ u t x)
          (fun i x => cxCombGrad Dυ Du t i x - Du i x)
          (fun x => cxComb μ m t x - m x)
          (fun x => cxComb υ u t x - u x)
        = mfgOperatorPair (V := V) (H := H) (DpH := DpH)
            (fun i x => cxCombGrad Dυ Du t i x)
            (fun x => cxComb μ m t x)
            (fun x => cxComb υ u t x)
            (fun i x => t * (Dυ i x - Du i x))
            (fun x => t * (μ x - m x))
            (fun x => t * (υ x - u x)) := by
    congr 1
    · funext i x; exact h_grad i x
    · funext x; exact h_μ x
    · funext x; exact h_υ x
  rw [hLHS_eq]
  -- Apply `mfgOperatorPair_smul_test` with `Dν := Dυ - Du`,
  -- `η := μ - m`, `ν := υ - u`.
  have := mfgOperatorPair_smul_test (V := V) (H := H) (DpH := DpH)
            (fun i x => cxCombGrad Dυ Du t i x)
            (fun x => cxComb μ m t x)
            (fun x => cxComb υ u t x)
            (fun i x => Dυ i x - Du i x)
            (μ - m) (υ - u) t
  -- Match the lambdas: `(μ - m) x = μ x - m x`, etc.
  simpa [Pi.sub_apply] using this

/-- **Strong VI for `A_0`** (paper `Source/FGU-monotone_revised.tex`,
lines 1311–1314, application of `rmk:hemicontinuous-upgrade`).

Given:
* a set `D ⊂ MFGTriple d` of admissible `(μ, υ, Dυ)` triples,
* a *segment closure* hypothesis: for every two triples in `D`, their
  pointwise convex combination at any `t ∈ [0, 1]` is again in `D`,
* hemicontinuity of `A_0 = mfgOperatorPair` on `D`,
* a *limit triple* `(m, u, Du) ∈ D`,
* the *weak* VI at `(m, u, Du)`: for every `(μ, υ, Dυ) ∈ D`,
  `0 ≤ ⟨A_0[μ, υ], (μ - m, υ - u)⟩`,

we obtain the *strong* VI at `(m, u, Du)`: for every
`(μ, υ, Dυ) ∈ D`, `0 ≤ ⟨A_0[m, u], (μ - m, υ - u)⟩`.

The proof is a Minty-style segment argument: apply the weak VI at the
homotopy point `(μ_t, υ_t, Dυ_t)`, factor out `t > 0` by linearity in
the test direction, send `t → 0⁺` using hemicontinuity. The continuity
endpoint at `t = 0` reads `mfgOperatorPair … Du m u … = ⟨A_0[m, u], …⟩`.

Adapted from `Monotone.hemicont_upgrade` (paper
`rmk:hemicontinuous-upgrade`). -/
theorem main_strong_VI
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    {D : Set (MFGTriple d)}
    (hSeg : ∀ ⦃μBar ῡ Dῡ⦄, (μBar, ῡ, Dῡ) ∈ D →
            ∀ ⦃μ υ Dυ⦄, (μ, υ, Dυ) ∈ D →
            ∀ t ∈ Set.Icc (0 : ℝ) 1,
              ((fun x => cxComb μ μBar t x),
               (fun x => cxComb υ ῡ t x),
               (fun i x => cxCombGrad Dυ Dῡ t i x)) ∈ D)
    (hAhc : IsHemicontinuousMFG_restricted d D
              (mfgOperatorPair (V := V) (H := H) (DpH := DpH)))
    {m u : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm : (m, u, Du) ∈ D)
    (hweak : ∀ ⦃μ υ Dυ⦄, (μ, υ, Dυ) ∈ D →
             0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
                   (fun i x => Dυ i x - Du i x) (μ - m) (υ - u)) :
    ∀ ⦃μ υ Dυ⦄, (μ, υ, Dυ) ∈ D →
      0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH) Du m u
            (fun i x => Dυ i x - Du i x) (μ - m) (υ - u) := by
  intro μ υ Dυ hμ
  -- Define `g t := ⟨A_0[μ_t, υ_t, Dυ_t], ((μ - m, υ - u))⟩`.
  set g : ℝ → ℝ := fun t =>
    mfgOperatorPair (V := V) (H := H) (DpH := DpH)
      (fun i x => cxCombGrad Dυ Du t i x)
      (fun x => cxComb μ m t x)
      (fun x => cxComb υ u t x)
      (fun i x => Dυ i x - Du i x)
      (μ - m) (υ - u) with hg_def
  -- Step 1. For every `t ∈ Ioc 0 1`, `0 ≤ g t`.
  have hg_pos : ∀ ⦃t : ℝ⦄, t ∈ Set.Ioc (0 : ℝ) 1 → 0 ≤ g t := by
    intro t ht
    obtain ⟨ht_pos, ht_le⟩ := ht
    have ht_mem : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht_pos.le, ht_le⟩
    -- The segment endpoint `(μ_t, υ_t, Dυ_t)` is in `D` by `hSeg`.
    have hseg_mem : ((fun x => cxComb μ m t x),
                     (fun x => cxComb υ u t x),
                     (fun i x => cxCombGrad Dυ Du t i x)) ∈ D :=
      hSeg hm hμ t ht_mem
    -- Apply the weak VI at the segment point. The "limit" point in the
    -- weak-VI hypothesis is `(m, u, Du)`, so the test direction is
    -- `((μ_t - m, υ_t - u, Dυ_t - Du))`.
    have hwk := hweak hseg_mem
    -- The `hweak` hypothesis expresses the test direction in `Pi.sub`
    -- form `(fun x ↦ cxComb μ m t x) - m`; convert it to the pointwise
    -- form `fun x ↦ cxComb μ m t x - m x` so the segment lemma applies.
    have hwk' :
        0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH)
              (fun i x => cxCombGrad Dυ Du t i x)
              (fun x => cxComb μ m t x)
              (fun x => cxComb υ u t x)
              (fun i x => cxCombGrad Dυ Du t i x - Du i x)
              (fun x => cxComb μ m t x - m x)
              (fun x => cxComb υ u t x - u x) := hwk
    -- Now rewrite via `mfgOperatorPair_segment_test_eq_smul`.
    have h_eq := mfgOperatorPair_segment_test_eq_smul (V := V) (H := H)
                   (DpH := DpH) Dυ Du μ m υ u t
    rw [h_eq] at hwk'
    -- `hwk' : 0 ≤ t * g t`. Divide by `t > 0`.
    exact (mul_nonneg_iff_of_pos_left ht_pos).1 hwk'
  -- Step 2. The map `g` is continuous on `[0, 1]` (hemicontinuity).
  have hg_cont : ContinuousOn g (Set.Icc (0 : ℝ) 1) := by
    -- Hemicontinuity of `A_0` along the segment from `(m, u, Du)` (at
    -- `t = 0`) to `(μ, υ, Dυ)` (at `t = 1`), evaluated against the test
    -- triple `(μ - m, υ - u, Dυ - Du)`.
    have := hAhc hm hμ
    -- The restricted predicate yields continuity at the difference
    -- triple `(μ - m, υ - u, Dυ - Du)` written via `fun x => μ x - m x`,
    -- which is definitionally `Pi.sub_apply` of `(μ - m)`.
    simpa [hg_def, Pi.sub_def, Pi.sub_apply] using this
  -- Step 3. The value at `0` is `⟨A_0[m, u], …⟩`.
  have hg_zero : g 0
      = mfgOperatorPair (V := V) (H := H) (DpH := DpH) Du m u
          (fun i x => Dυ i x - Du i x) (μ - m) (υ - u) := by
    simp [hg_def, cxComb, cxCombGrad]
  -- Step 4. Take the limit `t → 0⁺` along `Ioc 0 1`.
  have h_subset : Set.Ioc (0 : ℝ) 1 ⊆ Set.Icc (0 : ℝ) 1 :=
    Set.Ioc_subset_Icc_self
  have hcwa : ContinuousWithinAt g (Set.Ioc (0 : ℝ) 1) 0 := by
    have hcwa_Icc : ContinuousWithinAt g (Set.Icc (0 : ℝ) 1) 0 :=
      hg_cont 0 ⟨le_rfl, by norm_num⟩
    exact hcwa_Icc.mono h_subset
  have hNeBot : (𝓝[Set.Ioc (0 : ℝ) 1] 0).NeBot :=
    left_nhdsWithin_Ioc_neBot (by norm_num : (0 : ℝ) < 1)
  have htendsto : Tendsto g (𝓝[Set.Ioc (0 : ℝ) 1] 0) (𝓝 (g 0)) := hcwa
  have h_g0_nonneg : 0 ≤ g 0 := by
    refine ge_of_tendsto htendsto ?_
    exact Filter.eventually_of_mem self_mem_nhdsWithin (fun t ht => hg_pos ht)
  -- Conclude.
  rw [hg_zero] at h_g0_nonneg
  exact h_g0_nonneg

/-! ### Sanity-check example for the strong VI -/

/-- Sanity-check: with the trivial Hamiltonian `H = 0`, `D_pH = 0`, and
`V = 0`, the singleton domain `D = {(1, 0, 0)}` trivially admits the
weak-VI hypothesis (the integrand vanishes), and the conclusion is also
the trivial `0 ≤ 0`. The example verifies the signature of
`main_strong_VI`. -/
example (d : ℕ) :
    ∀ ⦃μ υ Dυ⦄,
      (μ, υ, Dυ) ∈
        ({((fun _ => (1:ℝ)), (fun _ => (0:ℝ)), (fun _ _ => (0:ℝ)))}
          : Set (MFGTriple d)) →
      0 ≤ mfgOperatorPair
            (V := fun _ => (0:ℝ))
            (H := fun _ _ _ => (0:ℝ))
            (DpH := fun _ _ _ => (0 : Fin d → ℝ))
            (fun _ _ => (0:ℝ))
            (fun _ => (1:ℝ))
            (fun _ => (0:ℝ))
            (fun i x => Dυ i x - (fun _ _ => (0:ℝ)) i x)
            (μ - (fun _ => (1:ℝ))) (υ - (fun _ => (0:ℝ))) := by
  refine main_strong_VI (d := d)
    (V := fun _ => (0:ℝ))
    (H := fun _ _ _ => (0:ℝ))
    (DpH := fun _ _ _ => (0 : Fin d → ℝ))
    (D := {((fun _ => (1:ℝ)), (fun _ => (0:ℝ)), (fun _ _ => (0:ℝ)))})
    ?hSeg ?hAhc ?hm ?hweak
  · -- Segment closure: in the singleton domain, both endpoints coincide
    -- with the canonical triple, so the convex combination is constant
    -- in `t` and stays in the singleton.
    intro μBar ῡ Dῡ hBar μ υ Dυ hμ t _
    rw [Set.mem_singleton_iff, Prod.mk.injEq, Prod.mk.injEq] at hBar hμ
    obtain ⟨hμBar, hῡ, hDῡ⟩ := hBar
    obtain ⟨hμ', hυ, hDυ⟩ := hμ
    subst hμBar; subst hῡ; subst hDῡ
    subst hμ'; subst hυ; subst hDυ
    rw [Set.mem_singleton_iff, Prod.mk.injEq, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · funext x; unfold cxComb; ring
    · funext x; unfold cxComb; ring
    · funext i x; unfold cxCombGrad; ring
  · -- Hemicontinuity (restricted form, per
    -- `infra-P7-sigfix-T1-drain-A-restricted-hemicont`): from the
    -- existing example for `A_0`, weakened via `.toRestricted`.
    refine
      IsHemicontinuousMFG.toRestricted (B := mfgOperatorPair
        (V := fun _ : (Fin d → ℝ) => (0:ℝ))
        (H := fun _ _ _ => (0:ℝ))
        (DpH := fun _ _ _ => (0 : Fin d → ℝ))) ?_
    refine A0_isHemicontinuous (d := d) (fun _ => (0:ℝ)) _ _ ?hReg 2 one_lt_two _ ?hData
    · refine
        { periodic_H := ?_, periodic_DpH := ?_,
          measurable_H := ?_, measurable_DpH := ?_,
          continuous_H_pm := ?_, continuous_DpH_pm := ?_ }
      · intro _ _; exact IsPeriodic.const (0 : ℝ)
      · intro _ _; exact IsPeriodic.const (0 : Fin d → ℝ)
      · exact measurable_const
      · exact measurable_const
      · refine Filter.Eventually.of_forall ?_
        intro _; exact continuousOn_const
      · refine Filter.Eventually.of_forall ?_
        intro _; exact continuousOn_const
    · intro μBar ῡ Dῡ hBar μ υ Dυ hμ η ν Dν
      rw [Set.mem_singleton_iff, Prod.mk.injEq, Prod.mk.injEq] at hBar hμ
      obtain ⟨hμBar, hῡ, hDῡ⟩ := hBar
      obtain ⟨hμ', hυ, hDυ⟩ := hμ
      subst hμBar; subst hῡ; subst hDῡ
      subst hμ'; subst hυ; subst hDυ
      refine
        { hPos := ?_,
          g_unreg := fun _ => (0:ℝ),
          g_gat := fun _ => (0:ℝ),
          hg_unreg_int := ?_,
          hg_gat_int := ?_,
          hF_unreg_meas := ?_,
          hF_unreg_bound := ?_,
          hF_gat_meas := ?_,
          hF_gat_bound := ?_ }
      · -- Segment positivity (a.e.-uniform-in-`t` form, per
        -- `infra-P4-hemicont-segment-data-ae-relax`).
        refine Filter.Eventually.of_forall ?_
        intro x t _
        have : cxComb (fun _ : (Fin d → ℝ) => (1:ℝ)) (fun _ => (1:ℝ)) t x = 1 := by
          unfold cxComb; ring
        rw [this]; norm_num
      · exact (integrable_zero _ _ _).integrableOn
      · exact (integrable_zero _ _ _).integrableOn
      · intro t _
        have hzero :
            (fun x : (Fin d → ℝ) =>
              aepsiIntegrandAt_unreg (d := d)
                (fun _ => (0:ℝ))
                (fun _ _ _ => (0:ℝ))
                (fun _ _ _ => (0 : Fin d → ℝ))
                (fun _ _ => (0:ℝ)) (fun _ _ => (0:ℝ))
                (fun _ => (1:ℝ)) (fun _ => (1:ℝ))
                (fun _ => (0:ℝ)) (fun _ => (0:ℝ))
                Dν η ν x t)
              = fun _ : (Fin d → ℝ) => (0:ℝ) := by
          funext x
          unfold aepsiIntegrandAt_unreg cxComb cxCombGrad
          simp [euclideanDot]
        rw [hzero]
        exact aestronglyMeasurable_const
      · intro t _
        refine Filter.Eventually.of_forall ?_
        intro x
        unfold aepsiIntegrandAt_unreg cxComb cxCombGrad
        simp [euclideanDot]
      · intro t _
        have hzero :
            (fun x : (Fin d → ℝ) =>
              aepsiIntegrandAt_gateaux (d := d) (2:ℝ)
                (fun _ _ => (0:ℝ)) (fun _ _ => (0:ℝ))
                (fun _ => (0:ℝ)) (fun _ => (0:ℝ))
                Dν ν x t)
              = fun _ : (Fin d → ℝ) => (0:ℝ) := by
          funext x
          unfold aepsiIntegrandAt_gateaux cxComb cxCombGrad
          simp [euclideanDot]
        rw [hzero]
        exact aestronglyMeasurable_const
      · intro t _
        refine Filter.Eventually.of_forall ?_
        intro x
        unfold aepsiIntegrandAt_gateaux cxComb cxCombGrad
        simp [euclideanDot]
  · -- The limit triple is the canonical triple.
    rfl
  · -- Weak VI: the integrand is identically zero.
    intro μ υ Dυ hμ
    rw [Set.mem_singleton_iff, Prod.mk.injEq, Prod.mk.injEq] at hμ
    obtain ⟨hμ', hυ, hDυ⟩ := hμ
    subst hμ'; subst hυ; subst hDυ
    -- Now compute that the pairing is exactly zero.
    have hzero :
        mfgOperatorPair (V := fun _ => (0:ℝ)) (H := fun _ _ _ => (0:ℝ))
            (DpH := fun _ _ _ => (0 : Fin d → ℝ))
            (fun _ _ => (0:ℝ)) (fun _ => (1:ℝ)) (fun _ => (0:ℝ))
            (fun i x => (fun _ _ => (0:ℝ)) i x - (fun _ _ => (0:ℝ)) i x)
            ((fun _ => (1:ℝ)) - (fun _ => (1:ℝ)))
            ((fun _ => (0:ℝ)) - (fun _ => (0:ℝ)))
          = 0 := by
      unfold mfgOperatorPair
      simp [euclideanDot]
    rw [hzero]

/-! ## Final conclusion: bundle into `IsStrongSolution`

This section formalises the closing bookkeeping step of the paper
(`Source/FGU-monotone_revised.tex`, lines 1295–1314, last sentence
"We then conclude the proof by Lemma `lem:strong.is.strong` with
`ε = 0`"). At this point we have the **strong VI** at the limit pair
`(m, u, Du)` for the unregularized operator `A_0`. Applying the three
clauses of `lem:strong.is.strong` (formalised as
`lem_strong_is_strong_HJB_ineq`, `lem_strong_is_strong_HJB_eq_paperForm`,
`lem_strong_is_strong_transport`) at `ε = 0` yields the HJB inequality,
the HJB equality on `{m > 0}`, and the weak transport equation —
exactly the three clauses of `IsStrongSolution`. -/

open StationaryMFG.Solutions.Strong
open StationaryMFG.Hamiltonian (mDpH)

/-- **Final bookkeeping step** (paper line 1314, "We then conclude the
proof by Lemma `lem:strong.is.strong` with `ε = 0`").

Given the three test-pair specializations of the strong VI for `A_0` at
`(m, u, Du)` (set form, signed set form, transport form, all at
`ε = 0`), together with integrability of the HJB residual, the residual
times `m`, and the flux `m · D_pH(·, Du, m)`, the limit pair `(m, u)` is
a **strong solution** in the sense of Definition `def:strong`
(`IsStrongSolution V H (mDpH DpH) Du m u`).

The proof bundles:
* `lem_strong_is_strong_HJB_ineq` for the a.e. inequality
  `u + H − V ≤ 0`;
* `lem_strong_is_strong_HJB_eq_paperForm` for the a.e. identity
  `(u + H − V) · m = 0`, which gives equality on `{m > 0}` by
  `mul_eq_zero` (since `m > 0 ⇒ m ≠ 0`);
* `lem_strong_is_strong_transport` at `ε = 0`, where the
  γ̄-Laplacian Gateaux summand drops out and the bracketed integral
  reduces to the unregularized flux part
  `(m − 1) φ + m · (D_pH(x, Du, m) ⬝ Dφ)`. We rewrite this against the
  flux extension `J := mDpH DpH` (paper hypothesis `(a:mDpHat0)`) using
  the algebraic identity `(m • DpH) ⬝ v = m * (DpH ⬝ v)`. -/
theorem main_conclude_isStrongSolution
    {γBar : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    (hRes : Integrable (hjbResidual V H Du m u)
              (volume.restrict (UnitCube d)))
    (hResM : Integrable (fun x => hjbResidual V H Du m u x * m x)
              (volume.restrict (UnitCube d)))
    (hFluxInt : Integrable (fun x => mDpH DpH x (fun i => Du i x) (m x))
              (volume.restrict (UnitCube d)))
    (hVI_set : StrongVI_setForm V H DpH γBar 0 Du m u)
    (hVI_signed : StrongVI_setForm_signed V H DpH γBar 0 Du m u)
    (hVI_transport : StrongVI_transportForm V H DpH γBar 0 Du m u) :
    IsStrongSolution V H (mDpH DpH) Du m u := by
  refine ⟨?_, ?_⟩
  · -- HJB clause: combine (a) and (b).
    refine ⟨?_, ?_⟩
    · -- (a) `u + H - V ≤ 0` a.e.
      exact lem_strong_is_strong_HJB_ineq (V := V) (H := H) (DpH := DpH)
        γBar 0 Du m u hRes hVI_set
    · -- (b) `0 < m → u + H - V = 0` a.e., from `(u + H − V) · m = 0`.
      have hPaper := lem_strong_is_strong_HJB_eq_paperForm
        (V := V) (H := H) (DpH := DpH) γBar 0 Du m u hResM hVI_signed
      refine hPaper.mono ?_
      intro x hx hmpos
      -- `hx : (u + H - V) * m = 0`. With `m > 0`, deduce `u + H - V = 0`.
      have hmne : m x ≠ 0 := ne_of_gt hmpos
      rcases mul_eq_zero.mp hx with hzero | hmzero
      · exact hzero
      · exact (hmne hmzero).elim
  · -- Transport clause.
    refine ⟨?_, ?_⟩
    · -- Integrability of the flux `J(·, Du(·), m(·)) = m · D_pH(·, Du, m)`.
      exact hFluxInt
    · -- Weak transport equation.
      intro φ
      -- Apply (c) at `ε = 0`. The Gateaux summand `ε * I₂` drops out.
      have htrans := lem_strong_is_strong_transport
        (V := V) (H := H) (DpH := DpH) γBar 0 Du m u hVI_transport φ
      -- `htrans : I₁ + 0 * I₂ = 0`, i.e. `I₁ = 0` where
      -- `I₁ = ∫ transportFluxIntegrand DpH Du m φ`.
      have hI₁_zero :
          (∫ x in UnitCube d, transportFluxIntegrand DpH Du m φ x
              ∂(volume : Measure (Fin d → ℝ))) = 0 := by
        have := htrans
        simp at this
        exact this
      -- Now match `transportFluxIntegrand DpH Du m φ` against the
      -- integrand of `IsStrongSolution_Transport` with `J := mDpH DpH`.
      -- transportFluxIntegrand x = (m x - 1) * φ x
      --                            + m x * (DpH x (Du · x) (m x) ⬝ Dφ x).
      -- IsStrongSolution_Transport integrand x =
      --   (m x - 1) * φ x + (mDpH DpH) x (Du · x) (m x) ⬝ Dφ x.
      -- These agree pointwise via `(m • DpH) ⬝ v = m * (DpH ⬝ v)`.
      have hpointwise : ∀ x : Fin d → ℝ,
          (m x - 1) * (φ : (Fin d → ℝ) → ℝ) x
            + (mDpH DpH) x (fun i => Du i x) (m x)
                ⬝ (fun i =>
                    (SmoothPeriodic.partialDeriv i φ : (Fin d → ℝ) → ℝ) x)
            = transportFluxIntegrand DpH Du m φ x := by
        intro x
        unfold transportFluxIntegrand mDpH
        -- `(m x • DpH x …) ⬝ w = m x * (DpH x … ⬝ w)`.
        have hsmul :
            (m x • DpH x (fun i => Du i x) (m x))
                ⬝ (fun i =>
                    (SmoothPeriodic.partialDeriv i φ : (Fin d → ℝ) → ℝ) x)
              = m x * (DpH x (fun i => Du i x) (m x)
                  ⬝ (fun i =>
                      (SmoothPeriodic.partialDeriv i φ :
                        (Fin d → ℝ) → ℝ) x)) := by
          unfold euclideanDot
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro i _
          simp [Pi.smul_apply, smul_eq_mul, mul_assoc]
        rw [hsmul]
      have hintegrand_eq :
          (fun x : Fin d → ℝ =>
              (m x - 1) * (φ : (Fin d → ℝ) → ℝ) x
                + (mDpH DpH) x (fun i => Du i x) (m x)
                    ⬝ (fun i =>
                        (SmoothPeriodic.partialDeriv i φ :
                          (Fin d → ℝ) → ℝ) x))
            = (fun x => transportFluxIntegrand DpH Du m φ x) := by
        funext x; exact hpointwise x
      -- Rewrite the goal integrand and conclude via `hI₁_zero`.
      have hint_eq :
          (∫ x in UnitCube d,
              (m x - 1) * (φ : (Fin d → ℝ) → ℝ) x
                + (mDpH DpH) x (fun i => Du i x) (m x)
                    ⬝ (fun i =>
                        (SmoothPeriodic.partialDeriv i φ :
                          (Fin d → ℝ) → ℝ) x)
              ∂(volume : Measure (Fin d → ℝ)))
            = ∫ x in UnitCube d, transportFluxIntegrand DpH Du m φ x
                ∂(volume : Measure (Fin d → ℝ)) := by
        rw [hintegrand_eq]
      rw [hint_eq]
      exact hI₁_zero

/-! ### Sanity-check example for `main_conclude_isStrongSolution` -/

/-- Sanity-check: with the trivial Hamiltonian `H = 0`, `D_pH = 0`,
`V = 0`, `m = 1`, `u = 0`, `Du = 0`, the integrability hypotheses are
satisfied (everything is identically zero) and the three strong-VI
specializations hold trivially (each pairing is identically zero), so
`IsStrongSolution` follows. -/
example :
    IsStrongSolution (d := d)
      (V := fun _ => (0 : ℝ))
      (H := fun _ _ _ => (0 : ℝ))
      (J := mDpH (fun _ _ _ => (0 : Fin d → ℝ)))
      (Du := fun _ _ => (0 : ℝ))
      (m := fun _ => (1 : ℝ))
      (u := fun _ => (0 : ℝ)) := by
  refine main_conclude_isStrongSolution (γBar := (2 : ℝ))
    (V := fun _ => (0 : ℝ))
    (H := fun _ _ _ => (0 : ℝ))
    (DpH := fun _ _ _ => (0 : Fin d → ℝ))
    ?hRes ?hResM ?hFluxInt ?hVI_set ?hVI_signed ?hVI_transport
  · -- Integrability of `hjbResidual V H Du m u = 0`.
    have h0 : hjbResidual (d := d)
        (fun _ : Fin d → ℝ => (0 : ℝ))
        (fun _ _ _ => (0 : ℝ))
        (fun _ _ => (0 : ℝ))
        (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ))
        = (fun _ => (0 : ℝ)) := by
      funext x; unfold hjbResidual; simp
    rw [h0]
    exact integrable_zero _ _ _
  · have h0 : (fun x : Fin d → ℝ => hjbResidual (d := d)
        (fun _ : Fin d → ℝ => (0 : ℝ))
        (fun _ _ _ => (0 : ℝ))
        (fun _ _ => (0 : ℝ))
        (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ)) x
        * ((fun _ : Fin d → ℝ => (1 : ℝ)) x))
        = (fun _ => (0 : ℝ)) := by
      funext x; unfold hjbResidual; simp
    rw [h0]
    exact integrable_zero _ _ _
  · -- Integrability of the flux `mDpH 0 = 0`.
    have h0 : (fun x : Fin d → ℝ =>
        mDpH (fun _ _ _ => (0 : Fin d → ℝ)) x
          (fun i => (fun _ _ => (0 : ℝ)) i x)
          ((fun _ => (1 : ℝ)) x))
        = (fun _ => (0 : Fin d → ℝ)) := by
      funext x; unfold mDpH; simp
    rw [h0]
    exact integrable_zero _ _ _
  · -- Strong-VI set form: pairing is identically zero.
    intro S _hSmeas _hSfin
    have hzero :
        mfgOperatorEpsPair (d := d)
            (V := fun _ => (0 : ℝ))
            (H := fun _ _ _ => (0 : ℝ))
            (DpH := fun _ _ _ => (0 : Fin d → ℝ))
            (γBar := (2 : ℝ)) (ε := (0 : ℝ))
            (fun _ _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ))
            (fun _ _ => (0 : ℝ))
            (fun x => S.indicator (fun _ => (1 : ℝ)) x)
            (fun _ => (0 : ℝ)) = 0 := by
      unfold mfgOperatorEpsPair mfgOperatorPair gateauxWpPair
      simp [euclideanDot]
    rw [hzero]
  · -- Strong-VI signed set form.
    intro σ _hσ S _hSmeas _hSfin
    have hzero :
        mfgOperatorEpsPair (d := d)
            (V := fun _ => (0 : ℝ))
            (H := fun _ _ _ => (0 : ℝ))
            (DpH := fun _ _ _ => (0 : Fin d → ℝ))
            (γBar := (2 : ℝ)) (ε := (0 : ℝ))
            (fun _ _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ))
            (fun _ _ => (0 : ℝ))
            (fun x => σ * ((fun _ : Fin d → ℝ => (1 : ℝ)) x)
                * S.indicator (fun _ => (1 : ℝ)) x)
            (fun _ => (0 : ℝ)) = 0 := by
      unfold mfgOperatorEpsPair mfgOperatorPair gateauxWpPair
      simp [euclideanDot]
    rw [hzero]
  · -- Strong-VI transport form.
    intro σ _hσ φ
    have hzero :
        mfgOperatorEpsPair (d := d)
            (V := fun _ => (0 : ℝ))
            (H := fun _ _ _ => (0 : ℝ))
            (DpH := fun _ _ _ => (0 : Fin d → ℝ))
            (γBar := (2 : ℝ)) (ε := (0 : ℝ))
            (fun _ _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ))
            (fun i x => σ *
              ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x)
            (fun _ => (0 : ℝ))
            (fun x => σ * (φ : (Fin d → ℝ) → ℝ) x) = 0 := by
      unfold mfgOperatorEpsPair mfgOperatorPair gateauxWpPair
      simp [euclideanDot]
    rw [hzero]

/-! ## Phase 4 input bundle for Theorem 1 (`thm:main-simple.power.growth`)

This section defines `H4SimplePowerInputs`, the Phase 4 hypothesis
bundle for the simple power-growth case (paper
`Source/FGU-monotone_revised.tex`, line 314). The full chain of
intermediate steps — regularized existence (`thm:strongAepsi`), uniform
a priori bounds, weak compactness extraction, limit passage to the weak
VI for `A_0`, hemicontinuity upgrade to the strong VI, and bookkeeping
into the three clauses of `def:strong` — is formalised by the children
listed in the task's `depends_on` metadata.

The bundle packages the bridge-supplied limit data so that the
bookkeeping step `main_conclude_isStrongSolution` produces
`IsStrongSolution`. It is consumed downstream by
`simplePowerThinChain_of_paperHypotheses`, which constructs the bundle
from the paper hypotheses `(hmon, hpow, hV)` alone and feeds the
canonical public theorem `thm_main_simplePowerGrowth_paper`
(`BanachBridge.lean`).
-/

/--
**Phase 4 input bundle for the simple-power-growth chain** (paper line
314, Theorem 1).

`H4SimplePowerInputs V H DpH γBar` packages the upstream Phase 4 data
that the children (`paper:thm:strongAepsi` →
`paper:thm:apriori-simple.power.growth` →
`infra:P4-weak-compactness` → `infra:P4-limit-passage` →
`infra:P4-A0-hemicontinuous` → `main_strong_VI`) collectively produce
about the candidate limit pair `(m, u, Du)` once a Banach realization
of the bare-function pair has been chosen.

Concretely, the bundle records:

* `m`, `u` : the candidate strong-solution pair on the torus, with
  `0 ≤ᵐ m` (paper line 1292, `eq:compactness`, conservation of the
  cone constraint under weak limits);
* `Du` : an explicit weak-derivative family for `u`;
* `mLp`, `uSob` : the regularity outputs `m ∈ L^{β̄}_per`,
  `u ∈ W^{1,γ̄}_per` (paper line 315 conclusion, lines 1188–1192
  apriori bounds);
* `hRes`, `hResM`, `hFluxInt` : integrability of the HJB residual,
  residual times `m`, and the flux `m · D_pH(·, Du, m)` — these come
  from the apriori bounds + Hölder (paper lines 1188–1192) and are the
  precondition of `lem:strong.is.strong`;
* `hVI_set`, `hVI_signed`, `hVI_transport` : the three test-pair
  specializations of the strong VI for `A_0` at `(m, u, Du)`, all at
  `ε = 0`. These are the *output* of the limit-passage +
  hemicontinuity-upgrade chain (paper lines 1276–1314).

The bundle is consumed by `simplePowerThinChain_of_paperHypotheses`
(via `main_conclude_isStrongSolution`) en route to the canonical public
theorem `thm_main_simplePowerGrowth_paper`.
-/
structure H4SimplePowerInputs
    (γBar : ℝ)
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (betaBar gammaBar : ℝ≥0∞) where
  /-- Candidate density. -/
  m : (Fin d → ℝ) → ℝ
  /-- Candidate value function. -/
  u : (Fin d → ℝ) → ℝ
  /-- Explicit weak-derivative family for `u`. -/
  Du : Fin d → (Fin d → ℝ) → ℝ
  /-- `m ∈ L^{β̄}_per` (paper Theorem 1 conclusion). -/
  mLp : Periodic.MemLpPer betaBar m
  /-- `u ∈ W^{1,γ̄}_per` (paper Theorem 1 conclusion). -/
  uSob : Periodic.MemSobolevPer gammaBar u
  /-- Non-negativity of `m`, surviving the weak limit (paper line 1292,
  `eq:compactness`). -/
  m_nonneg :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ m x
  /-- Integrability of the HJB residual `u + H − V`. -/
  hRes :
    MeasureTheory.Integrable
      (StationaryMFG.Theorems.SimplePower.hjbResidual V H Du m u)
      (MeasureTheory.volume.restrict (UnitCube d))
  /-- Integrability of `(u + H − V) · m`. -/
  hResM :
    MeasureTheory.Integrable
      (fun x =>
        StationaryMFG.Theorems.SimplePower.hjbResidual V H Du m u x * m x)
      (MeasureTheory.volume.restrict (UnitCube d))
  /-- Integrability of the flux `m · D_pH(·, Du, m)`. -/
  hFluxInt :
    MeasureTheory.Integrable
      (fun x => StationaryMFG.Hamiltonian.mDpH DpH x (fun i => Du i x) (m x))
      (MeasureTheory.volume.restrict (UnitCube d))
  /-- Strong-VI set form at `ε = 0`. -/
  hVI_set :
    StationaryMFG.Theorems.SimplePower.StrongVI_setForm
      V H DpH γBar 0 Du m u
  /-- Strong-VI signed set form at `ε = 0`. -/
  hVI_signed :
    StationaryMFG.Theorems.SimplePower.StrongVI_setForm_signed
      V H DpH γBar 0 Du m u
  /-- Strong-VI transport form at `ε = 0`. -/
  hVI_transport :
    StationaryMFG.Theorems.SimplePower.StrongVI_transportForm
      V H DpH γBar 0 Du m u
  /-- `Du i` is the periodic weak derivative of `u` in direction `i`
  (the weak-gradient tie; paper `def:Sobolev`). Surfaced from the
  weak-limit bundle's `huLim_DuLim_weakDeriv`. -/
  hDu_weakDeriv :
    ∀ i, StationaryMFG.Periodic.HasWeakDerivPer (d := d) i u (Du i)
  /-- Each weak-gradient component `Du i` lies in `L^{γ̄}_per`
  (paper `def:Sobolev`). Surfaced from the weak-limit bundle's
  `hDuLim_memLp_γ`. The exponent `ENNReal.ofReal γBar` coincides with
  the `MemSobolevPer` exponent `gammaBar` at the concrete instantiation
  (`γBar = gammaBar hpow.α hpow.β`). -/
  hDu_memLp_γ :
    ∀ i, StationaryMFG.Periodic.MemLpPer (d := d)
      (ENNReal.ofReal γBar) (Du i)

end SimplePower
end Theorems
end StationaryMFG
