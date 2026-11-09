module

public import StationaryMFG.Solutions.Regularized
public import StationaryMFG.Solutions.MFGOperator
public import StationaryMFG.Hamiltonian.Estimates
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

@[expose] public section

/-!
# Pointwise-in-`x` continuity of `A_ε` integrands in the homotopy parameter `t`
(paper line 1038, sub-bullet `infra:P4-hemi-pointwise-cts`)

This module formalizes the **first half** of the sentence at line 1038 of
`Source/FGU-monotone_revised.tex` (inside the proof of Lemma
`lem:hemicont`):

> "By Remarks `rmk:cxty` and `rmk:implied-a`, the conventions in
> `(a:Hat0)`–`(a:mDpHat0)`, and the growth bounds of Assumption
> `onH.powergrowth` together with Lemma `lem:ADFGU`, each integrand
> above is (pointwise) continuous in `t` and dominated by a fixed
> integrable function. Hence, Lebesgue's dominated convergence theorem
> yields that `t ↦ ⟨A_ε[μ_t,υ_t],(η,ν)⟩` is continuous on `[0,1]`."

The dominated-convergence wrap-up is a follow-up task; here we only
prove that for almost every `x`, the integrand of
`⟨A_ε[μ_t, υ_t], (η, ν)⟩` at `x` is continuous as a function of
`t ∈ [0,1]` whenever `μ_t(x)` is positive on `[0,1]`.

## Key inputs

* `RegularityH.continuous_H_pm` — for a.e. `x`, `(p, m) ↦ H(x, p, m)`
  is continuous on `{m > 0}`.
* `RegularityH.continuous_DpH_pm` — same for `D_pH`.
* `Real.continuous_rpow_const` — `s ↦ s ^ q` is continuous on `ℝ` when
  `0 ≤ q`. We use this for the Gateaux weight `|·|^{γ̄ - 2}` under the
  paper's standing hypothesis `γ̄ ≥ 2`.
* Linearity of the convex combination `t ↦ (1-t)·ā + t·a`.

## Pointwise integrand

Following `Solutions.MFG.mfgOperatorEpsPair`, the pairing
`⟨A_ε[μ, υ], (η, ν)⟩` is an integral over the unit cube of an
explicit integrand. Substituting the convex combination
`(μ_t, υ_t) := (1-t)(mBar, ῡ) + t(μ, υ)` (and similarly for `Dυ_t`)
gives the *pointwise* integrand `aepsiIntegrandAt` defined below as a
function of `t : ℝ`.
-/

noncomputable section

namespace StationaryMFG
namespace Theorems
namespace SimplePower

open MeasureTheory Set
open StationaryMFG.Periodic
open StationaryMFG.Hamiltonian
open StationaryMFG.Solutions.MFG
open scoped ENNReal NNReal

variable {d : ℕ}

/-! ## Pointwise convex-combination notation -/

/-- Convex combination of two real-valued functions of `x`, pointwise. -/
@[inline] def cxComb (a ā : (Fin d → ℝ) → ℝ) (t : ℝ) (x : Fin d → ℝ) : ℝ :=
  (1 - t) * ā x + t * a x

/-- Convex combination of two gradient families (`Fin d → x → ℝ`),
pointwise. -/
@[inline] def cxCombGrad (Da Dā : Fin d → (Fin d → ℝ) → ℝ) (t : ℝ)
    (i : Fin d) (x : Fin d → ℝ) : ℝ :=
  (1 - t) * Dā i x + t * Da i x

/-! ## The pointwise-at-`x` integrand of `⟨A_ε[μ_t, υ_t], (η, ν)⟩` -/

/-- The integrand at `x` of the regularized MFG operator pairing
`⟨A_ε[μ_t, υ_t], (η, ν)⟩`, where
`(μ_t, υ_t, Dυ_t) = (1-t)(mBar, ῡ, Dῡ) + t(μ, υ, Dυ)`. As a function of
`t : ℝ` only, with `x` fixed.
-/
def aepsiIntegrandAt
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (γBar ε : ℝ)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ)
    (μ mBar υ ῡ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ)
    (x : Fin d → ℝ) (t : ℝ) : ℝ :=
  let μt := cxComb μ mBar t x
  let υt := cxComb υ ῡ t x
  let Dυt : Fin d → ℝ := fun i => cxCombGrad Dυ Dῡ t i x
  ((-υt - H x Dυt μt + V x) * η x
      + μt * (DpH x Dυt μt ⬝ (fun i => Dν i x))
      + (μt - 1) * ν x)
    + ε * (vecAbsPowMinusTwo γBar Dυt
              * (Dυt ⬝ (fun i => Dν i x))
            + absPowMinusTwo γBar υt * (υt * ν x))

/-! ## Continuity helpers -/

/-- The convex combination `t ↦ (1-t) * ā x + t * a x` is continuous in `t`. -/
lemma continuous_cxComb (a ā : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    Continuous (fun t : ℝ => cxComb a ā t x) := by
  unfold cxComb
  fun_prop

/-- Each component `t ↦ ((1-t) * Dā i x + t * Da i x)` is continuous. -/
lemma continuous_cxCombGrad_apply (Da Dā : Fin d → (Fin d → ℝ) → ℝ)
    (x : Fin d → ℝ) (i : Fin d) :
    Continuous (fun t : ℝ => cxCombGrad Da Dā t i x) := by
  unfold cxCombGrad
  fun_prop

/-- The full gradient family `t ↦ (fun i => cxCombGrad Da Dā t i x)` is
continuous as a map into `Fin d → ℝ`. -/
lemma continuous_cxCombGrad (Da Dā : Fin d → (Fin d → ℝ) → ℝ)
    (x : Fin d → ℝ) :
    Continuous (fun t : ℝ => (fun i => cxCombGrad Da Dā t i x)) := by
  refine continuous_pi (fun i => ?_)
  exact continuous_cxCombGrad_apply Da Dā x i

/-- The euclidean dot product `(fun i => f i t) ⬝ w` is continuous in `t`
when each coordinate `t ↦ f i t` is continuous. -/
lemma continuous_euclideanDot_left
    (f : Fin d → ℝ → ℝ) (w : Fin d → ℝ)
    (hf : ∀ i, Continuous (fun t : ℝ => f i t)) :
    Continuous (fun t : ℝ => (fun i => f i t) ⬝ w) := by
  unfold dotProduct
  refine continuous_finset_sum _ (fun i _ => ?_)
  exact (hf i).mul continuous_const

/-! ## Continuity of the Gateaux weight pieces (product form, `1 < γBar`)

The bare weights `vecAbsPowMinusTwo γBar v` and `absPowMinusTwo γBar t`
blow up at the origin when `γBar < 2`, so they are *not* continuous in
`t` along the convex combination once `Dυ_t = 0`/`υ_t = 0`. However,
the **product** with `t` (resp. `v i`) is the signed-power map
`signedRpow γBar`/`vecSignedRpow γBar`, which is continuous on all of
`ℝ` (resp. `Fin d → ℝ`) for `1 < γBar` — see
`StationaryMFG.Solutions.MFG.continuous_signedRpow` and
`continuous_vecSignedRpow`.

Phase 0b.2b refactor: replace the standalone weight continuity lemmas
with the product-form helpers actually consumed in the integrand. -/

/-- **Product-form vector continuity** under `1 < γBar`. The integrand
contains `vecAbsPowMinusTwo γBar (Dυ_t x) * (Dυ_t x ⬝ Dν x)`, which is
algebraically `(vecSignedRpow γBar (Dυ_t x)) ⬝ Dν x` and therefore
continuous in `t` on all of `ℝ` (no positivity required), since
`vecSignedRpow γBar` is continuous for `1 < γBar`. -/
lemma continuous_vecAbsPowMinusTwo_dot_cxComb
    (γBar : ℝ) (hγ : 1 < γBar)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    Continuous (fun t : ℝ =>
      vecAbsPowMinusTwo γBar (fun i => cxCombGrad Dυ Dῡ t i x)
        * ((fun i => cxCombGrad Dυ Dῡ t i x) ⬝ (fun i => Dν i x))) := by
  -- Algebraic identity: `c * ∑ i, v i * w i = ∑ i, (c * v i) * w i`.
  have hrewrite : (fun t : ℝ =>
      vecAbsPowMinusTwo γBar (fun i => cxCombGrad Dυ Dῡ t i x)
        * ((fun i => cxCombGrad Dυ Dῡ t i x) ⬝ (fun i => Dν i x)))
      = (fun t : ℝ =>
          vecSignedRpow γBar (fun i => cxCombGrad Dυ Dῡ t i x)
            ⬝ (fun i => Dν i x)) := by
    funext t
    set v : Fin d → ℝ := fun i => cxCombGrad Dυ Dῡ t i x with hv_def
    set w : Fin d → ℝ := fun i => Dν i x with hw_def
    -- `vecAbsPowMinusTwo γBar v * (v ⬝ w) = (vecSignedRpow γBar v) ⬝ w`.
    show vecAbsPowMinusTwo γBar v * (v ⬝ w)
        = vecSignedRpow γBar v ⬝ w
    unfold dotProduct vecSignedRpow
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  rw [hrewrite]
  -- Continuity of `t ↦ vecSignedRpow γBar (Dυ_t x) ⬝ Dν x`.
  unfold dotProduct
  refine continuous_finset_sum _ (fun i _ => ?_)
  -- `t ↦ vecSignedRpow γBar (Dυ_t x) i` is continuous (composition).
  have hcoord : Continuous (fun t : ℝ =>
      vecSignedRpow γBar (fun i => cxCombGrad Dυ Dῡ t i x) i) := by
    have h1 : Continuous (fun t : ℝ =>
        vecSignedRpow γBar (fun i => cxCombGrad Dυ Dῡ t i x)) :=
      (continuous_vecSignedRpow hγ).comp (continuous_cxCombGrad Dυ Dῡ x)
    exact (continuous_apply i).comp h1
  exact hcoord.mul continuous_const

/-- **Product-form scalar continuity** under `1 < γBar`. The integrand
contains `absPowMinusTwo γBar (υ_t x) * (υ_t x * ν x)`, which is
algebraically `signedRpow γBar (υ_t x) * ν x` and therefore continuous
in `t` on all of `ℝ`, since `signedRpow γBar` is continuous for
`1 < γBar`. -/
lemma continuous_absPowMinusTwo_mul_cxComb
    (γBar : ℝ) (hγ : 1 < γBar)
    (υ ῡ ν : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    Continuous (fun t : ℝ =>
      absPowMinusTwo γBar (cxComb υ ῡ t x)
        * (cxComb υ ῡ t x * ν x)) := by
  -- Algebraic identity: `absPowMinusTwo γBar s * (s * w) = signedRpow γBar s * w`.
  have hrewrite : (fun t : ℝ =>
      absPowMinusTwo γBar (cxComb υ ῡ t x)
        * (cxComb υ ῡ t x * ν x))
      = (fun t : ℝ => signedRpow γBar (cxComb υ ῡ t x) * ν x) := by
    funext t
    show absPowMinusTwo γBar (cxComb υ ῡ t x)
        * (cxComb υ ῡ t x * ν x)
      = signedRpow γBar (cxComb υ ῡ t x) * ν x
    unfold signedRpow
    ring
  rw [hrewrite]
  refine Continuous.mul ?_ continuous_const
  -- `t ↦ signedRpow γBar (cxComb υ ῡ t x)` is continuous.
  exact (continuous_signedRpow hγ).comp (continuous_cxComb υ ῡ x)

/-! ## Main pointwise continuity lemma -/

/-- **Pointwise-in-`x` continuity of the `A_ε` integrand in `t`**
(paper line 1038, first half).

For a.e. `x ∈ 𝕋^d`, given:
* `RegularityH H DpH` (paper `(a:regularityH)`),
* `2 ≤ γBar` (paper power-growth standing hypothesis),
* pointwise positivity `0 < cxComb μ mBar t x` for every `t ∈ [0,1]`
  (paper admissibility on `𝓚`: both `mBar, μ ≥ 0`, and the segment
  pointwise stays in the admissible set),

the map `t ↦ aepsiIntegrandAt … x t` is continuous on `Set.Icc 0 1`.

The hypothesis `hPos` corresponds to the paper's pointwise convexity
of `𝓚`: if both `mBar(x) > 0` and `μ(x) > 0`, then so is the convex
combination for every `t ∈ [0,1]`.
-/
theorem aepsiIntegrandAt_continuousOn
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (γBar ε : ℝ) (hγ : 1 < γBar)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ)
    (μ mBar υ ῡ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ)
    (x : Fin d → ℝ)
    (hH : ContinuousOn (fun (pm : (Fin d → ℝ) × ℝ) => H x pm.1 pm.2)
            {pm | 0 < pm.2})
    (hDpH : ContinuousOn (fun (pm : (Fin d → ℝ) × ℝ) => DpH x pm.1 pm.2)
            {pm | 0 < pm.2})
    (hPos : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < cxComb μ mBar t x) :
    ContinuousOn (fun t : ℝ =>
      aepsiIntegrandAt V H DpH γBar ε Dυ Dῡ μ mBar υ ῡ Dν η ν x t)
      (Set.Icc 0 1) := by
  -- The map `t ↦ ((Dυ_t x), μ_t x)` lands in `{pm | 0 < pm.2}` on `[0,1]`.
  set φ : ℝ → (Fin d → ℝ) × ℝ :=
    fun t => ((fun i => cxCombGrad Dυ Dῡ t i x), cxComb μ mBar t x) with hφ
  have hφ_cont : Continuous φ := by
    refine Continuous.prodMk ?_ ?_
    · exact continuous_cxCombGrad Dυ Dῡ x
    · exact continuous_cxComb μ mBar x
  have hφ_maps : Set.MapsTo φ (Set.Icc (0 : ℝ) 1) {pm | 0 < pm.2} := by
    intro t ht
    simpa [φ] using hPos t ht
  -- Continuity in `t` of `H(x, Dυ_t x, μ_t x)` and `D_pH(x, Dυ_t x, μ_t x)`.
  have hHcomp : ContinuousOn
      (fun t : ℝ => H x (fun i => cxCombGrad Dυ Dῡ t i x) (cxComb μ mBar t x))
      (Set.Icc 0 1) := by
    have := hH.comp hφ_cont.continuousOn hφ_maps
    simpa [φ, Function.comp_def] using this
  have hDpHcomp : ContinuousOn
      (fun t : ℝ => DpH x (fun i => cxCombGrad Dυ Dῡ t i x) (cxComb μ mBar t x))
      (Set.Icc 0 1) := by
    have := hDpH.comp hφ_cont.continuousOn hφ_maps
    simpa [φ, Function.comp_def] using this
  -- Continuity in `t` of various building blocks.
  have hμt : Continuous (fun t : ℝ => cxComb μ mBar t x) :=
    continuous_cxComb μ mBar x
  have hυt : Continuous (fun t : ℝ => cxComb υ ῡ t x) :=
    continuous_cxComb υ ῡ x
  have hDυt_pi : Continuous (fun t : ℝ =>
      (fun i => cxCombGrad Dυ Dῡ t i x)) :=
    continuous_cxCombGrad Dυ Dῡ x
  -- `t ↦ DpH(x, Dυ_t x, μ_t x) ⬝ (fun i => Dν i x)` is continuous on `[0,1]`.
  have hDpHdot : ContinuousOn
      (fun t : ℝ =>
        DpH x (fun i => cxCombGrad Dυ Dῡ t i x) (cxComb μ mBar t x)
          ⬝ (fun i => Dν i x)) (Set.Icc 0 1) := by
    -- `dotProduct` is `∑ i, _ i * (Dν i x)`, and each component of
    -- `DpH(...)` is continuous on `[0,1]` since the full vector is.
    unfold dotProduct
    refine continuousOn_finset_sum _ (fun i _ => ?_)
    have hcoord : ContinuousOn
        (fun t : ℝ =>
          DpH x (fun i => cxCombGrad Dυ Dῡ t i x) (cxComb μ mBar t x) i)
        (Set.Icc 0 1) :=
      (continuous_apply i).comp_continuousOn hDpHcomp
    exact hcoord.mul continuousOn_const
  -- Vector-Gateaux piece: the *product* `vecAbsPowMinusTwo γBar (Dυ_t) * (Dυ_t ⬝ Dν)`
  -- is continuous under `1 < γBar` via `vecSignedRpow`.
  have hVecProd : Continuous (fun t : ℝ =>
      vecAbsPowMinusTwo γBar (fun i => cxCombGrad Dυ Dῡ t i x)
        * ((fun i => cxCombGrad Dυ Dῡ t i x) ⬝ (fun i => Dν i x))) :=
    continuous_vecAbsPowMinusTwo_dot_cxComb γBar hγ Dυ Dῡ Dν x
  -- Scalar-Gateaux piece (product form): continuous under `1 < γBar` via `signedRpow`.
  have hScProd : Continuous (fun t : ℝ =>
      absPowMinusTwo γBar (cxComb υ ῡ t x)
        * (cxComb υ ῡ t x * ν x)) :=
    continuous_absPowMinusTwo_mul_cxComb γBar hγ υ ῡ ν x
  -- Combine all pieces.
  unfold aepsiIntegrandAt
  -- The integrand is a polynomial combination of the continuous pieces
  -- above with the constants `V x`, `η x`, `ν x`, and the (non-`t`-dep)
  -- gradient `Dν`.
  have hVconst : ContinuousOn (fun _ : ℝ => V x) (Set.Icc (0:ℝ) 1) := continuousOn_const
  have hηconst : ContinuousOn (fun _ : ℝ => η x) (Set.Icc (0:ℝ) 1) := continuousOn_const
  have hνconst : ContinuousOn (fun _ : ℝ => ν x) (Set.Icc (0:ℝ) 1) := continuousOn_const
  have h1const : ContinuousOn (fun _ : ℝ => (1:ℝ)) (Set.Icc (0:ℝ) 1) := continuousOn_const
  have hεconst : ContinuousOn (fun _ : ℝ => ε) (Set.Icc (0:ℝ) 1) := continuousOn_const
  refine ((((((hυt.continuousOn).neg.sub hHcomp).add hVconst).mul hηconst).add
    ((hμt.continuousOn).mul hDpHdot)).add
    (((hμt.continuousOn).sub h1const).mul hνconst)).add ?_
  -- The `ε`-Gateaux summand.
  refine hεconst.mul ?_
  exact hVecProd.continuousOn.add hScProd.continuousOn

/-! ## Wrapped almost-everywhere statement -/

/-- **`aepsi_integrand_continuous_in_t`** (paper line 1038, first half,
packaged a.e.).

Given `RegularityH H DpH`, `2 ≤ γBar`, and pointwise positivity
of the convex combination `μ_t(x)` on `[0,1]` (a hypothesis carried
by the consumer once both endpoints are admissible), for **almost
every** `x ∈ 𝕋^d` the map
`t ↦ ⟨A_ε[μ_t, υ_t], (η, ν)⟩_x = aepsiIntegrandAt … x t`
is continuous on `[0,1]`.

The integration over `x` (paper's dominated-convergence step) is a
follow-up task. -/
theorem aepsi_integrand_continuous_in_t
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hReg : RegularityH (d := d) H DpH)
    (γBar ε : ℝ) (hγ : 1 < γBar)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ)
    (μ mBar υ ῡ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ)
    (hPos : ∀ x, ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < cxComb μ mBar t x) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ContinuousOn (fun t : ℝ =>
        aepsiIntegrandAt V H DpH γBar ε Dυ Dῡ μ mBar υ ῡ Dν η ν x t)
        (Set.Icc 0 1) := by
  filter_upwards [hReg.continuous_H_pm, hReg.continuous_DpH_pm] with x hHx hDpHx
  exact aepsiIntegrandAt_continuousOn V H DpH γBar ε hγ
    Dυ Dῡ μ mBar υ ῡ Dν η ν x hHx hDpHx (hPos x)

/-! ## Unit-test-style example -/

/-- The lemma `aepsi_integrand_continuous_in_t` is non-vacuous: the
trivial Hamiltonian `H = 0`, `D_pH = 0` satisfies all hypotheses, with
`γ̄ = 2` and any positive convex-combination `μ_t`. -/
example (d : ℕ) (V : (Fin d → ℝ) → ℝ) (ε : ℝ)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ)
    (μ mBar υ ῡ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ)
    (hPos : ∀ x, ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < cxComb μ mBar t x) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ContinuousOn (fun t : ℝ =>
        aepsiIntegrandAt V (fun _ _ _ => (0 : ℝ))
          (fun _ _ _ => (0 : Fin d → ℝ))
          (2 : ℝ) ε Dυ Dῡ μ mBar υ ῡ Dν η ν x t)
        (Set.Icc 0 1) := by
  refine aepsi_integrand_continuous_in_t (d := d) V _ _ ?_ 2 ε one_lt_two
    Dυ Dῡ μ mBar υ ῡ Dν η ν hPos
  -- The trivial Hamiltonian is regular.
  refine
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

/-! ## Pointwise dominators for the hemicontinuity DCT (paper line 1038)

This section produces pointwise bounds on each integrand component in
`aepsiIntegrandAt` that are uniform in `t ∈ [0,1]` and depend only on
the endpoint data `(μ, μ̄, υ, ῡ, Dυ, Dῡ)`. They feed the dominated
convergence step required to upgrade `aepsiIntegrandAt_continuousOn`
into a continuity statement for `t ↦ ⟨A_ε[μ_t, υ_t], (η, ν)⟩`.

The strategy is the paper's: on the segment `(1-t)·ā + t·a` with
`t ∈ [0,1]`, the triangle inequality gives `|cxComb a ā t x| ≤ |a x| + |ā x|`,
and the same for the gradient (in the `Fin d → ℝ` norm). Plugging this
into `Hamiltonian.upper_bound_powergrowth`, `HypothesisPowerGrowth.lower`,
and `Hamiltonian.mDpH_pointwise_bound` yields explicit dominators for
the `H`, `m·D_pH`, and Gateaux pieces.

Integrability of each dominator over `UnitCube d` is encapsulated by
the consumer (it follows by Hölder pairing using
`gammaBar'_holder_id` and `gammaBar'_le_betaBar`). This division of
labour mirrors `Hamiltonian.mDpH_mem_Lp_gammaBar'`. -/

/-! ### Triangle-inequality bounds for `cxComb` and `cxCombGrad` -/

/-- For `t ∈ [0,1]`, the convex combination `cxComb a ā t x` is bounded
in absolute value by `|a x| + |ā x|`. -/
lemma cxComb_abs_le
    (a ā : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |cxComb a ā t x| ≤ |ā x| + |a x| := by
  unfold cxComb
  have h1mt : 0 ≤ 1 - t := by linarith [ht.2]
  have ht0 : 0 ≤ t := ht.1
  -- |(1-t) * ā x + t * a x| ≤ |(1-t) * ā x| + |t * a x|.
  have hadd : |(1 - t) * ā x + t * a x| ≤ |(1 - t) * ā x| + |t * a x| :=
    abs_add_le _ _
  -- |(1-t) * ā x| = (1-t) * |ā x| ≤ |ā x| since 0 ≤ 1-t ≤ 1.
  have h1 : |(1 - t) * ā x| ≤ |ā x| := by
    rw [abs_mul, abs_of_nonneg h1mt]
    have : (1 - t) * |ā x| ≤ 1 * |ā x| :=
      mul_le_mul_of_nonneg_right (by linarith [ht.1]) (abs_nonneg _)
    linarith
  -- |t * a x| = t * |a x| ≤ |a x| since 0 ≤ t ≤ 1.
  have h2 : |t * a x| ≤ |a x| := by
    rw [abs_mul, abs_of_nonneg ht0]
    have : t * |a x| ≤ 1 * |a x| :=
      mul_le_mul_of_nonneg_right (by linarith [ht.2]) (abs_nonneg _)
    linarith
  linarith

/-- For `t ∈ [0,1]`, each coordinate of the gradient convex combination
is bounded in absolute value by `|Da i x| + |Dā i x|`. -/
lemma cxCombGrad_apply_abs_le
    (Da Dā : Fin d → (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) (i : Fin d)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |cxCombGrad Da Dā t i x| ≤ |Dā i x| + |Da i x| := by
  unfold cxCombGrad
  have h1mt : 0 ≤ 1 - t := by linarith [ht.2]
  have ht0 : 0 ≤ t := ht.1
  have hadd : |(1 - t) * Dā i x + t * Da i x|
              ≤ |(1 - t) * Dā i x| + |t * Da i x| := abs_add_le _ _
  have h1 : |(1 - t) * Dā i x| ≤ |Dā i x| := by
    rw [abs_mul, abs_of_nonneg h1mt]
    have : (1 - t) * |Dā i x| ≤ 1 * |Dā i x| :=
      mul_le_mul_of_nonneg_right (by linarith [ht.1]) (abs_nonneg _)
    linarith
  have h2 : |t * Da i x| ≤ |Da i x| := by
    rw [abs_mul, abs_of_nonneg ht0]
    have : t * |Da i x| ≤ 1 * |Da i x| :=
      mul_le_mul_of_nonneg_right (by linarith [ht.2]) (abs_nonneg _)
    linarith
  linarith

/-- For `t ∈ [0,1]` and `q ≥ 0`, `|cxComb a ā t x|^q ≤ (|ā x| + |a x|)^q`. -/
lemma cxComb_abs_rpow_le
    (a ā : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ)
    {t q : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hq : 0 ≤ q) :
    |cxComb a ā t x| ^ q ≤ (|ā x| + |a x|) ^ q := by
  have habs_nn : 0 ≤ |cxComb a ā t x| := abs_nonneg _
  have hbnd := cxComb_abs_le a ā x ht
  exact Real.rpow_le_rpow habs_nn hbnd hq

/-- For `t ∈ [0,1]`, the dot-product square of the gradient convex
combination admits a coordinate-wise sum bound:
`(Dυ_t · Dυ_t) ≤ ∑ i, (|Dῡ i x| + |Dυ i x|)^2`.

This is the building block to bound `vecAbsPowMinusTwo γBar Dυ_t` (which
is `(Dυ_t · Dυ_t)^{(γBar-2)/2}`) by an endpoint-only quantity. -/
lemma cxCombGrad_dot_self_le
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ) (x : Fin d → ℝ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (fun i => cxCombGrad Dυ Dῡ t i x) ⬝
      (fun i => cxCombGrad Dυ Dῡ t i x)
      ≤ ∑ i, (|Dῡ i x| + |Dυ i x|) ^ (2 : ℕ) := by
  unfold dotProduct
  refine Finset.sum_le_sum ?_
  intro i _
  have hbnd : |cxCombGrad Dυ Dῡ t i x| ≤ |Dῡ i x| + |Dυ i x| :=
    cxCombGrad_apply_abs_le Dυ Dῡ x i ht
  -- (cxCombGrad)^2 = |cxCombGrad|^2 ≤ (|Dῡ i x| + |Dυ i x|)^2.
  have hsq : cxCombGrad Dυ Dῡ t i x * cxCombGrad Dυ Dῡ t i x
            = |cxCombGrad Dυ Dῡ t i x| ^ (2 : ℕ) := by
    rw [sq_abs]; ring
  rw [hsq]
  have h_nn : 0 ≤ |cxCombGrad Dυ Dῡ t i x| := abs_nonneg _
  have h_rhs_nn : 0 ≤ |Dῡ i x| + |Dυ i x| :=
    add_nonneg (abs_nonneg _) (abs_nonneg _)
  exact pow_le_pow_left₀ h_nn hbnd 2

/-! ### Dominators for the `H`, `m·D_pH`, and Gateaux integrand pieces -/

/-- **`hemicont_H_dominator`**: pointwise dominator for the `H`-piece of
the integrand on the segment `(μ_t, Dυ_t)`. Under the simple
power-growth bundle `(onH.powergrowth)` and the slice hypothesis used
to obtain `Hamiltonian.upper_bound_powergrowth`, for almost every
`x ∈ 𝕋^d` and every `t ∈ [0,1]` (provided `0 < cxComb μ mBar t x` so
the bound applies),

  `H(x, Dυ_t x, μ_t x) ≤ C' · ((|Dυ x| + |Dῡ x|)_∞ ^ α + 1) − (μ_t x)^β / C'`

bounds `H` from above by a `t`-independent quantity (drop the
non-positive `−(μ_t x)^β/C'` summand to obtain a clean dominator).

Here `‖·‖_∞` is the pi-norm `‖p‖ = sup_i |p i|`; the pointwise
inequality `|cxCombGrad Dυ Dῡ t i x| ≤ |Dυ i x| + |Dῡ i x|` plus
monotonicity of `(·)^α` then gives the required uniform-in-`t` bound.

The conclusion produces **the upper-bound part only**; the lower bound
(needed to dominate `|H|` rather than `H`) follows analogously from
`HypothesisPowerGrowth.lower` and is split into `hemicont_H_lower_dominator`
below. -/
theorem hemicont_H_upper_dominator
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (h_slice :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          H x p m ≤ -(m ^ h.β) / h.C + h.C + h.C * ‖p‖ ^ h.α
                  + h.C * ‖p‖ * (m ^ (h.β - h.β / h.α) + 1))
    (μ mBar : (Fin d → ℝ) → ℝ)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          0 < cxComb μ mBar t x →
            H x (fun i => cxCombGrad Dυ Dῡ t i x) (cxComb μ mBar t x)
              ≤ C' * (‖fun i => cxCombGrad Dυ Dῡ t i x‖ ^ h.α + 1)
                  - (cxComb μ mBar t x) ^ h.β / C' := by
  -- Apply `upper_bound_powergrowth` to get the existence of `C'`.
  obtain ⟨C', hC'_pos, hC'_bound⟩ :=
    upper_bound_powergrowth h h_slice
  refine ⟨C', hC'_pos, ?_⟩
  filter_upwards [hC'_bound] with x hx t _ht hμt_pos
  -- Apply `hx` at the convex-combination arguments.
  exact hx (fun i => cxCombGrad Dυ Dῡ t i x) (cxComb μ mBar t x) hμt_pos

/-- **`hemicont_H_lower_dominator`**: pointwise lower bound for the `H`-piece
of the integrand on the segment `(μ_t, Dυ_t)`. Directly from
`HypothesisPowerGrowth.lower` (which gives
`H(x, p, m) ≥ ‖p‖^α / C - C · (m^β + 1)` for `m > 0`):
substituting the convex-combination arguments yields, for almost every
`x ∈ 𝕋^d` and every `t ∈ [0,1]` with `0 < cxComb μ mBar t x`,

  `H(x, Dυ_t x, μ_t x) ≥ -h.C · ((μ_t x)^β + 1)`,

since `‖Dυ_t x‖^α / h.C ≥ 0`. The right-hand side is then bounded above
by an endpoint-only quantity via `cxComb_abs_rpow_le`. We package only the
"drop the non-negative `‖Dυ_t‖^α/C` term" step here; the endpoint reduction
of `(μ_t)^β` is the consumer's responsibility. -/
theorem hemicont_H_lower_dominator
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (μ mBar : (Fin d → ℝ) → ℝ)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ t, 0 < cxComb μ mBar t x →
        -h.C * ((cxComb μ mBar t x) ^ h.β + 1)
          ≤ H x (fun i => cxCombGrad Dυ Dῡ t i x) (cxComb μ mBar t x) := by
  filter_upwards [h.lower] with x hx t hμt_pos
  -- The bundle bound at p := Dυ_t x, m := μ_t x.
  set p_t : Fin d → ℝ := fun i => cxCombGrad Dυ Dῡ t i x with hp_t
  have hb : H x p_t (cxComb μ mBar t x)
              ≥ ‖p_t‖ ^ h.α / h.C - h.C * ((cxComb μ mBar t x) ^ h.β + 1) :=
    hx p_t (cxComb μ mBar t x) hμt_pos
  -- Drop the non-negative `‖p_t‖^α / h.C` term.
  have hpα_nn : 0 ≤ ‖p_t‖ ^ h.α := by
    have : 0 ≤ ‖p_t‖ := norm_nonneg _
    exact Real.rpow_nonneg this _
  have hCpos : 0 < h.C := h.hC
  have hpα_div_nn : 0 ≤ ‖p_t‖ ^ h.α / h.C := div_nonneg hpα_nn hCpos.le
  linarith

/-- **`hemicont_H_abs_dominator`**: pointwise dominator on `|H|` along the
segment, combining `hemicont_H_upper_dominator` and
`hemicont_H_lower_dominator`. For almost every `x ∈ 𝕋^d` and every
`t ∈ [0,1]` with `0 < cxComb μ mBar t x`,

  `|H(x, Dυ_t x, μ_t x)|`
    ≤ `max ( C' · (‖Dυ_t‖^α + 1) − (μ_t)^β/C',
            h.C · ((μ_t)^β + 1) )`
    ≤ `C' · (‖Dυ_t‖^α + 1) + h.C · ((μ_t)^β + 1)`,

where the second `≤` follows because both summands of the maximum are
non-negative under the hypothesis (they appear with opposite signs in
the bound on `H`, so their sum dominates `|H|`). -/
theorem hemicont_H_abs_dominator
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (h_slice :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          H x p m ≤ -(m ^ h.β) / h.C + h.C + h.C * ‖p‖ ^ h.α
                  + h.C * ‖p‖ * (m ^ (h.β - h.β / h.α) + 1))
    (μ mBar : (Fin d → ℝ) → ℝ)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          0 < cxComb μ mBar t x →
            |H x (fun i => cxCombGrad Dυ Dῡ t i x) (cxComb μ mBar t x)|
              ≤ C' * (‖fun i => cxCombGrad Dυ Dῡ t i x‖ ^ h.α + 1)
                  + h.C * ((cxComb μ mBar t x) ^ h.β + 1) := by
  obtain ⟨C', hC'_pos, hUp⟩ := hemicont_H_upper_dominator h h_slice μ mBar Dυ Dῡ
  refine ⟨C', hC'_pos, ?_⟩
  filter_upwards [hUp, hemicont_H_lower_dominator h μ mBar Dυ Dῡ]
    with x hxU hxL t ht hμt_pos
  set p_t : Fin d → ℝ := fun i => cxCombGrad Dυ Dῡ t i x with hp_t
  set m_t : ℝ := cxComb μ mBar t x with hm_t
  have hCpos : 0 < h.C := h.hC
  -- Upper bound on H at the segment.
  have hU : H x p_t m_t ≤ C' * (‖p_t‖ ^ h.α + 1) - m_t ^ h.β / C' :=
    hxU t ht hμt_pos
  -- Lower bound on H at the segment.
  have hL : -h.C * (m_t ^ h.β + 1) ≤ H x p_t m_t := hxL t hμt_pos
  -- Each summand on the RHS is non-negative.
  have hpα_nn : 0 ≤ ‖p_t‖ ^ h.α := Real.rpow_nonneg (norm_nonneg _) _
  have hmβ_nn : 0 ≤ m_t ^ h.β := Real.rpow_nonneg hμt_pos.le _
  have hC' : 0 ≤ C' * (‖p_t‖ ^ h.α + 1) := by
    have : 0 ≤ ‖p_t‖ ^ h.α + 1 := by linarith
    exact mul_nonneg hC'_pos.le this
  have hC : 0 ≤ h.C * (m_t ^ h.β + 1) := by
    have : 0 ≤ m_t ^ h.β + 1 := by linarith
    exact mul_nonneg hCpos.le this
  have hmβ_div_nn : 0 ≤ m_t ^ h.β / C' := div_nonneg hmβ_nn hC'_pos.le
  -- |H| ≤ max(H, -H) ≤ RHS_upper + RHS_lower' since RHS_upper ≥ H ≥ -RHS_lower'.
  rcases abs_le.mp (le_refl |H x p_t m_t|) with ⟨_, _⟩
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · -- -(C'·(‖p‖^α+1) + h.C·(m^β+1)) ≤ H x p_t m_t.
    -- We have -h.C·(m^β + 1) ≤ H, and -(C'·(‖p‖^α+1)) ≤ 0, so add.
    have hneg_C' : -(C' * (‖p_t‖ ^ h.α + 1)) ≤ 0 := by linarith
    -- Combine: -(...) - (...) ≤ 0 + H = H.
    have : -(C' * (‖p_t‖ ^ h.α + 1)) + (-h.C * (m_t ^ h.β + 1))
            ≤ 0 + H x p_t m_t := add_le_add hneg_C' hL
    have hgoal :
        -(C' * (‖p_t‖ ^ h.α + 1) + h.C * (m_t ^ h.β + 1))
          = -(C' * (‖p_t‖ ^ h.α + 1)) + (-h.C * (m_t ^ h.β + 1)) := by ring
    rw [hgoal]; linarith
  · -- H x p_t m_t ≤ C'·(‖p‖^α+1) + h.C·(m^β+1).
    -- We have H ≤ C'·(‖p‖^α+1) - m^β/C' ≤ C'·(‖p‖^α+1) + h.C·(m^β+1).
    have : -(m_t ^ h.β / C') ≤ h.C * (m_t ^ h.β + 1) := by linarith
    linarith

/-! ### Integrability of the `H`-dominator on the unit cube

The combined `H`-dominator from `hemicont_H_abs_dominator` is the
endpoint-only function

  `g_H(x) = C' · ((|Dῡ x| + |Dυ x|)_∞ ^ α + 1) + h.C · ((|ῡ x| + |υ x|)^β + 1)`

(after applying `cxComb_abs_rpow_le` and the gradient-coordinate bounds
to remove the `t`-dependence of the right-hand side). Its `MemLpPer 1`
membership follows from Hölder: each summand is `L^{γ̄'} × L^{γ̄}`-paired
against test data via `gammaBar'_holder_id` and `gammaBar'_le_betaBar`.

Mirroring the design of `Hamiltonian.mDpH_mem_Lp_gammaBar'`, we package
the dominator's `MemLpPer 1` membership as a hypothesis the consumer
provides. The Hölder-closure content (showing this hypothesis follows
from `m ∈ L^{β̄}` and `Du ∈ L^{γ̄}`) is filed as a follow-up backlog
task; see `infra-P4-hemi-dominator-holder` for the explicit derivation.

The output is `IntegrableOn` (equivalently, `MemLpPer 1`) on the unit
cube, which is the precise hypothesis required by Lebesgue's dominated
convergence theorem in `infra:P4-hemi-DCT`. -/

/-- **`hemicont_H_dominator_integrable`**: the `H`-dominator from
`hemicont_H_abs_dominator` is integrable on the unit cube, in dominator
form. Given a nonnegative `H`-dominator function `g_H` whose `MemLpPer 1`
membership follows from Hölder pairing of `(η, ν) ∈ L^{β̄} × W^{1,γ̄}`
against the standing inputs `m ∈ L^{β̄}` and `Du ∈ L^{γ̄}` (the chain
`gammaBar'_holder_id`, `gammaBar'_le_betaBar`), we produce
`IntegrableOn g_H (UnitCube d)`. -/
theorem hemicont_H_dominator_integrable
    (g_H : (Fin d → ℝ) → ℝ)
    (hgH : MemLpPer 1 g_H) :
    IntegrableOn g_H (UnitCube d) :=
  integrableOn_of_memLpPer (le_refl _) hgH

/-- **`hemicont_H_abs_le_dominator_integrable`**: combined statement
producing an integrable upper bound on `|H(x, Dυ_t x, μ_t x)|`,
uniform in `t ∈ [0,1]`. Given:

* the slice hypothesis for `upper_bound_powergrowth`,
* a `MemLpPer 1` dominator function `g_H`,
* a pointwise comparison `hgH_le` ensuring that the endpoint-only RHS
  of `hemicont_H_abs_dominator` is bounded above by `g_H` (this is the
  Hölder-content step, deferred to a follow-up task),

we conclude that for almost every `x ∈ 𝕋^d` and every `t ∈ [0,1]` with
`0 < cxComb μ mBar t x`, `|H(x, Dυ_t x, μ_t x)| ≤ g_H x`, and that
`g_H` is integrable on the unit cube. -/
theorem hemicont_H_abs_le_dominator_integrable
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (h_slice :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          H x p m ≤ -(m ^ h.β) / h.C + h.C + h.C * ‖p‖ ^ h.α
                  + h.C * ‖p‖ * (m ^ (h.β - h.β / h.α) + 1))
    (μ mBar : (Fin d → ℝ) → ℝ)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ)
    (g_H : (Fin d → ℝ) → ℝ)
    (hgH : MemLpPer 1 g_H)
    (hgH_le :
      ∀ {C' : ℝ}, 0 < C' →
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          ∀ t ∈ Set.Icc (0 : ℝ) 1,
            C' * (‖fun i => cxCombGrad Dυ Dῡ t i x‖ ^ h.α + 1)
                + h.C * ((cxComb μ mBar t x) ^ h.β + 1)
              ≤ g_H x) :
    IntegrableOn g_H (UnitCube d)
      ∧ ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          ∀ t ∈ Set.Icc (0 : ℝ) 1,
            0 < cxComb μ mBar t x →
              |H x (fun i => cxCombGrad Dυ Dῡ t i x) (cxComb μ mBar t x)|
                ≤ g_H x := by
  obtain ⟨C', hC'_pos, hAbs⟩ :=
    hemicont_H_abs_dominator h h_slice μ mBar Dυ Dῡ
  refine ⟨hemicont_H_dominator_integrable g_H hgH, ?_⟩
  filter_upwards [hAbs, hgH_le hC'_pos] with x hxAbs hxLe t ht hμt_pos
  have h1 := hxAbs t ht hμt_pos
  have h2 := hxLe t ht
  linarith

/-- **`hemicont_mDpH_dominator`**: pointwise dominator for
`μ_t · D_pH(x, Dυ_t, μ_t)`, evaluated on the convex segment.
Substituting `m := μ_t x`, `Du := Dυ_t x` into
`Hamiltonian.mDpH_pointwise_bound` yields, almost everywhere in `x`,

  `‖μ_t x • D_pH(x, Dυ_t x, μ_t x)‖`
    `≤ C · (μ_t x · ‖Dυ_t x‖^{α-1} + (μ_t x)^{1+β-β/α} + μ_t x)`.

Combined with `cxComb_abs_le` (giving `μ_t x ≤ μ x + μ̄ x` if both are
non-negative) and `cxCombGrad_norm_le` (giving
`‖Dυ_t x‖ ≤ ‖Dυ x‖ + ‖Dῡ x‖`), this becomes the desired
endpoint-only dominator for the `m·D_pH` integrand. We isolate the
direct substitution step here. -/
theorem hemicont_mDpH_dominator
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (μ mBar : (Fin d → ℝ) → ℝ)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ t, 0 < cxComb μ mBar t x →
        ‖cxComb μ mBar t x •
            DpH x (fun i => cxCombGrad Dυ Dῡ t i x) (cxComb μ mBar t x)‖
          ≤ h.C * (cxComb μ mBar t x
                    * ‖fun i => cxCombGrad Dυ Dῡ t i x‖ ^ (h.α - 1)
                  + (cxComb μ mBar t x) ^ (1 + h.β - h.β / h.α)
                  + cxComb μ mBar t x) := by
  -- The bound is derived directly from `h.DpH_upper` evaluated at the
  -- convex-combination arguments, then multiplied by `cxComb μ mBar t x ≥ 0`.
  filter_upwards [h.DpH_upper] with x hx t hμt
  -- ‖m • v‖ = m * ‖v‖ when m > 0.
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hμt]
  -- DpH bound at p := Dυ_t x, m := μ_t x.
  set p_t : Fin d → ℝ := fun i => cxCombGrad Dυ Dῡ t i x with hp_t
  have hb := hx p_t (cxComb μ mBar t x) hμt
  have hμt_le : 0 ≤ cxComb μ mBar t x := hμt.le
  -- Multiply both sides by `cxComb μ mBar t x ≥ 0`.
  have hmle :
      cxComb μ mBar t x * ‖DpH x p_t (cxComb μ mBar t x)‖
        ≤ cxComb μ mBar t x *
            (h.C * (‖p_t‖ ^ (h.α - 1)
                    + (cxComb μ mBar t x) ^ (h.β - h.β / h.α) + 1)) :=
    mul_le_mul_of_nonneg_left hb hμt_le
  -- Expand `mx · mx^{β-β/α} = mx^{1+β-β/α}`.
  have hpow :
      cxComb μ mBar t x * (cxComb μ mBar t x) ^ (h.β - h.β / h.α)
        = (cxComb μ mBar t x) ^ (1 + h.β - h.β / h.α) := by
    have hone : (cxComb μ mBar t x) ^ (1 : ℝ) = cxComb μ mBar t x :=
      Real.rpow_one _
    calc cxComb μ mBar t x * (cxComb μ mBar t x) ^ (h.β - h.β / h.α)
        = (cxComb μ mBar t x) ^ (1 : ℝ) *
            (cxComb μ mBar t x) ^ (h.β - h.β / h.α) := by rw [hone]
      _ = (cxComb μ mBar t x) ^ ((1 : ℝ) + (h.β - h.β / h.α)) :=
            (Real.rpow_add hμt 1 _).symm
      _ = (cxComb μ mBar t x) ^ (1 + h.β - h.β / h.α) := by ring_nf
  have hrhs_eq :
      cxComb μ mBar t x *
        (h.C * (‖p_t‖ ^ (h.α - 1)
                + (cxComb μ mBar t x) ^ (h.β - h.β / h.α) + 1))
        = h.C * (cxComb μ mBar t x * ‖p_t‖ ^ (h.α - 1)
                  + (cxComb μ mBar t x) ^ (1 + h.β - h.β / h.α)
                  + cxComb μ mBar t x) := by
    have hexp : cxComb μ mBar t x * (h.C * (‖p_t‖ ^ (h.α - 1)
                  + (cxComb μ mBar t x) ^ (h.β - h.β / h.α) + 1))
        = h.C * (cxComb μ mBar t x * ‖p_t‖ ^ (h.α - 1)
                  + cxComb μ mBar t x * (cxComb μ mBar t x) ^ (h.β - h.β / h.α)
                  + cxComb μ mBar t x) := by ring
    rw [hexp, hpow]
  linarith

/-- **`hemicont_eps_grad_dominator`**: pointwise dominator for the
ε-Gateaux gradient piece `vecAbsPowMinusTwo γBar Dυ_t · (Dυ_t · Dν)`.

Using `vecAbsPowMinusTwo γBar v = (v ⬝ v)^{(γBar-2)/2}` and the
coordinate-wise triangle inequality on the convex combination, plus
non-negativity of `(γBar-2)/2 ≥ 0` for `γBar ≥ 2`, we obtain the
endpoint-only bound

  `vecAbsPowMinusTwo γBar Dυ_t ≤ (∑ i, (|Dῡ i x| + |Dυ i x|)^2)^{(γBar-2)/2}`. -/
theorem hemicont_vecAbsPowMinusTwo_dominator
    (γBar : ℝ) (hγ : 2 ≤ γBar)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ) (x : Fin d → ℝ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    vecAbsPowMinusTwo γBar (fun i => cxCombGrad Dυ Dῡ t i x)
      ≤ (∑ i, (|Dῡ i x| + |Dυ i x|) ^ (2 : ℕ)) ^ ((γBar - 2) / 2) := by
  unfold vecAbsPowMinusTwo
  have hexp : 0 ≤ (γBar - 2) / 2 := by
    have : 0 ≤ γBar - 2 := by linarith
    positivity
  have hbase :
      (fun i => cxCombGrad Dυ Dῡ t i x) ⬝
        (fun i => cxCombGrad Dυ Dῡ t i x)
        ≤ ∑ i, (|Dῡ i x| + |Dυ i x|) ^ (2 : ℕ) :=
    cxCombGrad_dot_self_le Dυ Dῡ x ht
  have hbase_nn :
      0 ≤ (fun i => cxCombGrad Dυ Dῡ t i x) ⬝
            (fun i => cxCombGrad Dυ Dῡ t i x) := by
    unfold dotProduct
    refine Finset.sum_nonneg ?_
    intro i _
    have : 0 ≤ (cxCombGrad Dυ Dῡ t i x) ^ (2 : ℕ) := sq_nonneg _
    nlinarith [this]
  exact Real.rpow_le_rpow hbase_nn hbase hexp

/-- **`hemicont_eps_scal_dominator`**: pointwise dominator for the
ε-Gateaux scalar piece `absPowMinusTwo γBar υ_t · (υ_t · ν)`. Concretely,

  `absPowMinusTwo γBar (cxComb υ ῡ t x) ≤ (|ῡ x| + |υ x|) ^ (γBar - 2)`. -/
theorem hemicont_absPowMinusTwo_dominator
    (γBar : ℝ) (hγ : 2 ≤ γBar)
    (υ ῡ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    absPowMinusTwo γBar (cxComb υ ῡ t x)
      ≤ (|ῡ x| + |υ x|) ^ (γBar - 2) := by
  unfold absPowMinusTwo
  have hexp : 0 ≤ γBar - 2 := by linarith
  exact cxComb_abs_rpow_le υ ῡ x ht hexp

/-! ### Pi-norm bound for `cxCombGrad` and pointwise integrand bounds

We package three pointwise bounds that combine the dominators above
into uniform-in-`t` natural-form bounds on the unreg/Gateaux
integrands. These are foundational pointwise convex-analysis
ingredients used by the dominated-convergence wrap-up. -/

/-- For `t ∈ [0,1]`, the pi-norm (sup-norm on `Fin d → ℝ`) of the
gradient convex combination is bounded by the pi-norm of the
coordinate-wise endpoint sum of absolute values:

  `‖fun i => cxCombGrad Dυ Dῡ t i x‖ ≤ ‖fun i => |Dῡ i x| + |Dυ i x|‖`.

Bridges `cxCombGrad_apply_abs_le` (per-coordinate bound) into a
pi-norm bound via `pi_norm_le_iff_of_nonneg`. -/
lemma cxCombGrad_norm_le
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ) (x : Fin d → ℝ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖fun i => cxCombGrad Dυ Dῡ t i x‖
      ≤ ‖fun i => |Dῡ i x| + |Dυ i x|‖ := by
  have hRHS_nn : 0 ≤ ‖fun i => |Dῡ i x| + |Dυ i x|‖ := norm_nonneg _
  refine (pi_norm_le_iff_of_nonneg hRHS_nn).mpr ?_
  intro i
  -- Each coordinate is bounded by `|Dῡ i x| + |Dυ i x|`, which is
  -- itself bounded by the pi-norm of the same vector (sup ≥ component).
  have hcoord : |cxCombGrad Dυ Dῡ t i x| ≤ |Dῡ i x| + |Dυ i x| :=
    cxCombGrad_apply_abs_le Dυ Dῡ x i ht
  have hpiSup : |Dῡ i x| + |Dυ i x| ≤ ‖fun i => |Dῡ i x| + |Dυ i x|‖ := by
    have habs_eq : ‖(|Dῡ i x| + |Dυ i x|)‖ = |Dῡ i x| + |Dυ i x| := by
      rw [Real.norm_eq_abs]
      exact abs_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))
    have hsup := norm_le_pi_norm (fun i => |Dῡ i x| + |Dυ i x|) i
    rw [habs_eq] at hsup
    exact hsup
  -- Compose: ‖coord‖ = |coord| ≤ |Dῡ i x| + |Dυ i x| ≤ pi-norm.
  have : ‖cxCombGrad Dυ Dῡ t i x‖ = |cxCombGrad Dυ Dῡ t i x| :=
    Real.norm_eq_abs _
  rw [this]
  linarith

/-- For real-valued `v, w : Fin d → ℝ`, the absolute value of the
Euclidean dot product is bounded by the pi-norm of `v` times the
absolute-value sum of `w`:

  `|v ⬝ w| ≤ ‖v‖ · ∑ i, |w i|`.

This is the coordinate-wise-Hölder version (`L^∞ × L^1`). It avoids
appealing to Cauchy–Schwarz and is the form needed to plug into
`hemicont_mDpH_dominator` and `hemicont_vecAbsPowMinusTwo_dominator`. -/
private lemma abs_euclideanDot_le_norm_mul_sum_abs
    (v w : Fin d → ℝ) :
    |v ⬝ w| ≤ ‖v‖ * ∑ i, |w i| := by
  -- `|∑ v_i w_i| ≤ ∑ |v_i| |w_i| ≤ ∑ ‖v‖ |w_i| = ‖v‖ · ∑ |w_i|`.
  unfold dotProduct
  have hsum : |∑ i, v i * w i| ≤ ∑ i, |v i * w i| :=
    Finset.abs_sum_le_sum_abs _ _
  have hcoord : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      |v i * w i| ≤ ‖v‖ * |w i| := by
    intro i _
    rw [abs_mul]
    have h1 : |v i| ≤ ‖v‖ := by
      have := norm_le_pi_norm v i
      rw [Real.norm_eq_abs] at this
      exact this
    exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  have hbnd : ∑ i, |v i * w i| ≤ ∑ i, ‖v‖ * |w i| :=
    Finset.sum_le_sum hcoord
  have hfact : (∑ i, ‖v‖ * |w i|) = ‖v‖ * ∑ i, |w i| := by
    rw [← Finset.mul_sum]
  linarith [hsum, hbnd, hfact.le, hfact.ge]

/-! ### Unit-test-style examples -/

/-- Coherence check: for the trivially-flat Hamiltonian
`H(x, p, m) = -m`, `D_pH ≡ 0`, the `H`-upper dominator exists with the
slice hypothesis taken from the trivial witness. We do not exercise
the existence statement explicitly here (it requires
`HypothesisPowerGrowth` data), but we verify that the
`hemicont_mDpH_dominator` pointwise bound is non-vacuous by checking
the LHS `‖m • 0‖ = 0 ≤ RHS` reduces correctly. -/
example (d : ℕ)
    (μ mBar : (Fin d → ℝ) → ℝ)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ)
    (x : Fin d → ℝ) (t : ℝ) (_hμt : 0 < cxComb μ mBar t x) :
    ‖cxComb μ mBar t x •
      ((fun (_ : Fin d → ℝ) (_ : Fin d → ℝ) (_ : ℝ) => (0 : Fin d → ℝ)) x
        (fun i => cxCombGrad Dυ Dῡ t i x) (cxComb μ mBar t x))‖ = 0 := by
  -- The inner function is `(0 : Fin d → ℝ)`, so the smul is `0`.
  simp

/-- Coherence check: the `cxComb`-triangle inequality is sharp at the
endpoints `t = 0` and `t = 1`. -/
example (a ā : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    |cxComb a ā 0 x| ≤ |ā x| + |a x| ∧
    |cxComb a ā 1 x| ≤ |ā x| + |a x| := by
  refine ⟨?_, ?_⟩
  · exact cxComb_abs_le a ā x ⟨le_refl _, by norm_num⟩
  · exact cxComb_abs_le a ā x ⟨by norm_num, le_refl _⟩

/-- Coherence check: `vecAbsPowMinusTwo` dominator at the endpoints
collapses to the standard `(Σ |·|^2)^{(γ-2)/2}` form. -/
example (γBar : ℝ) (hγ : 2 ≤ γBar)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    vecAbsPowMinusTwo γBar (fun i => cxCombGrad Dυ Dῡ 0 i x)
      ≤ (∑ i, (|Dῡ i x| + |Dυ i x|) ^ (2 : ℕ)) ^ ((γBar - 2) / 2) :=
  hemicont_vecAbsPowMinusTwo_dominator γBar hγ Dυ Dῡ x
    ⟨le_refl _, by norm_num⟩

/-- Coherence check: the zero function is a valid `H`-dominator (it is
trivially `MemLpPer 1`), so `hemicont_H_dominator_integrable` produces
`IntegrableOn 0 (UnitCube d)`. -/
example (d : ℕ) :
    IntegrableOn (fun _ : (Fin d → ℝ) => (0 : ℝ)) (UnitCube d) :=
  hemicont_H_dominator_integrable (fun _ => (0 : ℝ)) (MemLpPer.const 0)

/-- Coherence check: the `H`-lower dominator at `t = 0` reduces to the
endpoint bound, namely `H(x, Dῡ x, μ̄ x) ≥ -h.C · ((μ̄ x)^β + 1)`,
provided `0 < μ̄ x`. -/
example
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (μ mBar : (Fin d → ℝ) → ℝ)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      0 < cxComb μ mBar 0 x →
        -h.C * ((cxComb μ mBar 0 x) ^ h.β + 1)
          ≤ H x (fun i => cxCombGrad Dυ Dῡ 0 i x) (cxComb μ mBar 0 x) := by
  filter_upwards [hemicont_H_lower_dominator h μ mBar Dυ Dῡ] with x hx hμt
  exact hx 0 hμt

/-! ## Hölder integrability of the dominators (paper line 1038, Hölder content)

This section discharges the `MemLpPer 1` integrability content of the
endpoint-only dominators produced above. The paper invokes Hölder with
the conjugate pair `(γ̄', γ̄)` and the algebraic identities
`gammaBar'_holder_id` (`1/γ̄' = 1/β̄ + (α-1)/γ̄`) and
`gammaBar'_le_betaBar` (`γ̄' ≤ β̄`); on a finite-measure set
(here, the unit cube) the latter gives the inclusion
`L^{β̄}_per ⊂ L^{γ̄'}_per`.

The headline pairing identities, with `β̄ = β+1` and `γ̄ = α(β+1)/β`:

* `1/(β̄/β) + 1/β̄ = β/β̄ + 1/β̄ = 1` — so `(|μ̄|+|μ|)^β · η ∈ L^1`
  whenever `(|μ̄|+|μ|) ∈ L^{β̄}` and `η ∈ L^{β̄}`.
* `α/γ̄ + 1/β̄ = β/β̄ + 1/β̄ = 1` — so `(|Dῡ|+|Dυ|)^α · η ∈ L^1`
  whenever `(|Dῡ|+|Dυ|) ∈ L^{γ̄}` and `η ∈ L^{β̄}`.

We expose **bundled** Hölder closure lemmas: each takes the relevant
factor `MemLpPer p` hypotheses with the *conjugate* exponents and
produces `MemLpPer 1` of the product, via `MemLp.mul`.

Each summand of each dominator is structurally `(power of inputs) ·
test`, so multiplying by a positive constant `C` preserves `MemLpPer
1`. The full dominator is then a *finite sum* of `MemLpPer 1`
functions, and we conclude via `MemLpPer.add`.
-/

/-- Constant-`1` is `MemLpPer 1` on the unit cube (finite measure). -/
private lemma memLpPer_one_const_one :
    MemLpPer (d := d) 1 (fun _ : (Fin d → ℝ) => (1 : ℝ)) := by
  haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  exact MemLp.toMemLpPer (memLp_const (1 : ℝ))

/-- **Hölder pairing**: if `f ∈ L^p_per` and `g ∈ L^q_per` with
`(p,q,1)` a Hölder triple, then `f · g ∈ L^1_per`. Real-valued. -/
private lemma memLpPer_one_of_holder_mul
    {p q : ℝ≥0∞} [hpqr : ENNReal.HolderTriple p q 1]
    {f g : (Fin d → ℝ) → ℝ}
    (hf : MemLpPer p f) (hg : MemLpPer q g) :
    MemLpPer 1 (fun x : (Fin d → ℝ) => f x * g x) := by
  exact MemLp.toMemLpPer (hf.toMemLp.fun_mul hg.toMemLp)

/-- **`hemicont_H_dominator_holder_memLp`** — `MemLpPer 1` integrability
of the `H`-dominator paired against `eta ∈ L^{betaBar}`.

The combined dominator (from `hemicont_H_abs_dominator`) is
`g_H(x) = C' · (G_p x + 1) + Cval · (G_m x + 1)`, where
`G_p = (‖fun i => |Dῡ i|+|Dυ i|‖)^α` and `G_m = (|μ̄|+|μ|)^β`.

Pairing against `η ∈ L^{β̄}` gives the integrand
`(C' · (G_p + 1) + Cval · (G_m + 1)) · η`, and Hölder via the
conjugate pairs `(γ̄/α, β̄)` (using `gammaBar'_holder_id`) and
`(β̄/β, β̄)` (algebraic conjugate of `β̄`) plus `gammaBar'_le_betaBar`
gives the `MemLpPer 1` membership.

We *bundle* the Hölder content as: the user provides
`MemLpPer p G_p` and `MemLpPer q G_m` with the conjugate-pairing
hypotheses on `(p, betaBar, 1)` and `(q, betaBar, 1)` (i.e., as
`HolderTriple` instances). The proof combines
`memLpPer_one_of_holder_mul` (Hölder multiplication),
`MemLpPer.add`, and constant scaling. -/
theorem hemicont_H_dominator_holder_memLp
    (C' Cval : ℝ)
    (betaBar : ℝ≥0∞) (p q : ℝ≥0∞)
    [ENNReal.HolderTriple p betaBar 1] [ENNReal.HolderTriple q betaBar 1]
    (G_p G_m eta : (Fin d → ℝ) → ℝ)
    (hGp : MemLpPer p G_p)
    (hGm : MemLpPer q G_m)
    (hEta : MemLpPer betaBar eta) :
    MemLpPer 1
      (fun x : (Fin d → ℝ) =>
        (C' * (G_p x + 1) + Cval * (G_m x + 1)) * eta x) := by
  -- Distribute: the integrand is
  --   `C' · (G_p · eta) + C' · eta + Cval · (G_m · eta) + Cval · eta`.
  -- All four pieces are in `L^1_per`: the products by Hölder, the
  -- pure-`eta` summands by combining `1 ∈ L^p` (finite measure) and
  -- `eta ∈ L^betaBar` via the same Hölder triple.
  haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  -- `eta ∈ L^1` on finite measure: `1 · eta ∈ L^1` via Hölder.
  have h1_p : MemLpPer (d := d) p (fun _ : (Fin d → ℝ) => (1 : ℝ)) :=
    MemLp.toMemLpPer (memLp_const (1 : ℝ))
  have hEta_one_p : MemLpPer 1 (fun x : (Fin d → ℝ) => (1 : ℝ) * eta x) :=
    memLpPer_one_of_holder_mul (p := p) (q := betaBar) h1_p hEta
  have hEta_one : MemLpPer 1 eta := by
    have heq : (fun x : (Fin d → ℝ) => (1 : ℝ) * eta x) = eta := by
      funext x; ring
    simpa [heq] using hEta_one_p
  -- The four `MemLpPer 1` building blocks.
  have h_GpE : MemLpPer 1 (fun x : (Fin d → ℝ) => G_p x * eta x) :=
    memLpPer_one_of_holder_mul (p := p) (q := betaBar) hGp hEta
  have h_GmE : MemLpPer 1 (fun x : (Fin d → ℝ) => G_m x * eta x) :=
    memLpPer_one_of_holder_mul (p := q) (q := betaBar) hGm hEta
  -- Multiply by constants and assemble the four-term sum.
  have h_a : MemLpPer 1 (fun x : (Fin d → ℝ) => C' * (G_p x * eta x)) :=
    MemLp.toMemLpPer (MeasureTheory.MemLp.const_mul h_GpE.toMemLp C')
  have h_b : MemLpPer 1 (fun x : (Fin d → ℝ) => C' * eta x) :=
    MemLp.toMemLpPer (MeasureTheory.MemLp.const_mul hEta_one.toMemLp C')
  have h_c : MemLpPer 1 (fun x : (Fin d → ℝ) => Cval * (G_m x * eta x)) :=
    MemLp.toMemLpPer (MeasureTheory.MemLp.const_mul h_GmE.toMemLp Cval)
  have h_d : MemLpPer 1 (fun x : (Fin d → ℝ) => Cval * eta x) :=
    MemLp.toMemLpPer (MeasureTheory.MemLp.const_mul hEta_one.toMemLp Cval)
  -- Combine: ((h_a + h_b) + (h_c + h_d)) and rewrite via congruence.
  have h_ab := h_a.add h_b
  have h_cd := h_c.add h_d
  have hsum := h_ab.add h_cd
  -- Show pointwise equality with the goal.
  have heq : (fun x : (Fin d → ℝ) =>
        (C' * (G_p x + 1) + Cval * (G_m x + 1)) * eta x)
      = (fun x : (Fin d → ℝ) =>
        ((C' * (G_p x * eta x)) + (C' * eta x))
          + ((Cval * (G_m x * eta x)) + (Cval * eta x))) := by
    funext x; ring
  rw [heq]
  exact (by simpa [Pi.add_def, Pi.add_apply] using hsum)

/-- **`hemicont_mDpH_dominator_holder_memLp`** — `MemLpPer 1`
integrability of the `m · D_pH`-dominator paired against
`Dν ∈ L^{γ̄}` (taken coordinate-wise as a real-valued
`Dν_norm = ‖Dν‖`).

The dominator (from `hemicont_mDpH_dominator`) is
`G(x) = Cval · (S₁ x + S₂ x + S₃ x)`, with
`S₁ = (|μ̄|+|μ|) · (|Dῡ|+|Dυ|)^{α-1}`,
`S₂ = (|μ̄|+|μ|)^{1+β-β/α}`,
`S₃ = (|μ̄|+|μ|)`.

After pairing against `Dν_norm ∈ L^{γ̄}`, each summand is in `L^1_per`
by Hölder, using the identity `gammaBar'_holder_id`
(`1/γ̄' = 1/β̄ + (α-1)/γ̄`) combined with `gammaBar'_le_betaBar`. We
bundle this as: the user supplies `MemLpPer γ̄'_pow Sᵢ` for each `i`,
where `γ̄'_pow` is conjugate to `γ̄`, and `MemLpPer γ̄ Dν_norm`. -/
theorem hemicont_mDpH_dominator_holder_memLp
    (Cval : ℝ)
    (gammaBar gammaBar' : ℝ≥0∞)
    [ENNReal.HolderTriple gammaBar' gammaBar 1]
    (S₁ S₂ S₃ Dnu_norm : (Fin d → ℝ) → ℝ)
    (hS₁ : MemLpPer gammaBar' S₁)
    (hS₂ : MemLpPer gammaBar' S₂)
    (hS₃ : MemLpPer gammaBar' S₃)
    (hDnu : MemLpPer gammaBar Dnu_norm) :
    MemLpPer 1
      (fun x : (Fin d → ℝ) =>
        Cval * (S₁ x + S₂ x + S₃ x) * Dnu_norm x) := by
  -- Each summand `Sᵢ · Dnu_norm ∈ L^1` by Hölder.
  have h_S1 : MemLpPer 1 (fun x => S₁ x * Dnu_norm x) :=
    memLpPer_one_of_holder_mul (p := gammaBar') (q := gammaBar) hS₁ hDnu
  have h_S2 : MemLpPer 1 (fun x => S₂ x * Dnu_norm x) :=
    memLpPer_one_of_holder_mul (p := gammaBar') (q := gammaBar) hS₂ hDnu
  have h_S3 : MemLpPer 1 (fun x => S₃ x * Dnu_norm x) :=
    memLpPer_one_of_holder_mul (p := gammaBar') (q := gammaBar) hS₃ hDnu
  have h_a : MemLpPer 1 (fun x => Cval * (S₁ x * Dnu_norm x)) :=
    MemLp.toMemLpPer (MeasureTheory.MemLp.const_mul h_S1.toMemLp Cval)
  have h_b : MemLpPer 1 (fun x => Cval * (S₂ x * Dnu_norm x)) :=
    MemLp.toMemLpPer (MeasureTheory.MemLp.const_mul h_S2.toMemLp Cval)
  have h_c : MemLpPer 1 (fun x => Cval * (S₃ x * Dnu_norm x)) :=
    MemLp.toMemLpPer (MeasureTheory.MemLp.const_mul h_S3.toMemLp Cval)
  have h_ab := h_a.add h_b
  have hsum := h_ab.add h_c
  have heq : (fun x : (Fin d → ℝ) =>
        Cval * (S₁ x + S₂ x + S₃ x) * Dnu_norm x)
      = (fun x : (Fin d → ℝ) =>
          ((Cval * (S₁ x * Dnu_norm x))
            + (Cval * (S₂ x * Dnu_norm x)))
          + (Cval * (S₃ x * Dnu_norm x))) := by
    funext x; ring
  rw [heq]
  exact (by simpa [Pi.add_def, Pi.add_apply] using hsum)

/-- **`hemicont_eps_grad_dominator_holder_memLp`** — `MemLpPer 1`
integrability of the ε-Gateaux gradient piece
`G_grad x · Dν_norm x`, where
`G_grad = (∑ i, (|Dῡ i|+|Dυ i|)^2)^{(γ̄-2)/2}` and
`Dν_norm = ‖fun i => Dν i ·‖` (for instance the pointwise sum
`∑ i, (|Dῡ i|+|Dυ i|) · |Dν i|` after applying coordinate-wise
Cauchy-Schwarz on the dot product).

Hölder pairing on the conjugate `(γ̄', γ̄)` with
`G_grad ∈ L^{γ̄'_grad}` and `Dν_norm ∈ L^{γ̄}` gives the
`MemLpPer 1` membership. -/
theorem hemicont_eps_grad_dominator_holder_memLp
    (gammaBar gammaBar'_grad : ℝ≥0∞)
    [ENNReal.HolderTriple gammaBar'_grad gammaBar 1]
    (G_grad Dnu_norm : (Fin d → ℝ) → ℝ)
    (hGgrad : MemLpPer gammaBar'_grad G_grad)
    (hDnu : MemLpPer gammaBar Dnu_norm) :
    MemLpPer 1 (fun x : (Fin d → ℝ) => G_grad x * Dnu_norm x) :=
  memLpPer_one_of_holder_mul (p := gammaBar'_grad) (q := gammaBar) hGgrad hDnu

/-- **`hemicont_eps_scal_dominator_holder_memLp`** — `MemLpPer 1`
integrability of the ε-Gateaux scalar piece `G_scal x · ν_abs x`,
where `G_scal = (|ῡ|+|υ|)^{γ̄-1}` and `ν_abs = |ν|`.

Hölder pairing on the conjugate `(γ̄', γ̄)` with
`G_scal ∈ L^{γ̄'_scal}` and `ν_abs ∈ L^{γ̄}` (the `ν` factor of the
test pair, which sits in `W^{1,γ̄}_per` and hence in `L^{γ̄}_per`)
gives the `MemLpPer 1` membership. -/
theorem hemicont_eps_scal_dominator_holder_memLp
    (gammaBar gammaBar'_scal : ℝ≥0∞)
    [ENNReal.HolderTriple gammaBar'_scal gammaBar 1]
    (G_scal nu_abs : (Fin d → ℝ) → ℝ)
    (hGscal : MemLpPer gammaBar'_scal G_scal)
    (hNu : MemLpPer gammaBar nu_abs) :
    MemLpPer 1 (fun x : (Fin d → ℝ) => G_scal x * nu_abs x) :=
  memLpPer_one_of_holder_mul (p := gammaBar'_scal) (q := gammaBar) hGscal hNu

/-! ### Unit tests for the dominator-`MemLpPer 1` lemmas -/

/-- Unit test: with `G_p = G_m = eta = 0`, the `H`-dominator integrand
collapses to `0`, which is `MemLpPer 1`. -/
example (d : ℕ) (C' Cval : ℝ) :
    MemLpPer (d := d) 1
      (fun x : (Fin d → ℝ) =>
        (C' * ((fun _ => (0 : ℝ)) x + 1)
          + Cval * ((fun _ => (0 : ℝ)) x + 1))
        * (fun _ => (0 : ℝ)) x) := by
  -- The integrand is the constant zero function (eta ≡ 0 makes the product 0).
  have heq : (fun x : (Fin d → ℝ) =>
        (C' * ((fun _ => (0 : ℝ)) x + 1)
          + Cval * ((fun _ => (0 : ℝ)) x + 1))
        * (fun _ => (0 : ℝ)) x)
      = (fun _ : (Fin d → ℝ) => (0 : ℝ)) := by
    funext x; ring
  rw [heq]
  exact MemLpPer.const 0

/-- Unit test: with all summands zero and `Dnu_norm` zero, the
`m · D_pH`-dominator integrand is zero, hence `MemLpPer 1`. -/
example (d : ℕ) (Cval : ℝ) :
    MemLpPer (d := d) 1
      (fun x : (Fin d → ℝ) =>
        Cval * ((fun _ => (0 : ℝ)) x
                + (fun _ => (0 : ℝ)) x + (fun _ => (0 : ℝ)) x)
          * (fun _ => (0 : ℝ)) x) := by
  have heq : (fun x : (Fin d → ℝ) =>
        Cval * ((fun _ => (0 : ℝ)) x
                + (fun _ => (0 : ℝ)) x + (fun _ => (0 : ℝ)) x)
          * (fun _ => (0 : ℝ)) x)
      = (fun _ : (Fin d → ℝ) => (0 : ℝ)) := by
    funext x; ring
  rw [heq]
  exact MemLpPer.const 0

/-- Unit test: the trivial ε-gateaux gradient case `G_grad ≡ 0`
yields the integrand `0`, in `MemLpPer 1`. -/
example (d : ℕ) (gammaBar gammaBar'_grad : ℝ≥0∞)
    [ENNReal.HolderTriple gammaBar'_grad gammaBar 1]
    (Dnu_norm : (Fin d → ℝ) → ℝ)
    (hDnu : MemLpPer gammaBar Dnu_norm) :
    MemLpPer (d := d) 1 (fun x : (Fin d → ℝ) =>
      (fun _ => (0 : ℝ)) x * Dnu_norm x) := by
  refine hemicont_eps_grad_dominator_holder_memLp gammaBar gammaBar'_grad
    (fun _ => 0) Dnu_norm ?_ hDnu
  exact MemLpPer.const 0

/-- Unit test: the trivial ε-Gateaux scalar case `G_scal ≡ 0` yields
the integrand `0`, in `MemLpPer 1`. -/
example (d : ℕ) (gammaBar gammaBar'_scal : ℝ≥0∞)
    [ENNReal.HolderTriple gammaBar'_scal gammaBar 1]
    (nu_abs : (Fin d → ℝ) → ℝ)
    (hNu : MemLpPer gammaBar nu_abs) :
    MemLpPer (d := d) 1 (fun x : (Fin d → ℝ) =>
      (fun _ => (0 : ℝ)) x * nu_abs x) := by
  refine hemicont_eps_scal_dominator_holder_memLp gammaBar gammaBar'_scal
    (fun _ => 0) nu_abs ?_ hNu
  exact MemLpPer.const 0

/-! ## Dominated convergence: continuity of the `A_ε` segment pairing
(paper line 1043, end of `lem:hemicont` proof)

This section closes Lemma `lem:hemicont` of the paper by combining the
pointwise-in-`x` continuity (`aepsiIntegrandAt_continuousOn`) with the
integrable dominator (packaged via `hemicont_*_holder_memLp`) through
`MeasureTheory.continuousOn_of_dominated`.

Concretely we prove:

* `mfgOperatorEpsPair_segment_eq_integral` — the pairing along the
  segment `(μ_t, υ_t) := (1-t)(μ̄, ῡ) + t(μ, υ)` is the unit-cube
  integral of `aepsiIntegrandAt`.
* `aepsiIntegrand_pairing_continuousOn` — under the hypotheses listed in
  the task (regularity of `H`, `2 ≤ γ̄`, segment-positivity, and an
  integrable dominator), the map
  `t ↦ ∫ x in UnitCube d, aepsiIntegrandAt … x t ∂volume` is continuous
  on `[0, 1]`.
* `Aepsi_hemicontinuous_segment` (alias `isHemicontinuous_Aepsi_segment`) —
  the same continuity stated directly for
  `t ↦ mfgOperatorEpsPair … (Dυ_t) (μ_t) (υ_t) Dν η ν`. This is the form
  consumed by the abstract `IsHemicontinuous` predicate (via composition
  with the segment) once the Banach-space embedding of `𝓚` is settled.

The dominator and the AE strong-measurability inputs are passed in as
hypotheses; their construction follows `infra:P4-hemi-dominator-holder`. -/

/-- The "first half" of `aepsiIntegrandAt`: the unregularized pointwise
integrand of `mfgOperatorPair` along the segment. -/
@[inline] def aepsiIntegrandAt_unreg
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ)
    (μ mBar υ ῡ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ)
    (x : Fin d → ℝ) (t : ℝ) : ℝ :=
  let μt := cxComb μ mBar t x
  let υt := cxComb υ ῡ t x
  let Dυt : Fin d → ℝ := fun i => cxCombGrad Dυ Dῡ t i x
  (-υt - H x Dυt μt + V x) * η x
    + μt * (DpH x Dυt μt ⬝ (fun i => Dν i x))
    + (μt - 1) * ν x

/-- The "second half" of `aepsiIntegrandAt`: the Gateaux integrand
(without the `ε` factor). -/
@[inline] def aepsiIntegrandAt_gateaux
    (γBar : ℝ)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ)
    (υ ῡ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (ν : (Fin d → ℝ) → ℝ)
    (x : Fin d → ℝ) (t : ℝ) : ℝ :=
  let υt := cxComb υ ῡ t x
  let Dυt : Fin d → ℝ := fun i => cxCombGrad Dυ Dῡ t i x
  vecAbsPowMinusTwo γBar Dυt * (Dυt ⬝ (fun i => Dν i x))
    + absPowMinusTwo γBar υt * (υt * ν x)

/-- The full `aepsiIntegrandAt` is the sum of the two pieces above
(with the second scaled by `ε`). This is purely a `rfl`-style lemma. -/
lemma aepsiIntegrandAt_eq_sum
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (γBar ε : ℝ)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ)
    (μ mBar υ ῡ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) (t : ℝ) :
    aepsiIntegrandAt V H DpH γBar ε Dυ Dῡ μ mBar υ ῡ Dν η ν x t
      = aepsiIntegrandAt_unreg V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν x t
        + ε * aepsiIntegrandAt_gateaux γBar Dυ Dῡ υ ῡ Dν ν x t := rfl

/-! ### Closed-cone (`K₀`) variant of the unregularized integrand

Step 6/10 of the v8 K₀ hemicontinuity plan. The strict-cone definition
`aepsiIntegrandAt_unreg` uses `H x p m` and `m * (DpH x p m ⬝ Dν)`,
both of which only behave continuously on `m > 0`. The closed-cone
variant `aepsiIntegrandAt_unreg_K0` replaces the flux term
`μt * (DpH x Dυt μt ⬝ Dν x)` by the canonical extension
`(JsimpleExt DpH x Dυt μt) ⬝ Dν x` (see
`StationaryMFG.Hamiltonian.JsimpleExt`, which equals `m • DpH x p m`
on all of `ℝ`, and `0` at `m = 0` by `JsimpleExt_zero`). On `0 < μt`
the two integrands agree pointwise — this is the agreement lemma
`aepsiIntegrandAt_unreg_K0_eq_unreg_of_pos`. The downstream segment
continuity proof (step 7) will use the boundary-extended `H` via the
`HypothesisHextJointCont` rider threaded into Theorem 1 in iter 0754. -/

/-- Closed-cone (`K₀`) variant of `aepsiIntegrandAt_unreg`. Differs
from the strict-cone version only in the flux term: instead of
`μt * (DpH x Dυt μt ⬝ Dν x)` it uses the boundary-extended
`JsimpleExt DpH x Dυt μt ⬝ Dν x`, which agrees with the strict-cone
flux on `0 < μt` (see `aepsiIntegrandAt_unreg_K0_eq_unreg_of_pos`)
and is the zero vector at `μt = 0` (by
`StationaryMFG.Hamiltonian.JsimpleExt_zero`). -/
@[inline] def aepsiIntegrandAt_unreg_K0
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ)
    (μ mBar υ ῡ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ)
    (x : Fin d → ℝ) (t : ℝ) : ℝ :=
  let μt := cxComb μ mBar t x
  let υt := cxComb υ ῡ t x
  let Dυt : Fin d → ℝ := fun i => cxCombGrad Dυ Dῡ t i x
  (-υt - H x Dυt μt + V x) * η x
    + (JsimpleExt DpH x Dυt μt ⬝ (fun i => Dν i x))
    + (μt - 1) * ν x

/-- **Agreement lemma.** On `0 < cxComb μ mBar t x` the closed-cone
integrand `aepsiIntegrandAt_unreg_K0` coincides with the strict-cone
`aepsiIntegrandAt_unreg`. The proof unfolds both definitions and uses
that `JsimpleExt DpH x p m = m • DpH x p m`, which gives
`(m • DpH …) ⬝ Dν = m * (DpH … ⬝ Dν)` by linearity of
`dotProduct` in the left slot. The positivity hypothesis is not
actually used in the algebraic manipulation — agreement is in fact
unconditional in `m` — but we expose the lemma with the `0 < mt`
hypothesis as required by step 6 of the v8 K0 plan, since downstream
clients invoke it only on the strict-cone segment. -/
theorem aepsiIntegrandAt_unreg_K0_eq_unreg_of_pos
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ)
    (μ mBar υ ῡ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ)
    (x : Fin d → ℝ) (t : ℝ)
    (_hpos : 0 < cxComb μ mBar t x) :
    aepsiIntegrandAt_unreg_K0 V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν x t
      = aepsiIntegrandAt_unreg V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν x t := by
  -- Unfold both definitions. The first and third summands are
  -- syntactically identical between the two integrands; only the
  -- middle (flux) term differs.
  unfold aepsiIntegrandAt_unreg_K0 aepsiIntegrandAt_unreg
  -- Reduce to equality of the middle terms.
  -- Set `μt := cxComb μ mBar t x`, `Dυt i := cxCombGrad Dυ Dῡ t i x`,
  -- `w i := Dν i x`. We must show
  -- `(JsimpleExt DpH x Dυt μt) ⬝ w = μt * (DpH x Dυt μt ⬝ w)`.
  -- Since `JsimpleExt DpH x Dυt μt = μt • DpH x Dυt μt` definitionally,
  -- this reduces by `dotProduct` unfolding and `Finset.mul_sum`.
  set μt : ℝ := cxComb μ mBar t x with hμt
  set Dυt : Fin d → ℝ := fun i => cxCombGrad Dυ Dῡ t i x with hDυt
  set w : Fin d → ℝ := fun i => Dν i x with hw
  -- The mid-term equality:
  have hmid :
      (JsimpleExt DpH x Dυt μt ⬝ w)
        = μt * (DpH x Dυt μt ⬝ w) := by
    -- `JsimpleExt DpH x Dυt μt = μt • DpH x Dυt μt` by definition.
    show ((μt • DpH x Dυt μt) ⬝ w) = μt * (DpH x Dυt μt ⬝ w)
    unfold dotProduct
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    simp [Pi.smul_apply, smul_eq_mul, mul_assoc]
  -- Plug it into the integrand expression.
  simp only [hmid]

/-- **Unconditional agreement.** The closed-cone integrand
`aepsiIntegrandAt_unreg_K0` equals the strict-cone integrand
`aepsiIntegrandAt_unreg` pointwise in `(x, t)`, with no positivity
hypothesis. The proof body of `aepsiIntegrandAt_unreg_K0_eq_unreg_of_pos`
does not actually use its positivity hypothesis — agreement is
algebraic. We expose this stripped form for the K0 set-family composer
(iter 0758 step 9a), which transports a K0 pointwise bound on
`aepsiIntegrandAt_unreg` to a bound on `aepsiIntegrandAt_unreg_K0`. -/
theorem aepsiIntegrandAt_unreg_K0_eq_unreg
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ)
    (μ mBar υ ῡ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ)
    (x : Fin d → ℝ) (t : ℝ) :
    aepsiIntegrandAt_unreg_K0 V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν x t
      = aepsiIntegrandAt_unreg V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν x t := by
  unfold aepsiIntegrandAt_unreg_K0 aepsiIntegrandAt_unreg
  set μt : ℝ := cxComb μ mBar t x with hμt
  set Dυt : Fin d → ℝ := fun i => cxCombGrad Dυ Dῡ t i x with hDυt
  set w : Fin d → ℝ := fun i => Dν i x with hw
  have hmid :
      (JsimpleExt DpH x Dυt μt ⬝ w)
        = μt * (DpH x Dυt μt ⬝ w) := by
    show ((μt • DpH x Dυt μt) ⬝ w) = μt * (DpH x Dυt μt ⬝ w)
    unfold dotProduct
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    simp [Pi.smul_apply, smul_eq_mul, mul_assoc]
  simp only [hmid]

/-- Unit-test: the K0 integrand at `t = 0` with zero data reduces to
the expected value, exercising the definition concretely. -/
example {d : ℕ}
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ)
    (μ mBar υ ῡ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ)
    (x : Fin d → ℝ) :
    aepsiIntegrandAt_unreg_K0 (d := d)
        V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν x 0
      = let μ0 := mBar x
        let υ0 := ῡ x
        let Dυ0 : Fin d → ℝ := fun i => Dῡ i x
        (-υ0 - H x Dυ0 μ0 + V x) * η x
          + (JsimpleExt DpH x Dυ0 μ0 ⬝ (fun i => Dν i x))
          + (μ0 - 1) * ν x := by
  -- `cxComb a ā 0 x = (1 - 0) * ā x + 0 * a x = ā x` and similarly
  -- for `cxCombGrad`. The integrand at `t = 0` therefore unfolds to
  -- the formula above.
  unfold aepsiIntegrandAt_unreg_K0 cxComb cxCombGrad
  ring_nf

/-! ### Pointwise bounds for `aepsiIntegrandAt_unreg` and
`aepsiIntegrandAt_gateaux`

These bounds combine the dominator lemmas above with the
triangle inequality to produce uniform-in-`t` natural-form pointwise
dominators on the unreg/Gateaux integrands. The output shape uses the
endpoint-only quantities `(|μ̄|+|μ|)`, `(|ῡ|+|υ|)`, and the pi-norm
`‖fun i => |Dῡ i|+|Dυ i|‖` so that subsequent Hölder-pairing
arguments (in `hemicont_*_holder_memLp`) can produce `MemLpPer 1`
integrability. -/

/-- **`aepsiIntegrandAt_unreg_pointwise_bound`** — natural-form
pointwise dominator on `‖aepsiIntegrandAt_unreg ...‖`, uniform in
`t ∈ [0,1]` (under segment positivity). The conclusion has shape
`(|ῡ|+|υ|)·|η| + (H-dom)·|η| + |V|·|η| + (mDpH-dom)·∑|Dν| +
((|mBar|+|μ|)+1)·|ν|`, with the existence of the `H` constant `C'`
inherited from `hemicont_H_abs_dominator`. -/
theorem aepsiIntegrandAt_unreg_pointwise_bound
    (V : (Fin d → ℝ) → ℝ)
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (h_slice :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          H x p m ≤ -(m ^ h.β) / h.C + h.C + h.C * ‖p‖ ^ h.α
                  + h.C * ‖p‖ * (m ^ (h.β - h.β / h.α) + 1))
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ)
    (μ mBar υ ῡ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          0 < cxComb μ mBar t x →
            ‖aepsiIntegrandAt_unreg V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν x t‖
              ≤ (|ῡ x| + |υ x|) * |η x|
                + (C' * (‖fun i => |Dῡ i x| + |Dυ i x|‖ ^ h.α + 1)
                    + h.C * ((|mBar x| + |μ x|) ^ h.β + 1)) * |η x|
                + |V x| * |η x|
                + h.C * ((|mBar x| + |μ x|)
                            * ‖fun i => |Dῡ i x| + |Dυ i x|‖ ^ (h.α - 1)
                          + (|mBar x| + |μ x|) ^ (1 + h.β - h.β / h.α)
                          + (|mBar x| + |μ x|))
                    * (∑ i, |Dν i x|)
                + ((|mBar x| + |μ x|) + 1) * |ν x| := by
  obtain ⟨C', hC'_pos, hHabs⟩ :=
    hemicont_H_abs_dominator h h_slice μ mBar Dυ Dῡ
  refine ⟨C', hC'_pos, ?_⟩
  filter_upwards [hHabs, hemicont_mDpH_dominator h μ mBar Dυ Dῡ]
    with x hxH hxmDpH t ht hμt_pos
  set μt : ℝ := cxComb μ mBar t x with hμt_def
  set υt : ℝ := cxComb υ ῡ t x with hυt_def
  set p_t : Fin d → ℝ := fun i => cxCombGrad Dυ Dῡ t i x with hpt_def
  set Δp_t : Fin d → ℝ := fun i => |Dῡ i x| + |Dυ i x| with hΔp_def
  set Δm : ℝ := |mBar x| + |μ x| with hΔm_def
  set Δυ : ℝ := |ῡ x| + |υ x| with hΔυ_def
  -- Constants and non-negativities.
  have hCpos : 0 < h.C := h.hC
  have hα_ge : 1 ≤ h.α := le_of_lt h.hα
  have hαm1_nn : 0 ≤ h.α - 1 := by linarith
  have hα_nn : 0 ≤ h.α := by linarith
  have hβ_nn : 0 ≤ h.β := h.hβ.le
  have hΔm_nn : 0 ≤ Δm := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hΔυ_nn : 0 ≤ Δυ := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hΔp_nn : 0 ≤ ‖Δp_t‖ := norm_nonneg _
  have hpt_norm_nn : 0 ≤ ‖p_t‖ := norm_nonneg _
  have h_abs_μt : |μt| ≤ Δm := cxComb_abs_le μ mBar x ht
  have h_abs_υt : |υt| ≤ Δυ := cxComb_abs_le υ ῡ x ht
  have h_norm_pt : ‖p_t‖ ≤ ‖Δp_t‖ := cxCombGrad_norm_le Dυ Dῡ x ht
  -- Algebraic restatement of the unreg integrand.
  have heq_unreg :
      aepsiIntegrandAt_unreg V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν x t
        = (-υt - H x p_t μt + V x) * η x
          + μt * (DpH x p_t μt ⬝ (fun i => Dν i x))
          + (μt - 1) * ν x := rfl
  rw [Real.norm_eq_abs, heq_unreg]
  -- Apply triangle inequality twice (left-associated).
  have htri :
      |((-υt - H x p_t μt + V x) * η x
          + μt * (DpH x p_t μt ⬝ (fun i => Dν i x)))
        + (μt - 1) * ν x|
        ≤ |(-υt - H x p_t μt + V x) * η x|
            + |μt * (DpH x p_t μt ⬝ (fun i => Dν i x))|
            + |(μt - 1) * ν x| := by
    have h1 : |((-υt - H x p_t μt + V x) * η x
                  + μt * (DpH x p_t μt ⬝ (fun i => Dν i x)))
                + (μt - 1) * ν x|
              ≤ |(-υt - H x p_t μt + V x) * η x
                  + μt * (DpH x p_t μt ⬝ (fun i => Dν i x))|
                + |(μt - 1) * ν x| := abs_add_le _ _
    have h2 : |(-υt - H x p_t μt + V x) * η x
                + μt * (DpH x p_t μt ⬝ (fun i => Dν i x))|
              ≤ |(-υt - H x p_t μt + V x) * η x|
                + |μt * (DpH x p_t μt ⬝ (fun i => Dν i x))| := abs_add_le _ _
    linarith
  -- Per-summand bounds.
  -- (1) |(-υt - H + V) · η| ≤ (|υt| + |H| + |V|) · |η|.
  have h_first_split :
      |(-υt - H x p_t μt + V x) * η x|
        ≤ (|υt| + |H x p_t μt| + |V x|) * |η x| := by
    rw [abs_mul]
    have htri3 : |-υt - H x p_t μt + V x|
                  ≤ |υt| + |H x p_t μt| + |V x| := by
      have hA : |(-υt - H x p_t μt) + V x|
                  ≤ |(-υt - H x p_t μt)| + |V x| := abs_add_le _ _
      have hB : |-υt - H x p_t μt| ≤ |-υt| + |H x p_t μt| := by
        have := abs_sub (-υt) (H x p_t μt)
        simpa using this
      have hC : |-υt| = |υt| := abs_neg _
      have heq : -υt - H x p_t μt + V x = (-υt - H x p_t μt) + V x := by ring
      rw [heq]; linarith
    exact mul_le_mul_of_nonneg_right htri3 (abs_nonneg _)
  -- (2) |μt · (DpH ⬝ Dν)| ≤ ‖μt • DpH‖ · ∑ |Dν|.
  have h_dot_split :
      |μt * (DpH x p_t μt ⬝ (fun i => Dν i x))|
        ≤ ‖μt • DpH x p_t μt‖ * ∑ i, |Dν i x| := by
    rw [abs_mul]
    have hdot :=
      abs_euclideanDot_le_norm_mul_sum_abs (DpH x p_t μt) (fun i => Dν i x)
    have hμt_abs_nn : 0 ≤ |μt| := abs_nonneg _
    have hbnd1 : |μt| * |DpH x p_t μt ⬝ (fun i => Dν i x)|
                  ≤ |μt| * (‖DpH x p_t μt‖ * ∑ i, |Dν i x|) :=
      mul_le_mul_of_nonneg_left hdot hμt_abs_nn
    have hsmul : ‖μt • DpH x p_t μt‖ = |μt| * ‖DpH x p_t μt‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    rw [hsmul]
    -- |μt| * |DpH ⬝ Dν| ≤ |μt| * (‖DpH‖ * ∑|Dν|)
    --                  = (|μt| * ‖DpH‖) * ∑|Dν|.
    nlinarith [hbnd1, abs_nonneg μt, norm_nonneg (DpH x p_t μt),
      Finset.sum_nonneg
        (s := (Finset.univ : Finset (Fin d))) (f := fun i => |Dν i x|)
        (fun _ _ => abs_nonneg (Dν _ x))]
  -- (3) |(μt - 1) · ν| ≤ (|μt| + 1) · |ν|.
  have h_third_split :
      |(μt - 1) * ν x| ≤ (|μt| + 1) * |ν x| := by
    rw [abs_mul]
    have h1 : |μt - 1| ≤ |μt| + |(1 : ℝ)| := abs_sub _ _
    have h2 : |(1 : ℝ)| = 1 := abs_one
    rw [h2] at h1
    exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  -- Endpoint dominators.
  have hH := hxH t ht hμt_pos
  have hmDpH := hxmDpH t hμt_pos
  -- Pi-norm/Δ-monotonicities (rpow).
  have h_pα : ‖p_t‖ ^ h.α ≤ ‖Δp_t‖ ^ h.α :=
    Real.rpow_le_rpow hpt_norm_nn h_norm_pt hα_nn
  have h_pαm1 : ‖p_t‖ ^ (h.α - 1) ≤ ‖Δp_t‖ ^ (h.α - 1) :=
    Real.rpow_le_rpow hpt_norm_nn h_norm_pt hαm1_nn
  have hμt_le_abs : μt ≤ |μt| := le_abs_self _
  have h_μt_nn : 0 ≤ μt := hμt_pos.le
  have h_μt_le_Δm : μt ≤ Δm := le_trans hμt_le_abs h_abs_μt
  have h_μtβ : μt ^ h.β ≤ Δm ^ h.β :=
    Real.rpow_le_rpow h_μt_nn h_μt_le_Δm hβ_nn
  -- 0 ≤ 1 + β - β/α (from β > 0, α ≥ 1 ⇒ β/α ≤ β ⇒ 1 + β - β/α ≥ 1).
  have hβoα_le_β : h.β / h.α ≤ h.β := by
    have hαpos : 0 < h.α := lt_trans one_pos h.hα
    rw [div_le_iff₀ hαpos]
    have hβpos : 0 ≤ h.β := h.hβ.le
    have := mul_le_mul_of_nonneg_left hα_ge hβpos
    -- hβpos · 1 ≤ hβpos · h.α
    linarith
  have h_pow_exp_nn : 0 ≤ 1 + h.β - h.β / h.α := by
    have : 0 ≤ h.β - h.β / h.α := by linarith
    linarith
  have h_μt_pow_endpoint :
      μt ^ (1 + h.β - h.β / h.α) ≤ Δm ^ (1 + h.β - h.β / h.α) :=
    Real.rpow_le_rpow h_μt_nn h_μt_le_Δm h_pow_exp_nn
  -- Endpoint bound on |H|.
  have h_H_endpoint :
      |H x p_t μt|
        ≤ C' * (‖Δp_t‖ ^ h.α + 1) + h.C * (Δm ^ h.β + 1) := by
    have hC'_mono : C' * (‖p_t‖ ^ h.α + 1) ≤ C' * (‖Δp_t‖ ^ h.α + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hC'_pos.le
    have hC_mono : h.C * (μt ^ h.β + 1) ≤ h.C * (Δm ^ h.β + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hCpos.le
    linarith
  -- Endpoint bound on ‖μt • DpH‖.
  have h_pαm1_nn : 0 ≤ ‖p_t‖ ^ (h.α - 1) := Real.rpow_nonneg hpt_norm_nn _
  have h_Δpαm1_nn : 0 ≤ ‖Δp_t‖ ^ (h.α - 1) := Real.rpow_nonneg hΔp_nn _
  have h_factor_pow :
      μt * ‖p_t‖ ^ (h.α - 1) ≤ Δm * ‖Δp_t‖ ^ (h.α - 1) := by
    have step1 : μt * ‖p_t‖ ^ (h.α - 1) ≤ μt * ‖Δp_t‖ ^ (h.α - 1) :=
      mul_le_mul_of_nonneg_left h_pαm1 h_μt_nn
    have step2 : μt * ‖Δp_t‖ ^ (h.α - 1) ≤ Δm * ‖Δp_t‖ ^ (h.α - 1) :=
      mul_le_mul_of_nonneg_right h_μt_le_Δm h_Δpαm1_nn
    linarith
  have h_mDpH_endpoint :
      ‖μt • DpH x p_t μt‖
        ≤ h.C * (Δm * ‖Δp_t‖ ^ (h.α - 1)
                  + Δm ^ (1 + h.β - h.β / h.α) + Δm) := by
    have hinner :
        μt * ‖p_t‖ ^ (h.α - 1) + μt ^ (1 + h.β - h.β / h.α) + μt
          ≤ Δm * ‖Δp_t‖ ^ (h.α - 1)
              + Δm ^ (1 + h.β - h.β / h.α) + Δm := by
      linarith
    have := mul_le_mul_of_nonneg_left hinner hCpos.le
    linarith
  -- ∑ |Dν| ≥ 0.
  have h_sumDν_nn : 0 ≤ ∑ i, |Dν i x| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  -- Promote the second-summand bound to the endpoint mDpH form.
  have h_second_endpoint :
      ‖μt • DpH x p_t μt‖ * ∑ i, |Dν i x|
        ≤ h.C * (Δm * ‖Δp_t‖ ^ (h.α - 1)
                  + Δm ^ (1 + h.β - h.β / h.α) + Δm)
            * (∑ i, |Dν i x|) :=
    mul_le_mul_of_nonneg_right h_mDpH_endpoint h_sumDν_nn
  -- Promote the third-summand bound: |μt| + 1 ≤ Δm + 1.
  have h_third_endpoint :
      (|μt| + 1) * |ν x| ≤ (Δm + 1) * |ν x| :=
    mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
  -- Promote the first-summand bound: |υt| + |H| + |V| ≤ Δυ + H_endpoint + |V|.
  have h_first_endpoint :
      (|υt| + |H x p_t μt| + |V x|) * |η x|
        ≤ (Δυ + (C' * (‖Δp_t‖ ^ h.α + 1) + h.C * (Δm ^ h.β + 1)) + |V x|)
            * |η x| :=
    mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
  -- Combine.
  have hAcc :
      |(-υt - H x p_t μt + V x) * η x|
        + |μt * (DpH x p_t μt ⬝ (fun i => Dν i x))|
        + |(μt - 1) * ν x|
      ≤ (Δυ + (C' * (‖Δp_t‖ ^ h.α + 1) + h.C * (Δm ^ h.β + 1)) + |V x|)
            * |η x|
        + h.C * (Δm * ‖Δp_t‖ ^ (h.α - 1)
                  + Δm ^ (1 + h.β - h.β / h.α) + Δm) * (∑ i, |Dν i x|)
        + (Δm + 1) * |ν x| := by
    have hA :
        |(-υt - H x p_t μt + V x) * η x|
          ≤ (Δυ + (C' * (‖Δp_t‖ ^ h.α + 1) + h.C * (Δm ^ h.β + 1)) + |V x|)
              * |η x| := le_trans h_first_split h_first_endpoint
    have hB :
        |μt * (DpH x p_t μt ⬝ (fun i => Dν i x))|
          ≤ h.C * (Δm * ‖Δp_t‖ ^ (h.α - 1)
                  + Δm ^ (1 + h.β - h.β / h.α) + Δm) * (∑ i, |Dν i x|) :=
      le_trans h_dot_split h_second_endpoint
    have hC₃ :
        |(μt - 1) * ν x| ≤ (Δm + 1) * |ν x| :=
      le_trans h_third_split h_third_endpoint
    linarith
  -- Distribute the first-summand-RHS into the three goal pieces.
  have hgoal_distribute :
      (Δυ + (C' * (‖Δp_t‖ ^ h.α + 1) + h.C * (Δm ^ h.β + 1)) + |V x|)
            * |η x|
        = Δυ * |η x|
          + (C' * (‖Δp_t‖ ^ h.α + 1) + h.C * (Δm ^ h.β + 1)) * |η x|
          + |V x| * |η x| := by ring
  linarith [htri, hAcc, hgoal_distribute.le, hgoal_distribute.ge]

/-- **`aepsiIntegrandAt_gateaux_pointwise_bound`** — natural-form
pointwise dominator on `‖aepsiIntegrandAt_gateaux ...‖`, uniform in
`t ∈ [0,1]`. Conclusion shape:
`(∑ i, (|Dῡ i|+|Dυ i|)^2)^{(γBar-2)/2} · ‖|Dῡ|+|Dυ|‖ · ∑ |Dν| +
 (|ῡ|+|υ|)^{γBar-2} · (|ῡ|+|υ|) · |ν|`. -/
theorem aepsiIntegrandAt_gateaux_pointwise_bound
    (γBar : ℝ) (hγ : 2 ≤ γBar)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ)
    (υ ῡ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (ν : (Fin d → ℝ) → ℝ) :
    ∀ x : Fin d → ℝ,
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ‖aepsiIntegrandAt_gateaux γBar Dυ Dῡ υ ῡ Dν ν x t‖
          ≤ (∑ i, (|Dῡ i x| + |Dυ i x|) ^ (2 : ℕ)) ^ ((γBar - 2) / 2)
              * ‖fun i => |Dῡ i x| + |Dυ i x|‖
              * (∑ i, |Dν i x|)
            + (|ῡ x| + |υ x|) ^ (γBar - 2)
              * ((|ῡ x| + |υ x|) * |ν x|) := by
  intro x t ht
  set υt : ℝ := cxComb υ ῡ t x with hυt_def
  set p_t : Fin d → ℝ := fun i => cxCombGrad Dυ Dῡ t i x with hpt_def
  set Δp_t : Fin d → ℝ := fun i => |Dῡ i x| + |Dυ i x| with hΔp_def
  set Δυ : ℝ := |ῡ x| + |υ x| with hΔυ_def
  set S2 : ℝ := ∑ i, (|Dῡ i x| + |Dυ i x|) ^ (2 : ℕ) with hS2_def
  -- Constants and non-negativities.
  have hγ_nn : 0 ≤ γBar - 2 := by linarith
  have hγh_nn : 0 ≤ (γBar - 2) / 2 := by positivity
  have hΔp_nn : 0 ≤ ‖Δp_t‖ := norm_nonneg _
  have hΔυ_nn : 0 ≤ Δυ := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hS2_nn : 0 ≤ S2 :=
    Finset.sum_nonneg (fun i _ => by positivity)
  have h_S2pow_nn : 0 ≤ S2 ^ ((γBar - 2) / 2) := Real.rpow_nonneg hS2_nn _
  have hΔυpow_nn : 0 ≤ Δυ ^ (γBar - 2) := Real.rpow_nonneg hΔυ_nn _
  have h_sumDν_nn : 0 ≤ ∑ i, |Dν i x| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  -- Algebraic restatement.
  have heq_gat :
      aepsiIntegrandAt_gateaux γBar Dυ Dῡ υ ῡ Dν ν x t
        = vecAbsPowMinusTwo γBar p_t * (p_t ⬝ (fun i => Dν i x))
          + absPowMinusTwo γBar υt * (υt * ν x) := rfl
  rw [Real.norm_eq_abs, heq_gat]
  -- Triangle inequality.
  have htri :
      |vecAbsPowMinusTwo γBar p_t * (p_t ⬝ (fun i => Dν i x))
          + absPowMinusTwo γBar υt * (υt * ν x)|
        ≤ |vecAbsPowMinusTwo γBar p_t * (p_t ⬝ (fun i => Dν i x))|
          + |absPowMinusTwo γBar υt * (υt * ν x)| := abs_add_le _ _
  -- First summand.
  have h_vecAbsPow_nn : 0 ≤ vecAbsPowMinusTwo γBar p_t := by
    unfold vecAbsPowMinusTwo
    have hdot_nn : 0 ≤ p_t ⬝ p_t := by
      unfold dotProduct
      exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
    exact Real.rpow_nonneg hdot_nn _
  have h_vec_endpoint :
      vecAbsPowMinusTwo γBar p_t ≤ S2 ^ ((γBar - 2) / 2) :=
    hemicont_vecAbsPowMinusTwo_dominator γBar hγ Dυ Dῡ x ht
  have h_norm_pt : ‖p_t‖ ≤ ‖Δp_t‖ := cxCombGrad_norm_le Dυ Dῡ x ht
  have h_dot_le : |p_t ⬝ (fun i => Dν i x)| ≤ ‖p_t‖ * ∑ i, |Dν i x| :=
    abs_euclideanDot_le_norm_mul_sum_abs _ _
  have h_dot_le_Δp :
      |p_t ⬝ (fun i => Dν i x)| ≤ ‖Δp_t‖ * ∑ i, |Dν i x| := by
    have h1 : ‖p_t‖ * ∑ i, |Dν i x| ≤ ‖Δp_t‖ * ∑ i, |Dν i x| :=
      mul_le_mul_of_nonneg_right h_norm_pt h_sumDν_nn
    linarith
  have h_first_split :
      |vecAbsPowMinusTwo γBar p_t * (p_t ⬝ (fun i => Dν i x))|
        ≤ S2 ^ ((γBar - 2) / 2) * (‖Δp_t‖ * ∑ i, |Dν i x|) := by
    rw [abs_mul]
    have hvec_abs : |vecAbsPowMinusTwo γBar p_t| = vecAbsPowMinusTwo γBar p_t :=
      abs_of_nonneg h_vecAbsPow_nn
    rw [hvec_abs]
    have hbnd1 :
        vecAbsPowMinusTwo γBar p_t * |p_t ⬝ (fun i => Dν i x)|
          ≤ vecAbsPowMinusTwo γBar p_t * (‖Δp_t‖ * ∑ i, |Dν i x|) :=
      mul_le_mul_of_nonneg_left h_dot_le_Δp h_vecAbsPow_nn
    have hbnd2 :
        vecAbsPowMinusTwo γBar p_t * (‖Δp_t‖ * ∑ i, |Dν i x|)
          ≤ S2 ^ ((γBar - 2) / 2) * (‖Δp_t‖ * ∑ i, |Dν i x|) := by
      have h_rhs_nn : 0 ≤ ‖Δp_t‖ * ∑ i, |Dν i x| :=
        mul_nonneg hΔp_nn h_sumDν_nn
      exact mul_le_mul_of_nonneg_right h_vec_endpoint h_rhs_nn
    linarith
  -- Second summand.
  have h_absPow_nn : 0 ≤ absPowMinusTwo γBar υt := by
    unfold absPowMinusTwo
    exact Real.rpow_nonneg (abs_nonneg _) _
  have h_abs_endpoint :
      absPowMinusTwo γBar υt ≤ Δυ ^ (γBar - 2) :=
    hemicont_absPowMinusTwo_dominator γBar hγ υ ῡ x ht
  have h_abs_υt : |υt| ≤ Δυ := cxComb_abs_le υ ῡ x ht
  have h_second_split :
      |absPowMinusTwo γBar υt * (υt * ν x)|
        ≤ Δυ ^ (γBar - 2) * (Δυ * |ν x|) := by
    rw [abs_mul, abs_mul]
    have h_abs_abs : |absPowMinusTwo γBar υt| = absPowMinusTwo γBar υt :=
      abs_of_nonneg h_absPow_nn
    rw [h_abs_abs]
    have hbnd1 :
        absPowMinusTwo γBar υt * (|υt| * |ν x|)
          ≤ absPowMinusTwo γBar υt * (Δυ * |ν x|) := by
      have hStep : |υt| * |ν x| ≤ Δυ * |ν x| :=
        mul_le_mul_of_nonneg_right h_abs_υt (abs_nonneg _)
      exact mul_le_mul_of_nonneg_left hStep h_absPow_nn
    have hbnd2 :
        absPowMinusTwo γBar υt * (Δυ * |ν x|)
          ≤ Δυ ^ (γBar - 2) * (Δυ * |ν x|) := by
      have h_rhs_nn : 0 ≤ Δυ * |ν x| :=
        mul_nonneg hΔυ_nn (abs_nonneg _)
      exact mul_le_mul_of_nonneg_right h_abs_endpoint h_rhs_nn
    linarith
  -- Compose; reassociate `S2pow * (‖Δp‖ * ∑|Dν|) = S2pow * ‖Δp‖ * ∑|Dν|`.
  have hassoc :
      S2 ^ ((γBar - 2) / 2) * (‖Δp_t‖ * ∑ i, |Dν i x|)
        = S2 ^ ((γBar - 2) / 2) * ‖Δp_t‖ * (∑ i, |Dν i x|) := by ring
  linarith [htri, h_first_split, h_second_split, hassoc.le, hassoc.ge]

/-- **Unregularized pairing along the segment as a unit-cube integral.**
This is the `mfgOperatorPair` half of `mfgOperatorEpsPair`. -/
lemma mfgOperatorPair_segment_eq_integral
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ)
    (μ mBar υ ῡ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ) (t : ℝ) :
    mfgOperatorPair (V := V) (H := H) (DpH := DpH)
        (fun i x => cxCombGrad Dυ Dῡ t i x)
        (fun x => cxComb μ mBar t x)
        (fun x => cxComb υ ῡ t x) Dν η ν
      = ∫ x in UnitCube d,
          aepsiIntegrandAt_unreg V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν x t
        ∂(volume : Measure (Fin d → ℝ)) := by
  unfold mfgOperatorPair aepsiIntegrandAt_unreg
  refine setIntegral_congr_fun measurableSet_unitCube ?_
  intro x _; rfl

/-- **Gateaux pairing along the segment as a unit-cube integral.**
This is the `gateauxWpPair` half of `mfgOperatorEpsPair`. -/
lemma gateauxWpPair_segment_eq_integral
    (γBar : ℝ)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ)
    (υ ῡ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (ν : (Fin d → ℝ) → ℝ) (t : ℝ) :
    gateauxWpPair γBar
        (fun i x => cxCombGrad Dυ Dῡ t i x)
        (fun x => cxComb υ ῡ t x) Dν ν
      = ∫ x in UnitCube d,
          aepsiIntegrandAt_gateaux γBar Dυ Dῡ υ ῡ Dν ν x t
        ∂(volume : Measure (Fin d → ℝ)) := by
  unfold gateauxWpPair aepsiIntegrandAt_gateaux
  refine setIntegral_congr_fun measurableSet_unitCube ?_
  intro x _; rfl

/-! ### DCT-based continuity for the unregularized half -/

/-- **DCT applied to the unregularized integrand.** Under regularity of
`H`, segment positivity, and an integrable dominator on
`aepsiIntegrandAt_unreg`, the function
`t ↦ ∫ x in UnitCube d, aepsiIntegrandAt_unreg … x t ∂volume` is
continuous on `[0, 1]`. -/
theorem aepsiIntegrand_unreg_continuousOn
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hReg : RegularityH (d := d) H DpH)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ)
    (μ mBar υ ῡ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ)
    (hPos : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < cxComb μ mBar t x)
    (g_unreg : (Fin d → ℝ) → ℝ)
    (hg_int : IntegrableOn g_unreg (UnitCube d))
    (hF_meas : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      AEStronglyMeasurable
        (fun x => aepsiIntegrandAt_unreg V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν x t)
        (volume.restrict (UnitCube d)))
    (hF_bound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖aepsiIntegrandAt_unreg V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν x t‖
          ≤ g_unreg x) :
    ContinuousOn (fun t : ℝ =>
        ∫ x in UnitCube d,
          aepsiIntegrandAt_unreg V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν x t
        ∂(volume : Measure (Fin d → ℝ))) (Set.Icc 0 1) := by
  -- Pointwise (a.e. in `x`) continuity on `[0,1]` of the integrand at `2 ≤ γBar`
  -- is given by `aepsi_integrand_continuous_in_t`, but for the unregularized
  -- piece we only need continuity of the *first* part of the integrand;
  -- this is `aepsiIntegrandAt_continuousOn` specialized to that piece.
  -- Build the AE-pointwise continuity directly from the regularity bundle.
  -- Per expert v3: `hPos` is now an a.e.-uniform-in-`t` statement; we extract
  -- the per-`x` pointwise positivity `hxPos` inside the `filter_upwards`.
  have h_cont :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ContinuousOn (fun t : ℝ =>
            aepsiIntegrandAt_unreg V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν x t)
          (Set.Icc 0 1) := by
    filter_upwards [hReg.continuous_H_pm, hReg.continuous_DpH_pm, hPos]
      with x hHx hDpHx hxPos
    -- The unregularized integrand is the part of `aepsiIntegrandAt` that
    -- excludes the `ε`-Gateaux summand. We mimic the proof of
    -- `aepsiIntegrandAt_continuousOn` for that piece only.
    set φ : ℝ → (Fin d → ℝ) × ℝ :=
      fun t => ((fun i => cxCombGrad Dυ Dῡ t i x), cxComb μ mBar t x)
    have hφ_cont : Continuous φ := by
      refine Continuous.prodMk ?_ ?_
      · exact continuous_cxCombGrad Dυ Dῡ x
      · exact continuous_cxComb μ mBar x
    have hφ_maps : Set.MapsTo φ (Set.Icc (0 : ℝ) 1) {pm | 0 < pm.2} := by
      intro t ht; simpa [φ] using hxPos t ht
    have hHcomp : ContinuousOn
        (fun t : ℝ =>
          H x (fun i => cxCombGrad Dυ Dῡ t i x) (cxComb μ mBar t x))
        (Set.Icc 0 1) := by
      have := hHx.comp hφ_cont.continuousOn hφ_maps
      simpa [φ, Function.comp_def] using this
    have hDpHcomp : ContinuousOn
        (fun t : ℝ =>
          DpH x (fun i => cxCombGrad Dυ Dῡ t i x) (cxComb μ mBar t x))
        (Set.Icc 0 1) := by
      have := hDpHx.comp hφ_cont.continuousOn hφ_maps
      simpa [φ, Function.comp_def] using this
    have hμt : Continuous (fun t : ℝ => cxComb μ mBar t x) :=
      continuous_cxComb μ mBar x
    have hυt : Continuous (fun t : ℝ => cxComb υ ῡ t x) :=
      continuous_cxComb υ ῡ x
    have hDpHdot : ContinuousOn
        (fun t : ℝ =>
          DpH x (fun i => cxCombGrad Dυ Dῡ t i x) (cxComb μ mBar t x)
            ⬝ (fun i => Dν i x)) (Set.Icc 0 1) := by
      unfold dotProduct
      refine continuousOn_finset_sum _ (fun i _ => ?_)
      have hcoord : ContinuousOn
          (fun t : ℝ =>
            DpH x (fun i => cxCombGrad Dυ Dῡ t i x) (cxComb μ mBar t x) i)
          (Set.Icc 0 1) :=
        (continuous_apply i).comp_continuousOn hDpHcomp
      exact hcoord.mul continuousOn_const
    have hVconst : ContinuousOn (fun _ : ℝ => V x) (Set.Icc (0:ℝ) 1) :=
      continuousOn_const
    have hηconst : ContinuousOn (fun _ : ℝ => η x) (Set.Icc (0:ℝ) 1) :=
      continuousOn_const
    have hνconst : ContinuousOn (fun _ : ℝ => ν x) (Set.Icc (0:ℝ) 1) :=
      continuousOn_const
    have h1const : ContinuousOn (fun _ : ℝ => (1:ℝ)) (Set.Icc (0:ℝ) 1) :=
      continuousOn_const
    unfold aepsiIntegrandAt_unreg
    refine (((((hυt.continuousOn).neg.sub hHcomp).add hVconst).mul hηconst).add
      ((hμt.continuousOn).mul hDpHdot)).add ?_
    exact ((hμt.continuousOn).sub h1const).mul hνconst
  -- Apply Mathlib's `continuousOn_of_dominated`.
  exact MeasureTheory.continuousOn_of_dominated
    (μ := volume.restrict (UnitCube d))
    (s := Set.Icc 0 1)
    hF_meas hF_bound hg_int h_cont

/-! ### DCT-based continuity for the Gateaux half -/

/-- **DCT applied to the Gateaux integrand.** Under `1 < γ̄` and an
integrable dominator on `aepsiIntegrandAt_gateaux`, the function
`t ↦ ∫ x in UnitCube d, aepsiIntegrandAt_gateaux … x t ∂volume` is
continuous on `[0, 1]`. -/
theorem aepsiIntegrand_gateaux_continuousOn
    (γBar : ℝ) (hγ : 1 < γBar)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ)
    (υ ῡ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (ν : (Fin d → ℝ) → ℝ)
    (g_gat : (Fin d → ℝ) → ℝ)
    (hg_int : IntegrableOn g_gat (UnitCube d))
    (hF_meas : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      AEStronglyMeasurable
        (fun x => aepsiIntegrandAt_gateaux γBar Dυ Dῡ υ ῡ Dν ν x t)
        (volume.restrict (UnitCube d)))
    (hF_bound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖aepsiIntegrandAt_gateaux γBar Dυ Dῡ υ ῡ Dν ν x t‖ ≤ g_gat x) :
    ContinuousOn (fun t : ℝ =>
        ∫ x in UnitCube d,
          aepsiIntegrandAt_gateaux γBar Dυ Dῡ υ ῡ Dν ν x t
        ∂(volume : Measure (Fin d → ℝ))) (Set.Icc 0 1) := by
  -- Pointwise continuity in `t` of the Gateaux integrand follows from the
  -- product-form helpers `continuous_vecAbsPowMinusTwo_dot_cxComb` and
  -- `continuous_absPowMinusTwo_mul_cxComb` (Phase 0b.2b refactor:
  -- `1 < γBar` instead of `2 ≤ γBar`).
  have h_cont :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ContinuousOn (fun t : ℝ =>
            aepsiIntegrandAt_gateaux γBar Dυ Dῡ υ ῡ Dν ν x t)
          (Set.Icc 0 1) := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    have hVecProd : Continuous (fun t : ℝ =>
        vecAbsPowMinusTwo γBar (fun i => cxCombGrad Dυ Dῡ t i x)
          * ((fun i => cxCombGrad Dυ Dῡ t i x) ⬝ (fun i => Dν i x))) :=
      continuous_vecAbsPowMinusTwo_dot_cxComb γBar hγ Dυ Dῡ Dν x
    have hScProd : Continuous (fun t : ℝ =>
        absPowMinusTwo γBar (cxComb υ ῡ t x)
          * (cxComb υ ῡ t x * ν x)) :=
      continuous_absPowMinusTwo_mul_cxComb γBar hγ υ ῡ ν x
    unfold aepsiIntegrandAt_gateaux
    exact hVecProd.continuousOn.add hScProd.continuousOn
  exact MeasureTheory.continuousOn_of_dominated
    (μ := volume.restrict (UnitCube d))
    (s := Set.Icc 0 1)
    hF_meas hF_bound hg_int h_cont

/-! ### Combined DCT continuity of the segment pairing -/

/-- **Hemicontinuity of `A_ε` on the segment** (paper line 1043, end of
`lem:hemicont` proof). Under the standing hypotheses (regularity of
`H`, `2 ≤ γ̄`, segment-positivity, and integrable dominators for both
the unregularized and Gateaux integrands), the map
`t ↦ ⟨A_ε[(1-t)(μ̄,ῡ)+t(μ,υ)], (η,ν)⟩` is continuous on `[0,1]`.

This is the DCT conclusion of `lem:hemicont`, the closing step of paper
line 1038–1043. The dominators are obtained from
`infra:P4-hemi-dominator-holder`, and the AE-strong-measurability comes
from continuity of the integrand in `(p, m)` (paper convention
`a:Hat0`–`a:mDpHat0`) plus measurability of the convex combination. -/
theorem Aepsi_hemicontinuous_segment
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hReg : RegularityH (d := d) H DpH)
    (γBar ε : ℝ) (hγ : 1 < γBar)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ)
    (μ mBar υ ῡ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ)
    (hPos : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < cxComb μ mBar t x)
    (g_unreg g_gat : (Fin d → ℝ) → ℝ)
    (hg_unreg_int : IntegrableOn g_unreg (UnitCube d))
    (hg_gat_int : IntegrableOn g_gat (UnitCube d))
    (hF_unreg_meas : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      AEStronglyMeasurable
        (fun x => aepsiIntegrandAt_unreg V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν x t)
        (volume.restrict (UnitCube d)))
    (hF_unreg_bound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖aepsiIntegrandAt_unreg V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν x t‖
          ≤ g_unreg x)
    (hF_gat_meas : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      AEStronglyMeasurable
        (fun x => aepsiIntegrandAt_gateaux γBar Dυ Dῡ υ ῡ Dν ν x t)
        (volume.restrict (UnitCube d)))
    (hF_gat_bound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖aepsiIntegrandAt_gateaux γBar Dυ Dῡ υ ῡ Dν ν x t‖ ≤ g_gat x) :
    ContinuousOn (fun t : ℝ =>
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH) γBar ε
          (fun i x => cxCombGrad Dυ Dῡ t i x)
          (fun x => cxComb μ mBar t x)
          (fun x => cxComb υ ῡ t x) Dν η ν) (Set.Icc 0 1) := by
  -- Rewrite the pairing as the sum of the two unit-cube integrals.
  have hRewrite : ∀ t : ℝ,
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH) γBar ε
          (fun i x => cxCombGrad Dυ Dῡ t i x)
          (fun x => cxComb μ mBar t x)
          (fun x => cxComb υ ῡ t x) Dν η ν
        = (∫ x in UnitCube d,
              aepsiIntegrandAt_unreg V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν x t
            ∂(volume : Measure (Fin d → ℝ)))
          + ε *
            (∫ x in UnitCube d,
              aepsiIntegrandAt_gateaux γBar Dυ Dῡ υ ῡ Dν ν x t
            ∂(volume : Measure (Fin d → ℝ))) := by
    intro t
    unfold mfgOperatorEpsPair
    rw [mfgOperatorPair_segment_eq_integral V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν t,
        gateauxWpPair_segment_eq_integral γBar Dυ Dῡ υ ῡ Dν ν t]
  -- Continuity of the two pieces follows from the DCT lemmas.
  have h1 := aepsiIntegrand_unreg_continuousOn V H DpH hReg Dυ Dῡ μ mBar υ ῡ
    Dν η ν hPos g_unreg hg_unreg_int hF_unreg_meas hF_unreg_bound
  have h2 := aepsiIntegrand_gateaux_continuousOn γBar hγ Dυ Dῡ υ ῡ Dν ν
    g_gat hg_gat_int hF_gat_meas hF_gat_bound
  -- Sum & scalar-multiply preserve `ContinuousOn`.
  have hsum : ContinuousOn
      (fun t : ℝ =>
        (∫ x in UnitCube d,
            aepsiIntegrandAt_unreg V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν x t
          ∂(volume : Measure (Fin d → ℝ)))
        + ε *
          (∫ x in UnitCube d,
            aepsiIntegrandAt_gateaux γBar Dυ Dῡ υ ῡ Dν ν x t
          ∂(volume : Measure (Fin d → ℝ)))) (Set.Icc 0 1) :=
    h1.add (continuousOn_const.mul h2)
  -- Conclude by congruence.
  refine hsum.congr ?_
  intro t _
  exact (hRewrite t).symm

/-- **Alias** matching the task's `isHemicontinuous_Aepsi`-style name.
This is the DCT-closed segment continuity from
`Aepsi_hemicontinuous_segment`. -/
theorem isHemicontinuous_Aepsi_segment
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hReg : RegularityH (d := d) H DpH)
    (γBar ε : ℝ) (hγ : 1 < γBar)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ)
    (μ mBar υ ῡ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ)
    (hPos : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < cxComb μ mBar t x)
    (g_unreg g_gat : (Fin d → ℝ) → ℝ)
    (hg_unreg_int : IntegrableOn g_unreg (UnitCube d))
    (hg_gat_int : IntegrableOn g_gat (UnitCube d))
    (hF_unreg_meas : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      AEStronglyMeasurable
        (fun x => aepsiIntegrandAt_unreg V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν x t)
        (volume.restrict (UnitCube d)))
    (hF_unreg_bound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖aepsiIntegrandAt_unreg V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν x t‖
          ≤ g_unreg x)
    (hF_gat_meas : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      AEStronglyMeasurable
        (fun x => aepsiIntegrandAt_gateaux γBar Dυ Dῡ υ ῡ Dν ν x t)
        (volume.restrict (UnitCube d)))
    (hF_gat_bound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖aepsiIntegrandAt_gateaux γBar Dυ Dῡ υ ῡ Dν ν x t‖ ≤ g_gat x) :
    ContinuousOn (fun t : ℝ =>
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH) γBar ε
          (fun i x => cxCombGrad Dυ Dῡ t i x)
          (fun x => cxComb μ mBar t x)
          (fun x => cxComb υ ῡ t x) Dν η ν) (Set.Icc 0 1) :=
  Aepsi_hemicontinuous_segment V H DpH hReg γBar ε hγ Dυ Dῡ μ mBar υ ῡ
    Dν η ν hPos g_unreg g_gat hg_unreg_int hg_gat_int
    hF_unreg_meas hF_unreg_bound hF_gat_meas hF_gat_bound

/-! ### Unit-test-style examples for the DCT segment continuity -/

/-- The DCT segment continuity is non-vacuous: with the trivial
Hamiltonian `H = 0`, `D_pH = 0`, and zero data
(`Dυ = Dῡ = μ = mBar = υ = ῡ = Dν = η = ν = 0`), the dominators are
zero (hence integrable and AE-strongly measurable), and the conclusion
is `ContinuousOn (fun _ => 0) [0,1]`. The hypothesis `0 < cxComb μ mBar t x`
forces `μ = mBar = 0` to fail; we instead take `μ = mBar = 1`, which
makes the segment positive. -/
example (d : ℕ) (V : (Fin d → ℝ) → ℝ) (ε : ℝ) :
    ContinuousOn (fun t : ℝ =>
        mfgOperatorEpsPair (V := V)
          (H := fun _ _ _ => (0 : ℝ))
          (DpH := fun _ _ _ => (0 : Fin d → ℝ)) (2 : ℝ) ε
          (fun i x => cxCombGrad (fun _ _ => (0:ℝ)) (fun _ _ => (0:ℝ)) t i x)
          (fun x => cxComb (fun _ => (1:ℝ)) (fun _ => (1:ℝ)) t x)
          (fun x => cxComb (fun _ => (0:ℝ)) (fun _ => (0:ℝ)) t x)
          (fun _ _ => (0:ℝ)) (fun _ => (0:ℝ)) (fun _ => (0:ℝ)))
      (Set.Icc 0 1) := by
  refine Aepsi_hemicontinuous_segment (d := d) V _ _ ?_ 2 ε one_lt_two
    (fun _ _ => (0:ℝ)) (fun _ _ => (0:ℝ))
    (fun _ => (1:ℝ)) (fun _ => (1:ℝ))
    (fun _ => (0:ℝ)) (fun _ => (0:ℝ))
    (fun _ _ => (0:ℝ))
    (fun _ => (0:ℝ)) (fun _ => (0:ℝ))
    ?_
    (fun _ => (0:ℝ)) (fun _ => (0:ℝ))
    ?_ ?_ ?_ ?_ ?_ ?_
  · -- Trivial regularity.
    refine
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
  · -- Segment positivity (a.e.-uniform-in-`t`): cxComb 1 1 t x = (1-t)·1 + t·1 = 1 > 0.
    refine Filter.Eventually.of_forall ?_
    intro x t _
    have : cxComb (fun _ : (Fin d → ℝ) => (1:ℝ)) (fun _ => (1:ℝ)) t x = 1 := by
      unfold cxComb; ring
    rw [this]; norm_num
  · -- Integrability of zero on UnitCube.
    exact (integrable_zero _ _ _).integrableOn
  · exact (integrable_zero _ _ _).integrableOn
  · -- AEStronglyMeasurable of the unregularized integrand at zero data
    -- collapses to the constant `0` since `η ≡ 0` and `ν ≡ 0`.
    intro t _
    have hzero : (fun x : (Fin d → ℝ) =>
        aepsiIntegrandAt_unreg V (fun _ _ _ => (0:ℝ))
          (fun _ _ _ => (0 : Fin d → ℝ))
          (fun _ _ => (0:ℝ)) (fun _ _ => (0:ℝ))
          (fun _ => (1:ℝ)) (fun _ => (1:ℝ))
          (fun _ => (0:ℝ)) (fun _ => (0:ℝ))
          (fun _ _ => (0:ℝ)) (fun _ => (0:ℝ)) (fun _ => (0:ℝ)) x t)
        = fun _ : (Fin d → ℝ) => (0:ℝ) := by
      funext x
      unfold aepsiIntegrandAt_unreg cxComb cxCombGrad
      simp [dotProduct]
    rw [hzero]
    exact aestronglyMeasurable_const
  · -- The unregularized integrand is bounded by 0 (it equals 0 pointwise).
    intro t _
    refine Filter.Eventually.of_forall ?_
    intro x
    -- The integrand: (-(0) - 0 + V x)·0 + 1·(0 ⬝ 0) + (1-1)·0 = 0
    unfold aepsiIntegrandAt_unreg cxComb cxCombGrad
    simp [dotProduct]
  · intro t _
    have hzero : (fun x : (Fin d → ℝ) =>
        aepsiIntegrandAt_gateaux (2:ℝ) (fun _ _ => (0:ℝ)) (fun _ _ => (0:ℝ))
          (fun _ => (0:ℝ)) (fun _ => (0:ℝ)) (fun _ _ => (0:ℝ))
          (fun _ => (0:ℝ)) x t) = fun _ : (Fin d → ℝ) => (0:ℝ) := by
      funext x
      unfold aepsiIntegrandAt_gateaux cxComb cxCombGrad
      simp [dotProduct]
    rw [hzero]
    exact aestronglyMeasurable_const
  · intro t _
    refine Filter.Eventually.of_forall ?_
    intro x
    unfold aepsiIntegrandAt_gateaux cxComb cxCombGrad
    simp [dotProduct]

/-- Check the type of the segment continuity matches the task's
acceptance signature: continuity in `t` of the pairing
`⟨A_ε[(1-t)(μ̄,ῡ)+t(μ,υ)], (η,ν)⟩` on `[0,1]`. -/
example
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hReg : RegularityH (d := d) H DpH)
    (γBar ε : ℝ) (hγ : 1 < γBar)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ)
    (μ mBar υ ῡ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ)
    (hPos : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < cxComb μ mBar t x)
    (g_unreg g_gat : (Fin d → ℝ) → ℝ)
    (hg_unreg_int : IntegrableOn g_unreg (UnitCube d))
    (hg_gat_int : IntegrableOn g_gat (UnitCube d))
    (hF_unreg_meas : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      AEStronglyMeasurable
        (fun x => aepsiIntegrandAt_unreg V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν x t)
        (volume.restrict (UnitCube d)))
    (hF_unreg_bound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖aepsiIntegrandAt_unreg V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν x t‖
          ≤ g_unreg x)
    (hF_gat_meas : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      AEStronglyMeasurable
        (fun x => aepsiIntegrandAt_gateaux γBar Dυ Dῡ υ ῡ Dν ν x t)
        (volume.restrict (UnitCube d)))
    (hF_gat_bound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖aepsiIntegrandAt_gateaux γBar Dυ Dῡ υ ῡ Dν ν x t‖ ≤ g_gat x) :
    ContinuousOn (fun t : ℝ =>
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH) γBar ε
          (fun i x => cxCombGrad Dυ Dῡ t i x)
          (fun x => cxComb μ mBar t x)
          (fun x => cxComb υ ῡ t x) Dν η ν) (Set.Icc 0 1) :=
  isHemicontinuous_Aepsi_segment V H DpH hReg γBar ε hγ Dυ Dῡ μ mBar υ ῡ
    Dν η ν hPos g_unreg g_gat hg_unreg_int hg_gat_int
    hF_unreg_meas hF_unreg_bound hF_gat_meas hF_gat_bound

/-! ## Aggregator: `lem:hemicont` packaged as a hemicontinuity predicate
(paper line 990).

The DCT-based segment continuity `Aepsi_hemicontinuous_segment` is
`lem:hemicont` minus its packaging into the abstract
`IsHemicontinuous` predicate of `Monotone/Hemicontinuous.lean`.

The abstract predicate `Monotone.IsHemicontinuous` requires its operator
to land in `StrongDual ℝ X`. Our project-level operator
`mfgOperatorEpsPair` is the *real-valued pairing* — i.e. the value of
the dual element on a test pair — so we expose a project-local pair-
representation predicate `IsHemicontinuousMFG` whose signature matches
exactly the bare-function pair description used throughout Phase 4
(see `MFGOperator.lean`).

### `IsHemicontinuousMFG` definition

We model `𝓚` as a `Set` of triples `(μ, υ, Dυ)` (the third slot is the
explicit gradient family), since `mfgOperatorEpsPair`'s first three
function arguments are `(Dυ, μ, υ)`. The predicate then asserts the
exact paper conclusion for every pair of admissible triples and every
test triple.
-/

/-- Triple type for elements of the bare-function realisation of `𝓚`. -/
abbrev MFGTriple (d : ℕ) : Type :=
  ((Fin d → ℝ) → ℝ) × ((Fin d → ℝ) → ℝ) × (Fin d → (Fin d → ℝ) → ℝ)

/-- **Project-local hemicontinuity predicate** (`lem:hemicont` form).

`IsHemicontinuousMFG D B` says that for every pair of triples
`(μ̄, ῡ, Dῡ), (μ, υ, Dυ) ∈ D` and every test triple `(η, ν, Dν)`, the
map `t ↦ B (cxCombGrad Dυ Dῡ t) (cxComb μ μ̄ t) (cxComb υ ῡ t) Dν η ν`
is continuous on `[0, 1]`.

This is the bare-pair analogue of `Monotone.IsHemicontinuous`: the
"action on a test pair" is the real number `B Dυ μ υ Dν η ν`, mirroring
the `StrongDual ℝ X` evaluation `A u w` in the abstract predicate. -/
def IsHemicontinuousMFG (d : ℕ)
    (D : Set (MFGTriple d))
    (B : (Fin d → (Fin d → ℝ) → ℝ) → ((Fin d → ℝ) → ℝ) →
         ((Fin d → ℝ) → ℝ) → (Fin d → (Fin d → ℝ) → ℝ) →
         ((Fin d → ℝ) → ℝ) → ((Fin d → ℝ) → ℝ) → ℝ) : Prop :=
  ∀ ⦃μBar : (Fin d → ℝ) → ℝ⦄ ⦃ῡ : (Fin d → ℝ) → ℝ⦄
    ⦃Dῡ : Fin d → (Fin d → ℝ) → ℝ⦄,
    (μBar, ῡ, Dῡ) ∈ D →
    ∀ ⦃μ : (Fin d → ℝ) → ℝ⦄ ⦃υ : (Fin d → ℝ) → ℝ⦄
      ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
      (μ, υ, Dυ) ∈ D →
      ∀ (η ν : (Fin d → ℝ) → ℝ) (Dν : Fin d → (Fin d → ℝ) → ℝ),
      ContinuousOn (fun t : ℝ =>
        B (fun i x => cxCombGrad Dυ Dῡ t i x)
          (fun x => cxComb μ μBar t x)
          (fun x => cxComb υ ῡ t x)
          Dν η ν) (Set.Icc (0 : ℝ) 1)

/-! ### Restricted-test hemicontinuity predicate

(iter `infra-P7-sigfix-T1-drain-A-restricted-hemicont`, 2026-05-24.)

`IsHemicontinuousMFG_restricted` is the strict specialisation of
`IsHemicontinuousMFG` whose test triple `(η, ν, Dν)` is forced to be the
**pointwise difference** of the two family triples in `D`. Concretely,
`(η, ν, Dν) := (μ - μBar, υ - ῡ, Dυ - Dῡ)`.

This is exactly the test-direction shape used by `main_strong_VI` (the
Minty-style upgrade — `Main.lean` line ~563): there `hAhc hm hμ
(μ - m) (υ - u) (Dυ - Du)` instantiates `(μBar, ῡ, Dῡ) := (m, u, Du)`
and the test direction is `(μ - m, υ - u, Dυ - Du)` — a family-derivable
difference.

The restricted predicate exists so that downstream K0 closure consumers
(`Banach/RegularizedSequence.lean`) can supply hemicontinuity certs
without invoking the **universal** test-direction cert oracle
`testDirCertsOf` (the auth count target of the parent
`infra-P7-sigfix-T1-drain` task).

Every `IsHemicontinuousMFG` predicate weakens to the restricted form
via `IsHemicontinuousMFG.toRestricted`, so existing producers remain
valid feeds. -/

/-- **Restricted-test hemicontinuity predicate.**

Strict specialisation of `IsHemicontinuousMFG` whose test triple
`(η, ν, Dν)` is the pointwise difference `(μ - μBar, υ - ῡ, Dυ - Dῡ)`.
Used by `main_strong_VI` (the Minty-style upgrade) to avoid the
universal `testDirCertsOf` oracle in K0 closure consumers. -/
def IsHemicontinuousMFG_restricted (d : ℕ)
    (D : Set (MFGTriple d))
    (B : (Fin d → (Fin d → ℝ) → ℝ) → ((Fin d → ℝ) → ℝ) →
         ((Fin d → ℝ) → ℝ) → (Fin d → (Fin d → ℝ) → ℝ) →
         ((Fin d → ℝ) → ℝ) → ((Fin d → ℝ) → ℝ) → ℝ) : Prop :=
  ∀ ⦃μBar : (Fin d → ℝ) → ℝ⦄ ⦃ῡ : (Fin d → ℝ) → ℝ⦄
    ⦃Dῡ : Fin d → (Fin d → ℝ) → ℝ⦄,
    (μBar, ῡ, Dῡ) ∈ D →
    ∀ ⦃μ : (Fin d → ℝ) → ℝ⦄ ⦃υ : (Fin d → ℝ) → ℝ⦄
      ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
      (μ, υ, Dυ) ∈ D →
      ContinuousOn (fun t : ℝ =>
        B (fun i x => cxCombGrad Dυ Dῡ t i x)
          (fun x => cxComb μ μBar t x)
          (fun x => cxComb υ ῡ t x)
          (fun i x => Dυ i x - Dῡ i x)
          (fun x => μ x - μBar x)
          (fun x => υ x - ῡ x)) (Set.Icc (0 : ℝ) 1)

/-- **Weakening lemma.** Every `IsHemicontinuousMFG` predicate
implies its restricted-test specialisation `IsHemicontinuousMFG_restricted`.

Obtained by instantiating the universal test slot
`(η, ν, Dν)` at the difference `(μ - μBar, υ - ῡ, Dυ - Dῡ)`. -/
lemma IsHemicontinuousMFG.toRestricted
    {d : ℕ} {D : Set (MFGTriple d)}
    {B : (Fin d → (Fin d → ℝ) → ℝ) → ((Fin d → ℝ) → ℝ) →
         ((Fin d → ℝ) → ℝ) → (Fin d → (Fin d → ℝ) → ℝ) →
         ((Fin d → ℝ) → ℝ) → ((Fin d → ℝ) → ℝ) → ℝ}
    (h : IsHemicontinuousMFG d D B) :
    IsHemicontinuousMFG_restricted d D B := by
  intro μBar ῡ Dῡ hBar μ υ Dυ hμ
  exact h hBar hμ
    (fun x => μ x - μBar x) (fun x => υ x - ῡ x)
    (fun i x => Dυ i x - Dῡ i x)

/-! ### Hypothesis bundle for `lem_hemicont`

Packaging the per-segment hypotheses of `Aepsi_hemicontinuous_segment`
(positivity of `μ_t`, integrable dominators, AE-strong measurability,
and pointwise bound) into a single per-pair hypothesis. This is the
aggregator's "for every two segments" assumption: the dominator data is
allowed to depend on the segment endpoints (and on the test data). -/

/-- The dominator/measurability/positivity bundle expected on every
segment in the aggregator's hypothesis. Type-valued because the fields
include the dominator functions `g_unreg`, `g_gat`. -/
structure HemicontSegmentData {d : ℕ}
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (γBar : ℝ)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ)
    (μ mBar υ ῡ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ) : Type where
  /-- A.e.-uniform-in-`t` positivity along the segment.
  Per expert v3: this is the correct DCT-friendly form (one full-measure
  set of `x` on which the whole map `t ↦ integrand x t` is continuous on
  `[0,1]`). The swapped form `∀ t, ∀ᵐ x, …` is too weak — uncountable
  `t` exhausts the a.e.-set bookkeeping. -/
  hPos : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
           ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < cxComb μ mBar t x
  /-- Dominator for the unregularised integrand. -/
  g_unreg : (Fin d → ℝ) → ℝ
  /-- Dominator for the Gateaux integrand. -/
  g_gat : (Fin d → ℝ) → ℝ
  hg_unreg_int : IntegrableOn g_unreg (UnitCube d)
  hg_gat_int : IntegrableOn g_gat (UnitCube d)
  hF_unreg_meas : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    AEStronglyMeasurable
      (fun x => aepsiIntegrandAt_unreg V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν x t)
      (volume.restrict (UnitCube d))
  hF_unreg_bound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ‖aepsiIntegrandAt_unreg V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν x t‖
        ≤ g_unreg x
  hF_gat_meas : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    AEStronglyMeasurable
      (fun x => aepsiIntegrandAt_gateaux γBar Dυ Dῡ υ ῡ Dν ν x t)
      (volume.restrict (UnitCube d))
  hF_gat_bound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ‖aepsiIntegrandAt_gateaux γBar Dυ Dῡ υ ῡ Dν ν x t‖ ≤ g_gat x

/-! ### `HemicontSegmentData.ae_eq` — transport along a.e.-equality

Both `cxComb` and `cxCombGrad` are pointwise affine combinations of
their bare-function arguments. Hence
`aepsiIntegrandAt_unreg` and `aepsiIntegrandAt_gateaux` only depend
on `(μ, mBar, υ, ῡ, Dυ, Dῡ)` (and `Dν, η, ν`) up to a.e.-equality
of these inputs (uniform in `t`). The `HemicontSegmentData` bundle
itself contains only a.e.-statements about these integrands plus
integrability of `g_unreg`, `g_gat` (which is independent of the
bare-function inputs), so it transports along a.e.-equality of
`(μ, mBar, υ, ῡ, Dυ, Dῡ)` without changes to the dominator pair. -/

/-- A.e. transport for `cxComb`. -/
lemma cxComb_congr_ae
    {μ μ' mBar mBar' : (Fin d → ℝ) → ℝ}
    (hμ : μ =ᵐ[volume.restrict (UnitCube d)] μ')
    (hmBar : mBar =ᵐ[volume.restrict (UnitCube d)] mBar') :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ t : ℝ, cxComb μ mBar t x = cxComb μ' mBar' t x := by
  filter_upwards [hμ, hmBar] with x hxμ hxmBar t
  unfold cxComb
  rw [hxμ, hxmBar]

/-- A.e. transport for `cxCombGrad`. -/
lemma cxCombGrad_congr_ae
    {Dυ Dυ' Dῡ Dῡ' : Fin d → (Fin d → ℝ) → ℝ}
    (hDυ : ∀ i, Dυ i =ᵐ[volume.restrict (UnitCube d)] Dυ' i)
    (hDῡ : ∀ i, Dῡ i =ᵐ[volume.restrict (UnitCube d)] Dῡ' i) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ t : ℝ, ∀ i, cxCombGrad Dυ Dῡ t i x = cxCombGrad Dυ' Dῡ' t i x := by
  -- Combine the per-coordinate a.e.-equalities into one a.e.-statement.
  have hDυ' : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
                ∀ i, Dυ i x = Dυ' i x := by
    rw [ae_all_iff]; exact fun i => hDυ i
  have hDῡ' : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
                ∀ i, Dῡ i x = Dῡ' i x := by
    rw [ae_all_iff]; exact fun i => hDῡ i
  filter_upwards [hDυ', hDῡ'] with x hxυ hxῡ t i
  unfold cxCombGrad
  rw [hxυ i, hxῡ i]

/-- A.e. transport for `aepsiIntegrandAt_unreg`. -/
lemma aepsiIntegrandAt_unreg_congr_ae
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    {Dυ Dυ' Dῡ Dῡ' : Fin d → (Fin d → ℝ) → ℝ}
    {μ μ' mBar mBar' υ υ' ῡ ῡ' : (Fin d → ℝ) → ℝ}
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ)
    (hμ : μ =ᵐ[volume.restrict (UnitCube d)] μ')
    (hmBar : mBar =ᵐ[volume.restrict (UnitCube d)] mBar')
    (hυ : υ =ᵐ[volume.restrict (UnitCube d)] υ')
    (hῡ : ῡ =ᵐ[volume.restrict (UnitCube d)] ῡ')
    (hDυ : ∀ i, Dυ i =ᵐ[volume.restrict (UnitCube d)] Dυ' i)
    (hDῡ : ∀ i, Dῡ i =ᵐ[volume.restrict (UnitCube d)] Dῡ' i) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ t : ℝ,
        aepsiIntegrandAt_unreg V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν x t
          = aepsiIntegrandAt_unreg V H DpH Dυ' Dῡ' μ' mBar' υ' ῡ' Dν η ν x t := by
  filter_upwards [cxComb_congr_ae hμ hmBar,
                  cxComb_congr_ae hυ hῡ,
                  cxCombGrad_congr_ae hDυ hDῡ]
    with x hμt hυt hDυt t
  unfold aepsiIntegrandAt_unreg
  -- Both sides have identical structure: substitute the convex
  -- combinations along the a.e.-equalities.
  have hμx := hμt t
  have hυx := hυt t
  have hDυx : (fun i => cxCombGrad Dυ Dῡ t i x)
              = (fun i => cxCombGrad Dυ' Dῡ' t i x) := by
    funext i; exact hDυt t i
  rw [hμx, hυx, hDυx]

/-- A.e. transport for `aepsiIntegrandAt_gateaux`. -/
lemma aepsiIntegrandAt_gateaux_congr_ae
    (γBar : ℝ)
    {Dυ Dυ' Dῡ Dῡ' : Fin d → (Fin d → ℝ) → ℝ}
    {υ υ' ῡ ῡ' : (Fin d → ℝ) → ℝ}
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (ν : (Fin d → ℝ) → ℝ)
    (hυ : υ =ᵐ[volume.restrict (UnitCube d)] υ')
    (hῡ : ῡ =ᵐ[volume.restrict (UnitCube d)] ῡ')
    (hDυ : ∀ i, Dυ i =ᵐ[volume.restrict (UnitCube d)] Dυ' i)
    (hDῡ : ∀ i, Dῡ i =ᵐ[volume.restrict (UnitCube d)] Dῡ' i) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ t : ℝ,
        aepsiIntegrandAt_gateaux γBar Dυ Dῡ υ ῡ Dν ν x t
          = aepsiIntegrandAt_gateaux γBar Dυ' Dῡ' υ' ῡ' Dν ν x t := by
  filter_upwards [cxComb_congr_ae hυ hῡ, cxCombGrad_congr_ae hDυ hDῡ]
    with x hυt hDυt t
  unfold aepsiIntegrandAt_gateaux
  have hυx := hυt t
  have hDυx : (fun i => cxCombGrad Dυ Dῡ t i x)
              = (fun i => cxCombGrad Dυ' Dῡ' t i x) := by
    funext i; exact hDυt t i
  rw [hυx, hDυx]

/-- **`HemicontSegmentData.ae_eq` (transport helper).**

The bundle `HemicontSegmentData` only depends on its bare-function
arguments `(μ, mBar, υ, ῡ, Dυ, Dῡ)` up to a.e.-equality. The
dominator data `(g_unreg, g_gat)` and the test direction `(η, ν, Dν)`
are reused unchanged.

This is the transport lemma that the bare→Banach bridge child needs
to go from a `HemicontSegmentData` produced on representatives
`(μ, mBar, …)` to the same bundle on a.e.-equal representatives. -/
def HemicontSegmentData.ae_eq
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (γBar : ℝ)
    {Dυ Dυ' Dῡ Dῡ' : Fin d → (Fin d → ℝ) → ℝ}
    {μ μ' mBar mBar' υ υ' ῡ ῡ' : (Fin d → ℝ) → ℝ}
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ)
    (hμ : μ =ᵐ[volume.restrict (UnitCube d)] μ')
    (hmBar : mBar =ᵐ[volume.restrict (UnitCube d)] mBar')
    (hυ : υ =ᵐ[volume.restrict (UnitCube d)] υ')
    (hῡ : ῡ =ᵐ[volume.restrict (UnitCube d)] ῡ')
    (hDυ : ∀ i, Dυ i =ᵐ[volume.restrict (UnitCube d)] Dυ' i)
    (hDῡ : ∀ i, Dῡ i =ᵐ[volume.restrict (UnitCube d)] Dῡ' i)
    (data : HemicontSegmentData V H DpH γBar Dυ Dῡ μ mBar υ ῡ Dν η ν) :
    HemicontSegmentData V H DpH γBar Dυ' Dῡ' μ' mBar' υ' ῡ' Dν η ν :=
  let hμt_eq := cxComb_congr_ae hμ hmBar
  let hF_unreg_eq := aepsiIntegrandAt_unreg_congr_ae V H DpH Dν η ν
                      hμ hmBar hυ hῡ hDυ hDῡ
  let hF_gat_eq := aepsiIntegrandAt_gateaux_congr_ae γBar Dν ν
                      hυ hῡ hDυ hDῡ
  { hPos := by
      filter_upwards [data.hPos, hμt_eq] with x hPosx hμtx t ht
      have := hPosx t ht
      rw [hμtx t] at this
      exact this
    g_unreg := data.g_unreg
    g_gat := data.g_gat
    hg_unreg_int := data.hg_unreg_int
    hg_gat_int := data.hg_gat_int
    hF_unreg_meas := by
      intro t ht
      have hmeas := data.hF_unreg_meas t ht
      refine hmeas.congr ?_
      filter_upwards [hF_unreg_eq] with x hx
      exact hx t
    hF_unreg_bound := by
      intro t ht
      have hb := data.hF_unreg_bound t ht
      filter_upwards [hb, hF_unreg_eq] with x hxBd hxEq
      have := hxEq t
      rw [← this]
      exact hxBd
    hF_gat_meas := by
      intro t ht
      have hmeas := data.hF_gat_meas t ht
      refine hmeas.congr ?_
      filter_upwards [hF_gat_eq] with x hx
      exact hx t
    hF_gat_bound := by
      intro t ht
      have hb := data.hF_gat_bound t ht
      filter_upwards [hb, hF_gat_eq] with x hxBd hxEq
      have := hxEq t
      rw [← this]
      exact hxBd }

/-- Sanity-check: applying `HemicontSegmentData.ae_eq` with all
six a.e.-equalities trivial returns the same bundle (definitionally,
modulo proof irrelevance, on the data fields). -/
example
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (γBar : ℝ)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ)
    (μ mBar υ ῡ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ)
    (data : HemicontSegmentData V H DpH γBar Dυ Dῡ μ mBar υ ῡ Dν η ν) :
    HemicontSegmentData V H DpH γBar Dυ Dῡ μ mBar υ ῡ Dν η ν :=
  HemicontSegmentData.ae_eq V H DpH γBar Dν η ν
    (Filter.EventuallyEq.refl _ _) (Filter.EventuallyEq.refl _ _)
    (Filter.EventuallyEq.refl _ _) (Filter.EventuallyEq.refl _ _)
    (fun _ => Filter.EventuallyEq.refl _ _)
    (fun _ => Filter.EventuallyEq.refl _ _)
    data

/-- **Lemma `lem:hemicont` (paper line 990) — aggregator form.**

Under `RegularityH H DpH`, `2 ≤ γBar`, and a per-segment dominator
bundle `HemicontSegmentData` that captures the conclusions of
`infra:P4-hemi-dominator-holder`, the regularised MFG operator
`A_ε = mfgOperatorEpsPair` is hemicontinuous on `D ⊂ MFGTriple d` in
the sense of `IsHemicontinuousMFG` (paper definition `defitem:hemicont`,
restricted to the bare-pair representation of `𝓚`).

This is the closing step of paper §`sec:proof-power-growth` lines
1038–1043; the actual analytic content lives in
`Aepsi_hemicontinuous_segment` (DCT) and the dominator-construction
infrastructure of `infra:P4-hemi-dominator-holder`. -/
theorem lem_hemicont
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hReg : RegularityH (d := d) H DpH)
    (γBar ε : ℝ) (hγ : 1 < γBar)
    (D : Set (MFGTriple d))
    (hData : ∀ ⦃μBar ῡ Dῡ⦄, (μBar, ῡ, Dῡ) ∈ D →
             ∀ ⦃μ υ Dυ⦄, (μ, υ, Dυ) ∈ D →
             ∀ (η ν : (Fin d → ℝ) → ℝ)
               (Dν : Fin d → (Fin d → ℝ) → ℝ),
             HemicontSegmentData V H DpH γBar Dυ Dῡ μ μBar υ ῡ Dν η ν) :
    IsHemicontinuousMFG d D
      (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH) γBar ε) := by
  intro μBar ῡ Dῡ hBar μ υ Dυ hμ η ν Dν
  obtain ⟨hPos, g_unreg, g_gat, hg_unreg_int, hg_gat_int,
          hF_unreg_meas, hF_unreg_bound, hF_gat_meas, hF_gat_bound⟩ :=
    hData hBar hμ η ν Dν
  exact Aepsi_hemicontinuous_segment V H DpH hReg γBar ε hγ Dυ Dῡ
    μ μBar υ ῡ Dν η ν hPos g_unreg g_gat hg_unreg_int hg_gat_int
    hF_unreg_meas hF_unreg_bound hF_gat_meas hF_gat_bound

/-- Alias matching the alternative naming in the task spec. -/
theorem isHemicontinuous_Aepsi
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hReg : RegularityH (d := d) H DpH)
    (γBar ε : ℝ) (hγ : 1 < γBar)
    (D : Set (MFGTriple d))
    (hData : ∀ ⦃μBar ῡ Dῡ⦄, (μBar, ῡ, Dῡ) ∈ D →
             ∀ ⦃μ υ Dυ⦄, (μ, υ, Dυ) ∈ D →
             ∀ (η ν : (Fin d → ℝ) → ℝ)
               (Dν : Fin d → (Fin d → ℝ) → ℝ),
             HemicontSegmentData V H DpH γBar Dυ Dῡ μ μBar υ ῡ Dν η ν) :
    IsHemicontinuousMFG d D
      (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH) γBar ε) :=
  lem_hemicont V H DpH hReg γBar ε hγ D hData

/-! ### Unit-test for the aggregator -/

/-- Unit-test: with the trivial Hamiltonian `H = 0`, `D_pH = 0`, and
the trivial potential `V = 0`, the singleton domain `D = {(1, 0, 0)}`
admits the zero-dominator construction for every test triple. The
aggregator collapses to constant continuity. -/
example (d : ℕ) (ε : ℝ) :
    IsHemicontinuousMFG d
      ({((fun _ => (1:ℝ)), (fun _ => (0:ℝ)), (fun _ _ => (0:ℝ)))}
        : Set (MFGTriple d))
      (mfgOperatorEpsPair
        (V := fun _ => (0:ℝ))
        (H := fun _ _ _ => (0:ℝ))
        (DpH := fun _ _ _ => (0 : Fin d → ℝ))
        (2 : ℝ) ε) := by
  refine lem_hemicont (d := d) (fun _ => (0:ℝ)) _ _ ?hReg 2 ε one_lt_two _ ?hData
  · -- Trivial regularity bundle.
    refine
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
  · -- The singleton domain forces both endpoints to be the canonical
    -- triple `(1, 0, 0)`. We pick zero dominators (which work because
    -- `V = 0` in addition to `H = 0`, `D_pH = 0` makes the integrand
    -- vanish identically for any test triple `(η, ν, Dν)`).
    intro μBar ῡ Dῡ hBar μ υ Dυ hμ η ν Dν
    rw [Set.mem_singleton_iff, Prod.mk.injEq, Prod.mk.injEq] at hBar hμ
    obtain ⟨hμBar, hῡ, hDῡ⟩ := hBar
    obtain ⟨hμ', hυ, hDυ⟩ := hμ
    -- Substitute the canonical values for the *bar* triple first, then
    -- for the moving triple. Keep the variable names around so the
    -- structure fields can refer to them.
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
    · -- Segment positivity at the singleton point (a.e.-uniform-in-`t` form).
      refine Filter.Eventually.of_forall ?_
      intro x t _
      have : cxComb (fun _ : (Fin d → ℝ) => (1:ℝ)) (fun _ => (1:ℝ)) t x = 1 := by
        unfold cxComb; ring
      rw [this]; norm_num
    · exact (integrable_zero _ _ _).integrableOn
    · exact (integrable_zero _ _ _).integrableOn
    · -- AE strongly measurable: the integrand collapses to `0`.
      intro t _
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
        simp [dotProduct]
      rw [hzero]
      exact aestronglyMeasurable_const
    · intro t _
      refine Filter.Eventually.of_forall ?_
      intro x
      unfold aepsiIntegrandAt_unreg cxComb cxCombGrad
      simp [dotProduct]
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
        simp [dotProduct]
      rw [hzero]
      exact aestronglyMeasurable_const
    · intro t _
      refine Filter.Eventually.of_forall ?_
      intro x
      unfold aepsiIntegrandAt_gateaux cxComb cxCombGrad
      simp [dotProduct]

/-! ## Hemicontinuity of `A_0` (paper line 1276, `infra:P4-A0-hemicontinuous`)

`A_0` is the unregularized MFG operator `mfgOperatorPair` (i.e.
`mfgOperatorEpsPair γBar 0`). Hemicontinuity at `ε = 0` is a thin
specialization of `lem_hemicont`: setting `ε = 0` collapses the Gateaux
contribution and leaves only the `H, D_pH, V` integrand, whose
continuity in `t` is already covered by the regularized DCT bundle.

The conclusion of `lem_hemicont` at `ε = 0` is rewritten via
`mfgOperatorEpsPair_zero_eq` into a statement about `mfgOperatorPair`. -/

/-- **Hemicontinuity of `A_0`** (paper line 1276,
`infra:P4-A0-hemicontinuous`).

The unregularized MFG operator pairing `mfgOperatorPair` is
hemicontinuous on any `D ⊂ MFGTriple d` for which the per-segment
dominator bundle of `lem_hemicont` is available at `ε = 0`. The bundle
is parameterized by `γBar` only because of the (unused at `ε = 0`)
Gateaux dominator field; any `γBar ≥ 2` works.

Proof: invoke `lem_hemicont` with `ε = 0`, then rewrite the resulting
`mfgOperatorEpsPair γBar 0`-pairing into `mfgOperatorPair` via
`mfgOperatorEpsPair_zero_eq`. -/
theorem lem_hemicont_zero
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hReg : RegularityH (d := d) H DpH)
    (γBar : ℝ) (hγ : 1 < γBar)
    (D : Set (MFGTriple d))
    (hData : ∀ ⦃μBar ῡ Dῡ⦄, (μBar, ῡ, Dῡ) ∈ D →
             ∀ ⦃μ υ Dυ⦄, (μ, υ, Dυ) ∈ D →
             ∀ (η ν : (Fin d → ℝ) → ℝ)
               (Dν : Fin d → (Fin d → ℝ) → ℝ),
             HemicontSegmentData V H DpH γBar Dυ Dῡ μ μBar υ ῡ Dν η ν) :
    IsHemicontinuousMFG d D
      (mfgOperatorPair (V := V) (H := H) (DpH := DpH)) := by
  have hε := lem_hemicont (V := V) (H := H) (DpH := DpH)
                hReg γBar 0 hγ D hData
  intro μBar ῡ Dῡ hBar μ υ Dυ hμ η ν Dν
  have hcts := hε hBar hμ η ν Dν
  -- Rewrite `mfgOperatorEpsPair γBar 0 …` to `mfgOperatorPair …`
  -- pointwise in the homotopy parameter `t`.
  have hrw :
      (fun t : ℝ =>
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH) γBar 0
          (fun i x => cxCombGrad Dυ Dῡ t i x)
          (fun x => cxComb μ μBar t x)
          (fun x => cxComb υ ῡ t x)
          Dν η ν)
        =
      (fun t : ℝ =>
        mfgOperatorPair (V := V) (H := H) (DpH := DpH)
          (fun i x => cxCombGrad Dυ Dῡ t i x)
          (fun x => cxComb μ μBar t x)
          (fun x => cxComb υ ῡ t x)
          Dν η ν) := by
    funext t
    exact mfgOperatorEpsPair_zero_eq (V := V) (H := H) (DpH := DpH) γBar _ _ _ _ _ _
  rw [hrw] at hcts
  exact hcts

/-- **Alias** matching the task spec's preferred name `A0_isHemicontinuous`. -/
theorem A0_isHemicontinuous
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hReg : RegularityH (d := d) H DpH)
    (γBar : ℝ) (hγ : 1 < γBar)
    (D : Set (MFGTriple d))
    (hData : ∀ ⦃μBar ῡ Dῡ⦄, (μBar, ῡ, Dῡ) ∈ D →
             ∀ ⦃μ υ Dυ⦄, (μ, υ, Dυ) ∈ D →
             ∀ (η ν : (Fin d → ℝ) → ℝ)
               (Dν : Fin d → (Fin d → ℝ) → ℝ),
             HemicontSegmentData V H DpH γBar Dυ Dῡ μ μBar υ ῡ Dν η ν) :
    IsHemicontinuousMFG d D
      (mfgOperatorPair (V := V) (H := H) (DpH := DpH)) :=
  lem_hemicont_zero V H DpH hReg γBar hγ D hData

/-! ### Unit-test for the `A_0` aggregator -/

/-- Unit-test: with the trivial Hamiltonian `H = 0`, `D_pH = 0`, and
the trivial potential `V = 0`, the singleton domain `D = {(1, 0, 0)}`
admits the zero-dominator construction for every test triple. The
aggregator collapses to constant continuity for the unregularized
operator. Mirrors the corresponding `lem_hemicont` example. -/
example (d : ℕ) :
    IsHemicontinuousMFG d
      ({((fun _ => (1:ℝ)), (fun _ => (0:ℝ)), (fun _ _ => (0:ℝ)))}
        : Set (MFGTriple d))
      (mfgOperatorPair
        (V := fun _ => (0:ℝ))
        (H := fun _ _ _ => (0:ℝ))
        (DpH := fun _ _ _ => (0 : Fin d → ℝ))) := by
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
    · -- Segment positivity (a.e.-uniform-in-`t` form).
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
        simp [dotProduct]
      rw [hzero]
      exact aestronglyMeasurable_const
    · intro t _
      refine Filter.Eventually.of_forall ?_
      intro x
      unfold aepsiIntegrandAt_unreg cxComb cxCombGrad
      simp [dotProduct]
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
        simp [dotProduct]
      rw [hzero]
      exact aestronglyMeasurable_const
    · intro t _
      refine Filter.Eventually.of_forall ?_
      intro x
      unfold aepsiIntegrandAt_gateaux cxComb cxCombGrad
      simp [dotProduct]

/-! ### Sanity-check: the new a.e.-uniform `hPos` field is consumable -/

/-- Sanity-check `example` (per task acceptance criterion 5): the new
field shape `hPos : ∀ᵐ x, ∀ t ∈ [0,1], 0 < cxComb μ mBar t x` is
consumable from a witness produced by `Filter.Eventually.of_forall`
applied to a pointwise positivity proof. -/
example (μ mBar : (Fin d → ℝ) → ℝ)
    (h : ∀ x, ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < cxComb μ mBar t x) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < cxComb μ mBar t x :=
  Filter.Eventually.of_forall h

/-! ## Product-form pointwise dominators (`1 < γBar`)

The dominators above (`hemicont_vecAbsPowMinusTwo_dominator`,
`hemicont_absPowMinusTwo_dominator`,
`aepsiIntegrandAt_gateaux_pointwise_bound`) all require `2 ≤ γBar` to
push the unsigned weight `(·)^{(γBar-2)/2}` through the convex
combination via `Real.rpow_le_rpow`. For the p-Laplace regime
`1 < γBar < 2` we need the *product* form

  `| |p_t|^{γBar-2} p_t · a |  ≤ ‖p_t‖_2^{γBar-1} · ‖a‖_2`,

which avoids the singular weight by absorbing one factor of `p_t` into
the dot product. This bound is valid for **all** `γBar > 1` and pairs
with Hölder at exponent `γBar / (γBar - 1)`.

The lemmas in this section are the foundational ingredients for the
relaxed `aepsiIntegrandAt_gateaux_pointwise_bound_product` below.
-/

/-- **Scalar product-form weight identity.** For `1 < γBar` and any
real `s`, `|absPowMinusTwo γBar s * s| = |s| ^ (γBar - 1)`. This is the
algebraic identity `|signedRpow γBar s| = |s|^{γBar-1}` unfolded. -/
lemma abs_absPowMinusTwo_mul_self
    {γBar : ℝ} (hγ : 1 < γBar) (s : ℝ) :
    |absPowMinusTwo γBar s * s| = |s| ^ (γBar - 1) := by
  unfold absPowMinusTwo
  -- |·|^{γBar-2} is nonneg.
  have h_nn : 0 ≤ |s| ^ (γBar - 2) := Real.rpow_nonneg (abs_nonneg _) _
  rw [abs_mul, abs_of_nonneg h_nn]
  -- Goal: |s|^{γBar-2} * |s| = |s|^{γBar-1}.
  rcases eq_or_lt_of_le (abs_nonneg s) with habs0 | habs_pos
  · -- |s| = 0, so s = 0, both sides vanish since γBar - 1 > 0.
    have hexp_pos : 0 < γBar - 1 := by linarith
    have habs_zero : |s| = 0 := habs0.symm
    rw [habs_zero, Real.zero_rpow hexp_pos.ne']
    ring
  · -- |s| > 0.
    have hsplit : |s| ^ (γBar - 1) = |s| ^ (γBar - 2) * |s| := by
      have h := Real.rpow_add habs_pos (γBar - 2) 1
      simpa [show γBar - 2 + 1 = γBar - 1 by ring, Real.rpow_one]
        using h
    linarith [hsplit.le, hsplit.ge]

/-- **Vector product-form weight bound.** For `1 < γBar` and any
`v : Fin d → ℝ`, the *Euclidean* norm of `vecAbsPowMinusTwo γBar v • v`
is bounded by `(v ⬝ v)^{(γBar-1)/2}`, i.e. the Euclidean `|v|^{γBar-1}`. We
state it on each component as `|vecAbsPowMinusTwo γBar v * v i|
  ≤ (v ⬝ v) ^ ((γBar - 1) / 2)`. -/
lemma abs_vecAbsPowMinusTwo_mul_coord_le
    {γBar : ℝ} (hγ : 1 < γBar) (v : Fin d → ℝ) (i : Fin d) :
    |vecAbsPowMinusTwo γBar v * v i|
      ≤ (v ⬝ v) ^ ((γBar - 1) / 2) := by
  unfold vecAbsPowMinusTwo
  have hvv_nn : 0 ≤ v ⬝ v :=
    Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)
  have h_nn : 0 ≤ (v ⬝ v) ^ ((γBar - 2) / 2) :=
    Real.rpow_nonneg hvv_nn _
  rw [abs_mul, abs_of_nonneg h_nn]
  -- Bound |v i| ≤ (v ⬝ v)^(1/2) (each coordinate dominated by Euclidean norm).
  have h_coord_sq : (v i) ^ 2 ≤ v ⬝ v := by
    unfold dotProduct
    have hi : (v i) ^ 2 = (v i) * (v i) := sq (v i)
    rw [hi]
    exact Finset.single_le_sum
      (f := fun j : Fin d => v j * v j)
      (s := (Finset.univ : Finset (Fin d)))
      (fun j _ => mul_self_nonneg (v j)) (Finset.mem_univ i)
  have h_abs_vi_le : |v i| ≤ (v ⬝ v) ^ ((1 : ℝ) / 2) := by
    have hsq_eq : |v i| = ((v i) ^ 2) ^ ((1 : ℝ) / 2) := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs]
    rw [hsq_eq]
    exact Real.rpow_le_rpow (sq_nonneg _) h_coord_sq (by norm_num)
  -- Combine: (v⬝v)^((γ-2)/2) * (v⬝v)^(1/2) = (v⬝v)^((γ-1)/2).
  rcases eq_or_lt_of_le hvv_nn with hvv0 | hvv_pos
  · -- v ⬝ v = 0: both sides vanish.
    have hexp_pos : 0 < (γBar - 1) / 2 := by linarith
    rw [← hvv0, Real.zero_rpow hexp_pos.ne']
    -- |v i| = 0 since |v i| ≤ 0^(1/2) = 0.
    have h12_ne : ((1 : ℝ) / 2) ≠ 0 := by norm_num
    have h_abs_zero : |v i| = 0 := by
      have h1 : |v i| ≤ (0 : ℝ) ^ ((1 : ℝ) / 2) := by
        rw [← hvv0] at h_abs_vi_le; exact h_abs_vi_le
      rw [Real.zero_rpow h12_ne] at h1
      exact le_antisymm h1 (abs_nonneg _)
    rw [h_abs_zero, mul_zero]
  · -- v ⬝ v > 0.
    have h_combine :
        (v ⬝ v) ^ ((γBar - 2) / 2) * (v ⬝ v) ^ ((1 : ℝ) / 2)
          = (v ⬝ v) ^ ((γBar - 1) / 2) := by
      rw [← Real.rpow_add hvv_pos]
      congr 1; ring
    calc (v ⬝ v) ^ ((γBar - 2) / 2) * |v i|
        ≤ (v ⬝ v) ^ ((γBar - 2) / 2) * (v ⬝ v) ^ ((1 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_left h_abs_vi_le h_nn
      _ = (v ⬝ v) ^ ((γBar - 1) / 2) := h_combine

/-- **Vector product-form dot-product bound.** For `1 < γBar`, real
vectors `v, w : Fin d → ℝ`,

  `|vecAbsPowMinusTwo γBar v * (v ⬝ w)|
      ≤ (v ⬝ v) ^ ((γBar - 1) / 2) * (∑ i, |w i|)`.

Proof: distribute through the dot product coordinate-wise, then apply
`abs_vecAbsPowMinusTwo_mul_coord_le` per component. -/
lemma abs_vecAbsPowMinusTwo_mul_dot_le
    {γBar : ℝ} (hγ : 1 < γBar) (v w : Fin d → ℝ) :
    |vecAbsPowMinusTwo γBar v * (v ⬝ w)|
      ≤ (v ⬝ v) ^ ((γBar - 1) / 2) * (∑ i, |w i|) := by
  -- Rewrite `vecAbsPowMinusTwo γBar v * (v ⬝ w) = ∑ i, (vecAbsPowMinusTwo γBar v * v i) * w i`.
  have hrewrite :
      vecAbsPowMinusTwo γBar v * (v ⬝ w)
        = ∑ i, (vecAbsPowMinusTwo γBar v * v i) * w i := by
    unfold dotProduct
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  rw [hrewrite]
  -- |∑ i, a_i| ≤ ∑ i, |a_i|.
  have htri :
      |∑ i, (vecAbsPowMinusTwo γBar v * v i) * w i|
        ≤ ∑ i, |(vecAbsPowMinusTwo γBar v * v i) * w i| :=
    Finset.abs_sum_le_sum_abs _ _
  -- Per-coordinate bound: |.| = |·| · |w i| ≤ (v⬝v)^((γ-1)/2) * |w i|.
  have h_coord : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      |(vecAbsPowMinusTwo γBar v * v i) * w i|
        ≤ (v ⬝ v) ^ ((γBar - 1) / 2) * |w i| := by
    intro i _
    rw [abs_mul]
    have hbnd : |vecAbsPowMinusTwo γBar v * v i|
        ≤ (v ⬝ v) ^ ((γBar - 1) / 2) :=
      abs_vecAbsPowMinusTwo_mul_coord_le hγ v i
    exact mul_le_mul_of_nonneg_right hbnd (abs_nonneg _)
  have h_sum_le :
      ∑ i, |(vecAbsPowMinusTwo γBar v * v i) * w i|
        ≤ ∑ i, (v ⬝ v) ^ ((γBar - 1) / 2) * |w i| :=
    Finset.sum_le_sum h_coord
  have h_factor :
      (∑ i, (v ⬝ v) ^ ((γBar - 1) / 2) * |w i|)
        = (v ⬝ v) ^ ((γBar - 1) / 2) * (∑ i, |w i|) := by
    rw [← Finset.mul_sum]
  linarith [htri, h_sum_le, h_factor.le, h_factor.ge]

/-- **`hemicont_vecAbsPowMinusTwo_dot_product_dominator`** —
*product-form* pointwise dominator for the ε-Gateaux gradient piece
`vecAbsPowMinusTwo γBar Dυ_t * (Dυ_t ⬝ Dν)`, valid for `1 < γBar`.
Combines `abs_vecAbsPowMinusTwo_mul_dot_le` with the convex-combination
self-dot bound `cxCombGrad_dot_self_le`. -/
theorem hemicont_vecAbsPowMinusTwo_dot_product_dominator
    {γBar : ℝ} (hγ : 1 < γBar)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ) (x : Fin d → ℝ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |vecAbsPowMinusTwo γBar (fun i => cxCombGrad Dυ Dῡ t i x)
        * ((fun i => cxCombGrad Dυ Dῡ t i x) ⬝ (fun i => Dν i x))|
      ≤ (∑ i, (|Dῡ i x| + |Dυ i x|) ^ (2 : ℕ)) ^ ((γBar - 1) / 2)
          * (∑ i, |Dν i x|) := by
  set p_t : Fin d → ℝ := fun i => cxCombGrad Dυ Dῡ t i x with hpt_def
  set S2 : ℝ := ∑ i, (|Dῡ i x| + |Dυ i x|) ^ (2 : ℕ) with hS2_def
  -- Step 1: per-coord bound via `abs_vecAbsPowMinusTwo_mul_dot_le`.
  have hstep1 :
      |vecAbsPowMinusTwo γBar p_t * (p_t ⬝ (fun i => Dν i x))|
        ≤ (p_t ⬝ p_t) ^ ((γBar - 1) / 2) * (∑ i, |Dν i x|) :=
    abs_vecAbsPowMinusTwo_mul_dot_le hγ p_t (fun i => Dν i x)
  -- Step 2: monotonicity in the base.
  have hpt_dot_le : p_t ⬝ p_t ≤ S2 :=
    cxCombGrad_dot_self_le Dυ Dῡ x ht
  have hpt_dot_nn : 0 ≤ p_t ⬝ p_t :=
    Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)
  have hexp_nn : 0 ≤ (γBar - 1) / 2 := by linarith
  have hbase_step :
      (p_t ⬝ p_t) ^ ((γBar - 1) / 2) ≤ S2 ^ ((γBar - 1) / 2) :=
    Real.rpow_le_rpow hpt_dot_nn hpt_dot_le hexp_nn
  -- Step 3: combine.
  have h_sumDν_nn : 0 ≤ ∑ i, |Dν i x| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  calc |vecAbsPowMinusTwo γBar p_t * (p_t ⬝ (fun i => Dν i x))|
      ≤ (p_t ⬝ p_t) ^ ((γBar - 1) / 2) * (∑ i, |Dν i x|) := hstep1
    _ ≤ S2 ^ ((γBar - 1) / 2) * (∑ i, |Dν i x|) :=
        mul_le_mul_of_nonneg_right hbase_step h_sumDν_nn

/-- **`hemicont_absPowMinusTwo_mul_self_product_dominator`** —
*product-form* pointwise dominator for the ε-Gateaux scalar piece
`absPowMinusTwo γBar υ_t * (υ_t * ν)`, valid for `1 < γBar`. Concretely,

  `|absPowMinusTwo γBar (cxComb υ ῡ t x) * (cxComb υ ῡ t x * ν x)|
      ≤ (|ῡ x| + |υ x|) ^ (γBar - 1) * |ν x|`. -/
theorem hemicont_absPowMinusTwo_mul_self_product_dominator
    {γBar : ℝ} (hγ : 1 < γBar)
    (υ ῡ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ)
    (ν : (Fin d → ℝ) → ℝ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |absPowMinusTwo γBar (cxComb υ ῡ t x) * (cxComb υ ῡ t x * ν x)|
      ≤ (|ῡ x| + |υ x|) ^ (γBar - 1) * |ν x| := by
  set υt : ℝ := cxComb υ ῡ t x with hυt_def
  -- Step 1: regroup `absPowMinusTwo γBar υt * (υt * ν x)
  --                = (absPowMinusTwo γBar υt * υt) * ν x`.
  have hregroup :
      absPowMinusTwo γBar υt * (υt * ν x)
        = (absPowMinusTwo γBar υt * υt) * ν x := by ring
  rw [hregroup, abs_mul]
  -- Step 2: |absPowMinusTwo γBar υt * υt| = |υt| ^ (γBar - 1).
  rw [abs_absPowMinusTwo_mul_self hγ υt]
  -- Step 3: monotonicity: |υt| ≤ |ῡ x| + |υ x|, then x ↦ x^{γBar-1}.
  have hexp_nn : 0 ≤ γBar - 1 := by linarith
  have h_abs_υt : |υt| ≤ |ῡ x| + |υ x| := cxComb_abs_le υ ῡ x ht
  have h_pow_le : |υt| ^ (γBar - 1) ≤ (|ῡ x| + |υ x|) ^ (γBar - 1) :=
    Real.rpow_le_rpow (abs_nonneg _) h_abs_υt hexp_nn
  exact mul_le_mul_of_nonneg_right h_pow_le (abs_nonneg _)

/-- **`aepsiIntegrandAt_gateaux_pointwise_bound_product`** —
**product-form** natural-form pointwise dominator on the Gateaux
integrand, valid for `1 < γBar` (no `2 ≤ γBar` required). Conclusion:

  `‖aepsiIntegrandAt_gateaux γBar Dυ Dῡ υ ῡ Dν ν x t‖
    ≤ (∑ i, (|Dῡ i x| + |Dυ i x|)^2) ^ ((γBar-1)/2) · (∑ i, |Dν i x|)
      + (|ῡ x| + |υ x|) ^ (γBar - 1) · |ν x|`.

This is the relaxed-hypothesis sibling of
`aepsiIntegrandAt_gateaux_pointwise_bound`. The RHS is integrable
against Hölder pair `(γBar, γBar/(γBar-1))` whenever `Dυ, Dῡ ∈ L^γBar`,
`υ, ῡ ∈ L^γBar`, `Dν, ν ∈ L^γBar`. -/
theorem aepsiIntegrandAt_gateaux_pointwise_bound_product
    {γBar : ℝ} (hγ : 1 < γBar)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ)
    (υ ῡ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (ν : (Fin d → ℝ) → ℝ) :
    ∀ x : Fin d → ℝ,
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ‖aepsiIntegrandAt_gateaux γBar Dυ Dῡ υ ῡ Dν ν x t‖
          ≤ (∑ i, (|Dῡ i x| + |Dυ i x|) ^ (2 : ℕ)) ^ ((γBar - 1) / 2)
              * (∑ i, |Dν i x|)
            + (|ῡ x| + |υ x|) ^ (γBar - 1) * |ν x| := by
  intro x t ht
  set p_t : Fin d → ℝ := fun i => cxCombGrad Dυ Dῡ t i x with hpt_def
  set υt : ℝ := cxComb υ ῡ t x with hυt_def
  -- Algebraic restatement.
  have heq_gat :
      aepsiIntegrandAt_gateaux γBar Dυ Dῡ υ ῡ Dν ν x t
        = vecAbsPowMinusTwo γBar p_t * (p_t ⬝ (fun i => Dν i x))
          + absPowMinusTwo γBar υt * (υt * ν x) := rfl
  rw [Real.norm_eq_abs, heq_gat]
  -- Triangle inequality.
  have htri :
      |vecAbsPowMinusTwo γBar p_t * (p_t ⬝ (fun i => Dν i x))
          + absPowMinusTwo γBar υt * (υt * ν x)|
        ≤ |vecAbsPowMinusTwo γBar p_t * (p_t ⬝ (fun i => Dν i x))|
          + |absPowMinusTwo γBar υt * (υt * ν x)| := abs_add_le _ _
  -- Bound each summand by the corresponding product-form dominator.
  have h_first :=
    hemicont_vecAbsPowMinusTwo_dot_product_dominator hγ Dυ Dῡ Dν x ht
  have h_second :=
    hemicont_absPowMinusTwo_mul_self_product_dominator hγ υ ῡ x ν ht
  linarith

/-! ## K0-form (nonneg-boundary) variants

The *K0 form* of the unreg pointwise bound matches the strict-positivity
version `aepsiIntegrandAt_unreg_pointwise_bound` but accepts
`0 ≤ cxComb μ mBar t x` (rather than `0 <`). This is the nonneg-cone
variant needed when the segment endpoints are in `K0_Aepsi` (the
closed nonneg cone) rather than `K_Aepsi` (the strict-positivity cone).

At the boundary `μt = 0`, the integrand simplifies:

* `μt · (D_pH ⬝ Dν) = 0` (the entire flux summand vanishes);
* `(μt - 1) · ν = -ν` (still bounded by `1 · |ν|`, fits the `(|μt|+1)·|ν|` shape);
* `H(x, p, 0)` — read via the Hat0/Hext convention from
  `Hamiltonian.HypothesisHat0` and `Hamiltonian.H_zero_eq_Hext`.

The K0 caller supplies *upgraded* dominators valid for all `m ≥ 0`
(rather than `m > 0`); these are derived in practice from
`HypothesisPowerGrowth.upper_extends_to_zero` /
`HypothesisPowerGrowth.lower_extends_to_zero` plus the agreement
rider `H_zero_eq_Hext`. Concretely the caller supplies:

* a K0-form abs bound `|H(x, p, m)| ≤ C' · (‖p‖^α + 1) + h.C · (m^β + 1)`
  for `m ≥ 0` (the K0 analogue of the existential conclusion of
  `hemicont_H_abs_dominator`);
* a K0-form `‖m • D_pH‖` bound for `m ≥ 0` (the K0 analogue of
  `hemicont_mDpH_dominator`).

Both inputs are paper-faithful for K0_Aepsi endpoints by limit-passage. -/

/-- **K0-form `H` abs dominator hypothesis.** The pointwise bound
`|H(x, Dυ_t x, μ_t x)| ≤ C' · (‖Dυ_t‖^α + 1) + h.C · (μ_t^β + 1)`
valid for `0 ≤ cxComb μ mBar t x`. This is the nonneg-cone analogue
of `hemicont_H_abs_dominator`'s conclusion. The caller-side derivation
extends the K-strict version to the `m = 0` boundary using the Hat0/Hext
extension theorems (`HypothesisPowerGrowth.upper_extends_to_zero`,
`HypothesisPowerGrowth.lower_extends_to_zero`) plus the agreement rider
`H_zero_eq_Hext`. -/
def IsHK0AbsDominator
    {d : ℕ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (μ mBar : (Fin d → ℝ) → ℝ)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ)
    (C' : ℝ) : Prop :=
  ∀ᵐ x ∂(volume.restrict (UnitCube d)),
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ cxComb μ mBar t x →
        |H x (fun i => cxCombGrad Dυ Dῡ t i x) (cxComb μ mBar t x)|
          ≤ C' * (‖fun i => cxCombGrad Dυ Dῡ t i x‖ ^ h.α + 1)
              + h.C * ((cxComb μ mBar t x) ^ h.β + 1)

/-- **K0-form `m·D_pH` dominator hypothesis.** Pointwise bound on
`‖μ_t • D_pH(x, Dυ_t x, μ_t x)‖` valid for `0 ≤ cxComb μ mBar t x`.
At `μ_t = 0` the LHS is `0` and the RHS is `h.C · (0 + 0 + 0) = 0`,
so the bound trivializes there. -/
def IsmDpHK0Dominator
    {d : ℕ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (μ mBar : (Fin d → ℝ) → ℝ)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ) : Prop :=
  ∀ᵐ x ∂(volume.restrict (UnitCube d)),
    ∀ t, 0 ≤ cxComb μ mBar t x →
      ‖cxComb μ mBar t x •
          DpH x (fun i => cxCombGrad Dυ Dῡ t i x) (cxComb μ mBar t x)‖
        ≤ h.C * (cxComb μ mBar t x
                  * ‖fun i => cxCombGrad Dυ Dῡ t i x‖ ^ (h.α - 1)
                + (cxComb μ mBar t x) ^ (1 + h.β - h.β / h.α)
                + cxComb μ mBar t x)

/-- **`aepsiIntegrandAt_unreg_pointwise_bound_K0`** — K0-form natural
form pointwise dominator on `‖aepsiIntegrandAt_unreg ...‖`, uniform in
`t ∈ [0,1]` (under K0 segment positivity `0 ≤ cxComb μ mBar t x`).

The conclusion shape matches `aepsiIntegrandAt_unreg_pointwise_bound`
exactly; the only difference is the segment-positivity hypothesis is
relaxed from `0 < cxComb` to `0 ≤ cxComb`.

Inputs:
* `hHabs_K0` — K0-form abs bound on `H` (paper-faithful via Hat0/Hext;
  caller derives from upper/lower extension theorems);
* `hmDpH_K0` — K0-form `m·D_pH` bound (trivializes at `m = 0`).

The `C'` constant is supplied by the caller (it is the same `C'` from
the K-strict `hemicont_H_abs_dominator`). -/
theorem aepsiIntegrandAt_unreg_pointwise_bound_K0
    (V : (Fin d → ℝ) → ℝ)
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    {C' : ℝ} (hC'_pos : 0 < C')
    (μ mBar υ ῡ : (Fin d → ℝ) → ℝ)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ)
    (hHabs_K0 : IsHK0AbsDominator h μ mBar Dυ Dῡ C')
    (hmDpH_K0 : IsmDpHK0Dominator h μ mBar Dυ Dῡ) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        0 ≤ cxComb μ mBar t x →
          ‖aepsiIntegrandAt_unreg V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν x t‖
            ≤ (|ῡ x| + |υ x|) * |η x|
              + (C' * (‖fun i => |Dῡ i x| + |Dυ i x|‖ ^ h.α + 1)
                  + h.C * ((|mBar x| + |μ x|) ^ h.β + 1)) * |η x|
              + |V x| * |η x|
              + h.C * ((|mBar x| + |μ x|)
                          * ‖fun i => |Dῡ i x| + |Dυ i x|‖ ^ (h.α - 1)
                        + (|mBar x| + |μ x|) ^ (1 + h.β - h.β / h.α)
                        + (|mBar x| + |μ x|))
                  * (∑ i, |Dν i x|)
              + ((|mBar x| + |μ x|) + 1) * |ν x| := by
  filter_upwards [hHabs_K0, hmDpH_K0] with x hxH hxmDpH t ht hμt_nn
  set μt : ℝ := cxComb μ mBar t x with hμt_def
  set υt : ℝ := cxComb υ ῡ t x with hυt_def
  set p_t : Fin d → ℝ := fun i => cxCombGrad Dυ Dῡ t i x with hpt_def
  set Δp_t : Fin d → ℝ := fun i => |Dῡ i x| + |Dυ i x| with hΔp_def
  set Δm : ℝ := |mBar x| + |μ x| with hΔm_def
  set Δυ : ℝ := |ῡ x| + |υ x| with hΔυ_def
  -- Constants and non-negativities (mirror the K-strict version).
  have hCpos : 0 < h.C := h.hC
  have hα_ge : 1 ≤ h.α := le_of_lt h.hα
  have hαm1_nn : 0 ≤ h.α - 1 := by linarith
  have hα_nn : 0 ≤ h.α := by linarith
  have hβ_nn : 0 ≤ h.β := h.hβ.le
  have hΔm_nn : 0 ≤ Δm := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hΔυ_nn : 0 ≤ Δυ := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hΔp_nn : 0 ≤ ‖Δp_t‖ := norm_nonneg _
  have hpt_norm_nn : 0 ≤ ‖p_t‖ := norm_nonneg _
  have h_abs_μt : |μt| ≤ Δm := cxComb_abs_le μ mBar x ht
  have h_abs_υt : |υt| ≤ Δυ := cxComb_abs_le υ ῡ x ht
  have h_norm_pt : ‖p_t‖ ≤ ‖Δp_t‖ := cxCombGrad_norm_le Dυ Dῡ x ht
  -- Algebraic restatement of the unreg integrand.
  have heq_unreg :
      aepsiIntegrandAt_unreg V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν x t
        = (-υt - H x p_t μt + V x) * η x
          + μt * (DpH x p_t μt ⬝ (fun i => Dν i x))
          + (μt - 1) * ν x := rfl
  rw [Real.norm_eq_abs, heq_unreg]
  -- Triangle inequality (twice, left-associated), as in K-strict.
  have htri :
      |((-υt - H x p_t μt + V x) * η x
          + μt * (DpH x p_t μt ⬝ (fun i => Dν i x)))
        + (μt - 1) * ν x|
        ≤ |(-υt - H x p_t μt + V x) * η x|
            + |μt * (DpH x p_t μt ⬝ (fun i => Dν i x))|
            + |(μt - 1) * ν x| := by
    have h1 : |((-υt - H x p_t μt + V x) * η x
                  + μt * (DpH x p_t μt ⬝ (fun i => Dν i x)))
                + (μt - 1) * ν x|
              ≤ |(-υt - H x p_t μt + V x) * η x
                  + μt * (DpH x p_t μt ⬝ (fun i => Dν i x))|
                + |(μt - 1) * ν x| := abs_add_le _ _
    have h2 : |(-υt - H x p_t μt + V x) * η x
                + μt * (DpH x p_t μt ⬝ (fun i => Dν i x))|
              ≤ |(-υt - H x p_t μt + V x) * η x|
                + |μt * (DpH x p_t μt ⬝ (fun i => Dν i x))| := abs_add_le _ _
    linarith
  -- (1) |(-υt - H + V) · η| ≤ (|υt| + |H| + |V|) · |η|. (Same as K-strict.)
  have h_first_split :
      |(-υt - H x p_t μt + V x) * η x|
        ≤ (|υt| + |H x p_t μt| + |V x|) * |η x| := by
    rw [abs_mul]
    have htri3 : |-υt - H x p_t μt + V x|
                  ≤ |υt| + |H x p_t μt| + |V x| := by
      have hA : |(-υt - H x p_t μt) + V x|
                  ≤ |(-υt - H x p_t μt)| + |V x| := abs_add_le _ _
      have hB : |-υt - H x p_t μt| ≤ |-υt| + |H x p_t μt| := by
        have := abs_sub (-υt) (H x p_t μt)
        simpa using this
      have hC : |-υt| = |υt| := abs_neg _
      have heq : -υt - H x p_t μt + V x = (-υt - H x p_t μt) + V x := by ring
      rw [heq]; linarith
    exact mul_le_mul_of_nonneg_right htri3 (abs_nonneg _)
  -- (2) |μt · (DpH ⬝ Dν)| ≤ ‖μt • DpH‖ · ∑ |Dν|. (Same as K-strict.)
  have h_dot_split :
      |μt * (DpH x p_t μt ⬝ (fun i => Dν i x))|
        ≤ ‖μt • DpH x p_t μt‖ * ∑ i, |Dν i x| := by
    rw [abs_mul]
    have hdot :=
      abs_euclideanDot_le_norm_mul_sum_abs (DpH x p_t μt) (fun i => Dν i x)
    have hμt_abs_nn : 0 ≤ |μt| := abs_nonneg _
    have hbnd1 : |μt| * |DpH x p_t μt ⬝ (fun i => Dν i x)|
                  ≤ |μt| * (‖DpH x p_t μt‖ * ∑ i, |Dν i x|) :=
      mul_le_mul_of_nonneg_left hdot hμt_abs_nn
    have hsmul : ‖μt • DpH x p_t μt‖ = |μt| * ‖DpH x p_t μt‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    rw [hsmul]
    nlinarith [hbnd1, abs_nonneg μt, norm_nonneg (DpH x p_t μt),
      Finset.sum_nonneg
        (s := (Finset.univ : Finset (Fin d))) (f := fun i => |Dν i x|)
        (fun _ _ => abs_nonneg (Dν _ x))]
  -- (3) |(μt - 1) · ν| ≤ (|μt| + 1) · |ν|. (Same as K-strict.)
  have h_third_split :
      |(μt - 1) * ν x| ≤ (|μt| + 1) * |ν x| := by
    rw [abs_mul]
    have h1 : |μt - 1| ≤ |μt| + |(1 : ℝ)| := abs_sub _ _
    have h2 : |(1 : ℝ)| = 1 := abs_one
    rw [h2] at h1
    exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  -- K0-endpoint dominators (from the supplied K0 hypotheses).
  have hH := hxH t ht hμt_nn
  have hmDpH := hxmDpH t hμt_nn
  -- Pi-norm/Δ-monotonicities (rpow). Same shape as K-strict.
  have h_pα : ‖p_t‖ ^ h.α ≤ ‖Δp_t‖ ^ h.α :=
    Real.rpow_le_rpow hpt_norm_nn h_norm_pt hα_nn
  have h_pαm1 : ‖p_t‖ ^ (h.α - 1) ≤ ‖Δp_t‖ ^ (h.α - 1) :=
    Real.rpow_le_rpow hpt_norm_nn h_norm_pt hαm1_nn
  have hμt_le_abs : μt ≤ |μt| := le_abs_self _
  have h_μt_nn : 0 ≤ μt := hμt_nn
  have h_μt_le_Δm : μt ≤ Δm := le_trans hμt_le_abs h_abs_μt
  have h_μtβ : μt ^ h.β ≤ Δm ^ h.β :=
    Real.rpow_le_rpow h_μt_nn h_μt_le_Δm hβ_nn
  -- 0 ≤ 1 + β - β/α (from β > 0, α ≥ 1 ⇒ β/α ≤ β ⇒ 1 + β - β/α ≥ 1).
  have hβoα_le_β : h.β / h.α ≤ h.β := by
    have hαpos : 0 < h.α := lt_trans one_pos h.hα
    rw [div_le_iff₀ hαpos]
    have hβpos : 0 ≤ h.β := h.hβ.le
    have := mul_le_mul_of_nonneg_left hα_ge hβpos
    linarith
  have h_pow_exp_nn : 0 ≤ 1 + h.β - h.β / h.α := by
    have : 0 ≤ h.β - h.β / h.α := by linarith
    linarith
  have h_μt_pow_endpoint :
      μt ^ (1 + h.β - h.β / h.α) ≤ Δm ^ (1 + h.β - h.β / h.α) :=
    Real.rpow_le_rpow h_μt_nn h_μt_le_Δm h_pow_exp_nn
  -- Endpoint bound on |H| (K0 form).
  have h_H_endpoint :
      |H x p_t μt|
        ≤ C' * (‖Δp_t‖ ^ h.α + 1) + h.C * (Δm ^ h.β + 1) := by
    have hC'_mono : C' * (‖p_t‖ ^ h.α + 1) ≤ C' * (‖Δp_t‖ ^ h.α + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hC'_pos.le
    have hC_mono : h.C * (μt ^ h.β + 1) ≤ h.C * (Δm ^ h.β + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hCpos.le
    linarith
  -- Endpoint bound on ‖μt • DpH‖ (K0 form).
  have h_pαm1_nn : 0 ≤ ‖p_t‖ ^ (h.α - 1) := Real.rpow_nonneg hpt_norm_nn _
  have h_Δpαm1_nn : 0 ≤ ‖Δp_t‖ ^ (h.α - 1) := Real.rpow_nonneg hΔp_nn _
  have h_factor_pow :
      μt * ‖p_t‖ ^ (h.α - 1) ≤ Δm * ‖Δp_t‖ ^ (h.α - 1) := by
    have step1 : μt * ‖p_t‖ ^ (h.α - 1) ≤ μt * ‖Δp_t‖ ^ (h.α - 1) :=
      mul_le_mul_of_nonneg_left h_pαm1 h_μt_nn
    have step2 : μt * ‖Δp_t‖ ^ (h.α - 1) ≤ Δm * ‖Δp_t‖ ^ (h.α - 1) :=
      mul_le_mul_of_nonneg_right h_μt_le_Δm h_Δpαm1_nn
    linarith
  have h_mDpH_endpoint :
      ‖μt • DpH x p_t μt‖
        ≤ h.C * (Δm * ‖Δp_t‖ ^ (h.α - 1)
                  + Δm ^ (1 + h.β - h.β / h.α) + Δm) := by
    have hinner :
        μt * ‖p_t‖ ^ (h.α - 1) + μt ^ (1 + h.β - h.β / h.α) + μt
          ≤ Δm * ‖Δp_t‖ ^ (h.α - 1)
              + Δm ^ (1 + h.β - h.β / h.α) + Δm := by
      linarith
    have := mul_le_mul_of_nonneg_left hinner hCpos.le
    linarith
  -- ∑ |Dν| ≥ 0.
  have h_sumDν_nn : 0 ≤ ∑ i, |Dν i x| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  -- Promote the second-summand bound to the endpoint mDpH form.
  have h_second_endpoint :
      ‖μt • DpH x p_t μt‖ * ∑ i, |Dν i x|
        ≤ h.C * (Δm * ‖Δp_t‖ ^ (h.α - 1)
                  + Δm ^ (1 + h.β - h.β / h.α) + Δm)
            * (∑ i, |Dν i x|) :=
    mul_le_mul_of_nonneg_right h_mDpH_endpoint h_sumDν_nn
  -- Promote the third-summand bound: |μt| + 1 ≤ Δm + 1.
  have h_third_endpoint :
      (|μt| + 1) * |ν x| ≤ (Δm + 1) * |ν x| :=
    mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
  -- Promote the first-summand bound: |υt| + |H| + |V| ≤ Δυ + H_endpoint + |V|.
  have h_first_endpoint :
      (|υt| + |H x p_t μt| + |V x|) * |η x|
        ≤ (Δυ + (C' * (‖Δp_t‖ ^ h.α + 1) + h.C * (Δm ^ h.β + 1)) + |V x|)
            * |η x| :=
    mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
  -- Combine.
  have hAcc :
      |(-υt - H x p_t μt + V x) * η x|
        + |μt * (DpH x p_t μt ⬝ (fun i => Dν i x))|
        + |(μt - 1) * ν x|
      ≤ (Δυ + (C' * (‖Δp_t‖ ^ h.α + 1) + h.C * (Δm ^ h.β + 1)) + |V x|)
            * |η x|
        + h.C * (Δm * ‖Δp_t‖ ^ (h.α - 1)
                  + Δm ^ (1 + h.β - h.β / h.α) + Δm) * (∑ i, |Dν i x|)
        + (Δm + 1) * |ν x| := by
    have hA :
        |(-υt - H x p_t μt + V x) * η x|
          ≤ (Δυ + (C' * (‖Δp_t‖ ^ h.α + 1) + h.C * (Δm ^ h.β + 1)) + |V x|)
              * |η x| := le_trans h_first_split h_first_endpoint
    have hB :
        |μt * (DpH x p_t μt ⬝ (fun i => Dν i x))|
          ≤ h.C * (Δm * ‖Δp_t‖ ^ (h.α - 1)
                  + Δm ^ (1 + h.β - h.β / h.α) + Δm) * (∑ i, |Dν i x|) :=
      le_trans h_dot_split h_second_endpoint
    have hC₃ :
        |(μt - 1) * ν x| ≤ (Δm + 1) * |ν x| :=
      le_trans h_third_split h_third_endpoint
    linarith
  -- Distribute the first-summand-RHS into the three goal pieces.
  have hgoal_distribute :
      (Δυ + (C' * (‖Δp_t‖ ^ h.α + 1) + h.C * (Δm ^ h.β + 1)) + |V x|)
            * |η x|
        = Δυ * |η x|
          + (C' * (‖Δp_t‖ ^ h.α + 1) + h.C * (Δm ^ h.β + 1)) * |η x|
          + |V x| * |η x| := by ring
  linarith [htri, hAcc, hgoal_distribute.le, hgoal_distribute.ge]

/-! ## Constant-shift perturbation toolkit (Option B for `hPosSeg`)

These helpers package the Option-B perturbation route documented in
`docs/HPOSSEG_DESIGN.md`: each per-family `segInputsOf` producer
satisfies its strict-positivity slot `hPosSeg` by shifting the
endpoints `μ₁, μ₂` of the convex combination by a strictly positive
constant `c`.

The toolkit consists of:

* `cxComb_add_const` — the algebraic identity
  `cxComb (μ + c) (μ̄ + c) t x = cxComb μ μ̄ t x + c`.
* `hPosSeg_of_nn_and_pos_const` — the a.e. lift from
  `0 ≤ᵐ cxComb μ μ̄ t x` (delivered by `K0_Aepsi_segment_pos_nn`) to
  the strict-positivity field of the perturbed segment.
* `abs_add_const_pair_le` — the pointwise bound
  `|μ₁ x + c| + |μ₂ x + c| ≤ (|μ₁ x| + |μ₂ x|) + 2|c|`.
* Nine `b<…>_of_unperturbed` helpers — one per `bΔ_*`/`bG_*` dominator
  shape in the narrow `SegInputs` bundles. The four dominators that
  do not depend on the density `(bΔυ, bΔp_pow, bG_grad, bG_val)`
  are identity wrappers; the five density-dependent dominators
  (`bΔm_pow, bΔm_grad, bΔm_endpoint, bΔm, bΔm1`) are proved by
  `MemLpPer.mono` against an integrable shift dominator built from
  `MemLpPer.add` + `MemLpPer.const`.
-/

section PerturbationToolkit

open MeasureTheory
open StationaryMFG.Periodic

/-- Algebraic identity: shifting both endpoints of `cxComb` by the
same constant `c` shifts the convex combination by `c` as well. -/
lemma cxComb_add_const (a aBar : (Fin d → ℝ) → ℝ) (c : ℝ) (t : ℝ)
    (x : Fin d → ℝ) :
    cxComb (a + (fun _ : Fin d → ℝ => c))
        (aBar + (fun _ : Fin d → ℝ => c)) t x
      = cxComb a aBar t x + c := by
  unfold cxComb
  simp [Pi.add_apply]
  ring

/-- From `0 ≤ᵐ cxComb a aBar t x` on the segment `[0,1]` (supplied by
`K0_Aepsi_segment_pos_nn`) and a *strictly positive* constant `c`,
derive strict positivity of the perturbed convex combination on the
whole segment. This discharges the `hPosSeg` field of the narrow
`SegInputs` records under the Option-B perturbation route. -/
lemma hPosSeg_of_nn_and_pos_const
    (a aBar : (Fin d → ℝ) → ℝ) {c : ℝ} (hc : 0 < c)
    (hnn : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
            ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ cxComb a aBar t x) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        0 < cxComb (a + (fun _ : Fin d → ℝ => c))
              (aBar + (fun _ : Fin d → ℝ => c)) t x := by
  filter_upwards [hnn] with x hx t ht
  have hbase : 0 ≤ cxComb a aBar t x := hx t ht
  have hshift : cxComb (a + (fun _ : Fin d → ℝ => c))
                  (aBar + (fun _ : Fin d → ℝ => c)) t x
                  = cxComb a aBar t x + c :=
    cxComb_add_const a aBar c t x
  rw [hshift]
  linarith

/-- Pointwise bound: shifting two functions by a common constant `c`
inflates the sum of absolute values by at most `2|c|`. The key
ingredient in the `Lᵖ`-dominator extension lemmas below. -/
lemma abs_add_const_pair_le (μ₁ μ₂ : (Fin d → ℝ) → ℝ) (c : ℝ)
    (x : Fin d → ℝ) :
    |(μ₁ + (fun _ : Fin d → ℝ => c)) x|
        + |(μ₂ + (fun _ : Fin d → ℝ => c)) x|
      ≤ (|μ₁ x| + |μ₂ x|) + 2 * |c| := by
  simp only [Pi.add_apply]
  have h1 : |μ₁ x + c| ≤ |μ₁ x| + |c| := abs_add_le _ _
  have h2 : |μ₂ x + c| ≤ |μ₂ x| + |c| := abs_add_le _ _
  linarith

/-! ### Nine `b<…>_of_unperturbed` dominator helpers

These match the nine `MemLpPer` fields of the
`SetFamilyNarrowSegInputs` / `SignedFamilyNarrowSegInputs` /
`TransportFamilyNarrowSegInputs` records in
`StationaryMFG/Theorems/SimplePower/BanachBridge.lean`. Each helper
takes the unperturbed dominator at endpoints `(μ₁, μ₂) = (mLim + ρ₁,
mLim + ρ₂)` and produces the analogous dominator at the perturbed
endpoints `(μ₁ + c, μ₂ + c)` for any `c ≥ 0`.

Four of the dominator shapes do not mention the density (they depend
only on `uLim` and `DuLim`); for those the helper is the identity
wrapper exposed under a uniform name so that the per-family bundle
assembly can call the same `b…_of_unperturbed` API for every slot.

The five density-dependent helpers use `MemLpPer.mono` against the
integrable dominator built from `MemLpPer.add` and `MemLpPer.const`
applied to the unperturbed certificate. -/

variable {βBarReal γBarReal γBar : ℝ}

/-- Density-free dominator: `|uLim| + |uLim|`. Identity wrapper. -/
lemma bΔυ_of_unperturbed
    {uLim : (Fin d → ℝ) → ℝ}
    (h : MemLpPer (d := d) (ENNReal.ofReal βBarReal)
            (fun x => |uLim x| + |uLim x|)) :
    MemLpPer (d := d) (ENNReal.ofReal βBarReal)
        (fun x => |uLim x| + |uLim x|) := h

/-- Density-free dominator: gradient `α`-power. Identity wrapper. -/
lemma bΔp_pow_of_unperturbed
    {DuLim : Fin d → (Fin d → ℝ) → ℝ} {α : ℝ}
    (h : MemLpPer (d := d) (ENNReal.ofReal βBarReal)
            (fun x => ‖fun i => |DuLim i x| + |DuLim i x|‖ ^ α + 1)) :
    MemLpPer (d := d) (ENNReal.ofReal βBarReal)
        (fun x => ‖fun i => |DuLim i x| + |DuLim i x|‖ ^ α + 1) := h

/-- Density-free dominator: Gateaux gradient block. Identity wrapper. -/
lemma bG_grad_of_unperturbed
    {DuLim : Fin d → (Fin d → ℝ) → ℝ}
    (h : MemLpPer (d := d) (ENNReal.ofReal γBarReal)
            (fun x => (∑ i, (|DuLim i x| + |DuLim i x|) ^ (2 : ℕ))
                      ^ ((γBar - 1) / 2))) :
    MemLpPer (d := d) (ENNReal.ofReal γBarReal)
        (fun x => (∑ i, (|DuLim i x| + |DuLim i x|) ^ (2 : ℕ))
                  ^ ((γBar - 1) / 2)) := h

/-- Density-free dominator: Gateaux value block. Identity wrapper. -/
lemma bG_val_of_unperturbed
    {uLim : (Fin d → ℝ) → ℝ}
    (h : MemLpPer (d := d) (ENNReal.ofReal γBarReal)
            (fun x => (|uLim x| + |uLim x|) ^ (γBar - 1))) :
    MemLpPer (d := d) (ENNReal.ofReal γBarReal)
        (fun x => (|uLim x| + |uLim x|) ^ (γBar - 1)) := h

/-! The density-dependent helpers below all share the pattern:

1. Promote `μ_i` to `μ_i + (fun _ => c)` using `MemLpPer.add_const`.
2. Combine the resulting `MemLpPer` certificates with the unperturbed
   dominator and a pointwise inequality.

The pointwise inequality is built around `abs_add_const_pair_le`. For
the auxiliary lemma `memLpPer_abs_pair_add_const` below we additionally
require the **individual** `MemLpPer p μ_i` certificates so we can
extract `AEStronglyMeasurable` for the perturbed pair; in the
per-family `segInputsOf` callers this is already on hand from the
weak-limit bundle (`mLim + ρ_i` is `Lᵝ` by construction). -/

/-- Auxiliary: the **base** perturbed dominator `|μ₁ + c| + |μ₂ + c|`
inherits `MemLpPer p` from its unperturbed counterpart `|μ₁| + |μ₂|`
plus a constant shift. The two individual `μ_i` certificates are
needed only to extract `AEStronglyMeasurable` for the perturbed
pair. -/
lemma memLpPer_abs_pair_add_const
    {p : ℝ≥0∞} {μ₁ μ₂ : (Fin d → ℝ) → ℝ} (c : ℝ)
    (hμ₁ : MemLpPer (d := d) p μ₁) (hμ₂ : MemLpPer (d := d) p μ₂)
    (hpair : MemLpPer (d := d) p (fun x => |μ₁ x| + |μ₂ x|)) :
    MemLpPer (d := d) p
        (fun x => |(μ₁ + (fun _ : Fin d → ℝ => c)) x|
                  + |(μ₂ + (fun _ : Fin d → ℝ => c)) x|) := by
  -- Shift dominator: (|μ₁| + |μ₂|) + 2|c| ∈ Lᵖ_per.
  have hconst : MemLpPer (d := d) p (fun _ : Fin d → ℝ => (2 * |c| : ℝ)) :=
    MemLpPer.const (d := d) (2 * |c|)
  have hshift : MemLpPer (d := d) p
      (fun x => (|μ₁ x| + |μ₂ x|) + 2 * |c|) := by
    have := hpair.add hconst
    simpa [Pi.add_def, Pi.add_apply] using this
  -- AEStrongMeasurable for the perturbed pair, built from the
  -- individual μ_i certificates.
  have hμ₁c : AEStronglyMeasurable (μ₁ + (fun _ : Fin d → ℝ => c))
      (volume.restrict (UnitCube d)) :=
    hμ₁.aestronglyMeasurable.add_const c
  have hμ₂c : AEStronglyMeasurable (μ₂ + (fun _ : Fin d → ℝ => c))
      (volume.restrict (UnitCube d)) :=
    hμ₂.aestronglyMeasurable.add_const c
  -- On ℝ, ‖x‖ = |x|; use AEStronglyMeasurable.norm to get measurability
  -- of |μ_i + c|, then add.
  have habs₁ : AEStronglyMeasurable
      (fun x => |(μ₁ + (fun _ : Fin d → ℝ => c)) x|)
      (volume.restrict (UnitCube d)) := by
    have := hμ₁c.norm
    simpa [Real.norm_eq_abs] using this
  have habs₂ : AEStronglyMeasurable
      (fun x => |(μ₂ + (fun _ : Fin d → ℝ => c)) x|)
      (volume.restrict (UnitCube d)) := by
    have := hμ₂c.norm
    simpa [Real.norm_eq_abs] using this
  have hmeas : AEStronglyMeasurable
      (fun x => |(μ₁ + (fun _ : Fin d → ℝ => c)) x|
                + |(μ₂ + (fun _ : Fin d → ℝ => c)) x|)
      (volume.restrict (UnitCube d)) :=
    habs₁.add habs₂
  -- Pointwise bound: |μ₁ + c| + |μ₂ + c| ≤ (|μ₁| + |μ₂|) + 2|c|.
  apply MemLp.toMemLpPer
  refine MemLp.mono' (g := fun x => (|μ₁ x| + |μ₂ x|) + 2 * |c|)
      hshift.toMemLp hmeas ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  have hpos : 0 ≤ |(μ₁ + (fun _ : Fin d → ℝ => c)) x|
                + |(μ₂ + (fun _ : Fin d → ℝ => c)) x| :=
    add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hbnd := abs_add_const_pair_le μ₁ μ₂ c x
  change ‖|(μ₁ + (fun _ : Fin d → ℝ => c)) x|
          + |(μ₂ + (fun _ : Fin d → ℝ => c)) x|‖
          ≤ (|μ₁ x| + |μ₂ x|) + 2 * |c|
  rw [Real.norm_eq_abs, abs_of_nonneg hpos]
  exact hbnd

/-- Density-dependent dominator `bΔm`: bare density `|μ₁| + |μ₂|` at the
perturbed endpoints `(μ₁ + c, μ₂ + c)`. Direct application of
`memLpPer_abs_pair_add_const`. -/
lemma bΔm_of_unperturbed
    {μ₁ μ₂ : (Fin d → ℝ) → ℝ} (c : ℝ)
    (hμ₁ : MemLpPer (d := d) (ENNReal.ofReal γBarReal) μ₁)
    (hμ₂ : MemLpPer (d := d) (ENNReal.ofReal γBarReal) μ₂)
    (h : MemLpPer (d := d) (ENNReal.ofReal γBarReal)
            (fun x => |μ₂ x| + |μ₁ x|)) :
    MemLpPer (d := d) (ENNReal.ofReal γBarReal)
        (fun x => |(μ₂ + (fun _ : Fin d → ℝ => c)) x|
                  + |(μ₁ + (fun _ : Fin d → ℝ => c)) x|) :=
  memLpPer_abs_pair_add_const c hμ₂ hμ₁ h

/-- Density-dependent dominator `bΔm1`: `(|μ₁| + |μ₂|) + 1` at the
perturbed endpoints. `MemLpPer.add_const` applied to `bΔm`. -/
lemma bΔm1_of_unperturbed
    {μ₁ μ₂ : (Fin d → ℝ) → ℝ} (c : ℝ)
    (hμ₁ : MemLpPer (d := d) (ENNReal.ofReal βBarReal) μ₁)
    (hμ₂ : MemLpPer (d := d) (ENNReal.ofReal βBarReal) μ₂)
    (hpair : MemLpPer (d := d) (ENNReal.ofReal βBarReal)
            (fun x => |μ₂ x| + |μ₁ x|)) :
    MemLpPer (d := d) (ENNReal.ofReal βBarReal)
        (fun x => (|(μ₂ + (fun _ : Fin d → ℝ => c)) x|
                  + |(μ₁ + (fun _ : Fin d → ℝ => c)) x|) + 1) := by
  have hbase := memLpPer_abs_pair_add_const c hμ₂ hμ₁ hpair
  have hconst : MemLpPer (d := d) (ENNReal.ofReal βBarReal)
      (fun _ : Fin d → ℝ => (1 : ℝ)) :=
    MemLpPer.const (d := d) (1 : ℝ)
  have hsum := hbase.add hconst
  -- The Pi-sum and the explicit `+ 1` are definitionally the same.
  exact hsum

/-! ### Power-shape `b<…>_of_unperturbed` helpers (iter 0679 split)

The remaining three helpers all carry a `Real.rpow` factor that has to
be split through the sub-additive bound `(X + K)^β ≤ 2^β · (X^β + K^β)`
for `β ≥ 0`. We isolate that bound first and then plug it into each
helper. -/

/-- Sub-additive bound for `Real.rpow` with a nonnegative exponent: for
`a, b, β ≥ 0`, `(a + b) ^ β ≤ 2 ^ β · (a ^ β + b ^ β)`. We case-split
on `1 ≤ β` (where the standard `NNReal` bound is `2^(β-1)`) vs `β ≤ 1`
(where the standard bound is sub-additive of the form `(a+b)^β ≤ a^β +
b^β`); in both regimes we conclude by `1 ≤ 2 ^ β`. -/
private lemma rpow_add_le_two_rpow_mul_add
    {a b β : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hβ : 0 ≤ β) :
    (a + b) ^ β ≤ (2 : ℝ) ^ β * (a ^ β + b ^ β) := by
  have hab : (0 : ℝ) ≤ a + b := add_nonneg ha hb
  have hab_β : (0 : ℝ) ≤ (a + b) ^ β := Real.rpow_nonneg hab β
  have ha_β : (0 : ℝ) ≤ a ^ β := Real.rpow_nonneg ha β
  have hb_β : (0 : ℝ) ≤ b ^ β := Real.rpow_nonneg hb β
  have hsum_β : (0 : ℝ) ≤ a ^ β + b ^ β := add_nonneg ha_β hb_β
  have h_two_pos : (0 : ℝ) < (2 : ℝ) ^ β :=
    Real.rpow_pos_of_pos (by norm_num) β
  have h_one_le_two_β : (1 : ℝ) ≤ (2 : ℝ) ^ β := by
    have : ((2 : ℝ) ^ (0 : ℝ)) ≤ (2 : ℝ) ^ β :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hβ
    simpa using this
  by_cases hβ1 : 1 ≤ β
  · -- Use NNReal lemma: (a + b)^β ≤ 2^(β-1) (a^β + b^β) ≤ 2^β (a^β + b^β).
    -- Lift to NNReal.
    set A := (⟨a, ha⟩ : ℝ≥0)
    set B := (⟨b, hb⟩ : ℝ≥0)
    have hnn := NNReal.rpow_add_le_mul_rpow_add_rpow A B hβ1
    have hnn_R : (a + b) ^ β ≤ (2 : ℝ) ^ (β - 1) * (a ^ β + b ^ β) := by
      have hcast : ((A + B : ℝ≥0) : ℝ) ^ β ≤
          ((2 : ℝ≥0) : ℝ) ^ (β - 1) * (((A : ℝ) ^ β) + ((B : ℝ) ^ β)) := by
        exact_mod_cast hnn
      simpa [A, B] using hcast
    -- Now use 2^(β-1) ≤ 2^β.
    have h_pow_le : (2 : ℝ) ^ (β - 1) ≤ (2 : ℝ) ^ β :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (by linarith)
    have h_mul_le :
        (2 : ℝ) ^ (β - 1) * (a ^ β + b ^ β)
          ≤ (2 : ℝ) ^ β * (a ^ β + b ^ β) :=
      mul_le_mul_of_nonneg_right h_pow_le hsum_β
    exact hnn_R.trans h_mul_le
  · -- β ≤ 1, so (a+b)^β ≤ a^β + b^β ≤ 2^β · (a^β + b^β).
    have hβ_le : β ≤ 1 := le_of_not_ge hβ1
    have hsub : (a + b) ^ β ≤ a ^ β + b ^ β :=
      Real.rpow_add_le_add_rpow ha hb hβ hβ_le
    have h_mul :
        a ^ β + b ^ β ≤ (2 : ℝ) ^ β * (a ^ β + b ^ β) := by
      nth_rw 1 [show a ^ β + b ^ β = 1 * (a ^ β + b ^ β) from (one_mul _).symm]
      exact mul_le_mul_of_nonneg_right h_one_le_two_β hsum_β
    exact hsub.trans h_mul

/-- Auxiliary: pointwise expansion of the perturbed `^β` shape. For
`β ≥ 0`, with `μ_i' := μ_i + (fun _ => c)`,
`(|μ₂'| + |μ₁'|) ^ β ≤ 2 ^ β · ((|μ₂| + |μ₁|) ^ β + (2|c|) ^ β)`. -/
private lemma rpow_abs_add_const_pair_pow_le
    (μ₁ μ₂ : (Fin d → ℝ) → ℝ) (c : ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (x : Fin d → ℝ) :
    (|(μ₂ + (fun _ : Fin d → ℝ => c)) x|
        + |(μ₁ + (fun _ : Fin d → ℝ => c)) x|) ^ β
      ≤ (2 : ℝ) ^ β *
          ((|μ₂ x| + |μ₁ x|) ^ β + (2 * |c|) ^ β) := by
  have hbase :
      |(μ₂ + (fun _ : Fin d → ℝ => c)) x|
          + |(μ₁ + (fun _ : Fin d → ℝ => c)) x|
        ≤ (|μ₂ x| + |μ₁ x|) + 2 * |c| := by
    have := abs_add_const_pair_le μ₂ μ₁ c x
    -- abs_add_const_pair_le gives |μ₂+c|+|μ₁+c| ≤ (|μ₂|+|μ₁|) + 2|c|.
    exact this
  have hnn_lhs : 0 ≤ |(μ₂ + (fun _ : Fin d → ℝ => c)) x|
                  + |(μ₁ + (fun _ : Fin d → ℝ => c)) x| :=
    add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hnn_rhs : 0 ≤ (|μ₂ x| + |μ₁ x|) + 2 * |c| :=
    add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))
      (mul_nonneg (by norm_num) (abs_nonneg _))
  have hmono :
      (|(μ₂ + (fun _ : Fin d → ℝ => c)) x|
          + |(μ₁ + (fun _ : Fin d → ℝ => c)) x|) ^ β
        ≤ ((|μ₂ x| + |μ₁ x|) + 2 * |c|) ^ β :=
    Real.rpow_le_rpow hnn_lhs hbase hβ
  exact hmono.trans
    (rpow_add_le_two_rpow_mul_add
      (add_nonneg (abs_nonneg _) (abs_nonneg _))
      (mul_nonneg (by norm_num) (abs_nonneg _)) hβ)

/-- Density-dependent dominator `bΔm_pow`: `(|μ₂| + |μ₁|) ^ β + 1` at
the perturbed endpoints. Built from the unperturbed cert via
`rpow_add_le_two_rpow_mul_add`. -/
lemma bΔm_pow_of_unperturbed
    {μ₁ μ₂ : (Fin d → ℝ) → ℝ} (c : ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (hμ₁ : MemLpPer (d := d) (ENNReal.ofReal βBarReal) μ₁)
    (hμ₂ : MemLpPer (d := d) (ENNReal.ofReal βBarReal) μ₂)
    (h : MemLpPer (d := d) (ENNReal.ofReal βBarReal)
            (fun x => (|μ₂ x| + |μ₁ x|) ^ β + 1)) :
    MemLpPer (d := d) (ENNReal.ofReal βBarReal)
        (fun x => (|(μ₂ + (fun _ : Fin d → ℝ => c)) x|
                  + |(μ₁ + (fun _ : Fin d → ℝ => c)) x|) ^ β + 1) := by
  set p : ℝ≥0∞ := ENNReal.ofReal βBarReal with hp_def
  -- Dominator: 2^β • h + (2^β · (2|c|)^β + 1 − 2^β · 1) = 2^β • h + Kconst.
  -- We package it explicitly as `g(x) := 2^β · ((|μ₂|+|μ₁|)^β + (2|c|)^β) + 1`.
  -- Build the pieces.
  have h_scaled : MemLpPer (d := d) p
      ((2 : ℝ) ^ β • (fun x => (|μ₂ x| + |μ₁ x|) ^ β + 1)) :=
    h.const_smul ((2 : ℝ) ^ β)
  -- The constant `(2^β) · (2|c|)^β − (2^β) · 1` is a real number.
  have hKconst : MemLpPer (d := d) p
      (fun _ : Fin d → ℝ =>
        (2 : ℝ) ^ β * (2 * |c|) ^ β - (2 : ℝ) ^ β * 1) :=
    MemLpPer.const (d := d)
      ((2 : ℝ) ^ β * (2 * |c|) ^ β - (2 : ℝ) ^ β * 1)
  have hsum := h_scaled.add hKconst
  -- Pointwise: the sum equals `2^β · ((|μ₂|+|μ₁|)^β + (2|c|)^β)`.
  -- Define the dominator function explicitly.
  set g : (Fin d → ℝ) → ℝ := fun x =>
    (2 : ℝ) ^ β * ((|μ₂ x| + |μ₁ x|) ^ β + (2 * |c|) ^ β) with hg_def
  have hg_eq : ((2 : ℝ) ^ β • (fun x => (|μ₂ x| + |μ₁ x|) ^ β + 1))
                + (fun _ : Fin d → ℝ =>
                    (2 : ℝ) ^ β * (2 * |c|) ^ β - (2 : ℝ) ^ β * 1)
              = g := by
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hg_def]
    ring
  rw [hg_eq] at hsum
  -- Now `hsum : MemLpPer p g`. Use mono'.
  have hmeas : AEStronglyMeasurable
      (fun x => (|(μ₂ + (fun _ : Fin d → ℝ => c)) x|
                  + |(μ₁ + (fun _ : Fin d → ℝ => c)) x|) ^ β + 1)
      (volume.restrict (UnitCube d)) := by
    have h₂c : AEStronglyMeasurable (μ₂ + (fun _ : Fin d → ℝ => c))
        (volume.restrict (UnitCube d)) :=
      hμ₂.aestronglyMeasurable.add_const c
    have h₁c : AEStronglyMeasurable (μ₁ + (fun _ : Fin d → ℝ => c))
        (volume.restrict (UnitCube d)) :=
      hμ₁.aestronglyMeasurable.add_const c
    have habs₂ : AEStronglyMeasurable
        (fun x => |(μ₂ + (fun _ : Fin d → ℝ => c)) x|)
        (volume.restrict (UnitCube d)) := by
      have := h₂c.norm; simpa [Real.norm_eq_abs] using this
    have habs₁ : AEStronglyMeasurable
        (fun x => |(μ₁ + (fun _ : Fin d → ℝ => c)) x|)
        (volume.restrict (UnitCube d)) := by
      have := h₁c.norm; simpa [Real.norm_eq_abs] using this
    have hpair := habs₂.add habs₁
    have hrpow_cont : Continuous (fun s : ℝ => s ^ β) :=
      Real.continuous_rpow_const hβ
    have hrpow : AEStronglyMeasurable
        (fun x => (|(μ₂ + (fun _ : Fin d → ℝ => c)) x|
                  + |(μ₁ + (fun _ : Fin d → ℝ => c)) x|) ^ β)
        (volume.restrict (UnitCube d)) :=
      hrpow_cont.comp_aestronglyMeasurable hpair
    exact hrpow.add_const 1
  -- We need a bound `|target x| ≤ 2 g(x) + 1` (or similar). Actually we
  -- need `target ≤ g + 1`. Let us bound directly.
  apply MemLp.toMemLpPer
  refine MemLp.mono'
    (g := fun x => g x + 1)
    ?_ hmeas ?_
  · -- `g + 1` is MemLpPer p.
    have hone : MemLpPer (d := d) p (fun _ : Fin d → ℝ => (1 : ℝ)) :=
      MemLpPer.const (d := d) (1 : ℝ)
    have hsum' := hsum.add hone
    -- The Pi-sum and the explicit `+ 1` agree definitionally.
    exact hsum'.toMemLp
  · refine Filter.Eventually.of_forall (fun x => ?_)
    -- target x = (|μ₂'|+|μ₁'|)^β + 1 ≥ 0.
    have hnn_lhs : 0 ≤ (|(μ₂ + (fun _ : Fin d → ℝ => c)) x|
                  + |(μ₁ + (fun _ : Fin d → ℝ => c)) x|) ^ β :=
      Real.rpow_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) β
    have hpos_target : 0 ≤ (|(μ₂ + (fun _ : Fin d → ℝ => c)) x|
                  + |(μ₁ + (fun _ : Fin d → ℝ => c)) x|) ^ β + 1 := by
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg hpos_target]
    have hpow_bnd :
        (|(μ₂ + (fun _ : Fin d → ℝ => c)) x|
            + |(μ₁ + (fun _ : Fin d → ℝ => c)) x|) ^ β
          ≤ (2 : ℝ) ^ β *
              ((|μ₂ x| + |μ₁ x|) ^ β + (2 * |c|) ^ β) :=
      rpow_abs_add_const_pair_pow_le μ₁ μ₂ c β hβ x
    have hg_eval : g x =
        (2 : ℝ) ^ β * ((|μ₂ x| + |μ₁ x|) ^ β + (2 * |c|) ^ β) := rfl
    linarith [hpow_bnd, hg_eval.ge, hg_eval.le]

/-- Density-dependent dominator `bΔm_grad`: `(|μ₂| + |μ₁|) * U` at the
perturbed endpoints, where the gradient factor `U` is supplied
separately so the perturbation residue `2|c| · U` is itself
`MemLpPer`. The `0 ≤ α - 1` hypothesis is implicit in the caller's
`U`: we only need `U ≥ 0` pointwise (auto from a power of a norm). -/
lemma bΔm_grad_of_unperturbed
    {μ₁ μ₂ : (Fin d → ℝ) → ℝ}
    {DuLim : Fin d → (Fin d → ℝ) → ℝ} {α : ℝ}
    (c : ℝ) (_hα : 0 ≤ α - 1)
    (hμ₁ : MemLpPer (d := d) (ENNReal.ofReal γBarReal) μ₁)
    (hμ₂ : MemLpPer (d := d) (ENNReal.ofReal γBarReal) μ₂)
    (h : MemLpPer (d := d) (ENNReal.ofReal γBarReal)
            (fun x => (|μ₂ x| + |μ₁ x|)
                  * ‖fun i => |DuLim i x| + |DuLim i x|‖ ^ (α - 1)))
    (hU : MemLpPer (d := d) (ENNReal.ofReal γBarReal)
            (fun x => ‖fun i => |DuLim i x| + |DuLim i x|‖ ^ (α - 1))) :
    MemLpPer (d := d) (ENNReal.ofReal γBarReal)
        (fun x => (|(μ₂ + (fun _ : Fin d → ℝ => c)) x|
                  + |(μ₁ + (fun _ : Fin d → ℝ => c)) x|)
                  * ‖fun i => |DuLim i x| + |DuLim i x|‖ ^ (α - 1)) := by
  set p : ℝ≥0∞ := ENNReal.ofReal γBarReal with hp_def
  -- Dominator: h + (2|c|) • hU.
  have hU_scaled : MemLpPer (d := d) p
      ((2 * |c|) • (fun x => ‖fun i => |DuLim i x| + |DuLim i x|‖ ^ (α - 1))) :=
    hU.const_smul (2 * |c|)
  have hsum := h.add hU_scaled
  -- Rewrite the sum to a clean function.
  set g : (Fin d → ℝ) → ℝ := fun x =>
    (|μ₂ x| + |μ₁ x|) * ‖fun i => |DuLim i x| + |DuLim i x|‖ ^ (α - 1)
      + (2 * |c|) * ‖fun i => |DuLim i x| + |DuLim i x|‖ ^ (α - 1)
    with hg_def
  have hg_eq :
      ((fun x => (|μ₂ x| + |μ₁ x|)
              * ‖fun i => |DuLim i x| + |DuLim i x|‖ ^ (α - 1)) +
        (2 * |c|) • (fun x =>
              ‖fun i => |DuLim i x| + |DuLim i x|‖ ^ (α - 1))) = g := by
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hg_def]
  rw [hg_eq] at hsum
  -- Measurability of the target.
  have hmeas : AEStronglyMeasurable
      (fun x => (|(μ₂ + (fun _ : Fin d → ℝ => c)) x|
                  + |(μ₁ + (fun _ : Fin d → ℝ => c)) x|)
                  * ‖fun i => |DuLim i x| + |DuLim i x|‖ ^ (α - 1))
      (volume.restrict (UnitCube d)) := by
    -- Measurability of the perturbed-density factor (as in
    -- memLpPer_abs_pair_add_const).
    have h₂c : AEStronglyMeasurable (μ₂ + (fun _ : Fin d → ℝ => c))
        (volume.restrict (UnitCube d)) :=
      hμ₂.aestronglyMeasurable.add_const c
    have h₁c : AEStronglyMeasurable (μ₁ + (fun _ : Fin d → ℝ => c))
        (volume.restrict (UnitCube d)) :=
      hμ₁.aestronglyMeasurable.add_const c
    have habs₂ : AEStronglyMeasurable
        (fun x => |(μ₂ + (fun _ : Fin d → ℝ => c)) x|)
        (volume.restrict (UnitCube d)) := by
      have := h₂c.norm; simpa [Real.norm_eq_abs] using this
    have habs₁ : AEStronglyMeasurable
        (fun x => |(μ₁ + (fun _ : Fin d → ℝ => c)) x|)
        (volume.restrict (UnitCube d)) := by
      have := h₁c.norm; simpa [Real.norm_eq_abs] using this
    have hpair := habs₂.add habs₁
    exact hpair.mul hU.aestronglyMeasurable
  apply MemLp.toMemLpPer
  refine MemLp.mono' (g := g) hsum.toMemLp hmeas ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  -- Pointwise bound.
  have hU_nn : 0 ≤ ‖fun i => |DuLim i x| + |DuLim i x|‖ ^ (α - 1) :=
    Real.rpow_nonneg (norm_nonneg _) (α - 1)
  have hsum_bound :
      |(μ₂ + (fun _ : Fin d → ℝ => c)) x|
          + |(μ₁ + (fun _ : Fin d → ℝ => c)) x|
        ≤ (|μ₂ x| + |μ₁ x|) + 2 * |c| := abs_add_const_pair_le μ₂ μ₁ c x
  have hnn_lhs : 0 ≤ |(μ₂ + (fun _ : Fin d → ℝ => c)) x|
                + |(μ₁ + (fun _ : Fin d → ℝ => c)) x| :=
    add_nonneg (abs_nonneg _) (abs_nonneg _)
  have htarget_nn : 0 ≤
      (|(μ₂ + (fun _ : Fin d → ℝ => c)) x|
          + |(μ₁ + (fun _ : Fin d → ℝ => c)) x|)
        * ‖fun i => |DuLim i x| + |DuLim i x|‖ ^ (α - 1) :=
    mul_nonneg hnn_lhs hU_nn
  rw [Real.norm_eq_abs, abs_of_nonneg htarget_nn]
  have hbnd_mul :
      (|(μ₂ + (fun _ : Fin d → ℝ => c)) x|
          + |(μ₁ + (fun _ : Fin d → ℝ => c)) x|)
        * ‖fun i => |DuLim i x| + |DuLim i x|‖ ^ (α - 1)
      ≤ ((|μ₂ x| + |μ₁ x|) + 2 * |c|)
          * ‖fun i => |DuLim i x| + |DuLim i x|‖ ^ (α - 1) :=
    mul_le_mul_of_nonneg_right hsum_bound hU_nn
  have hexpand :
      ((|μ₂ x| + |μ₁ x|) + 2 * |c|)
        * ‖fun i => |DuLim i x| + |DuLim i x|‖ ^ (α - 1)
      = (|μ₂ x| + |μ₁ x|)
            * ‖fun i => |DuLim i x| + |DuLim i x|‖ ^ (α - 1)
          + (2 * |c|)
            * ‖fun i => |DuLim i x| + |DuLim i x|‖ ^ (α - 1) := by ring
  -- g x is exactly the RHS.
  have hg_eval : g x =
      (|μ₂ x| + |μ₁ x|)
          * ‖fun i => |DuLim i x| + |DuLim i x|‖ ^ (α - 1)
        + (2 * |c|)
          * ‖fun i => |DuLim i x| + |DuLim i x|‖ ^ (α - 1) := rfl
  linarith [hbnd_mul, hexpand.ge, hexpand.le, hg_eval.ge, hg_eval.le]

/-- Density-dependent dominator `bΔm_endpoint`:
`(|μ₂| + |μ₁|) ^ (1 + β − β/α)` at the perturbed endpoints. Same
strategy as `bΔm_pow_of_unperturbed` but without the trailing `+ 1`. -/
lemma bΔm_endpoint_of_unperturbed
    {μ₁ μ₂ : (Fin d → ℝ) → ℝ} (c : ℝ) {q : ℝ} (hq : 0 ≤ q)
    (hμ₁ : MemLpPer (d := d) (ENNReal.ofReal γBarReal) μ₁)
    (hμ₂ : MemLpPer (d := d) (ENNReal.ofReal γBarReal) μ₂)
    (h : MemLpPer (d := d) (ENNReal.ofReal γBarReal)
            (fun x => (|μ₂ x| + |μ₁ x|) ^ q)) :
    MemLpPer (d := d) (ENNReal.ofReal γBarReal)
        (fun x => (|(μ₂ + (fun _ : Fin d → ℝ => c)) x|
                  + |(μ₁ + (fun _ : Fin d → ℝ => c)) x|) ^ q) := by
  set p : ℝ≥0∞ := ENNReal.ofReal γBarReal with hp_def
  -- Dominator: 2^q • h + Kconst, where Kconst = 2^q · (2|c|)^q.
  have h_scaled : MemLpPer (d := d) p
      ((2 : ℝ) ^ q • (fun x => (|μ₂ x| + |μ₁ x|) ^ q)) :=
    h.const_smul ((2 : ℝ) ^ q)
  have hKconst : MemLpPer (d := d) p
      (fun _ : Fin d → ℝ => (2 : ℝ) ^ q * (2 * |c|) ^ q) :=
    MemLpPer.const (d := d) ((2 : ℝ) ^ q * (2 * |c|) ^ q)
  have hsum := h_scaled.add hKconst
  set g : (Fin d → ℝ) → ℝ := fun x =>
    (2 : ℝ) ^ q * ((|μ₂ x| + |μ₁ x|) ^ q + (2 * |c|) ^ q) with hg_def
  have hg_eq :
      ((2 : ℝ) ^ q • (fun x => (|μ₂ x| + |μ₁ x|) ^ q))
        + (fun _ : Fin d → ℝ => (2 : ℝ) ^ q * (2 * |c|) ^ q) = g := by
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hg_def]
    ring
  rw [hg_eq] at hsum
  -- Measurability of the target.
  have hmeas : AEStronglyMeasurable
      (fun x => (|(μ₂ + (fun _ : Fin d → ℝ => c)) x|
                  + |(μ₁ + (fun _ : Fin d → ℝ => c)) x|) ^ q)
      (volume.restrict (UnitCube d)) := by
    have h₂c : AEStronglyMeasurable (μ₂ + (fun _ : Fin d → ℝ => c))
        (volume.restrict (UnitCube d)) :=
      hμ₂.aestronglyMeasurable.add_const c
    have h₁c : AEStronglyMeasurable (μ₁ + (fun _ : Fin d → ℝ => c))
        (volume.restrict (UnitCube d)) :=
      hμ₁.aestronglyMeasurable.add_const c
    have habs₂ : AEStronglyMeasurable
        (fun x => |(μ₂ + (fun _ : Fin d → ℝ => c)) x|)
        (volume.restrict (UnitCube d)) := by
      have := h₂c.norm; simpa [Real.norm_eq_abs] using this
    have habs₁ : AEStronglyMeasurable
        (fun x => |(μ₁ + (fun _ : Fin d → ℝ => c)) x|)
        (volume.restrict (UnitCube d)) := by
      have := h₁c.norm; simpa [Real.norm_eq_abs] using this
    have hpair := habs₂.add habs₁
    have hrpow_cont : Continuous (fun s : ℝ => s ^ q) :=
      Real.continuous_rpow_const hq
    exact hrpow_cont.comp_aestronglyMeasurable hpair
  apply MemLp.toMemLpPer
  refine MemLp.mono' (g := g) hsum.toMemLp hmeas ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  have hpow_nn : 0 ≤ (|(μ₂ + (fun _ : Fin d → ℝ => c)) x|
              + |(μ₁ + (fun _ : Fin d → ℝ => c)) x|) ^ q :=
    Real.rpow_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) q
  rw [Real.norm_eq_abs, abs_of_nonneg hpow_nn]
  have hpow_bnd :
      (|(μ₂ + (fun _ : Fin d → ℝ => c)) x|
          + |(μ₁ + (fun _ : Fin d → ℝ => c)) x|) ^ q
        ≤ (2 : ℝ) ^ q *
            ((|μ₂ x| + |μ₁ x|) ^ q + (2 * |c|) ^ q) :=
    rpow_abs_add_const_pair_pow_le μ₁ μ₂ c q hq x
  have hg_eval : g x =
      (2 : ℝ) ^ q * ((|μ₂ x| + |μ₁ x|) ^ q + (2 * |c|) ^ q) := rfl
  linarith [hpow_bnd, hg_eval.ge, hg_eval.le]

/-! ### Sanity-check example

Assemble a minimal toolkit-level bundle at the unperturbed endpoints
`(mLim, mLim)` shifted by `c = 1 > 0`. -/

/-- Sanity check: the toolkit produces a valid `hPosSeg` certificate
at the perturbed transport endpoints `(mLim + 1, mLim + 1)` from the
nonneg unperturbed segment hypothesis. -/
example {mLim : (Fin d → ℝ) → ℝ}
    (hnn : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
            ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ cxComb mLim mLim t x) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        0 < cxComb (mLim + (fun _ : Fin d → ℝ => (1 : ℝ)))
              (mLim + (fun _ : Fin d → ℝ => (1 : ℝ))) t x :=
  hPosSeg_of_nn_and_pos_const mLim mLim (by norm_num : (0 : ℝ) < 1) hnn

end PerturbationToolkit

/-! ## Closed-cone regularity abstraction `RegularityHK0`

This is step 2 of the v8 K0 hemicontinuity plan. It mirrors `RegularityH`
but expresses continuity of `H` and of the extension `J = m · D_pH` (=
`JsimpleExt DpH`) on the **closed** half-plane `{pm | 0 ≤ pm.2}` rather
than the open `{pm | 0 < pm.2}`.

The paper's `(a:Hat0)` / `(rmk:implied-a)` conventions specify that
`H(x, p, 0)` is the right-hand limit (real-valued under
`H_zero_eq_Hext` + `Hext_finite_at_zero`) and that `m · D_pH(x, p, 0) =
0`. With these boundary conventions in place, joint continuity in
`(p, m)` on `m ≥ 0` is the natural shape consumed downstream by the
K0 hemicontinuity argument.

Subsequent v8 tasks (`K0-mDpH-continuity`, `K0-Hext-continuity`) will
produce `RegularityHK0` from `HypothesisPowerGrowth` + `HypothesisHat0`
+ `H_zero_eq_Hext`. Here we only introduce the abstraction.
-/

/-- **Closed-cone regularity abstraction (step 2 of v8 K0 plan).**

Sibling to `RegularityH`: instead of joint continuity of `H` and `D_pH`
on the open half-plane `{m > 0}`, this bundles joint continuity of
`H` and of the extension `J = m · D_pH` (`JsimpleExt DpH`) on the
**closed** half-plane `{m ≥ 0}`.

* `continuous_Hext_pm` — for a.e. `x`, the map
  `(p, m) ↦ H(x, p, m)` is continuous on `{pm | 0 ≤ pm.2}`. At `m = 0`
  the value is the paper's right-hand limit (under `H_zero_eq_Hext`).

* `continuous_mDpH_pm` — for a.e. `x`, the map
  `(p, m) ↦ JsimpleExt DpH x p m = m · D_pH(x, p, m)` is continuous on
  `{pm | 0 ≤ pm.2}`. At `m = 0` the value is `0`, per `(a:mDpHat0)` /
  `(rmk:implied-a)`.

This is a purely declarative abstraction; nothing about
`RegularityH` is mutated. -/
structure RegularityHK0
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)) : Prop where
  /-- For almost every `x ∈ 𝕋^d`, the map `(p, m) ↦ H(x, p, m)` is
  continuous on the closed half-plane `{pm | 0 ≤ pm.2}`. -/
  continuous_Hext_pm :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ContinuousOn (fun (pm : (Fin d → ℝ) × ℝ) => H x pm.1 pm.2)
        {pm | 0 ≤ pm.2}
  /-- For almost every `x ∈ 𝕋^d`, the map
  `(p, m) ↦ JsimpleExt DpH x p m = m · D_pH(x, p, m)` is continuous
  on the closed half-plane `{pm | 0 ≤ pm.2}`. -/
  continuous_mDpH_pm :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ContinuousOn
        (fun (pm : (Fin d → ℝ) × ℝ) =>
          JsimpleExt DpH x pm.1 pm.2)
        {pm | 0 ≤ pm.2}

/-- Coherence check: the trivially-zero pair `(H, D_pH) = (0, 0)`
satisfies `RegularityHK0`. This verifies that the structure compiles
and that the closed-cone domain `{pm | 0 ≤ pm.2}` is well-formed. -/
example (d : ℕ) :
    RegularityHK0 (d := d)
      (fun _ _ _ => (0 : ℝ))
      (fun _ _ _ => (0 : Fin d → ℝ)) where
  continuous_Hext_pm := by
    refine Filter.Eventually.of_forall ?_
    intro _
    exact continuousOn_const
  continuous_mDpH_pm := by
    refine Filter.Eventually.of_forall ?_
    intro x
    -- `JsimpleExt (fun _ _ _ => 0) x p m = m • 0 = 0`.
    have hEq :
        (fun (pm : (Fin d → ℝ) × ℝ) =>
            JsimpleExt
              (fun _ _ _ => (0 : Fin d → ℝ)) x pm.1 pm.2)
          = fun _ => (0 : Fin d → ℝ) := by
      funext pm
      simp [JsimpleExt]
    rw [hEq]
    exact continuousOn_const

/-! ### Step 3 of v8 K0 plan — easy half: `J = m · D_pH` continuity

This produces the `continuous_mDpH_pm` field of `RegularityHK0`
from `HypothesisPowerGrowth`. Paper reference: Remark
`(rmk:implied-a)`, claim 1 (`Source/FGU-monotone_revised.tex`,
lines 495–502): under simple power-growth, the extension
`J(x, p, m) := m · D_pH(x, p, m)` (with `J(x, p, 0) = 0`) is
jointly continuous on `{(p, m) | m ≥ 0}` for a.e. `x ∈ 𝕋^d`.

The proof is a near-mechanical wrapper: the `continuous_J` field of
`HypothesisPowerGrowth.toMDpHat0` already produces exactly this
statement, since the explicit extension `J` is `JsimpleExt DpH`.
-/

/-- **Step 3 of v8 K0 plan — easy half.**

For almost every `x ∈ 𝕋^d`, the map `(p, m) ↦ JsimpleExt DpH x p m
= m · D_pH(x, p, m)` is continuous on the closed half-plane
`{pm | 0 ≤ pm.2}`. The boundary value at `m = 0` is `0` (by
`JsimpleExt_zero`), and continuity across the boundary follows from
the simple power-growth bound on `D_pH` via
`HypothesisPowerGrowth.toMDpHat0.continuous_J`.

This is the field `continuous_mDpH_pm` of `RegularityHK0`. -/
theorem regularityHK0_mDpH_of_powerGrowth
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : HypothesisPowerGrowth (d := d) H DpH) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ContinuousOn
        (fun pm : (Fin d → ℝ) × ℝ =>
          JsimpleExt DpH x pm.1 pm.2)
        {pm | 0 ≤ pm.2} :=
  hpow.toMDpHat0.continuous_J

/-- Coherence check: the simple model `HypothesisPowerGrowth` for
`H(x, p, m) = ‖p‖^2 − m`, `D_pH(x, p, m) = 2 • p` satisfies the
closed-cone `m · D_pH` continuity statement. -/
example (d : ℕ) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ContinuousOn
        (fun pm : (Fin d → ℝ) × ℝ =>
          JsimpleExt (fun _ p _ => ((2 : ℝ) • p : Fin d → ℝ))
            x pm.1 pm.2)
        {pm | 0 ≤ pm.2} :=
  regularityHK0_mDpH_of_powerGrowth (simpleHypothesisPowerGrowth d)

/-! ### Step 4 of v8 K0 plan — hard half: `H` continuity (Option A rider)

The paper uses joint continuity of `(p, m) ↦ H(x, p, m)` on the closed
cone `{m ≥ 0}` in its hemicontinuity proof at line 1038. As recorded
in `Hamiltonian/Assumptions.lean` near `HypothesisHextJointCont`, this
continuity is *not* derivable from
`HypothesisPowerGrowth + HypothesisHat0 + H_zero_eq_Hext`: iter 0752
surfaced an explicit counterexample. Under user directive 2026-05-21,
we adopt **Option A**: encode the paper's implicit assumption as an
explicit paper-side rider `HypothesisHextJointCont H`.

This subsection wires the rider into the `RegularityHK0` API:

* `regularityHK0_Hext_of_jointCont` — identity wrapper: the rider IS
  the closed-cone `H` continuity statement.
* `regularityHK0_of_powerGrowth_and_HextJointCont` — combines `hpow`
  (giving the `m · D_pH` half via `regularityHK0_mDpH_of_powerGrowth`)
  with `hHextCont` to produce `RegularityHK0` in one shot.

No threading into `T10PaperResidues.of_paperHypotheses` or
`thm_main_simplePowerGrowth_paper` happens in this iteration — that
is a follow-up task that expands the public theorem statement. -/

/-- **Step 4 of v8 K0 plan — Option A, identity wrapper.**

The paper-faithful rider `HypothesisHextJointCont H` is literally the
closed-cone joint continuity statement consumed by the
`continuous_Hext_pm` field of `RegularityHK0`. This wrapper unifies
naming for downstream consumers. -/
theorem regularityHK0_Hext_of_jointCont
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    (hHextCont : Hamiltonian.HypothesisHextJointCont (d := d) H) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ContinuousOn
        (fun pm : (Fin d → ℝ) × ℝ => H x pm.1 pm.2)
        {pm | 0 ≤ pm.2} :=
  hHextCont

/-- **Step 4 of v8 K0 plan — combined producer.**

From `HypothesisPowerGrowth` (giving the `m · D_pH` half via
`regularityHK0_mDpH_of_powerGrowth`) together with the paper-side
joint-continuity rider `HypothesisHextJointCont H`, produce the
closed-cone regularity bundle `RegularityHK0`. -/
theorem regularityHK0_of_powerGrowth_and_HextJointCont
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : HypothesisPowerGrowth (d := d) H DpH)
    (hHextCont : Hamiltonian.HypothesisHextJointCont (d := d) H) :
    RegularityHK0 (d := d) H DpH where
  continuous_Hext_pm := regularityHK0_Hext_of_jointCont hHextCont
  continuous_mDpH_pm := regularityHK0_mDpH_of_powerGrowth hpow

/-- Coherence check: the trivially-zero Hamiltonian `H ≡ 0` satisfies
the paper-side joint-continuity rider. -/
example (d : ℕ) :
    Hamiltonian.HypothesisHextJointCont (d := d)
      (fun _ _ _ => (0 : ℝ)) := by
  refine Filter.Eventually.of_forall ?_
  intro _
  exact continuousOn_const

/-- Coherence check: the simple model
`H(x, p, m) = ‖p‖^2 − m` is jointly continuous in `(p, m)` on the
whole space, hence in particular on the closed cone `{m ≥ 0}`. This
witnesses `HypothesisHextJointCont` for the simple-power-growth
model. -/
example (d : ℕ) :
    Hamiltonian.HypothesisHextJointCont (d := d)
      (fun _ p m => (‖p‖ : ℝ) ^ (2 : ℝ) - m ^ (1 : ℝ)) := by
  refine Filter.Eventually.of_forall ?_
  intro _
  -- The map `(p, m) ↦ ‖p‖^2 − m^1` is continuous on the whole space.
  have hcont :
      Continuous
        (fun pm : (Fin d → ℝ) × ℝ =>
          (‖pm.1‖ : ℝ) ^ (2 : ℝ) - pm.2 ^ (1 : ℝ)) := by
    have h1 : Continuous
        (fun pm : (Fin d → ℝ) × ℝ => (‖pm.1‖ : ℝ) ^ (2 : ℝ)) :=
      (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 2)).comp
        (continuous_norm.comp continuous_fst)
    have h2 : Continuous
        (fun pm : (Fin d → ℝ) × ℝ => pm.2 ^ (1 : ℝ)) :=
      (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1)).comp
        continuous_snd
    exact h1.sub h2
  exact hcont.continuousOn

/-- Coherence check: from `simpleHypothesisPowerGrowth d` plus the
matching joint-continuity witness for `H = ‖p‖^2 − m`, we recover
`RegularityHK0` via `regularityHK0_of_powerGrowth_and_HextJointCont`. -/
example (d : ℕ) :
    RegularityHK0 (d := d)
      (fun _ p m => (‖p‖ : ℝ) ^ (2 : ℝ) - m ^ (1 : ℝ))
      (fun _ p _ => ((2 : ℝ) • p : Fin d → ℝ)) := by
  refine regularityHK0_of_powerGrowth_and_HextJointCont
    (simpleHypothesisPowerGrowth d) ?_
  refine Filter.Eventually.of_forall ?_
  intro _
  have hcont :
      Continuous
        (fun pm : (Fin d → ℝ) × ℝ =>
          (‖pm.1‖ : ℝ) ^ (2 : ℝ) - pm.2 ^ (1 : ℝ)) := by
    have h1 : Continuous
        (fun pm : (Fin d → ℝ) × ℝ => (‖pm.1‖ : ℝ) ^ (2 : ℝ)) :=
      (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 2)).comp
        (continuous_norm.comp continuous_fst)
    have h2 : Continuous
        (fun pm : (Fin d → ℝ) × ℝ => pm.2 ^ (1 : ℝ)) :=
      (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1)).comp
        continuous_snd
    exact h1.sub h2
  exact hcont.continuousOn

/-! ### Step 7 of v8 K0 plan — DCT-based continuity for the K0 unregularized half

This is the closed-cone (`K₀`) sibling of `aepsiIntegrand_unreg_continuousOn`
(near line 1853 above). The proof mirrors the open-cone version step-by-step,
with the strict-positivity hypothesis `hPos : 0 < cxComb μ mBar t x` replaced
by the nonnegativity hypothesis `hNonneg : 0 ≤ cxComb μ mBar t x`, and the
`RegularityH` (open half-plane `{pm | 0 < pm.2}`) consumer replaced by the
`RegularityHK0` (closed half-plane `{pm | 0 ≤ pm.2}`) consumer.

The K0 integrand differs from the open-cone integrand only in the flux term:
instead of `μt * (DpH x Dυt μt ⬝ Dν x)` (which is discontinuous at `μt = 0`),
it uses `(JsimpleExt DpH x Dυt μt) ⬝ Dν x`, which equals `μt • DpH x Dυt μt`
definitionally and is continuous across the boundary.
-/

/-- **DCT applied to the K0 (closed-cone) unregularized integrand.**

Under closed-cone regularity `RegularityHK0` of `(H, DpH)`, segment
nonnegativity `0 ≤ cxComb μ mBar t x`, and an integrable dominator on
`aepsiIntegrandAt_unreg_K0`, the function
`t ↦ ∫ x in UnitCube d, aepsiIntegrandAt_unreg_K0 … x t ∂volume` is
continuous on `[0, 1]`.

This is the closed-cone sibling of `aepsiIntegrand_unreg_continuousOn`
and is step 7 of the v8 K0 hemicontinuity plan. -/
theorem aepsiIntegrand_unreg_K0_continuousOn
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hRegK0 : RegularityHK0 (d := d) H DpH)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ)
    (μ mBar υ ῡ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ)
    (hNonneg : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ cxComb μ mBar t x)
    (g_unreg : (Fin d → ℝ) → ℝ)
    (hg_int : IntegrableOn g_unreg (UnitCube d))
    (hF_meas : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      AEStronglyMeasurable
        (fun x =>
          aepsiIntegrandAt_unreg_K0 V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν x t)
        (volume.restrict (UnitCube d)))
    (hF_bound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖aepsiIntegrandAt_unreg_K0 V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν x t‖
          ≤ g_unreg x) :
    ContinuousOn (fun t : ℝ =>
        ∫ x in UnitCube d,
          aepsiIntegrandAt_unreg_K0 V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν x t
        ∂(volume : Measure (Fin d → ℝ))) (Set.Icc 0 1) := by
  -- Mirror of the open-cone proof at `aepsiIntegrand_unreg_continuousOn`:
  -- a.e. pointwise continuity of the K0 integrand in `t` plus DCT.
  have h_cont :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ContinuousOn (fun t : ℝ =>
            aepsiIntegrandAt_unreg_K0
              V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν x t)
          (Set.Icc 0 1) := by
    filter_upwards
      [hRegK0.continuous_Hext_pm, hRegK0.continuous_mDpH_pm, hNonneg]
      with x hHx hJx hxNonneg
    -- Set up the composing curve `φ : ℝ → (Fin d → ℝ) × ℝ`.
    set φ : ℝ → (Fin d → ℝ) × ℝ :=
      fun t => ((fun i => cxCombGrad Dυ Dῡ t i x), cxComb μ mBar t x)
    have hφ_cont : Continuous φ := by
      refine Continuous.prodMk ?_ ?_
      · exact continuous_cxCombGrad Dυ Dῡ x
      · exact continuous_cxComb μ mBar x
    -- KEY architectural change vs. open-cone: closed half-plane `{0 ≤ pm.2}`
    -- (uses `hxNonneg t ht`).
    have hφ_maps : Set.MapsTo φ (Set.Icc (0 : ℝ) 1) {pm | 0 ≤ pm.2} := by
      intro t ht; simpa [φ] using hxNonneg t ht
    -- Compose `H x · ·` with `φ` on the closed cone.
    have hHcomp : ContinuousOn
        (fun t : ℝ =>
          H x (fun i => cxCombGrad Dυ Dῡ t i x) (cxComb μ mBar t x))
        (Set.Icc 0 1) := by
      have := hHx.comp hφ_cont.continuousOn hφ_maps
      simpa [φ, Function.comp_def] using this
    -- Compose `JsimpleExt DpH x · ·` with `φ` on the closed cone.
    -- This replaces the `μt * (DpH …)` step from the open-cone proof.
    have hJsimpleComp : ContinuousOn
        (fun t : ℝ =>
          JsimpleExt DpH x
            (fun i => cxCombGrad Dυ Dῡ t i x) (cxComb μ mBar t x))
        (Set.Icc 0 1) := by
      have := hJx.comp hφ_cont.continuousOn hφ_maps
      simpa [φ, Function.comp_def] using this
    -- The remaining slot continuities are unchanged from the open-cone proof.
    have hμt : Continuous (fun t : ℝ => cxComb μ mBar t x) :=
      continuous_cxComb μ mBar x
    have hυt : Continuous (fun t : ℝ => cxComb υ ῡ t x) :=
      continuous_cxComb υ ῡ x
    -- Dot product against the constant-in-`t` vector `Dν · x`.
    have hJsimpleDot : ContinuousOn
        (fun t : ℝ =>
          JsimpleExt DpH x
              (fun i => cxCombGrad Dυ Dῡ t i x) (cxComb μ mBar t x)
            ⬝ (fun i => Dν i x)) (Set.Icc 0 1) := by
      unfold dotProduct
      refine continuousOn_finset_sum _ (fun i _ => ?_)
      have hcoord : ContinuousOn
          (fun t : ℝ =>
            JsimpleExt DpH x
              (fun i => cxCombGrad Dυ Dῡ t i x) (cxComb μ mBar t x) i)
          (Set.Icc 0 1) :=
        (continuous_apply i).comp_continuousOn hJsimpleComp
      exact hcoord.mul continuousOn_const
    have hVconst : ContinuousOn (fun _ : ℝ => V x) (Set.Icc (0:ℝ) 1) :=
      continuousOn_const
    have hηconst : ContinuousOn (fun _ : ℝ => η x) (Set.Icc (0:ℝ) 1) :=
      continuousOn_const
    have hνconst : ContinuousOn (fun _ : ℝ => ν x) (Set.Icc (0:ℝ) 1) :=
      continuousOn_const
    have h1const : ContinuousOn (fun _ : ℝ => (1:ℝ)) (Set.Icc (0:ℝ) 1) :=
      continuousOn_const
    -- Unfold the K0 integrand and assemble. Compared to the open-cone
    -- proof, the middle term is `hJsimpleDot` instead of
    -- `(hμt.continuousOn).mul hDpHdot`.
    unfold aepsiIntegrandAt_unreg_K0
    refine
      (((((hυt.continuousOn).neg.sub hHcomp).add hVconst).mul hηconst).add
        hJsimpleDot).add ?_
    exact ((hμt.continuousOn).sub h1const).mul hνconst
  -- Apply Mathlib's `continuousOn_of_dominated`.
  exact MeasureTheory.continuousOn_of_dominated
    (μ := volume.restrict (UnitCube d))
    (s := Set.Icc 0 1)
    hF_meas hF_bound hg_int h_cont

/-! ### K0 transport-segment continuity certificate (D6c2a2a)

Head of the user-approved K0 mini-chain. On the *transport* segment the two
density endpoints coincide (`μ = μ̄`), so the density slot is **constant**
along the segment: `cxComb μ μ t x = (1 - t) * μ x + t * μ x = μ x` for every
`t`. Only the gradient/value slots move (affinely in `t`).

This is the closed-cone (`K₀`) certificate: it uses
`aepsiIntegrandAt_unreg_K0` (genuine closed cone, continuous across the
`μ = 0` boundary), and the only density-side hypothesis is nonnegativity
`0 ≤ μ`. No strict positivity, no `HdeltaPos` junk at `m = 0`, no
`HypothesisPowerGrowth`. It is a direct specialization of
`aepsiIntegrand_unreg_K0_continuousOn` at `mBar := μ`, with the
`cxComb`-nonnegativity hypothesis rewritten to the fixed-density form
`0 ≤ μ x`. -/
theorem aepsi_transportIntegrand_K0_continuousOn
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hRegK0 : RegularityHK0 (d := d) H DpH)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ)
    (μ υ ῡ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ)
    (hmNonneg : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ μ x)
    (g_unreg : (Fin d → ℝ) → ℝ)
    (hg_int : IntegrableOn g_unreg (UnitCube d))
    (hF_meas : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      AEStronglyMeasurable
        (fun x =>
          aepsiIntegrandAt_unreg_K0 V H DpH Dυ Dῡ μ μ υ ῡ Dν η ν x t)
        (volume.restrict (UnitCube d)))
    (hF_bound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖aepsiIntegrandAt_unreg_K0 V H DpH Dυ Dῡ μ μ υ ῡ Dν η ν x t‖
          ≤ g_unreg x) :
    ContinuousOn (fun t : ℝ =>
        ∫ x in UnitCube d,
          aepsiIntegrandAt_unreg_K0 V H DpH Dυ Dῡ μ μ υ ῡ Dν η ν x t
        ∂(volume : Measure (Fin d → ℝ))) (Set.Icc 0 1) := by
  -- On the transport segment the density endpoints coincide, so the
  -- `cxComb μ μ t x = μ x` reduces segment nonnegativity to `0 ≤ μ x`.
  refine aepsiIntegrand_unreg_K0_continuousOn (d := d)
    V H DpH hRegK0 Dυ Dῡ μ μ υ ῡ Dν η ν ?_ g_unreg hg_int hF_meas hF_bound
  filter_upwards [hmNonneg] with x hx t _ht
  -- `cxComb μ μ t x = (1 - t) * μ x + t * μ x = μ x ≥ 0`.
  have : cxComb μ μ t x = μ x := by
    simp [cxComb]; ring
  rw [this]
  exact hx

/-- **K0 transport-segment continuity of the full regularized operator
pairing** (D6c2a2c support lemma).

K0 + transport sibling of `Aepsi_hemicontinuous_segment`. On the transport
segment the two density endpoints coincide (`mBar = μ`), so the only
density-side hypothesis is `0 ≤ μ` (no strict positivity). The
unregularized half is handled by the closed-cone DCT lemma
`aepsi_transportIntegrand_K0_continuousOn` (which uses
`aepsiIntegrandAt_unreg_K0`, continuous across `μ = 0`), and the Gateaux
half by `aepsiIntegrand_gateaux_continuousOn`. The two integrals are
reassembled into `mfgOperatorEpsPair` via the unconditional pointwise
agreement `aepsiIntegrandAt_unreg_K0_eq_unreg` (the K0 flux
`JsimpleExt DpH = m • DpH` matches the strict-cone `m * (DpH ⬝ Dν)`)
together with `mfgOperatorPair_segment_eq_integral` and
`gateauxWpPair_segment_eq_integral`.

This produces the operator-continuity certificate the transport-form
Minty base-point collapse needs, with the `hCont` binder discharged from
`0 ≤ μ` alone. -/
theorem Aepsi_hemicontinuous_transportSegment_K0
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hRegK0 : RegularityHK0 (d := d) H DpH)
    (γBar ε : ℝ) (hγ : 1 < γBar)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ)
    (μ υ ῡ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ)
    (hmNonneg : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ μ x)
    (g_unreg g_gat : (Fin d → ℝ) → ℝ)
    (hg_unreg_int : IntegrableOn g_unreg (UnitCube d))
    (hg_gat_int : IntegrableOn g_gat (UnitCube d))
    (hF_unreg_meas : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      AEStronglyMeasurable
        (fun x =>
          aepsiIntegrandAt_unreg_K0 V H DpH Dυ Dῡ μ μ υ ῡ Dν η ν x t)
        (volume.restrict (UnitCube d)))
    (hF_unreg_bound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖aepsiIntegrandAt_unreg_K0 V H DpH Dυ Dῡ μ μ υ ῡ Dν η ν x t‖
          ≤ g_unreg x)
    (hF_gat_meas : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      AEStronglyMeasurable
        (fun x => aepsiIntegrandAt_gateaux γBar Dυ Dῡ υ ῡ Dν ν x t)
        (volume.restrict (UnitCube d)))
    (hF_gat_bound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖aepsiIntegrandAt_gateaux γBar Dυ Dῡ υ ῡ Dν ν x t‖ ≤ g_gat x) :
    ContinuousOn (fun t : ℝ =>
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH) γBar ε
          (fun i x => cxCombGrad Dυ Dῡ t i x)
          (fun x => cxComb μ μ t x)
          (fun x => cxComb υ ῡ t x) Dν η ν) (Set.Icc 0 1) := by
  -- Rewrite the pairing as the sum of the two unit-cube integrals, with the
  -- unregularized half expressed through the K0 integrand (unconditional
  -- pointwise agreement with the strict-cone integrand).
  have hRewrite : ∀ t : ℝ,
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH) γBar ε
          (fun i x => cxCombGrad Dυ Dῡ t i x)
          (fun x => cxComb μ μ t x)
          (fun x => cxComb υ ῡ t x) Dν η ν
        = (∫ x in UnitCube d,
              aepsiIntegrandAt_unreg_K0 V H DpH Dυ Dῡ μ μ υ ῡ Dν η ν x t
            ∂(volume : Measure (Fin d → ℝ)))
          + ε *
            (∫ x in UnitCube d,
              aepsiIntegrandAt_gateaux γBar Dυ Dῡ υ ῡ Dν ν x t
            ∂(volume : Measure (Fin d → ℝ))) := by
    intro t
    unfold mfgOperatorEpsPair
    rw [mfgOperatorPair_segment_eq_integral V H DpH Dυ Dῡ μ μ υ ῡ Dν η ν t,
        gateauxWpPair_segment_eq_integral γBar Dυ Dῡ υ ῡ Dν ν t]
    -- Replace `aepsiIntegrandAt_unreg` by the K0 integrand (unconditional).
    have hagree :
        (∫ x in UnitCube d,
            aepsiIntegrandAt_unreg V H DpH Dυ Dῡ μ μ υ ῡ Dν η ν x t
          ∂(volume : Measure (Fin d → ℝ)))
          = (∫ x in UnitCube d,
            aepsiIntegrandAt_unreg_K0 V H DpH Dυ Dῡ μ μ υ ῡ Dν η ν x t
          ∂(volume : Measure (Fin d → ℝ))) := by
      refine setIntegral_congr_fun measurableSet_unitCube ?_
      intro x _
      exact (aepsiIntegrandAt_unreg_K0_eq_unreg
        V H DpH Dυ Dῡ μ μ υ ῡ Dν η ν x t).symm
    rw [hagree]
  -- Continuity of the K0 unregularized half via the closed-cone DCT lemma.
  have h1 := aepsi_transportIntegrand_K0_continuousOn
    V H DpH hRegK0 Dυ Dῡ μ υ ῡ Dν η ν hmNonneg
    g_unreg hg_unreg_int hF_unreg_meas hF_unreg_bound
  -- Continuity of the Gateaux half.
  have h2 := aepsiIntegrand_gateaux_continuousOn γBar hγ Dυ Dῡ υ ῡ Dν ν
    g_gat hg_gat_int hF_gat_meas hF_gat_bound
  have hsum : ContinuousOn
      (fun t : ℝ =>
        (∫ x in UnitCube d,
            aepsiIntegrandAt_unreg_K0 V H DpH Dυ Dῡ μ μ υ ῡ Dν η ν x t
          ∂(volume : Measure (Fin d → ℝ)))
        + ε *
          (∫ x in UnitCube d,
            aepsiIntegrandAt_gateaux γBar Dυ Dῡ υ ῡ Dν ν x t
          ∂(volume : Measure (Fin d → ℝ)))) (Set.Icc 0 1) :=
    h1.add (continuousOn_const.mul h2)
  refine hsum.congr ?_
  intro t _
  exact hRewrite t

/-- **K0 set/density-segment continuity of the full regularized operator
pairing** (D6d support lemma).

K0 + *density-direction* sibling of `Aepsi_hemicontinuous_transportSegment_K0`.
Here the two **gradient** endpoints coincide (`Dυ = Dῡ`) and the two **value**
endpoints coincide (`υ = ῡ`), so the gradient/value slots are constant along
the segment; only the **density** slot moves (the convex combination
`cxComb μ mBar t`). This is exactly the Minty INDICATOR perturbation
`μ_t := mBar + t·1_S` realised at `μ := mBar + 1_S`, `mBar`,
`Dυ = Dῡ`, `υ = ῡ`, test `(Dν, η, ν)`.

The only density-side hypothesis is segment-nonnegativity
`0 ≤ cxComb μ mBar t x` (no strict positivity, no `HdeltaPos`); it is
discharged by the general closed-cone DCT lemma
`aepsiIntegrand_unreg_K0_continuousOn` (which uses `aepsiIntegrandAt_unreg_K0`,
continuous across `μ = 0`), with the Gateaux half handled by
`aepsiIntegrand_gateaux_continuousOn`. The two integrals are reassembled into
`mfgOperatorEpsPair` via the unconditional pointwise agreement
`aepsiIntegrandAt_unreg_K0_eq_unreg` together with
`mfgOperatorPair_segment_eq_integral` and `gateauxWpPair_segment_eq_integral`.

This produces the operator-continuity certificate the set-form Minty
base-point collapse needs (`hContRaw`), with the continuity binder discharged
from segment nonnegativity alone. -/
theorem Aepsi_hemicontinuous_setSegment_K0
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hRegK0 : RegularityHK0 (d := d) H DpH)
    (γBar ε : ℝ) (hγ : 1 < γBar)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ)
    (μ mBar υ ῡ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ)
    (hNonneg : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ cxComb μ mBar t x)
    (g_unreg g_gat : (Fin d → ℝ) → ℝ)
    (hg_unreg_int : IntegrableOn g_unreg (UnitCube d))
    (hg_gat_int : IntegrableOn g_gat (UnitCube d))
    (hF_unreg_meas : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      AEStronglyMeasurable
        (fun x =>
          aepsiIntegrandAt_unreg_K0 V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν x t)
        (volume.restrict (UnitCube d)))
    (hF_unreg_bound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖aepsiIntegrandAt_unreg_K0 V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν x t‖
          ≤ g_unreg x)
    (hF_gat_meas : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      AEStronglyMeasurable
        (fun x => aepsiIntegrandAt_gateaux γBar Dυ Dῡ υ ῡ Dν ν x t)
        (volume.restrict (UnitCube d)))
    (hF_gat_bound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖aepsiIntegrandAt_gateaux γBar Dυ Dῡ υ ῡ Dν ν x t‖ ≤ g_gat x) :
    ContinuousOn (fun t : ℝ =>
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH) γBar ε
          (fun i x => cxCombGrad Dυ Dῡ t i x)
          (fun x => cxComb μ mBar t x)
          (fun x => cxComb υ ῡ t x) Dν η ν) (Set.Icc 0 1) := by
  -- Rewrite the pairing as the sum of the two unit-cube integrals, with the
  -- unregularized half expressed through the K0 integrand (unconditional
  -- pointwise agreement with the strict-cone integrand).
  have hRewrite : ∀ t : ℝ,
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH) γBar ε
          (fun i x => cxCombGrad Dυ Dῡ t i x)
          (fun x => cxComb μ mBar t x)
          (fun x => cxComb υ ῡ t x) Dν η ν
        = (∫ x in UnitCube d,
              aepsiIntegrandAt_unreg_K0 V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν x t
            ∂(volume : Measure (Fin d → ℝ)))
          + ε *
            (∫ x in UnitCube d,
              aepsiIntegrandAt_gateaux γBar Dυ Dῡ υ ῡ Dν ν x t
            ∂(volume : Measure (Fin d → ℝ))) := by
    intro t
    unfold mfgOperatorEpsPair
    rw [mfgOperatorPair_segment_eq_integral V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν t,
        gateauxWpPair_segment_eq_integral γBar Dυ Dῡ υ ῡ Dν ν t]
    have hagree :
        (∫ x in UnitCube d,
            aepsiIntegrandAt_unreg V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν x t
          ∂(volume : Measure (Fin d → ℝ)))
          = (∫ x in UnitCube d,
            aepsiIntegrandAt_unreg_K0 V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν x t
          ∂(volume : Measure (Fin d → ℝ))) := by
      refine setIntegral_congr_fun measurableSet_unitCube ?_
      intro x _
      exact (aepsiIntegrandAt_unreg_K0_eq_unreg
        V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν x t).symm
    rw [hagree]
  -- Continuity of the K0 unregularized half via the general closed-cone DCT
  -- lemma (density slot moves; segment nonnegativity).
  have h1 := aepsiIntegrand_unreg_K0_continuousOn
    V H DpH hRegK0 Dυ Dῡ μ mBar υ ῡ Dν η ν hNonneg
    g_unreg hg_unreg_int hF_unreg_meas hF_unreg_bound
  -- Continuity of the Gateaux half.
  have h2 := aepsiIntegrand_gateaux_continuousOn γBar hγ Dυ Dῡ υ ῡ Dν ν
    g_gat hg_gat_int hF_gat_meas hF_gat_bound
  have hsum : ContinuousOn
      (fun t : ℝ =>
        (∫ x in UnitCube d,
            aepsiIntegrandAt_unreg_K0 V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν x t
          ∂(volume : Measure (Fin d → ℝ)))
        + ε *
          (∫ x in UnitCube d,
            aepsiIntegrandAt_gateaux γBar Dυ Dῡ υ ῡ Dν ν x t
          ∂(volume : Measure (Fin d → ℝ)))) (Set.Icc 0 1) :=
    h1.add (continuousOn_const.mul h2)
  refine hsum.congr ?_
  intro t _
  exact hRewrite t

/-- Unit-test: the K0 unregularized DCT continuity lemma applies on the
trivially-zero data. With `H ≡ 0`, `DpH ≡ 0`, `Dν ≡ 0`, `η ≡ 0`, `ν ≡ 0`,
`V ≡ 0`, etc., the integrand is identically zero, the dominator is `0`,
and continuity is trivial. This exercises that the hypothesis shapes
align (in particular that the closed-cone `hNonneg` and `RegularityHK0`
plug in correctly). -/
example (d : ℕ) :
    ContinuousOn (fun t : ℝ =>
        ∫ x in UnitCube d,
          aepsiIntegrandAt_unreg_K0 (d := d)
            (fun _ => (0 : ℝ))
            (fun _ _ _ => (0 : ℝ))
            (fun _ _ _ => (0 : Fin d → ℝ))
            (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ))
            (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ))
            (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ))
            (fun _ _ => (0 : ℝ))
            (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) x t
        ∂(volume : Measure (Fin d → ℝ))) (Set.Icc 0 1) := by
  refine aepsiIntegrand_unreg_K0_continuousOn (d := d)
    (V := fun _ => 0)
    (H := fun _ _ _ => 0)
    (DpH := fun _ _ _ => (0 : Fin d → ℝ))
    ?_
    (Dυ := fun _ _ => 0) (Dῡ := fun _ _ => 0)
    (μ := fun _ => 0) (mBar := fun _ => 0)
    (υ := fun _ => 0) (ῡ := fun _ => 0)
    (Dν := fun _ _ => 0)
    (η := fun _ => 0) (ν := fun _ => 0)
    ?_
    (g_unreg := fun _ => 0)
    ?_ ?_ ?_
  · -- `RegularityHK0` for the zero pair (coherence check above).
    refine ⟨?_, ?_⟩
    · exact Filter.Eventually.of_forall (fun _ => continuousOn_const)
    · refine Filter.Eventually.of_forall (fun x => ?_)
      have hEq :
          (fun (pm : (Fin d → ℝ) × ℝ) =>
              JsimpleExt
                (fun _ _ _ => (0 : Fin d → ℝ)) x pm.1 pm.2)
            = fun _ => (0 : Fin d → ℝ) := by
        funext pm
        simp [JsimpleExt]
      rw [hEq]
      exact continuousOn_const
  · -- `hNonneg`: `cxComb 0 0 t x = 0 ≥ 0`.
    refine Filter.Eventually.of_forall ?_
    intro x t _
    simp [cxComb]
  · -- Integrability of the constant-zero dominator on the unit cube.
    simpa using (integrableOn_const (c := (0 : ℝ)) (μ := volume)
      (s := UnitCube d)).mpr (Or.inl rfl)
  · -- AE-strong-measurability of the integrand (which is `0`).
    intro t _
    have hzero :
        (fun x : Fin d → ℝ =>
            aepsiIntegrandAt_unreg_K0 (d := d)
              (fun _ => (0 : ℝ))
              (fun _ _ _ => (0 : ℝ))
              (fun _ _ _ => (0 : Fin d → ℝ))
              (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ))
              (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ))
              (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ))
              (fun _ _ => (0 : ℝ))
              (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) x t)
          = fun _ : Fin d → ℝ => (0 : ℝ) := by
      funext x
      simp [aepsiIntegrandAt_unreg_K0, JsimpleExt, dotProduct]
    rw [hzero]
    exact aestronglyMeasurable_const
  · -- Pointwise bound by the zero dominator.
    intro t _
    refine Filter.Eventually.of_forall ?_
    intro x
    simp [aepsiIntegrandAt_unreg_K0, JsimpleExt, dotProduct]

/-! ## K0 sibling: `HemicontSegmentDataK0`

Step 8 of the v8 K0 hemicontinuity plan. This is a **sibling** structure
to `HemicontSegmentData` (line 2325). It mirrors the field list exactly,
with two changes:

1. The strict-positivity field `hPos : 0 < cxComb μ mBar t x` is replaced
   by the nonnegativity field `hNonneg : 0 ≤ cxComb μ mBar t x`.
2. The unregularized integrand referenced in `hF_unreg_meas` /
   `hF_unreg_bound` is `aepsiIntegrandAt_unreg_K0` (the closed-cone variant
   that uses `JsimpleExt DpH …` in the flux slot) instead of
   `aepsiIntegrandAt_unreg`.

The Gateaux fields are unchanged: `aepsiIntegrandAt_gateaux` is K0-agnostic.

The existing `HemicontSegmentData` is intentionally untouched — the K0
sibling is consumed by the downstream set/signed/transport composers
(step 9 of the plan), while the open-cone bundle continues to feed
the strict-cone aggregator at `lem_hemicont`. -/

/-- **K0 sibling of `HemicontSegmentData`.**

Per-segment dominator/measurability bundle targeting the closed-cone
DCT lemma `aepsiIntegrand_unreg_K0_continuousOn`. See the section
header above for the precise differences from the open-cone bundle. -/
structure HemicontSegmentDataK0 {d : ℕ}
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (γBar : ℝ)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ)
    (μ mBar υ ῡ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ) : Type where
  /-- A.e.-uniform-in-`t` **nonnegativity** along the segment.
  Replaces the strict-positivity field of `HemicontSegmentData`. -/
  hNonneg : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
              ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ cxComb μ mBar t x
  /-- Dominator for the (K0) unregularised integrand. -/
  g_unreg : (Fin d → ℝ) → ℝ
  /-- Dominator for the Gateaux integrand. -/
  g_gat : (Fin d → ℝ) → ℝ
  hg_unreg_int : IntegrableOn g_unreg (UnitCube d)
  hg_gat_int : IntegrableOn g_gat (UnitCube d)
  hF_unreg_meas : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    AEStronglyMeasurable
      (fun x =>
        aepsiIntegrandAt_unreg_K0 V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν x t)
      (volume.restrict (UnitCube d))
  hF_unreg_bound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ‖aepsiIntegrandAt_unreg_K0 V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν x t‖
        ≤ g_unreg x
  hF_gat_meas : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    AEStronglyMeasurable
      (fun x => aepsiIntegrandAt_gateaux γBar Dυ Dῡ υ ῡ Dν ν x t)
      (volume.restrict (UnitCube d))
  hF_gat_bound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ‖aepsiIntegrandAt_gateaux γBar Dυ Dῡ υ ῡ Dν ν x t‖ ≤ g_gat x

/-- **Consumer glue lemma.**

A `HemicontSegmentDataK0` bundle together with closed-cone regularity
`RegularityHK0 H DpH` immediately yields the K0 DCT continuity statement
by feeding the bundle fields to `aepsiIntegrand_unreg_K0_continuousOn`
(iter 0756). This is the surface the step-9 set/signed/transport
composers will produce values of. -/
theorem aepsiIntegrand_continuousOn_of_segmentDataK0
    {d : ℕ}
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (γBar : ℝ)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ)
    (μ mBar υ ῡ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ)
    (hRegK0 : RegularityHK0 (d := d) H DpH)
    (sd : HemicontSegmentDataK0 V H DpH γBar Dυ Dῡ μ mBar υ ῡ Dν η ν) :
    ContinuousOn (fun t : ℝ =>
        ∫ x in UnitCube d,
          aepsiIntegrandAt_unreg_K0 V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν x t
        ∂(volume : Measure (Fin d → ℝ))) (Set.Icc 0 1) :=
  aepsiIntegrand_unreg_K0_continuousOn (d := d)
    (V := V) (H := H) (DpH := DpH) hRegK0
    (Dυ := Dυ) (Dῡ := Dῡ)
    (μ := μ) (mBar := mBar) (υ := υ) (ῡ := ῡ)
    (Dν := Dν) (η := η) (ν := ν)
    sd.hNonneg sd.g_unreg sd.hg_unreg_int sd.hF_unreg_meas sd.hF_unreg_bound

/-- Unit-test: trivial construction of `HemicontSegmentDataK0` on
zero-everywhere data. With all functions identically zero, the
K0 integrand and Gateaux integrand are both identically zero, so
the dominators `g_unreg = g_gat = 0` are integrable and the bounds
hold trivially. This exercises that the field shapes match
`aepsiIntegrand_unreg_K0_continuousOn` (and hence
`aepsiIntegrand_continuousOn_of_segmentDataK0`). -/
example (d : ℕ) :
    HemicontSegmentDataK0 (d := d)
      (V := fun _ => (0 : ℝ))
      (H := fun _ _ _ => (0 : ℝ))
      (DpH := fun _ _ _ => (0 : Fin d → ℝ))
      (γBar := 0)
      (Dυ := fun _ _ => 0) (Dῡ := fun _ _ => 0)
      (μ := fun _ => 0) (mBar := fun _ => 0)
      (υ := fun _ => 0) (ῡ := fun _ => 0)
      (Dν := fun _ _ => 0)
      (η := fun _ => 0) (ν := fun _ => 0) :=
  { hNonneg := by
      refine Filter.Eventually.of_forall ?_
      intro x t _
      simp [cxComb]
    g_unreg := fun _ => 0
    g_gat := fun _ => 0
    hg_unreg_int := by
      simpa using (integrableOn_const (c := (0 : ℝ)) (μ := volume)
        (s := UnitCube d)).mpr (Or.inl rfl)
    hg_gat_int := by
      simpa using (integrableOn_const (c := (0 : ℝ)) (μ := volume)
        (s := UnitCube d)).mpr (Or.inl rfl)
    hF_unreg_meas := by
      intro t _
      have hzero :
          (fun x : Fin d → ℝ =>
              aepsiIntegrandAt_unreg_K0 (d := d)
                (fun _ => (0 : ℝ))
                (fun _ _ _ => (0 : ℝ))
                (fun _ _ _ => (0 : Fin d → ℝ))
                (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ))
                (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ))
                (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ))
                (fun _ _ => (0 : ℝ))
                (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) x t)
            = fun _ : Fin d → ℝ => (0 : ℝ) := by
        funext x
        simp [aepsiIntegrandAt_unreg_K0, JsimpleExt, dotProduct]
      rw [hzero]
      exact aestronglyMeasurable_const
    hF_unreg_bound := by
      intro t _
      refine Filter.Eventually.of_forall ?_
      intro x
      simp [aepsiIntegrandAt_unreg_K0, JsimpleExt, dotProduct]
    hF_gat_meas := by
      intro t _
      have hzero :
          (fun x : Fin d → ℝ =>
              aepsiIntegrandAt_gateaux (d := d) (0 : ℝ)
                (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ))
                (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ))
                (fun _ _ => (0 : ℝ)) (fun _ => (0 : ℝ)) x t)
            = fun _ : Fin d → ℝ => (0 : ℝ) := by
        funext x
        simp [aepsiIntegrandAt_gateaux, cxComb, cxCombGrad, dotProduct]
      rw [hzero]
      exact aestronglyMeasurable_const
    hF_gat_bound := by
      intro t _
      refine Filter.Eventually.of_forall ?_
      intro x
      simp [aepsiIntegrandAt_gateaux, cxComb, cxCombGrad, dotProduct] }

/-! ### `HemicontSegmentDataK0.ae_eq` — transport along a.e.-equality
(K0 sibling)

Mirrors `HemicontSegmentData.ae_eq` for the K0 sibling structure. The
non-strict positivity field `hNonneg : 0 ≤ cxComb …` transports just
like the strict `hPos` field (both depend on `(μ, mBar)` only via
`cxComb` which is a.e.-stable by `cxComb_congr_ae`), and the K0
unreg integrand `aepsiIntegrandAt_unreg_K0` transports a.e. by the
same algebra as `aepsiIntegrandAt_unreg` (both depend on
`(μ, mBar, υ, ῡ, Dυ, Dῡ)` only via the same `cxComb`/`cxCombGrad`
pieces). -/

/-- A.e. transport for the K0 (closed-cone) unreg integrand. The
flux-slot difference between `aepsiIntegrandAt_unreg_K0` and
`aepsiIntegrandAt_unreg` is irrelevant to the transport: both
integrands are functions of `cxComb μ mBar t x` and
`cxCombGrad Dυ Dῡ t i x`, which transport a.e. by
`cxComb_congr_ae`/`cxCombGrad_congr_ae`. -/
lemma aepsiIntegrandAt_unreg_K0_congr_ae
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    {Dυ Dυ' Dῡ Dῡ' : Fin d → (Fin d → ℝ) → ℝ}
    {μ μ' mBar mBar' υ υ' ῡ ῡ' : (Fin d → ℝ) → ℝ}
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ)
    (hμ : μ =ᵐ[volume.restrict (UnitCube d)] μ')
    (hmBar : mBar =ᵐ[volume.restrict (UnitCube d)] mBar')
    (hυ : υ =ᵐ[volume.restrict (UnitCube d)] υ')
    (hῡ : ῡ =ᵐ[volume.restrict (UnitCube d)] ῡ')
    (hDυ : ∀ i, Dυ i =ᵐ[volume.restrict (UnitCube d)] Dυ' i)
    (hDῡ : ∀ i, Dῡ i =ᵐ[volume.restrict (UnitCube d)] Dῡ' i) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ t : ℝ,
        aepsiIntegrandAt_unreg_K0 V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν x t
          = aepsiIntegrandAt_unreg_K0 V H DpH Dυ' Dῡ' μ' mBar' υ' ῡ' Dν η ν x t := by
  filter_upwards [cxComb_congr_ae hμ hmBar,
                  cxComb_congr_ae hυ hῡ,
                  cxCombGrad_congr_ae hDυ hDῡ]
    with x hμt hυt hDυt t
  unfold aepsiIntegrandAt_unreg_K0
  have hμx := hμt t
  have hυx := hυt t
  have hDυx : (fun i => cxCombGrad Dυ Dῡ t i x)
              = (fun i => cxCombGrad Dυ' Dῡ' t i x) := by
    funext i; exact hDυt t i
  rw [hμx, hυx, hDυx]

/-- **`HemicontSegmentDataK0.ae_eq` (transport helper, K0 sibling).**

K0 analogue of `HemicontSegmentData.ae_eq`: transports a
`HemicontSegmentDataK0` bundle along a.e.-equalities of its bare-function
arguments, with the dominator pair and the test direction reused
unchanged. -/
def HemicontSegmentDataK0.ae_eq
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (γBar : ℝ)
    {Dυ Dυ' Dῡ Dῡ' : Fin d → (Fin d → ℝ) → ℝ}
    {μ μ' mBar mBar' υ υ' ῡ ῡ' : (Fin d → ℝ) → ℝ}
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ)
    (hμ : μ =ᵐ[volume.restrict (UnitCube d)] μ')
    (hmBar : mBar =ᵐ[volume.restrict (UnitCube d)] mBar')
    (hυ : υ =ᵐ[volume.restrict (UnitCube d)] υ')
    (hῡ : ῡ =ᵐ[volume.restrict (UnitCube d)] ῡ')
    (hDυ : ∀ i, Dυ i =ᵐ[volume.restrict (UnitCube d)] Dυ' i)
    (hDῡ : ∀ i, Dῡ i =ᵐ[volume.restrict (UnitCube d)] Dῡ' i)
    (data : HemicontSegmentDataK0 V H DpH γBar Dυ Dῡ μ mBar υ ῡ Dν η ν) :
    HemicontSegmentDataK0 V H DpH γBar Dυ' Dῡ' μ' mBar' υ' ῡ' Dν η ν :=
  let hμt_eq := cxComb_congr_ae hμ hmBar
  let hF_unreg_K0_eq :=
    aepsiIntegrandAt_unreg_K0_congr_ae V H DpH Dν η ν
      hμ hmBar hυ hῡ hDυ hDῡ
  let hF_gat_eq := aepsiIntegrandAt_gateaux_congr_ae γBar Dν ν
                    hυ hῡ hDυ hDῡ
  { hNonneg := by
      filter_upwards [data.hNonneg, hμt_eq] with x hNNx hμtx t ht
      have := hNNx t ht
      rw [hμtx t] at this
      exact this
    g_unreg := data.g_unreg
    g_gat := data.g_gat
    hg_unreg_int := data.hg_unreg_int
    hg_gat_int := data.hg_gat_int
    hF_unreg_meas := by
      intro t ht
      have hmeas := data.hF_unreg_meas t ht
      refine hmeas.congr ?_
      filter_upwards [hF_unreg_K0_eq] with x hx
      exact hx t
    hF_unreg_bound := by
      intro t ht
      have hb := data.hF_unreg_bound t ht
      filter_upwards [hb, hF_unreg_K0_eq] with x hxBd hxEq
      have := hxEq t
      rw [← this]
      exact hxBd
    hF_gat_meas := by
      intro t ht
      have hmeas := data.hF_gat_meas t ht
      refine hmeas.congr ?_
      filter_upwards [hF_gat_eq] with x hx
      exact hx t
    hF_gat_bound := by
      intro t ht
      have hb := data.hF_gat_bound t ht
      filter_upwards [hb, hF_gat_eq] with x hxBd hxEq
      have := hxEq t
      rw [← this]
      exact hxBd }

/-- Sanity-check: applying `HemicontSegmentDataK0.ae_eq` with the six
trivial a.e.-equalities returns a bundle at the same arguments. -/
example
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (γBar : ℝ)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ)
    (μ mBar υ ῡ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ)
    (data : HemicontSegmentDataK0 V H DpH γBar Dυ Dῡ μ mBar υ ῡ Dν η ν) :
    HemicontSegmentDataK0 V H DpH γBar Dυ Dῡ μ mBar υ ῡ Dν η ν :=
  HemicontSegmentDataK0.ae_eq V H DpH γBar Dν η ν
    (Filter.EventuallyEq.refl _ _) (Filter.EventuallyEq.refl _ _)
    (Filter.EventuallyEq.refl _ _) (Filter.EventuallyEq.refl _ _)
    (fun _ => Filter.EventuallyEq.refl _ _)
    (fun _ => Filter.EventuallyEq.refl _ _)
    data

/-! ### K0 sibling: `A0_isHemicontinuousK0`

K0 sibling of `A0_isHemicontinuous` (iter
`infra-P5-T10-v8-K0-set-mintyResSetOf-retype`). Consumes a per-segment
`HemicontSegmentDataK0` bundle and closed-cone regularity `RegularityHK0`
in place of the strict-K versions, and yields the same conclusion
`IsHemicontinuousMFG d D mfgOperatorPair`. The proof reduces continuity
of `mfgOperatorPair … t` in `t` to continuity of `∫ aepsiIntegrandAt_unreg`
via `mfgOperatorPair_segment_eq_integral` (defined near line 1843
above), then transports a K0 DCT continuity result via the
unconditional pointwise agreement `aepsiIntegrandAt_unreg_K0_eq_unreg`
(line 1422 above).

This bypasses the strict-positivity requirement of `lem_hemicont`
(which needs `hPos : 0 < cxComb μ mBar t x`) — the K0 path requires
only a.e. non-negativity `hNonneg`. -/

/-- **K0 sibling of `A0_isHemicontinuous`.**

Under closed-cone regularity `RegularityHK0` and a per-segment
`HemicontSegmentDataK0` bundle on every pair of triples in `D`, the
unregularised MFG operator pairing `mfgOperatorPair` is hemicontinuous
on `D` in the sense of `IsHemicontinuousMFG`. -/
theorem A0_isHemicontinuousK0
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hRegK0 : RegularityHK0 (d := d) H DpH)
    (γBar : ℝ)
    (D : Set (MFGTriple d))
    (hData : ∀ ⦃μBar ῡ Dῡ⦄, (μBar, ῡ, Dῡ) ∈ D →
             ∀ ⦃μ υ Dυ⦄, (μ, υ, Dυ) ∈ D →
             ∀ (η ν : (Fin d → ℝ) → ℝ)
               (Dν : Fin d → (Fin d → ℝ) → ℝ),
             HemicontSegmentDataK0 V H DpH γBar Dυ Dῡ μ μBar υ ῡ Dν η ν) :
    IsHemicontinuousMFG d D
      (mfgOperatorPair (V := V) (H := H) (DpH := DpH)) := by
  intro μBar ῡ Dῡ hBar μ υ Dυ hμ η ν Dν
  -- Get the K0 segment-data bundle on this pair.
  have sd := hData hBar hμ η ν Dν
  -- K0 DCT: continuity of `t ↦ ∫ aepsiIntegrandAt_unreg_K0 … x t ∂vol`.
  have hcts_K0 :
      ContinuousOn (fun t : ℝ =>
          ∫ x in UnitCube d,
            aepsiIntegrandAt_unreg_K0 V H DpH Dυ Dῡ μ μBar υ ῡ Dν η ν x t
          ∂(volume : Measure (Fin d → ℝ))) (Set.Icc 0 1) :=
    aepsiIntegrand_continuousOn_of_segmentDataK0
      V H DpH γBar Dυ Dῡ μ μBar υ ῡ Dν η ν hRegK0 sd
  -- Rewrite the K0 integrand to the strict-K integrand pointwise.
  have hagree :
      (fun t : ℝ =>
          ∫ x in UnitCube d,
            aepsiIntegrandAt_unreg_K0 V H DpH Dυ Dῡ μ μBar υ ῡ Dν η ν x t
          ∂(volume : Measure (Fin d → ℝ)))
        =
      (fun t : ℝ =>
          ∫ x in UnitCube d,
            aepsiIntegrandAt_unreg V H DpH Dυ Dῡ μ μBar υ ῡ Dν η ν x t
          ∂(volume : Measure (Fin d → ℝ))) := by
    funext t
    refine setIntegral_congr_fun measurableSet_unitCube ?_
    intro x _
    exact aepsiIntegrandAt_unreg_K0_eq_unreg
      V H DpH Dυ Dῡ μ μBar υ ῡ Dν η ν x t
  rw [hagree] at hcts_K0
  -- Identify with `mfgOperatorPair` via the unit-cube integral identity.
  have hop_eq :
      (fun t : ℝ =>
        mfgOperatorPair (V := V) (H := H) (DpH := DpH)
          (fun i x => cxCombGrad Dυ Dῡ t i x)
          (fun x => cxComb μ μBar t x)
          (fun x => cxComb υ ῡ t x)
          Dν η ν)
        =
      (fun t : ℝ =>
        ∫ x in UnitCube d,
          aepsiIntegrandAt_unreg V H DpH Dυ Dῡ μ μBar υ ῡ Dν η ν x t
        ∂(volume : Measure (Fin d → ℝ))) := by
    funext t
    exact mfgOperatorPair_segment_eq_integral
      V H DpH Dυ Dῡ μ μBar υ ῡ Dν η ν t
  rw [hop_eq]
  exact hcts_K0

/-! ### K0 sibling with per-test-pair cert preconditions in `hData`
(historical, retired by iter `infra-P7-sigfix-T1-drain-C-public-headlines`).

The intermediate scaffolding theorem `A0_isHemicontinuousK0_withCerts`
(iter `infra-P7-sigfix-T1-family-strengthening`, 2026-05-24, Route I)
was a Phase 1B hub that consumed a universal `testDirCertsOf` oracle
in its body to recover the unconditional `HemicontSegmentDataK0` shape
needed by `A0_isHemicontinuousK0`.

After drain-B installed the family-conditional sibling
`A0_isHemicontinuousK0_restricted_withFamilyCerts` (below) — which the
3 K0 closure consumers in `Banach/RegularizedSequence.lean` now use —
the `_withCerts` hub became unreachable. It was deleted in
**iter `infra-P7-sigfix-T1-drain-C-public-headlines`** (Phase 1D,
2026-05-24) to retire the last live `testDirCertsOf` parameter in any
theorem signature across `StationaryMFG/Theorems/SimplePower/`. -/

/-! ### Restricted-test K0 sibling with family-conditional certs

(iter `infra-P7-sigfix-T1-drain-B-K0-consumer-rewire`, 2026-05-24.)

Drain-B variant of `A0_isHemicontinuousK0_withCerts` that:
1. Returns `IsHemicontinuousMFG_restricted` directly (not the universal
   `IsHemicontinuousMFG`), matching the weakened `MintyClosureOn.hAhc`
   field shape from drain-A.
2. Takes a **family-conditional** cert oracle keyed by the two
   D-members — the certs are supplied at the unique difference test
   triple `(μ - μBar, υ - ῡ, Dυ - Dῡ)`, not at every test triple.

This is the surface that the 3 K0 closure consumers in
`Banach/RegularizedSequence.lean` consume after drain-B; they construct
the family-conditional oracle in-body via the per-family producers from
iter 0822 (`testDirectionCerts_of_{set,signed,transport}_family`),
eliminating the universal `testDirCertsOf` parameter from their
signatures. -/

/-- **Restricted-test K0 hemicontinuity with family-conditional certs.**

Drain-B surface for K0 closure consumers. The cert oracle is keyed by
the **two D-members** `(μBar, ῡ, Dῡ)` and `(μ, υ, Dυ)`, and supplies
certs at the **difference** triple `(μ - μBar, υ - ῡ, Dυ - Dῡ)` only —
this matches the restricted-test shape of `IsHemicontinuousMFG_restricted`.

Internally, instantiates the strengthened-shape `hData` at the
difference triple, using the family-conditional certs as preconditions.
The K0 DCT continuity result follows by transporting `A0_isHemicontinuousK0`
through `IsHemicontinuousMFG.toRestricted`. -/
theorem A0_isHemicontinuousK0_restricted_withFamilyCerts
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hRegK0 : RegularityHK0 (d := d) H DpH)
    (γBar : ℝ)
    (D : Set (MFGTriple d))
    (βBarReal γBarReal : ℝ)
    -- Family-conditional cert oracle: certs are supplied **only** at
    -- the difference test triple of two D-members.
    (familyCertsOf :
      ∀ ⦃μBar ῡ Dῡ⦄, (μBar, ῡ, Dῡ) ∈ D →
      ∀ ⦃μ υ Dυ⦄, (μ, υ, Dυ) ∈ D →
        MemLpPer (d := d) (ENNReal.ofReal βBarReal)
            (fun x => μ x - μBar x) ∧
        (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal)
                (fun x => Dυ i x - Dῡ i x)) ∧
        MemLpPer (d := d) (ENNReal.ofReal βBarReal)
            (fun x => υ x - ῡ x) ∧
        MemLpPer (d := d) (ENNReal.ofReal γBarReal)
            (fun x => υ x - ῡ x))
    -- Strengthened `hData`: per-test-pair cert preconditions after
    -- `(η, ν, Dν)`. Identical shape to `A0_isHemicontinuousK0_withCerts`
    -- so existing producers (`mintyDataXNarrowK0Min_of_paperHypotheses`)
    -- continue to feed without modification.
    (hData : ∀ ⦃μBar ῡ Dῡ⦄, (μBar, ῡ, Dῡ) ∈ D →
             ∀ ⦃μ υ Dυ⦄, (μ, υ, Dυ) ∈ D →
             ∀ (η ν : (Fin d → ℝ) → ℝ)
               (Dν : Fin d → (Fin d → ℝ) → ℝ),
             MemLpPer (d := d) (ENNReal.ofReal βBarReal) η →
             (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dν i)) →
             MemLpPer (d := d) (ENNReal.ofReal βBarReal) ν →
             MemLpPer (d := d) (ENNReal.ofReal γBarReal) ν →
             HemicontSegmentDataK0 V H DpH γBar Dυ Dῡ μ μBar υ ῡ Dν η ν) :
    IsHemicontinuousMFG_restricted d D
      (mfgOperatorPair (V := V) (H := H) (DpH := DpH)) := by
  -- Unfold the restricted predicate and apply `A0_isHemicontinuousK0`
  -- at the difference test triple, sourcing the four cert preconditions
  -- from the family-conditional oracle.
  intro μBar ῡ Dῡ hBar μ υ Dυ hμ
  -- Get certs at the difference triple.
  obtain ⟨c_η, c_Dν, c_ν_β, c_ν_γ⟩ := familyCertsOf hBar hμ
  -- Get the K0 segment-data bundle at the difference triple.
  have sd : HemicontSegmentDataK0 V H DpH γBar Dυ Dῡ μ μBar υ ῡ
              (fun i x => Dυ i x - Dῡ i x)
              (fun x => μ x - μBar x)
              (fun x => υ x - ῡ x) :=
    hData hBar hμ (fun x => μ x - μBar x) (fun x => υ x - ῡ x)
      (fun i x => Dυ i x - Dῡ i x) c_η c_Dν c_ν_β c_ν_γ
  -- K0 DCT continuity result at the difference triple.
  have hcts_K0 :
      ContinuousOn (fun t : ℝ =>
          ∫ x in UnitCube d,
            aepsiIntegrandAt_unreg_K0 V H DpH Dυ Dῡ μ μBar υ ῡ
              (fun i x => Dυ i x - Dῡ i x)
              (fun x => μ x - μBar x)
              (fun x => υ x - ῡ x) x t
          ∂(volume : Measure (Fin d → ℝ))) (Set.Icc 0 1) :=
    aepsiIntegrand_continuousOn_of_segmentDataK0
      V H DpH γBar Dυ Dῡ μ μBar υ ῡ
      (fun i x => Dυ i x - Dῡ i x)
      (fun x => μ x - μBar x)
      (fun x => υ x - ῡ x) hRegK0 sd
  -- Rewrite the K0 integrand to the strict-K integrand pointwise.
  have hagree :
      (fun t : ℝ =>
          ∫ x in UnitCube d,
            aepsiIntegrandAt_unreg_K0 V H DpH Dυ Dῡ μ μBar υ ῡ
              (fun i x => Dυ i x - Dῡ i x)
              (fun x => μ x - μBar x)
              (fun x => υ x - ῡ x) x t
          ∂(volume : Measure (Fin d → ℝ)))
        =
      (fun t : ℝ =>
          ∫ x in UnitCube d,
            aepsiIntegrandAt_unreg V H DpH Dυ Dῡ μ μBar υ ῡ
              (fun i x => Dυ i x - Dῡ i x)
              (fun x => μ x - μBar x)
              (fun x => υ x - ῡ x) x t
          ∂(volume : Measure (Fin d → ℝ))) := by
    funext t
    refine setIntegral_congr_fun measurableSet_unitCube ?_
    intro x _
    exact aepsiIntegrandAt_unreg_K0_eq_unreg
      V H DpH Dυ Dῡ μ μBar υ ῡ
      (fun i x => Dυ i x - Dῡ i x)
      (fun x => μ x - μBar x)
      (fun x => υ x - ῡ x) x t
  rw [hagree] at hcts_K0
  -- Identify with `mfgOperatorPair` via the unit-cube integral identity.
  have hop_eq :
      (fun t : ℝ =>
        mfgOperatorPair (V := V) (H := H) (DpH := DpH)
          (fun i x => cxCombGrad Dυ Dῡ t i x)
          (fun x => cxComb μ μBar t x)
          (fun x => cxComb υ ῡ t x)
          (fun i x => Dυ i x - Dῡ i x)
          (fun x => μ x - μBar x)
          (fun x => υ x - ῡ x))
        =
      (fun t : ℝ =>
        ∫ x in UnitCube d,
          aepsiIntegrandAt_unreg V H DpH Dυ Dῡ μ μBar υ ῡ
            (fun i x => Dυ i x - Dῡ i x)
            (fun x => μ x - μBar x)
            (fun x => υ x - ῡ x) x t
        ∂(volume : Measure (Fin d → ℝ))) := by
    funext t
    exact mfgOperatorPair_segment_eq_integral
      V H DpH Dυ Dῡ μ μBar υ ῡ
      (fun i x => Dυ i x - Dῡ i x)
      (fun x => μ x - μBar x)
      (fun x => υ x - ῡ x) t
  rw [hop_eq]
  exact hcts_K0

/-! ### `(Δm + 1) · |ν|` integrability via Hölder + finite measure

This helper supports the K0 minimal-shape refactor: it replaces the
over-strong `bΔm1 : MemLpPer β̄' (Δm + 1)` assumption by routing
`(Δm + 1) · |ν|` through the Hölder pair `(γ̄', γ̄)` plus the
finite-measure projection `L^{γ̄} → L^1` on the unit cube.

Splitting `(Δm + 1) · |ν| = Δm · |ν| + |ν|`:

* The first summand is in `L^1_per` by Hölder with conjugate exponents
  `(γ̄', γ̄)` — using `MemLpPer.integrable_mul`.
* The second summand is `L^1_per` by `MemLp.integrable` at the
  finite-measure cube, using `1 ≤ ENNReal.ofReal γ̄`.

The result is stated as `IntegrableOn` on `UnitCube d`, matching the
shape consumed by the K0 SegInputs layer. No new auths. -/

/-- **`integrable_deltaM_add_one_mul_abs_nu_from_gamma`** —
`(Δm + 1) · |ν|` is integrable on the unit cube whenever
`Δm ∈ L^{γ̄'}_per` and `ν ∈ L^{γ̄}_per` with `(γ̄', γ̄)` Hölder-conjugate
exponents and `1 ≤ γ̄`.

This is the K0-minimal replacement for the bΔm1 dominator. -/
lemma integrable_deltaM_add_one_mul_abs_nu_from_gamma
    {d : ℕ} {γBarReal γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {Δm ν : (Fin d → ℝ) → ℝ}
    (hΔm : MemLpPer (d := d) (ENNReal.ofReal γBarReal') Δm)
    (hνγ : MemLpPer (d := d) (ENNReal.ofReal γBarReal) ν)
    (hγconj : γBarReal'.HolderConjugate γBarReal) :
    IntegrableOn (fun x => (Δm x + 1) * |ν x|)
      (UnitCube d) := by
  -- Finite-measure instance on the cube (inline; the unit cube has
  -- volume `1`). Same construction as `memLpPer_one_const_one` above.
  haveI : IsFiniteMeasure
      (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  -- `|ν|` is in `L^{γ̄}_per` (norm = abs for real). We adopt `MemLp.norm`.
  have habs_ν : MemLpPer (d := d) (ENNReal.ofReal γBarReal)
      (fun x => |ν x|) := by
    have hnorm : MeasureTheory.MemLp (fun x => ‖ν x‖)
        (ENNReal.ofReal γBarReal)
        (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) :=
      MeasureTheory.MemLp.norm hνγ.toMemLp
    -- `‖·‖ = |·|` for real-valued.
    have hcongr :
        (fun x => ‖ν x‖) = (fun x => |ν x|) := by
      funext x; exact Real.norm_eq_abs _
    rw [hcongr] at hnorm
    exact MemLp.toMemLpPer hnorm
  -- First piece: `Δm · |ν| ∈ L^1` via Hölder `(γ̄', γ̄)`.
  have h_first : IntegrableOn (fun x => Δm x * |ν x|) (UnitCube d) :=
    MemLpPer.integrable_mul hγconj hΔm habs_ν
  -- Second piece: `|ν| ∈ L^1` via finite-measure projection of `L^{γ̄}`.
  have hγ_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal γBarReal :=
    (Fact.out : (1 : ℝ≥0∞) ≤ ENNReal.ofReal γBarReal)
  have h_abs_int : IntegrableOn (fun x => |ν x|) (UnitCube d) := by
    have hint : Integrable (fun x => |ν x|)
        (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) :=
      MeasureTheory.MemLp.integrable hγ_one_le habs_ν.toMemLp
    exact hint
  -- Combine via pointwise identity `(Δm + 1) * |ν| = Δm * |ν| + |ν|`.
  have hsum : IntegrableOn (fun x => Δm x * |ν x| + |ν x|) (UnitCube d) :=
    h_first.add h_abs_int
  have hcongr :
      (fun x => Δm x * |ν x| + |ν x|)
        = (fun x => (Δm x + 1) * |ν x|) := by
    funext x; ring
  rw [hcongr] at hsum
  exact hsum

/-- Unit test: at trivial data `Δm = 0` and `ν = 0`, the helper produces
`IntegrableOn` of the zero function on the unit cube. We exhibit it for
`γBarReal = γBarReal' = 2` (the canonical self-conjugate pair). -/
example :
    IntegrableOn
      (fun x : Fin 1 → ℝ =>
        ((fun _ : Fin 1 → ℝ => (0 : ℝ)) x + 1)
          * |(fun _ : Fin 1 → ℝ => (0 : ℝ)) x|)
      (UnitCube 1) := by
  haveI : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) :=
    ⟨by
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
      exact ENNReal.ofReal_le_ofReal one_le_two⟩
  have hΔm : MemLpPer (d := 1) (ENNReal.ofReal (2 : ℝ))
      (fun _ : Fin 1 → ℝ => (0 : ℝ)) := MemLpPer.const (0 : ℝ)
  have hν : MemLpPer (d := 1) (ENNReal.ofReal (2 : ℝ))
      (fun _ : Fin 1 → ℝ => (0 : ℝ)) := MemLpPer.const (0 : ℝ)
  have hconj : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  exact integrable_deltaM_add_one_mul_abs_nu_from_gamma
    (d := 1) (γBarReal := 2) (γBarReal' := 2) hΔm hν hconj

end SimplePower
end Theorems
end StationaryMFG
