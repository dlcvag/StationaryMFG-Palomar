module

public import StationaryMFG.Solutions.Regularized
public import StationaryMFG.Hamiltonian.Monotone
public import StationaryMFG.Monotone.AbstractWeak
public import StationaryMFG.Monotone.HemicontUpgrade

@[expose] public section

/-!
# `A_ε` is monotone on `𝓚` (paper line 1066)

This module proves the **monotonicity** of the regularized MFG operator
`A_ε` on the convex cone
`𝓚 = L^{β̄}_per(𝕋^d; ℝ⁺_0) × W^{1,γ̄}_per(𝕋^d)` (paper
`Source/FGU-monotone_revised.tex`, line 1066).

## Pairing form

Because `MFGDomain` is a `Set` of *bare-function pairs* (not a Banach
space — see `docs/CONVENTIONS.md` §1b), and `mfgOperatorEpsPair`
returns a real number from a duality pairing, we cannot use the
abstract `IsMonotone` predicate of `Monotone/Operator.lean`
(which expects `A : X → StrongDual ℝ X`). Instead we record the
monotonicity in pairing form: for any two domain points
`(m₁, u₁), (m₂, u₂) ∈ 𝓚`,
```
⟨A_ε[m₁, u₁] - A_ε[m₂, u₂], (m₁, u₁) - (m₂, u₂)⟩ ≥ 0.
```

## Decomposition

Substituting the linear test pair `(η, ν, Dν) = (m₁ - m₂, u₁ - u₂,
Du₁ - Du₂)` into both copies of `mfgOperatorEpsPair` and subtracting,
the `V`-summand and the `(μ - 1) (υ - u)` and `(-υ) η` summands cancel
exactly between the two operators. The remaining integrand is

```
(-H(x, Du₁, m₁) + H(x, Du₂, m₂)) (m₁ - m₂)
   + (m₁ • DpH(x, Du₁, m₁) - m₂ • DpH(x, Du₂, m₂)) ⬝ (Du₁ - Du₂)
+ ε · [ (|Du₁|^{γ̄-2} Du₁ - |Du₂|^{γ̄-2} Du₂) ⬝ (Du₁ - Du₂)
      + (|u₁|^{γ̄-2} u₁ - |u₂|^{γ̄-2} u₂) (u₁ - u₂) ].
```

The Hamiltonian summand is non-negative pointwise by
`HypothesisMonotone.monotone` (paper `(onH.monotone)`, eq. `hmon`).
The Gateaux summand is non-negative pointwise because `t ↦ |t|^{γ̄-2} t`
is monotone for `γ̄ ≥ 1` (it is the subgradient of the convex function
`t ↦ |t|^{γ̄}/γ̄`).

## Pointwise vs. integrated

We package the conclusion as a **pointwise** inequality (integrand
non-negative a.e.). Integrating to a single inequality on
`aepsiPairingDiff` requires integrability of both Hamiltonian and
Gateaux integrands, which is genuinely heavy in the bare-function setup
(it depends on `H, DpH ∈ L^∞`, the gradient family `Du ∈ L^{γ̄}`, etc.).
The pointwise statement is the version actually consumed by Phase 4's
`infra:P4-Aepsi-weak-VI`, which integrates only after multiplying by
the test pair under the joint integrability hypothesis carried in the
`IsWeakSolutionTestPair` admissibility predicate (cf. the strong-
implies-weak proof in `Solutions/StrongImpliesWeak.lean`).

## Predicate inputs

The pointwise monotonicity of the Gateaux integrand —

* scalar: `0 ≤ (|t|^{γ̄-2} t - |s|^{γ̄-2} s) (t - s)` for all `s, t : ℝ`,
* vector: `0 ≤ ((v·v)^{(γ̄-2)/2} v - (w·w)^{(γ̄-2)/2} w) ⬝ (v - w)` for all
  `v, w : Fin d → ℝ`,

— is taken as an *input hypothesis* of the main theorem, named
`hScalarMono` / `hVecMono`. These are mathematical facts (consequences
of the convexity of `t ↦ |t|^{γ̄}/γ̄` on `ℝ` and of the Euclidean norm
power on `ℝ^d`), to be proved in a follow-up task at the level of
`Real.rpow` algebra. Stating the main theorem parametrically in these
hypotheses keeps the proof of `aepsi_isMonotone` self-contained and
unblocks downstream Phase 4 work.

## Paper reference

`Source/FGU-monotone_revised.tex`, line 1066 (sub-bullet
`infra:P4-Aepsi-monotone`).
-/

noncomputable section

namespace StationaryMFG
namespace Theorems
namespace SimplePower

open MeasureTheory Set Filter
open StationaryMFG.Periodic
open StationaryMFG.Hamiltonian
open StationaryMFG.Solutions.MFG
open scoped ENNReal NNReal Topology

variable {d : ℕ}

/-! ## The Lasry–Lions inequality as a standalone predicate

The whole monotone-operator consumer chain below uses the
`HypothesisMonotone` argument **only** through its `monotone` field — the
a.e. Lasry–Lions inequality. We isolate that field's type as a standalone
predicate `LLInequality H DpH`, so that producers (e.g. a carrier-keyed
LL inequality that cannot be packaged into a full `RegularityH` bundle
without a globally-measurable `H`) can feed the chain directly. Existing
`HypothesisMonotone` callers route through `HypothesisMonotone.toLL`
(`= .monotone`). This relaxes only the *carrier* of the hypothesis, never
the LL content itself. -/

/-- The Lasry–Lions a.e. monotonicity inequality for `(H, DpH)` — exactly
the type of the `monotone` field of `HypothesisMonotone`. -/
def LLInequality
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)) : Prop :=
  ∀ᵐ x ∂(volume.restrict (UnitCube d)),
    ∀ p₁ m₁ p₂ m₂, 0 < m₁ → 0 < m₂ →
      0 ≤ (-H x p₁ m₁ + H x p₂ m₂) * (m₁ - m₂)
            + (m₁ • DpH x p₁ m₁ - m₂ • DpH x p₂ m₂) ⬝ (p₁ - p₂)

/-- The `monotone` field of a `HypothesisMonotone` bundle, exposed as an
`LLInequality`. Lets existing callers feed the LL-only chain.

Declared in the `Hamiltonian.HypothesisMonotone` namespace so that
`hMon.toLL` dot-notation resolves for `hMon : HypothesisMonotone …`. -/
theorem _root_.StationaryMFG.Hamiltonian.HypothesisMonotone.toLL
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hMon : StationaryMFG.Hamiltonian.HypothesisMonotone H DpH) :
    LLInequality H DpH :=
  hMon.monotone

/-! ## Pointwise integrands of the Hamiltonian and Gateaux parts -/

/-- The Lasry–Lions pointwise integrand at a point `x`:
`(-H(x, Du₁, m₁) + H(x, Du₂, m₂)) (m₁ - m₂)
+ (m₁ • DpH(x, Du₁, m₁) - m₂ • DpH(x, Du₂, m₂)) ⬝ (Du₁ - Du₂)`. -/
def llPointwise
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (Du₁ Du₂ : Fin d → (Fin d → ℝ) → ℝ)
    (m₁ m₂ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  (-H x (fun i => Du₁ i x) (m₁ x) + H x (fun i => Du₂ i x) (m₂ x))
      * (m₁ x - m₂ x)
    + (m₁ x • DpH x (fun i => Du₁ i x) (m₁ x)
        - m₂ x • DpH x (fun i => Du₂ i x) (m₂ x))
      ⬝ (fun i => Du₁ i x - Du₂ i x)

/-- The `ε`-Gateaux pointwise integrand at a point `x`. -/
def gateauxPointwise
    (γBar : ℝ)
    (Du₁ Du₂ : Fin d → (Fin d → ℝ) → ℝ)
    (u₁ u₂ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  (vecAbsPowMinusTwo γBar (fun i => Du₁ i x) • (fun i => Du₁ i x)
        - vecAbsPowMinusTwo γBar (fun i => Du₂ i x) • (fun i => Du₂ i x))
      ⬝ (fun i => Du₁ i x - Du₂ i x)
    + (absPowMinusTwo γBar (u₁ x) * u₁ x
        - absPowMinusTwo γBar (u₂ x) * u₂ x) * (u₁ x - u₂ x)

/-! ## Pointwise non-negativity of the Hamiltonian integrand -/

/-- **Pointwise Lasry–Lions inequality at the test pair**
`(Du₁, m₁), (Du₂, m₂)` for a.e. `x`. The integrand `llPointwise` is
non-negative whenever both densities are strictly positive at `x` and
the Hamiltonian satisfies `(onH.monotone)` (the LL inequality `(hmon)`).

Proof: this is the LL inequality `(hmon)` applied at
`(p₁, m₁) = (Du₁ x, m₁ x), (p₂, m₂) = (Du₂ x, m₂ x)`, after
identifying the dot-product summand
`(m₁ • DpH₁ - m₂ • DpH₂) ⬝ (Du₁ - Du₂)` with the LL second summand. -/
theorem llPointwise_nonneg_ae
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hLL : LLInequality H DpH)
    (Du₁ Du₂ : Fin d → (Fin d → ℝ) → ℝ)
    (m₁ m₂ : (Fin d → ℝ) → ℝ)
    (hpos₁ : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m₁ x)
    (hpos₂ : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m₂ x) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      0 ≤ llPointwise H DpH Du₁ Du₂ m₁ m₂ x := by
  refine ((hLL.and hpos₁).and hpos₂).mono ?_
  rintro x ⟨⟨hxMon, hxm₁⟩, hxm₂⟩
  -- Specialize the LL inequality at the test points.
  have hLL := hxMon (fun i => Du₁ i x) (m₁ x) (fun i => Du₂ i x) (m₂ x)
                hxm₁ hxm₂
  -- `hLL : 0 ≤ (-H₁ + H₂)(m₁ - m₂) + (m₁ • DpH₁ - m₂ • DpH₂) ⬝ (Du₁ - Du₂)`.
  -- The dot-product entry uses the function-difference `Du₁ - Du₂` as a
  -- Pi function. Convert to the `(fun i => Du₁ i x - Du₂ i x)` form.
  have hsub :
      ((fun i => Du₁ i x) - fun i => Du₂ i x : Fin d → ℝ)
        = fun i => Du₁ i x - Du₂ i x := by
    funext i; simp [Pi.sub_apply]
  rw [hsub] at hLL
  exact hLL

/-! ## Pointwise non-negativity of the ε-Gateaux integrand -/

/-- **Pointwise Gateaux monotonicity inequality at `x`**, given the two
abstract pointwise monotonicities of `t ↦ |t|^{γ̄-2} t`. -/
theorem gateauxPointwise_nonneg
    {γBar : ℝ}
    (hScalarMono :
      ∀ s t : ℝ,
        0 ≤ (absPowMinusTwo γBar t * t - absPowMinusTwo γBar s * s)
              * (t - s))
    (hVecMono :
      ∀ v w : Fin d → ℝ,
        0 ≤ (vecAbsPowMinusTwo γBar v • v - vecAbsPowMinusTwo γBar w • w)
              ⬝ (v - w))
    (Du₁ Du₂ : Fin d → (Fin d → ℝ) → ℝ)
    (u₁ u₂ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    0 ≤ gateauxPointwise γBar Du₁ Du₂ u₁ u₂ x := by
  unfold gateauxPointwise
  -- Apply `hVecMono` at `v = Du₁ x`, `w = Du₂ x`, after rewriting
  -- `(fun i => Du₁ i x - Du₂ i x) = (fun i => Du₁ i x) - (fun i => Du₂ i x)`.
  have hsub :
      ((fun i => Du₁ i x) - fun i => Du₂ i x : Fin d → ℝ)
        = fun i => Du₁ i x - Du₂ i x := by
    funext i; simp [Pi.sub_apply]
  have hVec := hVecMono (fun i => Du₁ i x) (fun i => Du₂ i x)
  rw [hsub] at hVec
  have hScalar := hScalarMono (u₂ x) (u₁ x)
  exact add_nonneg hVec hScalar

/-! ## The pairing-difference (statement form) -/

/-- The **pairing-difference** of `A_ε` evaluated on the linear test pair
`(m₁ - m₂, u₁ - u₂, Du₁ - Du₂)`:
```
⟨A_ε[m₁, u₁] - A_ε[m₂, u₂], (m₁, u₁) - (m₂, u₂)⟩.
```
This is the explicit algebraic quantity whose pointwise integrand is
shown here to be non-negative; the corresponding integral inequality
(monotonicity of `A_ε` on `𝓚`) follows by integrating, given joint
integrability hypotheses (deferred to the consumer). -/
def aepsiPairingDiff
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (γBar ε : ℝ)
    (Du₁ Du₂ : Fin d → (Fin d → ℝ) → ℝ)
    (m₁ u₁ m₂ u₂ : (Fin d → ℝ) → ℝ) : ℝ :=
  mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH) γBar ε Du₁ m₁ u₁
      (fun i x => Du₁ i x - Du₂ i x) (m₁ - m₂) (u₁ - u₂)
    - mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH) γBar ε Du₂ m₂ u₂
        (fun i x => Du₁ i x - Du₂ i x) (m₁ - m₂) (u₁ - u₂)

/-! ## Main: pointwise non-negativity of the pairing-difference integrand -/

/-- **`A_ε` is monotone on `𝓚` — pointwise integrand form (paper line 1066).**

Under `(onH.monotone)` for the Hamiltonian and the standard pointwise
monotonicities of `t ↦ |t|^{γ̄-2} t` (vector and scalar), the integrand
of the pairing-difference
`⟨A_ε[m₁, u₁] - A_ε[m₂, u₂], (m₁, u₁) - (m₂, u₂)⟩`
is non-negative for almost every `x`, provided `m₁, m₂` are strictly
positive a.e. (paper hypothesis "essinf m > 0", encoded as the
`InMFGOperatorDomain` admissibility) and `0 ≤ ε`.

The conclusion of the paper at line 1066 — non-negativity of the
**integrated** pairing — follows by integrating the pointwise inequality
under joint integrability of the integrands; see the file docstring for
why we keep that step at the consumer. -/
theorem aepsi_pointwise_monotone
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBar ε : ℝ}
    (hMon : LLInequality H DpH)
    (hε : 0 ≤ ε)
    (hScalarMono :
      ∀ s t : ℝ,
        0 ≤ (absPowMinusTwo γBar t * t - absPowMinusTwo γBar s * s)
              * (t - s))
    (hVecMono :
      ∀ v w : Fin d → ℝ,
        0 ≤ (vecAbsPowMinusTwo γBar v • v - vecAbsPowMinusTwo γBar w • w)
              ⬝ (v - w))
    (Du₁ Du₂ : Fin d → (Fin d → ℝ) → ℝ)
    (m₁ u₁ m₂ u₂ : (Fin d → ℝ) → ℝ)
    (hpos₁ : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m₁ x)
    (hpos₂ : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m₂ x) :
    let _ := V
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      0 ≤ llPointwise H DpH Du₁ Du₂ m₁ m₂ x
            + ε * gateauxPointwise γBar Du₁ Du₂ u₁ u₂ x := by
  -- Combine the two pointwise non-negativities.
  have hLL := llPointwise_nonneg_ae hMon Du₁ Du₂ m₁ m₂ hpos₁ hpos₂
  refine hLL.mono ?_
  intro x hLLx
  have hG := gateauxPointwise_nonneg (γBar := γBar)
              hScalarMono hVecMono Du₁ Du₂ u₁ u₂ x
  have hε_g : 0 ≤ ε * gateauxPointwise γBar Du₁ Du₂ u₁ u₂ x :=
    mul_nonneg hε hG
  linarith

/-! ## Algebraic decomposition of `aepsiPairingDiff`

The pairing-difference of `A_ε` evaluated on the linear test pair
`(m₁ - m₂, u₁ - u₂, Du₁ - Du₂)` decomposes algebraically into the
integral of `llPointwise + ε · gateauxPointwise`. The `V` summand and
the cross terms `(-υ)·η`, `(μ - 1)·ν` cancel exactly between the two
operators (the cancellation happens *before* integrating, so this is
just a pointwise identity on the integrands plus integral-additivity).

Concretely, the unfolded difference reduces to the integral of the
combined pointwise integrand `llPointwise + ε · gateauxPointwise`. -/

/-- **Pointwise integrand identity** for `aepsiPairingDiff`. Before any
integration, the integrand of
`mfgOperatorEpsPair γBar ε V H DpH Du₁ m₁ u₁ Dν η ν - mfgOperatorEpsPair
γBar ε V H DpH Du₂ m₂ u₂ Dν η ν` at the linear test pair `(η, ν, Dν) =
(m₁ - m₂, u₁ - u₂, Du₁ - Du₂)` equals
`llPointwise H DpH Du₁ Du₂ m₁ m₂ x + ε · gateauxPointwise γBar Du₁ Du₂
u₁ u₂ x` for every `x`. -/
lemma aepsiPairingDiff_integrand_eq
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (γBar ε : ℝ)
    (Du₁ Du₂ : Fin d → (Fin d → ℝ) → ℝ)
    (m₁ u₁ m₂ u₂ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    ((-(u₁ x) - H x (fun i => Du₁ i x) (m₁ x) + V x) * ((m₁ - m₂) x)
        + m₁ x * (DpH x (fun i => Du₁ i x) (m₁ x)
                    ⬝ (fun i => Du₁ i x - Du₂ i x))
        + (m₁ x - 1) * ((u₁ - u₂) x))
      - ((-(u₂ x) - H x (fun i => Du₂ i x) (m₂ x) + V x) * ((m₁ - m₂) x)
          + m₂ x * (DpH x (fun i => Du₂ i x) (m₂ x)
                      ⬝ (fun i => Du₁ i x - Du₂ i x))
          + (m₂ x - 1) * ((u₁ - u₂) x))
      + ε *
        ((vecAbsPowMinusTwo γBar (fun i => Du₁ i x)
              * ((fun i => Du₁ i x) ⬝ (fun i => Du₁ i x - Du₂ i x))
            + absPowMinusTwo γBar (u₁ x) * (u₁ x * ((u₁ - u₂) x)))
          - (vecAbsPowMinusTwo γBar (fun i => Du₂ i x)
              * ((fun i => Du₂ i x) ⬝ (fun i => Du₁ i x - Du₂ i x))
            + absPowMinusTwo γBar (u₂ x) * (u₂ x * ((u₁ - u₂) x))))
      = llPointwise H DpH Du₁ Du₂ m₁ m₂ x
          + ε * gateauxPointwise γBar Du₁ Du₂ u₁ u₂ x := by
  -- Both sides are explicit algebraic expressions; expand `llPointwise`,
  -- `gateauxPointwise`, the dot products and the `Pi.sub_apply`s, then
  -- normalise with `Finset.sum_sub_distrib` and `ring`.
  unfold llPointwise gateauxPointwise dotProduct
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  -- Normalize: push the `m_i x` factor inside the LHS dot-product sums.
  have hL_mfg₁ :
      m₁ x * ∑ i, DpH x (fun j => Du₁ j x) (m₁ x) i * (Du₁ i x - Du₂ i x)
        = ∑ i, m₁ x * (DpH x (fun j => Du₁ j x) (m₁ x) i * (Du₁ i x - Du₂ i x)) :=
    Finset.mul_sum _ _ _
  have hL_mfg₂ :
      m₂ x * ∑ i, DpH x (fun j => Du₂ j x) (m₂ x) i * (Du₁ i x - Du₂ i x)
        = ∑ i, m₂ x * (DpH x (fun j => Du₂ j x) (m₂ x) i * (Du₁ i x - Du₂ i x)) :=
    Finset.mul_sum _ _ _
  -- And distribute `vecAbsPowMinusTwo` over its dot-product sum.
  have hL_g₁ :
      vecAbsPowMinusTwo γBar (fun j => Du₁ j x)
            * ∑ i, Du₁ i x * (Du₁ i x - Du₂ i x)
        = ∑ i, vecAbsPowMinusTwo γBar (fun j => Du₁ j x)
                  * (Du₁ i x * (Du₁ i x - Du₂ i x)) :=
    Finset.mul_sum _ _ _
  have hL_g₂ :
      vecAbsPowMinusTwo γBar (fun j => Du₂ j x)
            * ∑ i, Du₂ i x * (Du₁ i x - Du₂ i x)
        = ∑ i, vecAbsPowMinusTwo γBar (fun j => Du₂ j x)
                  * (Du₂ i x * (Du₁ i x - Du₂ i x)) :=
    Finset.mul_sum _ _ _
  rw [hL_mfg₁, hL_mfg₂, hL_g₁, hL_g₂]
  -- Combine the two pairs of `Finset.sum`s on the LHS into two combined sums
  -- via `Finset.sum_sub_distrib`, matching the shape of the RHS.
  have hSum_mfg :
      (∑ i, m₁ x * (DpH x (fun j => Du₁ j x) (m₁ x) i * (Du₁ i x - Du₂ i x)))
          - (∑ i, m₂ x * (DpH x (fun j => Du₂ j x) (m₂ x) i * (Du₁ i x - Du₂ i x)))
        = ∑ i, (m₁ x * DpH x (fun j => Du₁ j x) (m₁ x) i
                  - m₂ x * DpH x (fun j => Du₂ j x) (m₂ x) i)
                * (Du₁ i x - Du₂ i x) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hSum_g :
      (∑ i, vecAbsPowMinusTwo γBar (fun j => Du₁ j x)
              * (Du₁ i x * (Du₁ i x - Du₂ i x)))
          - (∑ i, vecAbsPowMinusTwo γBar (fun j => Du₂ j x)
              * (Du₂ i x * (Du₁ i x - Du₂ i x)))
        = ∑ i, (vecAbsPowMinusTwo γBar (fun j => Du₁ j x) * Du₁ i x
                  - vecAbsPowMinusTwo γBar (fun j => Du₂ j x) * Du₂ i x)
                * (Du₁ i x - Du₂ i x) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  -- Use `linear_combination` or expand the LHS into the combined sums.
  -- Strategy: name the two sum-differences `S_mfg`, `S_g`; isolate them.
  set S_mfg₁ : ℝ :=
    ∑ i, m₁ x * (DpH x (fun j => Du₁ j x) (m₁ x) i * (Du₁ i x - Du₂ i x))
  set S_mfg₂ : ℝ :=
    ∑ i, m₂ x * (DpH x (fun j => Du₂ j x) (m₂ x) i * (Du₁ i x - Du₂ i x))
  set S_g₁ : ℝ :=
    ∑ i, vecAbsPowMinusTwo γBar (fun j => Du₁ j x)
            * (Du₁ i x * (Du₁ i x - Du₂ i x))
  set S_g₂ : ℝ :=
    ∑ i, vecAbsPowMinusTwo γBar (fun j => Du₂ j x)
            * (Du₂ i x * (Du₁ i x - Du₂ i x))
  set T_mfg : ℝ :=
    ∑ i, (m₁ x * DpH x (fun j => Du₁ j x) (m₁ x) i
            - m₂ x * DpH x (fun j => Du₂ j x) (m₂ x) i)
            * (Du₁ i x - Du₂ i x)
  set T_g : ℝ :=
    ∑ i, (vecAbsPowMinusTwo γBar (fun j => Du₁ j x) * Du₁ i x
            - vecAbsPowMinusTwo γBar (fun j => Du₂ j x) * Du₂ i x)
            * (Du₁ i x - Du₂ i x)
  -- Now the LHS uses `S_mfg₁, S_mfg₂, S_g₁, S_g₂`, and the RHS uses
  -- `T_mfg, T_g`. The bridge: `S_mfg₁ - S_mfg₂ = T_mfg`, `S_g₁ - S_g₂ = T_g`.
  have hSmfg : S_mfg₁ - S_mfg₂ = T_mfg := hSum_mfg
  have hSg : S_g₁ - S_g₂ = T_g := hSum_g
  linear_combination hSmfg + ε * hSg

/-- **Algebraic decomposition** of `aepsiPairingDiff`. Under joint
integrability of the two integrands (the `mfgOperatorPair`-integrand
on each side, and the `gateauxWpPair`-integrand on each side), the
pairing-difference equals the integral of the combined pointwise
integrand `llPointwise + ε · gateauxPointwise`.

The integrability hypotheses match those carried in the consumer's
`MFGOpEpsAuxHyps` bundle / `IsWeakSolutionTestPair` admissibility. -/
theorem aepsiPairingDiff_eq_LL_plus_eps
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (γBar ε : ℝ)
    (Du₁ Du₂ : Fin d → (Fin d → ℝ) → ℝ)
    (m₁ u₁ m₂ u₂ : (Fin d → ℝ) → ℝ)
    -- Integrability of the four integrands at the linear test pair.
    (hI_mfg₁ : IntegrableOn
      (fun x =>
        (-(u₁ x) - H x (fun i => Du₁ i x) (m₁ x) + V x) * ((m₁ - m₂) x)
          + m₁ x * (DpH x (fun i => Du₁ i x) (m₁ x)
                      ⬝ (fun i => Du₁ i x - Du₂ i x))
          + (m₁ x - 1) * ((u₁ - u₂) x))
      (UnitCube d))
    (hI_mfg₂ : IntegrableOn
      (fun x =>
        (-(u₂ x) - H x (fun i => Du₂ i x) (m₂ x) + V x) * ((m₁ - m₂) x)
          + m₂ x * (DpH x (fun i => Du₂ i x) (m₂ x)
                      ⬝ (fun i => Du₁ i x - Du₂ i x))
          + (m₂ x - 1) * ((u₁ - u₂) x))
      (UnitCube d))
    (hI_g₁ : IntegrableOn
      (fun x =>
        vecAbsPowMinusTwo γBar (fun i => Du₁ i x)
              * ((fun i => Du₁ i x) ⬝ (fun i => Du₁ i x - Du₂ i x))
          + absPowMinusTwo γBar (u₁ x) * (u₁ x * ((u₁ - u₂) x)))
      (UnitCube d))
    (hI_g₂ : IntegrableOn
      (fun x =>
        vecAbsPowMinusTwo γBar (fun i => Du₂ i x)
              * ((fun i => Du₂ i x) ⬝ (fun i => Du₁ i x - Du₂ i x))
          + absPowMinusTwo γBar (u₂ x) * (u₂ x * ((u₁ - u₂) x)))
      (UnitCube d)) :
    aepsiPairingDiff V H DpH γBar ε Du₁ Du₂ m₁ u₁ m₂ u₂
      = ∫ x in UnitCube d,
          (llPointwise H DpH Du₁ Du₂ m₁ m₂ x
            + ε * gateauxPointwise γBar Du₁ Du₂ u₁ u₂ x)
        ∂(volume : Measure (Fin d → ℝ)) := by
  -- Unfold `aepsiPairingDiff` to expose the four integrals.
  unfold aepsiPairingDiff mfgOperatorEpsPair mfgOperatorPair gateauxWpPair
  -- Combine the four integrals into a single integral via `integral_sub`
  -- and `integral_add`.
  rw [show
      (∫ x in UnitCube d,
          (-(u₁ x) - H x (fun i => Du₁ i x) (m₁ x) + V x) * ((m₁ - m₂) x)
            + m₁ x * (DpH x (fun i => Du₁ i x) (m₁ x)
                        ⬝ (fun i => Du₁ i x - Du₂ i x))
            + (m₁ x - 1) * ((u₁ - u₂) x)
          ∂(volume : Measure (Fin d → ℝ)))
        + ε *
            (∫ x in UnitCube d,
              vecAbsPowMinusTwo γBar (fun i => Du₁ i x)
                    * ((fun i => Du₁ i x) ⬝ (fun i => Du₁ i x - Du₂ i x))
                + absPowMinusTwo γBar (u₁ x) * (u₁ x * ((u₁ - u₂) x))
              ∂(volume : Measure (Fin d → ℝ)))
        - ((∫ x in UnitCube d,
            (-(u₂ x) - H x (fun i => Du₂ i x) (m₂ x) + V x) * ((m₁ - m₂) x)
              + m₂ x * (DpH x (fun i => Du₂ i x) (m₂ x)
                          ⬝ (fun i => Du₁ i x - Du₂ i x))
              + (m₂ x - 1) * ((u₁ - u₂) x)
            ∂(volume : Measure (Fin d → ℝ)))
          + ε *
              (∫ x in UnitCube d,
                vecAbsPowMinusTwo γBar (fun i => Du₂ i x)
                      * ((fun i => Du₂ i x) ⬝ (fun i => Du₁ i x - Du₂ i x))
                  + absPowMinusTwo γBar (u₂ x) * (u₂ x * ((u₁ - u₂) x))
                ∂(volume : Measure (Fin d → ℝ))))
      = (∫ x in UnitCube d,
          (-(u₁ x) - H x (fun i => Du₁ i x) (m₁ x) + V x) * ((m₁ - m₂) x)
            + m₁ x * (DpH x (fun i => Du₁ i x) (m₁ x)
                        ⬝ (fun i => Du₁ i x - Du₂ i x))
            + (m₁ x - 1) * ((u₁ - u₂) x)
          ∂(volume : Measure (Fin d → ℝ)))
        - (∫ x in UnitCube d,
            (-(u₂ x) - H x (fun i => Du₂ i x) (m₂ x) + V x) * ((m₁ - m₂) x)
              + m₂ x * (DpH x (fun i => Du₂ i x) (m₂ x)
                          ⬝ (fun i => Du₁ i x - Du₂ i x))
              + (m₂ x - 1) * ((u₁ - u₂) x)
            ∂(volume : Measure (Fin d → ℝ)))
        + ε *
            ((∫ x in UnitCube d,
              vecAbsPowMinusTwo γBar (fun i => Du₁ i x)
                    * ((fun i => Du₁ i x) ⬝ (fun i => Du₁ i x - Du₂ i x))
                + absPowMinusTwo γBar (u₁ x) * (u₁ x * ((u₁ - u₂) x))
              ∂(volume : Measure (Fin d → ℝ)))
            - (∫ x in UnitCube d,
                vecAbsPowMinusTwo γBar (fun i => Du₂ i x)
                      * ((fun i => Du₂ i x) ⬝ (fun i => Du₁ i x - Du₂ i x))
                  + absPowMinusTwo γBar (u₂ x) * (u₂ x * ((u₁ - u₂) x))
                ∂(volume : Measure (Fin d → ℝ)))) from by ring]
  -- Combine each pair of integrals.
  rw [← MeasureTheory.integral_sub hI_mfg₁ hI_mfg₂,
      ← MeasureTheory.integral_sub hI_g₁ hI_g₂]
  -- Combine the two-summand integral via `integral_add` (on the
  -- difference integrals).
  have hI_mfg_diff : IntegrableOn
      (fun x =>
        ((-(u₁ x) - H x (fun i => Du₁ i x) (m₁ x) + V x) * ((m₁ - m₂) x)
          + m₁ x * (DpH x (fun i => Du₁ i x) (m₁ x)
                      ⬝ (fun i => Du₁ i x - Du₂ i x))
          + (m₁ x - 1) * ((u₁ - u₂) x))
        - ((-(u₂ x) - H x (fun i => Du₂ i x) (m₂ x) + V x) * ((m₁ - m₂) x)
          + m₂ x * (DpH x (fun i => Du₂ i x) (m₂ x)
                      ⬝ (fun i => Du₁ i x - Du₂ i x))
          + (m₂ x - 1) * ((u₁ - u₂) x))) (UnitCube d) := hI_mfg₁.sub hI_mfg₂
  have hI_g_diff : IntegrableOn
      (fun x =>
        (vecAbsPowMinusTwo γBar (fun i => Du₁ i x)
              * ((fun i => Du₁ i x) ⬝ (fun i => Du₁ i x - Du₂ i x))
          + absPowMinusTwo γBar (u₁ x) * (u₁ x * ((u₁ - u₂) x)))
        - (vecAbsPowMinusTwo γBar (fun i => Du₂ i x)
              * ((fun i => Du₂ i x) ⬝ (fun i => Du₁ i x - Du₂ i x))
          + absPowMinusTwo γBar (u₂ x) * (u₂ x * ((u₁ - u₂) x))))
      (UnitCube d) := hI_g₁.sub hI_g₂
  -- The `ε * (·)` factor scales the second integral.
  rw [show
        ε * ∫ x in UnitCube d,
              (vecAbsPowMinusTwo γBar (fun i => Du₁ i x)
                    * ((fun i => Du₁ i x) ⬝ (fun i => Du₁ i x - Du₂ i x))
                + absPowMinusTwo γBar (u₁ x) * (u₁ x * ((u₁ - u₂) x)))
              - (vecAbsPowMinusTwo γBar (fun i => Du₂ i x)
                    * ((fun i => Du₂ i x) ⬝ (fun i => Du₁ i x - Du₂ i x))
                + absPowMinusTwo γBar (u₂ x) * (u₂ x * ((u₁ - u₂) x)))
            ∂(volume : Measure (Fin d → ℝ))
        = ∫ x in UnitCube d,
            ε * ((vecAbsPowMinusTwo γBar (fun i => Du₁ i x)
                      * ((fun i => Du₁ i x) ⬝ (fun i => Du₁ i x - Du₂ i x))
                  + absPowMinusTwo γBar (u₁ x) * (u₁ x * ((u₁ - u₂) x)))
                - (vecAbsPowMinusTwo γBar (fun i => Du₂ i x)
                      * ((fun i => Du₂ i x) ⬝ (fun i => Du₁ i x - Du₂ i x))
                  + absPowMinusTwo γBar (u₂ x) * (u₂ x * ((u₁ - u₂) x))))
            ∂(volume : Measure (Fin d → ℝ)) from
        (MeasureTheory.integral_const_mul ε _).symm]
  -- Combine the two single integrals.
  rw [← MeasureTheory.integral_add hI_mfg_diff (hI_g_diff.const_mul ε)]
  -- Pointwise integrand identity.
  refine setIntegral_congr_fun measurableSet_unitCube ?_
  intro x _
  exact aepsiPairingDiff_integrand_eq V H DpH γBar ε Du₁ Du₂ m₁ u₁ m₂ u₂ x

/-! ## Integrated form of the monotonicity inequality

The integrated counterpart of `aepsi_pointwise_monotone`: under the
same hypotheses plus integrability of the four integrands, the
pairing-difference is non-negative. -/

/-- **Integrated monotonicity of `A_ε`** (paper line 1066, integrated
form). Under the pointwise monotonicity hypotheses
(`HypothesisMonotone H DpH`, `0 ≤ ε`, `hScalarMono`, `hVecMono`) and
integrability of the two `mfgOperatorPair`-integrands and two
`gateauxWpPair`-integrands at the linear test pair, plus a.e.
positivity of the densities `m₁, m₂`, we have
`0 ≤ aepsiPairingDiff …`. -/
theorem aepsi_isMonotone_integrated
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBar ε : ℝ}
    (hMon : LLInequality H DpH)
    (hε : 0 ≤ ε)
    (hScalarMono :
      ∀ s t : ℝ,
        0 ≤ (absPowMinusTwo γBar t * t - absPowMinusTwo γBar s * s)
              * (t - s))
    (hVecMono :
      ∀ v w : Fin d → ℝ,
        0 ≤ (vecAbsPowMinusTwo γBar v • v - vecAbsPowMinusTwo γBar w • w)
              ⬝ (v - w))
    {Du₁ Du₂ : Fin d → (Fin d → ℝ) → ℝ}
    {m₁ u₁ m₂ u₂ : (Fin d → ℝ) → ℝ}
    (hpos₁ : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m₁ x)
    (hpos₂ : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m₂ x)
    (hI_mfg₁ : IntegrableOn
      (fun x =>
        (-(u₁ x) - H x (fun i => Du₁ i x) (m₁ x) + V x) * ((m₁ - m₂) x)
          + m₁ x * (DpH x (fun i => Du₁ i x) (m₁ x)
                      ⬝ (fun i => Du₁ i x - Du₂ i x))
          + (m₁ x - 1) * ((u₁ - u₂) x))
      (UnitCube d))
    (hI_mfg₂ : IntegrableOn
      (fun x =>
        (-(u₂ x) - H x (fun i => Du₂ i x) (m₂ x) + V x) * ((m₁ - m₂) x)
          + m₂ x * (DpH x (fun i => Du₂ i x) (m₂ x)
                      ⬝ (fun i => Du₁ i x - Du₂ i x))
          + (m₂ x - 1) * ((u₁ - u₂) x))
      (UnitCube d))
    (hI_g₁ : IntegrableOn
      (fun x =>
        vecAbsPowMinusTwo γBar (fun i => Du₁ i x)
              * ((fun i => Du₁ i x) ⬝ (fun i => Du₁ i x - Du₂ i x))
          + absPowMinusTwo γBar (u₁ x) * (u₁ x * ((u₁ - u₂) x)))
      (UnitCube d))
    (hI_g₂ : IntegrableOn
      (fun x =>
        vecAbsPowMinusTwo γBar (fun i => Du₂ i x)
              * ((fun i => Du₂ i x) ⬝ (fun i => Du₁ i x - Du₂ i x))
          + absPowMinusTwo γBar (u₂ x) * (u₂ x * ((u₁ - u₂) x)))
      (UnitCube d)) :
    0 ≤ aepsiPairingDiff V H DpH γBar ε Du₁ Du₂ m₁ u₁ m₂ u₂ := by
  rw [aepsiPairingDiff_eq_LL_plus_eps V H DpH γBar ε Du₁ Du₂ m₁ u₁ m₂ u₂
        hI_mfg₁ hI_mfg₂ hI_g₁ hI_g₂]
  -- The integrand is non-negative a.e. by `aepsi_pointwise_monotone`.
  have hpt := aepsi_pointwise_monotone (V := V) (H := H) (DpH := DpH)
              (γBar := γBar) (ε := ε)
              hMon hε hScalarMono hVecMono Du₁ Du₂ m₁ u₁ m₂ u₂ hpos₁ hpos₂
  exact MeasureTheory.integral_nonneg_of_ae hpt

/-! ## Sanity checks -/

/-- **Unit test (integrated)**: at the trivial Hamiltonian `H = 0,
DpH = 0`, with `Du₁ = Du₂ = 0`, `m₁ = m₂ = 1`, `u₁ = u₂ = 0`, and
`V = 0`, the `aepsiPairingDiff` is identically zero. -/
example {γBar ε : ℝ} :
    aepsiPairingDiff (d := d)
        (fun _ : Fin d → ℝ => (0 : ℝ))
        (fun _ _ _ => (0 : ℝ))
        (fun _ _ _ => (0 : Fin d → ℝ))
        γBar ε
        (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ))
        (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ))
        (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ))
      = 0 := by
  unfold aepsiPairingDiff mfgOperatorEpsPair mfgOperatorPair gateauxWpPair
    dotProduct
  simp

/-! ## Convexity and (sequential) norm-closedness of `𝓚`

Phase-4 infrastructure: the MFG cone
`𝓚 = MFGDomain betaBar gammaBar = L^{betaBar}_per(𝕋^d; ℝ⁺_0) ×
W^{1,gammaBar}_per(𝕋^d)` is convex and norm-closed. Convexity is a
re-export of `MFGDomain.convex`. Norm-closedness is phrased as
**sequential closedness in the `L^{betaBar}`-seminorm of the
m-component**: a sequence `(m_n, u_n) ∈ 𝓚` whose densities
converge in `L^{betaBar}` to a `MemLpPer betaBar` limit `m`, and
whose value functions all admit a `MemSobolevPer gammaBar` limit `u`,
yields `(m, u) ∈ 𝓚`. The substantive step is closedness of the
non-negative cone: `m_n ≥ 0` a.e. and `eLpNormPer betaBar (m_n - m) → 0`
imply `m ≥ 0` a.e., via convergence in measure plus an a.e.-convergent
subsequence.

Following `docs/CONVENTIONS.md` §1b, elements of `𝓚` are bare-function
pairs and `𝓚` carries no `TopologicalSpace` instance (this is by design
of the project). The sequential statement below is the practical
incarnation of "norm-closed in `L^{betaBar}_per × W^{1,gammaBar}_per`"
that downstream Phase 4 work consumes (cf. `infra:P4-coerc-identity`,
`infra:P4-weak-seq-compact-reflexive`).
-/

/-- **Convexity of `𝓚`** (Phase-4 alias). Re-export of
`MFGDomain.convex` under the SimplePower namespace. -/
theorem K_convex {betaBar gammaBar : ℝ≥0∞}
    (hβ : 1 ≤ betaBar) (hγ : 1 ≤ gammaBar) :
    Convex ℝ (MFGDomain (d := d) betaBar gammaBar) :=
  MFGDomain.convex hβ hγ

/-- **Sequential norm-closedness of `𝓚`** (Phase-4).

Suppose `(m_n, u_n) ∈ MFGDomain betaBar gammaBar` for every `n`, and
that:

* the candidate limit `m` satisfies `MemLpPer betaBar m`,
* the candidate limit `u` satisfies `MemSobolevPer gammaBar u`, and
* `eLpNormPer betaBar (m_n - m) → 0` (i.e. `m_n → m` in
  `L^{betaBar}_per`).

Then `(m, u) ∈ MFGDomain betaBar gammaBar`. The exponent constraint is
`betaBar ≠ 0`, used to invoke
`MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm`.

The proof uses convergence in measure on the unit cube and extracts an
a.e.-convergent subsequence; pointwise non-negativity is preserved
along the subsequence, hence in the limit.

-- Adapted from LpSpaces.EgorovLusinScheffe (the
-- `tendsto_ae_of_tendsto_eLpNormOn` strategy), specialised to the
-- cube-restricted measure. -/
theorem K_isClosed {betaBar gammaBar : ℝ≥0∞} (hβ : betaBar ≠ 0)
    {m_n : ℕ → (Fin d → ℝ) → ℝ} {u_n : ℕ → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    (hmem : ∀ n, (m_n n, u_n n) ∈ MFGDomain (d := d) betaBar gammaBar)
    (hLp : MemLpPer betaBar m) (hSob : MemSobolevPer gammaBar u)
    (hconv :
      Filter.Tendsto (fun n => eLpNormPer betaBar (m_n n - m))
        Filter.atTop (𝓝 0)) :
    (m, u) ∈ MFGDomain (d := d) betaBar gammaBar := by
  refine ⟨hLp, hSob, ?_⟩
  -- Convergence in `L^{betaBar}` ⇒ convergence in measure on the unit cube.
  have hMeas : ∀ n, AEStronglyMeasurable (m_n n)
      (Measure.restrict volume (UnitCube d)) := fun n => (hmem n).1.1
  have hMeas_m : AEStronglyMeasurable m
      (Measure.restrict volume (UnitCube d)) := hLp.1
  -- `eLpNormPer = eLpNorm _ _ (volume.restrict _)`, definitional.
  have hconv' :
      Filter.Tendsto
        (fun n => MeasureTheory.eLpNorm (m_n n - m) betaBar
          (Measure.restrict volume (UnitCube d)))
        Filter.atTop (𝓝 0) := hconv
  have hInMeas :
      MeasureTheory.TendstoInMeasure
        (Measure.restrict volume (UnitCube d)) m_n Filter.atTop m :=
    MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm
      (p := betaBar) hβ hconv'
  -- Extract an a.e.-convergent subsequence.
  obtain ⟨ns, _hns_mono, hae⟩ := hInMeas.exists_seq_tendsto_ae
  -- Each `m_(ns i) ≥ 0` a.e.; combined with the a.e. limit identity
  -- `m_(ns i) x → m x`, this gives `0 ≤ m x` a.e.
  have hpos_seq : ∀ i, 0 ≤ᵐ[Measure.restrict volume (UnitCube d)] m_n (ns i) :=
    fun i => (hmem (ns i)).2.2
  -- Combine: a.e.-eventually `0 ≤ m_(ns i) x` (from the per-i hypothesis,
  -- via countable a.e.-intersection) and a.e. `m_(ns i) x → m x`.
  have hpos_all :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ∀ i, 0 ≤ m_n (ns i) x :=
    (MeasureTheory.ae_all_iff).2 hpos_seq
  -- Conclude `0 ≤ m x` a.e. from the limit `m_(ns i) x → m x`.
  filter_upwards [hpos_all, hae] with x hxpos hxlim
  -- `hxpos : ∀ i, 0 ≤ m_(ns i) x`; `hxlim : m_(ns i) x → m x` along `i`.
  exact ge_of_tendsto' hxlim hxpos

/-! ## Sanity checks -/

/-- **Unit test**: at the trivial Hamiltonian `H = 0, DpH = 0`, with
`Du₁ = Du₂ = 0`, `m₁ = m₂ = 1`, `u₁ = u₂ = 0`, the LL integrand
vanishes pointwise. -/
example :
    ∀ x : Fin d → ℝ,
      llPointwise (d := d)
          (fun (_ : Fin d → ℝ) (_ : Fin d → ℝ) (_ : ℝ) => (0 : ℝ))
          (fun (_ : Fin d → ℝ) (_ : Fin d → ℝ) (_ : ℝ) => (0 : Fin d → ℝ))
          (fun _ _ => 0) (fun _ _ => 0)
          (fun _ => 1) (fun _ => 1) x
        = 0 := by
  intro x
  unfold llPointwise dotProduct
  simp

/-- **Unit test**: at `Du₁ = Du₂ = 0`, `u₁ = u₂ = 0`, the Gateaux
integrand vanishes pointwise. -/
example {γBar : ℝ} :
    ∀ x : Fin d → ℝ,
      gateauxPointwise (d := d) γBar
          (fun _ _ => 0) (fun _ _ => 0)
          (fun _ => 0) (fun _ => 0) x
        = 0 := by
  intro x
  unfold gateauxPointwise vecAbsPowMinusTwo absPowMinusTwo dotProduct
  simp

/-- **Unit test**: the LL integrand at `Du₁ = Du₂` and `m₁ = m₂` is
identically `0`. -/
example
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (Du : Fin d → (Fin d → ℝ) → ℝ) (m : (Fin d → ℝ) → ℝ) :
    ∀ x : Fin d → ℝ,
      llPointwise H DpH Du Du m m x = 0 := by
  intro x
  unfold llPointwise
  -- `(- H + H)(m - m) + (m • DpH - m • DpH) ⬝ (Du - Du) = 0`.
  have h1 :
      (-H x (fun i => Du i x) (m x) + H x (fun i => Du i x) (m x))
          * (m x - m x) = 0 := by ring
  have h2 :
      (m x • DpH x (fun i => Du i x) (m x)
          - m x • DpH x (fun i => Du i x) (m x)) = 0 := by
    funext i; simp
  have h3 :
      (0 : Fin d → ℝ) ⬝ (fun i => Du i x - Du i x) = 0 := by
    unfold dotProduct; simp
  rw [h2]
  rw [h3]
  rw [h1]
  ring

/-- **Unit test**: `K_convex` is a `Convex ℝ`-statement at extended exponents
`betaBar = gammaBar = 2`. -/
example : Convex ℝ (MFGDomain (d := d) (2 : ℝ≥0∞) (2 : ℝ≥0∞)) :=
  K_convex (by norm_num) (by norm_num)

/-! ## Weak variational inequality for `A_ε` (paper line 1068, eq. `eq:Aepsi.weak.ineq`)

This is `infra:P4-Aepsi-weak-VI`: apply `paper:thm:monotone.abstract-weak`
(Phase 3, `monotone_abstract_weak`) to the pair `(𝓚, A_ε)` to obtain
`(m_ε, u_ε)` such that
`⟨A_ε[m_ε, u_ε], (μ, υ) - (m_ε, u_ε)⟩ ≥ 0` for every `(μ, υ) ∈ 𝓚`.

### Bridge-parameterised wrapper

The bare-function pairing `mfgOperatorEpsPair` is *not* a continuous
linear functional on a Banach space — the underlying space of pair
functions `((Fin d → ℝ) → ℝ) × ((Fin d → ℝ) → ℝ)` carries no
`NormedAddCommGroup` instance in this project (see
`docs/CONVENTIONS.md` §1b: "We bridge to Mathlib's `MeasureTheory.Lp`
… **locally**, in the module that needs it, not project-wide"). The
docstring of `coercAepsi` (Coercivity.lean line 1257) explicitly says
the Banach-side bridge is "deferred to a sibling task".

Until that sibling task lands, `weakVI_Aepsi` is delivered as a
**bridge-parameterised wrapper**: it consumes a Banach-space realization
`(X, K, A)` of the bare-function operator together with the abstract
hypotheses (monotonicity, coercivity, convexity, reflexivity, and the
`FiniteConvexHullWeakVI` typeclass) and produces the abstract weak VI
on `X`. The downstream consumer (`infra:P4-Aepsi-strong-VI`,
hemicontinuous upgrade) takes the same abstract conclusion as input,
so all that's parametrically deferred is the construction of the
bridge `(X, realize, A)` itself.

This is exactly the application of `paper:thm:monotone.abstract-weak`
to `(𝓚, A_ε)`: every Banach realization of `(𝓚, A_ε)` produces, via
this lemma, the weak VI. -/

/-- **Weak variational inequality for `A_ε` on `𝓚`** (paper line 1068,
`eq:Aepsi.weak.ineq`).

A direct application of `monotone_abstract_weak` (Browder–Minty) to a
Banach realization `(X, K, A)` of the regularized MFG pair `(𝓚, A_ε)`.
The hypotheses correspond exactly to the three Phase-4 inputs:

* `hA_mono` — monotonicity of `A` on `K`, supplied by
  `infra:P4-Aepsi-monotone` after bridging.
* `hA_coerc` — coercivity of `A` on `K` at some `v₀`, supplied by
  `paper:prop:coercAepsi` after bridging.
* `hK_cvx` — convexity of `K`, supplied by `infra:P4-K-convex-closed`
  after bridging.

The conclusion is `∃ u ∈ closure K, ∀ v ∈ K, 0 ≤ A v (v - u)`, which is
the abstract weak VI. With `A` and `K` instantiated to the bridged
`A_ε`/`𝓚`, this is exactly paper eq. `eq:Aepsi.weak.ineq`. -/
theorem weakVI_Aepsi
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [Monotone.FiniteConvexHullWeakVI X]
    (hX : Periodic.IsReflexiveNormedSpace X)
    {K : Set X} (hK_cvx : Convex ℝ K)
    {A : X → StrongDual ℝ X}
    (hA_mono : Monotone.IsMonotone K A)
    {v₀ : X} (hA_coerc : Monotone.IsCoerciveAt K A v₀) :
    ∃ u ∈ closure K, ∀ v ∈ K, 0 ≤ A v (v - u) :=
  Monotone.monotone_abstract_weak hX hK_cvx hA_mono hA_coerc

/-- **Unit test for `weakVI_Aepsi`** (`ε = 1`, trivial 1D bridge).

For the trivial Banach realization `X := ℝ`, `K := {0}`, `A := 0`,
`v₀ := 0`, the hypotheses are vacuous (singleton domain ⇒ coercivity is
trivial; the zero operator is monotone). The conclusion is the trivial
VI `0 ≤ 0` at `u = 0`. This corresponds to applying `weakVI_Aepsi` at
the degenerate ε-regularized operator collapsed to the origin. -/
example
    [Monotone.FiniteConvexHullWeakVI ℝ]
    (hℝ : Periodic.IsReflexiveNormedSpace ℝ) :
    ∃ u ∈ closure ({0} : Set ℝ), ∀ v ∈ ({0} : Set ℝ),
      0 ≤ (fun _ => (0 : StrongDual ℝ ℝ)) v (v - u) :=
  weakVI_Aepsi (X := ℝ) hℝ
    (K := ({0} : Set ℝ))
    (convex_singleton 0)
    (A := fun _ => (0 : StrongDual ℝ ℝ))
    (Monotone.isMonotone_zero _)
    (v₀ := 0)
    (Monotone.isCoerciveAt_of_bounded_domain Bornology.isBounded_singleton _ rfl)

/-! ## Strong variational inequality for `A_ε` (paper line 1080,
eq. `eq:Aepsistrongineq`)

This is `infra:P4-Aepsi-strong-VI`: combine the weak VI
(`weakVI_Aepsi`, paper line 1068, eq. `eq:Aepsi.weak.ineq`) with
hemicontinuity (`paper:lem:hemicont`) via the hemicontinuous upgrade
(`paper:rmk:hemicontinuous-upgrade`,
`StationaryMFG/Monotone/HemicontUpgrade.lean`). The upgraded conclusion
is `⟨A_ε[m_ε, u_ε], (μ, υ) - (m_ε, u_ε)⟩ ≥ 0` for every
`(μ, υ) ∈ 𝓚`, where the operator is evaluated at the solution itself
rather than at the test point.

### Bridge-parameterised wrapper

As with `weakVI_Aepsi`, we deliver the conclusion abstractly on a
Banach realization `(X, K, A)` of the bare-function pair `(𝓚, A_ε)`.
The hemicontinuous upgrade requires the witness to lie in `K` itself
(not merely in `closure K`); to obtain this from `weakVI_Aepsi`, we
additionally consume `IsClosed K` (paper "𝓚 is convex and closed"),
so that `closure K = K`. The upgrade lemma
`Monotone.hemicont_upgrade` then turns the weak VI into the strong
one. -/

/-- **Strong variational inequality for `A_ε` on `𝓚`** (paper line 1080,
`eq:Aepsistrongineq`).

A bridge-parameterised wrapper that combines:

* `weakVI_Aepsi` (paper `eq:Aepsi.weak.ineq`), which produces a witness
  `u ∈ closure K` satisfying the weak VI `∀ v ∈ K, 0 ≤ A v (v - u)`.
* The closedness of `K` (`IsClosed K`), which lifts the witness to
  `u ∈ K`.
* `Monotone.hemicont_upgrade`
  (paper `rmk:hemicontinuous-upgrade`), which turns the weak VI into
  the strong VI `∀ v ∈ K, 0 ≤ A u (v - u)` once `u ∈ K`.

The hypotheses correspond exactly to the four Phase-4 inputs:

* `hA_mono` — monotonicity of `A` on `K`, supplied by
  `infra:P4-Aepsi-monotone` after bridging.
* `hA_coerc` — coercivity of `A` on `K` at some `v₀`, supplied by
  `paper:prop:coercAepsi` after bridging.
* `hK_cvx`, `hK_closed` — convexity and closedness of `K`, supplied by
  `infra:P4-K-convex-closed` after bridging.
* `hA_hemicont` — hemicontinuity of `A` on `K`, supplied by
  `paper:lem:hemicont` after bridging.

The conclusion is `∃ u ∈ K, ∀ v ∈ K, 0 ≤ A u (v - u)`, the abstract
strong VI. With `A` and `K` instantiated to the bridged `A_ε`/`𝓚`,
this is exactly paper eq. `eq:Aepsistrongineq`. -/
theorem strongVI_Aepsi
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [Monotone.FiniteConvexHullWeakVI X]
    (hX : Periodic.IsReflexiveNormedSpace X)
    {K : Set X} (hK_cvx : Convex ℝ K) (hK_closed : IsClosed K)
    {A : X → StrongDual ℝ X}
    (hA_mono : Monotone.IsMonotone K A)
    (hA_hemicont : Monotone.IsHemicontinuous K A)
    {v₀ : X} (hA_coerc : Monotone.IsCoerciveAt K A v₀) :
    ∃ u ∈ K, ∀ v ∈ K, 0 ≤ A u (v - u) := by
  -- Step 1: Apply the weak VI from `weakVI_Aepsi` (Browder-Minty).
  obtain ⟨u, hu_cl, hweak⟩ :=
    weakVI_Aepsi (X := X) hX (K := K) hK_cvx
      (A := A) hA_mono (v₀ := v₀) hA_coerc
  -- Step 2: Lift `u ∈ closure K` to `u ∈ K` via closedness.
  have hu_K : u ∈ K := by
    rwa [hK_closed.closure_eq] at hu_cl
  -- Step 3: Upgrade weak VI to strong VI via hemicontinuity.
  refine ⟨u, hu_K, ?_⟩
  intro v hv
  -- `hweak : ∀ v ∈ K, 0 ≤ A v (v - u)` (binder unfolded).
  have hweak' : ∀ ⦃w⦄, w ∈ K → 0 ≤ A w (w - u) := fun w hw => hweak w hw
  exact Monotone.hemicont_upgrade hK_cvx hA_hemicont hu_K hweak' hv

/-- **Unit test for `strongVI_Aepsi`** (`ε = 1`, trivial 1D bridge).

For the trivial Banach realization `X := ℝ`, `K := {0}`, `A := 0`,
`v₀ := 0`, the hypotheses are vacuous (singleton domain ⇒ coercivity is
trivial; the zero operator is monotone and hemicontinuous; `{0}` is
both convex and closed). The conclusion is the trivial strong VI
`0 ≤ 0` at `u = 0`. -/
example
    [Monotone.FiniteConvexHullWeakVI ℝ]
    (hℝ : Periodic.IsReflexiveNormedSpace ℝ) :
    ∃ u ∈ ({0} : Set ℝ), ∀ v ∈ ({0} : Set ℝ),
      0 ≤ (fun _ => (0 : StrongDual ℝ ℝ)) u (v - u) :=
  strongVI_Aepsi (X := ℝ) hℝ
    (K := ({0} : Set ℝ))
    (convex_singleton 0)
    (isClosed_singleton)
    (A := fun _ => (0 : StrongDual ℝ ℝ))
    (Monotone.isMonotone_zero _)
    (Monotone.isHemicontinuous_zero _)
    (v₀ := 0)
    (Monotone.isCoerciveAt_of_bounded_domain Bornology.isBounded_singleton _ rfl)

/-! ## Aggregator: existence of a regularized solution
(paper `thm:strongAepsi`, lines 1046–1058)

This is the paper-named theorem `thm:strongAepsi` (Proposition
"Existence of a Regularized Solution"): for every `ε > 0` there exists
`(m_ε, u_ε) ∈ 𝓚` such that
```
⟨A_ε[m_ε, u_ε], (μ, υ) - (m_ε, u_ε)⟩ ≥ 0,    ∀ (μ, υ) ∈ 𝓚.
```

The aggregator is a one-line re-export of the bridge-parameterised
`strongVI_Aepsi` declared above. The four abstract Phase-4 inputs —
monotonicity, hemicontinuity, coercivity, and convexity-with-closedness
of `K` — are quantified universally, exactly as in the children
`infra:P4-Aepsi-weak-VI` and `infra:P4-Aepsi-strong-VI`. With `(X, K, A,
v₀)` instantiated to a concrete Banach realization of the bare-function
pair `(𝓚, A_ε)`, this is paper eq. `eq:Aepsistrongineq`. -/

/-- **Existence of a regularized solution** (paper `thm:strongAepsi`,
line 1046, eq. `eq:Aepsistrongineq`).

Bridge-parameterised aggregator: under the assumptions of the simple
power-growth main theorem (Assumption `onH.monotone` and Assumption
`onH.powergrowth`, which feed the abstract monotonicity and
hemicontinuity inputs `hA_mono`, `hA_hemicont`; Proposition
`prop:coercAepsi`, which feeds `hA_coerc`; and convexity-and-closedness
of `𝓚`, which feed `hK_cvx`, `hK_closed`), and given a Banach
realization `(X, K, A)` of the regularized MFG pair `(𝓚, A_ε)`, there
exists `u ∈ K` such that
```
∀ v ∈ K,    0 ≤ A u (v - u).
```

This is a pure aggregator: the proof is a one-line invocation of
`strongVI_Aepsi`. The renaming to `thm_strongAepsi` matches the paper's
proposition label and is intended as the public, downstream-facing
entry point. -/
theorem thm_strongAepsi
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [Monotone.FiniteConvexHullWeakVI X]
    (hX : Periodic.IsReflexiveNormedSpace X)
    {K : Set X} (hK_cvx : Convex ℝ K) (hK_closed : IsClosed K)
    {A : X → StrongDual ℝ X}
    (hA_mono : Monotone.IsMonotone K A)
    (hA_hemicont : Monotone.IsHemicontinuous K A)
    {v₀ : X} (hA_coerc : Monotone.IsCoerciveAt K A v₀) :
    ∃ u ∈ K, ∀ v ∈ K, 0 ≤ A u (v - u) :=
  strongVI_Aepsi (X := X) hX hK_cvx hK_closed
    (A := A) hA_mono hA_hemicont (v₀ := v₀) hA_coerc

/-- **Alias** for `thm_strongAepsi` matching the alternative name from
the task spec. Same bridge-parameterised signature; same conclusion. -/
theorem existsStrongVI_Aepsi
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [Monotone.FiniteConvexHullWeakVI X]
    (hX : Periodic.IsReflexiveNormedSpace X)
    {K : Set X} (hK_cvx : Convex ℝ K) (hK_closed : IsClosed K)
    {A : X → StrongDual ℝ X}
    (hA_mono : Monotone.IsMonotone K A)
    (hA_hemicont : Monotone.IsHemicontinuous K A)
    {v₀ : X} (hA_coerc : Monotone.IsCoerciveAt K A v₀) :
    ∃ u ∈ K, ∀ v ∈ K, 0 ≤ A u (v - u) :=
  thm_strongAepsi (X := X) hX hK_cvx hK_closed
    (A := A) hA_mono hA_hemicont (v₀ := v₀) hA_coerc

/-- **Unit test for `thm_strongAepsi`** (`ε = 1`, trivial 1D bridge).

For the trivial Banach realization `X := ℝ`, `K := {0}`, `A := 0`,
`v₀ := 0`, the hypotheses are vacuous and the conclusion is the
trivial strong VI `0 ≤ 0` at `u = 0`. -/
example
    [Monotone.FiniteConvexHullWeakVI ℝ]
    (hℝ : Periodic.IsReflexiveNormedSpace ℝ) :
    ∃ u ∈ ({0} : Set ℝ), ∀ v ∈ ({0} : Set ℝ),
      0 ≤ (fun _ => (0 : StrongDual ℝ ℝ)) u (v - u) :=
  thm_strongAepsi (X := ℝ) hℝ
    (K := ({0} : Set ℝ))
    (convex_singleton 0)
    (isClosed_singleton)
    (A := fun _ => (0 : StrongDual ℝ ℝ))
    (Monotone.isMonotone_zero _)
    (Monotone.isHemicontinuous_zero _)
    (v₀ := 0)
    (Monotone.isCoerciveAt_of_bounded_domain Bornology.isBounded_singleton _ rfl)

end SimplePower
end Theorems
end StationaryMFG
