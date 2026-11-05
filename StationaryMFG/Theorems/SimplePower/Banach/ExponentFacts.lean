module

public import StationaryMFG.Hamiltonian.Assumptions
public import Mathlib.Data.Real.ConjExponents
public import Mathlib.Data.ENNReal.Basic
public import Mathlib.Data.ENNReal.Real

@[expose] public section

/-!
# Exponent sanity bundle for the simple power-growth Theorem 1

This module discharges Phase-4 rebuild task **T0 — exponent sanity check**
(see `docs/TASKS/in_flight/infra-P4-rebuild-T0-exponent-sanity.md`). Its
purpose is to *isolate* the type-level exponent constraints used by the
paper's headline theorem
(`Source/FGU-monotone_revised.tex`, line 314,
`thm:main-simple.power.growth`) into a single record
`SimplePowerExponentFacts γBar betaBar gammaBar betaBar'`, so that
downstream Banach-bridge tasks can thread the constraints uniformly.

## Paper formulas (`eq:gamma`, line 489–493)

Given the simple-power-growth Hamiltonian parameters `α > 1` and
`β > 0` from `HypothesisPowerGrowth`, the paper sets

```
β̄ = β + 1                          (eq:gamma)
γ̄ = α (β + 1) / β                  (eq:gamma)
β̄' = β̄ / (β̄ - 1) = (β+1) / β      (Hölder conjugate of β̄)
γ̄' = γ̄ / (γ̄ - 1)                  (Hölder conjugate of γ̄)
```

with the identity `γ̄ = α β̄'`. These exponents serve as the targets of
the existence statement: `m ∈ L^{β̄}_per`, `u ∈ W^{1,γ̄}_per`,
`V ∈ L^{β̄'}_per`. The Hölder conjugacies are used pervasively in the
Banach-bridge chain.

## Diagnostic finding (rebuild task T0)

`HypothesisPowerGrowth H DpH` carries `α, β : ℝ` as *bundle data*; in
contrast, the headline theorem
`thm_main_simplePowerGrowth_concrete` declares
`{γBar : ℝ} {betaBar gammaBar betaBar' : ℝ≥0∞}` as *implicit
type-level parameters*. Those parameters are bound by the surrounding
`{…}` binders and are completely independent of the concrete `α, β` in
`HypothesisPowerGrowth`. Consequently, **no producer theorem of the
form**

```lean
theorem simplePowerExponentFacts_of_powerGrowth
    {γBar : ℝ} {betaBar gammaBar betaBar' : ℝ≥0∞}
    (hpow : HypothesisPowerGrowth H DpH) :
    SimplePowerExponentFacts γBar betaBar gammaBar betaBar'
```

**is provable**: the goal involves variables that simply do not occur
in the hypothesis. The fix is to either (a) add the exponent fields to
`HypothesisPowerGrowth` itself, or (b) thread
`(hExp : SimplePowerExponentFacts γBar betaBar gammaBar betaBar')` as
an explicit hypothesis to the headline theorem. See the task file for
the full discussion.

This module ships:

* `SimplePowerExponentFacts` — the bundle definition.
* `SimplePowerExponentFacts.standardPaper` — the canonical constructor
  given `(α, β)` with `1 < α` and `0 < β`.
* Sanity-check `example`s exercising the constructor at the standard
  paper exponents `α = 2, β = 1` (so `β̄ = 2, γ̄ = 4, β̄' = 2`).
-/

namespace StationaryMFG
namespace Theorems
namespace SimplePower

open scoped ENNReal

/-- **Paper exponent bundle for Theorem 1.**

`SimplePowerExponentFacts γBar betaBar gammaBar betaBar'` packages the
type-level constraints on the auxiliary exponents that the paper's
headline existence theorem (line 314, `thm:main-simple.power.growth`)
silently assumes via `eq:gamma` (line 489–493).

The fields:

* `betaBar`, `gammaBar`, `betaBar'` are `ℝ≥0∞`-valued exponents that
  index `L^p_per` and `W^{1,p}_per` spaces; they are required to be
  strictly between `1` and `⊤` for the spaces to be reflexive Banach
  spaces (and for Hölder conjugacy to make sense).
* `γBar : ℝ` is the `ℝ`-valued companion of `gammaBar`, used wherever
  the proof reaches for `Real.HolderConjugate γBar γBar'`.
* `βConj` and `γConj` are the two Hölder-conjugacy facts used in the
  Banach-bridge chain (Hölder pairings, dual identifications). The
  conjugacy is stated on the `ℝ`-valued projections via
  `ℝ≥0∞.toReal`. -/
structure SimplePowerExponentFacts
    (γBar : ℝ)
    (betaBar gammaBar betaBar' : ℝ≥0∞) : Prop where
  /-- `1 < β̄` — needed for `L^{β̄}_per` to be reflexive. -/
  βBar_one_lt : 1 < betaBar
  /-- `β̄ < ⊤` — needed for `L^{β̄}_per` to be a genuine `L^p`. -/
  βBar_lt_top : betaBar < ⊤
  /-- `1 < γ̄` (the `ℝ≥0∞` version) — needed for `W^{1,γ̄}_per`
  reflexivity. -/
  gammaBar_one_lt : 1 < gammaBar
  /-- `γ̄ < ⊤` — needed for `W^{1,γ̄}_per` to be a genuine Sobolev space. -/
  gammaBar_lt_top : gammaBar < ⊤
  /-- `1 < β̄'` — the conjugate of `β̄` is a valid `L^p` exponent. -/
  betaBar'_one_lt : 1 < betaBar'
  /-- `β̄' < ⊤` — the conjugate of `β̄` is finite. -/
  betaBar'_lt_top : betaBar' < ⊤
  /-- `γBar` (real-valued) is `> 1`. -/
  γBar_one_lt_real : 1 < γBar
  /-- The `ℝ`-valued `γBar` is the `toReal` of the `ℝ≥0∞`-valued
  `gammaBar`. -/
  γBar_eq_toReal : γBar = gammaBar.toReal
  /-- Hölder conjugacy between `β̄` (real-valued) and `β̄'`
  (real-valued). -/
  βConj : Real.HolderConjugate betaBar.toReal betaBar'.toReal
  /-- Hölder conjugacy between `γ̄` (real-valued) and the implicit
  `γ̄'`, threaded as `γBar`'s conjugate by way of `Real.conjExponent`. -/
  γConj : Real.HolderConjugate gammaBar.toReal (gammaBar.toReal /
    (gammaBar.toReal - 1))

namespace SimplePowerExponentFacts

/-- The real-valued projection `β̄ : ℝ` derived from the bundle. -/
def betaBarReal {γBar : ℝ} {betaBar gammaBar betaBar' : ℝ≥0∞}
    (_ : SimplePowerExponentFacts γBar betaBar gammaBar betaBar') : ℝ :=
  betaBar.toReal

/-- The real-valued projection `β̄' : ℝ` derived from the bundle. -/
def betaBarPrimeReal {γBar : ℝ} {betaBar gammaBar betaBar' : ℝ≥0∞}
    (_ : SimplePowerExponentFacts γBar betaBar gammaBar betaBar') : ℝ :=
  betaBar'.toReal

/-- `β̄ : ℝ` is strictly greater than `1`. -/
lemma one_lt_betaBarReal {γBar : ℝ} {betaBar gammaBar betaBar' : ℝ≥0∞}
    (h : SimplePowerExponentFacts γBar betaBar gammaBar betaBar') :
    1 < betaBar.toReal := h.βConj.lt

/-- `β̄' : ℝ` is strictly greater than `1`. -/
lemma one_lt_betaBarPrimeReal {γBar : ℝ}
    {betaBar gammaBar betaBar' : ℝ≥0∞}
    (h : SimplePowerExponentFacts γBar betaBar gammaBar betaBar') :
    1 < betaBar'.toReal := h.βConj.symm.lt

end SimplePowerExponentFacts

/-! ### Canonical constructor at paper formulas

Given Hamiltonian growth parameters `α > 1` and `β > 0` from
`HypothesisPowerGrowth`, the paper formulas (`eq:gamma`, line 489–493)
read

```
β̄ = β + 1
γ̄ = α (β + 1) / β
β̄' = β̄ / (β̄ - 1) = (β + 1) / β
```

These are the *standard* exponents at which Theorem 1 lives. The
constructor below takes `(α, β)` and produces the corresponding
`SimplePowerExponentFacts` bundle on the canonical exponents. -/

namespace SimplePowerExponentFacts

/-- The paper's `β̄`, as an `ℝ≥0∞`. -/
@[simp] noncomputable def paperBetaBar (β : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (β + 1)

/-- The paper's `γ̄`, as an `ℝ≥0∞`. -/
@[simp] noncomputable def paperGammaBar (α β : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (α * (β + 1) / β)

/-- The paper's `β̄'`, as an `ℝ≥0∞`. -/
@[simp] noncomputable def paperBetaBarPrime (β : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((β + 1) / β)

/-- The paper's `γ̄`, as an `ℝ`. -/
@[simp] noncomputable def paperGammaBarReal (α β : ℝ) : ℝ :=
  α * (β + 1) / β

/-- `paperBetaBar β = β + 1` after `toReal` for `0 < β`. -/
lemma toReal_paperBetaBar {β : ℝ} (hβ : 0 < β) :
    (paperBetaBar β).toReal = β + 1 := by
  unfold paperBetaBar
  exact ENNReal.toReal_ofReal (by linarith)

/-- `paperGammaBar α β = α (β + 1) / β` after `toReal` for `1 < α`,
`0 < β`. -/
lemma toReal_paperGammaBar {α β : ℝ} (hα : 1 < α) (hβ : 0 < β) :
    (paperGammaBar α β).toReal = α * (β + 1) / β := by
  unfold paperGammaBar
  refine ENNReal.toReal_ofReal ?_
  have h1 : 0 < α := lt_trans zero_lt_one hα
  have h2 : 0 < β + 1 := by linarith
  exact le_of_lt (div_pos (mul_pos h1 h2) hβ)

/-- `paperBetaBarPrime β = (β + 1) / β` after `toReal` for `0 < β`. -/
lemma toReal_paperBetaBarPrime {β : ℝ} (hβ : 0 < β) :
    (paperBetaBarPrime β).toReal = (β + 1) / β := by
  unfold paperBetaBarPrime
  refine ENNReal.toReal_ofReal ?_
  have h2 : 0 < β + 1 := by linarith
  exact le_of_lt (div_pos h2 hβ)

/-- The Hölder conjugacy `(β + 1).HolderConjugate ((β + 1) / β)` at
the paper exponents (`β̄` vs. `β̄'`). -/
lemma paper_holderConjugate_betaBar {β : ℝ} (hβ : 0 < β) :
    Real.HolderConjugate (β + 1) ((β + 1) / β) := by
  rw [Real.holderConjugate_iff]
  refine ⟨by linarith, ?_⟩
  -- 1/(β+1) + β/(β+1) = (1+β)/(β+1) = 1
  have hβ1 : (0 : ℝ) < β + 1 := by linarith
  have hβ1ne : β + 1 ≠ 0 := ne_of_gt hβ1
  have hβne : β ≠ 0 := ne_of_gt hβ
  have hdiv : ((β + 1) / β)⁻¹ = β / (β + 1) := by
    field_simp
  rw [hdiv]
  field_simp
  ring

/-- The Hölder conjugacy for `γ̄`: `γ̄.HolderConjugate (γ̄ / (γ̄ - 1))`,
which holds whenever `γ̄ > 1`. -/
lemma paper_holderConjugate_gammaBar {α β : ℝ} (hα : 1 < α) (hβ : 0 < β) :
    Real.HolderConjugate (α * (β + 1) / β)
      (α * (β + 1) / β / (α * (β + 1) / β - 1)) := by
  -- Reduce to the standard `Real.HolderConjugate.conjExponent` once
  -- we know `1 < α (β+1) / β`.
  have hα0 : 0 < α := lt_trans zero_lt_one hα
  have hβ1 : 0 < β + 1 := by linarith
  have hpos : 0 < α * (β + 1) / β := div_pos (mul_pos hα0 hβ1) hβ
  -- Show `1 < α (β+1) / β`. Equivalent to `β < α (β + 1) = αβ + α`.
  -- Since `α > 1` and `β + 1 > 1` (as `β > 0`), the product `α (β+1) > β + 1 > β`.
  have h_one_lt : 1 < α * (β + 1) / β := by
    rw [lt_div_iff₀ hβ, one_mul]
    -- Goal: β < α * (β + 1).
    -- α (β + 1) = α β + α > β + α > β  (using α > 1 ⇒ αβ ≥ β if β ≥ 0,
    --   but more directly α (β+1) > 1·(β+1) = β + 1 > β).
    have h1 : (β + 1) < α * (β + 1) := by
      have : (1 : ℝ) * (β + 1) < α * (β + 1) :=
        mul_lt_mul_of_pos_right hα hβ1
      simpa using this
    linarith
  -- Now use Real.HolderConjugate.conjExponent.
  have := Real.HolderConjugate.conjExponent (p := α * (β + 1) / β) h_one_lt
  -- Rewrite the conjugate exponent `α (β+1) / β / (α (β+1) / β - 1)`.
  -- `Real.conjExponent p = p / (p - 1)`.
  unfold Real.conjExponent at this
  exact this

/-- **Canonical paper constructor.** Given Hamiltonian growth
parameters `α > 1` and `β > 0` (the data fields of
`HypothesisPowerGrowth`), produce `SimplePowerExponentFacts` at the
paper-mandated exponents

```
γBar = α (β + 1) / β
betaBar = β + 1
gammaBar = α (β + 1) / β
betaBar' = (β + 1) / β
```

This is the constructor downstream tasks should use to obtain a
`SimplePowerExponentFacts` once they have access to the
`HypothesisPowerGrowth` data fields `(hpow.α, hpow.β, hpow.hα,
hpow.hβ)`. -/
noncomputable def standardPaper {α β : ℝ} (hα : 1 < α) (hβ : 0 < β) :
    SimplePowerExponentFacts (paperGammaBarReal α β) (paperBetaBar β)
      (paperGammaBar α β) (paperBetaBarPrime β) := by
  have hα0 : 0 < α := lt_trans zero_lt_one hα
  have hβ1 : 0 < β + 1 := by linarith
  refine
    { βBar_one_lt := ?_
      βBar_lt_top := ?_
      gammaBar_one_lt := ?_
      gammaBar_lt_top := ?_
      betaBar'_one_lt := ?_
      betaBar'_lt_top := ?_
      γBar_one_lt_real := ?_
      γBar_eq_toReal := ?_
      βConj := ?_
      γConj := ?_ }
  · -- 1 < ofReal (β + 1).
    unfold paperBetaBar
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from
        (ENNReal.ofReal_one).symm]
    exact (ENNReal.ofReal_lt_ofReal_iff hβ1).mpr (by linarith)
  · -- ofReal (β + 1) < ⊤.
    unfold paperBetaBar
    exact ENNReal.ofReal_lt_top
  · -- 1 < ofReal (α (β+1)/β).
    unfold paperGammaBar
    have h_one_lt : 1 < α * (β + 1) / β := by
      rw [lt_div_iff₀ hβ, one_mul]
      have : (β + 1) < α * (β + 1) := by
        have : (1 : ℝ) * (β + 1) < α * (β + 1) :=
          mul_lt_mul_of_pos_right hα hβ1
        simpa using this
      linarith
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from
        (ENNReal.ofReal_one).symm]
    exact (ENNReal.ofReal_lt_ofReal_iff
      (div_pos (mul_pos hα0 hβ1) hβ)).mpr h_one_lt
  · -- ofReal (α (β+1)/β) < ⊤.
    unfold paperGammaBar
    exact ENNReal.ofReal_lt_top
  · -- 1 < ofReal ((β+1)/β).
    unfold paperBetaBarPrime
    have h_one_lt : 1 < (β + 1) / β := by
      rw [lt_div_iff₀ hβ, one_mul]
      linarith
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from
        (ENNReal.ofReal_one).symm]
    exact (ENNReal.ofReal_lt_ofReal_iff
      (div_pos hβ1 hβ)).mpr h_one_lt
  · -- ofReal ((β+1)/β) < ⊤.
    unfold paperBetaBarPrime
    exact ENNReal.ofReal_lt_top
  · -- 1 < α (β+1) / β  (real-valued).
    unfold paperGammaBarReal
    rw [lt_div_iff₀ hβ, one_mul]
    have : (β + 1) < α * (β + 1) := by
      have : (1 : ℝ) * (β + 1) < α * (β + 1) :=
        mul_lt_mul_of_pos_right hα hβ1
      simpa using this
    linarith
  · -- γBar = (paperGammaBar α β).toReal.
    unfold paperGammaBarReal paperGammaBar
    rw [ENNReal.toReal_ofReal]
    exact le_of_lt (div_pos (mul_pos hα0 hβ1) hβ)
  · -- Hölder conjugacy on β̄, β̄'.
    rw [toReal_paperBetaBar hβ, toReal_paperBetaBarPrime hβ]
    exact paper_holderConjugate_betaBar hβ
  · -- Hölder conjugacy on γ̄ : γ̄.HolderConjugate (γ̄ / (γ̄ - 1)).
    rw [toReal_paperGammaBar hα hβ]
    exact paper_holderConjugate_gammaBar hα hβ

/-- **Canonical constructor from a `HypothesisPowerGrowth` bundle.**

This is the *correctly-typed* analogue of the (unprovable) producer
theorem `simplePowerExponentFacts_of_powerGrowth`. Instead of
extracting a bundle at *arbitrary* type-level exponents, we extract it
at the *paper exponents* derived from the bundle's own `α, β` data
fields. Downstream tasks calling
`thm_main_simplePowerGrowth_concrete` should *also* fix
`betaBar = paperBetaBar hpow.β`, etc., so that this constructor
applies. -/
noncomputable def ofPowerGrowth {d : ℕ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH) :
    SimplePowerExponentFacts (paperGammaBarReal hpow.α hpow.β)
      (paperBetaBar hpow.β) (paperGammaBar hpow.α hpow.β)
      (paperBetaBarPrime hpow.β) :=
  standardPaper hpow.hα hpow.hβ

end SimplePowerExponentFacts

/-! ### Sanity-check examples -/

/-- The standard paper exponents `α = 2, β = 1` give
`β̄ = 2, γ̄ = 4, β̄' = 2`. We verify the bundle exists at those
choices. -/
example :
    SimplePowerExponentFacts
      (SimplePowerExponentFacts.paperGammaBarReal (2 : ℝ) 1)
      (SimplePowerExponentFacts.paperBetaBar (1 : ℝ))
      (SimplePowerExponentFacts.paperGammaBar (2 : ℝ) 1)
      (SimplePowerExponentFacts.paperBetaBarPrime (1 : ℝ)) :=
  SimplePowerExponentFacts.standardPaper (by norm_num : (1 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 1)

/-- A second exponent choice `α = 3, β = 2` (so `β̄ = 3,
γ̄ = 9/2, β̄' = 3/2`) — checks the constructor works at non-trivial
parameters too. -/
example :
    SimplePowerExponentFacts
      (SimplePowerExponentFacts.paperGammaBarReal (3 : ℝ) 2)
      (SimplePowerExponentFacts.paperBetaBar (2 : ℝ))
      (SimplePowerExponentFacts.paperGammaBar (3 : ℝ) 2)
      (SimplePowerExponentFacts.paperBetaBarPrime (2 : ℝ)) :=
  SimplePowerExponentFacts.standardPaper (by norm_num : (1 : ℝ) < 3)
    (by norm_num : (0 : ℝ) < 2)

end SimplePower
end Theorems
end StationaryMFG
