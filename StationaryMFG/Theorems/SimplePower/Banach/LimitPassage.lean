module

public import StationaryMFG.Theorems.SimplePower.Banach.WeakPairing

@[expose] public section

/-!
# Block E.1 — Limit passage for the first summand `(-υ - H + V) · (μ - m_{ε_k})`

This module discharges Phase-4 task `infra-P4-banach-E1-summand1`:
the **first** of the four limit-passage summands produced by the
strong-VI re-expansion of the simple-power-growth existence proof
(Block E of the five-block plan).

## Paper context

After the C–D extraction, the strong-VI test against the fixed test
triple `(η, ν, Dν)` produces four summands. The **first** is
```
S₁_k := ∫_{𝕋^d} (-υ(x) - H(x, Dυ(x), μ(x)) + V(x)) · (μ(x) - m_{ε_k}(x)) dx
```
with the multiplier
```
g(x) := -υ(x) - H(x, Dυ(x), μ(x)) + V(x)
```
fixed (independent of `k`) and known to lie in `L^{β̄'}_per` from
`paper:lem:ADFGU.a` (`eq:boundsH`) plus the standing assumption
`V ∈ L^{β̄'}`. The C.5+D extraction gives a weakly convergent
sub-sequence `m_{ε_k} ⇀ m` in `L^{β̄}_per`. By the weak-strong
integral pairing of `Banach/WeakPairing.lean`, `S₁_k → S₁` with
```
S₁ := ∫_{𝕋^d} g(x) · (μ(x) - m(x)) dx.
```

## Headline

The substantive content of Block E is the *packaging* of the pairing
lemma. The proof itself splits the integrand
`g · (μ - m_n) = g · μ − g · m_n`, integrates the difference against
`Lebesgue on the unit cube`, and combines the constant-in-`n` term
`∫ g · μ` (handled by `tendsto_const_nhds`) with the convergent term
`∫ g · m_n → ∫ g · m` (handled by the weak-pairing certificate).

The headline is `limit_passage_summand1`. We deliberately keep `μ` an
**arbitrary** `L^{β̄}_per` reference (rather than a free function of the
limit `m`): this matches the paper, where the fixed multiplier `g`
depends only on the test triple and the *limit* `μ`, and the term
`(μ - m_{ε_k})` is the running-difference whose weak limit is
`(μ - m)`.

## References / provenance

Direct application of the consumer-facing API
`tendsto_integral_of_weakConvUniversal_strongTest` from `Banach/WeakPairing.lean`
(Block E.0). No external reference adapted.
-/

noncomputable section

namespace StationaryMFG
namespace Theorems
namespace SimplePower
namespace Banach

open MeasureTheory
open StationaryMFG.Periodic
open scoped ENNReal NNReal
open Filter Topology

variable {d : ℕ}

/-! ### Headline theorem — Block E.1 -/

/-- **Limit passage for the first summand.**

Given:
* a real Hölder pair `(β̄, β̄')` with `1/β̄ + 1/β̄' = 1`;
* a sequence `m_n : ℕ → (Fin d → ℝ) → ℝ` of `L^{β̄}_per` functions
  with limit `m ∈ L^{β̄}_per`;
* a fixed multiplier `g ∈ L^{β̄'}_per`
  (the paper's `−υ − H(·, Dυ, μ) + V`);
* a fixed reference `μ ∈ L^{β̄}_per`
  (the paper's limit `μ` of `m_{ε_k}`);
* a weak-pairing certificate
  `h_weak : WeakConvPairing_universal hpq m_n m`,

the integral pairing
```
∫_{[0,1]^d} g(x) · (μ(x) - m_n n x)
```
converges to
```
∫_{[0,1]^d} g(x) · (μ(x) - m(x)).
```

The argument splits the integrand `g · (μ - m_n) = g · μ − g · m_n`,
isolates the constant-in-`n` term `∫ g · μ`, and applies the
weak-pairing certificate to the convergent term
`∫ g · m_n → ∫ g · m`.

Integrability of each pointwise product is supplied by the periodic
Hölder lemma `MemLpPer.integrable_mul` of `Periodic/Lp.lean`. -/
theorem limit_passage_summand1
    {βBar βBar' : ℝ} (hpq : βBar.HolderConjugate βBar')
    {m_n : ℕ → (Fin d → ℝ) → ℝ}
    {m μ g : (Fin d → ℝ) → ℝ}
    (hm_n : ∀ n, MemLpPer (ENNReal.ofReal βBar) (m_n n))
    (hm : MemLpPer (ENNReal.ofReal βBar) m)
    (hμ : MemLpPer (ENNReal.ofReal βBar) μ)
    (hg : MemLpPer (ENNReal.ofReal βBar') g)
    (h_weak : WeakConvPairing_universal (d := d) hpq m_n m) :
    Tendsto
      (fun n => ∫ x in UnitCube d, g x * (μ x - m_n n x))
      atTop
      (𝓝 (∫ x in UnitCube d, g x * (μ x - m x))) := by
  -- Step 1: rewrite each integrand as a pointwise difference.
  -- `g · (μ - m_n) = g · μ - g · m_n`.
  have h_split_n : ∀ n,
      (fun x => g x * (μ x - m_n n x))
        = (fun x => g x * μ x - g x * m_n n x) := by
    intro n
    funext x
    ring
  have h_split_lim :
      (fun x => g x * (μ x - m x))
        = (fun x => g x * μ x - g x * m x) := by
    funext x
    ring
  -- Step 2: integrability of each piece on the unit cube
  -- (Hölder pairing `(β̄', β̄)`).
  have hpq' : βBar'.HolderConjugate βBar := hpq.symm
  have hInt_gμ :
      IntegrableOn (fun x => g x * μ x) (UnitCube d) :=
    MemLpPer.integrable_mul hpq' hg hμ
  have hInt_gm : ∀ n,
      IntegrableOn (fun x => g x * m_n n x) (UnitCube d) :=
    fun n => MemLpPer.integrable_mul hpq' hg (hm_n n)
  have hInt_gm_lim :
      IntegrableOn (fun x => g x * m x) (UnitCube d) :=
    MemLpPer.integrable_mul hpq' hg hm
  -- Step 3: split the integrals via `integral_sub`.
  have h_int_split_n : ∀ n,
      ∫ x in UnitCube d, g x * (μ x - m_n n x)
        = (∫ x in UnitCube d, g x * μ x)
          - (∫ x in UnitCube d, g x * m_n n x) := by
    intro n
    rw [h_split_n n]
    exact MeasureTheory.integral_sub hInt_gμ (hInt_gm n)
  have h_int_split_lim :
      ∫ x in UnitCube d, g x * (μ x - m x)
        = (∫ x in UnitCube d, g x * μ x)
          - (∫ x in UnitCube d, g x * m x) := by
    rw [h_split_lim]
    exact MeasureTheory.integral_sub hInt_gμ hInt_gm_lim
  -- Step 4: the convergent piece `∫ g · m_n → ∫ g · m`. The
  -- weak-pairing certificate is stated as `m_n · g → m · g`; multiplication
  -- of reals is commutative, so we rewrite the integrands.
  have h_weak_pairing :
      Tendsto (fun n => ∫ x in UnitCube d, m_n n x * g x)
        atTop (𝓝 (∫ x in UnitCube d, m x * g x)) :=
    tendsto_integral_of_weakConvUniversal_strongTest hpq hm_n hm hg h_weak
  -- Rewrite to `g · m_n` form via commutativity of multiplication.
  have h_conv_gm :
      Tendsto (fun n => ∫ x in UnitCube d, g x * m_n n x)
        atTop (𝓝 (∫ x in UnitCube d, g x * m x)) := by
    have h_funext_n : ∀ n,
        (fun x => m_n n x * g x) = (fun x => g x * m_n n x) := by
      intro n
      funext x
      ring
    have h_funext_lim :
        (fun x => m x * g x) = (fun x => g x * m x) := by
      funext x
      ring
    -- Rewrite the integrals on both sides of the limit.
    have h_int_eq_n : ∀ n,
        ∫ x in UnitCube d, m_n n x * g x
          = ∫ x in UnitCube d, g x * m_n n x := by
      intro n
      rw [h_funext_n n]
    have h_int_eq_lim :
        ∫ x in UnitCube d, m x * g x
          = ∫ x in UnitCube d, g x * m x := by
      rw [h_funext_lim]
    -- Now produce the rewritten tendsto.
    have h1 : (fun n => ∫ x in UnitCube d, m_n n x * g x)
              = (fun n => ∫ x in UnitCube d, g x * m_n n x) := by
      funext n; exact h_int_eq_n n
    rw [h1] at h_weak_pairing
    rw [h_int_eq_lim] at h_weak_pairing
    exact h_weak_pairing
  -- Step 5: assemble. The constant piece is `∫ g · μ`, which is
  -- independent of `n`.
  have h_const :
      Tendsto (fun _ : ℕ => ∫ x in UnitCube d, g x * μ x)
        atTop (𝓝 (∫ x in UnitCube d, g x * μ x)) :=
    tendsto_const_nhds
  -- Subtract: `(const) - (∫ g · m_n) → (const) - (∫ g · m)`.
  have h_diff :
      Tendsto
        (fun n => (∫ x in UnitCube d, g x * μ x)
                    - (∫ x in UnitCube d, g x * m_n n x))
        atTop
        (𝓝 ((∫ x in UnitCube d, g x * μ x)
              - (∫ x in UnitCube d, g x * m x))) :=
    h_const.sub h_conv_gm
  -- Re-fold the integrand.
  have h_funext :
      (fun n => (∫ x in UnitCube d, g x * μ x)
                  - (∫ x in UnitCube d, g x * m_n n x))
        = (fun n => ∫ x in UnitCube d, g x * (μ x - m_n n x)) := by
    funext n
    rw [h_int_split_n n]
  rw [h_funext] at h_diff
  rw [← h_int_split_lim] at h_diff
  exact h_diff

/-! ### Sanity-check unit test

Exercise the headline at the trivial constant-zero data: `m_n := 0`,
`m := 0`, `μ := 0`, `g := 0`. Both sides of the limit reduce to `0`
and the convergence holds via `tendsto_const_nhds`. -/

example
    {βBar βBar' : ℝ} (hpq : βBar.HolderConjugate βBar') :
    Tendsto
      (fun (_ : ℕ) =>
        ∫ x in UnitCube d,
          (fun (_ : Fin d → ℝ) => (0 : ℝ)) x *
            ((fun (_ : Fin d → ℝ) => (0 : ℝ)) x -
              (fun (_ : Fin d → ℝ) => (0 : ℝ)) x))
      atTop
      (𝓝 (∫ x in UnitCube d,
        (fun (_ : Fin d → ℝ) => (0 : ℝ)) x *
          ((fun (_ : Fin d → ℝ) => (0 : ℝ)) x -
            (fun (_ : Fin d → ℝ) => (0 : ℝ)) x))) := by
  haveI : IsFiniteMeasure (Measure.restrict (volume : Measure (Fin d → ℝ))
            (UnitCube d)) :=
    ⟨by
      rw [Measure.restrict_apply MeasurableSet.univ]
      simp⟩
  -- All four functions are `MemLpPer _ 0` via `memLp_const`.
  have h0_β : MemLpPer (d := d) (ENNReal.ofReal βBar)
                (fun (_ : Fin d → ℝ) => (0 : ℝ)) :=
    MemLp.toMemLpPer (memLp_const (0 : ℝ))
  have h0_β' : MemLpPer (d := d) (ENNReal.ofReal βBar')
                (fun (_ : Fin d → ℝ) => (0 : ℝ)) :=
    MemLp.toMemLpPer (memLp_const (0 : ℝ))
  -- Weak-pairing certificate for the zero sequence with zero limit.
  have h_weak := WeakConvPairing_universal.zero (d := d) hpq
  exact limit_passage_summand1 hpq (m_n := fun _ => fun _ => (0 : ℝ))
    (m := fun _ => (0 : ℝ)) (μ := fun _ => (0 : ℝ))
    (g := fun _ => (0 : ℝ)) (fun _ => h0_β) h0_β h0_β h0_β' h_weak

/-! ### Headline theorem — Block E.2

The second of the four limit-passage summands produced by the
strong-VI re-expansion. It pairs the **fixed flux**
`flux := μ · D_pH(·, Dυ, μ)` (an `L^{γ̄'}_per` multiplier from
`paper:lem:ADFGU.b`) with the running difference
`(Dυ − Du_{ε_k})`, where `Du_{ε_k} ⇀ Du` weakly in `L^{γ̄}_per` from
Block D.

The structure mirrors `limit_passage_summand1`: split the integrand
`flux · (Dυ − Du_n) = flux · Dυ − flux · Du_n`, isolate the
constant-in-`n` term `∫ flux · Dυ`, and apply the weak-pairing
certificate to the convergent term `∫ flux · Du_n → ∫ flux · Du`.

The summand is stated **scalar-valued**: in the paper, both `flux`
and `(Dυ − Du)` are `ℝ^d`-valued, but their pointwise dot product
reduces to a `d`-fold sum of scalar products, so the eventual
final-closure step consumes `limit_passage_summand2` once per
coordinate.
-/

/-- **Limit passage for the second summand.**

Given:
* a real Hölder pair `(γ̄, γ̄')` with `1/γ̄ + 1/γ̄' = 1`;
* a sequence `Du_n : ℕ → (Fin d → ℝ) → ℝ` of `L^{γ̄}_per` functions
  (e.g. one component of the gradient `Du_{ε_k}`) with limit
  `Du ∈ L^{γ̄}_per`;
* a fixed flux `flux ∈ L^{γ̄'}_per`
  (the paper's `μ · D_pH(·, Dυ, μ)`, supplied component-wise);
* a fixed reference `Dυ ∈ L^{γ̄}_per`
  (the corresponding component of `Dυ`);
* a weak-pairing certificate
  `h_weak : WeakConvPairing_universal hpq Du_n Du`,

the integral pairing
```
∫_{[0,1]^d} flux(x) · (Dυ(x) − Du_n n x)
```
converges to
```
∫_{[0,1]^d} flux(x) · (Dυ(x) − Du(x)).
```

The argument splits the integrand
`flux · (Dυ − Du_n) = flux · Dυ − flux · Du_n`, isolates the
constant-in-`n` term `∫ flux · Dυ`, and applies the weak-pairing
certificate to the convergent term `∫ flux · Du_n → ∫ flux · Du`.
Integrability of each pointwise product is supplied by the periodic
Hölder lemma `MemLpPer.integrable_mul` of `Periodic/Lp.lean`. -/
theorem limit_passage_summand2
    {gammaBar gammaBar' : ℝ} (hpq : gammaBar.HolderConjugate gammaBar')
    {Du_n : ℕ → (Fin d → ℝ) → ℝ}
    {Du Dυ flux : (Fin d → ℝ) → ℝ}
    (hDu_n : ∀ n, MemLpPer (ENNReal.ofReal gammaBar) (Du_n n))
    (hDu : MemLpPer (ENNReal.ofReal gammaBar) Du)
    (hDυ : MemLpPer (ENNReal.ofReal gammaBar) Dυ)
    (hflux : MemLpPer (ENNReal.ofReal gammaBar') flux)
    (h_weak : WeakConvPairing_universal (d := d) hpq Du_n Du) :
    Tendsto
      (fun n => ∫ x in UnitCube d, flux x * (Dυ x - Du_n n x))
      atTop
      (𝓝 (∫ x in UnitCube d, flux x * (Dυ x - Du x))) := by
  -- Step 1: rewrite each integrand as a pointwise difference.
  -- `flux · (Dυ - Du_n) = flux · Dυ - flux · Du_n`.
  have h_split_n : ∀ n,
      (fun x => flux x * (Dυ x - Du_n n x))
        = (fun x => flux x * Dυ x - flux x * Du_n n x) := by
    intro n
    funext x
    ring
  have h_split_lim :
      (fun x => flux x * (Dυ x - Du x))
        = (fun x => flux x * Dυ x - flux x * Du x) := by
    funext x
    ring
  -- Step 2: integrability of each piece on the unit cube
  -- (Hölder pairing `(γ̄', γ̄)`).
  have hpq' : gammaBar'.HolderConjugate gammaBar := hpq.symm
  have hInt_fluxDυ :
      IntegrableOn (fun x => flux x * Dυ x) (UnitCube d) :=
    MemLpPer.integrable_mul hpq' hflux hDυ
  have hInt_fluxDu : ∀ n,
      IntegrableOn (fun x => flux x * Du_n n x) (UnitCube d) :=
    fun n => MemLpPer.integrable_mul hpq' hflux (hDu_n n)
  have hInt_fluxDu_lim :
      IntegrableOn (fun x => flux x * Du x) (UnitCube d) :=
    MemLpPer.integrable_mul hpq' hflux hDu
  -- Step 3: split the integrals via `integral_sub`.
  have h_int_split_n : ∀ n,
      ∫ x in UnitCube d, flux x * (Dυ x - Du_n n x)
        = (∫ x in UnitCube d, flux x * Dυ x)
          - (∫ x in UnitCube d, flux x * Du_n n x) := by
    intro n
    rw [h_split_n n]
    exact MeasureTheory.integral_sub hInt_fluxDυ (hInt_fluxDu n)
  have h_int_split_lim :
      ∫ x in UnitCube d, flux x * (Dυ x - Du x)
        = (∫ x in UnitCube d, flux x * Dυ x)
          - (∫ x in UnitCube d, flux x * Du x) := by
    rw [h_split_lim]
    exact MeasureTheory.integral_sub hInt_fluxDυ hInt_fluxDu_lim
  -- Step 4: the convergent piece `∫ flux · Du_n → ∫ flux · Du`. The
  -- weak-pairing certificate is stated as `Du_n · flux → Du · flux`;
  -- multiplication of reals is commutative, so we rewrite the integrands.
  have h_weak_pairing :
      Tendsto (fun n => ∫ x in UnitCube d, Du_n n x * flux x)
        atTop (𝓝 (∫ x in UnitCube d, Du x * flux x)) :=
    tendsto_integral_of_weakConvUniversal_strongTest hpq hDu_n hDu hflux h_weak
  -- Rewrite to `flux · Du_n` form via commutativity of multiplication.
  have h_conv_fluxDu :
      Tendsto (fun n => ∫ x in UnitCube d, flux x * Du_n n x)
        atTop (𝓝 (∫ x in UnitCube d, flux x * Du x)) := by
    have h_funext_n : ∀ n,
        (fun x => Du_n n x * flux x) = (fun x => flux x * Du_n n x) := by
      intro n
      funext x
      ring
    have h_funext_lim :
        (fun x => Du x * flux x) = (fun x => flux x * Du x) := by
      funext x
      ring
    have h_int_eq_n : ∀ n,
        ∫ x in UnitCube d, Du_n n x * flux x
          = ∫ x in UnitCube d, flux x * Du_n n x := by
      intro n
      rw [h_funext_n n]
    have h_int_eq_lim :
        ∫ x in UnitCube d, Du x * flux x
          = ∫ x in UnitCube d, flux x * Du x := by
      rw [h_funext_lim]
    have h1 : (fun n => ∫ x in UnitCube d, Du_n n x * flux x)
              = (fun n => ∫ x in UnitCube d, flux x * Du_n n x) := by
      funext n; exact h_int_eq_n n
    rw [h1] at h_weak_pairing
    rw [h_int_eq_lim] at h_weak_pairing
    exact h_weak_pairing
  -- Step 5: assemble. The constant piece is `∫ flux · Dυ`, which is
  -- independent of `n`.
  have h_const :
      Tendsto (fun _ : ℕ => ∫ x in UnitCube d, flux x * Dυ x)
        atTop (𝓝 (∫ x in UnitCube d, flux x * Dυ x)) :=
    tendsto_const_nhds
  have h_diff :
      Tendsto
        (fun n => (∫ x in UnitCube d, flux x * Dυ x)
                    - (∫ x in UnitCube d, flux x * Du_n n x))
        atTop
        (𝓝 ((∫ x in UnitCube d, flux x * Dυ x)
              - (∫ x in UnitCube d, flux x * Du x))) :=
    h_const.sub h_conv_fluxDu
  -- Re-fold the integrand.
  have h_funext :
      (fun n => (∫ x in UnitCube d, flux x * Dυ x)
                  - (∫ x in UnitCube d, flux x * Du_n n x))
        = (fun n => ∫ x in UnitCube d, flux x * (Dυ x - Du_n n x)) := by
    funext n
    rw [h_int_split_n n]
  rw [h_funext] at h_diff
  rw [← h_int_split_lim] at h_diff
  exact h_diff

/-! ### Sanity-check unit test — Block E.2

Exercise the headline at the trivial constant-zero data: `Du_n := 0`,
`Du := 0`, `Dυ := 0`, `flux := 0`. Both sides of the limit reduce to
`0` and the convergence holds via `tendsto_const_nhds`. -/

example
    {gammaBar gammaBar' : ℝ} (hpq : gammaBar.HolderConjugate gammaBar') :
    Tendsto
      (fun (_ : ℕ) =>
        ∫ x in UnitCube d,
          (fun (_ : Fin d → ℝ) => (0 : ℝ)) x *
            ((fun (_ : Fin d → ℝ) => (0 : ℝ)) x -
              (fun (_ : Fin d → ℝ) => (0 : ℝ)) x))
      atTop
      (𝓝 (∫ x in UnitCube d,
        (fun (_ : Fin d → ℝ) => (0 : ℝ)) x *
          ((fun (_ : Fin d → ℝ) => (0 : ℝ)) x -
            (fun (_ : Fin d → ℝ) => (0 : ℝ)) x))) := by
  haveI : IsFiniteMeasure (Measure.restrict (volume : Measure (Fin d → ℝ))
            (UnitCube d)) :=
    ⟨by
      rw [Measure.restrict_apply MeasurableSet.univ]
      simp⟩
  -- All four functions are `MemLpPer _ 0` via `memLp_const`.
  have h0_γ : MemLpPer (d := d) (ENNReal.ofReal gammaBar)
                (fun (_ : Fin d → ℝ) => (0 : ℝ)) :=
    MemLp.toMemLpPer (memLp_const (0 : ℝ))
  have h0_γ' : MemLpPer (d := d) (ENNReal.ofReal gammaBar')
                (fun (_ : Fin d → ℝ) => (0 : ℝ)) :=
    MemLp.toMemLpPer (memLp_const (0 : ℝ))
  have h_weak := WeakConvPairing_universal.zero (d := d) hpq
  exact limit_passage_summand2 hpq (Du_n := fun _ => fun _ => (0 : ℝ))
    (Du := fun _ => (0 : ℝ)) (Dυ := fun _ => (0 : ℝ))
    (flux := fun _ => (0 : ℝ)) (fun _ => h0_γ) h0_γ h0_γ h0_γ' h_weak

/-! ### Headline theorem — Block E.3

The third of the four limit-passage summands produced by the
strong-VI re-expansion. It pairs the **mass-defect** `(μ - 1)` with
the running difference `(υ - u_{ε_k})`, where `u_{ε_k} ⇀ u` weakly in
`L^{γ̄}_per` from Block D.

In the paper, the multiplier is `(μ - 1) ∈ L^{β̄}_per`, but we route
through Hölder pairing at the conjugate exponents `(γ̄, γ̄')`: the
finite-measure inclusion `L^{β̄}_per ↪ L^{γ̄'}_per` (paper
`eq:gamma`, `γ̄' ≤ β̄`) lets the consumer re-brand `(μ - 1)` as an
`L^{γ̄'}_per` test. Inside this lemma we therefore take the
multiplier in `L^{q}_per` directly; the rebrand is the consumer's
responsibility (via `MemLpPer.mono_exponent_finite` in
`Periodic/LpInclusion.lean`).

The structure mirrors `limit_passage_summand1` and
`limit_passage_summand2`: split the integrand
`m · (v - u_n) = m · v - m · u_n`, isolate the constant-in-`n` term
`∫ m · v`, and apply the weak-pairing certificate to the convergent
term `∫ m · u_n → ∫ m · u`.
-/

/-- **Limit passage for the third summand.**

Given:
* a real Hölder pair `(p, q)` with `1/p + 1/q = 1`
  (the consumer instantiates with `(γ̄, γ̄')`);
* a sequence `u_n : ℕ → (Fin d → ℝ) → ℝ` of `L^{p}_per` functions
  (the paper's `u_{ε_k}`) with limit `u ∈ L^{p}_per`;
* a fixed reference `v ∈ L^{p}_per` (the paper's value-function
  test `υ`);
* a fixed multiplier `m ∈ L^{q}_per` (the paper's `(μ - 1)`,
  re-branded from `L^{β̄}_per` via the finite-measure inclusion
  `L^{β̄}_per ↪ L^{γ̄'}_per`);
* a weak-pairing certificate
  `h_weak : WeakConvPairing_universal hpq u_n u`,

the integral pairing
```
∫_{[0,1]^d} m(x) · (v(x) - u_n n x)
```
converges to
```
∫_{[0,1]^d} m(x) · (v(x) - u(x)).
```

The argument splits the integrand
`m · (v - u_n) = m · v - m · u_n`, isolates the constant-in-`n`
term `∫ m · v`, and applies the weak-pairing certificate to the
convergent term `∫ m · u_n → ∫ m · u`.
Integrability of each pointwise product is supplied by the periodic
Hölder lemma `MemLpPer.integrable_mul` of `Periodic/Lp.lean`. -/
theorem limit_passage_summand3
    {p q : ℝ} (hpq : p.HolderConjugate q)
    {u_n : ℕ → (Fin d → ℝ) → ℝ}
    {u v m : (Fin d → ℝ) → ℝ}
    (hu_n : ∀ n, MemLpPer (ENNReal.ofReal p) (u_n n))
    (hu : MemLpPer (ENNReal.ofReal p) u)
    (hv : MemLpPer (ENNReal.ofReal p) v)
    (hm : MemLpPer (ENNReal.ofReal q) m)
    (h_weak : WeakConvPairing_universal (d := d) hpq u_n u) :
    Tendsto
      (fun n => ∫ x in UnitCube d, m x * (v x - u_n n x))
      atTop
      (𝓝 (∫ x in UnitCube d, m x * (v x - u x))) := by
  -- Step 1: rewrite each integrand as a pointwise difference.
  -- `m · (v - u_n) = m · v - m · u_n`.
  have h_split_n : ∀ n,
      (fun x => m x * (v x - u_n n x))
        = (fun x => m x * v x - m x * u_n n x) := by
    intro n
    funext x
    ring
  have h_split_lim :
      (fun x => m x * (v x - u x))
        = (fun x => m x * v x - m x * u x) := by
    funext x
    ring
  -- Step 2: integrability of each piece on the unit cube
  -- (Hölder pairing `(q, p)`).
  have hpq' : q.HolderConjugate p := hpq.symm
  have hInt_mv :
      IntegrableOn (fun x => m x * v x) (UnitCube d) :=
    MemLpPer.integrable_mul hpq' hm hv
  have hInt_mu : ∀ n,
      IntegrableOn (fun x => m x * u_n n x) (UnitCube d) :=
    fun n => MemLpPer.integrable_mul hpq' hm (hu_n n)
  have hInt_mu_lim :
      IntegrableOn (fun x => m x * u x) (UnitCube d) :=
    MemLpPer.integrable_mul hpq' hm hu
  -- Step 3: split the integrals via `integral_sub`.
  have h_int_split_n : ∀ n,
      ∫ x in UnitCube d, m x * (v x - u_n n x)
        = (∫ x in UnitCube d, m x * v x)
          - (∫ x in UnitCube d, m x * u_n n x) := by
    intro n
    rw [h_split_n n]
    exact MeasureTheory.integral_sub hInt_mv (hInt_mu n)
  have h_int_split_lim :
      ∫ x in UnitCube d, m x * (v x - u x)
        = (∫ x in UnitCube d, m x * v x)
          - (∫ x in UnitCube d, m x * u x) := by
    rw [h_split_lim]
    exact MeasureTheory.integral_sub hInt_mv hInt_mu_lim
  -- Step 4: the convergent piece `∫ m · u_n → ∫ m · u`. The
  -- weak-pairing certificate is stated as `u_n · m → u · m`;
  -- multiplication of reals is commutative, so we rewrite the integrands.
  have h_weak_pairing :
      Tendsto (fun n => ∫ x in UnitCube d, u_n n x * m x)
        atTop (𝓝 (∫ x in UnitCube d, u x * m x)) :=
    tendsto_integral_of_weakConvUniversal_strongTest hpq hu_n hu hm h_weak
  -- Rewrite to `m · u_n` form via commutativity of multiplication.
  have h_conv_mu :
      Tendsto (fun n => ∫ x in UnitCube d, m x * u_n n x)
        atTop (𝓝 (∫ x in UnitCube d, m x * u x)) := by
    have h_funext_n : ∀ n,
        (fun x => u_n n x * m x) = (fun x => m x * u_n n x) := by
      intro n
      funext x
      ring
    have h_funext_lim :
        (fun x => u x * m x) = (fun x => m x * u x) := by
      funext x
      ring
    have h_int_eq_n : ∀ n,
        ∫ x in UnitCube d, u_n n x * m x
          = ∫ x in UnitCube d, m x * u_n n x := by
      intro n
      rw [h_funext_n n]
    have h_int_eq_lim :
        ∫ x in UnitCube d, u x * m x
          = ∫ x in UnitCube d, m x * u x := by
      rw [h_funext_lim]
    have h1 : (fun n => ∫ x in UnitCube d, u_n n x * m x)
              = (fun n => ∫ x in UnitCube d, m x * u_n n x) := by
      funext n; exact h_int_eq_n n
    rw [h1] at h_weak_pairing
    rw [h_int_eq_lim] at h_weak_pairing
    exact h_weak_pairing
  -- Step 5: assemble. The constant piece is `∫ m · v`, which is
  -- independent of `n`.
  have h_const :
      Tendsto (fun _ : ℕ => ∫ x in UnitCube d, m x * v x)
        atTop (𝓝 (∫ x in UnitCube d, m x * v x)) :=
    tendsto_const_nhds
  have h_diff :
      Tendsto
        (fun n => (∫ x in UnitCube d, m x * v x)
                    - (∫ x in UnitCube d, m x * u_n n x))
        atTop
        (𝓝 ((∫ x in UnitCube d, m x * v x)
              - (∫ x in UnitCube d, m x * u x))) :=
    h_const.sub h_conv_mu
  -- Re-fold the integrand.
  have h_funext :
      (fun n => (∫ x in UnitCube d, m x * v x)
                  - (∫ x in UnitCube d, m x * u_n n x))
        = (fun n => ∫ x in UnitCube d, m x * (v x - u_n n x)) := by
    funext n
    rw [h_int_split_n n]
  rw [h_funext] at h_diff
  rw [← h_int_split_lim] at h_diff
  exact h_diff

/-! ### Sanity-check unit test — Block E.3

Exercise the headline at the trivial constant-zero data: `u_n := 0`,
`u := 0`, `v := 0`, `m := 0`. Both sides of the limit reduce to
`0` and the convergence holds via `tendsto_const_nhds`. -/

example
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    Tendsto
      (fun (_ : ℕ) =>
        ∫ x in UnitCube d,
          (fun (_ : Fin d → ℝ) => (0 : ℝ)) x *
            ((fun (_ : Fin d → ℝ) => (0 : ℝ)) x -
              (fun (_ : Fin d → ℝ) => (0 : ℝ)) x))
      atTop
      (𝓝 (∫ x in UnitCube d,
        (fun (_ : Fin d → ℝ) => (0 : ℝ)) x *
          ((fun (_ : Fin d → ℝ) => (0 : ℝ)) x -
            (fun (_ : Fin d → ℝ) => (0 : ℝ)) x))) := by
  haveI : IsFiniteMeasure (Measure.restrict (volume : Measure (Fin d → ℝ))
            (UnitCube d)) :=
    ⟨by
      rw [Measure.restrict_apply MeasurableSet.univ]
      simp⟩
  -- All four functions are `MemLpPer _ 0` via `memLp_const`.
  have h0_p : MemLpPer (d := d) (ENNReal.ofReal p)
                (fun (_ : Fin d → ℝ) => (0 : ℝ)) :=
    MemLp.toMemLpPer (memLp_const (0 : ℝ))
  have h0_q : MemLpPer (d := d) (ENNReal.ofReal q)
                (fun (_ : Fin d → ℝ) => (0 : ℝ)) :=
    MemLp.toMemLpPer (memLp_const (0 : ℝ))
  have h_weak := WeakConvPairing_universal.zero (d := d) hpq
  exact limit_passage_summand3 hpq (u_n := fun _ => fun _ => (0 : ℝ))
    (u := fun _ => (0 : ℝ)) (v := fun _ => (0 : ℝ))
    (m := fun _ => (0 : ℝ)) (fun _ => h0_p) h0_p h0_p h0_q h_weak

/-! ### Headline theorem — Block E.4

The fourth and final summand in the `ε → 0` limit-passage of the
regularized weak VI: the two **ε-multiplied Gateaux pairings**

```
G₁_k := ∫_{𝕋^d} |Du_{ε_k}|^{γ̄-2} Du_{ε_k} · D(υ - u_{ε_k}) dx
G₂_k := ∫_{𝕋^d} |u_{ε_k}|^{γ̄-2} u_{ε_k} · (υ - u_{ε_k}) dx
```

vanish in the limit because each `Gᵢ_k` is uniformly bounded
(by Hölder against the apriori estimate `‖u_{ε_k}‖_{W^{1,γ̄}} ≤ C`)
and `ε_k → 0`. The substantive content is the **real-numerical
kernel**: `ε k · reg k → 0` whenever `ε k → 0` and `|reg k| ≤ M`.
The headline simply applies the kernel twice and combines.

This pattern mirrors the `hres_tendsto` block of
`limit_passage_real` in `SimplePower/Main.lean`, factored out as a
reusable lemma so Block E.4 can package both Gateaux terms together. -/

/-- **Real-numerical kernel for the ε-Gateaux limit passage.**

If `ε k → 0` and `|reg k| ≤ M` for some `M`, then the product
`ε k · reg k` tends to `0`. This is the standalone real-line lemma
underlying Block E.4: the Gateaux pairings `G₁_k`, `G₂_k` are
uniformly bounded reals, and multiplication by `ε_k → 0` sends
them to zero. -/
theorem limit_passage_eps_real_vanish
    {ε reg : ℕ → ℝ} {M : ℝ}
    (hε : Tendsto ε atTop (𝓝 0))
    (hreg : ∀ k, |reg k| ≤ M) :
    Tendsto (fun k => ε k * reg k) atTop (𝓝 0) := by
  -- The proof mirrors the `hres_tendsto` block of `limit_passage_real`
  -- in `SimplePower/Main.lean`: squeeze `|ε k · reg k| ≤ |ε k| · M`,
  -- then `|ε k| · M → 0 · M = 0`.
  have hM_nonneg : 0 ≤ M := le_trans (abs_nonneg _) (hreg 0)
  have habs : Tendsto (fun k => |ε k|) atTop (𝓝 0) := by
    have habs_eq : (fun k => |ε k|) = (fun k => ‖ε k‖) := by
      funext k; rw [Real.norm_eq_abs]
    rw [habs_eq]
    simpa using hε.norm
  have hbnd_tendsto : Tendsto (fun k => |ε k| * M) atTop (𝓝 0) := by
    have : Tendsto (fun k => |ε k| * M) atTop (𝓝 (0 * M)) :=
      habs.mul_const M
    simpa using this
  refine squeeze_zero_norm (a := fun k => |ε k| * M) ?_ hbnd_tendsto
  intro k
  have h1 : |ε k * reg k| ≤ |ε k| * M := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hreg k) (abs_nonneg _)
  simpa [Real.norm_eq_abs] using h1

/-- **Limit passage for the ε-Gateaux summands** (Block E.4).

Given:
* a regularization sequence `ε : ℕ → ℝ` with `ε k → 0`;
* two real-valued sequences `G₁, G₂ : ℕ → ℝ` representing the
  gradient and scalar Gateaux pairings, each uniformly bounded
  (`|G₁ k| ≤ M₁`, `|G₂ k| ≤ M₂`);

the combined ε-Gateaux contribution

```
ε k · G₁ k + ε k · G₂ k
```

tends to `0`.

The bounds `M₁`, `M₂` come from the upstream apriori estimate
`‖u_{ε_k}‖_{W^{1,γ̄}} ≤ C` (paper `thm:apriori-simple.power.growth`,
lines 1244–1265) paired by Hölder against the test gradient/value
`(Dυ - Du_{ε_k})`/`(υ - u_{ε_k})` in `L^{γ̄}`. Producing the
concrete `Mᵢ` for the abstract operator-pairing form is the
upstream consumer's job; this lemma packages the **real-line**
vanishing `ε · (bounded) → 0`, the only fact the limit-passage
chain needs from Block E.4. -/
theorem limit_passage_eps_gateaux_vanish
    {ε G₁ G₂ : ℕ → ℝ} {M₁ M₂ : ℝ}
    (hε : Tendsto ε atTop (𝓝 0))
    (hG₁ : ∀ k, |G₁ k| ≤ M₁)
    (hG₂ : ∀ k, |G₂ k| ≤ M₂) :
    Tendsto (fun k => ε k * G₁ k + ε k * G₂ k) atTop (𝓝 0) := by
  -- Apply the real-numerical kernel to each summand.
  have h1 : Tendsto (fun k => ε k * G₁ k) atTop (𝓝 0) :=
    limit_passage_eps_real_vanish hε hG₁
  have h2 : Tendsto (fun k => ε k * G₂ k) atTop (𝓝 0) :=
    limit_passage_eps_real_vanish hε hG₂
  -- Combine: `0 + 0 = 0`.
  have hsum : Tendsto (fun k => ε k * G₁ k + ε k * G₂ k)
        atTop (𝓝 (0 + 0)) := h1.add h2
  simpa using hsum

/-! ### Sanity-check unit test — Block E.4

Exercise the headline at the trivial constant-zero data: `ε := 0`,
`G₁ := 0`, `G₂ := 0`, `M₁ = M₂ = 0`. The combined sum is the constant
zero sequence, which converges to `0` via `tendsto_const_nhds`. -/

example :
    Tendsto
      (fun (k : ℕ) =>
        (fun (_ : ℕ) => (0 : ℝ)) k * (fun (_ : ℕ) => (0 : ℝ)) k
          + (fun (_ : ℕ) => (0 : ℝ)) k * (fun (_ : ℕ) => (0 : ℝ)) k)
      atTop (𝓝 0) := by
  refine limit_passage_eps_gateaux_vanish (M₁ := 0) (M₂ := 0)
    (ε := fun _ => (0 : ℝ))
    (G₁ := fun _ => (0 : ℝ))
    (G₂ := fun _ => (0 : ℝ))
    tendsto_const_nhds ?_ ?_
  · intro _; simp
  · intro _; simp

end Banach
end SimplePower
end Theorems
end StationaryMFG
