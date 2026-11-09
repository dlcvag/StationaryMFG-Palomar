module

public import StationaryMFG.Solutions.Regularized
public import StationaryMFG.Periodic.UnitCube

@[expose] public section

/-!
# `lem:strong.is.strong`, parts (a) and (b): the HJB equation a.e. on `{m > 0}`

This module formalizes the **first equation** (`eq:HJleq0`, paper line 1147) of
Lemma `lem:strong.is.strong` of Ferreira–Gomes–Üçer
(`Source/FGU-monotone_revised.tex`, line 1147–1154).

## Paper statement

Let `ε ≥ 0` and `(m, u) ∈ 𝓚 = L^{β̄}(𝕋^d; ℝ⁺_0) × W^{1,γ̄}(𝕋^d)` satisfy the
strong variational inequality
```
⟨A_ε[m, u], (μ − m, υ − u)⟩ ≥ 0   for every (μ, υ) ∈ 𝓚.
```
Then `u(x) + H(x, Du(x), m(x)) − V(x) ≤ 0` for almost every `x ∈ 𝕋^d`.

## Paper proof (line 1149–1153)

Test the strong VI at `(μ, υ) = (m + φ, u)` for an arbitrary `φ ∈ C^∞(𝕋^d; ℝ⁺_0)`.
Substituting into `defAepsi` (paper line 925), the second and third summands and
the ε-Gateaux summand vanish (since `υ − u = 0` and `Dυ − Du = 0`):
```
∫_{𝕋^d} (−u − H(x, Du, m) + V) φ dx ≥ 0.
```
Letting `φ` range over (suitable approximations of) indicators of measurable
subsets of the cube yields `∫_S (−u − H + V) dx ≥ 0` for every measurable
`S ⊆ 𝕋^d`, and the standard "set-integral nonneg ⇒ a.e. nonneg" lemma
(`MeasureTheory.ae_nonneg_of_forall_setIntegral_nonneg`) concludes.

## Lean formulation

Following `docs/CONVENTIONS.md` §1b (bare functions, not equivalence classes),
we state the lemma directly in **set-test-pair form**: we hypothesize the
strong VI specialized at `(μ, υ) = (m + 1_S, u)` for arbitrary measurable
`S ⊆ UnitCube d` of finite measure (admissible since `m ≥ 0` and `1_S ≥ 0`).
This sub-class of test pairs already exhausts the information needed for
`eq:HJleq0` and avoids invoking smooth-test-function density (which lives in
the parked Phase-1 task `infra:P1-density-W1p-main`). The full strong VI
implies the set-test-pair specialization by linearity, but encoding the full
VI as a Lean predicate would require the smoothness-density bridge to feed
`ae_nonneg_of_forall_setIntegral_nonneg`; the project's policy is to delegate
that step to the consumer of the present lemma when needed.

The integrability hypothesis on the residual `hjbResidual` is also explicit; in
the paper it is part of the standing regularity setup (paper line 1147 via
`def:strong`'s preamble: `m · D_pH ∈ L¹` and `u, V, H(·, Du, m) ∈ L¹` on the
cube under the simple-power-growth hypotheses of `thm:main-simple.power.growth`).
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

/-! ## The HJB residual `−u − H(x, Du, m) + V` -/

/-- The HJB residual of the paper, `−u(x) − H(x, Du(x), m(x)) + V(x)`. The
inequality `eq:HJleq0` is `0 ≤ hjbResidual` a.e., i.e. the *negative* of
`u + H − V ≤ 0`. -/
def hjbResidual
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ) : (Fin d → ℝ) → ℝ :=
  fun x => -(u x) - H x (fun i => Du i x) (m x) + V x

/-! ## Reduction of `mfgOperatorEpsPair` at the special test pair `(η, 0, 0)` -/

/-- **Key reduction**: at the test pair `(η, ν, Dν) = (η, 0, 0)`, the regularized
MFG pairing collapses to `∫_{𝕋^d} hjbResidual · η dx`.

Concretely, with `Dν = 0` and `ν = 0`, both the `μ · DpH ⬝ Dν` summand and
the `(μ − 1) · ν` summand of `mfgOperatorPair` vanish pointwise, and the
ε-Gateaux pairing `gateauxWpPair γBar Du u 0 0` is identically zero (both of
its summands carry a factor of `Dν` or `ν`). The remaining contribution is the
HJB-residual integrand. -/
theorem mfgOperatorEpsPair_test_zero_eq_residual
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (γBar ε : ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u η : (Fin d → ℝ) → ℝ) :
    mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH) γBar ε Du m u
        (fun _ _ => (0 : ℝ)) η (fun _ => (0 : ℝ)) =
      ∫ x in UnitCube d, hjbResidual V H Du m u x * η x
        ∂(volume : Measure (Fin d → ℝ)) := by
  unfold mfgOperatorEpsPair mfgOperatorPair gateauxWpPair hjbResidual
  -- The ε-Gateaux pairing vanishes because `Dν = 0` and `ν = 0`.
  have hgateaux :
      (∫ x in UnitCube d,
          vecAbsPowMinusTwo γBar (fun i => Du i x)
                * ((fun i => Du i x) ⬝ (fun i : Fin d => (0 : ℝ)))
              + absPowMinusTwo γBar (u x) * (u x * (0 : ℝ))
          ∂(volume : Measure (Fin d → ℝ))) = 0 := by
    have hzero_pi : (fun _ : Fin d => (0 : ℝ)) = (0 : Fin d → ℝ) := by
      funext _; rfl
    have hint :
        (fun x : Fin d → ℝ =>
            vecAbsPowMinusTwo γBar (fun i => Du i x)
                  * ((fun i => Du i x) ⬝ (fun i : Fin d => (0 : ℝ)))
                + absPowMinusTwo γBar (u x) * (u x * (0 : ℝ)))
          = (fun _ : Fin d → ℝ => (0 : ℝ)) := by
      funext x
      rw [hzero_pi, euclideanDot_zero_right]
      simp
    rw [hint]
    simp
  rw [hgateaux, mul_zero, add_zero]
  -- The first integrand reduces to `(-u - H(x, Du, m) + V) * η` because the
  -- last two summands carry factors of `0`.
  refine setIntegral_congr_fun measurableSet_unitCube ?_
  intro x _
  -- DpH ⬝ 0 = 0, so `m x * (DpH ⬝ 0) = 0`; and `(m x - 1) * 0 = 0`.
  have hzero_pi : (fun _ : Fin d => (0 : ℝ)) = (0 : Fin d → ℝ) := by
    funext _; rfl
  have hdot : DpH x (fun i => Du i x) (m x) ⬝ (fun i : Fin d =>
      (fun (_ : Fin d) (_ : Fin d → ℝ) => (0 : ℝ)) i x) = 0 := by
    have : (fun i : Fin d => (fun (_ : Fin d) (_ : Fin d → ℝ) => (0 : ℝ)) i x)
          = (0 : Fin d → ℝ) := by funext i; rfl
    rw [this, euclideanDot_zero_right]
  change ((-u x - H x (fun i => Du i x) (m x) + V x) * η x +
            m x * (DpH x (fun i => Du i x) (m x) ⬝ (fun i : Fin d =>
              (fun (_ : Fin d) (_ : Fin d → ℝ) => (0 : ℝ)) i x))
            + (m x - 1) * ((fun _ : Fin d → ℝ => (0 : ℝ)) x))
        = (-u x - H x (fun i => Du i x) (m x) + V x) * η x
  rw [hdot]
  simp

/-! ## Set-test-pair form of the strong VI -/

/-- **Set-test-pair specialization of the strong VI**. The hypothesis records
that the regularized MFG pairing of `A_ε[m, u]` against the test pair
`(η, ν, Dν) = (1_S, 0, 0)` is non-negative for every measurable `S ⊆ UnitCube d`
of finite measure. This is the specialization of the strong variational
inequality at `(μ, υ) = (m + 1_S, u)`; it is admissible since `m ≥ 0` and
`1_S ≥ 0` imply `m + 1_S ≥ 0`. -/
def StrongVI_setForm
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (γBar ε : ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ) : Prop :=
  ∀ S : Set (Fin d → ℝ), MeasurableSet S →
    (volume.restrict (UnitCube d)) S < ∞ →
    0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH) γBar ε Du m u
          (fun _ _ => (0 : ℝ))
          (fun x => S.indicator (fun _ => (1 : ℝ)) x)
          (fun _ => (0 : ℝ))

/-! ## Main theorem: HJB inequality from the strong VI -/

/-- **`lem:strong.is.strong`, part (a)** (paper line 1147, eq. `eq:HJleq0`).

Under the strong variational inequality (in its set-test-pair form
`StrongVI_setForm`) and integrability of the HJB residual on the unit cube,
```
u(x) + H(x, Du(x), m(x)) − V(x) ≤ 0   for a.e. x ∈ 𝕋^d.
```

The proof: testing against `1_S` for measurable `S ⊆ UnitCube d` of finite
measure, `mfgOperatorEpsPair_test_zero_eq_residual` rewrites the pairing as
`∫_S hjbResidual dx`. Hence `0 ≤ ∫_S hjbResidual` for every such `S`. By
`MeasureTheory.ae_nonneg_of_forall_setIntegral_nonneg`, `0 ≤ hjbResidual` a.e.
on the cube, which is `eq:HJleq0`. -/
theorem lem_strong_is_strong_HJB_ineq
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (γBar ε : ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (hRes : Integrable (hjbResidual V H Du m u)
              (volume.restrict (UnitCube d)))
    (hVI : StrongVI_setForm V H DpH γBar ε Du m u) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      u x + H x (fun i => Du i x) (m x) - V x ≤ 0 := by
  -- Step 1. From `hVI`, deduce `0 ≤ ∫_S hjbResidual dx` for every measurable
  -- `S` of finite restricted-measure.
  have hSetIntegral :
      ∀ S : Set (Fin d → ℝ), MeasurableSet S →
        (volume.restrict (UnitCube d)) S < ∞ →
        0 ≤ ∫ x in S, hjbResidual V H Du m u x
              ∂(volume.restrict (UnitCube d)) := by
    intro S hSmeas _hSfin
    -- Translate the strong VI through `mfgOperatorEpsPair_test_zero_eq_residual`.
    have hpair := hVI S hSmeas _hSfin
    have hreduce :=
      mfgOperatorEpsPair_test_zero_eq_residual (V := V) (H := H) (DpH := DpH)
        γBar ε Du m u (fun x => S.indicator (fun _ => (1 : ℝ)) x)
    -- After substitution: `0 ≤ ∫ in UnitCube d, hjbResidual * 1_S`.
    rw [hreduce] at hpair
    -- Identify `∫ in UnitCube d, f * 1_S` with `∫ x in S, f ∂(volume.restrict (UnitCube d))`.
    -- First, rewrite the pointwise product against the indicator.
    have hpoint : ∀ x : Fin d → ℝ,
        hjbResidual V H Du m u x * S.indicator (fun _ => (1 : ℝ)) x
          = S.indicator (fun y => hjbResidual V H Du m u y) x := by
      intro x
      by_cases hx : x ∈ S
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]
    have hintegrand_eq :
        (fun x : Fin d → ℝ =>
            hjbResidual V H Du m u x * S.indicator (fun _ => (1 : ℝ)) x)
          = S.indicator (fun y : Fin d → ℝ => hjbResidual V H Du m u y) := by
      funext x; exact hpoint x
    rw [hintegrand_eq] at hpair
    -- `∫ x in UnitCube d, S.indicator g x = ∫_S g ∂(volume.restrict (UnitCube d))`.
    -- Apply `integral_indicator` then identify the resulting restricted measures.
    have heq :
        (∫ x in UnitCube d, S.indicator (fun y =>
              hjbResidual V H Du m u y) x ∂(volume : Measure (Fin d → ℝ))) =
            ∫ x in S, hjbResidual V H Du m u x
              ∂(volume.restrict (UnitCube d)) := by
      -- After `integral_indicator hSmeas`, LHS becomes
      -- `∫ x in S, hjbResidual ∂(volume.restrict (UnitCube d))`, which
      -- syntactically matches the RHS.
      rw [integral_indicator hSmeas]
    rw [heq] at hpair
    exact hpair
  -- Step 2. Apply `ae_nonneg_of_forall_setIntegral_nonneg` to get
  -- `0 ≤ hjbResidual` a.e. on the cube (with the restricted measure).
  have hres_nonneg :
      0 ≤ᵐ[volume.restrict (UnitCube d)] hjbResidual V H Du m u := by
    apply ae_nonneg_of_forall_setIntegral_nonneg hRes
    intro S hSmeas hSfin
    exact hSetIntegral S hSmeas hSfin
  -- Step 3. Translate `0 ≤ -u - H + V` into `u + H - V ≤ 0`.
  refine hres_nonneg.mono ?_
  intro x hx
  -- `hx : (0 : (Fin d → ℝ) → ℝ) x ≤ hjbResidual V H Du m u x`, i.e.
  -- after Pi.zero_apply / unfold: `0 ≤ -(u x) - H x (Du · x) (m x) + V x`.
  -- Goal: `u x + H x (Du · x) (m x) - V x ≤ 0`
  have hx' : (0 : ℝ) ≤ -(u x) - H x (fun i => Du i x) (m x) + V x := by
    simpa [hjbResidual, Pi.zero_apply] using hx
  linarith

/-! ## Sanity checks -/

/-- **Unit test**: at the trivial Hamiltonian `H = 0, DpH = 0`, with `V = 0`,
`m = 1`, `u = 0`, gradient family `Du = 0`, the residual `hjbResidual` is
identically `0`, so the test-pair reduction is the integral of `0 * η`. -/
example (η : (Fin d → ℝ) → ℝ) :
    mfgOperatorEpsPair (d := d)
        (V := fun _ => (0 : ℝ))
        (H := fun _ _ _ => (0 : ℝ))
        (DpH := fun _ _ _ => (0 : Fin d → ℝ))
        (γBar := (2 : ℝ)) (ε := (0 : ℝ))
        (fun _ _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ))
        (fun _ _ => (0 : ℝ)) η (fun _ => (0 : ℝ)) =
      ∫ x in UnitCube d, hjbResidual
            (fun _ : Fin d → ℝ => (0 : ℝ))
            (fun _ _ _ => (0 : ℝ))
            (fun _ _ => (0 : ℝ))
            (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ)) x * η x
        ∂(volume : Measure (Fin d → ℝ)) :=
  mfgOperatorEpsPair_test_zero_eq_residual
    (V := fun _ => (0 : ℝ))
    (H := fun _ _ _ => (0 : ℝ))
    (DpH := fun _ _ _ => (0 : Fin d → ℝ))
    (γBar := (2 : ℝ)) (ε := (0 : ℝ))
    (fun _ _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ)) η

/-- **Unit test**: in the trivial setting, the HJB residual is identically `0`,
so the inequality `u + H − V ≤ 0` a.e. holds (it is `0 ≤ 0`). -/
example :
    ∀ᵐ x ∂(volume.restrict (UnitCube (d := d))),
      ((fun _ : Fin d → ℝ => (0 : ℝ)) x)
        + (fun (_ : Fin d → ℝ) (_ : Fin d → ℝ) (_ : ℝ) => (0 : ℝ))
            x (fun i => (fun (_ : Fin d) (_ : Fin d → ℝ) => (0 : ℝ)) i x)
            ((fun _ : Fin d → ℝ => (1 : ℝ)) x)
        - (fun _ : Fin d → ℝ => (0 : ℝ)) x ≤ 0 := by
  refine Filter.Eventually.of_forall ?_
  intro x
  simp

/-! ## Part (b): the HJB equality `(u + H − V) · m = 0` a.e. on the cube

Paper line 1156, eq. `eq:HJ0`. The argument tests the strong VI at
`(μ, υ) = (m(1 ± φ/‖φ‖_∞), u)` for arbitrary nonzero smooth `φ`. The pairing
reduces to `±∫_{𝕋^d} (−u − H + V) m φ dx ≥ 0` (the factor `1/‖φ‖_∞` is positive
and divides out), so this integral vanishes for every smooth `φ`, hence
`(u + H − V) · m = 0` a.e.

We use the same set-form specialization as in part (a): take `φ` to be the
indicator of an arbitrary measurable `S ⊆ UnitCube d`. The test pairs
`(m + m·1_S, u)` and `(m − m·1_S, u)` are admissible because `m ≥ 0` and
`0 ≤ 1_S ≤ 1`. -/

/-- **Signed set-test-pair specialization of the strong VI.** Records that the
regularized MFG pairing of `A_ε[m, u]` against the test pair
`(η, ν, Dν) = (σ · m · 1_S, 0, 0)` is non-negative for every measurable
`S ⊆ UnitCube d` of finite restricted-cube measure and every sign
`σ ∈ {+1, −1}`. This is the specialization of the strong VI at
`(μ, υ) = (m(1 + σ · 1_S), u)`; it is admissible since `m ≥ 0` and `0 ≤ 1_S ≤ 1`. -/
def StrongVI_setForm_signed
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (γBar ε : ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ) : Prop :=
  ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
    ∀ S : Set (Fin d → ℝ), MeasurableSet S →
      (volume.restrict (UnitCube d)) S < ∞ →
      0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH) γBar ε Du m u
            (fun _ _ => (0 : ℝ))
            (fun x => σ * (m x) * S.indicator (fun _ => (1 : ℝ)) x)
            (fun _ => (0 : ℝ))

/-- **`lem:strong.is.strong`, part (b)** (paper line 1156, eq. `eq:HJ0`).

Under the signed set-test-pair form of the strong VI and integrability of the
pointwise product `hjbResidual · m` on the cube, the residual times the density
vanishes a.e.:
```
(-u(x) - H(x, Du(x), m(x)) + V(x)) · m(x) = 0   for a.e. x ∈ UnitCube d.
```
Equivalently, since `m ≥ 0`, this is the paper's `u + H − V = 0` a.e. on
`{m > 0}`. -/
theorem lem_strong_is_strong_HJB_eq
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (γBar ε : ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (hResM : Integrable (fun x => hjbResidual V H Du m u x * m x)
              (volume.restrict (UnitCube d)))
    (hVI : StrongVI_setForm_signed V H DpH γBar ε Du m u) :
    (fun x => hjbResidual V H Du m u x * m x)
      =ᵐ[volume.restrict (UnitCube d)] 0 := by
  -- Step 1. From `hVI` (with both signs), deduce `∫_S (hjbResidual · m) dx = 0`
  -- for every measurable `S` of finite restricted-cube measure.
  have hSetIntegralZero :
      ∀ S : Set (Fin d → ℝ), MeasurableSet S →
        (volume.restrict (UnitCube d)) S < ∞ →
        ∫ x in S, hjbResidual V H Du m u x * m x
              ∂(volume.restrict (UnitCube d)) = 0 := by
    intro S hSmeas hSfin
    -- Reduce both `±` pairings to `±∫_S hjbResidual · m`.
    -- Helper: at sign σ, the pairing equals σ · ∫_S hjbResidual · m.
    have hreduceSign :
        ∀ σ : ℝ,
          mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH) γBar ε Du m u
              (fun _ _ => (0 : ℝ))
              (fun x => σ * (m x) * S.indicator (fun _ => (1 : ℝ)) x)
              (fun _ => (0 : ℝ)) =
            σ * ∫ x in S, hjbResidual V H Du m u x * m x
                  ∂(volume.restrict (UnitCube d)) := by
      intro σ
      -- Apply the part-(a) reduction with `η = σ · m · 1_S`.
      rw [mfgOperatorEpsPair_test_zero_eq_residual (V := V) (H := H) (DpH := DpH)
            γBar ε Du m u
            (fun x => σ * (m x) * S.indicator (fun _ => (1 : ℝ)) x)]
      -- Pointwise: hjbResidual x * (σ · m x · 1_S(x)) = σ · 1_S(x) · (hjbResidual x · m x)
      -- = σ · S.indicator (fun y => hjbResidual y · m y) x.
      have hpoint : ∀ x : Fin d → ℝ,
          hjbResidual V H Du m u x *
              (σ * (m x) * S.indicator (fun _ => (1 : ℝ)) x)
            = σ * S.indicator (fun y => hjbResidual V H Du m u y * m y) x := by
        intro x
        by_cases hx : x ∈ S
        · simp [Set.indicator_of_mem hx]; ring
        · simp [Set.indicator_of_notMem hx]
      have hintegrand_eq :
          (fun x : Fin d → ℝ =>
              hjbResidual V H Du m u x *
                (σ * (m x) * S.indicator (fun _ => (1 : ℝ)) x))
            = (fun x : Fin d → ℝ =>
                σ * S.indicator (fun y : Fin d → ℝ =>
                    hjbResidual V H Du m u y * m y) x) := by
        funext x; exact hpoint x
      rw [hintegrand_eq]
      -- Pull the constant `σ` out and rewrite via `integral_indicator`.
      rw [integral_const_mul, integral_indicator hSmeas]
    -- Apply both signs.
    have hpos := hVI 1 (Or.inl rfl) S hSmeas hSfin
    have hneg := hVI (-1) (Or.inr rfl) S hSmeas hSfin
    rw [hreduceSign 1] at hpos
    rw [hreduceSign (-1)] at hneg
    have hpos' : 0 ≤ ∫ x in S, hjbResidual V H Du m u x * m x
                      ∂(volume.restrict (UnitCube d)) := by
      have := hpos; linarith
    have hneg' : ∫ x in S, hjbResidual V H Du m u x * m x
                      ∂(volume.restrict (UnitCube d)) ≤ 0 := by
      have := hneg
      -- `(-1) * I ≥ 0` ⇒ `I ≤ 0`.
      linarith
    linarith
  -- Step 2. Apply `Integrable.ae_eq_zero_of_forall_setIntegral_eq_zero`.
  exact hResM.ae_eq_zero_of_forall_setIntegral_eq_zero hSetIntegralZero

/-- **Corollary**: under the signed set-form of the strong VI, the paper-form
of `eq:HJ0` holds: `(u + H(x, Du, m) − V(x)) · m(x) = 0` for a.e. `x` on the cube.
This is just the negation rearrangement of `lem_strong_is_strong_HJB_eq`. -/
theorem lem_strong_is_strong_HJB_eq_paperForm
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (γBar ε : ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (hResM : Integrable (fun x => hjbResidual V H Du m u x * m x)
              (volume.restrict (UnitCube d)))
    (hVI : StrongVI_setForm_signed V H DpH γBar ε Du m u) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      (u x + H x (fun i => Du i x) (m x) - V x) * m x = 0 := by
  have hres := lem_strong_is_strong_HJB_eq (V := V) (H := H) (DpH := DpH)
      γBar ε Du m u hResM hVI
  -- `hres : (hjbResidual · m) =ᵐ 0`. Translate into `(u + H − V) · m = 0` a.e.
  refine hres.mono ?_
  intro x hx
  -- `hx : hjbResidual V H Du m u x * m x = (0 : (Fin d → ℝ) → ℝ) x`.
  have hx' : (-(u x) - H x (fun i => Du i x) (m x) + V x) * m x = 0 := by
    simpa [hjbResidual, Pi.zero_apply] using hx
  -- Goal: `(u x + H x (Du · x) (m x) - V x) * m x = 0`. Negate the factor.
  have hsymm :
      (u x + H x (fun i => Du i x) (m x) - V x) * m x =
        -((-(u x) - H x (fun i => Du i x) (m x) + V x) * m x) := by ring
  rw [hsymm, hx', neg_zero]

/-! ### Sanity checks for part (b) -/

/-- **Unit test**: in the trivial setting (`H = 0, DpH = 0, V = 0, m = 0, u = 0,
Du = 0`), the residual times `m` is identically `0`, so `eq:HJ0` is trivial. -/
example :
    ∀ᵐ x ∂(volume.restrict (UnitCube (d := d))),
      ((fun _ : Fin d → ℝ => (0 : ℝ)) x
        + (fun (_ : Fin d → ℝ) (_ : Fin d → ℝ) (_ : ℝ) => (0 : ℝ))
            x (fun i => (fun (_ : Fin d) (_ : Fin d → ℝ) => (0 : ℝ)) i x)
            ((fun _ : Fin d → ℝ => (0 : ℝ)) x)
        - (fun _ : Fin d → ℝ => (0 : ℝ)) x)
        * (fun _ : Fin d → ℝ => (0 : ℝ)) x = 0 := by
  refine Filter.Eventually.of_forall ?_
  intro x
  simp

/-! ## Part (c): the regularized weak transport equation

Paper line 1158, eq. `eq:strong-transport`. The argument tests the strong VI at
`(μ, υ) = (m, u ± φ)` for an arbitrary smooth periodic test function `φ`. The
operator pairing reduces to
```
± ∫_{𝕋^d} [(m - 1) φ + m · D_pH(x, Du, m) · Dφ
           + ε |Du|^{γ̄-2} Du · Dφ + ε |u|^{γ̄-2} u · φ] dx ≥ 0,
```
so the bracketed integral vanishes for every smooth `φ`, which is the
regularized form of `eq:strong-transport`. (At `ε = 0` the regularization
terms drop out and we recover the standard weak transport equation
`∫ [(m - 1) φ + m DpH · Dφ] dx = 0` of `IsStrongSolution_Transport`.)

Per the paper, `φ` is arbitrary in `W^{1,γ̄}_per`; we land the conclusion at
`φ ∈ SmoothPeriodic d`, the smooth-test class. Extension to `W^{1,γ̄}_per`
goes through `SmoothPeriodic.denseInSobolevPer` (Phase 1 task
`infra:P1-density`); this extension is left as a separate downstream task.
-/

/-- **Transport-form specialization of the strong VI** (paper line 1185). Records
that the regularized MFG pairing of `A_ε[m, u]` against the test pair
`(η, ν, Dν) = (0, σ · φ, σ · Dφ)` is non-negative for every smooth periodic
test function `φ` and every sign `σ ∈ {+1, −1}`.

This is the specialization of the strong variational inequality at the test
pair `(μ, υ) = (m, u + σ · φ)`; it is admissible since `μ = m ≥ 0` is preserved
and `u + σ · φ ∈ W^{1,γ̄}_per` is preserved (smooth periodics inject into the
Sobolev space, which is closed under addition). -/
def StrongVI_transportForm
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (γBar ε : ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ) : Prop :=
  ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
    ∀ φ : SmoothPeriodic d,
      0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH) γBar ε Du m u
            (fun i x => σ *
              ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x)
            (fun _ => (0 : ℝ))
            (fun x => σ * (φ : (Fin d → ℝ) → ℝ) x)

/-- The two-piece transport integrand of `eq:strong-transport`, encoded as a
**pair** of summed integrals matching the structure of `mfgOperatorEpsPair`:
the **MFG-flux part** `(m - 1) φ + m · (D_pH(x, Du, m) · Dφ)` and the
**γ̄-Laplacian Gateaux part** `|Du|^{γ̄-2} Du · Dφ + |u|^{γ̄-2} u · φ`. The
total bracketed integrand of paper eq. `eq:strong-transport` (line 1160) is
their `+ ε ·` combination. We expose the two-integral form to avoid
integrability hypotheses for the algebraic reduction below; consumers can
reassemble the bracketed integrand under their own integrability bridge. -/
def transportFluxIntegrand
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m : (Fin d → ℝ) → ℝ)
    (φ : SmoothPeriodic d) : (Fin d → ℝ) → ℝ :=
  fun x =>
    (m x - 1) * (φ : (Fin d → ℝ) → ℝ) x
      + m x * (DpH x (fun i => Du i x) (m x)
                ⬝ (fun i =>
                  ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                    (Fin d → ℝ) → ℝ) x))

/-- The γ̄-Laplacian Gateaux integrand `|Du|^{γ̄-2} Du · Dφ + |u|^{γ̄-2} u φ`. -/
def transportGateauxIntegrand
    (γBar : ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (u : (Fin d → ℝ) → ℝ)
    (φ : SmoothPeriodic d) : (Fin d → ℝ) → ℝ :=
  fun x =>
    vecAbsPowMinusTwo γBar (fun i => Du i x)
          * ((fun i => Du i x) ⬝ (fun i =>
            ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) x))
        + absPowMinusTwo γBar (u x) * (u x * (φ : (Fin d → ℝ) → ℝ) x)

/-- Auxiliary algebraic identity: scalar multiplication distributes through
`dotProduct` in the right slot. -/
private lemma euclideanDot_const_smul_right {d : ℕ} (σ : ℝ) (v w : Fin d → ℝ) :
    v ⬝ (fun i => σ * w i) = σ * (v ⬝ w) := by
  unfold dotProduct
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  ring

/-- **Key reduction**: at the test pair `(η, ν, Dν) = (0, σ · φ, σ · Dφ)` with
`φ ∈ SmoothPeriodic d` and `σ : ℝ`, the regularized MFG pairing of `A_ε[m, u]`
collapses to
```
σ · (∫_{𝕋^d} transportFluxIntegrand dx
      + ε · ∫_{𝕋^d} transportGateauxIntegrand dx).
```

Proof: unfold `mfgOperatorEpsPair`, `mfgOperatorPair`, `gateauxWpPair`. The
`(- u - H + V) * η` summand vanishes since `η = 0`. The remaining summands
factor pointwise as `σ · (…)` (the `σ` enters in two places: directly in
`(m − 1) · ν = (m − 1) · (σ φ)` and inside the dot products `… ⬝ (σ Dφ)`).
Pull `σ` out of each integral via `integral_const_mul`; rearrange the
resulting `σ · I₁ + ε · (σ · I₂) = σ · (I₁ + ε · I₂)` by ring.

This is the part-(c) analogue of `mfgOperatorEpsPair_test_zero_eq_residual`
(part-(a)). -/
theorem mfgOperatorEpsPair_test_first_zero_eq_transport
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (γBar ε σ : ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (φ : SmoothPeriodic d) :
    mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH) γBar ε Du m u
        (fun i x => σ *
          ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) x)
        (fun _ => (0 : ℝ))
        (fun x => σ * (φ : (Fin d → ℝ) → ℝ) x) =
      σ * ((∫ x in UnitCube d, transportFluxIntegrand DpH Du m φ x
              ∂(volume : Measure (Fin d → ℝ))) +
            ε * ∫ x in UnitCube d, transportGateauxIntegrand γBar Du u φ x
              ∂(volume : Measure (Fin d → ℝ))) := by
  unfold mfgOperatorEpsPair mfgOperatorPair gateauxWpPair
    transportFluxIntegrand transportGateauxIntegrand
  -- Pointwise rewrites factoring σ.
  have h_int1_pointwise : ∀ x : Fin d → ℝ,
      ((-(u x) - H x (fun i => Du i x) (m x) + V x) * (0 : ℝ)
        + m x * (DpH x (fun i => Du i x) (m x)
                  ⬝ (fun i : Fin d => σ *
                    ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                      (Fin d → ℝ) → ℝ) x))
        + (m x - 1) * (σ * (φ : (Fin d → ℝ) → ℝ) x))
      = σ * ((m x - 1) * (φ : (Fin d → ℝ) → ℝ) x
              + m x * (DpH x (fun i => Du i x) (m x)
                        ⬝ (fun i : Fin d =>
                          ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                            (Fin d → ℝ) → ℝ) x))) := by
    intro x
    rw [euclideanDot_const_smul_right σ (DpH x (fun i => Du i x) (m x))
        (fun i => ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                    (Fin d → ℝ) → ℝ) x)]
    ring
  have h_int2_pointwise : ∀ x : Fin d → ℝ,
      vecAbsPowMinusTwo γBar (fun i => Du i x)
            * ((fun i : Fin d => Du i x) ⬝ (fun i : Fin d => σ *
                ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x))
          + absPowMinusTwo γBar (u x) *
              (u x * (σ * (φ : (Fin d → ℝ) → ℝ) x))
      = σ * (vecAbsPowMinusTwo γBar (fun i => Du i x)
                * ((fun i : Fin d => Du i x) ⬝ (fun i : Fin d =>
                    ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                      (Fin d → ℝ) → ℝ) x))
              + absPowMinusTwo γBar (u x) *
                  (u x * (φ : (Fin d → ℝ) → ℝ) x)) := by
    intro x
    rw [euclideanDot_const_smul_right σ (fun i => Du i x)
        (fun i => ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                    (Fin d → ℝ) → ℝ) x)]
    ring
  -- Congruence: rewrite each integrand as `σ * (…)`.
  have hint1_eq :
      (∫ x in UnitCube d,
          (-(u x) - H x (fun i => Du i x) (m x) + V x) * (0 : ℝ)
            + m x * (DpH x (fun i => Du i x) (m x)
                      ⬝ (fun i : Fin d => σ *
                        ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                          (Fin d → ℝ) → ℝ) x))
            + (m x - 1) * (σ * (φ : (Fin d → ℝ) → ℝ) x)
          ∂(volume : Measure (Fin d → ℝ))) =
        σ * ∫ x in UnitCube d,
              (m x - 1) * (φ : (Fin d → ℝ) → ℝ) x
                + m x * (DpH x (fun i => Du i x) (m x)
                          ⬝ (fun i : Fin d =>
                            ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                              (Fin d → ℝ) → ℝ) x))
              ∂(volume : Measure (Fin d → ℝ)) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_unitCube ?_
    intro x _
    exact h_int1_pointwise x
  have hint2_eq :
      (∫ x in UnitCube d,
          vecAbsPowMinusTwo γBar (fun i => Du i x)
                * ((fun i : Fin d => Du i x) ⬝ (fun i : Fin d => σ *
                    ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                      (Fin d → ℝ) → ℝ) x))
              + absPowMinusTwo γBar (u x) *
                  (u x * (σ * (φ : (Fin d → ℝ) → ℝ) x))
          ∂(volume : Measure (Fin d → ℝ))) =
        σ * ∫ x in UnitCube d,
              vecAbsPowMinusTwo γBar (fun i => Du i x)
                    * ((fun i : Fin d => Du i x) ⬝ (fun i : Fin d =>
                        ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                          (Fin d → ℝ) → ℝ) x))
                  + absPowMinusTwo γBar (u x) *
                      (u x * (φ : (Fin d → ℝ) → ℝ) x)
              ∂(volume : Measure (Fin d → ℝ)) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_unitCube ?_
    intro x _
    exact h_int2_pointwise x
  rw [hint1_eq, hint2_eq]
  ring

/-! ## Main theorem: regularized weak transport equation from the strong VI -/

/-- **`lem:strong.is.strong`, part (c)** (paper line 1158, eq. `eq:strong-transport`).

Under the transport-form specialization `StrongVI_transportForm` of the strong
variational inequality, for every smooth periodic test function `φ` the
regularized transport bracketed integral splits into the unregularized
flux part and the γ̄-Laplacian Gateaux part, and the linear combination
```
∫_{𝕋^d} transportFluxIntegrand DpH Du m φ dx
   + ε · ∫_{𝕋^d} transportGateauxIntegrand γBar Du u φ dx = 0
```
holds. Equivalently, this is the paper's eq. `eq:strong-transport`:
```
∫_{𝕋^d} [(m - 1) φ + m · D_pH(x, Du, m) · Dφ
         + ε |Du|^{γ̄-2} Du · Dφ + ε |u|^{γ̄-2} u · φ] dx = 0.
```

Proof: testing `(η, ν, Dν) = (0, ±φ, ±Dφ)` (paper choice
`(μ, υ) = (m, u ± φ)` of line 1185), the strong VI gives
`±(I₁ + ε · I₂) ≥ 0`, where `I₁ = ∫ transportFluxIntegrand` and
`I₂ = ∫ transportGateauxIntegrand`. Combining the two signs forces
`I₁ + ε · I₂ = 0`, by `mfgOperatorEpsPair_test_first_zero_eq_transport`. -/
theorem lem_strong_is_strong_transport
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (γBar ε : ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (hVI : StrongVI_transportForm V H DpH γBar ε Du m u) :
    ∀ φ : SmoothPeriodic d,
      (∫ x in UnitCube d, transportFluxIntegrand DpH Du m φ x
          ∂(volume : Measure (Fin d → ℝ))) +
        ε * ∫ x in UnitCube d, transportGateauxIntegrand γBar Du u φ x
              ∂(volume : Measure (Fin d → ℝ)) = 0 := by
  intro φ
  -- Apply the reduction to both signs.
  have hpos := hVI 1 (Or.inl rfl) φ
  have hneg := hVI (-1) (Or.inr rfl) φ
  rw [mfgOperatorEpsPair_test_first_zero_eq_transport
        (V := V) (H := H) (DpH := DpH) γBar ε 1 Du m u φ] at hpos
  rw [mfgOperatorEpsPair_test_first_zero_eq_transport
        (V := V) (H := H) (DpH := DpH) γBar ε (-1) Du m u φ] at hneg
  -- `hpos : 0 ≤ 1 * (I₁ + ε * I₂)` and `hneg : 0 ≤ (-1) * (I₁ + ε * I₂)`.
  set I₁ : ℝ := ∫ x in UnitCube d, transportFluxIntegrand DpH Du m φ x
      ∂(volume : Measure (Fin d → ℝ)) with hI₁
  set I₂ : ℝ := ∫ x in UnitCube d, transportGateauxIntegrand γBar Du u φ x
      ∂(volume : Measure (Fin d → ℝ)) with hI₂
  -- After substitution: `0 ≤ I₁ + ε · I₂` and `0 ≤ -(I₁ + ε · I₂)`.
  have hpos' : 0 ≤ I₁ + ε * I₂ := by linarith
  have hneg' : I₁ + ε * I₂ ≤ 0 := by linarith
  linarith

/-! ## Sanity checks for part (c) -/

/-- **Unit test**: in the trivial setting (`H = 0, DpH = 0, V = 0, m = 1, u = 0,
Du = 0`), the reduction theorem applies and rewrites the operator pairing in
the displayed form. -/
example (γBar ε σ : ℝ) (φ : SmoothPeriodic d) :
    mfgOperatorEpsPair (d := d)
        (V := fun _ => (0 : ℝ))
        (H := fun _ _ _ => (0 : ℝ))
        (DpH := fun _ _ _ => (0 : Fin d → ℝ))
        γBar ε
        (fun _ _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ))
        (fun i x => σ *
          ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) x)
        (fun _ => (0 : ℝ))
        (fun x => σ * (φ : (Fin d → ℝ) → ℝ) x) =
      σ * ((∫ x in UnitCube d,
              transportFluxIntegrand (fun _ _ _ => (0 : Fin d → ℝ))
                (fun _ _ => (0 : ℝ)) (fun _ => (1 : ℝ)) φ x
              ∂(volume : Measure (Fin d → ℝ))) +
            ε * ∫ x in UnitCube d,
              transportGateauxIntegrand γBar
                (fun _ _ => (0 : ℝ)) (fun _ => (0 : ℝ)) φ x
              ∂(volume : Measure (Fin d → ℝ))) :=
  mfgOperatorEpsPair_test_first_zero_eq_transport
    (V := fun _ => (0 : ℝ))
    (H := fun _ _ _ => (0 : ℝ))
    (DpH := fun _ _ _ => (0 : Fin d → ℝ))
    γBar ε σ
    (fun _ _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ)) φ

end SimplePower
end Theorems
end StationaryMFG
