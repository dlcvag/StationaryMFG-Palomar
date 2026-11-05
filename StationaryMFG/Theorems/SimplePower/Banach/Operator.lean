module

public import StationaryMFG.Solutions.Regularized
public import StationaryMFG.Periodic.LpDuality
public import StationaryMFG.Periodic.LpInclusion
public import StationaryMFG.Periodic.Sobolev

@[expose] public section

/-!
# ℝ-linearity of `mfgOperatorEpsPair` in the test triple

This module discharges Block A.1 of the Banach-bridge plan:
**linearity of the regularized MFG operator pairing
`mfgOperatorEpsPair` in the test triple `(η, ν, Dν)`**.

For fixed primal datum `(Dυ, μ, υ)` and parameters
`(γBar, ε, V, H, DpH)`, the map

```
(η, ν, Dν) ↦ mfgOperatorEpsPair γBar ε V H DpH Dυ μ υ Dν η ν
```

is ℝ-linear. The integrand of `mfgOperatorEpsPair` (paper line 925,
`defAepsi`) is *pointwise* linear in the test triple, so each lemma
reduces, via `setIntegral_congr_fun`, to a pointwise algebraic
identity together with the standard integral linearity
(`integral_add`, `integral_const_mul`, `integral_zero`,
`integral_neg`).

We expose four lemmas:

* `mfgOperatorEpsPair_test_zero` — value at the zero test triple is
  `0`.
* `mfgOperatorEpsPair_test_add` — additivity in the test triple
  (carries an integrability side-condition on each summand of the
  integrand, which is the standard side condition for splitting an
  integral of a sum).
* `mfgOperatorEpsPair_test_smul` — homogeneity in the test triple.
* `mfgOperatorEpsPair_test_neg` — negation in the test triple.

After Blocks A.2 (boundedness in operator norm) and A.3 (assembly),
`mfgOperatorEpsPair` lifts to a continuous linear map
`A_ε : 𝓚 → StrongDual ℝ X`, consumable by Phase 3's Browder–Minty
machinery.
-/

noncomputable section

namespace StationaryMFG
namespace Theorems
namespace SimplePower
namespace Banach

open MeasureTheory Set
open StationaryMFG.Periodic
open StationaryMFG.Hamiltonian
open StationaryMFG.Solutions.MFG
open scoped ENNReal

variable {d : ℕ}

/-! ## Pointwise integrand identities

The first integrand (from `mfgOperatorPair`) is

```
mfgPairIntegrand x = (-(υ x) - H x (Dυ x) (μ x) + V x) * η x
                   + μ x * (DpH x (Dυ x) (μ x) ⬝ Dν x)
                   + (μ x - 1) * ν x
```

The second (from `gateauxWpPair`) is

```
gateauxIntegrand x = vecAbsPowMinusTwo γBar (Dυ x) * (Dυ x ⬝ Dν x)
                   + absPowMinusTwo γBar (υ x) * (υ x * ν x)
```

Both are pointwise linear in the test triple `(η, ν, Dν)`. -/

private lemma euclideanDot_add_right
    (v w₁ w₂ : Fin d → ℝ) :
    v ⬝ (w₁ + w₂) = v ⬝ w₁ + v ⬝ w₂ := by
  unfold euclideanDot
  simp [Pi.add_apply, mul_add, Finset.sum_add_distrib]

private lemma euclideanDot_smul_right
    (c : ℝ) (v w : Fin d → ℝ) :
    v ⬝ (c • w) = c * (v ⬝ w) := by
  unfold euclideanDot
  simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm]

private lemma euclideanDot_neg_right
    (v w : Fin d → ℝ) :
    v ⬝ (-w) = -(v ⬝ w) := by
  unfold euclideanDot
  simp [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

private lemma euclideanDot_zero_right_fun
    (v : Fin d → ℝ) :
    v ⬝ (fun _ : Fin d => (0 : ℝ)) = 0 := by
  unfold euclideanDot
  simp

/-- Pointwise additivity of the `mfgOperatorPair`-integrand in the test
triple. -/
private lemma mfgPair_integrand_test_add
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (μ υ : (Fin d → ℝ) → ℝ)
    (Dν₁ Dν₂ : Fin d → (Fin d → ℝ) → ℝ)
    (η₁ η₂ ν₁ ν₂ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * ((η₁ + η₂) x)
        + μ x * (DpH x (fun i => Dυ i x) (μ x)
                  ⬝ (fun i => (Dν₁ i + Dν₂ i) x))
        + (μ x - 1) * ((ν₁ + ν₂) x)
      = ((-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (η₁ x)
            + μ x * (DpH x (fun i => Dυ i x) (μ x)
                      ⬝ (fun i => Dν₁ i x))
            + (μ x - 1) * (ν₁ x))
        + ((-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (η₂ x)
            + μ x * (DpH x (fun i => Dυ i x) (μ x)
                      ⬝ (fun i => Dν₂ i x))
            + (μ x - 1) * (ν₂ x)) := by
  set p : Fin d → ℝ := DpH x (fun i => Dυ i x) (μ x)
  have hsum : (fun i => (Dν₁ i + Dν₂ i) x) =
      (fun i => Dν₁ i x) + (fun i => Dν₂ i x) := by
    funext i; simp [Pi.add_apply]
  rw [hsum, euclideanDot_add_right]
  simp [Pi.add_apply]; ring

/-- Pointwise additivity of the `gateauxWpPair`-integrand in the test
pair `(ν, Dν)`. -/
private lemma gateaux_integrand_test_add
    (γBar : ℝ)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (υ : (Fin d → ℝ) → ℝ)
    (Dν₁ Dν₂ : Fin d → (Fin d → ℝ) → ℝ)
    (ν₁ ν₂ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    vecAbsPowMinusTwo γBar (fun i => Dυ i x)
          * ((fun i => Dυ i x) ⬝ (fun i => (Dν₁ i + Dν₂ i) x))
        + absPowMinusTwo γBar (υ x) * (υ x * ((ν₁ + ν₂) x))
      = (vecAbsPowMinusTwo γBar (fun i => Dυ i x)
              * ((fun i => Dυ i x) ⬝ (fun i => Dν₁ i x))
            + absPowMinusTwo γBar (υ x) * (υ x * (ν₁ x)))
        + (vecAbsPowMinusTwo γBar (fun i => Dυ i x)
              * ((fun i => Dυ i x) ⬝ (fun i => Dν₂ i x))
            + absPowMinusTwo γBar (υ x) * (υ x * (ν₂ x))) := by
  have hsum : (fun i => (Dν₁ i + Dν₂ i) x) =
      (fun i => Dν₁ i x) + (fun i => Dν₂ i x) := by
    funext i; simp [Pi.add_apply]
  rw [hsum, euclideanDot_add_right]
  simp [Pi.add_apply]; ring

/-- Pointwise homogeneity of the `mfgOperatorPair`-integrand in the test
triple. -/
private lemma mfgPair_integrand_test_smul
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (μ υ : (Fin d → ℝ) → ℝ)
    (c : ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * ((c • η) x)
        + μ x * (DpH x (fun i => Dυ i x) (μ x)
                  ⬝ (fun i => (c • Dν i) x))
        + (μ x - 1) * ((c • ν) x)
      = c * ((-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (η x)
            + μ x * (DpH x (fun i => Dυ i x) (μ x)
                      ⬝ (fun i => Dν i x))
            + (μ x - 1) * (ν x)) := by
  have hsmul : (fun i => (c • Dν i) x) = c • (fun i => Dν i x) := by
    funext i; simp [Pi.smul_apply]
  rw [hsmul, euclideanDot_smul_right]
  simp [Pi.smul_apply, smul_eq_mul]; ring

/-- Pointwise homogeneity of the `gateauxWpPair`-integrand in the test
pair `(ν, Dν)`. -/
private lemma gateaux_integrand_test_smul
    (γBar : ℝ)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (υ : (Fin d → ℝ) → ℝ)
    (c : ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (ν : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    vecAbsPowMinusTwo γBar (fun i => Dυ i x)
          * ((fun i => Dυ i x) ⬝ (fun i => (c • Dν i) x))
        + absPowMinusTwo γBar (υ x) * (υ x * ((c • ν) x))
      = c * (vecAbsPowMinusTwo γBar (fun i => Dυ i x)
              * ((fun i => Dυ i x) ⬝ (fun i => Dν i x))
            + absPowMinusTwo γBar (υ x) * (υ x * (ν x))) := by
  have hsmul : (fun i => (c • Dν i) x) = c • (fun i => Dν i x) := by
    funext i; simp [Pi.smul_apply]
  rw [hsmul, euclideanDot_smul_right]
  simp [Pi.smul_apply, smul_eq_mul]; ring

/-- Pointwise vanishing of the `mfgOperatorPair`-integrand at the zero
test triple. -/
private lemma mfgPair_integrand_test_zero
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (μ υ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * ((0 : (Fin d → ℝ) → ℝ) x)
        + μ x * (DpH x (fun i => Dυ i x) (μ x)
                  ⬝ (fun i => ((0 : Fin d → (Fin d → ℝ) → ℝ) i) x))
        + (μ x - 1) * ((0 : (Fin d → ℝ) → ℝ) x)
      = 0 := by
  have hzero : (fun i => ((0 : Fin d → (Fin d → ℝ) → ℝ) i) x) =
      (fun _ : Fin d => (0 : ℝ)) := by
    funext i; simp
  rw [hzero, euclideanDot_zero_right_fun]
  simp

private lemma gateaux_integrand_test_zero
    (γBar : ℝ)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (υ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    vecAbsPowMinusTwo γBar (fun i => Dυ i x)
          * ((fun i => Dυ i x) ⬝
              (fun i => ((0 : Fin d → (Fin d → ℝ) → ℝ) i) x))
        + absPowMinusTwo γBar (υ x) * (υ x * ((0 : (Fin d → ℝ) → ℝ) x))
      = 0 := by
  have hzero : (fun i => ((0 : Fin d → (Fin d → ℝ) → ℝ) i) x) =
      (fun _ : Fin d => (0 : ℝ)) := by
    funext i; simp
  rw [hzero, euclideanDot_zero_right_fun]
  simp

/-! ## The four linearity lemmas -/

variable (V : (Fin d → ℝ) → ℝ)
variable (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
variable (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))

/-- **Vanishing of `mfgOperatorEpsPair` on the zero test triple.**

For every fixed primal datum `(Dυ, μ, υ)` and parameters
`(γBar, ε, V, H, DpH)`,

```
mfgOperatorEpsPair … Dυ μ υ 0 0 0 = 0.
```

Proved by reducing pointwise to `0` and integrating. -/
theorem mfgOperatorEpsPair_test_zero (γBar ε : ℝ)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (μ υ : (Fin d → ℝ) → ℝ) :
    mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
        γBar ε Dυ μ υ
        (0 : Fin d → (Fin d → ℝ) → ℝ)
        (0 : (Fin d → ℝ) → ℝ)
        (0 : (Fin d → ℝ) → ℝ) = 0 := by
  unfold mfgOperatorEpsPair mfgOperatorPair gateauxWpPair
  have hA : ∫ x in UnitCube d,
      (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) *
            ((0 : (Fin d → ℝ) → ℝ) x)
        + μ x * (DpH x (fun i => Dυ i x) (μ x)
                  ⬝ (fun i => ((0 : Fin d → (Fin d → ℝ) → ℝ) i) x))
        + (μ x - 1) * ((0 : (Fin d → ℝ) → ℝ) x)
      ∂(volume : Measure (Fin d → ℝ)) = 0 := by
    have hcong :
        (fun x =>
          (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) *
                ((0 : (Fin d → ℝ) → ℝ) x)
            + μ x * (DpH x (fun i => Dυ i x) (μ x)
                      ⬝ (fun i => ((0 : Fin d → (Fin d → ℝ) → ℝ) i) x))
            + (μ x - 1) * ((0 : (Fin d → ℝ) → ℝ) x))
          = (fun _ => (0 : ℝ)) := by
      funext x
      exact mfgPair_integrand_test_zero V H DpH Dυ μ υ x
    rw [show (fun x =>
            (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) *
                  ((0 : (Fin d → ℝ) → ℝ) x)
              + μ x * (DpH x (fun i => Dυ i x) (μ x)
                        ⬝ (fun i => ((0 : Fin d → (Fin d → ℝ) → ℝ) i) x))
              + (μ x - 1) * ((0 : (Fin d → ℝ) → ℝ) x)) =
          (fun _ => (0 : ℝ)) from hcong]
    simp
  have hB : ∫ x in UnitCube d,
      vecAbsPowMinusTwo γBar (fun i => Dυ i x)
            * ((fun i => Dυ i x) ⬝
                (fun i => ((0 : Fin d → (Fin d → ℝ) → ℝ) i) x))
          + absPowMinusTwo γBar (υ x)
              * (υ x * ((0 : (Fin d → ℝ) → ℝ) x))
        ∂(volume : Measure (Fin d → ℝ)) = 0 := by
    have hcong :
        (fun x =>
          vecAbsPowMinusTwo γBar (fun i => Dυ i x)
              * ((fun i => Dυ i x) ⬝
                  (fun i => ((0 : Fin d → (Fin d → ℝ) → ℝ) i) x))
            + absPowMinusTwo γBar (υ x)
                * (υ x * ((0 : (Fin d → ℝ) → ℝ) x)))
          = (fun _ => (0 : ℝ)) := by
      funext x
      exact gateaux_integrand_test_zero γBar Dυ υ x
    rw [show (fun x =>
            vecAbsPowMinusTwo γBar (fun i => Dυ i x)
                * ((fun i => Dυ i x) ⬝
                    (fun i => ((0 : Fin d → (Fin d → ℝ) → ℝ) i) x))
              + absPowMinusTwo γBar (υ x)
                  * (υ x * ((0 : (Fin d → ℝ) → ℝ) x))) =
          (fun _ => (0 : ℝ)) from hcong]
    simp
  rw [hA, hB]; ring

/-- **Homogeneity of `mfgOperatorEpsPair` in the test triple.**

For every scalar `c : ℝ` and every test triple `(η, ν, Dν)`,

```
mfgOperatorEpsPair … Dυ μ υ (c • Dν) (c • η) (c • ν)
  = c * mfgOperatorEpsPair … Dυ μ υ Dν η ν.
```

Proved pointwise (the integrand factors through `c · …`) plus
`integral_const_mul`. -/
theorem mfgOperatorEpsPair_test_smul (γBar ε : ℝ)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (μ υ : (Fin d → ℝ) → ℝ)
    (c : ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ) :
    mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
        γBar ε Dυ μ υ (fun i => c • Dν i) (c • η) (c • ν) =
      c * mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBar ε Dυ μ υ Dν η ν := by
  unfold mfgOperatorEpsPair mfgOperatorPair gateauxWpPair
  -- Pointwise rewrite each integrand to `c * (…)`.
  have hA :
      (fun x =>
        (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * ((c • η) x)
          + μ x * (DpH x (fun i => Dυ i x) (μ x)
                    ⬝ (fun i => (c • Dν i) x))
          + (μ x - 1) * ((c • ν) x))
        = (fun x => c *
            ((-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (η x)
              + μ x * (DpH x (fun i => Dυ i x) (μ x)
                        ⬝ (fun i => Dν i x))
              + (μ x - 1) * (ν x))) := by
    funext x
    exact mfgPair_integrand_test_smul V H DpH Dυ μ υ c Dν η ν x
  have hB :
      (fun x =>
        vecAbsPowMinusTwo γBar (fun i => Dυ i x)
            * ((fun i => Dυ i x) ⬝ (fun i => (c • Dν i) x))
          + absPowMinusTwo γBar (υ x) * (υ x * ((c • ν) x)))
        = (fun x => c *
            (vecAbsPowMinusTwo γBar (fun i => Dυ i x)
                * ((fun i => Dυ i x) ⬝ (fun i => Dν i x))
              + absPowMinusTwo γBar (υ x) * (υ x * (ν x)))) := by
    funext x
    exact gateaux_integrand_test_smul γBar Dυ υ c Dν ν x
  rw [hA, hB]
  rw [MeasureTheory.integral_const_mul (μ := volume.restrict (UnitCube d)) c
        (fun x =>
          (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (η x)
          + μ x * (DpH x (fun i => Dυ i x) (μ x)
                    ⬝ (fun i => Dν i x))
          + (μ x - 1) * (ν x))]
  rw [MeasureTheory.integral_const_mul (μ := volume.restrict (UnitCube d)) c
        (fun x =>
          vecAbsPowMinusTwo γBar (fun i => Dυ i x)
              * ((fun i => Dυ i x) ⬝ (fun i => Dν i x))
            + absPowMinusTwo γBar (υ x) * (υ x * (ν x)))]
  ring

/-- **Negation of `mfgOperatorEpsPair` in the test triple.**

For every test triple `(η, ν, Dν)`,

```
mfgOperatorEpsPair … Dυ μ υ (-Dν) (-η) (-ν)
  = -(mfgOperatorEpsPair … Dυ μ υ Dν η ν).
```

Specialization of `mfgOperatorEpsPair_test_smul` at `c = -1`. -/
theorem mfgOperatorEpsPair_test_neg (γBar ε : ℝ)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (μ υ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ) :
    mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
        γBar ε Dυ μ υ (fun i => -Dν i) (-η) (-ν) =
      -(mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBar ε Dυ μ υ Dν η ν) := by
  -- Specialize `_test_smul` at `c = -1`.
  have h := mfgOperatorEpsPair_test_smul (V := V) (H := H) (DpH := DpH)
              γBar ε Dυ μ υ (-1 : ℝ) Dν η ν
  -- `(-1 : ℝ) • x = -x` componentwise.
  have hDν : (fun i => ((-1 : ℝ) • Dν i)) = (fun i => -Dν i) := by
    funext i; funext x; simp [Pi.smul_apply]
  have hη : ((-1 : ℝ) • η) = (-η) := by
    funext x; simp [Pi.smul_apply]
  have hν : ((-1 : ℝ) • ν) = (-ν) := by
    funext x; simp [Pi.smul_apply]
  rw [hDν, hη, hν] at h
  rw [h]; ring

/-- **Additivity of `mfgOperatorEpsPair` in the test triple.**

For every pair of test triples `(η₁, ν₁, Dν₁)` and `(η₂, ν₂, Dν₂)`,
provided that the integrand of `mfgOperatorEpsPair` at each is
`IntegrableOn (UnitCube d)`,

```
mfgOperatorEpsPair … Dυ μ υ (Dν₁ + Dν₂) (η₁ + η₂) (ν₁ + ν₂)
  = mfgOperatorEpsPair … Dυ μ υ Dν₁ η₁ ν₁
      + mfgOperatorEpsPair … Dυ μ υ Dν₂ η₂ ν₂.
```

The integrability hypothesis is the standard side condition for
splitting an integral of a sum into a sum of integrals
(`MeasureTheory.integral_add`). -/
theorem mfgOperatorEpsPair_test_add (γBar ε : ℝ)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (μ υ : (Fin d → ℝ) → ℝ)
    (Dν₁ Dν₂ : Fin d → (Fin d → ℝ) → ℝ)
    (η₁ η₂ ν₁ ν₂ : (Fin d → ℝ) → ℝ)
    (hA₁ : IntegrableOn
      (fun x =>
        (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (η₁ x)
          + μ x * (DpH x (fun i => Dυ i x) (μ x)
                    ⬝ (fun i => Dν₁ i x))
          + (μ x - 1) * (ν₁ x))
      (UnitCube d))
    (hA₂ : IntegrableOn
      (fun x =>
        (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (η₂ x)
          + μ x * (DpH x (fun i => Dυ i x) (μ x)
                    ⬝ (fun i => Dν₂ i x))
          + (μ x - 1) * (ν₂ x))
      (UnitCube d))
    (hB₁ : IntegrableOn
      (fun x =>
        vecAbsPowMinusTwo γBar (fun i => Dυ i x)
            * ((fun i => Dυ i x) ⬝ (fun i => Dν₁ i x))
          + absPowMinusTwo γBar (υ x) * (υ x * (ν₁ x)))
      (UnitCube d))
    (hB₂ : IntegrableOn
      (fun x =>
        vecAbsPowMinusTwo γBar (fun i => Dυ i x)
            * ((fun i => Dυ i x) ⬝ (fun i => Dν₂ i x))
          + absPowMinusTwo γBar (υ x) * (υ x * (ν₂ x)))
      (UnitCube d)) :
    mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
        γBar ε Dυ μ υ (fun i => Dν₁ i + Dν₂ i) (η₁ + η₂) (ν₁ + ν₂) =
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBar ε Dυ μ υ Dν₁ η₁ ν₁
        + mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBar ε Dυ μ υ Dν₂ η₂ ν₂ := by
  unfold mfgOperatorEpsPair mfgOperatorPair gateauxWpPair
  -- Pointwise rewrite each combined integrand as a sum of two integrands.
  have hA :
      (fun x =>
        (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * ((η₁ + η₂) x)
          + μ x * (DpH x (fun i => Dυ i x) (μ x)
                    ⬝ (fun i => (Dν₁ i + Dν₂ i) x))
          + (μ x - 1) * ((ν₁ + ν₂) x))
        = (fun x =>
            ((-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (η₁ x)
                + μ x * (DpH x (fun i => Dυ i x) (μ x)
                          ⬝ (fun i => Dν₁ i x))
                + (μ x - 1) * (ν₁ x))
              + ((-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (η₂ x)
                + μ x * (DpH x (fun i => Dυ i x) (μ x)
                          ⬝ (fun i => Dν₂ i x))
                + (μ x - 1) * (ν₂ x))) := by
    funext x
    exact mfgPair_integrand_test_add V H DpH Dυ μ υ Dν₁ Dν₂ η₁ η₂ ν₁ ν₂ x
  have hB :
      (fun x =>
        vecAbsPowMinusTwo γBar (fun i => Dυ i x)
            * ((fun i => Dυ i x) ⬝ (fun i => (Dν₁ i + Dν₂ i) x))
          + absPowMinusTwo γBar (υ x) * (υ x * ((ν₁ + ν₂) x)))
        = (fun x =>
            (vecAbsPowMinusTwo γBar (fun i => Dυ i x)
                  * ((fun i => Dυ i x) ⬝ (fun i => Dν₁ i x))
                + absPowMinusTwo γBar (υ x) * (υ x * (ν₁ x)))
              + (vecAbsPowMinusTwo γBar (fun i => Dυ i x)
                  * ((fun i => Dυ i x) ⬝ (fun i => Dν₂ i x))
                + absPowMinusTwo γBar (υ x) * (υ x * (ν₂ x)))) := by
    funext x
    exact gateaux_integrand_test_add γBar Dυ υ Dν₁ Dν₂ ν₁ ν₂ x
  rw [hA, hB]
  -- Split the two combined integrals using `integral_add`.
  rw [MeasureTheory.integral_add hA₁ hA₂,
      MeasureTheory.integral_add hB₁ hB₂]
  ring

/-! ## Sanity-check example

Exercise `mfgOperatorEpsPair_test_add` directly: for the **same**
test triple on both sides (`Dν₁ = Dν₂ := Dν`, `η₁ = η₂ := η`,
`ν₁ = ν₂ := ν`), additivity yields `value = value + value`, i.e.
`value` is twice itself, which forces it to equal twice itself. We do
not derive `value = 0` (which would require concrete vanishing
hypotheses); we only check that `_test_add` *applies* type-correctly
and produces the expected algebraic shape.

Specialisation to the trivial Hamiltonian-data scenario, with the
zero-integrand integrability witnesses in place. -/

example (γBar ε : ℝ)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (μ υ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ)
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hA : IntegrableOn
      (fun x =>
        (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (η x)
          + μ x * (DpH x (fun i => Dυ i x) (μ x)
                    ⬝ (fun i => Dν i x))
          + (μ x - 1) * (ν x))
      (UnitCube d))
    (hB : IntegrableOn
      (fun x =>
        vecAbsPowMinusTwo γBar (fun i => Dυ i x)
            * ((fun i => Dυ i x) ⬝ (fun i => Dν i x))
          + absPowMinusTwo γBar (υ x) * (υ x * (ν x)))
      (UnitCube d)) :
    mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
        γBar ε Dυ μ υ
        (fun i => Dν i + Dν i) (η + η) (ν + ν) =
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBar ε Dυ μ υ Dν η ν
        + mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBar ε Dυ μ υ Dν η ν :=
  mfgOperatorEpsPair_test_add (V := V) (H := H) (DpH := DpH)
    γBar ε Dυ μ υ Dν Dν η η ν ν hA hA hB hB

/-! ## Hölder bound and continuity (Block A.2)

We now prove the **Hölder continuity bound** for `mfgOperatorEpsPair`
in the test triple `(η, ν, Dν)`. The integrand of `mfgOperatorEpsPair`
splits into five Hölder products (paper line 925, `defAepsi`):

* `(-υ - H + V) · η` — paired in `(L^{β̄'}, L^{β̄})`.
* `μ · (D_pH · Dν) = ∑_i (μ · D_pH_i) · Dν_i` — paired
  coordinate-wise in `(L^{γ̄'}, L^{γ̄})`. Here `m · D_pH ∈ L^{γ̄'}` is
  paper Lemma `lem:ADFGU.b` (`StationaryMFG.Hamiltonian.mDpH_mem_Lp_gammaBar'`).
* `(μ - 1) · ν` — paired in `(L^{β̄'}, L^{β̄})`.
* `ε · |Dυ|^{γ̄-2} (Dυ · Dν) = ε · ∑_i (|Dυ|^{γ̄-2} Dυ_i) · Dν_i`
  — paired coordinate-wise in `(L^{γ̄'}, L^{γ̄})`.
* `ε · |υ|^{γ̄-2} υ · ν` — paired in `(L^{γ̄'}, L^{γ̄})`.

The constant `C(ε, V, H, DpH, m, u, Du)` is the sum of the five
`L^{β̄'}`/`L^{γ̄'}` norms on the primal side. We accept these `MemLpPer`
hypotheses on the auxiliary functions as inputs (the consumer
discharges them from `paper:lem:ADFGU.{a,b}` plus the
`(γ̄-1)·γ̄' = γ̄` `rpow` identity).

The continuity corollary follows from the Hölder bound and the
ℝ-linearity (`mfgOperatorEpsPair_test_add`,
`mfgOperatorEpsPair_test_smul`) — i.e., the value at a perturbed
test triple differs from the value at the base triple by the value at
the difference, which is bounded by `C` times the seminorm of the
difference.
-/

variable {V H DpH}

/-- Auxiliary primal-side function: `F_HJB(x) := -υ x - H x (Dυ x) (μ x) + V x`.

Made non-private so that downstream feeder lemmas (e.g.
`auxHyps_of_paperHypotheses_at_triple` in `Banach/AssemblyContext.lean`)
can construct `MFGOpEpsAuxHyps` records explicitly using the AC2 lemmas
in `Hamiltonian/Estimates.lean`, which work on the literal
`fun x => -(υ x) - H x (...) + V x` form. -/
def F_HJB
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (μ υ : (Fin d → ℝ) → ℝ) : (Fin d → ℝ) → ℝ :=
  fun x => -(υ x) - H x (fun i => Dυ i x) (μ x) + V x

/-- Auxiliary primal-side function: `F_flux i x := μ x * (D_pH x (Dυ x) (μ x))_i`.
Non-private (see `F_HJB` rationale). -/
def F_flux
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (μ : (Fin d → ℝ) → ℝ) (i : Fin d) : (Fin d → ℝ) → ℝ :=
  fun x => μ x * DpH x (fun j => Dυ j x) (μ x) i

/-- Auxiliary primal-side function: `F_mass(x) := μ x - 1`.
Non-private (see `F_HJB` rationale). -/
def F_mass (μ : (Fin d → ℝ) → ℝ) : (Fin d → ℝ) → ℝ :=
  fun x => μ x - 1

/-- Auxiliary primal-side function (γ̄-Laplacian, gradient piece):
`G_grad i x := |Dυ x|^{γBar-2} · (Dυ x)_i`. Non-private (see `F_HJB`
rationale). -/
def G_grad (γBar : ℝ)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ) (i : Fin d) : (Fin d → ℝ) → ℝ :=
  fun x => vecAbsPowMinusTwo γBar (fun j => Dυ j x) * Dυ i x

/-- Auxiliary primal-side function (γ̄-Laplacian, value piece):
`G_val(x) := |υ x|^{γBar-2} · υ x`. Non-private (see `F_HJB` rationale). -/
def G_val (γBar : ℝ) (υ : (Fin d → ℝ) → ℝ) : (Fin d → ℝ) → ℝ :=
  fun x => absPowMinusTwo γBar (υ x) * υ x

/-- Pointwise rewrite of the `mfgOperatorPair`-integrand into a sum of
products `F · ξ` with `ξ ∈ {η, Dν_i, ν}`. -/
private lemma mfgPair_integrand_decomp
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (μ υ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (η x)
        + μ x * (DpH x (fun i => Dυ i x) (μ x) ⬝ (fun i => Dν i x))
        + (μ x - 1) * (ν x)
      = F_HJB V H Dυ μ υ x * η x
        + ∑ i : Fin d, F_flux DpH Dυ μ i x * Dν i x
        + F_mass μ x * ν x := by
  unfold F_HJB F_flux F_mass euclideanDot
  simp only [Finset.mul_sum]
  ring_nf

/-- Pointwise rewrite of the `gateauxWpPair`-integrand into a sum of
products `G · ξ` with `ξ ∈ {Dν_i, ν}`. -/
private lemma gateaux_integrand_decomp
    (γBar : ℝ)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (υ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (ν : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    vecAbsPowMinusTwo γBar (fun i => Dυ i x)
          * ((fun i => Dυ i x) ⬝ (fun i => Dν i x))
        + absPowMinusTwo γBar (υ x) * (υ x * (ν x))
      = (∑ i : Fin d, G_grad γBar Dυ i x * Dν i x)
        + G_val γBar υ x * ν x := by
  unfold G_grad G_val euclideanDot
  simp only [Finset.mul_sum]
  ring_nf

/-- **Hölder bound for `mfgOperatorEpsPair` in the test triple.**

Given Hölder-conjugate exponent pairs `(βBar, βBar')` and `(γBar,
γBar')`, primal-side functions `F_HJB`, `F_flux i`, `F_mass`,
`G_grad i`, `G_val` whose `MemLpPer p'` membership is hypothesised
(discharged at use sites by `paper:lem:ADFGU.b` and friends), and
test-side functions `η ∈ L^{βBar}_per`, `ν ∈ L^{βBar}_per ∩
L^{γBar}_per`, `Dν_i ∈ L^{γBar}_per`, the value of the regularized
operator pairing is bounded by the natural Hölder sum:

```
|⟨A_ε[m,u], (η,ν,Dν)⟩|
  ≤ ‖F_HJB‖_{β̄'} ‖η‖_{β̄}
    + ∑ᵢ ‖F_flux_i‖_{γ̄'} ‖Dν_i‖_{γ̄}
    + ‖F_mass‖_{β̄'} ‖ν‖_{β̄}
    + |ε| · (∑ᵢ ‖G_grad_i‖_{γ̄'} ‖Dν_i‖_{γ̄}
              + ‖G_val‖_{γ̄'} ‖ν‖_{γ̄}).
```

This is the "Hölder continuity bound" of paper line 925 / `defAepsi`,
in the precise form needed by Block A.3 to lift `mfgOperatorEpsPair`
to a continuous linear map on the test triple. -/
theorem mfgOperatorEpsPair_holder_bound
    {γBar βBar βBar' γBar' : ℝ}
    (hβ : βBar.HolderConjugate βBar')
    (hγ : γBar.HolderConjugate γBar')
    (ε : ℝ)
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (μ υ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ)
    -- Primal-side `MemLpPer` hypotheses (discharged from paper bounds).
    (hF_HJB : MemLpPer (ENNReal.ofReal βBar') (F_HJB V H Dυ μ υ))
    (hF_flux : ∀ i, MemLpPer (ENNReal.ofReal γBar') (F_flux DpH Dυ μ i))
    -- Phase 0 routing fix (`infra-P5-theorem1-phase-0`):
    -- `F_mass` is paired with the value test `ν ∈ L^γ̄`, so it
    -- lives in `L^γ̄'` rather than `L^β̄'`.
    (hF_mass : MemLpPer (ENNReal.ofReal γBar') (F_mass μ))
    (hG_grad : ∀ i, MemLpPer (ENNReal.ofReal γBar') (G_grad γBar Dυ i))
    (hG_val : MemLpPer (ENNReal.ofReal γBar') (G_val γBar υ))
    -- Test-side `MemLpPer` hypotheses.
    (hη : MemLpPer (ENNReal.ofReal βBar) η)
    (hν_γ : MemLpPer (ENNReal.ofReal γBar) ν)
    (hDν : ∀ i, MemLpPer (ENNReal.ofReal γBar) (Dν i))
    -- Per-summand integrability (needed for `integral_add` splits).
    (hI_HJB : IntegrableOn
      (fun x => F_HJB V H Dυ μ υ x * η x) (UnitCube d))
    (hI_flux : IntegrableOn
      (fun x => ∑ i : Fin d, F_flux DpH Dυ μ i x * Dν i x) (UnitCube d))
    (hI_flux_i : ∀ i, IntegrableOn
      (fun x => F_flux DpH Dυ μ i x * Dν i x) (UnitCube d))
    (hI_mass : IntegrableOn
      (fun x => F_mass μ x * ν x) (UnitCube d))
    (hI_grad : IntegrableOn
      (fun x => ∑ i : Fin d, G_grad γBar Dυ i x * Dν i x) (UnitCube d))
    (hI_grad_i : ∀ i, IntegrableOn
      (fun x => G_grad γBar Dυ i x * Dν i x) (UnitCube d))
    (hI_val : IntegrableOn
      (fun x => G_val γBar υ x * ν x) (UnitCube d)) :
    |mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
        γBar ε Dυ μ υ Dν η ν| ≤
      lpNormPer (ENNReal.ofReal βBar') (F_HJB V H Dυ μ υ)
            * lpNormPer (ENNReal.ofReal βBar) η
        + (∑ i : Fin d,
            lpNormPer (ENNReal.ofReal γBar') (F_flux DpH Dυ μ i)
              * lpNormPer (ENNReal.ofReal γBar) (Dν i))
        + lpNormPer (ENNReal.ofReal γBar') (F_mass μ)
            * lpNormPer (ENNReal.ofReal γBar) ν
        + |ε| * ((∑ i : Fin d,
              lpNormPer (ENNReal.ofReal γBar') (G_grad γBar Dυ i)
                * lpNormPer (ENNReal.ofReal γBar) (Dν i))
            + lpNormPer (ENNReal.ofReal γBar') (G_val γBar υ)
                * lpNormPer (ENNReal.ofReal γBar) ν) := by
  -- Step 1: rewrite `mfgOperatorEpsPair` as the sum of five integrals.
  set μres : Measure (Fin d → ℝ) := volume.restrict (UnitCube d) with hμres
  -- Pointwise rewrite of the `mfgOperatorPair`-integrand and the
  -- `gateauxWpPair`-integrand.
  have hPair_eq : mfgOperatorPair (V := V) (H := H) (DpH := DpH)
        Dυ μ υ Dν η ν =
      periodicIntegral (fun x => F_HJB V H Dυ μ υ x * η x)
        + periodicIntegral
            (fun x => ∑ i : Fin d, F_flux DpH Dυ μ i x * Dν i x)
        + periodicIntegral (fun x => F_mass μ x * ν x) := by
    unfold mfgOperatorPair periodicIntegral
    -- Cast both sides to integrals over the cube and split using `integral_add`.
    have hpt :
        (fun x =>
          (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (η x)
            + μ x * (DpH x (fun i => Dυ i x) (μ x) ⬝ (fun i => Dν i x))
            + (μ x - 1) * (ν x)) =
          (((fun x => F_HJB V H Dυ μ υ x * η x)
                + (fun x => ∑ i : Fin d, F_flux DpH Dυ μ i x * Dν i x))
              + (fun x => F_mass μ x * ν x)) := by
      funext x
      simp only [Pi.add_apply]
      exact mfgPair_integrand_decomp V H DpH Dυ μ υ Dν η ν x
    rw [hpt]
    rw [MeasureTheory.integral_add' (hI_HJB.add hI_flux) hI_mass]
    rw [MeasureTheory.integral_add' hI_HJB hI_flux]
  have hGate_eq : gateauxWpPair γBar Dυ υ Dν ν =
      periodicIntegral
          (fun x => ∑ i : Fin d, G_grad γBar Dυ i x * Dν i x)
        + periodicIntegral (fun x => G_val γBar υ x * ν x) := by
    unfold gateauxWpPair periodicIntegral
    have hpt :
        (fun x =>
          vecAbsPowMinusTwo γBar (fun i => Dυ i x)
              * ((fun i => Dυ i x) ⬝ (fun i => Dν i x))
            + absPowMinusTwo γBar (υ x) * (υ x * (ν x))) =
          ((fun x => ∑ i : Fin d, G_grad γBar Dυ i x * Dν i x)
              + (fun x => G_val γBar υ x * ν x)) := by
      funext x
      simp only [Pi.add_apply]
      exact gateaux_integrand_decomp γBar Dυ υ Dν ν x
    rw [hpt]
    rw [MeasureTheory.integral_add' hI_grad hI_val]
  -- Step 2: the `∑_i F_flux_i Dν_i` integral expands to `∑_i ∫ F_flux_i Dν_i`.
  have hflux_sum :
      periodicIntegral
          (fun x => ∑ i : Fin d, F_flux DpH Dυ μ i x * Dν i x) =
        ∑ i : Fin d,
          periodicIntegral (fun x => F_flux DpH Dυ μ i x * Dν i x) := by
    unfold periodicIntegral
    rw [MeasureTheory.integral_finset_sum (s := Finset.univ)
          (f := fun i x => F_flux DpH Dυ μ i x * Dν i x)
          (fun i _ => hI_flux_i i)]
  have hgrad_sum :
      periodicIntegral
          (fun x => ∑ i : Fin d, G_grad γBar Dυ i x * Dν i x) =
        ∑ i : Fin d,
          periodicIntegral (fun x => G_grad γBar Dυ i x * Dν i x) := by
    unfold periodicIntegral
    rw [MeasureTheory.integral_finset_sum (s := Finset.univ)
          (f := fun i x => G_grad γBar Dυ i x * Dν i x)
          (fun i _ => hI_grad_i i)]
  -- Step 3: per-summand Hölder bounds.
  have hHJB_bd :
      |periodicIntegral (fun x => F_HJB V H Dυ μ υ x * η x)| ≤
        lpNormPer (ENNReal.ofReal βBar') (F_HJB V H Dυ μ υ)
          * lpNormPer (ENNReal.ofReal βBar) η := by
    have := abs_periodicIntegral_mul_le hβ.symm hF_HJB hη
    simpa [mul_comm] using this
  have hflux_bd : ∀ i : Fin d,
      |periodicIntegral (fun x => F_flux DpH Dυ μ i x * Dν i x)| ≤
        lpNormPer (ENNReal.ofReal γBar') (F_flux DpH Dυ μ i)
          * lpNormPer (ENNReal.ofReal γBar) (Dν i) := by
    intro i
    have := abs_periodicIntegral_mul_le hγ.symm (hF_flux i) (hDν i)
    simpa [mul_comm] using this
  have hmass_bd :
      |periodicIntegral (fun x => F_mass μ x * ν x)| ≤
        lpNormPer (ENNReal.ofReal γBar') (F_mass μ)
          * lpNormPer (ENNReal.ofReal γBar) ν := by
    have := abs_periodicIntegral_mul_le hγ.symm hF_mass hν_γ
    simpa [mul_comm] using this
  have hgrad_bd : ∀ i : Fin d,
      |periodicIntegral (fun x => G_grad γBar Dυ i x * Dν i x)| ≤
        lpNormPer (ENNReal.ofReal γBar') (G_grad γBar Dυ i)
          * lpNormPer (ENNReal.ofReal γBar) (Dν i) := by
    intro i
    have := abs_periodicIntegral_mul_le hγ.symm (hG_grad i) (hDν i)
    simpa [mul_comm] using this
  have hval_bd :
      |periodicIntegral (fun x => G_val γBar υ x * ν x)| ≤
        lpNormPer (ENNReal.ofReal γBar') (G_val γBar υ)
          * lpNormPer (ENNReal.ofReal γBar) ν := by
    have := abs_periodicIntegral_mul_le hγ.symm hG_val hν_γ
    simpa [mul_comm] using this
  -- Step 4: aggregate via the triangle inequality.
  unfold mfgOperatorEpsPair
  rw [hPair_eq, hGate_eq, hflux_sum, hgrad_sum]
  -- Now bound the absolute value via repeated `abs_add_le`.
  have habs_grad_sum :
      |∑ i : Fin d,
        periodicIntegral (fun x => F_flux DpH Dυ μ i x * Dν i x)| ≤
        ∑ i : Fin d,
          |periodicIntegral (fun x => F_flux DpH Dυ μ i x * Dν i x)| :=
    Finset.abs_sum_le_sum_abs _ _
  have hflux_total :
      |∑ i : Fin d,
        periodicIntegral (fun x => F_flux DpH Dυ μ i x * Dν i x)| ≤
        ∑ i : Fin d,
          lpNormPer (ENNReal.ofReal γBar') (F_flux DpH Dυ μ i)
            * lpNormPer (ENNReal.ofReal γBar) (Dν i) :=
    le_trans habs_grad_sum (Finset.sum_le_sum (fun i _ => hflux_bd i))
  have habs_grad_sum2 :
      |∑ i : Fin d,
        periodicIntegral (fun x => G_grad γBar Dυ i x * Dν i x)| ≤
        ∑ i : Fin d,
          |periodicIntegral (fun x => G_grad γBar Dυ i x * Dν i x)| :=
    Finset.abs_sum_le_sum_abs _ _
  have hgrad_total :
      |∑ i : Fin d,
        periodicIntegral (fun x => G_grad γBar Dυ i x * Dν i x)| ≤
        ∑ i : Fin d,
          lpNormPer (ENNReal.ofReal γBar') (G_grad γBar Dυ i)
            * lpNormPer (ENNReal.ofReal γBar) (Dν i) :=
    le_trans habs_grad_sum2 (Finset.sum_le_sum (fun i _ => hgrad_bd i))
  -- Final bound on the gateaux block:
  set Igrad := ∑ i : Fin d,
        periodicIntegral (fun x => G_grad γBar Dυ i x * Dν i x) with hIgrad
  set Ival := periodicIntegral (fun x => G_val γBar υ x * ν x) with hIval
  set Iflux := ∑ i : Fin d,
        periodicIntegral (fun x => F_flux DpH Dυ μ i x * Dν i x) with hIflux
  set IHJB := periodicIntegral (fun x => F_HJB V H Dυ μ υ x * η x) with hIHJB
  set Imass := periodicIntegral (fun x => F_mass μ x * ν x) with hImass
  -- The total expression is `IHJB + Iflux + Imass + ε * (Igrad + Ival)`.
  have habs_total :
      |IHJB + Iflux + Imass + ε * (Igrad + Ival)| ≤
        |IHJB| + |Iflux| + |Imass| + |ε| * (|Igrad| + |Ival|) := by
    have h1 := abs_add_le (IHJB + Iflux + Imass) (ε * (Igrad + Ival))
    have h2 := abs_add_le (IHJB + Iflux) Imass
    have h3 := abs_add_le IHJB Iflux
    have h4 : |ε * (Igrad + Ival)| = |ε| * |Igrad + Ival| := abs_mul _ _
    have h5 : |Igrad + Ival| ≤ |Igrad| + |Ival| := abs_add_le _ _
    have h6 : |ε| * |Igrad + Ival| ≤ |ε| * (|Igrad| + |Ival|) :=
      mul_le_mul_of_nonneg_left h5 (abs_nonneg _)
    have h7 : |IHJB + Iflux + Imass + ε * (Igrad + Ival)| ≤
        (|IHJB| + |Iflux| + |Imass|) + |ε| * (|Igrad| + |Ival|) := by
      calc |IHJB + Iflux + Imass + ε * (Igrad + Ival)|
          ≤ |IHJB + Iflux + Imass| + |ε * (Igrad + Ival)| := h1
        _ ≤ (|IHJB + Iflux| + |Imass|) + |ε * (Igrad + Ival)| := by
              linarith [h2]
        _ ≤ ((|IHJB| + |Iflux|) + |Imass|) + |ε * (Igrad + Ival)| := by
              linarith [h3]
        _ = (|IHJB| + |Iflux| + |Imass|) + |ε| * |Igrad + Ival| := by
              rw [h4]
        _ ≤ (|IHJB| + |Iflux| + |Imass|) + |ε| * (|Igrad| + |Ival|) := by
              linarith [h6]
    linarith [h7]
  -- Combine.
  calc |IHJB + Iflux + Imass + ε * (Igrad + Ival)|
      ≤ |IHJB| + |Iflux| + |Imass| + |ε| * (|Igrad| + |Ival|) := habs_total
    _ ≤ lpNormPer (ENNReal.ofReal βBar') (F_HJB V H Dυ μ υ)
            * lpNormPer (ENNReal.ofReal βBar) η
          + (∑ i : Fin d,
              lpNormPer (ENNReal.ofReal γBar') (F_flux DpH Dυ μ i)
                * lpNormPer (ENNReal.ofReal γBar) (Dν i))
          + lpNormPer (ENNReal.ofReal γBar') (F_mass μ)
              * lpNormPer (ENNReal.ofReal γBar) ν
          + |ε| * ((∑ i : Fin d,
              lpNormPer (ENNReal.ofReal γBar') (G_grad γBar Dυ i)
                * lpNormPer (ENNReal.ofReal γBar) (Dν i))
            + lpNormPer (ENNReal.ofReal γBar') (G_val γBar υ)
                * lpNormPer (ENNReal.ofReal γBar) ν) := by
        have hε_nn : 0 ≤ |ε| := abs_nonneg _
        have hε_mono :
            |ε| * (|Igrad| + |Ival|) ≤
              |ε| * ((∑ i : Fin d,
                lpNormPer (ENNReal.ofReal γBar') (G_grad γBar Dυ i)
                  * lpNormPer (ENNReal.ofReal γBar) (Dν i))
              + lpNormPer (ENNReal.ofReal γBar') (G_val γBar υ)
                  * lpNormPer (ENNReal.ofReal γBar) ν) := by
          apply mul_le_mul_of_nonneg_left _ hε_nn
          have : |Igrad| + |Ival| ≤
              (∑ i : Fin d,
                lpNormPer (ENNReal.ofReal γBar') (G_grad γBar Dυ i)
                  * lpNormPer (ENNReal.ofReal γBar) (Dν i))
              + lpNormPer (ENNReal.ofReal γBar') (G_val γBar υ)
                  * lpNormPer (ENNReal.ofReal γBar) ν := by
            linarith [hgrad_total, hval_bd]
          exact this
        linarith [hHJB_bd, hflux_total, hmass_bd, hε_mono]

/-- **Continuity of `mfgOperatorEpsPair` in the test triple.**

For fixed primal datum `(Dυ, μ, υ)` and parameters, the value of
`mfgOperatorEpsPair` differs at two test triples by at most a Hölder
constant times the seminorm of the difference. This is the immediate
consequence of `mfgOperatorEpsPair_holder_bound` applied to the
difference triple `(η₁ - η₂, ν₁ - ν₂, Dν₁ - Dν₂)`, combined with the
ℝ-linearity (`mfgOperatorEpsPair_test_add`,
`mfgOperatorEpsPair_test_neg`).

Concretely: under the integrability and `MemLpPer` hypotheses required
by `_holder_bound` for the difference triple,

```
|⟨A_ε[m,u], (η₁,ν₁,Dν₁)⟩ - ⟨A_ε[m,u], (η₂,ν₂,Dν₂)⟩|
  ≤ ‖F_HJB‖_{β̄'} ‖η₁-η₂‖_{β̄}
    + ∑ᵢ ‖F_flux_i‖_{γ̄'} ‖Dν₁,ᵢ-Dν₂,ᵢ‖_{γ̄}
    + ‖F_mass‖_{β̄'} ‖ν₁-ν₂‖_{β̄}
    + |ε|·(...).
```

This is the form needed by Block A.3 to upgrade
`mfgOperatorEpsPair` to a continuous linear functional in the test
triple. -/
theorem mfgOperatorEpsPair_continuous_in_test
    {γBar βBar βBar' γBar' : ℝ}
    (hβ : βBar.HolderConjugate βBar')
    (hγ : γBar.HolderConjugate γBar')
    (ε : ℝ)
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (μ υ : (Fin d → ℝ) → ℝ)
    (Dν₁ Dν₂ : Fin d → (Fin d → ℝ) → ℝ)
    (η₁ η₂ ν₁ ν₂ : (Fin d → ℝ) → ℝ)
    -- Primal-side `MemLpPer` hypotheses.
    (hF_HJB : MemLpPer (ENNReal.ofReal βBar') (F_HJB V H Dυ μ υ))
    (hF_flux : ∀ i, MemLpPer (ENNReal.ofReal γBar') (F_flux DpH Dυ μ i))
    -- Phase 0 routing fix (`infra-P5-theorem1-phase-0`).
    (hF_mass : MemLpPer (ENNReal.ofReal γBar') (F_mass μ))
    (hG_grad : ∀ i, MemLpPer (ENNReal.ofReal γBar') (G_grad γBar Dυ i))
    (hG_val : MemLpPer (ENNReal.ofReal γBar') (G_val γBar υ))
    -- Test-side `MemLpPer` hypotheses for the *difference* triple.
    (hηd : MemLpPer (ENNReal.ofReal βBar) (η₁ - η₂))
    (hνd_γ : MemLpPer (ENNReal.ofReal γBar) (ν₁ - ν₂))
    (hDνd : ∀ i, MemLpPer (ENNReal.ofReal γBar) ((fun x => Dν₁ i x - Dν₂ i x)))
    -- Per-summand integrability for the difference triple.
    (hI_HJB : IntegrableOn
      (fun x => F_HJB V H Dυ μ υ x * (η₁ x - η₂ x)) (UnitCube d))
    (hI_flux : IntegrableOn
      (fun x => ∑ i : Fin d, F_flux DpH Dυ μ i x * (Dν₁ i x - Dν₂ i x))
      (UnitCube d))
    (hI_flux_i : ∀ i, IntegrableOn
      (fun x => F_flux DpH Dυ μ i x * (Dν₁ i x - Dν₂ i x)) (UnitCube d))
    (hI_mass : IntegrableOn
      (fun x => F_mass μ x * (ν₁ x - ν₂ x)) (UnitCube d))
    (hI_grad : IntegrableOn
      (fun x => ∑ i : Fin d, G_grad γBar Dυ i x * (Dν₁ i x - Dν₂ i x))
      (UnitCube d))
    (hI_grad_i : ∀ i, IntegrableOn
      (fun x => G_grad γBar Dυ i x * (Dν₁ i x - Dν₂ i x)) (UnitCube d))
    (hI_val : IntegrableOn
      (fun x => G_val γBar υ x * (ν₁ x - ν₂ x)) (UnitCube d))
    -- Linearity-input: integrability of the two `mfgOperatorPair`-integrands
    -- separately (needed to apply `mfgOperatorEpsPair_test_add`).
    (hLinA₁ : IntegrableOn
      (fun x =>
        (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (η₁ x - η₂ x)
          + μ x * (DpH x (fun i => Dυ i x) (μ x)
                    ⬝ (fun i => Dν₁ i x - Dν₂ i x))
          + (μ x - 1) * (ν₁ x - ν₂ x))
      (UnitCube d))
    (hLinA₂ : IntegrableOn
      (fun x =>
        (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (η₂ x)
          + μ x * (DpH x (fun i => Dυ i x) (μ x)
                    ⬝ (fun i => Dν₂ i x))
          + (μ x - 1) * (ν₂ x))
      (UnitCube d))
    (hLinB₁ : IntegrableOn
      (fun x =>
        vecAbsPowMinusTwo γBar (fun i => Dυ i x)
            * ((fun i => Dυ i x) ⬝ (fun i => Dν₁ i x - Dν₂ i x))
          + absPowMinusTwo γBar (υ x) * (υ x * (ν₁ x - ν₂ x)))
      (UnitCube d))
    (hLinB₂ : IntegrableOn
      (fun x =>
        vecAbsPowMinusTwo γBar (fun i => Dυ i x)
            * ((fun i => Dυ i x) ⬝ (fun i => Dν₂ i x))
          + absPowMinusTwo γBar (υ x) * (υ x * (ν₂ x)))
      (UnitCube d)) :
    |mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBar ε Dυ μ υ Dν₁ η₁ ν₁
        - mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBar ε Dυ μ υ Dν₂ η₂ ν₂| ≤
      lpNormPer (ENNReal.ofReal βBar') (F_HJB V H Dυ μ υ)
            * lpNormPer (ENNReal.ofReal βBar) (η₁ - η₂)
        + (∑ i : Fin d,
            lpNormPer (ENNReal.ofReal γBar') (F_flux DpH Dυ μ i)
              * lpNormPer (ENNReal.ofReal γBar)
                  (fun x => Dν₁ i x - Dν₂ i x))
        + lpNormPer (ENNReal.ofReal γBar') (F_mass μ)
            * lpNormPer (ENNReal.ofReal γBar) (ν₁ - ν₂)
        + |ε| * ((∑ i : Fin d,
              lpNormPer (ENNReal.ofReal γBar') (G_grad γBar Dυ i)
                * lpNormPer (ENNReal.ofReal γBar)
                    (fun x => Dν₁ i x - Dν₂ i x))
            + lpNormPer (ENNReal.ofReal γBar') (G_val γBar υ)
                * lpNormPer (ENNReal.ofReal γBar) (ν₁ - ν₂)) := by
  -- Step 1: rewrite the difference using ℝ-linearity (`_test_add` + `_test_neg`).
  -- We have `(η₁,ν₁,Dν₁) = (η₁ - η₂, ν₁ - ν₂, Dν₁ - Dν₂) + (η₂, ν₂, Dν₂)`.
  have hadd := mfgOperatorEpsPair_test_add (V := V) (H := H) (DpH := DpH)
                  γBar ε Dυ μ υ
                  (fun i x => Dν₁ i x - Dν₂ i x) Dν₂
                  (η₁ - η₂) η₂ (ν₁ - ν₂) ν₂
                  hLinA₁ hLinA₂ hLinB₁ hLinB₂
  -- Massage the LHS of `hadd` so that it matches `mfgOperatorEpsPair … Dν₁ η₁ ν₁`.
  have hLHS_eq :
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
        γBar ε Dυ μ υ
        (fun i => (fun x => Dν₁ i x - Dν₂ i x) + Dν₂ i)
        ((η₁ - η₂) + η₂) ((ν₁ - ν₂) + ν₂) =
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
        γBar ε Dυ μ υ Dν₁ η₁ ν₁ := by
    have hDν_eq : (fun i => (fun x => Dν₁ i x - Dν₂ i x) + Dν₂ i) = Dν₁ := by
      funext i; funext x; simp [Pi.add_apply]
    have hη_eq : (η₁ - η₂) + η₂ = η₁ := by
      funext x; simp [Pi.add_apply, Pi.sub_apply]
    have hν_eq : (ν₁ - ν₂) + ν₂ = ν₁ := by
      funext x; simp [Pi.add_apply, Pi.sub_apply]
    rw [hDν_eq, hη_eq, hν_eq]
  rw [hLHS_eq] at hadd
  -- Therefore the difference is the value at the difference triple.
  have hdiff_eq :
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBar ε Dυ μ υ Dν₁ η₁ ν₁
        - mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBar ε Dυ μ υ Dν₂ η₂ ν₂ =
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
        γBar ε Dυ μ υ
        (fun i x => Dν₁ i x - Dν₂ i x) (η₁ - η₂) (ν₁ - ν₂) := by
    linarith [hadd]
  rw [hdiff_eq]
  -- Step 2: apply the Hölder bound to the difference triple.
  exact mfgOperatorEpsPair_holder_bound
    (γBar := γBar) (βBar := βBar) (βBar' := βBar') (γBar' := γBar')
    hβ hγ ε V H DpH Dυ μ υ
    (fun i x => Dν₁ i x - Dν₂ i x) (η₁ - η₂) (ν₁ - ν₂)
    hF_HJB hF_flux hF_mass hG_grad hG_val
    hηd hνd_γ hDνd
    hI_HJB hI_flux hI_flux_i hI_mass hI_grad hI_grad_i hI_val

/-! ## Sanity-check: Hölder bound at the trivial Hamiltonian.

For the trivial Hamiltonian `H ≡ 0`, `D_pH ≡ 0`, the Hölder bound
applies whenever the auxiliary `F`-functions and the test-side
functions satisfy the standard `MemLpPer` predicates. -/

example
    {γBar βBar βBar' γBar' : ℝ}
    (hβ : βBar.HolderConjugate βBar')
    (hγ : γBar.HolderConjugate γBar')
    (ε : ℝ)
    (V : (Fin d → ℝ) → ℝ)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (μ υ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ)
    (hF_HJB : MemLpPer (ENNReal.ofReal βBar')
      (F_HJB V (fun _ _ _ => (0 : ℝ)) Dυ μ υ))
    (hF_flux : ∀ i, MemLpPer (ENNReal.ofReal γBar')
      (F_flux (fun _ _ _ => (0 : Fin d → ℝ)) Dυ μ i))
    (hF_mass : MemLpPer (ENNReal.ofReal γBar') (F_mass μ))
    (hG_grad : ∀ i, MemLpPer (ENNReal.ofReal γBar') (G_grad γBar Dυ i))
    (hG_val : MemLpPer (ENNReal.ofReal γBar') (G_val γBar υ))
    (hη : MemLpPer (ENNReal.ofReal βBar) η)
    (hν_γ : MemLpPer (ENNReal.ofReal γBar) ν)
    (hDν : ∀ i, MemLpPer (ENNReal.ofReal γBar) (Dν i))
    (hI_HJB : IntegrableOn
      (fun x => F_HJB V (fun _ _ _ => (0 : ℝ)) Dυ μ υ x * η x) (UnitCube d))
    (hI_flux : IntegrableOn
      (fun x => ∑ i : Fin d,
          F_flux (fun _ _ _ => (0 : Fin d → ℝ)) Dυ μ i x * Dν i x)
      (UnitCube d))
    (hI_flux_i : ∀ i, IntegrableOn
      (fun x =>
          F_flux (fun _ _ _ => (0 : Fin d → ℝ)) Dυ μ i x * Dν i x)
      (UnitCube d))
    (hI_mass : IntegrableOn
      (fun x => F_mass μ x * ν x) (UnitCube d))
    (hI_grad : IntegrableOn
      (fun x => ∑ i : Fin d, G_grad γBar Dυ i x * Dν i x) (UnitCube d))
    (hI_grad_i : ∀ i, IntegrableOn
      (fun x => G_grad γBar Dυ i x * Dν i x) (UnitCube d))
    (hI_val : IntegrableOn
      (fun x => G_val γBar υ x * ν x) (UnitCube d)) :
    |mfgOperatorEpsPair (V := V) (H := fun _ _ _ => (0 : ℝ))
        (DpH := fun _ _ _ => (0 : Fin d → ℝ))
        γBar ε Dυ μ υ Dν η ν| ≤
      lpNormPer (ENNReal.ofReal βBar')
            (F_HJB V (fun _ _ _ => (0 : ℝ)) Dυ μ υ)
            * lpNormPer (ENNReal.ofReal βBar) η
        + (∑ i : Fin d,
            lpNormPer (ENNReal.ofReal γBar')
              (F_flux (fun _ _ _ => (0 : Fin d → ℝ)) Dυ μ i)
              * lpNormPer (ENNReal.ofReal γBar) (Dν i))
        + lpNormPer (ENNReal.ofReal γBar') (F_mass μ)
            * lpNormPer (ENNReal.ofReal γBar) ν
        + |ε| * ((∑ i : Fin d,
              lpNormPer (ENNReal.ofReal γBar') (G_grad γBar Dυ i)
                * lpNormPer (ENNReal.ofReal γBar) (Dν i))
            + lpNormPer (ENNReal.ofReal γBar') (G_val γBar υ)
                * lpNormPer (ENNReal.ofReal γBar) ν) :=
  mfgOperatorEpsPair_holder_bound
    (γBar := γBar) (βBar := βBar) (βBar' := βBar') (γBar' := γBar')
    hβ hγ ε V (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : Fin d → ℝ))
    Dυ μ υ Dν η ν
    hF_HJB hF_flux hF_mass hG_grad hG_val
    hη hν_γ hDν
    hI_HJB hI_flux hI_flux_i hI_mass hI_grad hI_grad_i hI_val

/-! ## Block A.3 — CLM-form regularised MFG operator `A_ε_CLM`

We assemble the bare-function pairing `mfgOperatorEpsPair` into a
**continuous linear map**

```
mfgOperatorEps_CLM ε V H DpH (p : MFGDomain β̄ γ̄)
  : (LpPer β̄ d × SobolevPerLp 1 γ̄ d) →L[ℝ] ℝ.
```

via `LinearMap.mkContinuousOfExistsBound`, using

* Block A.1 (`mfgOperatorEpsPair_test_{add,smul,zero}`) for ℝ-linearity
  of the underlying linear map (transported through `Lp.coeFn_add` /
  `Lp.coeFn_smul` and `integral_congr_ae`);
* Block A.2 (`mfgOperatorEpsPair_holder_bound`) for the existence of an
  operator-norm bound, packaged as
  `‖value‖ ≤ C · ‖(η_lp, (ν_lp, Dν_lp))‖`;
* the helpers `MemLpPer.integrable_mul` (in `Periodic/Lp.lean`) and
  `MemLpPer.mono_exponent_finite` (in `Periodic/LpInclusion.lean`) for
  the integrability and L^β/L^γ-membership bridge of `ν` (which appears
  in two distinct Hölder pairs).

Per CONVENTIONS §1b, the CLM signature carries auxiliary primal-side
`MemLpPer` hypotheses on `(F_HJB, F_flux i, F_mass, G_grad i, G_val)`;
these are discharged by downstream Block-B tasks from the paper bounds
`paper:lem:ADFGU.{a,b}`.

This module ships:

* `LpPair_ofTriple` — package a bare test triple `(η, ν, Dν)` together
  with `MemLpPer`-certificates into the Banach pair via `MemLpPer.toLp`
  and `MemSobolevPer.toLpSobolev`.
* `MFGOpEpsAuxHyps` — the bundled auxiliary primal-side hypotheses
  (Hölder-conjugate exponents, primal `MemLpPer` certificates).
* `mfgOperatorEps_CLM` — the real Hölder-bounded CLM.
* `mfgOperatorEps_CLM_apply` — unfolding identity to
  `mfgOperatorEpsPair` on the Lp coercions.
* `mfgOperator0_CLM := mfgOperatorEps_CLM 0` — ε=0 specialisation.
* `mfgOperator0_CLM_apply` — ε=0 unfolding identity (named theorem).
-/

open StationaryMFG.Solutions.MFG

variable {βBar γBar : ℝ≥0∞}

/-- Package a bare test triple `(η, ν, Dν)` plus `MemLpPer`/`MemSobolevPer`
certificates into the Banach pair `LpPer βBar d × SobolevPerLp 1 γBar d`
via `MemLpPer.toLp` and `MemSobolevPer.toLpSobolev`. -/
noncomputable def LpPair_ofTriple [Fact (1 ≤ γBar)]
    {η ν : (Fin d → ℝ) → ℝ} {Dν : Fin d → (Fin d → ℝ) → ℝ}
    (hη : Periodic.MemLpPer βBar η)
    (hν : Periodic.MemSobolevPer γBar ν)
    (hDν : ∀ i, Periodic.MemLpPer γBar (Dν i)) :
    Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d :=
  (hη.toLp, hν.toLpSobolev hDν)

/-- **Bundled auxiliary primal-side hypotheses** required to assemble
the regularised MFG CLM. The bundle records:

* the real Hölder exponents `βBar, βBar', γBar, γBar'` (with
  conjugacy);
* the inclusion `βBar ≤ γBar` so an `Lᵞ`-test-side function can be
  re-used in an `Lᵝ` Hölder pair (the `ν` term appears in both);
* the primal-side `MemLpPer` certificates for `F_HJB`, `F_flux i`,
  `F_mass`, `G_grad i`, `G_val`.

The CLM domain (`LpPer (ENNReal.ofReal βBar) d × SobolevPerLp 1
(ENNReal.ofReal γBar) d`) is parameterised by the *real* exponents
`βBar, γBar` (ℝ-valued, `> 0`) for compatibility with the Hölder
bound theorem `mfgOperatorEpsPair_holder_bound`. -/
structure MFGOpEpsAuxHyps
    (γBarReal βBarReal βBarReal' γBarReal' : ℝ)
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ) : Prop where
  /-- `(βBar, βBar')` is a real Hölder-conjugate pair. -/
  hβ : βBarReal.HolderConjugate βBarReal'
  /-- `(γBar, γBar')` is a real Hölder-conjugate pair. -/
  hγ : γBarReal.HolderConjugate γBarReal'
  /-- `Lᵝ'`-membership of `F_HJB`. -/
  hF_HJB : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal') (F_HJB V H Du m u)
  /-- `Lᵞ'`-membership of `F_flux i`. -/
  hF_flux : ∀ i, Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (F_flux DpH Du m i)
  /-- `Lᵞ'`-membership of `F_mass`. Phase 0 routing fix
  (`infra-P5-theorem1-phase-0`): the mass defect `m - 1` is paired
  against the value test `ν ∈ L^γ̄`, so it lives in `L^γ̄'`. The
  exponent inclusion `γ̄' ≤ β̄` (which is the only routing premise
  needed for the underlying carriage `m ∈ L^β̄`) follows from
  `α > 1, β > 0` via `Hamiltonian.gammaBar'_le_betaBar`, eliminating
  both algebra side conditions `1 ≤ β` and `β ≤ α`. -/
  hF_mass : Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal') (F_mass m)
  /-- `Lᵞ'`-membership of `G_grad i`. -/
  hG_grad : ∀ i, Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (G_grad γBarReal Du i)
  /-- `Lᵞ'`-membership of `G_val`. -/
  hG_val : Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal') (G_val γBarReal u)
  /-- The β-Hölder exponent is finite (`ENNReal.ofReal βBar ≠ ⊤`); used
  to invoke `MemLpPer.mono_exponent_finite`. -/
  hβTop : ENNReal.ofReal γBarReal ≠ ⊤

namespace MFGOpEpsAuxHyps

variable {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
variable {V : (Fin d → ℝ) → ℝ}
variable {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
variable {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
variable {Du : Fin d → (Fin d → ℝ) → ℝ}
variable {m u : (Fin d → ℝ) → ℝ}

end MFGOpEpsAuxHyps

/-! ### Integrability of the five Hölder summands at every test triple

The five integrand summands (paper line 925) are products `F · ξ` with
`F ∈ Lᵖ'` (primal side) and `ξ ∈ Lᵖ` (test side). The auxiliary
hypotheses above plus `MemLpPer.integrable_mul` provide integrability
for each summand at every test triple. -/

variable {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
variable {V : (Fin d → ℝ) → ℝ}
variable {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
variable {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
variable {Du : Fin d → (Fin d → ℝ) → ℝ}
variable {m u : (Fin d → ℝ) → ℝ}

private lemma integrable_F_HJB_eta
    (h : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
            V H DpH Du m u)
    {η : (Fin d → ℝ) → ℝ}
    (hη : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) η) :
    IntegrableOn (fun x => F_HJB V H Du m u x * η x) (UnitCube d) :=
  Periodic.MemLpPer.integrable_mul h.hβ.symm h.hF_HJB hη

private lemma integrable_F_flux_Dnu_i
    (h : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
            V H DpH Du m u)
    {Dν : Fin d → (Fin d → ℝ) → ℝ}
    (hDν : ∀ i, Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dν i))
    (i : Fin d) :
    IntegrableOn (fun x => F_flux DpH Du m i x * Dν i x) (UnitCube d) :=
  Periodic.MemLpPer.integrable_mul h.hγ.symm (h.hF_flux i) (hDν i)

private lemma integrable_F_mass_nu
    (h : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
            V H DpH Du m u)
    {ν : (Fin d → ℝ) → ℝ}
    (hν_γ : Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal) ν) :
    IntegrableOn (fun x => F_mass m x * ν x) (UnitCube d) :=
  Periodic.MemLpPer.integrable_mul h.hγ.symm h.hF_mass hν_γ

private lemma integrable_G_grad_Dnu_i
    (h : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
            V H DpH Du m u)
    {Dν : Fin d → (Fin d → ℝ) → ℝ}
    (hDν : ∀ i, Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dν i))
    (i : Fin d) :
    IntegrableOn (fun x => G_grad γBarReal Du i x * Dν i x) (UnitCube d) :=
  Periodic.MemLpPer.integrable_mul h.hγ.symm (h.hG_grad i) (hDν i)

private lemma integrable_G_val_nu
    (h : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
            V H DpH Du m u)
    {ν : (Fin d → ℝ) → ℝ}
    (hν_γ : Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal) ν) :
    IntegrableOn (fun x => G_val γBarReal u x * ν x) (UnitCube d) :=
  Periodic.MemLpPer.integrable_mul h.hγ.symm h.hG_val hν_γ

private lemma integrable_flux_sum
    (h : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
            V H DpH Du m u)
    {Dν : Fin d → (Fin d → ℝ) → ℝ}
    (hDν : ∀ i, Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dν i)) :
    IntegrableOn
      (fun x => ∑ i : Fin d, F_flux DpH Du m i x * Dν i x) (UnitCube d) := by
  have : Integrable
      (fun x => ∑ i : Fin d, F_flux DpH Du m i x * Dν i x)
      (Measure.restrict volume (UnitCube d)) := by
    apply integrable_finset_sum
    intro i _
    exact integrable_F_flux_Dnu_i (γBarReal := γBarReal)
      (βBarReal := βBarReal) (βBarReal' := βBarReal')
      (γBarReal' := γBarReal') h hDν i
  exact this

private lemma integrable_grad_sum
    (h : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
            V H DpH Du m u)
    {Dν : Fin d → (Fin d → ℝ) → ℝ}
    (hDν : ∀ i, Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dν i)) :
    IntegrableOn
      (fun x => ∑ i : Fin d, G_grad γBarReal Du i x * Dν i x) (UnitCube d) := by
  have : Integrable
      (fun x => ∑ i : Fin d, G_grad γBarReal Du i x * Dν i x)
      (Measure.restrict volume (UnitCube d)) := by
    apply integrable_finset_sum
    intro i _
    exact integrable_G_grad_Dnu_i (γBarReal := γBarReal)
      (βBarReal := βBarReal) (βBarReal' := βBarReal')
      (γBarReal' := γBarReal') h hDν i
  exact this

/-! ### Integrability of the two block-A.1 integrands at every test triple

`mfgOperatorEpsPair_test_add` requires integrability of the entire
`mfgOperatorPair`-integrand and `gateauxWpPair`-integrand at each test
triple. We discharge these from the per-summand integrabilities above
using the integrand-decomposition lemmas. -/

lemma integrable_mfgPair_integrand
    (h : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
            V H DpH Du m u)
    {η ν : (Fin d → ℝ) → ℝ} {Dν : Fin d → (Fin d → ℝ) → ℝ}
    (hη : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) η)
    (hν_γ : Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal) ν)
    (hDν : ∀ i, Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dν i)) :
    IntegrableOn
      (fun x =>
        (-(u x) - H x (fun i => Du i x) (m x) + V x) * (η x)
          + m x * (DpH x (fun i => Du i x) (m x)
                    ⬝ (fun i => Dν i x))
          + (m x - 1) * (ν x))
      (UnitCube d) := by
  -- The integrand equals `F_HJB·η + (∑ F_flux_i·Dν_i) + F_mass·ν` pointwise.
  have hpt : (fun x =>
        (-(u x) - H x (fun i => Du i x) (m x) + V x) * (η x)
          + m x * (DpH x (fun i => Du i x) (m x)
                    ⬝ (fun i => Dν i x))
          + (m x - 1) * (ν x))
      = (fun x => F_HJB V H Du m u x * η x
            + ∑ i : Fin d, F_flux DpH Du m i x * Dν i x
            + F_mass m x * ν x) := by
    funext x
    exact mfgPair_integrand_decomp V H DpH Du m u Dν η ν x
  rw [hpt]
  exact ((integrable_F_HJB_eta (γBarReal := γBarReal) (βBarReal := βBarReal)
          (βBarReal' := βBarReal') (γBarReal' := γBarReal') h hη).add
        (integrable_flux_sum (γBarReal := γBarReal) (βBarReal := βBarReal)
          (βBarReal' := βBarReal') (γBarReal' := γBarReal') h hDν)).add
      (integrable_F_mass_nu (γBarReal := γBarReal) (βBarReal := βBarReal)
          (βBarReal' := βBarReal') (γBarReal' := γBarReal') h hν_γ)

lemma integrable_gateaux_integrand
    (h : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
            V H DpH Du m u)
    {ν : (Fin d → ℝ) → ℝ} {Dν : Fin d → (Fin d → ℝ) → ℝ}
    (hν_γ : Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal) ν)
    (hDν : ∀ i, Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dν i)) :
    IntegrableOn
      (fun x =>
        vecAbsPowMinusTwo γBarReal (fun i => Du i x)
            * ((fun i => Du i x) ⬝ (fun i => Dν i x))
          + absPowMinusTwo γBarReal (u x) * (u x * (ν x)))
      (UnitCube d) := by
  -- The integrand equals `(∑ G_grad_i·Dν_i) + G_val·ν` pointwise.
  have hpt : (fun x =>
        vecAbsPowMinusTwo γBarReal (fun i => Du i x)
            * ((fun i => Du i x) ⬝ (fun i => Dν i x))
          + absPowMinusTwo γBarReal (u x) * (u x * (ν x)))
      = (fun x => (∑ i : Fin d, G_grad γBarReal Du i x * Dν i x)
            + G_val γBarReal u x * ν x) := by
    funext x
    exact gateaux_integrand_decomp γBarReal Du u Dν ν x
  rw [hpt]
  exact (integrable_grad_sum (γBarReal := γBarReal) (βBarReal := βBarReal)
          (βBarReal' := βBarReal') (γBarReal' := γBarReal') h hDν).add
      (integrable_G_val_nu (γBarReal := γBarReal) (βBarReal := βBarReal)
          (βBarReal' := βBarReal') (γBarReal' := γBarReal') h hν_γ)

/-! ### Underlying linear map

The underlying map `(η_lp, (ν_lp, Dν_lp)) ↦ mfgOperatorEpsPair … (⇑Dν_lp)
(⇑η_lp) (⇑ν_lp)` is well-defined as a function of the Lp pair (each Lp
element has a chosen representative `⇑·`). We package it as a
`LinearMap` using A.1's `_test_add`/`_test_smul`/`_test_zero` plus
`integral_congr_ae` to bridge `Lp.coeFn_add`/`coeFn_smul`. -/

variable [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)]

/-- The bare-function value `mfgOperatorEpsPair … Du m u (⇑Dν_lp) (⇑η_lp)
(⇑ν_lp)` for an `Lp` test pair, as a real number. -/
noncomputable def palomar_Operator_mfgOpEps_LpFun
    (ε : ℝ)
    (q : Periodic.LpPer (ENNReal.ofReal βBarReal) d
          × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d) : ℝ :=
  mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
    γBarReal ε Du m u (fun i => ⇑(q.2.2 i)) (⇑q.1) (⇑q.2.1)

/-- A `MemLpPer (ENNReal.ofReal βBarReal)` certificate for the
representative of an `LpPer (ENNReal.ofReal βBarReal) d` element. -/
private lemma memLpPer_coe_lp_beta
    (f : Periodic.LpPer (ENNReal.ofReal βBarReal) d) :
    Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) (⇑f : (Fin d → ℝ) → ℝ) :=
  MeasureTheory.Lp.memLp f

/-- A `MemLpPer (ENNReal.ofReal γBarReal)` certificate for the
representative of an `LpPer (ENNReal.ofReal γBarReal) d` element. -/
private lemma memLpPer_coe_lp_gamma
    (f : MeasureTheory.Lp ℝ (ENNReal.ofReal γBarReal)
          (Measure.restrict volume (UnitCube d))) :
    Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal) (⇑f : (Fin d → ℝ) → ℝ) :=
  MeasureTheory.Lp.memLp f

/-- The underlying ℝ-linear map of `mfgOperatorEps_CLM`. -/
noncomputable def palomar_Operator_mfgOpEps_LinearMap
    (h : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
            V H DpH Du m u)
    (ε : ℝ) :
    (Periodic.LpPer (ENNReal.ofReal βBarReal) d
      × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d) →ₗ[ℝ] ℝ where
  toFun := palomar_Operator_mfgOpEps_LpFun (V := V) (H := H) (DpH := DpH)
            (γBarReal := γBarReal) (βBarReal := βBarReal) (Du := Du) (m := m) (u := u) ε
  map_add' := by
    intro q₁ q₂
    -- Unfold to the bare-function pairing on coercions.
    have h_eta_ae : ⇑(q₁.1 + q₂.1) =ᵐ[Measure.restrict volume (UnitCube d)]
                    ⇑q₁.1 + ⇑q₂.1 := MeasureTheory.Lp.coeFn_add q₁.1 q₂.1
    have h_nu_ae : ⇑(q₁.2.1 + q₂.2.1) =ᵐ[Measure.restrict volume (UnitCube d)]
                    ⇑q₁.2.1 + ⇑q₂.2.1 := MeasureTheory.Lp.coeFn_add q₁.2.1 q₂.2.1
    have h_Dnu_ae : ∀ i,
        ⇑(q₁.2.2 i + q₂.2.2 i)
          =ᵐ[Measure.restrict volume (UnitCube d)]
            ⇑(q₁.2.2 i) + ⇑(q₂.2.2 i) :=
      fun i => MeasureTheory.Lp.coeFn_add (q₁.2.2 i) (q₂.2.2 i)
    -- The sum operation on the product/Sobolev pair.
    have h1 : (q₁ + q₂).1 = q₁.1 + q₂.1 := rfl
    have h2 : (q₁ + q₂).2.1 = q₁.2.1 + q₂.2.1 := rfl
    have h3 : ∀ i, (q₁ + q₂).2.2 i = q₁.2.2 i + q₂.2.2 i := fun _ => rfl
    -- Set up Lp memberships.
    have hη₁ := memLpPer_coe_lp_beta (βBarReal := βBarReal) q₁.1
    have hη₂ := memLpPer_coe_lp_beta (βBarReal := βBarReal) q₂.1
    have hν₁_γ := memLpPer_coe_lp_gamma (γBarReal := γBarReal) q₁.2.1
    have hν₂_γ := memLpPer_coe_lp_gamma (γBarReal := γBarReal) q₂.2.1
    have hDν₁ : ∀ i, Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal) (⇑(q₁.2.2 i)) :=
      fun i => memLpPer_coe_lp_gamma (γBarReal := γBarReal) (q₁.2.2 i)
    have hDν₂ : ∀ i, Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal) (⇑(q₂.2.2 i)) :=
      fun i => memLpPer_coe_lp_gamma (γBarReal := γBarReal) (q₂.2.2 i)
    -- Integrability of the two integrands at q₁ and q₂.
    have hI_A1 := integrable_mfgPair_integrand h hη₁ hν₁_γ hDν₁
    have hI_A2 := integrable_mfgPair_integrand h hη₂ hν₂_γ hDν₂
    have hI_B1 := integrable_gateaux_integrand h hν₁_γ hDν₁
    have hI_B2 := integrable_gateaux_integrand h hν₂_γ hDν₂
    -- Step 1: pass `mfgOperatorEpsPair … (⇑(sum)) …` to
    -- `mfgOperatorEpsPair … (⇑q₁ + ⇑q₂) …` via `integral_congr_ae`.
    -- Strategy: rewrite the LHS bare-function pairing on the *single* triple
    -- `(⇑(q₁+q₂).1, ⇑(q₁+q₂).2.1, ⇑(q₁+q₂).2.2 i)` to the *summed* triple
    -- `(⇑q₁.1 + ⇑q₂.1, ⇑q₁.2.1 + ⇑q₂.2.1, ⇑(q₁.2.2 i) + ⇑(q₂.2.2 i))` via
    -- `integral_congr_ae` on each of the two integrals.
    show palomar_Operator_mfgOpEps_LpFun (V := V) (H := H) (DpH := DpH)
            (γBarReal := γBarReal) (βBarReal := βBarReal) (Du := Du) (m := m) (u := u) ε
              (q₁ + q₂)
          = palomar_Operator_mfgOpEps_LpFun (V := V) (H := H) (DpH := DpH)
              (γBarReal := γBarReal) (βBarReal := βBarReal) (Du := Du) (m := m) (u := u) ε q₁
            + palomar_Operator_mfgOpEps_LpFun (V := V) (H := H) (DpH := DpH)
              (γBarReal := γBarReal) (βBarReal := βBarReal) (Du := Du) (m := m) (u := u) ε q₂
    -- Unfold to expose the integrals.
    unfold palomar_Operator_mfgOpEps_LpFun mfgOperatorEpsPair mfgOperatorPair gateauxWpPair
    -- a.e. equality on each component.
    have hDnu_all : ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ∀ i, ⇑((q₁ + q₂).2.2 i) x = (⇑(q₁.2.2 i) + ⇑(q₂.2.2 i)) x := by
      rw [MeasureTheory.ae_all_iff]
      intro i
      have hi_eq : (q₁ + q₂).2.2 i = q₁.2.2 i + q₂.2.2 i := h3 i
      rw [hi_eq]
      filter_upwards [h_Dnu_ae i] with x hx
      exact hx
    have h_eta_ae' : ⇑(q₁ + q₂).1 =ᵐ[Measure.restrict volume (UnitCube d)]
                      ⇑q₁.1 + ⇑q₂.1 := by
      rw [h1]; exact h_eta_ae
    have h_nu_ae' : ⇑(q₁ + q₂).2.1 =ᵐ[Measure.restrict volume (UnitCube d)]
                      ⇑q₁.2.1 + ⇑q₂.2.1 := by
      rw [h2]; exact h_nu_ae
    -- Bridge integrand 1 (`A`-block). The integrand depends on q₁+q₂ via
    -- η = ⇑(q₁+q₂).1, ν = ⇑(q₁+q₂).2.1, and Dν i = ⇑((q₁+q₂).2.2 i). The
    -- u/m/Du positions are unchanged.
    have hA_bridge :
        ∫ x in UnitCube d,
          (-(u x) - H x (fun i => Du i x) (m x) + V x)
              * (⇑(q₁ + q₂).1 x)
            + m x * (DpH x (fun i => Du i x) (m x)
                      ⬝ (fun i => ⇑((q₁ + q₂).2.2 i) x))
            + (m x - 1) * (⇑(q₁ + q₂).2.1 x)
          ∂(volume : Measure (Fin d → ℝ))
        = ∫ x in UnitCube d,
            (-(u x) - H x (fun i => Du i x) (m x) + V x)
                * ((⇑q₁.1 + ⇑q₂.1) x)
              + m x * (DpH x (fun i => Du i x) (m x)
                        ⬝ (fun i => (⇑(q₁.2.2 i) + ⇑(q₂.2.2 i)) x))
              + (m x - 1) * ((⇑q₁.2.1 + ⇑q₂.2.1) x)
          ∂(volume : Measure (Fin d → ℝ)) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [h_eta_ae', h_nu_ae', hDnu_all] with x hxη hxν hxDnu
      congr 1
      · congr 1
        · rw [hxη]
        · congr 2
          funext i
          exact hxDnu i
      · rw [hxν]
    -- Bridge integrand 2 (`B`-block, the gateaux integrand).
    have hB_bridge :
        ∫ x in UnitCube d,
          vecAbsPowMinusTwo γBarReal (fun i => Du i x)
              * ((fun i => Du i x) ⬝ (fun i => ⇑((q₁ + q₂).2.2 i) x))
            + absPowMinusTwo γBarReal (u x)
                * (u x * (⇑(q₁ + q₂).2.1 x))
          ∂(volume : Measure (Fin d → ℝ))
        = ∫ x in UnitCube d,
            vecAbsPowMinusTwo γBarReal (fun i => Du i x)
                * ((fun i => Du i x) ⬝
                    (fun i => (⇑(q₁.2.2 i) + ⇑(q₂.2.2 i)) x))
              + absPowMinusTwo γBarReal (u x)
                  * (u x * ((⇑q₁.2.1 + ⇑q₂.2.1) x))
          ∂(volume : Measure (Fin d → ℝ)) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [h_nu_ae', hDnu_all] with x hxν hxDnu
      congr 1
      · congr 2
        funext i
        exact hxDnu i
      · rw [hxν]
    rw [hA_bridge, hB_bridge]
    -- Now apply A.1's `_test_add` (after refolding).
    have hadd := mfgOperatorEpsPair_test_add (V := V) (H := H) (DpH := DpH)
                  γBarReal ε Du m u
                  (fun i => ⇑(q₁.2.2 i)) (fun i => ⇑(q₂.2.2 i))
                  (⇑q₁.1) (⇑q₂.1) (⇑q₁.2.1) (⇑q₂.2.1)
                  hI_A1 hI_A2 hI_B1 hI_B2
    -- Unfold `hadd` and match shapes.
    unfold mfgOperatorEpsPair mfgOperatorPair gateauxWpPair at hadd
    -- The current goal differs from `hadd` only by `Pi.add_apply` rewrites
    -- and the trivial `(fun i x => Dν₁ i x + Dν₂ i x) i x = (Dν₁ i + Dν₂ i) x`.
    convert hadd using 2 <;> simp [Pi.add_apply]
  map_smul' := by
    intro c q
    have h_eta_ae : ⇑(c • q.1) =ᵐ[Measure.restrict volume (UnitCube d)]
                    c • ⇑q.1 := MeasureTheory.Lp.coeFn_smul c q.1
    have h_nu_ae : ⇑(c • q.2.1) =ᵐ[Measure.restrict volume (UnitCube d)]
                    c • ⇑q.2.1 := MeasureTheory.Lp.coeFn_smul c q.2.1
    have h_Dnu_ae : ∀ i,
        ⇑(c • q.2.2 i)
          =ᵐ[Measure.restrict volume (UnitCube d)]
            c • ⇑(q.2.2 i) :=
      fun i => MeasureTheory.Lp.coeFn_smul c (q.2.2 i)
    have h1 : (c • q).1 = c • q.1 := rfl
    have h2 : (c • q).2.1 = c • q.2.1 := rfl
    have h3 : ∀ i, (c • q).2.2 i = c • q.2.2 i := fun _ => rfl
    show palomar_Operator_mfgOpEps_LpFun (V := V) (H := H) (DpH := DpH)
            (γBarReal := γBarReal) (βBarReal := βBarReal) (Du := Du) (m := m) (u := u) ε
              (c • q)
          = (RingHom.id ℝ) c •
              palomar_Operator_mfgOpEps_LpFun (V := V) (H := H) (DpH := DpH)
              (γBarReal := γBarReal) (βBarReal := βBarReal) (Du := Du) (m := m) (u := u) ε q
    simp only [RingHom.id_apply, smul_eq_mul]
    unfold palomar_Operator_mfgOpEps_LpFun mfgOperatorEpsPair mfgOperatorPair gateauxWpPair
    -- a.e. equality on each component.
    have hDnu_all : ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ∀ i, ⇑((c • q).2.2 i) x = (c • ⇑(q.2.2 i)) x := by
      rw [MeasureTheory.ae_all_iff]
      intro i
      have hi_eq : (c • q).2.2 i = c • q.2.2 i := h3 i
      rw [hi_eq]
      filter_upwards [h_Dnu_ae i] with x hx
      exact hx
    have h_eta_ae' : ⇑(c • q).1 =ᵐ[Measure.restrict volume (UnitCube d)]
                      c • ⇑q.1 := by
      rw [h1]; exact h_eta_ae
    have h_nu_ae' : ⇑(c • q).2.1 =ᵐ[Measure.restrict volume (UnitCube d)]
                      c • ⇑q.2.1 := by
      rw [h2]; exact h_nu_ae
    -- Bridge each integrand to the smul'd form via `integral_congr_ae`.
    have hA_bridge :
        ∫ x in UnitCube d,
          (-(u x) - H x (fun i => Du i x) (m x) + V x)
              * (⇑(c • q).1 x)
            + m x * (DpH x (fun i => Du i x) (m x)
                      ⬝ (fun i => ⇑((c • q).2.2 i) x))
            + (m x - 1) * (⇑(c • q).2.1 x)
          ∂(volume : Measure (Fin d → ℝ))
        = ∫ x in UnitCube d,
            (-(u x) - H x (fun i => Du i x) (m x) + V x)
              * ((c • ⇑q.1) x)
              + m x * (DpH x (fun i => Du i x) (m x)
                        ⬝ (fun i => (c • ⇑(q.2.2 i)) x))
              + (m x - 1) * ((c • ⇑q.2.1) x)
          ∂(volume : Measure (Fin d → ℝ)) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [h_eta_ae', h_nu_ae', hDnu_all] with x hxη hxν hxDnu
      congr 1
      · congr 1
        · rw [hxη]
        · congr 2
          funext i
          exact hxDnu i
      · rw [hxν]
    have hB_bridge :
        ∫ x in UnitCube d,
          vecAbsPowMinusTwo γBarReal (fun i => Du i x)
              * ((fun i => Du i x) ⬝ (fun i => ⇑((c • q).2.2 i) x))
            + absPowMinusTwo γBarReal (u x)
                * (u x * (⇑(c • q).2.1 x))
          ∂(volume : Measure (Fin d → ℝ))
        = ∫ x in UnitCube d,
            vecAbsPowMinusTwo γBarReal (fun i => Du i x)
                * ((fun i => Du i x) ⬝
                    (fun i => (c • ⇑(q.2.2 i)) x))
              + absPowMinusTwo γBarReal (u x)
                  * (u x * ((c • ⇑q.2.1) x))
          ∂(volume : Measure (Fin d → ℝ)) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [h_nu_ae', hDnu_all] with x hxν hxDnu
      congr 1
      · congr 2
        funext i
        exact hxDnu i
      · rw [hxν]
    rw [hA_bridge, hB_bridge]
    -- Apply A.1's `_test_smul`.
    have hsmul := mfgOperatorEpsPair_test_smul (V := V) (H := H) (DpH := DpH)
                  γBarReal ε Du m u c
                  (fun i => ⇑(q.2.2 i)) (⇑q.1) (⇑q.2.1)
    unfold mfgOperatorEpsPair mfgOperatorPair gateauxWpPair at hsmul
    -- Match shapes.
    convert hsmul using 2 <;> simp [Pi.smul_apply]

/-! ### Operator-norm bound

The CLM bound comes from `mfgOperatorEpsPair_holder_bound` (Block A.2)
applied to the Lp coercions. We don't need a closed-form constant: it
suffices to show **existence** of a `C` independent of the test pair.
The right-hand side of A.2's bound depends on the test pair only
through `‖η‖_{β̄} = ‖q.1‖`, `‖ν‖_{β̄}, ‖ν‖_{γ̄}`, and `‖Dν_i‖_{γ̄}`. Each
of these is dominated by the *product norm* `‖q‖` (with a
finite-measure embedding constant for the β/γ swap). -/

lemma palomar_Operator_mfgOpEps_LinearMap_bound
    (h : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
            V H DpH Du m u)
    (ε : ℝ) :
    ∃ C : ℝ, ∀ q : Periodic.LpPer (ENNReal.ofReal βBarReal) d
                × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d,
      ‖palomar_Operator_mfgOpEps_LinearMap (γBarReal := γBarReal) (βBarReal := βBarReal)
          (βBarReal' := βBarReal') (γBarReal' := γBarReal')
          (V := V) (H := H) (DpH := DpH) (Du := Du) (m := m) (u := u) h ε q‖ ≤ C * ‖q‖ := by
  -- Define the primal-side aggregate dominator (independent of `q`).
  -- Phase 0 routing fix: `F_mass` lives in `L^γ̄'` (paired with `ν ∈ L^γ̄`).
  set Cβ : ℝ := Periodic.lpNormPer (ENNReal.ofReal βBarReal') (F_HJB V H Du m u)
              with hCβ
  set Cγ : ℝ := (∑ i : Fin d,
                  Periodic.lpNormPer (ENNReal.ofReal γBarReal')
                    (F_flux DpH Du m i))
                + Periodic.lpNormPer (ENNReal.ofReal γBarReal') (F_mass m)
                + (∑ i : Fin d,
                  Periodic.lpNormPer (ENNReal.ofReal γBarReal')
                    (G_grad γBarReal Du i))
                + Periodic.lpNormPer (ENNReal.ofReal γBarReal') (G_val γBarReal u)
              with hCγ
  -- A coarse upper bound: take `C := 2 * (Cβ + |ε| · Cγ + Cγ)` plus 1.
  -- We will directly use A.2's bound, then show each `‖·‖_{p}` factor is ≤ ‖q‖.
  -- For `mkContinuousOfExistsBound`, any `C` works.
  refine ⟨1 + Cβ + Cγ + |ε| * Cγ, ?_⟩
  intro q
  -- Apply A.2 at the test triple `(⇑q.2.2 i, ⇑q.1, ⇑q.2.1)`.
  have hη := memLpPer_coe_lp_beta (βBarReal := βBarReal) q.1
  have hν_γ := memLpPer_coe_lp_gamma (γBarReal := γBarReal) q.2.1
  have hDν : ∀ i, Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal) (⇑(q.2.2 i)) :=
    fun i => memLpPer_coe_lp_gamma (γBarReal := γBarReal) (q.2.2 i)
  -- The "value" we are bounding.
  set v : ℝ := mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                γBarReal ε Du m u (fun i => ⇑(q.2.2 i)) (⇑q.1) (⇑q.2.1) with hv
  -- A.2 bound.
  have hbd := mfgOperatorEpsPair_holder_bound
              (γBar := γBarReal) (βBar := βBarReal)
              (βBar' := βBarReal') (γBar' := γBarReal')
              h.hβ h.hγ ε V H DpH Du m u
              (fun i => ⇑(q.2.2 i)) (⇑q.1) (⇑q.2.1)
              h.hF_HJB h.hF_flux h.hF_mass h.hG_grad h.hG_val
              hη hν_γ hDν
              (integrable_F_HJB_eta (γBarReal := γBarReal) (βBarReal := βBarReal)
                (βBarReal' := βBarReal') (γBarReal' := γBarReal') h hη)
              (integrable_flux_sum (γBarReal := γBarReal) (βBarReal := βBarReal)
                (βBarReal' := βBarReal') (γBarReal' := γBarReal') h hDν)
              (fun i => integrable_F_flux_Dnu_i (γBarReal := γBarReal)
                (βBarReal := βBarReal) (βBarReal' := βBarReal')
                (γBarReal' := γBarReal') h hDν i)
              (integrable_F_mass_nu (γBarReal := γBarReal) (βBarReal := βBarReal)
                (βBarReal' := βBarReal') (γBarReal' := γBarReal') h hν_γ)
              (integrable_grad_sum (γBarReal := γBarReal) (βBarReal := βBarReal)
                (βBarReal' := βBarReal') (γBarReal' := γBarReal') h hDν)
              (fun i => integrable_G_grad_Dnu_i (γBarReal := γBarReal)
                (βBarReal := βBarReal) (βBarReal' := βBarReal')
                (γBarReal' := γBarReal') h hDν i)
              (integrable_G_val_nu (γBarReal := γBarReal) (βBarReal := βBarReal)
                (βBarReal' := βBarReal') (γBarReal' := γBarReal') h hν_γ)
  -- Norm equalities for the test side: each component norm equals the
  -- corresponding `lpNormPer` (via `lpNormPer_eq_norm_toLp` / the
  -- `Lp.norm_def` characterisation).
  have hη_norm : Periodic.lpNormPer (ENNReal.ofReal βBarReal) (⇑q.1) = ‖q.1‖ := by
    unfold Periodic.lpNormPer Periodic.eLpNormPer
    rw [MeasureTheory.Lp.norm_def]
  have hν_norm_γ : Periodic.lpNormPer (ENNReal.ofReal γBarReal) (⇑q.2.1) = ‖q.2.1‖ := by
    unfold Periodic.lpNormPer Periodic.eLpNormPer
    rw [MeasureTheory.Lp.norm_def]
  have hDν_norm : ∀ i,
      Periodic.lpNormPer (ENNReal.ofReal γBarReal) (⇑(q.2.2 i)) = ‖q.2.2 i‖ := by
    intro i
    unfold Periodic.lpNormPer Periodic.eLpNormPer
    rw [MeasureTheory.Lp.norm_def]
  -- Norms in `LpPer βBar` are non-negative (Lp norms are non-negative).
  have hη_nn : 0 ≤ ‖q.1‖ := norm_nonneg _
  have hν_nn : 0 ≤ ‖q.2.1‖ := norm_nonneg _
  have hDνi_nn : ∀ i, 0 ≤ ‖q.2.2 i‖ := fun i => norm_nonneg _
  -- ‖q‖ dominates each component norm.
  have hq_eta_le : ‖q.1‖ ≤ ‖q‖ := by
    have := Prod.norm_def q
    -- The product norm is `max` of components in Mathlib. ‖q‖ ≥ ‖q.1‖.
    calc ‖q.1‖ ≤ max ‖q.1‖ ‖q.2‖ := le_max_left _ _
      _ = ‖q‖ := (Prod.norm_def q).symm
  have hq_pair_le : ‖q.2‖ ≤ ‖q‖ := by
    calc ‖q.2‖ ≤ max ‖q.1‖ ‖q.2‖ := le_max_right _ _
      _ = ‖q‖ := (Prod.norm_def q).symm
  have hq_nu_le : ‖q.2.1‖ ≤ ‖q‖ := by
    calc ‖q.2.1‖ ≤ max ‖q.2.1‖ ‖q.2.2‖ := le_max_left _ _
      _ = ‖q.2‖ := (Prod.norm_def q.2).symm
      _ ≤ ‖q‖ := hq_pair_le
  have hq_Dnu_le : ∀ i, ‖q.2.2 i‖ ≤ ‖q‖ := by
    intro i
    calc ‖q.2.2 i‖ ≤ ‖q.2.2‖ := norm_le_pi_norm q.2.2 i
      _ ≤ max ‖q.2.1‖ ‖q.2.2‖ := le_max_right _ _
      _ = ‖q.2‖ := (Prod.norm_def q.2).symm
      _ ≤ ‖q‖ := hq_pair_le
  -- Now bound each summand of A.2's RHS by `(primal-norm) * ‖q‖`.
  set A_HJB : ℝ := Periodic.lpNormPer (ENNReal.ofReal βBarReal') (F_HJB V H Du m u) with hA_HJB
  -- Phase 0 routing fix: `A_mass` is in `γBar'`.
  set A_mass : ℝ := Periodic.lpNormPer (ENNReal.ofReal γBarReal') (F_mass m) with hA_mass
  set A_flux_i : Fin d → ℝ := fun i =>
    Periodic.lpNormPer (ENNReal.ofReal γBarReal') (F_flux DpH Du m i) with hA_flux_i
  set A_grad_i : Fin d → ℝ := fun i =>
    Periodic.lpNormPer (ENNReal.ofReal γBarReal') (G_grad γBarReal Du i) with hA_grad_i
  set A_val : ℝ := Periodic.lpNormPer (ENNReal.ofReal γBarReal') (G_val γBarReal u) with hA_val
  -- Non-negativity of all primal-side norms.
  have hA_HJB_nn : 0 ≤ A_HJB := Periodic.lpNormPer_nonneg _ _
  have hA_mass_nn : 0 ≤ A_mass := Periodic.lpNormPer_nonneg _ _
  have hA_flux_i_nn : ∀ i, 0 ≤ A_flux_i i :=
    fun i => Periodic.lpNormPer_nonneg _ _
  have hA_grad_i_nn : ∀ i, 0 ≤ A_grad_i i :=
    fun i => Periodic.lpNormPer_nonneg _ _
  have hA_val_nn : 0 ≤ A_val := Periodic.lpNormPer_nonneg _ _
  -- ‖v‖ ≤ A.2-RHS, A.2-RHS ≤ (Cβ + Cγ·(1+|ε|)) · ‖q‖.
  -- The unfolded `palomar_Operator_mfgOpEps_LinearMap` value is `v` (modulo `show`).
  have hLHS_eq : ‖palomar_Operator_mfgOpEps_LinearMap (γBarReal := γBarReal) (βBarReal := βBarReal)
                    (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                    (V := V) (H := H) (DpH := DpH) (Du := Du) (m := m) (u := u) h ε q‖
                = |v| := by
    show ‖palomar_Operator_mfgOpEps_LpFun (V := V) (H := H) (DpH := DpH)
              (γBarReal := γBarReal) (βBarReal := βBarReal)
              (Du := Du) (m := m) (u := u) ε q‖ = |v|
    unfold palomar_Operator_mfgOpEps_LpFun
    rw [Real.norm_eq_abs]
  rw [hLHS_eq]
  -- Now we need `|v| ≤ (1 + Cβ + Cγ + |ε|·Cγ) * ‖q‖`.
  -- Bound A.2-RHS by `(Cβ + Cγ·(1+|ε|)) · ‖q‖`.
  have h_q_nn : 0 ≤ ‖q‖ := norm_nonneg _
  -- Replace `lpNormPer βBar η` by `‖q.1‖`, `lpNormPer γBar (Dν i)` by
  -- `‖q.2.2 i‖`, `lpNormPer γBar ν` by `‖q.2.1‖`, and bound
  -- `lpNormPer βBar ν ≤ lpNormPer γBar ν = ‖q.2.1‖`.
  rw [hη_norm, hν_norm_γ] at hbd
  have hbd' : |v| ≤
      A_HJB * ‖q.1‖
      + (∑ i : Fin d, A_flux_i i * Periodic.lpNormPer (ENNReal.ofReal γBarReal) (⇑(q.2.2 i)))
      + A_mass * ‖q.2.1‖
      + |ε| * ((∑ i : Fin d, A_grad_i i * Periodic.lpNormPer (ENNReal.ofReal γBarReal) (⇑(q.2.2 i)))
              + A_val * ‖q.2.1‖) := hbd
  -- Now turn each `lpNormPer γBar (⇑(q.2.2 i))` into `‖q.2.2 i‖`.
  have h_eq_Dν : ∀ i,
      A_flux_i i * Periodic.lpNormPer (ENNReal.ofReal γBarReal) (⇑(q.2.2 i))
        = A_flux_i i * ‖q.2.2 i‖ := fun i => by rw [hDν_norm i]
  have h_eq_grad : ∀ i,
      A_grad_i i * Periodic.lpNormPer (ENNReal.ofReal γBarReal) (⇑(q.2.2 i))
        = A_grad_i i * ‖q.2.2 i‖ := fun i => by rw [hDν_norm i]
  have h_sum_flux :
      (∑ i : Fin d, A_flux_i i * Periodic.lpNormPer (ENNReal.ofReal γBarReal) (⇑(q.2.2 i)))
      = ∑ i : Fin d, A_flux_i i * ‖q.2.2 i‖ := by
    refine Finset.sum_congr rfl (fun i _ => h_eq_Dν i)
  have h_sum_grad :
      (∑ i : Fin d, A_grad_i i * Periodic.lpNormPer (ENNReal.ofReal γBarReal) (⇑(q.2.2 i)))
      = ∑ i : Fin d, A_grad_i i * ‖q.2.2 i‖ := by
    refine Finset.sum_congr rfl (fun i _ => h_eq_grad i)
  rw [h_sum_flux, h_sum_grad] at hbd'
  -- Now bound: A_HJB * ‖q.1‖ ≤ A_HJB * ‖q‖.
  have h_HJB_bd : A_HJB * ‖q.1‖ ≤ A_HJB * ‖q‖ :=
    mul_le_mul_of_nonneg_left hq_eta_le hA_HJB_nn
  have h_mass_bd : A_mass * ‖q.2.1‖ ≤ A_mass * ‖q‖ :=
    mul_le_mul_of_nonneg_left hq_nu_le hA_mass_nn
  have h_val_bd : A_val * ‖q.2.1‖ ≤ A_val * ‖q‖ :=
    mul_le_mul_of_nonneg_left hq_nu_le hA_val_nn
  -- Each `A_flux_i i * ‖q.2.2 i‖ ≤ A_flux_i i * ‖q‖`.
  have h_flux_i_bd : ∀ i, A_flux_i i * ‖q.2.2 i‖ ≤ A_flux_i i * ‖q‖ :=
    fun i => mul_le_mul_of_nonneg_left (hq_Dnu_le i) (hA_flux_i_nn i)
  have h_grad_i_bd : ∀ i, A_grad_i i * ‖q.2.2 i‖ ≤ A_grad_i i * ‖q‖ :=
    fun i => mul_le_mul_of_nonneg_left (hq_Dnu_le i) (hA_grad_i_nn i)
  have h_sum_flux_bd : (∑ i : Fin d, A_flux_i i * ‖q.2.2 i‖)
                      ≤ ∑ i : Fin d, A_flux_i i * ‖q‖ :=
    Finset.sum_le_sum (fun i _ => h_flux_i_bd i)
  have h_sum_grad_bd : (∑ i : Fin d, A_grad_i i * ‖q.2.2 i‖)
                      ≤ ∑ i : Fin d, A_grad_i i * ‖q‖ :=
    Finset.sum_le_sum (fun i _ => h_grad_i_bd i)
  -- Aggregate.
  have habs_eps_nn : 0 ≤ |ε| := abs_nonneg _
  have h_step1 : |v| ≤
      A_HJB * ‖q‖
      + (∑ i : Fin d, A_flux_i i * ‖q‖)
      + A_mass * ‖q‖
      + |ε| * ((∑ i : Fin d, A_grad_i i * ‖q‖)
              + A_val * ‖q‖) := by
    calc |v|
        ≤ A_HJB * ‖q.1‖
          + (∑ i : Fin d, A_flux_i i * ‖q.2.2 i‖)
          + A_mass * ‖q.2.1‖
          + |ε| * ((∑ i : Fin d, A_grad_i i * ‖q.2.2 i‖)
                  + A_val * ‖q.2.1‖) := hbd'
      _ ≤ A_HJB * ‖q‖
          + (∑ i : Fin d, A_flux_i i * ‖q.2.2 i‖)
          + A_mass * ‖q.2.1‖
          + |ε| * ((∑ i : Fin d, A_grad_i i * ‖q.2.2 i‖)
                  + A_val * ‖q.2.1‖) := by
              gcongr
      _ ≤ A_HJB * ‖q‖
          + (∑ i : Fin d, A_flux_i i * ‖q‖)
          + A_mass * ‖q‖
          + |ε| * ((∑ i : Fin d, A_grad_i i * ‖q‖)
                  + A_val * ‖q‖) := by
              gcongr with i
  -- Now factor `‖q‖` out of all summands:
  have h_factor :
      A_HJB * ‖q‖
      + (∑ i : Fin d, A_flux_i i * ‖q‖)
      + A_mass * ‖q‖
      + |ε| * ((∑ i : Fin d, A_grad_i i * ‖q‖)
              + A_val * ‖q‖)
      = (Cβ + ((∑ i : Fin d, A_flux_i i) + A_mass)
          + |ε| * ((∑ i : Fin d, A_grad_i i) + A_val)) * ‖q‖ := by
    have h1 : (∑ i : Fin d, A_flux_i i * ‖q‖) = (∑ i : Fin d, A_flux_i i) * ‖q‖ := by
      rw [Finset.sum_mul]
    have h2 : (∑ i : Fin d, A_grad_i i * ‖q‖) = (∑ i : Fin d, A_grad_i i) * ‖q‖ := by
      rw [Finset.sum_mul]
    rw [h1, h2]
    show A_HJB * ‖q‖ + (∑ i : Fin d, A_flux_i i) * ‖q‖ + A_mass * ‖q‖
        + |ε| * ((∑ i : Fin d, A_grad_i i) * ‖q‖ + A_val * ‖q‖)
      = (A_HJB + ((∑ i : Fin d, A_flux_i i) + A_mass)
            + |ε| * ((∑ i : Fin d, A_grad_i i) + A_val)) * ‖q‖
    ring
  -- Combine `h_step1` with `h_factor` to get `|v| ≤ (Cβ + …) · ‖q‖`.
  have h_step2 : |v| ≤
      (Cβ + ((∑ i : Fin d, A_flux_i i) + A_mass)
          + |ε| * ((∑ i : Fin d, A_grad_i i) + A_val)) * ‖q‖ := by
    rw [← h_factor]; exact h_step1
  -- Final: `(Cβ + ∑A_flux + A_mass + |ε|·(∑A_grad + A_val)) ≤ 1 + Cβ + Cγ + |ε|·Cγ`.
  have h_aggregate :
      Cβ + ((∑ i : Fin d, A_flux_i i) + A_mass)
        + |ε| * ((∑ i : Fin d, A_grad_i i) + A_val)
      ≤ 1 + Cβ + Cγ + |ε| * Cγ := by
    -- (∑ A_flux_i) + A_mass ≤ Cγ; (∑ A_grad_i + A_val) ≤ Cγ.
    have h_flux_sum_nn : 0 ≤ ∑ i : Fin d, A_flux_i i :=
      Finset.sum_nonneg (fun i _ => hA_flux_i_nn i)
    have h_grad_sum_nn : 0 ≤ ∑ i : Fin d, A_grad_i i :=
      Finset.sum_nonneg (fun i _ => hA_grad_i_nn i)
    have h_le_Cγ_flux : (∑ i : Fin d, A_flux_i i) + A_mass ≤ Cγ := by
      show (∑ i : Fin d, A_flux_i i) + A_mass
            ≤ (∑ i : Fin d, A_flux_i i) + A_mass
                + (∑ i : Fin d, A_grad_i i) + A_val
      linarith [h_grad_sum_nn, hA_val_nn]
    have h_le_Cγ_other : (∑ i : Fin d, A_grad_i i) + A_val ≤ Cγ := by
      show (∑ i : Fin d, A_grad_i i) + A_val
            ≤ (∑ i : Fin d, A_flux_i i) + A_mass
                + (∑ i : Fin d, A_grad_i i) + A_val
      linarith [h_flux_sum_nn, hA_mass_nn]
    have h_eps_part :
        |ε| * ((∑ i : Fin d, A_grad_i i) + A_val) ≤ |ε| * Cγ :=
      mul_le_mul_of_nonneg_left h_le_Cγ_other habs_eps_nn
    calc Cβ + ((∑ i : Fin d, A_flux_i i) + A_mass) + |ε| * ((∑ i : Fin d, A_grad_i i) + A_val)
        ≤ Cβ + Cγ + |ε| * Cγ := by
            have := add_le_add (add_le_add (le_refl Cβ) h_le_Cγ_flux) h_eps_part
            exact this
      _ ≤ 1 + Cβ + Cγ + |ε| * Cγ := by linarith
  -- Combine: |v| ≤ (Cβ + …) · ‖q‖ ≤ (1 + Cβ + Cγ + |ε|·Cγ) · ‖q‖.
  have hfinal :
      (Cβ + ((∑ i : Fin d, A_flux_i i) + A_mass)
          + |ε| * ((∑ i : Fin d, A_grad_i i) + A_val)) * ‖q‖
        ≤ (1 + Cβ + Cγ + |ε| * Cγ) * ‖q‖ :=
    mul_le_mul_of_nonneg_right h_aggregate h_q_nn
  exact le_trans h_step2 hfinal

/-! ### Assembly: the CLM and unfolding lemma -/

/-- **CLM-form regularised MFG operator** `A_ε_CLM`.

The continuous linear map from `LpPer (ENNReal.ofReal βBarReal) d ×
SobolevPerLp 1 (ENNReal.ofReal γBarReal) d` to `ℝ` whose value on a
bridged Lp pair `(η_lp, (ν_lp, Dν_lp))` is the bare-function pairing
`mfgOperatorEpsPair γBarReal ε V H DpH Du m u (⇑Dν_lp) (⇑η_lp) (⇑ν_lp)`.

Built via `LinearMap.mkContinuousOfExistsBound` from the underlying
`LinearMap` (constructed from A.1's `_test_{add,smul}`) with the
operator-norm bound from A.2's `_holder_bound`. The auxiliary
primal-side `MemLpPer` hypotheses are bundled in `MFGOpEpsAuxHyps`. -/
noncomputable def mfgOperatorEps_CLM
    (h : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
            V H DpH Du m u)
    (ε : ℝ) :
    (Periodic.LpPer (ENNReal.ofReal βBarReal) d
      × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d) →L[ℝ] ℝ :=
  LinearMap.mkContinuousOfExistsBound
    (palomar_Operator_mfgOpEps_LinearMap (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      (V := V) (H := H) (DpH := DpH) (Du := Du) (m := m) (u := u) h ε)
    (palomar_Operator_mfgOpEps_LinearMap_bound (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      (V := V) (H := H) (DpH := DpH) (Du := Du) (m := m) (u := u) h ε)

/-- **Unfolding identity** for `mfgOperatorEps_CLM`.

The CLM applied to a bridged Lp pair `(η_lp, (ν_lp, Dν_lp))` equals
the bare-function pairing on the Lp coercions. -/
theorem mfgOperatorEps_CLM_apply
    (h : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
            V H DpH Du m u)
    (ε : ℝ)
    (q : Periodic.LpPer (ENNReal.ofReal βBarReal) d
          × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d) :
    mfgOperatorEps_CLM (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      (V := V) (H := H) (DpH := DpH) (Du := Du) (m := m) (u := u) h ε q
      = mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε Du m u
          (fun i => ⇑(q.2.2 i)) (⇑q.1) (⇑q.2.1) := by
  unfold mfgOperatorEps_CLM
  rw [LinearMap.mkContinuousOfExistsBound_apply]
  rfl

/-- The `ε = 0` specialisation used by `paper:thm:main-simple.power.growth`. -/
noncomputable def mfgOperator0_CLM
    (h : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
            V H DpH Du m u) :
    (Periodic.LpPer (ENNReal.ofReal βBarReal) d
      × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d) →L[ℝ] ℝ :=
  mfgOperatorEps_CLM (γBarReal := γBarReal) (βBarReal := βBarReal)
    (βBarReal' := βBarReal') (γBarReal' := γBarReal')
    (V := V) (H := H) (DpH := DpH) (Du := Du) (m := m) (u := u) h 0

/-- Unfolding identity for `mfgOperator0_CLM` (ε=0 specialisation). -/
theorem mfgOperator0_CLM_apply
    (h : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
            V H DpH Du m u)
    (q : Periodic.LpPer (ENNReal.ofReal βBarReal) d
          × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d) :
    mfgOperator0_CLM (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      (V := V) (H := H) (DpH := DpH) (Du := Du) (m := m) (u := u) h q
      = mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal 0 Du m u
          (fun i => ⇑(q.2.2 i)) (⇑q.1) (⇑q.2.1) :=
  mfgOperatorEps_CLM_apply (γBarReal := γBarReal) (βBarReal := βBarReal)
    (βBarReal' := βBarReal') (γBarReal' := γBarReal')
    (V := V) (H := H) (DpH := DpH) (Du := Du) (m := m) (u := u) h 0 q

/-! ### Sanity-check example

Exercise `mfgOperator0_CLM_apply` on the trivial Hamiltonian (`H ≡ 0`,
`D_pH ≡ 0`). The CLM value equals the bare-function pairing on the Lp
coercions. -/

example
    (h : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
            V (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : Fin d → ℝ))
            Du m u)
    (q : Periodic.LpPer (ENNReal.ofReal βBarReal) d
          × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d) :
    mfgOperator0_CLM (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      (V := V) (H := fun _ _ _ => (0 : ℝ))
      (DpH := fun _ _ _ => (0 : Fin d → ℝ))
      (Du := Du) (m := m) (u := u) h q
      = mfgOperatorEpsPair (V := V) (H := fun _ _ _ => (0 : ℝ))
          (DpH := fun _ _ _ => (0 : Fin d → ℝ))
          γBarReal 0 Du m u
          (fun i => ⇑(q.2.2 i)) (⇑q.1) (⇑q.2.1) :=
  mfgOperator0_CLM_apply h q

end Banach
end SimplePower
end Theorems
end StationaryMFG
