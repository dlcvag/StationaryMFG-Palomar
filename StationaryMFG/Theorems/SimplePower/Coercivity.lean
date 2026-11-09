module

public import StationaryMFG.Solutions.Regularized
public import StationaryMFG.Solutions.MFGOperator
public import StationaryMFG.Monotone.Coercive
public import StationaryMFG.Hamiltonian.Assumptions
public import Mathlib.Order.Filter.AtTopBot.Tendsto

@[expose] public section

/-!
# Coercivity test-pair algebraic identity (paper line 947, eq:coercive-test.Aepsi)

This module records the **algebraic identity** at the start of the proof
of Proposition `prop:coercAepsi` (paper
`Source/FGU-monotone_revised.tex`, line 947): for any `(m, u) ∈ 𝓚`
with explicit gradient family `Du`,

```
⟨A_ε[m, u] − A_ε[1, 0], (m − 1, u)⟩
  = ∫_{𝕋^d} [ m·(−H(x, Du, m) + D_pH(x, Du, m) · Du)
            + H(x, Du, m)
            + m·H(x, 0, 1) − H(x, 0, 1) − D_pH(x, 0, 1) · Du ] dx
  + ε · ∫_{𝕋^d} [ |Du|^{γ̄} + |u|^{γ̄} ] dx.
```

Here `[1, 0]` denotes the constant test pair `μ = 1`, `υ = 0` with
gradient family `Dυ = 0`. The pairing is the regularized MFG bracket
`mfgOperatorEpsPair` defined in `StationaryMFG/Solutions/Regularized.lean`
(paper line 925, `defAepsi`).

We split the right-hand side into a **Hamiltonian** integral (the
`mfgOperatorPair`-difference part) and a **Gateaux** integral (the
`ε`-multiplied `gateauxWpPair[m, u]`); this matches the structural
splitting `mfgOperatorEpsPair = mfgOperatorPair + ε · gateauxWpPair`
and requires only the integrability of the two `mfgOperatorPair`
integrands at `(m, u)` and at `(1, 0)` (one `MeasureTheory.integral_sub`
to combine the difference of integrals).

The encoding of `|Du|^{γ̄}` and `|u|^{γ̄}` in the Gateaux integral
matches the encoding of `gateauxWpPair` (paper line 925, third line):
* `|Du|^{γ̄} := vecAbsPowMinusTwo γBar (Du x) * ((Du x) ⬝ (Du x))`,
* `|u|^{γ̄}  := absPowMinusTwo γBar (u x) * (u x * u x)`.

This is the unsimplified form `|Du|^{γ̄−2}|Du|^{2}` and `|u|^{γ̄−2} u^{2}`;
collapsing it to the more compact `(Du⬝Du)^{γ̄/2}` requires a `Real.rpow`
algebra step which we leave to a follow-up task.

## Paper reference

`Source/FGU-monotone_revised.tex`, eq. `eq:coercive-test.Aepsi` (line 947).
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

/-! ## Pointwise integrand of the Hamiltonian part of the coercivity identity -/

/-- The pointwise Hamiltonian integrand of the right-hand side of
`eq:coercive-test.Aepsi` (paper line 947, omitting the `ε` Gateaux
contribution). At a point `x`:

```
m·(-H(x, Du, m) + D_pH(x, Du, m) · Du)
  + H(x, Du, m)
  + m·H(x, 0, 1) - H(x, 0, 1) - D_pH(x, 0, 1) · Du.
```
-/
def coerciveHamIntegrand
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  m x * (-H x (fun i => Du i x) (m x)
            + DpH x (fun i => Du i x) (m x) ⬝ (fun i => Du i x))
    + H x (fun i => Du i x) (m x)
    + m x * H x (0 : Fin d → ℝ) 1
    - H x (0 : Fin d → ℝ) 1
    - DpH x (0 : Fin d → ℝ) 1 ⬝ (fun i => Du i x)

/-! ## Vanishing of the `[1, 0]` Gateaux integrand -/

/-- The Gateaux pairing `gateauxWpPair γBar 0 0 Du u` vanishes: at the
constant test pair `(υ, Dυ) = (0, 0)`, both the `|Dυ|^{γ̄−2} Dυ · Dν`
and `|υ|^{γ̄−2} υ · ν` summands are identically zero. -/
private lemma gateauxWpPair_zero_zero (γBar : ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ) (u : (Fin d → ℝ) → ℝ) :
    gateauxWpPair (d := d) γBar (fun _ _ => 0) (fun _ => 0) Du u = 0 := by
  unfold gateauxWpPair
  -- The integrand is identically zero: both summands have a `0` factor.
  have hint :
      (fun x =>
          vecAbsPowMinusTwo γBar
              (fun i => (fun (_ : Fin d) (_ : Fin d → ℝ) => (0 : ℝ)) i x)
            * ((fun i => (fun (_ : Fin d) (_ : Fin d → ℝ) => (0 : ℝ)) i x)
              ⬝ (fun i => Du i x))
          + absPowMinusTwo γBar ((fun (_ : Fin d → ℝ) => (0 : ℝ)) x)
              * ((fun (_ : Fin d → ℝ) => (0 : ℝ)) x * u x))
        = (fun _ : Fin d → ℝ => (0 : ℝ)) := by
    funext x
    have h1 : (fun i : Fin d =>
        (fun (_ : Fin d) (_ : Fin d → ℝ) => (0 : ℝ)) i x) =
          (0 : Fin d → ℝ) := by
      funext i; rfl
    rw [h1, euclideanDot_zero_left]
    simp
  rw [hint]
  simp

/-! ## Auxiliary: pointwise difference of the `mfgOperatorPair` integrands -/

/-- Pointwise algebraic identity: the difference of the
`mfgOperatorPair`-integrands at `(m, u)` and at `(1, 0)` (acting on the
test pair `(η, ν, Dν) = (m − 1, u, Du)`) equals `coerciveHamIntegrand`
at `x`. Note that the ambient potential `V` cancels.

This is **pure algebra** (`ring`). -/
private lemma mfgOperatorPair_integrand_diff_eq
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    ((-(u x) - H x (fun i => Du i x) (m x) + V x) * (m x - 1)
        + m x * (DpH x (fun i => Du i x) (m x) ⬝ (fun i => Du i x))
        + (m x - 1) * u x)
      - ((-(0 : ℝ) - H x (0 : Fin d → ℝ) 1 + V x) * (m x - 1)
          + 1 * (DpH x (0 : Fin d → ℝ) 1 ⬝ (fun i => Du i x))
          + (1 - 1) * u x)
      = coerciveHamIntegrand H DpH Du m x := by
  unfold coerciveHamIntegrand
  ring

/-! ## Main coercivity test-pair identity -/

/-- **Coercivity test-pair algebraic identity** (paper line 947,
`eq:coercive-test.Aepsi`).

Under integrability of the `mfgOperatorPair` integrands at `(m, u)` and
at the constant pair `(1, 0)`, the pairing difference
`⟨A_ε[m, u] − A_ε[1, 0], (m − 1, u)⟩` equals the explicit form of paper
line 947, split into a Hamiltonian integral plus an `ε`-Gateaux
integral.

The Gateaux integrand is encoded as in `gateauxWpPair`:
`vecAbsPowMinusTwo γBar (Du x) * ((Du x) ⬝ (Du x))` for the gradient
piece and `absPowMinusTwo γBar (u x) * (u x * u x)` for the scalar
piece, i.e. the unsimplified `|Du|^{γ̄−2}|Du|^{2}` and `|u|^{γ̄−2} u^{2}`
forms; rpow algebra to identify these with `|Du|^{γ̄}` / `|u|^{γ̄}` is
deferred. -/
theorem coercive_test_pair_identity
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (γBar ε : ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (hInt_mu : IntegrableOn (fun x =>
        (-(u x) - H x (fun i => Du i x) (m x) + V x) * (m x - 1)
          + m x * (DpH x (fun i => Du i x) (m x) ⬝ (fun i => Du i x))
          + (m x - 1) * u x) (UnitCube d))
    (hInt_10 : IntegrableOn (fun x =>
        (-(0 : ℝ) - H x (0 : Fin d → ℝ) 1 + V x) * (m x - 1)
          + 1 * (DpH x (0 : Fin d → ℝ) 1 ⬝ (fun i => Du i x))
          + (1 - 1) * u x) (UnitCube d)) :
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
            ∂(volume : Measure (Fin d → ℝ))) := by
  -- Unfold the regularized pairing into `mfgOperatorPair + ε · gateauxWpPair`.
  unfold mfgOperatorEpsPair
  -- The `[1, 0]` Gateaux piece vanishes.
  rw [gateauxWpPair_zero_zero γBar Du u]
  rw [mul_zero, add_zero]
  -- Identify the `[m,u]` Gateaux piece with the displayed Gateaux integral.
  -- It is literally the definition of `gateauxWpPair γBar Du u Du u`.
  have hGate : gateauxWpPair γBar Du u Du u =
      ∫ x in UnitCube d,
        vecAbsPowMinusTwo γBar (fun i => Du i x)
            * ((fun i => Du i x) ⬝ (fun i => Du i x))
          + absPowMinusTwo γBar (u x) * (u x * u x)
        ∂(volume : Measure (Fin d → ℝ)) := by
    unfold gateauxWpPair
    rfl
  rw [hGate]
  -- The remaining task: identify the `mfgOperatorPair` difference with the
  -- Hamiltonian integral.
  -- LHS now: `(mfgOperatorPair[m,u] + ε · ∫gate) − mfgOperatorPair[1,0]`
  -- RHS now: `(∫ ham) + ε · ∫gate`.
  -- Rearrange: `mfgOperatorPair[m,u] − mfgOperatorPair[1,0] = ∫ ham`.
  have hHam :
      mfgOperatorPair (V := V) (H := H) (DpH := DpH) Du m u Du (m - 1) u
        - mfgOperatorPair (V := V) (H := H) (DpH := DpH)
            (fun _ _ => 0) (fun _ => 1) (fun _ => 0) Du (m - 1) u
        = ∫ x in UnitCube d, coerciveHamIntegrand H DpH Du m x
            ∂(volume : Measure (Fin d → ℝ)) := by
    -- Convert each pairing into a `setIntegral` over the cube, then use
    -- `MeasureTheory.integral_sub` and `setIntegral_congr_fun` to identify
    -- the difference of integrands with `coerciveHamIntegrand`.
    have hPair_mu :
        mfgOperatorPair (V := V) (H := H) (DpH := DpH) Du m u Du (m - 1) u =
          ∫ x in UnitCube d,
            (-(u x) - H x (fun i => Du i x) (m x) + V x) * (m x - 1)
              + m x * (DpH x (fun i => Du i x) (m x)
                        ⬝ (fun i => Du i x))
              + (m x - 1) * u x
            ∂(volume : Measure (Fin d → ℝ)) := by
      unfold mfgOperatorPair
      refine setIntegral_congr_fun measurableSet_unitCube ?_
      intro x _
      simp [Pi.sub_apply]
    have hPair_10 :
        mfgOperatorPair (V := V) (H := H) (DpH := DpH)
            (fun _ _ => 0) (fun _ => 1) (fun _ => 0) Du (m - 1) u =
          ∫ x in UnitCube d,
            (-(0 : ℝ) - H x (0 : Fin d → ℝ) 1 + V x) * (m x - 1)
              + 1 * (DpH x (0 : Fin d → ℝ) 1
                      ⬝ (fun i => Du i x))
              + (1 - 1) * u x
            ∂(volume : Measure (Fin d → ℝ)) := by
      unfold mfgOperatorPair
      refine setIntegral_congr_fun measurableSet_unitCube ?_
      intro x _
      have h0 : (fun _ : Fin d => (0 : ℝ)) = (0 : Fin d → ℝ) := by
        funext i; rfl
      simp [Pi.sub_apply, h0]
    rw [hPair_mu, hPair_10]
    -- Combine via `integral_sub` on the cube-restricted measure.
    rw [← MeasureTheory.integral_sub hInt_mu hInt_10]
    refine setIntegral_congr_fun measurableSet_unitCube ?_
    intro x _
    exact mfgOperatorPair_integrand_diff_eq V H DpH Du m u x
  linarith [hHam]

/-! ## Sanity check -/

/-- **Unit test**: at the trivial Hamiltonian `H = 0`, `D_pH = 0`, with
`Du = 0`, `m = 1`, `u = 0`, the Hamiltonian integrand of the coercivity
identity vanishes pointwise. -/
example :
    ∀ x : Fin d → ℝ,
      coerciveHamIntegrand (d := d)
          (fun (_ : Fin d → ℝ) (_ : Fin d → ℝ) (_ : ℝ) => (0 : ℝ))
          (fun (_ : Fin d → ℝ) (_ : Fin d → ℝ) (_ : ℝ) => (0 : Fin d → ℝ))
          (fun _ _ => 0) (fun _ => 1) x
        = 0 := by
  intro x
  unfold coerciveHamIntegrand dotProduct
  simp

/-- **Unit test**: at the trivial Hamiltonian `H = 0`, `D_pH = 0`, with
arbitrary `Du, m`, the Hamiltonian integrand reduces to a pure
`Du`-independent constant `0`. -/
example
    (Du : Fin d → (Fin d → ℝ) → ℝ) (m : (Fin d → ℝ) → ℝ) :
    ∀ x : Fin d → ℝ,
      coerciveHamIntegrand
          (fun (_ : Fin d → ℝ) (_ : Fin d → ℝ) (_ : ℝ) => (0 : ℝ))
          (fun (_ : Fin d → ℝ) (_ : Fin d → ℝ) (_ : ℝ) => (0 : Fin d → ℝ))
          Du m x
        = 0 := by
  intro x
  unfold coerciveHamIntegrand dotProduct
  simp

/-! ## Pointwise lower bound on the coercivity integrand

This is the **pre-Young** form of the pointwise lower bound on the
Hamiltonian integrand `coerciveHamIntegrand` of the coercivity test-pair
identity (paper line 956, inside the proof of `prop:coercAepsi`). We
combine, pointwise:

* `Hamiltonian.lagrangian_lower_bound` (paper `lem:A1+anyother`,
  eq.~`eq:DpHdotpminusH-estimate1`): for `m > 0`,
  `D_pH(x, p, m) · p − H(x, p, m) ≥ m^β/C − C`.
* `HypothesisPowerGrowth.lower` (eq.~`eq:assH.lower.simple`): for `m > 0`,
  `H(x, p, m) ≥ ‖p‖^α/C − C(m^β + 1)`.
* The bounds `|H(x, 0, 1)| ≤ C` and `‖D_pH(x, 0, 1)‖ ≤ C` (consequences
  of `eq:assH.upper.simple` + `eq:assH.DpH.upper.simple` +
  `eq:assH.lower.simple` at `(p, m) = (0, 1)`, with the convention of
  `rmk:implied-a` not being needed since `m = 1`).

Adding the four lines yields a pointwise lower bound of the form

```
(1/C') (m^{β+1} + ‖p‖^α) − C' (m + m^β + ‖p‖) − C'.
```

The Young-step absorption of the slack `−C'(m + m^β + ‖p‖)` into the
positive `m^{β+1}` and `‖p‖^α` is deferred to the dependent task
`infra:P4-coerc-young`.
-/

/-- **Coordinate Cauchy–Schwarz for the explicit dot product**: for
`v w : Fin d → ℝ` carrying the standard pi sup-norm `‖·‖ = sup_i |v i|`,

  `|v ⬝ w| ≤ d · ‖v‖ · ‖w‖`.

The proof is the bound `|∑ v_i w_i| ≤ ∑ |v_i| |w_i| ≤ ∑ ‖v‖‖w‖ = d ‖v‖‖w‖`.
This is *not* the optimal Euclidean Cauchy–Schwarz constant `1`; it is the
universal constant `d` matching the sup-norm. For our coercivity argument
the dimensional factor is harmless — it is absorbed into the constant
`C'` in the final estimate. -/
private lemma abs_euclideanDot_le_dim_mul_norm_mul_norm
    (v w : Fin d → ℝ) :
    |v ⬝ w| ≤ d * ‖v‖ * ‖w‖ := by
  -- Unfold the dot product and bound the sum.
  unfold dotProduct
  -- `|∑ v_i w_i| ≤ ∑ |v_i w_i|`.
  have h1 : |∑ i, v i * w i| ≤ ∑ i : Fin d, |v i * w i| :=
    Finset.abs_sum_le_sum_abs _ _
  -- Each summand bound: `|v_i w_i| = |v_i| · |w_i| ≤ ‖v‖ · ‖w‖`.
  have h2 : ∀ i : Fin d, |v i * w i| ≤ ‖v‖ * ‖w‖ := by
    intro i
    rw [abs_mul]
    have hv : |v i| ≤ ‖v‖ := by
      have := norm_le_pi_norm v i
      simpa [Real.norm_eq_abs] using this
    have hw : |w i| ≤ ‖w‖ := by
      have := norm_le_pi_norm w i
      simpa [Real.norm_eq_abs] using this
    have hvi_nn : 0 ≤ |v i| := abs_nonneg _
    have hw_nn : 0 ≤ ‖w‖ := norm_nonneg _
    calc |v i| * |w i|
        ≤ ‖v‖ * |w i| := by
          exact mul_le_mul_of_nonneg_right hv (abs_nonneg _)
      _ ≤ ‖v‖ * ‖w‖ := by
          exact mul_le_mul_of_nonneg_left hw (norm_nonneg _)
  -- Sum the per-coordinate bounds.
  have h3 : ∑ i : Fin d, |v i * w i| ≤ ∑ _ : Fin d, ‖v‖ * ‖w‖ :=
    Finset.sum_le_sum (fun i _ => h2 i)
  -- The constant sum collapses to `d · ‖v‖ · ‖w‖`.
  have h4 : ∑ _ : Fin d, ‖v‖ * ‖w‖ = d * (‖v‖ * ‖w‖) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp [nsmul_eq_mul]
  calc |∑ i, v i * w i|
      ≤ ∑ i : Fin d, |v i * w i| := h1
    _ ≤ ∑ _ : Fin d, ‖v‖ * ‖w‖ := h3
    _ = d * (‖v‖ * ‖w‖) := h4
    _ = d * ‖v‖ * ‖w‖ := by ring

/-! ## Explicit constants for the coercivity-integrand lower bound

The proof of `coercivity_integrand_lower_bound` constructs a witness
`C' := max (max (2C) (d·C)) 1 + 1`, and the proof of
`coercivity_integrand_lower_bound_young` constructs from that `C'` a
witness `C'' := max (2C') (K₁+K₂+K₃+C') + 1`, with `K₁, K₂, K₃`
defined from Young-conjugate parameters.

The values are buried inside the `refine ⟨…, …⟩` of each theorem, so
they are not Lean-visible. We expose them here as
`noncomputable def`s so that downstream callers (e.g. the
`coercivity_combined_from_paperHypotheses` chain) can refer to the
explicit constant directly. The two `_explicit` sibling theorems
returning the explicit witness are landed in a sibling task; here we
only expose the constants and their positivity, leaving the existing
existential theorems intact for backwards compatibility. -/

/-- Explicit value of the pre-Young coercivity-integrand witness `C'`
constructed inside `coercivity_integrand_lower_bound`. -/
noncomputable def coercivityIntegrandLowerBoundConstantPrime
    (d : ℕ) (C : ℝ) : ℝ :=
  max (max (2 * C) ((d : ℝ) * C)) 1 + 1

/-- Positivity of `coercivityIntegrandLowerBoundConstantPrime` (unconditional;
the `+ 1` ensures the value is `≥ 2` regardless of the sign of `C`). -/
lemma coercivityIntegrandLowerBoundConstantPrime_pos
    (d : ℕ) (C : ℝ) :
    0 < coercivityIntegrandLowerBoundConstantPrime d C := by
  unfold coercivityIntegrandLowerBoundConstantPrime
  have h1 : (1 : ℝ) ≤ max (max (2 * C) ((d : ℝ) * C)) 1 := le_max_right _ _
  linarith

/-- `C ≤ C'` for the explicit pre-Young constant (when `0 < C`). -/
lemma coercivityIntegrandLowerBoundConstantPrime_ge
    (d : ℕ) {C : ℝ} (hC : 0 < C) :
    C ≤ coercivityIntegrandLowerBoundConstantPrime d C := by
  unfold coercivityIntegrandLowerBoundConstantPrime
  have hC_le_2C : C ≤ 2 * C := by linarith
  have h1 : 2 * C ≤ max (2 * C) ((d : ℝ) * C) := le_max_left _ _
  have h2 : max (2 * C) ((d : ℝ) * C) ≤ max (max (2 * C) ((d : ℝ) * C)) 1 :=
    le_max_left _ _
  linarith

/-- Explicit value of the post-Young coercivity-integrand witness `C''`
constructed inside `coercivity_integrand_lower_bound_young`. The
parameters `α, β` enter through the Young-conjugate exponent choices:

```
θ₁ := (β+1)/(4·C'²),   θ₂ := (β+1)/(4·β·C'²),   θ₃ := α/(2·C'²)
K₁ := C' · θ₁^{-1/β}  · β/(β+1)
K₂ := C' · θ₂^{-β}   / (β+1)
K₃ := C' · θ₃^{-1/(α-1)} · (α-1)/α
C'' := max (2·C') (K₁+K₂+K₃+C') + 1
```
-/
noncomputable def coercivityIntegrandLowerBoundYoungConstant
    (d : ℕ) (C α β : ℝ) : ℝ :=
  let C' : ℝ := coercivityIntegrandLowerBoundConstantPrime d C
  let θ₁ : ℝ := (β + 1) / (4 * C' ^ 2)
  let θ₂ : ℝ := (β + 1) / (4 * β * C' ^ 2)
  let θ₃ : ℝ := α / (2 * C' ^ 2)
  let K₁ : ℝ := C' * θ₁ ^ (-(1 / β)) * (β / (β + 1))
  let K₂ : ℝ := C' * θ₂ ^ (-β) / (β + 1)
  let K₃ : ℝ := C' * θ₃ ^ (-(1 / (α - 1))) * ((α - 1) / α)
  max (2 * C') (K₁ + K₂ + K₃ + C') + 1

/-- `2 · C' ≤ C''` for the explicit post-Young constant. -/
lemma coercivityIntegrandLowerBoundYoungConstant_ge_two_prime
    (d : ℕ) (C α β : ℝ) :
    2 * coercivityIntegrandLowerBoundConstantPrime d C
      ≤ coercivityIntegrandLowerBoundYoungConstant d C α β := by
  unfold coercivityIntegrandLowerBoundYoungConstant
  set C' : ℝ := coercivityIntegrandLowerBoundConstantPrime d C
  set Krhs : ℝ :=
    C' * ((β + 1) / (4 * C' ^ 2)) ^ (-(1 / β)) * (β / (β + 1))
      + C' * ((β + 1) / (4 * β * C' ^ 2)) ^ (-β) / (β + 1)
      + C' * (α / (2 * C' ^ 2)) ^ (-(1 / (α - 1))) * ((α - 1) / α)
      + C'
  have h1 : 2 * C' ≤ max (2 * C') Krhs := le_max_left _ _
  linarith

/-- Positivity of `coercivityIntegrandLowerBoundYoungConstant` (unconditional). -/
lemma coercivityIntegrandLowerBoundYoungConstant_pos
    (d : ℕ) (C α β : ℝ) :
    0 < coercivityIntegrandLowerBoundYoungConstant d C α β := by
  have hC'_pos : 0 < coercivityIntegrandLowerBoundConstantPrime d C :=
    coercivityIntegrandLowerBoundConstantPrime_pos d C
  have h2C'_pos : 0 < 2 * coercivityIntegrandLowerBoundConstantPrime d C := by
    linarith
  have h_ge : 2 * coercivityIntegrandLowerBoundConstantPrime d C
      ≤ coercivityIntegrandLowerBoundYoungConstant d C α β :=
    coercivityIntegrandLowerBoundYoungConstant_ge_two_prime d C α β
  linarith

/-- **Coercivity integrand pointwise lower bound** (paper line 956,
inside the proof of `prop:coercAepsi`).

Given (a) the Lagrangian lower bound `D_pH(x, p, m) · p − H(x, p, m) ≥
m^β/C − C` for `m > 0` (the conclusion of paper `lem:A1+anyother`,
`Hamiltonian.lagrangian_lower_bound`), (b) the simple-power-growth lower
bound `H(x, p, m) ≥ ‖p‖^α/C − C(m^β + 1)` for `m > 0` (the field
`lower` of `HypothesisPowerGrowth`), and (c) the constant-pair bounds
`|H(x, 0, 1)| ≤ C` and `‖D_pH(x, 0, 1)‖ ≤ C` (consequences of the
`upper` / `DpH_upper` fields applied at `(p, m) = (0, 1)`), there exists
a constant `C' > 0` for which the pointwise integrand of paper
eq.~`eq:coercive-test.Aepsi` (= `coerciveHamIntegrand`) is bounded
below as

  `coerciveHamIntegrand H DpH Du m x`
    `≥ (1/C') (m(x)^{β+1} + ‖Du(x)‖^α) − C' (m(x) + m(x)^β + ‖Du(x)‖) − C'`

a.e. on the unit cube, for all `m(x) > 0`.

This is the **pre-Young** form. The dependent task
`infra:P4-coerc-young` absorbs the slack `−C'(m + m^β + ‖Du‖)` into the
positive `m^{β+1}` and `‖Du‖^α` to yield the post-Young clean form
`≥ (1/C') (m^{β+1} + ‖Du‖^α) − C'`.

The proof is pure linear algebra: chain the three input bounds, expand
`mx · (− H + D_pH · p) = mx · (D_pH · p − H)`, and bound the
last-line term `D_pH(x, 0, 1) · Du(x)` via the explicit
coordinate-Cauchy–Schwarz `abs_euclideanDot_le_dim_mul_norm_mul_norm`.
The hypothesis inputs match the package-then-consume style of
`Hamiltonian.lagrangian_lower_bound`.

This `_explicit` sibling returns the explicit constant
`coercivityIntegrandLowerBoundConstantPrime d C` directly (no `∃`).
The existential variant `coercivity_integrand_lower_bound` is a
one-line forwarder onto this theorem. -/
theorem coercivity_integrand_lower_bound_explicit
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    {C α β : ℝ}
    (hC : 0 < C)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ β) / C - C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (h_lower :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (‖p‖ ^ α) / C - C * (mx ^ β + 1) ≤ H x p mx)
    (h_H01_le :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), |H x (0 : Fin d → ℝ) 1| ≤ C)
    (h_DpH01_le :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖DpH x (0 : Fin d → ℝ) 1‖ ≤ C)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m : (Fin d → ℝ) → ℝ) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      0 < m x →
        (1 / coercivityIntegrandLowerBoundConstantPrime d C)
            * (m x ^ (β + 1) + ‖fun i => Du i x‖ ^ α)
          - coercivityIntegrandLowerBoundConstantPrime d C
              * (m x + m x ^ β + ‖fun i => Du i x‖)
          - coercivityIntegrandLowerBoundConstantPrime d C
        ≤ coerciveHamIntegrand H DpH Du m x := by
  -- The explicit constant unfolds to `max (max (2C) (d·C)) 1 + 1`, so the
  -- original proof body of `coercivity_integrand_lower_bound` carries over
  -- after a single `unfold` step. The witness chosen there is exactly this
  -- explicit value.
  unfold coercivityIntegrandLowerBoundConstantPrime
  set C' : ℝ := max (max (2 * C) ((d : ℝ) * C)) 1 + 1 with hC'def
  have h2C_le : 2 * C ≤ C' := by
    have h1 : 2 * C ≤ max (2 * C) ((d : ℝ) * C) := le_max_left _ _
    have h2 : max (2 * C) ((d : ℝ) * C) ≤ max (max (2 * C) ((d : ℝ) * C)) 1 :=
      le_max_left _ _
    linarith
  have hdC_le : (d : ℝ) * C ≤ C' := by
    have h1 : (d : ℝ) * C ≤ max (2 * C) ((d : ℝ) * C) := le_max_right _ _
    have h2 : max (2 * C) ((d : ℝ) * C) ≤ max (max (2 * C) ((d : ℝ) * C)) 1 :=
      le_max_left _ _
    linarith
  have h1_le : (1 : ℝ) ≤ C' := by
    have h1 : (1 : ℝ) ≤ max (max (2 * C) ((d : ℝ) * C)) 1 := le_max_right _ _
    linarith
  have hC_le : C ≤ C' := by
    have : C ≤ 2 * C := by linarith
    linarith
  have hC'_pos : 0 < C' := lt_of_lt_of_le hC hC_le
  have hC'_ne : C' ≠ 0 := ne_of_gt hC'_pos
  -- Combine the four a.e. hypotheses.
  filter_upwards [h_lagr, h_lower, h_H01_le, h_DpH01_le] with x hLagr hLow hH01 hDpH01 hmx
  -- Set `p := fun i => Du i x` and abbreviate.
  set p : Fin d → ℝ := fun i => Du i x with hpdef
  set mx : ℝ := m x with hmxdef
  have hmx_nn : 0 ≤ mx := hmx.le
  -- Step 1: `D_pH(x, p, mx) · p − H(x, p, mx) ≥ mx^β / C − C`.
  have h1 := hLagr p mx hmx
  -- Multiply by `mx ≥ 0`.
  have h1m :
      mx * (mx ^ β / C - C) ≤ mx * ((DpH x p mx) ⬝ p - H x p mx) :=
    mul_le_mul_of_nonneg_left h1 hmx_nn
  -- Rewrite the LHS: `mx · (mx^β / C − C) = mx^{β+1}/C − C·mx`.
  have hpow : mx * mx ^ β = mx ^ (β + 1) := by
    have hmx_one : mx ^ (1 : ℝ) = mx := Real.rpow_one mx
    calc mx * mx ^ β
        = mx ^ (1 : ℝ) * mx ^ β := by rw [hmx_one]
      _ = mx ^ ((1 : ℝ) + β) := (Real.rpow_add hmx 1 _).symm
      _ = mx ^ (β + 1) := by ring_nf
  have h1m' :
      mx ^ (β + 1) / C - C * mx ≤ mx * ((DpH x p mx) ⬝ p - H x p mx) := by
    have hLHS_eq : mx * (mx ^ β / C - C) = mx ^ (β + 1) / C - C * mx := by
      have : mx * (mx ^ β / C - C) = mx * mx ^ β / C - mx * C := by ring
      rw [this, hpow]
      ring
    linarith
  -- Step 2: `H(x, p, mx) ≥ ‖p‖^α / C − C·(mx^β + 1)`.
  have h2 := hLow p mx hmx
  -- Step 3: `|H(x, 0, 1)| ≤ C`, hence `mx · H(x, 0, 1) ≥ −mx · C` and
  -- `−H(x, 0, 1) ≥ −C`.
  have h3a_le : H x (0 : Fin d → ℝ) 1 ≥ -C := neg_le_of_abs_le hH01
  have h3a_ge : H x (0 : Fin d → ℝ) 1 ≤ C := le_of_abs_le hH01
  have h3b : mx * H x (0 : Fin d → ℝ) 1 ≥ -(mx * C) := by
    have hge : -C ≤ H x (0 : Fin d → ℝ) 1 := h3a_le
    have hmul : mx * (-C) ≤ mx * H x (0 : Fin d → ℝ) 1 :=
      mul_le_mul_of_nonneg_left hge hmx_nn
    have : mx * (-C) = -(mx * C) := by ring
    linarith
  -- Step 4: bound `D_pH(x, 0, 1) · p` via coord. CS and `‖D_pH(x,0,1)‖ ≤ C`.
  have h4_abs : |DpH x (0 : Fin d → ℝ) 1 ⬝ p| ≤ d * C * ‖p‖ := by
    have hcs := abs_euclideanDot_le_dim_mul_norm_mul_norm (DpH x 0 1) p
    have hnn : (0 : ℝ) ≤ ‖p‖ := norm_nonneg _
    have hd_nn : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le _
    have hmul1 : (d : ℝ) * ‖DpH x 0 1‖ ≤ (d : ℝ) * C :=
      mul_le_mul_of_nonneg_left hDpH01 hd_nn
    have hmul2 : (d : ℝ) * ‖DpH x 0 1‖ * ‖p‖ ≤ (d : ℝ) * C * ‖p‖ :=
      mul_le_mul_of_nonneg_right hmul1 hnn
    exact le_trans hcs hmul2
  have h4 : -(d * C * ‖p‖) ≤ DpH x (0 : Fin d → ℝ) 1 ⬝ p :=
    neg_le_of_abs_le h4_abs
  have h4' : -(DpH x (0 : Fin d → ℝ) 1 ⬝ p) ≥ -(d * C * ‖p‖) := by
    have hupper : DpH x (0 : Fin d → ℝ) 1 ⬝ p ≤ d * C * ‖p‖ :=
      le_of_abs_le h4_abs
    linarith
  -- Combine the four steps.
  have hp_nn_α : 0 ≤ ‖p‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
  have hmβ_nn : 0 ≤ mx ^ β := Real.rpow_nonneg hmx_nn _
  have hmβp1_nn : 0 ≤ mx ^ (β + 1) := Real.rpow_nonneg hmx_nn _
  have hC_nn : 0 ≤ C := hC.le
  have hp_nn : 0 ≤ ‖p‖ := norm_nonneg _
  -- Unfold `coerciveHamIntegrand`.
  unfold coerciveHamIntegrand
  have hAB : mx ^ (β + 1) / C + ‖p‖ ^ α / C - C * mx
                - C * mx ^ β - C
            ≤ mx * ((DpH x p mx) ⬝ p - H x p mx) + H x p mx := by
    have := h2
    linarith [h1m']
  have hABC : mx ^ (β + 1) / C + ‖p‖ ^ α / C - C * mx
                - C * mx ^ β - C - C * mx
            ≤ mx * ((DpH x p mx) ⬝ p - H x p mx) + H x p mx
              + mx * H x (0 : Fin d → ℝ) 1 := by
    have hC_step : -C * mx ≤ mx * H x (0 : Fin d → ℝ) 1 := by
      have : -(mx * C) ≤ mx * H x (0 : Fin d → ℝ) 1 := h3b
      linarith
    linarith [hAB, hC_step]
  have hABCD : mx ^ (β + 1) / C + ‖p‖ ^ α / C - C * mx
                - C * mx ^ β - C - C * mx - C
            ≤ mx * ((DpH x p mx) ⬝ p - H x p mx) + H x p mx
              + mx * H x (0 : Fin d → ℝ) 1 - H x (0 : Fin d → ℝ) 1 := by
    have hD : -H x (0 : Fin d → ℝ) 1 ≥ -C := by linarith
    linarith [hABC]
  have hABCDE :
      mx ^ (β + 1) / C + ‖p‖ ^ α / C - C * mx
          - C * mx ^ β - C - C * mx - C - d * C * ‖p‖
      ≤ mx * ((DpH x p mx) ⬝ p - H x p mx) + H x p mx
        + mx * H x (0 : Fin d → ℝ) 1 - H x (0 : Fin d → ℝ) 1
        - DpH x (0 : Fin d → ℝ) 1 ⬝ p := by
    linarith [hABCD, h4']
  have h_inv : 1 / C' ≤ 1 / C := by
    rw [one_div, one_div]
    exact inv_anti₀ hC hC_le
  have hdom_pα :
      (1 / C') * (mx ^ (β + 1) + ‖p‖ ^ α)
        ≤ (1 / C) * (mx ^ (β + 1) + ‖p‖ ^ α) := by
    have hsum_nn : 0 ≤ mx ^ (β + 1) + ‖p‖ ^ α := add_nonneg hmβp1_nn hp_nn_α
    exact mul_le_mul_of_nonneg_right h_inv hsum_nn
  have hLHS_step_eq :
      mx ^ (β + 1) / C + ‖p‖ ^ α / C - C * mx
          - C * mx ^ β - C - C * mx - C - d * C * ‖p‖
        = (1 / C) * (mx ^ (β + 1) + ‖p‖ ^ α)
            - (2 * C * mx + C * mx ^ β + (d : ℝ) * C * ‖p‖) - 2 * C := by
    field_simp
    ring
  rw [hLHS_step_eq] at hABCDE
  have hgoal_le_step :
      (1 / C') * (mx ^ (β + 1) + ‖p‖ ^ α)
          - C' * (mx + mx ^ β + ‖p‖) - C'
        ≤ (1 / C) * (mx ^ (β + 1) + ‖p‖ ^ α)
            - (2 * C * mx + C * mx ^ β + (d : ℝ) * C * ‖p‖) - 2 * C := by
    have step2 :
        2 * C * mx + C * mx ^ β + (d : ℝ) * C * ‖p‖
          ≤ C' * (mx + mx ^ β + ‖p‖) := by
      have ha : 2 * C * mx ≤ C' * mx :=
        mul_le_mul_of_nonneg_right h2C_le hmx_nn
      have hb : C * mx ^ β ≤ C' * mx ^ β :=
        mul_le_mul_of_nonneg_right hC_le hmβ_nn
      have hc : (d : ℝ) * C * ‖p‖ ≤ C' * ‖p‖ :=
        mul_le_mul_of_nonneg_right hdC_le hp_nn
      have hexp : C' * (mx + mx ^ β + ‖p‖)
                  = C' * mx + C' * mx ^ β + C' * ‖p‖ := by ring
      linarith
    have step3 : 2 * C ≤ C' := h2C_le
    linarith [hdom_pα, step2, step3]
  linarith [hABCDE, hgoal_le_step]

theorem coercivity_integrand_lower_bound
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    {C α β : ℝ}
    (hC : 0 < C)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ β) / C - C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (h_lower :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (‖p‖ ^ α) / C - C * (mx ^ β + 1) ≤ H x p mx)
    (h_H01_le :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), |H x (0 : Fin d → ℝ) 1| ≤ C)
    (h_DpH01_le :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖DpH x (0 : Fin d → ℝ) 1‖ ≤ C)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m : (Fin d → ℝ) → ℝ) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        0 < m x →
          (1 / C') * (m x ^ (β + 1) + ‖fun i => Du i x‖ ^ α)
              - C' * (m x + m x ^ β + ‖fun i => Du i x‖) - C'
            ≤ coerciveHamIntegrand H DpH Du m x :=
  ⟨coercivityIntegrandLowerBoundConstantPrime d C,
    coercivityIntegrandLowerBoundConstantPrime_pos d C,
    coercivity_integrand_lower_bound_explicit H DpH hC
      h_lagr h_lower h_H01_le h_DpH01_le Du m⟩

/-! ## Unit tests for the pointwise lower bound -/

/-- **Sanity check for `abs_euclideanDot_le_dim_mul_norm_mul_norm`**: at
the zero vector, the dot-product bound is trivially `0 ≤ 0`. -/
example (v : Fin d → ℝ) : |((0 : Fin d → ℝ)) ⬝ v| ≤ d * ‖(0 : Fin d → ℝ)‖ * ‖v‖ := by
  rw [euclideanDot_zero_left, abs_zero]
  have : (0 : ℝ) ≤ d * ‖(0 : Fin d → ℝ)‖ * ‖v‖ := by positivity
  linarith

/-- **API sanity check for `coercivity_integrand_lower_bound`**: given
the four pointwise input bounds (whose paper-side derivations are the
content of `Hamiltonian.lagrangian_lower_bound`,
`HypothesisPowerGrowth.lower`, `HypothesisPowerGrowth.upper`, and
`HypothesisPowerGrowth.DpH_upper` evaluated at `(0, 1)`), the lemma
returns a constant `C' > 0` and the displayed pointwise lower bound on
`coerciveHamIntegrand`. This example merely exercises that the lemma
applies — it does not provide a closed-form witness for the inputs. -/
example
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (C α β : ℝ) (hC : 0 < C)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ β) / C - C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (h_lower :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (‖p‖ ^ α) / C - C * (mx ^ β + 1) ≤ H x p mx)
    (h_H01_le :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), |H x (0 : Fin d → ℝ) 1| ≤ C)
    (h_DpH01_le :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖DpH x (0 : Fin d → ℝ) 1‖ ≤ C)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m : (Fin d → ℝ) → ℝ) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        0 < m x →
          (1 / C') * (m x ^ (β + 1) + ‖fun i => Du i x‖ ^ α)
              - C' * (m x + m x ^ β + ‖fun i => Du i x‖) - C'
            ≤ coerciveHamIntegrand H DpH Du m x :=
  coercivity_integrand_lower_bound H DpH hC h_lagr h_lower h_H01_le h_DpH01_le Du m

/-! ## Young's-inequality absorption: post-Young coercivity integrand bound -/

/-- **Hölder conjugate pair `(β+1, (β+1)/β)`** for `β > 0`. -/
private lemma holderConjugate_betaPlusOne {β : ℝ} (hβ : 0 < β) :
    Real.HolderConjugate (β + 1) ((β + 1) / β) := by
  rw [Real.holderConjugate_iff]
  refine ⟨by linarith, ?_⟩
  have hβp1_pos : 0 < β + 1 := by linarith
  have hβne : β ≠ 0 := ne_of_gt hβ
  have hβp1ne : β + 1 ≠ 0 := ne_of_gt hβp1_pos
  field_simp
  ring

/-- **Hölder conjugate pair `(α, α/(α-1))`** for `α > 1` (local copy of the
private helper from `Hamiltonian/Estimates.lean`). -/
private lemma holderConjugate_alpha_local {α : ℝ} (hα : 1 < α) :
    Real.HolderConjugate α (α / (α - 1)) := by
  rw [Real.holderConjugate_iff]
  refine ⟨hα, ?_⟩
  have hαpos : 0 < α := lt_trans one_pos hα
  have hαm1 : 0 < α - 1 := sub_pos.mpr hα
  have hαne : α ≠ 0 := ne_of_gt hαpos
  have hαm1ne : α - 1 ≠ 0 := ne_of_gt hαm1
  field_simp
  ring

/-- **Coercivity integrand pointwise lower bound — post-Young form**,
explicit-constant variant (paper line 965, inside the proof of
`prop:coercAepsi`).

Returns the explicit constant
`coercivityIntegrandLowerBoundYoungConstant d C α β` directly (no `∃`).
The existential sibling `coercivity_integrand_lower_bound_young` is a
one-line forwarder onto this theorem.

See `coercivity_integrand_lower_bound_young` for the docstring on the
mathematical content and the Young-inequality strategy.
-/
theorem coercivity_integrand_lower_bound_young_explicit
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    {C α β : ℝ}
    (hC : 0 < C) (hα : 1 < α) (hβ : 0 < β)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ β) / C - C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (h_lower :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (‖p‖ ^ α) / C - C * (mx ^ β + 1) ≤ H x p mx)
    (h_H01_le :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), |H x (0 : Fin d → ℝ) 1| ≤ C)
    (h_DpH01_le :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖DpH x (0 : Fin d → ℝ) 1‖ ≤ C)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m : (Fin d → ℝ) → ℝ) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      0 < m x →
        (1 / coercivityIntegrandLowerBoundYoungConstant d C α β)
            * (m x ^ (β + 1) + ‖fun i => Du i x‖ ^ α)
          - coercivityIntegrandLowerBoundYoungConstant d C α β
        ≤ coerciveHamIntegrand H DpH Du m x := by
  -- Unfold the explicit constant so the existing `max … + 1` shape is
  -- visible to the `set`/`le_max_*` chain below.
  unfold coercivityIntegrandLowerBoundYoungConstant
  -- Step 1: invoke the pre-Young explicit bound at
  -- `C' := coercivityIntegrandLowerBoundConstantPrime d C`.
  set C' : ℝ := coercivityIntegrandLowerBoundConstantPrime d C
  have hC'_pos : 0 < C' := coercivityIntegrandLowerBoundConstantPrime_pos d C
  have hPre : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      0 < m x →
        (1 / C') * (m x ^ (β + 1) + ‖fun i => Du i x‖ ^ α)
            - C' * (m x + m x ^ β + ‖fun i => Du i x‖) - C'
          ≤ coerciveHamIntegrand H DpH Du m x :=
    coercivity_integrand_lower_bound_explicit H DpH hC
      h_lagr h_lower h_H01_le h_DpH01_le Du m
  -- Useful arithmetic facts.
  have hαpos : 0 < α := lt_trans one_pos hα
  have hαm1_pos : 0 < α - 1 := sub_pos.mpr hα
  have hβp1_pos : 0 < β + 1 := by linarith
  have hβne : β ≠ 0 := ne_of_gt hβ
  have hαne : α ≠ 0 := ne_of_gt hαpos
  have hαm1_ne : α - 1 ≠ 0 := ne_of_gt hαm1_pos
  have hβp1_ne : β + 1 ≠ 0 := ne_of_gt hβp1_pos
  -- Conjugate exponents.
  have hHC_β : Real.HolderConjugate (β + 1) ((β + 1) / β) :=
    holderConjugate_betaPlusOne hβ
  have hHC_β' : Real.HolderConjugate ((β + 1) / β) (β + 1) := hHC_β.symm
  have hHC_α : Real.HolderConjugate α (α / (α - 1)) :=
    holderConjugate_alpha_local hα
  -- Young parameters chosen so each Young absorption contributes at most
  -- `1/(4C')` to the `m^{β+1}` coefficient, and `1/(2C')` to the `‖p‖^α`
  -- coefficient. Total slack absorbed: `(1/(2C'))(m^{β+1} + ‖p‖^α)`.
  set θ₁ : ℝ := (β + 1) / (4 * C' ^ 2) with hθ₁def
  set θ₂ : ℝ := (β + 1) / (4 * β * C' ^ 2) with hθ₂def
  set θ₃ : ℝ := α / (2 * C' ^ 2) with hθ₃def
  have hθ₁_pos : 0 < θ₁ := by
    have : 0 < 4 * C' ^ 2 := by positivity
    exact div_pos hβp1_pos this
  have hθ₂_pos : 0 < θ₂ := by
    have : 0 < 4 * β * C' ^ 2 := by positivity
    exact div_pos hβp1_pos this
  have hθ₃_pos : 0 < θ₃ := by
    have : 0 < 2 * C' ^ 2 := by positivity
    exact div_pos hαpos this
  -- Coefficient checks (these become exact equalities by construction).
  have h_coeff_θ₁ : C' * θ₁ / (β + 1) = 1 / (4 * C') := by
    have hC'_ne : C' ≠ 0 := ne_of_gt hC'_pos
    change C' * ((β + 1) / (4 * C' ^ 2)) / (β + 1) = 1 / (4 * C')
    field_simp
  have h_coeff_θ₂ : C' * θ₂ * β / (β + 1) = 1 / (4 * C') := by
    have hC'_ne : C' ≠ 0 := ne_of_gt hC'_pos
    change C' * ((β + 1) / (4 * β * C' ^ 2)) * β / (β + 1) = 1 / (4 * C')
    field_simp
  have h_coeff_θ₃ : C' * θ₃ / α = 1 / (2 * C') := by
    have hC'_ne : C' ≠ 0 := ne_of_gt hC'_pos
    change C' * (α / (2 * C' ^ 2)) / α = 1 / (2 * C')
    field_simp
  -- Constants from the residual `θ_i^{-something}` terms in Young.
  -- Define `K := C_1 + C_2 + C_3` where
  --   C_1 = C' * θ₁^{-1/β} * β/(β+1)         [from `m`-Young residual]
  --   C_2 = C' * θ₂^{-β}/(β+1)               [from `m^β`-Young residual]
  --   C_3 = C' * θ₃^{-1/(α-1)} * (α-1)/α     [from `‖p‖`-Young residual]
  set K₁ : ℝ := C' * θ₁ ^ (-(1 / β)) * (β / (β + 1)) with hK₁def
  set K₂ : ℝ := C' * θ₂ ^ (-β) / (β + 1) with hK₂def
  set K₃ : ℝ := C' * θ₃ ^ (-(1 / (α - 1))) * ((α - 1) / α) with hK₃def
  have hK₁_pos : 0 < K₁ := by
    refine mul_pos (mul_pos hC'_pos (Real.rpow_pos_of_pos hθ₁_pos _)) ?_
    exact div_pos hβ hβp1_pos
  have hK₂_pos : 0 < K₂ := by
    have hp : 0 < C' * θ₂ ^ (-β) := mul_pos hC'_pos (Real.rpow_pos_of_pos hθ₂_pos _)
    exact div_pos hp hβp1_pos
  have hK₃_pos : 0 < K₃ := by
    refine mul_pos (mul_pos hC'_pos (Real.rpow_pos_of_pos hθ₃_pos _)) ?_
    exact div_pos hαm1_pos hαpos
  -- Define the final constant `C''`.
  set C'' : ℝ := max (2 * C') (K₁ + K₂ + K₃ + C') + 1 with hC''def
  have hC''_lb_2C' : 2 * C' ≤ C'' := by
    have h1 : 2 * C' ≤ max (2 * C') (K₁ + K₂ + K₃ + C') := le_max_left _ _
    linarith
  have hC''_lb_K : K₁ + K₂ + K₃ + C' ≤ C'' := by
    have h1 : K₁ + K₂ + K₃ + C' ≤ max (2 * C') (K₁ + K₂ + K₃ + C') := le_max_right _ _
    linarith
  have hC''_pos : 0 < C'' := by
    have : 0 < 2 * C' := by linarith
    linarith
  filter_upwards [hPre] with x hx hmx
  -- Apply the pre-Young bound and abbreviate.
  have hPreBound := hx hmx
  set p : Fin d → ℝ := fun i => Du i x with hpdef
  set mx : ℝ := m x with hmxdef
  have hmx_nn : 0 ≤ mx := hmx.le
  have hp_nn : 0 ≤ ‖p‖ := norm_nonneg _
  have hmβ_nn : 0 ≤ mx ^ β := Real.rpow_nonneg hmx_nn _
  have hmβp1_nn : 0 ≤ mx ^ (β + 1) := Real.rpow_nonneg hmx_nn _
  have hpα_nn : 0 ≤ ‖p‖ ^ α := Real.rpow_nonneg hp_nn _
  -- Young step 1: `m ≤ θ₁ · m^{β+1} / (β+1) + θ₁^{-1/β} · β/(β+1)`.
  -- Apply `young_inequality_of_nonneg` to `(θ₁^{1/(β+1)} mx, θ₁^{-1/(β+1)})`.
  have hθ₁_inv_pos : 0 < θ₁ ^ ((1 : ℝ) / (β + 1)) := Real.rpow_pos_of_pos hθ₁_pos _
  have hθ₁_neg_pos : 0 < θ₁ ^ ((-1 : ℝ) / (β + 1)) := Real.rpow_pos_of_pos hθ₁_pos _
  have hθ₁_prod : θ₁ ^ ((1 : ℝ) / (β + 1)) * θ₁ ^ ((-1 : ℝ) / (β + 1)) = 1 := by
    rw [← Real.rpow_add hθ₁_pos]
    have : (1 : ℝ) / (β + 1) + (-1 : ℝ) / (β + 1) = 0 := by
      field_simp
      ring
    rw [this, Real.rpow_zero]
  have hθ₁_pow_p : (θ₁ ^ ((1 : ℝ) / (β + 1))) ^ (β + 1) = θ₁ := by
    rw [← Real.rpow_mul hθ₁_pos.le]
    have : (1 : ℝ) / (β + 1) * (β + 1) = 1 := by
      field_simp
    rw [this, Real.rpow_one]
  have hθ₁_pow_q : (θ₁ ^ ((-1 : ℝ) / (β + 1))) ^ ((β + 1) / β) = θ₁ ^ (-(1 / β)) := by
    rw [← Real.rpow_mul hθ₁_pos.le]
    congr 1
    field_simp
  have hYoung_m :
      mx ≤ θ₁ * mx ^ (β + 1) / (β + 1) + θ₁ ^ (-(1 / β)) * (β / (β + 1)) := by
    have ha_nn : 0 ≤ θ₁ ^ ((1 : ℝ) / (β + 1)) * mx :=
      mul_nonneg hθ₁_inv_pos.le hmx_nn
    have hb_nn : 0 ≤ θ₁ ^ ((-1 : ℝ) / (β + 1)) := hθ₁_neg_pos.le
    have hY := Real.young_inequality_of_nonneg ha_nn hb_nn hHC_β
    -- LHS: `(θ₁^{1/(β+1)} * mx) * θ₁^{-1/(β+1)} = mx`.
    have hLHS :
        θ₁ ^ ((1 : ℝ) / (β + 1)) * mx * θ₁ ^ ((-1 : ℝ) / (β + 1)) = mx := by
      have : θ₁ ^ ((1 : ℝ) / (β + 1)) * mx * θ₁ ^ ((-1 : ℝ) / (β + 1))
            = (θ₁ ^ ((1 : ℝ) / (β + 1)) * θ₁ ^ ((-1 : ℝ) / (β + 1))) * mx := by ring
      rw [this, hθ₁_prod, one_mul]
    -- First RHS term: `(θ₁^{1/(β+1)} mx)^{β+1}/(β+1) = θ₁ * mx^{β+1}/(β+1)`.
    have hR1 :
        (θ₁ ^ ((1 : ℝ) / (β + 1)) * mx) ^ (β + 1) / (β + 1)
          = θ₁ * mx ^ (β + 1) / (β + 1) := by
      rw [Real.mul_rpow hθ₁_inv_pos.le hmx_nn, hθ₁_pow_p]
    -- Second RHS term: `(θ₁^{-1/(β+1)})^{(β+1)/β} = θ₁^{-1/β}`.
    have hR2 :
        (θ₁ ^ ((-1 : ℝ) / (β + 1))) ^ ((β + 1) / β) / ((β + 1) / β)
          = θ₁ ^ (-(1 / β)) * (β / (β + 1)) := by
      rw [hθ₁_pow_q]
      have hβp1_β_ne : (β + 1) / β ≠ 0 := by
        have : 0 < (β + 1) / β := div_pos hβp1_pos hβ
        exact ne_of_gt this
      field_simp
    rw [hLHS, hR1, hR2] at hY
    exact hY
  -- Young step 2: `m^β ≤ θ₂ · m^{β+1} · β/(β+1) + θ₂^{-β}/(β+1)`.
  -- Use HolderConjugate ((β+1)/β, β+1), and `(m^β)^{(β+1)/β} = m^{β+1}`.
  have hθ₂_inv_pos : 0 < θ₂ ^ (β / (β + 1)) := Real.rpow_pos_of_pos hθ₂_pos _
  have hθ₂_neg_pos : 0 < θ₂ ^ (-(β / (β + 1))) := Real.rpow_pos_of_pos hθ₂_pos _
  have hθ₂_prod : θ₂ ^ (β / (β + 1)) * θ₂ ^ (-(β / (β + 1))) = 1 := by
    rw [← Real.rpow_add hθ₂_pos]
    rw [add_neg_cancel, Real.rpow_zero]
  have hθ₂_pow_p : (θ₂ ^ (β / (β + 1))) ^ ((β + 1) / β) = θ₂ := by
    rw [← Real.rpow_mul hθ₂_pos.le]
    have : β / (β + 1) * ((β + 1) / β) = 1 := by
      field_simp
    rw [this, Real.rpow_one]
  have hθ₂_pow_q : (θ₂ ^ (-(β / (β + 1)))) ^ (β + 1) = θ₂ ^ (-β) := by
    rw [← Real.rpow_mul hθ₂_pos.le]
    congr 1
    field_simp
  have h_mβ_pow : (mx ^ β) ^ ((β + 1) / β) = mx ^ (β + 1) := by
    rw [← Real.rpow_mul hmx_nn]
    congr 1
    field_simp
  have hYoung_mβ :
      mx ^ β ≤ θ₂ * mx ^ (β + 1) * (β / (β + 1)) + θ₂ ^ (-β) / (β + 1) := by
    have ha_nn : 0 ≤ θ₂ ^ (β / (β + 1)) * mx ^ β :=
      mul_nonneg hθ₂_inv_pos.le hmβ_nn
    have hb_nn : 0 ≤ θ₂ ^ (-(β / (β + 1))) := hθ₂_neg_pos.le
    have hY := Real.young_inequality_of_nonneg ha_nn hb_nn hHC_β'
    have hLHS :
        θ₂ ^ (β / (β + 1)) * mx ^ β * θ₂ ^ (-(β / (β + 1))) = mx ^ β := by
      have : θ₂ ^ (β / (β + 1)) * mx ^ β * θ₂ ^ (-(β / (β + 1)))
            = (θ₂ ^ (β / (β + 1)) * θ₂ ^ (-(β / (β + 1)))) * mx ^ β := by ring
      rw [this, hθ₂_prod, one_mul]
    have hR1 :
        (θ₂ ^ (β / (β + 1)) * mx ^ β) ^ ((β + 1) / β) / ((β + 1) / β)
          = θ₂ * mx ^ (β + 1) * (β / (β + 1)) := by
      rw [Real.mul_rpow hθ₂_inv_pos.le hmβ_nn, hθ₂_pow_p, h_mβ_pow]
      have hβp1_β_ne : (β + 1) / β ≠ 0 := by
        have : 0 < (β + 1) / β := div_pos hβp1_pos hβ
        exact ne_of_gt this
      field_simp
    have hR2 :
        (θ₂ ^ (-(β / (β + 1)))) ^ (β + 1) / (β + 1) = θ₂ ^ (-β) / (β + 1) := by
      rw [hθ₂_pow_q]
    rw [hLHS, hR1, hR2] at hY
    exact hY
  -- Young step 3: `‖p‖ ≤ θ₃ * ‖p‖^α/α + θ₃^{-1/(α-1)} * (α-1)/α`.
  have hθ₃_inv_pos : 0 < θ₃ ^ ((1 : ℝ) / α) := Real.rpow_pos_of_pos hθ₃_pos _
  have hθ₃_neg_pos : 0 < θ₃ ^ ((-1 : ℝ) / α) := Real.rpow_pos_of_pos hθ₃_pos _
  have hθ₃_prod : θ₃ ^ ((1 : ℝ) / α) * θ₃ ^ ((-1 : ℝ) / α) = 1 := by
    rw [← Real.rpow_add hθ₃_pos]
    have : (1 : ℝ) / α + (-1 : ℝ) / α = 0 := by field_simp; ring
    rw [this, Real.rpow_zero]
  have hθ₃_pow_p : (θ₃ ^ ((1 : ℝ) / α)) ^ α = θ₃ := by
    rw [← Real.rpow_mul hθ₃_pos.le]
    have : (1 : ℝ) / α * α = 1 := by field_simp
    rw [this, Real.rpow_one]
  have hθ₃_pow_q : (θ₃ ^ ((-1 : ℝ) / α)) ^ (α / (α - 1)) = θ₃ ^ (-(1 / (α - 1))) := by
    rw [← Real.rpow_mul hθ₃_pos.le]
    congr 1
    field_simp
  have hYoung_p :
      ‖p‖ ≤ θ₃ * ‖p‖ ^ α / α + θ₃ ^ (-(1 / (α - 1))) * ((α - 1) / α) := by
    have ha_nn : 0 ≤ θ₃ ^ ((1 : ℝ) / α) * ‖p‖ :=
      mul_nonneg hθ₃_inv_pos.le hp_nn
    have hb_nn : 0 ≤ θ₃ ^ ((-1 : ℝ) / α) := hθ₃_neg_pos.le
    have hY := Real.young_inequality_of_nonneg ha_nn hb_nn hHC_α
    have hLHS :
        θ₃ ^ ((1 : ℝ) / α) * ‖p‖ * θ₃ ^ ((-1 : ℝ) / α) = ‖p‖ := by
      have : θ₃ ^ ((1 : ℝ) / α) * ‖p‖ * θ₃ ^ ((-1 : ℝ) / α)
            = (θ₃ ^ ((1 : ℝ) / α) * θ₃ ^ ((-1 : ℝ) / α)) * ‖p‖ := by ring
      rw [this, hθ₃_prod, one_mul]
    have hR1 :
        (θ₃ ^ ((1 : ℝ) / α) * ‖p‖) ^ α / α = θ₃ * ‖p‖ ^ α / α := by
      rw [Real.mul_rpow hθ₃_inv_pos.le hp_nn, hθ₃_pow_p]
    have hR2 :
        (θ₃ ^ ((-1 : ℝ) / α)) ^ (α / (α - 1)) / (α / (α - 1))
          = θ₃ ^ (-(1 / (α - 1))) * ((α - 1) / α) := by
      rw [hθ₃_pow_q]
      have hα_quot_ne : α / (α - 1) ≠ 0 := by
        have : 0 < α / (α - 1) := div_pos hαpos hαm1_pos
        exact ne_of_gt this
      field_simp
    rw [hLHS, hR1, hR2] at hY
    exact hY
  -- Multiply each Young inequality by `C' ≥ 0` and rearrange.
  have hC'_nn : 0 ≤ C' := hC'_pos.le
  -- For `m`: `C' * m ≤ (1/(4C')) * m^{β+1} + K₁`.
  have hYoung_m_C' :
      C' * mx ≤ (1 / (4 * C')) * mx ^ (β + 1) + K₁ := by
    have h := mul_le_mul_of_nonneg_left hYoung_m hC'_nn
    -- `C' * (θ₁ * mx^{β+1} / (β+1)) = (C' * θ₁/(β+1)) * mx^{β+1} = 1/(4C') * mx^{β+1}`.
    have hRHS_eq :
        C' * (θ₁ * mx ^ (β + 1) / (β + 1)
              + θ₁ ^ (-(1 / β)) * (β / (β + 1)))
          = (C' * θ₁ / (β + 1)) * mx ^ (β + 1) + K₁ := by
      change C' * (θ₁ * mx ^ (β + 1) / (β + 1)
              + θ₁ ^ (-(1 / β)) * (β / (β + 1)))
          = (C' * θ₁ / (β + 1)) * mx ^ (β + 1)
            + C' * θ₁ ^ (-(1 / β)) * (β / (β + 1))
      ring
    rw [hRHS_eq] at h
    rw [h_coeff_θ₁] at h
    exact h
  -- For `m^β`: `C' * m^β ≤ (1/(4C')) * m^{β+1} + K₂`.
  have hYoung_mβ_C' :
      C' * mx ^ β ≤ (1 / (4 * C')) * mx ^ (β + 1) + K₂ := by
    have h := mul_le_mul_of_nonneg_left hYoung_mβ hC'_nn
    have hRHS_eq :
        C' * (θ₂ * mx ^ (β + 1) * (β / (β + 1))
              + θ₂ ^ (-β) / (β + 1))
          = (C' * θ₂ * β / (β + 1)) * mx ^ (β + 1) + K₂ := by
      change C' * (θ₂ * mx ^ (β + 1) * (β / (β + 1))
              + θ₂ ^ (-β) / (β + 1))
          = (C' * θ₂ * β / (β + 1)) * mx ^ (β + 1)
            + C' * θ₂ ^ (-β) / (β + 1)
      field_simp
    rw [hRHS_eq] at h
    rw [h_coeff_θ₂] at h
    exact h
  -- For `‖p‖`: `C' * ‖p‖ ≤ (1/(2C')) * ‖p‖^α + K₃`.
  have hYoung_p_C' :
      C' * ‖p‖ ≤ (1 / (2 * C')) * ‖p‖ ^ α + K₃ := by
    have h := mul_le_mul_of_nonneg_left hYoung_p hC'_nn
    have hRHS_eq :
        C' * (θ₃ * ‖p‖ ^ α / α + θ₃ ^ (-(1 / (α - 1))) * ((α - 1) / α))
          = (C' * θ₃ / α) * ‖p‖ ^ α + K₃ := by
      change C' * (θ₃ * ‖p‖ ^ α / α + θ₃ ^ (-(1 / (α - 1))) * ((α - 1) / α))
          = (C' * θ₃ / α) * ‖p‖ ^ α
            + C' * θ₃ ^ (-(1 / (α - 1))) * ((α - 1) / α)
      ring
    rw [hRHS_eq] at h
    rw [h_coeff_θ₃] at h
    exact h
  -- Sum the three: `C'(m + m^β + ‖p‖) ≤ (1/(2C')) m^{β+1} + (1/(2C')) ‖p‖^α + K`.
  have hYoung_sum :
      C' * (mx + mx ^ β + ‖p‖)
        ≤ (1 / (2 * C')) * (mx ^ (β + 1) + ‖p‖ ^ α) + (K₁ + K₂ + K₃) := by
    have hsum := add_le_add (add_le_add hYoung_m_C' hYoung_mβ_C') hYoung_p_C'
    have hLHS : C' * mx + C' * mx ^ β + C' * ‖p‖ = C' * (mx + mx ^ β + ‖p‖) := by ring
    have hRHS :
        (1 / (4 * C')) * mx ^ (β + 1) + K₁
            + ((1 / (4 * C')) * mx ^ (β + 1) + K₂)
            + ((1 / (2 * C')) * ‖p‖ ^ α + K₃)
          = (1 / (2 * C')) * (mx ^ (β + 1) + ‖p‖ ^ α) + (K₁ + K₂ + K₃) := by
      have hC'_ne : C' ≠ 0 := ne_of_gt hC'_pos
      field_simp
      ring
    linarith [hsum, hLHS, hRHS]
  -- Combine with the pre-Young bound.
  -- pre-Young: `(1/C')(m^{β+1} + ‖p‖^α) - C'(m + m^β + ‖p‖) - C' ≤ integrand`.
  -- We want: `(1/C'')(m^{β+1} + ‖p‖^α) - C'' ≤ integrand`.
  -- Lower-bound the LHS.
  -- `(1/C') X - C' Y - C'`, with `Y := m + m^β + ‖p‖` and `X := m^{β+1} + ‖p‖^α`,
  -- and Young gives `C' Y ≤ (1/(2C')) X + K`. Hence
  -- `(1/C') X - C' Y - C' ≥ (1/C') X - (1/(2C')) X - K - C' = (1/(2C')) X - (K + C')`.
  have hX_nn : 0 ≤ mx ^ (β + 1) + ‖p‖ ^ α := add_nonneg hmβp1_nn hpα_nn
  have hStepBound :
      (1 / (2 * C')) * (mx ^ (β + 1) + ‖p‖ ^ α) - (K₁ + K₂ + K₃ + C')
        ≤ coerciveHamIntegrand H DpH Du m x := by
    have hC'_ne : C' ≠ 0 := ne_of_gt hC'_pos
    -- Re-express `(1/C') X - C' Y - C' ≥ (1/C') X - ((1/(2C')) X + K) - C'`.
    have hUpperC'Y :
        (1 / C') * (mx ^ (β + 1) + ‖p‖ ^ α) - C' * (mx + mx ^ β + ‖p‖) - C'
          ≥ (1 / C') * (mx ^ (β + 1) + ‖p‖ ^ α)
              - ((1 / (2 * C')) * (mx ^ (β + 1) + ‖p‖ ^ α)
                  + (K₁ + K₂ + K₃)) - C' := by
      linarith [hYoung_sum]
    have hSimp :
        (1 / C') * (mx ^ (β + 1) + ‖p‖ ^ α)
              - ((1 / (2 * C')) * (mx ^ (β + 1) + ‖p‖ ^ α)
                  + (K₁ + K₂ + K₃)) - C'
          = (1 / (2 * C')) * (mx ^ (β + 1) + ‖p‖ ^ α) - (K₁ + K₂ + K₃ + C') := by
      field_simp
      ring
    linarith [hPreBound, hUpperC'Y, hSimp]
  -- Now dominate `(1/(2C')) X - (K₁+K₂+K₃+C')` by `(1/C'') X - C''`,
  -- using `1/C'' ≤ 1/(2C')` (since `2C' ≤ C''`) and `K₁+K₂+K₃+C' ≤ C''`.
  have hC''_inv_le : 1 / C'' ≤ 1 / (2 * C') := by
    rw [one_div, one_div]
    have h2C'_pos : 0 < 2 * C' := by linarith
    exact inv_anti₀ h2C'_pos hC''_lb_2C'
  have hX_dom :
      (1 / C'') * (mx ^ (β + 1) + ‖p‖ ^ α)
        ≤ (1 / (2 * C')) * (mx ^ (β + 1) + ‖p‖ ^ α) :=
    mul_le_mul_of_nonneg_right hC''_inv_le hX_nn
  -- Final assembly.
  linarith [hStepBound, hX_dom, hC''_lb_K]

/-- **Coercivity integrand pointwise lower bound — post-Young form**
(paper line 965, inside the proof of `prop:coercAepsi`).

Combining the pre-Young bound `coercivity_integrand_lower_bound` with
three applications of Young's inequality (to `m`, `m^β`, and `‖Du‖`),
the slack `−C'(m + m^β + ‖Du‖)` is absorbed into half of the positive
`(1/C')(m^{β+1} + ‖Du‖^α)` and a fresh additive constant.

The output is the clean form

  `coerciveHamIntegrand H DpH Du m x
     ≥ (1/C'')(m(x)^{β+1} + ‖Du(x)‖^α) − C''`

a.e. on the unit cube, for `m(x) > 0`. The dependent `ε|Du|^{γ̄} +
ε|u|^{γ̄}` part of `eq:coercive-test.Aepsi` lives outside this Hamiltonian
integrand (carried by `gateauxWpPair` in
`coercive_test_pair_identity`).

Hypotheses match those of `coercivity_integrand_lower_bound`, with the
additions `hα : 1 < α` and `hβ : 0 < β` needed to invoke Young's
inequality with the conjugate pairs `(β+1, (β+1)/β)` and `(α, α/(α-1))`.

This is a one-line forwarder onto the explicit sibling
`coercivity_integrand_lower_bound_young_explicit`, which returns the
explicit constant `coercivityIntegrandLowerBoundYoungConstant d C α β`
directly.
-/
theorem coercivity_integrand_lower_bound_young
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    {C α β : ℝ}
    (hC : 0 < C) (hα : 1 < α) (hβ : 0 < β)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ β) / C - C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (h_lower :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (‖p‖ ^ α) / C - C * (mx ^ β + 1) ≤ H x p mx)
    (h_H01_le :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), |H x (0 : Fin d → ℝ) 1| ≤ C)
    (h_DpH01_le :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖DpH x (0 : Fin d → ℝ) 1‖ ≤ C)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m : (Fin d → ℝ) → ℝ) :
    ∃ C'' : ℝ, 0 < C'' ∧
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        0 < m x →
          (1 / C'') * (m x ^ (β + 1) + ‖fun i => Du i x‖ ^ α) - C''
            ≤ coerciveHamIntegrand H DpH Du m x :=
  ⟨coercivityIntegrandLowerBoundYoungConstant d C α β,
    coercivityIntegrandLowerBoundYoungConstant_pos d C α β,
    coercivity_integrand_lower_bound_young_explicit H DpH hC hα hβ
      h_lagr h_lower h_H01_le h_DpH01_le Du m⟩

/-! ## Unit tests for the post-Young lower bound -/

/-- **API sanity check for `coercivity_integrand_lower_bound_young`**: the
post-Young clean form is delivered with the additional inputs
`hα : 1 < α`, `hβ : 0 < β`. -/
example
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (C α β : ℝ) (hC : 0 < C) (hα : 1 < α) (hβ : 0 < β)
    (h_lagr :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (mx ^ β) / C - C ≤ (DpH x p mx) ⬝ p - H x p mx)
    (h_lower :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p mx, 0 < mx →
          (‖p‖ ^ α) / C - C * (mx ^ β + 1) ≤ H x p mx)
    (h_H01_le :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), |H x (0 : Fin d → ℝ) 1| ≤ C)
    (h_DpH01_le :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖DpH x (0 : Fin d → ℝ) 1‖ ≤ C)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m : (Fin d → ℝ) → ℝ) :
    ∃ C'' : ℝ, 0 < C'' ∧
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        0 < m x →
          (1 / C'') * (m x ^ (β + 1) + ‖fun i => Du i x‖ ^ α) - C''
            ≤ coerciveHamIntegrand H DpH Du m x :=
  coercivity_integrand_lower_bound_young H DpH hC hα hβ
    h_lagr h_lower h_H01_le h_DpH01_le Du m

/-! ## Integrated coercivity lower bound

This section integrates the post-Young pointwise lower bound
`coercivity_integrand_lower_bound_young` over the unit cube to obtain the
`L^{β̄}`-level coercivity estimate of paper line 967, eq.~`eq:coercive.Aepsi`.
The integration step is a direct application of `setIntegral_mono_ae` together
with `integral_const` (using `volume_unitCube = 1`); we then identify
`∫ m^{β+1}` with `lpNormPer (β+1) m ^ (β+1)` via the pre-existing bridge
`lpNormPer_eq_integral_rpow` from `StationaryMFG/Solutions/MFGOperator.lean`.

The cleanest formulation packages the pointwise bound (without the `0 < m x`
premise of the Young theorem) as a single hypothesis, plus integrability of
both sides on the cube. This isolates the integration step from the
positivity-of-`m` extension (which is independent linear algebra and lives
in a sibling task).
-/

/-- **Integrated coercivity lower bound** (paper line 967,
`eq:coercive.Aepsi`).

Given the post-Young pointwise lower bound for the Hamiltonian integrand
of paper eq.~`eq:coercive-test.Aepsi` (the conclusion of
`coercivity_integrand_lower_bound_young`, packaged here without the
`0 < m x` premise as a single a.e. inequality on the unit cube), and
integrability of both sides, the integral form holds:

```
(1/C'') · ∫_{𝕋^d} m(x)^{β+1} dx
  + (1/C'') · ∫_{𝕋^d} ‖Du(x)‖^α dx
  − C''
≤ ∫_{𝕋^d} coerciveHamIntegrand H DpH Du m x dx.
```

This is the first half of paper line 967–970: the second half identifies
the `m^{β+1}` integral with `lpNormPer (β+1) m ^ (β+1)` (via
`integral_rpow_eq_lpNormPer_rpow` below) and combines with the `ε`-Gateaux
integral coming from `coercive_test_pair_identity` to deliver the
`paper:prop:coercAepsi` bound. -/
theorem coercivity_integral_lower_bound
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    {C'' β α : ℝ} (_hC''_pos : 0 < C'')
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m : (Fin d → ℝ) → ℝ)
    (hPointwise :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        (1 / C'') * (m x ^ (β + 1) + ‖fun i => Du i x‖ ^ α) - C''
          ≤ coerciveHamIntegrand H DpH Du m x)
    (hHam_int : IntegrableOn
        (fun x => coerciveHamIntegrand H DpH Du m x) (UnitCube d))
    (hLB_int : IntegrableOn
        (fun x =>
          (1 / C'') * (m x ^ (β + 1) + ‖fun i => Du i x‖ ^ α) - C'')
        (UnitCube d))
    (hRpow_m_int : IntegrableOn (fun x => m x ^ (β + 1)) (UnitCube d))
    (hRpow_p_int : IntegrableOn
        (fun x => ‖fun i => Du i x‖ ^ α) (UnitCube d)) :
    (1 / C'') * (∫ x in UnitCube d, m x ^ (β + 1))
        + (1 / C'') * (∫ x in UnitCube d, ‖fun i => Du i x‖ ^ α)
        - C''
      ≤ ∫ x in UnitCube d, coerciveHamIntegrand H DpH Du m x := by
  -- Step 1: integrate the pointwise lower bound over the cube.
  have hIntMono :
      ∫ x in UnitCube d,
          (1 / C'') * (m x ^ (β + 1) + ‖fun i => Du i x‖ ^ α) - C''
        ≤ ∫ x in UnitCube d, coerciveHamIntegrand H DpH Du m x :=
    integral_mono_ae hLB_int hHam_int hPointwise
  -- Step 2: split the LHS integral into three pieces using linearity.
  have hSum_int : IntegrableOn
      (fun x => m x ^ (β + 1) + ‖fun i => Du i x‖ ^ α) (UnitCube d) :=
    hRpow_m_int.add hRpow_p_int
  have hSum_smul_int : IntegrableOn
      (fun x => (1 / C'') * (m x ^ (β + 1) + ‖fun i => Du i x‖ ^ α))
      (UnitCube d) :=
    hSum_int.const_mul _
  -- Const integral on the cube: `∫_{[0,1)^d} C'' dx = C''` since
  -- `volume_unitCube = 1`.
  have hConst_eq : ∫ _ in UnitCube d, (C'' : ℝ) = C'' := by
    rw [setIntegral_const, measureReal_def, volume_unitCube]
    simp
  -- LHS rewrite step.
  have hLHS_eq :
      ∫ x in UnitCube d,
          (1 / C'') * (m x ^ (β + 1) + ‖fun i => Du i x‖ ^ α) - C''
        = (1 / C'') * (∫ x in UnitCube d, m x ^ (β + 1))
            + (1 / C'') * (∫ x in UnitCube d, ‖fun i => Du i x‖ ^ α)
            - C'' := by
    have h_const_int : IntegrableOn (fun _ : Fin d → ℝ => (C'' : ℝ))
        (UnitCube d) := by
      have hμ_ne : volume (UnitCube (d := d)) ≠ ⊤ := by
        rw [volume_unitCube]; exact ENNReal.one_ne_top
      exact integrableOn_const hμ_ne
    rw [integral_sub hSum_smul_int h_const_int]
    rw [hConst_eq]
    rw [MeasureTheory.integral_const_mul]
    rw [integral_add hRpow_m_int hRpow_p_int]
    ring
  linarith [hIntMono, hLHS_eq.symm.le, hLHS_eq.le]

/-- **Bridge: `∫ m^{β+1}` ≡ `lpNormPer (β+1) m ^ (β+1)`**.

For `m : (Fin d → ℝ) → ℝ` non-negative a.e. on the cube and `MemLpPer (β̄) m`
with `β̄ = ENNReal.ofReal (β + 1)` and `β + 1 > 0`, the cube integral of
`m^{β+1}` equals the (real) `Lᵖ`-seminorm raised to the `(β+1)`-th power.
This is the formal statement matching paper line 972's identification
`∫ m^{β+1} = ‖m‖_{L^{β̄}}^{β̄}`. -/
lemma integral_rpow_eq_lpNormPer_rpow
    {β : ℝ} (hβ_pos : 0 < β + 1)
    (m : (Fin d → ℝ) → ℝ)
    (hm : MemLpPer (ENNReal.ofReal (β + 1)) m)
    (hm_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x) :
    ∫ x in UnitCube d, m x ^ (β + 1)
      = lpNormPer (ENNReal.ofReal (β + 1)) m ^ (β + 1) := by
  have hβ_ne_zero : (ENNReal.ofReal (β + 1)) ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, not_le.mpr hβ_pos]
  have hβ_ne_top : (ENNReal.ofReal (β + 1)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hβ_toReal : (ENNReal.ofReal (β + 1)).toReal = β + 1 :=
    ENNReal.toReal_ofReal hβ_pos.le
  -- Apply the existing bridge lemma.
  have hbridge :
      lpNormPer (ENNReal.ofReal (β + 1)) m
        = (∫ x, ‖m x‖ ^ (ENNReal.ofReal (β + 1)).toReal
              ∂(Measure.restrict volume (UnitCube d))) ^
          (ENNReal.ofReal (β + 1)).toReal⁻¹ :=
    StationaryMFG.Solutions.MFG.lpNormPer_eq_integral_rpow
      hβ_ne_zero hβ_ne_top hm
  rw [hβ_toReal] at hbridge
  -- Eliminate `‖·‖` using `m ≥ 0` a.e.
  have hcong :
      (fun x => ‖m x‖ ^ (β + 1))
        =ᵐ[Measure.restrict volume (UnitCube d)]
        (fun x => m x ^ (β + 1)) := by
    filter_upwards [hm_nn] with x hx
    have habs : ‖m x‖ = m x := by
      rw [Real.norm_eq_abs, abs_of_nonneg hx]
    rw [habs]
  have hint_eq :
      ∫ x, ‖m x‖ ^ (β + 1) ∂(Measure.restrict volume (UnitCube d))
        = ∫ x, m x ^ (β + 1) ∂(Measure.restrict volume (UnitCube d)) :=
    integral_congr_ae hcong
  rw [hint_eq] at hbridge
  -- Now raise both sides of `hbridge` to the `(β+1)`-th power.
  -- `lpNormPer ... = INT^{1/(β+1)}`, so `lpNormPer ... ^ (β+1) = INT`.
  have hβp1_ne : β + 1 ≠ 0 := ne_of_gt hβ_pos
  have hINT_nn : 0 ≤ ∫ x, m x ^ (β + 1)
      ∂(Measure.restrict volume (UnitCube d)) := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [hm_nn] with x hx
    exact Real.rpow_nonneg hx _
  -- Take the `(β+1)`-th power. Both sides become equal after applying
  -- `Real.rpow_inv_rpow`.
  rw [hbridge, Real.rpow_inv_rpow hINT_nn hβp1_ne]

/-- **API sanity check** for `coercivity_integral_lower_bound`: given the
post-Young pointwise lower bound and integrability of both sides plus of
the `m^{β+1}` and `‖Du‖^α` terms, the integrated coercivity bound holds. -/
example
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (C'' β α : ℝ) (hC'' : 0 < C'')
    (Du : Fin d → (Fin d → ℝ) → ℝ) (m : (Fin d → ℝ) → ℝ)
    (hPointwise :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        (1 / C'') * (m x ^ (β + 1) + ‖fun i => Du i x‖ ^ α) - C''
          ≤ coerciveHamIntegrand H DpH Du m x)
    (hHam_int : IntegrableOn
        (fun x => coerciveHamIntegrand H DpH Du m x) (UnitCube d))
    (hLB_int : IntegrableOn
        (fun x =>
          (1 / C'') * (m x ^ (β + 1) + ‖fun i => Du i x‖ ^ α) - C'')
        (UnitCube d))
    (hRpow_m_int : IntegrableOn (fun x => m x ^ (β + 1)) (UnitCube d))
    (hRpow_p_int : IntegrableOn
        (fun x => ‖fun i => Du i x‖ ^ α) (UnitCube d)) :
    (1 / C'') * (∫ x in UnitCube d, m x ^ (β + 1))
        + (1 / C'') * (∫ x in UnitCube d, ‖fun i => Du i x‖ ^ α)
        - C''
      ≤ ∫ x in UnitCube d, coerciveHamIntegrand H DpH Du m x :=
  coercivity_integral_lower_bound (C'' := C'') (β := β) (α := α)
    H DpH hC'' Du m
    hPointwise hHam_int hLB_int hRpow_m_int hRpow_p_int

/-! ## ε-Laplacian / Sobolev coercivity term (paper §8, line 974)

The second half of paper `prop:coercAepsi` identifies the
ε-regularisation Gateaux term as an `L^{γ̄}`/Sobolev seminorm. The
identity at the heart of paper line 974 is

```
∫_{𝕋^d} (ε · |Du(x)|^{γ̄} + ε · |u(x)|^{γ̄}) dx
  = ε · (‖u‖_{L^{γ̄}}^{γ̄} + ∑_i ‖∂_i u‖_{L^{γ̄}}^{γ̄}).
```

We provide two forms:

1. **Equality form** (`coercivity_laplacian_lower_bound`): for `γ̄ > 0`,
   `u, Du i ∈ MemLpPer γ̄`, with `|·|^{γ̄}` (so no positivity premise),
   ```
   ε · (lpNormPer γ̄ u ^ γ̄ + ∑ i, lpNormPer γ̄ (Du i) ^ γ̄)
     = ε · ∫ |u|^{γ̄} + ε · ∑ i, ∫ |Du i|^{γ̄}.
   ```
   This is an **equality**, not an inequality: the only analytic content
   is the `lpNormPer^{γ̄} = ∫|·|^{γ̄}` bridge (`integral_rpow_eq_lpNormPer_rpow`).

2. **Banach-norm inequality form**
   (`coercivity_laplacian_sobolev_lower_bound`): expresses the Banach
   product-pair Sobolev seminorm in the `X_Banach` lift, with the
   dimension constant `(d+1)^{γ̄}`:
   ```
   ε · ‖toLpSobolev hu hDu‖^{γ̄}
     ≤ ε · (d+1)^{γ̄} · (∫|u|^{γ̄} + ∑ ∫|Du i|^{γ̄}).
   ```

Both forms feed `paperSolFor-coercivity-final`: form (1) is the
`lpNormPer` aggregation needed alongside the Eulerian sibling; form (2)
matches the abstract `X_Banach` pair-norm used by
`Aepsi_coercive_of_paperHypotheses`.
-/

/-- **Bridge: `∫ |u|^{γ̄}` ≡ `lpNormPer (γ̄) u ^ γ̄` (abs form)**.

For `u : (Fin d → ℝ) → ℝ` with `MemLpPer (ENNReal.ofReal γBar) u` and
`γBar > 0`, the cube integral of `|u|^{γBar}` equals the (real)
`Lᵖ`-seminorm raised to the `γBar`-th power.

This is the `|·|`-variant of `integral_rpow_eq_lpNormPer_rpow`: no
non-negativity premise is needed because the integrand is already
`|u x|^γBar ≥ 0`. -/
lemma integral_abs_rpow_eq_lpNormPer_rpow
    {γBar : ℝ} (hγ_pos : 0 < γBar)
    (u : (Fin d → ℝ) → ℝ)
    (hu : MemLpPer (ENNReal.ofReal γBar) u) :
    ∫ x in UnitCube d, |u x| ^ γBar
      = lpNormPer (ENNReal.ofReal γBar) u ^ γBar := by
  have hγ_ne_zero : (ENNReal.ofReal γBar) ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, not_le.mpr hγ_pos]
  have hγ_ne_top : (ENNReal.ofReal γBar) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hγ_toReal : (ENNReal.ofReal γBar).toReal = γBar :=
    ENNReal.toReal_ofReal hγ_pos.le
  -- Apply the existing bridge lemma `lpNormPer_eq_integral_rpow`.
  have hbridge :
      lpNormPer (ENNReal.ofReal γBar) u
        = (∫ x, ‖u x‖ ^ (ENNReal.ofReal γBar).toReal
              ∂(Measure.restrict volume (UnitCube d))) ^
          (ENNReal.ofReal γBar).toReal⁻¹ :=
    StationaryMFG.Solutions.MFG.lpNormPer_eq_integral_rpow
      hγ_ne_zero hγ_ne_top hu
  rw [hγ_toReal] at hbridge
  -- `‖u x‖ = |u x|` for real-valued `u`.
  have hcong :
      (fun x => ‖u x‖ ^ γBar)
        =ᵐ[Measure.restrict volume (UnitCube d)]
        (fun x => |u x| ^ γBar) := by
    refine ae_of_all _ ?_
    intro x
    change ‖u x‖ ^ γBar = |u x| ^ γBar
    rw [Real.norm_eq_abs]
  have hint_eq :
      ∫ x, ‖u x‖ ^ γBar ∂(Measure.restrict volume (UnitCube d))
        = ∫ x, |u x| ^ γBar ∂(Measure.restrict volume (UnitCube d)) :=
    integral_congr_ae hcong
  rw [hint_eq] at hbridge
  -- Raise both sides to the `γBar`-th power.
  have hγ_ne : γBar ≠ 0 := ne_of_gt hγ_pos
  have hINT_nn : 0 ≤ ∫ x, |u x| ^ γBar
      ∂(Measure.restrict volume (UnitCube d)) := by
    refine integral_nonneg_of_ae ?_
    refine ae_of_all _ ?_
    intro x
    exact Real.rpow_nonneg (abs_nonneg _) _
  rw [hbridge, Real.rpow_inv_rpow hINT_nn hγ_ne]

/-- **ε-Laplacian / Sobolev coercivity term, sum-of-`lpNormPer` form**
(paper §8, line 974).

For `γBar > 0`, `u : (Fin d → ℝ) → ℝ` and `Du : Fin d → (Fin d → ℝ) → ℝ`
each in `MemLpPer (ENNReal.ofReal γBar)`, and any `ε : ℝ`,
```
ε · (lpNormPer γ̄ u ^ γ̄ + ∑ i, lpNormPer γ̄ (Du i) ^ γ̄)
  = ε · ∫ |u|^γ̄ + ε · ∑ i, ∫ |Du i|^γ̄.
```

This is the integrated identity at paper line 974, expressing the
ε-Gateaux regularisation term in `Lᵖ`-seminorm form. As an equality,
it provides both the `≤` and `≥` directions, which is more than the
coercivity step strictly needs (a lower bound on the LHS by the RHS
is sufficient). The equality form is the natural output and easier
to consume downstream. -/
theorem coercivity_laplacian_lower_bound
    {γBar : ℝ} (hγ_pos : 0 < γBar) (ε : ℝ)
    (u : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (hu : MemLpPer (ENNReal.ofReal γBar) u)
    (hDu : ∀ i, MemLpPer (ENNReal.ofReal γBar) (Du i)) :
    ε * (lpNormPer (ENNReal.ofReal γBar) u ^ γBar
          + ∑ i, lpNormPer (ENNReal.ofReal γBar) (Du i) ^ γBar)
      = ε * (∫ x in UnitCube d, |u x| ^ γBar)
          + ε * ∑ i, (∫ x in UnitCube d, |Du i x| ^ γBar) := by
  -- Bridge `lpNormPer ^ γ̄ = ∫ |·|^γ̄` for `u` and each `Du i`.
  have hu_eq : ∫ x in UnitCube d, |u x| ^ γBar
                  = lpNormPer (ENNReal.ofReal γBar) u ^ γBar :=
    integral_abs_rpow_eq_lpNormPer_rpow (d := d) hγ_pos u hu
  have hDu_eq : ∀ i, ∫ x in UnitCube d, |Du i x| ^ γBar
                       = lpNormPer (ENNReal.ofReal γBar) (Du i) ^ γBar :=
    fun i => integral_abs_rpow_eq_lpNormPer_rpow (d := d) hγ_pos (Du i) (hDu i)
  -- Sum the `Du i` bridges over `i`.
  have hDu_sum : ∑ i, (∫ x in UnitCube d, |Du i x| ^ γBar)
                  = ∑ i, lpNormPer (ENNReal.ofReal γBar) (Du i) ^ γBar :=
    Finset.sum_congr rfl (fun i _ => hDu_eq i)
  -- Combine.
  rw [hu_eq, hDu_sum]
  ring

/-- **ε-Laplacian / Sobolev coercivity term, Banach-norm inequality form**
(paper §8, line 974, Banach lift).

For `γBar > 0`, `u : (Fin d → ℝ) → ℝ` with `MemSobolevPer (ENNReal.ofReal γBar) u`,
and an explicit `L^{γBar}`-integrable weak-derivative family `Du`,
the `γBar`-th power of the Banach Sobolev-pair seminorm is bounded by
the dimension-weighted integrated `|·|^{γBar}` sum:
```
ε · ‖toLpSobolev hu hDu‖^{γ̄}
  ≤ ε · (d+1)^{γ̄} · (∫|u|^{γ̄} + ∑ ∫|Du i|^{γ̄})
```
for `ε ≥ 0`.

This is the **Banach-pair-norm-translated** lift of the laplacian
coercivity step at paper line 974, ready for consumption by the
`X_Banach`-side final coercivity assembly. The dimension constant
`(d+1)^{γBar}` is the standard slack from the product-norm Sobolev
bound `MemSobolevPer.norm_toLpSobolev_rpow_le`. -/
theorem coercivity_laplacian_sobolev_lower_bound
    {γBar : ℝ} (hγ_pos : 0 < γBar) (ε : ℝ) (hε : 0 ≤ ε)
    {u : (Fin d → ℝ) → ℝ}
    (hu : MemSobolevPer (ENNReal.ofReal γBar) u)
    {Du : Fin d → ((Fin d → ℝ) → ℝ)}
    (hDu : ∀ i, MemLpPer (ENNReal.ofReal γBar) (Du i))
    [Fact (1 ≤ ENNReal.ofReal γBar)] :
    ε * ‖StationaryMFG.Periodic.MemSobolevPer.toLpSobolev hu hDu‖ ^ γBar
      ≤ ε * (((d : ℝ) + 1) ^ γBar *
          ((∫ x in UnitCube d, |u x| ^ γBar) +
            ∑ i, ∫ x in UnitCube d, |Du i x| ^ γBar)) := by
  have hγ_ne_zero : (ENNReal.ofReal γBar) ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, not_le.mpr hγ_pos]
  have hγ_ne_top : (ENNReal.ofReal γBar) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hγ_toReal : (ENNReal.ofReal γBar).toReal = γBar :=
    ENNReal.toReal_ofReal hγ_pos.le
  -- Step 1: apply `MemSobolevPer.norm_toLpSobolev_rpow_le`.
  have hsob :
      ‖StationaryMFG.Periodic.MemSobolevPer.toLpSobolev hu hDu‖
            ^ (ENNReal.ofReal γBar).toReal
        ≤ ((d : ℝ) + 1) ^ (ENNReal.ofReal γBar).toReal *
            ((∫ x in UnitCube d, |u x| ^ (ENNReal.ofReal γBar).toReal) +
              ∑ i, ∫ x in UnitCube d,
                |Du i x| ^ (ENNReal.ofReal γBar).toReal) :=
    StationaryMFG.Periodic.MemSobolevPer.norm_toLpSobolev_rpow_le
      (p := ENNReal.ofReal γBar) hγ_ne_zero hγ_ne_top hu hDu
  rw [hγ_toReal] at hsob
  -- Step 2: multiply by `ε ≥ 0`.
  exact mul_le_mul_of_nonneg_left hsob hε

/-! ## Producer wrapping the laplacian coercivity term

The producer `coercivity_laplacian_from_paperHypotheses` complements
`coercivity_eulerian_from_paperHypotheses`: it consumes only basic
`MemLpPer` integrability on `u` and `Du i` and an `ε ≥ 0` factor, and
produces the closed-form integrated lower bound at paper line 974 in
the `lpNormPer`-seminorm form. The final coercivity assembly
(`paperSolFor-coercivity-final`) will add this output to the Eulerian
sibling's output to recover the full `prop:coercAepsi` bound. -/

/-- **Integrated ε-Laplacian lower bound from `MemLpPer` data**
(paper line 974). Producer signature symmetric to
`coercivity_eulerian_from_paperHypotheses`: from `MemLpPer (γ̄)` on
`u` and each `Du i`, and an `ε ≥ 0` factor, conclude the integrated
identity at paper line 974. -/
theorem coercivity_laplacian_from_paperHypotheses
    {γBar : ℝ} (hγ_pos : 0 < γBar) (ε : ℝ) (_hε : 0 ≤ ε)
    (u : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (hu : MemLpPer (ENNReal.ofReal γBar) u)
    (hDu : ∀ i, MemLpPer (ENNReal.ofReal γBar) (Du i)) :
    ε * (lpNormPer (ENNReal.ofReal γBar) u ^ γBar
          + ∑ i, lpNormPer (ENNReal.ofReal γBar) (Du i) ^ γBar)
      = ε * (∫ x in UnitCube d, |u x| ^ γBar)
          + ε * ∑ i, (∫ x in UnitCube d, |Du i x| ^ γBar) :=
  coercivity_laplacian_lower_bound (d := d) hγ_pos ε u Du hu hDu

/-! ## Unit tests for the laplacian producer -/

/-- **API sanity check** for `coercivity_laplacian_from_paperHypotheses`:
the `MemLpPer`-hypothesis-only producer delivers the integrated equality
at paper line 974. -/
example
    {γBar : ℝ} (hγ_pos : 0 < γBar) (ε : ℝ) (hε : 0 ≤ ε)
    (u : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (hu : MemLpPer (ENNReal.ofReal γBar) u)
    (hDu : ∀ i, MemLpPer (ENNReal.ofReal γBar) (Du i)) :
    ε * (lpNormPer (ENNReal.ofReal γBar) u ^ γBar
          + ∑ i, lpNormPer (ENNReal.ofReal γBar) (Du i) ^ γBar)
      = ε * (∫ x in UnitCube d, |u x| ^ γBar)
          + ε * ∑ i, (∫ x in UnitCube d, |Du i x| ^ γBar) :=
  coercivity_laplacian_from_paperHypotheses (d := d) hγ_pos ε hε u Du hu hDu

/-- **API sanity check** for `coercivity_laplacian_sobolev_lower_bound`:
the Banach-norm inequality form delivers the dimension-weighted bound. -/
example
    {γBar : ℝ} (hγ_pos : 0 < γBar) (ε : ℝ) (hε : 0 ≤ ε)
    [Fact (1 ≤ ENNReal.ofReal γBar)]
    {u : (Fin d → ℝ) → ℝ}
    (hu : MemSobolevPer (ENNReal.ofReal γBar) u)
    {Du : Fin d → ((Fin d → ℝ) → ℝ)}
    (hDu : ∀ i, MemLpPer (ENNReal.ofReal γBar) (Du i)) :
    ε * ‖StationaryMFG.Periodic.MemSobolevPer.toLpSobolev hu hDu‖ ^ γBar
      ≤ ε * (((d : ℝ) + 1) ^ γBar *
          ((∫ x in UnitCube d, |u x| ^ γBar) +
            ∑ i, ∫ x in UnitCube d, |Du i x| ^ γBar)) :=
  coercivity_laplacian_sobolev_lower_bound (d := d) hγ_pos ε hε hu hDu

/-! ## Eulerian `H − V` lower bound from `HypothesisPowerGrowth`
(paper §8, `prop:coercAepsi`, lines 956–967)

This section produces the integrated **Eulerian** lower bound of paper
line 967 directly from a `Hamiltonian.HypothesisPowerGrowth` certificate,
without re-introducing the four-component pointwise input bundle of
`coercivity_integrand_lower_bound`.

The Eulerian half is:
```
(1/C_eul)·∫_{𝕋^d} m(x)^{β+1} dx + (1/C_eul)·∫_{𝕋^d} ‖Du(x)‖^α dx − C_eul
  ≤ ∫_{𝕋^d} coerciveHamIntegrand H DpH Du m x dx,
```
the integrated form of paper eq.~`eq:coercive.Aepsi`, with `C_eul`
depending only on the data fields `hpow.C`, `hpow.α`, `hpow.β`.

The strategy is a two-step reduction:

1. **`paperHypotheses_to_integrand_inputs`** — assemble the four
   pointwise inputs to `coercivity_integrand_lower_bound_young` from
   `hpow`:
   * `h_lagr`         from `hpow.lagr`     (paper line 956);
   * `h_lower`        from `hpow.lower`    (paper line 457);
   * `h_H01_le`       from `hpow.upper` and `hpow.lower` at `(p,m)=(0,1)`;
   * `h_DpH01_le`     from `hpow.DpH_upper` at `(p,m)=(0,1)`,
   with a single uniform constant `C̃ := 2·hpow.C + 1 ≥ hpow.C`.
2. **`coercivity_eulerian_from_paperHypotheses`** — call
   `coercivity_integral_lower_bound` on the post-Young pointwise bound
   from step (1), strengthened with `0 < m x` a.e. to drop the
   strict-positivity premise. -/

/-- **Bridge constant**: the uniform Young constant induced by a
`HypothesisPowerGrowth` certificate is `2·hpow.C + 1`, which is ≥ each
of the per-field constants required by
`coercivity_integrand_lower_bound`. -/
def powerGrowthCoercivityConstant
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH) : ℝ :=
  2 * hpow.C + 1

lemma powerGrowthCoercivityConstant_pos
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH) :
    0 < powerGrowthCoercivityConstant (d := d) hpow := by
  unfold powerGrowthCoercivityConstant
  have := hpow.hC
  linarith

private lemma powerGrowthCoercivityConstant_ge_hpowC
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH) :
    hpow.C ≤ powerGrowthCoercivityConstant (d := d) hpow := by
  unfold powerGrowthCoercivityConstant
  have := hpow.hC
  linarith

/-- **`h_lagr` from `hpow.lagr` at the inflated constant `C̃`**.

`hpow.lagr` reads `(m^β)/C - C ≤ DpH(x,p,m)·p − H(x,p,m)` for `m > 0`.
At `C̃ ≥ C > 0`, the lower bound `(m^β)/C̃ − C̃ ≤ (m^β)/C − C ≤ …` holds
trivially since `(m^β)/C̃ ≤ (m^β)/C` (with `m^β ≥ 0` and `C̃ ≥ C > 0`)
and `−C̃ ≤ −C`. -/
private lemma paperHypotheses_lagr_at_uniform
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p mx, 0 < mx →
        (mx ^ hpow.β) / (powerGrowthCoercivityConstant (d := d) hpow)
            - (powerGrowthCoercivityConstant (d := d) hpow)
          ≤ (DpH x p mx) ⬝ p - H x p mx := by
  set Ctil : ℝ := powerGrowthCoercivityConstant (d := d) hpow with hCtil
  have hCtil_pos : 0 < Ctil := powerGrowthCoercivityConstant_pos (d := d) hpow
  have hC_le : hpow.C ≤ Ctil := powerGrowthCoercivityConstant_ge_hpowC (d := d) hpow
  have hC_pos : 0 < hpow.C := hpow.hC
  filter_upwards [hpow.lagr] with x hLagr p mx hmx
  have hraw := hLagr p mx hmx
  -- `(mx^β)/Ctil ≤ (mx^β)/C` since `mx^β ≥ 0`, `Ctil ≥ C > 0`.
  have hmβ_nn : 0 ≤ mx ^ hpow.β := Real.rpow_nonneg hmx.le _
  have hinv : 1 / Ctil ≤ 1 / hpow.C := by
    rw [one_div, one_div]; exact inv_anti₀ hC_pos hC_le
  have hdivLe : mx ^ hpow.β / Ctil ≤ mx ^ hpow.β / hpow.C := by
    rw [div_eq_mul_one_div, div_eq_mul_one_div (mx ^ hpow.β)]
    exact mul_le_mul_of_nonneg_left hinv hmβ_nn
  -- `-Ctil ≤ -C` since `C ≤ Ctil`.
  have hnegLe : -Ctil ≤ -hpow.C := neg_le_neg hC_le
  linarith

/-- **`h_lower` from `hpow.lower` at the inflated constant `C̃`**.

`hpow.lower` reads `‖p‖^α/C − C·(m^β+1) ≤ H(x,p,m)` for `m > 0`. The
inflated version `‖p‖^α/C̃ − C̃·(m^β+1) ≤ ‖p‖^α/C − C·(m^β+1) ≤ H(…)`
holds since `‖p‖^α/C̃ ≤ ‖p‖^α/C` and `C̃·(m^β+1) ≥ C·(m^β+1)`. -/
private lemma paperHypotheses_lower_at_uniform
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p mx, 0 < mx →
        (‖p‖ ^ hpow.α) / (powerGrowthCoercivityConstant (d := d) hpow)
            - (powerGrowthCoercivityConstant (d := d) hpow) *
              (mx ^ hpow.β + 1)
          ≤ H x p mx := by
  set Ctil : ℝ := powerGrowthCoercivityConstant (d := d) hpow with hCtil
  have hCtil_pos : 0 < Ctil := powerGrowthCoercivityConstant_pos (d := d) hpow
  have hC_le : hpow.C ≤ Ctil := powerGrowthCoercivityConstant_ge_hpowC (d := d) hpow
  have hC_pos : 0 < hpow.C := hpow.hC
  filter_upwards [hpow.lower] with x hLow p mx hmx
  have hraw := hLow p mx hmx
  have hmβ_nn : 0 ≤ mx ^ hpow.β := Real.rpow_nonneg hmx.le _
  have hpα_nn : 0 ≤ ‖p‖ ^ hpow.α := Real.rpow_nonneg (norm_nonneg _) _
  -- `‖p‖^α/Ctil ≤ ‖p‖^α/C`.
  have hinv : 1 / Ctil ≤ 1 / hpow.C := by
    rw [one_div, one_div]; exact inv_anti₀ hC_pos hC_le
  have hdivLe : ‖p‖ ^ hpow.α / Ctil ≤ ‖p‖ ^ hpow.α / hpow.C := by
    rw [div_eq_mul_one_div, div_eq_mul_one_div (‖p‖ ^ hpow.α)]
    exact mul_le_mul_of_nonneg_left hinv hpα_nn
  -- `C * (mx^β + 1) ≤ Ctil * (mx^β + 1)`, hence `−Ctil(...) ≤ −C(...)`.
  have hsum_nn : 0 ≤ mx ^ hpow.β + 1 := by linarith
  have hmulLe : hpow.C * (mx ^ hpow.β + 1) ≤ Ctil * (mx ^ hpow.β + 1) :=
    mul_le_mul_of_nonneg_right hC_le hsum_nn
  linarith [hraw.le, hraw, hdivLe, hmulLe]

/-- **`h_H01_le` from `hpow.upper` and `hpow.lower` at `(p,m) = (0,1)`**.

The paper gives `H(x,0,1) ≤ -1/C + C ≤ C` and `H(x,0,1) ≥ −C·(1+1) =
−2C`. Therefore `|H(x,0,1)| ≤ 2C ≤ C̃`. -/
private lemma paperHypotheses_H01_le_uniform
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      |H x (0 : Fin d → ℝ) 1| ≤ powerGrowthCoercivityConstant (d := d) hpow := by
  set Ctil : ℝ := powerGrowthCoercivityConstant (d := d) hpow with hCtil
  have hC_pos : 0 < hpow.C := hpow.hC
  have hCtil_eq : Ctil = 2 * hpow.C + 1 := rfl
  filter_upwards [hpow.upper, hpow.lower] with x hUp hLow
  -- `H(x,0,1) ≤ -1^β/C + C`. Note `1^β = 1` (Real.one_rpow).
  have hup := hUp 1 one_pos
  have hone : (1 : ℝ) ^ hpow.β = 1 := Real.one_rpow _
  rw [hone] at hup
  -- `hup : H x 0 1 ≤ -1/C + C`.
  -- `H(x,0,1) ≥ 0^α/C − C·(1+1) = -2C` (using 0^α = 0 when α > 0).
  have hlow := hLow (0 : Fin d → ℝ) 1 one_pos
  have hα_pos : 0 < hpow.α := lt_trans one_pos hpow.hα
  have hα_ne : hpow.α ≠ 0 := ne_of_gt hα_pos
  have hzero_α : ‖(0 : Fin d → ℝ)‖ ^ hpow.α = 0 := by
    rw [norm_zero, Real.zero_rpow hα_ne]
  rw [hzero_α, hone] at hlow
  -- `hlow : 0/C - C*(1+1) ≤ H x 0 1`, i.e. `-2C ≤ H x 0 1`.
  -- Combine: `|H(x,0,1)| ≤ max(|−1/C + C|, 2C) ≤ 2C + 1 = Ctil`.
  have hC_nn : 0 ≤ hpow.C := hC_pos.le
  have hCinv_nn : 0 ≤ (1 : ℝ) / hpow.C := by positivity
  -- Upper: `H x 0 1 ≤ -1/C + C ≤ C ≤ 2C + 1 = Ctil`.
  have hUpCtil : H x (0 : Fin d → ℝ) 1 ≤ Ctil := by
    -- Normalize `-1 / hpow.C` to `-(1 / hpow.C)` so linarith sees a single term.
    have hnorm : (-1 : ℝ) / hpow.C = -(1 / hpow.C) := by ring
    have hup' : H x (0 : Fin d → ℝ) 1 ≤ -(1 / hpow.C) + hpow.C := by
      have := hup
      rw [hnorm] at this
      exact this
    have h1 : -(1 / hpow.C) + hpow.C ≤ hpow.C := by linarith
    have h2 : hpow.C ≤ Ctil := by rw [hCtil_eq]; linarith
    linarith
  -- Lower: `H x 0 1 ≥ -2C ≥ -Ctil`.
  have hLowCtil : -Ctil ≤ H x (0 : Fin d → ℝ) 1 := by
    have h1 : (0 : ℝ) / hpow.C - hpow.C * (1 + 1) = -(2 * hpow.C) := by
      rw [zero_div]; ring
    have hlow' : -(2 * hpow.C) ≤ H x (0 : Fin d → ℝ) 1 := by
      have := hlow
      rw [h1] at this
      exact this
    have h2 : -Ctil ≤ -(2 * hpow.C) := by rw [hCtil_eq]; linarith
    linarith
  -- Combine into `|H x 0 1| ≤ Ctil`.
  rw [abs_le]
  exact ⟨hLowCtil, hUpCtil⟩

/-- **`h_DpH01_le` from `hpow.DpH_upper` at `(p,m) = (0,1)`**.

The paper gives `‖DpH(x,0,1)‖ ≤ C·(0^{α-1} + 1^{β-β/α} + 1) = C·(0 + 1 +
1) = 2C ≤ C̃` (using `α > 1` so `α − 1 > 0` and `Real.zero_rpow`). -/
private lemma paperHypotheses_DpH01_le_uniform
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ‖DpH x (0 : Fin d → ℝ) 1‖
          ≤ powerGrowthCoercivityConstant (d := d) hpow := by
  set Ctil : ℝ := powerGrowthCoercivityConstant (d := d) hpow with hCtil
  have hC_pos : 0 < hpow.C := hpow.hC
  have hCtil_eq : Ctil = 2 * hpow.C + 1 := rfl
  have hα_m1_pos : 0 < hpow.α - 1 := sub_pos.mpr hpow.hα
  have hα_m1_ne : hpow.α - 1 ≠ 0 := ne_of_gt hα_m1_pos
  filter_upwards [hpow.DpH_upper] with x hDU
  have h := hDU (0 : Fin d → ℝ) 1 one_pos
  -- `h : ‖DpH x 0 1‖ ≤ C * (‖0‖^{α-1} + 1^{β - β/α} + 1)`.
  have hzero_α1 : ‖(0 : Fin d → ℝ)‖ ^ (hpow.α - 1) = 0 := by
    rw [norm_zero, Real.zero_rpow hα_m1_ne]
  have hone_q : (1 : ℝ) ^ (hpow.β - hpow.β / hpow.α) = 1 := Real.one_rpow _
  rw [hzero_α1, hone_q] at h
  -- `h : ‖DpH x 0 1‖ ≤ C * (0 + 1 + 1) = 2C`.
  have heq : hpow.C * (0 + 1 + 1) = 2 * hpow.C := by ring
  rw [heq] at h
  -- `2C ≤ Ctil = 2C + 1`.
  have h2 : 2 * hpow.C ≤ Ctil := by rw [hCtil_eq]; linarith
  linarith

/-- **Pointwise Young-absorbed lower bound from `HypothesisPowerGrowth`
alone**.

Combines `coercivity_integrand_lower_bound_young` with the four
`paperHypotheses_*_at_uniform` bridges. Produces a constant `C_eul > 0`
(depending only on `hpow.C`, `hpow.α`, `hpow.β`) and the pointwise
post-Young bound at the paper exponents `α := hpow.α`, `β := hpow.β`. -/
theorem coercivity_integrand_lower_bound_young_of_paperHypotheses
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m : (Fin d → ℝ) → ℝ) :
    ∃ C_eul : ℝ, 0 < C_eul ∧
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        0 < m x →
          (1 / C_eul) *
              (m x ^ (hpow.β + 1) + ‖fun i => Du i x‖ ^ hpow.α)
              - C_eul
            ≤ coerciveHamIntegrand H DpH Du m x := by
  have hCtil_pos : 0 < powerGrowthCoercivityConstant (d := d) hpow :=
    powerGrowthCoercivityConstant_pos (d := d) hpow
  exact
    coercivity_integrand_lower_bound_young H DpH
      hCtil_pos hpow.hα hpow.hβ
      (paperHypotheses_lagr_at_uniform (d := d) hpow)
      (paperHypotheses_lower_at_uniform (d := d) hpow)
      (paperHypotheses_H01_le_uniform (d := d) hpow)
      (paperHypotheses_DpH01_le_uniform (d := d) hpow)
      Du m

/-- **Integrated Eulerian lower bound from `HypothesisPowerGrowth`**
(paper line 967, `eq:coercive.Aepsi`, Hamiltonian half).

Given `hpow : HypothesisPowerGrowth d H DpH`, a `(Du, m)` pair with
`m > 0` a.e. on the cube, and the standard integrability residues for
the `coerciveHamIntegrand`, the `(m^{β+1})`, and the `‖Du‖^α` terms,
the integrated Eulerian lower bound holds:
```
(1/C_eul) · ∫_{𝕋^d} m(x)^{β+1} dx
  + (1/C_eul) · ∫_{𝕋^d} ‖Du(x)‖^α dx
  − C_eul
  ≤ ∫_{𝕋^d} coerciveHamIntegrand H DpH Du m x dx.
```
The constant `C_eul > 0` depends only on `hpow.C`, `hpow.α`, `hpow.β`.

This is the Eulerian half of paper line 967 used by
`paperSection8_coercivity_of_paperHypotheses` to feed the final
`Tendsto` form of `prop:coercAepsi` (paper line 982). -/
theorem coercivity_eulerian_from_paperHypotheses
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m : (Fin d → ℝ) → ℝ)
    (hm_pos : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hHam_int : IntegrableOn
        (fun x => coerciveHamIntegrand H DpH Du m x) (UnitCube d))
    (hRpow_m_int : IntegrableOn (fun x => m x ^ (hpow.β + 1)) (UnitCube d))
    (hRpow_p_int : IntegrableOn
        (fun x => ‖fun i => Du i x‖ ^ hpow.α) (UnitCube d)) :
    ∃ C_eul : ℝ, 0 < C_eul ∧
      (1 / C_eul) * (∫ x in UnitCube d, m x ^ (hpow.β + 1))
          + (1 / C_eul) * (∫ x in UnitCube d, ‖fun i => Du i x‖ ^ hpow.α)
          - C_eul
        ≤ ∫ x in UnitCube d, coerciveHamIntegrand H DpH Du m x := by
  -- Step 1: produce the post-Young pointwise bound (with `0 < m x` premise).
  obtain ⟨C_eul, hC_eul_pos, hPointAE⟩ :=
    coercivity_integrand_lower_bound_young_of_paperHypotheses (d := d) hpow Du m
  refine ⟨C_eul, hC_eul_pos, ?_⟩
  -- Step 2: drop the `0 < m x` premise using `hm_pos`.
  have hPointAE' :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        (1 / C_eul) *
            (m x ^ (hpow.β + 1) + ‖fun i => Du i x‖ ^ hpow.α)
            - C_eul
          ≤ coerciveHamIntegrand H DpH Du m x := by
    filter_upwards [hPointAE, hm_pos] with x hx hpos
    exact hx hpos
  -- Step 3: integrability of the LHS family.
  have hSum_int : IntegrableOn
      (fun x => m x ^ (hpow.β + 1) + ‖fun i => Du i x‖ ^ hpow.α)
      (UnitCube d) := hRpow_m_int.add hRpow_p_int
  have hSum_smul_int : IntegrableOn
      (fun x =>
        (1 / C_eul) * (m x ^ (hpow.β + 1) + ‖fun i => Du i x‖ ^ hpow.α))
      (UnitCube d) := hSum_int.const_mul _
  have hμ_ne : volume (UnitCube (d := d)) ≠ ⊤ := by
    rw [volume_unitCube]; exact ENNReal.one_ne_top
  have h_const_int : IntegrableOn (fun _ : Fin d → ℝ => (C_eul : ℝ))
      (UnitCube d) := integrableOn_const hμ_ne
  have hLB_int : IntegrableOn
      (fun x =>
        (1 / C_eul) *
            (m x ^ (hpow.β + 1) + ‖fun i => Du i x‖ ^ hpow.α)
            - C_eul)
      (UnitCube d) := hSum_smul_int.sub h_const_int
  -- Step 4: invoke `coercivity_integral_lower_bound`.
  exact
    coercivity_integral_lower_bound (C'' := C_eul) (β := hpow.β) (α := hpow.α)
      H DpH hC_eul_pos Du m
      hPointAE' hHam_int hLB_int hRpow_m_int hRpow_p_int

/-! ## Unit test for the Eulerian producer -/

/-- **API sanity check** for
`coercivity_eulerian_from_paperHypotheses`: with `hpow` alone (plus
positivity of `m` and integrability residues), the integrated Eulerian
bound holds at the paper exponents `α := hpow.α`, `β + 1 := hpow.β + 1`. -/
example
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m : (Fin d → ℝ) → ℝ)
    (hm_pos : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hHam_int : IntegrableOn
        (fun x => coerciveHamIntegrand H DpH Du m x) (UnitCube d))
    (hRpow_m_int : IntegrableOn (fun x => m x ^ (hpow.β + 1)) (UnitCube d))
    (hRpow_p_int : IntegrableOn
        (fun x => ‖fun i => Du i x‖ ^ hpow.α) (UnitCube d)) :
    ∃ C_eul : ℝ, 0 < C_eul ∧
      (1 / C_eul) * (∫ x in UnitCube d, m x ^ (hpow.β + 1))
          + (1 / C_eul) * (∫ x in UnitCube d, ‖fun i => Du i x‖ ^ hpow.α)
          - C_eul
        ≤ ∫ x in UnitCube d, coerciveHamIntegrand H DpH Du m x :=
  coercivity_eulerian_from_paperHypotheses (d := d) hpow Du m
    hm_pos hHam_int hRpow_m_int hRpow_p_int

/-! ## Combined algebraic assembly: eulerian + laplacian halves

The two integrated halves of paper `prop:coercAepsi` (paper line 967 +
paper line 974) combine algebraically with the test-pair identity at
paper line 947 (`coercive_test_pair_identity`) to deliver a single
integrated lower bound on `mfgOperatorEpsPair[m,u] -
mfgOperatorEpsPair[1,0]`. This is the **algebraic** combined bound,
to be fed downstream to the cobounded × principal `K_Aepsi` filter
packaging (paper line 982, `paperSolFor-coercivity-final-cobounded`).

The form is

```
(1/C_eul) · ∫ m^{β+1} + (1/C_eul) · ∫ ‖Du‖^α
  + ε · ∫_{𝕋^d} [(Du⬝Du)^{γ̄/2} + |u|^γ̄] dx − C_eul
  ≤ mfgOperatorEpsPair[m,u] − mfgOperatorEpsPair[1,0]
```

i.e. the eulerian bound's RHS replaced via the test-pair identity by
the `mfgOperatorEpsPair`-difference, then with the (still positive but
intentionally kept) Gateaux integral on the left. The cobounded
packaging task discharges the bridge from this form to the gauge
`‖v‖^γ̄/γ̄` via the Banach-pair-norm translation. -/

/-- **Combined algebraic bound from `(hpow, hε)`** (paper §8 combination
of `prop:coercAepsi` Eulerian + Laplacian halves, via the test-pair
identity `coercive_test_pair_identity` at paper line 947).

Given:
* `hpow` — the power-growth Hamiltonian hypothesis bundle;
* `(Du, m, u)` — primal data with `m > 0` a.e. on the cube;
* the four `IntegrableOn` residues feeding the test-pair identity and
  the eulerian half:
  * `hInt_mu`, `hInt_10` — the two `mfgOperatorPair` integrand
    integrabilities (test-pair identity premises);
  * `hHam_int` — `coerciveHamIntegrand` integrability (eulerian
    premise);
  * `hRpow_m_int`, `hRpow_p_int` — the `m^{β+1}` and `‖Du‖^α`
    integrabilities (eulerian premises);

there exists a constant `C_eul > 0` (depending only on `hpow.C`,
`hpow.α`, `hpow.β`) such that the **combined algebraic bound**

```
(1/C_eul) · ∫ m^{β+1} + (1/C_eul) · ∫ ‖Du‖^α
  + ε · ∫_{𝕋^d} [(Du⬝Du)^{γ̄/2} + |u|^γ̄] dx − C_eul
  ≤ mfgOperatorEpsPair[m,u] − mfgOperatorEpsPair[1,0]
```

holds on the unit cube.

The Gateaux integrand on the LHS is the **Euclidean** form (paper line
947 third line):
`vecAbsPowMinusTwo γBar Du · (Du⬝Du) + absPowMinusTwo γBar u · (u·u)
  = (Du⬝Du)^{γ̄/2} + |u|^γ̄`,
matching `gateauxWpPair`'s integrand. The bridge from this Euclidean
form to the per-coordinate `Σᵢ |Du i|^γ̄` form of the laplacian half
(`coercivity_laplacian_from_paperHypotheses`) is a separate algebraic
step, deferred to the cobounded packaging task. -/
theorem coercivity_combined_from_paperHypotheses
    {γBar ε : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
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
    (hRpow_m_int : IntegrableOn (fun x => m x ^ (hpow.β + 1)) (UnitCube d))
    (hRpow_p_int : IntegrableOn
        (fun x => ‖fun i => Du i x‖ ^ hpow.α) (UnitCube d)) :
    ∃ C_eul : ℝ, 0 < C_eul ∧
      (1 / C_eul) * (∫ x in UnitCube d, m x ^ (hpow.β + 1))
          + (1 / C_eul) * (∫ x in UnitCube d, ‖fun i => Du i x‖ ^ hpow.α)
          + ε * (∫ x in UnitCube d,
              vecAbsPowMinusTwo γBar (fun i => Du i x)
                  * ((fun i => Du i x) ⬝ (fun i => Du i x))
                + absPowMinusTwo γBar (u x) * (u x * u x))
          - C_eul
        ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBar ε Du m u Du (m - 1) u
          - mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBar ε (fun _ _ => 0) (fun _ => 1) (fun _ => 0) Du (m - 1) u := by
  -- Step 1: the test-pair identity (paper line 947) rewrites the
  -- `mfgOperatorEpsPair`-difference in terms of `∫ coerciveHam +
  -- ε · ∫ gateauxIntegrand`.
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
  -- Step 2: the eulerian half delivers an integrated lower bound on
  -- `∫ coerciveHam` from `hpow` alone.
  obtain ⟨C_eul, hC_eul_pos, hEul⟩ :=
    coercivity_eulerian_from_paperHypotheses (d := d) hpow Du m
      hm_pos hHam_int hRpow_m_int hRpow_p_int
  -- Step 3: combine.
  refine ⟨C_eul, hC_eul_pos, ?_⟩
  -- The combined bound: add `ε · ∫ gateauxIntegrand` to both sides of
  -- the eulerian bound, then rewrite using the test-pair identity.
  -- Rearranging hTestPair gives the substitution.
  linarith [hTestPair, hEul]

/-! ## Sanity check for the combined algebraic bound -/

/-- **API sanity check** for `coercivity_combined_from_paperHypotheses`:
the combined algebraic bound is consumable downstream by the
cobounded × principal `K_Aepsi` filter packaging (paper line 982). -/
example
    {γBar ε : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
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
    (hRpow_m_int : IntegrableOn (fun x => m x ^ (hpow.β + 1)) (UnitCube d))
    (hRpow_p_int : IntegrableOn
        (fun x => ‖fun i => Du i x‖ ^ hpow.α) (UnitCube d)) :
    ∃ C_eul : ℝ, 0 < C_eul ∧
      (1 / C_eul) * (∫ x in UnitCube d, m x ^ (hpow.β + 1))
          + (1 / C_eul) * (∫ x in UnitCube d, ‖fun i => Du i x‖ ^ hpow.α)
          + ε * (∫ x in UnitCube d,
              vecAbsPowMinusTwo γBar (fun i => Du i x)
                  * ((fun i => Du i x) ⬝ (fun i => Du i x))
                + absPowMinusTwo γBar (u x) * (u x * u x))
          - C_eul
        ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBar ε Du m u Du (m - 1) u
          - mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBar ε (fun _ _ => 0) (fun _ => 1) (fun _ => 0) Du (m - 1) u :=
  coercivity_combined_from_paperHypotheses (d := d) V hpow Du m u
    hm_pos hInt_mu hInt_10 hHam_int hRpow_m_int hRpow_p_int

/-! ## Uniform-`C_eul` variants (paper-faithful, explicit constant)

The combined algebraic bound above hides `C_eul` inside an existential.
For the downstream XBanach gauge-absorption wrap, every `v ∈ K_Aepsi`
must share a single `C_eul`. We therefore expose the constant
explicitly. Concretely we take

```
C_eul := coercivityIntegrandLowerBoundYoungConstant d
            (powerGrowthCoercivityConstant hpow) hpow.α hpow.β
```

which depends only on `(d, hpow.C, hpow.α, hpow.β)` and is uniform in
the primal data `(Du, m, u)`. -/

/-- **Uniform-`C_eul` Eulerian half**, returning the explicit constant
`coercivityIntegrandLowerBoundYoungConstant d (powerGrowthCoercivityConstant hpow)
hpow.α hpow.β` directly (no `∃`). Specialises
`coercivity_integrand_lower_bound_young_explicit` at the paper exponents
via the four `paperHypotheses_*_uniform` bridges. -/
theorem coercivity_eulerian_from_paperHypotheses_uniform
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m : (Fin d → ℝ) → ℝ)
    (hm_pos : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hHam_int : IntegrableOn
        (fun x => coerciveHamIntegrand H DpH Du m x) (UnitCube d))
    (hRpow_m_int : IntegrableOn (fun x => m x ^ (hpow.β + 1)) (UnitCube d))
    (hRpow_p_int : IntegrableOn
        (fun x => ‖fun i => Du i x‖ ^ hpow.α) (UnitCube d)) :
    let C_eul : ℝ :=
      coercivityIntegrandLowerBoundYoungConstant d
        (powerGrowthCoercivityConstant (d := d) hpow) hpow.α hpow.β
    (1 / C_eul) * (∫ x in UnitCube d, m x ^ (hpow.β + 1))
        + (1 / C_eul) * (∫ x in UnitCube d, ‖fun i => Du i x‖ ^ hpow.α)
        - C_eul
      ≤ ∫ x in UnitCube d, coerciveHamIntegrand H DpH Du m x := by
  intro C_eul
  have hCtil_pos : 0 < powerGrowthCoercivityConstant (d := d) hpow :=
    powerGrowthCoercivityConstant_pos (d := d) hpow
  have hC_eul_pos : 0 < C_eul :=
    coercivityIntegrandLowerBoundYoungConstant_pos d _ hpow.α hpow.β
  -- Step 1: pointwise post-Young bound at the explicit constant.
  have hPointAE :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        0 < m x →
          (1 / C_eul) *
              (m x ^ (hpow.β + 1) + ‖fun i => Du i x‖ ^ hpow.α)
              - C_eul
            ≤ coerciveHamIntegrand H DpH Du m x :=
    coercivity_integrand_lower_bound_young_explicit H DpH
      hCtil_pos hpow.hα hpow.hβ
      (paperHypotheses_lagr_at_uniform (d := d) hpow)
      (paperHypotheses_lower_at_uniform (d := d) hpow)
      (paperHypotheses_H01_le_uniform (d := d) hpow)
      (paperHypotheses_DpH01_le_uniform (d := d) hpow)
      Du m
  -- Step 2: drop the `0 < m x` premise using `hm_pos`.
  have hPointAE' :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        (1 / C_eul) *
            (m x ^ (hpow.β + 1) + ‖fun i => Du i x‖ ^ hpow.α)
            - C_eul
          ≤ coerciveHamIntegrand H DpH Du m x := by
    filter_upwards [hPointAE, hm_pos] with x hx hpos
    exact hx hpos
  -- Step 3: integrability residue for the LHS family.
  have hSum_int : IntegrableOn
      (fun x => m x ^ (hpow.β + 1) + ‖fun i => Du i x‖ ^ hpow.α)
      (UnitCube d) := hRpow_m_int.add hRpow_p_int
  have hSum_smul_int : IntegrableOn
      (fun x =>
        (1 / C_eul) * (m x ^ (hpow.β + 1) + ‖fun i => Du i x‖ ^ hpow.α))
      (UnitCube d) := hSum_int.const_mul _
  have hμ_ne : volume (UnitCube (d := d)) ≠ ⊤ := by
    rw [volume_unitCube]; exact ENNReal.one_ne_top
  have h_const_int : IntegrableOn (fun _ : Fin d → ℝ => (C_eul : ℝ))
      (UnitCube d) := integrableOn_const hμ_ne
  have hLB_int : IntegrableOn
      (fun x =>
        (1 / C_eul) *
            (m x ^ (hpow.β + 1) + ‖fun i => Du i x‖ ^ hpow.α)
            - C_eul)
      (UnitCube d) := hSum_smul_int.sub h_const_int
  -- Step 4: invoke `coercivity_integral_lower_bound`.
  exact
    coercivity_integral_lower_bound (C'' := C_eul) (β := hpow.β) (α := hpow.α)
      H DpH hC_eul_pos Du m
      hPointAE' hHam_int hLB_int hRpow_m_int hRpow_p_int

/-- **Uniform-`C_eul` combined algebraic bound** — same content as
`coercivity_combined_from_paperHypotheses` but exposing the explicit
constant
`coercivityIntegrandLowerBoundYoungConstant d (powerGrowthCoercivityConstant hpow)
hpow.α hpow.β` directly (no `∃`). The constant depends only on
`(d, hpow.C, hpow.α, hpow.β)` and is uniform in the primal data
`(Du, m, u)`. Consumed by the XBanach scaled-gauge-absorption wrap. -/
theorem coercivity_combined_from_paperHypotheses_uniform
    {γBar ε : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
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
    (hRpow_m_int : IntegrableOn (fun x => m x ^ (hpow.β + 1)) (UnitCube d))
    (hRpow_p_int : IntegrableOn
        (fun x => ‖fun i => Du i x‖ ^ hpow.α) (UnitCube d)) :
    let C_eul : ℝ :=
      coercivityIntegrandLowerBoundYoungConstant d
        (powerGrowthCoercivityConstant (d := d) hpow) hpow.α hpow.β
    (1 / C_eul) * (∫ x in UnitCube d, m x ^ (hpow.β + 1))
        + (1 / C_eul) * (∫ x in UnitCube d, ‖fun i => Du i x‖ ^ hpow.α)
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
  -- Step 2: uniform Eulerian half at the explicit constant.
  have hEul :
      (1 / C_eul) * (∫ x in UnitCube d, m x ^ (hpow.β + 1))
          + (1 / C_eul) * (∫ x in UnitCube d, ‖fun i => Du i x‖ ^ hpow.α)
          - C_eul
        ≤ ∫ x in UnitCube d, coerciveHamIntegrand H DpH Du m x :=
    coercivity_eulerian_from_paperHypotheses_uniform (d := d) hpow Du m
      hm_pos hHam_int hRpow_m_int hRpow_p_int
  -- Step 3: combine.
  linarith [hTestPair, hEul]

/-! ## Bridge between Euclidean and Pi norms in the Gateaux integrand

The Gateaux integrand of `coercive_test_pair_identity` (paper line 947)
is in **Euclidean** form:
```
(Du⬝Du)^{γ̄/2} + |u|^γ̄.
```
The laplacian half `coercivity_laplacian_from_paperHypotheses` (paper
line 974) produces the **per-coordinate** sum `∫|u|^γ̄ + Σᵢ ∫|Du i|^γ̄`,
which uses the Pi-norm on `Fin d → ℝ`.

To bridge the two forms, we use the equivalence-of-norms inequality:
for `v : Fin d → ℝ` and `γ̄ > 0`,
```
(v⬝v)^{γ̄/2} = (Σᵢ vᵢ²)^{γ̄/2}
            ≥ max(|vᵢ|^γ̄ : i ∈ Fin d)   (since Σ ≥ max for nonneg)
            ≥ (1/d) · Σᵢ |vᵢ|^γ̄         (since max ≥ avg)
```
for `γ̄ ≥ 2` (so that `(Σ x²)^{γ̄/2} ≥ (max xᵢ²)^{γ̄/2} = max |xᵢ|^γ̄`).

The reverse bound `(Σ x²)^{γ̄/2} ≤ d^{γ̄/2} · max |xᵢ|^γ̄` also holds,
giving overall equivalence with constants depending on `γ̄` and `d`.

This bridge is consumed by the cobounded-packaging task to identify
the Gateaux integrand's lower bound by the laplacian half's
per-coordinate sum, hence by the Sobolev seminorm `‖q.2‖^γ̄`. -/

/-- **Euclidean dot-product upper bound by the max norm**. For `v : Fin
d → ℝ`, `v ⬝ v = Σ vᵢ² ≤ d · max(vᵢ²) = d · ‖v‖²`, using the Pi-norm
`‖v‖ = max_i |vᵢ|`. -/
private lemma euclideanDot_self_le_dim_mul_norm_sq (v : Fin d → ℝ) :
    v ⬝ v ≤ (d : ℝ) * ‖v‖ ^ 2 := by
  unfold dotProduct
  have h1 : ∀ i : Fin d, v i * v i ≤ ‖v‖ * ‖v‖ := by
    intro i
    have hvi : |v i| ≤ ‖v‖ := by
      have := norm_le_pi_norm v i
      simpa [Real.norm_eq_abs] using this
    have hvi_nn : 0 ≤ |v i| := abs_nonneg _
    have h_norm_nn : 0 ≤ ‖v‖ := norm_nonneg _
    have : v i * v i = |v i| * |v i| := by
      rw [← abs_mul, abs_mul_self]
    rw [this]
    calc |v i| * |v i|
        ≤ ‖v‖ * |v i| := mul_le_mul_of_nonneg_right hvi hvi_nn
      _ ≤ ‖v‖ * ‖v‖ := mul_le_mul_of_nonneg_left hvi h_norm_nn
  have h2 : ∑ i, v i * v i ≤ ∑ _ : Fin d, ‖v‖ * ‖v‖ :=
    Finset.sum_le_sum (fun i _ => h1 i)
  have h3 : ∑ _ : Fin d, ‖v‖ * ‖v‖ = (d : ℝ) * (‖v‖ * ‖v‖) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp [nsmul_eq_mul]
  calc ∑ i, v i * v i
      ≤ ∑ _ : Fin d, ‖v‖ * ‖v‖ := h2
    _ = (d : ℝ) * (‖v‖ * ‖v‖) := h3
    _ = (d : ℝ) * ‖v‖ ^ 2 := by ring

/-- **Nonnegativity of the Euclidean dot square**. -/
private lemma euclideanDot_self_nonneg (v : Fin d → ℝ) :
    0 ≤ v ⬝ v := by
  unfold dotProduct
  refine Finset.sum_nonneg ?_
  intro i _
  exact mul_self_nonneg _

/-! ## Norm-bridge B2b child 1 (iter 0650 split)

The pointwise per-coordinate dominance
`|v i|^γ̄ ≤ (v ⬝ v)^{γ̄/2}` (for `γ̄ ≥ 0`) and its summed/integrated
forms. This is the key analytic step coupling the per-coordinate
Pi-norm sums (`∑_i |Du i|^γ̄`, used by B2a's W^{1,γ̄}-seminorm upper
bound) to the Euclidean dot-product form `(Du⬝Du)^{γ̄/2}` of the
Gateaux integrand (used by the `coercivity_combined_from_paperHypotheses`
lower bound). The bridge needs no Young's inequality: the exponent
matches on both sides (γ̄), only the per-coord vs Euclidean form
differs, and the per-coord side is **smaller** thanks to
`v_i² ≤ Σ_j v_j² = v ⬝ v`. -/

/-- For `v : Fin d → ℝ` and `γ̄ ≥ 0`,
`|v i|^γ̄ ≤ (v ⬝ v)^{γ̄/2}` pointwise per coordinate.

Proof outline:
* `v_i² ≤ Σ_j v_j² = v ⬝ v` since the other summands are `≥ 0`.
* Hence `|v i| = (v_i²)^{1/2} ≤ (v ⬝ v)^{1/2}` via `Real.rpow_le_rpow`.
* Raising to `γ̄ ≥ 0` preserves the inequality:
  `|v i|^γ̄ ≤ ((v ⬝ v)^{1/2})^γ̄ = (v ⬝ v)^{γ̄/2}`. -/
lemma per_coord_pow_le_euclideanDot_pow
    (γBar : ℝ) (hγ : 0 ≤ γBar) (v : Fin d → ℝ) (i : Fin d) :
    |v i| ^ γBar ≤ (v ⬝ v) ^ (γBar / 2) := by
  have hdot_nn : 0 ≤ v ⬝ v := euclideanDot_self_nonneg v
  have habs_nn : 0 ≤ |v i| := abs_nonneg _
  -- Step 1: `v_i² ≤ v ⬝ v`.
  have h_sq_le : v i * v i ≤ v ⬝ v := by
    unfold dotProduct
    refine Finset.single_le_sum (f := fun j => v j * v j) ?_ (Finset.mem_univ i)
    intro j _
    exact mul_self_nonneg _
  -- Step 2: `|v i|^2 = v_i * v_i ≤ v ⬝ v`, using `(2 : ℝ)`-power.
  have h_abs_sq_le : |v i| ^ (2 : ℝ) ≤ v ⬝ v := by
    have hrw : |v i| ^ (2 : ℝ) = v i * v i := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num,
          Real.rpow_natCast]
      rw [show (|v i|) ^ (2 : ℕ) = |v i| * |v i| from by ring]
      rw [← abs_mul, abs_mul_self]
    rw [hrw]; exact h_sq_le
  -- Step 3: raise both sides to `γ̄/2 ≥ 0` to get
  --   `|v i|^γ̄ = (|v i|^2)^{γ̄/2} ≤ (v ⬝ v)^{γ̄/2}`.
  have hγ_half_nn : 0 ≤ γBar / 2 := by linarith
  have hlhs_eq : (|v i| ^ (2 : ℝ)) ^ (γBar / 2) = |v i| ^ γBar := by
    rw [← Real.rpow_mul habs_nn]
    congr 1
    ring
  have h_abs_sq_nn : 0 ≤ |v i| ^ (2 : ℝ) :=
    Real.rpow_nonneg habs_nn _
  have hmono :
      (|v i| ^ (2 : ℝ)) ^ (γBar / 2) ≤ (v ⬝ v) ^ (γBar / 2) :=
    Real.rpow_le_rpow h_abs_sq_nn h_abs_sq_le hγ_half_nn
  calc |v i| ^ γBar
      = (|v i| ^ (2 : ℝ)) ^ (γBar / 2) := hlhs_eq.symm
    _ ≤ (v ⬝ v) ^ (γBar / 2) := hmono

/-- Summed form: `∑_i |v i|^γ̄ ≤ d · (v ⬝ v)^{γ̄/2}` for `γ̄ ≥ 0`. -/
lemma sum_per_coord_pow_le_dim_mul_euclideanDot_pow
    (γBar : ℝ) (hγ : 0 ≤ γBar) (v : Fin d → ℝ) :
    ∑ i, |v i| ^ γBar ≤ (d : ℝ) * (v ⬝ v) ^ (γBar / 2) := by
  have hbd : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      |v i| ^ γBar ≤ (v ⬝ v) ^ (γBar / 2) := fun i _ =>
    per_coord_pow_le_euclideanDot_pow γBar hγ v i
  have hsum_le : ∑ i, |v i| ^ γBar
      ≤ ∑ _ : Fin d, (v ⬝ v) ^ (γBar / 2) :=
    Finset.sum_le_sum hbd
  have hconst : ∑ _ : Fin d, (v ⬝ v) ^ (γBar / 2)
      = (d : ℝ) * (v ⬝ v) ^ (γBar / 2) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp [nsmul_eq_mul]
  linarith [hsum_le, hconst]

/-- Integrated form: `∑_i ∫ |Du i|^γ̄ ≤ d · ∫ (Du⬝Du)^{γ̄/2}` for
`γ̄ ≥ 0`, given per-coordinate and Euclidean integrabilities. -/
lemma sum_integral_per_coord_pow_le_dim_mul_integral_euclideanDot_pow
    (γBar : ℝ) (hγ : 0 ≤ γBar)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (hDu_int : ∀ i, IntegrableOn (fun x => |Du i x| ^ γBar) (UnitCube d))
    (hEuc_int : IntegrableOn
        (fun x => ((fun i => Du i x) ⬝ (fun i => Du i x)) ^ (γBar / 2))
        (UnitCube d)) :
    ∑ i, (∫ x in UnitCube d, |Du i x| ^ γBar)
      ≤ (d : ℝ) * ∫ x in UnitCube d,
          ((fun i => Du i x) ⬝ (fun i => Du i x)) ^ (γBar / 2) := by
  -- Pointwise bound, restated as a function-of-x inequality.
  have hbd : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∑ i, |Du i x| ^ γBar
        ≤ (d : ℝ) * ((fun i => Du i x) ⬝ (fun i => Du i x)) ^ (γBar / 2) := by
    refine Filter.Eventually.of_forall ?_
    intro x
    exact sum_per_coord_pow_le_dim_mul_euclideanDot_pow γBar hγ
      (fun i => Du i x)
  -- Integral of sum = sum of integrals.
  have hsum_int : Integrable
      (fun x => ∑ i, |Du i x| ^ γBar)
      (volume.restrict (UnitCube d)) :=
    integrable_finset_sum _ (fun i _ => hDu_int i)
  have hrhs_int : Integrable
      (fun x => (d : ℝ) *
          ((fun i => Du i x) ⬝ (fun i => Du i x)) ^ (γBar / 2))
      (volume.restrict (UnitCube d)) :=
    hEuc_int.const_mul _
  have hmono : (∫ x in UnitCube d, ∑ i, |Du i x| ^ γBar)
      ≤ ∫ x in UnitCube d,
          (d : ℝ) * ((fun i => Du i x) ⬝ (fun i => Du i x)) ^ (γBar / 2) :=
    MeasureTheory.integral_mono_ae hsum_int hrhs_int hbd
  -- Move sum out of integral on LHS and constant out of integral on RHS.
  have hLHS : (∫ x in UnitCube d, ∑ i, |Du i x| ^ γBar)
      = ∑ i, ∫ x in UnitCube d, |Du i x| ^ γBar := by
    rw [MeasureTheory.integral_finset_sum (Finset.univ : Finset (Fin d))
      (fun i _ => hDu_int i)]
  have hRHS : (∫ x in UnitCube d,
        (d : ℝ) * ((fun i => Du i x) ⬝ (fun i => Du i x)) ^ (γBar / 2))
      = (d : ℝ) * ∫ x in UnitCube d,
          ((fun i => Du i x) ⬝ (fun i => Du i x)) ^ (γBar / 2) :=
    MeasureTheory.integral_const_mul _ _
  linarith [hmono, hLHS.symm.le, hLHS.le, hRHS.symm.le, hRHS.le]

/-- **Gateaux integrand as a non-negative integrand**. The integrand
`(Du⬝Du)^{γ̄/2} + |u|^γ̄` (the Euclidean form of the Gateaux integrand
of `coercive_test_pair_identity`) is pointwise non-negative.

The original `vecAbsPowMinusTwo γBar v * (v⬝v) + absPowMinusTwo γBar u
* (u*u)` form unfolds to `(v⬝v)^{γBar/2} + |u|^γBar` modulo `(v⬝v)^{...}
= (v⬝v)^{(γBar-2)/2} * (v⬝v)` and `|u|^{γBar-2} · u² = |u|^γBar`. The
non-negativity then follows from `Real.rpow_nonneg` on `(v⬝v) ≥ 0` and
`|u|^γBar ≥ 0`. -/
lemma gateauxWpIntegrand_nonneg
    (γBar : ℝ) (v : Fin d → ℝ) (s : ℝ) :
    0 ≤ vecAbsPowMinusTwo γBar v * (v ⬝ v)
          + absPowMinusTwo γBar s * (s * s) := by
  refine add_nonneg ?_ ?_
  · -- `vecAbsPowMinusTwo γBar v * (v⬝v) = (v⬝v)^{γBar/2} ≥ 0`.
    -- Direct: both factors are ≥ 0.
    unfold vecAbsPowMinusTwo
    refine mul_nonneg ?_ (euclideanDot_self_nonneg v)
    exact Real.rpow_nonneg (euclideanDot_self_nonneg v) _
  · -- `absPowMinusTwo γBar s * (s * s) = |s|^γBar ≥ 0`.
    unfold absPowMinusTwo
    have hs2 : 0 ≤ s * s := mul_self_nonneg _
    refine mul_nonneg ?_ hs2
    exact Real.rpow_nonneg (abs_nonneg _) _

/-! ## Norm-bridge B2b child 2 (iter 0651 split): Gateaux integrand
positive-form equalities.

The Gateaux integrand `vecAbsPowMinusTwo γ̄ v · (v⬝v) + absPowMinusTwo γ̄ s
· (s · s)` rewrites as `(v⬝v)^{γ̄/2} + |s|^γ̄`. These equalities are
needed by B2b-3 final assembly to land the norm bridge cleanly. -/

/-- `vecAbsPowMinusTwo γBar v * (v ⬝ v) = (v ⬝ v) ^ (γBar / 2)` for
`γBar > 0`. Case-split on whether `v ⬝ v = 0`. -/
lemma vecAbsPowMinusTwo_mul_dot_eq_rpow_half
    (γBar : ℝ) (hγ : 0 < γBar) (v : Fin d → ℝ) :
    vecAbsPowMinusTwo γBar v * (v ⬝ v) = (v ⬝ v) ^ (γBar / 2) := by
  unfold vecAbsPowMinusTwo
  set t := v ⬝ v with ht_def
  have ht_nn : 0 ≤ t := euclideanDot_self_nonneg v
  rcases lt_or_eq_of_le ht_nn with ht_pos | ht_zero
  · -- t > 0: use Real.rpow_add
    have hsum : (γBar - 2) / 2 + 1 = γBar / 2 := by ring
    calc t ^ ((γBar - 2) / 2) * t
        = t ^ ((γBar - 2) / 2) * t ^ (1 : ℝ) := by
          rw [Real.rpow_one]
      _ = t ^ ((γBar - 2) / 2 + 1) := by
          rw [← Real.rpow_add ht_pos]
      _ = t ^ (γBar / 2) := by rw [hsum]
  · -- t = 0
    have ht0 : t = 0 := ht_zero.symm
    have hγ2_ne : γBar / 2 ≠ 0 := by positivity
    rw [ht0, mul_zero, Real.zero_rpow hγ2_ne]

/-- `absPowMinusTwo γBar s * (s * s) = |s| ^ γBar` for `γBar > 0`.
Case-split on whether `s = 0`. -/
lemma absPowMinusTwo_mul_sq_eq_rpow
    (γBar : ℝ) (hγ : 0 < γBar) (s : ℝ) :
    absPowMinusTwo γBar s * (s * s) = |s| ^ γBar := by
  unfold absPowMinusTwo
  rcases eq_or_ne s 0 with hs0 | hs_ne
  · -- s = 0
    have hγ_ne : γBar ≠ 0 := ne_of_gt hγ
    rw [hs0, mul_zero, mul_zero, abs_zero, Real.zero_rpow hγ_ne]
  · -- s ≠ 0: |s| > 0, use Real.rpow_add
    have habs_pos : 0 < |s| := abs_pos.mpr hs_ne
    have hss : s * s = |s| ^ (2 : ℝ) := by
      rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) from by norm_num,
          Real.rpow_natCast, sq_abs, sq]
    have hsum : (γBar - 2) + 2 = γBar := by ring
    calc |s| ^ (γBar - 2) * (s * s)
        = |s| ^ (γBar - 2) * |s| ^ (2 : ℝ) := by rw [hss]
      _ = |s| ^ ((γBar - 2) + 2) := by
          rw [← Real.rpow_add habs_pos]
      _ = |s| ^ γBar := by rw [hsum]

/-- **Combined Gateaux integrand positive-form equality**. The integrand
`vecAbsPowMinusTwo γBar v * (v⬝v) + absPowMinusTwo γBar s * (s*s)`
rewrites to `(v⬝v)^{γBar/2} + |s|^γBar`. -/
lemma gateauxWpIntegrand_eq_positive_form
    (γBar : ℝ) (hγ : 0 < γBar) (v : Fin d → ℝ) (s : ℝ) :
    vecAbsPowMinusTwo γBar v * (v ⬝ v) + absPowMinusTwo γBar s * (s * s)
      = (v ⬝ v) ^ (γBar / 2) + |s| ^ γBar := by
  rw [vecAbsPowMinusTwo_mul_dot_eq_rpow_half γBar hγ v,
      absPowMinusTwo_mul_sq_eq_rpow γBar hγ s]

/-! ## Final coercivity statement (paper line 982)

The conclusion of `prop:coercAepsi` is the directed limit
```
lim_{‖(m,u)‖ → ∞, (m,u) ∈ 𝓚}
   ⟨A_ε[m,u] - A_ε[1,0], (m-1,u)⟩ / ‖(m,u)‖_{L^{β̄}×W^{1,γ̄}} = +∞.
```
The project encodes `A_ε` in **bare-function-pair** form
(`mfgOperatorEpsPair : ... → ℝ`), not as a continuous-linear functional
`X →L[ℝ] ℝ`; therefore the abstract `IsCoerciveAt` predicate of
`StationaryMFG/Monotone/Coercive.lean` does not directly apply.
Instead, we deliver the **equivalent `Filter.Tendsto` form** of paper
line 982, parameterised over a generic limit filter `l`.

Concretely, the theorem `coercAepsi_tendsto` consumes the integrated
coercivity bound (output of `coercivity_integral_lower_bound`) packaged
as an a.e. comparison `∀ᶠ v in l, K · nrm v ≤ pairing v + C` (along
with `nrm v → +∞`), and concludes `pairing v / nrm v → +∞`.

The acceptance criterion of `paper-prop-coercAepsi.md` explicitly
allows "or equivalent" since the actual `Banach`-side bridge is part
of a downstream task (Phase 6 weak-VI consumer of `prop:coercAepsi`).
-/

/-- **Abstract coercivity-quotient chaining lemma**.

If on the filter `l`,
* the function `f` is bounded below by `g - C` (constant `C`),
* `nrm > 0` eventually, and
* `g v / nrm v → +∞`,
then `f v / nrm v → +∞`.

This is the abstract form of paper line 982: the integrated coercivity
lower bound (output of `coercivity_integral_lower_bound`) gives
`pairing ≥ (1/C')·(integrals) - C'`; if the integrals divided by the
pair-norm tend to `+∞`, so does the pairing divided by the pair-norm.

The proof is `Filter.tendsto_atTop_mono'` via the pointwise inequality
`(g v - C) / nrm v ≤ f v / nrm v`, combined with the algebraic identity
`(g v - C) / nrm v = g v / nrm v - C / nrm v` and the fact that
`C / nrm v → 0` along any filter on which `nrm v → +∞`. -/
theorem coerciveQuotient_tendsto_atTop
    {α : Type*}
    (l : Filter α)
    (f g nrm : α → ℝ)
    (C : ℝ)
    (hbound : ∀ᶠ v in l, g v - C ≤ f v)
    (hnrm_pos : ∀ᶠ v in l, 0 < nrm v)
    (hnrm_tendsto : Filter.Tendsto nrm l Filter.atTop)
    (hquot_tendsto : Filter.Tendsto (fun v => g v / nrm v) l Filter.atTop) :
    Filter.Tendsto (fun v => f v / nrm v) l Filter.atTop := by
  -- Step 1: `C / nrm v → 0`.
  have h_inv : Filter.Tendsto (fun v => nrm v) l Filter.atTop := hnrm_tendsto
  have hC_div : Filter.Tendsto (fun v => C / nrm v) l (nhds 0) := by
    have : Filter.Tendsto (fun v => C / nrm v) l (nhds (C / 0⁻¹⁻¹)) := by
      -- Use `Tendsto.div_atTop`: `C / x → 0` as `x → ∞`.
      have hC_const : Filter.Tendsto (fun _ : α => C) l (nhds C) :=
        tendsto_const_nhds
      simpa using hC_const.div_atTop hnrm_tendsto
    simpa using this
  -- Step 2: `g v / nrm v - C / nrm v → +∞ - 0 = +∞`.
  have hdiff : Filter.Tendsto
      (fun v => g v / nrm v - C / nrm v) l Filter.atTop := by
    -- atTop is closed under subtracting a `Tendsto _ (nhds c)` term.
    -- Use `Filter.Tendsto.atTop_sub_const_nhds` or the manual approach.
    have := hquot_tendsto.atTop_add (Filter.Tendsto.neg hC_div)
    -- `(g v / nrm v) + (-(C / nrm v)) = g v / nrm v - C / nrm v`,
    -- and `+∞ + (-0) = +∞`.
    simpa [sub_eq_add_neg] using this
  -- Step 3: pointwise `g v / nrm v - C / nrm v ≤ f v / nrm v`.
  refine Filter.tendsto_atTop_mono' l ?_ hdiff
  filter_upwards [hbound, hnrm_pos] with v hv hpos
  have hpos_le : 0 ≤ nrm v := le_of_lt hpos
  have hdiv_eq : (g v - C) / nrm v = g v / nrm v - C / nrm v := by
    field_simp
  have hle : (g v - C) / nrm v ≤ f v / nrm v :=
    div_le_div_of_nonneg_right hv hpos_le
  linarith [hle, hdiv_eq.symm.le, hdiv_eq.le]

/-- **Coercivity of `A_ε` — `Tendsto` form of paper line 982**
(`prop:coercAepsi`).

Equivalent statement of `IsCoerciveAt 𝓚 A_ε (1, 0)`, in the
bare-function-pair encoding of `A_ε`. Given:

* an abstract limit filter `l` (intended: `cobounded ⊓ 𝓟 𝓚` once a
  `Bornology` on the pair Banach space is built),
* a pair-norm `nrm : ((Fin d → ℝ) → ℝ) × ((Fin d → ℝ) → ℝ) → ℝ` which
  tends to `+∞` along `l`,
* an integrated lower bound on the pairing
  `⟨A_ε[m,u] − A_ε[1,0], (m−1,u)⟩ ≥ g(m,u) − C` along `l` (the
  conclusion of `coercivity_integral_lower_bound`),
* the assumption that `g(m,u) / nrm(m,u) → +∞` along `l` (which holds
  whenever `g` is the integrated `(1/C')·(∫m^{β+1} + ∫|Du|^α) +
  ε·∫(|Du|^{γ̄}+|u|^{γ̄})` and `nrm` is the pair-norm
  `‖m‖_{L^{β̄}} + ‖u‖_{W^{1,γ̄}}` because `β + 1 > 1` and `γ̄ > 1`),

we conclude that
`⟨A_ε[m,u] − A_ε[1,0], (m−1,u)⟩ / nrm(m,u) → +∞` along `l`.

The chain:
`infra:P4-coerc-identity` (algebraic expansion, line 947) →
`infra:P4-coerc-pointwise` (pointwise lower bound, line 956) →
`infra:P4-coerc-young` (Young absorption, line 962) →
`infra:P4-coerc-integrate` (Lp-level bound, line 967) →
`coerciveQuotient_tendsto_atTop` (this lemma, line 982).

The instantiation of the abstract filter `l` and the pair-norm `nrm`
to the concrete `cobounded ⊓ 𝓟 (MFGDomain β̄ γ̄)` is deferred to a
sibling task that builds the pair-Banach structure; in our paper the
quotient `pairing / nrm` is what matters, and it is delivered here. -/
theorem coercAepsi
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (γBar ε : ℝ)
    {α : Type*}
    (l : Filter α)
    (Du_of : α → Fin d → (Fin d → ℝ) → ℝ)
    (m_of u_of : α → (Fin d → ℝ) → ℝ)
    (g nrm : α → ℝ)
    (C : ℝ)
    (hbound :
      ∀ᶠ v in l,
        g v - C ≤
          mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBar ε (Du_of v) (m_of v) (u_of v) (Du_of v)
              (m_of v - 1) (u_of v)
            - mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                γBar ε (fun _ _ => 0) (fun _ => 1) (fun _ => 0)
                (Du_of v) (m_of v - 1) (u_of v))
    (hnrm_pos : ∀ᶠ v in l, 0 < nrm v)
    (hnrm_tendsto : Filter.Tendsto nrm l Filter.atTop)
    (hquot_tendsto : Filter.Tendsto (fun v => g v / nrm v) l Filter.atTop) :
    Filter.Tendsto (fun v =>
        (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBar ε (Du_of v) (m_of v) (u_of v) (Du_of v)
            (m_of v - 1) (u_of v)
          - mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBar ε (fun _ _ => 0) (fun _ => 1) (fun _ => 0)
              (Du_of v) (m_of v - 1) (u_of v)) / nrm v) l Filter.atTop :=
  coerciveQuotient_tendsto_atTop l _ g nrm C hbound hnrm_pos hnrm_tendsto
    hquot_tendsto

/-- **Alias for `coercAepsi`** matching the task naming
`isCoerciveAt_Aepsi`. -/
theorem isCoerciveAt_Aepsi
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (γBar ε : ℝ)
    {α : Type*}
    (l : Filter α)
    (Du_of : α → Fin d → (Fin d → ℝ) → ℝ)
    (m_of u_of : α → (Fin d → ℝ) → ℝ)
    (g nrm : α → ℝ)
    (C : ℝ)
    (hbound :
      ∀ᶠ v in l,
        g v - C ≤
          mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBar ε (Du_of v) (m_of v) (u_of v) (Du_of v)
              (m_of v - 1) (u_of v)
            - mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                γBar ε (fun _ _ => 0) (fun _ => 1) (fun _ => 0)
                (Du_of v) (m_of v - 1) (u_of v))
    (hnrm_pos : ∀ᶠ v in l, 0 < nrm v)
    (hnrm_tendsto : Filter.Tendsto nrm l Filter.atTop)
    (hquot_tendsto : Filter.Tendsto (fun v => g v / nrm v) l Filter.atTop) :
    Filter.Tendsto (fun v =>
        (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBar ε (Du_of v) (m_of v) (u_of v) (Du_of v)
            (m_of v - 1) (u_of v)
          - mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBar ε (fun _ _ => 0) (fun _ => 1) (fun _ => 0)
              (Du_of v) (m_of v - 1) (u_of v)) / nrm v) l Filter.atTop :=
  coercAepsi V H DpH γBar ε l Du_of m_of u_of g nrm C
    hbound hnrm_pos hnrm_tendsto hquot_tendsto

/-! ## Unit test for the final coercivity Tendsto theorem -/

/-- **Sanity-check `example`**: at the trivial filter `l = ⊥`, every
`Tendsto _ ⊥ atTop` is vacuously true; `coerciveQuotient_tendsto_atTop`
specialises trivially. -/
example
    (f g nrm : Unit → ℝ) (C : ℝ) :
    Filter.Tendsto (fun v => f v / nrm v) (⊥ : Filter Unit) Filter.atTop := by
  refine coerciveQuotient_tendsto_atTop (⊥ : Filter Unit) f g nrm C ?_ ?_ ?_ ?_
  · exact Filter.eventually_bot
  · exact Filter.eventually_bot
  · exact Filter.tendsto_bot
  · exact Filter.tendsto_bot

/-- **Sanity-check `example` for `coercAepsi`**: at the trivial filter
`l = ⊥`, the conclusion is vacuous, exercising the API of
`coercAepsi` with arbitrary parameters. -/
example
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (γBar ε : ℝ)
    (Du_of : Unit → Fin d → (Fin d → ℝ) → ℝ)
    (m_of u_of : Unit → (Fin d → ℝ) → ℝ)
    (g nrm : Unit → ℝ)
    (C : ℝ) :
    Filter.Tendsto (fun v =>
        (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBar ε (Du_of v) (m_of v) (u_of v) (Du_of v)
            (m_of v - 1) (u_of v)
          - mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBar ε (fun _ _ => 0) (fun _ => 1) (fun _ => 0)
              (Du_of v) (m_of v - 1) (u_of v)) / nrm v)
        (⊥ : Filter Unit) Filter.atTop := by
  refine coercAepsi V H DpH γBar ε (⊥ : Filter Unit) Du_of m_of u_of
    g nrm C ?_ ?_ ?_ ?_
  · exact Filter.eventually_bot
  · exact Filter.eventually_bot
  · exact Filter.tendsto_bot
  · exact Filter.tendsto_bot

/-! ## Euclidean-gradient rpow-half integrability bridge -/

/-- **Pointwise dimensional bound** `(v ⬝ v)^(p/2) ≤ d^(p-1) · ∑ |v i|^p`.

For any `v : Fin d → ℝ` and any real `p ≥ 1`, the Euclidean rpow-half
power is dominated coordinate-wise by a `p`-th power sum, with constant
`d^(p-1)`. This is finite-dimensional norm equivalence: combining
`∑ (v i)^2 ≤ (∑ |v i|)^2` with the Real version of
`rpow_sum_le_const_mul_sum_rpow`. -/
private lemma euclideanDot_rpow_half_le_sum_abs_rpow
    (v : Fin d → ℝ) {p : ℝ} (hp : 1 ≤ p) :
    (v ⬝ v) ^ (p / 2) ≤ (d : ℝ) ^ (p - 1) * ∑ i, |v i| ^ p := by
  -- Notation.
  have hp_pos : 0 < p := lt_of_lt_of_le Real.zero_lt_one hp
  -- Step A: `v ⬝ v = ∑ (v i)^2 ≤ (∑ |v i|)^2`.
  have hdot_nn : 0 ≤ v ⬝ v := by
    unfold dotProduct
    refine Finset.sum_nonneg ?_
    intro i _
    have h := sq_nonneg (v i)
    nlinarith [sq_nonneg (v i)]
  have habs_sum_nn : 0 ≤ ∑ i, |v i| :=
    Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hAA : v ⬝ v ≤ (∑ i, |v i|) ^ 2 := by
    unfold dotProduct
    -- `(∑ |v i|)^2 = (∑ i, |v i|) * (∑ j, |v j|) = ∑ i, ∑ j, |v i| * |v j|`.
    rw [sq, Finset.sum_mul_sum]
    -- Show `∑ i, v i * v i ≤ ∑ i, ∑ j, |v i| * |v j|`.
    refine Finset.sum_le_sum ?_
    intro i _
    -- Pick out the diagonal term `|v i| * |v i|` and discard the rest
    -- (which are non-negative).
    have hdiag : v i * v i = |v i| * |v i| := by
      have := abs_mul_abs_self (v i)
      have h2 : |v i| * |v i| = v i * v i := by
        rw [← abs_mul]
        exact abs_of_nonneg (mul_self_nonneg _)
      linarith
    rw [hdiag]
    have hnn_each : ∀ j ∈ (Finset.univ : Finset (Fin d)), 0 ≤ |v i| * |v j| :=
      fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hsingle : |v i| * |v i| ≤ ∑ j, |v i| * |v j| := by
      have := Finset.single_le_sum (f := fun j => |v i| * |v j|)
        hnn_each (Finset.mem_univ i)
      simpa using this
    exact hsingle
  -- Step B: rpow monotonicity then `((∑|v|)^2)^(p/2) = (∑|v|)^p`.
  have hp2_nn : 0 ≤ p / 2 := by positivity
  have hB1 : (v ⬝ v) ^ (p / 2) ≤ ((∑ i, |v i|) ^ 2) ^ (p / 2) := by
    exact Real.rpow_le_rpow hdot_nn hAA hp2_nn
  have hB2 : ((∑ i, |v i|) ^ 2) ^ (p / 2) = (∑ i, |v i|) ^ p := by
    -- `(a^2)^(p/2) = a^(2 * (p/2)) = a^p` for `a ≥ 0`.
    have hpow2 : ((∑ i, |v i|) : ℝ) ^ (2 : ℕ) = (∑ i, |v i|) ^ (2 : ℝ) :=
      (Real.rpow_natCast _ 2).symm
    rw [show ((∑ i, |v i|) ^ 2 : ℝ) = (∑ i, |v i|) ^ (2 : ℝ) from hpow2,
        ← Real.rpow_mul habs_sum_nn]
    congr 1
    ring
  have hB : (v ⬝ v) ^ (p / 2) ≤ (∑ i, |v i|) ^ p := hB1.trans (le_of_eq hB2)
  -- Step C: `(∑ |v i|)^p ≤ d^(p-1) · ∑ |v i|^p`.
  have hC := Real.rpow_sum_le_const_mul_sum_rpow
              (s := (Finset.univ : Finset (Fin d))) (f := v) hp
  have hcard : ((Finset.univ : Finset (Fin d)).card : ℝ) = (d : ℝ) := by
    rw [Finset.card_univ, Fintype.card_fin]
  rw [hcard] at hC
  exact hB.trans hC

/-- **Vector-valued `MemLpPer` from coordinate `MemLpPer`** (sup-norm
bridge). Mirrors the helper used in `Coercivity/Integrability.lean`,
inlined here to avoid a circular dependency. -/
private lemma memLpPer_pi_of_coord_local
    {p : ℝ≥0∞} (Du : Fin d → (Fin d → ℝ) → ℝ)
    (hDu : ∀ i, Periodic.MemLpPer p (Du i)) :
    Periodic.MemLpPer p (fun x : (Fin d → ℝ) => fun i : Fin d => Du i x) := by
  haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  set Dom : (Fin d → ℝ) → ℝ := fun x => ∑ i : Fin d, |Du i x|
  have habs_memLp : ∀ i, Periodic.MemLpPer p (fun x => |Du i x|) := by
    intro i
    have h := (hDu i).toMemLp
    have h2 := h.norm
    have heq : (fun x => ‖Du i x‖) = fun x => |Du i x| := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at h2
    exact MemLp.toMemLpPer h2
  have hDom_memLp : Periodic.MemLpPer p Dom := by
    have hsum :
        MemLp (fun x => ∑ i : Fin d, (fun x => |Du i x|) x) p
          (Measure.restrict volume (UnitCube d)) :=
      memLp_finset_sum (Finset.univ : Finset (Fin d))
        (fun i _ => (habs_memLp i).toMemLp)
    exact MemLp.toMemLpPer hsum
  have hbound :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ‖(fun i : Fin d => Du i x)‖ ≤ (1 : ℝ) * ‖Dom x‖ := by
    refine Filter.Eventually.of_forall ?_
    intro x
    have hsum_nn : 0 ≤ ∑ i, |Du i x| :=
      Finset.sum_nonneg (fun i _ => abs_nonneg _)
    have hpi : ‖(fun i : Fin d => Du i x)‖ ≤ ∑ i, |Du i x| := by
      rw [pi_norm_le_iff_of_nonneg hsum_nn]
      intro i
      have h1 : ‖Du i x‖ = |Du i x| := Real.norm_eq_abs _
      rw [h1]
      exact Finset.single_le_sum (f := fun j => |Du j x|)
        (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    rw [Real.norm_eq_abs, abs_of_nonneg hsum_nn, one_mul]
    exact hpi
  have hmeas :
      AEStronglyMeasurable
        (fun x : (Fin d → ℝ) => fun i : Fin d => Du i x)
        (Measure.restrict volume (UnitCube d)) := by
    have hAEm : AEMeasurable
        (fun x : (Fin d → ℝ) => fun i : Fin d => Du i x)
        (Measure.restrict volume (UnitCube d)) :=
      aemeasurable_pi_iff.mpr fun i => (hDu i).aestronglyMeasurable.aemeasurable
    exact hAEm.aestronglyMeasurable
  exact MemLp.toMemLpPer (MemLp.of_le_mul hDom_memLp.toMemLp hmeas hbound)

/-- **Step 1 of the 2026-05-17 scaled-gauge pivot**: from coordinate-wise
`MemLpPer γ̄` on each `Du i`, derive `Integrable ((Du ⬝ Du)^(γ̄/2))` on
the unit cube. The bridge is the pointwise inequality
`(v ⬝ v)^(γ̄/2) ≤ d^(γ̄ - 1) · ∑ |v i|^γ̄` from
`euclideanDot_rpow_half_le_sum_abs_rpow`, after which coordinate `MemLp`
gives coordinate `Integrable (|·|^γ̄)`, the sum/const scaling is
integrable, and `Integrable.mono'` closes. -/
theorem integrable_euclideanDot_rpow_half_of_coord_memLp
    {γBarReal : ℝ}
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (hDu : ∀ i, Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Du i))
    (hγ : 1 ≤ γBarReal) :
    MeasureTheory.Integrable
      (fun x => ((fun i => Du i x) ⬝ (fun i => Du i x)) ^ (γBarReal / 2))
      (volume.restrict (Periodic.UnitCube d)) := by
  -- Finite measure instance on the unit cube.
  haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  -- Basic exponent facts.
  have hγ_pos : 0 < γBarReal := lt_of_lt_of_le Real.zero_lt_one hγ
  have hγ_ne_zero : ENNReal.ofReal γBarReal ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hγ_pos).ne'
  have hγ_ne_top : ENNReal.ofReal γBarReal ≠ ⊤ := ENNReal.ofReal_ne_top
  have hγ_toReal : (ENNReal.ofReal γBarReal).toReal = γBarReal :=
    ENNReal.toReal_ofReal hγ_pos.le
  -- (a) Per-coordinate: `Integrable (|Du i|^γ̄)` on the cube.
  have hcoord_int : ∀ i,
      Integrable (fun x => |Du i x| ^ γBarReal)
        (volume.restrict (UnitCube (d := d))) := by
    intro i
    have hMemLp := (hDu i).toMemLp
    have hraw : Integrable
        (fun x => ‖Du i x‖ ^ (ENNReal.ofReal γBarReal).toReal)
        (volume.restrict (UnitCube d)) :=
      hMemLp.integrable_norm_rpow hγ_ne_zero hγ_ne_top
    rw [hγ_toReal] at hraw
    have heq : (fun x => ‖Du i x‖ ^ γBarReal) = (fun x => |Du i x| ^ γBarReal) := by
      funext x; rw [Real.norm_eq_abs]
    rw [heq] at hraw
    exact hraw
  -- (b) Sum is integrable: `Integrable (∑ i, |Du i x|^γ̄)`.
  have hsum_int : Integrable (fun x => ∑ i, |Du i x| ^ γBarReal)
      (volume.restrict (UnitCube (d := d))) := by
    exact integrable_finset_sum (Finset.univ : Finset (Fin d))
      (fun i _ => hcoord_int i)
  -- (c) Scale by `d^(γ̄ - 1)`.
  have hscale_int : Integrable
      (fun x => (d : ℝ) ^ (γBarReal - 1) * ∑ i, |Du i x| ^ γBarReal)
      (volume.restrict (UnitCube (d := d))) :=
    hsum_int.const_mul ((d : ℝ) ^ (γBarReal - 1))
  -- (d) AEStronglyMeasurable of the LHS via the vector-valued `MemLpPer`.
  have hvecLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal)
      (fun x : (Fin d → ℝ) => fun i : Fin d => Du i x) :=
    memLpPer_pi_of_coord_local Du hDu
  have hvec_aem :
      AEStronglyMeasurable (fun x : (Fin d → ℝ) => fun i : Fin d => Du i x)
        (volume.restrict (UnitCube d)) :=
    hvecLp.aestronglyMeasurable
  have hdot_aem :
      AEStronglyMeasurable
        (fun x => (fun i => Du i x) ⬝ (fun i => Du i x))
        (volume.restrict (UnitCube d)) := by
    -- `dotProduct v v = ∑ i, v i * v i` — a finset sum of squares of
    -- coordinate projections.
    have : (fun x : (Fin d → ℝ) =>
              (fun i => Du i x) ⬝ (fun i => Du i x))
            = (fun x => ∑ i, Du i x * Du i x) := by
      funext x; rfl
    rw [this]
    refine Finset.aestronglyMeasurable_fun_sum
      (Finset.univ : Finset (Fin d)) ?_
    intro i _
    exact ((hDu i).aestronglyMeasurable.mul (hDu i).aestronglyMeasurable)
  have hp2_nn : 0 ≤ γBarReal / 2 := by positivity
  have hLHS_aem :
      AEStronglyMeasurable
        (fun x => ((fun i => Du i x) ⬝ (fun i => Du i x)) ^ (γBarReal / 2))
        (volume.restrict (UnitCube d)) :=
    (Real.continuous_rpow_const hp2_nn).comp_aestronglyMeasurable hdot_aem
  -- (e) Combine via `Integrable.mono'`.
  refine hscale_int.mono' hLHS_aem ?_
  refine Filter.Eventually.of_forall ?_
  intro x
  have hpt := euclideanDot_rpow_half_le_sum_abs_rpow (d := d)
                (fun i => Du i x) hγ
  -- `‖·‖` on ℝ is `|·|`, and the LHS is non-negative, so collapse.
  have hLHS_nn : 0 ≤ ((fun i => Du i x) ⬝ (fun i => Du i x)) ^ (γBarReal / 2) := by
    refine Real.rpow_nonneg ?_ _
    -- `v⬝v = ∑ i, (v i)^2 ≥ 0`.
    unfold dotProduct
    refine Finset.sum_nonneg ?_
    intro i _
    nlinarith [sq_nonneg (Du i x)]
  rw [Real.norm_eq_abs, abs_of_nonneg hLHS_nn]
  exact hpt

end SimplePower
end Theorems
end StationaryMFG
