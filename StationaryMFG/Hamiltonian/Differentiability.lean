module

public import StationaryMFG.Hamiltonian.Assumptions
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

@[expose] public section

/-!
# Hamiltonian — paper rider `(rmk:cxty)` + `D_pH = ∇_p H`

This file bundles two paper-side riders on the Hamiltonian `H` and
its `p`-gradient `D_pH`, both implicit in
`Source/FGU-monotone_revised.tex`:

* **`(rmk:cxty)`** (line 432): for a.e. `x ∈ 𝕋^d` and every `m > 0`,
  the map `p ↦ H(x, p, m)` is convex on `ℝ^d`. The paper deduces
  this from the monotonicity inequality `hmon` by taking `m_1 = m_2`;
  however, that derivation silently identifies `D_pH` with the
  classical gradient `∇_p H`, an identification that *our* Lean
  model does **not** carry (see
  `StationaryMFG/Hamiltonian/Assumptions.lean`, where `D_pH` is a
  separate field of `RegularityH`). We therefore record the
  convexity as an explicit paper-side rider.

* **`D_pH = ∇_p H`** (paper line 1670, in the proof of the
  infimal-convolution differentiability): for a.e. `x ∈ 𝕋^d` and
  every `(p, m)` with `0 < m`, the section `q ↦ H(x, q, m)` is
  Fréchet-differentiable at `p` with derivative the continuous
  linear functional `w ↦ D_pH(x, p, m) ⬝ w`. This is the
  identification the paper takes for granted once it talks about
  subdifferentials and `D_pH`.

The two riders together form `HypothesisHpDifferentiable H DpH`,
which is the prerequisite for the subdifferential inclusion lemmas
(infimal-convolution properties, paper Lemmas `lem:inf-conv-props-ii`
and `lem:inf-conv-props-iii`) consumed by child tasks C and D of the
`paper-lem-inf-conv-props-ii` split.

Both riders are *new* hypotheses — they are **not** derivable from
the existing bundles (`RegularityH`, `HypothesisMonotone`,
`HypothesisPowerGrowth`), precisely because our model unbundles
`D_pH` from the literal Fréchet derivative.

## Module conventions

Per `docs/CONVENTIONS.md`:

* Points `x` live in `Fin d → ℝ`; "for a.e. `x ∈ 𝕋^d`" is the
  measure restriction `volume.restrict (UnitCube d)`.
* `‖p‖` is the sup-norm on `Fin d → ℝ`. The dot product
  `D_pH(x, p, m) ⬝ w` is `dotProduct` from
  `StationaryMFG/Hamiltonian/Assumptions.lean`.
* The Fréchet derivative is taken in the sup-norm topology on
  `Fin d → ℝ`. The continuous linear functional `dotCLMHam q` is
  the duality pairing `w ↦ q ⬝ w`, packaged as a CLM with operator
  norm bound `d * ‖q‖`. (We mirror the `dotCLM` definition from
  `StationaryMFG/Theorems/InfimalConvolution/Kernel.lean` locally,
  to avoid a downward import from `Hamiltonian` into `Theorems`.)
-/

namespace StationaryMFG
namespace Hamiltonian

open MeasureTheory
open StationaryMFG.Periodic

variable {d : ℕ}

/-! ## Auxiliary: `dotCLMHam`

`dotCLMHam q : (Fin d → ℝ) →L[ℝ] ℝ` is the continuous linear
functional `w ↦ q ⬝ w` (`dotProduct`), packaged as a CLM. This
mirrors `StationaryMFG.InfimalConvolution.dotCLM`; we duplicate the
construction here so that the differentiability rider can be stated
inside the `Hamiltonian` namespace without importing
`InfimalConvolution`. -/

/-- Coordinatewise bound `q ⬝ x ≤ d ‖q‖ ‖x‖` for the sup-norm
`‖·‖` on `Fin d → ℝ`. Each summand `|q i * x i|` is bounded by
`‖q‖ * ‖x‖`, and there are `d` summands. -/
private lemma euclideanDot_le_card_mul_norm
    (q v : Fin d → ℝ) : q ⬝ v ≤ (d : ℝ) * (‖q‖ * ‖v‖) := by
  unfold dotProduct
  calc ∑ i, q i * v i
      ≤ ∑ _i : Fin d, ‖q‖ * ‖v‖ := by
        refine Finset.sum_le_sum ?_
        intro i _
        calc q i * v i
            ≤ |q i * v i| := le_abs_self _
          _ = |q i| * |v i| := abs_mul _ _
          _ ≤ ‖q‖ * ‖v‖ := by
              have hq : |q i| ≤ ‖q‖ := by
                simpa [Real.norm_eq_abs] using (norm_le_pi_norm q i)
              have hv : |v i| ≤ ‖v‖ := by
                simpa [Real.norm_eq_abs] using (norm_le_pi_norm v i)
              exact mul_le_mul hq hv (abs_nonneg _) (norm_nonneg _)
    _ = (d : ℝ) * (‖q‖ * ‖v‖) := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

/-- Absolute-value form of `euclideanDot_le_card_mul_norm`. -/
private lemma abs_euclideanDot_le_card_mul_norm
    (q v : Fin d → ℝ) : |q ⬝ v| ≤ (d : ℝ) * ‖q‖ * ‖v‖ := by
  have h1 := euclideanDot_le_card_mul_norm (d := d) q v
  have h2 := euclideanDot_le_card_mul_norm (d := d) (-q) v
  have hneg : (-q) ⬝ v = -(q ⬝ v) := by
    unfold dotProduct
    simp [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  rw [hneg] at h2
  -- `(-q) ⬝ v = -q ⬝ v ≤ d * ‖-q‖ * ‖v‖ = d * ‖q‖ * ‖v‖`.
  have hneg_norm : ‖(-q : Fin d → ℝ)‖ = ‖q‖ := by simp
  rw [hneg_norm] at h2
  have hub : q ⬝ v ≤ (d : ℝ) * ‖q‖ * ‖v‖ := by
    have := h1
    nlinarith [norm_nonneg q, norm_nonneg v]
  have hlb : -(q ⬝ v) ≤ (d : ℝ) * ‖q‖ * ‖v‖ := by
    have := h2
    nlinarith [norm_nonneg q, norm_nonneg v]
  exact abs_le.mpr ⟨by linarith, hub⟩

/-- The linear functional `w ↦ q ⬝ w` packaged as a continuous
linear map `(Fin d → ℝ) →L[ℝ] ℝ`. Local mirror of
`StationaryMFG.InfimalConvolution.dotCLM`, defined here to keep
`HypothesisHpDifferentiable` self-contained within the
`Hamiltonian` namespace. -/
noncomputable def dotCLMHam (q : Fin d → ℝ) :
    (Fin d → ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun w => q ⬝ w
      map_add' := by
        intro x y
        unfold dotProduct
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl ?_
        intro i _
        simp [Pi.add_apply]
        ring
      map_smul' := by
        intro a x
        unfold dotProduct
        simp only [RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _
        simp [Pi.smul_apply, smul_eq_mul]
        ring }
    ((d : ℝ) * ‖q‖)
    (by
      intro x
      have hbnd := abs_euclideanDot_le_card_mul_norm (d := d) q x
      simpa [Real.norm_eq_abs] using hbnd)

@[simp] lemma dotCLMHam_apply (q w : Fin d → ℝ) :
    dotCLMHam q w = q ⬝ w := rfl

@[simp] lemma dotCLMHam_zero :
    dotCLMHam (0 : Fin d → ℝ) = 0 := by
  ext w
  simp [dotCLMHam_apply, dotProduct]

/-! ## Paper rider `HypothesisHpDifferentiable`

Bundles convexity in `p` (paper `rmk:cxty`) and the identification
`D_pH = ∇_p H` (paper line 1670). Both are paper-implicit
hypotheses our Lean model exposes explicitly. -/

/--
**Paper rider — `HypothesisHpDifferentiable H DpH`**.

Records two paper-side assumptions on `H` and `D_pH`, both implicit
in `Source/FGU-monotone_revised.tex` and used by the
infimal-convolution differentiability lemmas:

* `hasFDerivAt_H_p`: for a.e. `x ∈ 𝕋^d` and every `(p, m)` with
  `0 < m`, the section `q ↦ H(x, q, m)` is Fréchet-differentiable
  at `p` with derivative `dotCLMHam (D_pH x p m)` (i.e.
  `w ↦ D_pH(x, p, m) ⬝ w`). This is the paper-line-1670
  identification `D_pH = ∇_p H`.

* `convexOn_H_p`: for a.e. `x ∈ 𝕋^d` and every `m > 0`, the
  section `q ↦ H(x, q, m)` is convex on `ℝ^d`. This is the
  paper `rmk:cxty` (line 432).

Both riders are *new* hypotheses: they are not derivable from
`RegularityH`, `HypothesisMonotone`, or `HypothesisPowerGrowth`
in our setting, because our model bundles `D_pH` as a separate
function from the literal Fréchet derivative.

Downstream consumers (children C/D of the
`paper-lem-inf-conv-props-ii` split) will require this bundle to
state and prove subdifferential inclusions and the `M^ε`
inversion identity.
-/
structure HypothesisHpDifferentiable
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)) : Prop where
  /-- Paper line 1670 — `D_pH` is the Fréchet derivative of
  `q ↦ H(x, q, m)` at every `p` (for `m > 0`, a.e. `x`). -/
  hasFDerivAt_H_p :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ (p : Fin d → ℝ) (m : ℝ), 0 < m →
        HasFDerivAt (fun q : Fin d → ℝ => H x q m) (dotCLMHam (DpH x p m)) p
  /-- Paper `rmk:cxty` (line 432) — `q ↦ H(x, q, m)` is convex on
  `ℝ^d` for `m > 0` and a.e. `x`. -/
  convexOn_H_p :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ m : ℝ, 0 < m →
        ConvexOn ℝ (Set.univ : Set (Fin d → ℝ))
          (fun q : Fin d → ℝ => H x q m)

/-! ## Example instances

We supply two coherence-check instances of
`HypothesisHpDifferentiable`. Both use a `DpH ≡ 0` field, since the
sup-norm geometry of `Fin d → ℝ` makes the standard model
`H(x,p,m) = ‖p‖^2 − m` *not* differentiable in `p` at every point
(the sup-norm is not differentiable at corner vectors), so we cannot
inhabit the differentiability bundle with the `simpleHypothesisPowerGrowth`
data directly. A paper-faithful nontrivial example will accompany
the infimal-convolution kernel `K^ε` (child C/D), where
differentiability is genuinely proved. -/

/-- The trivially-zero Hamiltonian satisfies
`HypothesisHpDifferentiable`. The Fréchet derivative of a constant
function is the zero CLM, and constants are convex. -/
example (d : ℕ) :
    HypothesisHpDifferentiable (d := d)
      (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : Fin d → ℝ)) where
  hasFDerivAt_H_p := by
    refine Filter.Eventually.of_forall ?_
    intro _ p m _
    -- Goal: `HasFDerivAt (fun _ => 0) (dotCLMHam 0) p`. The CLM
    -- `dotCLMHam 0` equals the zero CLM.
    have h0 : (dotCLMHam (0 : Fin d → ℝ)) = 0 := dotCLMHam_zero
    rw [h0]
    exact hasFDerivAt_const (𝕜 := ℝ) (E := (Fin d → ℝ)) (0 : ℝ) p
  convexOn_H_p := by
    refine Filter.Eventually.of_forall ?_
    intro _ _ _
    exact convexOn_const (𝕜 := ℝ) (E := (Fin d → ℝ)) (0 : ℝ) convex_univ

/-- A constant-valued Hamiltonian
`H(x, p, m) = c` with `D_pH = 0` satisfies
`HypothesisHpDifferentiable` for any real constant `c`. Coherence
check — every constant `c` gives an inhabitant. -/
example (d : ℕ) (c : ℝ) :
    HypothesisHpDifferentiable (d := d)
      (fun _ _ _ => c) (fun _ _ _ => (0 : Fin d → ℝ)) where
  hasFDerivAt_H_p := by
    refine Filter.Eventually.of_forall ?_
    intro _ p m _
    have h0 : (dotCLMHam (0 : Fin d → ℝ)) = 0 := dotCLMHam_zero
    rw [h0]
    exact hasFDerivAt_const (𝕜 := ℝ) (E := (Fin d → ℝ)) c p
  convexOn_H_p := by
    refine Filter.Eventually.of_forall ?_
    intro _ _ _
    exact convexOn_const (𝕜 := ℝ) (E := (Fin d → ℝ)) c convex_univ

/-! ## Paper rider `HypothesisDpHMeasurable`

A paper-side rider on `H` and `D_pH` bundling joint Borel
measurability. Used by the measurability cascade for `q^ε` and
`H^ε` (paper line 1684, in the proof of `lem:inf-conv-props.(ii)`):
once `M^ε_{x,m}` is invertible, the formula
`q^ε(x, p, m) = p − (M^ε_{x,m})⁻¹(p)` plus measurable inputs gives
Borel measurability of `q^ε` and hence (via the H-epsilon formula)
of `H^ε`.

The paper takes for granted that `H` and its `p`-gradient `D_pH`
are jointly measurable in `(x, p, m)`. In our Lean model these
assumptions are not implied by the existing bundles (`RegularityH`,
`HypothesisMonotone`, `HypothesisPowerGrowth`, or the continuity
riders in `Theorems/InfimalConvolution`), so we record them
explicitly as a sibling of `HypothesisHpDifferentiable`. -/

/--
**Paper rider — `HypothesisDpHMeasurable H DpH`**.

Joint Borel measurability of the Hamiltonian and its gradient:

* `measurable_H` — `(x, p, m) ↦ H(x, p, m)` is jointly Borel
  measurable as a function `(Fin d → ℝ) × (Fin d → ℝ) × ℝ → ℝ`.
* `measurable_DpH` — `(x, s, m) ↦ D_pH(x, s, m)` is jointly Borel
  measurable as a function
  `(Fin d → ℝ) × (Fin d → ℝ) × ℝ → (Fin d → ℝ)`.

Both are paper-side assumptions (implicit in the
`lem:inf-conv-props.(ii)` measurability claim, paper line 1684). -/
structure HypothesisDpHMeasurable
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)) : Prop where
  /-- Joint Borel measurability of `H` in `(x, p, m)`. -/
  measurable_H :
    Measurable (fun xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ =>
      H xpm.1 xpm.2.1 xpm.2.2)
  /-- Joint Borel measurability of `D_pH` in `(x, s, m)`. -/
  measurable_DpH :
    Measurable (fun xsm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ =>
      DpH xsm.1 xsm.2.1 xsm.2.2)

/-! ### Example instances for `HypothesisDpHMeasurable`

We verify that the trivially-zero Hamiltonian and the constant
Hamiltonian inhabit the new rider. Constants are measurable, so
both fields are `measurable_const`. -/

/-- The zero Hamiltonian (with `D_pH ≡ 0`) satisfies
`HypothesisDpHMeasurable`. -/
example (d : ℕ) :
    HypothesisDpHMeasurable (d := d)
      (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : Fin d → ℝ)) where
  measurable_H := measurable_const
  measurable_DpH := measurable_const

/-- A constant-valued Hamiltonian with `D_pH ≡ 0` satisfies
`HypothesisDpHMeasurable`. -/
example (d : ℕ) (c : ℝ) :
    HypothesisDpHMeasurable (d := d)
      (fun _ _ _ => c) (fun _ _ _ => (0 : Fin d → ℝ)) where
  measurable_H := measurable_const
  measurable_DpH := measurable_const

/-! ## Paper rider `HypothesisHepsilonFtcSlice`

A paper-side rider recording, for a **regularized** Hamiltonian/gradient
pair `(Hε, DpHε)`, the FTC-slice identity `eq:DpHdelta.dotp.minusH`
(`Source/FGU-monotone_revised.tex`, line 1815, "as in `lem:A1+anyother`").

This is the exact regularized analogue of `HypothesisMonotone.lagr_ftc_slice`
for the *base* pair `(H, DpH)` (paper lines 642–645). Its mathematical
content is the paper-silent identification of the regularized gradient
`D_pH^ε` with the genuine `p`-gradient `∂_p H^ε` of the regularized
Hamiltonian along the segment `[0, p]`.

**Why a rider, not a derived fact.** The base pair already carries the
same identity as the explicit field `HypothesisMonotone.lagr_ftc_slice`,
precisely because our Lean model unbundles `D_pH` from the literal
Fréchet derivative (`StationaryMFG/Hamiltonian/Assumptions.lean`,
`docs/CONVENTIONS.md`). For the regularized pair the identity is the
paper's `eq:DpHdelta.dotp.minusH`: the envelope-theorem differentiability
of the convex inf-convolution `H^ε(x, ·, m)` in `p`, identifying its
`p`-gradient with `D_pH^ε`. In our model the full envelope-theorem
differentiability of `H^ε` is the same D2-gated gap that
`lem:inf-conv-props.(ii)` carries: from the subgradient inclusion
(`qEpsilon_subdiff_inclusion_Hepsilon`) we obtain a *one-sided* support
inequality, not the two-sided Fréchet derivative that the FTC integral
form requires. We therefore record the regularized FTC slice as an
explicit paper rider, mirroring the base-pair field. It is a genuine
analytic regularity clause (a differentiability/FTC statement about the
regularized objects), **not** a proof-output oracle: it does not encode
the monotonicity conclusion `lem:H.delta.monotone`, only the gradient
identification that feeds it. -/
structure HypothesisHepsilonFtcSlice
    (Hε : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpHε : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)) : Prop where
  /-- **Paper `eq:DpHdelta.dotp.minusH`** (line 1815). For a.e. `x ∈ 𝕋^d`
  and every `(p, m)` with `0 < m`, the regularized gradient `D_pH^ε`
  realises the FTC slice of `H^ε` along `[0, p]`:

  > `D_pH^ε(x, p, m)·p − (H^ε(x, p, m) − H^ε(x, 0, m))`
  > `= ∫₀¹ (D_pH^ε(x, p, m) − D_pH^ε(x, t·p, m))·p dt`. -/
  ftc_slice :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p m, 0 < m →
        (DpHε x p m) ⬝ p - (Hε x p m - Hε x (0 : Fin d → ℝ) m)
          = ∫ t in (0 : ℝ)..1,
              ((DpHε x p m - DpHε x (t • p) m) ⬝ p)

/-- The trivially-zero regularized pair satisfies
`HypothesisHepsilonFtcSlice`: both sides of the slice identity vanish. -/
example (d : ℕ) :
    HypothesisHepsilonFtcSlice (d := d)
      (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : Fin d → ℝ)) where
  ftc_slice := by
    refine Filter.Eventually.of_forall ?_
    intro _ p m _
    simp

end Hamiltonian
end StationaryMFG
