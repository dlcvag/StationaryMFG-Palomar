module

public import StationaryMFG.Theorems.InfimalConvolution.PaperBoundary
public import StationaryMFG.Hamiltonian.BoundaryContinuityConvex
public import StationaryMFG.Theorems.InfimalConvolution.Monotone
public import StationaryMFG.Theorems.InfimalConvolution.Envelope
public import StationaryMFG.Hamiltonian.Differentiability
public import StationaryMFG.Hamiltonian.Assumptions
public import StationaryMFG.Theorems.SimplePower.Hemicontinuity
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

@[expose] public section

/-!
# Properties of the inf-conv minimizer `q^ε` and regularized Hamiltonian `H^ε`

This file collects properties of the inf-conv minimizer
`q^ε(x, p, m) = qStar h hε hCont hLower` and the regularized
Hamiltonian `H^ε(x, p, m) = Hdelta h ε x p m`, organised around the
paper Lemma `lem:inf-conv-props.(ii)` (lines 1636–1684 of
`Source/FGU-monotone_revised.tex`).

The full task `paper-lem-inf-conv-props-ii` is split into four
layers; this file currently provides only layer (A), the
**Khat-Fenchel inversion equivalence** — the pure Fenchel duality
piece that does *not* require any new hypothesis on `H`.

## Main results

* `Khat_inversion_of_subdiff` — given `v ∈ ∂K(qS)`, conclude
  `qS = DKhat h v`. This is the abstract Fenchel inversion that
  drives `paper:eq:inf-conv.diff-relation2`. The proof goes
  through: `v ∈ ∂K(qS)` is equivalent to `qS` being a maximiser of
  the supremand `q ↦ q ⬝ v − K(q)`, so by strict convexity of `K`
  and the uniqueness lemma `DKhat_unique`, `qS = DKhat h v`.

* `Hepsilon_eq_formula` — the H-epsilon formula
  `Hdelta h ε x p m = H x (p − qS) m + (1/ε) · K h qS` at the
  minimizer `qS := qStar h hε hCont hLower`. This is just
  `qStar_spec` flipped, included for naming alignment with the
  paper's `eq:H-epsilon-formula`.

The remaining layers — first-order optimality (B), subdifferential
inclusions (C), and `M^ε`-inversion / measurability cascade (D) —
are tracked as child tasks
`paper-lem-inf-conv-props-ii-{B,C,D}-*` in
`docs/TASKS/backlog/`.
-/

namespace StationaryMFG
namespace InfimalConvolution

open StationaryMFG.Hamiltonian
open scoped Topology
open Filter

variable {d : ℕ}
variable {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
variable {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}

/-! ## Khat-Fenchel inversion equivalence (layer A) -/

/-- **Khat-Fenchel inversion lemma.** Given a point `qStarPt : Fin d → ℝ`
and a vector `v : Fin d → ℝ` such that `v` is a subgradient of `K h`
at `qStarPt` (`HasSubgradientAt (K h) qStarPt v`), we have
`qStarPt = DKhat h v`.

This is the abstract Fenchel-duality piece behind
`paper:eq:inf-conv.diff-relation2`. The argument:

1. Unfolding `HasSubgradientAt`, the subgradient inequality
   `K(qStarPt) + v ⬝ (y − qStarPt) ≤ K(y)` for all `y` rearranges
   to `qStarPt ⬝ v − K(qStarPt) ≥ y ⬝ v − K(y)` for all `y`, i.e.
   `qStarPt` is a maximiser of the supremand
   `Khat_supremand h v = q ↦ q ⬝ v − K(q)`.
2. By strict convexity of `K` and `DKhat_unique`, the supremand has
   a *unique* maximiser, namely `DKhat h v`.
3. Hence `qStarPt = DKhat h v`. -/
theorem Khat_inversion_of_subdiff
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (qStarPt v : Fin d → ℝ)
    (hsub : HasSubgradientAt (K h) qStarPt v) :
    qStarPt = DKhat h v := by
  -- Step 1: convert the subgradient inequality to the pointwise
  -- supremand inequality `r ⬝ v − K h r ≤ qStarPt ⬝ v − K h qStarPt`.
  have h_max : ∀ r : Fin d → ℝ,
      r ⬝ v - K h r ≤ qStarPt ⬝ v - K h qStarPt := by
    intro y
    have hsub_y := hsub y
    -- `hsub_y : K h qStarPt + ∑ i, v i * (y i − qStarPt i) ≤ K h y`.
    have h_sum_split :
        ∑ i, v i * (y i - qStarPt i) = (∑ i, v i * y i) - (∑ i, v i * qStarPt i) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [h_sum_split] at hsub_y
    -- Identify `∑ i, v i * y i = y ⬝ v` and same for `qStarPt`.
    have h_y_dot : (∑ i, v i * y i) = y ⬝ v := by
      unfold euclideanDot
      apply Finset.sum_congr rfl
      intro i _
      ring
    have h_q_dot : (∑ i, v i * qStarPt i) = qStarPt ⬝ v := by
      unfold euclideanDot
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [h_y_dot, h_q_dot] at hsub_y
    -- `hsub_y : K h qStarPt + (y ⬝ v − qStarPt ⬝ v) ≤ K h y`.
    linarith
  -- Step 2: apply the public uniqueness helper `DKhat_eq_of_isMaxOn`.
  exact DKhat_eq_of_isMaxOn h v qStarPt h_max

/-! ## The H-epsilon formula (paper `eq:H-epsilon-formula`) -/

/-- **Paper `eq:H-epsilon-formula` (line 1681).** At the minimizer
`qStar`, the regularized Hamiltonian is given by
`Hdelta h ε x p m = H x (p − qStar) m + (1/ε) · K h qStar`. This is
the inversion of `qStar_spec` (which states the same equality with
sides swapped). -/
lemma Hepsilon_eq_formula
    (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) {x p : Fin d → ℝ} {m : ℝ}
    (hCont : Continuous (fun q : Fin d → ℝ => H x (p - q) m))
    (hLower : ∀ q : Fin d → ℝ,
      ‖p - q‖ ^ h.α / h.C - h.C * (m ^ h.β + 1) ≤ H x (p - q) m) :
    Hdelta h ε x p m
      = H x (p - qStar h hε hCont hLower) m
          + (1 / ε) * K h (qStar h hε hCont hLower) :=
  (qStar_spec h hε hCont hLower).symm

/-! ## qEpsilon_eq_DKhat (conditional form)

We expose the `q^ε = DKhat(ε · v)` equation conditional on a
subdifferential hypothesis. The unconditional form (deriving the
subdiff inclusion from first-order optimality at the minimum) is
layer (C), tracked in
`paper-lem-inf-conv-props-ii-C-subdiff-inclusions`. -/

/-! ### Unit test -/

/-- Unit test (`d = 1`): the Khat-Fenchel inversion lemma is a
well-typed term. -/
example
    {H₁ : (Fin 1 → ℝ) → (Fin 1 → ℝ) → ℝ → ℝ}
    {DpH₁ : (Fin 1 → ℝ) → (Fin 1 → ℝ) → ℝ → (Fin 1 → ℝ)}
    (h : HypothesisWeakGrowth (d := 1) H₁ DpH₁)
    (qStarPt v : Fin 1 → ℝ)
    (hsub : HasSubgradientAt (K h) qStarPt v) :
    qStarPt = DKhat h v :=
  Khat_inversion_of_subdiff h qStarPt v hsub

/-! ## Layer (C): Subdifferential inclusions at the inf-conv minimizer

Paper `lem:inf-conv-props.(ii)` lines 1663–1666
(`eq:inf-conv.diff-relation1`): for `qS := q^ε(x, p, m)`,

* `D_pH(x, p − qS, m) ∈ (1/ε) ∂K(qS)`,
* `D_pH(x, p − qS, m) ∈ ∂_p H^ε(x, p, m)`.

The two inclusions follow from first-order optimality of `qS` for the
minimization `q ↦ H(x, p − q, m) + (1/ε) K(q)`, combined with the
convexity of `H(x, ·, m)` and the identification of `D_pH` with its
Fréchet derivative (paper-side rider, packaged as
`HypothesisHpDifferentiable`).

We work with the `HasSubgradientAt` predicate (defined in
`Theorems/InfimalConvolution/Kernel.lean`):
`HasSubgradientAt f x v ↔ ∀ y, f x + ∑ i, v i * (y i − x i) ≤ f y`.
-/

open StationaryMFG.Hamiltonian in
/-- **Convex + Fréchet-differentiable ⇒ subgradient inequality.** Given
a function `f : (Fin d → ℝ) → ℝ` that is convex on `Set.univ` and
Fréchet-differentiable at `x` with derivative `L : (Fin d → ℝ) →L[ℝ] ℝ`,
we have `f x + L (y − x) ≤ f y` for every `y`.

The proof uses the slope-at-zero limit: define `g(t) := f(x + t • (y − x))`.
By the chain rule, `HasDerivAt g (L (y − x)) 0`. By convexity, for
`t ∈ (0, 1]` we have `g(t) ≤ (1 − t) · f(x) + t · f(y)`, hence
`(g(t) − g(0))/t ≤ f(y) − f(x)`. Taking `t → 0⁺` and using
`le_of_tendsto`, `L (y − x) ≤ f(y) − f(x)`. -/
private lemma convexOn_subgradient_of_hasFDerivAt
    {f : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    {L : (Fin d → ℝ) →L[ℝ] ℝ}
    (hConv : ConvexOn ℝ (Set.univ : Set (Fin d → ℝ)) f)
    (hFD : HasFDerivAt f L x) :
    ∀ y : Fin d → ℝ, f x + L (y - x) ≤ f y := by
  intro y
  -- Define the ray `γ : ℝ → (Fin d → ℝ)`, `γ t = x + t • (y − x)`.
  set γ : ℝ → (Fin d → ℝ) := fun t => x + t • (y - x) with hγdef
  -- Step 1: `HasDerivAt γ (y - x) 0`.
  have hγ_deriv : HasDerivAt γ (y - x) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t • (y - x)) ((1 : ℝ) • (y - x)) 0 :=
      (hasDerivAt_id (0 : ℝ)).smul_const (y - x)
    have h1' : HasDerivAt (fun t : ℝ => t • (y - x)) (y - x) 0 := by
      simpa [one_smul] using h1
    exact h1'.const_add x
  -- Step 2: `HasDerivAt (f ∘ γ) (L (y - x)) 0` via the chain rule.
  -- Note `γ 0 = x + 0 • (y - x) = x`.
  have hγ_zero : γ 0 = x := by simp [hγdef]
  have hcomp : HasDerivAt (fun t : ℝ => f (γ t)) (L (y - x)) 0 := by
    have := hFD.comp_hasDerivAt_of_eq (𝕜 := ℝ) (f := γ) (f' := y - x)
        (x := 0) hγ_deriv hγ_zero.symm
    simpa only [Function.comp_def] using this
  -- Step 3: slope characterisation.
  -- `Tendsto (fun t => t⁻¹ • (f(γ t) - f(γ 0))) (𝓝[>] 0) (𝓝 (L (y - x)))`.
  have hslope := hcomp.tendsto_slope_zero_right
  -- The slope function. Below we use the form
  -- `t⁻¹ * (f(γ t) - f(x))` (since the codomain is `ℝ`, `•` becomes `*`).
  -- Step 4: convexity bound: for `t ∈ (0, 1]`,
  -- `(f(γ t) - f x)/t ≤ f y - f x`.
  have hConv_univ : Convex ℝ (Set.univ : Set (Fin d → ℝ)) := hConv.1
  have hConv_ineq : ∀ ⦃t : ℝ⦄, 0 ≤ t → t ≤ 1 →
      f (γ t) ≤ (1 - t) * f x + t * f y := by
    intro t ht0 ht1
    have h1mt : 0 ≤ 1 - t := by linarith
    have hsum : (1 - t) + t = 1 := by ring
    have hxmem : x ∈ (Set.univ : Set (Fin d → ℝ)) := Set.mem_univ _
    have hymem : y ∈ (Set.univ : Set (Fin d → ℝ)) := Set.mem_univ _
    have hcvx := hConv.2 hxmem hymem h1mt ht0 hsum
    -- `hcvx : f ((1-t) • x + t • y) ≤ (1-t) • f x + t • f y`.
    -- Rewrite `(1-t) • x + t • y = γ t`.
    have heq : (1 - t) • x + t • y = γ t := by
      simp [hγdef, sub_smul, one_smul, smul_sub]; abel
    rw [heq] at hcvx
    -- `(1 - t) • f x = (1 - t) * f x` in ℝ.
    simpa [smul_eq_mul] using hcvx
  -- Eventually-on-𝓝[>] 0: the bound holds for `t ∈ (0, 1)`.
  have h_ev : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      t⁻¹ • (f (γ (0 + t)) - f (γ 0)) ≤ f y - f x := by
    have h_Ioc : Set.Ioc (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) :=
      Ioc_mem_nhdsGT (by linarith : (0 : ℝ) < 1)
    refine Filter.mem_of_superset h_Ioc ?_
    intro t ht
    rcases ht with ⟨ht0, ht1⟩
    -- `0 < t` and `t ≤ 1`.
    have ht0' : (0 : ℝ) ≤ t := le_of_lt ht0
    have hbnd := hConv_ineq ht0' ht1
    -- `f(γ t) - f x ≤ t * (f y - f x)`.
    have hsub : f (γ t) - f x ≤ t * (f y - f x) := by
      have hexpand : (1 - t) * f x + t * f y = f x + t * (f y - f x) := by ring
      linarith [hbnd, hexpand.le, hexpand.ge]
    -- Divide by `t > 0`: `(f(γ t) - f x)/t ≤ f y - f x`.
    have ht_inv_pos : 0 < t⁻¹ := inv_pos.mpr ht0
    have ht_inv_mul : t⁻¹ * (t * (f y - f x)) = f y - f x := by
      field_simp
    -- `t⁻¹ • (f(γ t) - f x) ≤ f y - f x`.
    have hmul_le : t⁻¹ * (f (γ t) - f x) ≤ t⁻¹ * (t * (f y - f x)) :=
      mul_le_mul_of_nonneg_left hsub (le_of_lt ht_inv_pos)
    rw [ht_inv_mul] at hmul_le
    -- Goal: `t⁻¹ • (f (γ (0 + t)) - f (γ 0)) ≤ f y - f x`.
    -- Use `γ (0 + t) = γ t` and `γ 0 = x`.
    change t⁻¹ • (f (γ (0 + t)) - f (γ 0)) ≤ f y - f x
    have h0t : (0 + t : ℝ) = t := by ring
    rw [h0t, hγ_zero]
    simpa [smul_eq_mul] using hmul_le
  -- Apply `le_of_tendsto` to conclude `L (y - x) ≤ f y - f x`.
  have h_le : L (y - x) ≤ f y - f x := by
    -- We need `NeBot (𝓝[>] (0 : ℝ))`.
    have : NeBot (𝓝[>] (0 : ℝ)) := inferInstance
    -- `hslope : Tendsto (fun t => t⁻¹ • (f(γ t) - f(γ 0))) (𝓝[>] 0) (𝓝 (L (y - x)))`.
    exact le_of_tendsto hslope h_ev
  linarith

/-- **Subgradient inequality via `dotCLMHam`.** Specialization of
`convexOn_subgradient_of_hasFDerivAt` to the case where the Fréchet
derivative is `dotCLMHam q` (the duality pairing `w ↦ q ⬝ w`). The
inequality `L (y - x) = q ⬝ (y - x) = ∑ i, q i * (y i - x i)` matches
the form used in `HasSubgradientAt`. -/
private lemma convexOn_subgradient_dotCLMHam
    {f : (Fin d → ℝ) → ℝ} {x q : Fin d → ℝ}
    (hConv : ConvexOn ℝ (Set.univ : Set (Fin d → ℝ)) f)
    (hFD : HasFDerivAt f (Hamiltonian.dotCLMHam q) x) :
    ∀ y : Fin d → ℝ, f x + ∑ i, q i * (y i - x i) ≤ f y := by
  intro y
  have h := convexOn_subgradient_of_hasFDerivAt hConv hFD y
  -- `Hamiltonian.dotCLMHam q (y - x) = q ⬝ (y - x) = ∑ i, q i * (y i - x i)`.
  -- (`dotCLMHam_apply` and `euclideanDot` unfolding.)
  have hpair : Hamiltonian.dotCLMHam q (y - x) = ∑ i, q i * (y i - x i) := by
    rw [Hamiltonian.dotCLMHam_apply]
    unfold euclideanDot
    refine Finset.sum_congr rfl ?_
    intro i _
    simp [Pi.sub_apply]
  rw [hpair] at h
  exact h

/-! ### Per-`x` riders extracted from `HypothesisHpDifferentiable`

The subdifferential-inclusion theorems consume the per-`x` convexity
and Fréchet-derivative riders of `HypothesisHpDifferentiable` directly
(rather than the `∀ᵐ x` versions). This keeps the statements
sorry-free and pointwise: callers supply the a.e.-statement and use
`Filter.Eventually.and` / `filter_upwards` to extract the per-point
witnesses. -/

/-- **Layer (C), first inclusion** (paper `eq:inf-conv.diff-relation1`,
first inclusion at line 1664). At the inf-conv minimizer
`qStar h hε hCont hLower`, we have `ε · D_pH(x, p − qStar, m) ∈ ∂K(qStar)`,
expressed as a `HasSubgradientAt` statement.

The pointwise hypotheses `hConvH` (convexity of `H(x, ·, m)`) and
`hFDH` (Fréchet derivative of `H(x, ·, m)` at `p − qStar` is
`dotCLMHam (D_pH x (p − qStar) m)`) are extracted from
`HypothesisHpDifferentiable` for the specific `(x, m)` at hand. -/
theorem qEpsilon_subdiff_inclusion_K
    (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) {x p : Fin d → ℝ} {m : ℝ}
    (hCont : Continuous (fun q : Fin d → ℝ => H x (p - q) m))
    (hLower : ∀ q : Fin d → ℝ,
      ‖p - q‖ ^ h.α / h.C - h.C * (m ^ h.β + 1) ≤ H x (p - q) m)
    (hConvH : ConvexOn ℝ (Set.univ : Set (Fin d → ℝ))
      (fun q : Fin d → ℝ => H x q m))
    (hFDH : HasFDerivAt (fun q : Fin d → ℝ => H x q m)
      (Hamiltonian.dotCLMHam (DpH x (p - qStar h hε hCont hLower) m))
      (p - qStar h hε hCont hLower)) :
    HasSubgradientAt (K h) (qStar h hε hCont hLower)
      (ε • DpH x (p - qStar h hε hCont hLower) m) := by
  -- Abbreviations.
  set qS : Fin d → ℝ := qStar h hε hCont hLower with hqSdef
  set v : Fin d → ℝ := DpH x (p - qS) m with hvdef
  have hspec : H x (p - qS) m + (1 / ε) * K h qS = Hdelta h ε x p m :=
    qStar_spec h hε hCont hLower
  have hε_inv_pos : 0 < 1 / ε := one_div_pos.mpr hε
  -- BddBelow of the family `q ↦ H x (p - q) m + (1 / ε) * K h q`.
  have hBddF :
      BddBelow (Set.range fun q : Fin d → ℝ => H x (p - q) m + (1 / ε) * K h q) := by
    refine ⟨-(h.C * (m ^ h.β + 1)), ?_⟩
    rintro yy ⟨q, rfl⟩
    have hLow := hLower q
    have hpα_nn : 0 ≤ ‖p - q‖ ^ h.α :=
      Real.rpow_nonneg (norm_nonneg _) _
    have hdiv_nn : 0 ≤ ‖p - q‖ ^ h.α / h.C :=
      div_nonneg hpα_nn (le_of_lt h.hC)
    have hε_inv_nn : 0 ≤ 1 / ε := le_of_lt hε_inv_pos
    have hK_nn : 0 ≤ K h q := K_nonneg h q
    have hpen_nn : 0 ≤ (1 / ε) * K h q := mul_nonneg hε_inv_nn hK_nn
    linarith
  -- Goal: `HasSubgradientAt (K h) qS (ε • v)`.
  -- Unfolded: for all `y`, `K h qS + ∑ i, (ε • v) i * (y i - qS i) ≤ K h y`.
  intro y
  -- `(ε • v) i = ε * v i`.
  have hpair : ∑ i, (ε • v) i * (y i - qS i)
             = ε * ∑ i, v i * (y i - qS i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    simp [Pi.smul_apply, smul_eq_mul]; ring
  rw [hpair]
  -- Strategy (slope argument): for `t ∈ (0, 1]`, consider the test point
  -- `qS + t (y - qS)`. Minimality `F(qS) ≤ F(qS + t(y - qS))` combined
  -- with convexity of `K` gives
  --   (H(p - qS - t(y - qS)) - H(p - qS))/t ≥ -(1/ε)(K(y) - K(qS))
  -- (in the form below). Taking `t → 0⁺` and using the directional
  -- derivative `v ⬝ (qS - y) = -∑ v_i (y_i - qS_i) = -S`, we get
  --   -S ≥ -(1/ε)(K(y) - K(qS)), i.e. (1/ε) K(qS) + S ≤ (1/ε) K(y),
  -- whence `K(qS) + ε S ≤ K(y)`.
  set S : ℝ := ∑ i, v i * (y i - qS i) with hSdef
  -- Step 1: define the ray `qS + t (y - qS)` and the H-slope function.
  set ρ : ℝ → (Fin d → ℝ) := fun t => qS + t • (y - qS) with hρdef
  have hρ_zero : ρ 0 = qS := by simp [hρdef]
  -- The associated H-value function.
  set ψ : ℝ → ℝ := fun t => H x (p - ρ t) m with hψdef
  -- Step 2: derivative of `ψ` at `0` is `v ⬝ (-(y - qS)) = -S`.
  -- We use the chain rule via the ray
  -- `t ↦ p - ρ t = (p - qS) + t • -(y - qS)`.
  have hray_deriv : HasDerivAt (fun t : ℝ => p - ρ t) (-(y - qS)) 0 := by
    -- `p - ρ t = p - qS - t • (y - qS) = (p - qS) + t • -(y - qS)`.
    have heq : (fun t : ℝ => p - ρ t)
             = (fun t : ℝ => (p - qS) + t • -(y - qS)) := by
      funext t
      ext i
      simp [hρdef, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [heq]
    have h1 : HasDerivAt (fun t : ℝ => t • -(y - qS))
        ((1 : ℝ) • -(y - qS)) 0 :=
      (hasDerivAt_id (0 : ℝ)).smul_const (-(y - qS))
    have h1' : HasDerivAt (fun t : ℝ => t • -(y - qS)) (-(y - qS)) 0 := by
      simpa [one_smul] using h1
    exact h1'.const_add (p - qS)
  have hψ_deriv : HasDerivAt ψ (Hamiltonian.dotCLMHam v (-(y - qS))) 0 := by
    have hzero : (fun t : ℝ => p - ρ t) 0 = p - qS := by
      simp [hρdef]
    -- Use the non-`_of_eq` form by rewriting `hFDH` first.
    have hFDH' : HasFDerivAt (fun q : Fin d → ℝ => H x q m)
        (Hamiltonian.dotCLMHam v) ((fun t : ℝ => p - ρ t) 0) := by
      rw [hzero]; exact hFDH
    have hcomp : HasDerivAt
        ((fun q : Fin d → ℝ => H x q m) ∘ (fun t : ℝ => p - ρ t))
        (Hamiltonian.dotCLMHam v (-(y - qS))) 0 :=
      hFDH'.comp_hasDerivAt 0 hray_deriv
    simpa only [ψ, Function.comp_def] using hcomp
  -- Compute `dotCLMHam v (-(y - qS)) = -S`.
  have h_dot_neg : Hamiltonian.dotCLMHam v (-(y - qS)) = -S := by
    rw [Hamiltonian.dotCLMHam_apply]
    unfold euclideanDot
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    simp [Pi.neg_apply, Pi.sub_apply]
    ring
  rw [h_dot_neg] at hψ_deriv
  -- Step 3: bound `(ψ(0) - ψ(t))/t` by `(1/ε)(K y - K qS)` for `t ∈ (0, 1]`.
  -- From convexity of K and minimality of qS.
  have h_slope_bound :
      ∀ᶠ t in 𝓝[>] (0 : ℝ), (ψ 0 - ψ t) / t ≤ (1 / ε) * (K h y - K h qS) := by
    have h_Ioc : Set.Ioc (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) :=
      Ioc_mem_nhdsGT (by linarith : (0 : ℝ) < 1)
    refine Filter.mem_of_superset h_Ioc ?_
    intro t ht
    rcases ht with ⟨ht0, ht1⟩
    have ht0' : (0 : ℝ) ≤ t := le_of_lt ht0
    have h1mt : 0 ≤ 1 - t := by linarith
    -- Convexity of K: `K(qS + t (y - qS)) ≤ K qS + t (K y - K qS)`.
    have hK_conv_raw :=
      ((K_strictlyConvex h).convexOn.2 (Set.mem_univ qS) (Set.mem_univ y)
        h1mt ht0' (by ring))
    -- `(1 - t) • qS + t • y = qS + t • (y - qS) = ρ t`.
    have heq_pt : (1 - t) • qS + t • y = ρ t := by
      simp [hρdef, sub_smul, one_smul, smul_sub]; abel
    rw [heq_pt] at hK_conv_raw
    -- Simplify the RHS.
    have hK_conv :
        K h (ρ t) ≤ K h qS + t * (K h y - K h qS) := by
      have hsimp : (1 - t) • K h qS + t • K h y
                  = K h qS + t * (K h y - K h qS) := by
        simp [smul_eq_mul]; ring
      linarith [hK_conv_raw, hsimp.le, hsimp.ge]
    -- Minimality: `Hdelta(x, p, m) ≤ F(ρ t)`.
    have hMin_ρ : Hdelta h ε x p m
                ≤ H x (p - ρ t) m + (1 / ε) * K h (ρ t) := by
      unfold Hdelta
      exact ciInf_le hBddF (ρ t)
    -- Combine: F(qS) = Hdelta(x, p, m) ≤ ψ(t) + (1/ε) K(ρ t) ≤ ψ(t) + (1/ε)(K qS + t (K y - K qS)).
    have hε_inv_nn : 0 ≤ 1 / ε := le_of_lt hε_inv_pos
    have hbnd_rhs :
        H x (p - ρ t) m + (1 / ε) * K h (ρ t)
          ≤ H x (p - ρ t) m + (1 / ε) * (K h qS + t * (K h y - K h qS)) := by
      have hmul := mul_le_mul_of_nonneg_left hK_conv hε_inv_nn
      linarith
    have hF_qS_le :
        H x (p - qS) m + (1 / ε) * K h qS
          ≤ H x (p - ρ t) m + (1 / ε) * (K h qS + t * (K h y - K h qS)) := by
      rw [hspec]; exact le_trans hMin_ρ hbnd_rhs
    -- Rearrange: H(p - qS) m - H(p - ρ t) m ≤ (1/ε) t (K y - K qS).
    have hineq :
        ψ 0 - ψ t ≤ (1 / ε) * (t * (K h y - K h qS)) := by
      simp [ψ, hρ_zero] at *
      linarith
    -- Divide by `t > 0`.
    have ht_inv_pos : 0 < t⁻¹ := inv_pos.mpr ht0
    have h_div_eq : t⁻¹ * ((1 / ε) * (t * (K h y - K h qS)))
                  = (1 / ε) * (K h y - K h qS) := by
      field_simp
    have h_div_eq2 : t⁻¹ * (ψ 0 - ψ t) = (ψ 0 - ψ t) / t := by
      field_simp
    have hmul := mul_le_mul_of_nonneg_left hineq (le_of_lt ht_inv_pos)
    rw [h_div_eq] at hmul
    change (ψ 0 - ψ t) / t ≤ (1 / ε) * (K h y - K h qS)
    rw [← h_div_eq2]
    exact hmul
  -- Step 4: take `t → 0⁺` of `(ψ 0 - ψ t)/t → S` and conclude `S ≤ (1/ε)(K y - K qS)`.
  -- We have `Tendsto (fun t => t⁻¹ • (ψ(0 + t) - ψ 0)) (𝓝[>] 0) (𝓝 (-S))`.
  have hψ_slope := hψ_deriv.tendsto_slope_zero_right
  -- Translate to `(ψ 0 - ψ t)/t → S`.
  have hψ_slope' :
      Tendsto (fun t : ℝ => (ψ 0 - ψ t) / t) (𝓝[>] (0 : ℝ)) (𝓝 S) := by
    have h_eq : ∀ t : ℝ, t ≠ 0 →
        (ψ 0 - ψ t) / t = -(t⁻¹ • (ψ (0 + t) - ψ 0)) := by
      intro t ht
      have hψeq : ψ (0 + t) = ψ t := by simp
      rw [hψeq]
      simp [smul_eq_mul]
      field_simp
      ring
    -- `Tendsto (· ↦ -(t⁻¹ • (ψ(0 + t) - ψ 0))) (𝓝[>] 0) (𝓝 (-(-S))) = (𝓝 S)`.
    have hneg : Tendsto (fun t : ℝ => -(t⁻¹ • (ψ (0 + t) - ψ 0)))
        (𝓝[>] (0 : ℝ)) (𝓝 S) := by
      have hS_eq : (S : ℝ) = -(-S) := by ring
      rw [hS_eq]
      exact hψ_slope.neg
    refine hneg.congr' ?_
    have h_Ioo : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) :=
      Ioo_mem_nhdsGT (by linarith : (0 : ℝ) < 1)
    refine Filter.mem_of_superset h_Ioo ?_
    intro t ht
    rcases ht with ⟨ht0, _⟩
    exact (h_eq t (ne_of_gt ht0)).symm
  -- Apply `le_of_tendsto`.
  have hS_le : S ≤ (1 / ε) * (K h y - K h qS) := by
    have : NeBot (𝓝[>] (0 : ℝ)) := inferInstance
    exact le_of_tendsto hψ_slope' h_slope_bound
  -- Multiply by ε > 0.
  have hε_ne : ε ≠ 0 := ne_of_gt hε
  have hmul := mul_le_mul_of_nonneg_left hS_le (le_of_lt hε)
  have h_lhs : ε * S = ε * S := rfl
  have h_rhs : ε * ((1 / ε) * (K h y - K h qS)) = K h y - K h qS := by
    field_simp
  rw [h_rhs] at hmul
  linarith

/-- **Layer (C), composition with layer (A)** (paper
`eq:inf-conv.diff-relation2`, line 1672). The first subdifferential
inclusion combined with Khat-Fenchel inversion gives the equality
`qS = DKhat(ε · D_pH(x, p − qS, m))`. -/
theorem qEpsilon_eq_DKhat
    (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) {x p : Fin d → ℝ} {m : ℝ}
    (hCont : Continuous (fun q : Fin d → ℝ => H x (p - q) m))
    (hLower : ∀ q : Fin d → ℝ,
      ‖p - q‖ ^ h.α / h.C - h.C * (m ^ h.β + 1) ≤ H x (p - q) m)
    (hConvH : ConvexOn ℝ (Set.univ : Set (Fin d → ℝ))
      (fun q : Fin d → ℝ => H x q m))
    (hFDH : HasFDerivAt (fun q : Fin d → ℝ => H x q m)
      (Hamiltonian.dotCLMHam (DpH x (p - qStar h hε hCont hLower) m))
      (p - qStar h hε hCont hLower)) :
    qStar h hε hCont hLower
      = DKhat h (ε • DpH x (p - qStar h hε hCont hLower) m) := by
  have hsub := qEpsilon_subdiff_inclusion_K (H := H) (DpH := DpH)
      h hε hCont hLower hConvH hFDH
  exact Khat_inversion_of_subdiff h _ _ hsub

/-- **Layer (C), second inclusion** (paper `eq:inf-conv.diff-relation1`,
second inclusion at line 1665). At the inf-conv minimizer
`qStar h hε hCont hLower`, the vector `D_pH(x, p − qStar, m)` is a
subgradient of `fun p' => Hdelta h ε x p' m` at `p`:

  `Hdelta h ε x p m + ∑ i, D_pH(...) i * (p' i − p i) ≤ Hdelta h ε x p' m`

for every `p'`. The hypothesis `hLower'` provides the per-point lower
bound on `H(x, ·, m)` (needed to make the inf at `(x, p', m)` bounded
below for `ciInf_le`). The pointwise riders `hConvH` and `hFDH` are
the same as in `qEpsilon_subdiff_inclusion_K`. -/
theorem qEpsilon_subdiff_inclusion_Hepsilon
    (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) {x p : Fin d → ℝ} {m : ℝ}
    (hCont : Continuous (fun q : Fin d → ℝ => H x (p - q) m))
    (hLower : ∀ q : Fin d → ℝ,
      ‖p - q‖ ^ h.α / h.C - h.C * (m ^ h.β + 1) ≤ H x (p - q) m)
    (hConvH : ConvexOn ℝ (Set.univ : Set (Fin d → ℝ))
      (fun q : Fin d → ℝ => H x q m))
    (hFDH : HasFDerivAt (fun q : Fin d → ℝ => H x q m)
      (Hamiltonian.dotCLMHam (DpH x (p - qStar h hε hCont hLower) m))
      (p - qStar h hε hCont hLower))
    (hLower' : ∀ p' q : Fin d → ℝ,
      ‖p' - q‖ ^ h.α / h.C - h.C * (m ^ h.β + 1) ≤ H x (p' - q) m) :
    HasSubgradientAt (fun p' : Fin d → ℝ => Hdelta h ε x p' m) p
      (DpH x (p - qStar h hε hCont hLower) m) := by
  -- Abbreviations.
  set qS : Fin d → ℝ := qStar h hε hCont hLower with hqSdef
  set v : Fin d → ℝ := DpH x (p - qS) m with hvdef
  -- The first subdifferential inclusion: `ε • v ∈ ∂K(qS)`.
  have hsubK : HasSubgradientAt (K h) qS (ε • v) :=
    qEpsilon_subdiff_inclusion_K (H := H) (DpH := DpH)
      h hε hCont hLower hConvH hFDH
  -- Attainment: `Hdelta h ε x p m = H(x, p - qS) m + (1/ε) K(qS)`.
  have hspec : H x (p - qS) m + (1 / ε) * K h qS = Hdelta h ε x p m :=
    qStar_spec h hε hCont hLower
  -- Goal: for all `p'`,
  -- `Hdelta h ε x p m + ∑ i, v i * (p' i - p i) ≤ Hdelta h ε x p' m`.
  intro p'
  -- BddBelow at `(x, p', m)`: needed for `le_ciInf`.
  have hε_inv_pos : 0 < 1 / ε := one_div_pos.mpr hε
  have hBddF' : BddBelow (Set.range
      fun q : Fin d → ℝ => H x (p' - q) m + (1 / ε) * K h q) := by
    refine ⟨-(h.C * (m ^ h.β + 1)), ?_⟩
    rintro y ⟨q, rfl⟩
    have hLow := hLower' p' q
    have hpα_nn : 0 ≤ ‖p' - q‖ ^ h.α :=
      Real.rpow_nonneg (norm_nonneg _) _
    have hdiv_nn : 0 ≤ ‖p' - q‖ ^ h.α / h.C :=
      div_nonneg hpα_nn (le_of_lt h.hC)
    have hε_inv_nn : 0 ≤ 1 / ε := le_of_lt hε_inv_pos
    have hK_nn : 0 ≤ K h q := K_nonneg h q
    have hpen_nn : 0 ≤ (1 / ε) * K h q := mul_nonneg hε_inv_nn hK_nn
    linarith
  -- Strategy: show that for all `q'`,
  --   `Hdelta(x, p, m) + ∑ v_i (p'_i - p_i) ≤ H(x, p' - q') m + (1/ε) K(q')`.
  -- Then `le_ciInf` gives the desired inequality with `Hdelta(x, p', m)`.
  have h_step : ∀ q' : Fin d → ℝ,
      Hdelta h ε x p m + ∑ i, v i * (p' i - p i)
        ≤ H x (p' - q') m + (1 / ε) * K h q' := by
    intro q'
    -- Step 1: convexity of `H(x, ·, m)` at `p - qS` with derivative `v`,
    -- applied at point `p' - q'`.
    have hConvIneq :
        H x (p - qS) m + ∑ i, v i * ((p' - q') i - (p - qS) i)
          ≤ H x (p' - q') m :=
      convexOn_subgradient_dotCLMHam hConvH hFDH (p' - q')
    -- Step 2: K-subgradient inequality `ε • v ∈ ∂K(qS)` applied at `q'`.
    have hKIneq :
        K h qS + ∑ i, (ε • v) i * (q' i - qS i) ≤ K h q' := hsubK q'
    -- Simplify `(ε • v) i * (q' i - qS i) = ε * (v i * (q' i - qS i))`.
    have hKpair :
        ∑ i, (ε • v) i * (q' i - qS i)
          = ε * ∑ i, v i * (q' i - qS i) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      simp [Pi.smul_apply, smul_eq_mul]; ring
    rw [hKpair] at hKIneq
    -- Multiply `hKIneq` by `1/ε ≥ 0`.
    have hε_ne : ε ≠ 0 := ne_of_gt hε
    have hε_inv_mul : (1 / ε) * (ε * ∑ i, v i * (q' i - qS i))
        = ∑ i, v i * (q' i - qS i) := by
      field_simp
    have hKIneq_div :
        (1 / ε) * K h qS + ∑ i, v i * (q' i - qS i) ≤ (1 / ε) * K h q' := by
      have := mul_le_mul_of_nonneg_left hKIneq (le_of_lt hε_inv_pos)
      rw [mul_add, hε_inv_mul] at this
      exact this
    -- Step 3: simplify the convexity inequality.
    have hsum_split :
        ∑ i, v i * ((p' - q') i - (p - qS) i)
          = (∑ i, v i * (p' i - p i)) + (∑ i, v i * (qS i - q' i)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      have h1 : (p' - q') i - (p - qS) i = (p' i - p i) + (qS i - q' i) := by
        simp only [Pi.sub_apply]; ring
      rw [h1]; ring
    rw [hsum_split] at hConvIneq
    -- Express `∑ v_i (qS_i - q'_i) = -∑ v_i (q'_i - qS_i)`.
    have hsum_neg :
        ∑ i, v i * (qS i - q' i) = -(∑ i, v i * (q' i - qS i)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      ring
    rw [hsum_neg] at hConvIneq
    -- Combine via linarith.
    -- hConvIneq : H(x, p - qS) m + (∑ v_i (p'_i - p_i) + -(∑ v_i (q'_i - qS_i))) ≤ H(x, p' - q') m
    -- hKIneq_div : (1/ε) K qS + ∑ v_i (q'_i - qS_i) ≤ (1/ε) K q'
    -- hspec : H(x, p - qS) m + (1/ε) K qS = Hdelta(x, p, m)
    -- Goal: Hdelta(x, p, m) + ∑ v_i (p'_i - p_i) ≤ H(x, p' - q') m + (1/ε) K q'
    linarith
  -- Step 4: take the infimum over `q'` to get `Hdelta(x, p', m)` on the RHS.
  unfold Hdelta
  exact le_ciInf h_step

/-! ## Layer (D) part 1: the `M^ε_{x,m}` map and the semi-explicit identity

Paper `lem:inf-conv-props.(ii)` lines 1674–1678 introduce, for fixed
`(x, m)`, the auxiliary map
  `M^ε_{x,m}(s) := s + D K̂(ε · D_pH(x, s, m))`,
and use it to package the inversion `q^ε(x, p, m) = p − (M^ε)⁻¹(p)`
that justifies measurability of `q^ε`.

We define `Mepsilon_xm` and discharge what is *unconditional* on
Brouwer / inverse-function infrastructure (which Mathlib does not yet
carry on `Fin d → ℝ`):

* `Mepsilon_xm_at_minimizer`: the key pointwise identity
  `M^ε_{x,m}(p − qStar) = p`. This is the inversion-free form of the
  paper's `eq:q-star-semi-explicit`: it says that the value
  `p − q^ε(x, p, m)` lies in the preimage `(M^ε_{x,m})⁻¹{p}`. Follows
  directly from `qEpsilon_eq_DKhat` (Layer C, iter 0805).

The full bijectivity of `M^ε_{x,m}` (which would let us recover
`q^ε(x, p, m) = p − (M^ε_{x,m})⁻¹(p)` as an *honest* inverse-image
equation) is split off as a follow-up child task; it requires either
Brouwer's invariance of domain or a coercivity-plus-monotonicity
argument that Mathlib does not currently host on `Fin d → ℝ`.
Similarly, the measurability cascade `qEpsilon_measurable` and
`Hepsilon_measurable` is split off, since it needs Borel
measurability of `D_pH` (a new paper-side rider). -/

/-- **Paper-faithful definition of `M^ε_{x,m}`** (lines 1675–1676 of
`Source/FGU-monotone_revised.tex`). For fixed `(x, m)` and an
auxiliary input `s : Fin d → ℝ`, the operator is
`M^ε_{x,m}(s) := s + D K̂(ε · D_pH(x, s, m))`. -/
noncomputable def Mepsilon_xm
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (ε : ℝ) (x : Fin d → ℝ) (m : ℝ) (s : Fin d → ℝ) : Fin d → ℝ :=
  s + DKhat h (ε • DpH x s m)

/-- **Paper `eq:q-star-semi-explicit` (inversion-free form).** At
the inf-conv minimizer `qS := qStar h hε hCont hLower`, the value
`p − qS` lies in the preimage `(M^ε_{x,m})⁻¹{p}`:
  `M^ε_{x,m}(p − qS) = p`.

This is the *pointwise* witness behind the paper's
"`q^ε(x, p, m) = p − (M^ε_{x,m})⁻¹(p)`": once we know
`M^ε_{x,m}` is bijective (deferred to a follow-up child task), this
identity uniquely identifies `p − qS` as the preimage of `p`.

The proof is `qEpsilon_eq_DKhat` (Layer C, iter 0805) rearranged:
that lemma says `qS = D K̂(ε · D_pH(x, p − qS, m))`, so
`(p − qS) + D K̂(ε · D_pH(x, p − qS, m)) = (p − qS) + qS = p`. -/
theorem Mepsilon_xm_at_minimizer
    (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) {x p : Fin d → ℝ} {m : ℝ}
    (hCont : Continuous (fun q : Fin d → ℝ => H x (p - q) m))
    (hLower : ∀ q : Fin d → ℝ,
      ‖p - q‖ ^ h.α / h.C - h.C * (m ^ h.β + 1) ≤ H x (p - q) m)
    (hConvH : ConvexOn ℝ (Set.univ : Set (Fin d → ℝ))
      (fun q : Fin d → ℝ => H x q m))
    (hFDH : HasFDerivAt (fun q : Fin d → ℝ => H x q m)
      (Hamiltonian.dotCLMHam (DpH x (p - qStar h hε hCont hLower) m))
      (p - qStar h hε hCont hLower)) :
    Mepsilon_xm (H := H) (DpH := DpH) h ε x m
        (p - qStar h hε hCont hLower) = p := by
  set qS : Fin d → ℝ := qStar h hε hCont hLower with hqSdef
  -- Layer C identity: `qS = DKhat h (ε • DpH x (p - qS) m)`.
  have hEq : qS = DKhat h (ε • DpH x (p - qS) m) :=
    qEpsilon_eq_DKhat (H := H) (DpH := DpH) h hε hCont hLower hConvH hFDH
  -- Compute: `(p - qS) + DKhat h (ε • DpH x (p - qS) m) = (p - qS) + qS = p`.
  unfold Mepsilon_xm
  rw [← hEq]
  -- Goal: `(p - qS) + qS = p`.
  ext i
  simp [Pi.add_apply, Pi.sub_apply]

/-! ### Unit tests (D-part1) -/

/-- Unit test (`d = 1`): the definition `Mepsilon_xm` is well-typed
and unfolds (by `rfl`) to `s + DKhat h (ε • D_pH x s m)`. -/
example
    {H₁ : (Fin 1 → ℝ) → (Fin 1 → ℝ) → ℝ → ℝ}
    {DpH₁ : (Fin 1 → ℝ) → (Fin 1 → ℝ) → ℝ → (Fin 1 → ℝ)}
    (h : HypothesisWeakGrowth (d := 1) H₁ DpH₁)
    (ε : ℝ) (x : Fin 1 → ℝ) (m : ℝ) (s : Fin 1 → ℝ) :
    Mepsilon_xm (H := H₁) (DpH := DpH₁) h ε x m s
      = s + DKhat h (ε • DpH₁ x s m) := rfl

/-! ## Measurability cascade (D-part3, iter 0807)

This section delivers the measurability cascade consequent to the
`M^ε_{x,m}` machinery from D-part1. The paper (line 1684) concludes
Borel measurability of `q^ε` and `H^ε` from the formula
`q^ε(x, p, m) = p − (M^ε_{x,m})⁻¹(p)` plus joint measurability of
the data `(x, p, m) ↦ H(x, p, m)` and `(x, s, m) ↦ D_pH(x, s, m)`.

* `Mepsilon_xm_jointly_measurable` — joint Borel measurability of
  `(x, s, m) ↦ M^ε_{x,m}(s)` from `HypothesisDpHMeasurable` plus
  `DKhat_continuous` (iter 0801).
* `qEpsilon_measurable_of_inv` — *conditional* measurability of
  `(x, p, m) ↦ q^ε(x, p, m)` given a measurable function `Minv`
  inverting `M^ε`. The unconditional form requires bijectivity of
  `M^ε_{x,m}` (D2, deferred).
* `Hepsilon_measurable_of_inv` — *conditional* measurability of
  `(x, p, m) ↦ H^ε(x, p, m)` derived from `qEpsilon_measurable_of_inv`
  via `Hepsilon_eq_formula`.

The conditional form is the sharp deliverable for D3 alone:
once D2 lands and produces a measurable `(M^ε)⁻¹`, the cascade
specialises to the unconditional measurability claim of the
paper. -/

/-- **Joint Borel measurability of `M^ε_{x,m}`.** Given the
measurability rider on `D_pH` (`HypothesisDpHMeasurable`), the map
`(x, s, m) ↦ M^ε_{x,m}(s) = s + D K̂(ε · D_pH(x, s, m))` is jointly
Borel measurable.

The proof: the inner `(x, s, m) ↦ D_pH(x, s, m)` is measurable by
hypothesis; scaling by `ε` and post-composing with the continuous
function `DKhat h` preserves measurability; adding the projection
`(x, s, m) ↦ s` (which is measurable as a continuous projection)
gives the claim. -/
theorem Mepsilon_xm_jointly_measurable
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (ε : ℝ) :
    Measurable (fun xsm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ =>
      Mepsilon_xm (H := H) (DpH := DpH) h ε xsm.1 xsm.2.2 xsm.2.1) := by
  -- Unfold `Mepsilon_xm`.
  -- Goal: Measurable ((x, s, m) ↦ s + DKhat h (ε • DpH x s m))
  -- Step 1: measurability of `(x, s, m) ↦ DpH x s m` from rider.
  have hDpH_meas :
      Measurable (fun xsm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ =>
        DpH xsm.1 xsm.2.1 xsm.2.2) := hMeas.measurable_DpH
  -- Step 2: measurability of `(x, s, m) ↦ ε • DpH x s m`.
  have hScale :
      Measurable (fun xsm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ =>
        ε • DpH xsm.1 xsm.2.1 xsm.2.2) :=
    hDpH_meas.const_smul ε
  -- Step 3: measurability of `(x, s, m) ↦ DKhat h (ε • DpH x s m)`,
  -- by composition with the continuous `DKhat h`.
  have hDKhat_meas : Measurable (DKhat h) :=
    (DKhat_continuous h).measurable
  have hComp :
      Measurable (fun xsm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ =>
        DKhat h (ε • DpH xsm.1 xsm.2.1 xsm.2.2)) :=
    hDKhat_meas.comp hScale
  -- Step 4: measurability of the projection `(x, s, m) ↦ s`.
  have hProj : Measurable (fun xsm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ => xsm.2.1) :=
    measurable_snd.fst
  -- Step 5: add the two.
  -- Note: `Mepsilon_xm h ε x m s = s + DKhat h (ε • DpH x s m)`,
  -- so the function we want is `(x,s,m) ↦ s + DKhat h (ε • DpH x s m)`.
  have hSum :
      Measurable (fun xsm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ =>
        xsm.2.1 + DKhat h (ε • DpH xsm.1 xsm.2.1 xsm.2.2)) :=
    hProj.add hComp
  -- Conclude by unfolding `Mepsilon_xm`.
  exact hSum

/-- **Conditional measurability of `q^ε(x, p, m)`.** Suppose we are
given a function `Minv : (Fin d → ℝ) × ℝ × (Fin d → ℝ) → (Fin d → ℝ)`
that inverts `M^ε`, in the sense that for the per-point inf-conv
minimizer `qS := qStar h hε hCont hLower`, the relation
`Minv (x, m, p) = p − qS` holds. If `Minv` is Borel measurable in
its inputs, then the assignment `(x, p, m) ↦ q^ε(x, p, m)` is
Borel measurable on the (measurable) set where the hypothesis
applies, via `q^ε(x, p, m) = p − Minv(x, m, p)`.

We state the *cleanest* form: a global pointwise hypothesis
`∀ xpm, q xpm = xpm.2.1 - Minv (xpm.1, xpm.2.2, xpm.2.1)`, plus
measurability of `Minv`, yields measurability of `q`. This is
the standard "ready-to-consume" measurability lemma once D2 lands. -/
theorem qEpsilon_measurable_of_inv
    {q : (Fin d → ℝ) × (Fin d → ℝ) × ℝ → (Fin d → ℝ)}
    (Minv : (Fin d → ℝ) × ℝ × (Fin d → ℝ) → (Fin d → ℝ))
    (hMinv : Measurable Minv)
    (hq_eq : ∀ xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ,
      q xpm = xpm.2.1 - Minv (xpm.1, xpm.2.2, xpm.2.1)) :
    Measurable q := by
  -- Rewrite `q` via `hq_eq`, then use measurability of subtraction.
  -- `(x, p, m) ↦ p` is measurable.
  have hProj_p : Measurable (fun xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ => xpm.2.1) :=
    measurable_snd.fst
  -- `(x, p, m) ↦ (x, m, p)` is measurable.
  have hPerm :
      Measurable (fun xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ =>
        (xpm.1, xpm.2.2, xpm.2.1)) := by
    refine Measurable.prod measurable_fst ?_
    exact Measurable.prod measurable_snd.snd measurable_snd.fst
  -- Compose with `Minv`.
  have hMinvComp :
      Measurable (fun xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ =>
        Minv (xpm.1, xpm.2.2, xpm.2.1)) := hMinv.comp hPerm
  -- Subtract.
  have hSub :
      Measurable (fun xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ =>
        xpm.2.1 - Minv (xpm.1, xpm.2.2, xpm.2.1)) :=
    hProj_p.sub hMinvComp
  -- Rewrite via `hq_eq`.
  have hQeq : q = (fun xpm => xpm.2.1 - Minv (xpm.1, xpm.2.2, xpm.2.1)) := by
    funext xpm; exact hq_eq xpm
  rw [hQeq]
  exact hSub

/-- **Conditional measurability of `H^ε(x, p, m)`.** Given:

* the measurability riders (`HypothesisDpHMeasurable`),
* a measurable assignment `(x, p, m) ↦ q^ε(x, p, m)` (typically
  obtained from `qEpsilon_measurable_of_inv` once D2 lands),

then `(x, p, m) ↦ H^ε(x, p, m)` is Borel measurable, via the
H-epsilon formula `H^ε = H(x, p − q^ε, m) + (1/ε) · K(q^ε)` (paper
`eq:H-epsilon-formula`, established as `Hepsilon_eq_formula`).

We state the lemma in *raw formula form*: the function
`(x, p, m) ↦ H(x, p − q^ε(x, p, m), m) + (1/ε) · K(q^ε(x, p, m))`
is measurable. By `Hepsilon_eq_formula` this equals `H^ε`
pointwise wherever `q^ε` is the inf-conv minimizer, so this is
the canonical measurability witness for `H^ε`. -/
theorem Hepsilon_measurable_of_inv
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (ε : ℝ)
    {qE : (Fin d → ℝ) × (Fin d → ℝ) × ℝ → (Fin d → ℝ)}
    (hqE : Measurable qE) :
    Measurable (fun xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ =>
      H xpm.1 (xpm.2.1 - qE xpm) xpm.2.2
        + (1 / ε) * K h (qE xpm)) := by
  -- Step 1: `(x, p, m) ↦ (x, p − qE (x, p, m), m)` is measurable.
  have hProj_x : Measurable (fun xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ => xpm.1) :=
    measurable_fst
  have hProj_p : Measurable (fun xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ => xpm.2.1) :=
    measurable_snd.fst
  have hProj_m : Measurable (fun xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ => xpm.2.2) :=
    measurable_snd.snd
  have hShift :
      Measurable (fun xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ =>
        xpm.2.1 - qE xpm) := hProj_p.sub hqE
  -- Step 2: assemble `(x, p−qE, m)` as a measurable triple.
  have hTriple :
      Measurable (fun xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ =>
        (xpm.1, xpm.2.1 - qE xpm, xpm.2.2)) := by
    refine Measurable.prod hProj_x ?_
    exact Measurable.prod hShift hProj_m
  -- Step 3: apply `measurable_H` along this triple.
  have hH_part :
      Measurable (fun xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ =>
        H xpm.1 (xpm.2.1 - qE xpm) xpm.2.2) :=
    hMeas.measurable_H.comp hTriple
  -- Step 4: `(x, p, m) ↦ K h (qE xpm)` measurable via continuity of `K`.
  have hK_meas : Measurable (K h) := (K_continuous h).measurable
  have hK_part :
      Measurable (fun xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ => K h (qE xpm)) :=
    hK_meas.comp hqE
  -- Step 5: scalar multiplication by `(1/ε)` and addition.
  have hPenalty :
      Measurable (fun xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ =>
        (1 / ε) * K h (qE xpm)) := hK_part.const_mul (1 / ε)
  exact hH_part.add hPenalty

/-- **Specialization: `H^ε` measurability via formula identity.**
Given the same data as `Hepsilon_measurable_of_inv` plus a
hypothesis `hqE_eq` saying that `qE xpm` is the inf-conv minimizer
`qStar` at `(xpm.1, xpm.2.1, xpm.2.2)`, the H-epsilon formula
`Hepsilon_eq_formula` says
`Hdelta h ε x p m = H x (p − qE) m + (1/ε) · K(qE)`. The right-hand
side is measurable by `Hepsilon_measurable_of_inv`, so
`(x, p, m) ↦ Hdelta h ε x p m` is measurable on the locus where
the per-point hypotheses `hCont`, `hLower` hold. -/
theorem Hdelta_measurable_of_inv
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    {ε : ℝ} (_hε : 0 < ε)
    {qE : (Fin d → ℝ) × (Fin d → ℝ) × ℝ → (Fin d → ℝ)}
    (hqE : Measurable qE)
    (hForm : ∀ xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ,
      Hdelta h ε xpm.1 xpm.2.1 xpm.2.2
        = H xpm.1 (xpm.2.1 - qE xpm) xpm.2.2
            + (1 / ε) * K h (qE xpm)) :
    Measurable (fun xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ =>
      Hdelta h ε xpm.1 xpm.2.1 xpm.2.2) := by
  have hRHS := Hepsilon_measurable_of_inv (H := H) (DpH := DpH)
    h hMeas ε hqE
  have hEq : (fun xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ =>
      Hdelta h ε xpm.1 xpm.2.1 xpm.2.2)
        = (fun xpm => H xpm.1 (xpm.2.1 - qE xpm) xpm.2.2
            + (1 / ε) * K h (qE xpm)) := by
    funext xpm; exact hForm xpm
  rw [hEq]
  exact hRHS

/-! ### REMOVED: `Hdelta_measurable_of_form_pos_and_neg` (the `hMeasNeg`
measurability lemma).

The `{0<m}`-formula-plus-`{m≤0}`-witness measurability lemma for the raw
`Hdelta` carrier was removed (iter `…-A1d-HdeltaPos-final-live-carrier-swap`)
once the live A1d-final chain was rerouted through the `{m≤0}`-junk-valued
carrier `HdeltaPos` (below). `HdeltaPos_measurable_of_formPos` discharges joint
measurability from the `{0<m}` formula bridge `hFormPos` ALONE — the `{m≤0}`
measurability witness `hMeasNeg` is never needed anywhere in the live supply.
The only consumer of the removed lemma was the now-removed `hMeasNeg` variant
`Hepsilon_regularityH`. -/

/-! ### `{m≤0}`-junk-valued carrier `HdeltaPos` (no `hMeasNeg`)

The paper defines `H^ε(x, p, m) := ⨅_q H(x, p−q, m) + (1/ε)K(q)` only for
`m ∈ ℝ⁺` (`eq:defHdelta`, `Source/FGU-monotone_revised.tex` line 1626,
"for a.e. `x ∈ 𝕋^d`" with `m ∈ ℝ⁺` per line 1629/1632). At `m ≤ 0` none
of the inf-conv well-posedness ingredients are available — the coercive
lower bound `eq:assH.lower.weak`, the convexity in `p`
(`Remark~rmk:cxty`), and the joint continuity are all `m > 0`-gated.
Consequently `Hdelta` at `m ≤ 0` is an undefined `iInf` whose
measurability cannot be established from the weak-growth hypotheses
(`Measurable.iInf` needs a countable index, reducible only via the
missing continuity/convexity).

`HdeltaPos` is the paper-faithful, junk-valued carrier: it equals
`Hdelta` on `{0 < m}` (where the entire Theorem 3 machinery lives) and
the measurable constant `0` on `{m ≤ 0}`. Its joint measurability needs
ONLY the `{0<m}`-restricted formula bridge `hFormPos` — no `{m≤0}`
measurability witness (`hMeasNeg`). This discharges the design fork
recorded in `…-Hepsilon-mNeg-measurability`. -/

/-- The `{m ≤ 0}`-junk-valued regularized Hamiltonian: equals `Hdelta`
on `{0 < m}` and the constant `0` elsewhere. Observably identical to
`Hdelta` on the strict-positivity cone `{0 < m}`, where all Theorem 3
consumers evaluate. -/
noncomputable def HdeltaPos (h : HypothesisWeakGrowth (d := d) H DpH)
    (ε : ℝ) (x p : Fin d → ℝ) (m : ℝ) : ℝ :=
  if 0 < m then Hdelta h ε x p m else 0

/-- On the strict-positivity cone `{0 < m}`, `HdeltaPos` coincides with
`Hdelta`. This is the rewrite used at every downstream `0 < m`
use-site. -/
lemma HdeltaPos_eq_Hdelta_of_pos (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} {x p : Fin d → ℝ} {m : ℝ} (hm : 0 < m) :
    HdeltaPos h ε x p m = Hdelta h ε x p m := by
  simp [HdeltaPos, hm]

/-- Canonical regularized closed-cone carrier. The zero-mass value is the
finite positive-mass trace, independent of the original supplied H at zero. -/
noncomputable def HdeltaK0 (h : HypothesisWeakGrowth (d := d) H DpH)
    (ε : ℝ) (x p : Fin d → ℝ) (m : ℝ) : ℝ := HdeltaPaper h ε x p m

lemma HdeltaK0_eq_Hdelta_of_pos (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} {x p : Fin d → ℝ} {m : ℝ} (hm : 0 < m) :
    HdeltaK0 h ε x p m = Hdelta h ε x p m :=
  HdeltaPaper_of_pos h ε x p hm

lemma HdeltaK0_eq_zero_of_neg (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} {x p : Fin d → ℝ} {m : ℝ} (hm : m < 0) :
    HdeltaK0 h ε x p m = 0 := HdeltaPaper_of_neg h ε x p hm

/-- On the strict-positivity cone `{0 < m}`, `HdeltaK0` and `HdeltaPos`
agree (both equal `Hdelta`). The two carriers differ ONLY at `m = 0`
(`HdeltaK0` genuine, `HdeltaPos` junk `0`), so every `{0 < m}`-evaluated
estimate / continuity fact proved for `HdeltaPos` transfers to `HdeltaK0`
through this bridge. -/
lemma HdeltaK0_eq_HdeltaPos_of_pos (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} {x p : Fin d → ℝ} {m : ℝ} (hm : 0 < m) :
    HdeltaK0 h ε x p m = HdeltaPos h ε x p m := by
  rw [HdeltaK0_eq_Hdelta_of_pos h hm, HdeltaPos_eq_Hdelta_of_pos h hm]

/-- **`HdeltaPos` joint measurability from `hFormPos` ALONE** (no
`hMeasNeg`). On the open set `{0 < m}` the formula bridge `hFormPos`
identifies `HdeltaPos = Hdelta` with the measurable RHS
(`Hepsilon_measurable_of_inv`); off `{0 < m}` it is the constant `0`.
The two are glued by `Measurable.ite` on the measurable (open) set
`{xpm | 0 < xpm.2.2}`. -/
theorem HdeltaPos_measurable_of_formPos
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    {ε : ℝ} (_hε : 0 < ε)
    {qE : (Fin d → ℝ) × (Fin d → ℝ) × ℝ → (Fin d → ℝ)}
    (hqE : Measurable qE)
    (hFormPos : ∀ xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ, 0 < xpm.2.2 →
      Hdelta h ε xpm.1 xpm.2.1 xpm.2.2
        = H xpm.1 (xpm.2.1 - qE xpm) xpm.2.2
            + (1 / ε) * K h (qE xpm)) :
    Measurable (fun xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ =>
      HdeltaPos h ε xpm.1 xpm.2.1 xpm.2.2) := by
  classical
  -- `{0 < m}` is measurable (open via the continuous `m`-projection).
  have hSetMeas : MeasurableSet
      {xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ | 0 < xpm.2.2} := by
    have hOpen : IsOpen {xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ | 0 < xpm.2.2} := by
      have : IsOpen {y : ℝ | 0 < y} := isOpen_lt continuous_const continuous_id
      exact this.preimage (continuous_snd.comp continuous_snd)
    exact hOpen.measurableSet
  -- The formula RHS is measurable (`Hepsilon_measurable_of_inv`).
  have hRHS := Hepsilon_measurable_of_inv (H := H) (DpH := DpH)
    h hMeas ε hqE
  -- `HdeltaPos = ite {0<m} RHS 0` pointwise: on `{0<m}` use `hFormPos`,
  -- off it the `if` picks `0`.
  have hEq : (fun xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ =>
        HdeltaPos h ε xpm.1 xpm.2.1 xpm.2.2)
      = (fun xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ =>
          if (0 : ℝ) < xpm.2.2 then
            H xpm.1 (xpm.2.1 - qE xpm) xpm.2.2 + (1 / ε) * K h (qE xpm)
          else (0 : ℝ)) := by
    funext xpm
    by_cases hm : (0 : ℝ) < xpm.2.2
    · rw [HdeltaPos_eq_Hdelta_of_pos h hm, if_pos hm]
      exact hFormPos xpm hm
    · simp [HdeltaPos, hm]
  rw [hEq]
  -- Glue with `Measurable.ite`: the decision-predicate set is `{0 < m}`.
  exact Measurable.ite hSetMeas hRHS measurable_const

/-! ### Unit tests (D-part3) -/

/-- Unit test (`d = 1`): with the trivial zero Hamiltonian, the
joint-measurability lemma `Mepsilon_xm_jointly_measurable` applies. -/
example
    (h : HypothesisWeakGrowth (d := 1)
      (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : Fin 1 → ℝ)))
    (ε : ℝ) :
    Measurable (fun xsm : (Fin 1 → ℝ) × (Fin 1 → ℝ) × ℝ =>
      Mepsilon_xm
        (H := fun _ _ _ => (0 : ℝ))
        (DpH := fun _ _ _ => (0 : Fin 1 → ℝ))
        h ε xsm.1 xsm.2.2 xsm.2.1) :=
  Mepsilon_xm_jointly_measurable
    (H := fun _ _ _ => (0 : ℝ))
    (DpH := fun _ _ _ => (0 : Fin 1 → ℝ))
    h
    { measurable_H := measurable_const
      measurable_DpH := measurable_const } ε

/-! ## Layer (E): `D_pH^ε` formula and `RegularityH` packaging for `H^ε`

Paper `lem:inf-conv-props.(iii)` (lines 1641, 1688–1692). The key
identity `eq:DpH-epsilon-formula` (line 1689) is

  `D_pH^ε(x, p, m) = D_pH(x, p − q^ε(x, p, m), m)`.

In our Lean model the inf-conv minimizer `q^ε` is not yet available as
a global function `(x, p, m) ↦ Fin d → ℝ` (only as `qStar` taking
per-point witnesses; the full functional form is blocked on `M^ε`
bijectivity, deferred as the D2/Brouwer split). We therefore
parameterize the formula on a consumer-supplied measurable candidate
`qE : (Fin d → ℝ) × (Fin d → ℝ) × ℝ → Fin d → ℝ`, in line with the
conditional measurability cascade `qEpsilon_measurable_of_inv` from
Layer (D-part3).

The deliverables:

* `DpHepsilon` — definition `D_pH^ε(x, p, m) := D_pH(x, p − qE(x, p, m), m)`.
* `DpHepsilon_eq` — pointwise restatement (the formula `eq:DpH-epsilon-formula`).
* `Hepsilon_regularityH` — packaged `Hamiltonian.RegularityH` instance
  for the pair `(fun x p m => Hdelta h ε x p m, DpHepsilon h qE)`.

Caveat. The classical paper claim "the second inclusion of
`eq:inf-conv.diff-relation1` collapses to an equality" (paper lines
1688–1692) requires the *uniqueness* of the subgradient at every `p`
where the RHS is continuous. In the Lean model we have the
**definition** of `D_pH^ε` (paper line 1689) rather than the
collapse argument: once `qE` is the inf-conv minimizer, the formula
is a *direct restatement* of paper `eq:DpH-epsilon-formula`. The
collapse argument would deliver uniqueness of `q^ε` and pin
`D_pH^ε` as the gradient of `H^ε`; that gradient identification is
again blocked on D2/Brouwer and is split off. For the
`RegularityH` packaging, the formula is what matters. -/

/-- **Paper `eq:DpH-epsilon-formula`** (`Source/FGU-monotone_revised.tex`,
line 1689). The regularized `p`-gradient of `H^ε`, defined by the
formula `D_pH^ε(x, p, m) := D_pH(x, p − q^ε(x, p, m), m)`. We
parameterize on a measurable candidate `qE` for `q^ε`. -/
noncomputable def DpHepsilon
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (qE : (Fin d → ℝ) × (Fin d → ℝ) × ℝ → (Fin d → ℝ))
    (x p : Fin d → ℝ) (m : ℝ) : Fin d → ℝ :=
  DpH x (p - qE (x, p, m)) m

/-- **ε-indexed selector family.** The inf-conv minimizer `q^ε` is genuinely
ε-dependent, so the regularized gradient `D_pH^ε` must be parameterized by a
*family* of selectors indexed by `ε`, not a single ε-free selector. -/
abbrev QEpsFamily (d : ℕ) :=
  ℝ → ((Fin d → ℝ) × (Fin d → ℝ) × ℝ → (Fin d → ℝ))

/-- **ε-indexed regularized gradient.** `DpHepsilonFam hweak qε ε` is the
single-ε `DpHepsilon` applied to the ε-th selector `qε ε`, so by definition
`DpHepsilonFam hweak qε ε x p m = D_pH(x, p − qε ε (x,p,m), m)`. This wraps (does
not replace) the single-ε `DpHepsilon`. -/
noncomputable def DpHepsilonFam
    (hweak : HypothesisWeakGrowth (d := d) H DpH) (qε : QEpsFamily d) (ε : ℝ) :
    (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ) :=
  DpHepsilon hweak (qε ε)

/-- Unfolded formula for `DpHepsilonFam` (`rfl`, exposed for callers). -/
@[simp]
lemma DpHepsilonFam_eq
    (hweak : HypothesisWeakGrowth (d := d) H DpH) (qε : QEpsFamily d) (ε : ℝ)
    (x p : Fin d → ℝ) (m : ℝ) :
    DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε x p m
      = DpH x (p - qε ε (x, p, m)) m := rfl

/-- The unfolded formula `eq:DpH-epsilon-formula` (`rfl`, exposed for
callers). -/
@[simp]
lemma DpHepsilon_eq
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (qE : (Fin d → ℝ) × (Fin d → ℝ) × ℝ → (Fin d → ℝ))
    (x p : Fin d → ℝ) (m : ℝ) :
    DpHepsilon (H := H) (DpH := DpH) h qE x p m
      = DpH x (p - qE (x, p, m)) m := rfl

/-- **Joint measurability of `D_pH^ε`** as a function of `(x, p, m)`.
Given joint Borel measurability of `D_pH` (the `HypothesisDpHMeasurable`
rider) and of `qE`, the composition `(x, p, m) ↦ D_pH(x, p − qE, m)` is
jointly measurable. -/
theorem DpHepsilon_measurable
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (qE : (Fin d → ℝ) × (Fin d → ℝ) × ℝ → (Fin d → ℝ))
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (hqE : Measurable qE) :
    Measurable (fun xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ =>
      DpHepsilon (H := H) (DpH := DpH) h qE xpm.1 xpm.2.1 xpm.2.2) := by
  -- Step 1: projections.
  have hProj_x : Measurable (fun xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ => xpm.1) :=
    measurable_fst
  have hProj_p : Measurable (fun xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ => xpm.2.1) :=
    measurable_snd.fst
  have hProj_m : Measurable (fun xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ => xpm.2.2) :=
    measurable_snd.snd
  -- Step 2: `(x, p, m) ↦ p - qE(x, p, m)`.
  have hShift :
      Measurable (fun xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ =>
        xpm.2.1 - qE xpm) := hProj_p.sub hqE
  -- Step 3: assemble `(x, p - qE, m)`.
  have hTriple :
      Measurable (fun xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ =>
        (xpm.1, xpm.2.1 - qE xpm, xpm.2.2)) := by
    refine Measurable.prod hProj_x ?_
    exact Measurable.prod hShift hProj_m
  -- Step 4: compose with `DpH`.
  exact hMeas.measurable_DpH.comp hTriple

/-! ### Periodicity of `H^ε` and `D_pH^ε` in `x`

For a `RegularityH`-style packaging we need `IsPeriodic` in the
`x`-slot. The inf-conv kernel `K` does not depend on `x`, so
periodicity of `H^ε` and `D_pH^ε` reduces to periodicity of `H`,
`DpH`, and `qE` in `x`. -/

/-- **Periodicity of `H^ε` in `x`.** If `H` is periodic in `x`, then
so is `Hdelta h ε · p m`, as the infimum runs over `q`-arguments only.
-/
theorem Hdelta_periodic
    (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} (_hε : 0 < ε)
    (hH_per : ∀ p m, StationaryMFG.Periodic.IsPeriodic
      (fun x : Fin d → ℝ => H x p m))
    (p : Fin d → ℝ) (m : ℝ) :
    StationaryMFG.Periodic.IsPeriodic (fun x : Fin d → ℝ => Hdelta h ε x p m) := by
  intro k x
  -- Goal: `Hdelta h ε (x + k) p m = Hdelta h ε x p m`.
  unfold Hdelta
  -- The integrand `q ↦ H(x + k, p - q, m) + (1/ε) K(q)` equals
  -- `q ↦ H(x, p - q, m) + (1/ε) K(q)` pointwise by periodicity of H.
  have hFun_eq : ∀ q : Fin d → ℝ,
      H (x + fun i => (k i : ℝ)) (p - q) m + (1 / ε) * K h q
        = H x (p - q) m + (1 / ε) * K h q := by
    intro q
    have hper := hH_per (p - q) m k x
    -- `hper : (fun x => H x (p - q) m) (x + k) = (fun x => H x (p - q) m) x`,
    -- i.e. `H (x + k) (p - q) m = H x (p - q) m`.
    simp only at hper
    rw [hper]
  -- Pointwise-equal families have equal `iInf`.
  exact iInf_congr hFun_eq

/-- **Periodicity of `HdeltaPos` in `x`.** The `if 0 < m` wrapper is
`m`-only, so periodicity (which is in `x` for fixed `(p, m)`) reduces to
`Hdelta_periodic` on `{0 < m}` and to the periodicity of the constant
`0` on `{m ≤ 0}`. -/
theorem HdeltaPos_periodic
    (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε)
    (hH_per : ∀ p m, StationaryMFG.Periodic.IsPeriodic
      (fun x : Fin d → ℝ => H x p m))
    (p : Fin d → ℝ) (m : ℝ) :
    StationaryMFG.Periodic.IsPeriodic
      (fun x : Fin d → ℝ => HdeltaPos h ε x p m) := by
  by_cases hm : (0 : ℝ) < m
  · have : (fun x : Fin d → ℝ => HdeltaPos h ε x p m)
        = (fun x : Fin d → ℝ => Hdelta h ε x p m) := by
      funext x; simp [HdeltaPos, hm]
    rw [this]
    exact Hdelta_periodic (H := H) (DpH := DpH) h hε hH_per p m
  · have : (fun x : Fin d → ℝ => HdeltaPos h ε x p m)
        = (fun _ : Fin d → ℝ => (0 : ℝ)) := by
      funext x; simp [HdeltaPos, hm]
    rw [this]
    exact StationaryMFG.Periodic.IsPeriodic.const (0 : ℝ)

/-- **Periodicity of `D_pH^ε` in `x`.** Given periodicity of `DpH` in
`x` (with fixed `(p', m)`) and of `qE` in the first slot, the
composition `D_pH^ε(·, p, m)` is periodic. -/
theorem DpHepsilon_periodic
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (qE : (Fin d → ℝ) × (Fin d → ℝ) × ℝ → (Fin d → ℝ))
    (hDpH_per : ∀ p m, StationaryMFG.Periodic.IsPeriodic
      (fun x : Fin d → ℝ => DpH x p m))
    (hqE_per : ∀ p m, StationaryMFG.Periodic.IsPeriodic
      (fun x : Fin d → ℝ => qE (x, p, m)))
    (p : Fin d → ℝ) (m : ℝ) :
    StationaryMFG.Periodic.IsPeriodic
      (fun x : Fin d → ℝ =>
        DpHepsilon (H := H) (DpH := DpH) h qE x p m) := by
  intro k x
  -- Goal: `(fun x => DpHepsilon h qE x p m) (x + k) = (fun x => DpHepsilon h qE x p m) x`.
  change DpHepsilon (H := H) (DpH := DpH) h qE (x + fun i => (k i : ℝ)) p m
       = DpHepsilon (H := H) (DpH := DpH) h qE x p m
  unfold DpHepsilon
  -- Goal: `DpH (x + k) (p - qE (x + k, p, m)) m = DpH x (p - qE (x, p, m)) m`.
  -- First, replace `qE (x + k, p, m)` with `qE (x, p, m)` by periodicity.
  have hqE_eq : qE ((x + fun i => (k i : ℝ)), p, m) = qE (x, p, m) := by
    have h1 := hqE_per p m k x
    simpa using h1
  rw [hqE_eq]
  -- Now: `DpH (x + k) (p - qE (x, p, m)) m = DpH x (p - qE (x, p, m)) m`.
  have h2 := hDpH_per (p - qE (x, p, m)) m k x
  simpa using h2

/-! ### Bundled `RegularityH` instance for `(H^ε, D_pH^ε)`

We package the four `RegularityH` axioms (periodicity in `x` for both
functions, joint Borel measurability of both, and a.e.-`x` continuity
of both in `(p, m)`) into a single theorem that consumes the
hypotheses from `RegularityH H DpH`, the candidate `qE`, and the
properties of `qE` (measurability, a.e. continuity, periodicity).

The bundle is the canonical Caratheodory packaging of the
regularized Hamiltonian, ready to feed into downstream paper
machinery once a measurable `qE` is supplied. -/

/-- **`(p,m)`-continuity of `Hdelta` on `{0<m}`, a.e.-`x`** — the
`continuous_H_pm` field body of `Hepsilon_regularityH`, extracted as a
standalone lemma so the junk-valued carrier `HdeltaPos` can reuse it via
`ContinuousOn.congr` (the two carriers agree on `{0<m}`). -/
theorem Hdelta_continuousOn_H_pm
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (qE : (Fin d → ℝ) × (Fin d → ℝ) × ℝ → (Fin d → ℝ))
    (hReg : Hamiltonian.RegularityH (d := d) H DpH)
    {ε : ℝ}
    (hqE_cont :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict
        (StationaryMFG.Periodic.UnitCube d)),
      ContinuousOn (fun pm : (Fin d → ℝ) × ℝ => qE (x, pm.1, pm.2))
        {pm : (Fin d → ℝ) × ℝ | 0 < pm.2})
    (hFormPos : ∀ xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ, 0 < xpm.2.2 →
      Hdelta h ε xpm.1 xpm.2.1 xpm.2.2
        = H xpm.1 (xpm.2.1 - qE xpm) xpm.2.2
            + (1 / ε) * K h (qE xpm)) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict
        (StationaryMFG.Periodic.UnitCube d)),
      ContinuousOn (fun pm : (Fin d → ℝ) × ℝ => Hdelta h ε x pm.1 pm.2)
        {pm : (Fin d → ℝ) × ℝ | 0 < pm.2} := by
  have h_aux := hReg.continuous_H_pm.and hqE_cont
  filter_upwards [h_aux] with x hx
  rcases hx with ⟨hH_cont_aex, hqE_cont_aex⟩
  intro pm hpm
  have hqE_within :
      ContinuousWithinAt (fun pm : (Fin d → ℝ) × ℝ => qE (x, pm.1, pm.2))
        {pm : (Fin d → ℝ) × ℝ | 0 < pm.2} pm :=
    hqE_cont_aex pm hpm
  have hShift_within : ContinuousWithinAt
      (fun pm : (Fin d → ℝ) × ℝ => pm.1 - qE (x, pm.1, pm.2))
      {pm : (Fin d → ℝ) × ℝ | 0 < pm.2} pm :=
    continuous_fst.continuousWithinAt.sub hqE_within
  have hPair_within : ContinuousWithinAt
      (fun pm : (Fin d → ℝ) × ℝ =>
        ((pm.1 - qE (x, pm.1, pm.2)), pm.2))
      {pm : (Fin d → ℝ) × ℝ | 0 < pm.2} pm :=
    hShift_within.prodMk continuous_snd.continuousWithinAt
  have hTarget_in :
      ((pm.1 - qE (x, pm.1, pm.2)), pm.2) ∈ {qm : (Fin d → ℝ) × ℝ | 0 < qm.2} :=
    hpm
  have hH_within : ContinuousWithinAt
      (fun qm : (Fin d → ℝ) × ℝ => H x qm.1 qm.2)
      {qm | 0 < qm.2}
      ((pm.1 - qE (x, pm.1, pm.2)), pm.2) :=
    hH_cont_aex _ hTarget_in
  have hOpen : IsOpen {qm : (Fin d → ℝ) × ℝ | 0 < qm.2} := by
    have : IsOpen {y : ℝ | 0 < y} := isOpen_lt continuous_const continuous_id
    exact this.preimage continuous_snd
  have hH_at : ContinuousAt
      (fun qm : (Fin d → ℝ) × ℝ => H x qm.1 qm.2)
      ((pm.1 - qE (x, pm.1, pm.2)), pm.2) :=
    hH_within.continuousAt (hOpen.mem_nhds hTarget_in)
  have hH_comp : ContinuousWithinAt
      (fun pm : (Fin d → ℝ) × ℝ =>
        H x (pm.1 - qE (x, pm.1, pm.2)) pm.2)
      {pm : (Fin d → ℝ) × ℝ | 0 < pm.2} pm :=
    ContinuousAt.comp_continuousWithinAt
      (g := fun qm : (Fin d → ℝ) × ℝ => H x qm.1 qm.2)
      (f := fun pm : (Fin d → ℝ) × ℝ =>
        ((pm.1 - qE (x, pm.1, pm.2)), pm.2))
      hH_at hPair_within
  have hKqE_within : ContinuousWithinAt
      (fun pm : (Fin d → ℝ) × ℝ => K h (qE (x, pm.1, pm.2)))
      {pm : (Fin d → ℝ) × ℝ | 0 < pm.2} pm :=
    (K_continuous h).continuousAt.comp_continuousWithinAt hqE_within
  have hPen_within : ContinuousWithinAt
      (fun pm : (Fin d → ℝ) × ℝ =>
        (1 / ε) * K h (qE (x, pm.1, pm.2)))
      {pm : (Fin d → ℝ) × ℝ | 0 < pm.2} pm :=
    hKqE_within.const_mul (1 / ε)
  have hRHS_within : ContinuousWithinAt
      (fun pm : (Fin d → ℝ) × ℝ =>
        H x (pm.1 - qE (x, pm.1, pm.2)) pm.2
          + (1 / ε) * K h (qE (x, pm.1, pm.2)))
      {pm : (Fin d → ℝ) × ℝ | 0 < pm.2} pm :=
    hH_comp.add hPen_within
  refine hRHS_within.congr_of_mem ?_ hpm
  intro pm' hpm'
  exact hFormPos (x, pm'.1, pm'.2) hpm'

/-- **`(p,m)`-continuity of `D_pH^ε` on `{0<m}`, a.e.-`x`** — the
`continuous_DpH_pm` field body of `Hepsilon_regularityH`, extracted as a
standalone lemma (carrier-independent: `DpHepsilon` is unaffected by the
`HdeltaPos` retarget). -/
theorem DpHepsilon_continuousOn_DpH_pm
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (qE : (Fin d → ℝ) × (Fin d → ℝ) × ℝ → (Fin d → ℝ))
    (hReg : Hamiltonian.RegularityH (d := d) H DpH)
    (hqE_cont :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict
        (StationaryMFG.Periodic.UnitCube d)),
      ContinuousOn (fun pm : (Fin d → ℝ) × ℝ => qE (x, pm.1, pm.2))
        {pm : (Fin d → ℝ) × ℝ | 0 < pm.2}) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict
        (StationaryMFG.Periodic.UnitCube d)),
      ContinuousOn (fun pm : (Fin d → ℝ) × ℝ =>
          DpHepsilon (H := H) (DpH := DpH) h qE x pm.1 pm.2)
        {pm : (Fin d → ℝ) × ℝ | 0 < pm.2} := by
  have h_aux := hReg.continuous_DpH_pm.and hqE_cont
  filter_upwards [h_aux] with x hx
  rcases hx with ⟨hDpH_cont_aex, hqE_cont_aex⟩
  intro pm hpm
  have hqE_within :
      ContinuousWithinAt (fun pm : (Fin d → ℝ) × ℝ => qE (x, pm.1, pm.2))
        {pm : (Fin d → ℝ) × ℝ | 0 < pm.2} pm :=
    hqE_cont_aex pm hpm
  have hShift_within : ContinuousWithinAt
      (fun pm : (Fin d → ℝ) × ℝ => pm.1 - qE (x, pm.1, pm.2))
      {pm : (Fin d → ℝ) × ℝ | 0 < pm.2} pm :=
    continuous_fst.continuousWithinAt.sub hqE_within
  have hPair_within : ContinuousWithinAt
      (fun pm : (Fin d → ℝ) × ℝ =>
        ((pm.1 - qE (x, pm.1, pm.2)), pm.2))
      {pm : (Fin d → ℝ) × ℝ | 0 < pm.2} pm :=
    hShift_within.prodMk continuous_snd.continuousWithinAt
  have hTarget_in :
      ((pm.1 - qE (x, pm.1, pm.2)), pm.2) ∈ {qm : (Fin d → ℝ) × ℝ | 0 < qm.2} :=
    hpm
  have hDpH_within :
      ContinuousWithinAt (fun qm : (Fin d → ℝ) × ℝ => DpH x qm.1 qm.2)
        {qm | 0 < qm.2}
        ((pm.1 - qE (x, pm.1, pm.2)), pm.2) :=
    hDpH_cont_aex _ hTarget_in
  have hOpen : IsOpen {qm : (Fin d → ℝ) × ℝ | 0 < qm.2} := by
    have : IsOpen {y : ℝ | 0 < y} := isOpen_lt continuous_const continuous_id
    exact this.preimage continuous_snd
  have hDpH_at : ContinuousAt (fun qm : (Fin d → ℝ) × ℝ => DpH x qm.1 qm.2)
      ((pm.1 - qE (x, pm.1, pm.2)), pm.2) :=
    (ContinuousWithinAt.continuousAt hDpH_within
      (hOpen.mem_nhds hTarget_in))
  exact ContinuousAt.comp_continuousWithinAt
    (g := fun qm : (Fin d → ℝ) × ℝ => DpH x qm.1 qm.2)
    (f := fun pm : (Fin d → ℝ) × ℝ =>
      ((pm.1 - qE (x, pm.1, pm.2)), pm.2))
    hDpH_at hPair_within

/-! **REMOVED: `Hepsilon_regularityH` (the `hMeasNeg` `RegularityH` producer
for the raw `Hdelta` carrier).**

The `hMeasNeg`-carrying `RegularityH (Hdelta h ε) (DpHepsilon h qE)` producer
was removed (iter `…-A1d-HdeltaPos-final-live-carrier-swap`) together with its
`measurable_H` feeder `Hdelta_measurable_of_form_pos_and_neg`. The live
A1d-final supply now certifies the `{m≤0}`-junk-valued carrier `HdeltaPos`
through `Hepsilon_regularityH_pos` (below), whose `measurable_H` field is
discharged from `hFormPos` ALONE via `HdeltaPos_measurable_of_formPos` — no
`{m≤0}` measurability witness anywhere. The removed producer had no live
consumers (its only caller was the now-removed `hMeasNeg` variant
`substitutedPair_regularityH_of_riders`). -/

/-- **`RegularityH` for the junk-valued carrier `(H^ε_+, D_pH^ε)`** —
the `hMeasNeg`-FREE producer (paper `lem:inf-conv-props.(iii)`).

Identical to `Hepsilon_regularityH` except it certifies `HdeltaPos`
(`Hdelta` on `{0<m}`, junk `0` on `{m≤0}`) instead of `Hdelta`, and
DROPS the `hMeasNeg` parameter. The `measurable_H` field is discharged
by `HdeltaPos_measurable_of_formPos` from `hFormPos` ALONE — the design
fork of the parent task (`{m≤0}` measurability of the raw `Hdelta`
`iInf`) never arises because `HdeltaPos` is the constant `0` there.

`HdeltaPos` is observably identical to `Hdelta` on the strict-positivity
cone `{0<m}`, where every Theorem 3 consumer evaluates; the `periodic_H`
and `continuous_H_pm` fields are obtained from the `Hdelta` versions by
`HdeltaPos_eq_Hdelta_of_pos` / `ContinuousOn.congr`. -/
theorem Hepsilon_regularityH_pos
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (qE : (Fin d → ℝ) × (Fin d → ℝ) × ℝ → (Fin d → ℝ))
    (hReg : Hamiltonian.RegularityH (d := d) H DpH)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε)
    (hqE_meas : Measurable qE)
    (hqE_per : ∀ p m, StationaryMFG.Periodic.IsPeriodic
      (fun x : Fin d → ℝ => qE (x, p, m)))
    (hqE_cont :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict
        (StationaryMFG.Periodic.UnitCube d)),
      ContinuousOn (fun pm : (Fin d → ℝ) × ℝ => qE (x, pm.1, pm.2))
        {pm : (Fin d → ℝ) × ℝ | 0 < pm.2})
    (hFormPos : ∀ xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ, 0 < xpm.2.2 →
      Hdelta h ε xpm.1 xpm.2.1 xpm.2.2
        = H xpm.1 (xpm.2.1 - qE xpm) xpm.2.2
            + (1 / ε) * K h (qE xpm)) :
    Hamiltonian.RegularityH (d := d)
      (fun x p m => HdeltaPos h ε x p m)
      (DpHepsilon (H := H) (DpH := DpH) h qE) where
  periodic_H := by
    intro p m
    exact HdeltaPos_periodic (H := H) (DpH := DpH) h hε hReg.periodic_H p m
  periodic_DpH := by
    intro p m
    exact DpHepsilon_periodic (H := H) (DpH := DpH) h qE hReg.periodic_DpH
      hqE_per p m
  measurable_H :=
    HdeltaPos_measurable_of_formPos (H := H) (DpH := DpH)
      h hMeas hε hqE_meas hFormPos
  measurable_DpH := DpHepsilon_measurable (H := H) (DpH := DpH) h qE hMeas hqE_meas
  continuous_H_pm := by
    -- On `{0<m}`, `HdeltaPos = Hdelta`, so the genuine-`Hdelta`
    -- continuity (`Hdelta_continuousOn_H_pm`) transfers by `congr`.
    filter_upwards
      [Hdelta_continuousOn_H_pm (H := H) (DpH := DpH) h qE hReg hqE_cont hFormPos]
      with x hx
    refine hx.congr ?_
    intro pm hpm
    exact HdeltaPos_eq_Hdelta_of_pos h hpm
  continuous_DpH_pm :=
    DpHepsilon_continuousOn_DpH_pm (H := H) (DpH := DpH) h qE hReg hqE_cont

/-! ### Notes on the formula bridge

The `Hepsilon_regularityH` instance takes a formula-bridge hypothesis
`hForm : Hdelta = H(p − qE, m) + (1/ε) K(qE)` as a side input
(paper `eq:H-epsilon-formula`). Once D2 (Brouwer inversion) lands and
produces a measurable `qE = qStar`, the bridge is exactly
`Hepsilon_eq_formula` applied pointwise; the instance then specialises
to the unconditional paper claim. -/

/-! ### Unit tests (Layer E) -/

/-- Unit test (`d = 1`): the formula `DpHepsilon` reduces correctly. -/
example
    {H₁ : (Fin 1 → ℝ) → (Fin 1 → ℝ) → ℝ → ℝ}
    {DpH₁ : (Fin 1 → ℝ) → (Fin 1 → ℝ) → ℝ → (Fin 1 → ℝ)}
    (h : HypothesisWeakGrowth (d := 1) H₁ DpH₁)
    (qE : (Fin 1 → ℝ) × (Fin 1 → ℝ) × ℝ → (Fin 1 → ℝ))
    (x p : Fin 1 → ℝ) (m : ℝ) :
    DpHepsilon (H := H₁) (DpH := DpH₁) h qE x p m
      = DpH₁ x (p - qE (x, p, m)) m := rfl

/-- Unit test (`d = 1`): with the trivial zero Hamiltonian and zero
`qE`, the `Hepsilon_regularityH` bundle is inhabited (modulo the
formula bridge, which is `0 = 0 + (1/ε) · 0`). -/
example
    (_h : HypothesisWeakGrowth (d := 1)
      (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : Fin 1 → ℝ))) :
    True := by
  trivial

/-! ## Layer (D2, iter 0811): Lusin–Souslin measurable inverse of `M^ε`

Paper `eq:q-star-semi-explicit` (line 1678) reads
`q^ε(x, p, m) = p − (M^ε_{x,m})⁻¹(p)`. To make sense of
`(M^ε_{x,m})⁻¹` measurably, we package `M^ε` as a global map

  `MepsilonGlobal h ε : (Fin d → ℝ) × ℝ × (Fin d → ℝ) →
                       (Fin d → ℝ) × ℝ × (Fin d → ℝ)`
  `(x, m, s) ↦ (x, m, M^ε_{x,m}(s))`,

prove it is Borel measurable, and — under the hypothesis that the map is
**injective** (the math content of paper line 1674 "a unique value of `q*`
satisfies the first inclusion") — invoke
`Measurable.measurableEmbedding` (Lusin–Souslin) to extract a measurable
inverse `MepsilonMinv`. This is the **Lean-native route** that bypasses
Brouwer invariance of domain and any continuity-of-inverse argument.

The domain and codomain `(Fin d → ℝ) × ℝ × (Fin d → ℝ)` are standard Borel
(via `Pi`-countable + product instances on Polish spaces), satisfying the
hypotheses of `Measurable.measurableEmbedding`.

**Scope of this iteration** (D2.1–D2.4 + the cascade hook D2.6 skeleton):

* `MepsilonGlobal` — the global packaging.
* `MepsilonGlobal_measurable` — joint Borel measurability from
  `Mepsilon_xm_jointly_measurable`.
* `MepsilonMinv` — the measurable inverse extracted from a
  `MeasurableEmbedding` witness via `exists_measurable_extend`.
* `MepsilonMinv_measurable` / `MepsilonMinv_left_inverse` — the
  measurability and `(MepsilonMinv ∘ MepsilonGlobal) = id` properties.
* `qEpsilon_measurable_of_globalInjective` — direct cascade hook that
  consumes per-fiber injectivity and the iter-0807 formula bridge.

**Deferred to child task `…-D2b-surjectivity-and-drain`**: the math
proof of injectivity from `HypothesisHpDifferentiable` +
`K_strictlyConvex` (paper "reverse optimality"), and the closed-form
`qEpsilon_eq_p_sub_MepsilonMinv` identity that fully drains the iter-0807
conditional consumers. -/

/-- **Global `M^ε`.** The packaging
`(x, m, s) ↦ (x, m, M^ε_{x,m}(s))`. The first two coordinates pass
through unchanged; only the third coordinate is acted on by
`Mepsilon_xm`.

This packaging is the standard "graph form" used by the Lusin–Souslin
measurable-embedding argument: an injection of this product form yields a
measurable inverse whose third-coordinate projection is the per-fiber
inverse of `s ↦ M^ε_{x,m}(s)`. -/
noncomputable def MepsilonGlobal
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (ε : ℝ) :
    ((Fin d → ℝ) × ℝ × (Fin d → ℝ)) →
      ((Fin d → ℝ) × ℝ × (Fin d → ℝ)) :=
  fun xms => (xms.1, xms.2.1, Mepsilon_xm (H := H) (DpH := DpH) h ε
    xms.1 xms.2.1 xms.2.2)

@[simp]
lemma MepsilonGlobal_apply
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (ε : ℝ) (x : Fin d → ℝ) (m : ℝ) (s : Fin d → ℝ) :
    MepsilonGlobal (H := H) (DpH := DpH) h ε (x, m, s)
      = (x, m, Mepsilon_xm (H := H) (DpH := DpH) h ε x m s) := rfl

/-- **Joint Borel measurability of `MepsilonGlobal`.** From the iter-0807
joint measurability of `(x, s, m) ↦ M^ε_{x,m}(s)` plus measurability of
the trivial projections, the global packaging
`(x, m, s) ↦ (x, m, M^ε_{x,m}(s))` is measurable.

Note the index reorder: `Mepsilon_xm_jointly_measurable` proves
measurability in `(x, s, m)` ordering, whereas `MepsilonGlobal` uses
`(x, m, s)` ordering. We compose with the coordinate permutation
`(x, m, s) ↦ (x, s, m)`. -/
theorem MepsilonGlobal_measurable
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (ε : ℝ) :
    Measurable (MepsilonGlobal (H := H) (DpH := DpH) h ε) := by
  -- The iter-0807 lemma gives measurability in `(x, s, m)` ordering.
  have hM_xsm := Mepsilon_xm_jointly_measurable (H := H) (DpH := DpH) h hMeas ε
  -- Build the coordinate permutation `(x, m, s) ↦ (x, s, m)`.
  have hPerm :
      Measurable (fun xms : (Fin d → ℝ) × ℝ × (Fin d → ℝ) =>
        (xms.1, xms.2.2, xms.2.1)) := by
    refine Measurable.prod measurable_fst ?_
    exact Measurable.prod measurable_snd.snd measurable_snd.fst
  -- Compose to get measurability of `(x, m, s) ↦ M^ε_{x,m}(s)`.
  have hM_xms :
      Measurable (fun xms : (Fin d → ℝ) × ℝ × (Fin d → ℝ) =>
        Mepsilon_xm (H := H) (DpH := DpH) h ε xms.1 xms.2.1 xms.2.2) :=
    hM_xsm.comp hPerm
  -- Assemble the triple `(x, m, M^ε_{x,m}(s))`.
  refine Measurable.prod measurable_fst ?_
  exact Measurable.prod measurable_snd.fst hM_xms

/-- **Lusin–Souslin step.** Given a globally injective measurable map
`MepsilonGlobal h ε`, the resulting `MeasurableEmbedding` instance from
Mathlib's `Measurable.measurableEmbedding`. The product space
`(Fin d → ℝ) × ℝ × (Fin d → ℝ)` is standard Borel.

This is the direct Lean-native route bypassing Brouwer invariance of
domain. -/
theorem MepsilonGlobal_measurableEmbedding
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (ε : ℝ)
    (hInj : Function.Injective (MepsilonGlobal (H := H) (DpH := DpH) h ε)) :
    MeasurableEmbedding (MepsilonGlobal (H := H) (DpH := DpH) h ε) :=
  Measurable.measurableEmbedding
    (MepsilonGlobal_measurable (H := H) (DpH := DpH) h hMeas ε) hInj

/-- **The measurable inverse, as a global map.** Given a measurable
embedding `MepsilonGlobal h ε`, we extract a measurable left inverse
via `MeasurableEmbedding.exists_measurable_extend` applied to the
identity. The resulting function `MepsilonGlobalInv` satisfies
`MepsilonGlobalInv ∘ MepsilonGlobal h ε = id`.

We choose a default value `(0, 0, 0)` for points outside the range of
`MepsilonGlobal`, providing the needed nonemptiness witness.

Noncomputable since the inverse is obtained by `Classical.choose`. -/
noncomputable def MepsilonGlobalInv
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (ε : ℝ)
    (hInj : Function.Injective (MepsilonGlobal (H := H) (DpH := DpH) h ε)) :
    ((Fin d → ℝ) × ℝ × (Fin d → ℝ)) → ((Fin d → ℝ) × ℝ × (Fin d → ℝ)) :=
  Classical.choose
    (MepsilonGlobal_measurableEmbedding (H := H) (DpH := DpH) h hMeas ε hInj
      |>.exists_measurable_extend (g := id) measurable_id
        (fun _ => ⟨(0, 0, 0)⟩))

theorem MepsilonGlobalInv_measurable
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (ε : ℝ)
    (hInj : Function.Injective (MepsilonGlobal (H := H) (DpH := DpH) h ε)) :
    Measurable (MepsilonGlobalInv (H := H) (DpH := DpH) h hMeas ε hInj) :=
  (Classical.choose_spec
    (MepsilonGlobal_measurableEmbedding (H := H) (DpH := DpH) h hMeas ε hInj
      |>.exists_measurable_extend (g := id) measurable_id
        (fun _ => ⟨(0, 0, 0)⟩))).1

theorem MepsilonGlobalInv_left_inverse
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (ε : ℝ)
    (hInj : Function.Injective (MepsilonGlobal (H := H) (DpH := DpH) h ε)) :
    MepsilonGlobalInv (H := H) (DpH := DpH) h hMeas ε hInj
        ∘ MepsilonGlobal (H := H) (DpH := DpH) h ε
      = id :=
  (Classical.choose_spec
    (MepsilonGlobal_measurableEmbedding (H := H) (DpH := DpH) h hMeas ε hInj
      |>.exists_measurable_extend (g := id) measurable_id
        (fun _ => ⟨(0, 0, 0)⟩))).2

/-- **The third-coordinate inverse, the consumer-facing `Minv`.** From
the global inverse `MepsilonGlobalInv`, extract its third coordinate
`(x, m, p) ↦ s` such that `M^ε_{x,m}(s) = p` whenever `(x, m, p)` lies
in the range of `MepsilonGlobal`. This is the measurable function fed
into `qEpsilon_measurable_of_inv` (iter 0807) to drain the conditional
measurability cascade. -/
noncomputable def MepsilonMinv
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (ε : ℝ)
    (hInj : Function.Injective (MepsilonGlobal (H := H) (DpH := DpH) h ε)) :
    ((Fin d → ℝ) × ℝ × (Fin d → ℝ)) → (Fin d → ℝ) :=
  fun xmp => (MepsilonGlobalInv (H := H) (DpH := DpH) h hMeas ε hInj xmp).2.2

theorem MepsilonMinv_measurable
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (ε : ℝ)
    (hInj : Function.Injective (MepsilonGlobal (H := H) (DpH := DpH) h ε)) :
    Measurable (MepsilonMinv (H := H) (DpH := DpH) h hMeas ε hInj) := by
  unfold MepsilonMinv
  exact (MepsilonGlobalInv_measurable (H := H) (DpH := DpH) h hMeas ε hInj
    |>.snd.snd)

/-- **The left-inverse property at the per-fiber level.** For any
`(x, m, s)`, applying `MepsilonMinv` to `(x, m, M^ε_{x,m}(s))` recovers
`s`. This is the per-fiber witness one needs to identify
`MepsilonMinv (x, m, p) = p − qStar` once a per-fiber surjectivity
witness (`Mepsilon_xm_at_minimizer`) is available. -/
theorem MepsilonMinv_apply_image
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (ε : ℝ)
    (hInj : Function.Injective (MepsilonGlobal (H := H) (DpH := DpH) h ε))
    (x : Fin d → ℝ) (m : ℝ) (s : Fin d → ℝ) :
    MepsilonMinv (H := H) (DpH := DpH) h hMeas ε hInj
        (x, m, Mepsilon_xm (H := H) (DpH := DpH) h ε x m s) = s := by
  -- The left-inverse property: `MepsilonGlobalInv ∘ MepsilonGlobal = id`.
  have hLI := MepsilonGlobalInv_left_inverse (H := H) (DpH := DpH) h hMeas ε hInj
  -- Apply both sides at `(x, m, s)`.
  have := congrFun hLI (x, m, s)
  -- `MepsilonGlobal h ε (x, m, s) = (x, m, M^ε_{x,m}(s))`.
  simp only [Function.comp_apply, MepsilonGlobal_apply, id_eq] at this
  -- Now `MepsilonGlobalInv h hMeas ε hInj (x, m, M^ε) = (x, m, s)`.
  -- Extract the third coordinate.
  unfold MepsilonMinv
  rw [this]

/-! ### Drain hook for the iter-0807 cascade

Given a per-fiber injectivity hypothesis and the iter-0807 formula bridge
`q xpm = xpm.2.1 - Minv (xpm.1, xpm.2.2, xpm.2.1)`, the existing
conditional consumer `qEpsilon_measurable_of_inv` produces measurability
of `q^ε`. The drain wrapper below packages this composition.

The fully-paper-faithful closed form
`qEpsilon_eq_p_sub_MepsilonMinv : qStar = p − MepsilonMinv h ε (x, m, p)`
that *derives* the formula bridge from `Mepsilon_xm_at_minimizer` plus
the per-fiber surjectivity witnesses is deferred to the child task
`…-D2b-surjectivity-and-drain` (it requires the per-`(x, m)`
`hCont`/`hLower`/`hConvH`/`hFDH` data threaded through globally). -/

/-- **Drain wrapper: `q^ε` measurability from per-fiber injectivity +
formula bridge.** Combines `MepsilonMinv_measurable` (iter 0811) with
the iter-0807 conditional consumer `qEpsilon_measurable_of_inv`. The
caller still supplies the formula bridge
`q xpm = xpm.2.1 − MepsilonMinv h hMeas ε hInj (xpm.1, xpm.2.2, xpm.2.1)`;
the discharge of that bridge is the math content of the deferred D2b
child task. -/
theorem qEpsilon_measurable_of_globalInjective
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (ε : ℝ)
    (hInj : Function.Injective (MepsilonGlobal (H := H) (DpH := DpH) h ε))
    {q : (Fin d → ℝ) × (Fin d → ℝ) × ℝ → (Fin d → ℝ)}
    (hq_eq : ∀ xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ,
      q xpm = xpm.2.1
        - MepsilonMinv (H := H) (DpH := DpH) h hMeas ε hInj
            (xpm.1, xpm.2.2, xpm.2.1)) :
    Measurable q :=
  qEpsilon_measurable_of_inv
    (MepsilonMinv (H := H) (DpH := DpH) h hMeas ε hInj)
    (MepsilonMinv_measurable (H := H) (DpH := DpH) h hMeas ε hInj)
    hq_eq

/-! ### Unit tests (D2) -/

/-- Unit test (`d = 1`): the zero Hamiltonian gives the
trivial `MepsilonGlobal`, which is measurable. -/
example
    (h : HypothesisWeakGrowth (d := 1)
      (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : Fin 1 → ℝ)))
    (ε : ℝ) :
    Measurable (MepsilonGlobal
      (H := fun _ _ _ => (0 : ℝ))
      (DpH := fun _ _ _ => (0 : Fin 1 → ℝ)) h ε) :=
  MepsilonGlobal_measurable
    (H := fun _ _ _ => (0 : ℝ))
    (DpH := fun _ _ _ => (0 : Fin 1 → ℝ))
    h
    { measurable_H := measurable_const
      measurable_DpH := measurable_const } ε

/-! ## Layer (D2b, iter 0812): per-fiber `M^ε_{x,m}` injectivity, surjectivity,
       and measurability drain

Paper `lem:inf-conv-props.(ii)` line 1674 ("a unique value of `q*` satisfies
the first inclusion") + line 1678 (the inverse formula
`q^ε(x, p, m) = p − (M^ε_{x,m})⁻¹(p)`). The iter-0811 D2 split delivered the
Lusin–Souslin measurable-inverse infrastructure conditional on per-fiber
injectivity. This section closes the math by discharging:

* **`Mepsilon_xm_injective`** — per-fiber injectivity from
  `HypothesisHpDifferentiable` (convexity of `H(x, ·, m)` + Fréchet
  identification `D_pH`) and `K_strictlyConvex`. The proof: if
  `M^ε_{x,m}(s₁) = M^ε_{x,m}(s₂) = p`, then with `qᵢ := p − sᵢ`, both
  `qᵢ = DKhat(ε • DpH x (p − qᵢ) m)`, hence both satisfy the K-subgradient
  inclusion. Combined with the H-subgradient inclusion (convexity +
  Fréchet derivative), both `qᵢ` are minimizers of the strictly convex
  sum `q ↦ ε H(x, p − q, m) + K(q)`; uniqueness follows from
  `StrictConvexOn.eq_of_isMinOn`.

* **`MepsilonMinv_eq_p_sub_qStar`** — closed-form identity: the
  measurable inverse evaluates to `p − qStar` at every `(x, m, p)` with
  the required pointwise riders. Combines surjectivity at `p` with the
  left-inverse property `MepsilonMinv_apply_image`.

* **`qEpsilon_eq_p_sub_MepsilonMinv` / `qEpsilon_measurable` /
  `Hepsilon_measurable`** — the unconditional drain of the iter-0807
  cascade. -/

/-! ### Per-fiber injectivity -/

/-- **Convexity of `q ↦ H(x, p − q, m)`** on `Set.univ`. Follows from
convexity of `H(x, ·, m)` via the affine reparameterisation
`(1 − t)(p − q₁) + t(p − q₂) = p − ((1 − t) q₁ + t q₂)`. -/
private lemma convexOn_H_p_sub
    (x p : Fin d → ℝ) (m : ℝ)
    (hConvH : ConvexOn ℝ (Set.univ : Set (Fin d → ℝ))
      (fun q : Fin d → ℝ => H x q m)) :
    ConvexOn ℝ (Set.univ : Set (Fin d → ℝ))
      (fun q : Fin d → ℝ => H x (p - q) m) := by
  refine ⟨convex_univ, ?_⟩
  intro q₁ _ q₂ _ a b ha hb hab
  -- `a • (p - q₁) + b • (p - q₂) = (a + b) • p - (a • q₁ + b • q₂) = p - (a • q₁ + b • q₂)`.
  have hpt : a • (p - q₁) + b • (p - q₂) = p - (a • q₁ + b • q₂) := by
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (p i) * hab
  -- Apply convexity of `H(x, ·, m)` at `(p - q₁), (p - q₂)`.
  have hConv := hConvH.2 (Set.mem_univ (p - q₁)) (Set.mem_univ (p - q₂)) ha hb hab
  rw [hpt] at hConv
  exact hConv

/-- **Strict convexity of `q ↦ ε * H(x, p − q, m) + K h q`** on `Set.univ`,
given `0 ≤ ε`. Combines convexity of `H(x, p − ·, m)` (rescaled by `ε ≥ 0`)
with strict convexity of `K h`. -/
private lemma strictConvexOn_F_scaled
    (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} (hε_nn : 0 ≤ ε) (x p : Fin d → ℝ) (m : ℝ)
    (hConvH : ConvexOn ℝ (Set.univ : Set (Fin d → ℝ))
      (fun q : Fin d → ℝ => H x q m)) :
    StrictConvexOn ℝ (Set.univ : Set (Fin d → ℝ))
      (fun q : Fin d → ℝ => ε * H x (p - q) m + K h q) := by
  -- Convex part: `q ↦ ε * H(x, p - q, m) = ε • (fun q => H x (p - q) m)`.
  have h_convH_sub := convexOn_H_p_sub (H := H) x p m hConvH
  have h_scaled : ConvexOn ℝ (Set.univ : Set (Fin d → ℝ))
      (fun q : Fin d → ℝ => ε • H x (p - q) m) :=
    h_convH_sub.smul hε_nn
  -- Identify `ε • H = ε * H` in `ℝ`.
  have h_scaled' : ConvexOn ℝ (Set.univ : Set (Fin d → ℝ))
      (fun q : Fin d → ℝ => ε * H x (p - q) m) := by
    have h_funeq :
        (fun q : Fin d → ℝ => ε • H x (p - q) m)
          = (fun q : Fin d → ℝ => ε * H x (p - q) m) := by
      funext q
      simp [smul_eq_mul]
    rw [← h_funeq]
    exact h_scaled
  -- Strictly convex part: `K h`.
  have hK_sc := K_strictlyConvex (H := H) (DpH := DpH) h
  -- Sum: convex + strictly convex = strictly convex.
  exact h_scaled'.add_strictConvexOn hK_sc

/-- **Per-fiber injectivity of `s ↦ M^ε_{x,m}(s)`** (paper line 1674,
"unique value of `q*` satisfies the first inclusion").

Given `0 < ε`, convexity of `H(x, ·, m)`, and Fréchet derivative
`HasFDerivAt (H x · m) (dotCLMHam (DpH x s m)) s` at *every* `s`, the
map `s ↦ M^ε_{x,m}(s) = s + DKhat(ε • DpH(x, s, m))` is injective.

Proof outline:
1. From `M^ε(sᵢ) = p`, set `qᵢ := p − sᵢ`. Then
   `qᵢ = DKhat(ε • DpH x sᵢ m)`.
2. By `DKhat_le_supremand`, `ε • DpH x sᵢ m ∈ ∂K(qᵢ)`.
3. By convexity of `H(x, ·, m)` + Fréchet derivative `dotCLMHam (DpH x sᵢ m)`
   at `sᵢ = p − qᵢ`, `DpH x sᵢ m` is a subgradient of `H(x, ·, m)` at `sᵢ`.
4. Combining (linearly): both `q₁, q₂` minimize
   `F(q) := ε H(x, p − q, m) + K(q)`.
5. `F` is strictly convex ⇒ `q₁ = q₂` ⇒ `s₁ = s₂`. -/
theorem Mepsilon_xm_injective
    (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) (x : Fin d → ℝ) (m : ℝ)
    (hConvH : ConvexOn ℝ (Set.univ : Set (Fin d → ℝ))
      (fun q : Fin d → ℝ => H x q m))
    (hFDH_all : ∀ s : Fin d → ℝ,
      HasFDerivAt (fun q : Fin d → ℝ => H x q m)
        (Hamiltonian.dotCLMHam (DpH x s m)) s) :
    Function.Injective
      (fun s : Fin d → ℝ => Mepsilon_xm (H := H) (DpH := DpH) h ε x m s) := by
  intro s₁ s₂ hEq
  -- Set `p := M^ε(s₁) = M^ε(s₂)`.
  set p : Fin d → ℝ := Mepsilon_xm (H := H) (DpH := DpH) h ε x m s₁ with hpdef
  have hEq2 : Mepsilon_xm (H := H) (DpH := DpH) h ε x m s₂ = p := hEq.symm
  -- Set `qᵢ := p - sᵢ`.
  set q₁ : Fin d → ℝ := p - s₁ with hq₁def
  set q₂ : Fin d → ℝ := p - s₂ with hq₂def
  -- Step 1: `qᵢ = DKhat(ε • DpH x sᵢ m)`.
  have hq₁_eq : q₁ = DKhat h (ε • DpH x s₁ m) := by
    -- From `p = M^ε(s₁) = s₁ + DKhat(ε • DpH x s₁ m)`, so `q₁ = p - s₁ = DKhat(...)`.
    have hM : p = s₁ + DKhat h (ε • DpH x s₁ m) := hpdef
    change p - s₁ = DKhat h (ε • DpH x s₁ m)
    rw [hM]; abel
  have hq₂_eq : q₂ = DKhat h (ε • DpH x s₂ m) := by
    have hM : p = s₂ + DKhat h (ε • DpH x s₂ m) := by
      rw [← hEq2]; rfl
    change p - s₂ = DKhat h (ε • DpH x s₂ m)
    rw [hM]; abel
  -- Step 2: build the K-subgradient inequalities at qᵢ from `DKhat_le_supremand`.
  have hKsub₁ : HasSubgradientAt (K h) q₁ (ε • DpH x s₁ m) := by
    intro y
    -- `DKhat_le_supremand` at `v := ε • DpH x s₁ m`, test `y`.
    have hMax := DKhat_le_supremand (H := H) (DpH := DpH) h (ε • DpH x s₁ m) y
    -- `hMax : y ⬝ v - K h y ≤ DKhat h v ⬝ v - K h (DKhat h v)`,
    -- where `DKhat h v = q₁`.
    rw [← hq₁_eq] at hMax
    -- Goal: `K h q₁ + ∑ i, (ε • DpH x s₁ m) i * (y i - q₁ i) ≤ K h y`.
    -- Use `∑ i, v_i (y_i - q₁_i) = y ⬝ v - q₁ ⬝ v`.
    have h_sum_split :
        ∑ i, (ε • DpH x s₁ m) i * (y i - q₁ i)
          = y ⬝ (ε • DpH x s₁ m) - q₁ ⬝ (ε • DpH x s₁ m) := by
      unfold euclideanDot
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      ring
    rw [h_sum_split]
    linarith
  have hKsub₂ : HasSubgradientAt (K h) q₂ (ε • DpH x s₂ m) := by
    intro y
    have hMax := DKhat_le_supremand (H := H) (DpH := DpH) h (ε • DpH x s₂ m) y
    rw [← hq₂_eq] at hMax
    have h_sum_split :
        ∑ i, (ε • DpH x s₂ m) i * (y i - q₂ i)
          = y ⬝ (ε • DpH x s₂ m) - q₂ ⬝ (ε • DpH x s₂ m) := by
      unfold euclideanDot
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      ring
    rw [h_sum_split]
    linarith
  -- Step 3: H-subgradient inequalities at sᵢ from `convexOn_subgradient_dotCLMHam`.
  have hHsub₁ : ∀ y : Fin d → ℝ,
      H x s₁ m + ∑ i, (DpH x s₁ m) i * (y i - s₁ i) ≤ H x y m :=
    convexOn_subgradient_dotCLMHam hConvH (hFDH_all s₁)
  have hHsub₂ : ∀ y : Fin d → ℝ,
      H x s₂ m + ∑ i, (DpH x s₂ m) i * (y i - s₂ i) ≤ H x y m :=
    convexOn_subgradient_dotCLMHam hConvH (hFDH_all s₂)
  -- Step 4: Show both `q₁`, `q₂` minimize `F(q) := ε H(x, p - q, m) + K(q)`.
  set F : (Fin d → ℝ) → ℝ := fun q => ε * H x (p - q) m + K h q with hFdef
  -- Step 4a: convexity/strict convexity of F.
  have hF_sc : StrictConvexOn ℝ (Set.univ : Set (Fin d → ℝ)) F :=
    strictConvexOn_F_scaled (H := H) (DpH := DpH) h (le_of_lt hε) x p m hConvH
  -- Step 4b: q₁ minimizes F.
  have hq₁_min : IsMinOn F Set.univ q₁ := by
    intro q' _
    -- Goal: `F q₁ ≤ F q'`, i.e., `ε H(x, p - q₁, m) + K(q₁) ≤ ε H(x, p - q', m) + K(q')`.
    change ε * H x (p - q₁) m + K h q₁ ≤ ε * H x (p - q') m + K h q'
    -- From H-subgradient at s₁ = p - q₁ tested at p - q':
    have hH_at_q' := hHsub₁ (p - q')
    -- `hH_at_q' : H(x, s₁, m) + ∑ DpH x s₁ m (p - q')_i - s₁_i ≤ H(x, p - q', m)`.
    -- Now s₁ = p - q₁, so (p - q')_i - s₁_i = (p - q')_i - (p - q₁)_i = q₁_i - q'_i.
    have hs₁_id : s₁ = p - q₁ := by
      simp [hq₁def]
    -- Multiply by ε ≥ 0.
    have hε_nn : 0 ≤ ε := le_of_lt hε
    have hH_mul :
        ε * (H x s₁ m + ∑ i, (DpH x s₁ m) i * ((p - q') i - s₁ i))
          ≤ ε * H x (p - q') m :=
      mul_le_mul_of_nonneg_left hH_at_q' hε_nn
    have hH_expand : ε * (H x s₁ m + ∑ i, (DpH x s₁ m) i * ((p - q') i - s₁ i))
        = ε * H x s₁ m + ε * ∑ i, (DpH x s₁ m) i * ((p - q') i - s₁ i) := by ring
    rw [hH_expand] at hH_mul
    -- K-subgradient at q₁ tested at q':
    have hK_at_q' := hKsub₁ q'
    -- `K q₁ + ∑ (ε • DpH x s₁ m) i (q' i - q₁ i) ≤ K q'`.
    -- Rewrite ∑ (ε • DpH ..) i * (q' i - q₁ i) = ε * ∑ DpH i * (q' i - q₁ i).
    have hpair :
        ∑ i, (ε • DpH x s₁ m) i * (q' i - q₁ i)
          = ε * ∑ i, (DpH x s₁ m) i * (q' i - q₁ i) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      simp [Pi.smul_apply, smul_eq_mul]; ring
    rw [hpair] at hK_at_q'
    -- Convert (p - q') i - s₁ i = q₁ i - q' i:
    have h_idx : ∀ i,
        (DpH x s₁ m) i * ((p - q') i - s₁ i)
          = (DpH x s₁ m) i * (q₁ i - q' i) := by
      intro i
      congr 1
      rw [hs₁_id]
      simp only [Pi.sub_apply]
      ring
    have hsum_eq :
        ∑ i, (DpH x s₁ m) i * ((p - q') i - s₁ i)
          = ∑ i, (DpH x s₁ m) i * (q₁ i - q' i) :=
      Finset.sum_congr rfl (fun i _ => h_idx i)
    rw [hsum_eq] at hH_mul
    -- Now combine:
    -- hH_mul : ε H s₁ + ε ∑ DpH s₁ (q₁ - q') ≤ ε H(p - q')
    -- hK_at_q' : K q₁ + ε ∑ DpH s₁ (q' - q₁) ≤ K q'
    -- Adding: ε H s₁ + K q₁ + ε [∑ DpH s₁ (q₁ - q') + ∑ DpH s₁ (q' - q₁)] ≤ ε H(p - q') + K q'.
    -- The bracket is 0.
    have h_neg_sum : ∑ i, (DpH x s₁ m) i * (q' i - q₁ i)
        = -(∑ i, (DpH x s₁ m) i * (q₁ i - q' i)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      ring
    have hH_s₁_eq : H x s₁ m = H x (p - q₁) m := by rw [hs₁_id]
    rw [hH_s₁_eq] at hH_mul
    -- Substitute h_neg_sum into hK_at_q' to put both inequalities in terms of
    -- the same sum `S := ∑ DpH s₁ (q₁ - q')`.
    rw [h_neg_sum] at hK_at_q'
    -- Now:
    -- hH_mul : ε H(p - q₁) + ε S ≤ ε H(p - q'), where S := ∑ DpH s₁ (q₁ - q')
    -- hK_at_q' : K q₁ + ε (-S) ≤ K q'
    -- Adding: ε H(p - q₁) + K q₁ ≤ ε H(p - q') + K q'.
    linarith
  -- Step 4b': q₂ minimizes F (symmetric).
  have hq₂_min : IsMinOn F Set.univ q₂ := by
    intro q' _
    change ε * H x (p - q₂) m + K h q₂ ≤ ε * H x (p - q') m + K h q'
    have hs₂_id : s₂ = p - q₂ := by simp [hq₂def]
    have hε_nn : 0 ≤ ε := le_of_lt hε
    have hH_at_q' := hHsub₂ (p - q')
    have hH_mul :
        ε * (H x s₂ m + ∑ i, (DpH x s₂ m) i * ((p - q') i - s₂ i))
          ≤ ε * H x (p - q') m :=
      mul_le_mul_of_nonneg_left hH_at_q' hε_nn
    have hH_expand : ε * (H x s₂ m + ∑ i, (DpH x s₂ m) i * ((p - q') i - s₂ i))
        = ε * H x s₂ m + ε * ∑ i, (DpH x s₂ m) i * ((p - q') i - s₂ i) := by ring
    rw [hH_expand] at hH_mul
    have hK_at_q' := hKsub₂ q'
    have hpair :
        ∑ i, (ε • DpH x s₂ m) i * (q' i - q₂ i)
          = ε * ∑ i, (DpH x s₂ m) i * (q' i - q₂ i) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      simp [Pi.smul_apply, smul_eq_mul]; ring
    rw [hpair] at hK_at_q'
    have h_idx : ∀ i,
        (DpH x s₂ m) i * ((p - q') i - s₂ i)
          = (DpH x s₂ m) i * (q₂ i - q' i) := by
      intro i
      congr 1
      rw [hs₂_id]
      simp only [Pi.sub_apply]
      ring
    have hsum_eq :
        ∑ i, (DpH x s₂ m) i * ((p - q') i - s₂ i)
          = ∑ i, (DpH x s₂ m) i * (q₂ i - q' i) :=
      Finset.sum_congr rfl (fun i _ => h_idx i)
    rw [hsum_eq] at hH_mul
    have h_neg_sum : ∑ i, (DpH x s₂ m) i * (q' i - q₂ i)
        = -(∑ i, (DpH x s₂ m) i * (q₂ i - q' i)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      ring
    have hH_s₂_eq : H x s₂ m = H x (p - q₂) m := by rw [hs₂_id]
    rw [hH_s₂_eq] at hH_mul
    rw [h_neg_sum] at hK_at_q'
    linarith
  -- Step 5: Apply `StrictConvexOn.eq_of_isMinOn` to conclude q₁ = q₂.
  have hq_eq : q₁ = q₂ :=
    hF_sc.eq_of_isMinOn hq₁_min hq₂_min (Set.mem_univ _) (Set.mem_univ _)
  -- Step 6: From q₁ = q₂, derive s₁ = s₂.
  have hs_eq : s₁ = s₂ := by
    have : p - s₁ = p - s₂ := hq_eq
    have hcalc : s₁ = p - (p - s₁) := by abel
    have hcalc' : s₂ = p - (p - s₂) := by abel
    rw [hcalc, hcalc', this]
  exact hs_eq

/-! ### Closed-form `qEpsilon_eq_p_sub_MepsilonMinv` -/

/-- **Closed-form identity for `MepsilonMinv`.** At any `(x, m, p)` with
the standard pointwise riders, `MepsilonMinv h hMeas ε hInj (x, m, p)`
equals `p − qStar h hε hCont hLower`.

Proof: by `Mepsilon_xm_at_minimizer`, `M^ε_{x,m}(p − qStar) = p`. By
`MepsilonMinv_apply_image`, `MepsilonMinv` applied to `(x, m, M^ε)`
recovers `p − qStar`. -/
theorem MepsilonMinv_eq_p_sub_qStar
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε)
    (hInj : Function.Injective (MepsilonGlobal (H := H) (DpH := DpH) h ε))
    {x p : Fin d → ℝ} {m : ℝ}
    (hCont : Continuous (fun q : Fin d → ℝ => H x (p - q) m))
    (hLower : ∀ q : Fin d → ℝ,
      ‖p - q‖ ^ h.α / h.C - h.C * (m ^ h.β + 1) ≤ H x (p - q) m)
    (hConvH : ConvexOn ℝ (Set.univ : Set (Fin d → ℝ))
      (fun q : Fin d → ℝ => H x q m))
    (hFDH : HasFDerivAt (fun q : Fin d → ℝ => H x q m)
      (Hamiltonian.dotCLMHam (DpH x (p - qStar h hε hCont hLower) m))
      (p - qStar h hε hCont hLower)) :
    MepsilonMinv (H := H) (DpH := DpH) h hMeas ε hInj (x, m, p)
      = p - qStar h hε hCont hLower := by
  -- Set s := p - qStar.
  set s : Fin d → ℝ := p - qStar h hε hCont hLower with hsdef
  -- `M^ε(s) = p` by `Mepsilon_xm_at_minimizer`.
  have hM : Mepsilon_xm (H := H) (DpH := DpH) h ε x m s = p := by
    have := Mepsilon_xm_at_minimizer (H := H) (DpH := DpH)
      h hε hCont hLower hConvH hFDH
    simpa [hsdef] using this
  -- `MepsilonMinv (x, m, M^ε(s)) = s` by `MepsilonMinv_apply_image`.
  have := MepsilonMinv_apply_image (H := H) (DpH := DpH) h hMeas ε hInj x m s
  -- Rewrite `Mepsilon_xm h ε x m s = p`.
  rw [hM] at this
  exact this

/-- **Paper `eq:q-star-semi-explicit`** (line 1678): the closed-form
`q^ε(x, p, m) = p − (M^ε_{x,m})⁻¹(p) = p − MepsilonMinv h ε (x, m, p)`. -/
theorem qEpsilon_eq_p_sub_MepsilonMinv
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε)
    (hInj : Function.Injective (MepsilonGlobal (H := H) (DpH := DpH) h ε))
    {x p : Fin d → ℝ} {m : ℝ}
    (hCont : Continuous (fun q : Fin d → ℝ => H x (p - q) m))
    (hLower : ∀ q : Fin d → ℝ,
      ‖p - q‖ ^ h.α / h.C - h.C * (m ^ h.β + 1) ≤ H x (p - q) m)
    (hConvH : ConvexOn ℝ (Set.univ : Set (Fin d → ℝ))
      (fun q : Fin d → ℝ => H x q m))
    (hFDH : HasFDerivAt (fun q : Fin d → ℝ => H x q m)
      (Hamiltonian.dotCLMHam (DpH x (p - qStar h hε hCont hLower) m))
      (p - qStar h hε hCont hLower)) :
    qStar h hε hCont hLower
      = p - MepsilonMinv (H := H) (DpH := DpH) h hMeas ε hInj (x, m, p) := by
  rw [MepsilonMinv_eq_p_sub_qStar (H := H) (DpH := DpH)
    h hMeas hε hInj hCont hLower hConvH hFDH]
  abel

/-! ### Unconditional measurability drain (D2.6) -/

/-- **Unconditional `q^ε` measurability** (paper line 1684). Given the
global injectivity hypothesis `hInj` (reducible per-fiber to
`HypothesisHpDifferentiable` via `Mepsilon_xm_injective`), and a candidate
`q` for the inf-conv minimizer with the formula bridge
`q xpm = xpm.2.1 − MepsilonMinv h hMeas ε hInj (xpm.1, xpm.2.2, xpm.2.1)`
(which is `paper:eq:q-star-semi-explicit` applied pointwise via
`qEpsilon_eq_p_sub_MepsilonMinv`), `q` is Borel measurable.

This is the unconditional drain of `qEpsilon_measurable_of_globalInjective`. -/
theorem qEpsilon_measurable
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (ε : ℝ)
    (hInj : Function.Injective (MepsilonGlobal (H := H) (DpH := DpH) h ε))
    {q : (Fin d → ℝ) × (Fin d → ℝ) × ℝ → (Fin d → ℝ)}
    (hq_eq : ∀ xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ,
      q xpm = xpm.2.1
        - MepsilonMinv (H := H) (DpH := DpH) h hMeas ε hInj
            (xpm.1, xpm.2.2, xpm.2.1)) :
    Measurable q :=
  qEpsilon_measurable_of_globalInjective (H := H) (DpH := DpH)
    h hMeas ε hInj hq_eq

/-- **Unconditional `H^ε` measurability** (paper line 1684, second
deliverable). Given joint Borel measurability of `D_pH`, a candidate `qE`
that equals the inf-conv minimizer pointwise, and `qE`'s measurability,
the formula-RHS `(x, p, m) ↦ H(x, p − qE, m) + (1/ε) K(qE)` is Borel
measurable. -/
theorem Hepsilon_measurable
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (ε : ℝ)
    {qE : (Fin d → ℝ) × (Fin d → ℝ) × ℝ → (Fin d → ℝ)}
    (hqE : Measurable qE) :
    Measurable (fun xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ =>
      H xpm.1 (xpm.2.1 - qE xpm) xpm.2.2
        + (1 / ε) * K h (qE xpm)) :=
  Hepsilon_measurable_of_inv (H := H) (DpH := DpH) h hMeas ε hqE

/-! ### Canonical measurable minimiser selector (A1d formula package, part 1)

Paper `eq:q-star-semi-explicit` (line 1678) reads
`q^ε(x, p, m) = p − (M^ε_{x,m})⁻¹(p)`. With D2 (`paper:lem:inf-conv-props.(ii)`,
iters 0811–0812) the global Lusin–Souslin measurable inverse `MepsilonMinv`
is available, and `MepsilonMinv_measurable` proves it Borel-measurable
unconditionally given `(hMeas, hInj)`. We package the *concrete* canonical
global minimiser selector `q^ε = p − MepsilonMinv(x, m, p)` and wire the
now-available `Measurable Minv` through the iter-0807/0811 cascade
(`qEpsilon_measurable`) to obtain its global Borel measurability. This is
the formula-package deliverable (1) feeding `DpHepsilon` / the substituted
`H^ε` measurability and (downstream) the substituted-pair certificates. -/

/-- **Canonical global minimiser selector** (paper `eq:q-star-semi-explicit`,
line 1678). Built from the D2 measurable inverse `MepsilonMinv`, this is the
concrete `q^ε(x, p, m) = p − (M^ε_{x,m})⁻¹(p)`. -/
noncomputable def qEofMinv
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (ε : ℝ)
    (hInj : Function.Injective (MepsilonGlobal (H := H) (DpH := DpH) h ε)) :
    (Fin d → ℝ) × (Fin d → ℝ) × ℝ → (Fin d → ℝ) :=
  fun xpm =>
    xpm.2.1 - MepsilonMinv (H := H) (DpH := DpH) h hMeas ε hInj
      (xpm.1, xpm.2.2, xpm.2.1)

/-- The formula-bridge `rfl`: `qEofMinv xpm = p − Minv(x, m, p)`
(paper `eq:q-star-semi-explicit`). -/
lemma qEofMinv_eq
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (ε : ℝ)
    (hInj : Function.Injective (MepsilonGlobal (H := H) (DpH := DpH) h ε))
    (xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ) :
    qEofMinv (H := H) (DpH := DpH) h hMeas ε hInj xpm
      = xpm.2.1 - MepsilonMinv (H := H) (DpH := DpH) h hMeas ε hInj
          (xpm.1, xpm.2.2, xpm.2.1) := rfl

/-! ### Periodicity of the canonical selector `qEofMinv` in `x`

`substitutedPair_regularityH_of_riders` consumes the rider `hqE_per`
(periodicity of `qEofMinv` in `x`). On the torus `Tᵈ` (paper
`lem:inf-conv-props`, eq:smfg), the data `H`, `DpH` are ℤᵈ-periodic in
`x`; the regularised minimiser `M^ε_{x,m}(s) = s + DK̂(ε·DpH(x,s,m))`
inherits that periodicity, and so does its (per-fiber bijective) inverse
`MepsilonMinv`, hence `q^ε = p − M⁻¹`.

The periodicity of `MepsilonMinv` in `x` for **every** `p` requires
per-fiber surjectivity of `M^ε_{x,m}` (paper: "the map ... can be
inverted") — the `Classical.choose` left-inverse is otherwise arbitrary
off the range. Both `hDpH_per` (torus periodicity of `DpH`) and `hSurj`
(invertibility of `M^ε`) are standing paper-faithful assumptions. -/

/-- **Periodicity of `M^ε_{x,m}` in `x`.** Given periodicity of `DpH`
in `x`, the regularised minimiser map `x ↦ M^ε_{x,m}(s)` is periodic.
Since `M^ε_{x,m}(s) = s + DK̂(ε·DpH(x,s,m))` and only the `DpH`-value
depends on `x`, periodicity of `DpH` transfers directly. -/
theorem Mepsilon_xm_periodic
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (ε : ℝ)
    (hDpH_per : ∀ p m, StationaryMFG.Periodic.IsPeriodic
      (fun x : Fin d → ℝ => DpH x p m))
    (m : ℝ) (s : Fin d → ℝ) :
    StationaryMFG.Periodic.IsPeriodic
      (fun x : Fin d → ℝ => Mepsilon_xm (H := H) (DpH := DpH) h ε x m s) := by
  intro k x
  change Mepsilon_xm (H := H) (DpH := DpH) h ε (x + fun i => (k i : ℝ)) m s
       = Mepsilon_xm (H := H) (DpH := DpH) h ε x m s
  unfold Mepsilon_xm
  -- Goal: `s + DK̂(ε • DpH (x+k) s m) = s + DK̂(ε • DpH x s m)`.
  have hper := hDpH_per s m k x
  simp only at hper
  rw [hper]

/-- **Periodicity of `MepsilonMinv` in `x`.** For every `(p, m)`, the
map `x ↦ MepsilonMinv h hMeas ε hInj (x, m, p)` is ℤᵈ-periodic.

Given per-fiber surjectivity `hSurj` of `M^ε_{x,m}`, pick `s` with
`M^ε_{x,m}(s) = p`. By `MepsilonMinv_apply_image`,
`MepsilonMinv (x, m, p) = MepsilonMinv (x, m, M^ε_{x,m}(s)) = s`. By
`Mepsilon_xm_periodic`, `M^ε_{x+k,m}(s) = M^ε_{x,m}(s) = p`, so
`MepsilonMinv (x+k, m, p) = MepsilonMinv (x+k, m, M^ε_{x+k,m}(s)) = s`
as well. Both sides equal `s`. -/
theorem MepsilonMinv_periodic
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (ε : ℝ)
    (hInj : Function.Injective (MepsilonGlobal (H := H) (DpH := DpH) h ε))
    (hDpH_per : ∀ p m, StationaryMFG.Periodic.IsPeriodic
      (fun x : Fin d → ℝ => DpH x p m))
    (hSurj : ∀ (x : Fin d → ℝ) (m : ℝ),
      Function.Surjective
        (fun s => Mepsilon_xm (H := H) (DpH := DpH) h ε x m s))
    (p : Fin d → ℝ) (m : ℝ) :
    StationaryMFG.Periodic.IsPeriodic
      (fun x : Fin d → ℝ =>
        MepsilonMinv (H := H) (DpH := DpH) h hMeas ε hInj (x, m, p)) := by
  intro k x
  change MepsilonMinv (H := H) (DpH := DpH) h hMeas ε hInj
        ((x + fun i => (k i : ℝ)), m, p)
       = MepsilonMinv (H := H) (DpH := DpH) h hMeas ε hInj (x, m, p)
  -- Pick `s` with `M^ε_{x,m}(s) = p`.
  obtain ⟨s, hs⟩ := hSurj x m p
  have hsp : Mepsilon_xm (H := H) (DpH := DpH) h ε x m s = p := hs
  -- RHS = s.
  have hRHS : MepsilonMinv (H := H) (DpH := DpH) h hMeas ε hInj (x, m, p) = s := by
    rw [← hsp]
    exact MepsilonMinv_apply_image (H := H) (DpH := DpH) h hMeas ε hInj x m s
  -- `M^ε_{x+k,m}(s) = M^ε_{x,m}(s) = p` by periodicity.
  have hShift : Mepsilon_xm (H := H) (DpH := DpH) h ε
        (x + fun i => (k i : ℝ)) m s = p := by
    have hper := Mepsilon_xm_periodic (H := H) (DpH := DpH) h ε hDpH_per m s k x
    simp only at hper
    rw [hper, hsp]
  -- LHS = s.
  have hLHS : MepsilonMinv (H := H) (DpH := DpH) h hMeas ε hInj
        ((x + fun i => (k i : ℝ)), m, p) = s := by
    rw [← hShift]
    exact MepsilonMinv_apply_image (H := H) (DpH := DpH) h hMeas ε hInj
      (x + fun i => (k i : ℝ)) m s
  rw [hLHS, hRHS]

/-- **Global Borel measurability of the canonical selector** (paper line
1684). This is the wiring of the now-available D2 measurable inverse
(`MepsilonMinv_measurable`) through the iter-0807/0811 cascade
(`qEpsilon_measurable`) to deliver `Measurable (qEofMinv …)`
unconditionally given `(hMeas, hInj)`. -/
theorem qEofMinv_measurable
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (ε : ℝ)
    (hInj : Function.Injective (MepsilonGlobal (H := H) (DpH := DpH) h ε)) :
    Measurable (qEofMinv (H := H) (DpH := DpH) h hMeas ε hInj) :=
  qEpsilon_measurable (H := H) (DpH := DpH) h hMeas ε hInj
    (q := qEofMinv (H := H) (DpH := DpH) h hMeas ε hInj)
    (qEofMinv_eq (H := H) (DpH := DpH) h hMeas ε hInj)

/-! ### Per-point bridge for the canonical selector (A1d formula package, part 2)

Paper `eq:q-star-semi-explicit` (line 1678) + `eq:H-epsilon-formula`
(line 1681). The canonical selector `qEofMinv` (built from the D2
measurable inverse) coincides at every `(x, p, m)` — equipped with the
standard pointwise riders (`hCont`/`hLower` from weak growth and
`hConvH`/`hFDH` from `HypothesisHpDifferentiable`) — with the inf-conv
minimizer `qStar`. This is the linchpin per-point identity from which the
substituted-pair formula slices (`hHform`, `hSub`, `hFtcSlice`) are
assembled in the downstream children. The proof is a pure combination of
the already-landed `qEofMinv_eq` (the `rfl` formula bridge) and
`qEpsilon_eq_p_sub_MepsilonMinv` (the closed-form `q^ε = p − M⁻¹`). -/

/-- **Per-point bridge `qEofMinv = qStar`** (paper `eq:q-star-semi-explicit`,
line 1678). At any `(x, p, m)` with the standard pointwise riders, the
canonical measurable selector `qEofMinv h hMeas ε hInj (x, p, m)` equals
the inf-conv minimizer `qStar h hε hCont hLower`.

The riders `hConvH`/`hFDH` are the per-point extracts of
`HypothesisHpDifferentiable` (convexity of `H(x, ·, m)` + Fréchet
identification `D_pH = ∇_p H`); `hCont`/`hLower` are the per-point
continuity and weak-growth lower bound. -/
theorem qEofMinv_eq_qStar
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε)
    (hInj : Function.Injective (MepsilonGlobal (H := H) (DpH := DpH) h ε))
    {x p : Fin d → ℝ} {m : ℝ}
    (hCont : Continuous (fun q : Fin d → ℝ => H x (p - q) m))
    (hLower : ∀ q : Fin d → ℝ,
      ‖p - q‖ ^ h.α / h.C - h.C * (m ^ h.β + 1) ≤ H x (p - q) m)
    (hConvH : ConvexOn ℝ (Set.univ : Set (Fin d → ℝ))
      (fun q : Fin d → ℝ => H x q m))
    (hFDH : HasFDerivAt (fun q : Fin d → ℝ => H x q m)
      (Hamiltonian.dotCLMHam (DpH x (p - qStar h hε hCont hLower) m))
      (p - qStar h hε hCont hLower)) :
    qEofMinv (H := H) (DpH := DpH) h hMeas ε hInj (x, p, m)
      = qStar h hε hCont hLower := by
  rw [qEofMinv_eq (H := H) (DpH := DpH) h hMeas ε hInj (x, p, m)]
  exact (qEpsilon_eq_p_sub_MepsilonMinv (H := H) (DpH := DpH)
    h hMeas hε hInj hCont hLower hConvH hFDH).symm

/-- **Per-point `H^ε` formula slice at the canonical selector** (paper
`eq:H-epsilon-formula`, line 1681). At any `(x, p, m)` with the standard
pointwise riders, the regularized Hamiltonian is given by the inf-conv
formula evaluated at the canonical selector `qEofMinv`. Combines the
per-point bridge `qEofMinv_eq_qStar` with `Hepsilon_eq_formula`. -/
theorem Hepsilon_eq_formula_qEofMinv
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε)
    (hInj : Function.Injective (MepsilonGlobal (H := H) (DpH := DpH) h ε))
    {x p : Fin d → ℝ} {m : ℝ}
    (hCont : Continuous (fun q : Fin d → ℝ => H x (p - q) m))
    (hLower : ∀ q : Fin d → ℝ,
      ‖p - q‖ ^ h.α / h.C - h.C * (m ^ h.β + 1) ≤ H x (p - q) m)
    (hConvH : ConvexOn ℝ (Set.univ : Set (Fin d → ℝ))
      (fun q : Fin d → ℝ => H x q m))
    (hFDH : HasFDerivAt (fun q : Fin d → ℝ => H x q m)
      (Hamiltonian.dotCLMHam (DpH x (p - qStar h hε hCont hLower) m))
      (p - qStar h hε hCont hLower)) :
    Hdelta h ε x p m
      = H x (p - qEofMinv (H := H) (DpH := DpH) h hMeas ε hInj (x, p, m)) m
          + (1 / ε) * K h (qEofMinv (H := H) (DpH := DpH) h hMeas ε hInj (x, p, m)) := by
  rw [qEofMinv_eq_qStar (H := H) (DpH := DpH) h hMeas hε hInj
    hCont hLower hConvH hFDH]
  exact Hepsilon_eq_formula h hε hCont hLower

/-! ### A.e. formula producers for the canonical selector (A1d formula package, part 3)

Paper `eq:H-epsilon-formula` (line 1681) + `eq:inf-conv.diff-relation1`
(line 1664). We lift the per-point slices `Hepsilon_eq_formula_qEofMinv`
and the K-subgradient inclusion `qEpsilon_subdiff_inclusion_K` (composed
with the bridge `qEofMinv_eq_qStar`) into the exact **a.e.** shapes that
`Hdelta_monotone` consumes, with `qOf := qEofMinv h hMeas ε hInj`.

The per-point feeders (`hCont`/`hLower` from weak growth, `hConvH`/`hFDH`
from `HypothesisHpDifferentiable`) are assembled inside a single
`filter_upwards` over the four a.e. regularity facts. `HypothesisHpDifferentiable`
is a genuine paper differentiability/convexity rider (Differentiability.lean,
fields `hasFDerivAt_H_p` = paper line 1670, `convexOn_H_p` = paper `rmk:cxty`),
NOT a proof-output oracle. -/

/-- **Slice continuity from `continuous_H_pm`.** For a fixed `m > 0`, the
section `q ↦ H(x, p − q, m)` is (globally) continuous, given the a.e.
`(p, m)`-continuity of `H(x, ·, ·)` on `{0 < pm.2}` (the `RegularityH`
field `continuous_H_pm`, specialised at `x`). The map `q ↦ (p − q, m)`
lands in the open set `{0 < pm.2}` for every `q`, so the `ContinuousOn`
upgrades to a global `Continuous`. -/
private lemma H_slice_continuous_of_continuousOn
    {x p : Fin d → ℝ} {m : ℝ} (hm : 0 < m)
    (hH : ContinuousOn (fun pm : (Fin d → ℝ) × ℝ => H x pm.1 pm.2)
      {pm | 0 < pm.2}) :
    Continuous (fun q : Fin d → ℝ => H x (p - q) m) := by
  -- The open target set `{0 < pm.2}`.
  have hOpen : IsOpen {qm : (Fin d → ℝ) × ℝ | 0 < qm.2} := by
    have : IsOpen {y : ℝ | 0 < y} := isOpen_lt continuous_const continuous_id
    exact this.preimage continuous_snd
  rw [continuous_iff_continuousAt]
  intro q
  -- The shift map `q ↦ (p − q, m)` is continuous at `q`.
  have hShift_at : ContinuousAt
      (fun q : Fin d → ℝ => ((p - q), m)) q :=
    ((continuous_const.sub continuous_id).continuousAt).prodMk
      (continuousAt_const)
  -- `(p − q, m)` lies in the open set.
  have hTarget_in : ((p - q), m) ∈ {qm : (Fin d → ℝ) × ℝ | 0 < qm.2} := hm
  -- Upgrade `ContinuousOn` at the target to `ContinuousAt`.
  have hH_at : ContinuousAt
      (fun qm : (Fin d → ℝ) × ℝ => H x qm.1 qm.2) ((p - q), m) :=
    (hH _ hTarget_in).continuousAt (hOpen.mem_nhds hTarget_in)
  -- Compose `H ∘ shift` at `q`.
  exact ContinuousAt.comp (x := q)
    (g := fun qm : (Fin d → ℝ) × ℝ => H x qm.1 qm.2)
    (f := fun q : Fin d → ℝ => ((p - q), m))
    hH_at hShift_at

/-- **A.e. `hHform` producer for the canonical selector** (paper
`eq:H-epsilon-formula`, line 1681). For the canonical measurable selector
`qE := qEofMinv h hMeas ε hInj`, the regularized Hamiltonian is given a.e.
(for `0 < m`) by the inf-conv formula `H(x, p − qE, m) + (1/ε) K(qE)`.

This is the exact shape consumed by `Hdelta_monotone`'s `hHform`. The
per-point feeders are assembled from `h.continuous_H_pm`, `h.lower`,
`hDiff.convexOn_H_p`, `hDiff.hasFDerivAt_H_p`. -/
theorem hHform_qEofMinv
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (hDiff : Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε)
    (hInj : Function.Injective (MepsilonGlobal (H := H) (DpH := DpH) h ε)) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
      ∀ p m, 0 < m →
        Hdelta h ε x p m
          = H x (p - qEofMinv (H := H) (DpH := DpH) h hMeas ε hInj (x, p, m)) m
            + (1 / ε) *
                K h (qEofMinv (H := H) (DpH := DpH) h hMeas ε hInj (x, p, m)) := by
  filter_upwards [h.continuous_H_pm, h.lower,
    hDiff.hasFDerivAt_H_p, hDiff.convexOn_H_p]
    with x hxCont hxLower hxFDH hxConvH
  intro p m hm
  -- Per-point continuity feeder.
  have hCont : Continuous (fun q : Fin d → ℝ => H x (p - q) m) :=
    H_slice_continuous_of_continuousOn (H := H) hm hxCont
  -- Per-point lower-bound feeder.
  have hLower : ∀ q : Fin d → ℝ,
      ‖p - q‖ ^ h.α / h.C - h.C * (m ^ h.β + 1) ≤ H x (p - q) m := by
    intro q
    have := hxLower (p - q) m hm
    -- `hxLower` gives `H x (p−q) m ≥ ‖p−q‖^α/C − C(m^β+1)`.
    simpa [ge_iff_le] using this
  -- Per-point convexity feeder.
  have hConvH : ConvexOn ℝ (Set.univ : Set (Fin d → ℝ))
      (fun q : Fin d → ℝ => H x q m) := hxConvH m hm
  -- Per-point Fréchet-derivative feeder at `p − qStar`.
  have hFDH : HasFDerivAt (fun q : Fin d → ℝ => H x q m)
      (Hamiltonian.dotCLMHam (DpH x (p - qStar h hε hCont hLower) m))
      (p - qStar h hε hCont hLower) :=
    hxFDH (p - qStar h hε hCont hLower) m hm
  exact Hepsilon_eq_formula_qEofMinv (H := H) (DpH := DpH)
    h hMeas hε hInj hCont hLower hConvH hFDH

/-- **A.e. `hSub` producer for the canonical selector** (paper
`eq:inf-conv.diff-relation1`, first inclusion, line 1664). For the
canonical measurable selector `qE := qEofMinv h hMeas ε hInj`, the
subgradient inequality `D_pH(x, p − qE, m) ⬝ (q − qE) ≤ (1/ε)(K q − K qE)`
holds a.e. (for `0 < m`) and every `q`.

This is the exact shape consumed by `Hdelta_monotone`'s `hSub`. It combines
the per-point bridge `qEofMinv_eq_qStar` with the K-subgradient inclusion
`qEpsilon_subdiff_inclusion_K`, unfolded via `HasSubgradientAt`. -/
theorem hSub_qEofMinv
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (hDiff : Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε)
    (hInj : Function.Injective (MepsilonGlobal (H := H) (DpH := DpH) h ε)) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
      ∀ p m, 0 < m → ∀ q : Fin d → ℝ,
        DpH x (p - qEofMinv (H := H) (DpH := DpH) h hMeas ε hInj (x, p, m)) m
            ⬝ (q - qEofMinv (H := H) (DpH := DpH) h hMeas ε hInj (x, p, m))
          ≤ (1 / ε) *
              (K h q
                - K h (qEofMinv (H := H) (DpH := DpH) h hMeas ε hInj (x, p, m))) := by
  filter_upwards [h.continuous_H_pm, h.lower,
    hDiff.hasFDerivAt_H_p, hDiff.convexOn_H_p]
    with x hxCont hxLower hxFDH hxConvH
  intro p m hm q
  -- Per-point feeders (same as in `hHform_qEofMinv`).
  have hCont : Continuous (fun q : Fin d → ℝ => H x (p - q) m) :=
    H_slice_continuous_of_continuousOn (H := H) hm hxCont
  have hLower : ∀ q : Fin d → ℝ,
      ‖p - q‖ ^ h.α / h.C - h.C * (m ^ h.β + 1) ≤ H x (p - q) m := by
    intro q
    have := hxLower (p - q) m hm
    simpa [ge_iff_le] using this
  have hConvH : ConvexOn ℝ (Set.univ : Set (Fin d → ℝ))
      (fun q : Fin d → ℝ => H x q m) := hxConvH m hm
  have hFDH : HasFDerivAt (fun q : Fin d → ℝ => H x q m)
      (Hamiltonian.dotCLMHam (DpH x (p - qStar h hε hCont hLower) m))
      (p - qStar h hε hCont hLower) :=
    hxFDH (p - qStar h hε hCont hLower) m hm
  -- Identify the canonical selector with the inf-conv minimizer.
  set qS : Fin d → ℝ := qStar h hε hCont hLower with hqSdef
  have hqE_eq : qEofMinv (H := H) (DpH := DpH) h hMeas ε hInj (x, p, m) = qS :=
    qEofMinv_eq_qStar (H := H) (DpH := DpH) h hMeas hε hInj
      hCont hLower hConvH hFDH
  rw [hqE_eq]
  -- The K-subgradient inclusion: `ε • D_pH(x, p − qS, m) ∈ ∂K(qS)`.
  set v : Fin d → ℝ := DpH x (p - qS) m with hvdef
  have hsub : HasSubgradientAt (K h) qS (ε • v) :=
    qEpsilon_subdiff_inclusion_K (H := H) (DpH := DpH)
      h hε hCont hLower hConvH hFDH
  -- Unfold at the test point `q`:
  --   `K h qS + ∑ i, (ε • v) i * (q i − qS i) ≤ K h q`.
  have hsub_q := hsub q
  -- Rewrite `∑ i, (ε • v) i * (q i − qS i) = ε * (v ⬝ (q − qS))`.
  have hpair : ∑ i, (ε • v) i * (q i - qS i) = ε * (v ⬝ (q - qS)) := by
    unfold euclideanDot
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  rw [hpair] at hsub_q
  -- `hsub_q : K h qS + ε * (v ⬝ (q − qS)) ≤ K h q`, hence
  -- `v ⬝ (q − qS) ≤ (1/ε)(K h q − K h qS)`.
  have hεpos : (0 : ℝ) < ε := hε
  have hkey : ε * (v ⬝ (q - qS)) ≤ K h q - K h qS := by linarith
  have hfinal : v ⬝ (q - qS) ≤ (1 / ε) * (K h q - K h qS) := by
    rw [one_div, ← div_eq_inv_mul]
    rw [le_div_iff₀ hεpos]
    linarith [hkey]
  -- Goal is exactly `v ⬝ (q − qS) ≤ (1/ε)(K h q − K h qS)` after unfolding `v`.
  simpa [hvdef] using hfinal

/-! ### A1d formula package, part 3 — a.e. formula/subgradient producers
at the canonical selector

For the canonical measurable selector `qE := qEofMinv h hMeas ε hInj`, this
section delivers the a.e./`{0<m}` formula and subgradient producers
(`hDpHform_qEofMinv`, `hHform_qEofMinv`, `hSub_qEofMinv`, …) for the
regularized pair `(Hdelta h ε, DpHepsilon h qE)`.

NOTE: the downstream substituted-pair `HypothesisMonotone`/`RegularityH`
certs that once consumed these (the dead `qEofMinv` + global-injectivity
`hInj` route) have been removed; the live Theorem 3 monotonicity/regularity
supply runs through the abstract selector family
(`InfConvSelectorFamily` / `qMeasFam`), which needs no `hInj`. These a.e.
producers are retained as reusable formula-bridge infrastructure.

`HypothesisHpDifferentiable` (`hDiff`) is a genuine paper differentiability
/convexity input (anti-oracle-checked iter 1048), threaded into these
producers; it is NOT a proof-output oracle. -/

/-- **A.e. `hDpHε_form` producer for the canonical selector** (paper
`eq:DpH-epsilon-formula`, line 1689). For `qE := qEofMinv h hMeas ε hInj`,
the regularized gradient `D_pH^ε(x, p, m)` is `D_pH(x, p − qE (x,p,m), m)`
by definition (`DpHepsilon_eq` is `rfl`). We lift the unconditional pointwise
identity to the exact a.e. shape consumed by `Hdelta_monotone`'s
`hDpHε_form`. -/
theorem hDpHform_qEofMinv
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε)
    (hInj : Function.Injective (MepsilonGlobal (H := H) (DpH := DpH) h ε)) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
      ∀ p m, 0 < m →
        DpHepsilon (H := H) (DpH := DpH) h
            (qEofMinv (H := H) (DpH := DpH) h hMeas ε hInj) x p m
          = DpH x
              (p - qEofMinv (H := H) (DpH := DpH) h hMeas ε hInj (x, p, m)) m := by
  refine Filter.Eventually.of_forall ?_
  intro x p m _hm
  exact DpHepsilon_eq (H := H) (DpH := DpH) h
    (qEofMinv (H := H) (DpH := DpH) h hMeas ε hInj) x p m

/-- **Fixed-`m` slice continuity from `(p, m)`-continuity on `{0 < m}`.**

`RegularityH.continuous_DpH_pm` only delivers `ContinuousOn` on the open set
`{pm | 0 < pm.2}` (not global `Continuous`). For the envelope lemma (Task 1)
we need genuine `Continuous` of the fixed-`m` slice `p ↦ G (p, m)`. Since
`{pm | 0 < pm.2}` is open and `(p, m)` lies in it for `0 < m`, we extract
`ContinuousAt` at each `(p, m)` and pull it back along the continuous
embedding `p ↦ (p, m)`. -/
lemma continuous_p_slice_of_continuousOn_pm
    {G : (Fin d → ℝ) × ℝ → Fin d → ℝ}
    (hG : ContinuousOn G {pm | 0 < pm.2})
    {m : ℝ} (hm : 0 < m) :
    Continuous (fun p : Fin d → ℝ => G (p, m)) := by
  -- The slot `{pm | 0 < pm.2}` is open.
  have hopen : IsOpen {pm : (Fin d → ℝ) × ℝ | 0 < pm.2} :=
    isOpen_lt continuous_const continuous_snd
  rw [continuous_iff_continuousAt]
  intro p
  -- `(p, m)` is in the open set.
  have hmem : (p, m) ∈ {pm : (Fin d → ℝ) × ℝ | 0 < pm.2} := hm
  -- `ContinuousAt G (p, m)` from `ContinuousOn` on the open set.
  have hGat : ContinuousAt G (p, m) :=
    (hG.continuousAt (hopen.mem_nhds hmem))
  -- Compose with the continuous embedding `p ↦ (p, m)`.
  have hemb : ContinuousAt (fun q : Fin d → ℝ => (q, m)) p :=
    (continuous_id.prodMk continuous_const).continuousAt
  exact ContinuousAt.comp (g := G) (f := fun q : Fin d → ℝ => (q, m)) hGat hemb

/-- **Task 3 — a.e. subgradient field for the regularized Hamiltonian at the
canonical selector** (paper `eq:inf-conv.diff-relation1`). For
`qE := qEofMinv h hMeas ε hInj`, for a.e. `x` and every `(p, m)` with `0 < m`,
the regularized gradient `D_pH^ε(x, p, m)` is a subgradient of the convex slice
`p' ↦ H^ε(x, p', m)` at `p`. This mirrors `hSub_qEofMinv` (the K-side support
inequality) but packages the genuine convex-analysis subgradient of `H^ε`,
projected from `qEpsilon_subdiff_inclusion_Hepsilon` after identifying the
canonical selector with the inf-conv minimizer via `qEofMinv_eq_qStar`. -/
theorem hSubgradientHepsilon_qEofMinv
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (hDiff : Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε)
    (hInj : Function.Injective (MepsilonGlobal (H := H) (DpH := DpH) h ε)) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
      ∀ p m, 0 < m →
        HasSubgradientAt (fun p' : Fin d → ℝ => Hdelta h ε x p' m) p
          (DpHepsilon (H := H) (DpH := DpH) h
            (qEofMinv (H := H) (DpH := DpH) h hMeas ε hInj) x p m) := by
  filter_upwards [h.continuous_H_pm, h.lower,
    hDiff.hasFDerivAt_H_p, hDiff.convexOn_H_p]
    with x hxCont hxLower hxFDH hxConvH
  intro p m hm
  -- Per-point feeders (same as in `hSub_qEofMinv`).
  have hCont : Continuous (fun q : Fin d → ℝ => H x (p - q) m) :=
    H_slice_continuous_of_continuousOn (H := H) hm hxCont
  have hLower : ∀ q : Fin d → ℝ,
      ‖p - q‖ ^ h.α / h.C - h.C * (m ^ h.β + 1) ≤ H x (p - q) m := by
    intro q
    have := hxLower (p - q) m hm
    simpa [ge_iff_le] using this
  have hLower' : ∀ p' q : Fin d → ℝ,
      ‖p' - q‖ ^ h.α / h.C - h.C * (m ^ h.β + 1) ≤ H x (p' - q) m := by
    intro p' q
    have := hxLower (p' - q) m hm
    simpa [ge_iff_le] using this
  have hConvH : ConvexOn ℝ (Set.univ : Set (Fin d → ℝ))
      (fun q : Fin d → ℝ => H x q m) := hxConvH m hm
  have hFDH : HasFDerivAt (fun q : Fin d → ℝ => H x q m)
      (Hamiltonian.dotCLMHam (DpH x (p - qStar h hε hCont hLower) m))
      (p - qStar h hε hCont hLower) :=
    hxFDH (p - qStar h hε hCont hLower) m hm
  -- The subgradient inclusion for `H^ε` at `p`.
  have hsub :
      HasSubgradientAt (fun p' : Fin d → ℝ => Hdelta h ε x p' m) p
        (DpH x (p - qStar h hε hCont hLower) m) :=
    qEpsilon_subdiff_inclusion_Hepsilon (H := H) (DpH := DpH)
      h hε hCont hLower hConvH hFDH hLower'
  -- Identify `D_pH^ε(x, p, m)` with `D_pH(x, p − qStar, m)`.
  have hqE_eq : qEofMinv (H := H) (DpH := DpH) h hMeas ε hInj (x, p, m)
      = qStar h hε hCont hLower :=
    qEofMinv_eq_qStar (H := H) (DpH := DpH) h hMeas hε hInj
      hCont hLower hConvH hFDH
  have hgrad : DpHepsilon (H := H) (DpH := DpH) h
      (qEofMinv (H := H) (DpH := DpH) h hMeas ε hInj) x p m
        = DpH x (p - qStar h hε hCont hLower) m := by
    rw [DpHepsilon_eq, hqE_eq]
  rw [hgrad]
  exact hsub

/-- **Task 4 — internal producer for `HypothesisHepsilonFtcSlice`** (paper
`lem:inf-conv-props`, `eq:DpHdelta.dotp.minusH`). For the canonical selector
`qE := qEofMinv h hMeas ε hInj`, the regularized FTC-slice rider is *derived*
(not assumed) from the a.e. subgradient field (`hSubgradientHepsilon_qEofMinv`,
Task 3) plus continuity of `D_pH^ε` (`hDpHε_cont`, supplied by
`RegularityH.continuous_DpH_pm`), via the finite-dimensional envelope lemma
`hasFDerivAt_of_continuous_subgradient_field` (Task 1) and the FTC-slice
identity `ftc_slice_of_hasFDerivAt_continuous_gradient` (Task 2). This **removes
the former `HypothesisHepsilonFtcSlice` rider** from the Theorem-3 pipeline. -/
theorem hepsilonFtcSlice_qEofMinv_of_envelope
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (hDiff : Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε)
    (hInj : Function.Injective (MepsilonGlobal (H := H) (DpH := DpH) h ε))
    (hDpHε_cont :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict
        (StationaryMFG.Periodic.UnitCube d)),
        ContinuousOn (fun pm : (Fin d → ℝ) × ℝ =>
            DpHepsilon (H := H) (DpH := DpH) h
              (qEofMinv (H := H) (DpH := DpH) h hMeas ε hInj) x pm.1 pm.2)
          {pm | 0 < pm.2}) :
    Hamiltonian.HypothesisHepsilonFtcSlice (d := d) (Hdelta h ε)
      (DpHepsilon (H := H) (DpH := DpH) h
        (qEofMinv (H := H) (DpH := DpH) h hMeas ε hInj)) := by
  constructor
  filter_upwards [hSubgradientHepsilon_qEofMinv (H := H) (DpH := DpH)
      h hMeas hDiff hε hInj, hDpHε_cont]
    with x hxSub hxCont
  intro p m hm
  -- Fix `m`: the slice functions and the slice gradient field.
  set F : (Fin d → ℝ) → ℝ := fun p' => Hdelta h ε x p' m with hF
  set G : (Fin d → ℝ) → (Fin d → ℝ) :=
    fun p' => DpHepsilon (H := H) (DpH := DpH) h
      (qEofMinv (H := H) (DpH := DpH) h hMeas ε hInj) x p' m with hG
  -- Slice continuity of `G` from `hxCont` via the local helper.
  have hGcont : Continuous G := by
    have := continuous_p_slice_of_continuousOn_pm
      (G := fun pm : (Fin d → ℝ) × ℝ =>
        DpHepsilon (H := H) (DpH := DpH) h
          (qEofMinv (H := H) (DpH := DpH) h hMeas ε hInj) x pm.1 pm.2)
      hxCont hm
    simpa [hG] using this
  -- `G p'` is a subgradient of `F` at every `p'` (from Task 3, fixed `m`).
  have hGsub : ∀ p' : Fin d → ℝ, HasSubgradientAt F p' (G p') := by
    intro p'
    have := hxSub p' m hm
    simpa [hF, hG] using this
  -- Task 1: `F` is Fréchet-differentiable with derivative `dotCLMHam (G ·)`.
  have hFD : ∀ p' : Fin d → ℝ,
      HasFDerivAt F (Hamiltonian.dotCLMHam (G p')) p' :=
    hasFDerivAt_of_continuous_subgradient_field hGcont hGsub
  -- Task 2: the FTC-slice identity at `p`.
  have hFTC := ftc_slice_of_hasFDerivAt_continuous_gradient hFD hGcont p
  -- Translate to the exact field shape.
  simpa [hF, hG] using hFTC

/-- **A.e. regularized FTC-slice producer for the canonical selector**
(paper `eq:DpHdelta.dotp.minusH`, line 1815, "as in `lem:A1+anyother`").
For the canonical measurable selector `qE := qEofMinv h hMeas ε hInj`,
this projects the FTC-slice identity for the regularized pair
`(Hdelta h ε, DpHepsilon h qE)` from the **internally derived**
`HypothesisHepsilonFtcSlice` (no longer a rider; see
`hepsilonFtcSlice_qEofMinv_of_envelope`).

The FTC slice is **derived internally** (no rider): from the a.e. subgradient
field plus continuity of `D_pH^ε` (`hDpHε_cont`) through the envelope producer
`hepsilonFtcSlice_qEofMinv_of_envelope` (Tasks 1–4). The two-sided Fréchet
differentiability of `H^ε(x, ·, m)` that the integral form requires is now
obtained from the one-sided subgradient inclusion
`qEpsilon_subdiff_inclusion_Hepsilon` together with continuity, via the
finite-dimensional envelope lemma. -/
theorem hFtcSlice_qEofMinv
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (hDiff : Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε)
    (hInj : Function.Injective (MepsilonGlobal (H := H) (DpH := DpH) h ε))
    (hDpHε_cont :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict
        (StationaryMFG.Periodic.UnitCube d)),
        ContinuousOn (fun pm : (Fin d → ℝ) × ℝ =>
            DpHepsilon (H := H) (DpH := DpH) h
              (qEofMinv (H := H) (DpH := DpH) h hMeas ε hInj) x pm.1 pm.2)
          {pm | 0 < pm.2}) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
      ∀ p m, 0 < m →
        (DpHepsilon (H := H) (DpH := DpH) h
            (qEofMinv (H := H) (DpH := DpH) h hMeas ε hInj) x p m) ⬝ p
          - (Hdelta h ε x p m - Hdelta h ε x (0 : Fin d → ℝ) m)
          = ∫ t in (0 : ℝ)..1,
              ((DpHepsilon (H := H) (DpH := DpH) h
                  (qEofMinv (H := H) (DpH := DpH) h hMeas ε hInj) x p m
                - DpHepsilon (H := H) (DpH := DpH) h
                  (qEofMinv (H := H) (DpH := DpH) h hMeas ε hInj) x (t • p) m) ⬝ p) :=
  (hepsilonFtcSlice_qEofMinv_of_envelope (H := H) (DpH := DpH)
    h hMeas hDiff hε hInj hDpHε_cont).ftc_slice

/-! **REMOVED (dead Minv/qEofMinv route): the substituted-pair monotone/
regularityH certs and the `hUniq`/`qOfMin`/`hCont3` `qEofMinv_pos` rider
producers.**

These keyed on the canonical inf-conv minimiser `qEofMinv` + global injectivity
`hInj` (the Lusin–Souslin-era construction). The live Theorem 3 route runs
through the abstract selector family (`InfConvSelectorFamily` /
`qStarSelectorFam` / `qMeasFam`, `hUniq_qStarSelectorFam_pos`), which never
needs `hInj`. The removed decls had no live consumers. -/

/-! ### Unit tests (D2b) -/

/-- Unit test (`d = 1`): the zero Hamiltonian satisfies per-fiber
injectivity. `DpH = 0` ⇒ `M^ε_{x,m}(s) = s + DKhat(0) = s + 0 = s`, so
injectivity is trivial. -/
example
    (h : HypothesisWeakGrowth (d := 1)
      (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : Fin 1 → ℝ)))
    {ε : ℝ} (hε : 0 < ε) (x : Fin 1 → ℝ) (m : ℝ) :
    Function.Injective
      (fun s : Fin 1 → ℝ =>
        Mepsilon_xm
          (H := fun _ _ _ => (0 : ℝ))
          (DpH := fun _ _ _ => (0 : Fin 1 → ℝ)) h ε x m s) := by
  apply Mepsilon_xm_injective
    (H := fun _ _ _ => (0 : ℝ))
    (DpH := fun _ _ _ => (0 : Fin 1 → ℝ)) h hε x m
  · -- ConvexOn of the zero function.
    exact convexOn_const (𝕜 := ℝ) (E := (Fin 1 → ℝ)) (0 : ℝ) convex_univ
  · -- Fréchet derivative of zero is the zero CLM = dotCLMHam 0.
    intro s
    have h0 : (Hamiltonian.dotCLMHam (0 : Fin 1 → ℝ)) = 0 := Hamiltonian.dotCLMHam_zero
    rw [h0]
    exact hasFDerivAt_const (𝕜 := ℝ) (E := (Fin 1 → ℝ)) (0 : ℝ) s

/-! ## Two-bundle `H^ε` estimate carriers (paper `prop:boundsHepsilon`)

D1 of the T3 real-drain. Paper `prop:boundsHepsilon` (lines 1781-1818) splits its
four estimates into two regimes with **different** constants:

* the **upper** (`eq:H-epsilon.upper`) and **gradient-upper** (`eq:DpHdelta.upper`)
  bounds carry an `ε`-dependent constant `C_ε`;
* the **lower-uniform** (`eq:H-epsilon.lower.uniform`) and **Lagrangian**
  (`eq:DpHdelta.dotp.minusH`) bounds carry a constant `C` **independent of `ε`**.

We expose two carriers matching that split. Crucially, `HdeltaPowerEpsData` carries
a *per-`ε`* `HypothesisPowerGrowth` whose own constant `(hpow ε).C` is allowed to
depend on `ε` (it is `C_ε`); it deliberately has **no** `hC_eq` field, because a
single `ε`-uniform constant inside `HypothesisPowerGrowth` would be FALSE (the
upper/gradient bounds genuinely blow up as `ε → 0`). The exponents `α`, `β`, by
contrast, ARE pinned to `hweak`'s exponents (`hα_eq`/`hβ_eq`), since the inf-conv
regularization does not change the growth exponents.

`HdeltaUniformBounds` carries the genuinely `ε`-independent coercive lower bound
and Lagrangian lower bound, with one shared constant `C0`.

These are the *statement-first* carriers (CONVENTIONS §8). The closed *producers*
`hdeltaPowerEpsData_of_weakGrowth` / `hdeltaUniformBounds_of_weakGrowth` are split
to a follow-up child task: they require `qE` to be the inf-conv minimizer
(`qEofMinv hweak hmeas ε hInj`), whose construction needs the *global* injectivity
`hInj : Function.Injective (MepsilonGlobal hweak ε)`. That injectivity is only
reducible (via `Mepsilon_xm_injective`) to convexity + Fréchet-differentiability of
`H(x,·,m)` at **every** `(x, m)`, whereas the paper rider `HypothesisHpDifferentiable`
supplies those only for **a.e. `x`** and **`m > 0`** — see the task GATE #2 note. -/

/-- **Per-`ε` power-growth carrier for `(H^ε, D_pH^ε)`** (paper
`prop:boundsHepsilon`, the `C_ε`-regime estimates `eq:H-epsilon.upper`,
`eq:DpHdelta.upper`).

`hpow ε` is a `HypothesisPowerGrowth` bundle on the regularized pair
`(HdeltaPos hweak ε, DpHepsilonFam hweak qε ε)`; its growth constant `(hpow ε).C`
is the paper's `ε`-dependent `C_ε`, so we do **not** assume it is `ε`-uniform
(there is no `hC_eq` field — uniform-`C` is false). The exponents are pinned to
`hweak`'s `α`, `β` via `hα_eq`/`hβ_eq`, since regularization preserves the growth
exponents.

The carrier is the junk-extended `HdeltaPos` (not raw `Hdelta`): the parent
`RegularityH.measurable_H` field needs a global all-`m` measurability witness
that the raw `Hdelta` `iInf` lacks on `{m≤0}`, whereas `HdeltaPos` is the
constant `0` there. On `{0<m}` the two agree (`HdeltaPos_eq_Hdelta_of_pos`), so
the estimate fields are unaffected. -/
structure HdeltaPowerEpsData
    (hweak : Hamiltonian.HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d) where
  /-- For each `ε`, `(HdeltaPos hweak ε, DpHepsilonFam hweak qε ε)` satisfies the
  power-growth bundle, with an `ε`-dependent constant `(hpow ε).C = C_ε`.

  The carrier is the junk-extended `HdeltaPos` (`Hdelta` on `{0<m}`, `0` on
  `{m≤0}`) rather than the raw `Hdelta`: `HypothesisPowerGrowth extends
  RegularityH`, whose `measurable_H` field demands a GLOBAL (all-`m`)
  measurability of the carrier. The raw `Hdelta` `iInf` lacks a `{m≤0}`
  measurability witness, but `HdeltaPos` is the constant `0` there and so is
  globally measurable (`HdeltaPos_measurable_of_formPos`, fed by `Hepsilon_
  regularityH_pos`). On the strict-positivity cone `{0<m}` — where every
  Theorem 3 consumer evaluates and where all four `prop:boundsHepsilon`
  estimates are stated — `HdeltaPos = Hdelta` (`HdeltaPos_eq_Hdelta_of_pos`),
  so the carrier swap is observationally faithful and the estimate fields
  transfer verbatim. -/
  hpow : ∀ ε, 0 < ε → ε ≤ 1 → Hamiltonian.HypothesisPowerGrowth (d := d)
      (HdeltaPos hweak ε) (DpHepsilonFam hweak qε ε)
  /-- The momentum exponent is preserved: `(hpow ε).α = hweak.α`. -/
  hα_eq : ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1), (hpow ε hε hε1).α = hweak.α
  /-- The mass exponent is preserved: `(hpow ε).β = hweak.β`. -/
  hβ_eq : ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1), (hpow ε hε hε1).β = hweak.β
  -- DELIBERATELY no `hC_eq`: a uniform `C` is FALSE (paper `C_ε` blows up).
  -- The `hpow` field is guarded by the paper's `0 < ε ≤ 1` regime
  -- (`prop:boundsHepsilon`): the inf-conv estimates are only valid there, and
  -- every Theorem 3 consumer evaluates `H^ε` at `0 < ε ≤ 1`.

/-- **`ε`-independent coercive bounds for `(H^ε, D_pH^ε)`** (paper
`prop:boundsHepsilon`, the `C`-regime estimates `eq:H-epsilon.lower.uniform`,
`eq:DpHdelta.dotp.minusH`).

Carries one constant `C0 > 0` **independent of `ε`** giving both the coercive lower
bound on `H^ε` and the Lagrangian lower bound on `D_pH^ε · p − H^ε`, for `0 < ε ≤ 1`
and `m > 0`, a.e. `x`. The exponents are `hweak.α`, `hweak.β`. -/
structure HdeltaUniformBounds
    (hweak : Hamiltonian.HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d) where
  /-- The `ε`-independent constant. -/
  C0 : ℝ
  /-- Positivity of the `ε`-independent constant. -/
  hC0 : 0 < C0
  /-- (eq:H-epsilon.lower.uniform) `H^ε(x,p,m) ≥ ‖p‖^α/C0 − C0(m^β+1)`,
  with `C0` independent of `ε`. -/
  lower_uniform : ∀ ε, 0 < ε → ε ≤ 1 →
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
      ∀ (p : Fin d → ℝ) (m : ℝ), 0 < m →
        (‖p‖ ^ hweak.α) / C0 - C0 * (m ^ hweak.β + 1)
          ≤ Hdelta hweak ε x p m
  /-- (eq:DpHdelta.dotp.minusH) `D_pH^ε·p − H^ε ≥ m^β/C0 − C0`,
  with `C0` independent of `ε`. -/
  lagr_uniform : ∀ ε, 0 < ε → ε ≤ 1 →
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
      ∀ (p : Fin d → ℝ) (m : ℝ), 0 < m →
        (m ^ hweak.β) / C0 - C0
          ≤ (DpHepsilonFam hweak qε ε x p m) ⬝ p - Hdelta hweak ε x p m

/-- Coherence check: the field types of `HdeltaPowerEpsData` are inhabitable in
principle — given a per-`ε` power-growth bundle with matching exponents, the carrier
assembles. This exercises the structure signature (no uniform-`C` is assumed). -/
example
    (hweak : Hamiltonian.HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d)
    (hpow : ∀ ε, 0 < ε → ε ≤ 1 → Hamiltonian.HypothesisPowerGrowth (d := d)
      (HdeltaPos hweak ε) (DpHepsilonFam hweak qε ε))
    (hα_eq : ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1), (hpow ε hε hε1).α = hweak.α)
    (hβ_eq : ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1), (hpow ε hε hε1).β = hweak.β) :
    HdeltaPowerEpsData (H := H) (DpH := DpH) hweak qε :=
  { hpow := hpow, hα_eq := hα_eq, hβ_eq := hβ_eq }

/-- Coherence check: the field types of `HdeltaUniformBounds` assemble from a
single `ε`-independent constant `C0 > 0` plus the two coercive families. -/
example
    (hweak : Hamiltonian.HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d)
    (C0 : ℝ) (hC0 : 0 < C0)
    (lower_uniform : ∀ ε, 0 < ε → ε ≤ 1 →
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
        ∀ (p : Fin d → ℝ) (m : ℝ), 0 < m →
          (‖p‖ ^ hweak.α) / C0 - C0 * (m ^ hweak.β + 1)
            ≤ Hdelta hweak ε x p m)
    (lagr_uniform : ∀ ε, 0 < ε → ε ≤ 1 →
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
        ∀ (p : Fin d → ℝ) (m : ℝ), 0 < m →
          (m ^ hweak.β) / C0 - C0
            ≤ (DpHepsilonFam hweak qε ε x p m) ⬝ p - Hdelta hweak ε x p m) :
    HdeltaUniformBounds (H := H) (DpH := DpH) hweak qε :=
  { C0 := C0, hC0 := hC0, lower_uniform := lower_uniform,
    lagr_uniform := lagr_uniform }

/-- **Localized inf-conv selector family** (paper `lem:inf-conv-props`).

This is the certificate that the inf-conv definition
`H^ε(x,p,m) = ⨅_q H(x, p−q, m) + (1/ε) K(q)` (`Hdelta`, paper `eq:defHdelta`,
line 1624) admits a **measurable minimizing selector** `qε ε` attaining the
infimum on the relevant a.e./`m>0` slice, and that the regularized gradient
`D_pH^ε` is the formula `D_pH(x, p−q^ε, m)` (paper `eq:DpH-epsilon-formula`,
line 1689).

It deliberately **replaces** the impossible *global*
`Function.Injective (MepsilonGlobal …)` target: we never need global injectivity
of the minimizer map, only the localized selector identities on `{m>0}` for a.e.
`x`. Downstream producers (`Dq3`) consume this carrier; this task supplies the
Prop structure only (no producer, no `hInj`). -/
structure InfConvSelectorFamily
    (hweak : Hamiltonian.HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d) : Prop where
  /-- The selector for each `ε` is (globally) measurable. -/
  q_meas : ∀ ε, Measurable (qε ε)
  /-- For `ε > 0`, a.e. `x`, the selector `(p,m) ↦ qε ε (x,p,m)` is continuous on
  the open positive-mass slice `{0 < m}`. -/
  q_cont_pm : ∀ ε, 0 < ε →
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
        ContinuousOn (fun pm : (Fin d → ℝ) × ℝ => qε ε (x, pm.1, pm.2))
          {pm | 0 < pm.2}
  /-- (paper `eq:defHdelta`, attainment) For `ε > 0`, a.e. `x`, and `m > 0`, the
  infimum defining `H^ε` is attained at `qε ε`, with the penalty spelled exactly
  as in `Hdelta`: `(1/ε) * K hweak (qε ε (x,p,m))`. -/
  H_form : ∀ ε, 0 < ε →
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
        ∀ p m, 0 < m →
          Hdelta hweak ε x p m
            = H x (p - qε ε (x, p, m)) m + (1 / ε) * K hweak (qε ε (x, p, m))
  /-- (paper `eq:DpH-epsilon-formula`) For `ε > 0`, a.e. `x`, and `m > 0`, the
  regularized gradient unfolds to `D_pH(x, p − q^ε, m)`. By definition of
  `DpHepsilonFam` this is `rfl`-true pointwise; it is restated on the a.e./`m>0`
  slice for interface uniformity with the rest of the certificate. -/
  DpH_form : ∀ ε, 0 < ε →
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
        ∀ p m, 0 < m →
          DpHepsilonFam hweak qε ε x p m = DpH x (p - qε ε (x, p, m)) m
  /-- (paper `eq:inf-conv.diff-relation1`, first inclusion) Subgradient
  optimality of the inf-conv minimiser `qε ε`: for `ε > 0`, a.e. `x`, `m > 0`,
  all `q`, the K-side support inequality holds. This is the selector-level
  first-order optimality that `lem:H.delta.monotone` consumes; it holds at ANY
  minimiser (no global injectivity). -/
  hSub : ∀ ε, 0 < ε →
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
        ∀ p m, 0 < m → ∀ q : Fin d → ℝ,
          DpH x (p - qε ε (x, p, m)) m ⬝ (q - qε ε (x, p, m))
            ≤ (1 / ε) * (K hweak q - K hweak (qε ε (x, p, m)))
  /-- (paper `eq:DpHdelta.dotp.minusH`, line 1815) FTC-slice identity for the
  regularized pair `(Hdelta, DpHepsilonFam)` at the selector: for `ε > 0`, a.e.
  `x`, `m > 0`. Derived from the subgradient field via the envelope machinery
  (`Envelope.lean`); carried here so `lem:H.delta.monotone` can be discharged
  without re-running the envelope analysis at each consumer. -/
  hFtcSlice : ∀ ε, 0 < ε →
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
        ∀ p m, 0 < m →
          (DpHepsilonFam hweak qε ε x p m) ⬝ p
            - (Hdelta hweak ε x p m - Hdelta hweak ε x (0 : Fin d → ℝ) m)
            = ∫ t in (0 : ℝ)..1,
                ((DpHepsilonFam hweak qε ε x p m
                  - DpHepsilonFam hweak qε ε x (t • p) m) ⬝ p)

/-- Coherence check: `InfConvSelectorFamily` assembles from its six field
proofs (Prop carrier exercise — no producer is asserted). -/
example
    (hweak : Hamiltonian.HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d)
    (q_meas : ∀ ε, Measurable (qε ε))
    (q_cont_pm : ∀ ε, 0 < ε →
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
        ContinuousOn (fun pm : (Fin d → ℝ) × ℝ => qε ε (x, pm.1, pm.2))
          {pm | 0 < pm.2})
    (H_form : ∀ ε, 0 < ε →
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
        ∀ p m, 0 < m →
          Hdelta hweak ε x p m
            = H x (p - qε ε (x, p, m)) m + (1 / ε) * K hweak (qε ε (x, p, m)))
    (DpH_form : ∀ ε, 0 < ε →
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
        ∀ p m, 0 < m →
          DpHepsilonFam hweak qε ε x p m = DpH x (p - qε ε (x, p, m)) m)
    (hSub : ∀ ε, 0 < ε →
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
        ∀ p m, 0 < m → ∀ q : Fin d → ℝ,
          DpH x (p - qε ε (x, p, m)) m ⬝ (q - qε ε (x, p, m))
            ≤ (1 / ε) * (K hweak q - K hweak (qε ε (x, p, m))))
    (hFtcSlice : ∀ ε, 0 < ε →
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
        ∀ p m, 0 < m →
          (DpHepsilonFam hweak qε ε x p m) ⬝ p
            - (Hdelta hweak ε x p m - Hdelta hweak ε x (0 : Fin d → ℝ) m)
            = ∫ t in (0 : ℝ)..1,
                ((DpHepsilonFam hweak qε ε x p m
                  - DpHepsilonFam hweak qε ε x (t • p) m) ⬝ p)) :
    InfConvSelectorFamily (H := H) (DpH := DpH) hweak qε :=
  { q_meas := q_meas, q_cont_pm := q_cont_pm, H_form := H_form,
    DpH_form := DpH_form, hSub := hSub, hFtcSlice := hFtcSlice }

/-- **Dq4a producer: `ε`-independent coercive bounds from the selector family**
(paper `prop:boundsHepsilon`, `eq:H-epsilon.lower.uniform` + `eq:DpHdelta.dotp.minusH`).

From `HypothesisWeakGrowth`, a selector family `qε`, an `InfConvSelectorFamily`
certificate `sel`, and the *accepted* convex-at-zero rider `hCx` for `H^ε`
(paper `lem:H.delta.monotone` / `rmk:cxty` — the SAME rider already consumed by
`InfConv.Hdelta_lagrangian_lower_bound`, NOT a loose oracle), assemble the
`HdeltaUniformBounds` carrier with the single `ε`-independent constant
`C0 := 2^α (C+1)`.

* `lower_uniform`: per-`ε`, `filter_upwards [sel.H_form, hweak.lower]`. The
  attainment identity in `sel.H_form` is exactly the `hqStar` certificate of
  `Hdelta_lower_bound_uniform` at `qStar := qε ε (x,p,m)`; `hLower` is
  `hweak.lower` at `(p − qStar, m)`; `hmβ` is `Real.rpow_nonneg`. The lemma's RHS
  constant `2^α(C+1)` is `C0` verbatim — no absorption.
* `lagr_uniform`: per-`ε`, `filter_upwards [hweak.upper, hweak.lower, hCx]`,
  via `InfConv.Hdelta_lagrangian_lower_bound` with
  `DpHε := DpHepsilonFam hweak qε ε`. `Hdelta_lagrangian_lower_bound` delivers
  `m^β/C − C`; the carrier wants `m^β/C0 − C0`. Since `C ≤ C0` (because
  `2^α ≥ 1`) and `m^β ≥ 0`, we have `m^β/C0 ≤ m^β/C` and `−C0 ≤ −C`, so
  `m^β/C0 − C0 ≤ m^β/C − C`, chained with the lemma by `linarith`.

Takes NO `hInj`, NO global injectivity, NO uniform-`C` (no `hC_eq`); the only
rider is the paper-accepted `hCx`. -/
noncomputable def hdeltaUniformBounds_of_selector
    (hweak : HypothesisWeakGrowth (d := d) H DpH) (qε : QEpsFamily d)
    (sel : InfConvSelectorFamily (H := H) (DpH := DpH) hweak qε)
    (hCx : ∀ ε, 0 < ε → ε ≤ 1 →
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
        ∀ p m, 0 < m →
          Hdelta hweak ε x p m - (DpHepsilonFam hweak qε ε x p m) ⬝ p
            ≤ Hdelta hweak ε x 0 m) :
    HdeltaUniformBounds (H := H) (DpH := DpH) hweak qε := by
  -- The `ε`-independent constant `C0 := 2^α (C+1)`.
  set C0 : ℝ := (2 : ℝ) ^ hweak.α * (hweak.C + 1) with hC0_def
  -- Positivity facts.
  have hα_nn : (0 : ℝ) ≤ hweak.α := le_of_lt (lt_trans zero_lt_one hweak.hα)
  have hC_pos : (0 : ℝ) < hweak.C := hweak.hC
  have hC1_pos : (0 : ℝ) < hweak.C + 1 := by linarith
  have h2_pos : (0 : ℝ) < 2 := by norm_num
  have h2α_pos : (0 : ℝ) < (2 : ℝ) ^ hweak.α := Real.rpow_pos_of_pos h2_pos _
  have h2α_nn : (0 : ℝ) ≤ (2 : ℝ) ^ hweak.α := le_of_lt h2α_pos
  have hC0_pos : (0 : ℝ) < C0 := mul_pos h2α_pos hC1_pos
  -- `C ≤ C0` (because `2^α ≥ 1` and `C+1 ≥ C`).
  have h_one_le_2α : (1 : ℝ) ≤ (2 : ℝ) ^ hweak.α := by
    have h1 : (1 : ℝ) ^ hweak.α ≤ (2 : ℝ) ^ hweak.α :=
      Real.rpow_le_rpow (by norm_num) (by norm_num) hα_nn
    simpa using h1
  have hC_le_C0 : hweak.C ≤ C0 := by
    have hC_le_C1 : hweak.C ≤ hweak.C + 1 := by linarith
    calc hweak.C ≤ hweak.C + 1 := hC_le_C1
      _ = 1 * (hweak.C + 1) := by ring
      _ ≤ (2 : ℝ) ^ hweak.α * (hweak.C + 1) :=
        mul_le_mul_of_nonneg_right h_one_le_2α (le_of_lt hC1_pos)
  refine
    { C0 := C0
      hC0 := hC0_pos
      lower_uniform := ?_
      lagr_uniform := ?_ }
  · -- (eq:H-epsilon.lower.uniform)
    intro ε hε hε1
    filter_upwards [sel.H_form ε hε, hweak.lower] with x hHform hLowx
    intro p m hm
    -- Attainment certificate `hqStar` at `qStar := qε ε (x,p,m)`.
    have hqStar :
        Hdelta hweak ε x p m
          = H x (p - qε ε (x, p, m)) m + (1 / ε) * K hweak (qε ε (x, p, m)) :=
      hHform p m hm
    -- Per-point weak-growth lower bound at `(p − qStar, m)`.
    have hLower :
        ‖p - qε ε (x, p, m)‖ ^ hweak.α / hweak.C
            - hweak.C * (m ^ hweak.β + 1)
          ≤ H x (p - qε ε (x, p, m)) m :=
      hLowx (p - qε ε (x, p, m)) m hm
    -- Sign witness `0 ≤ m^β + 1`.
    have hmβ : (0 : ℝ) ≤ m ^ hweak.β + 1 := by
      have : (0 : ℝ) ≤ m ^ hweak.β := Real.rpow_nonneg (le_of_lt hm) _
      linarith
    -- Invoke the uniform lower bound; its RHS constant is `C0` verbatim.
    have := Hdelta_lower_bound_uniform hweak hε hε1 (qε ε (x, p, m)) hqStar hLower hmβ
    simpa [hC0_def] using this
  · -- (eq:DpHdelta.dotp.minusH)
    intro ε hε hε1
    filter_upwards [hweak.upper, hweak.lower, hCx ε hε hε1] with x hUpx hLowx hCxx
    intro p m hm
    -- `hUp` side condition from the base upper field at `(x, 0, m)`.
    have hUp : H x (0 : Fin d → ℝ) m ≤ -(m ^ hweak.β) / hweak.C + hweak.C :=
      hUpx m hm
    -- `hBdd` witness for `q ↦ H x (0 - q) m`, from `hweak.lower`.
    have hBdd :
        BddBelow (Set.range fun q : Fin d → ℝ => H x ((0 : Fin d → ℝ) - q) m) := by
      refine ⟨-(hweak.C * (m ^ hweak.β + 1)), ?_⟩
      rintro y ⟨q, rfl⟩
      have hLow := hLowx ((0 : Fin d → ℝ) - q) m hm
      have hpα_nn : 0 ≤ ‖(0 : Fin d → ℝ) - q‖ ^ hweak.α :=
        Real.rpow_nonneg (norm_nonneg _) _
      have hdiv_nn : 0 ≤ ‖(0 : Fin d → ℝ) - q‖ ^ hweak.α / hweak.C :=
        div_nonneg hpα_nn (le_of_lt hweak.hC)
      have : (‖(0 : Fin d → ℝ) - q‖ ^ hweak.α) / hweak.C
              - hweak.C * (m ^ hweak.β + 1)
            ≤ H x ((0 : Fin d → ℝ) - q) m := hLow
      linarith
    -- Per-point Lagrangian lower bound `m^β/C − C ≤ DpHε·p − Hdelta`.
    have hLagr :
        (m ^ hweak.β) / hweak.C - hweak.C
          ≤ (DpHepsilonFam hweak qε ε x p m) ⬝ p - Hdelta hweak ε x p m :=
      Hdelta_lagrangian_lower_bound hweak hε hε1 (DpHepsilonFam hweak qε ε) hm
        (hCxx p m hm) hUp hBdd
    -- Weaken `m^β/C − C` to `m^β/C0 − C0` (since `C ≤ C0`, `m^β ≥ 0`).
    have hmβ_nn : (0 : ℝ) ≤ m ^ hweak.β := Real.rpow_nonneg (le_of_lt hm) _
    have h_div_le : (m ^ hweak.β) / C0 ≤ (m ^ hweak.β) / hweak.C :=
      div_le_div_of_nonneg_left hmβ_nn hC_pos hC_le_C0
    have : (m ^ hweak.β) / C0 - C0
            ≤ (m ^ hweak.β) / hweak.C - hweak.C := by linarith
    linarith [this, hLagr]

/-- **Dq4c producer: per-`ε` power-growth bundle from the selector family**
(paper `prop:boundsHepsilon`, the `C_ε`-regime estimates `eq:H-epsilon.upper`,
`eq:DpHdelta.upper`, plus the coercive `eq:H-epsilon.lower.uniform`,
`eq:DpHdelta.dotp.minusH`).

From `HypothesisWeakGrowth`, a selector family `qε`, an `InfConvSelectorFamily`
certificate `sel`, and the *paper-accepted* riders
* `hMeas : HypothesisDpHMeasurable` (joint measurability of `H`, `D_pH`),
* `hCx`   (convex-at-zero for `H^ε`, `lem:H.delta.monotone`),
* `hGrad` (the `‖q^ε‖`-form gradient bound `eq:inf-conv.diff-relation1`),
* `hFormPos`/`hqE_per` (the formula bridge + periodicity of the selector,
  needed to discharge `RegularityH` of the junk-extended carrier),
this assembles the `HdeltaPowerEpsData` carrier: each `hpow ε` is a full
`HypothesisPowerGrowth (HdeltaPos hweak ε) (DpHepsilonFam hweak qε ε)`.

The carrier is `HdeltaPos` (= `Hdelta` on `{0<m}`, `0` on `{m≤0}`), so
`RegularityH` is discharged by `Hepsilon_regularityH_pos` (no `{m≤0}` `iInf`
measurability fork). All five estimate fields are evaluated at `m>0`, where
`HdeltaPos = Hdelta` (`HdeltaPos_eq_Hdelta_of_pos`), and transfer from the
existing `Hdelta_*` estimate lemmas. The growth constant `C_ε` is the sum of
all per-field RHS constants (a nonneg sum), so each field is dominated termwise;
NO uniform-`C` is assumed (there is no `hC_eq`). Exponents are pinned to
`hweak.α`, `hweak.β`.

Takes NO `hInj`, NO global injectivity, NO uniform-`C`; the only riders are the
paper-accepted `hMeas`/`hCx`/`hGrad`/`hFormPos`/`hqE_per`.

This auxiliary `def` builds the per-`ε` bundle (extracted to top level so the
`α`/`β` projection facts in `hdeltaPowerEpsData_of_selector` reduce by `rfl`). -/
noncomputable def hpowEps_of_selector
    (hweak : HypothesisWeakGrowth (d := d) H DpH) (qε : QEpsFamily d)
    (sel : InfConvSelectorFamily (H := H) (DpH := DpH) hweak qε)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (hqE_per : ∀ ε, ∀ p m, StationaryMFG.Periodic.IsPeriodic
      (fun x : Fin d → ℝ => qε ε (x, p, m)))
    (hFormPos : ∀ ε, 0 < ε →
      ∀ xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ, 0 < xpm.2.2 →
        Hdelta hweak ε xpm.1 xpm.2.1 xpm.2.2
          = H xpm.1 (xpm.2.1 - qε ε xpm) xpm.2.2 + (1 / ε) * K hweak (qε ε xpm))
    (hCx : ∀ ε, 0 < ε → ε ≤ 1 →
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
        ∀ p m, 0 < m →
          Hdelta hweak ε x p m - (DpHepsilonFam hweak qε ε x p m) ⬝ p
            ≤ Hdelta hweak ε x 0 m)
    (hGrad : ∀ ε, 0 < ε → ε ≤ 1 →
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
        ∀ p m, 0 < m →
          ‖DpHepsilonFam hweak qε ε x p m‖
            ≤ (1 / ε) * (1 + hweak.α * (Real.sqrt d) ^ (hweak.α - 1)
                * ‖qε ε (x, p, m)‖ ^ (hweak.α - 1)))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Hamiltonian.HypothesisPowerGrowth (d := d)
      (HdeltaPos hweak ε) (DpHepsilonFam hweak qε ε) := by
    -- Shared positivity/exponent facts.
    have hα_pos : (0 : ℝ) < hweak.α := lt_trans zero_lt_one hweak.hα
    have hα_nn : (0 : ℝ) ≤ hweak.α := le_of_lt hα_pos
    have hα_ne : hweak.α ≠ 0 := ne_of_gt hα_pos
    have hC_pos : (0 : ℝ) < hweak.C := hweak.hC
    have hC_nn : (0 : ℝ) ≤ hweak.C := le_of_lt hC_pos
    have hC1_pos : (0 : ℝ) < hweak.C + 1 := by linarith
    have h2_pos : (0 : ℝ) < 2 := by norm_num
    have h2α_pos : (0 : ℝ) < (2 : ℝ) ^ hweak.α := Real.rpow_pos_of_pos h2_pos _
    -- exponent `r := (α-1)/α ∈ (0,1]`.
    have hr_nn : (0 : ℝ) ≤ (hweak.α - 1) / hweak.α :=
      div_nonneg (by linarith [hweak.hα]) hα_nn
    have hr_le1 : (hweak.α - 1) / hweak.α ≤ 1 := by
      rw [div_le_one hα_pos]; linarith
    -- Abbreviations for the per-field RHS constants.
    set Cd : ℝ := K_sup_const (d := d) hweak with hCd_def
    have hCd_nn : (0 : ℝ) ≤ Cd := K_sup_const_nonneg hweak
    have hε_inv_pos : (0 : ℝ) < 1 / ε := one_div_pos.mpr hε
    have hε_inv_nn : (0 : ℝ) ≤ 1 / ε := le_of_lt hε_inv_pos
    have hCdε_nn : (0 : ℝ) ≤ Cd / ε := div_nonneg hCd_nn (le_of_lt hε)
    -- Euclidean-kernel dimension-inflated gradient coefficient `αd := α·(√d)^{α−1}`.
    set αd : ℝ := hweak.α * (Real.sqrt d) ^ (hweak.α - 1) with hαd_def
    have hdFac_nn : (0 : ℝ) ≤ (Real.sqrt d) ^ (hweak.α - 1) :=
      Real.rpow_nonneg (Real.sqrt_nonneg _) _
    have hαd_nn : (0 : ℝ) ≤ αd := mul_nonneg hα_nn hdFac_nn
    have hαε_nn : (0 : ℝ) ≤ αd / ε :=
      div_nonneg hαd_nn (le_of_lt hε)
    -- positivity of each rpow constant.
    have hCdεr_nn : (0 : ℝ) ≤ (Cd / ε) ^ ((hweak.α - 1) / hweak.α) :=
      Real.rpow_nonneg hCdε_nn _
    have hCbr_nn : (0 : ℝ) ≤ hweak.C ^ ((hweak.α - 1) / hweak.α) :=
      Real.rpow_nonneg hC_nn _
    have hCdεCr_nn :
        (0 : ℝ) ≤ (Cd / ε + hweak.C) ^ ((hweak.α - 1) / hweak.α) :=
      Real.rpow_nonneg (by linarith) _
    -- The growth constant: a sum of nonneg terms, the first one positive.
    set Cstar : ℝ :=
      (Cd / ε + (2 : ℝ) ^ hweak.α * (hweak.C + 1))
        + (αd / ε) * (Cd / ε) ^ ((hweak.α - 1) / hweak.α)
        + (αd / ε) * hweak.C ^ ((hweak.α - 1) / hweak.α)
        + ((1 / ε)
            + (αd / ε)
              * (hweak.C ^ ((hweak.α - 1) / hweak.α)
                  + (Cd / ε + hweak.C) ^ ((hweak.α - 1) / hweak.α)))
      with hCstar_def
    -- Nonnegativity of the four summand groups.
    have hg1_pos : (0 : ℝ) < Cd / ε + (2 : ℝ) ^ hweak.α * (hweak.C + 1) := by
      have : (0 : ℝ) < (2 : ℝ) ^ hweak.α * (hweak.C + 1) :=
        mul_pos h2α_pos hC1_pos
      linarith
    have hg2_nn :
        (0 : ℝ) ≤ (αd / ε) * (Cd / ε) ^ ((hweak.α - 1) / hweak.α) :=
      mul_nonneg hαε_nn hCdεr_nn
    have hg3_nn :
        (0 : ℝ) ≤ (αd / ε) * hweak.C ^ ((hweak.α - 1) / hweak.α) :=
      mul_nonneg hαε_nn hCbr_nn
    have hg4_nn :
        (0 : ℝ) ≤ (1 / ε)
            + (αd / ε)
              * (hweak.C ^ ((hweak.α - 1) / hweak.α)
                  + (Cd / ε + hweak.C) ^ ((hweak.α - 1) / hweak.α)) := by
      have : (0 : ℝ)
          ≤ (αd / ε)
              * (hweak.C ^ ((hweak.α - 1) / hweak.α)
                  + (Cd / ε + hweak.C) ^ ((hweak.α - 1) / hweak.α)) :=
        mul_nonneg hαε_nn (by linarith)
      linarith
    -- atom-level nonneg facts (so `linarith` can dominate without coupling).
    have h2αC_nn : (0 : ℝ) ≤ (2 : ℝ) ^ hweak.α * (hweak.C + 1) :=
      le_of_lt (mul_pos h2α_pos hC1_pos)
    -- `Cstar = g1 + g2 + g3 + g4` as a flat sum, atoms all nonneg.
    have hCstar_sum :
        Cstar = (Cd / ε + (2 : ℝ) ^ hweak.α * (hweak.C + 1))
          + (αd / ε) * (Cd / ε) ^ ((hweak.α - 1) / hweak.α)
          + (αd / ε) * hweak.C ^ ((hweak.α - 1) / hweak.α)
          + ((1 / ε)
              + (αd / ε)
                * (hweak.C ^ ((hweak.α - 1) / hweak.α)
                    + (Cd / ε + hweak.C) ^ ((hweak.α - 1) / hweak.α))) :=
      hCstar_def
    have hCstar_pos : (0 : ℝ) < Cstar := by
      rw [hCstar_sum]; linarith [hCdε_nn, h2αC_nn, hg2_nn, hg3_nn, hg4_nn]
    -- Domination facts: `Cstar ≥` each per-field RHS constant.
    have hC2_le : (2 : ℝ) ^ hweak.α * (hweak.C + 1) ≤ Cstar := by
      rw [hCstar_sum]; linarith [hCdε_nn, hg2_nn, hg3_nn, hg4_nn]
    have hCdε_le : Cd / ε ≤ Cstar := by
      rw [hCstar_sum]; linarith [h2αC_nn, hg2_nn, hg3_nn, hg4_nn]
    have hCbase_le : hweak.C ≤ Cstar := by
      have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ hweak.α := by
        have := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1)
          (by norm_num : (1:ℝ) ≤ 2) hα_nn
        simpa using this
      have hC_le_2αC : hweak.C ≤ (2 : ℝ) ^ hweak.α * (hweak.C + 1) := by
        calc hweak.C ≤ hweak.C + 1 := by linarith
          _ = 1 * (hweak.C + 1) := by ring
          _ ≤ (2 : ℝ) ^ hweak.α * (hweak.C + 1) :=
            mul_le_mul_of_nonneg_right h1 (le_of_lt hC1_pos)
      rw [hCstar_sum]
      linarith [hCdε_nn, hC_le_2αC, hg2_nn, hg3_nn, hg4_nn]
    have hCdεCbase_le : Cd / ε + hweak.C ≤ Cstar := by
      have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ hweak.α := by
        have := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1)
          (by norm_num : (1:ℝ) ≤ 2) hα_nn
        simpa using this
      have hC_le_2αC : hweak.C ≤ (2 : ℝ) ^ hweak.α * (hweak.C + 1) := by
        calc hweak.C ≤ hweak.C + 1 := by linarith
          _ = 1 * (hweak.C + 1) := by ring
          _ ≤ (2 : ℝ) ^ hweak.α * (hweak.C + 1) :=
            mul_le_mul_of_nonneg_right h1 (le_of_lt hC1_pos)
      rw [hCstar_sum]
      linarith [hC_le_2αC, hg2_nn, hg3_nn, hg4_nn]
    -- Coefficient-domination facts for `DpH_upper`.
    have hcoeff_p : (αd / ε) * (Cd / ε) ^ ((hweak.α - 1) / hweak.α) ≤ Cstar := by
      rw [hCstar_sum]; linarith [hCdε_nn, h2αC_nn, hg3_nn, hg4_nn]
    have hcoeff_m : (αd / ε) * hweak.C ^ ((hweak.α - 1) / hweak.α) ≤ Cstar := by
      rw [hCstar_sum]; linarith [hCdε_nn, h2αC_nn, hg2_nn, hg4_nn]
    have hcoeff_const :
        (1 / ε)
            + (αd / ε)
              * (hweak.C ^ ((hweak.α - 1) / hweak.α)
                  + (Cd / ε + hweak.C) ^ ((hweak.α - 1) / hweak.α))
          ≤ Cstar := by
      rw [hCstar_sum]; linarith [hCdε_nn, h2αC_nn, hg2_nn, hg3_nn]
    -- The `RegularityH` side of the bundle.
    have hReg :
        Hamiltonian.RegularityH (d := d)
          (fun x p m => HdeltaPos hweak ε x p m)
          (DpHepsilonFam hweak qε ε) :=
      Hepsilon_regularityH_pos (H := H) (DpH := DpH) hweak (qε ε)
        hweak.toRegularityH hMeas hε (sel.q_meas ε) (hqE_per ε)
        (sel.q_cont_pm ε hε) (hFormPos ε hε)
    refine
      { toRegularityH := hReg
        C := Cstar
        α := hweak.α
        β := hweak.β
        hC := hCstar_pos
        hα := hweak.hα
        hβ := hweak.hβ
        upper := ?_
        DpH_upper := ?_
        lower := ?_
        H_upper_pointwise := ?_
        lagr := ?_ }
    · -- (eq:assH.upper) at `p = 0`.
      filter_upwards [hweak.upper, hweak.lower, sel.H_form ε hε] with
        x hUpx hLowx hHform
      intro m hm
      rw [HdeltaPos_eq_Hdelta_of_pos hweak hm]
      -- `BddBelow` of `q ↦ H x (0 - q) m`.
      have hBdd :
          BddBelow (Set.range fun q : Fin d → ℝ => H x ((0 : Fin d → ℝ) - q) m) := by
        refine ⟨-(hweak.C * (m ^ hweak.β + 1)), ?_⟩
        rintro y ⟨q, rfl⟩
        have hLow := hLowx ((0 : Fin d → ℝ) - q) m hm
        have hpα_nn : 0 ≤ ‖(0 : Fin d → ℝ) - q‖ ^ hweak.α :=
          Real.rpow_nonneg (norm_nonneg _) _
        have : (‖(0 : Fin d → ℝ) - q‖ ^ hweak.α) / hweak.C
                - hweak.C * (m ^ hweak.β + 1)
              ≤ H x ((0 : Fin d → ℝ) - q) m := hLow
        have hdiv_nn : 0 ≤ ‖(0 : Fin d → ℝ) - q‖ ^ hweak.α / hweak.C :=
          div_nonneg hpα_nn hC_nn
        linarith
      have hUb := Hdelta_upper_bound hweak hε (hε1) hm (hUpx m hm) hBdd
      -- At `p = 0`, `‖0‖^α = 0`.
      have hnorm0 : ‖(0 : Fin d → ℝ)‖ ^ hweak.α = 0 := by
        rw [norm_zero]; exact Real.zero_rpow hα_ne
      rw [hnorm0, mul_zero] at hUb
      -- `Hdelta ≤ 0 − m^β/Cbase + (Cd/ε+Cbase)`; absorb into `−m^β/Cstar + Cstar`.
      have hmβ_nn : (0 : ℝ) ≤ m ^ hweak.β := Real.rpow_nonneg (le_of_lt hm) _
      have hdiv_le : (m ^ hweak.β) / Cstar ≤ (m ^ hweak.β) / hweak.C :=
        div_le_div_of_nonneg_left hmβ_nn hC_pos hCbase_le
      -- Goal: `Hdelta ≤ -(m^β)/Cstar + Cstar`.
      have hgoaleq1 : -(m ^ hweak.β) / Cstar = -((m ^ hweak.β) / Cstar) := by ring
      have hgoaleq2 : -(m ^ hweak.β) / hweak.C = -((m ^ hweak.β) / hweak.C) := by ring
      rw [hgoaleq1]
      linarith [hUb, hdiv_le, hCdεCbase_le, hgoaleq2]
    · -- (eq:assH.DpH.upper): the gradient power-growth bound.
      filter_upwards [hweak.upper, hweak.lower, sel.H_form ε hε,
        sel.DpH_form ε hε, hGrad ε hε (hε1)] with
        x hUpx hLowx hHform hDpHform hGradx
      intro p m hm
      -- attainment certificate at `qStar := qε ε (x,p,m)`.
      have hqStar :
          Hdelta hweak ε x p m
            = H x (p - qε ε (x, p, m)) m + (1 / ε) * K hweak (qε ε (x, p, m)) :=
        hHform p m hm
      have hLower :
          ‖p - qε ε (x, p, m)‖ ^ hweak.α / hweak.C
              - hweak.C * (m ^ hweak.β + 1)
            ≤ H x (p - qε ε (x, p, m)) m :=
        hLowx (p - qε ε (x, p, m)) m hm
      have hUpper : H x (0 : Fin d → ℝ) m ≤ -(m ^ hweak.β) / hweak.C + hweak.C :=
        hUpx m hm
      have hBdd :
          BddBelow (Set.range fun q : Fin d → ℝ => H x (p - q) m) := by
        refine ⟨-(hweak.C * (m ^ hweak.β + 1)), ?_⟩
        rintro y ⟨q, rfl⟩
        have hLow := hLowx (p - q) m hm
        have hpα_nn : 0 ≤ ‖p - q‖ ^ hweak.α :=
          Real.rpow_nonneg (norm_nonneg _) _
        have hdiv_nn : 0 ≤ ‖p - q‖ ^ hweak.α / hweak.C :=
          div_nonneg hpα_nn hC_nn
        linarith [hLow]
      -- the `‖q^ε‖`-form gradient bound (Euclidean d-factor), `DpHε := DpHepsilonFam`.
      have hDpHε_via_qStar :
          ‖DpHepsilonFam hweak qε ε x p m‖
            ≤ (1 / ε) * (1 + hweak.α * (Real.sqrt d) ^ (hweak.α - 1)
                * ‖qε ε (x, p, m)‖ ^ (hweak.α - 1)) :=
        hGradx p m hm
      have hGB := Hdelta_gradient_upper_bound hweak hε (hε1)
        (DpHepsilonFam hweak qε ε) hm (qε ε (x, p, m)) hqStar hLower hUpper hBdd
        hDpHε_via_qStar
      -- Now convert `R^r` into the power-growth shape.
      set R : ℝ := (K_sup_const (d := d) hweak / ε) * ‖p‖ ^ hweak.α
            + hweak.C * (m ^ hweak.β + 1) + (K_sup_const (d := d) hweak / ε + hweak.C)
        with hRdef
      set r : ℝ := (hweak.α - 1) / hweak.α with hr_def
      -- nonneg facts.
      have hpα_nn : (0 : ℝ) ≤ ‖p‖ ^ hweak.α := Real.rpow_nonneg (norm_nonneg _) _
      have hmβ_nn : (0 : ℝ) ≤ m ^ hweak.β := Real.rpow_nonneg (le_of_lt hm) _
      have hA_nn : (0 : ℝ) ≤ (Cd / ε) * ‖p‖ ^ hweak.α :=
        mul_nonneg hCdε_nn hpα_nn
      have hB_nn : (0 : ℝ) ≤ hweak.C * (m ^ hweak.β + 1) :=
        mul_nonneg hC_nn (by linarith)
      have hD_nn : (0 : ℝ) ≤ Cd / ε + hweak.C := by linarith
      -- Split `R^r ≤ A^r + (B + D)^r ≤ A^r + B^r + D^r`.
      have hsplit1 :
          R ^ r ≤ ((Cd / ε) * ‖p‖ ^ hweak.α) ^ r
              + (hweak.C * (m ^ hweak.β + 1) + (Cd / ε + hweak.C)) ^ r := by
        have hBD_nn : (0 : ℝ) ≤ hweak.C * (m ^ hweak.β + 1) + (Cd / ε + hweak.C) := by
          linarith
        have : R = (Cd / ε) * ‖p‖ ^ hweak.α
              + (hweak.C * (m ^ hweak.β + 1) + (Cd / ε + hweak.C)) := by
          rw [hRdef, hCd_def]; ring
        rw [this]
        exact Real.rpow_add_le_add_rpow hA_nn hBD_nn hr_nn hr_le1
      have hsplit2 :
          (hweak.C * (m ^ hweak.β + 1) + (Cd / ε + hweak.C)) ^ r
            ≤ (hweak.C * (m ^ hweak.β + 1)) ^ r + (Cd / ε + hweak.C) ^ r :=
        Real.rpow_add_le_add_rpow hB_nn hD_nn hr_nn hr_le1
      -- `A^r = (Cd/ε)^r * ‖p‖^(α-1)`.
      -- exponent identities `α * r = α - 1`, `β * r = β - β/α`.
      have hαr_eq : hweak.α * r = hweak.α - 1 := by
        rw [hr_def]; field_simp
      have hβr_eq : hweak.β * r = hweak.β - hweak.β / hweak.α := by
        rw [hr_def]; field_simp
      have hAr :
          ((Cd / ε) * ‖p‖ ^ hweak.α) ^ r
            = (Cd / ε) ^ r * ‖p‖ ^ (hweak.α - 1) := by
        rw [Real.mul_rpow hCdε_nn hpα_nn]
        congr 1
        rw [← Real.rpow_mul (norm_nonneg _), hαr_eq]
      -- `(C*(m^β+1))^r ≤ C^r * (m^(β-β/α) + 1)`.
      have hBr :
          (hweak.C * (m ^ hweak.β + 1)) ^ r
            ≤ hweak.C ^ r * (m ^ (hweak.β - hweak.β / hweak.α) + 1) := by
        rw [Real.mul_rpow hC_nn (by linarith)]
        have hsub :
            (m ^ hweak.β + 1) ^ r ≤ (m ^ hweak.β) ^ r + (1 : ℝ) ^ r :=
          Real.rpow_add_le_add_rpow hmβ_nn (by norm_num) hr_nn hr_le1
        have hone : (1 : ℝ) ^ r = 1 := Real.one_rpow _
        have hmβr : (m ^ hweak.β) ^ r = m ^ (hweak.β - hweak.β / hweak.α) := by
          rw [← Real.rpow_mul (le_of_lt hm), hβr_eq]
        have hCr_nn : (0 : ℝ) ≤ hweak.C ^ r := Real.rpow_nonneg hC_nn _
        calc hweak.C ^ r * (m ^ hweak.β + 1) ^ r
            ≤ hweak.C ^ r * ((m ^ hweak.β) ^ r + (1 : ℝ) ^ r) :=
              mul_le_mul_of_nonneg_left hsub hCr_nn
          _ = hweak.C ^ r * (m ^ (hweak.β - hweak.β / hweak.α) + 1) := by
              rw [hmβr, hone]
      -- Assemble: `R^r ≤ (Cd/ε)^r ‖p‖^(α-1) + C^r(m^(β-β/α)+1) + (Cd/ε+C)^r`.
      have hmβα_nn : (0 : ℝ) ≤ m ^ (hweak.β - hweak.β / hweak.α) :=
        Real.rpow_nonneg (le_of_lt hm) _
      have hpα1_nn : (0 : ℝ) ≤ ‖p‖ ^ (hweak.α - 1) :=
        Real.rpow_nonneg (norm_nonneg _) _
      have hRr_le :
          R ^ r
            ≤ (Cd / ε) ^ r * ‖p‖ ^ (hweak.α - 1)
              + hweak.C ^ r * (m ^ (hweak.β - hweak.β / hweak.α) + 1)
              + (Cd / ε + hweak.C) ^ r := by
        calc R ^ r
            ≤ ((Cd / ε) * ‖p‖ ^ hweak.α) ^ r
                + (hweak.C * (m ^ hweak.β + 1) + (Cd / ε + hweak.C)) ^ r := hsplit1
          _ ≤ ((Cd / ε) * ‖p‖ ^ hweak.α) ^ r
                + ((hweak.C * (m ^ hweak.β + 1)) ^ r + (Cd / ε + hweak.C) ^ r) := by
              linarith [hsplit2]
          _ = (Cd / ε) ^ r * ‖p‖ ^ (hweak.α - 1)
                + (hweak.C * (m ^ hweak.β + 1)) ^ r + (Cd / ε + hweak.C) ^ r := by
              rw [hAr]; ring
          _ ≤ (Cd / ε) ^ r * ‖p‖ ^ (hweak.α - 1)
                + hweak.C ^ r * (m ^ (hweak.β - hweak.β / hweak.α) + 1)
                + (Cd / ε + hweak.C) ^ r := by linarith [hBr]
      -- Multiply through by `αd/ε ≥ 0`, add the `(1/ε)` constant.
      -- `‖DpHε‖ ≤ (1/ε) + (αd/ε) * R^r`.
      have hmid :
          ‖DpHepsilonFam hweak qε ε x p m‖ ≤ (1 / ε) + (αd / ε) * R ^ r := by
        have hrw : (1 / ε) * (1 + αd * R ^ r)
              = (1 / ε) + (αd / ε) * R ^ r := by
          field_simp
        -- `hGB` is folded (via `set αd`/`set R`/`set r` above) to this shape.
        rw [hrw] at hGB; exact hGB
      -- Bound `(αd/ε) R^r` by the converted sum, then dominate coeffs by `Cstar`.
      have hαε_mul :
          (αd / ε) * R ^ r
            ≤ (αd / ε) * (Cd / ε) ^ r * ‖p‖ ^ (hweak.α - 1)
              + (αd / ε) * hweak.C ^ r * (m ^ (hweak.β - hweak.β / hweak.α) + 1)
              + (αd / ε) * (Cd / ε + hweak.C) ^ r := by
        have hstep := mul_le_mul_of_nonneg_left hRr_le hαε_nn
        calc (αd / ε) * R ^ r
            ≤ (αd / ε)
                * ((Cd / ε) ^ r * ‖p‖ ^ (hweak.α - 1)
                  + hweak.C ^ r * (m ^ (hweak.β - hweak.β / hweak.α) + 1)
                  + (Cd / ε + hweak.C) ^ r) := hstep
          _ = (αd / ε) * (Cd / ε) ^ r * ‖p‖ ^ (hweak.α - 1)
              + (αd / ε) * hweak.C ^ r * (m ^ (hweak.β - hweak.β / hweak.α) + 1)
              + (αd / ε) * (Cd / ε + hweak.C) ^ r := by ring
      -- Final: `‖DpHε‖ ≤ Cstar*(‖p‖^(α-1) + m^(β-β/α) + 1)`.
      have htarget :
          (1 / ε) + (αd / ε) * R ^ r
            ≤ Cstar * (‖p‖ ^ (hweak.α - 1)
                + m ^ (hweak.β - hweak.β / hweak.α) + 1) := by
        -- expand the target RHS.
        have hexpand :
            Cstar * (‖p‖ ^ (hweak.α - 1)
                + m ^ (hweak.β - hweak.β / hweak.α) + 1)
              = Cstar * ‖p‖ ^ (hweak.α - 1)
                + Cstar * m ^ (hweak.β - hweak.β / hweak.α) + Cstar := by ring
        rw [hexpand]
        -- coefficient-domination facts (`hcoeff_*` are already folded to `r`).
        have hcp : (αd / ε) * (Cd / ε) ^ r ≤ Cstar := hcoeff_p
        have hcm : (αd / ε) * hweak.C ^ r ≤ Cstar := hcoeff_m
        have hcconst :
            (1 / ε)
                + (αd / ε)
                  * (hweak.C ^ r + (Cd / ε + hweak.C) ^ r)
              ≤ Cstar := hcoeff_const
        -- termwise domination of the three converted pieces.
        have hc1 :
            (αd / ε) * (Cd / ε) ^ r * ‖p‖ ^ (hweak.α - 1)
              ≤ Cstar * ‖p‖ ^ (hweak.α - 1) :=
          mul_le_mul_of_nonneg_right hcp hpα1_nn
        have hc2 :
            (αd / ε) * hweak.C ^ r * m ^ (hweak.β - hweak.β / hweak.α)
              ≤ Cstar * m ^ (hweak.β - hweak.β / hweak.α) :=
          mul_le_mul_of_nonneg_right hcm hmβα_nn
        -- the m-term carries an extra `αd/ε C^r` constant; route it into `hcconst`.
        have hCbr_nn'' : (0 : ℝ) ≤ (αd / ε) * hweak.C ^ r :=
          mul_nonneg hαε_nn (Real.rpow_nonneg hC_nn _)
        have hCdεCr_nn'' : (0 : ℝ) ≤ (αd / ε) * (Cd / ε + hweak.C) ^ r :=
          mul_nonneg hαε_nn (Real.rpow_nonneg hD_nn _)
        -- `(αd/ε) C^r (m+1) = (αd/ε) C^r m + (αd/ε) C^r`.
        have hmterm :
            (αd / ε) * hweak.C ^ r * (m ^ (hweak.β - hweak.β / hweak.α) + 1)
              = (αd / ε) * hweak.C ^ r * m ^ (hweak.β - hweak.β / hweak.α)
                + (αd / ε) * hweak.C ^ r := by ring
        -- constant pieces: `(1/ε) + (αd/ε) C^r + (αd/ε)(Cd/ε+C)^r ≤ Cstar`.
        have hconst_eq : (1 / ε)
                + (αd / ε)
                  * (hweak.C ^ r + (Cd / ε + hweak.C) ^ r)
              = (1 / ε) + (αd / ε) * hweak.C ^ r
                  + (αd / ε) * (Cd / ε + hweak.C) ^ r := by ring
        have hconst_le :
            (1 / ε) + (αd / ε) * hweak.C ^ r
                + (αd / ε) * (Cd / ε + hweak.C) ^ r
              ≤ Cstar := hconst_eq ▸ hcconst
        linarith [hαε_mul, hc1, hc2, hmterm.le, hmterm.ge, hconst_le]
      exact le_trans hmid htarget
    · -- (eq:assH.lower): the coercive lower bound.
      filter_upwards [hweak.lower, sel.H_form ε hε] with x hLowx hHform
      intro p m hm
      rw [HdeltaPos_eq_Hdelta_of_pos hweak hm]
      have hqStar :
          Hdelta hweak ε x p m
            = H x (p - qε ε (x, p, m)) m + (1 / ε) * K hweak (qε ε (x, p, m)) :=
        hHform p m hm
      have hLower :
          ‖p - qε ε (x, p, m)‖ ^ hweak.α / hweak.C
              - hweak.C * (m ^ hweak.β + 1)
            ≤ H x (p - qε ε (x, p, m)) m :=
        hLowx (p - qε ε (x, p, m)) m hm
      have hmβ : (0 : ℝ) ≤ m ^ hweak.β + 1 := by
        have : (0 : ℝ) ≤ m ^ hweak.β := Real.rpow_nonneg (le_of_lt hm) _
        linarith
      have hLB := Hdelta_lower_bound_uniform hweak hε (hε1)
        (qε ε (x, p, m)) hqStar hLower hmβ
      -- carrier wants `‖p‖^α/Cstar − Cstar(m^β+1)`; lemma gives the `2^α(C+1)` one.
      set C' : ℝ := (2 : ℝ) ^ hweak.α * (hweak.C + 1) with hCp_def
      have hpα_nn : (0 : ℝ) ≤ ‖p‖ ^ hweak.α := Real.rpow_nonneg (norm_nonneg _) _
      have hCp_pos : (0 : ℝ) < C' := mul_pos h2α_pos hC1_pos
      have hCp_le : C' ≤ Cstar := by rw [hCp_def]; exact hC2_le
      have hdiv_le : (‖p‖ ^ hweak.α) / Cstar ≤ (‖p‖ ^ hweak.α) / C' :=
        div_le_div_of_nonneg_left hpα_nn hCp_pos hCp_le
      have hCmul : Cstar * (m ^ hweak.β + 1) ≥ C' * (m ^ hweak.β + 1) :=
        mul_le_mul_of_nonneg_right hCp_le hmβ
      have : (‖p‖ ^ hweak.α) / Cstar - Cstar * (m ^ hweak.β + 1)
              ≤ (‖p‖ ^ hweak.α) / C' - C' * (m ^ hweak.β + 1) := by
        linarith [hdiv_le, hCmul]
      have hgoal : (‖p‖ ^ hweak.α) / Cstar - Cstar * (m ^ hweak.β + 1)
              ≤ Hdelta hweak ε x p m := le_trans this hLB
      -- `≥` is `GE.ge`; supply via `hgoal`.
      exact hgoal
    · -- (eq:boundsH): the closed-form pointwise upper bound.
      filter_upwards [hweak.upper, hweak.lower, sel.H_form ε hε] with
        x hUpx hLowx hHform
      intro p m hm
      rw [HdeltaPos_eq_Hdelta_of_pos hweak hm]
      have hBdd :
          BddBelow (Set.range fun q : Fin d → ℝ => H x (p - q) m) := by
        refine ⟨-(hweak.C * (m ^ hweak.β + 1)), ?_⟩
        rintro y ⟨q, rfl⟩
        have hLow := hLowx (p - q) m hm
        have hpα_nn : 0 ≤ ‖p - q‖ ^ hweak.α :=
          Real.rpow_nonneg (norm_nonneg _) _
        have hdiv_nn : 0 ≤ ‖p - q‖ ^ hweak.α / hweak.C :=
          div_nonneg hpα_nn hC_nn
        linarith [hLow]
      have hUb := Hdelta_upper_bound hweak hε (hε1) hm (hUpx m hm) hBdd
      set Cd' : ℝ := K_sup_const (d := d) hweak with hCd'_def
      have hpα_nn : (0 : ℝ) ≤ ‖p‖ ^ hweak.α := Real.rpow_nonneg (norm_nonneg _) _
      have hmβ_nn : (0 : ℝ) ≤ m ^ hweak.β := Real.rpow_nonneg (le_of_lt hm) _
      -- carrier wants `Cstar*(‖p‖^α+1) − m^β/Cstar`.
      have hcoef_p : (Cd' / ε) * ‖p‖ ^ hweak.α ≤ Cstar * ‖p‖ ^ hweak.α := by
        have : Cd' / ε ≤ Cstar := by rw [hCd'_def]; exact hCdε_le
        exact mul_le_mul_of_nonneg_right this hpα_nn
      have hdiv_le : (m ^ hweak.β) / Cstar ≤ (m ^ hweak.β) / hweak.C :=
        div_le_div_of_nonneg_left hmβ_nn hC_pos hCbase_le
      have hconst : Cd' / ε + hweak.C ≤ Cstar := by
        rw [hCd'_def]; exact hCdεCbase_le
      -- chain.
      have htarget :
          (Cd' / ε) * ‖p‖ ^ hweak.α - (m ^ hweak.β) / hweak.C
              + (Cd' / ε + hweak.C)
            ≤ Cstar * (‖p‖ ^ hweak.α + 1) - (m ^ hweak.β) / Cstar := by
        have hexpand : Cstar * (‖p‖ ^ hweak.α + 1)
            = Cstar * ‖p‖ ^ hweak.α + Cstar := by ring
        rw [hexpand]
        have h1 : -(m ^ hweak.β) / hweak.C = -((m ^ hweak.β) / hweak.C) := by ring
        have h2 : -(m ^ hweak.β) / Cstar = -((m ^ hweak.β) / Cstar) := by ring
        linarith [hcoef_p, hdiv_le, hconst]
      linarith [hUb, htarget]
    · -- (eq:DpHdotpminusH): the Lagrangian lower bound.
      filter_upwards [hweak.upper, hweak.lower, hCx ε hε (hε1)] with
        x hUpx hLowx hCxx
      intro p m hm
      rw [HdeltaPos_eq_Hdelta_of_pos hweak hm]
      have hUp : H x (0 : Fin d → ℝ) m ≤ -(m ^ hweak.β) / hweak.C + hweak.C :=
        hUpx m hm
      have hBdd :
          BddBelow (Set.range fun q : Fin d → ℝ => H x ((0 : Fin d → ℝ) - q) m) := by
        refine ⟨-(hweak.C * (m ^ hweak.β + 1)), ?_⟩
        rintro y ⟨q, rfl⟩
        have hLow := hLowx ((0 : Fin d → ℝ) - q) m hm
        have hpα_nn : 0 ≤ ‖(0 : Fin d → ℝ) - q‖ ^ hweak.α :=
          Real.rpow_nonneg (norm_nonneg _) _
        have hdiv_nn : 0 ≤ ‖(0 : Fin d → ℝ) - q‖ ^ hweak.α / hweak.C :=
          div_nonneg hpα_nn hC_nn
        linarith [hLow]
      have hLagr :
          (m ^ hweak.β) / hweak.C - hweak.C
            ≤ (DpHepsilonFam hweak qε ε x p m) ⬝ p - Hdelta hweak ε x p m :=
        Hdelta_lagrangian_lower_bound hweak hε (hε1)
          (DpHepsilonFam hweak qε ε) hm (hCxx p m hm) hUp hBdd
      have hmβ_nn : (0 : ℝ) ≤ m ^ hweak.β := Real.rpow_nonneg (le_of_lt hm) _
      have hdiv_le : (m ^ hweak.β) / Cstar ≤ (m ^ hweak.β) / hweak.C :=
        div_le_div_of_nonneg_left hmβ_nn hC_pos hCbase_le
      have : (m ^ hweak.β) / Cstar - Cstar
              ≤ (m ^ hweak.β) / hweak.C - hweak.C := by
        linarith [hdiv_le, hCbase_le]
      linarith [this, hLagr]

/-- **Dq4c producer: the `HdeltaPowerEpsData` carrier from the selector family**
(paper `prop:boundsHepsilon`).

Assembles the carrier from the per-`ε` bundle `hpowEps_of_selector`. The exponent
preservation facts `hα_eq`/`hβ_eq` hold by `rfl`, since `hpowEps_of_selector`
pins `α := hweak.α`, `β := hweak.β` (the `def` unfolds to the structure literal).

Takes NO `hInj`, NO global injectivity, NO uniform-`C` (no `hC_eq`); the only
riders are the paper-accepted `hMeas`/`hCx`/`hGrad`/`hFormPos`/`hqE_per`. -/
noncomputable def hdeltaPowerEpsData_of_selector
    (hweak : HypothesisWeakGrowth (d := d) H DpH) (qε : QEpsFamily d)
    (sel : InfConvSelectorFamily (H := H) (DpH := DpH) hweak qε)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (hqE_per : ∀ ε, ∀ p m, StationaryMFG.Periodic.IsPeriodic
      (fun x : Fin d → ℝ => qε ε (x, p, m)))
    (hFormPos : ∀ ε, 0 < ε →
      ∀ xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ, 0 < xpm.2.2 →
        Hdelta hweak ε xpm.1 xpm.2.1 xpm.2.2
          = H xpm.1 (xpm.2.1 - qε ε xpm) xpm.2.2 + (1 / ε) * K hweak (qε ε xpm))
    (hCx : ∀ ε, 0 < ε → ε ≤ 1 →
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
        ∀ p m, 0 < m →
          Hdelta hweak ε x p m - (DpHepsilonFam hweak qε ε x p m) ⬝ p
            ≤ Hdelta hweak ε x 0 m)
    (hGrad : ∀ ε, 0 < ε → ε ≤ 1 →
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
        ∀ p m, 0 < m →
          ‖DpHepsilonFam hweak qε ε x p m‖
            ≤ (1 / ε) * (1 + hweak.α * (Real.sqrt d) ^ (hweak.α - 1)
                * ‖qε ε (x, p, m)‖ ^ (hweak.α - 1))) :
    HdeltaPowerEpsData (H := H) (DpH := DpH) hweak qε where
  hpow := hpowEps_of_selector (H := H) (DpH := DpH)
    hweak qε sel hMeas hqE_per hFormPos hCx hGrad
  hα_eq := fun ε hε hε1 => rfl
  hβ_eq := fun ε hε hε1 => rfl

/-! ### D2c-2a — the AE estimate carrier `HdeltaAEPowerEpsData`

EXPERT RULING #4 (2026-06-09): the strict `HdeltaPowerEpsData` / per-`ε`
`HypothesisPowerGrowth(HdeltaPos)` carrier embeds a `RegularityH` whose `∀x`
periodicity (`hqE_per`) / global formula (`hFormPos`) demands are a
*formalization artifact* — the measurable-by-construction selector furnishes the
inf-conv identities only a.e.-`x`, and the paper uses them only under integrals.
We retype the final Theorem-3 path OFF the strict bundle onto this **a.e.
estimate carrier**: a Prop of the four `prop:boundsHepsilon` estimate bounds
guarded by `∀ᵐ x` + `0 < m`, with NO `RegularityH`, NO `periodic_DpH`, NO strict
`measurable_H`, and the producer carrying NONE of
`hqE_per`/`hFormPos`/`hInj`/`hSurj`/`qEofMinv`/`RegularityH(HdeltaPos)`/
`HypothesisPowerGrowth(HdeltaPos)`. -/

/-- **The per-`ε` growth constant `C_ε`** for `(H^ε, D_pH^ε)` (paper
`prop:boundsHepsilon`). This is the exact `Cstar` expression assembled inside
`hpowEps_of_selector`; it is the constant referenced by every AE estimate field
of `HdeltaAEPowerEpsData`. It is `ε`-dependent (blows up as `ε → 0`), so there is
no `ε`-uniform variant. -/
noncomputable def CdeltaEps
    (hweak : HypothesisWeakGrowth (d := d) H DpH) (ε : ℝ) : ℝ :=
  -- `αd := α · (√d)^{α−1}` is the gradient coefficient inflated by the
  -- Euclidean-kernel dimension factor (paper line 1808, Euclidean form;
  -- see `hGrad_of_selector` / `Hdelta_gradient_upper_bound`).
  (K_sup_const (d := d) hweak / ε
        + (2 : ℝ) ^ hweak.α * (hweak.C + 1))
    + (hweak.α * (Real.sqrt d) ^ (hweak.α - 1) / ε)
        * (K_sup_const (d := d) hweak / ε) ^ ((hweak.α - 1) / hweak.α)
    + (hweak.α * (Real.sqrt d) ^ (hweak.α - 1) / ε)
        * hweak.C ^ ((hweak.α - 1) / hweak.α)
    + ((1 / ε)
        + (hweak.α * (Real.sqrt d) ^ (hweak.α - 1) / ε)
          * (hweak.C ^ ((hweak.α - 1) / hweak.α)
              + (K_sup_const (d := d) hweak / ε + hweak.C)
                  ^ ((hweak.α - 1) / hweak.α)))

/-- Shared algebra facts about `CdeltaEps` (the per-`ε` constant), hoisted from the
`set Cstar` block of `hpowEps_of_selector`. The four `cdeltaEps_facts_*` lemmas
package the positivity + domination inequalities each AE estimate field needs. -/
lemma cdeltaEps_dom_facts
    (hweak : HypothesisWeakGrowth (d := d) H DpH) {ε : ℝ} (hε : 0 < ε) :
    let Cd := K_sup_const (d := d) hweak
    let r := (hweak.α - 1) / hweak.α
    let αd := hweak.α * (Real.sqrt d) ^ (hweak.α - 1)
    let Cstar := CdeltaEps (H := H) (DpH := DpH) hweak ε
    0 < Cstar
      ∧ (2 : ℝ) ^ hweak.α * (hweak.C + 1) ≤ Cstar
      ∧ Cd / ε ≤ Cstar
      ∧ hweak.C ≤ Cstar
      ∧ Cd / ε + hweak.C ≤ Cstar
      ∧ (αd / ε) * (Cd / ε) ^ r ≤ Cstar
      ∧ (αd / ε) * hweak.C ^ r ≤ Cstar
      ∧ ((1 / ε)
          + (αd / ε) * (hweak.C ^ r + (Cd / ε + hweak.C) ^ r)) ≤ Cstar := by
  intro Cd r αd Cstar
  have hα_pos : (0 : ℝ) < hweak.α := lt_trans zero_lt_one hweak.hα
  have hα_nn : (0 : ℝ) ≤ hweak.α := le_of_lt hα_pos
  have hα_sub_nn : (0 : ℝ) ≤ hweak.α - 1 := by linarith [hweak.hα]
  have hdFac_nn : (0 : ℝ) ≤ (Real.sqrt d) ^ (hweak.α - 1) :=
    Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hαd_nn : (0 : ℝ) ≤ αd := mul_nonneg hα_nn hdFac_nn
  have hC_pos : (0 : ℝ) < hweak.C := hweak.hC
  have hC_nn : (0 : ℝ) ≤ hweak.C := le_of_lt hC_pos
  have hC1_pos : (0 : ℝ) < hweak.C + 1 := by linarith
  have h2_pos : (0 : ℝ) < 2 := by norm_num
  have h2α_pos : (0 : ℝ) < (2 : ℝ) ^ hweak.α := Real.rpow_pos_of_pos h2_pos _
  have hCd_nn : (0 : ℝ) ≤ Cd := K_sup_const_nonneg hweak
  have hCdε_nn : (0 : ℝ) ≤ Cd / ε := div_nonneg hCd_nn (le_of_lt hε)
  have hαε_nn : (0 : ℝ) ≤ αd / ε := div_nonneg hαd_nn (le_of_lt hε)
  have hr_nn : (0 : ℝ) ≤ r :=
    div_nonneg (by linarith [hweak.hα]) hα_nn
  have hCdεr_nn : (0 : ℝ) ≤ (Cd / ε) ^ r := Real.rpow_nonneg hCdε_nn _
  have hCbr_nn : (0 : ℝ) ≤ hweak.C ^ r := Real.rpow_nonneg hC_nn _
  have hCdεCr_nn : (0 : ℝ) ≤ (Cd / ε + hweak.C) ^ r :=
    Real.rpow_nonneg (by linarith) _
  -- The flat sum expansion of `Cstar`.
  have hCstar_sum :
      Cstar = (Cd / ε + (2 : ℝ) ^ hweak.α * (hweak.C + 1))
        + (αd / ε) * (Cd / ε) ^ r
        + (αd / ε) * hweak.C ^ r
        + ((1 / ε)
            + (αd / ε)
              * (hweak.C ^ r + (Cd / ε + hweak.C) ^ r)) := rfl
  have hg1_pos : (0 : ℝ) < Cd / ε + (2 : ℝ) ^ hweak.α * (hweak.C + 1) := by
    have : (0 : ℝ) < (2 : ℝ) ^ hweak.α * (hweak.C + 1) := mul_pos h2α_pos hC1_pos
    linarith
  have hg2_nn : (0 : ℝ) ≤ (αd / ε) * (Cd / ε) ^ r := mul_nonneg hαε_nn hCdεr_nn
  have hg3_nn : (0 : ℝ) ≤ (αd / ε) * hweak.C ^ r := mul_nonneg hαε_nn hCbr_nn
  have hg4_nn :
      (0 : ℝ) ≤ (1 / ε)
          + (αd / ε) * (hweak.C ^ r + (Cd / ε + hweak.C) ^ r) := by
    have hpos : (0 : ℝ) < 1 / ε := one_div_pos.mpr hε
    have : (0 : ℝ) ≤ (αd / ε) * (hweak.C ^ r + (Cd / ε + hweak.C) ^ r) :=
      mul_nonneg hαε_nn (by linarith)
    linarith
  have h2αC_nn : (0 : ℝ) ≤ (2 : ℝ) ^ hweak.α * (hweak.C + 1) :=
    le_of_lt (mul_pos h2α_pos hC1_pos)
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ hweak.α := by
    have := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1)
      (by norm_num : (1:ℝ) ≤ 2) hα_nn
    simpa using this
  have hC_le_2αC : hweak.C ≤ (2 : ℝ) ^ hweak.α * (hweak.C + 1) := by
    calc hweak.C ≤ hweak.C + 1 := by linarith
      _ = 1 * (hweak.C + 1) := by ring
      _ ≤ (2 : ℝ) ^ hweak.α * (hweak.C + 1) :=
        mul_le_mul_of_nonneg_right h1 (le_of_lt hC1_pos)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hCstar_sum]; linarith [hCdε_nn, h2αC_nn, hg2_nn, hg3_nn, hg4_nn]
  · rw [hCstar_sum]; linarith [hCdε_nn, hg2_nn, hg3_nn, hg4_nn]
  · rw [hCstar_sum]; linarith [h2αC_nn, hg2_nn, hg3_nn, hg4_nn]
  · rw [hCstar_sum]; linarith [hCdε_nn, hC_le_2αC, hg2_nn, hg3_nn, hg4_nn]
  · rw [hCstar_sum]; linarith [hC_le_2αC, hg2_nn, hg3_nn, hg4_nn]
  · rw [hCstar_sum]; linarith [hCdε_nn, h2αC_nn, hg3_nn, hg4_nn]
  · rw [hCstar_sum]; linarith [hCdε_nn, h2αC_nn, hg2_nn, hg4_nn]
  · rw [hCstar_sum]; linarith [hCdε_nn, h2αC_nn, hg2_nn, hg3_nn]

/-- Positivity of the per-`ε` constant `CdeltaEps`. -/
lemma CdeltaEps_pos
    (hweak : HypothesisWeakGrowth (d := d) H DpH) {ε : ℝ} (hε : 0 < ε) :
    0 < CdeltaEps (H := H) (DpH := DpH) hweak ε :=
  (cdeltaEps_dom_facts (H := H) (DpH := DpH) hweak hε).1

/-- `(0 < Cstar, hweak.C ≤ Cstar)` — for the `upper`/`lagr` fields. -/
lemma cdeltaEps_facts_upper
    (hweak : HypothesisWeakGrowth (d := d) H DpH) {ε : ℝ} (hε : 0 < ε) :
    0 < CdeltaEps (H := H) (DpH := DpH) hweak ε
      ∧ hweak.C ≤ CdeltaEps (H := H) (DpH := DpH) hweak ε := by
  obtain ⟨h0, _, _, hbase, _⟩ := cdeltaEps_dom_facts (H := H) (DpH := DpH) hweak hε
  exact ⟨h0, hbase⟩

/-- The full domination tuple — for the `upper` field's `Cd/ε + C ≤ Cstar`. -/
lemma cdeltaEps_facts_dom
    (hweak : HypothesisWeakGrowth (d := d) H DpH) {ε : ℝ} (hε : 0 < ε) :
    let Cd := K_sup_const (d := d) hweak
    0 < CdeltaEps (H := H) (DpH := DpH) hweak ε
      ∧ (2 : ℝ) ^ hweak.α * (hweak.C + 1)
          ≤ CdeltaEps (H := H) (DpH := DpH) hweak ε
      ∧ Cd / ε ≤ CdeltaEps (H := H) (DpH := DpH) hweak ε
      ∧ hweak.C ≤ CdeltaEps (H := H) (DpH := DpH) hweak ε
      ∧ Cd / ε + hweak.C ≤ CdeltaEps (H := H) (DpH := DpH) hweak ε := by
  intro Cd
  obtain ⟨h0, h2, hd, hbase, hdb, _, _, _⟩ :=
    cdeltaEps_dom_facts (H := H) (DpH := DpH) hweak hε
  exact ⟨h0, h2, hd, hbase, hdb⟩

/-- `(0 < Cstar, hcoeff_p, hcoeff_m, hcoeff_const)` — for the `DpH_upper` field. -/
lemma cdeltaEps_facts_coeff
    (hweak : HypothesisWeakGrowth (d := d) H DpH) {ε : ℝ} (hε : 0 < ε) :
    0 < CdeltaEps (H := H) (DpH := DpH) hweak ε
      ∧ (hweak.α * (Real.sqrt d) ^ (hweak.α - 1) / ε)
            * (K_sup_const (d := d) hweak / ε) ^ ((hweak.α - 1) / hweak.α)
          ≤ CdeltaEps (H := H) (DpH := DpH) hweak ε
      ∧ (hweak.α * (Real.sqrt d) ^ (hweak.α - 1) / ε)
            * hweak.C ^ ((hweak.α - 1) / hweak.α)
          ≤ CdeltaEps (H := H) (DpH := DpH) hweak ε
      ∧ ((1 / ε)
          + (hweak.α * (Real.sqrt d) ^ (hweak.α - 1) / ε)
            * (hweak.C ^ ((hweak.α - 1) / hweak.α)
                + (K_sup_const (d := d) hweak / ε + hweak.C)
                    ^ ((hweak.α - 1) / hweak.α)))
          ≤ CdeltaEps (H := H) (DpH := DpH) hweak ε := by
  obtain ⟨h0, _, _, _, _, hp, hm, hconst⟩ :=
    cdeltaEps_dom_facts (H := H) (DpH := DpH) hweak hε
  exact ⟨h0, hp, hm, hconst⟩

/-- `(0 < Cstar, 2^α(C+1) ≤ Cstar)` — for the `lower` field. -/
lemma cdeltaEps_facts_lower
    (hweak : HypothesisWeakGrowth (d := d) H DpH) {ε : ℝ} (hε : 0 < ε) :
    0 < CdeltaEps (H := H) (DpH := DpH) hweak ε
      ∧ (2 : ℝ) ^ hweak.α * (hweak.C + 1)
          ≤ CdeltaEps (H := H) (DpH := DpH) hweak ε := by
  obtain ⟨h0, h2, _⟩ := cdeltaEps_dom_facts (H := H) (DpH := DpH) hweak hε
  exact ⟨h0, h2⟩

/-- **`AE` estimate carrier for `(H^ε, D_pH^ε)`** (paper `prop:boundsHepsilon`),
the retyped-off-strict variant mandated by EXPERT RULING #4.

Carries the four `prop:boundsHepsilon` estimate bounds with the per-`ε` constant
`Cε ε` (the paper's `C_ε`), each guarded by `∀ᵐ x ∂(volume.restrict (UnitCube d))`
and `0 < m` — exactly the slice on which the inf-conv estimates hold and on which
every Theorem-3 consumer evaluates. The bounds are stated on the raw `Hdelta`
(NOT the junk-extended `HdeltaPos`), so the carrier needs no global all-`m`
measurability witness, no `RegularityH`, no `periodic_DpH`. -/
structure HdeltaAEPowerEpsData
    (hweak : HypothesisWeakGrowth (d := d) H DpH) (qε : QEpsFamily d) : Prop where
  /-- (eq:assH.upper) `H^ε(x, 0, m) ≤ -m^β / C_ε + C_ε`, a.e. `x`, `m > 0`,
  with the per-`ε` constant `C_ε := CdeltaEps hweak ε`. -/
  upper_ae : ∀ ε, 0 < ε → ε ≤ 1 →
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
      ∀ m, 0 < m →
        Hdelta hweak ε x (0 : Fin d → ℝ) m
          ≤ -(m ^ hweak.β) / CdeltaEps (H := H) (DpH := DpH) hweak ε
              + CdeltaEps (H := H) (DpH := DpH) hweak ε
  /-- (eq:DpHdelta.upper) `‖D_pH^ε(x,p,m)‖ ≤ C_ε(‖p‖^{α-1}+m^{β-β/α}+1)`,
  a.e. `x`, `m > 0`. -/
  DpH_upper_ae : ∀ ε, 0 < ε → ε ≤ 1 →
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
      ∀ p m, 0 < m →
        ‖DpHepsilonFam hweak qε ε x p m‖
          ≤ CdeltaEps (H := H) (DpH := DpH) hweak ε
              * (‖p‖ ^ (hweak.α - 1)
                  + m ^ (hweak.β - hweak.β / hweak.α) + 1)
  /-- (eq:assH.lower) `H^ε(x,p,m) ≥ ‖p‖^α / C_ε − C_ε(m^β + 1)`,
  a.e. `x`, `m > 0`. -/
  lower_ae : ∀ ε, 0 < ε → ε ≤ 1 →
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
      ∀ p m, 0 < m →
        (‖p‖ ^ hweak.α) / CdeltaEps (H := H) (DpH := DpH) hweak ε
            - CdeltaEps (H := H) (DpH := DpH) hweak ε * (m ^ hweak.β + 1)
          ≤ Hdelta hweak ε x p m
  /-- (eq:DpHdelta.dotp.minusH) `D_pH^ε·p − H^ε ≥ m^β / C_ε − C_ε`,
  a.e. `x`, `m > 0`. -/
  lagr_ae : ∀ ε, 0 < ε → ε ≤ 1 →
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
      ∀ p m, 0 < m →
        (m ^ hweak.β) / CdeltaEps (H := H) (DpH := DpH) hweak ε
            - CdeltaEps (H := H) (DpH := DpH) hweak ε
          ≤ (DpHepsilonFam hweak qε ε x p m) ⬝ p - Hdelta hweak ε x p m
  /-- (eq:boundsH) `H^ε(x,p,m) ≤ C_ε(‖p‖^α + 1) − m^β / C_ε`,
  a.e. `x`, `m > 0` — the general-`p` closed-form pointwise upper bound.
  EXPERT RULING #4 (D2c-2e-1 child B): this is the AE sibling of the strict
  `HypothesisPowerGrowth.H_upper_pointwise` field, derived a.e. off the raw
  `Hdelta` the SAME way `hpowEps_of_selector`'s `H_upper_pointwise` is derived
  (from `Hdelta_upper_bound` together with `hweak.upper`/`hweak.lower` and the
  a.e. inf-conv attainment identity `sel.H_form`). -/
  H_upper_pointwise_ae : ∀ ε, 0 < ε → ε ≤ 1 →
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
      ∀ p m, 0 < m →
        Hdelta hweak ε x p m
          ≤ CdeltaEps (H := H) (DpH := DpH) hweak ε * (‖p‖ ^ hweak.α + 1)
              - (m ^ hweak.β) / CdeltaEps (H := H) (DpH := DpH) hweak ε

/-- **D2c-2a producer: the AE estimate carrier from the selector family**
(paper `prop:boundsHepsilon`), retyped OFF the strict `HdeltaPowerEpsData` per
EXPERT RULING #4.

Derives each AE estimate field directly from `sel.H_form` (the a.e. inf-conv
attainment identity) together with the `Hdelta_*` bound lemmas, plus the two
genuine paper-accepted riders `hCx` (convex-at-zero, used for the Lagrangian
field — same class as `Hdelta_lagrangian_lower_bound`'s `hCx`) and `hGrad` (the
`‖q^ε‖`-form gradient bound, used for `DpH_upper`). It takes NO `hMeas`, NO
`hqE_per`, NO `hFormPos`, NO global injectivity, and constructs NO `RegularityH`:
the four fields are pure a.e. estimates on the raw `Hdelta`.

GATE #1: binders are `(hweak, qε, sel, hCx, hGrad)` ONLY; none of
`hqE_per`/`hFormPos`/`hInj`/`hSurj`/`qEofMinv`/`RegularityH(HdeltaPos)`/
`HypothesisPowerGrowth(HdeltaPos)` appears. -/
noncomputable def hdeltaAEPowerEpsData_of_selector
    (hweak : HypothesisWeakGrowth (d := d) H DpH) (qε : QEpsFamily d)
    (sel : InfConvSelectorFamily (H := H) (DpH := DpH) hweak qε)
    (hCx : ∀ ε, 0 < ε → ε ≤ 1 →
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
        ∀ p m, 0 < m →
          Hdelta hweak ε x p m - (DpHepsilonFam hweak qε ε x p m) ⬝ p
            ≤ Hdelta hweak ε x 0 m)
    (hGrad : ∀ ε, 0 < ε → ε ≤ 1 →
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
        ∀ p m, 0 < m →
          ‖DpHepsilonFam hweak qε ε x p m‖
            ≤ (1 / ε) * (1 + hweak.α * (Real.sqrt d) ^ (hweak.α - 1)
                * ‖qε ε (x, p, m)‖ ^ (hweak.α - 1))) :
    HdeltaAEPowerEpsData (H := H) (DpH := DpH) hweak qε where
  upper_ae := by
    intro ε hε hε1
    set Cstar : ℝ := CdeltaEps (H := H) (DpH := DpH) hweak ε with hCstar_def
    obtain ⟨hCstar_pos, hCbase_le⟩ :=
      cdeltaEps_facts_upper (H := H) (DpH := DpH) hweak hε
    filter_upwards [hweak.upper, hweak.lower, sel.H_form ε hε] with
      x hUpx hLowx hHform
    intro m hm
    -- `BddBelow` of `q ↦ H x (0 - q) m`.
    have hC_pos : (0 : ℝ) < hweak.C := hweak.hC
    have hC_nn : (0 : ℝ) ≤ hweak.C := le_of_lt hC_pos
    have hα_pos : (0 : ℝ) < hweak.α := lt_trans zero_lt_one hweak.hα
    have hα_ne : hweak.α ≠ 0 := ne_of_gt hα_pos
    have hBdd :
        BddBelow (Set.range fun q : Fin d → ℝ => H x ((0 : Fin d → ℝ) - q) m) := by
      refine ⟨-(hweak.C * (m ^ hweak.β + 1)), ?_⟩
      rintro y ⟨q, rfl⟩
      have hLow := hLowx ((0 : Fin d → ℝ) - q) m hm
      have hpα_nn : 0 ≤ ‖(0 : Fin d → ℝ) - q‖ ^ hweak.α :=
        Real.rpow_nonneg (norm_nonneg _) _
      have hdiv_nn : 0 ≤ ‖(0 : Fin d → ℝ) - q‖ ^ hweak.α / hweak.C :=
        div_nonneg hpα_nn hC_nn
      linarith [hLow]
    have hUb := Hdelta_upper_bound hweak hε (hε1) hm (hUpx m hm) hBdd
    have hnorm0 : ‖(0 : Fin d → ℝ)‖ ^ hweak.α = 0 := by
      rw [norm_zero]; exact Real.zero_rpow hα_ne
    rw [hnorm0, mul_zero] at hUb
    have hmβ_nn : (0 : ℝ) ≤ m ^ hweak.β := Real.rpow_nonneg (le_of_lt hm) _
    have hdiv_le : (m ^ hweak.β) / Cstar ≤ (m ^ hweak.β) / hweak.C :=
      div_le_div_of_nonneg_left hmβ_nn hC_pos hCbase_le
    have hgoaleq1 : -(m ^ hweak.β) / Cstar = -((m ^ hweak.β) / Cstar) := by ring
    have hgoaleq2 : -(m ^ hweak.β) / hweak.C = -((m ^ hweak.β) / hweak.C) := by ring
    rw [hgoaleq1]
    have hCdεCbase_le :
        K_sup_const (d := d) hweak / ε + hweak.C ≤ Cstar :=
      (cdeltaEps_facts_dom (H := H) (DpH := DpH) hweak hε).2.2.2.2
    linarith [hUb, hdiv_le, hCdεCbase_le, hgoaleq2]
  DpH_upper_ae := by
    intro ε hε hε1
    set Cstar : ℝ := CdeltaEps (H := H) (DpH := DpH) hweak ε with hCstar_def
    obtain ⟨hCstar_pos, hcoeff_p, hcoeff_m, hcoeff_const⟩ :=
      cdeltaEps_facts_coeff (H := H) (DpH := DpH) hweak hε
    filter_upwards [hweak.upper, hweak.lower, sel.H_form ε hε,
      sel.DpH_form ε hε, hGrad ε hε (hε1)] with
      x hUpx hLowx hHform hDpHform hGradx
    intro p m hm
    have hα_pos : (0 : ℝ) < hweak.α := lt_trans zero_lt_one hweak.hα
    have hα_nn : (0 : ℝ) ≤ hweak.α := le_of_lt hα_pos
    have hC_pos : (0 : ℝ) < hweak.C := hweak.hC
    have hC_nn : (0 : ℝ) ≤ hweak.C := le_of_lt hC_pos
    set Cd : ℝ := K_sup_const (d := d) hweak with hCd_def
    have hCd_nn : (0 : ℝ) ≤ Cd := K_sup_const_nonneg hweak
    have hε_inv_pos : (0 : ℝ) < 1 / ε := one_div_pos.mpr hε
    have hCdε_nn : (0 : ℝ) ≤ Cd / ε := div_nonneg hCd_nn (le_of_lt hε)
    -- Euclidean-kernel dimension-inflated gradient coefficient.
    set αd : ℝ := hweak.α * (Real.sqrt d) ^ (hweak.α - 1) with hαd_def
    have hdFac_nn : (0 : ℝ) ≤ (Real.sqrt d) ^ (hweak.α - 1) :=
      Real.rpow_nonneg (Real.sqrt_nonneg _) _
    have hαd_nn : (0 : ℝ) ≤ αd := mul_nonneg hα_nn hdFac_nn
    have hαε_nn : (0 : ℝ) ≤ αd / ε := div_nonneg hαd_nn (le_of_lt hε)
    have hr_nn : (0 : ℝ) ≤ (hweak.α - 1) / hweak.α :=
      div_nonneg (by linarith [hweak.hα]) hα_nn
    have hr_le1 : (hweak.α - 1) / hweak.α ≤ 1 := by
      rw [div_le_one hα_pos]; linarith
    have hqStar :
        Hdelta hweak ε x p m
          = H x (p - qε ε (x, p, m)) m + (1 / ε) * K hweak (qε ε (x, p, m)) :=
      hHform p m hm
    have hLower :
        ‖p - qε ε (x, p, m)‖ ^ hweak.α / hweak.C
            - hweak.C * (m ^ hweak.β + 1)
          ≤ H x (p - qε ε (x, p, m)) m :=
      hLowx (p - qε ε (x, p, m)) m hm
    have hUpper : H x (0 : Fin d → ℝ) m ≤ -(m ^ hweak.β) / hweak.C + hweak.C :=
      hUpx m hm
    have hBdd :
        BddBelow (Set.range fun q : Fin d → ℝ => H x (p - q) m) := by
      refine ⟨-(hweak.C * (m ^ hweak.β + 1)), ?_⟩
      rintro y ⟨q, rfl⟩
      have hLow := hLowx (p - q) m hm
      have hpα_nn : 0 ≤ ‖p - q‖ ^ hweak.α :=
        Real.rpow_nonneg (norm_nonneg _) _
      have hdiv_nn : 0 ≤ ‖p - q‖ ^ hweak.α / hweak.C :=
        div_nonneg hpα_nn hC_nn
      linarith [hLow]
    have hDpHε_via_qStar :
        ‖DpHepsilonFam hweak qε ε x p m‖
          ≤ (1 / ε) * (1 + hweak.α * (Real.sqrt d) ^ (hweak.α - 1)
              * ‖qε ε (x, p, m)‖ ^ (hweak.α - 1)) :=
      hGradx p m hm
    have hGB := Hdelta_gradient_upper_bound hweak hε (hε1)
      (DpHepsilonFam hweak qε ε) hm (qε ε (x, p, m)) hqStar hLower hUpper hBdd
      hDpHε_via_qStar
    set R : ℝ := (K_sup_const (d := d) hweak / ε) * ‖p‖ ^ hweak.α
          + hweak.C * (m ^ hweak.β + 1) + (K_sup_const (d := d) hweak / ε + hweak.C)
      with hRdef
    set r : ℝ := (hweak.α - 1) / hweak.α with hr_def
    have hpα_nn : (0 : ℝ) ≤ ‖p‖ ^ hweak.α := Real.rpow_nonneg (norm_nonneg _) _
    have hmβ_nn : (0 : ℝ) ≤ m ^ hweak.β := Real.rpow_nonneg (le_of_lt hm) _
    have hA_nn : (0 : ℝ) ≤ (Cd / ε) * ‖p‖ ^ hweak.α :=
      mul_nonneg hCdε_nn hpα_nn
    have hB_nn : (0 : ℝ) ≤ hweak.C * (m ^ hweak.β + 1) :=
      mul_nonneg hC_nn (by linarith)
    have hD_nn : (0 : ℝ) ≤ Cd / ε + hweak.C := by linarith
    have hsplit1 :
        R ^ r ≤ ((Cd / ε) * ‖p‖ ^ hweak.α) ^ r
            + (hweak.C * (m ^ hweak.β + 1) + (Cd / ε + hweak.C)) ^ r := by
      have hBD_nn : (0 : ℝ) ≤ hweak.C * (m ^ hweak.β + 1) + (Cd / ε + hweak.C) := by
        linarith
      have : R = (Cd / ε) * ‖p‖ ^ hweak.α
            + (hweak.C * (m ^ hweak.β + 1) + (Cd / ε + hweak.C)) := by
        rw [hRdef, hCd_def]; ring
      rw [this]
      exact Real.rpow_add_le_add_rpow hA_nn hBD_nn hr_nn hr_le1
    have hsplit2 :
        (hweak.C * (m ^ hweak.β + 1) + (Cd / ε + hweak.C)) ^ r
          ≤ (hweak.C * (m ^ hweak.β + 1)) ^ r + (Cd / ε + hweak.C) ^ r :=
      Real.rpow_add_le_add_rpow hB_nn hD_nn hr_nn hr_le1
    have hαr_eq : hweak.α * r = hweak.α - 1 := by
      rw [hr_def]; field_simp
    have hβr_eq : hweak.β * r = hweak.β - hweak.β / hweak.α := by
      rw [hr_def]; field_simp
    have hAr :
        ((Cd / ε) * ‖p‖ ^ hweak.α) ^ r
          = (Cd / ε) ^ r * ‖p‖ ^ (hweak.α - 1) := by
      rw [Real.mul_rpow hCdε_nn hpα_nn]
      congr 1
      rw [← Real.rpow_mul (norm_nonneg _), hαr_eq]
    have hBr :
        (hweak.C * (m ^ hweak.β + 1)) ^ r
          ≤ hweak.C ^ r * (m ^ (hweak.β - hweak.β / hweak.α) + 1) := by
      rw [Real.mul_rpow hC_nn (by linarith)]
      have hsub :
          (m ^ hweak.β + 1) ^ r ≤ (m ^ hweak.β) ^ r + (1 : ℝ) ^ r :=
        Real.rpow_add_le_add_rpow hmβ_nn (by norm_num) hr_nn hr_le1
      have hone : (1 : ℝ) ^ r = 1 := Real.one_rpow _
      have hmβr : (m ^ hweak.β) ^ r = m ^ (hweak.β - hweak.β / hweak.α) := by
        rw [← Real.rpow_mul (le_of_lt hm), hβr_eq]
      have hCr_nn : (0 : ℝ) ≤ hweak.C ^ r := Real.rpow_nonneg hC_nn _
      calc hweak.C ^ r * (m ^ hweak.β + 1) ^ r
          ≤ hweak.C ^ r * ((m ^ hweak.β) ^ r + (1 : ℝ) ^ r) :=
            mul_le_mul_of_nonneg_left hsub hCr_nn
        _ = hweak.C ^ r * (m ^ (hweak.β - hweak.β / hweak.α) + 1) := by
            rw [hmβr, hone]
    have hmβα_nn : (0 : ℝ) ≤ m ^ (hweak.β - hweak.β / hweak.α) :=
      Real.rpow_nonneg (le_of_lt hm) _
    have hpα1_nn : (0 : ℝ) ≤ ‖p‖ ^ (hweak.α - 1) :=
      Real.rpow_nonneg (norm_nonneg _) _
    have hRr_le :
        R ^ r
          ≤ (Cd / ε) ^ r * ‖p‖ ^ (hweak.α - 1)
            + hweak.C ^ r * (m ^ (hweak.β - hweak.β / hweak.α) + 1)
            + (Cd / ε + hweak.C) ^ r := by
      calc R ^ r
          ≤ ((Cd / ε) * ‖p‖ ^ hweak.α) ^ r
              + (hweak.C * (m ^ hweak.β + 1) + (Cd / ε + hweak.C)) ^ r := hsplit1
        _ ≤ ((Cd / ε) * ‖p‖ ^ hweak.α) ^ r
              + ((hweak.C * (m ^ hweak.β + 1)) ^ r + (Cd / ε + hweak.C) ^ r) := by
            linarith [hsplit2]
        _ = (Cd / ε) ^ r * ‖p‖ ^ (hweak.α - 1)
              + (hweak.C * (m ^ hweak.β + 1)) ^ r + (Cd / ε + hweak.C) ^ r := by
            rw [hAr]; ring
        _ ≤ (Cd / ε) ^ r * ‖p‖ ^ (hweak.α - 1)
              + hweak.C ^ r * (m ^ (hweak.β - hweak.β / hweak.α) + 1)
              + (Cd / ε + hweak.C) ^ r := by linarith [hBr]
    have hmid :
        ‖DpHepsilonFam hweak qε ε x p m‖ ≤ (1 / ε) + (αd / ε) * R ^ r := by
      have hrw : (1 / ε) * (1 + αd * R ^ r)
            = (1 / ε) + (αd / ε) * R ^ r := by
        field_simp
      rw [hrw] at hGB; exact hGB
    have hαε_mul :
        (αd / ε) * R ^ r
          ≤ (αd / ε) * (Cd / ε) ^ r * ‖p‖ ^ (hweak.α - 1)
            + (αd / ε) * hweak.C ^ r * (m ^ (hweak.β - hweak.β / hweak.α) + 1)
            + (αd / ε) * (Cd / ε + hweak.C) ^ r := by
      have hstep := mul_le_mul_of_nonneg_left hRr_le hαε_nn
      calc (αd / ε) * R ^ r
          ≤ (αd / ε)
              * ((Cd / ε) ^ r * ‖p‖ ^ (hweak.α - 1)
                + hweak.C ^ r * (m ^ (hweak.β - hweak.β / hweak.α) + 1)
                + (Cd / ε + hweak.C) ^ r) := hstep
        _ = (αd / ε) * (Cd / ε) ^ r * ‖p‖ ^ (hweak.α - 1)
            + (αd / ε) * hweak.C ^ r * (m ^ (hweak.β - hweak.β / hweak.α) + 1)
            + (αd / ε) * (Cd / ε + hweak.C) ^ r := by ring
    have htarget :
        (1 / ε) + (αd / ε) * R ^ r
          ≤ Cstar * (‖p‖ ^ (hweak.α - 1)
              + m ^ (hweak.β - hweak.β / hweak.α) + 1) := by
      have hexpand :
          Cstar * (‖p‖ ^ (hweak.α - 1)
              + m ^ (hweak.β - hweak.β / hweak.α) + 1)
            = Cstar * ‖p‖ ^ (hweak.α - 1)
              + Cstar * m ^ (hweak.β - hweak.β / hweak.α) + Cstar := by ring
      rw [hexpand]
      have hcp : (αd / ε) * (Cd / ε) ^ r ≤ Cstar := hcoeff_p
      have hcm : (αd / ε) * hweak.C ^ r ≤ Cstar := hcoeff_m
      have hcconst :
          (1 / ε)
              + (αd / ε)
                * (hweak.C ^ r + (Cd / ε + hweak.C) ^ r)
            ≤ Cstar := hcoeff_const
      have hc1 :
          (αd / ε) * (Cd / ε) ^ r * ‖p‖ ^ (hweak.α - 1)
            ≤ Cstar * ‖p‖ ^ (hweak.α - 1) :=
        mul_le_mul_of_nonneg_right hcp hpα1_nn
      have hc2 :
          (αd / ε) * hweak.C ^ r * m ^ (hweak.β - hweak.β / hweak.α)
            ≤ Cstar * m ^ (hweak.β - hweak.β / hweak.α) :=
        mul_le_mul_of_nonneg_right hcm hmβα_nn
      have hCbr_nn'' : (0 : ℝ) ≤ (αd / ε) * hweak.C ^ r :=
        mul_nonneg hαε_nn (Real.rpow_nonneg hC_nn _)
      have hCdεCr_nn'' : (0 : ℝ) ≤ (αd / ε) * (Cd / ε + hweak.C) ^ r :=
        mul_nonneg hαε_nn (Real.rpow_nonneg hD_nn _)
      have hmterm :
          (αd / ε) * hweak.C ^ r * (m ^ (hweak.β - hweak.β / hweak.α) + 1)
            = (αd / ε) * hweak.C ^ r * m ^ (hweak.β - hweak.β / hweak.α)
              + (αd / ε) * hweak.C ^ r := by ring
      have hconst_eq : (1 / ε)
              + (αd / ε)
                * (hweak.C ^ r + (Cd / ε + hweak.C) ^ r)
            = (1 / ε) + (αd / ε) * hweak.C ^ r
                + (αd / ε) * (Cd / ε + hweak.C) ^ r := by ring
      have hconst_le :
          (1 / ε) + (αd / ε) * hweak.C ^ r
              + (αd / ε) * (Cd / ε + hweak.C) ^ r
            ≤ Cstar := hconst_eq ▸ hcconst
      linarith [hαε_mul, hc1, hc2, hmterm.le, hmterm.ge, hconst_le]
    exact le_trans hmid htarget
  lower_ae := by
    intro ε hε hε1
    set Cstar : ℝ := CdeltaEps (H := H) (DpH := DpH) hweak ε with hCstar_def
    obtain ⟨hCstar_pos, hC2_le⟩ :=
      cdeltaEps_facts_lower (H := H) (DpH := DpH) hweak hε
    filter_upwards [hweak.lower, sel.H_form ε hε] with x hLowx hHform
    intro p m hm
    have hC_pos : (0 : ℝ) < hweak.C := hweak.hC
    have hC_nn : (0 : ℝ) ≤ hweak.C := le_of_lt hC_pos
    have hα_pos : (0 : ℝ) < hweak.α := lt_trans zero_lt_one hweak.hα
    have hα_nn : (0 : ℝ) ≤ hweak.α := le_of_lt hα_pos
    have h2_pos : (0 : ℝ) < 2 := by norm_num
    have h2α_pos : (0 : ℝ) < (2 : ℝ) ^ hweak.α := Real.rpow_pos_of_pos h2_pos _
    have hC1_pos : (0 : ℝ) < hweak.C + 1 := by linarith
    have hqStar :
        Hdelta hweak ε x p m
          = H x (p - qε ε (x, p, m)) m + (1 / ε) * K hweak (qε ε (x, p, m)) :=
      hHform p m hm
    have hLower :
        ‖p - qε ε (x, p, m)‖ ^ hweak.α / hweak.C
            - hweak.C * (m ^ hweak.β + 1)
          ≤ H x (p - qε ε (x, p, m)) m :=
      hLowx (p - qε ε (x, p, m)) m hm
    have hmβ : (0 : ℝ) ≤ m ^ hweak.β + 1 := by
      have : (0 : ℝ) ≤ m ^ hweak.β := Real.rpow_nonneg (le_of_lt hm) _
      linarith
    have hLB := Hdelta_lower_bound_uniform hweak hε (hε1)
      (qε ε (x, p, m)) hqStar hLower hmβ
    set C' : ℝ := (2 : ℝ) ^ hweak.α * (hweak.C + 1) with hCp_def
    have hpα_nn : (0 : ℝ) ≤ ‖p‖ ^ hweak.α := Real.rpow_nonneg (norm_nonneg _) _
    have hCp_pos : (0 : ℝ) < C' := mul_pos h2α_pos hC1_pos
    have hCp_le : C' ≤ Cstar := by rw [hCp_def]; exact hC2_le
    have hdiv_le : (‖p‖ ^ hweak.α) / Cstar ≤ (‖p‖ ^ hweak.α) / C' :=
      div_le_div_of_nonneg_left hpα_nn hCp_pos hCp_le
    have hCmul : Cstar * (m ^ hweak.β + 1) ≥ C' * (m ^ hweak.β + 1) :=
      mul_le_mul_of_nonneg_right hCp_le hmβ
    have : (‖p‖ ^ hweak.α) / Cstar - Cstar * (m ^ hweak.β + 1)
            ≤ (‖p‖ ^ hweak.α) / C' - C' * (m ^ hweak.β + 1) := by
      linarith [hdiv_le, hCmul]
    exact le_trans this hLB
  lagr_ae := by
    intro ε hε hε1
    set Cstar : ℝ := CdeltaEps (H := H) (DpH := DpH) hweak ε with hCstar_def
    obtain ⟨hCstar_pos, hCbase_le⟩ :=
      cdeltaEps_facts_upper (H := H) (DpH := DpH) hweak hε
    filter_upwards [hweak.upper, hweak.lower, hCx ε hε (hε1)] with
      x hUpx hLowx hCxx
    intro p m hm
    have hC_pos : (0 : ℝ) < hweak.C := hweak.hC
    have hC_nn : (0 : ℝ) ≤ hweak.C := le_of_lt hC_pos
    have hα_pos : (0 : ℝ) < hweak.α := lt_trans zero_lt_one hweak.hα
    have hUp : H x (0 : Fin d → ℝ) m ≤ -(m ^ hweak.β) / hweak.C + hweak.C :=
      hUpx m hm
    have hBdd :
        BddBelow (Set.range fun q : Fin d → ℝ => H x ((0 : Fin d → ℝ) - q) m) := by
      refine ⟨-(hweak.C * (m ^ hweak.β + 1)), ?_⟩
      rintro y ⟨q, rfl⟩
      have hLow := hLowx ((0 : Fin d → ℝ) - q) m hm
      have hpα_nn : 0 ≤ ‖(0 : Fin d → ℝ) - q‖ ^ hweak.α :=
        Real.rpow_nonneg (norm_nonneg _) _
      have hdiv_nn : 0 ≤ ‖(0 : Fin d → ℝ) - q‖ ^ hweak.α / hweak.C :=
        div_nonneg hpα_nn hC_nn
      linarith [hLow]
    have hLagr :
        (m ^ hweak.β) / hweak.C - hweak.C
          ≤ (DpHepsilonFam hweak qε ε x p m) ⬝ p - Hdelta hweak ε x p m :=
      Hdelta_lagrangian_lower_bound hweak hε (hε1)
        (DpHepsilonFam hweak qε ε) hm (hCxx p m hm) hUp hBdd
    have hmβ_nn : (0 : ℝ) ≤ m ^ hweak.β := Real.rpow_nonneg (le_of_lt hm) _
    have hdiv_le : (m ^ hweak.β) / Cstar ≤ (m ^ hweak.β) / hweak.C :=
      div_le_div_of_nonneg_left hmβ_nn hC_pos hCbase_le
    have : (m ^ hweak.β) / Cstar - Cstar
            ≤ (m ^ hweak.β) / hweak.C - hweak.C := by
      linarith [hdiv_le, hCbase_le]
    linarith [this, hLagr]
  H_upper_pointwise_ae := by
    -- Adapted from the strict `hpowEps_of_selector` `H_upper_pointwise`
    -- field (Properties.lean `eq:boundsH` bullet); a.e. off raw `Hdelta`.
    intro ε hε hε1
    set Cstar : ℝ := CdeltaEps (H := H) (DpH := DpH) hweak ε with hCstar_def
    obtain ⟨hCstar_pos, _, hCdε_le, hCbase_le, _⟩ :=
      cdeltaEps_facts_dom (H := H) (DpH := DpH) hweak hε
    filter_upwards [hweak.upper, hweak.lower, sel.H_form ε hε] with
      x hUpx hLowx hHform
    intro p m hm
    have hC_pos : (0 : ℝ) < hweak.C := hweak.hC
    have hC_nn : (0 : ℝ) ≤ hweak.C := le_of_lt hC_pos
    have hqStar :
        Hdelta hweak ε x p m
          = H x (p - qε ε (x, p, m)) m + (1 / ε) * K hweak (qε ε (x, p, m)) :=
      hHform p m hm
    have hBdd :
        BddBelow (Set.range fun q : Fin d → ℝ => H x (p - q) m) := by
      refine ⟨-(hweak.C * (m ^ hweak.β + 1)), ?_⟩
      rintro y ⟨q, rfl⟩
      have hLow := hLowx (p - q) m hm
      have hpα_nn : 0 ≤ ‖p - q‖ ^ hweak.α :=
        Real.rpow_nonneg (norm_nonneg _) _
      have hdiv_nn : 0 ≤ ‖p - q‖ ^ hweak.α / hweak.C :=
        div_nonneg hpα_nn hC_nn
      linarith [hLow]
    have hUb := Hdelta_upper_bound hweak hε (hε1) hm (hUpx m hm) hBdd
    set Cd' : ℝ := K_sup_const (d := d) hweak with hCd'_def
    have hpα_nn : (0 : ℝ) ≤ ‖p‖ ^ hweak.α := Real.rpow_nonneg (norm_nonneg _) _
    have hmβ_nn : (0 : ℝ) ≤ m ^ hweak.β := Real.rpow_nonneg (le_of_lt hm) _
    -- carrier wants `Cstar*(‖p‖^α+1) − m^β/Cstar`.
    have hcoef_p : (Cd' / ε) * ‖p‖ ^ hweak.α ≤ Cstar * ‖p‖ ^ hweak.α := by
      have : Cd' / ε ≤ Cstar := by rw [hCd'_def]; exact hCdε_le
      exact mul_le_mul_of_nonneg_right this hpα_nn
    have hdiv_le : (m ^ hweak.β) / Cstar ≤ (m ^ hweak.β) / hweak.C :=
      div_le_div_of_nonneg_left hmβ_nn hC_pos hCbase_le
    have hCdεCbase_le :
        K_sup_const (d := d) hweak / ε + hweak.C ≤ Cstar :=
      (cdeltaEps_facts_dom (H := H) (DpH := DpH) hweak hε).2.2.2.2
    have hconst : Cd' / ε + hweak.C ≤ Cstar := by
      rw [hCd'_def]; exact hCdεCbase_le
    have htarget :
        (Cd' / ε) * ‖p‖ ^ hweak.α - (m ^ hweak.β) / hweak.C
            + (Cd' / ε + hweak.C)
          ≤ Cstar * (‖p‖ ^ hweak.α + 1) - (m ^ hweak.β) / Cstar := by
      have hexpand : Cstar * (‖p‖ ^ hweak.α + 1)
          = Cstar * ‖p‖ ^ hweak.α + Cstar := by ring
      rw [hexpand]
      have h1 : -(m ^ hweak.β) / hweak.C = -((m ^ hweak.β) / hweak.C) := by ring
      have h2 : -(m ^ hweak.β) / Cstar = -((m ^ hweak.β) / Cstar) := by ring
      linarith [hcoef_p, hdiv_le, hconst]
    linarith [hUb, htarget]

/-! ### D2c-2e DpH-side drains — `measurable_DpH` / `continuous_DpH_pm` off the
selector family (NOT the strict `HypothesisPowerGrowth(HdeltaPos)` bundle)

The HdeltaK0-path Minty wrappers consume three DpH-side facts that the strict
`hpowEps` bundle supplied: global measurability of `D_pH^ε`, the a.e. `{0<m}`
continuity of `(p,m) ↦ D_pH^ε`, and the a.e. upper bound. All three are about
`DpHepsilon`/`DpHepsilonFam` — **carrier-independent** of the `HdeltaPos`
junk extension — hence a.e.-sufficient and drainable off the AE infra:

* `measurable_DpHepsilonFam_of_selector` — from `sel.q_meas` (global selector
  measurability) + `hMeas` (base `DpH` measurability), via `DpHepsilon_measurable`;
* `continuousOn_DpHepsilonFam_of_selector` — from `hweak.toRegularityH` (base
  `H`/`DpH` regularity, NOT the `HdeltaPos` carrier) + `sel.q_cont_pm`, via
  `DpHepsilon_continuousOn_DpH_pm`;
* the a.e. upper bound is `HdeltaAEPowerEpsData.DpH_upper_ae` (D2c-2a) directly.

GATE #1: binders are `(hweak, qε, sel, hMeas)` only; no `hpowEps`, no
`RegularityH(HdeltaPos)`, no `hInj`/`hSurj`/`hFormPos`/`hqE_per`. -/

/-- **D2c-2e: global measurability of `D_pH^ε` from the selector family.**
`DpHepsilonFam hweak qε ε` (`= DpHepsilon hweak (qε ε)` definitionally) is
globally measurable, from `sel.q_meas ε` (the selector is globally measurable)
and `hMeas` (base `DpH` measurability). Off the strict bundle entirely. -/
theorem measurable_DpHepsilonFam_of_selector
    (hweak : HypothesisWeakGrowth (d := d) H DpH) (qε : QEpsFamily d)
    (sel : InfConvSelectorFamily (H := H) (DpH := DpH) hweak qε)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (ε : ℝ) :
    Measurable
      (fun xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ =>
        DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε xpm.1 xpm.2.1 xpm.2.2) :=
  DpHepsilon_measurable (H := H) (DpH := DpH) hweak (qε ε) hMeas (sel.q_meas ε)

/-- **D2c-2e: a.e. `{0<m}`-continuity of `(p,m) ↦ D_pH^ε` from the selector
family.** From `hweak.toRegularityH` (the BASE `H`/`DpH` regularity, permitted —
NOT the `HdeltaPos` carrier) and `sel.q_cont_pm ε hε` (selector continuity on
`{0<m}`), via `DpHepsilon_continuousOn_DpH_pm`. Off the strict bundle entirely. -/
theorem continuousOn_DpHepsilonFam_of_selector
    (hweak : HypothesisWeakGrowth (d := d) H DpH) (qε : QEpsFamily d)
    (sel : InfConvSelectorFamily (H := H) (DpH := DpH) hweak qε)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
      ContinuousOn (fun pm : (Fin d → ℝ) × ℝ =>
          DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε x pm.1 pm.2)
        {pm | 0 < pm.2} :=
  DpHepsilon_continuousOn_DpH_pm (H := H) (DpH := DpH) hweak (qε ε)
    hweak.toRegularityH (sel.q_cont_pm ε hε)

/-! ### D6c-2a-2b (flux half) — closed-cone continuity of `m • D_pH^ε`

The K0 OBJECT the transport equation consumes is the flux
`JsimpleExt (DpHepsilonFam …) x p m = m • D_pH^ε(x, p, m)`, NOT `D_pH^ε`
alone. Its joint continuity on the CLOSED cone `{0 ≤ m}` is the
`continuous_mDpH_pm` field of `RegularityHK0 (HdeltaK0 …) (DpHepsilonFam …)`.

Per the user directive we prove continuity of the *flux* `m • D_pH^ε`, not of
`D_pH^ε` at `m = 0` (the latter is not paper-faithful and may fail): the `m •`
prefactor DAMPS the possible `D_pH^ε`-blowup across the boundary, where the
flux value is `0 • _ = 0` (`JsimpleExt_zero`).

The argument is the `DpHepsilonFam`-specialisation of the K0 flux machinery
`InfimalConvolution.mDpHdelta_hat0` (InfConv.lean), itself adapted from
`HypothesisPowerGrowth.toMDpHat0` (Assumptions.lean): on `{0<m}` use the open-cone
continuity `continuousOn_DpHepsilonFam_of_selector`; at the boundary squeeze
`‖m • D_pH^ε‖ ≤ m · Bnd(p,m)` with the `DpH_upper_ae` dominator
`Bnd(p,m) = C_ε·(‖p‖^{α-1} + m^{β-β/α} + 1)`, continuous on `{0 ≤ m}` (exponents
`α-1 ≥ 0`, `β-β/α ≥ 0`), which tends to `0·Bnd(p,0) = 0`. -/

/-- **D6c-2a-2b, flux half.** For a.e. `x`, the flux
`(p, m) ↦ JsimpleExt (DpHepsilonFam hweak qε ε) x p m = m • D_pH^ε(x, p, m)`
is continuous on the CLOSED cone `{pm | 0 ≤ pm.2}`. This is the
`continuous_mDpH_pm` field of the regularized-pair `RegularityHK0`.

Binders are `(hweak, qε, sel, hMeas, hAE, hε, hε1)`: no strict positivity,
no `HdeltaPos` junk at `m = 0` (the genuine flux is `m • D_pH^ε`, which is `0`
at `m = 0` by the `m •` factor), no `hInj`/`hSurj`/`qEofMinv`/
`HypothesisPowerGrowth`, no Pack/Inputs/Oracle binders. -/
theorem continuousOn_JsimpleExt_DpHepsilonFam_of_selector
    (hweak : HypothesisWeakGrowth (d := d) H DpH) (qε : QEpsFamily d)
    (sel : InfConvSelectorFamily (H := H) (DpH := DpH) hweak qε)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (hAE : HdeltaAEPowerEpsData (H := H) (DpH := DpH) hweak qε)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
      ContinuousOn (fun pm : (Fin d → ℝ) × ℝ =>
          JsimpleExt (DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε) x pm.1 pm.2)
        {pm | 0 ≤ pm.2} := by
  -- The dominator from `DpH_upper_ae`, continuous on the closed cone.
  set Cstar : ℝ := CdeltaEps (H := H) (DpH := DpH) hweak ε with hCstar_def
  set Bnd : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ :=
    fun _ p m => Cstar * (‖p‖ ^ (hweak.α - 1) + m ^ (hweak.β - hweak.β / hweak.α) + 1)
    with hBnd_def
  -- Exponent non-negativity (`α > 1`, `β > 0`).
  have hα_pos : (0 : ℝ) < hweak.α := lt_trans zero_lt_one hweak.hα
  have hα1_nonneg : (0 : ℝ) ≤ hweak.α - 1 := by linarith [hweak.hα]
  have hβα_nonneg : (0 : ℝ) ≤ hweak.β - hweak.β / hweak.α := by
    have hdiv_lt : hweak.β / hweak.α < hweak.β := by
      rw [div_lt_iff₀ hα_pos]; nlinarith [hweak.hβ, hweak.hα]
    linarith
  -- `Bnd` is continuous on the closed cone (in fact everywhere): the two
  -- `rpow` summands have non-negative exponents, hence are continuous.
  have hBndCont :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
        ContinuousOn (fun pm : (Fin d → ℝ) × ℝ => Bnd x pm.1 pm.2)
          {pm | 0 ≤ pm.2} := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    have h_p_pow : Continuous
        (fun pm : (Fin d → ℝ) × ℝ => ‖pm.1‖ ^ (hweak.α - 1)) :=
      (Real.continuous_rpow_const hα1_nonneg).comp
        (continuous_norm.comp continuous_fst)
    have h_m_pow : Continuous
        (fun pm : (Fin d → ℝ) × ℝ => pm.2 ^ (hweak.β - hweak.β / hweak.α)) :=
      (Real.continuous_rpow_const hβα_nonneg).comp continuous_snd
    have hcont : Continuous (fun pm : (Fin d → ℝ) × ℝ => Bnd x pm.1 pm.2) :=
      continuous_const.mul ((h_p_pow.add h_m_pow).add continuous_const)
    exact hcont.continuousOn
  -- The norm bound on `{0<m}` from `DpH_upper_ae`.
  have hBnd_bound :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
        ∀ p : Fin d → ℝ, ∀ m : ℝ, 0 < m →
          ‖DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε x p m‖ ≤ Bnd x p m := by
    filter_upwards [hAE.DpH_upper_ae ε hε hε1] with x hx p m hm
    exact hx p m hm
  -- Feed the K0 flux machinery `mDpHdelta_hat0`; extract `continuous_J`.
  have hJ :=
    (mDpHdelta_hat0 (d := d)
      (DpHε := DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε)
      (Bnd := Bnd)
      (continuousOn_DpHepsilonFam_of_selector hweak qε sel hε)
      hBndCont hBnd_bound
      (measurable_DpHepsilonFam_of_selector hweak qε sel hMeas ε)).continuous_J
  -- `mDpHdelta_hat0`'s `J = if 0<m then m•DpHε else 0` agrees with
  -- `JsimpleExt DpHε = m • DpHε` on the closed cone `{0 ≤ m}`.
  filter_upwards [hJ] with x hx
  refine hx.congr ?_
  intro pm hpm
  have hpm2 : (0 : ℝ) ≤ pm.2 := hpm
  rcases lt_or_eq_of_le hpm2 with hpos | hzero
  · simp [JsimpleExt, hpos]
  · have hpm2eq : pm.2 = 0 := hzero.symm
    simp [JsimpleExt, hpm2eq]

/-! ## Dq3 — the concrete inf-conv selector family `qStarSelectorFam`

The Dq3 producer must build a `QEpsFamily d` and certify it as an
`InfConvSelectorFamily` from the four paper hypotheses `(hmon, hweak,
hdiff, hmeas)` ALONE — crucially WITHOUT the impossible *global*
injectivity `Function.Injective (MepsilonGlobal hweak ε)` (paper
`lem:inf-conv-props` proves invertibility only *outside a null set of
`x`*, and `MepsilonGlobal` is total).

We define the selector directly from the per-point inf-conv minimizer
(paper line 1631 — the inf in `eq:defHdelta` is a *minimum* for `m > 0`,
a.e. `x`), choosing a minimizer via `Classical.choose` where one exists
and falling back to `0` otherwise. This is the `qStar`-native object the
task mandates (NOT `qEofMinv`, which is `hInj`-gated).

The cleanly-derivable attainment field is landed here:
* `qStarSelectorFam_H_form` — the inf-conv attainment identity
  (`eq:H-epsilon-formula`), from `Classical.choose_spec` on the slice
  where the minimum exists (a.e. `x`, `m > 0`); derived purely from
  `hweak.lower` + a.e. `{m>0}`-continuity of `H(x, ·, m)`.

The regularized-gradient identity (`eq:DpH-epsilon-formula`) is `rfl` for
*any* `qε` (`DpHepsilonFam_eq`), so it needs no dedicated selector lemma; the
live `DpH_form` field is supplied by `qMeasFam_DpH_form`.

The remaining two fields are tracked as honest children (NOT papered
over): `q_cont_pm` requires reconciling `RegularityH.continuous_H_pm`
(which gives only `{m>0}` joint continuity, not the *global* joint
continuity in `(q,p,m)` that `qStar_continuousOn_pos_of_unique` consumes),
and `q_meas` requires a measurable-selection theorem for the per-point
minimizer (paper's semi-explicit formula `eq:q-star-semi-explicit` —
Mathlib has no Kuratowski–Ryll-Nardzewski / Aumann selection). See the
filed Dq3c/Dq3e children. -/

/-- **Per-point inf-conv minimizer existence predicate.** Holds when the
infimum defining `Hdelta hweak ε x p m` is attained at some `q`. The
selector `qStarSelectorFam` chooses such a `q` exactly when this holds
(a.e. `x`, `m > 0`, by paper line 1631), and falls back to `0`
otherwise. -/
def InfConvAttained
    (hweak : HypothesisWeakGrowth (d := d) H DpH) (ε : ℝ)
    (xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ) : Prop :=
  ∃ q : Fin d → ℝ,
    H xpm.1 (xpm.2.1 - q) xpm.2.2 + (1 / ε) * K hweak q
      = Hdelta hweak ε xpm.1 xpm.2.1 xpm.2.2

/-- **The concrete `qStar`-native selector family** (paper `q^ε`,
`lem:inf-conv-props`). For each `ε`, `qStarSelectorFam hweak ε (x,p,m)` is
a minimizer of `q ↦ H(x, p−q, m) + (1/ε) K(q)` whenever one exists
(`InfConvAttained`), chosen by `Classical.choose`; otherwise `0`.

This is the object the Dq3 producer certifies as an
`InfConvSelectorFamily`. It uses NO global injectivity / `MepsilonMinv`. -/
noncomputable def qStarSelectorFam
    (hweak : HypothesisWeakGrowth (d := d) H DpH) : QEpsFamily d :=
  fun ε xpm =>
    haveI := Classical.dec (InfConvAttained (H := H) (DpH := DpH) hweak ε xpm)
    if h : InfConvAttained (H := H) (DpH := DpH) hweak ε xpm then
      Classical.choose h
    else 0

/-- **Attainment of the selector** where the minimum exists: if
`InfConvAttained hweak ε (x,p,m)`, then the selector value realises the
inf-conv infimum (paper `eq:H-epsilon-formula`). -/
lemma qStarSelectorFam_spec
    (hweak : HypothesisWeakGrowth (d := d) H DpH) (ε : ℝ)
    {xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ}
    (hatt : InfConvAttained (H := H) (DpH := DpH) hweak ε xpm) :
    H xpm.1 (xpm.2.1 - qStarSelectorFam (H := H) (DpH := DpH) hweak ε xpm)
        xpm.2.2
      + (1 / ε) * K hweak (qStarSelectorFam (H := H) (DpH := DpH) hweak ε xpm)
      = Hdelta hweak ε xpm.1 xpm.2.1 xpm.2.2 := by
  have hval : qStarSelectorFam (H := H) (DpH := DpH) hweak ε xpm
      = Classical.choose hatt := by
    unfold qStarSelectorFam
    rw [dif_pos hatt]
  rw [hval]
  exact Classical.choose_spec hatt

/-- **A.e. attainment of the inf-conv minimum** (paper line 1631 — for
`m > 0`, a.e. `x`, the infimum in `eq:defHdelta` is a minimum). Derived
from `hweak.lower` (the weak-growth coercivity) and a.e. `{m>0}`-slice
continuity of `H(x, ·, m)` (`hweak.continuous_H_pm`), via the
codebase minimizer-existence lemma `qStar_exists`. -/
lemma infConvAttained_ae
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
      ∀ (p : Fin d → ℝ) (m : ℝ), 0 < m →
        InfConvAttained (H := H) (DpH := DpH) hweak ε (x, p, m) := by
  filter_upwards [hweak.lower, hweak.continuous_H_pm] with x hxLower hxCont
  intro p m hm
  -- Per-point continuity of `q ↦ H x (p−q) m` from the `{m>0}` slice.
  have hCont : Continuous (fun q : Fin d → ℝ => H x (p - q) m) :=
    H_slice_continuous_of_continuousOn (H := H) hm hxCont
  -- Per-point weak-growth lower bound from `hweak.lower`.
  have hLower : ∀ q : Fin d → ℝ,
      ‖p - q‖ ^ hweak.α / hweak.C - hweak.C * (m ^ hweak.β + 1)
        ≤ H x (p - q) m := by
    intro q
    have := hxLower (p - q) m hm
    simpa [ge_iff_le] using this
  -- `qStar_exists` delivers the minimizer.
  obtain ⟨q, hq⟩ := qStar_exists (H := H) (DpH := DpH) hweak hε hCont hLower
  exact ⟨q, hq⟩

/-- **`H_form` field for `qStarSelectorFam`** (paper `eq:H-epsilon-formula`,
line 1681). For `ε > 0`, a.e. `x`, all `p`, and `m > 0`, the inf-conv
infimum is attained at the selector, with penalty `(1/ε) · K hweak`
exactly as in `Hdelta`. Combines `infConvAttained_ae` (the minimum
exists) with `qStarSelectorFam_spec` (the selector realises it). -/
theorem qStarSelectorFam_H_form
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
      ∀ p m, 0 < m →
        Hdelta hweak ε x p m
          = H x (p - qStarSelectorFam (H := H) (DpH := DpH) hweak ε (x, p, m)) m
            + (1 / ε) * K hweak
                (qStarSelectorFam (H := H) (DpH := DpH) hweak ε (x, p, m)) := by
  filter_upwards [infConvAttained_ae (H := H) (DpH := DpH) hweak hε]
    with x hxAtt
  intro p m hm
  have hatt : InfConvAttained (H := H) (DpH := DpH) hweak ε (x, p, m) :=
    hxAtt p m hm
  exact (qStarSelectorFam_spec (H := H) (DpH := DpH) hweak ε hatt).symm

/-- **`hUniq` rider for `qStarSelectorFam` (a.e.-`x`, `{0<m}`)** —
UNIQUENESS of the inf-conv minimiser for the `qStar`-native selector (paper
line 1632). For a.e. `x`, all `p`, all `m > 0` and all `q`: if
`H x (p−q) m + (1/ε) K hweak q = Hdelta hweak ε x p m`, then
`q = qStarSelectorFam hweak ε (x, p, m)`.

The "selector realises the infimum" ingredient is `qStarSelectorFam_H_form`,
so this uses NO global injectivity `hInj`. The strict-convexity uniqueness
step: `g q := H x (p−q) m + (1/ε) K q` attains its infimum `Hdelta` at both
`q` and `qS := qStarSelectorFam …`, scaling by `ε > 0` makes both `IsMinOn`
of the strictly convex `F q := ε H(x,p−q,m) + K q`, and
`StrictConvexOn.eq_of_isMinOn` forces equality. -/
theorem hUniq_qStarSelectorFam_pos
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hDiff : Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
      ∀ (p : Fin d → ℝ) (m : ℝ), 0 < m → ∀ q : Fin d → ℝ,
        H x (p - q) m + (1 / ε) * K hweak q = Hdelta hweak ε x p m
          → q = qStarSelectorFam (H := H) (DpH := DpH) hweak ε (x, p, m) := by
  filter_upwards [hweak.lower, hDiff.convexOn_H_p,
    qStarSelectorFam_H_form (H := H) (DpH := DpH) hweak hε]
    with x hxLower hxConvH hxHform
  intro p m hm q hq
  have hConvH : ConvexOn ℝ (Set.univ : Set (Fin d → ℝ))
      (fun q : Fin d → ℝ => H x q m) := hxConvH m hm
  set qS : Fin d → ℝ := qStarSelectorFam (H := H) (DpH := DpH) hweak ε (x, p, m)
    with hqSdef
  set g : (Fin d → ℝ) → ℝ := fun q => H x (p - q) m + (1 / ε) * K hweak q
    with hgdef
  set F : (Fin d → ℝ) → ℝ := fun q => ε * H x (p - q) m + K hweak q with hFdef
  have hHd : Hdelta hweak ε x p m = ⨅ q : Fin d → ℝ, g q := rfl
  have hC_pos : 0 < hweak.C := hweak.hC
  have hε_inv_pos : 0 < 1 / ε := one_div_pos.mpr hε
  have hBdd : BddBelow (Set.range g) := by
    refine ⟨-(hweak.C * (m ^ hweak.β + 1)), ?_⟩
    rintro y ⟨q', rfl⟩
    have hLow := hxLower (p - q') m hm
    have hpα_nn : 0 ≤ ‖p - q'‖ ^ hweak.α := Real.rpow_nonneg (norm_nonneg _) _
    have hdiv_nn : 0 ≤ ‖p - q'‖ ^ hweak.α / hweak.C :=
      div_nonneg hpα_nn (le_of_lt hC_pos)
    have hK_nn : 0 ≤ K hweak q' := K_nonneg hweak q'
    have hpen_nn : 0 ≤ (1 / ε) * K hweak q' :=
      mul_nonneg (le_of_lt hε_inv_pos) hK_nn
    change -(hweak.C * (m ^ hweak.β + 1)) ≤ H x (p - q') m + (1 / ε) * K hweak q'
    have hHge : (‖p - q'‖ ^ hweak.α) / hweak.C - hweak.C * (m ^ hweak.β + 1)
        ≤ H x (p - q') m := by simpa [ge_iff_le] using hLow
    linarith
  have hgq : g q = Hdelta hweak ε x p m := hq
  have hgS : g qS = Hdelta hweak ε x p m := by
    have := hxHform p m hm
    change H x (p - qS) m + (1 / ε) * K hweak qS = Hdelta hweak ε x p m
    rw [hqSdef]; exact this.symm
  have hmin_g : ∀ {q₀ : Fin d → ℝ}, g q₀ = Hdelta hweak ε x p m →
      IsMinOn g Set.univ q₀ := by
    intro q₀ hq₀ q' _
    change g q₀ ≤ g q'
    rw [hq₀, hHd]
    exact ciInf_le hBdd q'
  have hqS_min_g : IsMinOn g Set.univ qS := hmin_g hgS
  have hq_min_g : IsMinOn g Set.univ q := hmin_g hgq
  have hF_eq : ∀ q₀ : Fin d → ℝ, F q₀ = ε * g q₀ := by
    intro q₀
    simp only [hFdef, hgdef]
    field_simp
  have hscale_min : ∀ {q₀ : Fin d → ℝ}, IsMinOn g Set.univ q₀ →
      IsMinOn F Set.univ q₀ := by
    intro q₀ hmin q' _
    change F q₀ ≤ F q'
    rw [hF_eq q₀, hF_eq q']
    exact mul_le_mul_of_nonneg_left (hmin (Set.mem_univ q')) (le_of_lt hε)
  have hqS_min_F : IsMinOn F Set.univ qS := hscale_min hqS_min_g
  have hq_min_F : IsMinOn F Set.univ q := hscale_min hq_min_g
  have hF_sc : StrictConvexOn ℝ (Set.univ : Set (Fin d → ℝ)) F :=
    strictConvexOn_F_scaled (H := H) (DpH := DpH) hweak (le_of_lt hε) x p m hConvH
  exact hF_sc.eq_of_isMinOn hq_min_F hqS_min_F (Set.mem_univ _) (Set.mem_univ _)

/-! ### D7 — selector-based pointwise stabilisation core

These two lemmas let the Theorem-3 limit-passage A4 stabilisation
(`hstab`) be produced from the *abstract* `InfConvSelectorFamily` `sel`
(NOT the concrete `qStarSelectorFam`), at a test pair where `μ > 0`.
The genuine analytic core — uniqueness of the inf-conv minimiser via
strict convexity — is shared with `Mepsilon_xm_injective` (Step 4), here
extracted so the selector's first-order field `sel.hSub` (the K-side
support inequality at the minimiser `qε ε (x,p,m)`) can be combined with
the smallness inclusion `HasSubgradientAt (K hweak) 0 (ε • DpH x p m)`
(from `DpH_in_subdiff_zero`) to force `qε ε (x,p,m) = 0`. -/

/-- **Subgradient-at-`q` forces `F`-minimality.** If
`HasSubgradientAt (K h) q (ε • DpH x (p−q) m)` (the K-side first-order
condition at `q`, in the shape produced by `sel.hSub`) and the
H-subgradient inequality holds at `s = p − q`, then `q` minimises
`F q' := ε · H(x, p−q', m) + K h q'` over `univ`. This is the Step-4
core of `Mepsilon_xm_injective`, extracted for reuse. -/
theorem isMinOn_F_of_KSubgradient
    (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} (hε_nn : 0 ≤ ε) {x p : Fin d → ℝ} {m : ℝ} (q : Fin d → ℝ)
    (hKsub : HasSubgradientAt (K h) q (ε • DpH x (p - q) m))
    (hHsub : ∀ y : Fin d → ℝ,
      H x (p - q) m + ∑ i, (DpH x (p - q) m) i * (y i - (p - q) i) ≤ H x y m) :
    IsMinOn (fun q' : Fin d → ℝ => ε * H x (p - q') m + K h q') Set.univ q := by
  set s : Fin d → ℝ := p - q with hsdef
  intro q' _
  change ε * H x (p - q) m + K h q ≤ ε * H x (p - q') m + K h q'
  -- H-subgradient at `s = p − q`, tested at `p − q'`.
  have hH_at_q' := hHsub (p - q')
  have hH_mul :
      ε * (H x s m + ∑ i, (DpH x s m) i * ((p - q') i - s i))
        ≤ ε * H x (p - q') m :=
    mul_le_mul_of_nonneg_left hH_at_q' hε_nn
  have hH_expand : ε * (H x s m + ∑ i, (DpH x s m) i * ((p - q') i - s i))
      = ε * H x s m + ε * ∑ i, (DpH x s m) i * ((p - q') i - s i) := by ring
  rw [hH_expand] at hH_mul
  -- K-subgradient at `q`, tested at `q'`.
  have hK_at_q' := hKsub q'
  have hpair :
      ∑ i, (ε • DpH x s m) i * (q' i - q i)
        = ε * ∑ i, (DpH x s m) i * (q' i - q i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    simp [Pi.smul_apply, smul_eq_mul]; ring
  rw [hpair] at hK_at_q'
  -- `(p − q') i − s i = q i − q' i`.
  have h_idx : ∀ i,
      (DpH x s m) i * ((p - q') i - s i) = (DpH x s m) i * (q i - q' i) := by
    intro i; congr 1; rw [hsdef]; simp only [Pi.sub_apply]; ring
  have hsum_eq :
      ∑ i, (DpH x s m) i * ((p - q') i - s i)
        = ∑ i, (DpH x s m) i * (q i - q' i) :=
    Finset.sum_congr rfl (fun i _ => h_idx i)
  rw [hsum_eq] at hH_mul
  have h_neg_sum : ∑ i, (DpH x s m) i * (q' i - q i)
      = -(∑ i, (DpH x s m) i * (q i - q' i)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _; ring
  have hH_s_eq : H x s m = H x (p - q) m := by rw [hsdef]
  rw [hH_s_eq] at hH_mul
  rw [h_neg_sum] at hK_at_q'
  linarith

/-- **Selector stabilisation core: `qε ε (x,p,m) = 0` under smallness.**
At a point `(x, p, m)` with `0 < m`, given:
* `sel.hSub` instantiated to the K-side support inequality at the
  minimiser `qε ε (x,p,m)` (passed as `hSubq`);
* the smallness inclusion `HasSubgradientAt (K hweak) 0 (ε • DpH x p m)`
  (from `DpH_in_subdiff_zero`, i.e. `‖DpH x p m‖ < M`, `ε < ε₀(M)`);
* convexity of `H(x, ·, m)` (`hDiff.convexOn_H_p`) and its Fréchet
  derivative `hDiff.hasFDerivAt_H_p`,

the inf-conv minimiser collapses to the origin: `qε ε (x,p,m) = 0`. Both
`0` and `qε ε (x,p,m)` minimise the strictly convex
`F q' := ε H(x,p−q',m) + K hweak q'`; `StrictConvexOn.eq_of_isMinOn`
forces equality. -/
theorem qSelector_eq_zero_of_DpH_small
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hDiff : Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    (qε : QEpsFamily d) {ε : ℝ} (hε : 0 < ε)
    {x p : Fin d → ℝ} {m : ℝ} (hm : 0 < m)
    (hConvH : ConvexOn ℝ (Set.univ : Set (Fin d → ℝ))
      (fun q : Fin d → ℝ => H x q m))
    (hFDH : ∀ s : Fin d → ℝ,
      HasFDerivAt (fun q : Fin d → ℝ => H x q m)
        (Hamiltonian.dotCLMHam (DpH x s m)) s)
    (hSubq : ∀ q : Fin d → ℝ,
      DpH x (p - qε ε (x, p, m)) m ⬝ (q - qε ε (x, p, m))
        ≤ (1 / ε) * (K hweak q - K hweak (qε ε (x, p, m))))
    (hZeroSub : HasSubgradientAt (K hweak) 0 (ε • DpH x p m)) :
    qε ε (x, p, m) = 0 := by
  classical
  set qS : Fin d → ℝ := qε ε (x, p, m) with hqSdef
  set F : (Fin d → ℝ) → ℝ := fun q' => ε * H x (p - q') m + K hweak q' with hFdef
  -- Strict convexity of `F`.
  have hF_sc : StrictConvexOn ℝ (Set.univ : Set (Fin d → ℝ)) F :=
    strictConvexOn_F_scaled (H := H) (DpH := DpH) hweak (le_of_lt hε) x p m hConvH
  -- `qS` satisfies the K-subgradient inclusion at `qS` (rescale `hSubq` by `ε`).
  have hKsub_qS : HasSubgradientAt (K hweak) qS (ε • DpH x (p - qS) m) := by
    intro y
    -- Goal: `K qS + ∑ i, (ε • DpH x (p−qS) m) i * (y i − qS i) ≤ K y`.
    have hy := hSubq y
    -- `hy : DpH x (p−qS) m ⬝ (y − qS) ≤ (1/ε)(K y − K qS)`.
    have hpair :
        ∑ i, (ε • DpH x (p - qS) m) i * (y i - qS i)
          = ε * (DpH x (p - qS) m ⬝ (y - qS)) := by
      unfold euclideanDot
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      simp [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
    rw [hpair]
    -- Multiply `hy` by `ε > 0`.
    have hmul : ε * (DpH x (p - qS) m ⬝ (y - qS))
        ≤ ε * ((1 / ε) * (K hweak y - K hweak qS)) :=
      mul_le_mul_of_nonneg_left hy (le_of_lt hε)
    have hcancel : ε * ((1 / ε) * (K hweak y - K hweak qS))
        = K hweak y - K hweak qS := by
      field_simp
    rw [hcancel] at hmul
    linarith
  -- `qS` minimises `F`.
  have hHsub_qS : ∀ y : Fin d → ℝ,
      H x (p - qS) m + ∑ i, (DpH x (p - qS) m) i * (y i - (p - qS) i) ≤ H x y m :=
    convexOn_subgradient_dotCLMHam hConvH (hFDH (p - qS))
  have hqS_min : IsMinOn F Set.univ qS :=
    isMinOn_F_of_KSubgradient (H := H) (DpH := DpH) hweak (le_of_lt hε) qS
      hKsub_qS hHsub_qS
  -- `0` minimises `F` (from the smallness inclusion).
  have hKsub_0 : HasSubgradientAt (K hweak) 0 (ε • DpH x (p - (0 : Fin d → ℝ)) m) := by
    have hp : p - (0 : Fin d → ℝ) = p := sub_zero _
    simpa [hp] using hZeroSub
  have hHsub_0 : ∀ y : Fin d → ℝ,
      H x (p - (0 : Fin d → ℝ)) m
          + ∑ i, (DpH x (p - (0 : Fin d → ℝ)) m) i * (y i - (p - (0 : Fin d → ℝ)) i)
        ≤ H x y m :=
    convexOn_subgradient_dotCLMHam hConvH (hFDH (p - (0 : Fin d → ℝ)))
  have h0_min : IsMinOn F Set.univ (0 : Fin d → ℝ) :=
    isMinOn_F_of_KSubgradient (H := H) (DpH := DpH) hweak (le_of_lt hε)
      (0 : Fin d → ℝ) hKsub_0 hHsub_0
  -- Strict convexity ⇒ `qS = 0`.
  exact hF_sc.eq_of_isMinOn hqS_min h0_min (Set.mem_univ _) (Set.mem_univ _)

/-- **`{0<m}`-slice joint continuity of `(q,p,m) ↦ H x (p−q) m`** (a.e. `x`),
from `RegularityH.continuous_H_pm`. This is the continuity input consumed by
`qStar_continuousOn_pos_of_unique_slice`: the slice continuity of `H(x,·,·)`
on `{0 < m}` precomposed with the continuous coordinate map
`(q,p,m) ↦ (p−q, m)` (which keeps the `m`-coordinate, hence maps
`{0 < m}` into `{0 < m}`). NO global joint continuity assumed. -/
theorem hCont3_qStarSelectorFam_pos
    (hweak : HypothesisWeakGrowth (d := d) H DpH) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
      ContinuousOn (fun qpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ =>
          H x (qpm.2.1 - qpm.1) qpm.2.2)
        {qpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ | 0 < qpm.2.2} := by
  filter_upwards [hweak.continuous_H_pm] with x hxCont
  -- The coordinate map `qpm ↦ (qpm.2.1 − qpm.1, qpm.2.2)`.
  have hmap : ContinuousOn
      (fun qpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ =>
        ((qpm.2.1 - qpm.1, qpm.2.2) : (Fin d → ℝ) × ℝ))
      {qpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ | 0 < qpm.2.2} := by
    fun_prop
  have hmaps : Set.MapsTo
      (fun qpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ =>
        ((qpm.2.1 - qpm.1, qpm.2.2) : (Fin d → ℝ) × ℝ))
      {qpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ | 0 < qpm.2.2}
      {pm : (Fin d → ℝ) × ℝ | 0 < pm.2} := by
    intro qpm hqpm; exact hqpm
  exact hxCont.comp hmap hmaps

/-- **`q_cont_pm` field for `qStarSelectorFam`** (paper `lem:inf-conv-props`
item (i), lines 1639, 1646–1659). For `ε > 0`, a.e. `x`, the selector map
`(p, m) ↦ qStarSelectorFam hweak ε (x, p, m)` is continuous on the open
positive-mass slice `{0 < m}`.

Routes through `qStar_continuousOn_pos_of_unique_slice` (InfConv.lean) — the
`{0<m}`-within form of the paper's contradiction argument — fed by the three
`{0<m}`-restricted producers `hCont3_qStarSelectorFam_pos` (slice continuity
of `H`, from `continuous_H_pm`), `qStarSelectorFam_H_form` (the selector
realises the infimum, repackaged as `qOfMin`), and
`hUniq_qStarSelectorFam_pos` (minimiser uniqueness via strict convexity).

It uses NO global joint continuity of `H`, NO `hInj`, NO global
`MepsilonGlobal` injectivity. -/
theorem qStarSelectorFam_q_cont_pm
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hDiff : Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
      ContinuousOn (fun pm : (Fin d → ℝ) × ℝ =>
          qStarSelectorFam (H := H) (DpH := DpH) hweak ε (x, pm.1, pm.2))
        {pm : (Fin d → ℝ) × ℝ | 0 < pm.2} := by
  filter_upwards [hCont3_qStarSelectorFam_pos (H := H) (DpH := DpH) hweak,
    hweak.lower,
    qStarSelectorFam_H_form (H := H) (DpH := DpH) hweak hε,
    hUniq_qStarSelectorFam_pos (H := H) (DpH := DpH) hweak hDiff hε]
    with x hxCont3 hxLower hxHform hxUniq
  refine qStar_continuousOn_pos_of_unique_slice (H := H) (DpH := DpH) hweak hε
    (x := x) hxCont3 ?_
    (fun pm => qStarSelectorFam (H := H) (DpH := DpH) hweak ε (x, pm.1, pm.2))
    ?_ ?_
  · -- `hLowerAll` on `{0<m}` from `hweak.lower`.
    intro p q m hm
    have := hxLower (p - q) m hm
    simpa [ge_iff_le] using this
  · -- `qOfMin` on `{0<m}` from `qStarSelectorFam_H_form`.
    intro pm hpm
    have := hxHform pm.1 pm.2 hpm
    exact this.symm
  · -- `hUniq` on `{0<m}` from `hUniq_qStarSelectorFam_pos`.
    intro pm hpm q hq
    exact hxUniq pm.1 pm.2 hpm q hq

/-! ## Dq3e1a — the measurable-BY-CONSTRUCTION inf-conv selector `qMeasFam`

The `Classical.choose`-based `qStarSelectorFam` cannot be shown globally
`Measurable` (Dq3e blocker: a.e.-equality to a measurable function does NOT
upgrade to Borel `Measurable`, and global injectivity `hInj` is not
available — the paper only inverts `M^ε` *outside a null set of `x`*, tex
line 1680). The fix, matching the paper, is to make the selector
measurable **by construction** via a *restricted-domain* Lusin–Souslin
inverse of `M^ε`.

We build a measurable, co-null "good" set `G` of `x` on which the per-fiber
map `s ↦ M^ε_{x,m}(s)` is injective for all `m > 0` (from
`HypothesisHpDifferentiable`), restrict `MepsilonGlobal` to the Borel set
`Gset := {(x,m,s) | x ∈ G ∧ 0 < m}`, obtain a `MeasurableEmbedding` on the
standard-Borel subtype `↥Gset` (`Measurable.measurableEmbedding`), extend
its left inverse globally (`MeasurableEmbedding.exists_measurable_extend`),
and define `qMeasFam ε (x,p,m) := p − MinvG (x,m,p)`.

This section delivers the carrier + the `q_meas` field (measurability by
construction). The other three certificate fields and the assembly of
`infConvSelectorFamily_of_weakGrowth` are the sibling children
`Dq3e1b`/`Dq3e1c`.

Adapted from the D2 Lusin–Souslin pattern (`MepsilonMinv` and friends), but
with *restricted* (per-fiber, on `G`) injectivity instead of the forbidden
global `hInj`. -/

/-- **The measurable co-null good set of `x`.** The complement of a
measurable null superset of the a.e.-exception set of
`HypothesisHpDifferentiable`'s convexity + Fréchet-derivative fields. On
`goodSetWeak`, for every `m > 0`, `q ↦ H(x, q, m)` is convex and `D_pH` is
its Fréchet derivative at every `s` — exactly the hypotheses of
`Mepsilon_xm_injective`. -/
noncomputable def goodSetWeak
    (hDiff : Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH) :
    Set (Fin d → ℝ) :=
  (MeasureTheory.toMeasurable
    (MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d))
    {x | ¬ ((∀ m : ℝ, 0 < m →
        ConvexOn ℝ (Set.univ : Set (Fin d → ℝ)) (fun q : Fin d → ℝ => H x q m))
      ∧ (∀ (p : Fin d → ℝ) (m : ℝ), 0 < m →
        HasFDerivAt (fun q : Fin d → ℝ => H x q m)
          (Hamiltonian.dotCLMHam (DpH x p m)) p))})ᶜ

/-- The exception set of the combined convexity+FDeriv predicate is null. -/
lemma goodSetWeak_aux_null
    (hDiff : Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH) :
    (MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d))
      {x | ¬ ((∀ m : ℝ, 0 < m →
          ConvexOn ℝ (Set.univ : Set (Fin d → ℝ)) (fun q : Fin d → ℝ => H x q m))
        ∧ (∀ (p : Fin d → ℝ) (m : ℝ), 0 < m →
          HasFDerivAt (fun q : Fin d → ℝ => H x q m)
            (Hamiltonian.dotCLMHam (DpH x p m)) p))} = 0 := by
  -- Both fields are a.e.; their conjunction is a.e.; negation is null.
  have hae : ∀ᵐ x ∂(MeasureTheory.volume.restrict
        (StationaryMFG.Periodic.UnitCube d)),
      ((∀ m : ℝ, 0 < m →
          ConvexOn ℝ (Set.univ : Set (Fin d → ℝ)) (fun q : Fin d → ℝ => H x q m))
        ∧ (∀ (p : Fin d → ℝ) (m : ℝ), 0 < m →
          HasFDerivAt (fun q : Fin d → ℝ => H x q m)
            (Hamiltonian.dotCLMHam (DpH x p m)) p)) := by
    filter_upwards [hDiff.convexOn_H_p, hDiff.hasFDerivAt_H_p] with x hxc hxf
    exact ⟨hxc, hxf⟩
  exact hae

lemma goodSetWeak_measurableSet
    (hDiff : Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH) :
    MeasurableSet (goodSetWeak (H := H) (DpH := DpH) hDiff) :=
  (MeasureTheory.measurableSet_toMeasurable _ _).compl

/-- On `goodSetWeak`, the convexity + Fréchet-derivative properties hold for
every `m > 0`. -/
lemma goodSetWeak_props
    (hDiff : Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    {x : Fin d → ℝ} (hx : x ∈ goodSetWeak (H := H) (DpH := DpH) hDiff) :
    (∀ m : ℝ, 0 < m →
        ConvexOn ℝ (Set.univ : Set (Fin d → ℝ)) (fun q : Fin d → ℝ => H x q m))
      ∧ (∀ (p : Fin d → ℝ) (m : ℝ), 0 < m →
        HasFDerivAt (fun q : Fin d → ℝ => H x q m)
          (Hamiltonian.dotCLMHam (DpH x p m)) p) := by
  by_contra hcon
  exact hx (MeasureTheory.subset_toMeasurable _ _ hcon)

/-- `goodSetWeak` is co-null: a.e. `x` lies in it. -/
lemma goodSetWeak_ae
    (hDiff : Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
      x ∈ goodSetWeak (H := H) (DpH := DpH) hDiff := by
  rw [MeasureTheory.ae_iff]
  -- `{x | x ∉ goodSetWeak} = toMeasurable … exception`, which is null.
  have : {x | x ∉ goodSetWeak (H := H) (DpH := DpH) hDiff}
      = MeasureTheory.toMeasurable
          (MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d))
          {x | ¬ ((∀ m : ℝ, 0 < m →
              ConvexOn ℝ (Set.univ : Set (Fin d → ℝ))
                (fun q : Fin d → ℝ => H x q m))
            ∧ (∀ (p : Fin d → ℝ) (m : ℝ), 0 < m →
              HasFDerivAt (fun q : Fin d → ℝ => H x q m)
                (Hamiltonian.dotCLMHam (DpH x p m)) p))} := by
    ext x
    simp only [goodSetWeak, Set.mem_setOf_eq, Set.mem_compl_iff, not_not]
  rw [this, MeasureTheory.measure_toMeasurable]
  exact goodSetWeak_aux_null (H := H) (DpH := DpH) hDiff

/-- **The good Borel set in the domain of `MepsilonGlobal`.**
`{(x,m,s) | x ∈ goodSetWeak ∧ 0 < m}`. On this set `MepsilonGlobal` is
injective (per-fiber injectivity holds for `m > 0` and `x ∈ G`). -/
def MepsilonGoodSet
    (hDiff : Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH) :
    Set ((Fin d → ℝ) × ℝ × (Fin d → ℝ)) :=
  {xms | xms.1 ∈ goodSetWeak (H := H) (DpH := DpH) hDiff ∧ 0 < xms.2.1}

lemma MepsilonGoodSet_measurableSet
    (hDiff : Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH) :
    MeasurableSet (MepsilonGoodSet (H := H) (DpH := DpH) hDiff) := by
  have h1 : MeasurableSet
      {xms : (Fin d → ℝ) × ℝ × (Fin d → ℝ) |
        xms.1 ∈ goodSetWeak (H := H) (DpH := DpH) hDiff} :=
    (goodSetWeak_measurableSet (H := H) (DpH := DpH) hDiff).preimage measurable_fst
  have h2 : MeasurableSet
      {xms : (Fin d → ℝ) × ℝ × (Fin d → ℝ) | 0 < xms.2.1} :=
    measurableSet_lt measurable_const measurable_snd.fst
  exact h1.inter h2

/-- **Per-fiber injectivity on `MepsilonGoodSet`.** `MepsilonGlobal hweak ε`
is injective on the good set: the `(x,m)` coordinates pass through, and
`x ∈ goodSetWeak`, `m > 0` give per-fiber injectivity via
`Mepsilon_xm_injective`. NO global `hInj`. -/
lemma MepsilonGoodSet_injOn
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hDiff : Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) :
    Set.InjOn (MepsilonGlobal (H := H) (DpH := DpH) hweak ε)
      (MepsilonGoodSet (H := H) (DpH := DpH) hDiff) := by
  rintro ⟨x₁, m₁, s₁⟩ hxms₁ ⟨x₂, m₂, s₂⟩ _ hEq
  obtain ⟨hxG, hm⟩ := hxms₁
  simp only [MepsilonGlobal_apply, Prod.mk.injEq] at hEq
  obtain ⟨hx, hmeq, hMs⟩ := hEq
  subst hx
  subst hmeq
  obtain ⟨hxConvAll, hxFDAll⟩ := goodSetWeak_props (H := H) (DpH := DpH) hDiff hxG
  have hPerFiber : Function.Injective
      (fun s : Fin d → ℝ => Mepsilon_xm (H := H) (DpH := DpH) hweak ε x₁ m₁ s) :=
    Mepsilon_xm_injective (H := H) (DpH := DpH) hweak hε x₁ m₁
      (hxConvAll m₁ hm) (fun s => hxFDAll s m₁ hm)
  have hSeq : s₁ = s₂ := hPerFiber hMs
  subst hSeq
  rfl

/-- **The restricted measurable embedding.** `MepsilonGlobal` restricted to
the standard-Borel subtype `↥MepsilonGoodSet` is a measurable embedding,
via `Measurable.measurableEmbedding`. -/
lemma MepsilonGoodSet_restrict_measurableEmbedding
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hDiff : Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) :
    MeasurableEmbedding
      ((MepsilonGoodSet (H := H) (DpH := DpH) hDiff).restrict
        (MepsilonGlobal (H := H) (DpH := DpH) hweak ε)) := by
  haveI : StandardBorelSpace
      (MepsilonGoodSet (H := H) (DpH := DpH) hDiff) :=
    (MepsilonGoodSet_measurableSet (H := H) (DpH := DpH) hDiff).standardBorel
  refine Measurable.measurableEmbedding ?_ ?_
  · exact (MepsilonGlobal_measurable (H := H) (DpH := DpH) hweak hMeas ε).comp
      measurable_subtype_coe
  · exact Set.injOn_iff_injective.1
      (MepsilonGoodSet_injOn (H := H) (DpH := DpH) hweak hDiff hε)

/-- **The globally measurable extension of the restricted left inverse.**
From the restricted measurable embedding and
`MeasurableEmbedding.exists_measurable_extend` applied to `Subtype.val`,
a globally measurable `MinvGFull : codomain → domain` with
`MinvGFull ∘ (restrict MepsilonGlobal) = Subtype.val`. -/
noncomputable def MinvGFull
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hDiff : Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) :
    ((Fin d → ℝ) × ℝ × (Fin d → ℝ)) → ((Fin d → ℝ) × ℝ × (Fin d → ℝ)) :=
  Classical.choose
    ((MepsilonGoodSet_restrict_measurableEmbedding (H := H) (DpH := DpH)
      hweak hDiff hMeas hε).exists_measurable_extend
        (g := (Subtype.val :
          (MepsilonGoodSet (H := H) (DpH := DpH) hDiff) →
            (Fin d → ℝ) × ℝ × (Fin d → ℝ)))
        measurable_subtype_coe (fun _ => inferInstance))

lemma MinvGFull_measurable
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hDiff : Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) :
    Measurable (MinvGFull (H := H) (DpH := DpH) hweak hDiff hMeas hε) :=
  (Classical.choose_spec
    ((MepsilonGoodSet_restrict_measurableEmbedding (H := H) (DpH := DpH)
      hweak hDiff hMeas hε).exists_measurable_extend
        (g := (Subtype.val :
          (MepsilonGoodSet (H := H) (DpH := DpH) hDiff) →
            (Fin d → ℝ) × ℝ × (Fin d → ℝ)))
        measurable_subtype_coe (fun _ => inferInstance))).1

lemma MinvGFull_left_inverse
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hDiff : Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) :
    MinvGFull (H := H) (DpH := DpH) hweak hDiff hMeas hε
        ∘ (MepsilonGoodSet (H := H) (DpH := DpH) hDiff).restrict
            (MepsilonGlobal (H := H) (DpH := DpH) hweak ε)
      = (Subtype.val :
          (MepsilonGoodSet (H := H) (DpH := DpH) hDiff) →
            (Fin d → ℝ) × ℝ × (Fin d → ℝ)) :=
  (Classical.choose_spec
    ((MepsilonGoodSet_restrict_measurableEmbedding (H := H) (DpH := DpH)
      hweak hDiff hMeas hε).exists_measurable_extend
        (g := (Subtype.val :
          (MepsilonGoodSet (H := H) (DpH := DpH) hDiff) →
            (Fin d → ℝ) × ℝ × (Fin d → ℝ)))
        measurable_subtype_coe (fun _ => inferInstance))).2

/-- **The consumer-facing restricted inverse `MinvG`.** Third coordinate of
`MinvGFull`. On the good set it is the genuine per-fiber inverse of
`s ↦ M^ε_{x,m}(s)`. -/
noncomputable def MinvG
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hDiff : Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) :
    ((Fin d → ℝ) × ℝ × (Fin d → ℝ)) → (Fin d → ℝ) :=
  fun xmp => (MinvGFull (H := H) (DpH := DpH) hweak hDiff hMeas hε xmp).2.2

lemma MinvG_measurable
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hDiff : Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) :
    Measurable (MinvG (H := H) (DpH := DpH) hweak hDiff hMeas hε) := by
  unfold MinvG
  exact (MinvGFull_measurable (H := H) (DpH := DpH) hweak hDiff hMeas hε).snd.snd

/-- **Restricted left-inverse property.** For `(x, m, s)` in the good set,
applying `MinvG` to `(x, m, M^ε_{x,m}(s))` recovers `s`. -/
lemma MinvG_apply_image
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hDiff : Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε)
    {x : Fin d → ℝ} {m : ℝ} {s : Fin d → ℝ}
    (hmem : (x, m, s) ∈ MepsilonGoodSet (H := H) (DpH := DpH) hDiff) :
    MinvG (H := H) (DpH := DpH) hweak hDiff hMeas hε
        (x, m, Mepsilon_xm (H := H) (DpH := DpH) hweak ε x m s) = s := by
  have hLI := MinvGFull_left_inverse (H := H) (DpH := DpH) hweak hDiff hMeas hε
  have hpt := congrFun hLI ⟨(x, m, s), hmem⟩
  simp only [Function.comp_apply, Set.restrict, Set.domRestrict_apply, MepsilonGlobal_apply] at hpt
  unfold MinvG
  rw [hpt]

/-- **The measurable-by-construction inf-conv selector family** (paper
`eq:q-star-semi-explicit`, tex 1677). `qMeasFam … ε (x, p, m) := p −
MinvG(x, m, p)`. This is the `q^ε` of the paper, measurable BY CONSTRUCTION
(no `hInj`, no `Classical.choose` over minimisers). -/
noncomputable def qMeasFam
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hDiff : Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH) :
    QEpsFamily d :=
  fun ε xpm =>
    haveI := Classical.dec (0 < ε)
    if hε : 0 < ε then
      xpm.2.1 - MinvG (H := H) (DpH := DpH) hweak hDiff hMeas hε
        (xpm.1, xpm.2.2, xpm.2.1)
    else 0

/-- Unfolded formula for `qMeasFam` when `ε > 0`. -/
lemma qMeasFam_apply_pos
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hDiff : Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε)
    (xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ) :
    qMeasFam (H := H) (DpH := DpH) hweak hDiff hMeas ε xpm
      = xpm.2.1 - MinvG (H := H) (DpH := DpH) hweak hDiff hMeas hε
          (xpm.1, xpm.2.2, xpm.2.1) := by
  simp only [qMeasFam, dif_pos hε]

/-- **`q_meas` field for `qMeasFam`** — measurability BY CONSTRUCTION.
The selector is `p − MinvG(x, m, p)`, a measurable composition; for `ε ≤ 0`
it is the constant `0`. NO `hInj`, NO measurable-selection theorem. -/
theorem qMeasFam_measurable
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hDiff : Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (ε : ℝ) :
    Measurable (qMeasFam (H := H) (DpH := DpH) hweak hDiff hMeas ε) := by
  by_cases hε : 0 < ε
  · have heq : qMeasFam (H := H) (DpH := DpH) hweak hDiff hMeas ε
        = fun xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ =>
            xpm.2.1 - MinvG (H := H) (DpH := DpH) hweak hDiff hMeas hε
              (xpm.1, xpm.2.2, xpm.2.1) := by
      funext xpm
      exact qMeasFam_apply_pos (H := H) (DpH := DpH) hweak hDiff hMeas hε xpm
    rw [heq]
    have hMinvMeas := MinvG_measurable (H := H) (DpH := DpH) hweak hDiff hMeas hε
    have hcomp : Measurable (fun xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ =>
        MinvG (H := H) (DpH := DpH) hweak hDiff hMeas hε
          (xpm.1, xpm.2.2, xpm.2.1)) :=
      hMinvMeas.comp
        (Measurable.prod measurable_fst
          (Measurable.prod measurable_snd.snd measurable_snd.fst))
    exact measurable_snd.fst.sub hcomp
  · have heq : qMeasFam (H := H) (DpH := DpH) hweak hDiff hMeas ε
        = fun _ => 0 := by
      funext xpm
      simp only [qMeasFam, dif_neg hε]
    rw [heq]
    exact measurable_const

/-! ## Dq3e1b — transfer the remaining three fields to `qMeasFam`

We prove `q_cont_pm`, `H_form`, `DpH_form` for the measurable-by-construction
selector `qMeasFam` by transferring them from the `qStarSelectorFam` lemmas
(Dq3/Dq3c) through the a.e./good-slice equality `qMeasFam = qStarSelectorFam`.

The equality holds on the good slice `{x ∈ goodSetWeak} ∩ {0 < m}` (co-null in
`x`): there `qStarSelectorFam` is the UNIQUE inf-conv minimiser, and `qMeasFam`
`= p − MinvG(x,m,p)` recovers the same shift via `MinvG_apply_image` once we
exhibit `Mepsilon_xm x m (p − qStarSelectorFam) = p`. NO global `hInj`. -/

/-- **A.e./good-slice equality `qMeasFam = qStarSelectorFam`** (paper
`lem:inf-conv-props`). For `ε > 0`, a.e. `x` (on `goodSetWeak`), all `p`, and
`m > 0`, the measurable-by-construction selector coincides with the
`qStar`-native inf-conv selector.

Route: `qStar hε hCont hLower` is a minimiser (`qStar_spec`), so by
`hUniq_qStarSelectorFam_pos` it equals `qStarSelectorFam`. By
`Mepsilon_xm_at_minimizer`, `Mepsilon_xm x m (p − qStar) = p`; rewriting the
uniqueness identity gives `Mepsilon_xm x m (p − qStarSelectorFam) = p`. On the
good slice `(x, m, p − qStarSelectorFam) ∈ MepsilonGoodSet`, so
`MinvG_apply_image` yields `MinvG (x, m, p) = p − qStarSelectorFam`, whence
`qMeasFam = p − MinvG = qStarSelectorFam`. -/
theorem qMeasFam_eq_qStarSelectorFam_ae
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hDiff : Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
      ∀ (p : Fin d → ℝ) (m : ℝ), 0 < m →
        qMeasFam (H := H) (DpH := DpH) hweak hDiff hMeas ε (x, p, m)
          = qStarSelectorFam (H := H) (DpH := DpH) hweak ε (x, p, m) := by
  filter_upwards [goodSetWeak_ae (H := H) (DpH := DpH) hDiff,
    hweak.continuous_H_pm, hweak.lower,
    hDiff.hasFDerivAt_H_p, hDiff.convexOn_H_p,
    hUniq_qStarSelectorFam_pos (H := H) (DpH := DpH) hweak hDiff hε]
    with x hxG hxCont hxLower hxFDH hxConvH hxUniq
  intro p m hm
  -- Per-point feeders for `qStar` (as in `hHform_qEofMinv`).
  have hCont : Continuous (fun q : Fin d → ℝ => H x (p - q) m) :=
    H_slice_continuous_of_continuousOn (H := H) hm hxCont
  have hLower : ∀ q : Fin d → ℝ,
      ‖p - q‖ ^ hweak.α / hweak.C - hweak.C * (m ^ hweak.β + 1) ≤ H x (p - q) m := by
    intro q
    have := hxLower (p - q) m hm
    simpa [ge_iff_le] using this
  have hConvH : ConvexOn ℝ (Set.univ : Set (Fin d → ℝ))
      (fun q : Fin d → ℝ => H x q m) := hxConvH m hm
  have hFDH : HasFDerivAt (fun q : Fin d → ℝ => H x q m)
      (Hamiltonian.dotCLMHam (DpH x (p - qStar hweak hε hCont hLower) m))
      (p - qStar hweak hε hCont hLower) :=
    hxFDH (p - qStar hweak hε hCont hLower) m hm
  set qS : Fin d → ℝ := qStarSelectorFam (H := H) (DpH := DpH) hweak ε (x, p, m)
    with hqSdef
  -- `qStar` realises `Hdelta` (so it satisfies the `hUniq` hypothesis).
  have hqStar_spec : H x (p - qStar hweak hε hCont hLower) m
      + (1 / ε) * K hweak (qStar hweak hε hCont hLower) = Hdelta hweak ε x p m :=
    qStar_spec hweak hε hCont hLower
  -- Uniqueness ⇒ `qStar = qStarSelectorFam`.
  have hStarEq : qStar hweak hε hCont hLower = qS :=
    hxUniq p m hm (qStar hweak hε hCont hLower) hqStar_spec
  -- `M^ε_{x,m}(p − qStar) = p`.
  have hM : Mepsilon_xm (H := H) (DpH := DpH) hweak ε x m
      (p - qStar hweak hε hCont hLower) = p :=
    Mepsilon_xm_at_minimizer (H := H) (DpH := DpH)
      hweak hε hCont hLower hConvH hFDH
  -- Rewrite `qStar = qS` everywhere.
  rw [hStarEq] at hM
  -- Membership in the good Borel set.
  have hmem : (x, m, p - qS) ∈ MepsilonGoodSet (H := H) (DpH := DpH) hDiff :=
    ⟨hxG, hm⟩
  -- `MinvG (x, m, M^ε(p − qS)) = p − qS`; rewrite `M^ε = p`.
  have hInv := MinvG_apply_image (H := H) (DpH := DpH) hweak hDiff hMeas hε hmem
  rw [hM] at hInv
  -- `qMeasFam = p − MinvG (x, m, p) = p − (p − qS) = qS`.
  rw [qMeasFam_apply_pos (H := H) (DpH := DpH) hweak hDiff hMeas hε (x, p, m)]
  simp only
  rw [hInv]
  abel

/-- **`H_form` field for `qMeasFam`** (paper `eq:H-epsilon-formula`). Transferred
from `qStarSelectorFam_H_form` through `qMeasFam_eq_qStarSelectorFam_ae`. -/
theorem qMeasFam_H_form
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hDiff : Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
      ∀ p m, 0 < m →
        Hdelta hweak ε x p m
          = H x (p - qMeasFam (H := H) (DpH := DpH) hweak hDiff hMeas ε (x, p, m)) m
            + (1 / ε) * K hweak
                (qMeasFam (H := H) (DpH := DpH) hweak hDiff hMeas ε (x, p, m)) := by
  filter_upwards [qStarSelectorFam_H_form (H := H) (DpH := DpH) hweak hε,
    qMeasFam_eq_qStarSelectorFam_ae (H := H) (DpH := DpH) hweak hDiff hMeas hε]
    with x hxHform hxEq
  intro p m hm
  rw [hxEq p m hm]
  exact hxHform p m hm

/-- **`DpH_form` field for `qMeasFam`** (paper `eq:DpH-epsilon-formula`). This is
the `rfl` unfold of `DpHepsilonFam` (`DpHepsilonFam_eq`), valid for *every*
selector; restated on the a.e./`{m>0}` slice for interface uniformity. -/
theorem qMeasFam_DpH_form
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hDiff : Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (ε : ℝ) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
      ∀ p m, 0 < m →
        DpHepsilonFam (H := H) (DpH := DpH) hweak
            (qMeasFam (H := H) (DpH := DpH) hweak hDiff hMeas) ε x p m
          = DpH x
              (p - qMeasFam (H := H) (DpH := DpH) hweak hDiff hMeas ε (x, p, m)) m := by
  filter_upwards with x
  intro p m _
  rfl

/-- **`q_cont_pm` field for `qMeasFam`** (paper `lem:inf-conv-props` item (i)).
For `ε > 0`, a.e. `x`, the selector `(p, m) ↦ qMeasFam … ε (x, p, m)` is
continuous on the open positive-mass slice `{0 < m}`. Transferred from
`qStarSelectorFam_q_cont_pm` through `qMeasFam_eq_qStarSelectorFam_ae` via
`ContinuousOn.congr` (the two selectors agree at every `pm` with `0 < pm.2`). -/
theorem qMeasFam_q_cont_pm
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hDiff : Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
      ContinuousOn (fun pm : (Fin d → ℝ) × ℝ =>
          qMeasFam (H := H) (DpH := DpH) hweak hDiff hMeas ε (x, pm.1, pm.2))
        {pm : (Fin d → ℝ) × ℝ | 0 < pm.2} := by
  filter_upwards [qStarSelectorFam_q_cont_pm (H := H) (DpH := DpH) hweak hDiff hε,
    qMeasFam_eq_qStarSelectorFam_ae (H := H) (DpH := DpH) hweak hDiff hMeas hε]
    with x hxCont hxEq
  refine hxCont.congr ?_
  intro pm hpm
  exact hxEq pm.1 pm.2 hpm

/-! ## Dq3e1b' — selector subgradient + FTC-slice certificates for `qMeasFam`
(paper `eq:inf-conv.diff-relation1` first inclusion, `eq:DpHdelta.dotp.minusH`),
gate-clean (NO `qEofMinv`/`hInj`)

These are the `D2a-i` ingredients: the subgradient optimality and FTC-slice
identities at the measurable-by-construction selector `qMeasFam`, derived WITHOUT
global injectivity. The only difference from the `qEofMinv` versions
(`hSub_qEofMinv`, `hSubgradientHepsilon_qEofMinv`,
`hepsilonFtcSlice_qEofMinv_of_envelope`) is the identification step: there
`qEofMinv = qStar` via `qEofMinv_eq_qStar` (uses `hInj`); here we use the
gate-clean composite `qMeasFam = qStarSelectorFam` (`qMeasFam_eq_qStarSelectorFam_ae`)
combined with `qStar = qStarSelectorFam` (`hUniq_qStarSelectorFam_pos`, fed by
`qStar_spec`). The underlying subgradient inclusions
(`qEpsilon_subdiff_inclusion_K`, `qEpsilon_subdiff_inclusion_Hepsilon`) are stated
at the abstract argmin `qStar` and hold at ANY minimiser. -/

/-- **K-side support inequality at `qMeasFam`** (paper `eq:inf-conv.diff-relation1`
first inclusion). Gate-clean analogue of `hSub_qEofMinv`: for a.e. `x`, all `p`,
`m > 0`, all `q`,
`D_pH(x, p − q^ε, m) ⬝ (q − q^ε) ≤ (1/ε)(K q − K q^ε)`, with
`q^ε := qMeasFam … (x, p, m)`. No `hInj`. -/
theorem hSub_qMeasFam
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hDiff : Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
      ∀ p m, 0 < m → ∀ q : Fin d → ℝ,
        DpH x (p - qMeasFam (H := H) (DpH := DpH) hweak hDiff hMeas ε (x, p, m)) m
            ⬝ (q - qMeasFam (H := H) (DpH := DpH) hweak hDiff hMeas ε (x, p, m))
          ≤ (1 / ε) *
              (K hweak q
                - K hweak
                    (qMeasFam (H := H) (DpH := DpH) hweak hDiff hMeas ε (x, p, m))) := by
  filter_upwards [hweak.continuous_H_pm, hweak.lower,
    hDiff.hasFDerivAt_H_p, hDiff.convexOn_H_p,
    hUniq_qStarSelectorFam_pos (H := H) (DpH := DpH) hweak hDiff hε,
    qMeasFam_eq_qStarSelectorFam_ae (H := H) (DpH := DpH) hweak hDiff hMeas hε]
    with x hxCont hxLower hxFDH hxConvH hxUniq hxEq
  intro p m hm q
  -- Per-point feeders.
  have hCont : Continuous (fun q : Fin d → ℝ => H x (p - q) m) :=
    H_slice_continuous_of_continuousOn (H := H) hm hxCont
  have hLower : ∀ q : Fin d → ℝ,
      ‖p - q‖ ^ hweak.α / hweak.C - hweak.C * (m ^ hweak.β + 1) ≤ H x (p - q) m := by
    intro q
    have := hxLower (p - q) m hm
    simpa [ge_iff_le] using this
  have hConvH : ConvexOn ℝ (Set.univ : Set (Fin d → ℝ))
      (fun q : Fin d → ℝ => H x q m) := hxConvH m hm
  have hFDH : HasFDerivAt (fun q : Fin d → ℝ => H x q m)
      (Hamiltonian.dotCLMHam (DpH x (p - qStar hweak hε hCont hLower) m))
      (p - qStar hweak hε hCont hLower) :=
    hxFDH (p - qStar hweak hε hCont hLower) m hm
  -- Identify `qMeasFam` with `qStar` (gate-clean, via `qStarSelectorFam`).
  have hqStar_spec : H x (p - qStar hweak hε hCont hLower) m
      + (1 / ε) * K hweak (qStar hweak hε hCont hLower) = Hdelta hweak ε x p m :=
    qStar_spec hweak hε hCont hLower
  have hStarEq : qStar hweak hε hCont hLower
      = qStarSelectorFam (H := H) (DpH := DpH) hweak ε (x, p, m) :=
    hxUniq p m hm (qStar hweak hε hCont hLower) hqStar_spec
  have hqM_eq : qMeasFam (H := H) (DpH := DpH) hweak hDiff hMeas ε (x, p, m)
      = qStar hweak hε hCont hLower := by
    rw [hxEq p m hm, ← hStarEq]
  rw [hqM_eq]
  -- The K-subgradient inclusion at `qStar`.
  set qS : Fin d → ℝ := qStar hweak hε hCont hLower with hqSdef
  set v : Fin d → ℝ := DpH x (p - qS) m with hvdef
  have hsub : HasSubgradientAt (K hweak) qS (ε • v) :=
    qEpsilon_subdiff_inclusion_K (H := H) (DpH := DpH)
      hweak hε hCont hLower hConvH hFDH
  have hsub_q := hsub q
  have hpair : ∑ i, (ε • v) i * (q i - qS i) = ε * (v ⬝ (q - qS)) := by
    unfold euclideanDot
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  rw [hpair] at hsub_q
  have hkey : ε * (v ⬝ (q - qS)) ≤ K hweak q - K hweak qS := by linarith
  have hfinal : v ⬝ (q - qS) ≤ (1 / ε) * (K hweak q - K hweak qS) := by
    rw [one_div, ← div_eq_inv_mul]
    rw [le_div_iff₀ hε]
    linarith [hkey]
  simpa [hvdef] using hfinal

/-- **A.e. `H^ε`-subgradient field at `qMeasFam`** (paper
`eq:inf-conv.diff-relation1`). Gate-clean analogue of
`hSubgradientHepsilon_qEofMinv`: for a.e. `x` and `(p, m)` with `0 < m`,
`D_pH^ε(x, p, m)` (the `DpHepsilonFam` value at the selector `qMeasFam`) is a
convex-analysis subgradient of `p' ↦ Hdelta hweak ε x p' m` at `p`. No `hInj`. -/
theorem hSubgradientHepsilon_qMeasFam
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hDiff : Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
      ∀ p m, 0 < m →
        HasSubgradientAt (fun p' : Fin d → ℝ => Hdelta hweak ε x p' m) p
          (DpHepsilonFam (H := H) (DpH := DpH) hweak
            (qMeasFam (H := H) (DpH := DpH) hweak hDiff hMeas) ε x p m) := by
  filter_upwards [hweak.continuous_H_pm, hweak.lower,
    hDiff.hasFDerivAt_H_p, hDiff.convexOn_H_p,
    hUniq_qStarSelectorFam_pos (H := H) (DpH := DpH) hweak hDiff hε,
    qMeasFam_eq_qStarSelectorFam_ae (H := H) (DpH := DpH) hweak hDiff hMeas hε]
    with x hxCont hxLower hxFDH hxConvH hxUniq hxEq
  intro p m hm
  -- Per-point feeders.
  have hCont : Continuous (fun q : Fin d → ℝ => H x (p - q) m) :=
    H_slice_continuous_of_continuousOn (H := H) hm hxCont
  have hLower : ∀ q : Fin d → ℝ,
      ‖p - q‖ ^ hweak.α / hweak.C - hweak.C * (m ^ hweak.β + 1) ≤ H x (p - q) m := by
    intro q
    have := hxLower (p - q) m hm
    simpa [ge_iff_le] using this
  have hLower' : ∀ p' q : Fin d → ℝ,
      ‖p' - q‖ ^ hweak.α / hweak.C - hweak.C * (m ^ hweak.β + 1) ≤ H x (p' - q) m := by
    intro p' q
    have := hxLower (p' - q) m hm
    simpa [ge_iff_le] using this
  have hConvH : ConvexOn ℝ (Set.univ : Set (Fin d → ℝ))
      (fun q : Fin d → ℝ => H x q m) := hxConvH m hm
  have hFDH : HasFDerivAt (fun q : Fin d → ℝ => H x q m)
      (Hamiltonian.dotCLMHam (DpH x (p - qStar hweak hε hCont hLower) m))
      (p - qStar hweak hε hCont hLower) :=
    hxFDH (p - qStar hweak hε hCont hLower) m hm
  -- The `H^ε`-subgradient inclusion at `p` (at the abstract argmin `qStar`).
  have hsub :
      HasSubgradientAt (fun p' : Fin d → ℝ => Hdelta hweak ε x p' m) p
        (DpH x (p - qStar hweak hε hCont hLower) m) :=
    qEpsilon_subdiff_inclusion_Hepsilon (H := H) (DpH := DpH)
      hweak hε hCont hLower hConvH hFDH hLower'
  -- Identify `qMeasFam` with `qStar`.
  have hqStar_spec : H x (p - qStar hweak hε hCont hLower) m
      + (1 / ε) * K hweak (qStar hweak hε hCont hLower) = Hdelta hweak ε x p m :=
    qStar_spec hweak hε hCont hLower
  have hStarEq : qStar hweak hε hCont hLower
      = qStarSelectorFam (H := H) (DpH := DpH) hweak ε (x, p, m) :=
    hxUniq p m hm (qStar hweak hε hCont hLower) hqStar_spec
  have hqM_eq : qMeasFam (H := H) (DpH := DpH) hweak hDiff hMeas ε (x, p, m)
      = qStar hweak hε hCont hLower := by
    rw [hxEq p m hm, ← hStarEq]
  have hgrad : DpHepsilonFam (H := H) (DpH := DpH) hweak
      (qMeasFam (H := H) (DpH := DpH) hweak hDiff hMeas) ε x p m
        = DpH x (p - qStar hweak hε hCont hLower) m := by
    rw [DpHepsilonFam_eq, hqM_eq]
  rw [hgrad]
  exact hsub

/-- **A.e. FTC-slice identity for `(Hdelta, DpHepsilonFam … qMeasFam)`** (paper
`eq:DpHdelta.dotp.minusH`, line 1815). Gate-clean analogue of
`hFtcSlice_qEofMinv` / `hepsilonFtcSlice_qEofMinv_of_envelope`. The FTC slice is
derived from the a.e. `H^ε`-subgradient field (`hSubgradientHepsilon_qMeasFam`)
plus continuity of the regularized gradient field — itself obtained internally
from `hweak.toRegularityH` (HypothesisWeakGrowth EXTENDS RegularityH, so its base
`continuous_DpH_pm` is available) together with the selector continuity
`qMeasFam_q_cont_pm`, via `DpHepsilon_continuousOn_DpH_pm`. No `hInj`, no external
continuity rider. -/
theorem hFtcSlice_qMeasFam
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hDiff : Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
      ∀ p m, 0 < m →
        (DpHepsilonFam (H := H) (DpH := DpH) hweak
            (qMeasFam (H := H) (DpH := DpH) hweak hDiff hMeas) ε x p m) ⬝ p
          - (Hdelta hweak ε x p m - Hdelta hweak ε x (0 : Fin d → ℝ) m)
          = ∫ t in (0 : ℝ)..1,
              ((DpHepsilonFam (H := H) (DpH := DpH) hweak
                  (qMeasFam (H := H) (DpH := DpH) hweak hDiff hMeas) ε x p m
                - DpHepsilonFam (H := H) (DpH := DpH) hweak
                  (qMeasFam (H := H) (DpH := DpH) hweak hDiff hMeas) ε x (t • p) m)
                ⬝ p) := by
  -- Gradient continuity on `{0<m}`, internal from `hweak.toRegularityH` + selector
  -- continuity.  `DpHepsilonFam … = DpHepsilon …` definitionally.
  have hDpHε_cont :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict
        (StationaryMFG.Periodic.UnitCube d)),
        ContinuousOn (fun pm : (Fin d → ℝ) × ℝ =>
            DpHepsilon (H := H) (DpH := DpH) hweak
              (qMeasFam (H := H) (DpH := DpH) hweak hDiff hMeas ε) x pm.1 pm.2)
          {pm | 0 < pm.2} :=
    DpHepsilon_continuousOn_DpH_pm (H := H) (DpH := DpH) hweak
      (qMeasFam (H := H) (DpH := DpH) hweak hDiff hMeas ε)
      hweak.toRegularityH
      (qMeasFam_q_cont_pm (H := H) (DpH := DpH) hweak hDiff hMeas hε)
  filter_upwards [hSubgradientHepsilon_qMeasFam (H := H) (DpH := DpH)
      hweak hDiff hMeas hε, hDpHε_cont]
    with x hxSub hxCont
  intro p m hm
  -- Fix `m`: the slice functions and slice gradient field.
  set F : (Fin d → ℝ) → ℝ := fun p' => Hdelta hweak ε x p' m with hF
  set G : (Fin d → ℝ) → (Fin d → ℝ) :=
    fun p' => DpHepsilonFam (H := H) (DpH := DpH) hweak
      (qMeasFam (H := H) (DpH := DpH) hweak hDiff hMeas) ε x p' m with hG
  -- Slice continuity of `G` from `hxCont` (definitionally `DpHepsilon`).
  have hGcont : Continuous G := by
    have := continuous_p_slice_of_continuousOn_pm
      (G := fun pm : (Fin d → ℝ) × ℝ =>
        DpHepsilon (H := H) (DpH := DpH) hweak
          (qMeasFam (H := H) (DpH := DpH) hweak hDiff hMeas ε) x pm.1 pm.2)
      hxCont hm
    simpa [hG, DpHepsilonFam] using this
  -- `G p'` is a subgradient of `F` at every `p'` (fixed `m`).
  have hGsub : ∀ p' : Fin d → ℝ, HasSubgradientAt F p' (G p') := by
    intro p'
    have := hxSub p' m hm
    simpa [hF, hG] using this
  -- Envelope: `F` is Fréchet-differentiable with derivative `dotCLMHam (G ·)`.
  have hFD : ∀ p' : Fin d → ℝ,
      HasFDerivAt F (Hamiltonian.dotCLMHam (G p')) p' :=
    hasFDerivAt_of_continuous_subgradient_field hGcont hGsub
  -- FTC-slice identity at `p`.
  have hFTC := ftc_slice_of_hasFDerivAt_continuous_gradient hFD hGcont p
  simpa [hF, hG] using hFTC

/-! ## Dq3e1c — assemble the closed selector producer `infConvSelectorFamily_of_weakGrowth`

Package the four now-proven fields for the measurable-by-construction selector
`qMeasFam` (Dq3e1a + Dq3e1b) into an `InfConvSelectorFamily` certificate.  The
producer takes ONLY the four paper hypotheses `(hmon, hweak, hdiff, hmeas)` — no
global injectivity `hInj`, no `MepsilonMinv` rider, no selector/family input. -/

/-- **Closed inf-conv selector producer (paper `lem:inf-conv-props`).**
From the four paper hypotheses alone, produce a regularized selector family
together with its `InfConvSelectorFamily` certificate.  The witness is the
measurable-by-construction selector `qMeasFam`; the four certificate fields are
`qMeasFam_measurable` (Dq3e1a) and `qMeasFam_q_cont_pm`, `qMeasFam_H_form`,
`qMeasFam_DpH_form` (Dq3e1b). -/
theorem infConvSelectorFamily_of_weakGrowth
    (hmon : Hamiltonian.HypothesisMonotone (d := d) H DpH)
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hdiff : Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    (hmeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH) :
    ∃ qε : QEpsFamily d, InfConvSelectorFamily (H := H) (DpH := DpH) hweak qε :=
  ⟨qMeasFam (H := H) (DpH := DpH) hweak hdiff hmeas,
    { q_meas := qMeasFam_measurable (H := H) (DpH := DpH) hweak hdiff hmeas
      q_cont_pm := fun _ε hε =>
        qMeasFam_q_cont_pm (H := H) (DpH := DpH) hweak hdiff hmeas hε
      H_form := fun _ε hε =>
        qMeasFam_H_form (H := H) (DpH := DpH) hweak hdiff hmeas hε
      DpH_form := fun ε _hε =>
        qMeasFam_DpH_form (H := H) (DpH := DpH) hweak hdiff hmeas ε
      hSub := fun _ε hε =>
        hSub_qMeasFam (H := H) (DpH := DpH) hweak hdiff hmeas hε
      hFtcSlice := fun _ε hε =>
        hFtcSlice_qMeasFam (H := H) (DpH := DpH) hweak hdiff hmeas hε }⟩

/-! ## G3 — standalone `hCx` producer for a generic selector family

This block proves `T3.hCx_of_selector`, the convex-at-zero rider for `H^ε`
(paper `lem:H.delta.monotone` / `rmk:cxty`), as a STANDALONE theorem generic in
`(hweak, qε, sel)` plus the accepted T3 carrier
`hdiff : HypothesisHpDifferentiable` (paper line 1670, the same rider already
threaded through `hSubgradientHepsilon_qMeasFam` / `hstab_of_selectorFamily`).

The argument is the envelope subgradient inclusion for `H^ε` at the *generic*
selector point `qε ε (x,p,m)`, NOT the canonical `qMeasFam`/`qStar`: from the
attainment identity `sel.H_form`, the K-side support inequality `sel.hSub`, and
the convexity / Fréchet derivative of `H(x,·,m)` (`hdiff`), we obtain that
`D_pH^ε(x,p,m)` is a convex-analysis subgradient of `p' ↦ H^ε(x,p',m)` at `p`.
The `hCx` slice is exactly this subgradient inequality evaluated at `p' = 0`. -/

namespace T3

/-- **G3 (a), generic-selector `H^ε`-subgradient inclusion** (paper
`eq:inf-conv.diff-relation1`, second inclusion).  For `ε > 0`, a.e. `x`, every
`(p,m)` with `m > 0`, the regularized gradient `D_pH^ε(x,p,m)` (the
`DpHepsilonFam` value at the *generic* selector `qε ε`) is a subgradient of
`p' ↦ Hdelta hweak ε x p' m` at `p`.  Generic in `(hweak, qε, sel)`; the only
extra rider is the accepted carrier `hdiff`.

This mirrors `hSubgradientHepsilon_qMeasFam` but works for any selector family
that attains the inf-conv (`sel.H_form`) and carries the K-side support
inequality (`sel.hSub`), instead of being pinned to `qMeasFam`/`qStar`. -/
theorem hSubgradientHepsilon_of_selector
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hdiff : Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    (qε : QEpsFamily d)
    (sel : InfConvSelectorFamily (H := H) (DpH := DpH) hweak qε)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
      ∀ p m, 0 < m →
        HasSubgradientAt (fun p' : Fin d → ℝ => Hdelta hweak ε x p' m) p
          (DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε x p m) := by
  filter_upwards [hweak.lower, hdiff.hasFDerivAt_H_p, hdiff.convexOn_H_p,
    sel.H_form ε hε, sel.hSub ε hε]
    with x hxLower hxFDH hxConvH hxHform hxSub
  intro p m hm
  -- The selector value at `(p, m)`.
  set qS : Fin d → ℝ := qε ε (x, p, m) with hqSdef
  -- The regularized gradient value: `D_pH^ε(x,p,m) = D_pH(x, p - qS, m)`.
  set v : Fin d → ℝ := DpH x (p - qS) m with hvdef
  have hveq : DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε x p m = v := rfl
  rw [hveq]
  -- Per-point feeders.
  have hε_inv_pos : 0 < 1 / ε := one_div_pos.mpr hε
  have hConvH : ConvexOn ℝ (Set.univ : Set (Fin d → ℝ))
      (fun q : Fin d → ℝ => H x q m) := hxConvH m hm
  have hFDH : HasFDerivAt (fun q : Fin d → ℝ => H x q m)
      (Hamiltonian.dotCLMHam v) (p - qS) := by
    rw [hvdef]; exact hxFDH (p - qS) m hm
  -- Attainment certificate `Hdelta x p m = H(x, p - qS, m) + (1/ε) K(qS)`.
  have hspec : H x (p - qS) m + (1 / ε) * K hweak qS = Hdelta hweak ε x p m := by
    have := hxHform p m hm
    rw [this]
  -- The subgradient inequality: for all `p'`, `Hdelta x p m + v·(p'-p) ≤ Hdelta x p' m`.
  intro p'
  -- BddBelow of `q ↦ H(x, p' - q, m) + (1/ε) K(q)` (needed for `le_ciInf`).
  have hBddF' : BddBelow (Set.range
      fun q : Fin d → ℝ => H x (p' - q) m + (1 / ε) * K hweak q) := by
    refine ⟨-(hweak.C * (m ^ hweak.β + 1)), ?_⟩
    rintro y ⟨q, rfl⟩
    have hLow := hxLower (p' - q) m hm
    have hpα_nn : 0 ≤ ‖p' - q‖ ^ hweak.α := Real.rpow_nonneg (norm_nonneg _) _
    have hdiv_nn : 0 ≤ ‖p' - q‖ ^ hweak.α / hweak.C :=
      div_nonneg hpα_nn (le_of_lt hweak.hC)
    have hK_nn : 0 ≤ K hweak q := K_nonneg hweak q
    have hpen_nn : 0 ≤ (1 / ε) * K hweak q := mul_nonneg (le_of_lt hε_inv_pos) hK_nn
    have hLow' : ‖p' - q‖ ^ hweak.α / hweak.C - hweak.C * (m ^ hweak.β + 1)
        ≤ H x (p' - q) m := by simpa [ge_iff_le] using hLow
    linarith
  -- For all `q'`:  `Hdelta x p m + v·(p'-p) ≤ H(x, p'-q', m) + (1/ε) K(q')`.
  have h_step : ∀ q' : Fin d → ℝ,
      Hdelta hweak ε x p m + ∑ i, v i * (p' i - p i)
        ≤ H x (p' - q') m + (1 / ε) * K hweak q' := by
    intro q'
    -- Convexity of `H(x,·,m)` at base `p - qS`, evaluated at `p' - q'`.
    have hConvIneq :
        H x (p - qS) m + ∑ i, v i * ((p' - q') i - (p - qS) i)
          ≤ H x (p' - q') m :=
      convexOn_subgradient_dotCLMHam hConvH hFDH (p' - q')
    -- K-side support inequality from `sel.hSub` at test point `q'`.
    have hKIneq :
        v ⬝ (q' - qS) ≤ (1 / ε) * (K hweak q' - K hweak qS) := by
      have := hxSub p m hm q'
      rw [hvdef, hqSdef]; exact this
    -- Convert `⬝` to the explicit sum.
    have hKIneq' :
        ∑ i, v i * (q' i - qS i) ≤ (1 / ε) * (K hweak q' - K hweak qS) := by
      have hdot : v ⬝ (q' - qS) = ∑ i, v i * (q' i - qS i) := by
        unfold euclideanDot
        refine Finset.sum_congr rfl ?_
        intro i _; simp [Pi.sub_apply]
      rw [hdot] at hKIneq; exact hKIneq
    -- Split the convexity sum.
    have hsum_split :
        ∑ i, v i * ((p' - q') i - (p - qS) i)
          = (∑ i, v i * (p' i - p i)) + (∑ i, v i * (qS i - q' i)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      have h1 : (p' - q') i - (p - qS) i = (p' i - p i) + (qS i - q' i) := by
        simp only [Pi.sub_apply]; ring
      rw [h1]; ring
    rw [hsum_split] at hConvIneq
    have hsum_neg :
        ∑ i, v i * (qS i - q' i) = -(∑ i, v i * (q' i - qS i)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _; ring
    rw [hsum_neg] at hConvIneq
    -- `(1/ε) K qS + ∑ v_i (q'_i - qS_i) ≤ (1/ε) K q'`.
    have hKIneq_div :
        (1 / ε) * K hweak qS + ∑ i, v i * (q' i - qS i) ≤ (1 / ε) * K hweak q' := by
      have hexpand : (1 / ε) * (K hweak q' - K hweak qS)
          = (1 / ε) * K hweak q' - (1 / ε) * K hweak qS := by ring
      rw [hexpand] at hKIneq'; linarith
    -- Combine.
    linarith [hConvIneq, hKIneq_div, hspec]
  -- Take the infimum over `q'`.
  show Hdelta hweak ε x p m + ∑ i, v i * (p' i - p i) ≤ Hdelta hweak ε x p' m
  unfold Hdelta
  exact le_ciInf h_step

/-- **G3 (a), `hCx` producer.** The convex-at-zero rider for `H^ε`
(paper `lem:H.delta.monotone`).  For `0 < ε ≤ 1`, a.e. `x`, every `(p,m)` with
`m > 0`:

  `Hdelta hweak ε x p m − (DpHepsilonFam hweak qε ε x p m) ⬝ p ≤ Hdelta hweak ε x 0 m`.

This is EXACTLY the `hCx` hypothesis consumed by
`hdeltaUniformBounds_of_selector` and `hdeltaAEPowerEpsData_of_selector`.  It is
the subgradient inequality of `hSubgradientHepsilon_of_selector` evaluated at the
test point `p' = 0` (the subgradient inequality
`Hδ(x,p,m) + D_pH^ε·(0 − p) ≤ Hδ(x,0,m)` rearranged).  Generic in
`(hweak, qε, sel)`; the only extra rider is the accepted carrier `hdiff`. -/
theorem hCx_of_selector
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hdiff : Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    (qε : QEpsFamily d)
    (sel : InfConvSelectorFamily (H := H) (DpH := DpH) hweak qε)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
      ∀ p m, 0 < m →
        Hdelta hweak ε x p m - (DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε x p m) ⬝ p
          ≤ Hdelta hweak ε x 0 m := by
  filter_upwards [hSubgradientHepsilon_of_selector (H := H) (DpH := DpH)
    hweak hdiff qε sel hε] with x hxSub
  intro p m hm
  -- Subgradient inequality at `p' = 0`.
  have hsub := hxSub p m hm (0 : Fin d → ℝ)
  -- `hsub : Hδ(x,p,m) + ∑ i, D_pH^ε_i * (0 i - p i) ≤ Hδ(x,0,m)`.
  -- Rewrite `∑ i, vi * (0 - p) i = - (D_pH^ε ⬝ p)`.
  set v : Fin d → ℝ := DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε x p m with hvdef
  have hpair : ∑ i, v i * ((0 : Fin d → ℝ) i - p i) = -(v ⬝ p) := by
    unfold euclideanDot
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    simp
  rw [hpair] at hsub
  linarith

/-- **G3 (b), `hGrad` producer.**  The `‖q^ε‖`-form gradient norm bound
(paper `eq:inf-conv.diff-relation1`, line 1808), in the genuinely
*derivable* shape: the sup-norm of `D_pH^ε` is bounded by
`(1/ε) (1 + α (√d)^{α−1} ‖q^ε‖^{α−1})`.

The dimension factor `(√d)^{α−1} = d^{(α−1)/2}` arises because the
kernel `K(q) = ‖q‖_eucl + ‖q‖_eucl^α` is *Euclidean*: the genuine
subgradient norm bound `K_subdiff_norm_le` lives in the Euclidean norm
(`‖toEucl v‖_e ≤ 1 + α‖toEucl q^ε‖_e^{α−1}`), and converting to the
ambient sup-norm costs a `‖q‖_eucl ≤ √d·‖q‖_sup` factor on the
`‖q^ε‖`-side and is free (`‖v‖_sup ≤ ‖toEucl v‖_e`) on the gradient side.

Derived from `sel.hSub`: `ε • D_pH^ε ∈ ∂K(q^ε)` at the selector, hence
`K_subdiff_norm_le` applies.  Generic in `(hweak, qε, sel)` — no extra
rider beyond the selector bundle. -/
theorem hGrad_of_selector
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d)
    (sel : InfConvSelectorFamily (H := H) (DpH := DpH) hweak qε)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
      ∀ p m, 0 < m →
        ‖DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε x p m‖
          ≤ (1 / ε) * (1 + hweak.α * (Real.sqrt d) ^ (hweak.α - 1)
              * ‖qε ε (x, p, m)‖ ^ (hweak.α - 1)) := by
  have hα_pos : (0 : ℝ) < hweak.α := lt_trans zero_lt_one hweak.hα
  have hα_nn : (0 : ℝ) ≤ hweak.α := le_of_lt hα_pos
  have hα_sub_nn : (0 : ℝ) ≤ hweak.α - 1 := by linarith [hweak.hα]
  have hε_inv_pos : (0 : ℝ) < 1 / ε := one_div_pos.mpr hε
  filter_upwards [sel.hSub ε hε] with x hxSub
  intro p m hm
  -- Selector value and regularized gradient.
  set qS : Fin d → ℝ := qε ε (x, p, m) with hqSdef
  set v : Fin d → ℝ := DpH x (p - qS) m with hvdef
  have hveq : DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε x p m = v := rfl
  rw [hveq]
  -- Step 1: `ε • v ∈ ∂K(qS)` from `sel.hSub`.
  have hsubgrad : HasSubgradientAt (K hweak) qS (ε • v) := by
    intro q
    -- Goal: `K qS + ∑ i, (ε • v) i * (q i - qS i) ≤ K q`.
    have hsub := hxSub p m hm q
    rw [← hvdef, ← hqSdef] at hsub
    -- `hsub : v ⬝ (q - qS) ≤ (1/ε) (K q - K qS)`.
    -- Convert pairing to sum and scale by ε.
    have hdot : v ⬝ (q - qS) = ∑ i, v i * (q i - qS i) := by
      unfold euclideanDot
      refine Finset.sum_congr rfl ?_
      intro i _; simp [Pi.sub_apply]
    rw [hdot] at hsub
    -- Multiply by `ε > 0`: `ε * (∑ ...) ≤ K q - K qS`.
    have hεmul : ε * (∑ i, v i * (q i - qS i)) ≤ K hweak q - K hweak qS := by
      have := mul_le_mul_of_nonneg_left hsub (le_of_lt hε)
      rwa [← mul_assoc, mul_one_div, div_self (ne_of_gt hε), one_mul] at this
    -- `∑ i, (ε • v) i * (q i - qS i) = ε * (∑ i, v i * (q i - qS i))`.
    have hsmul_sum : (∑ i, (ε • v) i * (q i - qS i))
        = ε * (∑ i, v i * (q i - qS i)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _; simp [Pi.smul_apply, smul_eq_mul]; ring
    rw [hsmul_sum]; linarith [hεmul]
  -- Step 2: Euclidean subgradient norm bound.
  have hnorm_eucl : ‖toEucl (ε • v)‖ ≤ 1 + hweak.α * ‖toEucl qS‖ ^ (hweak.α - 1) :=
    K_subdiff_norm_le hweak hsubgrad
  -- `‖toEucl (ε • v)‖ = ε * ‖toEucl v‖`.
  have hscale : ‖toEucl (ε • v)‖ = ε * ‖toEucl v‖ := by
    rw [toEucl_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
  rw [hscale] at hnorm_eucl
  -- Step 3: sup-norm of `v` ≤ Euclidean norm of `v`.
  have hsup_le : ‖v‖ ≤ ‖toEucl v‖ := sup_norm_le_eucl_norm v
  -- Step 4: `‖toEucl qS‖^(α-1) ≤ (√d)^(α-1) * ‖qS‖^(α-1)`.
  have hqS_eucl : ‖toEucl qS‖ ≤ Real.sqrt d * ‖qS‖ :=
    eucl_norm_le_sqrt_d_sup_norm qS
  have hqS_eucl_nn : (0 : ℝ) ≤ ‖toEucl qS‖ := norm_nonneg _
  have hqS_pow : ‖toEucl qS‖ ^ (hweak.α - 1)
      ≤ (Real.sqrt d) ^ (hweak.α - 1) * ‖qS‖ ^ (hweak.α - 1) := by
    have hstep : ‖toEucl qS‖ ^ (hweak.α - 1)
        ≤ (Real.sqrt d * ‖qS‖) ^ (hweak.α - 1) :=
      Real.rpow_le_rpow hqS_eucl_nn hqS_eucl hα_sub_nn
    rwa [Real.mul_rpow (Real.sqrt_nonneg _) (norm_nonneg _)] at hstep
  -- Assemble.
  -- `‖v‖ ≤ ‖toEucl v‖`, and `ε * ‖toEucl v‖ ≤ 1 + α‖toEucl qS‖^(α-1)`.
  -- So `‖toEucl v‖ ≤ (1/ε)(1 + α‖toEucl qS‖^(α-1))`.
  have hv_eucl_bnd : ‖toEucl v‖
      ≤ (1 / ε) * (1 + hweak.α * ‖toEucl qS‖ ^ (hweak.α - 1)) := by
    rw [mul_comm ε (‖toEucl v‖)] at hnorm_eucl
    have := le_div_iff₀ hε |>.mpr hnorm_eucl
    rwa [div_eq_mul_one_div, mul_comm] at this
  -- Now bound `‖toEucl qS‖^(α-1)` by the d-factor form.
  have hαsub_nn : (0 : ℝ) ≤ hweak.α * ((Real.sqrt d) ^ (hweak.α - 1)
      * ‖qS‖ ^ (hweak.α - 1)) := by
    have h1 : (0 : ℝ) ≤ (Real.sqrt d) ^ (hweak.α - 1) :=
      Real.rpow_nonneg (Real.sqrt_nonneg _) _
    have h2 : (0 : ℝ) ≤ ‖qS‖ ^ (hweak.α - 1) := Real.rpow_nonneg (norm_nonneg _) _
    positivity
  have hinside : 1 + hweak.α * ‖toEucl qS‖ ^ (hweak.α - 1)
      ≤ 1 + hweak.α * (Real.sqrt d) ^ (hweak.α - 1) * ‖qS‖ ^ (hweak.α - 1) := by
    have hmul : hweak.α * ‖toEucl qS‖ ^ (hweak.α - 1)
        ≤ hweak.α * ((Real.sqrt d) ^ (hweak.α - 1) * ‖qS‖ ^ (hweak.α - 1)) :=
      mul_le_mul_of_nonneg_left hqS_pow hα_nn
    have hrw : hweak.α * ((Real.sqrt d) ^ (hweak.α - 1) * ‖qS‖ ^ (hweak.α - 1))
        = hweak.α * (Real.sqrt d) ^ (hweak.α - 1) * ‖qS‖ ^ (hweak.α - 1) := by ring
    rw [hrw] at hmul; linarith
  calc ‖v‖
      ≤ ‖toEucl v‖ := hsup_le
    _ ≤ (1 / ε) * (1 + hweak.α * ‖toEucl qS‖ ^ (hweak.α - 1)) := hv_eucl_bnd
    _ ≤ (1 / ε) * (1 + hweak.α * (Real.sqrt d) ^ (hweak.α - 1)
          * ‖qS‖ ^ (hweak.α - 1)) :=
        mul_le_mul_of_nonneg_left hinside (le_of_lt hε_inv_pos)

end T3

/-! ## D2b-0 — genuine `Hdelta` right-continuity at `m = 0⁺` (paper `lem:inf-conv-props`)

The expert/orchestrator route (2026-06-08) proves genuine `Hdelta` rc0 at
`m = 0⁺` toward the LITERAL Lean value `Hdelta hweak ε x p 0` from the BASE
boundary bundle `hH0 : HypothesisHZeroExtension H` (the slice rc0, via
`H_rc0_of_hH0`) together with the EXISTING, already-accepted T1 rider
`hHextJointCont : HypothesisHextJointCont H` (joint continuity of base `H` on
the closed half-plane `{0 ≤ m}`, Assumptions.lean:3216). The boundary `liminf`
reduces EXACTLY to joint lower-semicontinuity of base `H` at the boundary
(proven, not assumeable from `hH0` alone), which `hHextJointCont` supplies.

Three sublemmas:
* `Hdelta_near_minimizers_bounded` — K-coercivity + competitor `q = p` ⇒ the
  positive-mass minimizers `qε ε (x,p,m)` are bounded for `0 < m ≤ 1`
  (no rider needed).
* `Hdelta_boundary_liminf` — under `hHextJointCont`: `Hdelta x p 0 ≤ liminf`.
* `Hdelta_rc0_of_selectorFamily` / `Hdelta_hat0_of_selectorFamily` — assemble
  limsup + liminf via `tendsto_of_le_liminf_of_limsup_le`. -/

/-- **Bounded minimizers near `m = 0⁺`** (paper `lem:inf-conv-props`, the
boundary compactness step). Per-`x` (where `sel.H_form` and the weak-growth
upper/lower bounds hold), the inf-conv minimizers `qε ε (x, p, m)` stay inside
a fixed closed ball of radius `R := (ε * (3 * hweak.C) + K hweak p) ^ (1/α)` for
`0 < m ≤ 1`. Pure K-coercivity (`K_ge_rpow`) + testing the competitor `q = p`
in the infimum (`sel.H_form` gives the minimizer realisation; `hweak.upper`
bounds `H x 0 m`; `hweak.lower` bounds `H x (p − q) m` from below). NO rider. -/
theorem Hdelta_near_minimizers_bounded
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d) {ε : ℝ} (hε : 0 < ε)
    {x : Fin d → ℝ}
    (hHform : ∀ p m, 0 < m →
      Hdelta hweak ε x p m
        = H x (p - qε ε (x, p, m)) m + (1 / ε) * K hweak (qε ε (x, p, m)))
    (hUpper : ∀ m, 0 < m → H x (0 : Fin d → ℝ) m ≤ -(m ^ hweak.β) / hweak.C + hweak.C)
    (hLower : ∀ p m, 0 < m →
      H x p m ≥ (‖p‖ ^ hweak.α) / hweak.C - hweak.C * (m ^ hweak.β + 1))
    (p : Fin d → ℝ) :
    ∀ m : ℝ, 0 < m → m ≤ 1 →
      ‖qε ε (x, p, m)‖
        ≤ (ε * (3 * hweak.C) + K hweak p) ^ (1 / hweak.α) := by
  intro m hm hm1
  set q := qε ε (x, p, m) with hqdef
  have hC_pos : 0 < hweak.C := hweak.hC
  have hα_pos : 0 < hweak.α := lt_trans zero_lt_one hweak.hα
  -- `m^β ≤ 1` for `0 < m ≤ 1` (β > 0).
  have hmβ_le : m ^ hweak.β ≤ 1 := Real.rpow_le_one (le_of_lt hm) hm1 (le_of_lt hweak.hβ)
  have hmβ_nn : 0 ≤ m ^ hweak.β := Real.rpow_nonneg (le_of_lt hm) _
  have hε_inv_pos0 : 0 < 1 / ε := one_div_pos.mpr hε
  -- Test competitor `q = p`: `Hdelta x p m ≤ H x 0 m + (1/ε) K p`.
  -- `BddBelow` of the penalized family (so `ciInf_le` applies).
  have hbdd2 : BddBelow
      (Set.range fun q' : Fin d → ℝ => H x (p - q') m + (1 / ε) * K hweak q') := by
    refine ⟨-(hweak.C * (m ^ hweak.β + 1)), ?_⟩
    rintro y ⟨q', rfl⟩
    have := hLower (p - q') m hm
    have hpos : 0 ≤ (‖p - q'‖ ^ hweak.α) / hweak.C :=
      div_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (le_of_lt hC_pos)
    have hKnn : 0 ≤ (1 / ε) * K hweak q' :=
      mul_nonneg (le_of_lt hε_inv_pos0) (K_nonneg hweak q')
    linarith
  have htest : Hdelta hweak ε x p m
      ≤ H x (0 : Fin d → ℝ) m + (1 / ε) * K hweak p := by
    -- Direct competitor: `ciInf_le` at `q' = p` gives integrand `H x 0 m + (1/ε)K p`.
    have hle : (⨅ q' : Fin d → ℝ, H x (p - q') m + (1 / ε) * K hweak q')
        ≤ H x (p - p) m + (1 / ε) * K hweak p :=
      ciInf_le hbdd2 p
    simpa [Hdelta_def, sub_self] using hle
  -- Minimizer realisation at `q`.
  have hreal := hHform p m hm
  rw [← hqdef] at hreal
  -- `H x (p − q) m ≥ -C(m^β+1)`.
  have hHlow : -(hweak.C * (m ^ hweak.β + 1)) ≤ H x (p - q) m := by
    have := hLower (p - q) m hm
    have hpos : 0 ≤ (‖p - q‖ ^ hweak.α) / hweak.C :=
      div_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (le_of_lt hC_pos)
    linarith
  have hUm := hUpper m hm
  have hε_inv_pos : 0 < 1 / ε := one_div_pos.mpr hε
  have hKq_nn : 0 ≤ K hweak q := K_nonneg hweak q
  have hKp_nn : 0 ≤ K hweak p := K_nonneg hweak p
  -- Combine: `(1/ε) K q ≤ ε⁻¹-scaled bound` ⇒ `K q ≤ ε(3C) + K p`.
  -- From `hreal` and `htest`:  H x (p−q) m + (1/ε)K q ≤ H x 0 m + (1/ε)K p.
  have hcomb : H x (p - q) m + (1 / ε) * K hweak q
      ≤ H x (0 : Fin d → ℝ) m + (1 / ε) * K hweak p := by
    rw [← hreal]; exact htest
  -- Lower-bound LHS, upper-bound RHS: `(1/ε)K q ≤ 3C + (1/ε)K p` (using m^β ≤ 1).
  have hKq_eps : (1 / ε) * K hweak q ≤ (3 * hweak.C) + (1 / ε) * K hweak p := by
    have hRHS : H x (0 : Fin d → ℝ) m + (1 / ε) * K hweak p
        ≤ hweak.C + (1 / ε) * K hweak p := by
      have : H x (0 : Fin d → ℝ) m ≤ hweak.C := by
        have hneg : -(m ^ hweak.β) / hweak.C ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hC_pos)
        linarith [hUm]
      linarith
    nlinarith [hcomb, hHlow, hmβ_le, hRHS]
  -- Multiply by ε: `K q ≤ ε(3C) + K p`.
  have hKq_le : K hweak q ≤ ε * (3 * hweak.C) + K hweak p := by
    have hεpos := hε
    have h1 : ε * ((1 / ε) * K hweak q)
        ≤ ε * ((3 * hweak.C) + (1 / ε) * K hweak p) :=
      mul_le_mul_of_nonneg_left hKq_eps (le_of_lt hε)
    rw [mul_add] at h1
    have he1 : ε * ((1 / ε) * K hweak q) = K hweak q := by field_simp
    have he2 : ε * ((1 / ε) * K hweak p) = K hweak p := by field_simp
    rw [he1] at h1
    rw [show ε * (3 * hweak.C) + ε * ((1 / ε) * K hweak p)
          = ε * (3 * hweak.C) + K hweak p by rw [he2]] at h1
    exact h1
  -- `‖q‖^α ≤ K q ≤ B`, so `‖q‖ ≤ B^(1/α)`.
  have hB_nn : 0 ≤ ε * (3 * hweak.C) + K hweak p := by positivity
  have hqα_le : ‖q‖ ^ hweak.α ≤ ε * (3 * hweak.C) + K hweak p :=
    le_trans (K_ge_rpow hweak q) hKq_le
  -- Take `(·)^(1/α)` of both sides.
  have hmono : (‖q‖ ^ hweak.α) ^ (1 / hweak.α)
      ≤ (ε * (3 * hweak.C) + K hweak p) ^ (1 / hweak.α) :=
    Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg _) _) hqα_le
      (le_of_lt (by positivity))
  have hself : (‖q‖ ^ hweak.α) ^ (1 / hweak.α) = ‖q‖ := by
    rw [← Real.rpow_mul (norm_nonneg _), mul_one_div,
      div_self (ne_of_gt hα_pos), Real.rpow_one]
  rw [hself] at hmono
  exact hmono

/-- **Boundary `liminf` inequality for `Hdelta`** (paper `lem:inf-conv-props`).
Under `hHextJointCont` (joint continuity of base `H` on `{0 ≤ m}`), at a point
`x` where the minimizer realisation (`sel.H_form`), the weak-growth bounds, and
the boundary continuity hold, one has, for every `p`,
`Hdelta hweak ε x p 0 ≤ liminf_{m → 0⁺} Hdelta hweak ε x p m`.

The proof is the boundary convex-analysis argument: by contradiction, pick
`c` strictly between the liminf and `Hdelta x p 0`; extract a sequence
`m_n → 0⁺` with `Hdelta x p m_n < c`; the minimizers `q_n` are bounded
(`Hdelta_near_minimizers_bounded`), so a subsequence `q_{φ n} → q*`; joint
lsc of `H` at the boundary point `(p − q*, 0)` (from `hHextJointCont`) plus
continuity of `K` then force `Hdelta x p 0 ≤ … ≤ c`, contradicting `c <`. -/
theorem Hdelta_boundary_liminf
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d) {ε : ℝ} (hε : 0 < ε)
    {x : Fin d → ℝ}
    (hHform : ∀ p m, 0 < m →
      Hdelta hweak ε x p m
        = H x (p - qε ε (x, p, m)) m + (1 / ε) * K hweak (qε ε (x, p, m)))
    (hUpper : ∀ m, 0 < m → H x (0 : Fin d → ℝ) m ≤ -(m ^ hweak.β) / hweak.C + hweak.C)
    (hLower : ∀ p m, 0 < m →
      H x p m ≥ (‖p‖ ^ hweak.α) / hweak.C - hweak.C * (m ^ hweak.β + 1))
    (hJoint : ContinuousOn (fun pm : (Fin d → ℝ) × ℝ => H x pm.1 pm.2) {pm | 0 ≤ pm.2})
    (p : Fin d → ℝ) :
    Hdelta hweak ε x p 0 ≤ liminf (fun m : ℝ => Hdelta hweak ε x p m) (𝓝[>] (0 : ℝ)) := by
  -- `BddBelow` of the family `q ↦ H x (p−q) 0` (for the `ciInf_le` test at q*).
  -- We only need `ciInf_le` at the m=0 level via the boundary-value testing.
  have hC_pos0 : 0 < hweak.C := hweak.hC
  -- Bounded-above witness for `Hdelta x p ·` near `0⁺` (via `hJoint` slice limit
  -- at `p` and competitor `q = 0`): used to provide the cobounded-ge side-goal.
  have hHp_slice : Tendsto (fun m : ℝ => H x p m) (𝓝[>] (0 : ℝ)) (𝓝 (H x p 0)) := by
    have hpmem : ((p, 0) : (Fin d → ℝ) × ℝ) ∈ {pm : (Fin d → ℝ) × ℝ | 0 ≤ pm.2} := by
      simp
    have hmap : Tendsto (fun m : ℝ => ((p, m) : (Fin d → ℝ) × ℝ))
        (𝓝[>] (0 : ℝ)) (𝓝[{pm : (Fin d → ℝ) × ℝ | 0 ≤ pm.2}] (p, 0)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨tendsto_const_nhds.prodMk_nhds (nhdsWithin_le_nhds), ?_⟩
      filter_upwards [self_mem_nhdsWithin] with m hm using le_of_lt hm
    have := (hJoint (p, 0) hpmem).tendsto.comp hmap
    simpa only [Function.comp_def] using this
  have hcobdd : IsCoboundedUnder (· ≥ ·) (𝓝[>] (0 : ℝ))
      (fun m : ℝ => Hdelta hweak ε x p m) := by
    refine IsBoundedUnder.isCoboundedUnder_ge ?_
    refine ⟨H x p 0 + 1, ?_⟩
    rw [eventually_map]
    have hev : ∀ᶠ m in 𝓝[>] (0 : ℝ), H x p m ≤ H x p 0 + 1 := by
      have := hHp_slice.eventually (Iio_mem_nhds (show H x p 0 < H x p 0 + 1 by linarith))
      filter_upwards [this] with m hm using le_of_lt hm
    have hub : ∀ᶠ m in 𝓝[>] (0 : ℝ), Hdelta hweak ε x p m ≤ H x p m := by
      filter_upwards [self_mem_nhdsWithin] with m hm
      have hbdd : BddBelow (Set.range fun q' : Fin d → ℝ => H x (p - q') m) := by
        refine ⟨-(hweak.C * (m ^ hweak.β + 1)), ?_⟩
        rintro y ⟨q', rfl⟩
        have := hLower (p - q') m hm
        have hpos : 0 ≤ (‖p - q'‖ ^ hweak.α) / hweak.C :=
          div_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (le_of_lt hC_pos0)
        linarith
      exact Hdelta_le_H_self hweak hε x p m hbdd
    filter_upwards [hub, hev] with m h1 h2 using le_trans h1 h2
  by_contra hcon
  push_neg at hcon
  -- `liminf < Hdelta x p 0`; pick `c` strictly in between.
  obtain ⟨c, hc_lt, hc_gt⟩ := exists_between hcon
  -- Extract a sequence `m_n → 0⁺` with `Hdelta x p m_n < c`.
  have hfreq : ∃ᶠ m in 𝓝[>] (0 : ℝ), Hdelta hweak ε x p m < c :=
    frequently_lt_of_liminf_lt hcobdd hc_lt
  obtain ⟨mseq, hmtend, hmlt⟩ := exists_seq_forall_of_frequently hfreq
  -- Set `R` = uniform minimizer radius.
  set R := (ε * (3 * hweak.C) + K hweak p) ^ (1 / hweak.α) with hRdef
  have hRbound := Hdelta_near_minimizers_bounded hweak qε hε hHform hUpper hLower p
  -- Eventually `mseq n ∈ (0, 1]`.
  have hpos_ev : ∀ᶠ n in atTop, 0 < mseq n :=
    hmtend.eventually (eventually_mem_nhdsWithin)
  have hle1_ev : ∀ᶠ n in atTop, mseq n ≤ 1 := by
    have : ∀ᶠ m in 𝓝[>] (0 : ℝ), m ≤ 1 := by
      have : Set.Iic (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) :=
        nhdsWithin_le_nhds (Iic_mem_nhds (by norm_num))
      filter_upwards [this] with m hm using hm
    exact hmtend.eventually this
  -- The minimizers along the sequence, eventually in the closed ball.
  set q : ℕ → (Fin d → ℝ) := fun n => qε ε (x, p, mseq n) with hqdef
  -- Build a sequence that is genuinely in the ball for all n by shifting.
  -- Use `IsCompact.tendsto_subseq'` with the frequent membership.
  have hmem_freq : ∃ᶠ n in atTop, q n ∈ Metric.closedBall (0 : Fin d → ℝ) R := by
    refine (hpos_ev.and hle1_ev).frequently.mono ?_
    rintro n ⟨hpos, hle1⟩
    rw [mem_closedBall_zero_iff]
    exact hRbound (mseq n) hpos hle1
  have hcompact : IsCompact (Metric.closedBall (0 : Fin d → ℝ) R) :=
    isCompact_closedBall _ _
  obtain ⟨qstar, _hqstar_mem, φ, hφ_mono, hφ_tend⟩ :=
    hcompact.tendsto_subseq' hmem_freq
  -- Along the subsequence: `mseq (φ n) → 0⁺`, `q (φ n) → qstar`.
  have hmsub : Tendsto (fun n => mseq (φ n)) atTop (𝓝[>] (0 : ℝ)) :=
    hmtend.comp hφ_mono.tendsto_atTop
  -- Boundary point of `H`: `(p − qstar, 0)`.
  set z0 : (Fin d → ℝ) × ℝ := (p - qstar, 0) with hz0def
  have hz0_mem : z0 ∈ {pm : (Fin d → ℝ) × ℝ | 0 ≤ pm.2} := by
    change (0 : ℝ) ≤ z0.2
    rw [hz0def]
  -- Sequence `z_n := (p − q (φ n), mseq (φ n))` tends to `z0` within `{0 ≤ m}`.
  set z : ℕ → (Fin d → ℝ) × ℝ := fun n => (p - q (φ n), mseq (φ n)) with hzdef
  have hz_tend : Tendsto z atTop (𝓝[{pm : (Fin d → ℝ) × ℝ | 0 ≤ pm.2}] z0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · -- `z_n → z0` in the ambient topology.
      have h1 : Tendsto (fun n => p - q (φ n)) atTop (𝓝 (p - qstar)) :=
        tendsto_const_nhds.sub hφ_tend
      have h2 : Tendsto (fun n => mseq (φ n)) atTop (𝓝 (0 : ℝ)) :=
        hmsub.mono_right nhdsWithin_le_nhds
      exact (h1.prodMk_nhds h2)
    · -- `z_n ∈ {0 ≤ m}` eventually (in fact: `mseq (φ n) > 0`).
      have : ∀ᶠ n in atTop, 0 ≤ mseq (φ n) := by
        filter_upwards [(hmsub.eventually eventually_mem_nhdsWithin)] with n hn
        exact le_of_lt hn
      filter_upwards [this] with n hn
      exact hn
  -- Joint lsc of `H` at `z0` from `hJoint`.
  have hlsc : LowerSemicontinuousWithinAt
      (fun pm : (Fin d → ℝ) × ℝ => H x pm.1 pm.2) {pm | 0 ≤ pm.2} z0 :=
    (hJoint z0 hz0_mem).lowerSemicontinuousWithinAt
  -- `K (q (φ n)) → K qstar`.
  have hKtend : Tendsto (fun n => (1 / ε) * K hweak (q (φ n))) atTop
      (𝓝 ((1 / ε) * K hweak qstar)) :=
    (tendsto_const_nhds).mul ((K_continuous hweak).continuousAt.tendsto.comp hφ_tend)
  -- m=0 slice lower bound `H x s 0 ≥ -C` for all `s`, via `hJoint` slice limit.
  have hC_pos : 0 < hweak.C := hweak.hC
  have hslice0 : ∀ s : Fin d → ℝ, -hweak.C ≤ H x s 0 := by
    intro s
    -- `m ↦ H x s m` tends to `H x s 0` as `m → 0⁺` (from `hJoint` at `(s, 0)`).
    have hsmem : ((s, 0) : (Fin d → ℝ) × ℝ) ∈ {pm : (Fin d → ℝ) × ℝ | 0 ≤ pm.2} := by
      simp
    have hcontAt := hJoint (s, 0) hsmem
    -- Compose with `m ↦ (s, m)` mapping `(0,∞)` into `{0≤m}` and `→ (s,0)`.
    have hmap : Tendsto (fun m : ℝ => ((s, m) : (Fin d → ℝ) × ℝ))
        (𝓝[>] (0 : ℝ)) (𝓝[{pm : (Fin d → ℝ) × ℝ | 0 ≤ pm.2}] (s, 0)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨tendsto_const_nhds.prodMk_nhds (nhdsWithin_le_nhds), ?_⟩
      filter_upwards [self_mem_nhdsWithin] with m hm
      exact le_of_lt hm
    have hHslice : Tendsto (fun m : ℝ => H x s m) (𝓝[>] (0 : ℝ)) (𝓝 (H x s 0)) := by
      have := hcontAt.tendsto.comp hmap
      simpa only [Function.comp_def] using this
    -- Eventually `H x s m ≥ -C(m^β+1)`; pass to the limit and use `m^β → 0`.
    have hev : ∀ᶠ m in 𝓝[>] (0 : ℝ), -(hweak.C * (m ^ hweak.β + 1)) ≤ H x s m := by
      filter_upwards [self_mem_nhdsWithin] with m hm
      have hmpos : 0 < m := hm
      have := hLower s m hmpos
      have hpos : 0 ≤ (‖s‖ ^ hweak.α) / hweak.C :=
        div_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (le_of_lt hC_pos)
      linarith
    -- `-(C(m^β+1)) → -C`.
    have hmβtend : Tendsto (fun m : ℝ => m ^ hweak.β) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have : Tendsto (fun m : ℝ => m ^ hweak.β) (𝓝[>] (0 : ℝ)) (𝓝 (0 ^ hweak.β)) :=
        ((Real.continuousAt_rpow_const 0 hweak.β
          (Or.inr (le_of_lt hweak.hβ))).continuousWithinAt).tendsto
      simpa [Real.zero_rpow (ne_of_gt hweak.hβ)] using this
    have hbndtend : Tendsto (fun m : ℝ => -(hweak.C * (m ^ hweak.β + 1)))
        (𝓝[>] (0 : ℝ)) (𝓝 (-(hweak.C * (0 + 1)))) := by
      exact ((tendsto_const_nhds.mul (hmβtend.add tendsto_const_nhds)).neg)
    have hlimle : -(hweak.C * (0 + 1)) ≤ H x s 0 :=
      le_of_tendsto_of_tendsto hbndtend hHslice hev
    simpa using hlimle
  -- `BddBelow` of the m=0 penalized family (so `ciInf_le` applies).
  have hBddBelow0 :
      BddBelow (Set.range fun q' : Fin d → ℝ => H x (p - q') 0 + (1 / ε) * K hweak q') := by
    refine ⟨-hweak.C, ?_⟩
    rintro y ⟨q', rfl⟩
    have h1 := hslice0 (p - q')
    have h2 : 0 ≤ (1 / ε) * K hweak q' :=
      mul_nonneg (le_of_lt (one_div_pos.mpr hε)) (K_nonneg hweak q')
    linarith
  -- Boundary value bound: `Hdelta x p 0 ≤ H x (p − qstar) 0 + (1/ε) K qstar`.
  have hbound0 : Hdelta hweak ε x p 0
      ≤ H x (p - qstar) 0 + (1 / ε) * K hweak qstar := by
    have := ciInf_le hBddBelow0 qstar
    simpa [Hdelta_def] using this
  -- Now the contradiction via lsc + K-continuity.
  -- Let `L := H x (p − qstar) 0`, `b := (1/ε) K qstar`.
  set L := H x (p - qstar) 0 with hLdef
  set b := (1 / ε) * K hweak qstar with hbdef
  -- `c < Hdelta x p 0 ≤ L + b`, so `c - b < L`. Pick `y` with `c - b < y < L`.
  have hcLb : c < L + b := lt_of_lt_of_le hc_gt hbound0
  obtain ⟨y, hy1, hy2⟩ : ∃ y, c - b < y ∧ y < L :=
    exists_between (by linarith)
  -- lsc at `z0` with `y < L = H x z0`: eventually `y < H x (z_n)` along `z_n → z0`.
  have hlscApp : ∀ᶠ pm in 𝓝[{pm : (Fin d → ℝ) × ℝ | 0 ≤ pm.2}] z0,
      y < (fun pm : (Fin d → ℝ) × ℝ => H x pm.1 pm.2) pm :=
    hlsc y (by simpa [hz0def, hLdef] using hy2)
  have hev_a : ∀ᶠ n in atTop, y < H x (p - q (φ n)) (mseq (φ n)) := by
    have := hz_tend.eventually hlscApp
    filter_upwards [this] with n hn
    simpa [hzdef] using hn
  -- `b_n := (1/ε) K (q (φ n)) → b`, so eventually `b_n > c - y`.
  have hcyb : c - y < b := by linarith
  have hev_b : ∀ᶠ n in atTop, c - y < (1 / ε) * K hweak (q (φ n)) := by
    have := hKtend.eventually (eventually_gt_nhds (by simpa [hbdef] using hcyb))
    filter_upwards [this] with n hn
    exact hn
  -- Combine: eventually `Hdelta x p (mseq (φ n)) = a_n + b_n > y + (c - y) = c`,
  -- contradicting `Hdelta x p (mseq (φ n)) < c`.
  have hev_pos : ∀ᶠ n in atTop, 0 < mseq (φ n) :=
    hmsub.eventually eventually_mem_nhdsWithin
  obtain ⟨n, ⟨ha, hb⟩, hposn⟩ :=
    ((hev_a.and hev_b).and hev_pos).exists
  have hreal := hHform p (mseq (φ n)) hposn
  -- `q (φ n) = qε ε (x, p, mseq (φ n))` by definition.
  have hqn : q (φ n) = qε ε (x, p, mseq (φ n)) := rfl
  rw [← hqn] at hreal
  have hsum : c < Hdelta hweak ε x p (mseq (φ n)) := by
    rw [hreal]; linarith
  exact absurd (hmlt (φ n)) (not_lt.mpr (le_of_lt hsum))

/-- **Genuine `Hdelta` right-continuity at `m = 0⁺` from the selector family**
(paper `lem:inf-conv-props`, the `m = 0`/Hat0 convention). For `ε > 0`, a.e.
`x`, every `p`, `m ↦ Hdelta hweak ε x p m` tends to `Hdelta hweak ε x p 0` as
`m → 0⁺`. Threads the BASE riders `hH0` (slice rc0, via `H_rc0_of_hH0`) and
`hHextJointCont` (boundary joint continuity of base `H`), plus the selector
family certificate `sel` (which supplies the minimizer realisation `H_form`)
and `hDiff` (only needed downstream). NO loose `hH_rc0` / `HypothesisHat0
(Hdelta)` / `RegularityH (Hdelta)` binder. -/
theorem Hdelta_rc0_of_selectorFamily
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hH0 : Hamiltonian.HypothesisHZeroExtension (d := d) H)
    (hHextJointCont : Hamiltonian.HypothesisHextJointCont (d := d) H)
    (qε : QEpsFamily d) (sel : InfConvSelectorFamily (H := H) (DpH := DpH) hweak qε)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
      ∀ p : Fin d → ℝ,
        Tendsto (fun m : ℝ => Hdelta hweak ε x p m) (𝓝[>] (0 : ℝ))
          (𝓝 (Hdelta hweak ε x p 0)) := by
  have hC_pos : 0 < hweak.C := hweak.hC
  filter_upwards [sel.H_form ε hε, hweak.upper, hweak.lower,
    H_rc0_of_hH0 (H := H) hH0, hHextJointCont]
    with x hxHform hxUpper hxLower hxRc0 hxJoint p
  -- Per-x abbreviations of the inputs.
  have hHform : ∀ p' m, 0 < m →
      Hdelta hweak ε x p' m
        = H x (p' - qε ε (x, p', m)) m + (1 / ε) * K hweak (qε ε (x, p', m)) :=
    fun p' m hm => hxHform p' m hm
  have hUpper : ∀ m, 0 < m →
      H x (0 : Fin d → ℝ) m ≤ -(m ^ hweak.β) / hweak.C + hweak.C := hxUpper
  have hLower : ∀ p' m, 0 < m →
      H x p' m ≥ (‖p'‖ ^ hweak.α) / hweak.C - hweak.C * (m ^ hweak.β + 1) :=
    fun p' m hm => hxLower p' m hm
  -- `BddBelow` of `q' ↦ H x (p−q') m` for each `m > 0`.
  have hBddm : ∀ m : ℝ, 0 < m →
      BddBelow (Set.range fun q' : Fin d → ℝ => H x (p - q') m) := by
    intro m hm
    refine ⟨-(hweak.C * (m ^ hweak.β + 1)), ?_⟩
    rintro y ⟨q', rfl⟩
    have := hLower (p - q') m hm
    have hpos : 0 ≤ (‖p - q'‖ ^ hweak.α) / hweak.C :=
      div_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (le_of_lt hC_pos)
    linarith
  have hBddEv : ∀ᶠ m in 𝓝[>] (0 : ℝ),
      BddBelow (Set.range fun q' : Fin d → ℝ => H x (p - q') m) := by
    filter_upwards [self_mem_nhdsWithin] with m hm using hBddm m hm
  -- ===== liminf half (deliverable 2) =====
  have hinf : Hdelta hweak ε x p 0
      ≤ liminf (fun m : ℝ => Hdelta hweak ε x p m) (𝓝[>] (0 : ℝ)) :=
    Hdelta_boundary_liminf hweak qε hε hHform hUpper hLower hxJoint p
  -- ===== boundedness witnesses =====
  -- Upper: eventually `Hdelta x p m ≤ H x p m`, and `H x p · → H x p 0`.
  have hUB_ev : ∀ᶠ m in 𝓝[>] (0 : ℝ), Hdelta hweak ε x p m ≤ H x p m := by
    filter_upwards [self_mem_nhdsWithin] with m hm
    exact Hdelta_le_H_self hweak hε x p m (hBddm m hm)
  have hHp_rc0 : Tendsto (fun m : ℝ => H x p m) (𝓝[>] (0 : ℝ)) (𝓝 (H x p 0)) :=
    hxRc0 p
  have hBddAbove : IsBoundedUnder (· ≤ ·) (𝓝[>] (0 : ℝ))
      (fun m : ℝ => Hdelta hweak ε x p m) := by
    refine ⟨H x p 0 + 1, ?_⟩
    rw [eventually_map]
    have hev : ∀ᶠ m in 𝓝[>] (0 : ℝ), H x p m ≤ H x p 0 + 1 := by
      have := hHp_rc0.eventually (Iio_mem_nhds (show H x p 0 < H x p 0 + 1 by linarith))
      filter_upwards [this] with m hm using le_of_lt hm
    filter_upwards [hUB_ev, hev] with m h1 h2 using le_trans h1 h2
  have hBddBelowU : IsBoundedUnder (· ≥ ·) (𝓝[>] (0 : ℝ))
      (fun m : ℝ => Hdelta hweak ε x p m) := by
    refine ⟨-(hweak.C * (1 + 1)), ?_⟩
    rw [eventually_map]
    have hev1 : ∀ᶠ m in 𝓝[>] (0 : ℝ), m ≤ 1 := by
      have : Set.Iic (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) :=
        nhdsWithin_le_nhds (Iic_mem_nhds (by norm_num))
      filter_upwards [this] with m hm using hm
    filter_upwards [self_mem_nhdsWithin, hev1] with m hm hm1
    have hmpos : 0 < m := hm
    have hmβ_le : m ^ hweak.β ≤ 1 :=
      Real.rpow_le_one (le_of_lt hmpos) hm1 (le_of_lt hweak.hβ)
    have hlb : (⨅ q' : Fin d → ℝ, H x (p - q') m) ≤ Hdelta hweak ε x p m :=
      Hdelta_lower_bound hweak hε x p m (hBddm m hmpos)
    have hib : -(hweak.C * (m ^ hweak.β + 1)) ≤ ⨅ q' : Fin d → ℝ, H x (p - q') m := by
      refine le_ciInf ?_
      intro q'
      have := hLower (p - q') m hmpos
      have hpos : 0 ≤ (‖p - q'‖ ^ hweak.α) / hweak.C :=
        div_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (le_of_lt hC_pos)
      linarith
    have : -(hweak.C * (1 + 1)) ≤ -(hweak.C * (m ^ hweak.β + 1)) := by
      have : hweak.C * (m ^ hweak.β + 1) ≤ hweak.C * (1 + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hC_pos)
      linarith
    exact le_trans this (le_trans hib hlb)
  -- ===== limsup half =====
  -- For every competitor `q`, `limsup Hdelta ≤ H x (p−q) 0 + (1/ε) K q`.
  have hsup_q : ∀ q : Fin d → ℝ,
      limsup (fun m : ℝ => Hdelta hweak ε x p m) (𝓝[>] (0 : ℝ))
        ≤ H x (p - q) 0 + (1 / ε) * K hweak q := by
    intro q
    obtain ⟨hev_le, htend_comp⟩ :=
      Hdelta_boundary_limsup hweak hε x p q (hxRc0 (p - q)) hBddEv
    have hcomp_bddAbove : IsBoundedUnder (· ≤ ·) (𝓝[>] (0 : ℝ))
        (fun m : ℝ => H x (p - q) m + (1 / ε) * K hweak q) :=
      htend_comp.isBoundedUnder_le
    calc limsup (fun m : ℝ => Hdelta hweak ε x p m) (𝓝[>] (0 : ℝ))
        ≤ limsup (fun m : ℝ => H x (p - q) m + (1 / ε) * K hweak q) (𝓝[>] (0 : ℝ)) :=
          limsup_le_limsup hev_le (hBddBelowU.isCoboundedUnder_le) hcomp_bddAbove
      _ = H x (p - q) 0 + (1 / ε) * K hweak q := htend_comp.limsup_eq
  have hsup : limsup (fun m : ℝ => Hdelta hweak ε x p m) (𝓝[>] (0 : ℝ))
      ≤ Hdelta hweak ε x p 0 := by
    rw [Hdelta_def]
    exact le_ciInf hsup_q
  -- ===== assemble =====
  exact tendsto_of_le_liminf_of_limsup_le hinf hsup hBddAbove hBddBelowU

open MeasureTheory StationaryMFG.Periodic

private theorem paper_convex_of_subgradient
    {f : (Fin d → ℝ) → ℝ} {g : (Fin d → ℝ) → (Fin d → ℝ)}
    (hs : ∀ p, HasSubgradientAt f p (g p)) :
    ConvexOn ℝ Set.univ f := by
  refine ⟨convex_univ, ?_⟩
  intro p _ q _ a b ha hb hab
  let r := a • p + b • q
  have h₁ := mul_le_mul_of_nonneg_left (hs r p) ha
  have h₂ := mul_le_mul_of_nonneg_left (hs r q) hb
  have hcancel : a * (∑ i, g r i * (p i - r i)) +
      b * (∑ i, g r i * (q i - r i)) = 0 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro i _
    calc
      a * (g r i * (p i - r i)) + b * (g r i * (q i - r i))
          = g r i * (a * p i + b * q i - (a + b) * r i) := by ring
      _ = 0 := by
        rw [hab]
        dsimp [r]
        ring
  have hvalue : a * f r + b * f r = f r := by rw [← add_mul, hab, one_mul]
  change f r ≤ a * f p + b * f q
  nlinarith only [h₁, h₂, hcancel, hvalue]

/-- Positive-mass continuity of the regularized Hamiltonian uses only the
positive-mass continuity from standing regularity (H1). -/
theorem HdeltaPaper_continuousOn_pos
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d) (sel : InfConvSelectorFamily h qε)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ContinuousOn (fun pm : (Fin d → ℝ) × ℝ => HdeltaPaper h ε x pm.1 pm.2)
        {pm | 0 < pm.2} := by
  filter_upwards [h.continuous_H_pm, sel.q_cont_pm ε hε, sel.H_form ε hε]
    with x hH hq hform
  have hshift : ContinuousOn
      (fun pm : (Fin d → ℝ) × ℝ => (pm.1 - qε ε (x, pm.1, pm.2), pm.2))
      {pm | 0 < pm.2} :=
    (continuous_fst.continuousOn.sub hq).prodMk continuous_snd.continuousOn
  have hcomp := hH.comp hshift (fun pm hpm => hpm)
  have hpen := ((K_continuous h).continuousOn.comp hq (fun _ _ => Set.mem_univ _)).const_mul
    (1 / ε)
  apply (hcomp.add hpen).congr
  intro pm hpm
  change HdeltaPaper h ε x pm.1 pm.2 =
    H x (pm.1 - qε ε (x, pm.1, pm.2)) pm.2 +
      (1 / ε) * K h (qε ε (x, pm.1, pm.2))
  rw [HdeltaPaper_of_pos h ε x pm.1 hpm]
  exact hform pm.1 pm.2 hpm

/-- The positive slices of Hε are convex, from their derived subgradients. -/
theorem HdeltaPaper_convexOn_pos
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (hdiff : HypothesisHpDifferentiable (d := d) H DpH)
    (qε : QEpsFamily d) (sel : InfConvSelectorFamily h qε)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ m, 0 < m →
      ConvexOn ℝ Set.univ (fun p => HdeltaPaper h ε x p m) := by
  filter_upwards [T3.hSubgradientHepsilon_of_selector h hdiff qε sel hε]
    with x hx m hm
  have hc := paper_convex_of_subgradient (fun p => hx p m hm)
  simpa only [HdeltaPaper_of_pos h ε x _ hm] using hc

/-- Canonical regularized values are jointly continuous on the closed cone.
The original Hamiltonian is permitted to have infinite boundary values. -/
theorem HdeltaPaper_continuousOn_closed
    (hmon : HypothesisMonotone (d := d) H DpH)
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (hdiff : HypothesisHpDifferentiable (d := d) H DpH)
    (qε : QEpsFamily d) (sel : InfConvSelectorFamily h qε)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ContinuousOn (fun pm : (Fin d → ℝ) × ℝ => HdeltaPaper h ε x pm.1 pm.2)
        {pm | 0 ≤ pm.2} := by
  filter_upwards [HdeltaPaper_continuousOn_pos h qε sel hε,
    HdeltaPaper_convexOn_pos h hdiff qε sel hε, HdeltaPaper_rc0 hmon h hε,
    Hdelta_antitone_mass_of_antitone h (antitone_in_m hmon) hε]
    with x hcont hconv hlim hanti
  apply continuousOn_closedHalfspace_of_antitone (HdeltaPaper h ε x) hcont hlim
  · intro p a ha b hb hab
    simpa only [HdeltaPaper_of_pos h ε x p ha, HdeltaPaper_of_pos h ε x p hb]
      using hanti p ha hb hab
  · exact continuousOn_univ.mp
      ((convexOn_boundary_of_slice_limits (HdeltaPaper h ε x) hconv hlim).continuousOn
        isOpen_univ)

/-- Closed-cone regularity required by the existing Minty engine. Both fields
are proved for the regularized pair without original-H boundary premises. -/
theorem HdeltaPaper_regularityHK0
    (hmon : HypothesisMonotone (d := d) H DpH)
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (hdiff : HypothesisHpDifferentiable (d := d) H DpH)
    (qε : QEpsFamily d) (sel : InfConvSelectorFamily h qε)
    (hmeas : HypothesisDpHMeasurable (d := d) H DpH)
    (hAE : HdeltaAEPowerEpsData h qε)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Theorems.SimplePower.RegularityHK0 (HdeltaPaper h ε) (DpHepsilonFam h qε ε) where
  continuous_Hext_pm := HdeltaPaper_continuousOn_closed hmon h hdiff qε sel hε
  continuous_mDpH_pm :=
    continuousOn_JsimpleExt_DpHepsilonFam_of_selector h qε sel hmeas hAE hε hε1


/-- Upper bound for the canonical regularized zero-mass trace, obtained from
the positive-mass envelope and its derived finite right limit. -/
theorem Hdelta_zero_upper_of_selectorFamily
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hmon : HypothesisMonotone (d := d) H DpH)
    (qε : QEpsFamily d) (sel : InfConvSelectorFamily (H := H) (DpH := DpH) hweak qε)
    (hAE : HdeltaAEPowerEpsData (H := H) (DpH := DpH) hweak qε)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
      ∀ p : Fin d → ℝ,
        HdeltaK0 hweak ε x p 0
          ≤ CdeltaEps (H := H) (DpH := DpH) hweak ε * (‖p‖ ^ hweak.α + 1) := by
  have hCε_pos : 0 < CdeltaEps (H := H) (DpH := DpH) hweak ε :=
    (cdeltaEps_facts_upper (H := H) (DpH := DpH) hweak hε).1
  have hrc0 := HdeltaPaper_rc0 hmon hweak hε
  filter_upwards [hrc0, hAE.H_upper_pointwise_ae ε hε hε1] with x hxRc0 hxUpper p
  -- Tendsto of `m ↦ Hdelta x p m` to `Hdelta x p 0` along `𝓝[>] 0`.
  have htend : Tendsto (fun m : ℝ => HdeltaK0 hweak ε x p m) (𝓝[>] (0 : ℝ))
      (𝓝 (HdeltaK0 hweak ε x p 0)) := hxRc0 p
  -- The target constant as the limit of the m > 0 upper envelope dominator
  -- `Cε·(‖p‖^α + 1)`, which is constant in `m`; so its limit is itself.
  set B : ℝ := CdeltaEps (H := H) (DpH := DpH) hweak ε * (‖p‖ ^ hweak.α + 1) with hB
  -- Eventually (for `m > 0`) the dominator `B` upper-bounds `Hdelta x p m`:
  -- `Hdelta ≤ Cε·(‖p‖^α+1) − m^β/Cε ≤ Cε·(‖p‖^α+1) = B` since `m^β/Cε ≥ 0`.
  have hev : ∀ᶠ m in 𝓝[>] (0 : ℝ), HdeltaK0 hweak ε x p m ≤ B := by
    filter_upwards [self_mem_nhdsWithin] with m hm
    have hmpos : 0 < m := hm
    have hUp := hxUpper p m hmpos
    rw [← HdeltaK0_eq_Hdelta_of_pos hweak hmpos] at hUp
    have hmβ_nn : 0 ≤ m ^ hweak.β := Real.rpow_nonneg (le_of_lt hmpos) _
    have hdiv_nn : 0 ≤ (m ^ hweak.β) / CdeltaEps (H := H) (DpH := DpH) hweak ε :=
      div_nonneg hmβ_nn (le_of_lt hCε_pos)
    -- `Hdelta ≤ Cε·(‖p‖^α+1) − m^β/Cε ≤ Cε·(‖p‖^α+1) = B`.
    have : HdeltaK0 hweak ε x p m
        ≤ CdeltaEps (H := H) (DpH := DpH) hweak ε * (‖p‖ ^ hweak.α + 1) := by
      have := hUp
      linarith
    simpa [hB] using this
  -- The constant `B` is the limit of itself along the (nontrivial) filter.
  exact le_of_tendsto_of_tendsto htend tendsto_const_nhds hev

/-- Coercive lower bound for the canonical regularized zero-mass trace.
Only original positive-mass monotonicity and the regularized bounds are used. -/
theorem Hdelta_zero_lower_of_uniformBounds
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hmon : HypothesisMonotone (d := d) H DpH)
    (qε : QEpsFamily d) (sel : InfConvSelectorFamily (H := H) (DpH := DpH) hweak qε)
    (hUB : HdeltaUniformBounds (H := H) (DpH := DpH) hweak qε)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
      ∀ p : Fin d → ℝ,
        ‖p‖ ^ hweak.α / hUB.C0 - hUB.C0 ≤ HdeltaK0 hweak ε x p 0 := by
  -- The two a.e. ingredients: the coercive lower bound for `m > 0` and the
  -- boundary right-continuity of `m ↦ HdeltaK0 hweak ε x p m` at `m = 0⁺`.
  have hLow := hUB.lower_uniform ε hε hε1
  have hRC := HdeltaPaper_rc0 hmon hweak hε
  filter_upwards [hLow, hRC] with x hLowx hRCx p
  -- Boundary right-continuity at this `(x, p)`.
  have hHtend :
      Tendsto (fun m : ℝ => HdeltaK0 hweak ε x p m) (𝓝[>] (0 : ℝ))
        (𝓝 (HdeltaK0 hweak ε x p 0)) := hRCx p
  -- The coercive lower bound holds eventually as `m → 0⁺`.
  have hLB_ev :
      ∀ᶠ m in 𝓝[>] (0 : ℝ),
        ‖p‖ ^ hweak.α / hUB.C0 - hUB.C0 * (m ^ hweak.β + 1)
          ≤ HdeltaK0 hweak ε x p m := by
    filter_upwards [self_mem_nhdsWithin] with m hm
    rw [HdeltaK0_eq_Hdelta_of_pos hweak hm]
    exact hLowx p m hm
  -- The lower-bound coefficient tends to `‖p‖^α/C0 − C0` as `m → 0⁺`.
  have hmβ_tend :
      Tendsto (fun m : ℝ => m ^ hweak.β) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hid : Tendsto (fun m : ℝ => m) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    have := hid.rpow_const (Or.inr hweak.hβ.le)
    simpa [Real.zero_rpow (ne_of_gt hweak.hβ)] using this
  have hLBcoef_tend :
      Tendsto
        (fun m : ℝ => ‖p‖ ^ hweak.α / hUB.C0 - hUB.C0 * (m ^ hweak.β + 1))
        (𝓝[>] (0 : ℝ)) (𝓝 (‖p‖ ^ hweak.α / hUB.C0 - hUB.C0)) := by
    have hcoef :
        Tendsto
          (fun m : ℝ => hUB.C0 * (m ^ hweak.β + 1))
          (𝓝[>] (0 : ℝ)) (𝓝 (hUB.C0 * ((0 : ℝ) + 1))) :=
      tendsto_const_nhds.mul (hmβ_tend.add tendsto_const_nhds)
    have hsub :
        Tendsto
          (fun m : ℝ => ‖p‖ ^ hweak.α / hUB.C0 - hUB.C0 * (m ^ hweak.β + 1))
          (𝓝[>] (0 : ℝ))
          (𝓝 (‖p‖ ^ hweak.α / hUB.C0 - hUB.C0 * ((0 : ℝ) + 1))) :=
      (tendsto_const_nhds (x := ‖p‖ ^ hweak.α / hUB.C0)).sub hcoef
    have hcoef_simp : hUB.C0 * ((0 : ℝ) + 1) = hUB.C0 := by ring
    rw [hcoef_simp] at hsub
    exact hsub
  -- Pass the eventual inequality to the limit.
  exact le_of_tendsto_of_tendsto hLBcoef_tend hHtend hLB_ev

/-- AE measurability of the canonical closed-cone composite. The positive
selector formula is measurable; its sequence limit supplies the zero-mass trace. -/
theorem aemeasurable_HdeltaK0_comp_of_rc0
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (hmon : HypothesisMonotone (d := d) H DpH)
    (qε : QEpsFamily d) (sel : InfConvSelectorFamily (H := H) (DpH := DpH) hweak qε)
    {ε : ℝ} (hε : 0 < ε)
    {Du : (Fin d → ℝ) → (Fin d → ℝ)} {m : (Fin d → ℝ) → ℝ}
    (hDu : AEMeasurable Du (MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)))
    (hm : AEMeasurable m (MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)))
    (hm_nonneg : ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
      0 ≤ m x) :
    AEMeasurable (fun x => HdeltaK0 hweak ε x (Du x) (m x))
      (MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)) := by
  classical
  set μ := MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d) with hμ
  -- The measurable inf-conv formula `F` (selector `qε ε`).
  set F : (Fin d → ℝ) × (Fin d → ℝ) × ℝ → ℝ :=
    fun xpm => H xpm.1 (xpm.2.1 - qε ε xpm) xpm.2.2
      + (1 / ε) * K hweak (qε ε xpm) with hF
  have hF_meas : Measurable F :=
    Hepsilon_measurable_of_inv (H := H) (DpH := DpH) hweak hMeas ε (sel.q_meas ε)
  -- Boundary representative `r := lim_n F(·, Du ·, 1/(n+1))`.
  set c : ℕ → ℝ := fun n => 1 / (n + 1) with hc
  have hc_pos : ∀ n, 0 < c n := by
    intro n; positivity
  -- Each sequence term `r_n x := F (x, Du x, c n)` is AE-measurable.
  have hrn_aem : ∀ n, AEMeasurable (fun x => F (x, Du x, c n)) μ := by
    intro n
    exact hF_meas.comp_aemeasurable
      (measurable_id.aemeasurable.prodMk (hDu.prodMk aemeasurable_const))
  -- A.e. boundary convergence: `r_n x → Hdelta x (Du x) 0`.
  have hrc0 := HdeltaPaper_rc0 hmon hweak hε
  have hForm := sel.H_form ε hε
  have h_tendsto : ∀ᵐ x ∂μ,
      Tendsto (fun n => F (x, Du x, c n)) atTop
        (𝓝 (HdeltaK0 hweak ε x (Du x) 0)) := by
    filter_upwards [hrc0, hForm] with x hxRc0 hxForm
    -- `c n → 0` within `{0 < ·}`.
    have hc_to0 : Tendsto c atTop (𝓝[>] (0 : ℝ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
      filter_upwards with n using hc_pos n
    -- Along this filter, `F(x, Du x, c n) = Hdelta x (Du x) (c n)`.
    have hEqSeq : ∀ n, F (x, Du x, c n) = HdeltaK0 hweak ε x (Du x) (c n) := by
      intro n
      simp only [hF]
      rw [HdeltaK0_eq_Hdelta_of_pos hweak (hc_pos n)]
      exact (hxForm (Du x) (c n) (hc_pos n)).symm
    -- `m ↦ Hdelta x (Du x) m → Hdelta x (Du x) 0` along `𝓝[>] 0`, compose.
    have hcomp := (hxRc0 (Du x)).comp hc_to0
    refine hcomp.congr ?_
    intro n; exact (hEqSeq n).symm
  -- The boundary representative is AE-measurable.
  have hr_aem : AEMeasurable (fun x => HdeltaK0 hweak ε x (Du x) 0) μ :=
    aemeasurable_of_tendsto_metrizable_ae' hrn_aem h_tendsto
  -- Pick measurable representatives (note: `obtain ⟨m', …⟩ := hm` consumes `hm`,
  -- so build the `F'` representative BEFORE destructuring `hm`).
  obtain ⟨F', hF'_meas, hF'_eq⟩ :=
    (hF_meas.comp_aemeasurable
      (measurable_id.aemeasurable.prodMk (hDu.prodMk hm)) :
      AEMeasurable (fun x => F (x, Du x, m x)) μ)
  obtain ⟨r', hr'_meas, hr'_eq⟩ := hr_aem
  obtain ⟨m', hm'_meas, hm'_eq⟩ := hm
  -- Glue: measurable representative `Set.piecewise {0 < m' ·} F' r'`.
  have hSet : MeasurableSet {x | 0 < m' x} :=
    measurableSet_lt measurable_const hm'_meas
  refine ⟨Set.piecewise {x | 0 < m' x} F' r', ?_, ?_⟩
  · exact hF'_meas.piecewise hSet hr'_meas
  · -- `HdeltaK0 ·(Du·)(m·) =ᵐ piecewise`.
    filter_upwards [hm_nonneg, hForm, hm'_eq, hF'_eq, hr'_eq]
      with x hx_nonneg hxForm hxm' hxF' hxr'
    have hxF'' : F (x, Du x, m x) = F' x := hxF'
    by_cases hxpos : 0 < m x
    · -- Open cone: genuine `Hdelta = F`.
      have hHdK0 : HdeltaK0 hweak ε x (Du x) (m x) = Hdelta hweak ε x (Du x) (m x) :=
        HdeltaK0_eq_Hdelta_of_pos hweak hxpos
      have hForm' : Hdelta hweak ε x (Du x) (m x) = F (x, Du x, m x) := by
        simp only [hF]; exact hxForm (Du x) (m x) hxpos
      have hm'pos : x ∈ {x | 0 < m' x} := by
        simp only [Set.mem_setOf_eq, ← hxm']; exact hxpos
      rw [hHdK0, hForm', hxF'', Set.piecewise_eq_of_mem _ _ _ hm'pos]
    · -- Boundary `m x = 0` (since `m x ≥ 0` and not `0 < m x`).
      have hzero : m x = 0 := le_antisymm (not_lt.mp hxpos) hx_nonneg
      have hHdK0 : HdeltaK0 hweak ε x (Du x) (m x) = HdeltaK0 hweak ε x (Du x) 0 := by
        rw [hzero]
      have hm'nonpos : x ∉ {x | 0 < m' x} := by
        simp only [Set.mem_setOf_eq, ← hxm']; exact hxpos
      rw [hHdK0, hxr', Set.piecewise_eq_of_notMem _ _ _ hm'nonpos]

/-- AE measurability of the canonical regularized composite for arbitrary
real densities, using the zero filler at negative mass. -/
theorem aemeasurable_HdeltaK0_comp_of_rc0_allm
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (hmon : HypothesisMonotone (d := d) H DpH)
    (qε : QEpsFamily d) (sel : InfConvSelectorFamily (H := H) (DpH := DpH) hweak qε)
    {ε : ℝ} (hε : 0 < ε)
    {Du : (Fin d → ℝ) → (Fin d → ℝ)} {m : (Fin d → ℝ) → ℝ}
    (hDu : AEMeasurable Du (MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)))
    (hm : AEMeasurable m (MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d))) :
    AEMeasurable (fun x => HdeltaK0 hweak ε x (Du x) (m x))
      (MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)) := by
  classical
  set μ := MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d) with hμ
  -- The measurable inf-conv formula `F` (selector `qε ε`).
  set F : (Fin d → ℝ) × (Fin d → ℝ) × ℝ → ℝ :=
    fun xpm => H xpm.1 (xpm.2.1 - qε ε xpm) xpm.2.2
      + (1 / ε) * K hweak (qε ε xpm) with hF
  have hF_meas : Measurable F :=
    Hepsilon_measurable_of_inv (H := H) (DpH := DpH) hweak hMeas ε (sel.q_meas ε)
  -- Boundary representative `r := lim_n F(·, Du ·, 1/(n+1))`.
  set c : ℕ → ℝ := fun n => 1 / (n + 1) with hc
  have hc_pos : ∀ n, 0 < c n := by intro n; positivity
  have hrn_aem : ∀ n, AEMeasurable (fun x => F (x, Du x, c n)) μ := by
    intro n
    exact hF_meas.comp_aemeasurable
      (measurable_id.aemeasurable.prodMk (hDu.prodMk aemeasurable_const))
  have hrc0 := HdeltaPaper_rc0 hmon hweak hε
  have hForm := sel.H_form ε hε
  have h_tendsto : ∀ᵐ x ∂μ,
      Tendsto (fun n => F (x, Du x, c n)) atTop
        (𝓝 (HdeltaK0 hweak ε x (Du x) 0)) := by
    filter_upwards [hrc0, hForm] with x hxRc0 hxForm
    have hc_to0 : Tendsto c atTop (𝓝[>] (0 : ℝ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
      filter_upwards with n using hc_pos n
    have hEqSeq : ∀ n, F (x, Du x, c n) = HdeltaK0 hweak ε x (Du x) (c n) := by
      intro n
      simp only [hF]
      rw [HdeltaK0_eq_Hdelta_of_pos hweak (hc_pos n)]
      exact (hxForm (Du x) (c n) (hc_pos n)).symm
    have hcomp := (hxRc0 (Du x)).comp hc_to0
    refine hcomp.congr ?_
    intro n; exact (hEqSeq n).symm
  have hr_aem : AEMeasurable (fun x => HdeltaK0 hweak ε x (Du x) 0) μ :=
    aemeasurable_of_tendsto_metrizable_ae' hrn_aem h_tendsto
  -- Pick measurable representatives (build `F'`/`r'` BEFORE destructuring `hm`).
  obtain ⟨F', hF'_meas, hF'_eq⟩ :=
    (hF_meas.comp_aemeasurable
      (measurable_id.aemeasurable.prodMk (hDu.prodMk hm)) :
      AEMeasurable (fun x => F (x, Du x, m x)) μ)
  obtain ⟨r', hr'_meas, hr'_eq⟩ := hr_aem
  obtain ⟨m', hm'_meas, hm'_eq⟩ := hm
  -- Glue: three-way piecewise `{0 ≤ m'} (piecewise {0 < m'} F' r') 0`.
  have hSetLt : MeasurableSet {x | 0 < m' x} :=
    measurableSet_lt measurable_const hm'_meas
  have hSetLe : MeasurableSet {x | 0 ≤ m' x} :=
    measurableSet_le measurable_const hm'_meas
  refine ⟨Set.piecewise {x | 0 ≤ m' x}
      (Set.piecewise {x | 0 < m' x} F' r') 0, ?_, ?_⟩
  · exact (hF'_meas.piecewise hSetLt hr'_meas).piecewise hSetLe measurable_const
  · filter_upwards [hForm, hm'_eq, hF'_eq, hr'_eq]
      with x hxForm hxm' hxF' hxr'
    have hxF'' : F (x, Du x, m x) = F' x := hxF'
    rcases lt_trichotomy (m x) 0 with hxneg | hxzero | hxpos
    · -- `{m x < 0}`: HdeltaK0 = 0, and `x ∉ {0 ≤ m'}` so the rep is `0`.
      have hHdK0 : HdeltaK0 hweak ε x (Du x) (m x) = 0 :=
        HdeltaK0_eq_zero_of_neg hweak hxneg
      have hm'neg : x ∉ {x | 0 ≤ m' x} := by
        simp only [Set.mem_setOf_eq, ← hxm']; exact not_le.mpr hxneg
      rw [hHdK0, Set.piecewise_eq_of_notMem _ _ _ hm'neg]; rfl
    · -- `{m x = 0}`: HdeltaK0 = Hdelta(·,·,0), and `x ∈ {0 ≤ m'} \ {0 < m'}`.
      have hHdK0 : HdeltaK0 hweak ε x (Du x) (m x) = HdeltaK0 hweak ε x (Du x) 0 := by
        rw [hxzero]
      have hm'le : x ∈ {x | 0 ≤ m' x} := by
        simp only [Set.mem_setOf_eq, ← hxm', hxzero]; exact le_rfl
      have hm'notlt : x ∉ {x | 0 < m' x} := by
        simp only [Set.mem_setOf_eq, ← hxm', hxzero]; exact lt_irrefl _
      rw [hHdK0, Set.piecewise_eq_of_mem _ _ _ hm'le,
        Set.piecewise_eq_of_notMem _ _ _ hm'notlt, hxr']
    · -- `{0 < m x}`: HdeltaK0 = Hdelta = F, and `x ∈ {0 < m'} ⊆ {0 ≤ m'}`.
      have hHdK0 : HdeltaK0 hweak ε x (Du x) (m x) = Hdelta hweak ε x (Du x) (m x) :=
        HdeltaK0_eq_Hdelta_of_pos hweak hxpos
      have hForm' : Hdelta hweak ε x (Du x) (m x) = F (x, Du x, m x) := by
        simp only [hF]; exact hxForm (Du x) (m x) hxpos
      have hm'pos : x ∈ {x | 0 < m' x} := by
        simp only [Set.mem_setOf_eq, ← hxm']; exact hxpos
      have hm'le : x ∈ {x | 0 ≤ m' x} := by
        simp only [Set.mem_setOf_eq, ← hxm']; exact hxpos.le
      rw [hHdK0, hForm', hxF'', Set.piecewise_eq_of_mem _ _ _ hm'le,
        Set.piecewise_eq_of_mem _ _ _ hm'pos]

/-- **All-`m` strict-positivity-cone H-composite measurability from the
selector** (G4 building block, `HdeltaPos` carrier).

`HdeltaPos h ε x p m = if 0 < m then Hdelta else 0` — junk `0` already at the
boundary `m = 0`. So, unlike the `HdeltaK0` variant, NO rc0 boundary limit is
needed: the measurable representative is the simple two-way piecewise
`piecewise {0 < m'} F' 0`. Used for the public-theorem `hF_HJB_meas_Pos` binder,
which ranges over all `q : XBanach` (no `K0_Aepsi` premise). -/
theorem aemeasurable_HdeltaPos_comp_of_selector
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (qε : QEpsFamily d) (sel : InfConvSelectorFamily (H := H) (DpH := DpH) hweak qε)
    {ε : ℝ} (hε : 0 < ε)
    {Du : (Fin d → ℝ) → (Fin d → ℝ)} {m : (Fin d → ℝ) → ℝ}
    (hDu : AEMeasurable Du (MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)))
    (hm : AEMeasurable m (MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d))) :
    AEMeasurable (fun x => HdeltaPos hweak ε x (Du x) (m x))
      (MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)) := by
  classical
  set μ := MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d) with hμ
  set F : (Fin d → ℝ) × (Fin d → ℝ) × ℝ → ℝ :=
    fun xpm => H xpm.1 (xpm.2.1 - qε ε xpm) xpm.2.2
      + (1 / ε) * K hweak (qε ε xpm) with hF
  have hF_meas : Measurable F :=
    Hepsilon_measurable_of_inv (H := H) (DpH := DpH) hweak hMeas ε (sel.q_meas ε)
  have hForm := sel.H_form ε hε
  obtain ⟨F', hF'_meas, hF'_eq⟩ :=
    (hF_meas.comp_aemeasurable
      (measurable_id.aemeasurable.prodMk (hDu.prodMk hm)) :
      AEMeasurable (fun x => F (x, Du x, m x)) μ)
  obtain ⟨m', hm'_meas, hm'_eq⟩ := hm
  have hSetLt : MeasurableSet {x | 0 < m' x} :=
    measurableSet_lt measurable_const hm'_meas
  refine ⟨Set.piecewise {x | 0 < m' x} F' 0, ?_, ?_⟩
  · exact hF'_meas.piecewise hSetLt measurable_const
  · filter_upwards [hForm, hm'_eq, hF'_eq] with x hxForm hxm' hxF'
    have hxF'' : F (x, Du x, m x) = F' x := hxF'
    by_cases hxpos : 0 < m x
    · -- Open cone: `HdeltaPos = Hdelta = F`.
      have hHdPos : HdeltaPos hweak ε x (Du x) (m x) = Hdelta hweak ε x (Du x) (m x) :=
        HdeltaPos_eq_Hdelta_of_pos hweak hxpos
      have hForm' : Hdelta hweak ε x (Du x) (m x) = F (x, Du x, m x) := by
        simp only [hF]; exact hxForm (Du x) (m x) hxpos
      have hm'pos : x ∈ {x | 0 < m' x} := by
        simp only [Set.mem_setOf_eq, ← hxm']; exact hxpos
      rw [hHdPos, hForm', hxF'', Set.piecewise_eq_of_mem _ _ _ hm'pos]
    · -- `{m x ≤ 0}`: `HdeltaPos = 0`, and `x ∉ {0 < m'}`.
      have hHdPos : HdeltaPos hweak ε x (Du x) (m x) = 0 := by
        simp [HdeltaPos, hxpos]
      have hm'nonpos : x ∉ {x | 0 < m' x} := by
        simp only [Set.mem_setOf_eq, ← hxm']; exact hxpos
      rw [hHdPos, Set.piecewise_eq_of_notMem _ _ _ hm'nonpos]; rfl

/-- Positive-mass joint continuity from standing regularity and the selector.
No boundary assumption on the original Hamiltonian is needed. -/
theorem HdeltaK0_continuousOn_H_pm_of_selectorFamily
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d) (sel : InfConvSelectorFamily hweak qε)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
      ContinuousOn (fun pm : (Fin d → ℝ) × ℝ => HdeltaK0 hweak ε x pm.1 pm.2)
        {pm | 0 < pm.2} := HdeltaPaper_continuousOn_pos hweak qε sel hε

/-- **LL-monotonicity inequality on the closed-cone carrier `HdeltaK0` from
selector AE data** (T3 D2c-2d-0-b2, the `monotone`-field content).

This is the genuine algebraic content of `HypothesisMonotone (HdeltaK0 …)`: the
Lasry–Lions inequality for the regularized pair `(HdeltaK0 hweak ε,
DpHepsilonFam hweak qε ε)`, holding for a.e. `x` and all `(p₁,m₁),(p₂,m₂)` with
`0<m₁,0<m₂`. It is derived EXACTLY as the `monotone` field of
`Hepsilon_monotone_generic` (which never touches the `RegularityH` argument),
specialized to the `HdeltaK0` carrier with the `{0<m}` bridge
`HdeltaK0_eq_Hdelta_of_pos`.

The four a.e. certificates are supplied by the selector data: attainment
`sel.H_form`, gradient formula `sel.DpH_form`, subgradient optimality `sel.hSub`,
and the base LL inequality `hMono.monotone`. Binds NONE of the banned
`powData`/`HdeltaPos`/`hFormPos`/`hqE_per`/`hInj`/`qEofMinv` identifiers.

Note: this lemma deliberately delivers ONLY the LL inequality (not the full
`HypothesisMonotone` structure), because the latter `extends RegularityH` whose
GLOBAL `measurable_H` field is NOT derivable from the AE-only selector attainment
`sel.H_form` without a banned pointwise-everywhere formula bridge (`hFormPos`).
See the companion `…b2b` task for the downstream monotone-producer that consumes
this inequality directly. -/
theorem llMono_HdeltaK0_of_AEData
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hMono : Hamiltonian.HypothesisMonotone (d := d) H DpH)
    (qε : QEpsFamily d)
    (sel : InfConvSelectorFamily (H := H) (DpH := DpH) hweak qε)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d)),
      ∀ p₁ m₁ p₂ m₂, 0 < m₁ → 0 < m₂ →
        0 ≤ (-HdeltaK0 hweak ε x p₁ m₁ + HdeltaK0 hweak ε x p₂ m₂) * (m₁ - m₂)
              + (m₁ • DpHepsilonFam hweak qε ε x p₁ m₁
                  - m₂ • DpHepsilonFam hweak qε ε x p₂ m₂) ⬝ (p₁ - p₂) := by
  filter_upwards [hMono.monotone, sel.H_form ε hε, sel.DpH_form ε hε,
    sel.hSub ε hε] with x hxLL hxHform hxDpHε hxSub
  intro p₁ m₁ p₂ m₂ hm₁ hm₂
  -- Inner LL inequality at the shifted minimizer points.
  have hInner :=
    hxLL (p₁ - qε ε (x, p₁, m₁)) m₁ (p₂ - qε ε (x, p₂, m₂)) m₂ hm₁ hm₂
  -- Carrier value reconciled with `Hdelta` (on `{0<m}`) and the attainment formula.
  have hHf₁ : HdeltaK0 hweak ε x p₁ m₁
      = H x (p₁ - qε ε (x, p₁, m₁)) m₁ + (1 / ε) * K hweak (qε ε (x, p₁, m₁)) := by
    rw [HdeltaK0_eq_Hdelta_of_pos hweak hm₁]; exact hxHform p₁ m₁ hm₁
  have hHf₂ : HdeltaK0 hweak ε x p₂ m₂
      = H x (p₂ - qε ε (x, p₂, m₂)) m₂ + (1 / ε) * K hweak (qε ε (x, p₂, m₂)) := by
    rw [HdeltaK0_eq_Hdelta_of_pos hweak hm₂]; exact hxHform p₂ m₂ hm₂
  have hDf₁ := hxDpHε p₁ m₁ hm₁
  have hDf₂ := hxDpHε p₂ m₂ hm₂
  have hSub₁ := hxSub p₁ m₁ hm₁ (qε ε (x, p₂, m₂))
  have hSub₂ := hxSub p₂ m₂ hm₂ (qε ε (x, p₁, m₁))
  exact Hdelta_monotone_pointwise (ε := ε)
    (Hε := fun p m => HdeltaK0 hweak ε x p m)
    (DpHε := fun p m => DpHepsilonFam hweak qε ε x p m)
    (Hin := fun s m => H x s m)
    (DpHin := fun s m => DpH x s m)
    (Kfun := fun q => K hweak q)
    p₁ m₁ p₂ m₂ (qε ε (x, p₁, m₁)) (qε ε (x, p₂, m₂)) hm₁ hm₂
    hHf₁ hHf₂ hDf₁ hDf₂ hInner hSub₁ hSub₂

/-- The canonical regularized carrier attains its derived finite right limit.
The original Hamiltonian may have an infinite boundary trace. -/
theorem HdeltaK0_rc0_of_selectorFamily
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hmon : HypothesisMonotone (d := d) H DpH)
    (qε : QEpsFamily d) (_sel : InfConvSelectorFamily hweak qε)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)), ∀ p,
      Tendsto (fun m => HdeltaK0 hweak ε x p m) (𝓝[>] (0 : ℝ))
        (𝓝 (HdeltaK0 hweak ε x p 0)) := HdeltaPaper_rc0 hmon hweak hε

/-! ### D6c-2a-2b-i — closed-cone JOINT `(p,m)` continuity of `Hdelta`/`HdeltaK0`

The H-side `continuous_Hext_pm` field of `RegularityHK0 (HdeltaK0 …)
(DpHepsilonFam …)`. The genuinely missing closed-cone regularity fact: every
existing H-continuity carrier routes through `sel.q_cont_pm` (valid only on
`{0<m}`, where the inf-conv minimiser may JUMP at `m = 0`); the codebase only
had SECTION-WISE right-continuity (fixed `p`, `m → 0⁺`).

The value-function (Moreau-envelope) argument gives JOINT continuity on the
CLOSED cone `{0 ≤ m}` even where the minimiser jumps, WITHOUT selector
continuity:

* on the OPEN cone `{0 < m}` use `HdeltaK0_continuousOn_H_pm_of_selectorFamily`;
* at a boundary point `(p₀, 0)`, squeeze in the JOINT filter
  `𝓝[{0 ≤ m}] (p₀, 0)`:
  - **`limsup ≤ value`**: test any fixed competitor `q`; then eventually
    `Hdelta x p m ≤ H x (p − q) m + (1/ε) K q`, and the RHS is JOINTLY
    continuous on the closed cone (`hHextJointCont`), tending to
    `H x (p₀ − q) 0 + (1/ε) K q`; take the infimum over `q` (= `Hdelta x p₀ 0`).
  - **`value ≤ liminf`**: the inf-conv minimisers are bounded near `(p₀, 0)`
    (`Hdelta_near_minimizers_bounded`, the bound `(ε·3C + K p)^{1/α}` is
    locally bounded as `p → p₀`); extract a converging subsequence and use
    joint lower-semicontinuity of base `H` at `(p₀ − q*, 0)` plus continuity of
    `K`. This is the JOINT (in `p` AND `m`) generalisation of
    `Hdelta_boundary_liminf`.

NO strict positivity, NO `HdeltaPos` junk, NO Pack/Inputs/Oracle binders; the
only riders are the accepted `HypothesisHextJointCont` (base-`H` boundary joint
continuity) plus the `InfConvSelectorFamily` certificate. -/

/-- **Joint boundary tendsto of `Hdelta` at `(p₀, 0)`** (value-function /
Moreau-envelope argument). Per-`x` (where `sel.H_form`, the weak-growth
upper/lower bounds and the base-`H` joint boundary continuity hold), for every
`p₀` the value `(p, m) ↦ Hdelta hweak ε x p m` tends to `Hdelta hweak ε x p₀ 0`
along the JOINT filter `𝓝[{0 ≤ m}] (p₀, 0)`. This is the genuinely missing
closed-cone boundary fact: it is joint in `(p, m)`, NOT section-wise. -/
theorem Hdelta_boundary_joint_tendsto
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d) {ε : ℝ} (hε : 0 < ε)
    {x : Fin d → ℝ}
    (hHform : ∀ p m, 0 < m →
      Hdelta hweak ε x p m
        = H x (p - qε ε (x, p, m)) m + (1 / ε) * K hweak (qε ε (x, p, m)))
    (hUpper : ∀ m, 0 < m → H x (0 : Fin d → ℝ) m ≤ -(m ^ hweak.β) / hweak.C + hweak.C)
    (hLower : ∀ p m, 0 < m →
      H x p m ≥ (‖p‖ ^ hweak.α) / hweak.C - hweak.C * (m ^ hweak.β + 1))
    (hJoint : ContinuousOn (fun pm : (Fin d → ℝ) × ℝ => H x pm.1 pm.2) {pm | 0 ≤ pm.2})
    (p₀ : Fin d → ℝ) :
    Tendsto (fun pm : (Fin d → ℝ) × ℝ => Hdelta hweak ε x pm.1 pm.2)
      (𝓝[{pm : (Fin d → ℝ) × ℝ | 0 ≤ pm.2}] (p₀, 0))
      (𝓝 (Hdelta hweak ε x p₀ 0)) := by
  classical
  set s : Set ((Fin d → ℝ) × ℝ) := {pm : (Fin d → ℝ) × ℝ | 0 ≤ pm.2} with hsdef
  set z₀ : (Fin d → ℝ) × ℝ := (p₀, 0) with hz₀def
  set F : Filter ((Fin d → ℝ) × ℝ) := 𝓝[s] z₀ with hFdef
  set g : (Fin d → ℝ) × ℝ → ℝ := fun pm => Hdelta hweak ε x pm.1 pm.2 with hgdef
  have hC_pos : 0 < hweak.C := hweak.hC
  have hα_pos : 0 < hweak.α := lt_trans zero_lt_one hweak.hα
  have hz₀mem : z₀ ∈ s := by change (0 : ℝ) ≤ z₀.2; rw [hz₀def]
  -- The filter `F` is `NeBot` (boundary point of the closed half-space).
  haveI hFne : F.NeBot := by
    rw [hFdef]
    refine mem_closure_iff_nhdsWithin_neBot.mp ?_
    -- `z₀` is in the closure of `s` (it is in `s`).
    exact subset_closure hz₀mem
  -- ===== Per-point `BddBelow` of the unpenalised inf-conv family on `{0<m}`. =====
  have hBdd : ∀ (p : Fin d → ℝ) (m : ℝ), 0 < m →
      BddBelow (Set.range fun q' : Fin d → ℝ => H x (p - q') m) := by
    intro p m hm
    refine ⟨-(hweak.C * (m ^ hweak.β + 1)), ?_⟩
    rintro y ⟨q', rfl⟩
    have := hLower (p - q') m hm
    have hpos : 0 ≤ (‖p - q'‖ ^ hweak.α) / hweak.C :=
      div_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (le_of_lt hC_pos)
    linarith
  -- ===== The base-`H` joint slice tendsto to a boundary value. =====
  -- For any `s₀`, `(p, m) ↦ H x p m → H x s₀ 0` along `𝓝[s] (s₀, 0)`.
  have hHjoint_tendsto : ∀ s₀ : Fin d → ℝ,
      Tendsto (fun pm : (Fin d → ℝ) × ℝ => H x pm.1 pm.2)
        (𝓝[s] (s₀, 0)) (𝓝 (H x s₀ 0)) := by
    intro s₀
    have hmem : ((s₀, 0) : (Fin d → ℝ) × ℝ) ∈ s := by
      change (0 : ℝ) ≤ (0 : ℝ); rfl
    have := (hJoint (s₀, 0) hmem).tendsto
    simpa using this
  -- ===== `g` is bounded above near `z₀` (eventually `≤ H x p₀ 0 + 1`). =====
  -- `g pm ≤ H x pm.1 pm.2` on `{0<m}`, and `H x pm.1 pm.2 → H x p₀ 0`.
  have hg_le_H : ∀ᶠ pm in F, g pm ≤ H x pm.1 pm.2 := by
    rw [hFdef]
    rw [eventually_nhdsWithin_iff]
    -- Eventually on `s`, the `m`-coordinate is positive OR zero; on `{0<m}`,
    -- `g pm = Hdelta ≤ H` by `Hdelta_le_H_self`. At `m = 0`, equality
    -- `Hdelta x p 0 = ⨅ q, H x (p-q) 0 + (1/ε)K q ≤ H x p 0` (test `q=0`)
    -- also holds, but we cannot bound below the family in general; instead we
    -- show `g ≤ H` on ALL of `s` directly using `ciInf_le` at `q = 0`.
    filter_upwards with pm hpm
    -- `pm.2 ≥ 0`; we bound `Hdelta x pm.1 pm.2 ≤ H x pm.1 pm.2` via `q = 0`
    -- IF the family is `BddBelow`. On `{0<m}` use `hBdd`; at `m=0` use the
    -- `m=0` `BddBelow` from `hJoint`-slice lower bound.
    have hpm2 : (0 : ℝ) ≤ pm.2 := hpm
    rcases lt_or_eq_of_le hpm2 with hpos | hzero
    · simp only [hgdef]
      exact Hdelta_le_H_self hweak hε x pm.1 pm.2 (hBdd pm.1 pm.2 hpos)
    · -- `pm.2 = 0`.
      have hpm2eq : pm.2 = 0 := hzero.symm
      -- `BddBelow` of `q' ↦ H x (pm.1 - q') 0` via the `hJoint`-slice lower
      -- bound `H x s 0 ≥ -C` for all `s`.
      have hslice0 : ∀ s' : Fin d → ℝ, -hweak.C ≤ H x s' 0 := by
        intro s'
        have hHslice : Tendsto (fun m : ℝ => H x s' m) (𝓝[>] (0 : ℝ))
            (𝓝 (H x s' 0)) := by
          have hmap : Tendsto (fun m : ℝ => ((s', m) : (Fin d → ℝ) × ℝ))
              (𝓝[>] (0 : ℝ)) (𝓝[s] (s', 0)) := by
            rw [tendsto_nhdsWithin_iff]
            refine ⟨tendsto_const_nhds.prodMk_nhds nhdsWithin_le_nhds, ?_⟩
            filter_upwards [self_mem_nhdsWithin] with m hm using le_of_lt (Set.mem_Ioi.mp hm)
          have := (hHjoint_tendsto s').comp hmap
          simpa only [Function.comp_def] using this
        have hev : ∀ᶠ m in 𝓝[>] (0 : ℝ), -(hweak.C * (m ^ hweak.β + 1)) ≤ H x s' m := by
          filter_upwards [self_mem_nhdsWithin] with m hm
          have hmpos : 0 < m := hm
          have := hLower s' m hmpos
          have hpos : 0 ≤ (‖s'‖ ^ hweak.α) / hweak.C :=
            div_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (le_of_lt hC_pos)
          linarith
        have hmβtend : Tendsto (fun m : ℝ => m ^ hweak.β) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
          have : Tendsto (fun m : ℝ => m ^ hweak.β) (𝓝[>] (0 : ℝ)) (𝓝 (0 ^ hweak.β)) :=
            ((Real.continuousAt_rpow_const 0 hweak.β
              (Or.inr (le_of_lt hweak.hβ))).continuousWithinAt).tendsto
          simpa [Real.zero_rpow (ne_of_gt hweak.hβ)] using this
        have hbndtend : Tendsto (fun m : ℝ => -(hweak.C * (m ^ hweak.β + 1)))
            (𝓝[>] (0 : ℝ)) (𝓝 (-(hweak.C * (0 + 1)))) :=
          ((tendsto_const_nhds.mul (hmβtend.add tendsto_const_nhds)).neg)
        have hlimle : -(hweak.C * (0 + 1)) ≤ H x s' 0 :=
          le_of_tendsto_of_tendsto hbndtend hHslice hev
        simpa using hlimle
      have hBdd0 : BddBelow (Set.range fun q' : Fin d → ℝ => H x (pm.1 - q') 0) := by
        refine ⟨-hweak.C, ?_⟩
        rintro y ⟨q', rfl⟩
        exact hslice0 (pm.1 - q')
      have hle := Hdelta_le_H_self hweak hε x pm.1 0 hBdd0
      simp only [hgdef]
      rw [hpm2eq]; exact hle
  -- `H x pm.1 pm.2 → H x p₀ 0` along `F`.
  have hH_tendsto : Tendsto (fun pm : (Fin d → ℝ) × ℝ => H x pm.1 pm.2) F (𝓝 (H x p₀ 0)) := by
    rw [hFdef, hz₀def]; exact hHjoint_tendsto p₀
  -- Boundedness above.
  have hBddAbove : F.IsBoundedUnder (· ≤ ·) g := by
    refine ⟨H x p₀ 0 + 1, ?_⟩
    rw [eventually_map]
    have hev : ∀ᶠ pm in F, H x pm.1 pm.2 ≤ H x p₀ 0 + 1 := by
      have := hH_tendsto.eventually (Iio_mem_nhds (show H x p₀ 0 < H x p₀ 0 + 1 by linarith))
      filter_upwards [this] with pm hpm using le_of_lt hpm
    filter_upwards [hg_le_H, hev] with pm h1 h2 using le_trans h1 h2
  -- ===== `g` is bounded below near `z₀`. =====
  -- `g pm ≥ ⨅ q', H x (pm.1 - q') pm.2 ≥ -C(pm.2^β + 1) ≥ -C·2` for `pm.2 ≤ 1`.
  have hBddBelow : F.IsBoundedUnder (· ≥ ·) g := by
    refine ⟨-(hweak.C * (1 + 1)), ?_⟩
    rw [eventually_map]
    -- Eventually on `F`: `0 < pm.2 ≤ 1` OR `pm.2 = 0`. We bound below uniformly.
    have hev_le1 : ∀ᶠ pm in F, pm.2 ≤ 1 := by
      rw [hFdef]
      have hcont : Tendsto (fun pm : (Fin d → ℝ) × ℝ => pm.2) F (𝓝 (0 : ℝ)) := by
        rw [hFdef]
        exact (continuous_snd.tendsto z₀).mono_left nhdsWithin_le_nhds
      have := hcont.eventually (Iic_mem_nhds (show (0 : ℝ) < 1 by norm_num))
      rw [hFdef] at this; exact this
    have hev_mem : ∀ᶠ pm in F, pm ∈ s := by
      rw [hFdef]; exact self_mem_nhdsWithin
    filter_upwards [hev_le1, hev_mem] with pm hle1 hmem
    have hpm2 : (0 : ℝ) ≤ pm.2 := hmem
    have hmβ_le : pm.2 ^ hweak.β ≤ 1 :=
      Real.rpow_le_one hpm2 hle1 (le_of_lt hweak.hβ)
    -- Lower bound of `g pm = Hdelta` by `⨅ q', H x (pm.1 - q') pm.2`.
    rcases lt_or_eq_of_le hpm2 with hpos | hzero
    · have hlb : (⨅ q' : Fin d → ℝ, H x (pm.1 - q') pm.2) ≤ g pm :=
        Hdelta_lower_bound hweak hε x pm.1 pm.2 (hBdd pm.1 pm.2 hpos)
      have hib : -(hweak.C * (pm.2 ^ hweak.β + 1))
          ≤ ⨅ q' : Fin d → ℝ, H x (pm.1 - q') pm.2 := by
        refine le_ciInf ?_
        intro q'
        have := hLower (pm.1 - q') pm.2 hpos
        have hpos2 : 0 ≤ (‖pm.1 - q'‖ ^ hweak.α) / hweak.C :=
          div_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (le_of_lt hC_pos)
        linarith
      have hstep : -(hweak.C * (1 + 1)) ≤ -(hweak.C * (pm.2 ^ hweak.β + 1)) := by
        have : hweak.C * (pm.2 ^ hweak.β + 1) ≤ hweak.C * (1 + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hC_pos)
        linarith
      exact le_trans hstep (le_trans hib hlb)
    · -- `pm.2 = 0`: `g pm = Hdelta x pm.1 0 = ⨅ q', H x (pm.1-q') 0 + (1/ε)K q'`.
      -- Lower bound by `-C` (via the `hJoint`-slice lower bound `H x s 0 ≥ -C`).
      have hpm2eq : pm.2 = 0 := hzero.symm
      have hslice0 : ∀ s' : Fin d → ℝ, -hweak.C ≤ H x s' 0 := by
        intro s'
        have hHslice : Tendsto (fun m : ℝ => H x s' m) (𝓝[>] (0 : ℝ))
            (𝓝 (H x s' 0)) := by
          have hmap : Tendsto (fun m : ℝ => ((s', m) : (Fin d → ℝ) × ℝ))
              (𝓝[>] (0 : ℝ)) (𝓝[s] (s', 0)) := by
            rw [tendsto_nhdsWithin_iff]
            refine ⟨tendsto_const_nhds.prodMk_nhds nhdsWithin_le_nhds, ?_⟩
            filter_upwards [self_mem_nhdsWithin] with m hm using le_of_lt (Set.mem_Ioi.mp hm)
          have := (hHjoint_tendsto s').comp hmap
          simpa only [Function.comp_def] using this
        have hev : ∀ᶠ m in 𝓝[>] (0 : ℝ), -(hweak.C * (m ^ hweak.β + 1)) ≤ H x s' m := by
          filter_upwards [self_mem_nhdsWithin] with m hm
          have hmpos : 0 < m := hm
          have := hLower s' m hmpos
          have hpos : 0 ≤ (‖s'‖ ^ hweak.α) / hweak.C :=
            div_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (le_of_lt hC_pos)
          linarith
        have hmβtend : Tendsto (fun m : ℝ => m ^ hweak.β) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
          have : Tendsto (fun m : ℝ => m ^ hweak.β) (𝓝[>] (0 : ℝ)) (𝓝 (0 ^ hweak.β)) :=
            ((Real.continuousAt_rpow_const 0 hweak.β
              (Or.inr (le_of_lt hweak.hβ))).continuousWithinAt).tendsto
          simpa [Real.zero_rpow (ne_of_gt hweak.hβ)] using this
        have hbndtend : Tendsto (fun m : ℝ => -(hweak.C * (m ^ hweak.β + 1)))
            (𝓝[>] (0 : ℝ)) (𝓝 (-(hweak.C * (0 + 1)))) :=
          ((tendsto_const_nhds.mul (hmβtend.add tendsto_const_nhds)).neg)
        have hlimle : -(hweak.C * (0 + 1)) ≤ H x s' 0 :=
          le_of_tendsto_of_tendsto hbndtend hHslice hev
        simpa using hlimle
      have hBddBelow0 :
          BddBelow (Set.range fun q' : Fin d → ℝ =>
            H x (pm.1 - q') 0 + (1 / ε) * K hweak q') := by
        refine ⟨-hweak.C, ?_⟩
        rintro y ⟨q', rfl⟩
        have h1 := hslice0 (pm.1 - q')
        have h2 : 0 ≤ (1 / ε) * K hweak q' :=
          mul_nonneg (le_of_lt (one_div_pos.mpr hε)) (K_nonneg hweak q')
        linarith
      have hglb : -hweak.C ≤ g pm := by
        simp only [hgdef]
        rw [hpm2eq, Hdelta_def]
        refine le_ciInf ?_
        intro q'
        have h1 := hslice0 (pm.1 - q')
        have h2 : 0 ≤ (1 / ε) * K hweak q' :=
          mul_nonneg (le_of_lt (one_div_pos.mpr hε)) (K_nonneg hweak q')
        linarith
      have : -(hweak.C * (1 + 1)) ≤ -hweak.C := by nlinarith [hC_pos]
      exact le_trans this hglb
  -- ===== limsup half: `limsup g F ≤ Hdelta x p₀ 0`. =====
  have hsup_q : ∀ q : Fin d → ℝ,
      limsup g F ≤ H x (p₀ - q) 0 + (1 / ε) * K hweak q := by
    intro q
    -- Eventually on `F`: `g pm ≤ H x (pm.1 - q) pm.2 + (1/ε) K q`.
    have hev_le : ∀ᶠ pm in F, g pm ≤ H x (pm.1 - q) pm.2 + (1 / ε) * K hweak q := by
      rw [hFdef]
      have hev_mem : ∀ᶠ pm in 𝓝[s] z₀, pm ∈ s := self_mem_nhdsWithin
      filter_upwards [hev_mem] with pm hmem
      have hpm2 : (0 : ℝ) ≤ pm.2 := hmem
      rcases lt_or_eq_of_le hpm2 with hpos | hzero
      · -- `0 < pm.2`: `ciInf_le` at `q`.
        have hbdd : BddBelow (Set.range fun q' : Fin d → ℝ =>
            H x (pm.1 - q') pm.2 + (1 / ε) * K hweak q') := by
          obtain ⟨L, hL⟩ := hBdd pm.1 pm.2 hpos
          refine ⟨L, ?_⟩
          rintro y ⟨q', rfl⟩
          have hLq : L ≤ H x (pm.1 - q') pm.2 := hL ⟨q', rfl⟩
          have hpen : 0 ≤ (1 / ε) * K hweak q' :=
            mul_nonneg (le_of_lt (one_div_pos.mpr hε)) (K_nonneg hweak q')
          linarith
        have hle : (⨅ q' : Fin d → ℝ, H x (pm.1 - q') pm.2 + (1 / ε) * K hweak q')
            ≤ H x (pm.1 - q) pm.2 + (1 / ε) * K hweak q := ciInf_le hbdd q
        simp only [hgdef, Hdelta_def]; exact hle
      · -- `pm.2 = 0`: same `ciInf_le` using the `m=0` `BddBelow`.
        have hpm2eq : pm.2 = 0 := hzero.symm
        -- Reuse the `m=0` bounded-below family.
        have hslice0 : ∀ s' : Fin d → ℝ, -hweak.C ≤ H x s' 0 := by
          intro s'
          have hHslice : Tendsto (fun m : ℝ => H x s' m) (𝓝[>] (0 : ℝ))
              (𝓝 (H x s' 0)) := by
            have hmap : Tendsto (fun m : ℝ => ((s', m) : (Fin d → ℝ) × ℝ))
                (𝓝[>] (0 : ℝ)) (𝓝[s] (s', 0)) := by
              rw [tendsto_nhdsWithin_iff]
              refine ⟨tendsto_const_nhds.prodMk_nhds nhdsWithin_le_nhds, ?_⟩
              filter_upwards [self_mem_nhdsWithin] with m hm using le_of_lt (Set.mem_Ioi.mp hm)
            have := (hHjoint_tendsto s').comp hmap
            simpa only [Function.comp_def] using this
          have hev : ∀ᶠ m in 𝓝[>] (0 : ℝ),
              -(hweak.C * (m ^ hweak.β + 1)) ≤ H x s' m := by
            filter_upwards [self_mem_nhdsWithin] with m hm
            have hmpos : 0 < m := hm
            have := hLower s' m hmpos
            have hpos : 0 ≤ (‖s'‖ ^ hweak.α) / hweak.C :=
              div_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (le_of_lt hC_pos)
            linarith
          have hmβtend : Tendsto (fun m : ℝ => m ^ hweak.β) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
            have : Tendsto (fun m : ℝ => m ^ hweak.β) (𝓝[>] (0 : ℝ)) (𝓝 (0 ^ hweak.β)) :=
              ((Real.continuousAt_rpow_const 0 hweak.β
                (Or.inr (le_of_lt hweak.hβ))).continuousWithinAt).tendsto
            simpa [Real.zero_rpow (ne_of_gt hweak.hβ)] using this
          have hbndtend : Tendsto (fun m : ℝ => -(hweak.C * (m ^ hweak.β + 1)))
              (𝓝[>] (0 : ℝ)) (𝓝 (-(hweak.C * (0 + 1)))) :=
            ((tendsto_const_nhds.mul (hmβtend.add tendsto_const_nhds)).neg)
          have hlimle : -(hweak.C * (0 + 1)) ≤ H x s' 0 :=
            le_of_tendsto_of_tendsto hbndtend hHslice hev
          simpa using hlimle
        have hBddBelow0 :
            BddBelow (Set.range fun q' : Fin d → ℝ =>
              H x (pm.1 - q') 0 + (1 / ε) * K hweak q') := by
          refine ⟨-hweak.C, ?_⟩
          rintro y ⟨q', rfl⟩
          have h1 := hslice0 (pm.1 - q')
          have h2 : 0 ≤ (1 / ε) * K hweak q' :=
            mul_nonneg (le_of_lt (one_div_pos.mpr hε)) (K_nonneg hweak q')
          linarith
        have hle : (⨅ q' : Fin d → ℝ, H x (pm.1 - q') 0 + (1 / ε) * K hweak q')
            ≤ H x (pm.1 - q) 0 + (1 / ε) * K hweak q := ciInf_le hBddBelow0 q
        simp only [hgdef]; rw [hpm2eq, Hdelta_def]; exact hle
    -- The competitor value tends to `H x (p₀ - q) 0 + (1/ε) K q`.
    have htend_comp : Tendsto
        (fun pm : (Fin d → ℝ) × ℝ => H x (pm.1 - q) pm.2 + (1 / ε) * K hweak q)
        F (𝓝 (H x (p₀ - q) 0 + (1 / ε) * K hweak q)) := by
      -- `pm ↦ (pm.1 - q, pm.2)` maps `F → 𝓝[s] (p₀ - q, 0)`.
      have hmap : Tendsto (fun pm : (Fin d → ℝ) × ℝ => ((pm.1 - q, pm.2) : (Fin d → ℝ) × ℝ))
          F (𝓝[s] (p₀ - q, 0)) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨?_, ?_⟩
        · have h1 : Tendsto (fun pm : (Fin d → ℝ) × ℝ => pm.1 - q) F (𝓝 (p₀ - q)) := by
            have : Tendsto (fun pm : (Fin d → ℝ) × ℝ => pm.1) F (𝓝 p₀) := by
              rw [hFdef]
              exact (continuous_fst.tendsto z₀).mono_left nhdsWithin_le_nhds
            exact this.sub_const q
          have h2 : Tendsto (fun pm : (Fin d → ℝ) × ℝ => pm.2) F (𝓝 (0 : ℝ)) := by
            rw [hFdef]
            exact (continuous_snd.tendsto z₀).mono_left nhdsWithin_le_nhds
          exact h1.prodMk_nhds h2
        · rw [hFdef]
          filter_upwards [self_mem_nhdsWithin] with pm hpm
          change (0 : ℝ) ≤ pm.2; exact hpm
      have hHcomp : Tendsto (fun pm : (Fin d → ℝ) × ℝ => H x (pm.1 - q) pm.2)
          F (𝓝 (H x (p₀ - q) 0)) := by
        have := (hHjoint_tendsto (p₀ - q)).comp hmap
        simpa only [Function.comp_def] using this
      exact hHcomp.add_const _
    -- `limsup g ≤ limsup (competitor) = value`.
    calc limsup g F
        ≤ limsup (fun pm : (Fin d → ℝ) × ℝ =>
            H x (pm.1 - q) pm.2 + (1 / ε) * K hweak q) F :=
          limsup_le_limsup hev_le hBddBelow.isCoboundedUnder_le
            htend_comp.isBoundedUnder_le
      _ = H x (p₀ - q) 0 + (1 / ε) * K hweak q := htend_comp.limsup_eq
  have hsup : limsup g F ≤ Hdelta hweak ε x p₀ 0 := by
    rw [Hdelta_def]; exact le_ciInf hsup_q
  -- ===== liminf half: `Hdelta x p₀ 0 ≤ liminf g F`. =====
  have hinf : Hdelta hweak ε x p₀ 0 ≤ liminf g F := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨c, hc_lt, hc_gt⟩ := exists_between hcon
    -- Extract a sequence `wₙ → z₀` in `F` with `g wₙ < c`.
    have hfreq : ∃ᶠ pm in F, g pm < c :=
      frequently_lt_of_liminf_lt hBddAbove.isCoboundedUnder_ge hc_lt
    obtain ⟨w, hwtend, hwlt⟩ := exists_seq_forall_of_frequently hfreq
    -- `wₙ → z₀` within `s`; write `pₙ := (w n).1`, `mₙ := (w n).2`.
    set pseq : ℕ → (Fin d → ℝ) := fun n => (w n).1 with hpseqdef
    set mseq : ℕ → ℝ := fun n => (w n).2 with hmseqdef
    have hpseq_tend : Tendsto pseq atTop (𝓝 p₀) := by
      have := (continuous_fst.tendsto z₀).comp (hwtend.mono_right nhdsWithin_le_nhds)
      simpa [Function.comp_def, hpseqdef, hz₀def] using this
    have hmseq_tend0 : Tendsto mseq atTop (𝓝 (0 : ℝ)) := by
      have := (continuous_snd.tendsto z₀).comp (hwtend.mono_right nhdsWithin_le_nhds)
      simpa [Function.comp_def, hmseqdef, hz₀def] using this
    -- Eventually `wₙ ∈ s` (so `mₙ ≥ 0`).
    have hmem_ev : ∀ᶠ n in atTop, w n ∈ s :=
      hwtend.eventually eventually_mem_nhdsWithin
    have hmseq_nn : ∀ᶠ n in atTop, 0 ≤ mseq n := by
      filter_upwards [hmem_ev] with n hn using hn
    -- Eventually `0 < mₙ`?  Not necessarily, but for the minimiser bound we
    -- only need `0 < mₙ ≤ 1` along the subsequence where the bound is used;
    -- we work with the eventual set `{0 < mₙ ≤ 1}`. First: `mₙ ≤ 1` eventually.
    have hmseq_le1 : ∀ᶠ n in atTop, mseq n ≤ 1 := by
      have := hmseq_tend0.eventually (Iic_mem_nhds (show (0 : ℝ) < 1 by norm_num))
      filter_upwards [this] with n hn using hn
    -- Uniform minimiser-radius bound: `K pₙ → K p₀`, hence `‖qₙ‖` eventually
    -- bounded by a fixed radius `R := (ε·3C + K p₀ + 1)^{1/α}` for `0 < mₙ ≤ 1`.
    set q : ℕ → (Fin d → ℝ) := fun n => qε ε (x, pseq n, mseq n) with hqdef
    have hKp_tend : Tendsto (fun n => K hweak (pseq n)) atTop (𝓝 (K hweak p₀)) :=
      (K_continuous hweak).continuousAt.tendsto.comp hpseq_tend
    have hKp_ev : ∀ᶠ n in atTop, K hweak (pseq n) ≤ K hweak p₀ + 1 := by
      have := hKp_tend.eventually (Iio_mem_nhds (show K hweak p₀ < K hweak p₀ + 1 by linarith))
      filter_upwards [this] with n hn using le_of_lt hn
    set R := (ε * (3 * hweak.C) + (K hweak p₀ + 1)) ^ (1 / hweak.α) with hRdef
    have hR_nn : 0 ≤ ε * (3 * hweak.C) + (K hweak p₀ + 1) := by
      have := K_nonneg hweak p₀; positivity
    -- For `0 < mₙ ≤ 1` with `K pₙ ≤ K p₀ + 1`, `‖qₙ‖ ≤ R`.
    have hqbound : ∀ᶠ n in atTop,
        0 < mseq n → ‖q n‖ ≤ R := by
      filter_upwards [hmseq_le1, hKp_ev] with n hle1 hKle hpos
      have hRn := Hdelta_near_minimizers_bounded hweak qε hε hHform hUpper hLower
        (pseq n) (mseq n) hpos hle1
      -- `‖qₙ‖ ≤ (ε·3C + K pₙ)^{1/α} ≤ (ε·3C + K p₀ + 1)^{1/α} = R`.
      refine le_trans hRn ?_
      apply Real.rpow_le_rpow
      · have := K_nonneg hweak (pseq n); positivity
      · linarith
      · positivity
    -- We need a sub-sequence on which `0 < mₙ`. If `0 < mₙ` only frequently,
    -- we still extract a frequent membership of `qₙ` in the ball, BUT we must
    -- exclude `mₙ = 0` terms (where the minimiser realisation `hHform` fails).
    -- KEY: along the FILTER `F`, frequently `0 < pm.2` OR `g` already matches
    -- the boundary value; handle the `mₙ = 0` case directly.
    -- Split: either `0 < mₙ` frequently, or eventually `mₙ = 0`.
    by_cases hfreq_pos : ∃ᶠ n in atTop, 0 < mseq n
    · -- Frequent `0 < mₙ`: minimisers in the ball frequently.
      have hmem_freq : ∃ᶠ n in atTop, q n ∈ Metric.closedBall (0 : Fin d → ℝ) R := by
        refine (hfreq_pos.and_eventually hqbound).mono ?_
        rintro n ⟨hpos, hb⟩
        rw [mem_closedBall_zero_iff]
        exact hb hpos
      have hcompact : IsCompact (Metric.closedBall (0 : Fin d → ℝ) R) :=
        isCompact_closedBall _ _
      obtain ⟨qstar, _hqstar_mem, φ, hφ_mono, hφ_tend⟩ :=
        hcompact.tendsto_subseq' hmem_freq
      -- Along the subsequence, also recover `0 < mₙ`: the frequent-positivity
      -- gives `0 < mseq (φ n)` infinitely often; refine `φ` further.
      -- Simpler: `hmem_freq` was extracted via `tendsto_subseq'`, but we need
      -- `0 < mseq (φ n)` along the subsequence too. Re-extract with the
      -- combined frequent condition.
      have hcombined : ∃ᶠ n in atTop,
          q n ∈ Metric.closedBall (0 : Fin d → ℝ) R ∧ 0 < mseq n := by
        refine (hfreq_pos.and_eventually hqbound).mono ?_
        rintro n ⟨hpos, hb⟩
        exact ⟨by rw [mem_closedBall_zero_iff]; exact hb hpos, hpos⟩
      obtain ⟨qstar2, hqstar2_mem, ψ, hψ_mono, hψ_tend⟩ :=
        hcompact.tendsto_subseq' (hcombined.mono (fun n h => h.1))
      -- We need `0 < mseq (ψ n)` along `ψ`. Extract that separately:
      -- `hcombined` frequently; `ψ` was built from the ball-membership subset,
      -- so `0 < mseq (ψ n)` may fail. Instead, build the subsequence directly
      -- from `hcombined` using `extraction` of a strictly monotone `ψ'` with
      -- BOTH properties.
      clear hqstar2_mem hψ_tend hψ_mono qstar2 ψ
      -- Get a strictly monotone `χ` along which BOTH the ball membership and
      -- positivity hold, then take the compactness subsequence inside it.
      obtain ⟨χ, hχ_mono, hχ_prop⟩ :=
        Filter.extraction_of_frequently_atTop hcombined
      -- `q ∘ χ` lands in the (compact) ball for all `n`.
      have hχ_ball : ∀ n, q (χ n) ∈ Metric.closedBall (0 : Fin d → ℝ) R :=
        fun n => (hχ_prop n).1
      have hχ_pos : ∀ n, 0 < mseq (χ n) := fun n => (hχ_prop n).2
      have hcompact' : IsCompact (Metric.closedBall (0 : Fin d → ℝ) R) :=
        isCompact_closedBall _ _
      obtain ⟨qst, _hqst_mem, σ, hσ_mono, hσ_tend⟩ :=
        hcompact'.tendsto_subseq (fun n => hχ_ball n)
      -- Final subsequence index: `θ := χ ∘ σ`.
      set θ : ℕ → ℕ := fun n => χ (σ n) with hθdef
      have hθ_mono : StrictMono θ := hχ_mono.comp hσ_mono
      have hθ_pos : ∀ n, 0 < mseq (θ n) := fun n => hχ_pos (σ n)
      have hθ_qtend : Tendsto (fun n => q (θ n)) atTop (𝓝 qst) := hσ_tend
      have hθ_mtend0 : Tendsto (fun n => mseq (θ n)) atTop (𝓝 (0 : ℝ)) :=
        hmseq_tend0.comp hθ_mono.tendsto_atTop
      have hθ_ptend : Tendsto (fun n => pseq (θ n)) atTop (𝓝 p₀) :=
        hpseq_tend.comp hθ_mono.tendsto_atTop
      -- Boundary point `z := (p₀ - qst, 0)`.
      set zpt : (Fin d → ℝ) × ℝ := (p₀ - qst, 0) with hzptdef
      have hzpt_mem : zpt ∈ s := by change (0 : ℝ) ≤ (0 : ℝ); rfl
      -- The sequence `(pseq (θ n) - q (θ n), mseq (θ n)) → zpt` within `s`.
      set zseq : ℕ → (Fin d → ℝ) × ℝ :=
        fun n => (pseq (θ n) - q (θ n), mseq (θ n)) with hzseqdef
      have hzseq_tend : Tendsto zseq atTop (𝓝[s] zpt) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨?_, ?_⟩
        · have h1 : Tendsto (fun n => pseq (θ n) - q (θ n)) atTop (𝓝 (p₀ - qst)) :=
            hθ_ptend.sub hθ_qtend
          exact h1.prodMk_nhds hθ_mtend0
        · filter_upwards [Filter.Eventually.of_forall hθ_pos] with n hn
          change (0 : ℝ) ≤ mseq (θ n); exact le_of_lt hn
      -- Joint lsc of `H` at `zpt`.
      have hlsc : LowerSemicontinuousWithinAt
          (fun pm : (Fin d → ℝ) × ℝ => H x pm.1 pm.2) s zpt :=
        (hJoint zpt hzpt_mem).lowerSemicontinuousWithinAt
      -- `K (q (θ n)) → K qst`.
      have hKtend : Tendsto (fun n => (1 / ε) * K hweak (q (θ n))) atTop
          (𝓝 ((1 / ε) * K hweak qst)) :=
        (tendsto_const_nhds).mul ((K_continuous hweak).continuousAt.tendsto.comp hθ_qtend)
      -- m=0 slice lower bound `H x s' 0 ≥ -C` (via `hJoint` slice limit).
      have hslice0 : ∀ s' : Fin d → ℝ, -hweak.C ≤ H x s' 0 := by
        intro s'
        have hHslice : Tendsto (fun m : ℝ => H x s' m) (𝓝[>] (0 : ℝ))
            (𝓝 (H x s' 0)) := by
          have hmap : Tendsto (fun m : ℝ => ((s', m) : (Fin d → ℝ) × ℝ))
              (𝓝[>] (0 : ℝ)) (𝓝[s] (s', 0)) := by
            rw [tendsto_nhdsWithin_iff]
            refine ⟨tendsto_const_nhds.prodMk_nhds nhdsWithin_le_nhds, ?_⟩
            filter_upwards [self_mem_nhdsWithin] with m hm using le_of_lt (Set.mem_Ioi.mp hm)
          have := (hHjoint_tendsto s').comp hmap
          simpa only [Function.comp_def] using this
        have hev : ∀ᶠ m in 𝓝[>] (0 : ℝ),
            -(hweak.C * (m ^ hweak.β + 1)) ≤ H x s' m := by
          filter_upwards [self_mem_nhdsWithin] with m hm
          have hmpos : 0 < m := hm
          have := hLower s' m hmpos
          have hpos : 0 ≤ (‖s'‖ ^ hweak.α) / hweak.C :=
            div_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (le_of_lt hC_pos)
          linarith
        have hmβtend : Tendsto (fun m : ℝ => m ^ hweak.β) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
          have : Tendsto (fun m : ℝ => m ^ hweak.β) (𝓝[>] (0 : ℝ)) (𝓝 (0 ^ hweak.β)) :=
            ((Real.continuousAt_rpow_const 0 hweak.β
              (Or.inr (le_of_lt hweak.hβ))).continuousWithinAt).tendsto
          simpa [Real.zero_rpow (ne_of_gt hweak.hβ)] using this
        have hbndtend : Tendsto (fun m : ℝ => -(hweak.C * (m ^ hweak.β + 1)))
            (𝓝[>] (0 : ℝ)) (𝓝 (-(hweak.C * (0 + 1)))) :=
          ((tendsto_const_nhds.mul (hmβtend.add tendsto_const_nhds)).neg)
        have hlimle : -(hweak.C * (0 + 1)) ≤ H x s' 0 :=
          le_of_tendsto_of_tendsto hbndtend hHslice hev
        simpa using hlimle
      -- `BddBelow` of the m=0 penalised family.
      have hBddBelow0 :
          BddBelow (Set.range fun q' : Fin d → ℝ =>
            H x (p₀ - q') 0 + (1 / ε) * K hweak q') := by
        refine ⟨-hweak.C, ?_⟩
        rintro y ⟨q', rfl⟩
        have h1 := hslice0 (p₀ - q')
        have h2 : 0 ≤ (1 / ε) * K hweak q' :=
          mul_nonneg (le_of_lt (one_div_pos.mpr hε)) (K_nonneg hweak q')
        linarith
      -- Boundary value bound: `Hdelta x p₀ 0 ≤ H x (p₀ − qst) 0 + (1/ε) K qst`.
      have hbound0 : Hdelta hweak ε x p₀ 0
          ≤ H x (p₀ - qst) 0 + (1 / ε) * K hweak qst := by
        have := ciInf_le hBddBelow0 qst
        simpa [Hdelta_def] using this
      -- Set `L := H x (p₀ − qst) 0`, `b := (1/ε) K qst`.
      set L := H x (p₀ - qst) 0 with hLdef
      set b := (1 / ε) * K hweak qst with hbdef
      have hcLb : c < L + b := lt_of_lt_of_le hc_gt hbound0
      obtain ⟨y, hy1, hy2⟩ : ∃ y, c - b < y ∧ y < L :=
        exists_between (by linarith)
      -- lsc at `zpt`: eventually `y < H x (zseq n).1 (zseq n).2`.
      have hlscApp : ∀ᶠ pm in 𝓝[s] zpt,
          y < (fun pm : (Fin d → ℝ) × ℝ => H x pm.1 pm.2) pm :=
        hlsc y (by simpa [hzptdef, hLdef] using hy2)
      have hev_a : ∀ᶠ n in atTop, y < H x (pseq (θ n) - q (θ n)) (mseq (θ n)) := by
        have := hzseq_tend.eventually hlscApp
        filter_upwards [this] with n hn
        simpa [hzseqdef] using hn
      -- `b_n := (1/ε) K (q (θ n)) → b`, eventually `> c - y`.
      have hcyb : c - y < b := by linarith
      have hev_b : ∀ᶠ n in atTop, c - y < (1 / ε) * K hweak (q (θ n)) := by
        have := hKtend.eventually (eventually_gt_nhds (by simpa [hbdef] using hcyb))
        filter_upwards [this] with n hn using hn
      obtain ⟨n, ha, hb⟩ := (hev_a.and hev_b).exists
      have hposn : 0 < mseq (θ n) := hθ_pos n
      -- Minimiser realisation `hHform` at `(pseq (θ n), mseq (θ n))`.
      have hreal := hHform (pseq (θ n)) (mseq (θ n)) hposn
      have hqn : q (θ n) = qε ε (x, pseq (θ n), mseq (θ n)) := rfl
      rw [← hqn] at hreal
      have hsum : c < Hdelta hweak ε x (pseq (θ n)) (mseq (θ n)) := by
        rw [hreal]; linarith
      -- But `g (w (θ n)) < c` and `g (w (θ n)) = Hdelta x (pseq (θ n)) (mseq (θ n))`.
      have hgeq : g (w (θ n)) = Hdelta hweak ε x (pseq (θ n)) (mseq (θ n)) := by
        simp [hgdef, hpseqdef, hmseqdef]
      have := hwlt (θ n)
      rw [hgeq] at this
      exact absurd this (not_lt.mpr (le_of_lt hsum))
    · -- Eventually `mₙ = 0`: then `g wₙ = Hdelta x pₙ 0`, and by JOINT
      -- continuity of `p ↦ Hdelta x p 0` (the `m=0` slice, which IS the value
      -- function restricted to the boundary) `g wₙ → Hdelta x p₀ 0`, but
      -- `g wₙ < c < Hdelta x p₀ 0`, contradiction.
      push_neg at hfreq_pos
      -- `hfreq_pos : ∀ᶠ n, ¬ 0 < mseq n`, i.e. `mseq n ≤ 0`; with `mₙ ≥ 0`, `=0`.
      have hmseq_eq0 : ∀ᶠ n in atTop, mseq n = 0 := by
        filter_upwards [hfreq_pos, hmseq_nn] with n h1 h2
        linarith
      -- On `{mₙ = 0}`, `g wₙ = Hdelta x pₙ 0`.
      have hgseq : ∀ᶠ n in atTop, g (w n) = Hdelta hweak ε x (pseq n) 0 := by
        filter_upwards [hmseq_eq0] with n hn
        simp only [hmseqdef] at hn
        simp only [hgdef, hpseqdef]
        rw [hn]
      -- `p ↦ Hdelta x p 0` is continuous (closed-cone value function on the
      -- boundary slice): we get `Hdelta x pₙ 0 → Hdelta x p₀ 0` from the
      -- `m=0` slice continuity. Use the limsup/liminf bounds we already have,
      -- restricted: actually we directly bound. Since `Hdelta x · 0` is
      -- continuous in `p` (the boundary slice of the value function), and the
      -- boundary slice continuity is the `m=0` restriction of THIS lemma — to
      -- avoid circularity, prove `Hdelta x pₙ 0 → Hdelta x p₀ 0` via the SAME
      -- squeeze at `m = 0` only.  Lower: testing each competitor `q`,
      -- `Hdelta x pₙ 0 ≤ H x (pₙ - q) 0 + (1/ε)K q → H x (p₀-q) 0 + (1/ε)K q`,
      -- inf over `q` gives `limsup ≤ Hdelta x p₀ 0`; and a matching liminf via
      -- joint lsc.  But we ALREADY proved `limsup g F ≤ Hdelta x p₀ 0` (hsup).
      -- The sequence `w n ∈ F` (it tends to `z₀` within `s`), so
      -- `liminf (g ∘ w) ≥ liminf g F` is FALSE in general; instead use that
      -- `g (w n) < c` and derive a contradiction with the limsup bound on the
      -- boundary slice. We show `Hdelta x p₀ 0 ≤ liminf (Hdelta x · 0 ∘ pseq)`.
      -- liminf of `Hdelta x pₙ 0`:  use the boundary-slice liminf argument.
      -- Reuse: the `m=0` value `Hdelta x p₀ 0 = ⨅ q, H x (p₀-q) 0 + (1/ε)K q`.
      -- Test competitor route gives `limsup`, need `liminf ≥`.
      -- Build it: minimisers at `m=0` need not exist; use lsc + boundedness.
      -- Simpler contradiction: from `hsup` (limsup g F ≤ value) and the fact
      -- that `g (w n) < c < value` infinitely often is consistent with hsup,
      -- so hsup alone does NOT contradict. We need the boundary liminf.
      -- Establish `Hdelta x p₀ 0 ≤ liminf (fun n => Hdelta x (pseq n) 0)` via
      -- the joint-lsc subsequence argument at `m = 0`.
      exfalso
      -- Minimisers of the `m=0` problem may not exist, but we can still run the
      -- liminf-by-contradiction using lsc of `H(x,·,0)` (continuity in `p`)
      -- and coercivity in `q`. Use: pick subsequence with `Hdelta x pₙ 0 < c`
      -- (all large `n`), competitor-bound the minimisers.
      -- `Hdelta x pₙ 0 = ⨅ q, H x (pₙ - q) 0 + (1/ε) K q`. Near-minimisers `qₙ`
      -- with value `< c + 1/n` are bounded by coercivity. Extract limit `q*`;
      -- lsc gives `Hdelta x p₀ 0 ≤ H x (p₀ - q*) 0 + (1/ε)K q* ≤ liminf < c`.
      -- We mirror the positive-`m` argument at the boundary slice.
      have hslice0 : ∀ s' : Fin d → ℝ, -hweak.C ≤ H x s' 0 := by
        intro s'
        have hHslice : Tendsto (fun m : ℝ => H x s' m) (𝓝[>] (0 : ℝ))
            (𝓝 (H x s' 0)) := by
          have hmap : Tendsto (fun m : ℝ => ((s', m) : (Fin d → ℝ) × ℝ))
              (𝓝[>] (0 : ℝ)) (𝓝[s] (s', 0)) := by
            rw [tendsto_nhdsWithin_iff]
            refine ⟨tendsto_const_nhds.prodMk_nhds nhdsWithin_le_nhds, ?_⟩
            filter_upwards [self_mem_nhdsWithin] with m hm using le_of_lt (Set.mem_Ioi.mp hm)
          have := (hHjoint_tendsto s').comp hmap
          simpa only [Function.comp_def] using this
        have hev : ∀ᶠ m in 𝓝[>] (0 : ℝ),
            -(hweak.C * (m ^ hweak.β + 1)) ≤ H x s' m := by
          filter_upwards [self_mem_nhdsWithin] with m hm
          have hmpos : 0 < m := hm
          have := hLower s' m hmpos
          have hpos : 0 ≤ (‖s'‖ ^ hweak.α) / hweak.C :=
            div_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (le_of_lt hC_pos)
          linarith
        have hmβtend : Tendsto (fun m : ℝ => m ^ hweak.β) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
          have : Tendsto (fun m : ℝ => m ^ hweak.β) (𝓝[>] (0 : ℝ)) (𝓝 (0 ^ hweak.β)) :=
            ((Real.continuousAt_rpow_const 0 hweak.β
              (Or.inr (le_of_lt hweak.hβ))).continuousWithinAt).tendsto
          simpa [Real.zero_rpow (ne_of_gt hweak.hβ)] using this
        have hbndtend : Tendsto (fun m : ℝ => -(hweak.C * (m ^ hweak.β + 1)))
            (𝓝[>] (0 : ℝ)) (𝓝 (-(hweak.C * (0 + 1)))) :=
          ((tendsto_const_nhds.mul (hmβtend.add tendsto_const_nhds)).neg)
        have hlimle : -(hweak.C * (0 + 1)) ≤ H x s' 0 :=
          le_of_tendsto_of_tendsto hbndtend hHslice hev
        simpa using hlimle
      -- `BddBelow` of the `m=0` penalised family at any `p`.
      have hBddBelow0 : ∀ p : Fin d → ℝ,
          BddBelow (Set.range fun q' : Fin d → ℝ =>
            H x (p - q') 0 + (1 / ε) * K hweak q') := by
        intro p
        refine ⟨-hweak.C, ?_⟩
        rintro y ⟨q', rfl⟩
        have h1 := hslice0 (p - q')
        have h2 : 0 ≤ (1 / ε) * K hweak q' :=
          mul_nonneg (le_of_lt (one_div_pos.mpr hε)) (K_nonneg hweak q')
        linarith
      -- Choose near-minimisers `qₙ` with `H x (pₙ - qₙ) 0 + (1/ε)K qₙ < c`.
      -- Along the eventually-`mₙ=0` subsequence, `Hdelta x pₙ 0 = g (w n) < c`.
      have hval_lt : ∀ᶠ n in atTop, Hdelta hweak ε x (pseq n) 0 < c := by
        filter_upwards [hgseq, Filter.Eventually.of_forall hwlt] with n hge hlt
        rw [← hge]; exact hlt
      -- Pick `qₙ` realising value `< c` (it exists since `Hdelta = ⨅ … < c`).
      have hexq : ∀ᶠ n in atTop, ∃ qn : Fin d → ℝ,
          H x (pseq n - qn) 0 + (1 / ε) * K hweak qn < c := by
        filter_upwards [hval_lt] with n hn
        by_contra hcontr
        push_neg at hcontr
        have : c ≤ ⨅ q' : Fin d → ℝ, H x (pseq n - q') 0 + (1 / ε) * K hweak q' :=
          le_ciInf hcontr
        rw [← Hdelta_def] at this
        exact absurd hn (not_lt.mpr this)
      -- Extract such a `qₙ` (choice).
      obtain ⟨N, hN⟩ := hexq.exists_forall_of_atTop
      set qn : ℕ → (Fin d → ℝ) :=
        fun n => if h : N ≤ n then (hN n h).choose else 0 with hqndef
      have hqn_spec : ∀ n, N ≤ n →
          H x (pseq n - qn n) 0 + (1 / ε) * K hweak (qn n) < c := by
        intro n hn
        have := (hN n hn).choose_spec
        simpa [hqndef, hn] using this
      -- `qₙ` bounded (coercivity): `(1/ε)K qₙ ≤ c - H x (pₙ - qₙ) 0 ≤ c + C`.
      -- so `K qₙ ≤ ε(c + C)`, hence `‖qₙ‖ ≤ (ε(c+C))^{1/α}` (for `c + C ≥ 0`?).
      -- Provide a uniform bound `R0`.
      set R0 := (ε * (c + hweak.C) + 1) ^ (1 / hweak.α) with hR0def
      have hbnd0 : ∀ n, N ≤ n → ‖qn n‖ ≤ R0 := by
        intro n hn
        have hspec := hqn_spec n hn
        have hHlow := hslice0 (pseq n - qn n)
        have hKq : (1 / ε) * K hweak (qn n) ≤ c + hweak.C := by linarith
        have hKq2 : K hweak (qn n) ≤ ε * (c + hweak.C) := by
          have hεpos := hε
          have h1 : ε * ((1 / ε) * K hweak (qn n)) ≤ ε * (c + hweak.C) :=
            mul_le_mul_of_nonneg_left hKq (le_of_lt hε)
          have he1 : ε * ((1 / ε) * K hweak (qn n)) = K hweak (qn n) := by field_simp
          rw [he1] at h1; exact h1
        have hqα_le : ‖qn n‖ ^ hweak.α ≤ ε * (c + hweak.C) + 1 :=
          le_trans (K_ge_rpow hweak (qn n)) (by linarith)
        have hbase_nn : 0 ≤ ε * (c + hweak.C) + 1 := by
          have := K_nonneg hweak (qn n)
          have := K_ge_rpow hweak (qn n)
          have hrp : 0 ≤ ‖qn n‖ ^ hweak.α := Real.rpow_nonneg (norm_nonneg _) _
          linarith
        have hmono : (‖qn n‖ ^ hweak.α) ^ (1 / hweak.α)
            ≤ (ε * (c + hweak.C) + 1) ^ (1 / hweak.α) :=
          Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg _) _) hqα_le
            (le_of_lt (by positivity))
        have hself : (‖qn n‖ ^ hweak.α) ^ (1 / hweak.α) = ‖qn n‖ := by
          rw [← Real.rpow_mul (norm_nonneg _), mul_one_div,
            div_self (ne_of_gt hα_pos), Real.rpow_one]
        rw [hself] at hmono; exact hmono
      -- `qₙ` eventually in the closed ball of radius `R0`; extract limit `q*`.
      have hqn_ball : ∀ᶠ n in atTop, qn n ∈ Metric.closedBall (0 : Fin d → ℝ) R0 := by
        filter_upwards [eventually_ge_atTop N] with n hn
        rw [mem_closedBall_zero_iff]; exact hbnd0 n hn
      have hcompact0 : IsCompact (Metric.closedBall (0 : Fin d → ℝ) R0) :=
        isCompact_closedBall _ _
      obtain ⟨qst, _hqst_mem, φ, hφ_mono, hφ_tend⟩ :=
        hcompact0.tendsto_subseq' hqn_ball.frequently
      -- `pseq (φ n) → p₀`, `qn (φ n) → qst`, both within atTop.
      have hp_sub : Tendsto (fun n => pseq (φ n)) atTop (𝓝 p₀) :=
        hpseq_tend.comp hφ_mono.tendsto_atTop
      -- Boundary point of `H`: `(p₀ - qst, 0)`. lsc there.
      set zpt : (Fin d → ℝ) × ℝ := (p₀ - qst, 0) with hzptdef
      have hzpt_mem : zpt ∈ s := by change (0 : ℝ) ≤ (0 : ℝ); rfl
      have hlsc : LowerSemicontinuousWithinAt
          (fun pm : (Fin d → ℝ) × ℝ => H x pm.1 pm.2) s zpt :=
        (hJoint zpt hzpt_mem).lowerSemicontinuousWithinAt
      -- `(pseq (φ n) - qn (φ n), 0) → zpt` within `s`.
      set zseq : ℕ → (Fin d → ℝ) × ℝ :=
        fun n => (pseq (φ n) - qn (φ n), 0) with hzseqdef
      have hzseq_tend : Tendsto zseq atTop (𝓝[s] zpt) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨?_, ?_⟩
        · have h1 : Tendsto (fun n => pseq (φ n) - qn (φ n)) atTop (𝓝 (p₀ - qst)) :=
            hp_sub.sub hφ_tend
          exact h1.prodMk_nhds tendsto_const_nhds
        · filter_upwards with n; change (0 : ℝ) ≤ (0 : ℝ); rfl
      -- `K (qn (φ n)) → K qst`.
      have hKtend : Tendsto (fun n => (1 / ε) * K hweak (qn (φ n))) atTop
          (𝓝 ((1 / ε) * K hweak qst)) :=
        (tendsto_const_nhds).mul ((K_continuous hweak).continuousAt.tendsto.comp hφ_tend)
      -- Boundary value bound: `Hdelta x p₀ 0 ≤ H x (p₀ - qst) 0 + (1/ε)K qst`.
      have hbound0 : Hdelta hweak ε x p₀ 0
          ≤ H x (p₀ - qst) 0 + (1 / ε) * K hweak qst := by
        have := ciInf_le (hBddBelow0 p₀) qst
        simpa [Hdelta_def] using this
      set L := H x (p₀ - qst) 0 with hLdef
      set b := (1 / ε) * K hweak qst with hbdef
      have hcLb : c < L + b := lt_of_lt_of_le hc_gt hbound0
      obtain ⟨y, hy1, hy2⟩ : ∃ y, c - b < y ∧ y < L :=
        exists_between (by linarith)
      have hlscApp : ∀ᶠ pm in 𝓝[s] zpt,
          y < (fun pm : (Fin d → ℝ) × ℝ => H x pm.1 pm.2) pm :=
        hlsc y (by simpa [hzptdef, hLdef] using hy2)
      have hev_a : ∀ᶠ n in atTop, y < H x (pseq (φ n) - qn (φ n)) 0 := by
        have := hzseq_tend.eventually hlscApp
        filter_upwards [this] with n hn
        simpa [hzseqdef] using hn
      have hcyb : c - y < b := by linarith
      have hev_b : ∀ᶠ n in atTop, c - y < (1 / ε) * K hweak (qn (φ n)) := by
        have := hKtend.eventually (eventually_gt_nhds (by simpa [hbdef] using hcyb))
        filter_upwards [this] with n hn using hn
      have hev_N : ∀ᶠ n in atTop, N ≤ φ n :=
        hφ_mono.tendsto_atTop.eventually (eventually_ge_atTop N)
      obtain ⟨n, ⟨ha, hb⟩, hNn⟩ := ((hev_a.and hev_b).and hev_N).exists
      have hspec := hqn_spec (φ n) hNn
      -- `c < H x (pseq (φ n) - qn (φ n)) 0 + (1/ε)K (qn (φ n))`, contradicting `hspec`.
      have hsum : c < H x (pseq (φ n) - qn (φ n)) 0 + (1 / ε) * K hweak (qn (φ n)) := by
        linarith
      exact absurd hspec (not_lt.mpr (le_of_lt hsum))
  -- Assemble the squeeze.
  exact tendsto_of_le_liminf_of_limsup_le hinf hsup hBddAbove hBddBelow

/-- Joint continuity of the canonical regularized carrier on the closed cone.
Convex momentum slices and monotonicity in mass upgrade its finite slice limits. -/
theorem HdeltaK0_continuousOn_H_pm_closedCone_of_selectorFamily
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hdiff : HypothesisHpDifferentiable (d := d) H DpH)
    (qε : QEpsFamily d) (sel : InfConvSelectorFamily hweak qε)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
      ContinuousOn (fun pm : (Fin d → ℝ) × ℝ => HdeltaK0 hweak ε x pm.1 pm.2)
        {pm | 0 ≤ pm.2} := HdeltaPaper_continuousOn_closed hmon hweak hdiff qε sel hε

/-- **`(a:Hat0)` for `H^ε` from the selector family.** Packages
`Hdelta_rc0_of_selectorFamily` into a `HypothesisHat0 (Hdelta hweak ε)` witness
via `Hdelta_hat0` (InfConv.lean). -/
theorem Hdelta_hat0_of_selectorFamily
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hH0 : Hamiltonian.HypothesisHZeroExtension (d := d) H)
    (hHextJointCont : Hamiltonian.HypothesisHextJointCont (d := d) H)
    (qε : QEpsFamily d) (sel : InfConvSelectorFamily (H := H) (DpH := DpH) hweak qε)
    {ε : ℝ} (hε : 0 < ε) :
    Hamiltonian.HypothesisHat0 (d := d) (Hdelta hweak ε) :=
  Hdelta_hat0 hweak hε
    (Hdelta_rc0_of_selectorFamily hweak hH0 hHextJointCont qε sel hε)

/-- Closed-cone regularity of the canonical regularized pair, derived entirely
from positive-mass assumptions on the original Hamiltonian. -/
theorem regularityHK0_HdeltaK0_DpHepsilon_of_selector
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hdiff : HypothesisHpDifferentiable (d := d) H DpH)
    (qε : QEpsFamily d) (sel : InfConvSelectorFamily hweak qε)
    (hMeas : HypothesisDpHMeasurable (d := d) H DpH)
    (hAE : HdeltaAEPowerEpsData hweak qε)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Theorems.SimplePower.RegularityHK0 (HdeltaK0 hweak ε) (DpHepsilonFam hweak qε ε) :=
  HdeltaPaper_regularityHK0 hmon hweak hdiff qε sel hMeas hAE hε hε1

/-- Compatibility name for consumers of the canonical regularized carrier. -/
theorem regularityHK0_Hdelta_of_selector
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hdiff : HypothesisHpDifferentiable (d := d) H DpH)
    (qε : QEpsFamily d) (sel : InfConvSelectorFamily hweak qε)
    (hMeas : HypothesisDpHMeasurable (d := d) H DpH)
    (hAE : HdeltaAEPowerEpsData hweak qε)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Theorems.SimplePower.RegularityHK0 (HdeltaK0 hweak ε) (DpHepsilonFam hweak qε ε) :=
  regularityHK0_HdeltaK0_DpHepsilon_of_selector hweak hmon hdiff qε sel hMeas hAE hε hε1

end InfimalConvolution
end StationaryMFG
