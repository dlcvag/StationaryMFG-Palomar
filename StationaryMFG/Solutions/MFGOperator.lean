module

public import StationaryMFG.Periodic.Lp
public import StationaryMFG.Periodic.Sobolev
public import StationaryMFG.Periodic.Integral
public import StationaryMFG.Solutions.Weak
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

@[expose] public section

/-!
# MFG domain, convex cone, and duality pairing

This module sets up the **product space**

```
𝓚 := L^{betaBar}_per(𝕋^d; ℝ⁺_0) × W^{1,gammaBar}_per(𝕋^d)
```

used as the domain of the MFG operator `A` (and its regularization `A_ε`)
throughout Phases 4–6 of the project. Following `docs/CONVENTIONS.md` §1b,
elements of `𝓚` are bare-function pairs `(m, u) : ((Fin d → ℝ) → ℝ) ×
((Fin d → ℝ) → ℝ)`; the membership constraint
`MemLpPer betaBar m ∧ MemSobolevPer gammaBar u ∧ 0 ≤ᵐ m` is encoded as a `Set`
predicate so that we can phrase convexity in Mathlib's standard way.

The deliverables are:

* `MFGDomain betaBar gammaBar` — the cone
  `{(m, u) : MemLpPer betaBar m ∧ MemSobolevPer gammaBar u ∧ 0 ≤ m a.e.}`,
  parameterised by extended exponents `betaBar, gammaBar ∈ [1, ∞]`.
* `MFGDomain.convex` — `Convex ℝ (MFGDomain betaBar gammaBar)`.
* `mfgPairing` — the explicit integral duality bracket
  `(f₁, f₂; Df₂) ↔ (η, ν; Dν) ↦ ∫ f₁ η + ∫ f₂ ν + ∑_i ∫ (∂_i f₂)(∂_i ν)`.
* `mfgPairing_holder_bound` — the per-summand Hölder bound for `mfgPairing`.

The reflexive Banach-space structure on `𝓚` itself flows from Mathlib's
product-space instance applied to (the toLp / toSobolevLp bridges of)
`L^{betaBar}_per` and `W^{1,gammaBar}_per`; this file does not need to expose it.

## Paper reference

`Source/FGU-monotone_revised.tex`, §2.5 `subs:solutions`, lines 846–874
(domain set-up) and §`sec:proof-power-growth` lines 901–935 (the integral
pairing in `defAepsi`).
-/

noncomputable section

namespace StationaryMFG
namespace Solutions
namespace MFG

open MeasureTheory Set
open StationaryMFG.Periodic
open StationaryMFG.Hamiltonian
open scoped ENNReal NNReal

variable {d : ℕ}

/-! ## Bridge: `MemLpPer p` with `p ≥ 1` ⇒ integrable on the unit cube

The unit cube has finite measure, so by Hölder's monotonicity of `L^p`
exponents, `MemLpPer p f` for `p ≥ 1` implies `MemLpPer 1 f` and hence
integrability on the cube. -/

private lemma isFiniteMeasure_restrict_unitCube :
    IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
  ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩

/-- `MemLpPer p f` with `1 ≤ p` implies `MemLpPer 1 f` (finite-measure
inclusion `L^p ↪ L^1`). -/
lemma memLpPer_one_of_mono {p : ℝ≥0∞} {f : (Fin d → ℝ) → ℝ}
    (hp : 1 ≤ p) (hf : MemLpPer p f) : MemLpPer 1 f := by
  haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    isFiniteMeasure_restrict_unitCube
  -- `MemLpPer p f` unfolds to `MemLp f p (volume.restrict (UnitCube d))`,
  -- so we can apply `MemLp.mono_exponent` directly.
  exact MemLp.toMemLpPer (hf.toMemLp.mono_exponent hp)

/-- `MemLpPer p f` with `1 ≤ p` implies `IntegrableOn f (UnitCube d)`. -/
lemma integrableOn_of_memLpPer {p : ℝ≥0∞} {f : (Fin d → ℝ) → ℝ}
    (hp : 1 ≤ p) (hf : MemLpPer p f) : IntegrableOn f (UnitCube d) :=
  (memLp_one_iff_integrable).1 (memLpPer_one_of_mono hp hf)

/-! ## Helpers: products with smooth periodic test functions are integrable. -/

private lemma _root_.StationaryMFG.Periodic.SmoothPeriodic.bounded_on_unitCube
    (φ : SmoothPeriodic d) :
    ∃ C : ℝ, ∀ x ∈ UnitCube d, ‖(φ : (Fin d → ℝ) → ℝ) x‖ ≤ C := by
  have hcompact : IsCompact (Set.pi Set.univ
      (fun _ : Fin d => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  obtain ⟨C, hC⟩ := hcompact.bddAbove_image
    φ.smooth.continuous.norm.continuousOn
  refine ⟨C, fun x hx => ?_⟩
  apply hC
  refine ⟨x, ?_, rfl⟩
  intro j _
  exact Set.Ico_subset_Icc_self (hx j (Set.mem_univ _))

private lemma integrableOn_mul_smoothPeriodic
    {f : (Fin d → ℝ) → ℝ} (hf : MemLpPer 1 f) (φ : SmoothPeriodic d) :
    IntegrableOn (fun x => f x * (φ : (Fin d → ℝ) → ℝ) x) (UnitCube d) := by
  obtain ⟨C, hC⟩ := φ.bounded_on_unitCube
  have hf_int : Integrable f (Measure.restrict volume (UnitCube d)) :=
    (memLp_one_iff_integrable).1 hf
  have hcont : AEStronglyMeasurable
      (fun x => f x * (φ : (Fin d → ℝ) → ℝ) x)
      (Measure.restrict volume (UnitCube d)) :=
    hf.aestronglyMeasurable.mul φ.smooth.continuous.aestronglyMeasurable
  have hbound : ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
      ‖f x * (φ : (Fin d → ℝ) → ℝ) x‖ ≤ ‖C * ‖f x‖‖ := by
    refine (ae_restrict_iff' measurableSet_unitCube).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro x hx
    rw [norm_mul]
    have hbnd : ‖(φ : (Fin d → ℝ) → ℝ) x‖ ≤ C := hC x hx
    have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hC _ hx)
    have hgoal : ‖f x‖ * ‖(φ : (Fin d → ℝ) → ℝ) x‖ ≤ C * ‖f x‖ := by
      have := mul_le_mul_of_nonneg_left hbnd (norm_nonneg (f x))
      linarith [this]
    have hrhs : ‖C * ‖f x‖‖ = C * ‖f x‖ := by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hCnn, abs_of_nonneg (norm_nonneg _)]
    linarith [hrhs, hgoal]
  exact MeasureTheory.Integrable.mono (hf_int.norm.const_mul C) hcont hbound

/-! ## Closure of `HasWeakDerivPer` under linear combinations

These lemmas need the underlying functions `f` to themselves be `L¹` on
the cube (otherwise the integration by parts on `f₁ + f₂` against a smooth
periodic test cannot be split coordinate-wise). The `MemSobolevPer p f`
predicate carries `MemLpPer p f`, so for `p ≥ 1` this is automatic.
-/

/-- Constant scaling of a weak derivative. -/
lemma hasWeakDerivPer_const_smul (i : Fin d) (c : ℝ)
    {f g : (Fin d → ℝ) → ℝ}
    (h : HasWeakDerivPer i f g) :
    HasWeakDerivPer i (c • f) (c • g) := by
  refine ⟨h.memLpPer.const_smul c, ?_⟩
  intro φ
  -- Pull `c` outside both integrals.
  have hsmul₁ :
      periodicIntegral (fun x => (c • g) x * (φ : (Fin d → ℝ) → ℝ) x) =
        c * periodicIntegral (fun x => g x * (φ : (Fin d → ℝ) → ℝ) x) := by
    have heq : (fun x => (c • g) x * (φ : (Fin d → ℝ) → ℝ) x) =
        (fun x => c • (g x * (φ : (Fin d → ℝ) → ℝ) x)) := by
      funext x
      simp [Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [heq]
    rw [periodicIntegral_smul (𝕜 := ℝ) c
      (fun x => g x * (φ : (Fin d → ℝ) → ℝ) x)]
    simp [smul_eq_mul]
  have hsmul₂ :
      periodicIntegral (fun x => (c • f) x *
          ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) x) =
        c * periodicIntegral (fun x => f x *
          ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) x) := by
    have heq : (fun x => (c • f) x *
        ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
          (Fin d → ℝ) → ℝ) x) =
          (fun x => c • (f x *
            ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) x)) := by
      funext x
      simp [Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [heq]
    rw [periodicIntegral_smul (𝕜 := ℝ) c
      (fun x => f x *
        ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
          (Fin d → ℝ) → ℝ) x)]
    simp [smul_eq_mul]
  rw [hsmul₁, hsmul₂, h.integral_eq φ]
  ring

/-- Sum of weak derivatives, for source functions in `L¹_per`. -/
lemma hasWeakDerivPer_add (i : Fin d)
    {f₁ g₁ f₂ g₂ : (Fin d → ℝ) → ℝ}
    (hf₁ : MemLpPer 1 f₁) (hf₂ : MemLpPer 1 f₂)
    (h₁ : HasWeakDerivPer i f₁ g₁) (h₂ : HasWeakDerivPer i f₂ g₂) :
    HasWeakDerivPer i (f₁ + f₂) (g₁ + g₂) := by
  refine ⟨h₁.memLpPer.add h₂.memLpPer, ?_⟩
  intro φ
  set ψ : (Fin d → ℝ) → ℝ :=
    ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
      (Fin d → ℝ) → ℝ) with hψ_def
  -- Integrabilities for the LHS pair.
  have hLHS₁ : IntegrableOn
      (fun x => g₁ x * (φ : (Fin d → ℝ) → ℝ) x) (UnitCube d) :=
    integrableOn_mul_smoothPeriodic h₁.memLpPer φ
  have hLHS₂ : IntegrableOn
      (fun x => g₂ x * (φ : (Fin d → ℝ) → ℝ) x) (UnitCube d) :=
    integrableOn_mul_smoothPeriodic h₂.memLpPer φ
  -- Integrabilities for the RHS pair.
  have hRHS₁ : IntegrableOn (fun x => f₁ x * ψ x) (UnitCube d) :=
    integrableOn_mul_smoothPeriodic hf₁ (SmoothPeriodic.partialDeriv i φ)
  have hRHS₂ : IntegrableOn (fun x => f₂ x * ψ x) (UnitCube d) :=
    integrableOn_mul_smoothPeriodic hf₂ (SmoothPeriodic.partialDeriv i φ)
  have hLHS_split :
      periodicIntegral
        (fun x => (g₁ + g₂) x * (φ : (Fin d → ℝ) → ℝ) x) =
        periodicIntegral (fun x => g₁ x * (φ : (Fin d → ℝ) → ℝ) x) +
          periodicIntegral (fun x => g₂ x * (φ : (Fin d → ℝ) → ℝ) x) := by
    have hsum :
        (fun x => (g₁ + g₂) x * (φ : (Fin d → ℝ) → ℝ) x) =
          (fun x => g₁ x * (φ : (Fin d → ℝ) → ℝ) x) +
            (fun x => g₂ x * (φ : (Fin d → ℝ) → ℝ) x) := by
      funext x; simp [Pi.add_apply]; ring
    rw [hsum, periodicIntegral_add hLHS₁ hLHS₂]
  have hRHS_split :
      periodicIntegral (fun x => (f₁ + f₂) x * ψ x) =
        periodicIntegral (fun x => f₁ x * ψ x) +
          periodicIntegral (fun x => f₂ x * ψ x) := by
    have hsum :
        (fun x => (f₁ + f₂) x * ψ x) =
          (fun x => f₁ x * ψ x) + (fun x => f₂ x * ψ x) := by
      funext x; simp [Pi.add_apply]; ring
    rw [hsum, periodicIntegral_add hRHS₁ hRHS₂]
  rw [hLHS_split, h₁.integral_eq φ, h₂.integral_eq φ, hRHS_split]
  ring

/-! ## Closure of `MemSobolevPer` under linear combinations

For `1 ≤ p`, `MemSobolevPer p` is closed under `+` and `c • ·`. The
witness families are produced by `hasWeakDerivPer_add` / `hasWeakDerivPer_const_smul`. -/

/-- Sum of `MemSobolevPer`-functions, for `1 ≤ p`. -/
lemma memSobolevPer_add {p : ℝ≥0∞} (hp : 1 ≤ p)
    {f₁ f₂ : (Fin d → ℝ) → ℝ}
    (h₁ : MemSobolevPer p f₁) (h₂ : MemSobolevPer p f₂) :
    MemSobolevPer p (f₁ + f₂) := by
  refine ⟨h₁.1.add h₂.1, ?_⟩
  obtain ⟨g₁, hg₁⟩ := h₁.2
  obtain ⟨g₂, hg₂⟩ := h₂.2
  refine ⟨fun i => g₁ i + g₂ i, ?_⟩
  intro i
  exact hasWeakDerivPer_add (d := d) i (memLpPer_one_of_mono hp h₁.1)
    (memLpPer_one_of_mono hp h₂.1) (hg₁ i) (hg₂ i)

/-- Constant scaling of a `MemSobolevPer`-function. (No need for `1 ≤ p`
since the IBP identity scales linearly without integrability.) -/
lemma memSobolevPer_const_smul {p : ℝ≥0∞} (c : ℝ)
    {f : (Fin d → ℝ) → ℝ} (h : MemSobolevPer p f) :
    MemSobolevPer p (c • f) := by
  refine ⟨h.1.const_smul c, ?_⟩
  obtain ⟨g, hg⟩ := h.2
  refine ⟨fun i => c • g i, ?_⟩
  intro i
  exact hasWeakDerivPer_const_smul (d := d) i c (hg i)

/-! ## The MFG domain `𝓚` -/

/-- The MFG domain
`𝓚 = L^{betaBar}_per(𝕋^d; ℝ⁺_0) × W^{1,gammaBar}_per(𝕋^d)` realised as a `Set` of
bare-function pairs `(m, u)` with `MemLpPer betaBar m`, `MemSobolevPer gammaBar u`,
and `m ≥ 0` almost everywhere on the unit cube. -/
def MFGDomain (betaBar gammaBar : ℝ≥0∞) :
    Set (((Fin d → ℝ) → ℝ) × ((Fin d → ℝ) → ℝ)) :=
  { p | MemLpPer betaBar p.1 ∧ MemSobolevPer gammaBar p.2 ∧
        0 ≤ᵐ[Measure.restrict volume (UnitCube d)] p.1 }

lemma mem_MFGDomain_iff {betaBar gammaBar : ℝ≥0∞}
    {p : ((Fin d → ℝ) → ℝ) × ((Fin d → ℝ) → ℝ)} :
    p ∈ MFGDomain (d := d) betaBar gammaBar ↔
      MemLpPer betaBar p.1 ∧ MemSobolevPer gammaBar p.2 ∧
        0 ≤ᵐ[Measure.restrict volume (UnitCube d)] p.1 := Iff.rfl

/-- **Convexity of the MFG domain.** For exponents `betaBar, gammaBar ∈ [1, ∞]`, the
cone `𝓚 = MFGDomain betaBar gammaBar` is convex in the bare-pair vector space. -/
theorem MFGDomain.convex {betaBar gammaBar : ℝ≥0∞} (_hβ : 1 ≤ betaBar) (hγ : 1 ≤ gammaBar) :
    Convex ℝ (MFGDomain (d := d) betaBar gammaBar) := by
  rw [convex_iff_add_mem]
  rintro ⟨m₁, u₁⟩ ⟨hm₁, hu₁, hpos₁⟩ ⟨m₂, u₂⟩ ⟨hm₂, hu₂, hpos₂⟩ a b ha hb _
  refine ⟨?_, ?_, ?_⟩
  · -- `MemLpPer betaBar (a • m₁ + b • m₂)` ≡ first component of `a • _ + b • _`.
    have hLp : MemLpPer betaBar (a • m₁ + b • m₂) :=
      (hm₁.const_smul a).add (hm₂.const_smul b)
    -- The product structure unfolds the pair components definitionally.
    exact hLp
  · -- `MemSobolevPer gammaBar (a • u₁ + b • u₂)`.
    have hSob : MemSobolevPer gammaBar (a • u₁ + b • u₂) :=
      memSobolevPer_add hγ
        (memSobolevPer_const_smul a hu₁)
        (memSobolevPer_const_smul b hu₂)
    exact hSob
  · -- `0 ≤ a • m₁ + b • m₂` a.e.
    have h_pos : 0 ≤ᵐ[Measure.restrict volume (UnitCube d)]
        (a • m₁ + b • m₂ : (Fin d → ℝ) → ℝ) := by
      filter_upwards [hpos₁, hpos₂] with x hx₁ hx₂
      have ha₁ : 0 ≤ a • m₁ x := by
        have : 0 ≤ a * m₁ x := mul_nonneg ha hx₁
        simpa [Pi.smul_apply, smul_eq_mul] using this
      have hb₂ : 0 ≤ b • m₂ x := by
        have : 0 ≤ b * m₂ x := mul_nonneg hb hx₂
        simpa [Pi.smul_apply, smul_eq_mul] using this
      have : 0 ≤ a • m₁ x + b • m₂ x := add_nonneg ha₁ hb₂
      simpa [Pi.add_apply, Pi.smul_apply] using this
    exact h_pos

/-! ## The MFG duality pairing

The pairing
`mfgPairing m u Du η ν Dν = ∫ m η + ∫ u ν + ∑_i ∫ (Du i) (Dν i)` is the
**explicit-integral** realisation of the duality bracket
`L^{betaBar}_per × W^{1,gammaBar}_per ↔ L^{betaBar'}_per × W^{1,gammaBar'}_per` used throughout
Phases 4–6 of the paper. The two ambient families
`Du, Dν : Fin d → (Fin d → ℝ) → ℝ` are the (explicit) weak-derivative
witnesses; the pairing does not require them to actually be weak
derivatives — it is well-defined as soon as the component-wise integrals
make sense.
-/

/-- The MFG duality pairing.

Inputs:

* `m, u` — primal bare functions (interpreted as elements of
  `L^{betaBar}_per × W^{1,gammaBar}_per`);
* `Du i` — explicit `i`-th partial derivative of `u`;
* `η, ν` — dual-side bare functions;
* `Dν i` — explicit `i`-th partial derivative of `ν`.

Output: the real number
`∫_{𝕋^d} m η + ∫_{𝕋^d} u ν + ∑_i ∫_{𝕋^d} (Du i) (Dν i)`. -/
def mfgPairing
    (m u : (Fin d → ℝ) → ℝ) (Du : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ) (Dν : Fin d → (Fin d → ℝ) → ℝ) : ℝ :=
  periodicIntegral (fun x => m x * η x) +
    periodicIntegral (fun x => u x * ν x) +
    ∑ i : Fin d, periodicIntegral (fun x => (Du i) x * (Dν i) x)

/-! ## Hölder bound for the pairing

Each summand of `mfgPairing` is bounded by the corresponding Hölder
product. We invoke `MeasureTheory.integral_mul_norm_le_Lp_mul_Lq` on the
cube-restricted measure, against a Hölder-conjugate exponent pair
`(p, q)` with `p, q ≥ 1` and `p.HolderConjugate q`.
-/

/-- Bridge: for `MemLpPer p f` with `p ≠ 0, ⊤`, the periodic seminorm
`lpNormPer p f` agrees with the explicit integral form
`(∫ ‖f‖^{p.toReal})^{1/p.toReal}`. -/
lemma lpNormPer_eq_integral_rpow {p : ℝ≥0∞} {f : (Fin d → ℝ) → ℝ}
    (hp₀ : p ≠ 0) (hp_top : p ≠ ⊤) (hf : MemLpPer p f) :
    lpNormPer p f =
      (∫ x, ‖f x‖ ^ p.toReal ∂(Measure.restrict volume (UnitCube d)))
          ^ p.toReal⁻¹ := by
  unfold lpNormPer eLpNormPer
  rw [MeasureTheory.toReal_eLpNorm]
  exact MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal hp₀ hp_top
    hf.aestronglyMeasurable

/-- **Per-summand Hölder bound** for the integral of a product of bare
periodic functions. With `p, q : ℝ` Hölder conjugate, `f ∈ L^p_per`,
`g ∈ L^q_per`,

```
|∫_{𝕋^d} f g| ≤ lpNormPer (ENNReal.ofReal p) f *
                lpNormPer (ENNReal.ofReal q) g.
```
-/
lemma abs_periodicIntegral_mul_le {p q : ℝ}
    (hpq : p.HolderConjugate q)
    {f g : (Fin d → ℝ) → ℝ}
    (hf : MemLpPer (ENNReal.ofReal p) f)
    (hg : MemLpPer (ENNReal.ofReal q) g) :
    |periodicIntegral (fun x => f x * g x)| ≤
      lpNormPer (ENNReal.ofReal p) f *
        lpNormPer (ENNReal.ofReal q) g := by
  set μ : Measure (Fin d → ℝ) := Measure.restrict volume (UnitCube d) with hμ_def
  haveI : IsFiniteMeasure μ := isFiniteMeasure_restrict_unitCube
  have hMemLp_f : MemLp f (ENNReal.ofReal p) μ := hf
  have hMemLp_g : MemLp g (ENNReal.ofReal q) μ := hg
  have hp_pos : 0 < p := hpq.pos
  have hq_pos : 0 < q := hpq.symm.pos
  have hp_ne_zero : (ENNReal.ofReal p) ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, not_le.mpr hp_pos]
  have hq_ne_zero : (ENNReal.ofReal q) ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, not_le.mpr hq_pos]
  have hp_ne_top : (ENNReal.ofReal p) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hq_ne_top : (ENNReal.ofReal q) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hp_toReal : (ENNReal.ofReal p).toReal = p :=
    ENNReal.toReal_ofReal hpq.nonneg
  have hq_toReal : (ENNReal.ofReal q).toReal = q :=
    ENNReal.toReal_ofReal hpq.symm.nonneg
  -- Hölder via Mathlib's integral form.
  have hbound :
      ∫ x, ‖f x‖ * ‖g x‖ ∂μ ≤
        (∫ x, ‖f x‖ ^ p ∂μ) ^ (1 / p) *
          (∫ x, ‖g x‖ ^ q ∂μ) ^ (1 / q) :=
    integral_mul_norm_le_Lp_mul_Lq hpq hMemLp_f hMemLp_g
  -- |∫ f g| ≤ ∫ |f g| = ∫ ‖f‖ ‖g‖.
  have habs :
      |periodicIntegral (fun x => f x * g x)| ≤ ∫ x, ‖f x‖ * ‖g x‖ ∂μ := by
    have hcong : (fun x => ‖f x * g x‖) = (fun x => ‖f x‖ * ‖g x‖) := by
      funext x; rw [norm_mul]
    have habs1 : |∫ x, f x * g x ∂μ| ≤ ∫ x, ‖f x * g x‖ ∂μ := by
      have := norm_integral_le_integral_norm
        (μ := μ) (f := fun x => f x * g x)
      simpa [Real.norm_eq_abs] using this
    rw [hcong] at habs1
    exact habs1
  -- Identify the rhs with `lpNormPer · lpNormPer`.
  have hLpf :
      lpNormPer (ENNReal.ofReal p) f = (∫ x, ‖f x‖ ^ p ∂μ) ^ (1 / p) := by
    rw [lpNormPer_eq_integral_rpow hp_ne_zero hp_ne_top hf, hp_toReal,
      one_div]
  have hLpg :
      lpNormPer (ENNReal.ofReal q) g = (∫ x, ‖g x‖ ^ q ∂μ) ^ (1 / q) := by
    rw [lpNormPer_eq_integral_rpow hq_ne_zero hq_ne_top hg, hq_toReal,
      one_div]
  calc
    |periodicIntegral (fun x => f x * g x)|
        ≤ ∫ x, ‖f x‖ * ‖g x‖ ∂μ := habs
    _ ≤ (∫ x, ‖f x‖ ^ p ∂μ) ^ (1 / p) *
          (∫ x, ‖g x‖ ^ q ∂μ) ^ (1 / q) := hbound
    _ = lpNormPer (ENNReal.ofReal p) f *
          lpNormPer (ENNReal.ofReal q) g := by rw [hLpf, hLpg]

/-- **Hölder bound for the MFG pairing.**

Given Hölder-conjugate exponent pairs `(betaBar, betaBar')` for the `L^p` part and
`(gammaBar, gammaBar')` for the Sobolev part, and assuming all six bare functions
satisfy the appropriate `MemLpPer` predicate, the pairing
`mfgPairing` is bounded by the natural (sum-of-products) Hölder
expression. -/
theorem mfgPairing_holder_bound
    {betaBar betaBar' gammaBar gammaBar' : ℝ}
    (hβ : betaBar.HolderConjugate betaBar')
    (hγ : gammaBar.HolderConjugate gammaBar')
    {m u : (Fin d → ℝ) → ℝ} {Du : Fin d → (Fin d → ℝ) → ℝ}
    {η ν : (Fin d → ℝ) → ℝ} {Dν : Fin d → (Fin d → ℝ) → ℝ}
    (hm : MemLpPer (ENNReal.ofReal betaBar) m)
    (hu : MemLpPer (ENNReal.ofReal gammaBar) u)
    (hDu : ∀ i, MemLpPer (ENNReal.ofReal gammaBar) (Du i))
    (hη : MemLpPer (ENNReal.ofReal betaBar') η)
    (hν : MemLpPer (ENNReal.ofReal gammaBar') ν)
    (hDν : ∀ i, MemLpPer (ENNReal.ofReal gammaBar') (Dν i)) :
    |mfgPairing m u Du η ν Dν| ≤
      lpNormPer (ENNReal.ofReal betaBar) m *
          lpNormPer (ENNReal.ofReal betaBar') η +
        lpNormPer (ENNReal.ofReal gammaBar) u *
          lpNormPer (ENNReal.ofReal gammaBar') ν +
        ∑ i : Fin d,
          lpNormPer (ENNReal.ofReal gammaBar) (Du i) *
            lpNormPer (ENNReal.ofReal gammaBar') (Dν i) := by
  -- Per-summand Hölder bounds.
  have h_m :
      |periodicIntegral (fun x => m x * η x)| ≤
        lpNormPer (ENNReal.ofReal betaBar) m *
          lpNormPer (ENNReal.ofReal betaBar') η :=
    abs_periodicIntegral_mul_le hβ hm hη
  have h_u :
      |periodicIntegral (fun x => u x * ν x)| ≤
        lpNormPer (ENNReal.ofReal gammaBar) u *
          lpNormPer (ENNReal.ofReal gammaBar') ν :=
    abs_periodicIntegral_mul_le hγ hu hν
  have h_grad : ∀ i : Fin d,
      |periodicIntegral (fun x => (Du i) x * (Dν i) x)| ≤
        lpNormPer (ENNReal.ofReal gammaBar) (Du i) *
          lpNormPer (ENNReal.ofReal gammaBar') (Dν i) := fun i =>
    abs_periodicIntegral_mul_le hγ (hDu i) (hDν i)
  -- Triangle inequality on `|· + · + sum|`.
  have habs_grad_sum :
      |∑ i : Fin d, periodicIntegral (fun x => (Du i) x * (Dν i) x)| ≤
        ∑ i : Fin d, |periodicIntegral (fun x => (Du i) x * (Dν i) x)| :=
    Finset.abs_sum_le_sum_abs _ _
  have hgrad_sum :
      ∑ i : Fin d, |periodicIntegral (fun x => (Du i) x * (Dν i) x)| ≤
        ∑ i : Fin d,
          lpNormPer (ENNReal.ofReal gammaBar) (Du i) *
            lpNormPer (ENNReal.ofReal gammaBar') (Dν i) :=
    Finset.sum_le_sum (fun i _ => h_grad i)
  unfold mfgPairing
  calc
    |periodicIntegral (fun x => m x * η x) +
        periodicIntegral (fun x => u x * ν x) +
        ∑ i : Fin d, periodicIntegral (fun x => (Du i) x * (Dν i) x)|
        ≤ |periodicIntegral (fun x => m x * η x)| +
            |periodicIntegral (fun x => u x * ν x)| +
            |∑ i : Fin d, periodicIntegral
              (fun x => (Du i) x * (Dν i) x)| := by
            have h1 :
                |periodicIntegral (fun x => m x * η x) +
                    periodicIntegral (fun x => u x * ν x)| ≤
                  |periodicIntegral (fun x => m x * η x)| +
                    |periodicIntegral (fun x => u x * ν x)| := abs_add_le _ _
            have h2 :
                |periodicIntegral (fun x => m x * η x) +
                    periodicIntegral (fun x => u x * ν x) +
                  ∑ i : Fin d, periodicIntegral
                    (fun x => (Du i) x * (Dν i) x)| ≤
                  |periodicIntegral (fun x => m x * η x) +
                    periodicIntegral (fun x => u x * ν x)| +
                    |∑ i : Fin d, periodicIntegral
                      (fun x => (Du i) x * (Dν i) x)| := abs_add_le _ _
            linarith
    _ ≤ lpNormPer (ENNReal.ofReal betaBar) m *
            lpNormPer (ENNReal.ofReal betaBar') η +
          lpNormPer (ENNReal.ofReal gammaBar) u *
            lpNormPer (ENNReal.ofReal gammaBar') ν +
          ∑ i : Fin d,
            lpNormPer (ENNReal.ofReal gammaBar) (Du i) *
              lpNormPer (ENNReal.ofReal gammaBar') (Dν i) := by
        have habs_grad : |∑ i : Fin d, periodicIntegral
            (fun x => (Du i) x * (Dν i) x)| ≤
          ∑ i : Fin d,
            lpNormPer (ENNReal.ofReal gammaBar) (Du i) *
              lpNormPer (ENNReal.ofReal gammaBar') (Dν i) :=
          le_trans habs_grad_sum hgrad_sum
        linarith [h_m, h_u]

/-! ## The MFG operator `A` and its weak-solution pairing identity

We now define the MFG operator
```
A(μ, υ) = ( -υ - H(x, Dυ, μ) + V(x),
             μ - div(μ D_pH(x, Dυ, μ)) - 1 )
```
on the domain `D(A) ⊃ {(μ, υ) : essinf μ > 0}` (paper line 849).

Following `docs/CONVENTIONS.md` §1b, we represent the value of `A(μ, υ)`
*via its action* on a test pair `(η, ν, Dν)`. The first component is an
honest function in `L^{β̄'}_per`; the second component is a distribution
in `W^{-1, γ̄'}_per`, so we encode it directly through the integral
duality bracket
```
⟨ μ - div(μ D_pH) - 1 , ν ⟩ := ∫ (μ - 1) ν dx + ∫ μ D_pH · Dν dx,
```
which is the *definitional* form of the distributional divergence
(integration by parts is built into the definition; no Mathlib
distributional calculus is needed). This is exactly the bracket used in
`defAepsi` (paper line 925) once the regularization is removed.

The bridge to the weak-solution definition is
`isWeakSolution_iff_operator_ineq`: a pair `(m, u)` with gradient family
`Du` is a weak solution (Definition `def:weak-solution-concept`,
formalized as `Solutions.Weak.IsWeakSolution`) iff the operator pairing
`mfgOperatorPair (μ, υ) - (m, u)` is non-negative for every admissible
test pair `(μ, υ)`.
-/

variable (V : (Fin d → ℝ) → ℝ)
variable (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
variable (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))

/-- **First component of the MFG operator** `A(μ, υ)`.

This is the bare function
```
x ↦ -υ(x) - H(x, Dυ(x), μ(x)) + V(x)
```
which the paper (line 854) places in `L^{β̄'}_per(𝕋^d)`. The gradient
family `Dυ : Fin d → (Fin d → ℝ) → ℝ` is passed explicitly, mirroring
the conventions of `IsStrongSolution` and `IsWeakSolution`. -/
def mfgOperatorFirst
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (μ υ : (Fin d → ℝ) → ℝ) : (Fin d → ℝ) → ℝ :=
  fun x => -(υ x) - H x (fun i => Dυ i x) (μ x) + V x

/-- **Pairing of the MFG operator `A(μ, υ)` with a test pair**
`(η, ν, Dν)`.

Encodes the duality bracket
```
⟨ A(μ, υ) , (η, ν) ⟩
  = ∫ (-υ - H(x, Dυ, μ) + V) η dx
  + ∫ (μ - 1) ν dx
  + ∫ μ · (D_pH(x, Dυ, μ) · Dν) dx,
```
where the last two integrals together realize the distributional
duality bracket `⟨ μ - div(μ D_pH) - 1 , ν ⟩`. The IBP identity
`∫ μ D_pH · Dν = -∫ div(μ D_pH) ν` is taken as the **definition** of
the distributional divergence acting on `ν` here; no Mathlib
distributional calculus is invoked.

We package the pairing as a single integral over the unit cube to make
the algebraic identity `mfgOperator_pairing_eq` definitionally
transparent. -/
def mfgOperatorPair
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (μ υ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ) : ℝ :=
  ∫ x in UnitCube d,
    (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * η x
      + μ x * (DpH x (fun i => Dυ i x) (μ x)
                ⬝ (fun i => Dν i x))
      + (μ x - 1) * ν x
  ∂(volume : Measure (Fin d → ℝ))

/-- **Admissibility predicate** for the MFG operator's domain
(paper line 859):

`InMFGOperatorDomain Dυ μ υ` records that `(μ, υ) ∈ L^∞ × W^{1,∞}` with
`essinf μ > 0`, formalized in the same pointwise-lower-bound form as
`IsWeakSolutionTestPair` (`Weak.lean`): the paper test space
`L^∞ × W^{1,∞}` with `essinf μ > 0` (the lower bound recorded in the
strictly stronger pointwise form `∃ c > 0, ∀ x, c ≤ μ x`).

We define the operator domain to *be* `IsWeakSolutionTestPair`, so the
two notions coincide definitionally. The paper says
`D(A) ⊃ {(μ, υ) ∈ L^∞ × W^{1,∞} : essinf μ > 0}`, so this is exactly
the subset on which we verify `A` is defined. -/
def InMFGOperatorDomain
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (μ υ : (Fin d → ℝ) → ℝ) : Prop :=
  Solutions.Weak.IsWeakSolutionTestPair Dυ μ υ

/-- The MFG operator's admissibility predicate coincides with the
weak-solution test-pair admissibility from `Solutions.Weak`. -/
lemma inMFGOperatorDomain_iff_isWeakSolutionTestPair
    (Dυ : Fin d → (Fin d → ℝ) → ℝ) (μ υ : (Fin d → ℝ) → ℝ) :
    InMFGOperatorDomain Dυ μ υ ↔
      Solutions.Weak.IsWeakSolutionTestPair Dυ μ υ := Iff.rfl

/-- **Pairing identity for the MFG operator**.

The pairing of `A(μ, υ)` against the test pair `((μ, υ) - (m, u))` —
that is, with `η = μ - m`, `ν = υ - u`, `Dν = Dυ - Du` — equals the
integrand of the weak-solution definition:
```
∫ ((-υ - H(x, Dυ, μ) + V)(μ - m)
   + μ · (D_pH(x, Dυ, μ) · (Dυ - Du))
   + (μ - 1)(υ - u)) dx.
```
This is the bridge that lets the abstract monotone-operator framework
of Phase 4 produce weak solutions. The proof is a pointwise algebraic
identity (the integrands are equal at every `x`). -/
theorem mfgOperator_pairing_eq
    (Dυ Du : Fin d → (Fin d → ℝ) → ℝ)
    (μ υ m u : (Fin d → ℝ) → ℝ) :
    mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
        (fun i x => Dυ i x - Du i x) (μ - m) (υ - u) =
      ∫ x in UnitCube d,
        (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (μ x - m x)
          + μ x * (DpH x (fun i => Dυ i x) (μ x)
                    ⬝ (fun i => Dυ i x - Du i x))
          + (μ x - 1) * (υ x - u x)
      ∂(volume : Measure (Fin d → ℝ)) := by
  unfold mfgOperatorPair
  refine setIntegral_congr_fun measurableSet_unitCube ?_
  intro x _
  simp [Pi.sub_apply]

/-- **Weak-solution-as-variational-inequality bridge** (paper line 860).

A pair `(m, u)` with explicit gradient family `Du` is a weak solution
in the sense of `Solutions.Weak.IsWeakSolution` iff for every
admissible test pair `(μ, υ)` (with explicit gradient family `Dυ`), the
scalar variational integrand is integrable and the MFG operator pairing
```
⟨ A(μ, υ) , (μ, υ) - (m, u) ⟩
```
is non-negative. This is exactly the reformulation of
`def:weak-solution-concept` advertised at paper line 860–873.

The proof is `Iff.rfl`-adjacent: rewriting the pairing on the
right-hand side via `mfgOperator_pairing_eq` recovers the
`IsWeakSolution` integrand verbatim, with its integrability clause retained. -/
theorem isWeakSolution_iff_operator_ineq
    (Du : Fin d → (Fin d → ℝ) → ℝ) (m u : (Fin d → ℝ) → ℝ) :
    Solutions.Weak.IsWeakSolution V H DpH Du m u ↔
      ∀ (Dυ : Fin d → (Fin d → ℝ) → ℝ) (μ υ : (Fin d → ℝ) → ℝ),
        InMFGOperatorDomain Dυ μ υ →
        Integrable (Solutions.Weak.weakSolutionIntegrand V H DpH Du m u Dυ μ υ)
          (volume.restrict (UnitCube d)) ∧
        0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
              (fun i x => Dυ i x - Du i x) (μ - m) (υ - u) := by
  unfold Solutions.Weak.IsWeakSolution InMFGOperatorDomain
  refine ⟨fun h Dυ μ υ hadm => ?_, fun h Dυ μ υ hadm => ?_⟩
  · refine ⟨(h Dυ μ υ hadm).1, ?_⟩
    rw [mfgOperator_pairing_eq]
    exact (h Dυ μ υ hadm).2
  · refine ⟨(h Dυ μ υ hadm).1, ?_⟩
    dsimp only [Solutions.Weak.weakSolutionIntegrand]
    rw [← mfgOperator_pairing_eq]
    exact (h Dυ μ υ hadm).2

/-! ## Pairing congruence + algebraic-split lemmas

The lemmas below form the **approved transport mechanism** between
quotient-side `Lp.coeFn` representatives and bare-function
`AEPeriodicRep.rep` representatives in Phase-4 closure code. Every
weak-pairing convergence proof should call `mfgOperatorPair_congr_ae`
or `_congr_ae_primal` to substitute representatives, instead of
re-deriving the substitution as ad-hoc `=ᵐ` threading.

The algebraic split lemma `mfgOperatorPair_split` matches the
integrand decomposition consumed by `tendsto_summand{1,2,3}` in
`Banach/Closure.lean`.
-/

section CongruenceLemmas

variable (V : (Fin d → ℝ) → ℝ)
  (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
  (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))

/-- **Test-triple a.e.-congruence** for the MFG operator pairing.

If two test triples `(Dν₁, η₁, ν₁)` and `(Dν₂, η₂, ν₂)` agree
a.e. on the unit cube (componentwise for the gradient family), the
two pairings agree. -/
theorem mfgOperatorPair_congr_ae
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (μ υ : (Fin d → ℝ) → ℝ)
    (Dν₁ Dν₂ : Fin d → (Fin d → ℝ) → ℝ)
    (η₁ η₂ ν₁ ν₂ : (Fin d → ℝ) → ℝ)
    (hDν : ∀ i, Dν₁ i =ᵐ[volume.restrict (UnitCube d)] Dν₂ i)
    (hη : η₁ =ᵐ[volume.restrict (UnitCube d)] η₂)
    (hν : ν₁ =ᵐ[volume.restrict (UnitCube d)] ν₂) :
    mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ Dν₁ η₁ ν₁
      = mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ Dν₂ η₂ ν₂ := by
  unfold mfgOperatorPair
  -- Bundle all the a.e.-equalities and apply integral_congr_ae.
  refine integral_congr_ae ?_
  -- Combine `hη`, `hν`, and the family `hDν` into a single ∀ᵐ.
  have hDν' : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ i, Dν₁ i x = Dν₂ i x := by
    rw [ae_all_iff]
    exact hDν
  filter_upwards [hη, hν, hDν'] with x hx_η hx_ν hx_Dν
  -- Pointwise rewrite of the integrand. The dot-product unfolds to a
  -- finite sum; rewrite each component.
  have hpt_Dν : (fun i => Dν₁ i x) = (fun i => Dν₂ i x) := by
    funext i; exact hx_Dν i
  rw [hx_η, hx_ν, hpt_Dν]

/-- **Primal-triple a.e.-congruence** for the MFG operator pairing.

If two primal triples `(Du₁, m₁, u₁)` and `(Du₂, m₂, u₂)` — interpreted
here as the *first*-slot data `(Dυ, μ, υ)` of `mfgOperatorPair` —
agree a.e. on the unit cube, the two pairings agree. (The names follow
the task spec: in `mfgOperatorPair`, the primal data is `Dυ μ υ`. The
distinguishing role of the lemma is that the *test* triple is fixed
and the *primal* triple varies.) -/
theorem mfgOperatorPair_congr_ae_primal
    (Du₁ Du₂ : Fin d → (Fin d → ℝ) → ℝ)
    (m₁ m₂ u₁ u₂ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ)
    (hDu : ∀ i, Du₁ i =ᵐ[volume.restrict (UnitCube d)] Du₂ i)
    (hm : m₁ =ᵐ[volume.restrict (UnitCube d)] m₂)
    (hu : u₁ =ᵐ[volume.restrict (UnitCube d)] u₂) :
    mfgOperatorPair (V := V) (H := H) (DpH := DpH) Du₁ m₁ u₁ Dν η ν
      = mfgOperatorPair (V := V) (H := H) (DpH := DpH) Du₂ m₂ u₂ Dν η ν := by
  unfold mfgOperatorPair
  refine integral_congr_ae ?_
  have hDu' : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ i, Du₁ i x = Du₂ i x := by
    rw [ae_all_iff]
    exact hDu
  filter_upwards [hm, hu, hDu'] with x hx_m hx_u hx_Du
  -- The integrand depends on `μ x`, `υ x`, and `(fun i => Dυ i x)`.
  have hpt : (fun i => Du₁ i x) = (fun i => Du₂ i x) := by
    funext i; exact hx_Du i
  rw [hx_m, hx_u, hpt]

/-- **Hamiltonian-carrier a.e.-congruence** for the MFG operator
pairing (D2b-2a).

The carrier `(H, DpH)` enters `mfgOperatorPair` only through the two
composites `x ↦ H x (Dυ x) (μ x)` and `x ↦ DpH x (Dυ x) (μ x)` in the
integrand. If those composites agree a.e. on the unit cube with the
composites of a second carrier `(H', DpH')`, the two pairings agree.

This is the carrier-transfer counterpart of `mfgOperatorPair_congr_ae`
(which varies the *slots* at a fixed carrier): here the *slots* are
fixed and the *carrier* varies. The intended use is a carrier swap
where `H = H'` on the support of `μ > 0` (e.g. `HdeltaK0 = HdeltaPos`
on the strict-positivity cone), so the caller discharges the composite
a.e.-equalities from a pointwise `{0 < μ}` agreement plus `μ > 0`
a.e. -/
theorem mfgOperatorPair_congr_H_ae
    (H' : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH' : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (μ υ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ)
    (hH : (fun x => H x (fun i => Dυ i x) (μ x))
            =ᵐ[volume.restrict (UnitCube d)]
          (fun x => H' x (fun i => Dυ i x) (μ x)))
    (hDpH : (fun x => DpH x (fun i => Dυ i x) (μ x))
              =ᵐ[volume.restrict (UnitCube d)]
            (fun x => DpH' x (fun i => Dυ i x) (μ x))) :
    mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ Dν η ν
      = mfgOperatorPair (V := V) (H := H') (DpH := DpH') Dυ μ υ Dν η ν := by
  unfold mfgOperatorPair
  refine integral_congr_ae ?_
  filter_upwards [hH, hDpH] with x hx_H hx_DpH
  rw [hx_H, hx_DpH]

/-! ### `AEPeriodicRep`-replacement lemmas -/

/-- **Test-side replacement.** Given an `AEPeriodicRep` for the
test-side scalar field `ν`, the pairing on the chosen periodic
representative equals the pairing on the original function. (Variants
for `η` and the gradient family follow analogously by chaining
`mfgOperatorPair_congr_ae`.) -/
theorem mfgOperatorPair_eq_on_AEPeriodicRep_test_ν
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (μ υ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ)
    (rep : Periodic.AEPeriodicRep ν) :
    mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ Dν η rep.rep
      = mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ Dν η ν :=
  mfgOperatorPair_congr_ae V H DpH Dυ μ υ Dν Dν η η rep.rep ν
    (fun _ => Filter.EventuallyEq.refl _ _)
    (Filter.EventuallyEq.refl _ _)
    rep.ae_eq

/-- **Test-side replacement for `η`.** -/
theorem mfgOperatorPair_eq_on_AEPeriodicRep_test_η
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (μ υ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ)
    (rep : Periodic.AEPeriodicRep η) :
    mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ Dν rep.rep ν
      = mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ Dν η ν :=
  mfgOperatorPair_congr_ae V H DpH Dυ μ υ Dν Dν rep.rep η ν ν
    (fun _ => Filter.EventuallyEq.refl _ _)
    rep.ae_eq
    (Filter.EventuallyEq.refl _ _)

/-- **Primal-side replacement for `μ`.** -/
theorem mfgOperatorPair_eq_on_AEPeriodicRep_primal_μ
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (μ υ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ)
    (rep : Periodic.AEPeriodicRep μ) :
    mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ rep.rep υ Dν η ν
      = mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ Dν η ν :=
  mfgOperatorPair_congr_ae_primal V H DpH Dυ Dυ rep.rep μ υ υ Dν η ν
    (fun _ => Filter.EventuallyEq.refl _ _)
    rep.ae_eq
    (Filter.EventuallyEq.refl _ _)

/-- **Primal-side replacement for `υ`.** -/
theorem mfgOperatorPair_eq_on_AEPeriodicRep_primal_υ
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (μ υ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ)
    (rep : Periodic.AEPeriodicRep υ) :
    mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ rep.rep Dν η ν
      = mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ Dν η ν :=
  mfgOperatorPair_congr_ae_primal V H DpH Dυ Dυ μ μ rep.rep υ Dν η ν
    (fun _ => Filter.EventuallyEq.refl _ _)
    (Filter.EventuallyEq.refl _ _)
    rep.ae_eq

/-! ### Algebraic split: integral additivity for `mfgOperatorPair`

`mfgOperatorPair` packs three integrands into a single integral. The
split lemma exposes the three component integrals separately, matching
the decomposition used by `tendsto_summand{1,2,3}` in
`Banach/Closure.lean`:
```
mfgOperatorPair Dυ μ υ Dν η ν
  = ∫ (-υ - H + V) · η               -- summand 1
  + ∫ μ · (D_pH ⬝ Dν)                -- summand 2 (a single integral
                                     --   over the dot product)
  + ∫ (μ - 1) · ν                    -- summand 3
```

We require **three separate integrability hypotheses** (one per
summand) instead of a single integrability of the whole sum, since
`integral_add` cannot recover the per-summand split otherwise. Every
downstream consumer already produces these three witnesses (see the
`tendsto_summand*` lemmas in `Banach/Closure.lean`).

(See `## AC scope amendment` in the task file for the rationale.)
-/

/-- **Algebraic split** of `mfgOperatorPair` into the three integrand
pieces matching `tendsto_summand{1,2,3}`. Requires the three
per-summand integrabilities. -/
theorem mfgOperatorPair_split
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (μ υ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ)
    (h_int1 : Integrable (fun x =>
        (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * η x)
        (volume.restrict (UnitCube d)))
    (h_int2 : Integrable (fun x =>
        μ x * (DpH x (fun i => Dυ i x) (μ x) ⬝ (fun i => Dν i x)))
        (volume.restrict (UnitCube d)))
    (h_int3 : Integrable (fun x => (μ x - 1) * ν x)
        (volume.restrict (UnitCube d))) :
    mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ Dν η ν
      = (∫ x in UnitCube d,
          (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * η x)
        + (∫ x in UnitCube d,
            μ x * (DpH x (fun i => Dυ i x) (μ x) ⬝ (fun i => Dν i x)))
        + (∫ x in UnitCube d, (μ x - 1) * ν x) := by
  unfold mfgOperatorPair
  -- The pairing integrand is `(s1 + s2) + s3` pointwise. Re-express
  -- it as `(s1 + s2) x + s3 x` form so that `integral_add` matches.
  set f1 : (Fin d → ℝ) → ℝ :=
    fun x => (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * η x with hf1
  set f2 : (Fin d → ℝ) → ℝ :=
    fun x => μ x * (DpH x (fun i => Dυ i x) (μ x) ⬝ (fun i => Dν i x)) with hf2
  set f3 : (Fin d → ℝ) → ℝ := fun x => (μ x - 1) * ν x with hf3
  have h12 : Integrable (fun x => f1 x + f2 x) (volume.restrict (UnitCube d)) :=
    h_int1.add h_int2
  have hrewrite :
      (∫ x in UnitCube d, f1 x + f2 x + f3 x) =
        (∫ x in UnitCube d, f1 x) + (∫ x in UnitCube d, f2 x)
        + (∫ x in UnitCube d, f3 x) := by
    have h₁ : ∫ x in UnitCube d, f1 x + f2 x + f3 x
        = (∫ x in UnitCube d, f1 x + f2 x)
          + ∫ x in UnitCube d, f3 x :=
      integral_add h12 h_int3
    have h₂ : ∫ x in UnitCube d, f1 x + f2 x
        = (∫ x in UnitCube d, f1 x) + ∫ x in UnitCube d, f2 x :=
      integral_add h_int1 h_int2
    rw [h₁, h₂]
  exact hrewrite

/-! ### ε-form analogue: congruence for `mfgOperatorEpsPair` -/

end CongruenceLemmas

/-- **Potential-side a.e.-congruence** for the MFG operator pairing.

If two potentials `V₁` and `V₂` agree a.e. on the unit cube, the two
pairings agree. Used in Phase 4 to swap an `Lp`-only potential for its
measurable representative when invoking aggregators that demand
`Measurable V`. The pairing's `V` dependence enters only via the
summand `(-υ - H(x, Dυ, μ) + V) · η`, which is a.e.-equal under
`V₁ =ᵐ V₂`. -/
theorem mfgOperatorPair_congr_V_ae
    (V₁ V₂ : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (μ υ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ)
    (hV : V₁ =ᵐ[volume.restrict (UnitCube d)] V₂) :
    mfgOperatorPair (V := V₁) (H := H) (DpH := DpH) Dυ μ υ Dν η ν
      = mfgOperatorPair (V := V₂) (H := H) (DpH := DpH) Dυ μ υ Dν η ν := by
  unfold mfgOperatorPair
  refine integral_congr_ae ?_
  filter_upwards [hV] with x hx_V
  rw [hx_V]

end MFG
end Solutions
end StationaryMFG
