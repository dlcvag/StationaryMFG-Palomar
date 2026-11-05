module

public import StationaryMFG.Periodic.Lp
public import StationaryMFG.Periodic.Integral
public import StationaryMFG.Periodic.TestFunctions
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Order.Fin.Tuple

@[expose] public section

/-!
# Distributional / weak partial derivative against periodic test functions

Per `docs/CONVENTIONS.md` §1, "the torus" is modelled by the half-open unit
cube and functions are bare maps `(Fin d → ℝ) → ℝ`. This file introduces the
*distributional* weak partial derivative against the smooth periodic test
functions `SmoothPeriodic d` defined in `TestFunctions.lean`:

`HasWeakDerivPer i f g  :=  MemLpPer 1 g  ∧
   ∀ φ : SmoothPeriodic d,
     ∫_𝕋 g · φ  =  - ∫_𝕋 f · ∂_i φ`.

The cheap structural results recorded here:

* `HasWeakDerivPer.memLpPer` — the derivative is in `L^1_per`.
* `HasWeakDerivPer.congr_ae` — congruence under a.e.-equality of the
  derivative on the unit cube.

The headline result is `HasWeakDerivPer.of_contDiff`: the classical partial
derivative of a smooth periodic function is the weak partial derivative.
The proof goes via the *integral-of-derivative-vanishes* lemma
`integral_partialDeriv_eq_zero` (which is the genuine analytic content) and
the Leibniz product rule applied to `φ * ψ`.
-/

namespace StationaryMFG
namespace Periodic

open MeasureTheory Set
open scoped ENNReal ContDiff

variable {d : ℕ}

/-- `f` has *weak partial derivative* `g` in direction `e_i` against periodic
test functions: `g` is in `L^1_per` and the integration-by-parts formula
`∫ g · φ = -∫ f · ∂_i φ` holds for every `φ ∈ SmoothPeriodic d`. -/
def HasWeakDerivPer (i : Fin d) (f g : (Fin d → ℝ) → ℝ) : Prop :=
  MemLpPer 1 g ∧
    ∀ φ : SmoothPeriodic d,
      periodicIntegral (fun x => g x * (φ : (Fin d → ℝ) → ℝ) x) =
        - periodicIntegral
            (fun x => f x *
              ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x)

namespace HasWeakDerivPer

/-- The weak derivative is, in particular, an `L^1_per` function. -/
lemma memLpPer {i : Fin d} {f g : (Fin d → ℝ) → ℝ}
    (h : HasWeakDerivPer i f g) : MemLpPer 1 g := h.1

/-- Unfolded form of the weak-derivative integration-by-parts identity. -/
lemma integral_eq {i : Fin d} {f g : (Fin d → ℝ) → ℝ}
    (h : HasWeakDerivPer i f g) (φ : SmoothPeriodic d) :
    periodicIntegral (fun x => g x * (φ : (Fin d → ℝ) → ℝ) x) =
      - periodicIntegral
          (fun x => f x *
            ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x) :=
  h.2 φ

/-- A weak-derivative function is integrable on the unit cube. -/
lemma integrableOn {i : Fin d} {f g : (Fin d → ℝ) → ℝ}
    (h : HasWeakDerivPer i f g) :
    IntegrableOn g (UnitCube d) := by
  have hMemLp : MemLp g 1 (Measure.restrict volume (UnitCube d)) := h.memLpPer.toMemLp
  have hInt : Integrable g (Measure.restrict volume (UnitCube d)) :=
    (memLp_one_iff_integrable).1 hMemLp
  exact hInt

/-- Congruence under a.e.-equality of the derivative. If `g'` is a.e. equal
to `g` on the unit cube and is itself in `L^1_per`, then `g'` is also a weak
derivative of `f` in direction `i`. -/
lemma congr_ae {i : Fin d} {f g g' : (Fin d → ℝ) → ℝ}
    (h : HasWeakDerivPer i f g)
    (hg' : MemLpPer 1 g')
    (hgg' : g =ᵐ[Measure.restrict volume (UnitCube d)] g') :
    HasWeakDerivPer i f g' := by
  refine ⟨hg', ?_⟩
  intro φ
  have hpair : (fun x => g x * (φ : (Fin d → ℝ) → ℝ) x)
      =ᵐ[Measure.restrict volume (UnitCube d)]
        (fun x => g' x * (φ : (Fin d → ℝ) → ℝ) x) := by
    filter_upwards [hgg'] with x hx
    simp [hx]
  have hint :
      periodicIntegral (fun x => g x * (φ : (Fin d → ℝ) → ℝ) x) =
        periodicIntegral (fun x => g' x * (φ : (Fin d → ℝ) → ℝ) x) := by
    unfold periodicIntegral
    exact integral_congr_ae hpair
  rw [← hint]
  exact h.integral_eq φ

/-- **Additivity of the weak periodic derivative** (Lᵖ-typed variant). If
`g₁ = ∂_i^w f₁` and `g₂ = ∂_i^w f₂` and additionally `f₁, f₂ ∈ Lᵖ_per` for
some `p ≥ 1`, then `g₁ + g₂ = ∂_i^w (f₁ + f₂)`. The Lᵖ hypothesis on
`f₁, f₂` ensures `f_j · ∂ᵢ φ` is integrable so that linearity of the integral
applies to the right-hand side of the IBP identity. -/
lemma add {i : Fin d} {f₁ f₂ g₁ g₂ : (Fin d → ℝ) → ℝ}
    {p : ℝ≥0∞} (hp1 : 1 ≤ p)
    (hf₁ : MemLpPer p f₁) (hf₂ : MemLpPer p f₂)
    (h₁ : HasWeakDerivPer i f₁ g₁) (h₂ : HasWeakDerivPer i f₂ g₂) :
    HasWeakDerivPer i (fun x => f₁ x + f₂ x) (fun x => g₁ x + g₂ x) := by
  refine ⟨?_, ?_⟩
  · -- `MemLpPer 1 (g₁ + g₂)`.
    exact (h₁.memLpPer.add h₂.memLpPer)
  · intro φ
    classical
    -- The unit cube has finite Lebesgue measure.
    have hfin : IsFiniteMeasure (Measure.restrict volume (UnitCube d)) :=
      ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
    -- Continuity of `φ` and `∂ᵢ φ` (smoothness ⇒ continuity).
    have hcont_φ : Continuous (φ : (Fin d → ℝ) → ℝ) :=
      φ.smooth.continuous
    have hcont_dφ : Continuous
        ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) :=
      (SmoothPeriodic.partialDeriv i φ).smooth.continuous
    -- Boundedness on the closed cube `[0,1]^d` (a compact superset of
    -- `UnitCube d`) by continuity.
    have hcompactCube : IsCompact (pi univ (fun _ : Fin d => Icc (0 : ℝ) 1)) :=
      isCompact_univ_pi (fun _ => isCompact_Icc)
    have hsub : UnitCube d ⊆ pi univ (fun _ : Fin d => Icc (0 : ℝ) 1) := by
      intro x hx j _
      exact Ico_subset_Icc_self (hx j (mem_univ _))
    obtain ⟨Cφ, hCφ⟩ :=
      hcompactCube.bddAbove_image (f := fun x => ‖(φ : (Fin d → ℝ) → ℝ) x‖)
        (hcont_φ.norm.continuousOn)
    obtain ⟨Cdφ, hCdφ⟩ :=
      hcompactCube.bddAbove_image (f := fun x =>
        ‖((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) x‖)
        (hcont_dφ.norm.continuousOn)
    -- Pointwise bounds on the closed cube.
    have hbnd_φ_pt : ∀ x ∈ pi univ (fun _ : Fin d => Icc (0 : ℝ) 1),
        ‖(φ : (Fin d → ℝ) → ℝ) x‖ ≤ Cφ := fun x hx =>
      hCφ ⟨x, hx, rfl⟩
    have hbnd_dφ_pt : ∀ x ∈ pi univ (fun _ : Fin d => Icc (0 : ℝ) 1),
        ‖((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) x‖ ≤ Cdφ := fun x hx =>
      hCdφ ⟨x, hx, rfl⟩
    -- Bound restricted to `UnitCube d` ⊆ closed cube, transferred to a.e.
    have hbnd_φ_ae : ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ‖(φ : (Fin d → ℝ) → ℝ) x‖ ≤ Cφ := by
      refine (ae_restrict_iff' (measurableSet_unitCube)).mpr ?_
      refine Filter.Eventually.of_forall ?_
      intro x hx
      exact hbnd_φ_pt x (hsub hx)
    have hbnd_dφ_ae : ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ‖((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) x‖ ≤ Cdφ := by
      refine (ae_restrict_iff' (measurableSet_unitCube)).mpr ?_
      refine Filter.Eventually.of_forall ?_
      intro x hx
      exact hbnd_dφ_pt x (hsub hx)
    -- Integrability of `g_j * φ`: `g_j ∈ L¹` and `φ` is bounded a.e.
    have hg₁_int : Integrable (fun x => g₁ x * (φ : (Fin d → ℝ) → ℝ) x)
        (Measure.restrict volume (UnitCube d)) :=
      (memLp_one_iff_integrable.mp h₁.memLpPer.toMemLp).mul_bdd
        hcont_φ.aestronglyMeasurable hbnd_φ_ae
    have hg₂_int : Integrable (fun x => g₂ x * (φ : (Fin d → ℝ) → ℝ) x)
        (Measure.restrict volume (UnitCube d)) :=
      (memLp_one_iff_integrable.mp h₂.memLpPer.toMemLp).mul_bdd
        hcont_φ.aestronglyMeasurable hbnd_φ_ae
    -- `f_j ∈ L¹_per` since the cube has finite measure and `f_j ∈ Lᵖ`.
    have hf₁_int : Integrable f₁
        (Measure.restrict volume (UnitCube d)) :=
      MeasureTheory.MemLp.integrable (μ := Measure.restrict volume (UnitCube d))
        hp1 hf₁.toMemLp
    have hf₂_int : Integrable f₂
        (Measure.restrict volume (UnitCube d)) :=
      MeasureTheory.MemLp.integrable (μ := Measure.restrict volume (UnitCube d))
        hp1 hf₂.toMemLp
    -- Integrability of `f_j * ∂ᵢ φ`: `f_j ∈ L¹` and `∂ᵢ φ` is bounded a.e.
    have hf₁_dφ_int : Integrable
        (fun x => f₁ x *
          ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) x)
        (Measure.restrict volume (UnitCube d)) :=
      hf₁_int.mul_bdd hcont_dφ.aestronglyMeasurable hbnd_dφ_ae
    have hf₂_dφ_int : Integrable
        (fun x => f₂ x *
          ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) x)
        (Measure.restrict volume (UnitCube d)) :=
      hf₂_int.mul_bdd hcont_dφ.aestronglyMeasurable hbnd_dφ_ae
    -- Now distribute and use linearity.
    have hLHS :
        periodicIntegral
            (fun x => (g₁ x + g₂ x) * (φ : (Fin d → ℝ) → ℝ) x)
          = periodicIntegral (fun x => g₁ x * (φ : (Fin d → ℝ) → ℝ) x)
            + periodicIntegral (fun x => g₂ x * (φ : (Fin d → ℝ) → ℝ) x) := by
      have hpt :
          (fun x : Fin d → ℝ => (g₁ x + g₂ x) * (φ : (Fin d → ℝ) → ℝ) x)
            = (fun x => g₁ x * (φ : (Fin d → ℝ) → ℝ) x)
                + (fun x => g₂ x * (φ : (Fin d → ℝ) → ℝ) x) := by
        funext x
        simp [Pi.add_apply, add_mul]
      rw [hpt]
      exact periodicIntegral_add (hg₁_int : IntegrableOn _ (UnitCube d) _)
        (hg₂_int : IntegrableOn _ (UnitCube d) _)
    have hRHS :
        periodicIntegral
            (fun x => (f₁ x + f₂ x) *
              ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x)
          = periodicIntegral
              (fun x => f₁ x *
                ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                    (Fin d → ℝ) → ℝ) x)
            + periodicIntegral
              (fun x => f₂ x *
                ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                    (Fin d → ℝ) → ℝ) x) := by
      have hpt :
          (fun x : Fin d → ℝ => (f₁ x + f₂ x) *
            ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x)
            = (fun x => f₁ x *
                ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                    (Fin d → ℝ) → ℝ) x)
              + (fun x => f₂ x *
                ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                    (Fin d → ℝ) → ℝ) x) := by
        funext x
        simp [Pi.add_apply, add_mul]
      rw [hpt]
      exact periodicIntegral_add (hf₁_dφ_int : IntegrableOn _ (UnitCube d) _)
        (hf₂_dφ_int : IntegrableOn _ (UnitCube d) _)
    rw [hLHS, hRHS]
    rw [h₁.integral_eq φ, h₂.integral_eq φ]
    ring

/-- **Scalar-multiple of a weak periodic derivative.** If `g = ∂_i^w f`, then
`c · g = ∂_i^w (c · f)`. -/
lemma const_smul {i : Fin d} {f g : (Fin d → ℝ) → ℝ}
    (c : ℝ) (h : HasWeakDerivPer i f g) :
    HasWeakDerivPer i (fun x => c * f x) (fun x => c * g x) := by
  refine ⟨?_, ?_⟩
  · -- `MemLpPer 1 (c · g)`: from `MemLpPer.const_smul`.
    have hcg := h.memLpPer.const_smul (𝕜 := ℝ) c
    -- `(c • g) x = c * g x` pointwise.
    have hpt : (c • g : (Fin d → ℝ) → ℝ) = fun x => c * g x := by
      funext x; simp [Pi.smul_apply, smul_eq_mul]
    rw [hpt] at hcg
    exact hcg
  · intro φ
    -- Pull the constant `c` out of both periodic integrals.
    have hLHS :
        periodicIntegral
            (fun x => c * g x * (φ : (Fin d → ℝ) → ℝ) x)
          = c * periodicIntegral
              (fun x => g x * (φ : (Fin d → ℝ) → ℝ) x) := by
      have hpt :
          (fun x : Fin d → ℝ => c * g x * (φ : (Fin d → ℝ) → ℝ) x)
            = fun x => c • (g x * (φ : (Fin d → ℝ) → ℝ) x) := by
        funext x; simp [smul_eq_mul]; ring
      rw [hpt]
      rw [periodicIntegral_smul (𝕜 := ℝ) (E := ℝ) c
        (fun x => g x * (φ : (Fin d → ℝ) → ℝ) x)]
      simp [smul_eq_mul]
    have hRHS :
        periodicIntegral
            (fun x => c * f x *
              ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x)
          = c * periodicIntegral
              (fun x => f x *
                ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                    (Fin d → ℝ) → ℝ) x) := by
      have hpt :
          (fun x : Fin d → ℝ => c * f x *
            ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x)
            = fun x => c • (f x *
                ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                    (Fin d → ℝ) → ℝ) x) := by
        funext x; simp [smul_eq_mul]; ring
      rw [hpt]
      rw [periodicIntegral_smul (𝕜 := ℝ) (E := ℝ) c
        (fun x => f x *
          ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) x)]
      simp [smul_eq_mul]
    rw [hLHS, hRHS, h.integral_eq φ]
    ring

end HasWeakDerivPer

/-! ## Smooth periodic ⇒ weak derivative

The key analytic step: if `F : (Fin d → ℝ) → ℝ` is smooth and periodic, then
`∫_{[0,1]^d} (∂_i F)(x) dx = 0`.

The proof uses Fubini to slice along coordinate `i`, applies the 1D
fundamental theorem of calculus to evaluate the inner integral as
`F(x with i = 1) - F(x with i = 0)`, and observes that this difference
vanishes by periodicity (the two points differ by the integer-lattice vector
`e_i = Pi.single i 1`).
-/

section IntegralOfPartialDerivVanishes

/-- Fact about `Pi.basisFun` evaluated explicitly: the basis vector at index
`i` is `Pi.single i 1`. -/
private lemma piBasisFun_eq_single (i : Fin d) :
    (Pi.basisFun ℝ (Fin d) i : Fin d → ℝ) =
      (Pi.single (M := fun _ => ℝ) i (1 : ℝ)) := by
  ext j
  by_cases h : j = i
  · subst h; simp [Pi.basisFun_apply]
  · simp [Pi.basisFun_apply, h]

/-- The integer-lattice translate of `Fin.insertNth i 0 y` by the unit vector
in direction `i` is `Fin.insertNth i 1 y`. -/
private lemma insertNth_one_eq_insertNth_zero_add_e
    {n : ℕ} (i : Fin (n + 1)) (y : Fin n → ℝ) :
    i.insertNth (1 : ℝ) y =
      i.insertNth (0 : ℝ) y + (Pi.single (M := fun _ => ℝ) i (1 : ℝ)) := by
  ext j
  rcases Fin.eq_self_or_eq_succAbove i j with hj | ⟨k, rfl⟩
  · subst hj; simp [Fin.insertNth_apply_same]
  · simp [Fin.insertNth_apply_succAbove, Fin.succAbove_ne i k]

/-- The integer-lattice unit vector at index `i`, viewed via integer cast,
equals the real unit vector `Pi.single i 1`. -/
private lemma intCoe_pi_single_eq {n : ℕ} (i : Fin (n + 1)) :
    (fun j : Fin (n + 1) =>
        (((Pi.single (M := fun _ => ℤ) i (1 : ℤ)) j : ℤ) : ℝ)) =
      (Pi.single (M := fun _ => ℝ) i (1 : ℝ)) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Pi.single_eq_of_ne hj]

/-- For a smooth periodic real-valued function `F` and any direction `i`, the
integral of `∂_i F` over the unit cube is zero. -/
lemma integral_partialDeriv_eq_zero
    (F : (Fin d → ℝ) → ℝ) (hF_smooth : ContDiff ℝ ((⊤ : ℕ∞) : ℕ∞ω) F)
    (hF_per : IsPeriodic F) (i : Fin d) :
    periodicIntegral
        (fun x => fderiv ℝ F x (Pi.basisFun ℝ (Fin d) i)) = 0 := by
  -- Step 0: `d` must be positive since `i : Fin d`. Set `d = n + 1`.
  rcases Nat.exists_eq_succ_of_ne_zero (Fin.size_positive i).ne' with ⟨n, rfl⟩
  -- Use the measurable equivalence `(Fin (n+1) → ℝ) ≃ ℝ × (Fin n → ℝ)` that
  -- splits off coordinate `i`.
  set e : (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i with he_def
  have hem : MeasurePreserving e (volume) ((volume).prod (volume)) := by
    have := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
    convert this using 1
  -- `e.symm (t, y) = i.insertNth t y`.
  have he_symm_eq : ∀ p : ℝ × (Fin n → ℝ),
      e.symm p = i.insertNth p.1 p.2 := by
    intro p
    rfl
  -- Step 1: pulled-back unit cube via `e.symm`.
  have hpre :
      e.symm ⁻¹' UnitCube (n + 1) =
        Ico (0 : ℝ) 1 ×ˢ pi (univ : Set (Fin n)) (fun _ => Ico (0 : ℝ) 1) := by
    ext ⟨t, y⟩
    simp only [mem_preimage, mem_unitCube_iff, mem_prod, mem_Ico, mem_pi,
      mem_univ, true_imp_iff]
    rw [he_symm_eq]
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · have h1 := h i
        rw [Fin.insertNth_apply_same] at h1
        exact h1
      · intro j
        have hj := h (i.succAbove j)
        rw [Fin.insertNth_apply_succAbove] at hj
        exact hj
    · rintro ⟨ht, hy⟩
      intro j
      rcases Fin.eq_self_or_eq_succAbove i j with hj | ⟨k, rfl⟩
      · subst hj
        rw [Fin.insertNth_apply_same]
        exact ht
      · rw [Fin.insertNth_apply_succAbove]
        exact hy k
  -- Step 2: continuity of the integrand.
  have hCont_full : Continuous fun x : Fin (n + 1) → ℝ =>
      fderiv ℝ F x (Pi.basisFun ℝ (Fin (n + 1)) i) :=
    (hF_smooth.continuous_fderiv (by decide : ((⊤ : ℕ∞) : ℕ∞ω) ≠ 0)).clm_apply continuous_const
  have he_symm_cont : Continuous (e.symm : ℝ × (Fin n → ℝ) → Fin (n + 1) → ℝ) := by
    -- `e.symm (t, y) = i.insertNth t y` is continuous.
    change Continuous
      (fun p : ℝ × (Fin n → ℝ) => i.insertNth (α := fun _ => ℝ) p.1 p.2)
    exact Continuous.finInsertNth (A := fun _ => ℝ) i continuous_fst continuous_snd
  have hCont : Continuous fun p : ℝ × (Fin n → ℝ) =>
      fderiv ℝ F (e.symm p) (Pi.basisFun ℝ (Fin (n + 1)) i) :=
    hCont_full.comp he_symm_cont
  -- Step 3: pull back the periodic integral via `e.symm`.
  unfold periodicIntegral
  have hsymm_meas : MeasurePreserving e.symm
      ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) volume :=
    hem.symm
  -- Rewrite UnitCube (n+1) as `e.symm '' (preimage)`.
  have hcube_image : (UnitCube (n + 1) : Set (Fin (n + 1) → ℝ)) =
      e.symm '' (e.symm ⁻¹' UnitCube (n + 1)) :=
    (Set.image_preimage_eq _ e.symm.surjective).symm
  rw [hcube_image,
      hsymm_meas.setIntegral_image_emb e.symm.measurableEmbedding
        (fun x => fderiv ℝ F x (Pi.basisFun ℝ (Fin (n + 1)) i)) _,
      hpre]
  -- Step 4: integrability on the product set, by inclusion in a compact superset.
  have hcompact :
      IsCompact (Icc (0 : ℝ) 1 ×ˢ pi (univ : Set (Fin n)) fun _ => Icc (0 : ℝ) 1) := by
    refine isCompact_Icc.prod ?_
    exact isCompact_univ_pi (fun _ => isCompact_Icc)
  have hsub :
      Ico (0 : ℝ) 1 ×ˢ pi (univ : Set (Fin n)) (fun _ => Ico (0 : ℝ) 1) ⊆
        Icc (0 : ℝ) 1 ×ˢ pi (univ : Set (Fin n)) fun _ => Icc (0 : ℝ) 1 := by
    intro p hp
    refine ⟨?_, ?_⟩
    · exact Ico_subset_Icc_self hp.1
    · intro j _
      exact Ico_subset_Icc_self (hp.2 j (mem_univ _))
  have hLocInt :
      LocallyIntegrable (fun p : ℝ × (Fin n → ℝ) =>
        fderiv ℝ F (e.symm p) (Pi.basisFun ℝ (Fin (n + 1)) i))
        ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) := by
    exact hCont.locallyIntegrable
  have hIntegrableOnCompact :
      IntegrableOn (fun p : ℝ × (Fin n → ℝ) =>
        fderiv ℝ F (e.symm p) (Pi.basisFun ℝ (Fin (n + 1)) i))
        (Icc (0 : ℝ) 1 ×ˢ pi (univ : Set (Fin n)) fun _ => Icc (0 : ℝ) 1)
        ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) :=
    hLocInt.integrableOn_isCompact hcompact
  have hIntegrableOn :
      IntegrableOn (fun p : ℝ × (Fin n → ℝ) =>
        fderiv ℝ F (e.symm p) (Pi.basisFun ℝ (Fin (n + 1)) i))
        (Ico (0 : ℝ) 1 ×ˢ pi (univ : Set (Fin n)) (fun _ => Ico (0 : ℝ) 1))
        ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) :=
    hIntegrableOnCompact.mono_set hsub
  -- Step 5: apply Fubini (integrate `t` first via the *symm* form) and FTC.
  have hIntOnRestrict :
      Integrable (fun p : ℝ × (Fin n → ℝ) =>
          fderiv ℝ F (e.symm p) (Pi.basisFun ℝ (Fin (n + 1)) i))
        (((volume : Measure ℝ).restrict (Ico (0 : ℝ) 1)).prod
          ((volume : Measure (Fin n → ℝ)).restrict
            (pi (univ : Set (Fin n)) fun _ => Ico (0 : ℝ) 1))) := by
    rw [Measure.prod_restrict]
    exact hIntegrableOn
  -- Use Fubini's theorem (symmetric form) to integrate `t` last.
  have hFubini :
      ∫ p in Ico (0 : ℝ) 1 ×ˢ pi (univ : Set (Fin n)) (fun _ => Ico (0 : ℝ) 1),
          fderiv ℝ F (e.symm p) (Pi.basisFun ℝ (Fin (n + 1)) i)
          ∂((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) =
        ∫ y in pi (univ : Set (Fin n)) (fun _ => Ico (0 : ℝ) 1),
          ∫ t in Ico (0 : ℝ) 1,
            fderiv ℝ F (i.insertNth t y) (Pi.basisFun ℝ (Fin (n + 1)) i) := by
    rw [← Measure.prod_restrict]
    rw [integral_prod_symm _ hIntOnRestrict]
    rfl
  rw [hFubini]
  -- For each `y`, the inner integral is `0` by FTC + periodicity.
  have hzero :
      ∀ y : Fin n → ℝ,
        ∫ t in Ico (0 : ℝ) 1,
            fderiv ℝ F (i.insertNth t y) (Pi.basisFun ℝ (Fin (n + 1)) i) = 0 := by
    intro y
    -- Define the 1D function `Fy : ℝ → ℝ`, `Fy t = F (insertNth i t y)`.
    set Fy : ℝ → ℝ := fun t => F (i.insertNth t y) with hFy_def
    -- Smoothness of `Fy`.
    have hins_smooth : ContDiff ℝ ((⊤ : ℕ∞) : ℕ∞ω)
        (fun t : ℝ => i.insertNth (α := fun _ => ℝ) t y) := by
      rw [contDiff_pi]
      intro j
      rcases Fin.eq_self_or_eq_succAbove i j with hj | ⟨k, rfl⟩
      · subst hj
        simp_rw [Fin.insertNth_apply_same]
        exact contDiff_id
      · simp_rw [Fin.insertNth_apply_succAbove]
        exact contDiff_const
    have hFy_smooth : ContDiff ℝ ((⊤ : ℕ∞) : ℕ∞ω) Fy := hF_smooth.comp hins_smooth
    -- 1D derivative of `Fy` at `t` equals `fderiv ℝ F (insertNth i t y) e_i`.
    have hFy_deriv : ∀ t : ℝ,
        HasDerivAt Fy
          (fderiv ℝ F (i.insertNth t y) (Pi.basisFun ℝ (Fin (n + 1)) i)) t := by
      intro t
      have hF_diff : HasFDerivAt F (fderiv ℝ F (i.insertNth t y))
          (i.insertNth t y) :=
        ((hF_smooth.differentiable (by decide : ((⊤ : ℕ∞) : ℕ∞ω) ≠ 0))
          (i.insertNth t y)).hasFDerivAt
      have hins_deriv :
          HasDerivAt (fun t : ℝ => i.insertNth (α := fun _ => ℝ) t y)
            (Pi.single (M := fun _ => ℝ) i (1 : ℝ)) t := by
        rw [hasDerivAt_pi]
        intro j
        rcases Fin.eq_self_or_eq_succAbove i j with hj | ⟨k, rfl⟩
        · subst hj
          simp_rw [Fin.insertNth_apply_same, Pi.single_eq_same]
          exact hasDerivAt_id _
        · simp_rw [Fin.insertNth_apply_succAbove]
          have hne : i.succAbove k ≠ i := Fin.succAbove_ne i k
          rw [Pi.single_eq_of_ne hne]
          exact hasDerivAt_const _ _
      have hcomp := hF_diff.comp_hasDerivAt t hins_deriv
      rw [piBasisFun_eq_single]
      exact hcomp
    -- Continuity of the derivative ⇒ `IntervalIntegrable`.
    have hFy'_cont : Continuous fun t =>
        fderiv ℝ F (i.insertNth t y) (Pi.basisFun ℝ (Fin (n + 1)) i) := by
      have hcont : Continuous (fun t : ℝ => i.insertNth (α := fun _ => ℝ) t y) :=
        Continuous.finInsertNth (A := fun _ => ℝ) i continuous_id continuous_const
      exact hCont_full.comp hcont
    have hFy'_int :
        IntervalIntegrable
          (fun t => fderiv ℝ F (i.insertNth t y) (Pi.basisFun ℝ (Fin (n + 1)) i))
          volume 0 1 := hFy'_cont.intervalIntegrable _ _
    -- FTC: `∫ t in 0..1, Fy'(t) dt = Fy 1 - Fy 0`.
    have hFTC :
        ∫ t in (0 : ℝ)..1,
            fderiv ℝ F (i.insertNth t y) (Pi.basisFun ℝ (Fin (n + 1)) i) =
          Fy 1 - Fy 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ => hFy_deriv t) hFy'_int
    -- Move from `∫ in Ico 0 1` to `∫ in 0..1`.
    rw [integral_Ico_eq_integral_Ioc]
    rw [show (∫ t in Ioc (0 : ℝ) 1,
              fderiv ℝ F (i.insertNth t y) (Pi.basisFun ℝ (Fin (n + 1)) i)) =
            ∫ t in (0 : ℝ)..1,
              fderiv ℝ F (i.insertNth t y) (Pi.basisFun ℝ (Fin (n + 1)) i) from ?_]
    · rw [hFTC]
      -- Boundary cancels by periodicity.
      have hperFy : Fy 1 = Fy 0 := by
        have hper_apply :
            F (i.insertNth (0 : ℝ) y +
                fun j => (((Pi.single (M := fun _ => ℤ) i (1 : ℤ)) j : ℤ) : ℝ)) =
              F (i.insertNth (0 : ℝ) y) :=
          hF_per (Pi.single (M := fun _ => ℤ) i (1 : ℤ)) _
        rw [intCoe_pi_single_eq] at hper_apply
        change F (i.insertNth (1 : ℝ) y) = F (i.insertNth (0 : ℝ) y)
        rw [insertNth_one_eq_insertNth_zero_add_e, hper_apply]
      rw [hperFy]; ring
    · rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  -- Now sum: outer integral of `0` is `0`.
  simp_rw [hzero]
  simp

end IntegralOfPartialDerivVanishes

/-! ## Periodisation of a cube-supported smooth bump

To prove a.e. uniqueness of the periodic weak derivative we need to feed the
`HasWeakDerivPer` integration-by-parts identity a *periodic* test function that,
on the unit cube, agrees with an arbitrary compactly-supported smooth bump
`ψ` whose closed support lies in the OPEN cube `(0,1)^d`. The construction is
the integer-lattice periodisation

`cubeBumpPer ψ s := ∑' k : Fin d → ℤ, ψ (s - k_ℝ)`.

Because `tsupport ψ` is a compact subset of `(0,1)^d` it is bounded away from
the boundary (`tsupport ψ ⊆ [δ, 1-δ]^d` for some `δ ∈ (0, 1/2]`), so the
lattice translates of the support are pairwise separated and the sum collapses
to (at most) a single nonzero term near every point. This makes `cubeBumpPer ψ`
smooth and periodic, and on the half-open unit cube it equals `ψ` exactly.

-- Adapted from `StationaryMFG.Periodic.BumpKernelPeriodization` (the
-- `bumpKernelPer` construction), re-derived for a general cube-supported bump.
-/

section CubeBumpPeriodization

open Function Filter
open scoped Topology

variable {d : ℕ}

/-- Coordinatewise "label" lattice point selecting the unique translate of a
support centred near `1/2`: `lblVec s i := round (s i - 1/2)`. -/
noncomputable def lblVec (s : Fin d → ℝ) : Fin d → ℤ :=
  fun i => round (s i - 1 / 2)

/-- The d-dim integer-lattice periodisation of a bump `ψ`. -/
noncomputable def cubeBumpPer (ψ : (Fin d → ℝ) → ℝ) : (Fin d → ℝ) → ℝ :=
  fun s => ∑' k : Fin d → ℤ, ψ (s - fun i => (k i : ℝ))

lemma cubeBumpPer_apply (ψ : (Fin d → ℝ) → ℝ) (s : Fin d → ℝ) :
    cubeBumpPer ψ s = ∑' k : Fin d → ℤ, ψ (s - fun i => (k i : ℝ)) := rfl

/-- Separation: a compact support inside the open unit cube `(0,1)^d` is
bounded away from the boundary by some `δ ∈ (0, 1/2]`. -/
lemma exists_delta_of_tsupport_subset_openCube
    {ψ : (Fin d → ℝ) → ℝ} (hψ_supp : HasCompactSupport ψ)
    (hψ_sub : tsupport ψ ⊆ Set.pi Set.univ (fun _ : Fin d => Set.Ioo (0 : ℝ) 1)) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧
      ∀ y ∈ tsupport ψ, ∀ i, δ ≤ y i ∧ y i ≤ 1 - δ := by
  classical
  rcases isEmpty_or_nonempty (Fin d) with hd | hd
  · -- `d = 0`: the margin condition is vacuous over `i : Fin d`.
    exact ⟨1 / 2, by norm_num, le_refl _, fun y _ i => (IsEmpty.false i).elim⟩
  by_cases hempty : (tsupport ψ).Nonempty
  · -- Continuous margin function `g y = ⨅ i, min (y i) (1 - y i)`, attains a
    -- positive minimum on the compact support.
    set g : (Fin d → ℝ) → ℝ :=
      fun y => Finset.univ.inf' Finset.univ_nonempty (fun i => min (y i) (1 - y i)) with hg_def
    -- Positivity of `g` on the support.
    have hg_pos : ∀ y ∈ tsupport ψ, 0 < g y := by
      intro y hy
      have hyOpen := hψ_sub hy
      rw [Set.mem_pi] at hyOpen
      rw [hg_def, Finset.lt_inf'_iff]
      intro i _
      have := hyOpen i (Set.mem_univ i)
      rw [Set.mem_Ioo] at this
      exact lt_min this.1 (by linarith [this.2])
    -- Continuity of `g`.
    have hg_cont : Continuous g := by
      rw [hg_def]
      refine Continuous.finset_inf'_apply _ (fun i _ => ?_)
      exact (continuous_apply i).min (continuous_const.sub (continuous_apply i))
    -- The infimum is attained on the compact support and positive.
    have hcompact : IsCompact (tsupport ψ) := hψ_supp
    obtain ⟨y₀, hy₀_mem, hy₀_min⟩ :=
      hcompact.exists_isMinOn hempty hg_cont.continuousOn
    set δ : ℝ := min (g y₀) (1 / 2) with hδ_def
    refine ⟨δ, ?_, ?_, ?_⟩
    · exact lt_min (hg_pos y₀ hy₀_mem) (by norm_num)
    · exact min_le_right _ _
    · intro y hy i
      have hgy : g y₀ ≤ g y := hy₀_min hy
      have hδle : δ ≤ g y := le_trans (min_le_left _ _) hgy
      have hcoord : g y ≤ min (y i) (1 - y i) := by
        rw [hg_def]; exact Finset.inf'_le _ (Finset.mem_univ i)
      have h1 : δ ≤ y i := le_trans hδle (le_trans hcoord (min_le_left _ _))
      have h2 : δ ≤ 1 - y i := le_trans hδle (le_trans hcoord (min_le_right _ _))
      exact ⟨h1, by linarith⟩
  · -- Empty support: any `δ` works (vacuously).
    exact ⟨1 / 2, by norm_num, le_refl _, fun y hy => absurd ⟨y, hy⟩ hempty⟩

/-- Pointwise: a translate `ψ (s - k_ℝ)` is zero unless `k = lblVec s`,
provided `tsupport ψ ⊆ [δ, 1-δ]^d` with `δ ≤ 1/2`. The triangle argument is
the same as for `bumpKernelPer`, recentred at `1/2`. -/
lemma cubeBump_translate_eq_zero_of_ne_lblVec
    {ψ : (Fin d → ℝ) → ℝ} {δ : ℝ} (hδ_pos : 0 < δ) (_hδ_le : δ ≤ 1 / 2)
    (hψ_margin : ∀ y ∈ tsupport ψ, ∀ i, δ ≤ y i ∧ y i ≤ 1 - δ)
    (s : Fin d → ℝ) {k : Fin d → ℤ} (hk : k ≠ lblVec s) :
    ψ (s - fun i => (k i : ℝ)) = 0 := by
  -- Find a coordinate where `k` differs from `lblVec s`.
  have hexists : ∃ i, k i ≠ lblVec s i := by
    by_contra hall
    exact hk (funext fun i => not_not.mp (fun h => hall ⟨i, h⟩))
  obtain ⟨i, hi⟩ := hexists
  -- Show the i-th coordinate of `s - k_ℝ` lies outside `[δ, 1-δ]`, so the point
  -- is not in `tsupport ψ`, so `ψ = 0` there.
  refine image_eq_zero_of_notMem_tsupport ?_
  intro hmem
  have hmargin := hψ_margin _ hmem i
  -- Coordinate value.
  have hcoord : (s - fun j => (k j : ℝ)) i = s i - (k i : ℝ) := by
    simp [Pi.sub_apply]
  rw [hcoord] at hmargin
  -- So `δ ≤ s i - k i ≤ 1 - δ`, i.e. `|s i - 1/2 - k i| ≤ 1/2 - δ`.
  have hbound : |(s i - 1 / 2) - (k i : ℝ)| ≤ 1 / 2 - δ := by
    rw [abs_le]; constructor <;> [linarith [hmargin.2]; linarith [hmargin.1]]
  -- But `lblVec s i = round (s i - 1/2)` is the nearest integer, and `k ≠ it`,
  -- so `|s i - 1/2 - k i| ≥ 1 - 1/2 = 1/2 > 1/2 - δ`. Contradiction.
  have hround : |(s i - 1 / 2) - (round (s i - 1 / 2) : ℝ)| ≤ 1 / 2 :=
    abs_sub_round (s i - 1 / 2)
  have hne_int : (round (s i - 1 / 2) - k i : ℤ) ≠ 0 := by
    intro h
    exact hi (by rw [lblVec]; exact (sub_eq_zero.mp h).symm)
  have h_one_le : (1 : ℤ) ≤ |round (s i - 1 / 2) - k i| := Int.one_le_abs hne_int
  have h_one_le_real :
      (1 : ℝ) ≤ |((round (s i - 1 / 2) : ℝ)) - (k i : ℝ)| := by
    have hcast : ((round (s i - 1 / 2) - k i : ℤ) : ℝ)
        = (round (s i - 1 / 2) : ℝ) - (k i : ℝ) := by push_cast; ring
    have : (1 : ℝ) ≤ ((|round (s i - 1 / 2) - k i| : ℤ) : ℝ) := by exact_mod_cast h_one_le
    rwa [Int.cast_abs, hcast] at this
  -- Triangle: 1 ≤ |round - k| ≤ |round - (s-1/2)| + |(s-1/2) - k| ≤ 1/2 + (1/2 - δ)
  have htri :
      |((round (s i - 1 / 2) : ℝ)) - (k i : ℝ)| ≤
        |(s i - 1 / 2) - (round (s i - 1 / 2) : ℝ)| + |(s i - 1 / 2) - (k i : ℝ)| := by
    calc |((round (s i - 1 / 2) : ℝ)) - (k i : ℝ)|
        = |((round (s i - 1 / 2) : ℝ) - (s i - 1 / 2)) + ((s i - 1 / 2) - (k i : ℝ))| := by
          ring_nf
      _ ≤ |((round (s i - 1 / 2) : ℝ) - (s i - 1 / 2))| + |(s i - 1 / 2) - (k i : ℝ)| :=
          abs_add_le _ _
      _ = |(s i - 1 / 2) - (round (s i - 1 / 2) : ℝ)| + |(s i - 1 / 2) - (k i : ℝ)| := by
          rw [abs_sub_comm]
  linarith

/-- Single-term collapse of the periodisation. -/
lemma cubeBumpPer_eq_single
    {ψ : (Fin d → ℝ) → ℝ} {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1 / 2)
    (hψ_margin : ∀ y ∈ tsupport ψ, ∀ i, δ ≤ y i ∧ y i ≤ 1 - δ)
    (s : Fin d → ℝ) :
    cubeBumpPer ψ s = ψ (s - fun i => ((lblVec s) i : ℝ)) := by
  rw [cubeBumpPer_apply]
  refine tsum_eq_single (lblVec s) (fun k hk => ?_)
  exact cubeBump_translate_eq_zero_of_ne_lblVec hδ_pos hδ_le hψ_margin s hk

/-- On the half-open unit cube, the periodisation equals `ψ` (only the `k = 0`
term survives because `0 ≤ s i < 1`). -/
lemma cubeBumpPer_eq_on_cube
    {ψ : (Fin d → ℝ) → ℝ} {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1 / 2)
    (hψ_margin : ∀ y ∈ tsupport ψ, ∀ i, δ ≤ y i ∧ y i ≤ 1 - δ)
    {s : Fin d → ℝ} (hs : s ∈ UnitCube d) :
    cubeBumpPer ψ s = ψ s := by
  rw [cubeBumpPer_eq_single hδ_pos hδ_le hψ_margin s]
  -- On the cube, `lblVec s = 0`: for `0 ≤ s i < 1`, `round (s i - 1/2) = 0`.
  have hlbl : lblVec s = 0 := by
    funext i
    rw [mem_unitCube_iff] at hs
    obtain ⟨h0, h1⟩ := hs i
    rw [lblVec]
    have : |(s i - 1 / 2) - (0 : ℝ)| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
    -- round of something within 1/2 of 0 is 0.
    have hrnd : round (s i - 1 / 2) = 0 := by
      rw [round_eq]
      have : ⌊s i - 1 / 2 + 1 / 2⌋ = ⌊s i⌋ := by ring_nf
      rw [this, Int.floor_eq_zero_iff]
      exact ⟨h0, h1⟩
    simpa using hrnd
  rw [hlbl]
  have : (fun i => (((0 : Fin d → ℤ) i : ℝ))) = (0 : Fin d → ℝ) := by funext i; simp
  rw [this, sub_zero]

/-! ### The single-branch and local agreement -/

/-- The single-translate branch of `cubeBumpPer` at base point `s₀`. -/
noncomputable def cubeBumpSingle (ψ : (Fin d → ℝ) → ℝ) (s₀ : Fin d → ℝ) :
    (Fin d → ℝ) → ℝ :=
  fun s => ψ (s - fun i => ((lblVec s₀) i : ℝ))

lemma cubeBumpSingle_contDiff {ψ : (Fin d → ℝ) → ℝ}
    (hψ_smooth : ContDiff ℝ ((⊤ : ℕ∞) : ℕ∞ω) ψ) (s₀ : Fin d → ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : ℕ∞ω) (cubeBumpSingle ψ s₀) := by
  unfold cubeBumpSingle
  exact hψ_smooth.comp (contDiff_id.sub contDiff_const)

/-- Locally near `s₀`, the periodisation equals the single-translate branch
indexed by `lblVec s₀`. -/
lemma cubeBumpPer_eventuallyEq_single
    {ψ : (Fin d → ℝ) → ℝ} {δ : ℝ} (hδ_pos : 0 < δ) (_hδ_le : δ ≤ 1 / 2)
    (hψ_margin : ∀ y ∈ tsupport ψ, ∀ i, δ ≤ y i ∧ y i ≤ 1 - δ)
    (s₀ : Fin d → ℝ) :
    cubeBumpPer ψ =ᶠ[𝓝 s₀] cubeBumpSingle ψ s₀ := by
  -- On a small ball of radius `δ/2` (in each coordinate) around `s₀`,
  -- `lblVec s = lblVec s₀`, so the collapse picks the same term.
  set η : ℝ := δ / 2 with hη_def
  have hηpos : 0 < η := by rw [hη_def]; linarith
  have hball_open : IsOpen ({s : Fin d → ℝ | ∀ i, |s i - s₀ i| < η}) := by
    have hset : ({s : Fin d → ℝ | ∀ i, |s i - s₀ i| < η})
        = ⋂ i : Fin d, {s : Fin d → ℝ | |s i - s₀ i| < η} := by
      ext s; simp [Set.mem_iInter]
    rw [hset]
    refine isOpen_iInter_of_finite (fun i => ?_)
    have hcont : Continuous (fun s : Fin d → ℝ => s i - s₀ i) :=
      (continuous_apply i).sub continuous_const
    exact isOpen_lt (continuous_abs.comp hcont) continuous_const
  have hmem : s₀ ∈ {s : Fin d → ℝ | ∀ i, |s i - s₀ i| < η} := by
    intro i; simpa using hηpos
  refine eventuallyEq_of_mem (hball_open.mem_nhds hmem) (fun s hs => ?_)
  -- Goal: `cubeBumpPer ψ s = cubeBumpSingle ψ s₀ s = ψ (s - (lblVec s₀)_ℝ)`.
  change cubeBumpPer ψ s = ψ (s - fun i => ((lblVec s₀) i : ℝ))
  rw [cubeBumpPer_apply]
  refine tsum_eq_single (lblVec s₀) (fun k hk => ?_)
  -- For `k ≠ lblVec s₀`, the term vanishes: same coordinate triangle argument,
  -- using that `s` is close to `s₀`.
  have hexists : ∃ i, k i ≠ lblVec s₀ i := by
    by_contra hall
    exact hk (funext fun i => not_not.mp (fun h => hall ⟨i, h⟩))
  obtain ⟨i, hi⟩ := hexists
  refine image_eq_zero_of_notMem_tsupport ?_
  intro hmemSupp
  have hmargin := hψ_margin _ hmemSupp i
  have hcoord : (s - fun j => (k j : ℝ)) i = s i - (k i : ℝ) := by simp [Pi.sub_apply]
  rw [hcoord] at hmargin
  have hbound : |(s i - 1 / 2) - (k i : ℝ)| ≤ 1 / 2 - δ := by
    rw [abs_le]; constructor <;> [linarith [hmargin.2]; linarith [hmargin.1]]
  -- `lblVec s₀ i = round (s₀ i - 1/2)`, integer, ≠ k i.
  have hne_int : (round (s₀ i - 1 / 2) - k i : ℤ) ≠ 0 := by
    intro h
    exact hi (by rw [lblVec]; exact (sub_eq_zero.mp h).symm)
  have h_one_le : (1 : ℤ) ≤ |round (s₀ i - 1 / 2) - k i| := Int.one_le_abs hne_int
  have h_one_le_real :
      (1 : ℝ) ≤ |((round (s₀ i - 1 / 2) : ℝ)) - (k i : ℝ)| := by
    have hcast : ((round (s₀ i - 1 / 2) - k i : ℤ) : ℝ)
        = (round (s₀ i - 1 / 2) : ℝ) - (k i : ℝ) := by push_cast; ring
    have : (1 : ℝ) ≤ ((|round (s₀ i - 1 / 2) - k i| : ℤ) : ℝ) := by exact_mod_cast h_one_le
    rwa [Int.cast_abs, hcast] at this
  have hround : |(s₀ i - 1 / 2) - (round (s₀ i - 1 / 2) : ℝ)| ≤ 1 / 2 :=
    abs_sub_round (s₀ i - 1 / 2)
  have hclose : |s i - s₀ i| < η := hs i
  -- Triangle: 1 ≤ |round(s₀-1/2) - k|
  --   ≤ |round(s₀-1/2) - (s₀-1/2)| + |(s₀ - 1/2) - (s - 1/2)| + |(s-1/2) - k|
  --   ≤ 1/2 + |s₀ i - s i| + (1/2 - δ).
  have hmid : |(s₀ i - 1 / 2) - (s i - 1 / 2)| = |s i - s₀ i| := by
    rw [show (s₀ i - 1 / 2) - (s i - 1 / 2) = -(s i - s₀ i) by ring, abs_neg]
  have htri :
      |((round (s₀ i - 1 / 2) : ℝ)) - (k i : ℝ)| ≤
        |(s₀ i - 1 / 2) - (round (s₀ i - 1 / 2) : ℝ)|
          + |(s₀ i - 1 / 2) - (s i - 1 / 2)|
          + |(s i - 1 / 2) - (k i : ℝ)| := by
    calc |((round (s₀ i - 1 / 2) : ℝ)) - (k i : ℝ)|
        = |((round (s₀ i - 1 / 2) : ℝ) - (s₀ i - 1 / 2))
            + ((s₀ i - 1 / 2) - (s i - 1 / 2))
            + ((s i - 1 / 2) - (k i : ℝ))| := by ring_nf
      _ ≤ |((round (s₀ i - 1 / 2) : ℝ) - (s₀ i - 1 / 2))
            + ((s₀ i - 1 / 2) - (s i - 1 / 2))|
            + |(s i - 1 / 2) - (k i : ℝ)| := abs_add_le _ _
      _ ≤ |((round (s₀ i - 1 / 2) : ℝ) - (s₀ i - 1 / 2))|
            + |((s₀ i - 1 / 2) - (s i - 1 / 2))|
            + |(s i - 1 / 2) - (k i : ℝ)| := by
            have := abs_add_le ((round (s₀ i - 1 / 2) : ℝ) - (s₀ i - 1 / 2))
              ((s₀ i - 1 / 2) - (s i - 1 / 2))
            linarith
      _ = |(s₀ i - 1 / 2) - (round (s₀ i - 1 / 2) : ℝ)|
            + |(s₀ i - 1 / 2) - (s i - 1 / 2)|
            + |(s i - 1 / 2) - (k i : ℝ)| := by
            rw [abs_sub_comm ((round (s₀ i - 1 / 2) : ℝ)) (s₀ i - 1 / 2)]
  rw [hmid] at htri
  -- combine: 1 ≤ 1/2 + η + (1/2 - δ) = 1 + η - δ < 1 since η = δ/2 < δ.
  have : (1 : ℝ) < 1 + η - δ := by linarith
  linarith

/-- Smoothness of the periodisation. -/
lemma cubeBumpPer_contDiff
    {ψ : (Fin d → ℝ) → ℝ} (hψ_smooth : ContDiff ℝ ((⊤ : ℕ∞) : ℕ∞ω) ψ)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1 / 2)
    (hψ_margin : ∀ y ∈ tsupport ψ, ∀ i, δ ≤ y i ∧ y i ≤ 1 - δ) :
    ContDiff ℝ ((⊤ : ℕ∞) : ℕ∞ω) (cubeBumpPer ψ) := by
  rw [contDiff_iff_contDiffAt]
  intro s₀
  exact (cubeBumpSingle_contDiff hψ_smooth s₀).contDiffAt.congr_of_eventuallyEq
    (cubeBumpPer_eventuallyEq_single hδ_pos hδ_le hψ_margin s₀)

/-- Periodicity of the periodisation (independent of the separation `δ`,
provided the sum converges termwise — which it does, being a single term
near every point). We only need the formal reindex `k ↦ k - n`. -/
lemma cubeBumpPer_periodic (ψ : (Fin d → ℝ) → ℝ) :
    IsPeriodic (cubeBumpPer ψ) := by
  intro n s
  rw [cubeBumpPer_apply, cubeBumpPer_apply]
  let e : (Fin d → ℤ) ≃ (Fin d → ℤ) :=
    { toFun := fun k => k - n
      invFun := fun k => k + n
      left_inv := fun k => by ext i; simp
      right_inv := fun k => by ext i; simp }
  have heq := e.tsum_eq
    (f := fun k : Fin d → ℤ => ψ (s - fun i => (k i : ℝ)))
  have hkey : ∀ k : Fin d → ℤ,
      ψ ((s + fun i => (n i : ℝ)) - fun i => (k i : ℝ))
        = ψ (s - fun i => ((e k) i : ℝ)) := by
    intro k
    congr 1
    funext i
    have hek : (e k) i = k i - n i := rfl
    change s i + (n i : ℝ) - (k i : ℝ) = s i - ((e k) i : ℝ)
    rw [hek]; push_cast; ring
  calc (∑' k : Fin d → ℤ, ψ ((s + fun i => (n i : ℝ)) - fun i => (k i : ℝ)))
      = ∑' k : Fin d → ℤ, ψ (s - fun i => ((e k) i : ℝ)) := tsum_congr hkey
    _ = ∑' k : Fin d → ℤ, ψ (s - fun i => ((k i) : ℝ)) := heq

/-- The Frechet derivative of `cubeBumpPer ψ` at `s₀` agrees with that of the
single-translate branch. -/
lemma cubeBumpPer_fderiv_eq
    {ψ : (Fin d → ℝ) → ℝ} {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1 / 2)
    (hψ_margin : ∀ y ∈ tsupport ψ, ∀ i, δ ≤ y i ∧ y i ≤ 1 - δ)
    (s₀ : Fin d → ℝ) :
    fderiv ℝ (cubeBumpPer ψ) s₀ = fderiv ℝ (cubeBumpSingle ψ s₀) s₀ :=
  (cubeBumpPer_eventuallyEq_single hδ_pos hδ_le hψ_margin s₀).fderiv_eq

/-- On the cube the partial derivative of the periodisation equals that of `ψ`.
For `s₀ ∈ UnitCube d`, `lblVec s₀ = 0`, so the single branch is literally `ψ`. -/
lemma cubeBumpPer_partialDeriv_eq_on_cube
    {ψ : (Fin d → ℝ) → ℝ} {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1 / 2)
    (hψ_margin : ∀ y ∈ tsupport ψ, ∀ i, δ ≤ y i ∧ y i ≤ 1 - δ)
    {s₀ : Fin d → ℝ} (hs₀ : s₀ ∈ UnitCube d) (i : Fin d) :
    fderiv ℝ (cubeBumpPer ψ) s₀ (Pi.basisFun ℝ (Fin d) i)
      = fderiv ℝ ψ s₀ (Pi.basisFun ℝ (Fin d) i) := by
  rw [cubeBumpPer_fderiv_eq hδ_pos hδ_le hψ_margin]
  -- The single branch is `s ↦ ψ (s - (lblVec s₀)_ℝ)`; on cube `lblVec s₀ = 0`.
  have hlbl : lblVec s₀ = 0 := by
    funext j
    rw [mem_unitCube_iff] at hs₀
    obtain ⟨h0, h1⟩ := hs₀ j
    rw [lblVec]
    have hrnd : round (s₀ j - 1 / 2) = 0 := by
      rw [round_eq]
      have hfe : ⌊s₀ j - 1 / 2 + 1 / 2⌋ = ⌊s₀ j⌋ := by ring_nf
      rw [hfe, Int.floor_eq_zero_iff]
      exact ⟨h0, h1⟩
    simpa using hrnd
  have hbranch : cubeBumpSingle ψ s₀ = ψ := by
    funext s
    rw [cubeBumpSingle, hlbl]
    have : (fun i => (((0 : Fin d → ℤ) i : ℝ))) = (0 : Fin d → ℝ) := by funext i; simp
    rw [this, sub_zero]
  rw [hbranch]

/-- Package the cube-supported bump's periodisation as a `SmoothPeriodic d`. -/
noncomputable def SmoothPeriodic.ofCubeSupportedBump
    {ψ : (Fin d → ℝ) → ℝ}
    (hψ_smooth : ContDiff ℝ ((⊤ : ℕ∞) : ℕ∞ω) ψ) (hψ_supp : HasCompactSupport ψ)
    (hψ_sub : tsupport ψ ⊆ Set.pi Set.univ (fun _ : Fin d => Set.Ioo (0 : ℝ) 1)) :
    SmoothPeriodic d :=
  let δdata := exists_delta_of_tsupport_subset_openCube hψ_supp hψ_sub
  { toFun := cubeBumpPer ψ
    smooth := cubeBumpPer_contDiff hψ_smooth δdata.choose_spec.1
      δdata.choose_spec.2.1 δdata.choose_spec.2.2
    periodic := cubeBumpPer_periodic ψ }

@[simp] lemma SmoothPeriodic.coe_ofCubeSupportedBump
    {ψ : (Fin d → ℝ) → ℝ}
    (hψ_smooth : ContDiff ℝ ((⊤ : ℕ∞) : ℕ∞ω) ψ) (hψ_supp : HasCompactSupport ψ)
    (hψ_sub : tsupport ψ ⊆ Set.pi Set.univ (fun _ : Fin d => Set.Ioo (0 : ℝ) 1)) :
    ((SmoothPeriodic.ofCubeSupportedBump hψ_smooth hψ_supp hψ_sub
        : SmoothPeriodic d) : (Fin d → ℝ) → ℝ) = cubeBumpPer ψ := rfl

end CubeBumpPeriodization

namespace HasWeakDerivPer

/-- **A smooth periodic function is its own weak derivative carrier.** For
`φ : SmoothPeriodic d`, the classical partial derivative `∂_i φ` is the weak
partial derivative of `φ` in direction `i`. -/
theorem of_contDiff (i : Fin d) (φ : SmoothPeriodic d) :
    HasWeakDerivPer i (φ : (Fin d → ℝ) → ℝ)
      ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) : (Fin d → ℝ) → ℝ) := by
  refine ⟨?_, ?_⟩
  · -- MemLpPer 1 (∂_i φ): use that ∂_i φ is continuous and the cube has
    -- finite measure.
    have hfinite :
        IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
      ⟨by
        rw [Measure.restrict_apply MeasurableSet.univ]
        simp⟩
    have hcont :
        Continuous ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) :=
      (SmoothPeriodic.partialDeriv i φ).smooth.continuous
    -- A continuous function on a compact superset of the unit cube is
    -- bounded; combined with finite measure ⇒ integrable ⇒ MemLp 1.
    have hloc : LocallyIntegrable
        ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) := hcont.locallyIntegrable
    -- The closed cube is compact:
    have hcompactCube : IsCompact (pi univ (fun _ : Fin d => Icc (0 : ℝ) 1)) :=
      isCompact_univ_pi (fun _ => isCompact_Icc)
    have hsub : UnitCube d ⊆ pi univ (fun _ : Fin d => Icc (0 : ℝ) 1) := by
      intro x hx j _
      exact Ico_subset_Icc_self (hx j (mem_univ _))
    have hIntCompact :
        IntegrableOn
          ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ)
          (pi univ (fun _ : Fin d => Icc (0 : ℝ) 1)) :=
      hloc.integrableOn_isCompact hcompactCube
    have hInt :
        IntegrableOn
          ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ)
          (UnitCube d) :=
      hIntCompact.mono_set hsub
    -- Convert `IntegrableOn ... (UnitCube d)` to `MemLpPer 1`.
    exact MemLp.toMemLpPer ((memLp_one_iff_integrable).2 hInt)
  · intro ψ
    -- The proof: by Leibniz, `∂_i (φ ψ) = (∂_i φ) ψ + φ (∂_i ψ)`. Integrate
    -- both sides over the cube. The LHS is `∫ ∂_i (φ ψ) = 0` by
    -- `integral_partialDeriv_eq_zero` applied to `F = φ ψ`. So
    -- `∫ (∂_i φ) ψ + ∫ φ (∂_i ψ) = 0`, i.e. the desired identity.
    set φf : (Fin d → ℝ) → ℝ := (φ : (Fin d → ℝ) → ℝ) with hφf
    set ψf : (Fin d → ℝ) → ℝ := (ψ : (Fin d → ℝ) → ℝ) with hψf
    set Diφ : (Fin d → ℝ) → ℝ :=
      ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
          (Fin d → ℝ) → ℝ) with hDiφ
    set Diψ : (Fin d → ℝ) → ℝ :=
      ((SmoothPeriodic.partialDeriv i ψ : SmoothPeriodic d) :
          (Fin d → ℝ) → ℝ) with hDiψ
    -- Leibniz: pointwise, `fderiv ℝ (φψ) x e_i = ψ x * ∂_i φ x + φ x * ∂_i ψ x`.
    have hLeibniz : ∀ x,
        fderiv ℝ (fun y => φf y * ψf y) x (Pi.basisFun ℝ (Fin d) i) =
          Diφ x * ψf x + φf x * Diψ x := by
      intro x
      have hφ_diff : DifferentiableAt ℝ φf x :=
        (φ.smooth.differentiable (by decide : ((⊤ : ℕ∞) : ℕ∞ω) ≠ 0)).differentiableAt
      have hψ_diff : DifferentiableAt ℝ ψf x :=
        (ψ.smooth.differentiable (by decide : ((⊤ : ℕ∞) : ℕ∞ω) ≠ 0)).differentiableAt
      rw [fderiv_fun_mul hφ_diff hψ_diff]
      -- `Diφ x = fderiv ℝ φf x e_i`, `Diψ x = fderiv ℝ ψf x e_i`.
      have hDiφ_eq : Diφ x = fderiv ℝ φf x (Pi.basisFun ℝ (Fin d) i) := rfl
      have hDiψ_eq : Diψ x = fderiv ℝ ψf x (Pi.basisFun ℝ (Fin d) i) := rfl
      rw [hDiφ_eq, hDiψ_eq]
      -- Now apply the linear-map combination at `e_i`, then commute additions.
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        smul_eq_mul]
      ring
    -- Smoothness and periodicity of the product `φ * ψ`.
    have hprod_smooth : ContDiff ℝ ((⊤ : ℕ∞) : ℕ∞ω) (fun y => φf y * ψf y) :=
      φ.smooth.mul ψ.smooth
    have hprod_per : IsPeriodic (fun y => φf y * ψf y) := by
      intro k x
      simp [hφf, hψf, φ.periodic k x, ψ.periodic k x]
    -- Integral of the LHS: `∫ ∂_i (φ ψ) = 0`.
    have hZero :
        periodicIntegral
            (fun x => fderiv ℝ (fun y => φf y * ψf y) x
              (Pi.basisFun ℝ (Fin d) i)) = 0 :=
      integral_partialDeriv_eq_zero _ hprod_smooth hprod_per i
    -- Pointwise rewrite: split the integrand using Leibniz.
    have hSplit :
        (fun x => fderiv ℝ (fun y => φf y * ψf y) x (Pi.basisFun ℝ (Fin d) i)) =
          (fun x => Diφ x * ψf x + φf x * Diψ x) := by
      funext x; exact hLeibniz x
    rw [hSplit] at hZero
    -- Integrability of each piece (continuous functions on a finite-measure cube).
    have hCubeFin : volume (UnitCube d) ≠ ⊤ := by simp
    have hAB : IntegrableOn (fun x => Diφ x * ψf x) (UnitCube d) := by
      have hcont :
          Continuous (fun x : Fin d → ℝ => Diφ x * ψf x) :=
        (((SmoothPeriodic.partialDeriv i φ).smooth.continuous).mul ψ.smooth.continuous)
      exact (hcont.locallyIntegrable.integrableOn_isCompact
        (isCompact_univ_pi (fun _ => isCompact_Icc))).mono_set
        (fun x hx j _ => Ico_subset_Icc_self (hx j (mem_univ _)))
    have hCD : IntegrableOn (fun x => φf x * Diψ x) (UnitCube d) := by
      have hcont :
          Continuous (fun x : Fin d → ℝ => φf x * Diψ x) :=
        (φ.smooth.continuous.mul ((SmoothPeriodic.partialDeriv i ψ).smooth.continuous))
      exact (hcont.locallyIntegrable.integrableOn_isCompact
        (isCompact_univ_pi (fun _ => isCompact_Icc))).mono_set
        (fun x hx j _ => Ico_subset_Icc_self (hx j (mem_univ _)))
    -- Linearity of the periodic integral.
    have hAdd :
        periodicIntegral (fun x => Diφ x * ψf x + φf x * Diψ x) =
          periodicIntegral (fun x => Diφ x * ψf x) +
            periodicIntegral (fun x => φf x * Diψ x) := by
      unfold periodicIntegral
      exact integral_add hAB hCD
    rw [hAdd] at hZero
    -- Move to the desired identity.
    linarith [hZero]

/-- **a.e. uniqueness of the periodic weak derivative.** If both `g` and `g'`
are weak partial derivatives of the same `f` in direction `i`, they agree a.e.
on the unit cube.

The argument (route 2): subtracting the two IBP identities and feeding the
periodisation `SmoothPeriodic.ofCubeSupportedBump ψ` of an arbitrary
cube-interior-supported smooth bump `ψ` shows `∫_cube ψ · (g - g') = 0` for all
such `ψ`. Mathlib's `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` on the
open cube `(0,1)^d` then gives `g = g'` a.e. on the open cube; the boundary is
null, so the equality upgrades to a.e. on the half-open cube. -/
theorem unique {i : Fin d} {f g g' : (Fin d → ℝ) → ℝ}
    (h : HasWeakDerivPer (d := d) i f g) (h' : HasWeakDerivPer (d := d) i f g') :
    g =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] g' := by
  classical
  set μ : Measure (Fin d → ℝ) := volume.restrict (UnitCube d) with hμ_def
  -- The open cube `U = (0,1)^d`.
  set U : Set (Fin d → ℝ) := Set.pi Set.univ (fun _ : Fin d => Set.Ioo (0 : ℝ) 1) with hU_def
  have hU_open : IsOpen U := by
    rw [hU_def]
    exact isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
  have hU_sub_cube : U ⊆ UnitCube d := by
    intro x hx j _
    have := hx j (Set.mem_univ j)
    rw [Set.mem_Ioo] at this
    exact ⟨le_of_lt this.1, this.2⟩
  -- `g - g'` is integrable on the cube, hence locally integrable on `U`.
  have hg_int : IntegrableOn g (UnitCube d) := h.integrableOn
  have hg'_int : IntegrableOn g' (UnitCube d) := h'.integrableOn
  have hdiff_int : Integrable (fun x => g x - g' x) μ := by
    rw [hμ_def]; exact hg_int.sub hg'_int
  have hloc : LocallyIntegrableOn (fun x => g x - g' x) U μ := by
    have : LocallyIntegrable (fun x => g x - g' x) μ := hdiff_int.locallyIntegrable
    exact this.locallyIntegrableOn U
  -- The vanishing-integral hypothesis for all cube-interior bumps.
  have hvanish : ∀ (ψ : (Fin d → ℝ) → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → ∫ x, ψ x • (fun y => g y - g' y) x ∂μ = 0 := by
    intro ψ hψ_smooth hψ_supp hψ_sub
    -- Package the periodisation as a periodic test function.
    have hψ_smooth' : ContDiff ℝ ((⊤ : ℕ∞) : ℕ∞ω) ψ := hψ_smooth
    set Ψ : SmoothPeriodic d :=
      SmoothPeriodic.ofCubeSupportedBump hψ_smooth' hψ_supp (by rw [← hU_def]; exact hψ_sub)
      with hΨ_def
    obtain ⟨δ, hδ_pos, hδ_le, hδ_margin⟩ :=
      exists_delta_of_tsupport_subset_openCube hψ_supp (by rw [← hU_def]; exact hψ_sub)
    -- On the cube, `Ψ = ψ` and `∂_i Ψ = ∂_i ψ`.
    have hΨ_on_cube : ∀ x ∈ UnitCube d, (Ψ : (Fin d → ℝ) → ℝ) x = ψ x := by
      intro x hx
      rw [hΨ_def, SmoothPeriodic.coe_ofCubeSupportedBump]
      exact cubeBumpPer_eq_on_cube hδ_pos hδ_le hδ_margin hx
    have hdΨ_on_cube : ∀ x ∈ UnitCube d,
        ((SmoothPeriodic.partialDeriv i Ψ : SmoothPeriodic d) : (Fin d → ℝ) → ℝ) x
          = fderiv ℝ ψ x (Pi.basisFun ℝ (Fin d) i) := by
      intro x hx
      rw [SmoothPeriodic.coe_partialDeriv]
      rw [hΨ_def, SmoothPeriodic.coe_ofCubeSupportedBump]
      exact cubeBumpPer_partialDeriv_eq_on_cube hδ_pos hδ_le hδ_margin hx i
    -- The two IBP identities for `g` and `g'` against `Ψ`.
    have hIBP_g := h.integral_eq Ψ
    have hIBP_g' := h'.integral_eq Ψ
    -- Rewrite each `periodicIntegral` on the cube using `Ψ = ψ`, `∂Ψ = ∂ψ`.
    have hLg : periodicIntegral (fun x => g x * (Ψ : (Fin d → ℝ) → ℝ) x)
        = periodicIntegral (fun x => g x * ψ x) := by
      unfold periodicIntegral
      refine setIntegral_congr_fun measurableSet_unitCube (fun x hx => ?_)
      rw [hΨ_on_cube x hx]
    have hLg' : periodicIntegral (fun x => g' x * (Ψ : (Fin d → ℝ) → ℝ) x)
        = periodicIntegral (fun x => g' x * ψ x) := by
      unfold periodicIntegral
      refine setIntegral_congr_fun measurableSet_unitCube (fun x hx => ?_)
      rw [hΨ_on_cube x hx]
    have hRf : periodicIntegral (fun x => f x *
          ((SmoothPeriodic.partialDeriv i Ψ : SmoothPeriodic d) : (Fin d → ℝ) → ℝ) x)
        = periodicIntegral (fun x => f x * fderiv ℝ ψ x (Pi.basisFun ℝ (Fin d) i)) := by
      unfold periodicIntegral
      refine setIntegral_congr_fun measurableSet_unitCube (fun x hx => ?_)
      rw [hdΨ_on_cube x hx]
    rw [hLg, hRf] at hIBP_g
    rw [hLg', hRf] at hIBP_g'
    -- So `∫_cube g·ψ = ∫_cube g'·ψ`, i.e. `∫_cube (g-g')·ψ = 0`.
    have hgg' : periodicIntegral (fun x => g x * ψ x)
        = periodicIntegral (fun x => g' x * ψ x) := by
      rw [hIBP_g, hIBP_g']
    -- Translate to the `μ`-integral of `ψ • (g - g')`.
    have hψ_cont : Continuous ψ := hψ_smooth.continuous
    -- Boundedness of `ψ` on a compact superset of the cube ⇒ a.e. bound.
    have hcompactCube : IsCompact (Set.pi Set.univ (fun _ : Fin d => Set.Icc (0 : ℝ) 1)) :=
      isCompact_univ_pi (fun _ => isCompact_Icc)
    have hsub : UnitCube d ⊆ Set.pi Set.univ (fun _ : Fin d => Set.Icc (0 : ℝ) 1) := by
      intro x hx j _
      exact Set.Ico_subset_Icc_self (hx j (Set.mem_univ _))
    obtain ⟨Cψ, hCψ⟩ := hcompactCube.bddAbove_image (f := fun x => ‖ψ x‖)
      hψ_cont.norm.continuousOn
    have hbnd_ae : ∀ᵐ x ∂(volume.restrict (UnitCube d)), ‖ψ x‖ ≤ Cψ := by
      refine (ae_restrict_iff' measurableSet_unitCube).mpr ?_
      exact Filter.Eventually.of_forall (fun x hx => hCψ ⟨x, hsub hx, rfl⟩)
    have hgψ_int : Integrable (fun x => g x * ψ x) (volume.restrict (UnitCube d)) :=
      (memLp_one_iff_integrable.mp h.memLpPer.toMemLp).mul_bdd hψ_cont.aestronglyMeasurable hbnd_ae
    have hg'ψ_int : Integrable (fun x => g' x * ψ x) (volume.restrict (UnitCube d)) :=
      (memLp_one_iff_integrable.mp h'.memLpPer.toMemLp).mul_bdd hψ_cont.aestronglyMeasurable hbnd_ae
    -- `∫ x, ψ x • (g x - g' x) ∂μ = ∫_cube ψ·g - ∫_cube ψ·g'`.
    have hμ_eq : ∫ x, ψ x • (fun y => g y - g' y) x ∂μ
        = periodicIntegral (fun x => g x * ψ x)
          - periodicIntegral (fun x => g' x * ψ x) := by
      rw [hμ_def]
      have hpt : (fun x => ψ x • (fun y => g y - g' y) x)
          = (fun x => g x * ψ x - g' x * ψ x) := by
        funext x; simp [smul_eq_mul]; ring
      rw [hpt]
      unfold periodicIntegral
      rw [integral_sub hgψ_int hg'ψ_int]
    rw [hμ_eq, hgg', sub_self]
  -- Apply the Mathlib lemma on the open cube.
  have hae_U : ∀ᵐ x ∂μ, x ∈ U → (fun y => g y - g' y) x = 0 :=
    hU_open.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc hvanish
  -- Upgrade a.e.-on-U to a.e.-on-cube: the complement of `U` is `μ`-null.
  have hUvol : volume U = 1 := by rw [hU_def, Real.volume_pi_Ioo]; simp
  have hnull : μ Uᶜ = 0 := by
    rw [hμ_def, Measure.restrict_apply hU_open.measurableSet.compl]
    -- `Uᶜ ∩ UnitCube = UnitCube \ U`, volume `= vol(UnitCube) - vol(U) = 0`.
    have hset : Uᶜ ∩ UnitCube d = UnitCube d \ U := by
      rw [Set.diff_eq, Set.inter_comm]
    rw [hset, measure_diff hU_sub_cube hU_open.measurableSet.nullMeasurableSet
      (by rw [hUvol]; exact ENNReal.one_ne_top), volume_unitCube, hUvol]
    simp
  have hae_boundary : ∀ᵐ x ∂μ, x ∈ U := by
    rw [ae_iff]
    simpa only [Set.compl_def] using hnull
  filter_upwards [hae_U, hae_boundary] with x hx hxU
  have := hx hxU
  simpa [sub_eq_zero] using this

end HasWeakDerivPer

/-! ### Sample example: the constant-1 test function has zero weak derivative -/

example (i : Fin d) :
    HasWeakDerivPer (d := d) i
      (fun _ : (Fin d → ℝ) => (1 : ℝ))
      (fun _ : (Fin d → ℝ) => (0 : ℝ)) := by
  refine ⟨?_, ?_⟩
  · have : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
      ⟨by
        rw [Measure.restrict_apply MeasurableSet.univ]
        simp⟩
    exact MemLp.toMemLpPer (memLp_const (0 : ℝ))
  · intro ψ
    have hg : (fun x : Fin d → ℝ => (0 : ℝ) * (ψ : (Fin d → ℝ) → ℝ) x) =
        (fun _ => (0 : ℝ)) := by funext x; simp
    rw [hg]
    have h0 : periodicIntegral (fun _ : Fin d → ℝ => (0 : ℝ)) = 0 := by
      simp [periodicIntegral_const]
    rw [h0]
    have hf : (fun x : Fin d → ℝ => (1 : ℝ) *
        ((SmoothPeriodic.partialDeriv i ψ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) x) =
        (fun x => fderiv ℝ (ψ : (Fin d → ℝ) → ℝ) x (Pi.basisFun ℝ (Fin d) i)) := by
      funext x; simp [SmoothPeriodic.coe_partialDeriv]
    rw [hf]
    rw [integral_partialDeriv_eq_zero
      (ψ : (Fin d → ℝ) → ℝ) ψ.smooth ψ.periodic i]
    simp

/-! ### Sample example: zero has zero weak derivative -/

example (i : Fin d) :
    HasWeakDerivPer (d := d) i
      (fun _ : (Fin d → ℝ) => (0 : ℝ))
      (fun _ : (Fin d → ℝ) => (0 : ℝ)) := by
  refine ⟨?_, ?_⟩
  · have : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
      ⟨by
        rw [Measure.restrict_apply MeasurableSet.univ]
        simp⟩
    exact MemLp.toMemLpPer (memLp_const (0 : ℝ))
  · intro φ
    have hg : (fun x : Fin d → ℝ => (0 : ℝ) * (φ : (Fin d → ℝ) → ℝ) x) =
        (fun _ => (0 : ℝ)) := by funext x; simp
    have hf : (fun x : Fin d → ℝ => (0 : ℝ) *
        ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) x) =
        (fun _ => (0 : ℝ)) := by funext x; simp
    rw [hg, hf]
    simp [periodicIntegral_const]

/-! ### Sample example: uniqueness of the weak derivative

Two weak derivatives of the constant function `1` agree a.e. on the cube. -/

#check @HasWeakDerivPer.unique

example (i : Fin d) {g g' : (Fin d → ℝ) → ℝ}
    (h : HasWeakDerivPer (d := d) i (fun _ => (1 : ℝ)) g)
    (h' : HasWeakDerivPer (d := d) i (fun _ => (1 : ℝ)) g') :
    g =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] g' :=
  h.unique h'

/-! ## Weak-derivative limit passage

The bare-function limit-passage lemma for the periodic weak derivative:
if `u_n → u` and `Du_n → Du` weakly (in the bare-function `Tendsto`-of-
integrals sense, against arbitrary smooth periodic test functions), and
each `Du_n n` is the periodic weak derivative of `u_n n` in direction
`i`, then `Du` is the periodic weak derivative of `u` in direction `i`.

This discharges (the bare-function form of) AC2 of
`infra-P4-rebuild-T8-discharge-aux-weakLimit`. It is independent of the
`LpPer` / `Lp` quotient: any source of weak convergence (Mathlib `Lp`
weak conv, project-internal `WeakConvPairing`, smooth-density chain)
that produces the `Tendsto`-of-integrals hypotheses can plug in.

The proof is a one-line limit unique trick: for every test function `φ`,
both `Tendsto`'s give us
* `∫ Du_n n · φ → ∫ Du · φ`,
* `∫ u_n n · ∂_i φ → ∫ u · ∂_i φ`,
and the per-`n` weak-derivative identity
`∫ Du_n n · φ = -∫ u_n n · ∂_i φ` lets us identify the two limits up to
sign, yielding the integration-by-parts identity for `(u, Du)` against
`φ`. -/

theorem HasWeakDerivPer.of_weak_limit
    {i : Fin d}
    {u_n Du_n : ℕ → (Fin d → ℝ) → ℝ}
    {u Du : (Fin d → ℝ) → ℝ}
    (hDu : MemLpPer 1 Du)
    (hSeq : ∀ n, HasWeakDerivPer i (u_n n) (Du_n n))
    (hConvU : ∀ φ : SmoothPeriodic d,
        Filter.Tendsto
          (fun n => periodicIntegral
                      (fun x => u_n n x * (φ : (Fin d → ℝ) → ℝ) x))
          Filter.atTop
          (nhds (periodicIntegral
                    (fun x => u x * (φ : (Fin d → ℝ) → ℝ) x))))
    (hConvDu : ∀ φ : SmoothPeriodic d,
        Filter.Tendsto
          (fun n => periodicIntegral
                      (fun x => Du_n n x * (φ : (Fin d → ℝ) → ℝ) x))
          Filter.atTop
          (nhds (periodicIntegral
                    (fun x => Du x * (φ : (Fin d → ℝ) → ℝ) x)))) :
    HasWeakDerivPer i u Du := by
  refine ⟨hDu, ?_⟩
  intro φ
  -- Abbreviate the partial-derivative test function.
  set ψ : SmoothPeriodic d := SmoothPeriodic.partialDeriv i φ with hψ_def
  -- LHS limit: `∫ Du_n n · φ → ∫ Du · φ`.
  have hL :
      Filter.Tendsto
        (fun n => periodicIntegral
                    (fun x => Du_n n x * (φ : (Fin d → ℝ) → ℝ) x))
        Filter.atTop
        (nhds (periodicIntegral
                  (fun x => Du x * (φ : (Fin d → ℝ) → ℝ) x))) :=
    hConvDu φ
  -- RHS limit: `-∫ u_n n · ∂_i φ → -∫ u · ∂_i φ`.
  have hR_pos :
      Filter.Tendsto
        (fun n => periodicIntegral
                    (fun x => u_n n x * (ψ : (Fin d → ℝ) → ℝ) x))
        Filter.atTop
        (nhds (periodicIntegral
                  (fun x => u x * (ψ : (Fin d → ℝ) → ℝ) x))) :=
    hConvU ψ
  have hR :
      Filter.Tendsto
        (fun n => - periodicIntegral
                    (fun x => u_n n x * (ψ : (Fin d → ℝ) → ℝ) x))
        Filter.atTop
        (nhds (- periodicIntegral
                  (fun x => u x * (ψ : (Fin d → ℝ) → ℝ) x))) :=
    hR_pos.neg
  -- Per-`n` weak-derivative identity: rewrite the sequence on the LHS.
  have hEq : ∀ n,
      periodicIntegral
          (fun x => Du_n n x * (φ : (Fin d → ℝ) → ℝ) x) =
        - periodicIntegral
            (fun x => u_n n x * (ψ : (Fin d → ℝ) → ℝ) x) := by
    intro n
    have := (hSeq n).integral_eq φ
    simpa [hψ_def] using this
  -- The two limits agree along the sequence, so the limits are equal.
  have hL' :
      Filter.Tendsto
        (fun n => - periodicIntegral
                    (fun x => u_n n x * (ψ : (Fin d → ℝ) → ℝ) x))
        Filter.atTop
        (nhds (periodicIntegral
                  (fun x => Du x * (φ : (Fin d → ℝ) → ℝ) x))) := by
    refine hL.congr ?_
    intro n
    exact hEq n
  -- Identify the two limits.
  have hUnique :
      periodicIntegral (fun x => Du x * (φ : (Fin d → ℝ) → ℝ) x) =
        - periodicIntegral
            (fun x => u x * (ψ : (Fin d → ℝ) → ℝ) x) :=
    tendsto_nhds_unique hL' hR
  -- Repackage with `ψ := SmoothPeriodic.partialDeriv i φ`.
  simpa [hψ_def] using hUnique

/-! ### Sanity check on the limit-passage lemma -/

/-- The constant sequence `u_n := u`, `Du_n := Du` clearly converges to
`(u, Du)`, so the limit-passage lemma collapses to its hypothesis. -/
example
    {i : Fin d} {u Du : (Fin d → ℝ) → ℝ}
    (h : HasWeakDerivPer i u Du) :
    HasWeakDerivPer i u Du := by
  refine HasWeakDerivPer.of_weak_limit
    (u_n := fun _ => u) (Du_n := fun _ => Du)
    h.memLpPer (fun _ => h) ?_ ?_
  · intro φ; exact tendsto_const_nhds
  · intro φ; exact tendsto_const_nhds

end Periodic
end StationaryMFG
