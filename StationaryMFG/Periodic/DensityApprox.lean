module

public import StationaryMFG.Periodic.Sobolev
public import StationaryMFG.Periodic.Integral

@[expose] public section

/-!
# Smooth-density closure in `W^{1,γ̄}_per` via Hölder pairing continuity

This file supplies the analytic bridge that lets a transport / variational
identity proved for *all smooth periodic test functions* be extended to *all*
`W^{1,γ̄}_per` test functions.

The two ingredients are:

* the **smooth-density theorem** in `W^{1,γ̄}_per`, already fully proved in
  `Periodic/Sobolev.lean` (`SmoothPeriodic.exists_sobolevPer_sub_le`): both the
  function and its gradient are approximated by a periodic mollification;
* the **Hölder pairing continuity bound** proved here: a pairing
  `φ ↦ ∫_{𝕋^d} a · φ` with `a ∈ L^{γ̄'}_per` is Lipschitz in the `L^{γ̄}_per`
  seminorm of `φ`.

Combining the two gives
`integralIdentity_extend_to_W1gamma_via_smooth_density`: the transport
functional vanishing on smooth periodic functions forces it to vanish on the
full Sobolev test class.

Paper reference: `eq:congest.transport` (line ~1404), "for all
`φ ∈ W^{1,γ̄}(𝕋^d)`": the density step justifying the extension from the
authors' smooth-test proof to the full Sobolev class.

-- Adapted from LpSpaces.Density / Mollification (whole-space convolution
-- density); re-derived here for periodic functions on the unit cube.
-/

namespace StationaryMFG
namespace Periodic

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

variable {d : ℕ}

/-! ### Hölder pairing continuity -/

/-- **Hölder pairing bound on the torus.**

For a "dual" function `a ∈ L^q_per` and a "primal" function `φ ∈ L^p_per`
whose exponents form a Hölder triple `HolderTriple p q 1` (i.e. `1/p + 1/q = 1`),
the absolute value of the paired periodic integral is bounded by the product
of the two seminorms:

```
‖∫_{𝕋^d} a · φ‖ ≤ lpNormPer q a · lpNormPer p φ.
```

This is the genuinely-missing analytic primitive behind the smooth-density
closure: it makes the transport functional `φ ↦ ∫ a·φ` continuous (indeed
Lipschitz) in the `L^p_per` seminorm. -/
theorem abs_periodicIntegral_mul_le_lpNormPer_mul
    {p q : ℝ≥0∞} [ENNReal.HolderTriple p q 1]
    {a φ : (Fin d → ℝ) → ℝ}
    (ha : MemLpPer q a) (hφ : MemLpPer p φ) :
    ‖periodicIntegral (fun x => a x * φ x)‖
      ≤ lpNormPer q a * lpNormPer p φ := by
  -- `‖∫ a·φ‖ₑ ≤ ∫⁻ ‖a·φ‖ₑ`.
  have h_enorm_int :
      ‖periodicIntegral (fun x => a x * φ x)‖ₑ
        ≤ ∫⁻ x, ‖a x * φ x‖ₑ
            ∂(Measure.restrict volume (UnitCube d)) := by
    unfold periodicIntegral
    -- `∫ x in UnitCube, a x * φ x = ∫ x, a x * φ x ∂(restrict)` definitionally.
    exact enorm_integral_le_lintegral_enorm _
  -- `∫⁻ ‖a·φ‖ₑ = eLpNorm (a·φ) 1`.
  have h_eLpNorm_one :
      ∫⁻ x, ‖a x * φ x‖ₑ ∂(Measure.restrict volume (UnitCube d))
        = eLpNormPer 1 (fun x => a x * φ x) := by
    unfold eLpNormPer
    rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm (ha.aestronglyMeasurable.fun_mul hφ.aestronglyMeasurable)]
  -- Hölder: `eLpNorm (a·φ) 1 ≤ eLpNorm a q * eLpNorm φ p`, via `smul = mul`.
  have h_holder :
      eLpNormPer 1 (fun x => a x * φ x)
        ≤ eLpNormPer q a * eLpNormPer p φ := by
    have h_smul : (fun x => a x * φ x) = a • φ := by
      funext x; simp [smul_eq_mul]
    unfold eLpNormPer
    rw [h_smul]
    -- `eLpNorm (a • φ) 1 ≤ eLpNorm a q * eLpNorm φ p`.
    have := MeasureTheory.eLpNorm_smul_le_mul_eLpNorm
      (μ := Measure.restrict volume (UnitCube d))
      (p := q) (q := p) (r := 1)
      (f := φ) (φ := a) ha.aestronglyMeasurable hφ.aestronglyMeasurable
    exact this
  -- Combine into an `ℝ≥0∞` bound, then take `toReal`.
  have h_e_bound :
      ‖periodicIntegral (fun x => a x * φ x)‖ₑ
        ≤ eLpNormPer q a * eLpNormPer p φ :=
    le_trans h_enorm_int (le_of_le_of_eq (le_of_eq h_eLpNorm_one) rfl
      |>.trans h_holder)
  -- Finiteness of the right-hand product.
  have h_ne_top : eLpNormPer q a * eLpNormPer p φ ≠ (⊤ : ℝ≥0∞) :=
    ENNReal.mul_ne_top ha.eLpNormPer_ne_top hφ.eLpNormPer_ne_top
  -- `‖x‖ = ‖x‖ₑ.toReal`, then monotone `toReal`.
  have h_toReal := ENNReal.toReal_mono h_ne_top h_e_bound
  rw [ENNReal.toReal_mul] at h_toReal
  -- `‖·‖ₑ.toReal = ‖·‖`.
  simpa [enorm, lpNormPer, Real.enorm_eq_ofReal_abs,
    ENNReal.toReal_ofReal, abs_nonneg, Real.norm_eq_abs] using h_toReal

/-- **Lipschitz form of the pairing bound.**

The pairing functional `φ ↦ ∫ a·φ` is Lipschitz with constant `lpNormPer q a`
in the `L^p_per` seminorm: for `φ, ψ ∈ L^p_per`,
`‖∫ a·φ − ∫ a·ψ‖ ≤ lpNormPer q a · lpNormPer p (φ − ψ)`. -/
theorem abs_periodicIntegral_mul_sub_le
    {p q : ℝ≥0∞} [ENNReal.HolderTriple p q 1]
    {a φ ψ : (Fin d → ℝ) → ℝ}
    (ha : MemLpPer q a) (hφ : MemLpPer p φ) (hψ : MemLpPer p ψ) :
    ‖periodicIntegral (fun x => a x * φ x)
        - periodicIntegral (fun x => a x * ψ x)‖
      ≤ lpNormPer q a * lpNormPer p (fun x => φ x - ψ x) := by
  -- Integrability of both products on the cube (Hölder).
  have hint_φ : IntegrableOn (fun x => a x * φ x) (UnitCube d) := by
    have h_smul : (fun x => a x * φ x) = a • φ := by
      funext x; simp [smul_eq_mul]
    have hL1 : MemLp (a • φ) 1 (Measure.restrict volume (UnitCube d)) :=
      MeasureTheory.MemLp.smul (μ := Measure.restrict volume (UnitCube d))
        (p := q) (q := p) (r := 1) ha.toMemLp hφ.toMemLp
    have := (MeasureTheory.memLp_one_iff_integrable.mp hL1)
    rw [h_smul]; exact this
  have hint_ψ : IntegrableOn (fun x => a x * ψ x) (UnitCube d) := by
    have h_smul : (fun x => a x * ψ x) = a • ψ := by
      funext x; simp [smul_eq_mul]
    have hL1 : MemLp (a • ψ) 1 (Measure.restrict volume (UnitCube d)) :=
      MeasureTheory.MemLp.smul (μ := Measure.restrict volume (UnitCube d))
        (p := q) (q := p) (r := 1) ha.toMemLp hψ.toMemLp
    have := (MeasureTheory.memLp_one_iff_integrable.mp hL1)
    rw [h_smul]; exact this
  -- Linearity: `∫ a·φ − ∫ a·ψ = ∫ a·(φ − ψ)`.
  have h_sub :
      periodicIntegral (fun x => a x * φ x)
          - periodicIntegral (fun x => a x * ψ x)
        = periodicIntegral (fun x => a x * (φ x - ψ x)) := by
    unfold periodicIntegral
    rw [← MeasureTheory.integral_sub hint_φ hint_ψ]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x; ring
  rw [h_sub]
  -- `MemLpPer p (φ − ψ)`.
  have hsub_lp : MemLpPer p (fun x => φ x - ψ x) := by
    have : MemLpPer p (φ - ψ) := by
      have := MeasureTheory.MemLp.sub hφ.toMemLp hψ.toMemLp
      exact MemLp.toMemLpPer this
    exact this
  exact abs_periodicIntegral_mul_le_lpNormPer_mul ha hsub_lp

/-! ### Density-closure extension of an integral identity -/

/-- **Smooth-density closure of the transport identity (single-coefficient
core, `φ`-pairing only).**

Given a "dual" coefficient `a ∈ L^{γ̄'}_per` and a primal function
`f ∈ L^{γ̄}_per` (the Sobolev test function), if the pairing integral
`∫ a·φ` vanishes for every smooth periodic `φ` arbitrarily close to `f` in the
`L^{γ̄}_per` seminorm, then `∫ a·f = 0`.

This is the abstract Hölder-continuity transfer applied to a single pairing
term. The full transport functional is the finite sum of such terms (the
function term and the `d` gradient terms); see
`integralIdentity_extend_to_W1gamma_via_smooth_density`. -/
theorem periodicIntegral_pairing_eq_zero_of_smooth_dense
    {p q : ℝ≥0∞} [ENNReal.HolderTriple p q 1]
    {a f : (Fin d → ℝ) → ℝ}
    (ha : MemLpPer q a) (hf : MemLpPer p f)
    (h_approx : ∀ η : ℝ, 0 < η →
      ∃ φ : (Fin d → ℝ) → ℝ, MemLpPer p φ ∧
        lpNormPer p (fun x => f x - φ x) ≤ η ∧
        periodicIntegral (fun x => a x * φ x) = 0) :
    periodicIntegral (fun x => a x * f x) = 0 := by
  -- Suppose `c := ∫ a·f ≠ 0`; derive a contradiction by approximating finely.
  by_contra hne
  set c : ℝ := periodicIntegral (fun x => a x * f x) with hc_def
  have hc_pos : 0 < ‖c‖ := norm_pos_iff.mpr hne
  -- Choose `η` so that `lpNormPer q a · η < ‖c‖`.
  set K : ℝ := lpNormPer q a with hK_def
  have hK_nonneg : 0 ≤ K := lpNormPer_nonneg q a
  -- pick η = ‖c‖ / (K + 1) > 0; then K·η ≤ K/(K+1)·‖c‖ < ‖c‖.
  set η : ℝ := ‖c‖ / (K + 1) with hη_def
  have hη_pos : 0 < η := by
    apply div_pos hc_pos; linarith
  obtain ⟨φ, hφ_lp, hφ_close, hφ_zero⟩ := h_approx η hη_pos
  -- `‖∫ a·f − ∫ a·φ‖ ≤ K · lpNormPer p (f − φ) ≤ K · η`.
  have h_bound := abs_periodicIntegral_mul_sub_le (p := p) (q := q)
    ha hf hφ_lp
  rw [hφ_zero, sub_zero] at h_bound
  -- `‖∫ a·f‖ = ‖c‖`.
  have h_c_eq : ‖periodicIntegral (fun x => a x * f x)‖ = ‖c‖ := by rw [hc_def]
  rw [h_c_eq] at h_bound
  -- Combine: ‖c‖ ≤ K · lpNormPer p (f-φ) ≤ K · η.
  have h_lp_le : lpNormPer p (fun x => f x - φ x) ≤ η := hφ_close
  have h_step : ‖c‖ ≤ K * η := by
    refine le_trans h_bound ?_
    exact mul_le_mul_of_nonneg_left h_lp_le hK_nonneg
  -- But K · η = K · ‖c‖/(K+1) < ‖c‖.
  have h_contra : K * η < ‖c‖ := by
    have hKpos : (0:ℝ) < K + 1 := by linarith
    have hrw : K * η = K * ‖c‖ / (K + 1) := by
      rw [hη_def]; ring
    rw [hrw, div_lt_iff₀ hKpos]
    -- `K * ‖c‖ < ‖c‖ * (K + 1)`, i.e. `0 < ‖c‖`.
    nlinarith [hc_pos]
  linarith

/-! ### Full transport-functional extension to `W^{1,γ̄}_per` -/

/-- The transport functional, as a finite sum of Hölder pairings: the
`φ`-pairing against the coefficient `a` plus, for each coordinate `i`, the
`∂_iφ`-pairing against the coefficient `b i`. With `(f, g)` standing for the
test function and its weak-derivative family, this is

```
Λ(f, g) = ∫ a·f + ∑ i, ∫ (b i)·(g i).
```

For the congestion transport equation `eq:congest.transport`,
`a = (m-1) + ε|u|^{γ̄-2}u` and `b i = (mD_pH + ε|Du|^{γ̄-2}Du) i`. -/
noncomputable def transportFunctional
    (a : (Fin d → ℝ) → ℝ) (b : Fin d → ((Fin d → ℝ) → ℝ))
    (f : (Fin d → ℝ) → ℝ) (g : Fin d → ((Fin d → ℝ) → ℝ)) : ℝ :=
  periodicIntegral (fun x => a x * f x)
    + ∑ i : Fin d, periodicIntegral (fun x => b i x * g i x)

/-- **Combined-integrand form of the transport functional.**

The transport functional `Λ(a, b; f, g) = ∫ a·f + ∑ᵢ ∫ bᵢ·gᵢ` agrees with the
single combined integral of the pointwise sum
`a·f + ∑ᵢ bᵢ·gᵢ` over the torus, provided each pairing is integrable (which holds
under the Hölder coefficient/test membership facts).

This is the **key dotProduct ↔ transportFunctional bridge**: in the congestion
transport identity the dot product `(m•DpH)⬝Dφ = ∑ᵢ (m·DpH_i)·Dφ_i` is exactly
the finite sum `∑ᵢ bᵢ·gᵢ`, so the combined integrand
`(m−1)·φ + (m•DpH)⬝Dφ` integrates to `transportFunctional (m−1) (m•DpH) φ Dφ`.
The split uses `integral_add` (each summand integrable by Hölder) and
`integral_finset_sum` to push the integral through the finite sum. -/
theorem periodicIntegral_combined_eq_transportFunctional
    {p q : ℝ≥0∞} [ENNReal.HolderTriple p q 1]
    {a : (Fin d → ℝ) → ℝ} {b : Fin d → ((Fin d → ℝ) → ℝ)}
    (ha : MemLpPer q a) (hb : ∀ i, MemLpPer q (b i))
    {f : (Fin d → ℝ) → ℝ} {g : Fin d → ((Fin d → ℝ) → ℝ)}
    (hf : MemLpPer p f) (hg : ∀ i, MemLpPer p (g i)) :
    (∫ x in UnitCube d,
        a x * f x + ∑ i : Fin d, b i x * g i x
        ∂(volume : Measure (Fin d → ℝ)))
      = transportFunctional a b f g := by
  classical
  -- Each coordinate pairing is integrable on the cube (Hölder).
  have hint_af : IntegrableOn (fun x => a x * f x) (UnitCube d)
      (volume : Measure (Fin d → ℝ)) := by
    have : Integrable (a * f) (Measure.restrict volume (UnitCube d)) :=
      MeasureTheory.MemLp.integrable_mul ha.toMemLp hf.toMemLp
    exact this
  have hint_bg : ∀ i : Fin d,
      IntegrableOn (fun x => b i x * g i x) (UnitCube d)
        (volume : Measure (Fin d → ℝ)) := by
    intro i
    have : Integrable (b i * g i) (Measure.restrict volume (UnitCube d)) :=
      MeasureTheory.MemLp.integrable_mul (hb i).toMemLp (hg i).toMemLp
    exact this
  have hint_sum : IntegrableOn (fun x => ∑ i : Fin d, b i x * g i x)
      (UnitCube d) (volume : Measure (Fin d → ℝ)) := by
    have := integrable_finset_sum (μ := Measure.restrict volume (UnitCube d))
      (s := (Finset.univ : Finset (Fin d)))
      (f := fun i x => b i x * g i x) (fun i _ => hint_bg i)
    exact this
  -- Split the combined integral into the `a·f` part and the sum part.
  rw [MeasureTheory.integral_add hint_af hint_sum]
  -- Push the integral through the finite sum.
  rw [MeasureTheory.integral_finset_sum (s := (Finset.univ : Finset (Fin d)))
      (f := fun i x => b i x * g i x) (fun i _ => hint_bg i)]
  rfl

/-- **Continuity of the transport functional in the Sobolev seminorm.**

The difference of the transport functional at two test pairs is controlled by
the `W^{1,p}_per` seminorm of the difference, with Lipschitz constant the
largest `L^q_per` seminorm among the coefficients:

```
‖Λ(f, g) − Λ(f', g')‖ ≤ C · sobolevNormPer p (f − f') (i ↦ g i − g' i),
```

where `C` bounds every `lpNormPer q a`, `lpNormPer q (b i)`. -/
theorem abs_transportFunctional_sub_le
    {p q : ℝ≥0∞} [ENNReal.HolderTriple p q 1]
    {a : (Fin d → ℝ) → ℝ} {b : Fin d → ((Fin d → ℝ) → ℝ)}
    (ha : MemLpPer q a) (hb : ∀ i, MemLpPer q (b i))
    {f f' : (Fin d → ℝ) → ℝ} {g g' : Fin d → ((Fin d → ℝ) → ℝ)}
    (hf : MemLpPer p f) (hf' : MemLpPer p f')
    (hg : ∀ i, MemLpPer p (g i)) (hg' : ∀ i, MemLpPer p (g' i))
    {C : ℝ} (hC_a : lpNormPer q a ≤ C) (hC_b : ∀ i, lpNormPer q (b i) ≤ C)
    (hC_nonneg : 0 ≤ C) :
    ‖transportFunctional a b f g - transportFunctional a b f' g'‖
      ≤ C * sobolevNormPer p (fun x => f x - f' x)
          (fun i x => g i x - g' i x) := by
  -- Split the functional difference into the function term and gradient terms.
  unfold transportFunctional
  have h_split :
      (periodicIntegral (fun x => a x * f x)
            + ∑ i : Fin d, periodicIntegral (fun x => b i x * g i x))
          - (periodicIntegral (fun x => a x * f' x)
            + ∑ i : Fin d, periodicIntegral (fun x => b i x * g' i x))
        = (periodicIntegral (fun x => a x * f x)
            - periodicIntegral (fun x => a x * f' x))
          + ∑ i : Fin d, (periodicIntegral (fun x => b i x * g i x)
            - periodicIntegral (fun x => b i x * g' i x)) := by
    rw [Finset.sum_sub_distrib]; ring
  rw [h_split]
  -- Triangle inequality on the (1 + d)-term sum of norms.
  refine le_trans (norm_add_le _ _) ?_
  refine le_trans (add_le_add (le_refl _) (norm_sum_le _ _)) ?_
  -- Bound the function term.
  have h_fterm :
      ‖periodicIntegral (fun x => a x * f x)
          - periodicIntegral (fun x => a x * f' x)‖
        ≤ C * lpNormPer p (fun x => f x - f' x) := by
    refine le_trans (abs_periodicIntegral_mul_sub_le ha hf hf') ?_
    exact mul_le_mul_of_nonneg_right hC_a (lpNormPer_nonneg p _)
  -- Bound each gradient term.
  have h_gterm : ∀ i : Fin d,
      ‖periodicIntegral (fun x => b i x * g i x)
          - periodicIntegral (fun x => b i x * g' i x)‖
        ≤ C * lpNormPer p (fun x => g i x - g' i x) := by
    intro i
    refine le_trans (abs_periodicIntegral_mul_sub_le (hb i) (hg i) (hg' i)) ?_
    exact mul_le_mul_of_nonneg_right (hC_b i) (lpNormPer_nonneg p _)
  have h_gsum :
      ∑ i : Fin d, ‖periodicIntegral (fun x => b i x * g i x)
          - periodicIntegral (fun x => b i x * g' i x)‖
        ≤ ∑ i : Fin d, C * lpNormPer p (fun x => g i x - g' i x) :=
    Finset.sum_le_sum (fun i _ => h_gterm i)
  -- Assemble: ‖fterm‖ + ∑ ‖gterm‖ ≤ C·(lpNorm f-f' + ∑ lpNorm g-g').
  have h_total :
      ‖periodicIntegral (fun x => a x * f x)
          - periodicIntegral (fun x => a x * f' x)‖
        + ∑ i : Fin d, ‖periodicIntegral (fun x => b i x * g i x)
          - periodicIntegral (fun x => b i x * g' i x)‖
        ≤ C * lpNormPer p (fun x => f x - f' x)
            + ∑ i : Fin d, C * lpNormPer p (fun x => g i x - g' i x) :=
    add_le_add h_fterm h_gsum
  refine le_trans h_total ?_
  -- Factor `C` out of the right-hand side and recognise `sobolevNormPer`.
  unfold sobolevNormPer
  rw [mul_add, Finset.mul_sum]

/-- **Smooth-density closure of the transport functional to `W^{1,γ̄}_per`.**

This is the keystone density bridge (paper `eq:congest.transport`, line ~1404,
"for all `φ ∈ W^{1,γ̄}(𝕋^d)`").

Given coefficient functions `a, b i ∈ L^{γ̄'}_per` (`q`) and a Sobolev test
function `f ∈ W^{1,γ̄}_per` (`p`) with explicit weak-derivative family `g`
(all in `L^p_per`, with the regularity needed to invoke smooth density), if the
transport functional vanishes on every smooth periodic test function `φ`
(paired with its classical derivatives `∂_iφ`), then it vanishes on `(f, g)`.

The proof approximates `f` by smooth periodic `φ` in the `W^{1,p}_per`
seminorm (`SmoothPeriodic.exists_sobolevPer_sub_le`), and bounds the resulting
functional difference by `abs_transportFunctional_sub_le`, which tends to `0`. -/
theorem integralIdentity_extend_to_W1gamma_via_smooth_density
    {p q : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    [ENNReal.HolderTriple p q 1]
    {a : (Fin d → ℝ) → ℝ} {b : Fin d → ((Fin d → ℝ) → ℝ)}
    (ha : MemLpPer q a) (hb : ∀ i, MemLpPer q (b i))
    {f : (Fin d → ℝ) → ℝ}
    (hf_meas : AEStronglyMeasurable f (volume : Measure (Fin d → ℝ)))
    (hf_per : IsPeriodic f)
    (hf_loc : LocallyIntegrable f (volume : Measure (Fin d → ℝ)))
    (hf_lp : MemLpPer p f)
    {g : Fin d → ((Fin d → ℝ) → ℝ)}
    (hg_weak : ∀ i, HasWeakDerivPer i f (g i))
    (hg_meas : ∀ i, AEStronglyMeasurable (g i) (volume : Measure (Fin d → ℝ)))
    (hg_per : ∀ i, IsPeriodic (g i))
    (hg_loc : ∀ i, LocallyIntegrable (g i) (volume : Measure (Fin d → ℝ)))
    (hg_lp : ∀ i, MemLpPer p (g i))
    (h_smooth : ∀ φ : SmoothPeriodic d,
      transportFunctional a b (φ : (Fin d → ℝ) → ℝ)
        (fun i => ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
          (Fin d → ℝ) → ℝ)) = 0) :
    transportFunctional a b f g = 0 := by
  classical
  -- Uniform Lipschitz constant for the coefficient pairings: the additive
  -- bound `C' := lpNormPer q a + ∑ i, lpNormPer q (b i)`.
  set C' : ℝ := lpNormPer q a + ∑ i : Fin d, lpNormPer q (b i) with hC'_def
  have hC'_nonneg : 0 ≤ C' := by
    rw [hC'_def]
    have h₁ : 0 ≤ lpNormPer q a := lpNormPer_nonneg q a
    have h₂ : 0 ≤ ∑ i : Fin d, lpNormPer q (b i) :=
      Finset.sum_nonneg (fun i _ => lpNormPer_nonneg q (b i))
    linarith
  have hC'_a : lpNormPer q a ≤ C' := by
    rw [hC'_def]
    have h₂ : 0 ≤ ∑ i : Fin d, lpNormPer q (b i) :=
      Finset.sum_nonneg (fun i _ => lpNormPer_nonneg q (b i))
    linarith
  have hC'_b : ∀ i, lpNormPer q (b i) ≤ C' := by
    intro i
    rw [hC'_def]
    have hmem : lpNormPer q (b i) ≤ ∑ j : Fin d, lpNormPer q (b j) :=
      Finset.single_le_sum (fun j _ => lpNormPer_nonneg q (b j))
        (Finset.mem_univ i)
    have h₁ : 0 ≤ lpNormPer q a := lpNormPer_nonneg q a
    linarith
  -- Suppose the functional is nonzero; approximate finely for a contradiction.
  by_contra hne
  set c : ℝ := transportFunctional a b f g with hc_def
  have hc_pos : 0 < ‖c‖ := norm_pos_iff.mpr hne
  -- Approximation error needed: `ε := ‖c‖ / (C' + 1)`.
  set εr : ℝ := ‖c‖ / (C' + 1) with hεr_def
  have hεr_pos : 0 < εr := by
    apply div_pos hc_pos; linarith
  -- Smooth-density: pick φ with sobolevNormPer (f - φ) (g - ∂φ) ≤ εr.
  obtain ⟨φ, hφ⟩ := SmoothPeriodic.exists_sobolevPer_sub_le
    (p := p) hp hp_top hf_meas hf_per hf_loc hf_lp
    hg_weak hg_meas hg_per hg_loc hg_lp hεr_pos
  -- `MemLpPer p φ` and `MemLpPer p (∂_i φ)`.
  have hφ_lp : MemLpPer p (φ : (Fin d → ℝ) → ℝ) :=
    (MemSobolevPer.of_smoothPeriodic p φ).1
  have hφ_partial_lp : ∀ i, MemLpPer p
      ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
        (Fin d → ℝ) → ℝ) := fun i =>
    (MemSobolevPer.of_smoothPeriodic p
      (SmoothPeriodic.partialDeriv i φ)).1
  -- Continuity bound: ‖Λ(f,g) − Λ(φ,∂φ)‖ ≤ C' · sobolevNormPer (f-φ) (g-∂φ).
  have h_bound := abs_transportFunctional_sub_le (p := p) (q := q)
    ha hb hf_lp hφ_lp hg_lp hφ_partial_lp hC'_a hC'_b hC'_nonneg
  -- `Λ(φ, ∂φ) = 0` by the smooth-test hypothesis.
  rw [h_smooth φ, sub_zero] at h_bound
  -- `‖Λ(f,g)‖ = ‖c‖`.
  have h_c_eq : ‖transportFunctional a b f g‖ = ‖c‖ := by rw [hc_def]
  rw [h_c_eq] at h_bound
  -- Chain: ‖c‖ ≤ C' · sobolevNormPer (f-φ)(g-∂φ) ≤ C' · εr.
  have h_step : ‖c‖ ≤ C' * εr := by
    refine le_trans h_bound ?_
    exact mul_le_mul_of_nonneg_left hφ hC'_nonneg
  -- But C' · εr = C'·‖c‖/(C'+1) < ‖c‖.
  have h_contra : C' * εr < ‖c‖ := by
    have hpos : (0:ℝ) < C' + 1 := by linarith
    have hrw : C' * εr = C' * ‖c‖ / (C' + 1) := by rw [hεr_def]; ring
    rw [hrw, div_lt_iff₀ hpos]
    nlinarith [hc_pos]
  linarith

/-- **`AEPeriodicRep` sibling of the smooth-density closure.**

Identical conclusion to `integralIdentity_extend_to_W1gamma_via_smooth_density`,
but the §1b regularity of the (non-smooth) test pair `(f, g)` is supplied
through the `AEPeriodicRep` layer (`hf_rep`, `hg_rep`) instead of literal
pointwise `IsPeriodic` / `LocallyIntegrable` / `AEStronglyMeasurable`. The
periodic representatives `fRep := hf_rep.rep`, `gRep i := (hg_rep i).rep` are
built internally; the base lemma is applied to those reps, and the
`transportFunctional` conclusion is transported back to `(f, g)` by
`integral_congr_ae` (each pairing integrand is invariant under the a.e.
equalities `fRep =ᵐ f`, `gRep i =ᵐ g i` on the cube).

This is the periodic-on-the-nose-free entry point used by the T3 strong-VI
family, whose `u`/`Du` are `Lp.coeFn` representatives carrying only
`AEPeriodicRep` (sourced from `MemLpPer` via
`Periodic.aePeriodicRepOfMemLpPer`), NOT pointwise periodicity.

-- Adapted from the congestion (T2) sibling
-- `transport_linear_at_u_of_smooth_AEPeriodicRep`. -/
theorem integralIdentity_extend_to_W1gamma_via_smooth_density_AEPeriodicRep
    {p q : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    [ENNReal.HolderTriple p q 1]
    {a : (Fin d → ℝ) → ℝ} {b : Fin d → ((Fin d → ℝ) → ℝ)}
    (ha : MemLpPer q a) (hb : ∀ i, MemLpPer q (b i))
    {f : (Fin d → ℝ) → ℝ}
    (hf_lp : MemLpPer p f)
    (hf_rep : AEPeriodicRep f)
    {g : Fin d → ((Fin d → ℝ) → ℝ)}
    (hg_weak : ∀ i, HasWeakDerivPer i f (g i))
    (hg_lp : ∀ i, MemLpPer p (g i))
    (hg_rep : ∀ i, AEPeriodicRep (g i))
    (h_smooth : ∀ φ : SmoothPeriodic d,
      transportFunctional a b (φ : (Fin d → ℝ) → ℝ)
        (fun i => ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
          (Fin d → ℝ) → ℝ)) = 0) :
    transportFunctional a b f g = 0 := by
  classical
  haveI hfin : IsFiniteMeasure
      (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  -- The chosen periodic representatives.
  set fRep : (Fin d → ℝ) → ℝ := hf_rep.rep with hfRepdef
  set gRep : Fin d → ((Fin d → ℝ) → ℝ) := fun i => (hg_rep i).rep with hgRepdef
  -- a.e.-equalities on the cube: `fRep =ᵐ f`, `gRep i =ᵐ g i`.
  have hf_ae : fRep =ᵐ[Measure.restrict volume (UnitCube d)] f := hf_rep.ae_eq
  have hg_ae : ∀ i, gRep i =ᵐ[Measure.restrict volume (UnitCube d)] g i :=
    fun i => (hg_rep i).ae_eq
  -- `MemLpPer p` for the representatives (transfer across a.e.-equality).
  have hf_rep_lp : MemLpPer p fRep :=
    MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq hf_ae.symm hf_lp.toMemLp)
  have hg_rep_lp : ∀ i, MemLpPer p (gRep i) :=
    fun i => MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq (hg_ae i).symm (hg_lp i).toMemLp)
  -- `IsPeriodic` for the representatives (by definition of `AEPeriodicRep`).
  have hf_rep_per : IsPeriodic fRep := hf_rep.periodic
  have hg_rep_per : ∀ i, IsPeriodic (gRep i) := fun i => (hg_rep i).periodic
  -- `LocallyIntegrable` for the representatives via the periodic bridge.
  have hf_rep_loc : LocallyIntegrable fRep (volume : Measure (Fin d → ℝ)) :=
    hf_rep_lp.locallyIntegrable_of_periodic hp hf_rep_per
  have hg_rep_loc : ∀ i, LocallyIntegrable (gRep i)
      (volume : Measure (Fin d → ℝ)) :=
    fun i => (hg_rep_lp i).locallyIntegrable_of_periodic hp (hg_rep_per i)
  -- `AEStronglyMeasurable` for the representatives (from local integrability).
  have hf_rep_meas : AEStronglyMeasurable fRep
      (volume : Measure (Fin d → ℝ)) := hf_rep_loc.aestronglyMeasurable
  have hg_rep_meas : ∀ i, AEStronglyMeasurable (gRep i)
      (volume : Measure (Fin d → ℝ)) :=
    fun i => (hg_rep_loc i).aestronglyMeasurable
  -- Transfer weak derivatives from `f`/`g i` to `fRep`/`gRep i`:
  -- move the derivative slot via `congr_ae`, then the primal slot inline.
  have hweak_rep : ∀ i, HasWeakDerivPer i fRep (gRep i) := by
    intro i
    have hgRep_one : MemLpPer 1 (gRep i) :=
      MemLp.toMemLpPer ((hg_rep_lp i).toMemLp.mono_exponent hp)
    have hmid : HasWeakDerivPer i f (gRep i) :=
      (hg_weak i).congr_ae hgRep_one (hg_ae i).symm
    refine ⟨hmid.1, ?_⟩
    intro φ
    have hpair : (fun x => f x *
          ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) x)
        =ᵐ[Measure.restrict volume (UnitCube d)]
          (fun x => fRep x *
            ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x) := by
      filter_upwards [hf_ae] with x hx
      simp [hx]
    have hint :
        periodicIntegral (fun x => f x *
            ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x) =
          periodicIntegral (fun x => fRep x *
            ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x) := by
      unfold periodicIntegral
      exact integral_congr_ae hpair
    rw [hmid.integral_eq φ, hint]
  -- Apply the base lemma to the representatives.
  have hconc_rep :=
    integralIdentity_extend_to_W1gamma_via_smooth_density
      (p := p) (q := q) hp hp_top ha hb
      hf_rep_meas hf_rep_per hf_rep_loc hf_rep_lp
      hweak_rep hg_rep_meas hg_rep_per hg_rep_loc hg_rep_lp
      h_smooth
  -- Transport the conclusion back to `(f, g)` via `integral_congr_ae`.
  unfold transportFunctional periodicIntegral at hconc_rep ⊢
  have hA_eq : (∫ x in UnitCube d, a x * fRep x ∂(volume : Measure (Fin d → ℝ)))
      = ∫ x in UnitCube d, a x * f x ∂(volume : Measure (Fin d → ℝ)) := by
    refine integral_congr_ae ?_
    filter_upwards [hf_ae] with x hx
    rw [hx]
  have hB_eq : ∀ i,
      (∫ x in UnitCube d, b i x * gRep i x ∂(volume : Measure (Fin d → ℝ)))
      = ∫ x in UnitCube d, b i x * g i x ∂(volume : Measure (Fin d → ℝ)) := by
    intro i
    refine integral_congr_ae ?_
    filter_upwards [hg_ae i] with x hx
    rw [hx]
  rw [hA_eq, Finset.sum_congr rfl (fun i _ => hB_eq i)] at hconc_rep
  exact hconc_rep

end Periodic
end StationaryMFG
