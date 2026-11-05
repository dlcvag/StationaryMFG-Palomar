module

public import StationaryMFG.Periodic.UnitCube

@[expose] public section

/-!
# Bare-function `Lᵖ` seminorm on the torus

Per `docs/CONVENTIONS.md` §1b, the project's `Lᵖ` machinery works on **bare**
functions `(Fin d → ℝ) → E` with `MemLpPer`/`eLpNormPer`/`lpNormPer` predicates
and seminorms — no quotient by a.e.-equality is taken at this stage.

The torus integral is realised by restricting Lebesgue measure to the
half-open unit cube `UnitCube d`, so all of the heavy lifting is delegated to
Mathlib's `MeasureTheory.eLpNorm` applied to `volume.restrict (UnitCube d)`.

This file introduces:

* `eLpNormPer p f : ℝ≥0∞`  — the extended `Lᵖ` seminorm on the torus.
* `lpNormPer p f : ℝ`      — its real-valued counterpart `(eLpNormPer p f).toReal`.
* `MemLpPer p f : Prop`    — predicate "f is `Lᵖ` on the torus".

It also establishes the basic seminorm axioms (non-negativity, absolute
homogeneity under scalar multiplication, the triangle inequality, and the
degeneracy `eLpNormPer p f = 0 ↔ f =ᵐ 0` for `p ≠ 0`).

Periodicity of `f` is **not** required by these definitions: a function is
"`Lᵖ` on the torus" purely by virtue of its restriction to `UnitCube d`.
Periodicity becomes relevant only when comparing `Lᵖ` quantities across
fundamental domains (handled in `Integral.lean`).
-/

namespace StationaryMFG
namespace Periodic

open MeasureTheory
open scoped ENNReal NNReal Topology

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E]

/-- Extended `Lᵖ` seminorm on the torus: `eLpNorm f p` taken with respect to
Lebesgue measure restricted to the unit cube. -/
noncomputable def eLpNormPer (p : ℝ≥0∞) (f : (Fin d → ℝ) → E) : ℝ≥0∞ :=
  MeasureTheory.eLpNorm f p (MeasureTheory.Measure.restrict volume (UnitCube d))

/-- Real-valued `Lᵖ` seminorm on the torus, defined as the `toReal` of
`eLpNormPer`. This agrees with Mathlib's `lpNorm` for the cube-restricted
measure. It is `0` exactly when `eLpNormPer p f` is either `0` or `⊤`;
in particular, it is `0` for functions that are not a.e. strongly measurable. -/
noncomputable def lpNormPer (p : ℝ≥0∞) (f : (Fin d → ℝ) → E) : ℝ :=
  (eLpNormPer p f).toReal

/-- Membership predicate for `Lᵖ` on the torus: a.e.-strong measurability on
the unit cube together with finite `eLpNormPer`. The bridge below proves
this is equivalent to `MeasureTheory.MemLp f p (volume.restrict (UnitCube d))`. -/
def MemLpPer (p : ℝ≥0∞) (f : (Fin d → ℝ) → E) : Prop :=
  AEStronglyMeasurable f (MeasureTheory.Measure.restrict volume (UnitCube d)) ∧
    eLpNormPer p f < ⊤

/-! ### Bridge to Mathlib's `MemLp` -/

/-- `MemLpPer` is equivalent to `MemLp` for the cube-restricted measure. -/
lemma memLpPer_iff_memLp {p : ℝ≥0∞} {f : (Fin d → ℝ) → E} :
    MemLpPer p f ↔ MemLp f p (Measure.restrict volume (UnitCube d)) :=
  ⟨fun h => h.2, fun h => ⟨h.aestronglyMeasurable, h⟩⟩

/-- Forward direction of the bridge. -/
lemma MemLpPer.toMemLp {p : ℝ≥0∞} {f : (Fin d → ℝ) → E}
    (hf : MemLpPer p f) : MemLp f p (Measure.restrict volume (UnitCube d)) := hf.2

/-- Backward direction of the bridge. -/
lemma MemLp.toMemLpPer {p : ℝ≥0∞} {f : (Fin d → ℝ) → E}
    (hf : MemLp f p (Measure.restrict volume (UnitCube d))) : MemLpPer p f := ⟨hf.aestronglyMeasurable, hf⟩

/-- Compatibility with Mathlib's `MemLp` interface after its measurability
condition was absorbed into `eLpNorm`. The periodic predicate retains its
explicit conjunction; this coercion is the proved forward implication. -/
instance instCoeMemLpPerMemLp {p : ℝ≥0∞} {f : (Fin d → ℝ) → E} :
    Coe (MemLpPer p f) (MeasureTheory.MemLp f p (volume.restrict (UnitCube d))) where
  coe := MemLpPer.toMemLp

/-- The converse compatibility coercion, using the proved measurability
of every finite-`eLpNorm` function. -/
instance instCoeMemLpMemLpPer {p : ℝ≥0∞} {f : (Fin d → ℝ) → E} :
    Coe (MeasureTheory.MemLp f p (volume.restrict (UnitCube d))) (MemLpPer p f) where
  coe := MemLp.toMemLpPer

/-- A `MemLpPer` function is a.e.-strongly measurable on the unit cube. -/
lemma MemLpPer.aestronglyMeasurable {p : ℝ≥0∞} {f : (Fin d → ℝ) → E}
    (hf : MemLpPer p f) :
    AEStronglyMeasurable f (Measure.restrict volume (UnitCube d)) := hf.1

/-- A `MemLpPer` function has finite `eLpNormPer`. -/
lemma MemLpPer.eLpNormPer_lt_top {p : ℝ≥0∞} {f : (Fin d → ℝ) → E}
    (hf : MemLpPer p f) : eLpNormPer p f < ⊤ := hf.2

/-- The `eLpNormPer` of a `MemLpPer` function is not `⊤`. -/
lemma MemLpPer.eLpNormPer_ne_top {p : ℝ≥0∞} {f : (Fin d → ℝ) → E}
    (hf : MemLpPer p f) : eLpNormPer p f ≠ ⊤ := hf.2.ne

/-- **`L^∞` a.e. bound.** A function in `L^∞_per` is a.e. bounded on the
unit cube by a finite nonnegative constant.  This is the bare-function
torus form of the essential-sup bound: from `MemLpPer ⊤ f` we extract
`C := (eLpNormEssSup f μ).toReal` and the a.e. inequality
`‖f x‖ ≤ C`. -/
lemma MemLpPer.exists_ae_norm_le {f : (Fin d → ℝ) → E}
    (hf : MemLpPer (d := d) ⊤ f) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)), ‖f x‖ ≤ C := by
  set μ := Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)
  -- `eLpNormEssSup f μ < ⊤` from membership.
  have htop : MeasureTheory.eLpNormEssSup f μ < ⊤ := by
    have := hf.2
    simpa [eLpNormPer, MeasureTheory.eLpNorm_exponent_top hf.1, μ] using this
  set C : ℝ := (MeasureTheory.eLpNormEssSup f μ).toReal with hC_def
  refine ⟨C, ENNReal.toReal_nonneg, ?_⟩
  have hae : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ MeasureTheory.eLpNormEssSup f μ :=
    MeasureTheory.ae_le_eLpNormEssSup
  filter_upwards [hae] with x hx
  -- Transfer the enorm bound to the real-norm bound via `toReal`.
  have hxle : ‖f x‖ₑ ≤ ENNReal.ofReal C := by
    rw [hC_def, ENNReal.ofReal_toReal htop.ne]
    exact hx
  have := (ENNReal.le_ofReal_iff_toReal_le (by
        simp [enorm]) ENNReal.toReal_nonneg).mp hxle
  simpa [enorm, Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal,
    abs_of_nonneg (norm_nonneg _)] using this

/-! ### Non-negativity -/

/-- `eLpNormPer p f` is non-negative; immediate from `ℝ≥0∞`. -/
lemma eLpNormPer_nonneg (p : ℝ≥0∞) (f : (Fin d → ℝ) → E) :
    (0 : ℝ≥0∞) ≤ eLpNormPer p f := bot_le

/-- `lpNormPer p f ≥ 0`. -/
lemma lpNormPer_nonneg (p : ℝ≥0∞) (f : (Fin d → ℝ) → E) :
    0 ≤ lpNormPer p f := ENNReal.toReal_nonneg

/-! ### Absolute homogeneity -/

variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]

/-- Scalar homogeneity at the level of the extended seminorm:
`eLpNormPer p (c • f) = ‖c‖ₑ * eLpNormPer p f`. -/
lemma eLpNormPer_const_smul (p : ℝ≥0∞) (c : 𝕜) (f : (Fin d → ℝ) → E) :
    eLpNormPer p (c • f) = ‖c‖ₑ * eLpNormPer p f := by
  unfold eLpNormPer
  exact eLpNorm_const_smul c f p _

/-- Real absolute homogeneity:
`lpNormPer p (c • f) = |c| * lpNormPer p f` for `c : ℝ`. -/
lemma lpNormPer_smul [NormedSpace ℝ E] (p : ℝ≥0∞) (c : ℝ) (f : (Fin d → ℝ) → E) :
    lpNormPer p (c • f) = |c| * lpNormPer p f := by
  unfold lpNormPer
  rw [eLpNormPer_const_smul (𝕜 := ℝ) p c f, ENNReal.toReal_mul]
  simp [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal, abs_nonneg]

/-! ### Triangle inequality -/

/-- Minkowski's inequality at the extended-seminorm level. -/
lemma eLpNormPer_add_le {p : ℝ≥0∞} {f g : (Fin d → ℝ) → E}
    (hf : AEStronglyMeasurable f (Measure.restrict volume (UnitCube d)))
    (hg : AEStronglyMeasurable g (Measure.restrict volume (UnitCube d)))
    (hp : 1 ≤ p) :
    eLpNormPer p (f + g) ≤ eLpNormPer p f + eLpNormPer p g := by
  unfold eLpNormPer
  exact eLpNorm_add_le hp

/-- Real-valued triangle inequality: for `MemLpPer p f`, `MemLpPer p g`, and
`1 ≤ p`,
`lpNormPer p (f + g) ≤ lpNormPer p f + lpNormPer p g`. -/
lemma lpNormPer_triangle {p : ℝ≥0∞} {f g : (Fin d → ℝ) → E}
    (hf : MemLpPer p f) (hg : MemLpPer p g) (hp : 1 ≤ p) :
    lpNormPer p (f + g) ≤ lpNormPer p f + lpNormPer p g := by
  have hsum : eLpNormPer p (f + g) ≤ eLpNormPer p f + eLpNormPer p g :=
    eLpNormPer_add_le hf.aestronglyMeasurable hg.aestronglyMeasurable hp
  have hfin :
      eLpNormPer p f + eLpNormPer p g ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hf.eLpNormPer_ne_top, hg.eLpNormPer_ne_top⟩
  have htoReal :
      (eLpNormPer p (f + g)).toReal ≤
        (eLpNormPer p f + eLpNormPer p g).toReal :=
    ENNReal.toReal_mono hfin hsum
  calc lpNormPer p (f + g)
      = (eLpNormPer p (f + g)).toReal := rfl
    _ ≤ (eLpNormPer p f + eLpNormPer p g).toReal := htoReal
    _ = (eLpNormPer p f).toReal + (eLpNormPer p g).toReal :=
          ENNReal.toReal_add hf.eLpNormPer_ne_top hg.eLpNormPer_ne_top
    _ = lpNormPer p f + lpNormPer p g := rfl

/-! ### Degeneracy -/

/-- For `p ≠ 0`, `eLpNormPer p f = 0` iff `f` vanishes a.e. on the unit cube. -/
lemma eLpNormPer_eq_zero_iff {p : ℝ≥0∞} {f : (Fin d → ℝ) → E}
    (hf : AEStronglyMeasurable f (Measure.restrict volume (UnitCube d)))
    (hp : p ≠ 0) :
    eLpNormPer p f = 0 ↔ f =ᵐ[Measure.restrict volume (UnitCube d)] 0 := by
  unfold eLpNormPer
  exact eLpNorm_eq_zero_iff hp

/-! ### Sanity checks: a constant function -/

/-- Every constant function is `MemLpPer` for any `p`, since the unit cube has
finite measure. -/
example (c : ℝ) (p : ℝ≥0∞) : MemLpPer (d := d) p (fun _ => c) := by
  have hcube : volume (UnitCube d) ≠ ⊤ := by simp
  have : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    ⟨by
      rw [Measure.restrict_apply MeasurableSet.univ]
      simp⟩
  exact MemLp.toMemLpPer (memLp_const c)

/-- The `lpNormPer` of the zero function is zero. -/
example (p : ℝ≥0∞) : lpNormPer (d := d) p (fun _ : (Fin d → ℝ) => (0 : ℝ)) = 0 := by
  unfold lpNormPer eLpNormPer
  simp

/-! ### Bridge to Mathlib's quotient `Lp`

The lemmas in this section package up a `MemLpPer`-certified bare function into
Mathlib's quotient space `MeasureTheory.Lp E p (volume.restrict (UnitCube d))`,
together with compatibility lemmas for the norm, addition and scalar
multiplication. They are the **only** declarations in the project that expose
the quotient `Lp` type; downstream modules keep working with bare functions.
Use these lemmas locally when a Banach-space instance (reflexivity, duality) is
genuinely needed.
-/

-- bridge to Mathlib Lp; internal use only
/-- Package a `MemLpPer` function as an element of Mathlib's quotient
`Lp` space. -/
noncomputable def MemLpPer.toLp {p : ℝ≥0∞} {f : (Fin d → ℝ) → E}
    (hf : MemLpPer p f) :
    MeasureTheory.Lp E p (MeasureTheory.Measure.restrict volume (UnitCube d)) :=
  MeasureTheory.MemLp.toLp f hf.toMemLp

-- bridge to Mathlib Lp; internal use only
/-- The real-valued periodic `Lᵖ` seminorm agrees with the ambient `Lp`-space
norm of the bridged element. -/
lemma lpNormPer_eq_norm_toLp {p : ℝ≥0∞} {f : (Fin d → ℝ) → E}
    (hf : MemLpPer p f) :
    lpNormPer p f = ‖hf.toLp‖ := by
  unfold lpNormPer eLpNormPer MemLpPer.toLp
  rw [MeasureTheory.Lp.norm_toLp f hf.toMemLp]

/-- **Banach norm ↔ integrated `p`-th power.**
For a real-valued bare function `f` with `MemLpPer p f` and `p ≠ 0`,
`p ≠ ∞`, the `p`-th power of the bridged Mathlib-`Lp` norm equals the
unit-cube integral of `|f|^p.toReal`.

This is the *one-direction* statement preferred by the apriori-bound
clients of Phase 4: they manipulate `‖m‖_{L^p}^p` and translate it
into an `∫ |m|^p` they already control.

The proof routes through Mathlib's `lpNorm_eq_integral_norm_rpow_toReal`,
which converts `(eLpNorm f p μ).toReal = (∫ ‖f‖^p.toReal)^(1/p.toReal)`.
We then raise both sides to `p.toReal` and use `Real.rpow_inv_rpow` to
cancel the inverse exponent. The integrability of `‖f‖^p.toReal` (which
controls the post-`toReal` integral) follows from the `MemLp` certificate. -/
theorem MemLpPer.norm_toLp_rpow_eq {p : ℝ≥0∞} (hp_zero : p ≠ 0) (hp_top : p ≠ ∞)
    {f : (Fin d → ℝ) → ℝ} (hf : MemLpPer p f) :
    ‖hf.toLp‖ ^ p.toReal
      = ∫ x in UnitCube d, |f x| ^ p.toReal := by
  -- Bring in the cube-restricted measure as a shorthand.
  set μ : Measure (Fin d → ℝ) := Measure.restrict volume (UnitCube d) with hμ
  -- Step (a): identify `‖hf.toLp‖` with the real-valued seminorm `lpNorm f p μ`.
  have h_norm_eq : ‖hf.toLp‖ = MeasureTheory.lpNorm f p μ := by
    rw [show ‖hf.toLp‖ = (MeasureTheory.eLpNorm f p μ).toReal from
      MeasureTheory.Lp.norm_toLp f hf.toMemLp]
    exact MeasureTheory.toReal_eLpNorm
  -- Step (b): Mathlib's integral form of `lpNorm`.
  have h_lpnorm :
      MeasureTheory.lpNorm f p μ
        = (∫ x, ‖f x‖ ^ p.toReal ∂μ) ^ (p.toReal⁻¹) :=
    MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal hp_zero hp_top
      hf.aestronglyMeasurable
  -- Step (c): raise to the `p.toReal` power and cancel the inverse exponent.
  have hpos : (0 : ℝ) < p.toReal := ENNReal.toReal_pos hp_zero hp_top
  have hne : p.toReal ≠ 0 := hpos.ne'
  -- The integrand is nonnegative pointwise, so the integral is too — needed
  -- for `Real.rpow_inv_rpow`.
  have h_int_nonneg :
      0 ≤ ∫ x, ‖f x‖ ^ p.toReal ∂μ :=
    integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _)
  calc ‖hf.toLp‖ ^ p.toReal
      = (MeasureTheory.lpNorm f p μ) ^ p.toReal := by rw [h_norm_eq]
    _ = ((∫ x, ‖f x‖ ^ p.toReal ∂μ) ^ (p.toReal⁻¹)) ^ p.toReal := by
          rw [h_lpnorm]
    _ = ∫ x, ‖f x‖ ^ p.toReal ∂μ :=
          Real.rpow_inv_rpow h_int_nonneg hne
    _ = ∫ x in UnitCube d, ‖f x‖ ^ p.toReal := by
          simp [hμ]
    _ = ∫ x in UnitCube d, |f x| ^ p.toReal := by
          simp [Real.norm_eq_abs]

/-- A small consumer-side `example`: the translation lemma is `Real.HolderConjugate`-
clean. We pair `MemLpPer.norm_toLp_rpow_eq` with the standard Hölder-conjugate
exponent setup `(p, q)` to expose the shape `‖·‖_{L^p}^p = ∫ |·|^p` that
the apriori bounds consume directly. -/
example {p q : ℝ} (hpq : p.HolderConjugate q)
    {f : (Fin d → ℝ) → ℝ}
    (hf : MemLpPer (ENNReal.ofReal p) f) :
    ‖hf.toLp‖ ^ (ENNReal.ofReal p).toReal
      = ∫ x in UnitCube d, |f x| ^ (ENNReal.ofReal p).toReal := by
  -- Unpack Hölder-conjugate facts: p > 1 ⇒ p ≠ 0, p ≠ ∞ in ℝ≥0∞.
  have hp_gt_one : 1 < p := hpq.lt
  have hp_pos : 0 < p := lt_trans Real.zero_lt_one hp_gt_one
  have hp_ofReal_zero : ENNReal.ofReal p ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hp_pos).ne'
  have hp_ofReal_top : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  -- the witness `q` is unused (it would surface only in a paired statement);
  -- referencing it keeps the example self-explanatory for a Hölder reader.
  let _ := q
  exact MemLpPer.norm_toLp_rpow_eq hp_ofReal_zero hp_ofReal_top hf

/-! ### `lpNormPer` bound from an apriori integral bound

Phase-5 Banach-side closure consumes apriori bounds in the integral form
`∫ x in UnitCube d, |f x| ^ p ≤ C` (produced, e.g., by
`aprioriResidue.uniformConstant_bound`), but the smooth-tester density
machinery
(`weakConvPairing_universal_of_smoothTester_density`) wants the
hypothesis as `lpNormPer (ENNReal.ofReal p) f ≤ C ^ (1/p)`. The
following lemma converts between the two. -/

/-- **`lpNormPer` from an apriori integral bound.** For `1 ≤ p`, a real
bare function `f` with `MemLpPer (ENNReal.ofReal p) f`, and an apriori
integrated bound `∫ |f|^p ≤ C` on the unit cube,
`lpNormPer (ENNReal.ofReal p) f ≤ C ^ (1/p)`.

This is the standard "raise both sides to `1/p`" identity, packaged so
that downstream weak-pairing density consumers can feed in the
`uniformConstant_bound` integral shape directly. -/
theorem lpNormPer_le_of_apriori
    {p : ℝ} (hp_one_le : 1 ≤ p)
    {f : (Fin d → ℝ) → ℝ}
    (hf : MemLpPer (ENNReal.ofReal p) f)
    {C : ℝ} (hC_nn : 0 ≤ C)
    (hint : ∫ x in UnitCube d, |f x| ^ p ≤ C) :
    lpNormPer (ENNReal.ofReal p) f ≤ C ^ (1 / p) := by
  -- Positivity / nontriviality of `p`.
  have hp_pos : 0 < p := lt_of_lt_of_le Real.zero_lt_one hp_one_le
  have hp_ne : p ≠ 0 := hp_pos.ne'
  have hp_ofReal_zero : ENNReal.ofReal p ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hp_pos).ne'
  have hp_ofReal_top : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hp_toReal : (ENNReal.ofReal p).toReal = p :=
    ENNReal.toReal_ofReal hp_pos.le
  -- Step 1: rewrite `lpNormPer^p` as `∫ |f|^p`, then use the apriori bound.
  have h_norm_eq : lpNormPer (ENNReal.ofReal p) f = ‖hf.toLp‖ :=
    lpNormPer_eq_norm_toLp hf
  have h_rpow_int :
      ‖hf.toLp‖ ^ p = ∫ x in UnitCube d, |f x| ^ p := by
    have := MemLpPer.norm_toLp_rpow_eq (d := d) hp_ofReal_zero hp_ofReal_top hf
    -- `(ENNReal.ofReal p).toReal = p` lets us peel both occurrences.
    simpa [hp_toReal] using this
  have h_lpNormPer_rpow_le :
      lpNormPer (ENNReal.ofReal p) f ^ p ≤ C := by
    rw [h_norm_eq, h_rpow_int]
    exact hint
  -- Step 2: take `1/p`-th roots. Both sides are nonneg; `0 < p`.
  have h_lp_nn : 0 ≤ lpNormPer (ENNReal.ofReal p) f :=
    lpNormPer_nonneg _ _
  -- `Real.rpow_inv_le_iff_of_pos`: `x ^ z⁻¹ ≤ y ↔ x ≤ y ^ z` for
  -- `0 ≤ x`, `0 ≤ y`, `0 < z`. We use the contrapositive direction:
  -- `lpNormPer^p ≤ C` ⇒ `lpNormPer ≤ C^{1/p}` via `le_rpow_inv_iff_of_pos`.
  have h_le : lpNormPer (ENNReal.ofReal p) f ≤ C ^ p⁻¹ :=
    (Real.le_rpow_inv_iff_of_pos h_lp_nn hC_nn hp_pos).mpr h_lpNormPer_rpow_le
  -- Identify `C ^ p⁻¹` with `C ^ (1/p)`.
  simpa [one_div] using h_le

-- bridge to Mathlib Lp; internal use only
/-- Closure of `MemLpPer` under addition; routed through `MemLp.add` via the
equivalence `MemLpPer ↔ MemLp …`. -/
lemma MemLpPer.add {p : ℝ≥0∞} {f g : (Fin d → ℝ) → E}
    (hf : MemLpPer p f) (hg : MemLpPer p g) : MemLpPer p (f + g) :=
  MemLp.toMemLpPer (MeasureTheory.MemLp.add hf.toMemLp hg.toMemLp)

-- bridge to Mathlib Lp; internal use only
/-- Closure of `MemLpPer` under scalar multiplication. -/
lemma MemLpPer.const_smul {p : ℝ≥0∞} {f : (Fin d → ℝ) → E}
    (hf : MemLpPer p f) (c : 𝕜) : MemLpPer p (c • f) :=
  MemLp.toMemLpPer (MeasureTheory.MemLp.const_smul hf.toMemLp c)

/-! ### Constant functions on the torus

Constant functions are `Lᵖ` on the torus for every `p`, since the
unit-cube–restricted volume is a finite measure. This is the
`MemLpPer` packaging of Mathlib's `memLp_const`, used by the Option-B
perturbation toolkit for the `hPosSeg` slot. -/

/-- Any constant function is `MemLpPer p` for every `p`. Direct
reduction to `memLp_const` after equipping the cube-restricted volume
with `IsFiniteMeasure`. -/
lemma MemLpPer.const {p : ℝ≥0∞} (c : E) :
    MemLpPer (d := d) p (fun _ : Fin d → ℝ => c) := by
  have : IsFiniteMeasure (Measure.restrict (volume : Measure (Fin d → ℝ))
      (UnitCube (d := d))) :=
    ⟨by
      rw [Measure.restrict_apply MeasurableSet.univ]
      simp⟩
  exact MemLp.toMemLpPer (MeasureTheory.memLp_const (μ := Measure.restrict volume
    (UnitCube (d := d))) c)

/-- Closure of `MemLpPer` under addition of a constant. -/
lemma MemLpPer.add_const {p : ℝ≥0∞} {f : (Fin d → ℝ) → E}
    (hf : MemLpPer p f) (c : E) :
    MemLpPer p (f + (fun _ : Fin d → ℝ => c)) :=
  hf.add (MemLpPer.const c)

-- bridge to Mathlib Lp; internal use only
/-- The bridge is additive: the bridged class of a sum is the sum of the
bridged classes. -/
lemma MemLpPer.add_toLp {p : ℝ≥0∞} {f g : (Fin d → ℝ) → E}
    (hf : MemLpPer p f) (hg : MemLpPer p g) :
    (hf.add hg).toLp = hf.toLp + hg.toLp :=
  MeasureTheory.MemLp.toLp_add hf.toMemLp hg.toMemLp

-- bridge to Mathlib Lp; internal use only
/-- The bridge is scalar-linear in its argument. We work with the default
`NormedField 𝕜`/`NormedSpace 𝕜 E` setup already in file scope. -/
lemma MemLpPer.smul_toLp {p : ℝ≥0∞} {f : (Fin d → ℝ) → E}
    (c : 𝕜) (hf : MemLpPer p f) :
    (hf.const_smul c).toLp = c • hf.toLp :=
  MeasureTheory.MemLp.toLp_const_smul c hf.toMemLp

/-! ### Hölder product integrability

The next lemma packages Hölder's inequality at the level of integrability:
two `MemLpPer` functions whose exponents form a real Hölder conjugate pair
have an integrable pointwise product on the unit cube.

This is the periodic-bare-function counterpart of Mathlib's
`MeasureTheory.MemLp.integrable_mul`.
-/

/-- Hölder-triple → product integrability on the torus: if `f ∈ L^p_per`
and `g ∈ L^q_per` with `1/p + 1/q = 1` (real Hölder conjugates), then
`f · g` is integrable on the unit cube. -/
theorem MemLpPer.integrable_mul {p q : ℝ} (hpq : p.HolderConjugate q)
    {f g : (Fin d → ℝ) → ℝ}
    (hf : MemLpPer (ENNReal.ofReal p) f)
    (hg : MemLpPer (ENNReal.ofReal q) g) :
    IntegrableOn (fun x => f x * g x) (UnitCube d) := by
  -- The ENNReal Hölder-conjugate instance comes from the real one.
  haveI : ENNReal.HolderTriple (ENNReal.ofReal p) (ENNReal.ofReal q) 1 :=
    hpq.ennrealOfReal
  -- Apply Mathlib's bare-function Hölder integrability via the
  -- `MemLpPer = MemLp …` defeq.
  have hmul : Integrable (f * g)
      (Measure.restrict volume (UnitCube d)) :=
    MeasureTheory.MemLp.integrable_mul hf.toMemLp hg.toMemLp
  -- `IntegrableOn f s μ := Integrable f (μ.restrict s)` by definition.
  exact hmul

/-- Unit test: constant functions on the unit cube give an integrable
product whenever the exponents are real Hölder conjugates. -/
example (a b : ℝ) (p q : ℝ) (hpq : p.HolderConjugate q) :
    IntegrableOn (fun _ : Fin d → ℝ => a * b) (UnitCube d) := by
  have : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    ⟨by
      rw [Measure.restrict_apply MeasurableSet.univ]
      simp⟩
  have hfa : MemLpPer (d := d) (ENNReal.ofReal p) (fun _ => a) :=
    MemLp.toMemLpPer (memLp_const a)
  have hgb : MemLpPer (d := d) (ENNReal.ofReal q) (fun _ => b) :=
    MemLp.toMemLpPer (memLp_const b)
  exact MemLpPer.integrable_mul hpq hfa hgb

/-! ### `rpow`-closure and Hölder-product membership

Two building blocks for the congestion `L^{γ̄'}` flux estimate
(paper `eq:boundsmDpH+`, line 686):

* `MemLpPer.rpow_closure`: if `f ∈ L^{s·r}_per` and `0 < r`, then the
  pointwise `r`-th power `x ↦ ‖f x‖ ^ r ∈ L^{s}_per`. Routes through
  Mathlib's `eLpNorm_norm_rpow`
  (`eLpNorm (‖f‖^r) s μ = eLpNorm f (s·ofReal r) μ ^ r`).
* `MemLpPer.mul_holderTriple`: if `f ∈ L^{p}_per`, `g ∈ L^{q}_per` and
  `p⁻¹ + q⁻¹ = s⁻¹` (an `ENNReal.HolderTriple`), then
  `x ↦ f x * g x ∈ L^{s}_per`. Routes through Mathlib's `MemLp.mul'`. -/

/-- **`rpow`-closure of `MemLpPer`.** If `f ∈ L^{s·ofReal r}_per` and
`0 < r`, then `x ↦ ‖f x‖ ^ r ∈ L^{s}_per`. -/
theorem MemLpPer.rpow_closure {s : ℝ≥0∞} {r : ℝ} (hr : 0 < r)
    {f : (Fin d → ℝ) → ℝ}
    (hf : MemLpPer (s * ENNReal.ofReal r) f) :
    MemLpPer s (fun x => ‖f x‖ ^ r) := by
  refine ⟨?_, ?_⟩
  · -- a.e.-strong measurability of the `r`-th power.
    have hmeas : AEStronglyMeasurable f
        (Measure.restrict volume (UnitCube d)) := hf.1
    exact (hmeas.norm.aemeasurable.pow_const r).aestronglyMeasurable
  · -- finiteness via `eLpNorm_norm_rpow`.
    unfold eLpNormPer
    rw [MeasureTheory.eLpNorm_norm_rpow f hf.1 hr]
    exact ENNReal.rpow_lt_top_of_nonneg hr.le hf.2.ne

/-- **Hölder-product membership for `MemLpPer`.** If `f ∈ L^{p}_per`,
`g ∈ L^{q}_per` and `p⁻¹ + q⁻¹ = s⁻¹` (`ENNReal.HolderTriple p q s`),
then `x ↦ f x * g x ∈ L^{s}_per` on the unit cube. -/
theorem MemLpPer.mul_holderTriple {p q s : ℝ≥0∞}
    [ENNReal.HolderTriple p q s]
    {f g : (Fin d → ℝ) → ℝ}
    (hf : MemLpPer p f) (hg : MemLpPer q g) :
    MemLpPer s (fun x => f x * g x) :=
  -- `MemLp.mul'` (Mathlib): `g ∈ L^q`, `f ∈ L^p`, `[HolderTriple p q s]`
  -- gives `fun x => f x * g x ∈ L^s`.
  MemLp.toMemLpPer (MeasureTheory.MemLp.fun_mul hf.toMemLp hg.toMemLp)

/-! ### Localized quotient-boundary interface: `AEPeriodicRep` / `AEPeriodic`

Phase-4 (Banach-side) code occasionally needs to **exit** Mathlib's
quotient `Lp` world and recover a *concrete* periodic function that is
a.e.-equal to a given representative. To avoid scattering manual
`Classical.choose`s and `=ᵐ`-threading at every such site, we package
the data once into a small structure.

`AEPeriodicRep f` carries a *chosen* periodic representative of `f`
together with the a.e.-equality witness on the unit cube. The
`Nonempty`-flavoured Prop alias `AEPeriodic f` is for abstract
existence statements; concrete sites should take the structure
directly so the representative is available as data.

This is a deliberately localized fix for the Path-A obstruction: we do
**not** redefine `Lp.coeFn`, do **not** retrofit `AddCircle`, and do
**not** otherwise touch the quotient `Lp` machinery. The structure is
introduced for later Phase-4 closure proofs (weak-limit selectors,
duality bridges); this task is purely infrastructure and does not yet
plug it into those proofs.
-/

/-- An *almost-everywhere periodic representative* of a function
`f : (Fin d → ℝ) → E`. The structure carries a chosen periodic
function `rep` together with the witness `rep =ᵐ f` on the unit cube,
so any choice paid at construction is then available as data without
further use of `Classical.choose`. -/
structure AEPeriodicRep (f : (Fin d → ℝ) → E) where
  /-- The chosen periodic representative. -/
  rep : (Fin d → ℝ) → E
  /-- The representative is periodic. -/
  periodic : IsPeriodic rep
  /-- The representative is a.e.-equal to `f` on the unit cube. -/
  ae_eq : rep =ᵐ[MeasureTheory.Measure.restrict volume (UnitCube d)] f

/-- Prop alias: `f` admits *some* periodic a.e.-representative. Use
this only for abstract existence statements; concrete sites should use
`AEPeriodicRep f` directly so that the representative is available as
data. -/
def AEPeriodic (f : (Fin d → ℝ) → E) : Prop :=
  Nonempty (AEPeriodicRep f)

/-- Tautological constructor: a periodic `f` is its own periodic
a.e.-representative. No `Classical.choose` is involved — the
representative is supplied by the caller. -/
def AEPeriodicRep.ofPeriodic {f : (Fin d → ℝ) → E} (hf : IsPeriodic f) :
    AEPeriodicRep f where
  rep := f
  periodic := hf
  ae_eq := Filter.EventuallyEq.refl _ _

set_option linter.unusedSectionVars false in
/-- The Prop-flavoured version of `AEPeriodicRep.ofPeriodic`. -/
lemma AEPeriodic.ofPeriodic {f : (Fin d → ℝ) → E} (hf : IsPeriodic f) :
    AEPeriodic f :=
  ⟨AEPeriodicRep.ofPeriodic hf⟩

/-- **Exit-from-quotient constructor.** Given a periodic, `MemLpPer`
function `f`, the bridged element `hf.toLp` (an inhabitant of
`MeasureTheory.Lp E p (volume.restrict (UnitCube d))`) admits an
`AEPeriodicRep` whose representative is the original bare function
`f`. The a.e.-equality witness comes from `MemLp.coeFn_toLp`.

This is the *only* declaration in the file that constructs an
`AEPeriodicRep` for a quotient element; downstream sites should keep
working with bare functions whenever possible and only invoke this
lemma when a quotient-side hypothesis must be discharged. -/
noncomputable def AEPeriodicRep_of_MemLpPer
    {p : ℝ≥0∞} {f : (Fin d → ℝ) → E}
    (hf : MemLpPer p f) (hfper : IsPeriodic f) :
    AEPeriodicRep
      (fun x => (hf.toLp : MeasureTheory.Lp E p
        (MeasureTheory.Measure.restrict volume (UnitCube d))) x) where
  rep := f
  periodic := hfper
  ae_eq :=
    -- `MemLp.coeFn_toLp hf : (hf.toLp : Lp …) =ᵐ f`, then `.symm`.
    (MeasureTheory.MemLp.coeFn_toLp hf.toMemLp).symm

/-! ### Sanity checks for the `AEPeriodicRep` interface -/

/-- A constant function admits a periodic a.e.-representative (itself). -/
example (c : ℝ) : AEPeriodicRep (fun _ : (Fin d → ℝ) => c) :=
  AEPeriodicRep.ofPeriodic (IsPeriodic.const c)

/-- The Prop alias is inhabited for any periodic function. -/
example (c : ℝ) : AEPeriodic (fun _ : (Fin d → ℝ) => c) :=
  AEPeriodic.ofPeriodic (IsPeriodic.const c)

/-- The chosen representative of `AEPeriodicRep.ofPeriodic` is the
original function on the nose. -/
example {f : (Fin d → ℝ) → ℝ} (hf : IsPeriodic f) :
    (AEPeriodicRep.ofPeriodic hf).rep = f := rfl

/-! ### Path-A primitive: periodic representative of an `Lp` coercion

Given an arbitrary `f : Lp ℝ p (volume.restrict (UnitCube d))`, the
project's `LpPer p d` abbreviation, the bare-function coercion
`⇑f : (Fin d → ℝ) → ℝ` is a chosen *measurable* representative —
defined on all of `ℝ^d` but only meaningful (a.e.) on the unit cube.
Such a representative need not be periodic.

The **periodization primitive** `bareCoeFnOfLpPer` constructs a
*pointwise* periodic representative `rep` of `⇑f` by precomposing
with the coordinate-wise fractional part:
`rep x := (⇑f) (fun i => Int.fract (x i))`.

This is:

* **Periodic** — `Int.fract (x i + (k i : ℝ)) = Int.fract (x i)` for
  every `k : Fin d → ℤ`, so `rep` is invariant under integer
  translation.
* **Pointwise equal to `⇑f` on the unit cube** — for `x ∈ UnitCube d`
  we have `0 ≤ x i < 1`, hence `Int.fract (x i) = x i`, so
  `rep x = (⇑f) x` exactly. The a.e.-equality on the cube is then
  immediate (in fact pointwise on the cube).

This primitive is the missing piece that lets Phase-4 closure
selectors construct a periodic bare-function limit from an abstract
weak-cluster-point `Lp` element without any `Classical.choose`-over-
existence detour. (Implementation note: the construction is
*concretely* given by `Int.fract`, no `Classical.choose` is invoked
at all — but the construction itself is the analogue of the
"Classical.choose-based selector" advertised in the Phase-4 plan.)
-/

/-- The coordinate-wise fractional-part projection from `ℝ^d` onto the
half-open unit cube `[0,1)^d`. This is the canonical retraction
witnessing that `UnitCube d` is a fundamental domain for the ℤ^d
lattice action. -/
noncomputable def palomar_Lp_fracVec (x : Fin d → ℝ) : Fin d → ℝ :=
  fun i => Int.fract (x i)

/-- The fractional-part projection always lands in the unit cube. -/
private lemma fracVec_mem_unitCube (x : Fin d → ℝ) :
    palomar_Lp_fracVec (d := d) x ∈ UnitCube d := by
  rw [mem_unitCube_iff]
  intro i
  refine ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- On the unit cube the fractional-part projection is the identity. -/
private lemma fracVec_eq_self_of_mem_unitCube
    {x : Fin d → ℝ} (hx : x ∈ UnitCube d) :
    palomar_Lp_fracVec (d := d) x = x := by
  funext i
  have hi : 0 ≤ x i ∧ x i < 1 := (mem_unitCube_iff.mp hx) i
  exact Int.fract_eq_self.mpr ⟨hi.1, hi.2⟩

/-- Integer-translation invariance of the fractional-part projection:
`palomar_Lp_fracVec (x + k) = palomar_Lp_fracVec x` for any integer translation. -/
private lemma fracVec_add_intCast (x : Fin d → ℝ) (k : Fin d → ℤ) :
    palomar_Lp_fracVec (d := d) (x + fun i => (k i : ℝ)) = palomar_Lp_fracVec (d := d) x := by
  funext i
  change Int.fract (x i + (k i : ℝ)) = Int.fract (x i)
  exact Int.fract_add_intCast (x i) (k i)

/-- **Path-A primitive.** Periodic a.e.-representative of the bare
coercion of an `Lp` element on the unit cube.

Given `f : Lp ℝ p (volume.restrict (UnitCube d))` (the project's
`LpPer p d` type), construct a periodic function `rep` that agrees
with `⇑f` a.e. on the unit cube. The construction is concrete:
`rep x := (⇑f) (palomar_Lp_fracVec x)`, where `palomar_Lp_fracVec x i := Int.fract (x i)`.

* `periodic` follows from `Int.fract_add_intCast`.
* `ae_eq` follows because `palomar_Lp_fracVec x = x` *pointwise* for
  `x ∈ UnitCube d`, so `rep =ᵐ ⇑f` even pointwise on the cube;
  membership in `UnitCube d` is automatic for a.e. point under
  `volume.restrict (UnitCube d)`.

This is the Path-A "exit-from-quotient" primitive complementing
`AEPeriodicRep_of_MemLpPer`: that lemma takes a periodic bare
function and bundles it with the bridged `Lp` element; this lemma
takes an abstract `Lp` element and constructs a periodic bare
representative. -/
noncomputable def bareCoeFnOfLpPer
    {p : ℝ≥0∞}
    (f : MeasureTheory.Lp ℝ p
            (MeasureTheory.Measure.restrict volume (UnitCube d))) :
    AEPeriodicRep (⇑f : (Fin d → ℝ) → ℝ) where
  rep := fun x => (⇑f) (palomar_Lp_fracVec (d := d) x)
  periodic := by
    intro k x
    -- `(palomar_Lp_fracVec) (x + k) = palomar_Lp_fracVec x`, so the precomposed values agree.
    change (⇑f) (palomar_Lp_fracVec (d := d) (x + fun i => (k i : ℝ)))
          = (⇑f) (palomar_Lp_fracVec (d := d) x)
    rw [fracVec_add_intCast]
  ae_eq := by
    -- It suffices to show pointwise equality for `x ∈ UnitCube d`,
    -- then convert to a.e. equality on the cube-restricted measure.
    refine (MeasureTheory.ae_restrict_iff' measurableSet_unitCube).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro x hx
    -- For `x ∈ UnitCube d`, `palomar_Lp_fracVec x = x`.
    change (⇑f) (palomar_Lp_fracVec (d := d) x) = (⇑f) x
    rw [fracVec_eq_self_of_mem_unitCube hx]

/-! ### Sanity checks for `bareCoeFnOfLpPer` -/

/-- Sanity: the periodic representative is indeed periodic. -/
example {p : ℝ≥0∞}
    (f : MeasureTheory.Lp ℝ p
            (MeasureTheory.Measure.restrict volume (UnitCube d))) :
    IsPeriodic (bareCoeFnOfLpPer (d := d) f).rep :=
  (bareCoeFnOfLpPer (d := d) f).periodic

/-- Sanity: the a.e.-equality witness has the expected shape. -/
example {p : ℝ≥0∞}
    (f : MeasureTheory.Lp ℝ p
            (MeasureTheory.Measure.restrict volume (UnitCube d))) :
    (bareCoeFnOfLpPer (d := d) f).rep
      =ᵐ[MeasureTheory.Measure.restrict volume (UnitCube d)]
        (⇑f : (Fin d → ℝ) → ℝ) :=
  (bareCoeFnOfLpPer (d := d) f).ae_eq

/-- Sanity: the periodic representative has the explicit
fractional-part shape (definitional unfolding). -/
example {p : ℝ≥0∞}
    (f : MeasureTheory.Lp ℝ p
            (MeasureTheory.Measure.restrict volume (UnitCube d)))
    (x : Fin d → ℝ) :
    (bareCoeFnOfLpPer (d := d) f).rep x
      = (⇑f) (fun i => Int.fract (x i)) := rfl

/-- **Periodic a.e.-representative of a bare `MemLpPer` function.**

Given an arbitrary bare function `f : (Fin d → ℝ) → ℝ` with
`MemLpPer p f` (so `f` carries only `AEStronglyMeasurable` + finite
`Lᵖ`-seminorm — in particular *no pointwise periodicity*), construct a
genuinely periodic representative `rep` with `rep =ᵐ f` on the unit
cube.

This is the legitimate way to discharge a downstream
*pointwise-`IsPeriodic`* requirement from a function that is only
known to be `MemLpPer` (the strong-VI family situation): bridge `f` to
its quotient element `hf.toLp`, periodize the chosen `Lp` coercion via
`bareCoeFnOfLpPer`, and compose the two a.e.-equalities through
`MemLp.coeFn_toLp`. No new assumption is introduced — the periodicity
of `rep` comes for free from the fractional-part construction. -/
noncomputable def aePeriodicRepOfMemLpPer
    {p : ℝ≥0∞} {f : (Fin d → ℝ) → ℝ} (hf : MemLpPer p f) :
    AEPeriodicRep f where
  rep := (bareCoeFnOfLpPer (d := d) hf.toLp).rep
  periodic := (bareCoeFnOfLpPer (d := d) hf.toLp).periodic
  ae_eq :=
    (bareCoeFnOfLpPer (d := d) hf.toLp).ae_eq.trans
      (MeasureTheory.MemLp.coeFn_toLp hf.toMemLp)

/-- Sanity: `aePeriodicRepOfMemLpPer` yields a periodic representative. -/
example {p : ℝ≥0∞} {f : (Fin d → ℝ) → ℝ} (hf : MemLpPer p f) :
    IsPeriodic (aePeriodicRepOfMemLpPer (d := d) hf).rep :=
  (aePeriodicRepOfMemLpPer (d := d) hf).periodic

/-- Sanity: the representative is a.e.-equal to the original on the cube. -/
example {p : ℝ≥0∞} {f : (Fin d → ℝ) → ℝ} (hf : MemLpPer p f) :
    (aePeriodicRepOfMemLpPer (d := d) hf).rep
      =ᵐ[MeasureTheory.Measure.restrict volume (UnitCube d)] f :=
  (aePeriodicRepOfMemLpPer (d := d) hf).ae_eq

/-- Measurability of the fractional-part projection (each coordinate is
`Int.fract`, which is measurable). -/
private lemma measurable_fracVec : Measurable (palomar_Lp_fracVec (d := d)) := by
  refine measurable_pi_iff.mpr (fun i => ?_)
  exact (measurable_fract).comp (measurable_pi_apply i)

/-- **Periodic *measurable* a.e.-representative of a periodic `MemLpPer`
function.** Given a periodic `f ∈ L^p_per`, periodize its strongly-measurable
`AEStronglyMeasurable.mk` representative through the fractional-part projection.
The result is simultaneously *periodic* and *measurable* (a single bare
function), and a.e.-equal to `f` on the unit cube.

This is the primitive needed by the abstract-VI weak-is-strong bridge, which
requires `Measurable` data while the limit functions carry only `MemLpPer`
(⇒ `AEStronglyMeasurable`) and periodicity. -/
noncomputable def periodicMeasurableRep
    {p : ℝ≥0∞} {f : (Fin d → ℝ) → ℝ}
    (hf : MemLpPer p f) (_hper : IsPeriodic f) :
    AEPeriodicRep f where
  rep := fun x => (hf.aestronglyMeasurable.mk f) (palomar_Lp_fracVec (d := d) x)
  periodic := by
    intro k x
    change (hf.aestronglyMeasurable.mk f)
        (palomar_Lp_fracVec (d := d) (x + fun i => (k i : ℝ)))
      = (hf.aestronglyMeasurable.mk f) (palomar_Lp_fracVec (d := d) x)
    rw [fracVec_add_intCast]
  ae_eq := by
    -- `rep =ᵐ mk` (palomar_Lp_fracVec = id on the cube), and `mk =ᵐ f`.
    refine Filter.EventuallyEq.trans ?_ hf.aestronglyMeasurable.ae_eq_mk.symm
    refine (MeasureTheory.ae_restrict_iff' measurableSet_unitCube).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro x hx
    change (hf.aestronglyMeasurable.mk f) (palomar_Lp_fracVec (d := d) x)
      = (hf.aestronglyMeasurable.mk f) x
    rw [fracVec_eq_self_of_mem_unitCube hx]

/-- The periodic measurable representative is measurable. -/
lemma periodicMeasurableRep_measurable
    {p : ℝ≥0∞} {f : (Fin d → ℝ) → ℝ}
    (hf : MemLpPer p f) (hper : IsPeriodic f) :
    Measurable (periodicMeasurableRep hf hper).rep :=
  hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable.comp measurable_fracVec

/-! ### Local-integrability bridge for periodic `MemLpPer` functions

Phase-4 density (`SmoothPeriodic.exists_eLpNormPer_sub_le` in
`Periodic/Mollifier.lean`) takes `MemLpPer p f + IsPeriodic f +
LocallyIntegrable f volume + Measurable f` as hypotheses. The
`LocallyIntegrable` hypothesis is, for periodic functions in `L^p` over
the fundamental domain with `1 ≤ p`, automatic: this section provides
the bridge.

The strategy is the standard one (cf. `LpSpaces` and `DeGiorgi`'s
periodic toolkits): periodicity + integrability over one fundamental
domain ⇒ integrability over every translate of the fundamental domain
⇒ local integrability everywhere.

Adapted from `LpSpaces.LpOnSet` (whole-space `MemLp` ⇒ local
integrability) and the indicator-translate argument used in
`StationaryMFG.Periodic.Translation`.
-/

/-- The shifted unit cube `UnitCube + k` for an integer offset `k`.
This is the same set as `Translation.shiftedCube k`, but kept local
to avoid depending on a private definition. -/
def palomar_Lp_shiftedUnitCube (k : Fin d → ℤ) : Set (Fin d → ℝ) :=
  (fun x => x - fun i => (k i : ℝ)) ⁻¹' UnitCube d

private lemma measurableSet_shiftedUnitCube (k : Fin d → ℤ) :
    MeasurableSet (palomar_Lp_shiftedUnitCube (d := d) k) :=
  measurableSet_unitCube.preimage (by fun_prop)

private lemma mem_shiftedUnitCube_iff (k : Fin d → ℤ) (x : Fin d → ℝ) :
    x ∈ palomar_Lp_shiftedUnitCube (d := d) k ↔
      ∀ i, (k i : ℝ) ≤ x i ∧ x i < (k i : ℝ) + 1 := by
  unfold palomar_Lp_shiftedUnitCube
  simp only [Set.mem_preimage, mem_unitCube_iff, Pi.sub_apply]
  constructor
  · intro h i
    have := h i
    refine ⟨by linarith [this.1], by linarith [this.2]⟩
  · intro h i
    have := h i
    refine ⟨by linarith [this.1], by linarith [this.2]⟩

/-- `volume.restrict (UnitCube + k)` is the pushforward of
`volume.restrict (UnitCube d)` along the translation by `k`. This is the
key tool for moving `MemLp`/integrability data from the unit cube to any
integer-translate cube. -/
private lemma restrict_shiftedUnitCube_eq_map (k : Fin d → ℤ) :
    (volume : Measure (Fin d → ℝ)).restrict (palomar_Lp_shiftedUnitCube (d := d) k)
      = Measure.map (fun x : Fin d → ℝ => x + fun i => (k i : ℝ))
          ((volume : Measure (Fin d → ℝ)).restrict (UnitCube d)) := by
  set y : Fin d → ℝ := fun i => (k i : ℝ) with hy_def
  have hmp : MeasurePreserving (fun x : Fin d → ℝ => x + y)
      (volume : Measure (Fin d → ℝ)) volume :=
    measurePreserving_add_right volume y
  -- Identify `(·+y) ⁻¹' palomar_Lp_shiftedUnitCube k = UnitCube d`.
  have hpre : (fun x : Fin d → ℝ => x + y) ⁻¹' (palomar_Lp_shiftedUnitCube (d := d) k)
      = UnitCube d := by
    ext x
    unfold palomar_Lp_shiftedUnitCube
    simp only [Set.mem_preimage]
    have h_arith : (x + y) - y = x := by
      ext i; simp [Pi.add_apply, Pi.sub_apply, hy_def]
    rw [h_arith]
  conv_lhs => rw [← hmp.map_eq]
  rw [Measure.restrict_map hmp.measurable
        (measurableSet_shiftedUnitCube (d := d) k), hpre]

/-- For `MemLpPer p f` and `IsPeriodic f`, the function `f` restricted
to the integer-translate cube `UnitCube + k` lies in `MemLp p` for the
restricted volume measure. -/
lemma MemLpPer.memLp_restrict_shiftedUnitCube
    {p : ℝ≥0∞} {f : (Fin d → ℝ) → ℝ}
    (hf : MemLpPer p f) (hper : IsPeriodic f) (k : Fin d → ℤ) :
    MemLp f p ((volume : Measure (Fin d → ℝ)).restrict
                  (palomar_Lp_shiftedUnitCube (d := d) k)) := by
  rw [restrict_shiftedUnitCube_eq_map (d := d) k]
  set y : Fin d → ℝ := fun i => (k i : ℝ) with hy_def
  have hembed : MeasurableEmbedding (fun x : Fin d → ℝ => x + y) :=
    (MeasurableEquiv.addRight y).measurableEmbedding
  rw [hembed.memLp_map_measure_iff]
  -- `MemLp (f ∘ (· + y)) p (volume.restrict UnitCube)`.
  have hcomp : (f ∘ fun x : Fin d → ℝ => x + y) = f := by
    funext x; exact hper k x
  rw [hcomp]
  exact hf.toMemLp

/-- The shifted unit cube has volume 1. -/
private lemma volume_shiftedUnitCube (k : Fin d → ℤ) :
    (volume : Measure (Fin d → ℝ)) (palomar_Lp_shiftedUnitCube (d := d) k) = 1 := by
  -- LHS: `volume (shifted) = volume.restrict (shifted) univ`.
  have h_lhs :
      volume (palomar_Lp_shiftedUnitCube (d := d) k)
      = ((volume : Measure (Fin d → ℝ)).restrict (palomar_Lp_shiftedUnitCube (d := d) k))
        Set.univ := by
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  rw [h_lhs, restrict_shiftedUnitCube_eq_map (d := d) k]
  set y : Fin d → ℝ := fun i => (k i : ℝ)
  have hembed : MeasurableEmbedding (fun x : Fin d → ℝ => x + y) :=
    (MeasurableEquiv.addRight y).measurableEmbedding
  rw [Measure.map_apply hembed.measurable MeasurableSet.univ]
  simp [Measure.restrict_apply MeasurableSet.univ, volume_unitCube]

/-- For `MemLpPer p f` with `1 ≤ p`, periodic `f`, the function `f` is
integrable on each integer-translate cube `UnitCube + k`. -/
lemma MemLpPer.integrableOn_shiftedUnitCube
    {p : ℝ≥0∞} (hp : 1 ≤ p) {f : (Fin d → ℝ) → ℝ}
    (hf : MemLpPer p f) (hper : IsPeriodic f) (k : Fin d → ℤ) :
    IntegrableOn f (palomar_Lp_shiftedUnitCube (d := d) k)
      (volume : Measure (Fin d → ℝ)) := by
  -- Finite measure on the shifted cube.
  haveI : IsFiniteMeasure ((volume : Measure (Fin d → ℝ)).restrict
      (palomar_Lp_shiftedUnitCube (d := d) k)) := by
    constructor
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
        volume_shiftedUnitCube (d := d) k]
    exact ENNReal.one_lt_top
  -- `MemLp p` ⇒ `MemLp 1` on a finite-measure space, then `Integrable`.
  have h_memLp_p :
      MemLp f p ((volume : Measure (Fin d → ℝ)).restrict
        (palomar_Lp_shiftedUnitCube (d := d) k)) :=
    hf.memLp_restrict_shiftedUnitCube hper k
  have h_memLp_one :
      MemLp f 1 ((volume : Measure (Fin d → ℝ)).restrict
        (palomar_Lp_shiftedUnitCube (d := d) k)) :=
    h_memLp_p.mono_exponent hp
  exact (memLp_one_iff_integrable.mp h_memLp_one)

/-- Open neighbourhood of `x` of the form `(x i - 1, x i + 1)^d`. This
is bounded, of compact closure, and is contained in a finite union of
integer-translate unit cubes — exactly the data we need for local
integrability. -/
def palomar_Lp_openCubeAround (x : Fin d → ℝ) : Set (Fin d → ℝ) :=
  Set.pi Set.univ fun i => Set.Ioo (x i - 1) (x i + 1)

private lemma openCubeAround_isOpen (x : Fin d → ℝ) :
    IsOpen (palomar_Lp_openCubeAround (d := d) x) := by
  unfold palomar_Lp_openCubeAround
  exact isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)

private lemma mem_openCubeAround_self (x : Fin d → ℝ) :
    x ∈ palomar_Lp_openCubeAround (d := d) x := by
  unfold palomar_Lp_openCubeAround
  refine Set.mem_pi.mpr ?_
  intro i _
  refine Set.mem_Ioo.mpr ⟨?_, ?_⟩ <;> linarith

private lemma openCubeAround_mem_nhds (x : Fin d → ℝ) :
    palomar_Lp_openCubeAround (d := d) x ∈ 𝓝 x :=
  IsOpen.mem_nhds (openCubeAround_isOpen x) (mem_openCubeAround_self x)

/-- The "neighbour offset" indices: a `Fin d → Fin 3` selecting one of
`-1, 0, +1` per coordinate. This is the canonical 3^d-element finset. -/
def palomar_Lp_neighbourOffsets (d : ℕ) : Finset (Fin d → Fin 3) :=
  Finset.univ

/-- Convert a neighbour offset into an integer offset relative to a base
integer point. The encoding sends `Fin 3 → ℤ` via `0 ↦ -1, 1 ↦ 0, 2 ↦ 1`. -/
def palomar_Lp_offsetToInt (j : Fin 3) : ℤ :=
  (j : ℤ) - 1

/-- Cover of `palomar_Lp_openCubeAround x` by `3^d` integer-translate unit cubes
centred near `⌊x⌋`. The base integer index is `kBase i := ⌊x i⌋`, and
the cubes are indexed by `j : Fin d → Fin 3` with offset
`fun i => kBase i + palomar_Lp_offsetToInt (j i)`. -/
private lemma openCubeAround_subset_union_shiftedCubes
    (x : Fin d → ℝ) :
    palomar_Lp_openCubeAround (d := d) x ⊆
      ⋃ j ∈ palomar_Lp_neighbourOffsets d,
        palomar_Lp_shiftedUnitCube (d := d)
          (fun i => ⌊x i⌋ + palomar_Lp_offsetToInt (j i)) := by
  intro y hy
  -- For each coordinate, `y i ∈ (x i - 1, x i + 1)` so `y i` lies in
  -- one of three integer-translate intervals: `[⌊x i⌋ - 1, ⌊x i⌋)`,
  -- `[⌊x i⌋, ⌊x i⌋ + 1)`, or `[⌊x i⌋ + 1, ⌊x i⌋ + 2)`.
  -- Concretely, `⌊y i⌋ ∈ {⌊x i⌋ - 1, ⌊x i⌋, ⌊x i⌋ + 1}`.
  -- Define the per-coordinate `Fin 3` index by case split on `⌊y i⌋`.
  classical
  have hy' : ∀ i, x i - 1 < y i ∧ y i < x i + 1 := by
    intro i
    have := (Set.mem_pi.mp hy) i (Set.mem_univ _)
    exact Set.mem_Ioo.mp this
  -- Per-coordinate, choose `Fin 3` index.
  -- Build the index `j : Fin d → Fin 3`.
  -- Use `⌊y i⌋ - ⌊x i⌋ + 1 ∈ {0, 1, 2}`.
  -- Step 1: ⌊x i⌋ - 1 < y i so ⌊y i⌋ ≥ ⌊x i⌋ - 1.
  -- Step 2: y i < ⌊x i⌋ + 2 (since x i < ⌊x i⌋ + 1) so ⌊y i⌋ ≤ ⌊x i⌋ + 1.
  have hbounds : ∀ i, ⌊x i⌋ - 1 ≤ ⌊y i⌋ ∧ ⌊y i⌋ ≤ ⌊x i⌋ + 1 := by
    intro i
    refine ⟨?_, ?_⟩
    · -- ⌊x i⌋ - 1 ≤ ⌊y i⌋ ↔ ⌊x i⌋ ≤ ⌊y i⌋ + 1 ↔ ⌊x i⌋ < ⌊y i⌋ + 2
      -- via `Int.floor_le` and `(hy' i).1 : x i - 1 < y i`.
      have hxle : (⌊x i⌋ : ℝ) ≤ x i := Int.floor_le _
      have h1 : ((⌊x i⌋ - 1 : ℤ) : ℝ) ≤ y i := by
        have := (hy' i).1
        push_cast; linarith
      exact Int.le_floor.mpr h1
    · -- ⌊y i⌋ ≤ ⌊x i⌋ + 1 ↔ ⌊y i⌋ < ⌊x i⌋ + 2.
      have hxlt : x i < (⌊x i⌋ : ℝ) + 1 := Int.lt_floor_add_one _
      have h2 : y i < ((⌊x i⌋ + 2 : ℤ) : ℝ) := by
        have := (hy' i).2
        push_cast; linarith
      have : ⌊y i⌋ < ⌊x i⌋ + 2 := by
        have hh : ⌊y i⌋ < (⌊x i⌋ + 2 : ℤ) := by
          exact_mod_cast Int.floor_lt.mpr h2
        exact hh
      omega
  -- Convert per-coordinate to `Fin 3` index.
  let j : Fin d → Fin 3 := fun i =>
    ⟨((⌊y i⌋ - ⌊x i⌋ + 1 : ℤ)).toNat, by
      have h := hbounds i
      have h0 : 0 ≤ ⌊y i⌋ - ⌊x i⌋ + 1 := by linarith [h.1]
      have h1 : ⌊y i⌋ - ⌊x i⌋ + 1 ≤ 2 := by linarith [h.2]
      have hnat : ((⌊y i⌋ - ⌊x i⌋ + 1 : ℤ)).toNat ≤ 2 := by
        omega
      omega⟩
  refine Set.mem_iUnion₂.mpr ⟨j, Finset.mem_univ _, ?_⟩
  -- Show `y ∈ palomar_Lp_shiftedUnitCube (fun i => ⌊x i⌋ + palomar_Lp_offsetToInt (j i))`.
  rw [mem_shiftedUnitCube_iff]
  intro i
  -- The integer offset for coordinate `i` is `⌊y i⌋`.
  have hjval : palomar_Lp_offsetToInt (j i) = (⌊y i⌋ - ⌊x i⌋ : ℤ) := by
    unfold palomar_Lp_offsetToInt
    have h := hbounds i
    have h0 : 0 ≤ ⌊y i⌋ - ⌊x i⌋ + 1 := by linarith [h.1]
    have h_eq : (((⌊y i⌋ - ⌊x i⌋ + 1 : ℤ)).toNat : ℤ) = ⌊y i⌋ - ⌊x i⌋ + 1 :=
      Int.toNat_of_nonneg h0
    change ((j i : ℕ) : ℤ) - 1 = ⌊y i⌋ - ⌊x i⌋
    -- `(j i : ℕ) = (⌊y i⌋ - ⌊x i⌋ + 1).toNat`, and casting back gives the value.
    have : ((j i : ℕ) : ℤ) = ⌊y i⌋ - ⌊x i⌋ + 1 := by
      simpa [j] using h_eq
    linarith
  -- The cube offset:
  have h_offset : (((⌊x i⌋ + palomar_Lp_offsetToInt (j i) : ℤ) : ℝ)) = (⌊y i⌋ : ℝ) := by
    rw [hjval]
    push_cast; ring
  refine ⟨?_, ?_⟩
  · rw [h_offset]; exact Int.floor_le _
  · rw [h_offset]; exact Int.lt_floor_add_one _

/-- **Local integrability bridge.** For `MemLpPer p f` with `1 ≤ p` and
`IsPeriodic f`, `f` is locally integrable on `ℝ^d` with respect to the
volume measure.

This is the periodic analogue of "`L^p_loc` ⇒ `L^1_loc` for `1 ≤ p`",
combined with the elementary fact that a periodic `L^p` function over
the fundamental domain is automatically `L^p` over every fundamental
domain (and hence over any compact set, which is contained in finitely
many such domains).

This is the bridge needed by Phase-4 density consumers to drop the
`LocallyIntegrable f volume` hypothesis from
`SmoothPeriodic.exists_eLpNormPer_sub_le` (in `Periodic/Mollifier.lean`)
once they have `MemLpPer p f + IsPeriodic f` in scope. -/
theorem MemLpPer.locallyIntegrable_of_periodic
    {p : ℝ≥0∞} (hp : 1 ≤ p) {f : (Fin d → ℝ) → ℝ}
    (hf : MemLpPer p f) (hper : IsPeriodic f) :
    LocallyIntegrable f (volume : Measure (Fin d → ℝ)) := by
  intro x
  classical
  -- The neighbourhood `U := palomar_Lp_openCubeAround x` is open, contains `x`, and
  -- is contained in a finite union of integer-translate unit cubes.
  refine ⟨palomar_Lp_openCubeAround (d := d) x, openCubeAround_mem_nhds x, ?_⟩
  -- Show `IntegrableOn f (palomar_Lp_openCubeAround x) volume` by routing through
  -- the bigger union of integer-translate cubes.
  have h_union :
      IntegrableOn f
        (⋃ j ∈ palomar_Lp_neighbourOffsets d,
            palomar_Lp_shiftedUnitCube (d := d)
              (fun i => ⌊x i⌋ + palomar_Lp_offsetToInt (j i)))
        (volume : Measure (Fin d → ℝ)) := by
    refine (integrableOn_finset_iUnion (s := palomar_Lp_neighbourOffsets d)
      (t := fun j =>
        palomar_Lp_shiftedUnitCube (d := d)
          (fun i => ⌊x i⌋ + palomar_Lp_offsetToInt (j i)))).mpr ?_
    intro j _
    exact hf.integrableOn_shiftedUnitCube hp hper _
  exact h_union.mono_set
    (openCubeAround_subset_union_shiftedCubes (d := d) x)

/-- Sanity check: a constant function is locally integrable via the
periodic bridge. -/
example (c : ℝ) :
    LocallyIntegrable (fun _ : (Fin d → ℝ) => c)
      (volume : Measure (Fin d → ℝ)) := by
  have hcube : volume (UnitCube d) ≠ ⊤ := by simp
  haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  have hf : MemLpPer (d := d) 1 (fun _ : (Fin d → ℝ) => c) :=
    MemLp.toMemLpPer (memLp_const c)
  exact hf.locallyIntegrable_of_periodic le_rfl (IsPeriodic.const c)

end Periodic
end StationaryMFG
