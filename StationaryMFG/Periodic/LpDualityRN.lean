module

public import StationaryMFG.Periodic.LpDuality

@[expose] public section

/-!
# L¹ representer construction via Radon–Nikodym (periodic)

This module constructs the `L¹` representer of a continuous linear
functional `φ : LpPer p d →L[ℝ] ℝ` on the periodic unit cube
`UnitCube d ⊆ ℝ^d` for `1 ≤ p < ∞`. The representer
`g := phiRepresenter φ` is integrable, and the simple-function
identity `φ s = ∫ s · g` holds for every `s : Lp.simpleFunc ℝ p μ`.

This is the cube-restricted port of
`docs/references/LpSpaces/LpSpaces/LpDualityRNConstruction.lean`
(adapted to `Ω = UnitCube d` and `μ = volume.restrict (UnitCube d)`).

## Outline

1. `phiSet A := φ(indicatorConstLp p hA … 1)` for measurable `A`.
2. Verify `VectorMeasure` axioms (empty, non-measurable, σ-additivity).
3. Package as `phiSignedMeasure : SignedMeasure (Fin d → ℝ)`.
4. Prove absolute continuity wrt `volume.restrict (UnitCube d)`.
5. Define `phiRepresenter := (phiSignedMeasure φ).rnDeriv μ`.
6. Indicator integral formula via `withDensityᵥ_rnDeriv_eq`.
7. Lift to `c · 𝟙_A` (linearity) and to simple functions
   (`Lp.simpleFunc.induction`).

## References

- Adapted from `LpSpaces.LpDualityRNConstruction` (whole-space,
  generic finite-measure version), specialized to the unit cube.
-/

noncomputable section

open MeasureTheory Set Filter Function
open scoped ENNReal NNReal Topology symmDiff

namespace StationaryMFG
namespace Periodic
namespace LpDualityRN

variable {d : ℕ}

/-- Local abbreviation for the unit-cube measure. -/
local notation "μPer" =>
  (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d))

/-! ## Section 1 — The set function `phiSet` -/

/-- The set function `A ↦ φ(𝟙_A · 1)` extended by zero on non-measurable
sets. Adapted from `LpSpaces.LpDualityRNConstruction.phiSet`. -/
noncomputable def phiSet {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (φ : LpPer p d →L[ℝ] ℝ) (A : Set (Fin d → ℝ)) : ℝ := by
  classical
  haveI := Saturator.instIsFiniteMeasureRestrictUnitCube (d := d)
  exact if h : MeasurableSet A then
    φ (indicatorConstLp p h (measure_ne_top _ _) (1 : ℝ))
  else 0

theorem phiSet_apply_measurable {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (φ : LpPer p d →L[ℝ] ℝ)
    {A : Set (Fin d → ℝ)} (hA : MeasurableSet A) :
    phiSet (d := d) φ A =
      haveI := Saturator.instIsFiniteMeasureRestrictUnitCube (d := d)
      φ (indicatorConstLp p hA (measure_ne_top _ _) (1 : ℝ)) := by
  classical
  unfold phiSet
  exact dif_pos hA

theorem phiSet_apply_not_measurable {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (φ : LpPer p d →L[ℝ] ℝ)
    {A : Set (Fin d → ℝ)} (hA : ¬ MeasurableSet A) :
    phiSet (d := d) φ A = 0 := by
  classical
  unfold phiSet
  exact dif_neg hA

theorem phiSet_empty {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp_ne_top : p ≠ ∞)
    (φ : LpPer p d →L[ℝ] ℝ) :
    phiSet (d := d) φ ∅ = 0 := by
  haveI := Saturator.instIsFiniteMeasureRestrictUnitCube (d := d)
  rw [phiSet_apply_measurable φ MeasurableSet.empty]
  rw [show indicatorConstLp p MeasurableSet.empty (measure_ne_top _ _) (1 : ℝ) = 0 from
        indicatorConstLp_empty]
  exact map_zero φ

/-! ## Section 2 — σ-additivity of `phiSet` -/

theorem phiSet_disjoint_union {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp_ne_top : p ≠ ∞)
    (φ : LpPer p d →L[ℝ] ℝ)
    {A B : Set (Fin d → ℝ)} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : Disjoint A B) :
    phiSet (d := d) φ (A ∪ B) =
      phiSet (d := d) φ A + phiSet (d := d) φ B := by
  haveI := Saturator.instIsFiniteMeasureRestrictUnitCube (d := d)
  rw [phiSet_apply_measurable φ (hA.union hB),
      phiSet_apply_measurable φ hA,
      phiSet_apply_measurable φ hB]
  rw [show indicatorConstLp p (hA.union hB) (measure_ne_top _ _) (1 : ℝ)
        = indicatorConstLp p hA (measure_ne_top _ _) (1 : ℝ)
          + indicatorConstLp p hB (measure_ne_top _ _) (1 : ℝ) from
        indicatorConstLp_disjoint_union hA hB (measure_ne_top _ _)
          (measure_ne_top _ _) hAB (1 : ℝ)]
  exact map_add φ _ _

theorem phiSet_finset_sum_range {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp_ne_top : p ≠ ∞)
    (φ : LpPer p d →L[ℝ] ℝ)
    (A : ℕ → Set (Fin d → ℝ)) (hA : ∀ i, MeasurableSet (A i))
    (hAd : Pairwise (Disjoint on A)) (n : ℕ) :
    ∑ i ∈ Finset.range n, phiSet (d := d) φ (A i) =
      phiSet (d := d) φ (⋃ i ∈ Finset.range n, A i) := by
  induction n with
  | zero =>
    simp [phiSet_empty hp_ne_top φ]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h_set_eq : (⋃ i ∈ Finset.range (n + 1), A i) =
        (⋃ i ∈ Finset.range n, A i) ∪ A n := by
      ext x
      simp only [mem_iUnion, Finset.mem_range, mem_union]
      constructor
      · rintro ⟨i, hi, hxi⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
        · exact Or.inl ⟨i, hlt, hxi⟩
        · exact Or.inr (heq ▸ hxi)
      · rintro (⟨i, hi, hxi⟩ | hxn)
        · exact ⟨i, Nat.lt_succ_of_lt hi, hxi⟩
        · exact ⟨n, Nat.lt_succ_self n, hxn⟩
    have h_disj : Disjoint (⋃ i ∈ Finset.range n, A i) (A n) := by
      rw [Set.disjoint_iUnion_left]
      intro i
      rw [Set.disjoint_iUnion_left]
      intro hi
      exact hAd (Finset.mem_range.mp hi).ne
    have h_meas : MeasurableSet (⋃ i ∈ Finset.range n, A i) :=
      MeasurableSet.biUnion (Finset.range n).countable_toSet (fun i _ => hA i)
    have h_split := phiSet_disjoint_union hp_ne_top φ h_meas (hA n) h_disj
    rw [h_set_eq, h_split]

private theorem partial_iUnion_monotone (A : ℕ → Set (Fin d → ℝ)) :
    Monotone (fun n => ⋃ i ∈ Finset.range n, A i) := by
  intro n m hnm
  intro x hx
  simp only [mem_iUnion, Finset.mem_range] at hx ⊢
  obtain ⟨i, hi, hxi⟩ := hx
  exact ⟨i, lt_of_lt_of_le hi hnm, hxi⟩

private theorem measure_symmDiff_partial_iUnion_tendsto
    (A : ℕ → Set (Fin d → ℝ)) (hA : ∀ i, MeasurableSet (A i)) :
    Tendsto (fun n => (μPer : Measure (Fin d → ℝ))
        ((⋃ i ∈ Finset.range n, A i) ∆ (⋃ i, A i)))
      atTop (𝓝 0) := by
  haveI := Saturator.instIsFiniteMeasureRestrictUnitCube (d := d)
  set μ : Measure (Fin d → ℝ) := μPer
  have h_subset : ∀ n, (⋃ i ∈ Finset.range n, A i) ⊆ ⋃ i, A i := by
    intro n x hx
    simp only [mem_iUnion, Finset.mem_range] at hx
    obtain ⟨i, _, hxi⟩ := hx
    exact mem_iUnion.mpr ⟨i, hxi⟩
  have h_eq : ∀ n, μ ((⋃ i ∈ Finset.range n, A i) ∆ (⋃ i, A i))
      = μ (⋃ i, A i) - μ (⋃ i ∈ Finset.range n, A i) := by
    intro n
    rw [Set.symmDiff_def]
    rw [Set.diff_eq_empty.mpr (h_subset n)]
    simp only [empty_union]
    have hSn : MeasurableSet (⋃ i ∈ Finset.range n, A i) :=
      MeasurableSet.biUnion (Finset.range n).countable_toSet (fun i _ => hA i)
    rw [measure_diff (h_subset n) hSn.nullMeasurableSet (measure_ne_top _ _)]
  rw [show (fun n => μ ((⋃ i ∈ Finset.range n, A i) ∆ (⋃ i, A i)))
        = (fun n => μ (⋃ i, A i) - μ (⋃ i ∈ Finset.range n, A i)) from
        funext h_eq]
  have h_tendsto_partial :
      Tendsto (fun n => μ (⋃ i ∈ Finset.range n, A i)) atTop
        (𝓝 (μ (⋃ n, ⋃ i ∈ Finset.range n, A i))) :=
    tendsto_measure_iUnion_atTop (partial_iUnion_monotone A)
  have h_iUnion_eq : (⋃ n, ⋃ i ∈ Finset.range n, A i) = ⋃ i, A i := by
    ext x
    simp only [mem_iUnion, Finset.mem_range]
    constructor
    · rintro ⟨n, i, _, hxi⟩
      exact ⟨i, hxi⟩
    · rintro ⟨i, hxi⟩
      exact ⟨i + 1, i, Nat.lt_succ_self i, hxi⟩
  rw [h_iUnion_eq] at h_tendsto_partial
  have h_finite : μ (⋃ i, A i) ≠ ∞ := measure_ne_top _ _
  have h_sub_tendsto :
      Tendsto (fun n => μ (⋃ i, A i) - μ (⋃ i ∈ Finset.range n, A i)) atTop
        (𝓝 (μ (⋃ i, A i) - μ (⋃ i, A i))) := by
    apply ENNReal.Tendsto.sub tendsto_const_nhds h_tendsto_partial
    exact Or.inr h_finite
  rw [tsub_self] at h_sub_tendsto
  exact h_sub_tendsto

private theorem indicatorConstLp_partial_tendsto {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp_ne_top : p ≠ ∞)
    (A : ℕ → Set (Fin d → ℝ)) (hA : ∀ i, MeasurableSet (A i)) :
    haveI := Saturator.instIsFiniteMeasureRestrictUnitCube (d := d)
    Tendsto (fun n =>
      indicatorConstLp (μ := μPer) p
        (MeasurableSet.biUnion (Finset.range n).countable_toSet (fun i _ => hA i))
        (measure_ne_top _ _) (1 : ℝ))
      atTop
      (𝓝 (indicatorConstLp (μ := μPer) p
        (MeasurableSet.iUnion hA) (measure_ne_top _ _) (1 : ℝ))) := by
  haveI := Saturator.instIsFiniteMeasureRestrictUnitCube (d := d)
  apply tendsto_indicatorConstLp_set hp_ne_top
  exact measure_symmDiff_partial_iUnion_tendsto A hA

private theorem Lp_coeFn_finset_sum
    {α G : Type*} {m : MeasurableSpace α} {μ : Measure α}
    [NormedAddCommGroup G] {p : ℝ≥0∞}
    {ι : Type*} (s : Finset ι) (f : ι → Lp G p μ) :
    ∀ᵐ x ∂μ, (∑ i ∈ s, f i) x = ∑ i ∈ s, (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have h_zero : ⇑(0 : Lp G p μ) =ᵐ[μ] (0 : α → G) := Lp.coeFn_zero G p μ
    filter_upwards [h_zero] with x hx
    rw [hx]; rfl
  | insert a s hns ih =>
    rw [Finset.sum_insert hns]
    have h_add := Lp.coeFn_add (f a) (∑ i ∈ s, f i)
    filter_upwards [h_add, ih] with x hx hx_ih
    rw [hx, Pi.add_apply, hx_ih, Finset.sum_insert hns]

private theorem phiSet_partial_sum_tendsto {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp_ne_top : p ≠ ∞)
    (φ : LpPer p d →L[ℝ] ℝ)
    (A : ℕ → Set (Fin d → ℝ)) (hA : ∀ i, MeasurableSet (A i))
    (hAd : Pairwise (Disjoint on A)) :
    Tendsto (fun n => ∑ i ∈ Finset.range n, phiSet (d := d) φ (A i))
      atTop (𝓝 (phiSet (d := d) φ (⋃ i, A i))) := by
  haveI := Saturator.instIsFiniteMeasureRestrictUnitCube (d := d)
  have h_sum_eq : ∀ n, ∑ i ∈ Finset.range n, phiSet (d := d) φ (A i) =
      phiSet (d := d) φ (⋃ i ∈ Finset.range n, A i) :=
    fun n => phiSet_finset_sum_range hp_ne_top φ A hA hAd n
  rw [show (fun n => ∑ i ∈ Finset.range n, phiSet (d := d) φ (A i)) =
      (fun n => phiSet (d := d) φ (⋃ i ∈ Finset.range n, A i)) from funext h_sum_eq]
  have h_partial_meas : ∀ n,
      MeasurableSet (⋃ i ∈ Finset.range n, A i) :=
    fun n => MeasurableSet.biUnion (Finset.range n).countable_toSet (fun i _ => hA i)
  have h_iU_meas : MeasurableSet (⋃ i, A i) := MeasurableSet.iUnion hA
  have h_eq_partial : ∀ n,
      phiSet (d := d) φ (⋃ i ∈ Finset.range n, A i) =
        φ (indicatorConstLp (μ := μPer) p (h_partial_meas n)
            (measure_ne_top _ _) (1 : ℝ)) := fun n =>
    phiSet_apply_measurable φ (h_partial_meas n)
  have h_eq_full :
      phiSet (d := d) φ (⋃ i, A i) =
        φ (indicatorConstLp (μ := μPer) p h_iU_meas
            (measure_ne_top _ _) (1 : ℝ)) :=
    phiSet_apply_measurable φ h_iU_meas
  rw [show (fun n => phiSet (d := d) φ (⋃ i ∈ Finset.range n, A i)) =
      (fun n => φ (indicatorConstLp (μ := μPer) p (h_partial_meas n)
                  (measure_ne_top _ _) (1 : ℝ))) from funext h_eq_partial]
  rw [h_eq_full]
  exact (φ.continuous.tendsto _).comp
    (indicatorConstLp_partial_tendsto hp_ne_top A hA)

/-! ### Sign trick — absolute summability of `(phiSet ∘ A)` -/

noncomputable def palomar_LpDualityRN_signedPartialIndicator
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (φ : LpPer p d →L[ℝ] ℝ)
    (A : ℕ → Set (Fin d → ℝ)) (hA : ∀ i, MeasurableSet (A i)) (N : ℕ) :
    LpPer p d :=
  haveI := Saturator.instIsFiniteMeasureRestrictUnitCube (d := d)
  ∑ i ∈ Finset.range N,
    (Real.sign (phiSet (d := d) φ (A i))) •
      indicatorConstLp (μ := μPer) p (hA i)
        (measure_ne_top _ _) (1 : ℝ)

private theorem Real_sign_mul_self (x : ℝ) : Real.sign x * x = |x| := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [Real.sign_of_neg hx, abs_of_neg hx]; ring
  · rw [Real.sign_zero]; simp
  · rw [Real.sign_of_pos hx, abs_of_pos hx, one_mul]

private theorem phi_signedPartialIndicator_eq_sum_abs
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (φ : LpPer p d →L[ℝ] ℝ)
    (A : ℕ → Set (Fin d → ℝ)) (hA : ∀ i, MeasurableSet (A i)) (N : ℕ) :
    φ (palomar_LpDualityRN_signedPartialIndicator (d := d) φ A hA N) =
      ∑ i ∈ Finset.range N, |phiSet (d := d) φ (A i)| := by
  haveI := Saturator.instIsFiniteMeasureRestrictUnitCube (d := d)
  unfold palomar_LpDualityRN_signedPartialIndicator
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [φ.map_smul]
  rw [show φ (indicatorConstLp (μ := μPer) p (hA i)
              (measure_ne_top _ _) (1 : ℝ))
        = phiSet (d := d) φ (A i) from
        (phiSet_apply_measurable φ (hA i)).symm]
  simp only [smul_eq_mul]
  exact Real_sign_mul_self _

private theorem signedPartialIndicator_abs_le_one
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (φ : LpPer p d →L[ℝ] ℝ)
    (A : ℕ → Set (Fin d → ℝ)) (hA : ∀ i, MeasurableSet (A i))
    (hAd : Pairwise (Disjoint on A)) (N : ℕ) :
    ∀ᵐ x ∂(μPer : Measure (Fin d → ℝ)),
      ‖palomar_LpDualityRN_signedPartialIndicator (d := d) φ A hA N x‖ ≤
        (⋃ i, A i).indicator (fun _ => (1 : ℝ)) x := by
  haveI := Saturator.instIsFiniteMeasureRestrictUnitCube (d := d)
  have h_summand_coe : ∀ i,
      ⇑(Real.sign (phiSet (d := d) φ (A i)) •
          indicatorConstLp (μ := μPer) p (hA i)
            (measure_ne_top _ _) (1 : ℝ)) =ᵐ[μPer]
        fun x => Real.sign (phiSet (d := d) φ (A i)) •
                  (A i).indicator (fun _ => (1 : ℝ)) x := by
    intro i
    have h_smul := Lp.coeFn_smul
      (Real.sign (phiSet (d := d) φ (A i)))
      (indicatorConstLp (μ := μPer) p (hA i)
        (measure_ne_top _ _) (1 : ℝ))
    have h_ind : ⇑(indicatorConstLp (μ := μPer) p (hA i)
          (measure_ne_top _ _) (1 : ℝ))
        =ᵐ[μPer] (A i).indicator (fun _ => (1 : ℝ)) :=
      indicatorConstLp_coeFn
    refine h_smul.trans ?_
    filter_upwards [h_ind] with x hx
    show Real.sign (phiSet (d := d) φ (A i)) •
        ((indicatorConstLp (μ := μPer) p (hA i)
          (measure_ne_top _ _) (1 : ℝ)) x) =
        Real.sign (phiSet (d := d) φ (A i)) •
          (A i).indicator (fun _ => (1 : ℝ)) x
    rw [hx]
  have h_sum_coe := Lp_coeFn_finset_sum (μ := μPer) (p := p) (G := ℝ)
    (Finset.range N)
    (fun i =>
      Real.sign (phiSet (d := d) φ (A i)) •
        indicatorConstLp (μ := μPer) p (hA i)
          (measure_ne_top _ _) (1 : ℝ))
  have h_each_eq : ∀ᵐ x ∂(μPer : Measure (Fin d → ℝ)), ∀ i,
        (Real.sign (phiSet (d := d) φ (A i)) •
            indicatorConstLp (μ := μPer) p (hA i)
              (measure_ne_top _ _) (1 : ℝ)) x =
        Real.sign (phiSet (d := d) φ (A i)) •
          (A i).indicator (fun _ => (1 : ℝ)) x := by
    rw [ae_all_iff]
    intro i
    exact h_summand_coe i
  filter_upwards [h_sum_coe, h_each_eq] with x hx_sum hx_each
  show ‖(palomar_LpDualityRN_signedPartialIndicator (d := d) φ A hA N) x‖ ≤ _
  unfold palomar_LpDualityRN_signedPartialIndicator
  rw [hx_sum]
  rw [Finset.sum_congr rfl (fun i _ => hx_each i)]
  by_cases hxU : x ∈ ⋃ i, A i
  · obtain ⟨i, hxi⟩ := mem_iUnion.mp hxU
    rw [Set.indicator_of_mem hxU]
    by_cases hiN : i < N
    · have h_only_i : ∀ j ∈ Finset.range N, j ≠ i →
          Real.sign (phiSet (d := d) φ (A j)) •
            (A j).indicator (fun _ => (1 : ℝ)) x = 0 := by
        intro j _ hji
        have hxj : x ∉ A j := by
          intro hxj
          exact (hAd (Ne.symm hji)).le_bot ⟨hxi, hxj⟩
        rw [Set.indicator_of_notMem hxj]
        simp
      rw [Finset.sum_eq_single i h_only_i (fun h => absurd (Finset.mem_range.mpr hiN) h)]
      rw [Set.indicator_of_mem hxi]
      show ‖Real.sign (phiSet (d := d) φ (A i)) • (1 : ℝ)‖ ≤ 1
      simp only [smul_eq_mul, mul_one, Real.norm_eq_abs]
      rcases Real.sign_apply_eq (phiSet (d := d) φ (A i)) with h | h | h
      all_goals rw [h]; simp
    · have h_all_zero : ∀ j ∈ Finset.range N,
          Real.sign (phiSet (d := d) φ (A j)) •
            (A j).indicator (fun _ => (1 : ℝ)) x = 0 := by
        intro j hj
        have hji : j ≠ i := by
          intro h_eq
          rw [h_eq] at hj
          exact absurd (Finset.mem_range.mp hj) hiN
        have hxj : x ∉ A j := by
          intro hxj
          exact (hAd (Ne.symm hji)).le_bot ⟨hxi, hxj⟩
        rw [Set.indicator_of_notMem hxj]
        simp
      rw [Finset.sum_eq_zero h_all_zero]
      simp
  · rw [Set.indicator_of_notMem hxU]
    have h_all_zero : ∀ j ∈ Finset.range N,
        Real.sign (phiSet (d := d) φ (A j)) •
          (A j).indicator (fun _ => (1 : ℝ)) x = 0 := by
      intro j _
      have hxj : x ∉ A j := fun h => hxU (mem_iUnion.mpr ⟨j, h⟩)
      rw [Set.indicator_of_notMem hxj]
      simp
    rw [Finset.sum_eq_zero h_all_zero]
    simp

private theorem norm_signedPartialIndicator_le {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp_ne_top : p ≠ ∞)
    (φ : LpPer p d →L[ℝ] ℝ)
    (A : ℕ → Set (Fin d → ℝ)) (hA : ∀ i, MeasurableSet (A i))
    (hAd : Pairwise (Disjoint on A)) (N : ℕ) :
    ‖palomar_LpDualityRN_signedPartialIndicator (d := d) φ A hA N‖ ≤
      ((μPer : Measure (Fin d → ℝ)) (⋃ i, A i)).toReal ^ (1 / p.toReal) := by
  haveI := Saturator.instIsFiniteMeasureRestrictUnitCube (d := d)
  have hp_ne_zero : p ≠ 0 := (one_pos.trans_le (Fact.out (p := (1 ≤ p)))).ne'
  have h_iU_meas : MeasurableSet (⋃ i, A i) := MeasurableSet.iUnion hA
  rw [Lp.norm_def]
  have h_le : eLpNorm
      (⇑(palomar_LpDualityRN_signedPartialIndicator (d := d) φ A hA N)) p μPer ≤
      eLpNorm (fun x => (⋃ i, A i).indicator (fun _ => (1 : ℝ)) x) p μPer := by
    refine eLpNorm_mono_ae (Lp.aestronglyMeasurable _) ?_
    have h_bound := signedPartialIndicator_abs_le_one (d := d) φ A hA hAd N
    filter_upwards [h_bound] with x hx
    have h_ind_nn : 0 ≤ (⋃ i, A i).indicator (fun _ => (1 : ℝ)) x := by
      by_cases hx' : x ∈ ⋃ i, A i
      · rw [Set.indicator_of_mem hx']; norm_num
      · rw [Set.indicator_of_notMem hx']
    rw [Real.norm_eq_abs (((⋃ i, A i).indicator _) x), abs_of_nonneg h_ind_nn]
    exact hx
  have h_indicator_norm :
      eLpNorm (fun x => (⋃ i, A i).indicator (fun _ => (1 : ℝ)) x) p μPer =
      (1 : ℝ≥0∞) * (μPer (⋃ i, A i)) ^ (1 / p.toReal) := by
    rw [eLpNorm_indicator_const h_iU_meas.nullMeasurableSet hp_ne_zero hp_ne_top]
    simp [enorm_one]
  have h_le2 : eLpNorm
      (⇑(palomar_LpDualityRN_signedPartialIndicator (d := d) φ A hA N)) p μPer ≤
      (μPer (⋃ i, A i)) ^ (1 / p.toReal) := by
    rw [h_indicator_norm, one_mul] at h_le
    exact h_le
  have h_mu_ne_top : μPer (⋃ i, A i) ≠ ∞ := measure_ne_top _ _
  have h_rpow_ne_top :
      (μPer (⋃ i, A i)) ^ (1 / p.toReal) ≠ ∞ := by
    apply ENNReal.rpow_ne_top_of_nonneg _ h_mu_ne_top
    positivity
  have h_toReal := ENNReal.toReal_mono h_rpow_ne_top h_le2
  rw [show (μPer (⋃ i, A i) ^ (1 / p.toReal)).toReal =
        (μPer (⋃ i, A i)).toReal ^ (1 / p.toReal) from
        (ENNReal.toReal_rpow _ _).symm] at h_toReal
  exact h_toReal

private theorem summable_abs_phiSet {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp_ne_top : p ≠ ∞)
    (φ : LpPer p d →L[ℝ] ℝ)
    (A : ℕ → Set (Fin d → ℝ)) (hA : ∀ i, MeasurableSet (A i))
    (hAd : Pairwise (Disjoint on A)) :
    Summable (fun i => |phiSet (d := d) φ (A i)|) := by
  haveI := Saturator.instIsFiniteMeasureRestrictUnitCube (d := d)
  set C : ℝ := ‖φ‖ * ((μPer : Measure (Fin d → ℝ)) (⋃ i, A i)).toReal ^ (1 / p.toReal)
  apply summable_of_sum_range_le (c := C)
  · intro n; exact abs_nonneg _
  intro N
  rw [← phi_signedPartialIndicator_eq_sum_abs φ A hA N]
  have h_eq : φ (palomar_LpDualityRN_signedPartialIndicator (d := d) φ A hA N) =
      |φ (palomar_LpDualityRN_signedPartialIndicator (d := d) φ A hA N)| := by
    rw [phi_signedPartialIndicator_eq_sum_abs φ A hA N]
    rw [abs_of_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _))]
  rw [h_eq]
  calc |φ (palomar_LpDualityRN_signedPartialIndicator (d := d) φ A hA N)|
      ≤ ‖φ‖ * ‖palomar_LpDualityRN_signedPartialIndicator (d := d) φ A hA N‖ := by
        rw [← Real.norm_eq_abs]; exact φ.le_opNorm _
    _ ≤ ‖φ‖ * ((μPer (⋃ i, A i)).toReal ^ (1 / p.toReal)) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact norm_signedPartialIndicator_le hp_ne_top φ A hA hAd N
    _ = C := rfl

theorem phiSet_hasSum_disjoint {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp_ne_top : p ≠ ∞)
    (φ : LpPer p d →L[ℝ] ℝ)
    {A : ℕ → Set (Fin d → ℝ)} (hA : ∀ i, MeasurableSet (A i))
    (hAd : Pairwise (Disjoint on A)) :
    HasSum (fun i => phiSet (d := d) φ (A i))
      (phiSet (d := d) φ (⋃ i, A i)) := by
  have h_summable : Summable (fun i => |phiSet (d := d) φ (A i)|) :=
    summable_abs_phiSet hp_ne_top φ A hA hAd
  have h_summable_norm : Summable (fun i => ‖phiSet (d := d) φ (A i)‖) := by
    have h_eq : (fun i => ‖phiSet (d := d) φ (A i)‖) =
        (fun i => |phiSet (d := d) φ (A i)|) := by
      funext i; exact Real.norm_eq_abs _
    rw [h_eq]; exact h_summable
  rw [hasSum_iff_tendsto_nat_of_summable_norm h_summable_norm]
  exact phiSet_partial_sum_tendsto hp_ne_top φ A hA hAd

/-! ## Section 3 — Packaging as a `SignedMeasure` -/

/-- The signed measure `A ↦ φ(𝟙_A · 1)` associated to a continuous
linear functional `φ : LpPer p d →L[ℝ] ℝ`. -/
noncomputable def phiSignedMeasure {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp_ne_top : p ≠ ∞)
    (φ : LpPer p d →L[ℝ] ℝ) :
    SignedMeasure (Fin d → ℝ) where
  measureOf' := phiSet (d := d) φ
  empty' := phiSet_empty hp_ne_top φ
  not_measurable' _ hi := phiSet_apply_not_measurable φ hi
  m_iUnion' _ hAm hAd := phiSet_hasSum_disjoint hp_ne_top φ hAm hAd

@[simp]
theorem phiSignedMeasure_apply {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp_ne_top : p ≠ ∞)
    (φ : LpPer p d →L[ℝ] ℝ) (A : Set (Fin d → ℝ)) :
    phiSignedMeasure (d := d) hp_ne_top φ A = phiSet (d := d) φ A := rfl

/-! ## Section 4 — Absolute continuity -/

private theorem indicatorConstLp_eq_zero_of_measure_zero
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp_ne_top : p ≠ ∞)
    {A : Set (Fin d → ℝ)} (hA : MeasurableSet A)
    (hμA : (μPer : Measure (Fin d → ℝ)) A = 0) :
    haveI := Saturator.instIsFiniteMeasureRestrictUnitCube (d := d)
    indicatorConstLp (μ := μPer) p hA
        (measure_ne_top _ _) (1 : ℝ) = 0 := by
  haveI := Saturator.instIsFiniteMeasureRestrictUnitCube (d := d)
  apply Lp.ext
  have h_coe := indicatorConstLp_coeFn (μ := μPer) (p := p)
    (hs := hA) (hμs := (measure_ne_top _ _ : μPer A ≠ ∞))
    (c := (1 : ℝ))
  have h_zero : ⇑(0 : LpPer p d) =ᵐ[μPer] (0 : (Fin d → ℝ) → ℝ) :=
    Lp.coeFn_zero ℝ p μPer
  have h_ind_zero : A.indicator (fun _ => (1 : ℝ)) =ᵐ[μPer]
      (0 : (Fin d → ℝ) → ℝ) := by
    rw [Filter.EventuallyEq, ae_iff]
    apply measure_mono_null _ hμA
    intro x hx
    by_contra hxA
    apply hx
    show A.indicator (fun _ => (1 : ℝ)) x = 0
    rw [Set.indicator_of_notMem hxA]
  exact h_coe.trans (h_ind_zero.trans h_zero.symm)

theorem phiSignedMeasure_absolutelyContinuous {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp_ne_top : p ≠ ∞)
    (φ : LpPer p d →L[ℝ] ℝ) :
    phiSignedMeasure (d := d) hp_ne_top φ
      ≪ᵥ (μPer : Measure (Fin d → ℝ)).toENNRealVectorMeasure := by
  refine MeasureTheory.VectorMeasure.AbsolutelyContinuous.mk ?_
  intro A hA hμA_zero
  haveI := Saturator.instIsFiniteMeasureRestrictUnitCube (d := d)
  rw [Measure.toENNRealVectorMeasure_apply_measurable hA] at hμA_zero
  show phiSet (d := d) φ A = 0
  rw [phiSet_apply_measurable φ hA]
  rw [indicatorConstLp_eq_zero_of_measure_zero hp_ne_top hA hμA_zero]
  exact map_zero φ

/-! ## Section 5 — The L¹ representer via Radon–Nikodym -/

/-- The L¹ representer
`g := (phiSignedMeasure φ).rnDeriv (volume.restrict (UnitCube d))`. -/
noncomputable def phiRepresenter {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp_ne_top : p ≠ ∞)
    (φ : LpPer p d →L[ℝ] ℝ) : (Fin d → ℝ) → ℝ :=
  (phiSignedMeasure (d := d) hp_ne_top φ).rnDeriv μPer

theorem integrable_phiRepresenter {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp_ne_top : p ≠ ∞)
    (φ : LpPer p d →L[ℝ] ℝ) :
    Integrable (phiRepresenter (d := d) hp_ne_top φ) μPer := by
  unfold phiRepresenter
  exact MeasureTheory.SignedMeasure.integrable_rnDeriv _ _

theorem aestronglyMeasurable_phiRepresenter {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp_ne_top : p ≠ ∞)
    (φ : LpPer p d →L[ℝ] ℝ) :
    AEStronglyMeasurable (phiRepresenter (d := d) hp_ne_top φ) μPer :=
  (integrable_phiRepresenter (d := d) hp_ne_top φ).aestronglyMeasurable

/-- `MemLp 1` membership of the representer. -/
theorem memLp_one_phiRepresenter {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp_ne_top : p ≠ ∞)
    (φ : LpPer p d →L[ℝ] ℝ) :
    MemLp (phiRepresenter (d := d) hp_ne_top φ) 1 μPer :=
  memLp_one_iff_integrable.mpr (integrable_phiRepresenter (d := d) hp_ne_top φ)

/-- **Indicator integral formula.** For measurable `A`,
`φ(𝟙_A · 1) = ∫_A g` where `g = phiRepresenter φ`. -/
theorem phi_indicator_eq_setIntegral {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp_ne_top : p ≠ ∞)
    (φ : LpPer p d →L[ℝ] ℝ)
    {A : Set (Fin d → ℝ)} (hA : MeasurableSet A) :
    haveI := Saturator.instIsFiniteMeasureRestrictUnitCube (d := d)
    φ (indicatorConstLp (μ := μPer) p hA
        (measure_ne_top _ _) (1 : ℝ)) =
      ∫ x in A, phiRepresenter (d := d) hp_ne_top φ x ∂μPer := by
  haveI := Saturator.instIsFiniteMeasureRestrictUnitCube (d := d)
  have h_phi_set : φ (indicatorConstLp (μ := μPer) p hA
        (measure_ne_top _ _) (1 : ℝ)) = phiSet (d := d) φ A :=
    (phiSet_apply_measurable φ hA).symm
  rw [h_phi_set]
  rw [← MeasureTheory.withDensityᵥ_apply
      (integrable_phiRepresenter (d := d) hp_ne_top φ) hA]
  have h_rn := MeasureTheory.SignedMeasure.withDensityᵥ_rnDeriv_eq
    (phiSignedMeasure (d := d) hp_ne_top φ) μPer
    (phiSignedMeasure_absolutelyContinuous hp_ne_top φ)
  show phiSet (d := d) φ A =
    (μPer : Measure (Fin d → ℝ)).withDensityᵥ
      (phiRepresenter (d := d) hp_ne_top φ) A
  show phiSet (d := d) φ A =
    (μPer : Measure (Fin d → ℝ)).withDensityᵥ
      ((phiSignedMeasure (d := d) hp_ne_top φ).rnDeriv μPer) A
  rw [h_rn]
  rfl

/-! ## Section 6 — Scalar indicator bridge -/

theorem phi_smul_indicator_eq_integral {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp_ne_top : p ≠ ∞)
    (φ : LpPer p d →L[ℝ] ℝ)
    {A : Set (Fin d → ℝ)} (hA : MeasurableSet A) (c : ℝ) :
    haveI := Saturator.instIsFiniteMeasureRestrictUnitCube (d := d)
    φ (c • indicatorConstLp (μ := μPer) p hA
        (measure_ne_top _ _) (1 : ℝ)) =
      ∫ x, A.indicator (fun _ => c) x *
        phiRepresenter (d := d) hp_ne_top φ x ∂μPer := by
  haveI := Saturator.instIsFiniteMeasureRestrictUnitCube (d := d)
  rw [φ.map_smul]
  rw [phi_indicator_eq_setIntegral hp_ne_top φ hA]
  rw [smul_eq_mul]
  rw [show c * (∫ x in A, phiRepresenter (d := d) hp_ne_top φ x ∂μPer)
        = ∫ x in A, c * phiRepresenter (d := d) hp_ne_top φ x ∂μPer from
        (integral_const_mul c _).symm]
  rw [← integral_indicator hA]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hxA : x ∈ A
  · rw [Set.indicator_of_mem hxA, Set.indicator_of_mem hxA]
  · rw [Set.indicator_of_notMem hxA, Set.indicator_of_notMem hxA, zero_mul]

/-! ## Section 7 — Simple-function integral formula -/

/-- **The simple-function integral formula.** For every
`s : Lp.simpleFunc ℝ p μPer`, `φ s = ∫ s · g` with
`g := phiRepresenter φ`. -/
theorem phi_simpleFunc_eq_integral
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp_ne_top : p ≠ ∞)
    (φ : LpPer p d →L[ℝ] ℝ)
    (s : Lp.simpleFunc ℝ p μPer) :
    φ (s : LpPer p d) =
      ∫ x, (s : LpPer p d) x *
        phiRepresenter (d := d) hp_ne_top φ x ∂μPer := by
  haveI := Saturator.instIsFiniteMeasureRestrictUnitCube (d := d)
  have hp_ne_zero : p ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by simp : (0 : ℝ≥0∞) < 1)
      (Fact.out : (1 : ℝ≥0∞) ≤ p))
  set μ : Measure (Fin d → ℝ) := μPer with hμ_def
  set g_repr : (Fin d → ℝ) → ℝ := phiRepresenter (d := d) hp_ne_top φ
    with hg_repr_def
  have hg_int : Integrable g_repr μ :=
    integrable_phiRepresenter (d := d) hp_ne_top φ
  apply Lp.simpleFunc.induction (p := p) (μ := μ) hp_ne_zero hp_ne_top
    (P := fun s' : Lp.simpleFunc ℝ p μ =>
      φ (s' : LpPer p d) =
        ∫ x, (s' : LpPer p d) x * g_repr x ∂μ)
  · intro c A hA hμA
    have h_lp_eq :
        ((Lp.simpleFunc.indicatorConst p hA hμA.ne c) : LpPer p d) =
        c • indicatorConstLp (μ := μ) p hA (measure_ne_top _ _) (1 : ℝ) := by
      rw [Lp.simpleFunc.coe_indicatorConst]
      refine Lp.ext ?_
      have h_c := indicatorConstLp_coeFn (μ := μ) (p := p)
        (hs := hA) (hμs := measure_ne_top _ _) (c := c)
      have h_smul := Lp.coeFn_smul (𝕜 := ℝ) c
        (indicatorConstLp (μ := μ) p hA (measure_ne_top _ _) (1 : ℝ))
      have h_one := indicatorConstLp_coeFn (μ := μ) (p := p)
        (hs := hA) (hμs := measure_ne_top _ _) (c := (1 : ℝ))
      filter_upwards [h_c, h_smul, h_one] with x hxc hxsmul hxone
      rw [hxc, hxsmul, Pi.smul_apply, hxone]
      by_cases hxA : x ∈ A
      · simp [Set.indicator_of_mem hxA]
      · simp [Set.indicator_of_notMem hxA]
    rw [h_lp_eq, φ.map_smul, phi_indicator_eq_setIntegral hp_ne_top φ hA]
    rw [smul_eq_mul]
    rw [show c * (∫ x in A, g_repr x ∂μ) =
            ∫ x in A, c * g_repr x ∂μ from (integral_const_mul c _).symm]
    rw [← integral_indicator hA]
    apply integral_congr_ae
    have h_smul := Lp.coeFn_smul (𝕜 := ℝ) c
      (indicatorConstLp (μ := μ) p hA (measure_ne_top _ _) (1 : ℝ))
    have h_one := indicatorConstLp_coeFn (μ := μ) (p := p)
      (hs := hA) (hμs := measure_ne_top _ _) (c := (1 : ℝ))
    filter_upwards [h_smul, h_one] with x hxsmul hxone
    rw [hxsmul, Pi.smul_apply, smul_eq_mul, hxone]
    by_cases hxA : x ∈ A
    · rw [Set.indicator_of_mem hxA, Set.indicator_of_mem hxA, mul_one]
    · rw [Set.indicator_of_notMem hxA, Set.indicator_of_notMem hxA,
          mul_zero, zero_mul]
  · intro f g_simp hf hg _ hf_eq hg_eq
    have h_add_coe :
        ((SimpleFunc.toLp f hf + SimpleFunc.toLp g_simp hg : Lp.simpleFunc ℝ p μ)
          : LpPer p d) =
        (SimpleFunc.toLp f hf : LpPer p d) +
        (SimpleFunc.toLp g_simp hg : LpPer p d) := rfl
    rw [h_add_coe, φ.map_add, hf_eq, hg_eq]
    obtain ⟨Mf, hMf⟩ := f.exists_forall_norm_le
    obtain ⟨Mg, hMg⟩ := g_simp.exists_forall_norm_le
    have hf_coe : ⇑(SimpleFunc.toLp f hf : LpPer p d) =ᵐ[μ] f := by
      have h := MemLp.coeFn_toLp hf
      have h_eq : ((SimpleFunc.toLp f hf : Lp.simpleFunc ℝ p μ)
          : LpPer p d) = hf.toLp f :=
        Lp.simpleFunc.toLp_eq_toLp f hf
      rw [h_eq]; exact h
    have hg_coe : ⇑(SimpleFunc.toLp g_simp hg : LpPer p d) =ᵐ[μ] g_simp := by
      have h := MemLp.coeFn_toLp hg
      have h_eq : ((SimpleFunc.toLp g_simp hg : Lp.simpleFunc ℝ p μ)
          : LpPer p d) = hg.toLp g_simp :=
        Lp.simpleFunc.toLp_eq_toLp g_simp hg
      rw [h_eq]; exact h
    have h_int_f : Integrable
        (fun x => (SimpleFunc.toLp f hf : LpPer p d) x * g_repr x) μ := by
      apply hg_int.bdd_mul (Lp.aestronglyMeasurable _) (c := Mf)
      filter_upwards [hf_coe] with x hx
      rw [hx]; exact hMf x
    have h_int_g : Integrable
        (fun x => (SimpleFunc.toLp g_simp hg : LpPer p d) x * g_repr x) μ := by
      apply hg_int.bdd_mul (Lp.aestronglyMeasurable _) (c := Mg)
      filter_upwards [hg_coe] with x hx
      rw [hx]; exact hMg x
    rw [← MeasureTheory.integral_add h_int_f h_int_g]
    apply integral_congr_ae
    have h_sum_coe := Lp.coeFn_add
      (SimpleFunc.toLp f hf : LpPer p d)
      (SimpleFunc.toLp g_simp hg : LpPer p d)
    filter_upwards [h_sum_coe] with x hx
    rw [hx, Pi.add_apply, add_mul]

/-! ## Section 8 — Unconditional Riesz for `2 ≤ p < ∞`

Combining the L¹ representer (`phiRepresenter`), the simple-function
identity (`phi_simpleFunc_eq_integral`), the bounded-`Lp` extension
(`phi_eq_integral_of_bounded_simple_hyp`), the saturator argument
(`representer_memLq_and_norm_le`), and `Lp.induction`, we obtain the
unconditional Riesz representation theorem on the unit cube for
`2 ≤ p < ∞`. The hypothesis `2 ≤ p` is recorded for symmetry with the
`p ≤ 2` half but is not used in the proof body — once the L¹ candidate
is in hand, only `1 < p < ∞` is needed.

Adapted from
`LpSpaces.LpDualityFinitePQ.exists_representer_norm_eq_of_two_le_p`.
-/

/-- **Existence of the `Lᵠ` representer with norm equality** for
`2 ≤ p < ∞` on the unit cube. Every continuous linear functional
`φ : LpPer p d →L[ℝ] ℝ` is represented by integration against a
function `g ∈ Lᵠ(μ)`, and the matching `Lᵠ` norm equals `‖φ‖`. The
candidate `g := phiRepresenter φ` is the L¹ Radon–Nikodym derivative of
the signed measure `A ↦ φ(𝟙_A)`.

Adapted from
`LpSpaces.LpDualityFinitePQ.exists_representer_norm_eq_of_two_le_p`. -/
theorem exists_representer_norm_eq_of_two_le_p
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (hp_gt_one : 1 < p) (_hp_ge_two : 2 ≤ p) (hp_ne_top : p ≠ ∞)
    (φ : LpPer p d →L[ℝ] ℝ) :
    ∃ g : (Fin d → ℝ) → ℝ,
      MemLp g q (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d))
      ∧ (∀ f : LpPer p d,
          φ f = ∫ x, f x * g x
            ∂(Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)))
      ∧ eLpNorm g q
          (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d))
        = ENNReal.ofReal ‖φ‖ := by
  set μ : Measure (Fin d → ℝ) := Measure.restrict volume (UnitCube d) with hμ_def
  haveI : IsFiniteMeasure μ := Saturator.instIsFiniteMeasureRestrictUnitCube
  have hp_ne_zero : p ≠ 0 := by
    intro h; rw [h] at hp_gt_one; exact absurd hp_gt_one (by norm_num)
  -- Step 1. L¹ candidate from the Radon–Nikodym construction.
  set g : (Fin d → ℝ) → ℝ := phiRepresenter (d := d) hp_ne_top φ with hg_def
  have hg_aesm : AEStronglyMeasurable g μ :=
    aestronglyMeasurable_phiRepresenter (d := d) hp_ne_top φ
  have hg_int : Integrable g μ :=
    integrable_phiRepresenter (d := d) hp_ne_top φ
  -- Step 2. Simple-function integral identity.
  have h_simple_id : ∀ s : Lp.simpleFunc ℝ p μ,
      φ ((s : LpPer p d)) =
        ∫ x, ((s : LpPer p d)) x * g x ∂μ :=
    phi_simpleFunc_eq_integral (d := d) hp_ne_top φ
  -- Step 3. Bounded-`Lp` integral identity via the simple-function
  -- extension lemma.
  have h_bdd_id : ∀ (h : LpPer p d) (M : ℝ),
      (∀ᵐ x ∂μ, ‖h x‖ ≤ M) →
      φ h = ∫ x, h x * g x ∂μ := by
    intro h M hM_bd
    have hM_abs_nn : 0 ≤ |M| := abs_nonneg M
    have hM_abs_bd : ∀ᵐ x ∂μ, ‖h x‖ ≤ |M| := by
      filter_upwards [hM_bd] with x hx; exact hx.trans (le_abs_self M)
    exact phi_eq_integral_of_bounded_simple_hyp (d := d)
      hp_ne_top φ g hg_int h_simple_id h |M| hM_abs_nn hM_abs_bd
  -- Step 4. Apply `representer_memLq_and_norm_le` for `MemLp g q` and
  -- `eLpNorm g q μ ≤ ENNReal.ofReal ‖φ‖`.
  have h_repr_memLq :=
    representer_memLq_and_norm_le (d := d) (p := p) (q := q)
      hp_gt_one hp_ne_top φ g hg_aesm h_bdd_id
  obtain ⟨hg_memLp_q, hg_norm_le⟩ := h_repr_memLq
  -- Step 5. Hölder bound on `f ↦ ∫ f * g` (verbatim mirror of the
  -- corresponding block in `exists_representer_norm_eq_of_p_le_two`).
  have hq_lt_top : q < ∞ := by
    rw [ENNReal.HolderConjugate.lt_top_iff_one_lt q p]; exact hp_gt_one
  have hq_ne_top : q ≠ ∞ := hq_lt_top.ne
  have h_holder_bound : ∀ f : LpPer p d,
      ‖∫ x, f x * g x ∂μ‖ ≤
        (eLpNorm (⇑f) p μ).toReal * (eLpNorm g q μ).toReal := by
    intro f
    have hf_aesm : AEStronglyMeasurable (⇑f) μ := Lp.aestronglyMeasurable f
    have hf_memLp : MemLp (⇑f) p μ := Lp.memLp f
    have h1 : ‖∫ x, f x * g x ∂μ‖ ≤ ∫ x, ‖f x * g x‖ ∂μ :=
      norm_integral_le_integral_norm _
    haveI : ENNReal.HolderTriple p q 1 := inferInstance
    have hmemL1 : MemLp (fun x => f x * g x) 1 μ := by
      exact MemLp.fun_mul (μ := μ) (p := p) (q := q) (r := 1)
        hf_memLp hg_memLp_q
    have h_toReal : ∫ x, ‖f x * g x‖ ∂μ
        = (eLpNorm (fun x => f x * g x) 1 μ).toReal := by
      have h_aesm_mul : AEStronglyMeasurable
          (fun x : (Fin d → ℝ) => f x * g x) μ := hf_aesm.mul hg_aesm
      rw [eLpNorm_one_eq_lintegral_enorm h_aesm_mul]
      have h1' : ∫ x, ‖f x * g x‖ ∂μ
          = (∫⁻ x, ENNReal.ofReal ‖f x * g x‖ ∂μ).toReal :=
        integral_eq_lintegral_of_nonneg_ae
          (Filter.Eventually.of_forall (fun x => norm_nonneg _))
          h_aesm_mul.norm
      rw [h1']
      congr 1
      apply lintegral_congr_ae
      filter_upwards with x
      rw [ofReal_norm_eq_enorm]
    have h_holder :
        eLpNorm (fun x => f x * g x) 1 μ ≤ eLpNorm (⇑f) p μ * eLpNorm g q μ := by
      have :=
        MeasureTheory.eLpNorm_smul_le_mul_eLpNorm
          (μ := μ) (𝕜 := ℝ) (p := p) (q := q) (r := 1)
          (f := g) (φ := (⇑f : (Fin d → ℝ) → ℝ))
          hf_aesm hg_aesm
      simpa only [Pi.smul_apply', smul_eq_mul] using! this
    have hf_top : eLpNorm (⇑f) p μ ≠ ∞ := hf_memLp.eLpNorm_ne_top
    have hg_top : eLpNorm g q μ ≠ ∞ := hg_memLp_q.eLpNorm_ne_top
    have h_mul_top : eLpNorm (⇑f) p μ * eLpNorm g q μ ≠ ∞ :=
      ENNReal.mul_ne_top hf_top hg_top
    have h_holder_real :
        (eLpNorm (fun x => f x * g x) 1 μ).toReal ≤
          (eLpNorm (⇑f) p μ).toReal * (eLpNorm g q μ).toReal := by
      have := ENNReal.toReal_mono h_mul_top h_holder
      simpa [ENNReal.toReal_mul] using this
    calc ‖∫ x, f x * g x ∂μ‖
        ≤ ∫ x, ‖f x * g x‖ ∂μ := h1
      _ = (eLpNorm (fun x => f x * g x) 1 μ).toReal := h_toReal
      _ ≤ (eLpNorm (⇑f) p μ).toReal * (eLpNorm g q μ).toReal := h_holder_real
  -- Step 6. Continuous integral functional, agreement on simple functions
  -- and `Lp.induction`. Same skeleton as in `exists_representer_norm_eq_of_p_le_two`.
  haveI hpq1 : ENNReal.HolderTriple p q 1 := inferInstance
  have hi : ∀ f' : LpPer p d, Integrable (fun x => f' x * g x) μ := by
    intro f'
    have hf'_memLp : MemLp (⇑f') p μ := Lp.memLp f'
    have hL1 : MemLp (fun x => f' x * g x) 1 μ :=
      MemLp.fun_mul (μ := μ) (p := p) (q := q) (r := 1) hf'_memLp hg_memLp_q
    exact memLp_one_iff_integrable.mp hL1
  let ψgL : LpPer p d →ₗ[ℝ] ℝ :=
    { toFun := fun f' => ∫ x, f' x * g x ∂μ
      map_add' := by
        intro f₁ f₂
        have hadd := Lp.coeFn_add f₁ f₂
        have h_ae : (fun x => (f₁ + f₂) x * g x)
            =ᵐ[μ] fun x => f₁ x * g x + f₂ x * g x := by
          filter_upwards [hadd] with x hx
          rw [hx]
          simp [Pi.add_apply, add_mul]
        rw [integral_congr_ae h_ae, integral_add (hi f₁) (hi f₂)]
      map_smul' := by
        intro c f'
        have hcf := Lp.coeFn_smul c f'
        have h_ae : (fun x => (c • f') x * g x)
            =ᵐ[μ] fun x => c * (f' x * g x) := by
          filter_upwards [hcf] with x hx
          rw [hx]; simp [Pi.smul_apply, smul_eq_mul, mul_assoc]
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [integral_congr_ae h_ae, integral_const_mul] }
  let ψg : LpPer p d →L[ℝ] ℝ :=
    ψgL.mkContinuous ((eLpNorm g q μ).toReal) (fun f => by
      change ‖∫ x, f x * g x ∂μ‖ ≤ (eLpNorm g q μ).toReal * ‖f‖
      have h := h_holder_bound f
      rw [Lp.norm_def, mul_comm]
      exact h)
  have hψg_apply : ∀ f : LpPer p d, ψg f = ∫ x, f x * g x ∂μ := by
    intro f; rfl
  -- Show `φ - ψg = 0` via `Lp.induction`.
  have h_diff_zero : φ - ψg = 0 := by
    apply ContinuousLinearMap.ext
    intro f'
    change φ f' - ψg f' = 0
    revert f'
    apply Lp.induction (E := ℝ) (p := p) (μ := μ) hp_ne_top
      (motive := fun f' => φ f' - ψg f' = 0)
    · intro c s hs hμs
      set f_ind : LpPer p d :=
        (Lp.simpleFunc.indicatorConst p hs hμs.ne c : LpPer p d)
        with hf_ind_def
      have h_ae_f : ⇑f_ind =ᵐ[μ] s.indicator (fun _ => c) := by
        show ⇑((Lp.simpleFunc.indicatorConst p hs hμs.ne c :
            Lp.simpleFunc ℝ p μ) : LpPer p d) =ᵐ[μ] s.indicator (fun _ => c)
        rw [Lp.simpleFunc.coe_indicatorConst]
        exact indicatorConstLp_coeFn
      have h_bound : ∀ᵐ x ∂μ, ‖f_ind x‖ ≤ ‖c‖ := by
        filter_upwards [h_ae_f] with x hx
        rw [hx]
        by_cases hxs : x ∈ s
        · rw [Set.indicator_of_mem hxs]
        · rw [Set.indicator_of_notMem hxs]; simp
      have hφf := h_bdd_id f_ind ‖c‖ h_bound
      rw [hψg_apply f_ind, hφf, sub_self]
    · intro f₁ f₂ hf₁ hf₂ _ hf₁_eq hf₂_eq
      rw [map_add, map_add]
      linarith [hf₁_eq, hf₂_eq]
    · have h_cont : Continuous fun f' : LpPer p d => φ f' - ψg f' :=
        Continuous.sub φ.continuous ψg.continuous
      exact isClosed_eq h_cont continuous_const
  have h_full_id : ∀ f : LpPer p d, φ f = ∫ x, f x * g x ∂μ := by
    intro f
    have hcong := congrArg (fun T : LpPer p d →L[ℝ] ℝ => T f) h_diff_zero
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.zero_apply] at hcong
    have h_eq : φ f - ψg f = 0 := hcong
    have h_ψg : ψg f = ∫ x, f x * g x ∂μ := hψg_apply f
    linarith [h_ψg, h_eq]
  -- Step 7. Lower bound `‖φ‖ ≤ (eLpNorm g q μ).toReal` via Hölder.
  have h_phi_nn : 0 ≤ ‖φ‖ := norm_nonneg _
  have h_gnorm_nn : 0 ≤ (eLpNorm g q μ).toReal := ENNReal.toReal_nonneg
  have h_lower : ‖φ‖ ≤ (eLpNorm g q μ).toReal := by
    refine ContinuousLinearMap.opNorm_le_bound _ h_gnorm_nn ?_
    intro f
    rw [h_full_id f, Real.norm_eq_abs]
    have h := h_holder_bound f
    rw [Real.norm_eq_abs] at h
    rw [Lp.norm_def, mul_comm]
    exact h
  -- Step 8. Norm equality.
  have h_eLp_top : eLpNorm g q μ ≠ ∞ := hg_memLp_q.eLpNorm_ne_top
  have h_eLp_eq_ofReal : eLpNorm g q μ = ENNReal.ofReal (eLpNorm g q μ).toReal :=
    (ENNReal.ofReal_toReal h_eLp_top).symm
  have h_norm_eq : eLpNorm g q μ = ENNReal.ofReal ‖φ‖ := by
    have h_le_real : (eLpNorm g q μ).toReal ≤ ‖φ‖ := by
      have := ENNReal.toReal_mono (by simp) hg_norm_le
      simpa [ENNReal.toReal_ofReal h_phi_nn] using this
    have h_real_eq : (eLpNorm g q μ).toReal = ‖φ‖ :=
      le_antisymm h_le_real h_lower
    rw [h_eLp_eq_ofReal, h_real_eq]
  exact ⟨g, hg_memLp_q, h_full_id, h_norm_eq⟩

end LpDualityRN

/-! ## Unified Riesz representation for `1 < p < ∞` on the unit cube

Combines the two halves
* `exists_representer_norm_eq_of_p_le_two` (Part A, `1 < p ≤ 2`), and
* `LpDualityRN.exists_representer_norm_eq_of_two_le_p`
  (Part B, `2 ≤ p < ∞`),

into a single Riesz representation theorem on the unit cube, dispatched
by `p ≤ 2` vs `p > 2`.

Adapted from
`LpSpaces.LpDualityFinitePQ.exists_representer_norm_eq`. -/

/-- **Finite-measure Riesz representation theorem on the unit cube,
`1 < p < ∞`.**

For every continuous linear functional `φ : LpPer p d →L[ℝ] ℝ`, there is a
function `g ∈ Lᵠ(volume.restrict (UnitCube d))` (with `q` the Hölder
conjugate of `p`) such that

* `φ f = ∫ x, f x * g x ∂μ` for every `f : LpPer p d`, and
* `eLpNorm g q μ = ENNReal.ofReal ‖φ‖`.

The proof dispatches on `p ≤ 2` vs `p > 2`, using the `p ≤ 2` half at the
boundary value `p = 2`. -/
theorem exists_representer_norm_eq
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (hp_gt_one : 1 < p) (hp_ne_top : p ≠ ∞)
    (φ : LpPer p d →L[ℝ] ℝ) :
    ∃ g : (Fin d → ℝ) → ℝ,
      MemLp g q (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d))
      ∧ (∀ f : LpPer p d,
          φ f = ∫ x, f x * g x
            ∂(Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)))
      ∧ eLpNorm g q
          (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d))
        = ENNReal.ofReal ‖φ‖ := by
  by_cases hp2 : p ≤ 2
  · exact exists_representer_norm_eq_of_p_le_two
      (p := p) (q := q) hp_gt_one hp2 hp_ne_top φ
  · push_neg at hp2
    exact LpDualityRN.exists_representer_norm_eq_of_two_le_p
      (p := p) (q := q) hp_gt_one hp2.le hp_ne_top φ

end Periodic
end StationaryMFG
