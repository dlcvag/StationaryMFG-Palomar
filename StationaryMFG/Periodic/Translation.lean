module

public import StationaryMFG.Periodic.Lp
public import StationaryMFG.Periodic.Integral
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

@[expose] public section

/-!
# Translation continuity in `L^p_per`

For `MemLpPer p f` with `1 ≤ p < ∞` and `f` periodic, this file proves

`Tendsto (fun y => eLpNormPer p (fun x => f (x - y) - f x)) (𝓝 0) (𝓝 0)`.

The strategy reduces to whole-space translation continuity in `Lp(ℝ^d, volume)`
applied to a truncated version of `f`. Adapted from `LpSpaces.Translation.lean`.

Outline.

1. **Whole-space translation continuity** (`tendsto_eLpNorm_translate_sub`).
   For `g ∈ MemLp p volume` with `p ≠ ∞`, the eLpNorm of `g(· - y) - g(·)`
   tends to `0` as `y → 0`. Follows from Mathlib's
   `Filter.Tendsto.compMeasurePreservingLp` applied to the family of
   continuous measure-preserving translations.

2. **Truncated periodic function** `palomar_Translation_fTrunc`. Define
   `palomar_Translation_fTrunc f := Σ k ∈ {-2,-1,0,1}^d, (palomar_Translation_shiftedCube k).indicator f` where
   `palomar_Translation_shiftedCube k = [k, k+1)^d`. The cube translates partition `[-2, 2)^d` and
   have pairwise disjoint supports. Each summand lies in `MemLp p volume` because
   under translation invariance and periodicity, its `eLpNorm` equals
   `eLpNormPer p f`. A finite sum of `MemLp` is `MemLp`.

3. **Pointwise agreement**. For `x ∈ UnitCube` and `‖y i‖ ≤ 1` for all `i`,
   both `x` and `x - y` lie in `[-2, 2)^d`, so `palomar_Translation_fTrunc f x = f x` and
   `palomar_Translation_fTrunc f (x - y) = f (x - y)`.

4. **Final bound**. The cube `eLpNormPer p (f(·-y) - f(·))` equals the cube
   `eLpNorm` of `palomar_Translation_fTrunc f (· - y) - palomar_Translation_fTrunc f` (by 3 and `eLpNorm_congr_ae`). That
   in turn is bounded by the whole-space `eLpNorm` (`eLpNorm_mono_measure` with
   `Measure.restrict_le_self`). Step 1 sends the right-hand side to zero.

-- Adapted from LpSpaces.Translation (whole-space translation continuity in Lp).
-/

namespace StationaryMFG
namespace Periodic

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

variable {d : ℕ}

/-! ## Step 1: whole-space translation continuity in `Lp` -/

/-- **Whole-space translation continuity in `Lp(ℝ^d, volume)`.** For `p ≠ ∞`
and `g ∈ MemLp p volume`, `‖g(· - y) - g(·)‖_p → 0` as `y → 0`. -/
theorem tendsto_eLpNorm_translate_sub
    {p : ℝ≥0∞} (hp : p ≠ ∞) [Fact (1 ≤ p)]
    {g : (Fin d → ℝ) → ℝ} (hg : MemLp g p (volume : Measure (Fin d → ℝ))) :
    Tendsto (fun y : Fin d → ℝ =>
      eLpNorm (fun x => g (x - y) - g x) p volume) (𝓝 0) (𝓝 0) := by
  -- Package `(· - y)` as a continuous family of measure-preserving maps.
  let F : (Fin d → ℝ) → C(Fin d → ℝ, Fin d → ℝ) := fun y =>
    ⟨fun x => x - y, continuous_id.sub continuous_const⟩
  have hF_cont : Continuous F :=
    ContinuousMap.continuous_of_continuous_uncurry F
      (continuous_snd.sub continuous_fst)
  have hFG : Tendsto F (𝓝 0) (𝓝 (F 0)) := hF_cont.tendsto 0
  have hF_mp : ∀ y : Fin d → ℝ,
      MeasurePreserving (F y) (volume : Measure (Fin d → ℝ)) volume := fun y =>
    measurePreserving_sub_right (volume : Measure (Fin d → ℝ)) y
  have hF0_mp : MeasurePreserving (F 0) (volume : Measure (Fin d → ℝ)) volume :=
    hF_mp 0
  -- Apply Mathlib's compMeasurePreservingLp continuity lemma.
  set gLp := hg.toLp g with hgLp_def
  have h_const : Tendsto (fun _ : Fin d → ℝ => gLp) (𝓝 0) (𝓝 gLp) :=
    tendsto_const_nhds
  have h_lp :
      Tendsto (fun y : Fin d → ℝ =>
          Lp.compMeasurePreserving (F y) (hF_mp y) gLp) (𝓝 0)
        (𝓝 (Lp.compMeasurePreserving (F 0) hF0_mp gLp)) :=
    Filter.Tendsto.compMeasurePreservingLp h_const hFG hF_mp hF0_mp hp
  -- Convert to a tendsto on the difference's Lp norm.
  let φ : (Fin d → ℝ) → Lp ℝ p (volume : Measure (Fin d → ℝ)) :=
    fun y => Lp.compMeasurePreserving (F y) (hF_mp y) gLp
  have h_diff : Tendsto (fun y => φ y - φ 0) (𝓝 0) (𝓝 0) := by
    have := h_lp.sub (tendsto_const_nhds (x := φ 0))
    -- The target `(fun y => φ y - φ 0)` matches `this` after rewriting `φ 0 - φ 0 = 0`.
    have hzero : φ 0 - φ 0 = (0 : Lp ℝ p (volume : Measure (Fin d → ℝ))) := sub_self _
    rw [← hzero]
    exact this
  have h_norm : Tendsto (fun y => ‖φ y - φ 0‖) (𝓝 0) (𝓝 0) := by
    simpa using h_diff.norm
  -- Identify ‖φ y - φ 0‖ with (eLpNorm (g(·-y) - g)).toReal.
  have h_eq_real : ∀ y : Fin d → ℝ,
      ‖φ y - φ 0‖ = (eLpNorm (fun x => g (x - y) - g x) p volume).toReal := by
    intro y
    rw [Lp.norm_def]
    congr 1
    apply eLpNorm_congr_ae
    have hsub : ⇑(φ y - φ 0) =ᵐ[volume] fun x => φ y x - φ 0 x := Lp.coeFn_sub _ _
    have hgae : ⇑gLp =ᵐ[volume] g := MemLp.coeFn_toLp hg
    have hh1 : ⇑(φ y) =ᵐ[volume] gLp ∘ (F y) :=
      Lp.coeFn_compMeasurePreserving gLp (hF_mp y)
    have hh2 : (gLp : (Fin d → ℝ) → ℝ) ∘ (F y) =ᵐ[volume] g ∘ (F y) :=
      (hF_mp y).quasiMeasurePreserving.ae_eq_comp hgae
    have hh : ⇑(φ y) =ᵐ[volume] g ∘ (F y) := hh1.trans hh2
    have h01 : ⇑(φ 0) =ᵐ[volume] gLp ∘ (F 0) :=
      Lp.coeFn_compMeasurePreserving gLp hF0_mp
    have h02 : (gLp : (Fin d → ℝ) → ℝ) ∘ (F 0) =ᵐ[volume] g ∘ (F 0) :=
      hF0_mp.quasiMeasurePreserving.ae_eq_comp hgae
    have h0 : ⇑(φ 0) =ᵐ[volume] g ∘ (F 0) := h01.trans h02
    filter_upwards [hsub, hh, h0] with x hxsub hxh hx0
    simp only [hxsub, hxh, hx0, Function.comp_apply, F, sub_zero,
      ContinuousMap.coe_mk]
  -- The eLpNorm of the difference is finite.
  have h_finite : ∀ y : Fin d → ℝ,
      eLpNorm (fun x => g (x - y) - g x) p volume ≠ ⊤ := by
    intro y
    have hgy : MemLp (fun x => g (x - y)) p volume := by
      have := hg.comp_measurePreserving (hF_mp y)
      simpa only [F, Function.comp_def, ContinuousMap.coe_mk] using this
    exact (hgy.sub hg).ne
  have h_toReal :
      Tendsto (fun y : Fin d → ℝ =>
          (eLpNorm (fun x => g (x - y) - g x) p volume).toReal) (𝓝 0) (𝓝 0) := by
    have heq : (fun y : Fin d → ℝ =>
          (eLpNorm (fun x => g (x - y) - g x) p volume).toReal)
        = fun y => ‖φ y - φ 0‖ := by funext y; rw [h_eq_real]
    rw [heq]; exact h_norm
  exact (ENNReal.tendsto_toReal_zero_iff h_finite).mp h_toReal

/-! ## Step 2: definitions for the truncation -/

/-- The integer translates of `UnitCube d` we sum over: coordinates in
`{-2, -1, 0, 1}`. -/
def palomar_Translation_cubeTranslates (d : ℕ) : Finset (Fin d → ℤ) := by
  classical
  exact Fintype.piFinset (fun _ : Fin d => ({-2, -1, 0, 1} : Finset ℤ))

/-- The shifted cube `[k, k+1)^d`, presented as `(·-k)⁻¹' UnitCube`. -/
def palomar_Translation_shiftedCube (k : Fin d → ℤ) : Set (Fin d → ℝ) :=
  (fun y : Fin d → ℝ => y - fun i => (k i : ℝ)) ⁻¹' UnitCube d

private lemma measurableSet_shiftedCube (k : Fin d → ℤ) :
    MeasurableSet (palomar_Translation_shiftedCube k : Set (Fin d → ℝ)) :=
  measurableSet_unitCube.preimage (measurable_id.sub_const _)

private lemma mem_shiftedCube_iff (k : Fin d → ℤ) (x : Fin d → ℝ) :
    x ∈ (palomar_Translation_shiftedCube k : Set (Fin d → ℝ)) ↔
      ∀ i, (k i : ℝ) ≤ x i ∧ x i < (k i : ℝ) + 1 := by
  unfold palomar_Translation_shiftedCube UnitCube
  simp only [mem_preimage, Set.mem_pi, mem_univ, true_implies, Set.mem_Ico, Pi.sub_apply]
  refine ⟨fun h i => ?_, fun h i => ?_⟩
  · rcases h i with ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rcases h i with ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

/-- The shifted cubes are pairwise disjoint. -/
private lemma shiftedCube_pairwise_disjoint
    (k k' : Fin d → ℤ) (hkk' : k ≠ k') :
    Disjoint (palomar_Translation_shiftedCube k : Set (Fin d → ℝ)) (palomar_Translation_shiftedCube k') := by
  rw [Set.disjoint_iff]
  intro x ⟨hxk, hxk'⟩
  apply hkk'
  exact unique_int_translate_of_mem_unitCube hxk hxk'

/-- The truncation: a finite sum of indicators on cube translates. -/
noncomputable def palomar_Translation_fTrunc (f : (Fin d → ℝ) → ℝ) : (Fin d → ℝ) → ℝ := by
  classical
  exact ∑ k ∈ palomar_Translation_cubeTranslates d, (palomar_Translation_shiftedCube k).indicator f

/-! ### Pointwise behaviour of `palomar_Translation_fTrunc` -/

private lemma fTrunc_apply_of_mem_shiftedCube
    {f : (Fin d → ℝ) → ℝ} {k : Fin d → ℤ} {x : Fin d → ℝ}
    (hk : k ∈ palomar_Translation_cubeTranslates d) (hx : x ∈ (palomar_Translation_shiftedCube k : Set (Fin d → ℝ))) :
    palomar_Translation_fTrunc f x = f x := by
  classical
  unfold palomar_Translation_fTrunc
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single k]
  · simp [Set.indicator_of_mem hx]
  · intro k' _ hkne
    apply Set.indicator_of_notMem
    intro hxk'
    have hdisj := shiftedCube_pairwise_disjoint k' k hkne
    exact Set.disjoint_left.mp hdisj hxk' hx
  · intro hk_notin
    exact (hk_notin hk).elim

/-- A point `x` whose coordinates lie in `[-2, 2)` belongs to some shifted cube
indexed by `palomar_Translation_cubeTranslates d`. -/
private lemma exists_cubeTranslate_of_coords
    {x : Fin d → ℝ} (hx : ∀ i, -2 ≤ x i ∧ x i < 2) :
    ∃ k ∈ palomar_Translation_cubeTranslates d, x ∈ (palomar_Translation_shiftedCube k : Set (Fin d → ℝ)) := by
  classical
  refine ⟨fun i => ⌊x i⌋, ?_, ?_⟩
  · unfold palomar_Translation_cubeTranslates
    refine Fintype.mem_piFinset.mpr ?_
    intro i
    have hxi := hx i
    have hfi_ge : (-2 : ℤ) ≤ ⌊x i⌋ := by
      have hge : ((-2 : ℤ) : ℝ) ≤ x i := by exact_mod_cast hxi.1
      exact Int.le_floor.mpr hge
    have hfi_lt : ⌊x i⌋ < 2 := by
      have hlt : x i < ((2 : ℤ) : ℝ) := by exact_mod_cast hxi.2
      exact Int.floor_lt.mpr hlt
    have hfi_le : ⌊x i⌋ ≤ 1 := by omega
    interval_cases (⌊x i⌋) <;> simp
  · rw [mem_shiftedCube_iff]
    intro i
    refine ⟨Int.floor_le _, ?_⟩
    have := Int.lt_floor_add_one (x i)
    linarith

/-- For `x ∈ UnitCube` and `‖y i‖ ≤ 1`, `palomar_Translation_fTrunc f` agrees with `f` at both `x`
and `x - y`. -/
private lemma fTrunc_eq_on_unitCube_with_buffer
    {f : (Fin d → ℝ) → ℝ} {x y : Fin d → ℝ}
    (hx : x ∈ UnitCube d) (hy : ∀ i, |y i| ≤ 1) :
    palomar_Translation_fTrunc f x = f x ∧ palomar_Translation_fTrunc f (x - y) = f (x - y) := by
  rw [mem_unitCube_iff] at hx
  have hx_buf : ∀ i, -2 ≤ x i ∧ x i < 2 := fun i =>
    ⟨by linarith [(hx i).1], by linarith [(hx i).2]⟩
  have hxy_buf : ∀ i, -2 ≤ (x - y) i ∧ (x - y) i < 2 := fun i => by
    have hyi_le : y i ≤ 1 := (abs_le.mp (hy i)).2
    have hyi_ge : -1 ≤ y i := (abs_le.mp (hy i)).1
    simp only [Pi.sub_apply]
    exact ⟨by linarith [(hx i).1], by linarith [(hx i).2]⟩
  obtain ⟨k, hk, hxk⟩ := exists_cubeTranslate_of_coords hx_buf
  obtain ⟨k', hk', hxyk'⟩ := exists_cubeTranslate_of_coords hxy_buf
  exact ⟨fTrunc_apply_of_mem_shiftedCube hk hxk,
        fTrunc_apply_of_mem_shiftedCube hk' hxyk'⟩

/-! ## Step 3: each indicator-on-shifted-cube lies in `MemLp p volume` -/

/-- Identify `volume.restrict (palomar_Translation_shiftedCube k)` as a pushforward of
`volume.restrict UnitCube` by the translation `(· + k_ℝ)`. -/
private lemma restrict_shiftedCube_eq_map (k : Fin d → ℤ) :
    (volume : Measure (Fin d → ℝ)).restrict (palomar_Translation_shiftedCube k)
      = Measure.map (fun x : Fin d → ℝ => x + fun i => (k i : ℝ))
          ((volume : Measure (Fin d → ℝ)).restrict (UnitCube d)) := by
  set y : Fin d → ℝ := fun i => (k i : ℝ) with hy_def
  have hmp : MeasurePreserving (fun x : Fin d → ℝ => x + y)
      (volume : Measure (Fin d → ℝ)) volume :=
    measurePreserving_add_right volume y
  -- Identify `(·+y) ⁻¹' palomar_Translation_shiftedCube k = UnitCube d`.
  have hpre : (fun x : Fin d → ℝ => x + y) ⁻¹' (palomar_Translation_shiftedCube k) = UnitCube d := by
    ext x
    unfold palomar_Translation_shiftedCube
    constructor
    · intro hx
      -- hx : (x + y) ∈ (·-y) ⁻¹' UnitCube, i.e. (x+y) - y ∈ UnitCube.
      simp only [Set.mem_preimage] at hx
      have : (x + y) - y = x := by ext i; simp [Pi.add_apply, Pi.sub_apply]
      rwa [this] at hx
    · intro hx
      simp only [Set.mem_preimage]
      have hxsub : (x + y) - y = x := by
        ext i; simp [Pi.add_apply, Pi.sub_apply]
      rw [hxsub]
      exact hx
  -- Use `Measure.restrict_map` after rewriting via translation invariance.
  conv_lhs => rw [← hmp.map_eq]
  rw [Measure.restrict_map hmp.measurable (measurableSet_shiftedCube k), hpre]

/-- Each indicator-on-shifted-cube lies in `MemLp p volume`, with the same
seminorm as `eLpNormPer p f`. -/
private lemma memLp_indicator_shiftedCube
    {p : ℝ≥0∞} {f : (Fin d → ℝ) → ℝ} (hf : MemLpPer p f) (hper : IsPeriodic f)
    (k : Fin d → ℤ) :
    MemLp ((palomar_Translation_shiftedCube k).indicator f) p (volume : Measure (Fin d → ℝ)) := by
  rw [memLp_indicator_iff_restrict (measurableSet_shiftedCube k).nullMeasurableSet]
  rw [restrict_shiftedCube_eq_map k]
  set y : Fin d → ℝ := fun i => (k i : ℝ) with hy_def
  have hembed : MeasurableEmbedding (fun x : Fin d → ℝ => x + y) :=
    (MeasurableEquiv.addRight y).measurableEmbedding
  rw [hembed.memLp_map_measure_iff]
  -- `MemLp (f ∘ (·+y)) p (volume.restrict UnitCube)`.
  have hcomp : (f ∘ fun x : Fin d → ℝ => x + y) = f := by
    funext x; exact hper k x
  rw [hcomp]
  exact hf.toMemLp

/-! ## Step 4: `palomar_Translation_fTrunc f ∈ MemLp p volume` -/

/-- A finite sum of `MemLp` functions is `MemLp`. -/
private lemma memLp_finset_sum_aux {α : Type*} {m : MeasurableSpace α}
    {μ : Measure α} {p : ℝ≥0∞}
    {ι : Type*} (s : Finset ι) {F : ι → α → ℝ}
    (hF : ∀ i ∈ s, MemLp (F i) p μ) :
    MemLp (fun x => ∑ i ∈ s, F i x) p μ := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    exact (MemLp.zero : MemLp (fun _ : α => (0 : ℝ)) p μ)
  | insert i s hins ih =>
    have hi : MemLp (F i) p μ := hF i (Finset.mem_insert_self i s)
    have hsub : ∀ j ∈ s, MemLp (F j) p μ := fun j hj =>
      hF j (Finset.mem_insert_of_mem hj)
    have hsum : MemLp (fun x => ∑ j ∈ s, F j x) p μ := ih hsub
    have hadd : MemLp (fun x => F i x + ∑ j ∈ s, F j x) p μ := hi.add hsum
    have heq : (fun x => F i x + ∑ j ∈ s, F j x)
        = fun x => ∑ j ∈ insert i s, F j x := by
      funext x; rw [Finset.sum_insert hins]
    rw [heq] at hadd
    exact hadd

private lemma memLp_fTrunc
    {p : ℝ≥0∞}
    {f : (Fin d → ℝ) → ℝ} (hf : MemLpPer p f) (hper : IsPeriodic f) :
    MemLp (palomar_Translation_fTrunc f) p (volume : Measure (Fin d → ℝ)) := by
  classical
  unfold palomar_Translation_fTrunc
  -- The Finset.sum-of-functions form coincides with the lambda sum.
  have hfn : (∑ k ∈ palomar_Translation_cubeTranslates d, (palomar_Translation_shiftedCube k).indicator f)
      = (fun x => ∑ k ∈ palomar_Translation_cubeTranslates d, (palomar_Translation_shiftedCube k).indicator f x) := by
    funext x; rw [Finset.sum_apply]
  rw [hfn]
  exact memLp_finset_sum_aux _ (fun k _ => memLp_indicator_shiftedCube hf hper k)

/-! ## Step 5: the main theorem -/

/-- **Translation continuity in `L^p_per`.** For `MemLpPer p f` with
`1 ≤ p < ∞` and `IsPeriodic f`, `eLpNormPer p (f(·-y) - f(·)) → 0` as `y → 0`. -/
theorem tendsto_eLpNormPer_translation_sub
    {p : ℝ≥0∞} (hp : p ≠ ∞) [Fact (1 ≤ p)]
    {f : (Fin d → ℝ) → ℝ} (hf : MemLpPer p f) (hper : IsPeriodic f) :
    Tendsto (fun y : Fin d → ℝ =>
      eLpNormPer p (fun x => f (x - y) - f x)) (𝓝 0) (𝓝 0) := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  -- Build the truncated function and its whole-space translation continuity.
  have hfTrunc : MemLp (palomar_Translation_fTrunc f) p (volume : Measure (Fin d → ℝ)) :=
    memLp_fTrunc hf hper
  have h_whole := tendsto_eLpNorm_translate_sub (d := d) hp hfTrunc
  -- The key inequality: for `y` with `‖y i‖ ≤ 1`,
  --   eLpNormPer p (f(·-y) - f(·)) ≤ eLpNorm (palomar_Translation_fTrunc f (·-y) - palomar_Translation_fTrunc f) p volume.
  have h_bound : ∀ᶠ y in (𝓝 (0 : Fin d → ℝ)),
      eLpNormPer p (fun x => f (x - y) - f x)
        ≤ eLpNorm (fun x => palomar_Translation_fTrunc f (x - y) - palomar_Translation_fTrunc f x) p
            (volume : Measure (Fin d → ℝ)) := by
    -- The neighborhood `{y | ∀ i, |y i| ≤ 1}` of `0`.
    have hnbd : ∀ᶠ y : Fin d → ℝ in 𝓝 0, ∀ i, |y i| ≤ 1 := by
      have hev : ∀ᶠ y : Fin d → ℝ in 𝓝 (0 : Fin d → ℝ),
          ∀ i ∈ (Finset.univ : Finset (Fin d)), |y i| ≤ 1 := by
        refine (eventually_all_finset (Finset.univ : Finset (Fin d))).mpr ?_
        intro i _
        have hcont : ContinuousAt (fun y : Fin d → ℝ => |y i|) 0 :=
          (continuous_apply i).continuousAt.abs
        have h0 : |((0 : Fin d → ℝ) i)| < 1 := by simp
        exact (hcont.eventually_lt_const h0).mono (fun _ hy => le_of_lt hy)
      exact hev.mono fun y hy i => hy i (Finset.mem_univ _)
    refine hnbd.mono fun y hy => ?_
    -- On the unit cube, the differences agree pointwise.
    have h_pw_eq : ∀ x ∈ UnitCube d,
        f (x - y) - f x = palomar_Translation_fTrunc f (x - y) - palomar_Translation_fTrunc f x := by
      intro x hx
      obtain ⟨h1, h2⟩ := fTrunc_eq_on_unitCube_with_buffer (f := f) hx hy
      rw [h1, h2]
    -- Translate to a.e. equality on the cube-restricted measure.
    have h_ae_eq :
        (fun x : Fin d → ℝ => f (x - y) - f x)
          =ᵐ[(volume : Measure (Fin d → ℝ)).restrict (UnitCube d)]
          (fun x => palomar_Translation_fTrunc f (x - y) - palomar_Translation_fTrunc f x) := by
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_unitCube]
      exact Filter.Eventually.of_forall (fun x hx => h_pw_eq x hx)
    -- Cube eLpNorm equality, then bound by whole-space eLpNorm.
    have h_eq_cube : eLpNormPer p (fun x => f (x - y) - f x)
        = eLpNorm (fun x => palomar_Translation_fTrunc f (x - y) - palomar_Translation_fTrunc f x) p
            ((volume : Measure (Fin d → ℝ)).restrict (UnitCube d)) := by
      unfold eLpNormPer
      exact eLpNorm_congr_ae h_ae_eq
    rw [h_eq_cube]
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  -- Squeeze: 0 ≤ eLpNormPer ≤ eLpNorm with the latter going to 0.
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_whole
    (Filter.Eventually.of_forall (fun _ => zero_le)) h_bound

end Periodic
end StationaryMFG
