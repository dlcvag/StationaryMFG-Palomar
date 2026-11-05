module

public import StationaryMFG.Theorems.Congestion.PaperMuAux
public import StationaryMFG.Theorems.Congestion.PaperMuBoundary
public import StationaryMFG.Theorems.Congestion.MuIntegrability
public import Mathlib.MeasureTheory.Function.LpOrder

@[expose] public section

/-!
# Integrability of the paper's positive-domain auxiliary density

The infimum in paper `mu-definition` uses strictly positive masses. Its
measurability follows from positive sublevel tests and a countable limit at
zero. For the growth estimate we compare it with the existing auxiliary
density whose lower obstacle is `max m 1`; that comparison evaluates the
Hamiltonian only at positive masses and reuses the established Young bound.
-/

noncomputable section

namespace StationaryMFG.Theorems.Congestion.Paper

open MeasureTheory Filter Topology Set
open StationaryMFG.Periodic StationaryMFG.Hamiltonian
open StationaryMFG.Congestion
open scoped ENNReal NNReal

/-- Positive sublevels determine measurability, even when the infimum is
zero and the Hamiltonian has no finite boundary value. -/
theorem positiveAux_aemeasurable
    {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {F : X → ℝ → ℝ} {m b : X → ℝ}
    (hm : AEMeasurable m ν) (hb : AEMeasurable b ν)
    (hF : ∀ a, 0 < a → AEMeasurable (fun x => F x a) ν)
    (hne : ∀ᵐ x ∂ν, (positiveAuxSet (F x) (m x) (b x)).Nonempty)
    (hcont : ∀ᵐ x ∂ν, ContinuousOn (F x) (Ioi 0))
    (hanti : ∀ᵐ x ∂ν, AntitoneOn (F x) (Ioi 0)) :
    AEMeasurable (fun x => positiveAux (F x) (m x) (b x)) ν := by
  let μ : X → ℝ := fun x => positiveAux (F x) (m x) (b x)
  have hpos : ∀ a, 0 < a → NullMeasurableSet {x | μ x ≤ a} ν := by
    intro a ha
    have hset : {x | μ x ≤ a} =ᵐ[ν] {x | m x ≤ a ∧ F x a ≤ b x} := by
      filter_upwards [hne, hcont, hanti] with x hn hc ht
      exact propext (positiveAux_le_iff hn hc ht ha)
    have hmeas : NullMeasurableSet {x | m x ≤ a ∧ F x a ≤ b x} ν :=
      (hm.aestronglyMeasurable.nullMeasurableSet_le aestronglyMeasurable_const).inter
        ((hF a ha).aestronglyMeasurable.nullMeasurableSet_le hb.aestronglyMeasurable)
    exact hmeas.congr hset.symm
  have hzero : NullMeasurableSet {x | μ x ≤ 0} ν := by
    have hset : {x | μ x ≤ 0} =
        ⋂ n : ℕ, {x | μ x ≤ Hamiltonian.Paper.boundaryMass n} := by
      ext x
      simp only [mem_setOf_eq, mem_iInter]
      constructor
      · intro hx n
        exact hx.trans (Hamiltonian.Paper.boundaryMass_pos n).le
      · intro hx
        exact ge_of_tendsto' (Hamiltonian.Paper.boundaryMass_tendsto.mono_right
          nhdsWithin_le_nhds) hx
    rw [hset]
    exact NullMeasurableSet.iInter fun n =>
      hpos _ (Hamiltonian.Paper.boundaryMass_pos n)
  refine aemeasurable_of_nullMeasurable_Iic_rat fun q => ?_
  change NullMeasurableSet {x | μ x ≤ (q : ℝ)} ν
  rcases lt_trichotomy (q : ℝ) 0 with hq | hq | hq
  · have heq : {x | μ x ≤ (q : ℝ)} =ᵐ[ν] (∅ : Set X) := by
      filter_upwards [hne] with x hn
      apply propext
      exact iff_false_intro (not_le_of_gt (hq.trans_le (positiveAux_nonneg hn)))
    exact MeasurableSet.empty.nullMeasurableSet.congr heq.symm
  · simpa only [hq] using hzero
  · exact hpos _ hq

variable {d : ℕ}

/-- A positive lower obstacle gives an admissible subset of the paper's
set, so its legacy infimum is an upper bound for the paper infimum. -/
theorem positiveAux_le_muAux_max_one
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {k : ℝ} {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    (hne : (muAuxSet k (fun x => max (m x) 1) u V Du H x).Nonempty) :
    positiveAux (H x (fun i => Du i x)) (m x) (k - u x + V x) ≤
      muAux k (fun x => max (m x) 1) u V Du H x := by
  apply le_csInf hne
  intro t ht
  apply csInf_le (positiveAux_bddBelow _ _ _)
  refine ⟨lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans ht.2.1),
    (le_max_left _ _).trans ht.2.1, ?_⟩
  linarith [ht.2.2]

/-- Truncating the lower obstacle at one preserves nonemptiness without
using a value of the Hamiltonian at zero. -/
theorem muAuxSet_max_one_nonempty_of_positiveAux
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {k : ℝ} {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    (hne : (positiveAuxSet (H x (fun i => Du i x))
      (m x) (k - u x + V x)).Nonempty)
    (hanti : AntitoneOn (H x (fun i => Du i x)) (Ioi 0)) :
    (muAuxSet k (fun x => max (m x) 1) u V Du H x).Nonempty := by
  obtain ⟨t, ht⟩ := hne
  refine ⟨max t 1, (zero_lt_one.trans_le (le_max_right _ _)).le,
    max_le_max ht.2.1 le_rfl, ?_⟩
  have hH := (hanti ht.1 (ht.1.trans_le (le_max_left t 1)) (le_max_left t 1)).trans
    ht.2.2
  linarith

/-- The congestion upper bound tends to minus infinity at large mass,
so the positive-domain constraint set is nonempty. -/
theorem positiveAuxSet_nonempty_of_congestionGrowth
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone H DpH)
    (hcong : CongestionGrowthCore H DpH J)
    (k : ℝ) (m u V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      (positiveAuxSet (H x (fun i => Du i x)) (m x) (k - u x + V x)).Nonempty := by
  obtain ⟨K, δ, hK, hδ, hupper⟩ := H_upper_congestion_of_hmon hmon hcong
  have hlarge : ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ t, 1 ≤ t →
      H x (fun i => Du i x) t ≤
        2 * K * (‖(fun i => Du i x)‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) + 1)
          - δ * t ^ hcong.β := by
    filter_upwards [hupper] with x hx
    intro t ht
    have htpos : 0 < t := zero_lt_one.trans_le ht
    have hi : 1 / t ≤ (1 : ℝ) := (div_le_one htpos).2 ht
    have hit : 1 / t ^ hcong.τ ≤ (1 : ℝ) :=
      (div_le_one (Real.rpow_pos_of_pos htpos _)).2
        (Real.one_le_rpow ht hcong.hτ.1)
    have hcoef : K * (1 / t + 1 / t ^ hcong.τ) ≤ 2 * K := by
      nlinarith [hK.le]
    have hP : 0 ≤
        ‖(fun i => Du i x)‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) + 1 := by
      positivity
    exact (hx _ t htpos).trans
      (sub_le_sub_right (mul_le_mul_of_nonneg_right hcoef hP) _)
  have hlegacy := muAux_nonempty_of_large_bound (k := k)
    (m := fun x => max (m x) 1) (u := u) (V := V) (Du := Du)
    hcong.hβ hδ hlarge
  filter_upwards [hlegacy] with x hx
  obtain ⟨t, ht⟩ := hx
  refine ⟨t, zero_lt_one.trans_le ((le_max_right _ _).trans ht.2.1),
    (le_max_left _ _).trans ht.2.1, ?_⟩
  linarith [ht.2.2]

/-- The corrected auxiliary density belongs to `L^(β+1)`. Only positive
slice continuity and nonemptiness are used; both are available from the
paper hypotheses in applications. The input functions need only their
existing `MemLpPer` certificates, not globally measurable representatives. -/
theorem positiveAux_memLp_of_congestionGrowth
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone H DpH)
    (hcong : CongestionGrowthCore H DpH J)
    {k : ℝ} {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm : MemLpPer (ENNReal.ofReal (hcong.β + 1)) m)
    (hu : MemLpPer (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) u)
    (hV : MemLpPer (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (hDu : ∀ i, MemLpPer
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Du i))
    (hne : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      (positiveAuxSet (H x (fun i => Du i x)) (m x) (k - u x + V x)).Nonempty) :
    MemLpPer (ENNReal.ofReal (hcong.β + 1))
      (fun x => positiveAux (H x (fun i => Du i x)) (m x) (k - u x + V x)) := by
  have hcont : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ContinuousOn (H x (fun i => Du i x)) (Ioi 0) := by
    filter_upwards [hmon.continuous_H_pm] with x hx
    exact hx.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ ht => ht)
  have hanti : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      AntitoneOn (H x (fun i => Du i x)) (Ioi 0) := by
    filter_upwards [antitone_in_m hmon] with x hx
    exact hx _
  have hne' : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      (muAuxSet k (fun x => max (m x) 1) u V Du H x).Nonempty := by
    filter_upwards [hne, hanti] with x hn ha
    exact muAuxSet_max_one_nonempty_of_positiveAux hn ha
  obtain ⟨C, hC, hbound⟩ :=
    muAux_le_envelope_of_congestionGrowth_of_m_nonneg hmon hcong hcont hne'
  have hm' : MemLpPer (ENNReal.ofReal (hcong.β + 1)) (fun x => max (m x) 1) := by
    apply MemLp.toMemLpPer
    simpa only [Pi.sup_def] using
      hm.toMemLp.sup (MemLpPer.const (d := d) (1 : ℝ)).toMemLp
  have hG := muAuxEnvelope_memLp (C := C) hcong.hα hcong.hβ hm' hu hV hDu
  have hDu_meas : AEMeasurable (fun x => fun i => Du i x)
      (volume.restrict (UnitCube d)) := by
    rw [aemeasurable_pi_iff]
    exact fun i => (hDu i).aestronglyMeasurable.aemeasurable
  have hF : ∀ a, 0 < a → AEMeasurable (fun x => H x (fun i => Du i x) a)
      (volume.restrict (UnitCube d)) := by
    intro a _
    exact hmon.measurable_H.comp_aemeasurable
      (aemeasurable_id.prodMk (hDu_meas.prodMk aemeasurable_const))
  have hmeas := positiveAux_aemeasurable hm.aestronglyMeasurable.aemeasurable
    ((aemeasurable_const.sub hu.aestronglyMeasurable.aemeasurable).add
      hV.aestronglyMeasurable.aemeasurable) hF hne hcont hanti
  simp only [Pi.sub_def, Pi.add_def] at hmeas
  apply MemLp.toMemLpPer
  apply MemLp.of_le_mul (c := 1) hG.toMemLp hmeas.aestronglyMeasurable
  filter_upwards [hne, hne', hbound] with x hn hn' hb
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (positiveAux_nonneg hn),
    abs_of_nonneg (muAuxEnvelope_nonneg hC x), one_mul]
  exact (positiveAux_le_muAux_max_one hn').trans hb

/-- The paper's auxiliary-density integrability conclusion with all
analytic side conditions derived from the standing growth hypotheses. -/
theorem positiveAux_memLp
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone H DpH)
    (hcong : CongestionGrowthCore H DpH J)
    {k : ℝ} {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm : MemLpPer (ENNReal.ofReal (hcong.β + 1)) m)
    (hu : MemLpPer (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) u)
    (hV : MemLpPer (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (hDu : ∀ i, MemLpPer
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Du i)) :
    MemLpPer (ENNReal.ofReal (hcong.β + 1))
      (fun x => positiveAux (H x (fun i => Du i x)) (m x) (k - u x + V x)) :=
  positiveAux_memLp_of_congestionGrowth hmon hcong hm hu hV hDu
    (positiveAuxSet_nonempty_of_congestionGrowth hmon hcong k m u V Du)

/-- The density exponent and its dual give the required power closure. -/
theorem memLp_rpow_beta {β : ℝ} (hβ : 0 < β)
    {f : (Fin d → ℝ) → ℝ}
    (hf : MemLpPer (ENNReal.ofReal (β + 1)) f)
    (hn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ f x) :
    MemLpPer (ENNReal.ofReal ((β + 1) / β)) (fun x => f x ^ β) := by
  have hexp : ENNReal.ofReal ((β + 1) / β) * ENNReal.ofReal β =
      ENNReal.ofReal (β + 1) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  have hp : MemLpPer (ENNReal.ofReal ((β + 1) / β)) (fun x => ‖f x‖ ^ β) :=
    MemLpPer.rpow_closure hβ (by rw [hexp]; exact hf)
  apply MemLp.toMemLpPer
  apply MemLp.ae_eq (hf_Lp := hp.toMemLp)
  filter_upwards [hn] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg hx]

/-- Hölder integrability of the uniform dominator used for positive
auxiliary truncations. This lemma does not require a Hamiltonian. -/
theorem auxiliary_dominator_integrable {β : ℝ} (hβ : 0 < β) (C k : ℝ)
    {m u V μ : (Fin d → ℝ) → ℝ}
    (hm : MemLpPer (ENNReal.ofReal (β + 1)) m)
    (hu : MemLpPer (ENNReal.ofReal ((β + 1) / β)) u)
    (hV : MemLpPer (ENNReal.ofReal ((β + 1) / β)) V)
    (hμ : MemLpPer (ENNReal.ofReal (β + 1)) μ)
    (hμ_nonneg : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ μ x) :
    Integrable (fun x =>
      (|u x| + |V x| + |k - u x + V x| + C * ((μ x + 1) ^ β + 1)) *
        (μ x + 1 + |m x|)) (volume.restrict (UnitCube d)) := by
  have hμ1 : MemLpPer (ENNReal.ofReal (β + 1)) (fun x => μ x + 1) :=
    hμ.add (MemLpPer.const 1)
  have hμ1n : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ μ x + 1 :=
    hμ_nonneg.mono fun x hx => by linarith
  have hpw := memLp_rpow_beta hβ hμ1 hμ1n
  have hCpw : MemLpPer (ENNReal.ofReal ((β + 1) / β))
      (fun x => C * ((μ x + 1) ^ β + 1)) := by
    simpa only [Pi.smul_def, Pi.add_def, smul_eq_mul] using
      (hpw.add (MemLpPer.const 1)).const_smul (𝕜 := ℝ) C
  have huabs : MemLpPer (ENNReal.ofReal ((β + 1) / β)) (fun x => |u x|) := by
    simpa only [Real.norm_eq_abs] using MemLp.toMemLpPer hu.toMemLp.norm
  have hVabs : MemLpPer (ENNReal.ofReal ((β + 1) / β)) (fun x => |V x|) := by
    simpa only [Real.norm_eq_abs] using MemLp.toMemLpPer hV.toMemLp.norm
  have hb : MemLpPer (ENNReal.ofReal ((β + 1) / β)) (fun x => k - u x + V x) := by
    apply MemLp.toMemLpPer
    simpa only [Pi.sub_def, Pi.add_def] using
      ((MemLpPer.const k).toMemLp.sub hu.toMemLp).add hV.toMemLp
  have hbabs : MemLpPer (ENNReal.ofReal ((β + 1) / β))
      (fun x => |k - u x + V x|) := by
    simpa only [Real.norm_eq_abs] using MemLp.toMemLpPer hb.toMemLp.norm
  have htop := ((huabs.add hVabs).add hbabs).add hCpw
  have hmabs : MemLpPer (ENNReal.ofReal (β + 1)) (fun x => |m x|) := by
    simpa only [Real.norm_eq_abs] using MemLp.toMemLpPer hm.toMemLp.norm
  have hbottom := hμ1.add hmabs
  have hconj : Real.HolderConjugate ((β + 1) / β) (β + 1) := by
    refine ⟨?_, by positivity, by positivity⟩
    field_simp
  simpa only [Pi.add_def, IntegrableOn] using MemLpPer.integrable_mul hconj htop hbottom

/-- The paper's coercive quotient at the corrected auxiliary density
lies in the dual density space, including its locally finite zero case. -/
theorem positiveAux_quotient_memLp
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone H DpH)
    (hcong : CongestionGrowthCore H DpH J)
    {k : ℝ} {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm : MemLpPer (ENNReal.ofReal (hcong.β + 1)) m)
    (hu : MemLpPer (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) u)
    (hV : MemLpPer (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (hDu : ∀ i, MemLpPer
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Du i)) :
    MemLpPer (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
      (fun x => ‖(fun i => Du i x)‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) /
        (positiveAux (H x (fun i => Du i x)) (m x) (k - u x + V x) ^ hcong.τ + 1)) := by
  let μ := fun x => positiveAux (H x (fun i => Du i x)) (m x) (k - u x + V x)
  let q := fun x => ‖(fun i => Du i x)‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) /
    (μ x ^ hcong.τ + 1)
  have hne := positiveAuxSet_nonempty_of_congestionGrowth hmon hcong k m u V Du
  have hμ : MemLpPer (ENNReal.ofReal (hcong.β + 1)) μ :=
    positiveAux_memLp hmon hcong hm hu hV hDu
  have hμn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ μ x :=
    hne.mono fun _ hn => positiveAux_nonneg hn
  have hpw := memLp_rpow_beta hcong.hβ hμ hμn
  have hb : MemLpPer (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
      (fun x => k - u x + V x) := by
    apply MemLp.toMemLpPer
    simpa only [Pi.sub_def, Pi.add_def] using
      ((MemLpPer.const k).toMemLp.sub hu.toMemLp).add hV.toMemLp
  have hbabs : MemLpPer (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
      (fun x => |k - u x + V x|) := by
    simpa only [Real.norm_eq_abs] using MemLp.toMemLpPer hb.toMemLp.norm
  have hCpw : MemLpPer (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
      (fun x => hcong.C * (μ x ^ hcong.β + 1)) := by
    simpa only [Pi.smul_def, Pi.add_def, smul_eq_mul] using
      (hpw.add (MemLpPer.const 1)).const_smul (𝕜 := ℝ) hcong.C
  let G := fun x => hcong.C * (|k - u x + V x| + hcong.C * (μ x ^ hcong.β + 1))
  have hG : MemLpPer (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) G := by
    simpa only [G, Pi.smul_def, Pi.add_def, smul_eq_mul] using
      (hbabs.add hCpw).const_smul (𝕜 := ℝ) hcong.C
  have hDv : AEMeasurable (fun x => fun i => Du i x)
      (volume.restrict (UnitCube d)) := by
    rw [aemeasurable_pi_iff]
    exact fun i => (hDu i).aestronglyMeasurable.aemeasurable
  have hqmeas : AEStronglyMeasurable q (volume.restrict (UnitCube d)) :=
    ((hDv.norm.pow_const _).div
      ((hμ.aestronglyMeasurable.aemeasurable.pow_const _).add aemeasurable_const)).aestronglyMeasurable
  have hcont : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ContinuousOn (H x (fun i => Du i x)) (Ioi 0) := by
    filter_upwards [hmon.continuous_H_pm] with x hx
    exact hx.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ ht => ht)
  apply MemLp.toMemLpPer
  apply MemLp.of_le_mul (c := 1) hG.toMemLp hqmeas
  filter_upwards [hne, hcont, antitone_in_m hmon, finiteExtension_positiveAux_lower hcong]
    with x hn hc ha hl
  have hμnx : 0 ≤ μ x := positiveAux_nonneg hn
  have hlow := hl (fun i => Du i x) (m x) (k - u x + V x) hn hc (ha _)
  have hup := finiteExtension_positiveAux_le hn hc (ha (fun i => Du i x))
  have hcoeff : q x / hcong.C =
      (1 / hcong.C) * (1 / (μ x ^ hcong.τ + 1)) *
        ‖(fun i => Du i x)‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) := by
    dsimp [q]
    ring
  have hdiv : q x / hcong.C ≤ k - u x + V x + hcong.C * (μ x ^ hcong.β + 1) := by
    rw [hcoeff]
    linarith
  have hbound : q x ≤ G x := by
    have hraw := (div_le_iff₀ hcong.hC).1 hdiv
    have hbnd := mul_le_mul_of_nonneg_left (le_abs_self (k - u x + V x)) hcong.hC.le
    dsimp [G]
    nlinarith
  have hqn : 0 ≤ q x := by
    dsimp [q]
    have ht := Real.rpow_nonneg hμnx hcong.τ
    positivity
  have hGn : 0 ≤ G x := hqn.trans hbound
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hqn, abs_of_nonneg hGn, one_mul]
  exact hbound

end StationaryMFG.Theorems.Congestion.Paper
