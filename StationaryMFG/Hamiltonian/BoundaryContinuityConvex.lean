module

public import StationaryMFG.Hamiltonian.Monotone
public import StationaryMFG.Hamiltonian.Differentiability
public import Mathlib.Analysis.Convex.Continuous

@[expose] public section

/-!
# Joint continuity at zero mass from convexity

The closed-halfspace continuity used by the weak-growth existence theorem
follows from its existing monotonicity, convexity, and boundary-value data.
The finite boundary trace is convex, hence continuous. Monotonicity in mass
then sandwiches nearby values between this trace and a fixed positive-mass
slice. No bound on the momentum derivative near zero mass is required.
-/

namespace StationaryMFG.Hamiltonian

open MeasureTheory Filter Set Topology
open StationaryMFG.Periodic

/-- A continuous boundary trace and decreasing mass sections upgrade interior
joint continuity and pointwise right continuity to closed-halfspace continuity.
The parameter space is arbitrary; no convexity or norm is used here. -/
theorem continuousOn_closedHalfspace_of_antitone
    {E : Type*} [TopologicalSpace E] (F : E → ℝ → ℝ)
    (hcont : ContinuousOn (fun pm : E × ℝ => F pm.1 pm.2) {pm | 0 < pm.2})
    (hlim : ∀ p, Tendsto (F p) (𝓝[>] (0 : ℝ)) (𝓝 (F p 0)))
    (hanti : ∀ p, AntitoneOn (F p) (Ioi (0 : ℝ)))
    (hzero : Continuous (fun p => F p 0)) :
    ContinuousOn (fun pm : E × ℝ => F pm.1 pm.2) {pm | 0 ≤ pm.2} := by
  have hle_zero : ∀ p m, 0 ≤ m → F p m ≤ F p 0 := by
    intro p m hm
    rcases eq_or_lt_of_le hm with hm0 | hmpos
    · subst m
      exact le_rfl
    · apply ge_of_tendsto (hlim p)
      filter_upwards [Ioo_mem_nhdsGT hmpos] with t ht
      exact hanti p ht.1 hmpos ht.2.le
  have hanti_closed : ∀ p, AntitoneOn (F p) (Ici (0 : ℝ)) := by
    intro p a ha b hb hab
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ a from ha) with ha0 | hapos
    · subst a
      exact hle_zero p b hb
    · exact hanti p hapos (lt_of_lt_of_le hapos hab) hab
  rintro ⟨p, m⟩ hm
  by_cases hmpos : 0 < m
  · exact (hcont.continuousAt
      ((isOpen_lt continuous_const continuous_snd).mem_nhds hmpos)).continuousWithinAt
  · have hm0 : m = 0 := le_antisymm (le_of_not_gt hmpos) hm
    subst m
    change Tendsto (fun pm : E × ℝ => F pm.1 pm.2)
      (𝓝[{pm | 0 ≤ pm.2}] (p, 0)) (𝓝 (F p 0))
    rw [tendsto_order]
    constructor
    · intro a ha
      have ha_slice : ∀ᶠ t in 𝓝[>] (0 : ℝ), a < F p t :=
        (tendsto_order.mp (hlim p)).1 a ha
      have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
      obtain ⟨δ, hδ, haδ⟩ := (hpos.and ha_slice).exists
      have hslice : Continuous (fun q => F q δ) :=
        hcont.comp_continuous (continuous_id.prodMk continuous_const) (fun _ => hδ)
      have ha_near : ∀ᶠ pm : E × ℝ in 𝓝 (p, 0), a < F pm.1 δ :=
        (tendsto_order.mp (hslice.comp continuous_fst).continuousAt).1 a haδ
      have hm_near : ∀ᶠ pm : E × ℝ in 𝓝 (p, 0), pm.2 < δ :=
        (tendsto_order.mp continuous_snd.continuousAt).2 δ hδ
      filter_upwards [ha_near.filter_mono nhdsWithin_le_nhds,
        hm_near.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
        with pm hap hmp hnonneg
      exact lt_of_lt_of_le hap (hanti_closed pm.1 hnonneg hδ.le hmp.le)
    · intro b hb
      have hb_near : ∀ᶠ pm : E × ℝ in 𝓝 (p, 0), F pm.1 0 < b :=
        (tendsto_order.mp (hzero.comp continuous_fst).continuousAt).2 b hb
      filter_upwards [hb_near.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
        with pm hbp hnonneg
      exact lt_of_le_of_lt (hle_zero pm.1 pm.2 hnonneg) hbp

/-- Convexity passes to a finite right-hand boundary trace. -/
theorem convexOn_boundary_of_slice_limits
    {E : Type*} [AddCommMonoid E] [Module ℝ E] (F : E → ℝ → ℝ)
    (hconvex : ∀ m, 0 < m → ConvexOn ℝ univ (fun p => F p m))
    (hlim : ∀ p, Tendsto (F p) (𝓝[>] (0 : ℝ)) (𝓝 (F p 0))) :
    ConvexOn ℝ univ (fun p => F p 0) := by
  refine ⟨convex_univ, ?_⟩
  intro p hp q hq a b ha hb hab
  apply le_of_tendsto_of_tendsto (hlim (a • p + b • q))
    (((hlim p).const_mul a).add ((hlim q).const_mul b))
  filter_upwards [self_mem_nhdsWithin] with m hm
  exact (hconvex m hm).2 hp hq ha hb hab

/-- Under the hypotheses already present in the weak-growth main theorem,
joint continuity at zero mass is a consequence, not an extra assumption. -/
theorem HypothesisHextJointCont.of_convex
    {d : ℕ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone H DpH)
    (hdiff : HypothesisHpDifferentiable H DpH)
    (hH0 : HypothesisHZeroExtension H) : HypothesisHextJointCont H := by
  have hfinite : Hext_finite_at_zero H := by
    filter_upwards [hH0.hAgree] with x hx p
    rw [← hx p]
    exact WithTop.coe_ne_top
  have hlim := H_rc0_of_hHat0 hH0.hHat0 hfinite hH0.hAgree
  filter_upwards [hmon.continuous_H_pm, antitone_in_m hmon,
    hdiff.convexOn_H_p, hlim] with x hxcont hxanti hxconvex hxlim
  apply continuousOn_closedHalfspace_of_antitone (H x) hxcont hxlim hxanti
  exact continuousOn_univ.mp
    ((convexOn_boundary_of_slice_limits (H x) hxconvex hxlim).continuousOn isOpen_univ)

end StationaryMFG.Hamiltonian
