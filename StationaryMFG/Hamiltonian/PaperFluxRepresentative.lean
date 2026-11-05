module

public import StationaryMFG.Hamiltonian.PaperRepresentative
public import StationaryMFG.Hamiltonian.FluxExtension

@[expose] public section

/-!
# A measurable representative of the general limiting flux

The paper does not impose global measurability of an arbitrary supplied
boundary extension J. Its positive-mass values and continuous right limit
determine a measurable representative, agreeing with J at every
nonnegative mass and momentum for almost every spatial point.
-/

namespace StationaryMFG.Hamiltonian.Paper

open MeasureTheory Filter Topology Set StationaryMFG.Periodic

variable {d : ℕ}
variable {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
variable {DpH J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}

noncomputable def boundaryFlux
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (x p : Fin d → ℝ) : Fin d → ℝ :=
  limUnder atTop (fun n => boundaryMass n • canonicalGradient H x p (boundaryMass n))

noncomputable def canonicalFlux
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (x p : Fin d → ℝ) (m : ℝ) : Fin d → ℝ :=
  if 0 < m then m • canonicalGradient H x p m else boundaryFlux H x p

@[simp] theorem canonicalFlux_of_pos (x p : Fin d → ℝ) {m : ℝ} (hm : 0 < m) :
    canonicalFlux H x p m = m • canonicalGradient H x p m := if_pos hm

@[simp] theorem canonicalFlux_zero (x p : Fin d → ℝ) :
    canonicalFlux H x p 0 = boundaryFlux H x p := by simp [canonicalFlux]

theorem boundaryFlux_measurable
    (hH : Measurable
      (fun (xpm : (Fin d → ℝ) × (Fin d → ℝ) × {m : ℝ // 0 < m}) =>
        H xpm.1 xpm.2.1 xpm.2.2)) :
    Measurable (fun xp : (Fin d → ℝ) × (Fin d → ℝ) => boundaryFlux H xp.1 xp.2) := by
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.limUnder
  intro n
  exact ((measurable_const (a := boundaryMass n)).smul ((canonicalGradient_measurable hH).comp
    (measurable_fst.prodMk (measurable_snd.prodMk measurable_const)))).stronglyMeasurable

private theorem measurable_flux_piecewise
    (G : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (B : (Fin d → ℝ) → (Fin d → ℝ) → (Fin d → ℝ))
    (hG : Measurable (fun xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ =>
      G xpm.1 xpm.2.1 xpm.2.2))
    (hB : Measurable (fun xp : (Fin d → ℝ) × (Fin d → ℝ) => B xp.1 xp.2)) :
    Measurable (fun xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ =>
      if 0 < xpm.2.2 then xpm.2.2 • G xpm.1 xpm.2.1 xpm.2.2
      else B xpm.1 xpm.2.1) := by
  apply Measurable.ite (measurableSet_lt measurable_const measurable_snd.snd)
  · exact measurable_snd.snd.smul hG
  · exact hB.comp (measurable_fst.prodMk measurable_snd.fst)

theorem canonicalFlux_measurable
    (hH : Measurable
      (fun (xpm : (Fin d → ℝ) × (Fin d → ℝ) × {m : ℝ // 0 < m}) =>
        H xpm.1 xpm.2.1 xpm.2.2)) :
    Measurable (fun xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ =>
      canonicalFlux H xpm.1 xpm.2.1 xpm.2.2) := by
  unfold canonicalFlux
  exact measurable_flux_piecewise _ _ (canonicalGradient_measurable hH)
    (boundaryFlux_measurable hH)

theorem boundaryFlux_periodic
    (hper : ∀ p m, 0 < m → IsPeriodic (fun x => H x p m))
    (p : Fin d → ℝ) : IsPeriodic (fun x => boundaryFlux H x p) := by
  intro k x
  apply congrArg (limUnder atTop)
  funext n
  exact congrArg (fun v : Fin d → ℝ => boundaryMass n • v)
    (canonicalGradient_periodic hper p (boundaryMass n) k x)

theorem canonicalFlux_periodic
    (hper : ∀ p m, 0 < m → IsPeriodic (fun x => H x p m))
    (p : Fin d → ℝ) (m : ℝ) : IsPeriodic (fun x => canonicalFlux H x p m) := by
  by_cases hm : 0 < m
  · simpa only [canonicalFlux, if_pos hm, Pi.smul_def] using
      (canonicalGradient_periodic hper p m).smul m
  · simpa only [canonicalFlux, if_neg hm] using boundaryFlux_periodic hper p

theorem canonicalFlux_eq
    (hreg : RegularityH H DpH) (hJ : PaperFluxExtension DpH J) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p m, 0 ≤ m →
      canonicalFlux H x p m = J x p m := by
  filter_upwards [hreg.canonicalGradient_eq, hJ.tendsto_at_zero] with x he hj p m hm
  rcases eq_or_lt_of_le hm with hz | hp
  · rw [← hz, canonicalFlux_zero]
    apply Filter.Tendsto.limUnder_eq
    apply ((hj p).comp boundaryMass_tendsto).congr'
    apply Eventually.of_forall
    intro n
    exact congrArg (fun v : Fin d → ℝ => boundaryMass n • v)
      (he p _ (boundaryMass_pos n)).symm
  · rw [canonicalFlux_of_pos x p hp, he p m hp, hJ.J_of_pos x p m hp]

/-- All three paper flux-extension clauses hold for the canonical representative. -/
theorem canonicalFlux_extension
    (hreg : RegularityH H DpH) (hJ : PaperFluxExtension DpH J) :
    PaperFluxExtension (canonicalGradient H) (canonicalFlux H) where
  J_of_pos := fun x p _ hm => canonicalFlux_of_pos x p hm
  tendsto_at_zero := by
    filter_upwards [hJ.tendsto_at_zero, hreg.canonicalGradient_eq,
      canonicalFlux_eq hreg hJ] with x hj he hje p
    rw [hje p 0 le_rfl]
    apply (hj p).congr'
    filter_upwards [self_mem_nhdsWithin] with m hm
    rw [he p m hm]
  continuous_J := by
    filter_upwards [hJ.continuous_J, canonicalFlux_eq hreg hJ] with x hc he
    apply hc.congr
    intro pm hpm
    exact he pm.1 pm.2 hpm

end StationaryMFG.Hamiltonian.Paper
