module

public import StationaryMFG.Theorems.InfimalConvolution.PaperGrowth
public import StationaryMFG.Hamiltonian.PaperRepresentative
public import StationaryMFG.Solutions.Weak

@[expose] public section

/-!
# Weak-growth representatives and transport of weak solutions

Only positive test densities enter the weak variational inequality.
Changing H at zero and replacing the supplied gradient by its measurable
representative therefore needs no boundary premise on the original H.
-/

namespace StationaryMFG.Hamiltonian.Paper

open MeasureTheory StationaryMFG.Periodic

variable {d : ℕ}
variable {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
variable {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}

/-- The existing weak-growth bundle for the canonical representatives.
Its boundary values need not be correct or finite; all its premises are
positive-mass statements. The growth parameters are unchanged. -/
noncomputable def HypothesisWeakGrowth.toCanonical
    (h : HypothesisWeakGrowth H DpH) :
    Hamiltonian.HypothesisWeakGrowth (finiteExtension H) (canonicalGradient H) where
  toRegularityH := h.toRegularityH.finiteExtension_regularity
  C := h.C
  α := h.α
  β := h.β
  hC := h.hC
  hα := h.hα
  hβ := h.hβ
  f := h.f
  hf_continuous := h.hf_continuous
  upper := by
    filter_upwards [h.upper] with x hx m hm
    simpa only [finiteExtension_of_pos H x _ hm] using hx m hm
  DpH_upper := by
    filter_upwards [h.DpH_upper, h.toRegularityH.canonicalGradient_eq] with x hx he p m hm
    rw [he p m hm]
    exact hx p m hm
  lower := by
    filter_upwards [h.lower] with x hx p m hm
    simpa only [finiteExtension_of_pos H x _ hm] using hx p m hm

theorem weakSolution_of_canonical
    (hreg : RegularityH H DpH)
    {V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    (h : Solutions.Weak.IsWeakSolution V (finiteExtension H) (canonicalGradient H) Du m u) :
    Solutions.Weak.IsWeakSolution V H DpH Du m u := by
  intro Dυ μ υ hadm
  obtain ⟨c, hc, hμ⟩ := hadm.lower
  have hpos : ∀ x, 0 < μ x := fun x => hc.trans_le (hμ x)
  have he :
      Solutions.Weak.weakSolutionIntegrand V (finiteExtension H) (canonicalGradient H)
          Du m u Dυ μ υ =ᵐ[volume.restrict (UnitCube d)]
        Solutions.Weak.weakSolutionIntegrand V H DpH Du m u Dυ μ υ := by
    filter_upwards [hreg.canonicalGradient_eq] with x hx
    simp only [Solutions.Weak.weakSolutionIntegrand,
      finiteExtension_of_pos H x _ (hpos x), hx _ _ (hpos x)]
  exact ⟨(h Dυ μ υ hadm).1.congr he,
    (integral_congr_ae he) ▸ (h Dυ μ υ hadm).2⟩

end StationaryMFG.Hamiltonian.Paper
