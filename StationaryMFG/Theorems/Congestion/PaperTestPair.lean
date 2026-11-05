module

public import StationaryMFG.Theorems.Congestion.PaperTestPairBase
public import StationaryMFG.Theorems.Congestion.MuIntegrability
public import StationaryMFG.Theorems.Congestion.PaperMuAux

@[expose] public section

/-!
# Positive truncations as congestion test pairs

The density is arbitrary here. In the corrected proof it is the infimum
over positive masses. Admissibility uses its derived quotient integrability;
no Hamiltonian value at zero enters the test pair.
-/

namespace StationaryMFG.Theorems.Congestion.Paper

open scoped ENNReal

open MeasureTheory Filter Set Topology
open StationaryMFG.Periodic StationaryMFG.Congestion

variable {d : ℕ}

/-- The positive auxiliary infimum is periodic when its data are periodic. -/
theorem positiveAux_periodic
    {F : (Fin d → ℝ) → ℝ → ℝ} {m b : (Fin d → ℝ) → ℝ}
    (hF : ∀ t, 0 < t → IsPeriodic (fun x => F x t))
    (hm : IsPeriodic m) (hb : IsPeriodic b) :
    IsPeriodic (fun x => positiveAux (F x) (m x) (b x)) := by
  intro κ x
  dsimp only
  rw [hm κ x, hb κ x]
  apply positiveAux_congr_on_pos
  intro t ht
  exact hF t ht κ x

/-- Truncating any admissible weighted density preserves its quotient
integrability and gives the strictly positive lower bound required in K. -/
noncomputable def positiveTruncTestPair
    {βBar βBarPrime γBar : ℝ≥0∞} {α β τ δ : ℝ}
    {μ u : (Fin d → ℝ) → ℝ} {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hδ : 0 < δ) (hτ : 0 ≤ τ) (hαt : 0 ≤ α * (1 + τ / β))
    (hμPer : IsPeriodic μ) (huPer : IsPeriodic u) (hDuPer : ∀ i, IsPeriodic (Du i))
    (hμ : MemLpPer βBar μ)
    (hμnn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ μ x)
    (hu : MemSobolevPer γBar u)
    (hDu : ∀ i, MemLpPer γBar (Du i))
    (hDuWeak : ∀ i, HasWeakDerivPer i u (Du i))
    (hQ : MemLpPer βBarPrime (fun x =>
      ‖fun i => Du i x‖ ^ (α * (1 + τ / β)) / (μ x ^ τ + 1))) :
    CongestionLimitVITestPair (d := d) βBar βBarPrime γBar α β τ := by
  let ρ : (Fin d → ℝ) → ℝ := fun x => max (μ x) δ
  have hρ : MemLpPer βBar ρ := mPerDelta_memLpPer hδ.le hμ hμnn
  have hratio : MemLpPer βBarPrime (fun x =>
      ‖fun i => Du i x‖ ^ (α * (1 + τ / β)) / (ρ x ^ τ + 1)) := by
    apply MemLp.toMemLpPer
    apply MemLp.mono' hQ.toMemLp
    · have hp : AEMeasurable (fun x i => Du i x) (volume.restrict (UnitCube d)) :=
        aemeasurable_pi_iff.mpr fun i => (hDu i).aestronglyMeasurable.aemeasurable
      have hn := (Real.continuous_rpow_const hαt).comp_aestronglyMeasurable
        hp.aestronglyMeasurable.norm
      have hd := ((Real.continuous_rpow_const hτ).comp_aestronglyMeasurable
        hρ.aestronglyMeasurable).add (aestronglyMeasurable_const (b := (1 : ℝ)))
      exact (hn.aemeasurable.div hd.aemeasurable).aestronglyMeasurable
    · filter_upwards [hμnn] with x hx
      have hρnn : 0 ≤ ρ x := hδ.le.trans (le_max_right _ _)
      have hn : 0 ≤ ‖fun i => Du i x‖ ^ (α * (1 + τ / β)) :=
        Real.rpow_nonneg (norm_nonneg _) _
      have hd : 0 < μ x ^ τ + 1 := by
        have := Real.rpow_nonneg hx τ
        positivity
      have hρd : 0 < ρ x ^ τ + 1 := by
        have := Real.rpow_nonneg hρnn τ
        positivity
      rw [Real.norm_of_nonneg (div_nonneg hn hρd.le)]
      exact div_le_div_of_nonneg_left hn hd
        (by dsimp [ρ]; linarith [Real.rpow_le_rpow hx (le_max_left (μ x) δ) hτ])
  exact
    { μ := ρ
      υ := u
      Dυ := Du
      hμPer := by intro κ x; dsimp [ρ]; rw [hμPer κ x]
      hυPer := huPer
      hDυPer := hDuPer
      μLp := hρ
      υSob := hu
      μ_lower := ⟨δ, hδ, Eventually.of_forall fun x => le_max_right _ _⟩
      hDυ_weak := hDuWeak
      hRatio_memLp := hratio
      hDυ_memGamma := hDu }

end StationaryMFG.Theorems.Congestion.Paper
