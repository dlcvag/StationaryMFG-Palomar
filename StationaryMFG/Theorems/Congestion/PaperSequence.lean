module

public import StationaryMFG.Theorems.Congestion.PaperWitnessIdentity
public import StationaryMFG.Theorems.Congestion.PaperHJBComplement

@[expose] public section

/-! # The regularized congestion sequence from derived local boundary facts -/

noncomputable section
namespace StationaryMFG.Theorems.Congestion.Paper

open MeasureTheory Filter Set Topology
open StationaryMFG.Hamiltonian StationaryMFG.Periodic StationaryMFG.Congestion
open scoped ENNReal NNReal

variable {d : ℕ}

/-- The complementary HJB equation at the same native witness used for
all a priori estimates and the energy identity. -/
theorem regularizedData_HJB_eq
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hcong : CongestionGrowthCore H DpH J)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (gammaBar hcong.α hcong.β))]
    {V : (Fin d → ℝ) → ℝ}
    (hV : MemLpPer (ENNReal.ofReal (betaBar' hcong.β)) V)
    (ε : ℝ) (hε : 0 < ε) :
    let w := (regularizedData hmon hcong hV ε hε).weakVI.choose
    ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < w.1 x →
      w.2.1 x + H x (fun i => w.2.2 i x) (w.1 x) - V x = 0 := by
  haveI : Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) :=
    ‹Fact (1 ≤ ENNReal.ofReal (gammaBar hcong.α hcong.β))›
  let data := regularizedData hmon hcong hV ε hε
  exact HJB_eq_pos_of_BanachVI hmon hcong hV.aestronglyMeasurable hV ε
    data.weakVI.choose data.weakVI.choose_spec.2
    (coeM_nonneg_atWitness_of_closure data rfl)
    (coeWeakDeriv_atWitness_of_closure data rfl)

/-- The entire sequence, with all PDE and identity fields proved internally.
The two local boundary facts are derived from the paper hypotheses for the
chosen representative by the final existence theorem. Neither requires
finite Hamiltonian values or zero flux at every boundary momentum. -/
noncomputable def sequenceData
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hcong : CongestionGrowthCore H DpH J)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (gammaBar hcong.α hcong.β))]
    {V : (Fin d → ℝ) → ℝ}
    (hV : MemLpPer (ENNReal.ofReal (betaBar' hcong.β)) V)
    (hzero : ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p L,
      Tendsto (H x p) (𝓝[>] (0 : ℝ)) (𝓝 L) → H x p 0 = L)
    (hfluxzero : ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p L,
      Tendsto (H x p) (𝓝[>] (0 : ℝ)) (𝓝 L) → J x p 0 = 0) :
    CongestionRegularizedSequenceDataNN V H DpH J
      (upstreamPack V hcong hV hmon.convex_at_zero).hPowerCong hcong.τ :=
  sequenceData_of_witnessProperties hmon hcong hV
    (regularizedData_raw_HJB hmon hcong hV hzero)
    (regularizedData_HJB_eq hmon hcong hV)
    (fun ε hε => regularizedData_identity hmon hcong hV hfluxzero ε hε
      (regularizedData_HJB_eq hmon hcong hV ε hε))

end StationaryMFG.Theorems.Congestion.Paper
