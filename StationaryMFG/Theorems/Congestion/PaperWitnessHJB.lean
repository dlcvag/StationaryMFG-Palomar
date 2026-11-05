module

public import StationaryMFG.Theorems.Congestion.PaperAbstractHJB
public import StationaryMFG.Theorems.Congestion.StrongIsStrong

@[expose] public section

/-! # The paper's HJB inequality at the Banach variational witness -/

namespace StationaryMFG.Theorems.Congestion.Paper

open scoped ENNReal
open MeasureTheory Filter Set Topology
open StationaryMFG.Hamiltonian StationaryMFG.Hamiltonian.Paper StationaryMFG.Periodic
open StationaryMFG.Congestion StationaryMFG.Solutions.MFG

variable {d : ℕ}

/-- The regularized Banach witness satisfies the extended-real HJB inequality.
All boundary values used in this proof are derived at its actual arguments. -/
theorem HJB_le_of_BanachVI
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hcong : CongestionGrowthCore H DpH J)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    {V : (Fin d → ℝ) → ℝ}
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV : MemLpPer (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (ε : ℝ)
    (w : congestionXBanach d (ENNReal.ofReal (hcong.β + 1))
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))
    (hVI : ∀ v ∈ congestionBanachK d
      (ENNReal.ofReal (hcong.β + 1))
      (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
      hcong.α hcong.β hcong.τ,
      0 ≤ congestionAepsiOpK hmon hcong hVmeas hV ε v (v - w))
    (hmnn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ w.1 x)
    (hDuWeak : ∀ i, HasWeakDerivPer i (⇑w.2.1) (⇑(w.2.2 i))) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      Hext H x (fun i => w.2.2 i x) (w.1 x) ≤ ((V x - w.2.1 x : ℝ) : WithTop ℝ) := by
  have hm : MemLpPer (ENNReal.ofReal (hcong.β + 1)) (⇑w.1) := Lp.memLp w.1
  have huGamma : MemLpPer
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (⇑w.2.1) :=
    Lp.memLp w.2.1
  have hDu : ∀ i, MemLpPer
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (⇑(w.2.2 i)) :=
    fun i => Lp.memLp (w.2.2 i)
  have hu : MemLpPer (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) (⇑w.2.1) := by
    apply huGamma.mono_exponent_finite _ ENNReal.ofReal_ne_top
    apply ENNReal.ofReal_le_ofReal
    have hb : 0 < (hcong.β + 1) / hcong.β := div_pos (by linarith [hcong.hβ]) hcong.hβ
    nlinarith [mul_le_mul_of_nonneg_right hcong.hα.le hb.le,
      mul_div_assoc hcong.α (hcong.β + 1) hcong.β]
  apply HJB_le_of_positiveAux_truncationVI hmon hcong hm hu hV hDu hmnn
  intro k hk δ hδ
  have hμ := positiveAux_memLp (k := k) hmon hcong hm hu hV hDu
  have hQ := positiveAux_quotient_memLp (k := k) hmon hcong hm hu hV hDu
  have hne := positiveAuxSet_nonempty_of_congestionGrowth hmon hcong k
    (⇑w.1) (⇑w.2.1) V (fun i => ⇑(w.2.2 i))
  have hμnn := hne.mono fun _ hx => positiveAux_nonneg hx
  exact perdelta_vi_integral_le_of_density hmon hcong hμ hQ hμnn hVmeas hV
    rfl rfl hVI rfl rfl (fun _ => rfl) hDuWeak hδ

end StationaryMFG.Theorems.Congestion.Paper
