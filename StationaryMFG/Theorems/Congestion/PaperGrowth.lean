module

public import StationaryMFG.Hamiltonian.PaperRegularity
public import StationaryMFG.Theorems.Congestion.PaperBoundary

@[expose] public section

/-!
# Literal congestion-growth interface and its local boundary consequences

This is the growth specification of the corrected standalone challenge.
It contains neither finite Hamiltonian boundary values nor a globally zero
limiting flux. The zero-flux result below is derived only at momenta with
finite Hamiltonian boundary values.
-/

namespace StationaryMFG.Hamiltonian.Paper

open MeasureTheory Filter Set Topology
open StationaryMFG.Periodic
open scoped StationaryMFG.Hamiltonian

variable {d : ℕ}

/-- Assumption (A3), with the paper's general flux extension (H3). -/
structure HypothesisCongestionGrowth
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    extends RegularityH H DpH where
  C : ℝ
  α : ℝ
  β : ℝ
  τ : ℝ
  hC : 0 < C
  hα : 1 < α
  hβ : 0 < β
  hτ : 0 ≤ τ ∧ τ ≤ 1
  mDpHat0 : PaperFluxExtension DpH J
  upper :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ m, 0 < m → H x (0 : Fin d → ℝ) m ≤ -(m ^ β) / C + C
  DpH_upper :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p m, 0 < m →
        ‖DpH x p m‖
          ≤ C * ((1 / m) + (1 / m ^ τ)) * (‖p‖ ^ (α * (1 + τ / β) - 1))
            + C * ((m ^ (β - β / α)) + 1 / m)
  lower :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p m, 0 < m →
        H x p m
          ≥ (1 / C) * (1 / (m ^ τ + 1)) * (‖p‖ ^ (α * (1 + τ / β)))
            - C * (m ^ β + 1)

variable {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
variable {DpH J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}

/-- The congestion flux bound extends to vacuum by the prescribed limit.
This proof never assumes J(p,0)=0. -/
theorem HypothesisCongestionGrowth.mDpH_extended_bound
    (h : HypothesisCongestionGrowth H DpH J) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p m, 0 ≤ m →
      ‖J x p m‖ ≤
        h.C * (1 + m ^ (1 - h.τ)) * ‖p‖ ^ (h.α * (1 + h.τ / h.β) - 1)
          + h.C * (m ^ (h.β + 1 - h.β / h.α) + 1) := by
  have hαpos : 0 < h.α := lt_trans zero_lt_one h.hα
  have hs : 0 ≤ 1 - h.τ := sub_nonneg.mpr h.hτ.2
  have hb : 0 ≤ h.β + 1 - h.β / h.α := by
    have hd : h.β / h.α < h.β := (div_lt_iff₀ hαpos).mpr (by nlinarith [h.hα, h.hβ])
    linarith
  filter_upwards [h.DpH_upper, h.mDpHat0.tendsto_at_zero] with x hbound hlim
  intro p m hm
  let R : ℝ → ℝ := fun t =>
    h.C * (1 + t ^ (1 - h.τ)) * ‖p‖ ^ (h.α * (1 + h.τ / h.β) - 1)
      + h.C * (t ^ (h.β + 1 - h.β / h.α) + 1)
  have hR : Continuous R := by
    exact ((continuous_const.mul (continuous_const.add
      (Real.continuous_rpow_const hs))).mul continuous_const).add
        (continuous_const.mul ((Real.continuous_rpow_const hb).add continuous_const))
  have hpos : ∀ t, 0 < t → ‖t • DpH x p t‖ ≤ R t := by
    intro t ht
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    have hdiv : t / t ^ h.τ = t ^ (1 - h.τ) := by
      rw [Real.rpow_sub ht, Real.rpow_one]
    have hmul : t * t ^ (h.β - h.β / h.α) = t ^ (h.β + 1 - h.β / h.α) := by
      conv_lhs => lhs; rw [← Real.rpow_one t]
      rw [← Real.rpow_add ht]
      congr 1
      ring
    calc t * ‖DpH x p t‖ ≤ t *
        (h.C * (1 / t + 1 / t ^ h.τ) * ‖p‖ ^ (h.α * (1 + h.τ / h.β) - 1)
          + h.C * (t ^ (h.β - h.β / h.α) + 1 / t)) :=
        mul_le_mul_of_nonneg_left (hbound p t ht) ht.le
      _ = h.C * (t / t + t / t ^ h.τ) * ‖p‖ ^ (h.α * (1 + h.τ / h.β) - 1)
          + h.C * (t * t ^ (h.β - h.β / h.α) + t / t) := by ring
      _ = R t := by rw [div_self ht.ne', hdiv, hmul]
  rcases eq_or_lt_of_le hm with hz | hp
  · subst m
    apply le_of_tendsto_of_tendsto ((hlim p).norm)
      (hR.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hpos t ht
  · rw [h.mDpHat0.J_of_pos x p m hp]
    exact hpos m hp

/-- Congestion growth gives a uniform lower bound near zero mass, even
where the boundary value of H is infinite. -/
theorem HypothesisCongestionGrowth.lower_near_zero
    (h : HypothesisCongestionGrowth H DpH J) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p,
      ∀ᶠ m in 𝓝[>] (0 : ℝ), -(2 * h.C) ≤ H x p m := by
  filter_upwards [h.lower] with x hx p
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with m hm
  have hpow : m ^ h.β ≤ 1 := Real.rpow_le_one hm.1.le hm.2.le h.hβ.le
  have hmτ : 0 ≤ m ^ h.τ := Real.rpow_nonneg hm.1.le _
  have hC : 0 < h.C := h.hC
  have hterm : 0 ≤ (1 / h.C) * (1 / (m ^ h.τ + 1)) *
      (‖p‖ ^ (h.α * (1 + h.τ / h.β))) := by positivity
  have hl := hx p m hm.1
  nlinarith [mul_le_mul_of_nonneg_left hpow h.hC.le]

/-- The zero flux needed at finite solution arguments follows locally
from the paper assumptions. No conclusion is made at infinite-H momenta. -/
theorem HypothesisCongestionGrowth.flux_zero_at_finite_boundary
    (hmon : HypothesisMonotone H DpH)
    (h : HypothesisCongestionGrowth H DpH J) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p L,
      Tendsto (H x p) (𝓝[>] (0 : ℝ)) (𝓝 L) → J x p 0 = 0 := by
  filter_upwards [hmon.supporting_hyperplane, h.lower_near_zero,
    h.mDpHat0.tendsto_at_zero, h.mDpHat0.continuous_J]
    with x hs hl hj hc p L hfinite
  apply StationaryMFG.Theorems.Congestion.Paper.boundary_flux_zero_at_finite_point
    hfinite (fun q m hm => hs p q m hm)
    (fun q => ⟨2 * h.C, hl q⟩) hj
  exact (hc.comp_continuous (continuous_id.prodMk continuous_const)
    (fun _ => show (0 : ℝ) ≤ 0 from le_rfl)).continuousAt

/-- The raw product and limiting flux agree at a nonnegative density
when finite boundary limits have been established at its actual vacuum
momenta. This replaces the old global J_zero_at_zero premise locally. -/
theorem HypothesisCongestionGrowth.ae_flux_eq_raw_of_finite_boundary
    (hmon : HypothesisMonotone H DpH)
    (h : HypothesisCongestionGrowth H DpH J)
    (p : (Fin d → ℝ) → (Fin d → ℝ))
    (m : (Fin d → ℝ) → ℝ)
    (hm : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hfinite : ∀ᵐ x ∂(volume.restrict (UnitCube d)), m x = 0 →
      ∃ L : ℝ, Tendsto (H x (p x)) (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      J x (p x) (m x) = m x • DpH x (p x) (m x) := by
  filter_upwards [hm, hfinite, h.flux_zero_at_finite_boundary hmon] with x hmx hfx hz
  rcases eq_or_lt_of_le hmx with he | hp
  · have he' : m x = 0 := he.symm
    obtain ⟨L, hL⟩ := hfx he'
    rw [he', hz (p x) L hL, zero_smul]
  · exact h.mDpHat0.J_of_pos x (p x) (m x) hp

end StationaryMFG.Hamiltonian.Paper
