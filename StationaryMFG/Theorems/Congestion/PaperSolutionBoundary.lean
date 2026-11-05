module

public import StationaryMFG.Theorems.Congestion.PaperMuIntegrability
public import StationaryMFG.Theorems.Congestion.PaperHJB

@[expose] public section

/-! # Boundary and integrability consequences of the extended HJB bound -/

namespace StationaryMFG.Theorems.Congestion.Paper

open scoped ENNReal
open MeasureTheory Filter Set Topology
open StationaryMFG.Hamiltonian StationaryMFG.Hamiltonian.Paper StationaryMFG.Periodic

variable {d : ℕ}
variable {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}

/-- Positive slices lie below the extended right limit, including an
infinite limit. -/
theorem H_le_Hext_zero_of_antitone {x p : Fin d → ℝ} {a : ℝ}
    (hanti : AntitoneOn (H x p) (Ioi (0 : ℝ))) (ha : 0 < a) :
    (H x p a : WithTop ℝ) ≤ Hext H x p 0 := by
  have hlim := tendsto_Hext_zero_of_exists (exists_boundary_limit_of_antitone hanti)
  apply ge_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsGT ha] with t ht
  exact WithTop.coe_le_coe.mpr (hanti ht.1 ha ht.2.le)

/-- A finite upper bound on Hext excludes the infinite boundary limit. -/
theorem finiteBoundary_of_Hext_zero_le {x p : Fin d → ℝ} {b : ℝ}
    (ha : AntitoneOn (H x p) (Ioi (0 : ℝ)))
    (hH : Hext H x p 0 ≤ (b : WithTop ℝ)) :
    ∃ L : ℝ, L ≤ b ∧ Tendsto (H x p) (𝓝[>] 0) (𝓝 L) := by
  have hn : Hext H x p 0 ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hH
  lift Hext H x p 0 to ℝ using hn with L hL
  have ht := tendsto_Hext_zero_of_exists (exists_boundary_limit_of_antitone ha)
  change Tendsto (fun m => (H x p m : WithTop ℝ)) (𝓝[>] 0)
    (𝓝 (Hext H x p 0)) at ht
  rw [← hL] at ht
  refine ⟨L, WithTop.coe_le_coe.mp hH, ?_⟩
  have hr := (WithTop.tendsto_untopD (0 : ℝ) (a := (L : WithTop ℝ))
    WithTop.coe_ne_top).comp ht
  simpa only [Function.comp_def, WithTop.untopD_coe] using hr

/-- Any chosen real representative agreeing with finite boundary limits
inherits the real HJB inequality at the actual solution arguments. -/
theorem raw_HJB_of_Hext_le
    {x p : Fin d → ℝ} {m b : ℝ}
    (ha : AntitoneOn (H x p) (Ioi (0 : ℝ))) (hm : 0 ≤ m)
    (hzero : ∀ L : ℝ, Tendsto (H x p) (𝓝[>] 0) (𝓝 L) → H x p 0 = L)
    (hH : Hext H x p m ≤ (b : WithTop ℝ)) : H x p m ≤ b := by
  rcases hm.eq_or_lt with hm0 | hm0
  · subst m
    obtain ⟨L, hLb, hL⟩ := finiteBoundary_of_Hext_zero_le ha hH
    rwa [hzero L hL]
  · rw [Hext_of_pos H x p hm0] at hH
    exact WithTop.coe_le_coe.mp hH

/-- Once the HJB upper bound holds, the auxiliary density is exactly the
solution density. Thus its already-proved integrability bounds apply at m. -/
theorem positiveAux_eq_of_Hext_le {x p : Fin d → ℝ} {m b : ℝ}
    (hne : (positiveAuxSet (H x p) m b).Nonempty)
    (hc : ContinuousOn (H x p) (Ioi (0 : ℝ)))
    (ha : AntitoneOn (H x p) (Ioi (0 : ℝ)))
    (hm : 0 ≤ m) (hH : Hext H x p m ≤ (b : WithTop ℝ)) :
    positiveAux (H x p) m b = m := by
  apply le_antisymm _ (le_positiveAux hne)
  apply le_of_forall_gt_imp_ge_of_dense
  intro a hma
  have ha0 : 0 < a := hm.trans_lt hma
  apply (positiveAux_le_iff hne hc ha ha0).2
  refine ⟨hma.le, ?_⟩
  have hHa : (H x p a : WithTop ℝ) ≤ Hext H x p m := by
    rcases hm.eq_or_lt with hm0 | hm0
    · subst m
      exact H_le_Hext_zero_of_antitone ha ha0
    · rw [Hext_of_pos H x p hm0]
      exact WithTop.coe_le_coe.mpr (ha hm0 ha0 hma.le)
  exact WithTop.coe_le_coe.mp (hHa.trans hH)

/-- The weighted gradient quotient of a weak solution is in the dual
density space as soon as its extended HJB inequality has been proved. -/
theorem solution_quotient_memLp
    {DpH J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hcong : CongestionGrowthCore H DpH J)
    {m u V : (Fin d → ℝ) → ℝ} {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm : MemLpPer (ENNReal.ofReal (hcong.β + 1)) m)
    (hu : MemLpPer (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) u)
    (hV : MemLpPer (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (hDu : ∀ i, MemLpPer
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Du i))
    (hmnn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hHJB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      Hext H x (fun i => Du i x) (m x) ≤ ((V x - u x : ℝ) : WithTop ℝ)) :
    MemLpPer (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
      (fun x => ‖fun i => Du i x‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) /
        (m x ^ hcong.τ + 1)) := by
  have hQ := positiveAux_quotient_memLp (k := 0) hmon hcong hm hu hV hDu
  apply MemLp.toMemLpPer
  apply MemLp.ae_eq (hf_Lp := hQ.toMemLp)
  filter_upwards [hmon.continuous_H_pm, antitone_in_m hmon, hmnn, hHJB,
    positiveAuxSet_nonempty_of_congestionGrowth hmon hcong 0 m u V Du]
    with x hc ha hn hH he
  have hc' : ContinuousOn (H x (fun i => Du i x)) (Ioi 0) :=
    hc.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ ht => ht)
  have hH' : Hext H x (fun i => Du i x) (m x) ≤
      ((0 - u x + V x : ℝ) : WithTop ℝ) := by simpa [sub_eq_add_neg, add_comm] using hH
  rw [positiveAux_eq_of_Hext_le he hc' (ha _) hn hH']

end StationaryMFG.Theorems.Congestion.Paper
