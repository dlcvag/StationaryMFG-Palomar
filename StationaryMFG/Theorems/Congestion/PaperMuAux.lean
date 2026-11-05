module

public import StationaryMFG.Hamiltonian.PaperExtension

@[expose] public section

/-!
# The positive-domain auxiliary density

Paper equation `mu-definition` takes its infimum over strictly positive
masses. In particular, arbitrary supplied values of H at zero cannot put
zero into the admissible set. The lemmas here recover the endpoint by
continuity at positive masses and obtain a finite boundary limit only
where the auxiliary infimum is zero.
-/

namespace StationaryMFG.Theorems.Congestion.Paper

open Filter Topology Set

def positiveAuxSet (F : ℝ → ℝ) (m b : ℝ) : Set ℝ :=
  {t | 0 < t ∧ m ≤ t ∧ F t ≤ b}

noncomputable def positiveAux (F : ℝ → ℝ) (m b : ℝ) : ℝ :=
  sInf (positiveAuxSet F m b)

theorem positiveAux_bddBelow (F : ℝ → ℝ) (m b : ℝ) :
    BddBelow (positiveAuxSet F m b) :=
  ⟨m, fun _ ht => ht.2.1⟩

theorem le_positiveAux {F : ℝ → ℝ} {m b : ℝ}
    (hne : (positiveAuxSet F m b).Nonempty) : m ≤ positiveAux F m b :=
  le_csInf hne fun _ ht => ht.2.1

theorem positiveAux_nonneg {F : ℝ → ℝ} {m b : ℝ}
    (hne : (positiveAuxSet F m b).Nonempty) : 0 ≤ positiveAux F m b :=
  le_csInf hne fun _ ht => ht.1.le

/-- At every positive threshold a, the infimum is at most a precisely
when a itself satisfies the two inequalities in the admissible set. -/
theorem positiveAux_le_iff {F : ℝ → ℝ} {m b a : ℝ}
    (hne : (positiveAuxSet F m b).Nonempty)
    (hcont : ContinuousOn F (Ioi (0 : ℝ)))
    (hanti : AntitoneOn F (Ioi (0 : ℝ))) (ha : 0 < a) :
    positiveAux F m b ≤ a ↔ m ≤ a ∧ F a ≤ b := by
  constructor
  · intro hle
    refine ⟨(le_positiveAux hne).trans hle, ?_⟩
    have hbound : ∀ᶠ r in 𝓝[>] a, F r ≤ b := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      obtain ⟨t, ht, htr⟩ := exists_lt_of_csInf_lt hne (hle.trans_lt hr)
      exact (hanti ht.1 (ha.trans hr) htr.le).trans ht.2.2
    exact le_of_tendsto
      ((hcont.continuousAt (isOpen_Ioi.mem_nhds ha)).tendsto.mono_left nhdsWithin_le_nhds)
      hbound
  · rintro ⟨hm, hF⟩
    exact csInf_le (positiveAux_bddBelow F m b) ⟨ha, hm, hF⟩

/-- A positive auxiliary infimum is an admissible point. -/
theorem positiveAux_mem_of_pos {F : ℝ → ℝ} {m b : ℝ}
    (hne : (positiveAuxSet F m b).Nonempty)
    (hcont : ContinuousOn F (Ioi (0 : ℝ)))
    (hanti : AntitoneOn F (Ioi (0 : ℝ)))
    (hpos : 0 < positiveAux F m b) :
    positiveAux F m b ∈ positiveAuxSet F m b :=
  ⟨hpos, (positiveAux_le_iff hne hcont hanti hpos).1 le_rfl⟩

/-- If the auxiliary infimum is zero, the positive-mass Hamiltonian is
bounded above at this particular momentum. -/
theorem bound_of_positiveAux_zero {F : ℝ → ℝ} {m b : ℝ}
    (hne : (positiveAuxSet F m b).Nonempty)
    (hcont : ContinuousOn F (Ioi (0 : ℝ)))
    (hanti : AntitoneOn F (Ioi (0 : ℝ)))
    (hz : positiveAux F m b = 0) :
    ∀ a, 0 < a → F a ≤ b := by
  intro a ha
  exact ((positiveAux_le_iff hne hcont hanti ha).1 (by simpa [hz] using ha.le)).2

/-- The local finite boundary value required by the paper's μ argument
is derived when μ=0; it is not postulated for every momentum. -/
theorem finiteBoundary_of_positiveAux_zero {F : ℝ → ℝ} {m b : ℝ}
    (hne : (positiveAuxSet F m b).Nonempty)
    (hcont : ContinuousOn F (Ioi (0 : ℝ)))
    (hanti : AntitoneOn F (Ioi (0 : ℝ)))
    (hz : positiveAux F m b = 0) :
    ∃ L : ℝ, L ≤ b ∧ Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  have hb : ∀ a, 0 < a → F a ≤ b := bound_of_positiveAux_zero hne hcont hanti hz
  have hbounded : BddAbove (F '' Ioi (0 : ℝ)) := by
    refine ⟨b, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    exact hb a ha
  refine ⟨sSup (F '' Ioi (0 : ℝ)), ?_, hanti.tendsto_nhdsGT hbounded⟩
  apply csSup_le
  · exact ⟨F 1, 1, by norm_num, rfl⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact hb a ha

/-- Above the original nonnegative density, the auxiliary constraint is
saturated. This argument uses continuity only at positive mass. -/
theorem positiveAux_value_eq_of_lt {F : ℝ → ℝ} {m b : ℝ}
    (hne : (positiveAuxSet F m b).Nonempty)
    (hcont : ContinuousOn F (Ioi (0 : ℝ)))
    (hanti : AntitoneOn F (Ioi (0 : ℝ))) (hm : 0 ≤ m)
    (hlt : m < positiveAux F m b) : F (positiveAux F m b) = b := by
  have hpos := hm.trans_lt hlt
  have hle := (positiveAux_mem_of_pos hne hcont hanti hpos).2.2
  apply le_antisymm hle
  by_contra hnot
  have hstrict : F (positiveAux F m b) < b := lt_of_not_ge hnot
  have hlocal : ∀ᶠ t in 𝓝[<] (positiveAux F m b),
      m < t ∧ F t < b :=
    ((eventually_gt_nhds hlt).and
      ((hcont.continuousAt (isOpen_Ioi.mem_nhds hpos)).eventually
        (eventually_lt_nhds hstrict))).filter_mono nhdsWithin_le_nhds
  obtain ⟨t, ⟨hmt, hFt⟩, htμ⟩ := (hlocal.and self_mem_nhdsWithin).exists
  have htmem : t ∈ positiveAuxSet F m b := ⟨hm.trans_lt hmt, hmt.le, hFt.le⟩
  have hμt := csInf_le (positiveAux_bddBelow F m b) htmem
  exact (not_lt_of_ge hμt) htμ

/-- The product identity is independent of the chosen real extension at
zero, because μ=0 forces m=0. Its positive branch is the paper's identity. -/
theorem positiveAux_product_identity {F G : ℝ → ℝ} {m b : ℝ}
    (hne : (positiveAuxSet F m b).Nonempty)
    (hcont : ContinuousOn F (Ioi (0 : ℝ)))
    (hanti : AntitoneOn F (Ioi (0 : ℝ))) (hm : 0 ≤ m)
    (hG : ∀ t, 0 < t → G t = F t) :
    (positiveAux F m b - m) * (G (positiveAux F m b) - b) = 0 := by
  rcases eq_or_lt_of_le (le_positiveAux hne) with heq | hlt
  · rw [← heq, sub_self, zero_mul]
  · rw [hG _ (hm.trans_lt hlt), positiveAux_value_eq_of_lt hne hcont hanti hm hlt,
      sub_self, mul_zero]

/-- Every positive truncation of the auxiliary density satisfies the
Hamiltonian upper bound, including when its infimum is zero. -/
theorem positiveAux_max_bound {F : ℝ → ℝ} {m b δ : ℝ}
    (hne : (positiveAuxSet F m b).Nonempty)
    (hcont : ContinuousOn F (Ioi (0 : ℝ)))
    (hanti : AntitoneOn F (Ioi (0 : ℝ))) (hδ : 0 < δ) :
    F (max (positiveAux F m b) δ) ≤ b :=
  ((positiveAux_le_iff hne hcont hanti
    (hδ.trans_le (le_max_right _ _))).1 (le_max_left _ _)).2

/-- The auxiliary construction is unchanged by altering nonpositive
values of F. In particular it can use a canonical representative. -/
theorem positiveAux_congr_on_pos {F G : ℝ → ℝ} (m b : ℝ)
    (h : ∀ t, 0 < t → F t = G t) : positiveAux F m b = positiveAux G m b := by
  unfold positiveAux
  congr 1
  ext t
  constructor <;> intro ht
  · exact ⟨ht.1, ht.2.1, by simpa only [← h t ht.1] using ht.2.2⟩
  · exact ⟨ht.1, ht.2.1, by simpa only [h t ht.1] using ht.2.2⟩

end StationaryMFG.Theorems.Congestion.Paper
