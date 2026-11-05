module

public import StationaryMFG.Hamiltonian.Monotone
public import Mathlib.Topology.Order.Monotone
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-!
# Boundary limits and canonical representatives

Paper Remark `rmk:cxty`: mass monotonicity gives a right limit in
`ℝ ∪ {∞}`. When that limit is finite, a sequence of positive masses
constructs a measurable, periodic real representative at zero. The
construction never uses the arbitrary supplied value of H at zero.
-/

namespace StationaryMFG.Hamiltonian.Paper

open MeasureTheory Filter Topology Set StationaryMFG.Periodic

variable {d : ℕ}

/-- Every antitone real function on positive masses has a right limit,
possibly positive infinity. No growth assumption is used. -/
theorem exists_boundary_limit_of_antitone {f : ℝ → ℝ}
    (hf : AntitoneOn f (Ioi (0 : ℝ))) :
    ∃ L : WithTop ℝ, Tendsto (fun m => (f m : WithTop ℝ)) (𝓝[>] 0) (𝓝 L) := by
  by_cases hb : BddAbove (f '' Ioi (0 : ℝ))
  · exact ⟨↑(sSup (f '' Ioi (0 : ℝ))),
      WithTop.continuous_coe.continuousAt.tendsto.comp (hf.tendsto_nhdsGT hb)⟩
  · refine ⟨⊤, (WithTop.tendsto_nhds_top_iff _).2 ?_⟩
    intro b
    obtain ⟨y, ⟨m, hm, rfl⟩, hby⟩ := not_bddAbove_iff.1 hb b
    filter_upwards [Ioo_mem_nhdsGT hm] with t ht
    exact WithTop.coe_lt_coe.2 (hby.trans_le (hf ht.1 hm ht.2.le))

/-- A positive sequence tending to zero, fixed for all representatives. -/
noncomputable def boundaryMass (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem boundaryMass_pos (n : ℕ) : 0 < boundaryMass n := by
  unfold boundaryMass
  positivity

theorem boundaryMass_tendsto : Tendsto boundaryMass atTop (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
    Eventually.of_forall boundaryMass_pos⟩

/-- A real boundary trace defined from positive masses. Its value at a
point with an infinite or nonexistent real limit is irrelevant to the
finite-boundary specialization and is never asserted to equal Hext there. -/
noncomputable def boundaryTrace
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (x p : Fin d → ℝ) : ℝ :=
  limUnder atTop (fun n => H x p (boundaryMass n))

theorem boundaryTrace_eq_of_tendsto
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {x p : Fin d → ℝ} {L : ℝ}
    (h : Tendsto (H x p) (𝓝[>] 0) (𝓝 L)) : boundaryTrace H x p = L :=
  (h.comp boundaryMass_tendsto).limUnder_eq

/-- The canonical finite extension, retaining H exactly on positive mass. -/
noncomputable def finiteExtension
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (x p : Fin d → ℝ) (m : ℝ) : ℝ :=
  if 0 < m then H x p m else boundaryTrace H x p

@[simp] theorem finiteExtension_of_pos
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (x p : Fin d → ℝ) {m : ℝ} (hm : 0 < m) :
    finiteExtension H x p m = H x p m := if_pos hm

@[simp] theorem finiteExtension_zero
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (x p : Fin d → ℝ) :
    finiteExtension H x p 0 = boundaryTrace H x p := by
  simp [finiteExtension]

theorem boundaryTrace_periodic
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    (hper : ∀ p m, 0 < m → IsPeriodic (fun x => H x p m))
    (p : Fin d → ℝ) : IsPeriodic (fun x => boundaryTrace H x p) := by
  intro k x
  unfold boundaryTrace
  apply congrArg (limUnder atTop)
  funext n
  exact hper p _ (boundaryMass_pos n) k x

theorem finiteExtension_periodic
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    (hper : ∀ p m, 0 < m → IsPeriodic (fun x => H x p m))
    (p : Fin d → ℝ) (m : ℝ) : IsPeriodic (fun x => finiteExtension H x p m) := by
  by_cases hm : 0 < m
  · simpa only [finiteExtension, if_pos hm] using hper p m hm
  · simpa only [finiteExtension, if_neg hm] using boundaryTrace_periodic hper p

theorem boundaryTrace_measurable
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    (hH : Measurable
      (fun (xpm : (Fin d → ℝ) × (Fin d → ℝ) × {m : ℝ // 0 < m}) =>
        H xpm.1 xpm.2.1 xpm.2.2)) :
    Measurable (fun xp : (Fin d → ℝ) × (Fin d → ℝ) => boundaryTrace H xp.1 xp.2) := by
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.limUnder
  intro n
  exact (hH.comp (measurable_fst.prodMk
    (measurable_snd.prodMk (measurable_const
      (a := (⟨boundaryMass n, boundaryMass_pos n⟩ : {m : ℝ // 0 < m})))))).stronglyMeasurable

theorem finiteExtension_measurable
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    (hH : Measurable
      (fun (xpm : (Fin d → ℝ) × (Fin d → ℝ) × {m : ℝ // 0 < m}) =>
        H xpm.1 xpm.2.1 xpm.2.2)) :
    Measurable (fun xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ =>
      finiteExtension H xpm.1 xpm.2.1 xpm.2.2) := by
  let s : Set ((Fin d → ℝ) × (Fin d → ℝ) × ℝ) := {xpm | 0 < xpm.2.2}
  have hs : MeasurableSet s := measurableSet_lt measurable_const (measurable_snd.snd)
  have hpos : Measurable (fun xpm : s => H xpm.1.1 xpm.1.2.1 xpm.1.2.2) := by
    exact hH.comp ((measurable_fst.comp measurable_subtype_coe).prodMk
      (((measurable_fst.comp measurable_snd).comp measurable_subtype_coe).prodMk
        (((measurable_snd.comp measurable_snd).comp measurable_subtype_coe).subtype_mk
          (h := fun y => y.property))))
  have hneg : Measurable (fun xpm : ↥(sᶜ) => boundaryTrace H xpm.1.1 xpm.1.2.1) :=
    (boundaryTrace_measurable hH).comp
      ((measurable_fst.comp measurable_subtype_coe).prodMk
        ((measurable_fst.comp measurable_snd).comp measurable_subtype_coe))
  exact hpos.dite hneg hs

/-- The extended Hamiltonian depends only on the positive-mass data. -/
theorem Hext_congr_on_pos
    {H G : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {x p : Fin d → ℝ}
    (h : ∀ m, 0 < m → H x p m = G x p m) (m : ℝ) :
    Hext H x p m = Hext G x p m := by
  by_cases hm : 0 < m
  · simp only [Hext, if_pos hm, h m hm]
  · simp only [Hext, if_neg hm]
    congr 1
    funext L
    apply propext
    apply tendsto_congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact congrArg (fun r : ℝ => (r : WithTop ℝ)) (h t ht)

/-- Identify the extended boundary value at any point with a real limit. -/
theorem Hext_zero_eq_of_tendsto
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {x p : Fin d → ℝ} {L : ℝ}
    (h : Tendsto (H x p) (𝓝[>] 0) (𝓝 L)) :
    Hext H x p 0 = (L : WithTop ℝ) := by
  have hc := WithTop.continuous_coe.continuousAt.tendsto.comp h
  exact tendsto_nhds_unique (tendsto_Hext_zero_of_exists ⟨(L : WithTop ℝ), hc⟩) hc

theorem finiteExtension_tendsto_of_tendsto
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {x p : Fin d → ℝ} {L : ℝ}
    (h : Tendsto (H x p) (𝓝[>] 0) (𝓝 L)) :
    Tendsto (finiteExtension H x p) (𝓝[>] 0) (𝓝 L) := by
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (finiteExtension_of_pos H x p ht).symm

/-- Finite right limits give boundary agreement for the canonical extension,
without imposing any condition on the supplied values of H at zero. -/
theorem finiteExtension_agree
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    (hlim : ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p : Fin d → ℝ,
      ∃ L : ℝ, Tendsto (H x p) (𝓝[>] 0) (𝓝 L)) :
    H_zero_eq_Hext (finiteExtension H) := by
  filter_upwards [hlim] with x hx p
  obtain ⟨L, hL⟩ := hx p
  rw [finiteExtension_zero, boundaryTrace_eq_of_tendsto hL,
    Hext_zero_eq_of_tendsto (finiteExtension_tendsto_of_tendsto hL)]

/-- The canonical finite extension also satisfies the boundary-limit bundle. -/
theorem finiteExtension_hat0
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    (hlim : ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p : Fin d → ℝ,
      ∃ L : ℝ, Tendsto (H x p) (𝓝[>] 0) (𝓝 L)) :
    HypothesisHat0 (finiteExtension H) := by
  constructor
  filter_upwards [hlim] with x hx p
  obtain ⟨L, hL⟩ := hx p
  exact ⟨(L : WithTop ℝ), WithTop.continuous_coe.continuousAt.tendsto.comp
    (finiteExtension_tendsto_of_tendsto hL)⟩

end StationaryMFG.Hamiltonian.Paper
