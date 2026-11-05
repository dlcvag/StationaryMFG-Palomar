module

public import StationaryMFG.Theorems.InfimalConvolution.InfConv
public import StationaryMFG.Hamiltonian.PaperExtension
public import Mathlib.Topology.Order.Monotone

@[expose] public section

/-!
# Finite boundary traces of the regularized Hamiltonian

The original Hamiltonian may have an infinite right-hand limit at zero mass.
Nevertheless, each positive-scale infimal convolution has a finite boundary
trace. Test the competitor q = p to obtain an upper bound independent of mass;
monotonicity in mass then gives convergence to a finite supremum.

None of these results assumes a boundary value, boundary agreement, or boundary
continuity for the original H. They do not identify the trace with the raw
`Hdelta h ε x p 0`, which inf-convolves the arbitrary supplied value H at zero.
The trace must be used in the corrected closed-cone regularization.
-/

noncomputable section

namespace StationaryMFG.InfimalConvolution

open StationaryMFG.Hamiltonian StationaryMFG.Periodic
open MeasureTheory Filter Topology

variable {d : ℕ}
variable {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
variable {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}

private lemma paper_bddBelow_penalty
    (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) {x p : Fin d → ℝ} {m : ℝ}
    (hLower : ∀ r, (‖r‖ ^ h.α) / h.C - h.C * (m ^ h.β + 1) ≤ H x r m) :
    BddBelow (Set.range fun q : Fin d → ℝ =>
      H x (p - q) m + (1 / ε) * K h q) := by
  refine ⟨-(h.C * (m ^ h.β + 1)), ?_⟩
  rintro _ ⟨q, rfl⟩
  have hdiv : 0 ≤ ‖p - q‖ ^ h.α / h.C :=
    div_nonneg (Real.rpow_nonneg (norm_nonneg _) _) h.hC.le
  have hpen : 0 ≤ (1 / ε) * K h q :=
    mul_nonneg (one_div_pos.mpr hε).le (K_nonneg h q)
  linarith [hLower (p - q)]

/-- The q = p competitor bounds Hε by a finite quantity independently of mass.
Only positive-mass upper and lower bounds are used. -/
theorem Hdelta_le_zeroMomentum_add_penalty
    (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p m, 0 < m →
      Hdelta h ε x p m ≤ H x 0 m + (1 / ε) * K h p := by
  filter_upwards [h.lower] with x hx p m hm
  have hb := paper_bddBelow_penalty h hε (p := p) (fun r => hx r m hm)
  simpa only [Hdelta, sub_self] using ciInf_le hb p

/-- A uniform-in-mass upper bound for every fixed positive regularization scale. -/
theorem Hdelta_le_boundary_envelope
    (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p m, 0 < m →
      Hdelta h ε x p m ≤ h.C + (1 / ε) * K h p := by
  filter_upwards [Hdelta_le_zeroMomentum_add_penalty h hε, h.upper]
    with x hreg hupper p m hm
  have hmPow : 0 ≤ m ^ h.β / h.C :=
    div_nonneg (Real.rpow_nonneg hm.le _) h.hC.le
  have hu := hupper m hm
  rw [neg_div] at hu
  linarith only [hreg p m hm, hu, hmPow]

/-- Infimal convolution preserves monotonicity in positive mass. The original
Hamiltonian's arbitrary value at zero never enters this proof. -/
theorem Hdelta_antitone_mass_of_antitone
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (hanti : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p, AntitoneOn (H x p) (Set.Ioi (0 : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p, AntitoneOn (Hdelta h ε x p) (Set.Ioi (0 : ℝ)) := by
  filter_upwards [hanti, h.lower] with x hx hLower p
  intro m₁ hm₁ m₂ hm₂ hle
  apply ciInf_mono (paper_bddBelow_penalty h hε (fun r => hLower r m₂ hm₂))
  intro q
  exact add_le_add (hx (p - q) hm₁ hm₂ hle) le_rfl

/-- The finite boundary trace of Hε: the supremum of its positive-mass slices.
This is deliberately different from evaluating the raw infimum at mass zero. -/
def HdeltaBoundary (h : HypothesisWeakGrowth (d := d) H DpH)
    (ε : ℝ) (x p : Fin d → ℝ) : ℝ :=
  sSup ((Hdelta h ε x p) '' Set.Ioi (0 : ℝ))

/-- Each positive-scale regularization has a finite real right limit, even when
the original Hamiltonian has infinite boundary values at some momenta. -/
theorem Hdelta_tendsto_boundary_of_antitone
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (hanti : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p, AntitoneOn (H x p) (Set.Ioi (0 : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p,
      Tendsto (Hdelta h ε x p) (𝓝[>] (0 : ℝ)) (𝓝 (HdeltaBoundary h ε x p)) := by
  filter_upwards [Hdelta_antitone_mass_of_antitone h hanti hε,
    Hdelta_le_boundary_envelope h hε] with x hx hupper p
  apply (hx p).tendsto_nhdsGT
  refine ⟨h.C + (1 / ε) * K h p, ?_⟩
  rintro _ ⟨m, hm, rfl⟩
  exact hupper p m hm

/-- The boundary trace inherits the finite envelope, with no base-H boundary premise. -/
theorem HdeltaBoundary_le_envelope
    (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p,
      HdeltaBoundary h ε x p ≤ h.C + (1 / ε) * K h p := by
  filter_upwards [Hdelta_le_boundary_envelope h hε] with x hx p
  apply csSup_le
  · exact ⟨Hdelta h ε x p 1, 1, by norm_num, rfl⟩
  · rintro _ ⟨m, hm, rfl⟩
    exact hx p m hm

/-- Specialization of the finite right-limit theorem to Lasry--Lions monotonicity. -/
theorem Hdelta_tendsto_boundary
    (hmon : HypothesisMonotone (d := d) H DpH)
    (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p,
      Tendsto (Hdelta h ε x p) (𝓝[>] (0 : ℝ)) (𝓝 (HdeltaBoundary h ε x p)) :=
  Hdelta_tendsto_boundary_of_antitone h (antitone_in_m hmon) hε

/-- The extended Hamiltonian of the positive-mass regularization has finite
boundary values. This does not identify them with raw Hdelta at zero. -/
theorem Hdelta_Hext_zero_eq_boundary
    (hmon : HypothesisMonotone (d := d) H DpH)
    (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p,
      Hext (Hdelta h ε) x p 0 = ((HdeltaBoundary h ε x p : ℝ) : WithTop ℝ) := by
  filter_upwards [Hdelta_tendsto_boundary hmon h hε] with x hx p
  have ht : Tendsto (fun m : ℝ => ((Hdelta h ε x p m : ℝ) : WithTop ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 ((HdeltaBoundary h ε x p : ℝ) : WithTop ℝ)) :=
    WithTop.continuous_coe.tendsto _ |>.comp (hx p)
  exact tendsto_nhds_unique (tendsto_Hext_zero_of_exists ⟨_, ht⟩) ht

/-- The corrected regularized Hamiltonian on the closed nonnegative cone.
Its zero-mass value is constructed from positive masses, not from raw H at zero.
Negative masses use the harmless constant zero. -/
def HdeltaPaper (h : HypothesisWeakGrowth (d := d) H DpH)
    (ε : ℝ) (x p : Fin d → ℝ) (m : ℝ) : ℝ :=
  if 0 ≤ m then Hamiltonian.Paper.finiteExtension (Hdelta h ε) x p m else 0

@[simp] theorem HdeltaPaper_of_pos
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (ε : ℝ) (x p : Fin d → ℝ) {m : ℝ} (hm : 0 < m) :
    HdeltaPaper h ε x p m = Hdelta h ε x p m := by
  simp only [HdeltaPaper, if_pos hm.le, Hamiltonian.Paper.finiteExtension_of_pos _ _ _ hm]

@[simp] theorem HdeltaPaper_of_neg
    (h : HypothesisWeakGrowth (d := d) H DpH)
    (ε : ℝ) (x p : Fin d → ℝ) {m : ℝ} (hm : m < 0) :
    HdeltaPaper h ε x p m = 0 := if_neg (not_le.mpr hm)

/-- The canonical zero-mass value is the finite trace proved above. -/
theorem HdeltaPaper_zero_eq_boundary
    (hmon : HypothesisMonotone (d := d) H DpH)
    (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p,
      HdeltaPaper h ε x p 0 = HdeltaBoundary h ε x p := by
  filter_upwards [Hdelta_tendsto_boundary hmon h hε] with x hx p
  simp only [HdeltaPaper, le_refl, if_true, Hamiltonian.Paper.finiteExtension_zero]
  exact Hamiltonian.Paper.boundaryTrace_eq_of_tendsto (hx p)

/-- Right continuity is proved for the regularized extension itself without
an original-H finite-boundary premise. -/
theorem HdeltaPaper_rc0
    (hmon : HypothesisMonotone (d := d) H DpH)
    (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p,
      Tendsto (HdeltaPaper h ε x p) (𝓝[>] (0 : ℝ))
        (𝓝 (HdeltaPaper h ε x p 0)) := by
  filter_upwards [Hdelta_tendsto_boundary hmon h hε,
    HdeltaPaper_zero_eq_boundary hmon h hε] with x hx hzero p
  rw [hzero p]
  apply (hx p).congr'
  filter_upwards [self_mem_nhdsWithin] with m hm
  exact (HdeltaPaper_of_pos h ε x p hm).symm

/-- Boundary-limit existence belongs to each regularization, not to raw H. -/
theorem HdeltaPaper_hat0
    (hmon : HypothesisMonotone (d := d) H DpH)
    (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) : HypothesisHat0 (HdeltaPaper h ε) := by
  constructor
  filter_upwards [HdeltaPaper_rc0 hmon h hε] with x hx p
  exact ⟨↑(HdeltaPaper h ε x p 0),
    WithTop.continuous_coe.continuousAt.tendsto.comp (hx p)⟩

/-- Boundary agreement is a theorem for the chosen regularized representative. -/
theorem HdeltaPaper_agree
    (hmon : HypothesisMonotone (d := d) H DpH)
    (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) : H_zero_eq_Hext (HdeltaPaper h ε) := by
  filter_upwards [HdeltaPaper_rc0 hmon h hε] with x hx p
  exact (Hamiltonian.Paper.Hext_zero_eq_of_tendsto (hx p)).symm

/-- The old finite-extension bundle can be produced for Hε internally. It is
not required for the original Hamiltonian. -/
theorem HdeltaPaper_zeroExtension
    (hmon : HypothesisMonotone (d := d) H DpH)
    (h : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ} (hε : 0 < ε) : HypothesisHZeroExtension (HdeltaPaper h ε) :=
  ⟨HdeltaPaper_hat0 hmon h hε, HdeltaPaper_agree hmon h hε⟩

end StationaryMFG.InfimalConvolution
