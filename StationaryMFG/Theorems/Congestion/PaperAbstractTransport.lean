module

public import StationaryMFG.Theorems.Congestion.PaperTestPairBase
public import StationaryMFG.Theorems.Congestion.StrongIsStrong

@[expose] public section

/-! # Transport from the periodic variational inequality with a general flux

These proofs preserve the supplied continuous flux through both limit passages.
The boundary flux need not vanish at arbitrary momenta.
-/

noncomputable section
namespace StationaryMFG.Congestion

open MeasureTheory Filter Topology
open StationaryMFG.Periodic
  (IsPeriodic UnitCube MemLpPer MemSobolevPer SmoothPeriodic)
open StationaryMFG.Hamiltonian
  (HypothesisMonotone CongestionGrowthCore)
open StationaryMFG.Solutions.Strong (mDpH_Integrable)
open StationaryMFG.Solutions.MFG
  (hasWeakDerivPer_add mfgOperatorPair vecAbsPowMinusTwo absPowMinusTwo vecSignedRpow signedRpow
    continuous_vecSignedRpow continuous_signedRpow)
open scoped ENNReal
open scoped StationaryMFG.Hamiltonian

variable {d : ℕ}

/-! ## C1 — gradient-perturbed truncated test pair + abstract-VI transport bridge

This is the transport-side analogue of the witness lemmas
`congestion_VI_h_VI_at_mdelta_at_witness` (StrongIsStrong.lean), but sourced
from the abstract periodic limit weak VI `habs` (`mfgOperatorPair`) instead of
the Browder–Minty Banach witness `hVI`. The witness lemmas test against the
GRADIENT-perturbed test pair `(max(m,δ), u+tφ, Du+t∇φ)`; the scalar-only
`h_DCT_of_abstractPeriodicVI_aesm` does not cover this. Paper
`eq:congest.transport` (line 1538), per-`(δ,t)` first-variation inequality.
No new oracle, no `0<m` / `essinf m > 0` crutch (the truncation
`max(m,δ) ≥ δ > 0` supplies all positivity), no Banach/cone data.
-/

open StationaryMFG.Hamiltonian (HypothesisMonotone CongestionGrowthCore) in
/-- **Gradient-perturbed truncated admissible test pair at
`ρ = max(m,δ)`, value `u+tφ`, gradient `Du+t∇φ`** (paper
`eq:congest.transport`, line 1538; the transport / continuity-equation analogue
of `congestionLimitVITestPair_of_muAuxDelta`).

Assembles the 9-field `CongestionLimitVITestPair` at primal density
`μ := max(m x) δ`, value `υ := u + tφ`, gradient `Dυ i := Du i + t·∂ᵢφ`, with
all exponents pinned to `hcong.*`. Built via `mdelta_admissibility` at the
smooth test `ψ := t • φ` (so `(ψ:func) = tφ`, `∂ᵢψ = t·∂ᵢφ`); the ratio
integrability `hRatio_memLp` for the perturbed numerator is
`congestion_VI_perturbed_ratio_memLp`. The lower bound `μ_lower` is the
immediate `⟨δ, hδ, le_max_right⟩` — no `0 < m` crutch. -/
noncomputable def transportTruncTestPair
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    {m u : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hmPer : IsPeriodic m)
    (huPer : IsPeriodic u)
    (hDuPer : ∀ i, IsPeriodic (Du i))
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) m)
    (hm_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hu_Sob : MemSobolevPer (d := d)
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) u)
    (hu_L1 : MemLpPer (d := d) 1 u)
    (hu_memGamma : MemLpPer (d := d)
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) u)
    (hDu_weak : ∀ i, Periodic.HasWeakDerivPer (d := d) i u (Du i))
    (hDu_memGamma : ∀ i,
      MemLpPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Du i))
    (hQuot_m_mem :
      MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (fun x : Fin d → ℝ =>
          ‖fun i => Du i x‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) /
            (m x ^ hcong.τ + 1)))
    (φ : Periodic.SmoothPeriodic d) (t : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    CongestionLimitVITestPair (d := d)
      (ENNReal.ofReal (hcong.β + 1))
      (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
      hcong.α hcong.β hcong.τ := by
  classical
  haveI : Fact (1 ≤ ENNReal.ofReal (hcong.β + 1)) := by
    refine ⟨?_⟩
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from (ENNReal.ofReal_one).symm]
    exact ENNReal.ofReal_le_ofReal (by linarith [hcong.hβ.le])
  -- The smooth test `ψ := t • φ` and its gradient witness `Dψ i := t·∂ᵢφ`.
  set ψ : Periodic.SmoothPeriodic d := t • φ with hψdef
  have hψ_coe : (ψ : (Fin d → ℝ) → ℝ)
      = fun x => t * (φ : (Fin d → ℝ) → ℝ) x := by
    rw [hψdef]; funext x; rw [Periodic.SmoothPeriodic.coe_smul]; rfl
  set Dψ : Fin d → (Fin d → ℝ) → ℝ :=
    fun i => (Periodic.SmoothPeriodic.partialDeriv i ψ : (Fin d → ℝ) → ℝ)
    with hDψdef
  have hDψ_coe : ∀ i, Dψ i
      = fun x => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
          (Fin d → ℝ) → ℝ) x := by
    intro i
    rw [hDψdef]
    simp only [Periodic.SmoothPeriodic.coe_partialDeriv]
    funext x
    have hψφ : (ψ : (Fin d → ℝ) → ℝ) = t • (φ : (Fin d → ℝ) → ℝ) := by
      rw [hψ_coe]; funext y; simp [Pi.smul_apply]
    rw [hψφ, fderiv_const_smul (φ.smooth.differentiable (by simp) |>.differentiableAt)]
    simp [Pi.smul_apply]
  -- Hypotheses for `mdelta_admissibility`.
  have hτ : 0 ≤ hcong.τ := hcong.hτ.1
  have hαt : 1 ≤ hcong.α * (1 + hcong.τ / hcong.β) := by
    have hfrac : (0 : ℝ) ≤ hcong.τ / hcong.β := div_nonneg hτ hcong.hβ.le
    have h1 : (1 : ℝ) ≤ 1 + hcong.τ / hcong.β := by linarith
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ hcong.α * (1 + hcong.τ / hcong.β) :=
          mul_le_mul hcong.hα.le h1 (by norm_num)
            (le_trans (by norm_num) hcong.hα.le)
  have hDψ_weak : ∀ i,
      Periodic.HasWeakDerivPer (d := d) i ((ψ : (Fin d → ℝ) → ℝ)) (Dψ i) := by
    intro i; rw [hDψdef]
    exact Periodic.HasWeakDerivPer.of_contDiff i ψ
  -- `‖Dψ‖^{αt} ∈ L^{β̄'}` (smooth ⇒ continuous bounded on the finite cube).
  have hDψ_Lp :
      MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (fun x : Fin d → ℝ =>
          ‖fun i => Dψ i x‖ ^ (hcong.α * (1 + hcong.τ / hcong.β))) := by
    set αt : ℝ := hcong.α * (1 + hcong.τ / hcong.β) with hαtdef
    have hαt_nn : 0 ≤ αt := le_trans (by norm_num) hαt
    have hcont : ∀ i, Continuous (Dψ i) := by
      intro i; rw [hDψdef]
      exact (Periodic.SmoothPeriodic.partialDeriv i ψ).smooth.continuous
    have hnorm_cont : Continuous (fun x : Fin d → ℝ => ‖fun i => Dψ i x‖) :=
      (continuous_pi hcont).norm
    have hcompact :
        IsCompact (Set.pi Set.univ (fun _ : Fin d => Set.Icc (0 : ℝ) 1)) :=
      isCompact_univ_pi (fun _ => isCompact_Icc)
    obtain ⟨C, hC⟩ := hcompact.bddAbove_image hnorm_cont.continuousOn
    have hpow_cont : Continuous (fun x : Fin d → ℝ =>
        ‖fun i => Dψ i x‖ ^ αt) :=
      hnorm_cont.rpow_const (fun _ => Or.inr hαt_nn)
    refine Periodic.MemLp.toMemLpPer ?_
    refine MeasureTheory.MemLp.of_bound hpow_cont.aestronglyMeasurable
      (C ^ αt) ?_
    refine (ae_restrict_iff' Periodic.measurableSet_unitCube).2
      (Filter.Eventually.of_forall ?_)
    intro x hx
    have hx_cube : x ∈ Set.pi Set.univ (fun _ : Fin d => Set.Icc (0 : ℝ) 1) := by
      intro j _
      exact Set.Ico_subset_Icc_self (hx j (Set.mem_univ _))
    have hnorm_le : ‖fun i => Dψ i x‖ ≤ C := hC ⟨x, hx_cube, rfl⟩
    have hnorm_nn : 0 ≤ ‖fun i => Dψ i x‖ := norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hnorm_nn _)]
    exact Real.rpow_le_rpow hnorm_nn hnorm_le hαt_nn
  -- `congestionDomainK` membership of `(max(m,δ), u+tφ)` via `mdelta_admissibility`.
  have hdom :
      ((fun x => max (m x) δ),
          (fun x => u x + (ψ : (Fin d → ℝ) → ℝ) x)) ∈
        congestionDomainK (d := d)
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
          hcong.α hcong.β hcong.τ :=
    mdelta_admissibility (d := d)
      (m := m) (u := u) (Du := Du)
      ψ Dψ hδ hτ hαt hm_mem hm_nn hu_Sob hu_L1 hDu_weak
      hDψ_weak hQuot_m_mem hDψ_Lp
  -- Extract `μLp`, `μ_lower`.
  have hρLp : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1))
      (fun x => max (m x) δ) := hdom.1
  -- Periodicity of `ρ = max(m, δ)`.
  have hρPer : IsPeriodic (fun x => max (m x) δ) := by
    intro κ x; simp only []; rw [hmPer κ x]
  -- Periodicity of `υ = u + tφ`.
  have hυPer : IsPeriodic (fun x => u x + t * (φ : (Fin d → ℝ) → ℝ) x) := by
    intro κ x; simp only []
    rw [huPer κ x, (φ.periodic) κ x]
  -- Periodicity of each gradient `Dυ i = Du i + t·∂ᵢφ`.
  have hDυPer : ∀ i, IsPeriodic
      (fun x => Du i x + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
          (Fin d → ℝ) → ℝ) x) := by
    intro i κ x; simp only []
    rw [hDuPer i κ x, (Periodic.SmoothPeriodic.partialDeriv i φ).periodic κ x]
  -- Sobolev regularity of `υ = u + tφ` with witness `Du + t·∂ᵢφ`.
  have hυSob : MemSobolevPer (d := d)
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
      (fun x => u x + t * (φ : (Fin d → ℝ) → ℝ) x) := by
    refine ⟨?_, ⟨fun i x => Du i x + Dψ i x, ?_⟩⟩
    · have hψ_γ : MemLpPer (d := d)
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
          ((ψ : (Fin d → ℝ) → ℝ)) :=
        (Periodic.MemSobolevPer.of_smoothPeriodic _ ψ).1
      have hsum := hu_memGamma.add hψ_γ
      have heq : (u + (fun x => (ψ : (Fin d → ℝ) → ℝ) x))
          = (fun x => u x + t * (φ : (Fin d → ℝ) → ℝ) x) := by
        funext x; rw [Pi.add_apply, hψ_coe]
      rwa [heq] at hsum
    · intro i
      have hψ_L1 : MemLpPer (d := d) 1 ((ψ : (Fin d → ℝ) → ℝ)) :=
        (Periodic.MemSobolevPer.of_smoothPeriodic (1 : ℝ≥0∞) ψ).1
      have hbase := hasWeakDerivPer_add (i := i) hu_L1 hψ_L1
        (hDu_weak i) (hDψ_weak i)
      have heq : (u + (ψ : (Fin d → ℝ) → ℝ))
          = (fun x => u x + t * (φ : (Fin d → ℝ) → ℝ) x) := by
        funext x; rw [Pi.add_apply, hψ_coe]
      have heqd : (Du i + Dψ i)
          = (fun x => Du i x + Dψ i x) := by funext x; rfl
      rw [heq, heqd] at hbase
      exact hbase
  -- The perturbed-ratio `L^{β̄'}` membership.
  have hRatio : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
      (fun x =>
        (‖fun i => Du i x + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
              (Fin d → ℝ) → ℝ) x‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)))
          / (max (m x) δ ^ hcong.τ + 1)) :=
    congestion_VI_perturbed_ratio_memLp hcong hm_mem hm_nn hDu_memGamma
      hQuot_m_mem φ hδ t
  exact
    { μ := fun x => max (m x) δ
      υ := fun x => u x + t * (φ : (Fin d → ℝ) → ℝ) x
      Dυ := fun i x => Du i x
        + t * (Periodic.SmoothPeriodic.partialDeriv i φ : (Fin d → ℝ) → ℝ) x
      hμPer := hρPer
      hυPer := hυPer
      hDυPer := hDυPer
      μLp := hρLp
      υSob := hυSob
      μ_lower := ⟨δ, hδ, Filter.Eventually.of_forall (fun x => le_max_right _ _)⟩
      hDυ_weak := by
        intro i
        have hψ_L1 : MemLpPer (d := d) 1 ((ψ : (Fin d → ℝ) → ℝ)) :=
          (Periodic.MemSobolevPer.of_smoothPeriodic (1 : ℝ≥0∞) ψ).1
        have hbase := hasWeakDerivPer_add (i := i) hu_L1 hψ_L1
          (hDu_weak i) (hDψ_weak i)
        have heqv : (u + (ψ : (Fin d → ℝ) → ℝ))
            = (fun x => u x + t * (φ : (Fin d → ℝ) → ℝ) x) := by
          funext x; rw [Pi.add_apply, hψ_coe]
        have heqd : (Du i + Dψ i)
            = (fun x => Du i x + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                (Fin d → ℝ) → ℝ) x) := by
          funext x; rw [Pi.add_apply, hDψ_coe]
        rw [heqv, heqd] at hbase
        exact hbase
      hRatio_memLp := hRatio
      hDυ_memGamma := by
        intro i
        have hDψγ : MemLpPer (d := d)
            (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Dψ i) := by
          rw [hDψdef]
          exact (Periodic.MemSobolevPer.of_smoothPeriodic _
            (Periodic.SmoothPeriodic.partialDeriv i ψ)).1
        have hsum := (hDu_memGamma i).add hDψγ
        have heq : ((Du i) + Dψ i)
            = (fun x => Du i x
                + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                    (Fin d → ℝ) → ℝ) x) := by
          funext x; rw [Pi.add_apply, hDψ_coe]
        rwa [heq] at hsum }

open StationaryMFG.Hamiltonian (HypothesisMonotone CongestionGrowthCore) in
open scoped StationaryMFG.Hamiltonian in
/-- **Abstract-VI → per-`(δ,t)` transport first-variation inequality** (paper
`eq:congest.transport`, line 1538; C1 of the transport drain).

The abstract-VI analogue of the witness lemma
`congestion_VI_h_VI_at_mdelta_at_witness`: from the abstract periodic limit weak
VI `habs` (`mfgOperatorPair`-shaped) evaluated at `transportTruncTestPair`, it
produces the exact lower-bounded variational inequality that
`transport_mdelta_limit_of_L1` consumes as its `h_VI_at_mdelta n` hypothesis
(test direction `(t·φ, t·∇φ)`, `γBar = α(β+1)/β`, `C = hcong.C`, `β = hcong.β`,
and the regularization parameter taken to its limit value `ε = 0`, so the
Gateaux integral vanishes). No Banach witness, no cone data, no `0 < m` rider. -/
theorem transport_h_VI_at_mdelta_of_abstractPeriodicVI
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) m)
    (hm_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hu_memGamma : MemLpPer (d := d)
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) u)
    (hDu_memGamma : ∀ i,
      MemLpPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Du i))
    (hQuot_m_mem :
      MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (fun x : Fin d → ℝ =>
          ‖fun i => Du i x‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) /
            (m x ^ hcong.τ + 1)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    -- The abstract limit weak VI over periodic admissible test pairs.
    (habs :
      ∀ (T : CongestionLimitVITestPair (d := d)
              (ENNReal.ofReal (hcong.β + 1))
              (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
              (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
              hcong.α hcong.β hcong.τ),
        0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH)
              T.Dυ T.μ T.υ
              (fun i x => T.Dυ i x - Du i x)
              (T.μ - m) (T.υ - u))
    (T : CongestionLimitVITestPair (d := d)
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
          hcong.α hcong.β hcong.τ)
    -- The test pair is the gradient-perturbed truncation at `(δ, t)`.
    (φ : Periodic.SmoothPeriodic d) {δ : ℝ} (hδ : 0 < δ) {t : ℝ} (ht : 0 < t)
    (hTμ : T.μ = fun x => max (m x) δ)
    (hTυ : T.υ = fun x => u x + t * (φ : (Fin d → ℝ) → ℝ) x)
    (hTDυ : T.Dυ = fun i x => Du i x
      + t * (Periodic.SmoothPeriodic.partialDeriv i φ : (Fin d → ℝ) → ℝ) x) :
    (∫ x in UnitCube d,
        (u x + t * (φ : (Fin d → ℝ) → ℝ) x
            - hcong.C * ((max (m x) δ) ^ hcong.β + 1) - V x)
          * (max (m x) δ - m x)
        ∂(volume : Measure (Fin d → ℝ)))
    ≤
    (∫ x in UnitCube d,
        (max (m x) δ - 1) * (t * (φ : (Fin d → ℝ) → ℝ) x)
          + max (m x) δ
            * (DpH x
                (fun i => Du i x
                  + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                      (Fin d → ℝ) → ℝ) x)
                (max (m x) δ)
                ⬝ (fun i => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                      (Fin d → ℝ) → ℝ) x))
        ∂(volume : Measure (Fin d → ℝ)))
    +
    (∫ x in UnitCube d,
        (0 : ℝ) * vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
            (fun i => Du i x
              + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                  (Fin d → ℝ) → ℝ) x)
          * ((fun i => Du i x
                + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                    (Fin d → ℝ) → ℝ) x)
              ⬝ (fun i => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                  (Fin d → ℝ) → ℝ) x))
        + (0 : ℝ) * absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
            (u x + t * (φ : (Fin d → ℝ) → ℝ) x)
          * ((u x + t * (φ : (Fin d → ℝ) → ℝ) x)
              * (t * (φ : (Fin d → ℝ) → ℝ) x))
        ∂(volume : Measure (Fin d → ℝ))) := by
  classical
  -- The abstract VI at `T`, with the test pair's fields substituted.
  have hVI := habs T
  rw [hTμ, hTυ, hTDυ] at hVI
  -- Unfold `mfgOperatorPair` and collapse the gradient/value test directions
  -- `T.Dυ − Du = t·∂φ`, `T.υ − u = t·φ`, `T.μ − m = max(m,δ) − m`.
  have hcollapse :
      mfgOperatorPair (V := V) (H := H) (DpH := DpH)
          (fun i x => Du i x
            + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                (Fin d → ℝ) → ℝ) x)
          (fun x => max (m x) δ)
          (fun x => u x + t * (φ : (Fin d → ℝ) → ℝ) x)
          (fun i x =>
            (Du i x + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                  (Fin d → ℝ) → ℝ) x) - Du i x)
          ((fun x => max (m x) δ) - m)
          ((fun x => u x + t * (φ : (Fin d → ℝ) → ℝ) x) - u)
        = ∫ x in UnitCube d,
            (-(u x + t * (φ : (Fin d → ℝ) → ℝ) x)
                - H x (fun i => Du i x
                    + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                        (Fin d → ℝ) → ℝ) x) (max (m x) δ) + V x)
              * (max (m x) δ - m x)
              + max (m x) δ
                  * (DpH x (fun i => Du i x
                        + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                            (Fin d → ℝ) → ℝ) x) (max (m x) δ)
                      ⬝ (fun i => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                            (Fin d → ℝ) → ℝ) x))
              + (max (m x) δ - 1) * (t * (φ : (Fin d → ℝ) → ℝ) x)
            ∂(volume : Measure (Fin d → ℝ)) := by
    unfold mfgOperatorPair
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x
    simp only [Pi.sub_apply]
    have hdot : (fun i => (Du i x
          + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
              (Fin d → ℝ) → ℝ) x) - Du i x)
        = (fun i => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
            (Fin d → ℝ) → ℝ) x) := by
      funext i; ring
    rw [hdot]; ring
  rw [hcollapse] at hVI
  -- Build the raw `1/t`-scaled first-variation inequality with `ε = 0`.
  have h_raw : (0 : ℝ) ≤ (1 / t) *
      ((∫ x in UnitCube d,
          (-(u x + t * (φ : (Fin d → ℝ) → ℝ) x)
              - H x (fun i => Du i x
                  + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                      (Fin d → ℝ) → ℝ) x) (max (m x) δ) + V x)
            * (max (m x) δ - m x)
            + max (m x) δ
                * (DpH x (fun i => Du i x
                      + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                          (Fin d → ℝ) → ℝ) x) (max (m x) δ)
                    ⬝ (fun i => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                          (Fin d → ℝ) → ℝ) x))
            + (max (m x) δ - 1) * (t * (φ : (Fin d → ℝ) → ℝ) x)
          ∂(volume : Measure (Fin d → ℝ)))
        + (0 : ℝ) * (∫ x in UnitCube d,
              vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
                  (fun i => Du i x
                    + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                        (Fin d → ℝ) → ℝ) x)
                * ((fun i => Du i x
                      + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                          (Fin d → ℝ) → ℝ) x)
                    ⬝ (fun i => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                          (Fin d → ℝ) → ℝ) x))
              + absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
                  (u x + t * (φ : (Fin d → ℝ) → ℝ) x)
                * ((u x + t * (φ : (Fin d → ℝ) → ℝ) x)
                    * (t * (φ : (Fin d → ℝ) → ℝ) x))
            ∂(volume : Measure (Fin d → ℝ)))) := by
    have hinv_pos : 0 < 1 / t := by positivity
    have := mul_nonneg hinv_pos.le hVI
    simpa using this
  -- The three connector-integrand integrability certificates.
  obtain ⟨hLHSc_int, hRHSc_int, hMterm_int⟩ :=
    firstvar_integrands_integrable hmon hcong hm_mem hm_nn hu_memGamma hV
      hDu_memGamma φ hδ (t := t)
      (congestion_VI_perturbed_ratio_memLp hcong hm_mem hm_nn hDu_memGamma
        hQuot_m_mem φ hδ t)
  -- Convert to the `h_VI_at_mdelta` shape via the shared algebra helper.
  exact congestion_VI_at_mdelta (ε := 0) hcong φ hδ ht h_raw
    hLHSc_int hRHSc_int hMterm_int

/-! ## C2 — transport `h_iota` from the abstract periodic limit weak VI

The δ→0 dominated-convergence limit + t→0±/squeeze landing the smooth-test
transport identity `∫(m−1)φ + J(x,Du,m)·∇φ = 0` (paper `eq:congest.transport`,
line 1538) from the abstract limit periodic-VI `habs` alone, with **no Banach
witness / cone data** and no `0 < m` rider.

This is the abstract-VI sibling of `congestion_transport_at_witness`
(StrongIsStrong): the `∀ t` direction inequality `h_dir` is produced exactly as
`congestion_VI_hdir_at_witness` does, except the per-`(δ, t)` variational
inequality is sourced from `transport_h_VI_at_mdelta_of_abstractPeriodicVI`
(LimitPassage, C1) at the `transportTruncTestPair` density (regularization
parameter taken to its limit value `ε = 0`, so the Gateaux integral vanishes),
not from the Browder–Minty cone VI. The δ→0 limit engine
(`transport_mdelta_limit_of_L1_J`), the `L¹`-convergence certificates, and the
t→0±/squeeze (`iota_transport_smooth_assembled_J`) are reused verbatim. -/

open StationaryMFG.Hamiltonian (HypothesisMonotone CongestionGrowthCore) in
/-- **C2 (direction inequality): the per-`t` transport `ι(t) ≥ 0` from the
abstract periodic limit weak VI.** Abstract-VI analogue of
`congestion_VI_hdir_at_witness`: produces, for every real scale `t`, the
lower-bounded first-variation inequality at the smooth test `t·φ`, sourced from
`habs` through C1 + the δ→0 DCT engine. No Banach witness, no `0 < m`. -/
theorem transport_hdir_of_abstractPeriodicVI
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) m)
    (hm_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hu_memGamma : MemLpPer (d := d)
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) u)
    (hDu_memGamma : ∀ i,
      MemLpPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Du i))
    (hQuot_m_mem :
      MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (fun x : Fin d → ℝ =>
          ‖fun i => Du i x‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) /
            (m x ^ hcong.τ + 1)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    -- periodicity / Sobolev / weak-derivative data (for `transportTruncTestPair`)
    (hmPer : IsPeriodic m)
    (huPer : IsPeriodic u)
    (hDuPer : ∀ i, IsPeriodic (Du i))
    (hu_Sob : MemSobolevPer (d := d)
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) u)
    (hu_L1 : MemLpPer (d := d) 1 u)
    (hDu_weak : ∀ i, Periodic.HasWeakDerivPer (d := d) i u (Du i))
    -- the abstract limit weak VI over periodic admissible test pairs
    (habs :
      ∀ (T : CongestionLimitVITestPair (d := d)
              (ENNReal.ofReal (hcong.β + 1))
              (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
              (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
              hcong.α hcong.β hcong.τ),
        0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH)
              T.Dυ T.μ T.υ
              (fun i x => T.Dυ i x - Du i x)
              (T.μ - m) (T.υ - u))
    (φ : Periodic.SmoothPeriodic d) :
    ∀ t : ℝ,
      0 ≤
        (∫ x in UnitCube d,
            (m x - 1) * (t * (φ : (Fin d → ℝ) → ℝ) x)
              + (J x
                  (fun i => Du i x
                    + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                        (Fin d → ℝ) → ℝ) x)
                  (m x)
                ⬝ (fun i => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                    (Fin d → ℝ) → ℝ) x))
            ∂(volume : Measure (Fin d → ℝ)))
        +
        (∫ x in UnitCube d,
            (0 : ℝ) * vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
                (fun i => Du i x
                  + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                      (Fin d → ℝ) → ℝ) x)
              * ((fun i => Du i x
                    + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                        (Fin d → ℝ) → ℝ) x)
                  ⬝ (fun i => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                      (Fin d → ℝ) → ℝ) x))
            + (0 : ℝ) * absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
                (u x + t * (φ : (Fin d → ℝ) → ℝ) x)
              * ((u x + t * (φ : (Fin d → ℝ) → ℝ) x)
                  * (t * (φ : (Fin d → ℝ) → ℝ) x))
            ∂(volume : Measure (Fin d → ℝ))) := by
  classical
  -- `δSeq n = 1/(n+1)`.
  set δSeq : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ) with hδSeqdef
  have hδ_pos : ∀ n, 0 < δSeq n := by
    intro n; rw [hδSeqdef]
    exact div_pos one_pos (by positivity)
  have hδ_le_one : ∀ n, δSeq n ≤ 1 := by
    intro n; rw [hδSeqdef]
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hδ_tendsto : Filter.Tendsto δSeq Filter.atTop (nhds (0 : ℝ)) := by
    rw [hδSeqdef]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  -- The per-`(s, ψ)` connector conclusion at the positive scale `s`.
  have h_dir_at : ∀ (s : ℝ), 0 < s → ∀ (ψ : Periodic.SmoothPeriodic d),
      0 ≤
        (∫ x in UnitCube d,
            (m x - 1) * (s * (ψ : (Fin d → ℝ) → ℝ) x)
              + (J x
                  (fun i => Du i x
                    + s * (Periodic.SmoothPeriodic.partialDeriv i ψ :
                        (Fin d → ℝ) → ℝ) x)
                  (m x)
                ⬝ (fun i => s * (Periodic.SmoothPeriodic.partialDeriv i ψ :
                    (Fin d → ℝ) → ℝ) x))
            ∂(volume : Measure (Fin d → ℝ)))
        +
        (∫ x in UnitCube d,
            (0 : ℝ) * vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
                (fun i => Du i x
                  + s * (Periodic.SmoothPeriodic.partialDeriv i ψ :
                      (Fin d → ℝ) → ℝ) x)
              * ((fun i => Du i x
                    + s * (Periodic.SmoothPeriodic.partialDeriv i ψ :
                        (Fin d → ℝ) → ℝ) x)
                  ⬝ (fun i => s * (Periodic.SmoothPeriodic.partialDeriv i ψ :
                      (Fin d → ℝ) → ℝ) x))
            + (0 : ℝ) * absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
                (u x + s * (ψ : (Fin d → ℝ) → ℝ) x)
              * ((u x + s * (ψ : (Fin d → ℝ) → ℝ) x)
                  * (s * (ψ : (Fin d → ℝ) → ℝ) x))
            ∂(volume : Measure (Fin d → ℝ))) := by
    intro s hs ψ
    set φc : (Fin d → ℝ) → ℝ := fun x => s * (ψ : (Fin d → ℝ) → ℝ) x with hφc
    set Dφc : Fin d → (Fin d → ℝ) → ℝ :=
      fun i x => s * (Periodic.SmoothPeriodic.partialDeriv i ψ :
        (Fin d → ℝ) → ℝ) x with hDφc
    set Du' : Fin d → (Fin d → ℝ) → ℝ :=
      fun i x => Du i x + Dφc i x with hDu'def
    -- Smooth-function memberships: `φc ∈ L^{β̄'}`, `Dφc ∈ L^{γ̄}`.
    have hφc_betaP : MemLpPer (d := d)
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) φc := by
      have hraw : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
          ((ψ : (Fin d → ℝ) → ℝ)) :=
        (Periodic.MemSobolevPer.of_smoothPeriodic _ ψ).1
      have := hraw.const_smul (𝕜 := ℝ) s
      have heq : (s • (ψ : (Fin d → ℝ) → ℝ)) = φc := by
        funext x; simp [hφc, Pi.smul_apply, smul_eq_mul]
      rwa [heq] at this
    have hDφc_gamma : ∀ i, MemLpPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Dφc i) := by
      intro i
      have hraw : MemLpPer (d := d)
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
          ((Periodic.SmoothPeriodic.partialDeriv i ψ : (Fin d → ℝ) → ℝ)) :=
        (Periodic.MemSobolevPer.of_smoothPeriodic _
          (Periodic.SmoothPeriodic.partialDeriv i ψ)).1
      have := hraw.const_smul (𝕜 := ℝ) s
      have heq : (s • (Periodic.SmoothPeriodic.partialDeriv i ψ :
          (Fin d → ℝ) → ℝ)) = Dφc i := by
        funext x; simp [hDφc, Pi.smul_apply, smul_eq_mul]
      rwa [heq] at this
    have hDu'_gamma : ∀ i, MemLpPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Du' i) := by
      intro i
      have := (hDu_memGamma i).add (hDφc_gamma i)
      have heq : (Du i + Dφc i) = Du' i := by funext x; simp [hDu'def, Pi.add_apply]
      rwa [heq] at this
    have hm_aem : AEMeasurable m (volume.restrict (UnitCube d)) :=
      aestronglyMeasurable_iff_aemeasurable.mp hm_mem.aestronglyMeasurable
    have hDu'_aem : AEMeasurable (fun x => (fun i => Du' i x))
        (volume.restrict (UnitCube d)) := by
      rw [aemeasurable_pi_iff]; intro i
      exact aestronglyMeasurable_iff_aemeasurable.mp (hDu'_gamma i).aestronglyMeasurable
    -- The `J`-flux dominator at the perturbed point (used at the base scale `t=0`).
    obtain ⟨gJ', hgJ'_int, hgJ'_bound⟩ :=
      iota_FA_uniform_dominator_J (H := H) hcong hm_mem hm_nn hDu'_gamma
        φc Dφc hφc_betaP hDφc_gamma
        (fun t => fun x => (m x - 1) * φc x
          + (J x (fun i => Du' i x + t * Dφc i x) (m x)
              ⬝ (fun i => Dφc i x)))
        (fun t => rfl)
    -- Discharge 1: `hLHSaLim_int` (the `J`-limit integrand integrability).
    have hLHSaLim_int : Integrable (fun x =>
        (m x - 1) * φc x
          + (J x (fun i => Du' i x) (m x) ⬝ (fun i => Dφc i x)))
        (volume.restrict (UnitCube d)) := by
      have hbound0 := hgJ'_bound.self_of_nhds
      refine Integrable.mono' hgJ'_int ?_ ?_
      · have hmass : AEMeasurable (fun x => (m x - 1) * φc x)
            (volume.restrict (UnitCube d)) :=
          (hm_aem.sub_const 1).mul
            (aestronglyMeasurable_iff_aemeasurable.mp hφc_betaP.aestronglyMeasurable)
        have hflux : AEMeasurable
            (fun x => J x (fun i => Du' i x) (m x) ⬝ (fun i => Dφc i x))
            (volume.restrict (UnitCube d)) :=
          congestion_VI_Jflux_aemeasurable hcong.mDpHat0 hDu'_aem hm_aem
            (fun i => aestronglyMeasurable_iff_aemeasurable.mp
              (hDφc_gamma i).aestronglyMeasurable)
        exact (hmass.add hflux).aestronglyMeasurable
      · filter_upwards [hbound0] with x hx
        simpa using hx
    -- Discharge 3: `hFlux_diff_int` (per-`n` flux-difference integrability).
    have hFlux_diff_int : ∀ (n : ℕ), Integrable (fun x =>
        (max (m x) (δSeq n)
            * (DpH x (fun i => Du' i x) (max (m x) (δSeq n))
                ⬝ (fun i => Dφc i x)))
          - (J x (fun i => Du' i x) (m x) ⬝ (fun i => Dφc i x)))
        (volume.restrict (UnitCube d)) := by
      intro n
      have hmDpH : Integrable (fun x =>
          (max (m x) (δSeq n) - 1) * φc x
            + max (m x) (δSeq n)
              * (DpH x (fun i => Du i x + Dφc i x) (max (m x) (δSeq n))
                  ⬝ (fun i => Dφc i x))) (volume.restrict (UnitCube d)) := by
        obtain ⟨_, h2, _⟩ :=
          congestion_VI_firstvar_integrable_at_witness hmon hcong hm_mem hm_nn
            hu_memGamma hV hDu_memGamma hQuot_m_mem ψ (hδ_pos n) s
        exact h2
      have hmDpHflux : Integrable (fun x =>
          max (m x) (δSeq n)
            * (DpH x (fun i => Du' i x) (max (m x) (δSeq n))
                ⬝ (fun i => Dφc i x))) (volume.restrict (UnitCube d)) := by
        have hmass : Integrable (fun x => (max (m x) (δSeq n) - 1) * φc x)
            (volume.restrict (UnitCube d)) := by
          have hβconj : Real.HolderConjugate (hcong.β + 1)
              ((hcong.β + 1) / hcong.β) :=
            Theorems.SimplePower.SimplePowerExponentFacts.paper_holderConjugate_betaBar
              hcong.hβ
          have hmδ_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1))
              (fun x => max (m x) (δSeq n)) := by
            have := mPerDelta_memLpPer (d := d) (p := ENNReal.ofReal (hcong.β + 1))
              (δ := δSeq n) (hδ_pos n).le (m := m) hm_mem hm_nn
            simpa [mPerDelta] using! this
          have hmδ1 : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1))
              (fun x => max (m x) (δSeq n) - 1) := by
            have := hmδ_mem.add_const (-1 : ℝ)
            have heq : ((fun x => max (m x) (δSeq n))
                + fun _ : Fin d → ℝ => (-1 : ℝ))
                = (fun x => max (m x) (δSeq n) - 1) := by funext x; simp; ring
            rwa [heq] at this
          exact MemLpPer.integrable_mul hβconj hmδ1 hφc_betaP
        refine (hmDpH.sub hmass).congr (Filter.Eventually.of_forall (fun x => ?_))
        simp only [Pi.sub_apply, hDu'def]; ring
      have hJflux : Integrable (fun x =>
          J x (fun i => Du' i x) (m x) ⬝ (fun i => Dφc i x))
          (volume.restrict (UnitCube d)) := by
        have hmass : Integrable (fun x => (m x - 1) * φc x)
            (volume.restrict (UnitCube d)) := by
          have hβconj : Real.HolderConjugate (hcong.β + 1)
              ((hcong.β + 1) / hcong.β) :=
            Theorems.SimplePower.SimplePowerExponentFacts.paper_holderConjugate_betaBar
              hcong.hβ
          have hm1 : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1))
              (fun x => m x - 1) := by
            have := hm_mem.add_const (-1 : ℝ)
            have heq : (m + fun _ : Fin d → ℝ => (-1 : ℝ)) = (fun x => m x - 1) := by
              funext x; simp [Pi.add_apply]; ring
            rwa [heq] at this
          exact MemLpPer.integrable_mul hβconj hm1 hφc_betaP
        refine (hLHSaLim_int.sub hmass).congr
          (Filter.Eventually.of_forall (fun x => ?_))
        simp only [Pi.sub_apply]; ring
      exact hmDpHflux.sub hJflux
    -- Discharge 4: `hFlux_L1` (the `δ`-uniform flux `L¹` cert).
    have hFlux_L1 :
        Filter.Tendsto
          (fun n => ∫ x in UnitCube d,
              ‖max (m x) (δSeq n)
                  * (DpH x (fun i => Du' i x) (max (m x) (δSeq n))
                      ⬝ (fun i => Dφc i x))
                - J x (fun i => Du' i x) (m x) ⬝ (fun i => Dφc i x)‖
              ∂(volume : Measure (Fin d → ℝ)))
          Filter.atTop (nhds (0 : ℝ)) :=
      congestion_VI_Jflux_L1_diff_at (H := H) hcong hm_mem hm_nn
        hDu'_gamma hDφc_gamma hδ_pos hδ_le_one hδ_tendsto
    -- Discharge 2: `hMass_diff_int` (per-`n` mass-difference integrability).
    have hMass_diff_int : ∀ (n : ℕ), Integrable (fun x =>
        ((max (m x) (δSeq n) - 1) * φc x) - ((m x - 1) * φc x))
        (volume.restrict (UnitCube d)) := by
      intro n
      have hβconj : Real.HolderConjugate (hcong.β + 1) ((hcong.β + 1) / hcong.β) :=
        Theorems.SimplePower.SimplePowerExponentFacts.paper_holderConjugate_betaBar
          hcong.hβ
      have hmδ_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1))
          (fun x => max (m x) (δSeq n)) := by
        have := mPerDelta_memLpPer (d := d) (p := ENNReal.ofReal (hcong.β + 1))
          (δ := δSeq n) (hδ_pos n).le (m := m) hm_mem hm_nn
        simpa [mPerDelta] using! this
      have hmδ1 : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1))
          (fun x => max (m x) (δSeq n) - 1) := by
        have := hmδ_mem.add_const (-1 : ℝ)
        have heq : ((fun x => max (m x) (δSeq n)) + fun _ : Fin d → ℝ => (-1 : ℝ))
            = (fun x => max (m x) (δSeq n) - 1) := by funext x; simp; ring
        rwa [heq] at this
      have hm1 : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1))
          (fun x => m x - 1) := by
        have := hm_mem.add_const (-1 : ℝ)
        have heq : (m + fun _ : Fin d → ℝ => (-1 : ℝ)) = (fun x => m x - 1) := by
          funext x; simp [Pi.add_apply]; ring
        rwa [heq] at this
      have h1 : IntegrableOn (fun x => (max (m x) (δSeq n) - 1) * φc x)
          (UnitCube d) := MemLpPer.integrable_mul hβconj hmδ1 hφc_betaP
      have h2 : IntegrableOn (fun x => (m x - 1) * φc x) (UnitCube d) :=
        MemLpPer.integrable_mul hβconj hm1 hφc_betaP
      exact h1.sub h2
    -- Per-`n` variational inequality from the abstract VI (C1).
    have h_VI_at_mdelta : ∀ n,
        (∫ x in UnitCube d,
            (u x + φc x - hcong.C * ((max (m x) (δSeq n)) ^ hcong.β + 1) - V x)
              * (max (m x) (δSeq n) - m x)
            ∂(volume : Measure (Fin d → ℝ)))
        ≤
        (∫ x in UnitCube d,
            (max (m x) (δSeq n) - 1) * φc x
              + max (m x) (δSeq n)
                * (DpH x (fun i => Du i x + Dφc i x) (max (m x) (δSeq n))
                    ⬝ (fun i => Dφc i x))
            ∂(volume : Measure (Fin d → ℝ)))
        +
        (∫ x in UnitCube d,
            (0 : ℝ) * vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
                (fun i => Du i x + Dφc i x)
              * ((fun i => Du i x + Dφc i x) ⬝ (fun i => Dφc i x))
            + (0 : ℝ) * absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
                (u x + φc x) * ((u x + φc x) * φc x)
            ∂(volume : Measure (Fin d → ℝ))) := by
      intro n
      have hkey :=
        transport_h_VI_at_mdelta_of_abstractPeriodicVI hmon hcong hm_mem hm_nn
          hu_memGamma hDu_memGamma hQuot_m_mem hV habs
          (transportTruncTestPair hcong hmPer huPer hDuPer hm_mem hm_nn hu_Sob
            hu_L1 hu_memGamma hDu_weak hDu_memGamma hQuot_m_mem ψ s (hδ_pos n))
          ψ (hδ_pos n) hs rfl rfl rfl
      -- Rewrite `(t·ψ, t·∂ψ) = (φc, Dφc)` into the goal shape.
      simpa only [hφc, hDφc] using hkey
    -- The per-`n` connector integrands and their integrability.
    set LHSa : ℕ → (Fin d → ℝ) → ℝ := fun n x =>
      (max (m x) (δSeq n) - 1) * φc x
        + max (m x) (δSeq n)
          * (DpH x (fun i => Du i x + Dφc i x) (max (m x) (δSeq n))
              ⬝ (fun i => Dφc i x)) with hLHSadef
    set LHSaLim : (Fin d → ℝ) → ℝ := fun x =>
      (m x - 1) * φc x
        + (J x (fun i => Du i x + Dφc i x) (m x) ⬝ (fun i => Dφc i x))
      with hLHSaLimdef
    set RHSint : ℕ → (Fin d → ℝ) → ℝ := fun n x =>
      (u x + φc x - hcong.C * ((max (m x) (δSeq n)) ^ hcong.β + 1) - V x)
        * (max (m x) (δSeq n) - m x) with hRHSdef
    have hInts : ∀ n,
        Integrable (RHSint n) (volume.restrict (UnitCube d))
        ∧ Integrable (LHSa n) (volume.restrict (UnitCube d)) := by
      intro n
      obtain ⟨h1, h2, _⟩ :=
        congestion_VI_firstvar_integrable_at_witness hmon hcong hm_mem hm_nn
          hu_memGamma hV hDu_memGamma hQuot_m_mem ψ (hδ_pos n) s
      exact ⟨h1, h2⟩
    have hRHS_int : ∀ n, Integrable (RHSint n) (volume.restrict (UnitCube d)) :=
      fun n => (hInts n).1
    have hLHSa_int : ∀ n, Integrable (LHSa n) (volume.restrict (UnitCube d)) :=
      fun n => (hInts n).2
    have hLHSaLim_int' : Integrable LHSaLim (volume.restrict (UnitCube d)) := by
      rw [hLHSaLimdef]; exact hLHSaLim_int
    have hMass_L1 :
        Filter.Tendsto
          (fun n => ∫ x in UnitCube d,
              ‖φc x * (max (m x) (δSeq n)) - φc x * m x‖
              ∂(volume : Measure (Fin d → ℝ)))
          Filter.atTop (nhds (0 : ℝ)) :=
      congestion_VI_hMass_L1_at_witness hδ_pos hδ_tendsto hm_mem hm_nn ψ s
    have hRHS_L1 :
        Filter.Tendsto
          (fun n => ∫ x in UnitCube d, ‖RHSint n x - (0 : ℝ)‖
            ∂(volume : Measure (Fin d → ℝ)))
          Filter.atTop (nhds (0 : ℝ)) :=
      congestion_VI_hRHS_L1_at_witness hcong hδ_pos hδ_le_one hδ_tendsto hm_mem
        hm_nn hu_memGamma hV ψ s RHSint (fun n => rfl)
    have hLHS_L1 :
        Filter.Tendsto
          (fun n => ∫ x in UnitCube d, ‖LHSa n x - LHSaLim x‖
            ∂(volume : Measure (Fin d → ℝ)))
          Filter.atTop (nhds (0 : ℝ)) :=
      lhs_L1_diff_tendsto_J (DpH := DpH) (J := J) (m := m)
        (p := fun x => fun i => Du i x + Dφc i x) (δSeq := δSeq)
        φc (fun x => fun i => Dφc i x) LHSa LHSaLim
        (fun n => rfl) rfl
        hMass_diff_int hFlux_diff_int
        hMass_L1 hFlux_L1
    exact transport_mdelta_limit_of_L1_J (V := V) (DpH := DpH) (J := J)
      (Du := Du) (m := m) (u := u)
      (ε := 0) (γBar := hcong.α * (hcong.β + 1) / hcong.β)
      (β := hcong.β) (C := hcong.C)
      φc (0 : (Fin d → ℝ) → ℝ) (fun i x => Dφc i x)
      hδ_pos hδ_le_one hδ_tendsto h_VI_at_mdelta
      LHSa LHSaLim RHSint (fun n => rfl) rfl (fun n => rfl)
      hLHSa_int hLHSaLim_int' hRHS_int hLHS_L1 hRHS_L1
  -- The full `∀ t` statement: `t > 0`, `t = 0`, `t < 0`.
  intro t
  rcases lt_trichotomy t 0 with ht | ht | ht
  · have hposneg : 0 < -t := by linarith
    have hkey := h_dir_at (-t) hposneg (-φ)
    have hpd : ∀ (i : Fin d) (x : Fin d → ℝ),
        (Periodic.SmoothPeriodic.partialDeriv i (-φ) : (Fin d → ℝ) → ℝ) x
          = -((Periodic.SmoothPeriodic.partialDeriv i φ : (Fin d → ℝ) → ℝ) x) := by
      intro i x
      simp only [Periodic.SmoothPeriodic.coe_partialDeriv,
        Periodic.SmoothPeriodic.coe_neg]
      rw [fderiv_neg]
      rfl
    have hI1 :
        (∫ x in UnitCube d,
            (m x - 1) * (-t * ((-φ : Periodic.SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x)
              + (J x
                  (fun i => Du i x
                    + -t * (Periodic.SmoothPeriodic.partialDeriv i (-φ) :
                        (Fin d → ℝ) → ℝ) x)
                  (m x)
                ⬝ (fun i => -t
                    * (Periodic.SmoothPeriodic.partialDeriv i (-φ) :
                        (Fin d → ℝ) → ℝ) x))
            ∂(volume : Measure (Fin d → ℝ)))
        =
        (∫ x in UnitCube d,
            (m x - 1) * (t * (φ : (Fin d → ℝ) → ℝ) x)
              + (J x
                  (fun i => Du i x
                    + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                        (Fin d → ℝ) → ℝ) x)
                  (m x)
                ⬝ (fun i => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                    (Fin d → ℝ) → ℝ) x))
            ∂(volume : Measure (Fin d → ℝ))) := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      simp only []
      have hgradf : (fun i => Du i x
            + -t * (Periodic.SmoothPeriodic.partialDeriv i (-φ) :
                (Fin d → ℝ) → ℝ) x)
          = (fun i => Du i x
            + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                (Fin d → ℝ) → ℝ) x) := by
        funext i; rw [hpd i x]; ring
      have hgrad2 : (fun i => -t
              * (Periodic.SmoothPeriodic.partialDeriv i (-φ) :
                  (Fin d → ℝ) → ℝ) x)
          = (fun i => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
              (Fin d → ℝ) → ℝ) x) := by
        funext i; rw [hpd i x]; ring
      have hφval : (-t * ((-φ : Periodic.SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) x)
          = t * (φ : (Fin d → ℝ) → ℝ) x := by
        simp only [Periodic.SmoothPeriodic.coe_neg, Pi.neg_apply]; ring
      rw [hφval, hgradf, hgrad2]
    have hI2 :
        (∫ x in UnitCube d,
            (0 : ℝ) * vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
                (fun i => Du i x
                  + -t * (Periodic.SmoothPeriodic.partialDeriv i (-φ) :
                      (Fin d → ℝ) → ℝ) x)
              * ((fun i => Du i x
                    + -t * (Periodic.SmoothPeriodic.partialDeriv i (-φ) :
                        (Fin d → ℝ) → ℝ) x)
                  ⬝ (fun i => -t
                      * (Periodic.SmoothPeriodic.partialDeriv i (-φ) :
                          (Fin d → ℝ) → ℝ) x))
            + (0 : ℝ) * absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
                (u x + -t * ((-φ : Periodic.SmoothPeriodic d) :
                    (Fin d → ℝ) → ℝ) x)
              * ((u x + -t * ((-φ : Periodic.SmoothPeriodic d) :
                    (Fin d → ℝ) → ℝ) x)
                  * (-t * ((-φ : Periodic.SmoothPeriodic d) :
                      (Fin d → ℝ) → ℝ) x))
            ∂(volume : Measure (Fin d → ℝ)))
        =
        (∫ x in UnitCube d,
            (0 : ℝ) * vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
                (fun i => Du i x
                  + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                      (Fin d → ℝ) → ℝ) x)
              * ((fun i => Du i x
                    + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                        (Fin d → ℝ) → ℝ) x)
                  ⬝ (fun i => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                      (Fin d → ℝ) → ℝ) x))
            + (0 : ℝ) * absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
                (u x + t * (φ : (Fin d → ℝ) → ℝ) x)
              * ((u x + t * (φ : (Fin d → ℝ) → ℝ) x)
                  * (t * (φ : (Fin d → ℝ) → ℝ) x))
            ∂(volume : Measure (Fin d → ℝ))) := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      simp only []
      have hgradf : (fun i => Du i x
            + -t * (Periodic.SmoothPeriodic.partialDeriv i (-φ) :
                (Fin d → ℝ) → ℝ) x)
          = (fun i => Du i x
            + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                (Fin d → ℝ) → ℝ) x) := by
        funext i; rw [hpd i x]; ring
      have hgrad2 : (fun i => -t
              * (Periodic.SmoothPeriodic.partialDeriv i (-φ) :
                  (Fin d → ℝ) → ℝ) x)
          = (fun i => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
              (Fin d → ℝ) → ℝ) x) := by
        funext i; rw [hpd i x]; ring
      have hφval : (-t * ((-φ : Periodic.SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) x)
          = t * (φ : (Fin d → ℝ) → ℝ) x := by
        simp only [Periodic.SmoothPeriodic.coe_neg, Pi.neg_apply]; ring
      rw [hgradf, hgrad2, hφval]
    rw [hI1, hI2] at hkey
    exact hkey
  · subst ht
    have h1 : (∫ x in UnitCube d,
          (m x - 1) * ((0 : ℝ) * (φ : (Fin d → ℝ) → ℝ) x)
            + (J x
                (fun i => Du i x
                  + (0 : ℝ) * (Periodic.SmoothPeriodic.partialDeriv i φ :
                      (Fin d → ℝ) → ℝ) x)
                (m x)
              ⬝ (fun i => (0 : ℝ)
                  * (Periodic.SmoothPeriodic.partialDeriv i φ :
                      (Fin d → ℝ) → ℝ) x))
          ∂(volume : Measure (Fin d → ℝ))) = 0 := by
      have hint : (fun x : Fin d → ℝ =>
          (m x - 1) * ((0 : ℝ) * (φ : (Fin d → ℝ) → ℝ) x)
            + (J x
                (fun i => Du i x
                  + (0 : ℝ) * (Periodic.SmoothPeriodic.partialDeriv i φ :
                      (Fin d → ℝ) → ℝ) x)
                (m x)
              ⬝ (fun i => (0 : ℝ)
                  * (Periodic.SmoothPeriodic.partialDeriv i φ :
                      (Fin d → ℝ) → ℝ) x)))
          = (fun _ => (0 : ℝ)) := by
        funext x
        have hz : (fun i => (0 : ℝ)
            * (Periodic.SmoothPeriodic.partialDeriv i φ :
                (Fin d → ℝ) → ℝ) x) = (fun _ => (0 : ℝ)) := by
          funext i; ring
        rw [hz]
        unfold dotProduct
        simp
      rw [hint, MeasureTheory.integral_zero]
    have h2 : (∫ x in UnitCube d,
          (0 : ℝ) * vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
              (fun i => Du i x
                + (0 : ℝ) * (Periodic.SmoothPeriodic.partialDeriv i φ :
                    (Fin d → ℝ) → ℝ) x)
            * ((fun i => Du i x
                  + (0 : ℝ) * (Periodic.SmoothPeriodic.partialDeriv i φ :
                      (Fin d → ℝ) → ℝ) x)
                ⬝ (fun i => (0 : ℝ)
                    * (Periodic.SmoothPeriodic.partialDeriv i φ :
                        (Fin d → ℝ) → ℝ) x))
          + (0 : ℝ) * absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
              (u x + (0 : ℝ) * (φ : (Fin d → ℝ) → ℝ) x)
            * ((u x + (0 : ℝ) * (φ : (Fin d → ℝ) → ℝ) x)
                * ((0 : ℝ) * (φ : (Fin d → ℝ) → ℝ) x))
          ∂(volume : Measure (Fin d → ℝ))) = 0 := by
      have hint : (fun x : Fin d → ℝ =>
          (0 : ℝ) * vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
              (fun i => Du i x
                + (0 : ℝ) * (Periodic.SmoothPeriodic.partialDeriv i φ :
                    (Fin d → ℝ) → ℝ) x)
            * ((fun i => Du i x
                  + (0 : ℝ) * (Periodic.SmoothPeriodic.partialDeriv i φ :
                      (Fin d → ℝ) → ℝ) x)
                ⬝ (fun i => (0 : ℝ)
                    * (Periodic.SmoothPeriodic.partialDeriv i φ :
                        (Fin d → ℝ) → ℝ) x))
          + (0 : ℝ) * absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
              (u x + (0 : ℝ) * (φ : (Fin d → ℝ) → ℝ) x)
            * ((u x + (0 : ℝ) * (φ : (Fin d → ℝ) → ℝ) x)
                * ((0 : ℝ) * (φ : (Fin d → ℝ) → ℝ) x)))
          = (fun _ => (0 : ℝ)) := by
        funext x; ring
      rw [hint, MeasureTheory.integral_zero]
    rw [h1, h2]; norm_num
  · exact h_dir_at t ht φ

open StationaryMFG.Hamiltonian (HypothesisMonotone CongestionGrowthCore) in
/-- **C2: the smooth-test transport identity `h_iota` from the abstract periodic
limit weak VI** (paper `eq:congest.transport`, line 1538). Abstract-VI analogue
of `congestion_transport_at_witness`: combines the `∀ t` direction inequality
`transport_hdir_of_abstractPeriodicVI` with the t→0 DCT continuity `h_lim`
(`iota_firstorder_h_lim_dct_J`) through `iota_transport_smooth_assembled_J` to
land

```
∫ (m−1)·φ + J(x, Du, m)·∇φ = 0   (with the ε = 0 Gateaux term vanishing).
```

Sourced entirely from `habs`; no Banach witness / cone data, no `0 < m` rider,
no `Hext_finite_at_zero` / `HypothesisHepsilonFtcSlice`. The flux is in the
paper-faithful closed-half-line `J` form; the `m · DpH` ↔ `J` conversion is C3's
job. -/
theorem h_transport_iota_of_abstractPeriodicVI
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) m)
    (hm_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hu_memGamma : MemLpPer (d := d)
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) u)
    (hDu_memGamma : ∀ i,
      MemLpPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Du i))
    (hQuot_m_mem :
      MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (fun x : Fin d → ℝ =>
          ‖fun i => Du i x‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) /
            (m x ^ hcong.τ + 1)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (hmPer : IsPeriodic m)
    (huPer : IsPeriodic u)
    (hDuPer : ∀ i, IsPeriodic (Du i))
    (hu_Sob : MemSobolevPer (d := d)
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) u)
    (hu_L1 : MemLpPer (d := d) 1 u)
    (hDu_weak : ∀ i, Periodic.HasWeakDerivPer (d := d) i u (Du i))
    (habs :
      ∀ (T : CongestionLimitVITestPair (d := d)
              (ENNReal.ofReal (hcong.β + 1))
              (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
              (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
              hcong.α hcong.β hcong.τ),
        0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH)
              T.Dυ T.μ T.υ
              (fun i x => T.Dυ i x - Du i x)
              (T.μ - m) (T.υ - u))
    (φ : Periodic.SmoothPeriodic d) :
    (∫ x in UnitCube d,
        (m x - 1) * (φ : (Fin d → ℝ) → ℝ) x
          + (J x (fun i => Du i x) (m x)
              ⬝ (fun i => (Periodic.SmoothPeriodic.partialDeriv i φ :
                  (Fin d → ℝ) → ℝ) x))
        ∂(volume : Measure (Fin d → ℝ)))
    +
    (∫ x in UnitCube d,
        (0 : ℝ) * vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
            (fun i => Du i x)
          * ((fun i => Du i x)
              ⬝ (fun i => (Periodic.SmoothPeriodic.partialDeriv i φ :
                  (Fin d → ℝ) → ℝ) x))
        + (0 : ℝ) * absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β) (u x)
            * (u x * (φ : (Fin d → ℝ) → ℝ) x)
        ∂(volume : Measure (Fin d → ℝ))) = 0 := by
  classical
  set γBar : ℝ := hcong.α * (hcong.β + 1) / hcong.β with hγBardef
  set φf : (Fin d → ℝ) → ℝ := (φ : (Fin d → ℝ) → ℝ) with hφfdef
  set Dφf : Fin d → (Fin d → ℝ) → ℝ :=
    fun i => (Periodic.SmoothPeriodic.partialDeriv i φ : (Fin d → ℝ) → ℝ)
    with hDφfdef
  have hα : 1 < hcong.α := hcong.hα
  have hβ : 0 < hcong.β := hcong.hβ
  have hγ : 1 < γBar := by
    rw [hγBardef]
    exact StationaryMFG.Hamiltonian.one_lt_gammaBar hcong.α hcong.β hα hβ
  have hφf_betaP : MemLpPer (d := d)
      (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) φf :=
    (Periodic.MemSobolevPer.of_smoothPeriodic _ φ).1
  have hφf_gamma : MemLpPer (d := d) (ENNReal.ofReal γBar) φf := by
    rw [hγBardef]; exact (Periodic.MemSobolevPer.of_smoothPeriodic _ φ).1
  have hDφf_gamma : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBar) (Dφf i) := by
    intro i; rw [hγBardef, hDφfdef]
    exact (Periodic.MemSobolevPer.of_smoothPeriodic _
      (Periodic.SmoothPeriodic.partialDeriv i φ)).1
  have hDu_gamma : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBar) (Du i) := by
    intro i; rw [hγBardef]; exact hDu_memGamma i
  have hu_gamma : MemLpPer (d := d) (ENNReal.ofReal γBar) u := by
    rw [hγBardef]; exact hu_memGamma
  -- The integrands `FA`, `FB` of the DCT (`ε = 0`).
  set FA : ℝ → (Fin d → ℝ) → ℝ := fun t => fun x =>
    (m x - 1) * φf x
      + (J x (fun i => Du i x + t * Dφf i x) (m x) ⬝ (fun i => Dφf i x))
    with hFAdef
  set FB : ℝ → (Fin d → ℝ) → ℝ := fun t => fun x =>
    (0 : ℝ) * vecAbsPowMinusTwo γBar (fun i => Du i x + t * Dφf i x)
        * ((fun i => Du i x + t * Dφf i x) ⬝ (fun i => Dφf i x))
      + (0 : ℝ) * absPowMinusTwo γBar (u x + t * φf x)
          * ((u x + t * φf x) * φf x)
    with hFBdef
  have hcontA : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      Filter.Tendsto (fun t => FA t x) (nhds (0 : ℝ)) (nhds (FA 0 x)) := by
    have := iota_FA_continuous_at_zero_ae_J (DpH := DpH) (J := J) (Du := Du)
      (m := m) hcong.mDpHat0.continuous_J hm_nn φf Dφf
    filter_upwards [this] with x hx
    simpa [hFAdef] using hx
  have hcontB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      Filter.Tendsto (fun t => FB t x) (nhds (0 : ℝ)) (nhds (FB 0 x)) := by
    have := iota_FB_continuous_at_zero_ae (Du := Du) (u := u) (ε := 0)
      (γBar := γBar) hγ φf Dφf
    filter_upwards [this] with x hx
    simpa [hFBdef] using hx
  obtain ⟨gA, hgA_int, hboundA⟩ :=
    iota_FA_uniform_dominator_J (H := H) hcong hm_mem hm_nn hDu_gamma
      φf Dφf hφf_betaP hDφf_gamma FA (fun t => by rw [hFAdef])
  obtain ⟨gB, hgB_int, hboundB⟩ :=
    iota_FB_uniform_dominator (Du := Du) (u := u) (ε := 0) (γBar := γBar)
      hγ ((Theorems.SimplePower.SimplePowerExponentFacts.paper_holderConjugate_gammaBar
        hα hβ).symm)
      φf Dφf hu_gamma hφf_gamma hDu_gamma hDφf_gamma FB (fun t => by rw [hFBdef])
  have hm_aem : AEMeasurable m (volume.restrict (UnitCube d)) :=
    aestronglyMeasurable_iff_aemeasurable.mp hm_mem.aestronglyMeasurable
  have hu_aem : AEMeasurable u (volume.restrict (UnitCube d)) :=
    aestronglyMeasurable_iff_aemeasurable.mp hu_gamma.aestronglyMeasurable
  have hφf_aem : AEMeasurable φf (volume.restrict (UnitCube d)) :=
    aestronglyMeasurable_iff_aemeasurable.mp hφf_betaP.aestronglyMeasurable
  have hDu_aem : ∀ i, AEMeasurable (Du i) (volume.restrict (UnitCube d)) :=
    fun i => aestronglyMeasurable_iff_aemeasurable.mp (hDu_gamma i).aestronglyMeasurable
  have hDφf_aem : ∀ i, AEMeasurable (Dφf i) (volume.restrict (UnitCube d)) :=
    fun i => aestronglyMeasurable_iff_aemeasurable.mp (hDφf_gamma i).aestronglyMeasurable
  have hmeasA : ∀ᶠ t in nhds (0 : ℝ),
      AEStronglyMeasurable (FA t) (volume.restrict (UnitCube d)) := by
    refine Filter.Eventually.of_forall (fun t => ?_)
    rw [hFAdef]
    have hmass : AEMeasurable (fun x => (m x - 1) * φf x)
        (volume.restrict (UnitCube d)) :=
      (hm_aem.sub_const 1).mul hφf_aem
    have hpert_aem : AEMeasurable
        (fun x => (fun i => Du i x + t * Dφf i x))
        (volume.restrict (UnitCube d)) := by
      rw [aemeasurable_pi_iff]; intro i
      exact (hDu_aem i).add (aemeasurable_const.mul (hDφf_aem i))
    have hflux : AEMeasurable
        (fun x => J x (fun i => Du i x + t * Dφf i x) (m x)
          ⬝ (fun i => Dφf i x))
        (volume.restrict (UnitCube d)) :=
      congestion_VI_Jflux_aemeasurable hcong.mDpHat0 hpert_aem hm_aem hDφf_aem
    exact (hmass.add hflux).aestronglyMeasurable
  have hmeasB : ∀ᶠ t in nhds (0 : ℝ),
      AEStronglyMeasurable (FB t) (volume.restrict (UnitCube d)) := by
    refine Filter.Eventually.of_forall (fun t => ?_)
    rw [hFBdef]
    have hpert_aem : AEMeasurable
        (fun x => (fun i => Du i x + t * Dφf i x))
        (volume.restrict (UnitCube d)) := by
      rw [aemeasurable_pi_iff]; intro i
      exact (hDu_aem i).add (aemeasurable_const.mul (hDφf_aem i))
    have hscal_aem : AEMeasurable (fun x => u x + t * φf x)
        (volume.restrict (UnitCube d)) :=
      hu_aem.add (aemeasurable_const.mul hφf_aem)
    have hvecRpow_aem : AEMeasurable
        (fun x => vecSignedRpow γBar (fun i => Du i x + t * Dφf i x))
        (volume.restrict (UnitCube d)) :=
      (continuous_vecSignedRpow hγ).measurable.comp_aemeasurable hpert_aem
    have hvecdot_aem : AEMeasurable
        (fun x => vecSignedRpow γBar (fun i => Du i x + t * Dφf i x)
          ⬝ (fun i => Dφf i x))
        (volume.restrict (UnitCube d)) := by
      set g : Fin d → (Fin d → ℝ) → ℝ :=
        fun i x => vecSignedRpow γBar (fun j => Du j x + t * Dφf j x) i * Dφf i x
        with hgdef
      have hsum : AEMeasurable (∑ i, g i) (volume.restrict (UnitCube d)) :=
        Finset.aemeasurable_sum Finset.univ (fun i _ => by
          rw [hgdef]
          exact ((measurable_pi_apply i).comp_aemeasurable hvecRpow_aem).mul
            (hDφf_aem i))
      have heq : (fun x => vecSignedRpow γBar (fun i => Du i x + t * Dφf i x)
            ⬝ (fun i => Dφf i x))
          = (∑ i, g i) := by
        funext x; rw [Finset.sum_apply]; unfold dotProduct; rfl
      rw [heq]; exact hsum
    have hscRpow_aem : AEMeasurable (fun x => signedRpow γBar (u x + t * φf x))
        (volume.restrict (UnitCube d)) :=
      (continuous_signedRpow hγ).measurable.comp_aemeasurable hscal_aem
    have hAaem : AEMeasurable (fun x =>
        (0 : ℝ) * (vecSignedRpow γBar (fun i => Du i x + t * Dφf i x)
            ⬝ (fun i => Dφf i x))
          + (0 : ℝ) * (signedRpow γBar (u x + t * φf x) * φf x))
        (volume.restrict (UnitCube d)) :=
      (aemeasurable_const.mul hvecdot_aem).add
        (aemeasurable_const.mul (hscRpow_aem.mul hφf_aem))
    refine (hAaem.aestronglyMeasurable).congr (Filter.Eventually.of_forall
      (fun x => ?_))
    change (0 : ℝ) * (vecSignedRpow γBar (fun i => Du i x + t * Dφf i x)
          ⬝ (fun i => Dφf i x))
        + (0 : ℝ) * (signedRpow γBar (u x + t * φf x) * φf x)
      = FB t x
    have hvec : vecSignedRpow γBar (fun i => Du i x + t * Dφf i x)
          ⬝ (fun i => Dφf i x)
        = vecAbsPowMinusTwo γBar (fun i => Du i x + t * Dφf i x)
            * ((fun i => Du i x + t * Dφf i x) ⬝ (fun i => Dφf i x)) := by
      unfold dotProduct vecSignedRpow
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    have hsc : signedRpow γBar (u x + t * φf x) * φf x
        = absPowMinusTwo γBar (u x + t * φf x) * ((u x + t * φf x) * φf x) := by
      unfold signedRpow; ring
    rw [hvec, hsc, hFBdef]; ring
  have h_lim := iota_firstorder_h_lim_dct_J (DpH := DpH) (J := J) (Du := Du)
    (m := m) (u := u) (ε := 0) (γBar := γBar) φf Dφf FA FB
    (fun t => by rw [hFAdef]) (fun t => by rw [hFBdef])
    hcontA hcontB gA gB hgA_int hgB_int hboundA hboundB hmeasA hmeasB
  have h_dir := transport_hdir_of_abstractPeriodicVI hmon hcong hm_mem hm_nn
    hu_memGamma hDu_memGamma hQuot_m_mem hV hmPer huPer hDuPer hu_Sob hu_L1
    hDu_weak habs φ
  exact iota_transport_smooth_assembled_J (_V := V) (DpH := DpH) (J := J)
    (Du := Du) (m := m) (u := u) (ε := 0) (γBar := γBar) φf Dφf FA FB
    (fun t => by rw [hFAdef]) (fun t => by rw [hFBdef]) h_dir h_lim



end StationaryMFG.Congestion
