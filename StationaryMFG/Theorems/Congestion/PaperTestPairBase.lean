module

public import StationaryMFG.Theorems.Congestion.WellDefined

@[expose] public section

/-! # Admissible periodic congestion test pairs

This interface is independent of the compactness and boundary proof.
-/

namespace StationaryMFG.Congestion

open scoped ENNReal

open MeasureTheory Filter Topology
open StationaryMFG.Periodic (IsPeriodic UnitCube MemLpPer MemSobolevPer)
open StationaryMFG.Solutions.MFG

variable {d : ℕ}

/-- **Admissible test pair for the limit weak VI** (paper line 1604,
`eq:existweaksol.congestion`).

Carries an admissible primal test pair `(μ, υ, Dυ)` on the torus with the
periodicity certificates needed to make the limit weak VI well-typed.

The congestion restriction `(μ, υ) ∈ 𝓚` (paper Definition of `𝓚` on
line ≈1597 — `μ ∈ L^{β̄}_per` with `essinf μ > 0`, `υ ∈ W^{1,γ̄}_per`)
is recorded as `μLp`, `υSob`, and `μ_pos` for downstream consumers; the
limit-passage kernel itself is `𝓚`-domain-agnostic but the bridge-deferred
pairing-convergence statement `hpair_conv` in `CongestionLimitVIUpstreamPack`
requires these.
-/
structure CongestionLimitVITestPair
    (βBar βBarPrime γBar : ℝ≥0∞) (α β τ : ℝ) where
  /-- Primal test density `μ`. -/
  μ : (Fin d → ℝ) → ℝ
  /-- Primal test value-function `υ`. -/
  υ : (Fin d → ℝ) → ℝ
  /-- Weak-derivative family for `υ`. -/
  Dυ : Fin d → (Fin d → ℝ) → ℝ
  /-- Periodicity of `μ`. -/
  hμPer : IsPeriodic μ
  /-- Periodicity of `υ`. -/
  hυPer : IsPeriodic υ
  /-- Periodicity of each weak derivative `Dυ i`. -/
  hDυPer : ∀ i, IsPeriodic (Dυ i)
  /-- Lp-regularity of the density `μ ∈ L^{β̄}_per` (paper `𝓚` cone). -/
  μLp : MemLpPer βBar μ
  /-- Sobolev-regularity of the value function `υ ∈ W^{1,γ̄}_per`. -/
  υSob : MemSobolevPer γBar υ
  /-- **Uniform positive lower bound** for `μ` (the `𝓚`-cone restriction
  `essinf μ > 0` — paper `def-domainK`, tex 1329). A.e. positivity is
  NOT enough: the paper requires `essinf μ > 0`, equivalently a single
  positive constant `c > 0` with `c ≤ μ` a.e. -/
  μ_lower : ∃ c : ℝ, 0 < c ∧
    (fun _ => c) ≤ᵐ[volume.restrict (UnitCube d)] μ
  /-- **`Dυ` is the weak derivative of `υ`** (anchors the test gradient to
  `υ`, so the cone witness is exactly `Dυ` and `P3a7b` can source
  `hDυ_memGamma` / `hDu_lim_memGamma` from these fields). -/
  hDυ_weak : ∀ i, StationaryMFG.Periodic.HasWeakDerivPer i υ (Dυ i)
  /-- **Ratio integrability** `‖Dυ‖^{α(1+τ/β)}/(μ^τ+1) ∈ L^{β̄'}_per`
  (paper `def-domainK`, tex 1329 — the integrability clause making
  `A_ε[μ,υ]` well-defined). -/
  hRatio_memLp : MemLpPer βBarPrime
    (fun x => (‖fun i => Dυ i x‖ ^ (α * (1 + τ / β))) / (μ x ^ τ + 1))
  /-- **Gradient `L^{γ̄}_per` membership** `∀ i, Dυ i ∈ L^{γ̄}_per`. -/
  hDυ_memGamma : ∀ i, MemLpPer γBar (Dυ i)

namespace CongestionLimitVITestPair

variable {βBar βBarPrime γBar : ℝ≥0∞} {α β τ : ℝ}

/-- **Strict a.e. positivity of `μ`** (derived from the uniform lower
bound `μ_lower`). Kept so legacy dot-notation `T.μ_pos` resolves. -/
theorem μ_pos (T : CongestionLimitVITestPair (d := d) βBar βBarPrime γBar α β τ) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < T.μ x := by
  obtain ⟨c, hc, hle⟩ := T.μ_lower
  filter_upwards [hle] with x hx
  exact lt_of_lt_of_le hc hx

/-- **`𝓚`-cone membership** of the test pair `(μ, υ)` (paper
`def-domainK`, tex 1329), with witness gradient `Dυ`. Bundles the
enriched fields into the `congestionDomainK` predicate so downstream
consumers (`aEpsi_congestion_HJB_memLp`) can source the HJB multiplier. -/
theorem hCone (T : CongestionLimitVITestPair (d := d) βBar βBarPrime γBar α β τ) :
    (T.μ, T.υ) ∈
      StationaryMFG.Congestion.congestionDomainK
        (d := d) βBar βBarPrime γBar α β τ :=
  ⟨T.μLp, T.υSob, T.μ_lower, T.Dυ, T.hDυ_weak, T.hRatio_memLp⟩

end CongestionLimitVITestPair

theorem congestionLimitVI_integral_le_of_abstract_at_periodicDensity
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {V : (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {βBar βBarPrime γBar : ℝ≥0∞} {α β τ : ℝ}
    -- The abstract limit weak VI over periodic admissible test pairs.
    (habs :
      ∀ (T : CongestionLimitVITestPair (d := d) βBar βBarPrime γBar α β τ),
        0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH)
              T.Dυ T.μ T.υ
              (fun i x => T.Dυ i x - Du i x)
              (T.μ - m) (T.υ - u))
    -- A periodic admissible test pair whose value/gradient are the limit data.
    (T : CongestionLimitVITestPair (d := d) βBar βBarPrime γBar α β τ)
    (hTυ : T.υ = u) (hTDυ : T.Dυ = Du) :
    ∫ x in UnitCube d,
        (u x + H x (fun i => Du i x) (T.μ x) - V x) * (T.μ x - m x)
        ∂(volume : Measure (Fin d → ℝ)) ≤ 0 := by
  classical
  -- The abstract VI at `T`.
  have hVI := habs T
  -- Collapse the two non-density summands of `mfgOperatorPair`: with
  -- `T.υ = u` and `T.Dυ = Du`, the value test direction `T.υ - u` and the
  -- gradient test direction `T.Dυ - Du` are identically zero, so the
  -- transport summand `μ·(DpH ⬝ 0)` and the mass-defect summand `(μ-1)·0`
  -- vanish pointwise. The remaining integrand is the HJB density integrand.
  have hcollapse :
      mfgOperatorPair (V := V) (H := H) (DpH := DpH)
          T.Dυ T.μ T.υ
          (fun i x => T.Dυ i x - Du i x)
          (T.μ - m) (T.υ - u)
        = ∫ x in UnitCube d,
            (-(u x) - H x (fun i => Du i x) (T.μ x) + V x) * (T.μ x - m x)
            ∂(volume : Measure (Fin d → ℝ)) := by
    subst hTυ hTDυ
    unfold mfgOperatorPair
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x
    -- Pointwise: gradient/value test directions are zero, so the transport
    -- summand `μ·(DpH ⬝ 0)` and the mass-defect summand `(μ-1)·0` vanish.
    have hDν : (fun i => T.Dυ i x - T.Dυ i x) = (0 : Fin d → ℝ) := by
      funext i; simp
    have hdot : dotProduct
        (DpH x (fun i => T.Dυ i x) (T.μ x)) (fun _ : Fin d => (0 : ℝ)) = 0 := by
      have : (fun _ : Fin d => (0 : ℝ)) = (0 : Fin d → ℝ) := rfl
      rw [this, StationaryMFG.Hamiltonian.euclideanDot_zero_right]
    simp only [Pi.sub_apply, sub_self, hdot, mul_zero, add_zero]
  rw [hcollapse] at hVI
  -- `0 ≤ ∫ (-(u) - H + V)(ρ-m)` gives `∫ (u + H - V)(ρ-m) ≤ 0` by negation.
  have hneg :
      ∫ x in UnitCube d,
          (u x + H x (fun i => Du i x) (T.μ x) - V x) * (T.μ x - m x)
          ∂(volume : Measure (Fin d → ℝ))
        = -∫ x in UnitCube d,
            (-(u x) - H x (fun i => Du i x) (T.μ x) + V x) * (T.μ x - m x)
            ∂(volume : Measure (Fin d → ℝ)) := by
    rw [← MeasureTheory.integral_neg]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x; ring
  rw [hneg]
  linarith [hVI]


end StationaryMFG.Congestion
