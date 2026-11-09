module

public import StationaryMFG.Theorems.SimplePower.Paper
public import StationaryMFG.Theorems.Congestion.PaperMain
public import StationaryMFG.Solutions.PaperStrong
public import StationaryMFG.Periodic.WeakDerivative
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import StationaryMFG.Theorems.InfimalConvolution.PaperMain

/-!
# Integrability of the transport and weak-solution integrands

The lemmas derive integrability from the main hypotheses and witness regularity.
They ensure that the totalized Bochner integral in the solution definitions is
used only on integrable functions under the main theorems' full conclusions.
No new hypothesis is added to the challenge targets.
-/

@[expose] public section

open scoped ENNReal
open MeasureTheory Set
open StationaryMFG.Periodic StationaryMFG.Hamiltonian

namespace TransportIntegrabilityAudit

variable {d : ℕ}

lemma continuous_multiplier_integrable {f g : (Fin d → ℝ) → ℝ}
    (hf : IntegrableOn f (UnitCube d)) (hg : Continuous g) :
    IntegrableOn (fun x => f x * g x) (UnitCube d) := by
  apply hf.mul_continuousOn_of_subset hg.continuousOn measurableSet_unitCube
    (isCompact_univ_pi (fun _ : Fin d => isCompact_Icc))
  intro x hx i _
  exact Ico_subset_Icc_self (hx i (mem_univ _))

lemma exact_transport_integrand_integrable
    {V : (Fin d → ℝ) → ℝ}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    (h : StationaryMFG.Solutions.Strong.IsStrongSolution_Transport V J Du m u)
    (hm : IntegrableOn m (UnitCube d)) (φ : SmoothPeriodic d) :
    IntegrableOn (fun x =>
      (m x - 1) * φ x + J x (fun i => Du i x) (m x)
        ⬝ (fun i => SmoothPeriodic.partialDeriv i φ x)) (UnitCube d) := by
  haveI : IsFiniteMeasure (volume.restrict (UnitCube d)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  have hm1 : IntegrableOn (fun x => m x - 1) (UnitCube d) :=
    hm.sub (integrable_const 1)
  have hmass := continuous_multiplier_integrable hm1 φ.smooth.continuous
  have hJ : Integrable (fun x => J x (fun i => Du i x) (m x))
      (volume.restrict (UnitCube d)) := h.1
  have hprod : ∀ i, IntegrableOn (fun x => J x (fun j => Du j x) (m x) i *
      SmoothPeriodic.partialDeriv i φ x) (UnitCube d) := fun i =>
    continuous_multiplier_integrable (hJ.eval i) (SmoothPeriodic.partialDeriv i φ).smooth.continuous
  exact hmass.add (integrable_finset_sum Finset.univ (fun i _ => hprod i))

lemma exact_transport_integrand_integrable_from_memLp
    {V : (Fin d → ℝ) → ℝ}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    (h : StationaryMFG.Solutions.Strong.IsStrongSolution_Transport V J Du m u)
    (hm : MemLpPer p m) (φ : SmoothPeriodic d) :
    IntegrableOn (fun x =>
      (m x - 1) * φ x + J x (fun i => Du i x) (m x)
        ⬝ (fun i => SmoothPeriodic.partialDeriv i φ x)) (UnitCube d) := by
  haveI : IsFiniteMeasure (volume.restrict (UnitCube d)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  exact exact_transport_integrand_integrable h (MeasureTheory.MemLp.integrable hp hm.toMemLp) φ

#print axioms exact_transport_integrand_integrable
#print axioms exact_transport_integrand_integrable_from_memLp

lemma exact_transport_integrand_integrable_from_paper_regularity
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    {β : ℝ} (hβ : 0 < β)
    (h : StationaryMFG.Solutions.PaperStrong.IsStrongSolution V H J Du m u)
    (hm : MemLpPer (ENNReal.ofReal (betaBar β)) m) (φ : SmoothPeriodic d) :
    IntegrableOn (fun x =>
      (m x - 1) * φ x + J x (fun i => Du i x) (m x)
        ⬝ (fun i => SmoothPeriodic.partialDeriv i φ x)) (UnitCube d) := by
  exact exact_transport_integrand_integrable_from_memLp
    (fact_one_le_ofReal_betaBar hβ).out h.2 hm φ

#print axioms exact_transport_integrand_integrable_from_paper_regularity


theorem theorem1_with_integrability
    [Fact (0 < d)]
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hmon : StationaryMFG.Hamiltonian.Paper.HypothesisMonotone H DpH)
    (hpow : StationaryMFG.Hamiltonian.Paper.HypothesisPowerGrowth H DpH)
    (hV : MemLpPer (ENNReal.ofReal (betaBar' hpow.β)) V) :
    ∃ (m u : (Fin d → ℝ) → ℝ) (Du : Fin d → (Fin d → ℝ) → ℝ),
      StationaryMFG.Solutions.PaperStrong.IsStrongSolution V H
          (JsimplePositiveExt DpH) Du m u
        ∧ MemLpPer (ENNReal.ofReal (betaBar hpow.β)) m
        ∧ MemSobolevPer (ENNReal.ofReal (gammaBar hpow.α hpow.β)) u
        ∧ (∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
        ∧ (∀ i, HasWeakDerivPer i u (Du i))
        ∧ (∀ i, MemLpPer (ENNReal.ofReal (gammaBar hpow.α hpow.β)) (Du i))
        ∧ ∀ φ : SmoothPeriodic d, IntegrableOn (fun x =>
          (m x - 1) * φ x + JsimplePositiveExt DpH x (fun i => Du i x) (m x)
            ⬝ (fun i => SmoothPeriodic.partialDeriv i φ x)) (UnitCube d) := by
  obtain ⟨m, u, Du, hsol, hm, hu, hnn, hweak, hgrad⟩ :=
    StationaryMFG.Theorems.SimplePower.thm_main_simplePowerGrowth_faithful
      V H DpH hmon hpow hV
  exact ⟨m, u, Du, hsol, hm, hu, hnn, hweak, hgrad,
    exact_transport_integrand_integrable_from_paper_regularity hpow.hβ hsol hm⟩

theorem theorem2_with_integrability
    [Fact (0 < d)]
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hmon : StationaryMFG.Hamiltonian.Paper.HypothesisMonotone H DpH)
    (hcong : StationaryMFG.Hamiltonian.Paper.HypothesisCongestionGrowth H DpH J)
    (hV : MemLpPer (ENNReal.ofReal (betaBar' hcong.β)) V)
    (hVPer : IsPeriodic V) :
    ∃ (m u : (Fin d → ℝ) → ℝ) (Du : Fin d → (Fin d → ℝ) → ℝ),
      StationaryMFG.Solutions.PaperStrong.IsStrongSolution V H J Du m u
        ∧ MemLpPer (ENNReal.ofReal (hcong.β + 1)) m
        ∧ MemSobolevPer (ENNReal.ofReal (gammaBar hcong.α hcong.β)) u
        ∧ (∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
        ∧ (∀ i, HasWeakDerivPer i u (Du i))
        ∧ (∀ i, MemLpPer (ENNReal.ofReal (gammaBar hcong.α hcong.β)) (Du i))
        ∧ ∀ φ : SmoothPeriodic d, IntegrableOn (fun x =>
          (m x - 1) * φ x + J x (fun i => Du i x) (m x)
            ⬝ (fun i => SmoothPeriodic.partialDeriv i φ x)) (UnitCube d) := by
  obtain ⟨m, u, Du, hsol, hm, hu, hnn, hweak, hgrad⟩ :=
    StationaryMFG.Theorems.Congestion.thm_main_congestion_growth_faithful
      V H DpH J hmon hcong hV hVPer
  exact ⟨m, u, Du, hsol, hm, hu, hnn, hweak, hgrad,
    exact_transport_integrand_integrable_from_paper_regularity hcong.hβ hsol hm⟩

#print axioms theorem1_with_integrability
#print axioms theorem2_with_integrability

end TransportIntegrabilityAudit

open MeasureTheory StationaryMFG.Periodic StationaryMFG.Hamiltonian
open StationaryMFG.Solutions.Weak
open scoped StationaryMFG.Hamiltonian

namespace WeakIntegrabilityAudit

variable {d : ℕ}

lemma from_factors
    {b bp g gp : ℝ} (hb : b.HolderConjugate bp) (hg : g.HolderConjugate gp)
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {Du Dv : Fin d → (Fin d → ℝ) → ℝ}
    {m u mu v : (Fin d → ℝ) → ℝ}
    (h1 : MemLpPer (ENNReal.ofReal bp) (fun x => -v x - H x (fun i => Dv i x) (mu x) + V x))
    (hmu : MemLpPer (ENNReal.ofReal b) mu)
    (hgrad : ∀ i, MemLpPer (ENNReal.ofReal gp) (fun x => mu x * DpH x (fun j => Dv j x) (mu x) i))
    (hDv : ∀ i, MemLpPer (ENNReal.ofReal g) (Dv i))
    (hval : MemLpPer (ENNReal.ofReal gp) (fun x => mu x - 1))
    (hv : MemLpPer (ENNReal.ofReal g) v)
    (hm : MemLpPer (ENNReal.ofReal b) m)
    (hu : MemLpPer (ENNReal.ofReal g) u)
    (hDu : ∀ i, MemLpPer (ENNReal.ofReal g) (Du i)) :
    IntegrableOn (fun x =>
        (-v x - H x (fun i => Dv i x) (mu x) + V x) * (mu x - m x)
          + mu x * (DpH x (fun i => Dv i x) (mu x) ⬝ (fun i => Dv i x - Du i x))
          + (mu x - 1) * (v x - u x)) (UnitCube d) := by
  have hA := MemLpPer.integrable_mul hb.symm h1 (MemLp.toMemLpPer (hmu.toMemLp.sub hm.toMemLp))
  have hC := MemLpPer.integrable_mul hg.symm hval (MemLp.toMemLpPer (hv.toMemLp.sub hu.toMemLp))
  have hBi : ∀ i, IntegrableOn
      (fun x => (mu x * DpH x (fun j => Dv j x) (mu x) i) * (Dv i x - Du i x))
      (UnitCube d) := fun i =>
    MemLpPer.integrable_mul hg.symm (hgrad i) (MemLp.toMemLpPer ((hDv i).toMemLp.sub (hDu i).toMemLp))
  have hB := integrable_finset_sum Finset.univ (fun i _ => hBi i)
  have hsum := (hA.add hB).add hC
  refine hsum.congr ?_
  filter_upwards with x
  simp only [Pi.add_apply, Pi.sub_apply, dotProduct, Finset.mul_sum]
  congr 2
  exact Finset.sum_congr rfl (fun i _ => by ring)

lemma old_regular_integrable
    {b bp g gp : ℝ} (hb : b.HolderConjugate bp) (hg : g.HolderConjugate gp)
    (hexp : ENNReal.ofReal gp ≤ ENNReal.ofReal b)
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {Du Dv : Fin d → (Fin d → ℝ) → ℝ}
    {m u mu v : (Fin d → ℝ) → ℝ}
    (hweak : HypothesisWeakGrowth H DpH)
    (hdiff : HypothesisHpDifferentiable H DpH)
    (hV : MemLpPer (ENNReal.ofReal bp) V)
    (hm : MemLpPer (ENNReal.ofReal b) m)
    (hu : MemLpPer (ENNReal.ofReal g) u)
    (hDu : ∀ i, MemLpPer (ENNReal.ofReal g) (Du i))
    (htest : IsWeakSolutionTestPair Dv mu v) :
    IntegrableOn (fun x =>
        (-v x - H x (fun i => Dv i x) (mu x) + V x) * (mu x - m x)
          + mu x * (DpH x (fun i => Dv i x) (mu x) ⬝ (fun i => Dv i x - Du i x))
          + (mu x - 1) * (v x - u x)) (UnitCube d) := by
  obtain ⟨h1, hmu, hgrad, hDv, hval, hv⟩ :=
    StationaryMFG.InfimalConvolution.LimitPassage.keystone_sixFactors_of_testPair_VLp
      (βBar := b) (βBar' := bp) (γBar := g) (γBar' := gp)
      (zero_lt_one.trans hb.symm.lt) hweak.toRegularityH hweak hdiff hexp
      ENNReal.ofReal_ne_top hV
  exact from_factors hb hg (h1 Dv mu v htest) (hmu Dv mu v htest)
    (hgrad Dv mu v htest) (hDv Dv mu v htest) (hval Dv mu v htest)
    (hv Dv mu v htest) hm hu hDu

lemma paper_integrable
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {Du Dv : Fin d → (Fin d → ℝ) → ℝ}
    {m u mu v : (Fin d → ℝ) → ℝ}
    (hmon : StationaryMFG.Hamiltonian.Paper.HypothesisMonotone H DpH)
    (hweak : StationaryMFG.Hamiltonian.Paper.HypothesisWeakGrowth H DpH)
    (hV : MemLpPer (ENNReal.ofReal ((hweak.β + 1) / hweak.β)) V)
    (hm : MemLpPer (ENNReal.ofReal (hweak.β + 1)) m)
    (hu : MemSobolevPer (ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β)) u)
    (hDu : ∀ i, MemLpPer (ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β)) (Du i))
    (htest : IsWeakSolutionTestPair Dv mu v) :
    IntegrableOn (fun x =>
        (-v x - H x (fun i => Dv i x) (mu x) + V x) * (mu x - m x)
          + mu x * (DpH x (fun i => Dv i x) (mu x) ⬝ (fun i => Dv i x - Du i x))
          + (mu x - 1) * (v x - u x)) (UnitCube d) := by
  have hb := StationaryMFG.Theorems.SimplePower.SimplePowerExponentFacts.paper_holderConjugate_betaBar hweak.hβ
  have hg := StationaryMFG.Theorems.SimplePower.SimplePowerExponentFacts.paper_holderConjugate_gammaBar hweak.hα hweak.hβ
  have hexp : ENNReal.ofReal ((hweak.α * (hweak.β + 1) / hweak.β) /
        (hweak.α * (hweak.β + 1) / hweak.β - 1)) ≤ ENNReal.ofReal (hweak.β + 1) := by
    apply ENNReal.ofReal_le_ofReal
    rw [div_le_iff₀ (sub_pos.mpr hg.lt)]
    have hbeta := hweak.hβ
    have halpha := hweak.hα
    have heq : (hweak.α * (hweak.β + 1) / hweak.β) * hweak.β = hweak.α * (hweak.β + 1) := by
      field_simp
    nlinarith
  have hcanonical : StationaryMFG.Hamiltonian.Paper.HypothesisMonotone
      (StationaryMFG.Hamiltonian.Paper.finiteExtension H)
      (StationaryMFG.Hamiltonian.Paper.canonicalGradient H) :=
    { toRegularityH := hmon.toRegularityH.finiteExtension_paper_regularity
      monotone := hmon.finiteExtension_monotone.monotone }
  have hcanon := old_regular_integrable hb hg hexp hweak.toCanonical
    hcanonical.toHypothesisHpDifferentiable hV hm hu.1 hDu htest
  refine hcanon.congr ?_
  obtain ⟨c, hc, hmu⟩ := htest.lower
  filter_upwards [hmon.toRegularityH.canonicalGradient_eq] with x hx
  have hpos : 0 < mu x := hc.trans_le (hmu x)
  rw [StationaryMFG.Hamiltonian.Paper.finiteExtension_of_pos H x _ hpos, hx _ _ hpos]

#print axioms paper_integrable
end WeakIntegrabilityAudit
