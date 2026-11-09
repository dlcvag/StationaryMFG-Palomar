module

/-
Copyright (c) 2026 Stationary MFG project. All rights reserved.
Released under Apache 2.0 license as described in the repository LICENSE.
-/
public import Mathlib
public import StationaryMFG.Theorems.SimplePower.Paper
public import StationaryMFG.Theorems.Congestion.PaperMain
public import StationaryMFG.Theorems.InfimalConvolution.PaperMain

/-! Proof-bearing counterpart of Challenge.lean. The definitions are independently
repeated for comparison; the bridge lemmas prove their agreement with the proof
library. See README.md for conventions and verification instructions. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace StationaryMFGChallenge

/-- Coordinate space with the supremum norm; see README for norm equivalence. -/
abbrev Point (d : ℕ) := Fin d → ℝ
abbrev Field (d : ℕ) := Point d → ℝ
abbrev Gradient (d : ℕ) := Point d → Point d
variable {d : ℕ}

/-! ## 1. Periodic calculus and function spaces -/

namespace Periodic

def IsPeriodic {X : Type*} (f : Point d → X) : Prop :=
  ∀ k : Fin d → ℤ, ∀ x, f (x + fun i => (k i : ℝ)) = f x

def UnitCube (d : ℕ) : Set (Point d) :=
  Set.pi Set.univ fun _ : Fin d => Set.Ico (0 : ℝ) 1

abbrev cubeMeasure (d : ℕ) : Measure (Point d) := volume.restrict (UnitCube d)

/-- Integrability on the cube; periodicity is imposed separately. -/
abbrev MemLpPer {E : Type*} [NormedAddCommGroup E]
    (p : ℝ≥0∞) (f : Point d → E) : Prop := MemLp f p (cubeMeasure d)

/-- Smooth means C∞, not analytic. -/
structure SmoothPeriodic (d : ℕ) where
  toFun : Field d
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : ℕ∞ω) toFun
  periodic : IsPeriodic toFun

instance : CoeFun (SmoothPeriodic d) (fun _ => Field d) := ⟨SmoothPeriodic.toFun⟩

/-- Classical gradient of a test function, with coordinates in the standard basis. -/
def SmoothPeriodic.gradient (φ : SmoothPeriodic d) : Gradient d :=
  fun x i => fderiv ℝ (φ : Field d) x (Pi.basisFun ℝ (Fin d) i)

/-- L¹ derivative witness and integration by parts against all periodic smooth tests. -/
def HasWeakDerivPer (i : Fin d) (f g : Field d) : Prop :=
  MemLpPer 1 g ∧ ∀ φ : SmoothPeriodic d,
    (∫ x, g x * φ x ∂cubeMeasure d) =
      -(∫ x, f x * φ.gradient x i ∂cubeMeasure d)

/-- W¹ᵖ regularity with a specified weak gradient. -/
structure HasSobolevGradient (p : ℝ≥0∞) (u : Field d) (Du : Gradient d) : Prop where
  function_memLp : MemLpPer p u
  weak_deriv : ∀ i, HasWeakDerivPer i u (fun x => Du x i)
  gradient_memLp : ∀ i, MemLpPer p (fun x => Du x i)

end Periodic
open Periodic

/-! ## 2. Standing assumptions and the three growth alternatives -/

namespace Hamiltonian

scoped infixl:72 " ⬝ " => dotProduct

/-- The linear functional w ↦ q ⬝ w, used to specify the momentum derivative. -/
def dotFunctional (q : Point d) : Point d →L[ℝ] ℝ :=
  ∑ i, q i • ContinuousLinearMap.proj i

/-- Density integrability exponent: β + 1. -/
def betaBar (β : ℝ) : ℝ := β + 1

/-- Gradient integrability exponent: α(β + 1)/β. -/
def gammaBar (α β : ℝ) : ℝ := α * (β + 1) / β

/-- Conjugate exponent for the potential: (β + 1)/β. -/
def betaBar' (β : ℝ) : ℝ := (β + 1) / β

/-- Standing regularity (H1), including the actual momentum derivative. -/
structure RegularityH
    (H : Point d → Point d → ℝ → ℝ)
    (DpH : Point d → Point d → ℝ → Point d) : Prop where
  periodic_H : ∀ p m, 0 < m → IsPeriodic (fun x => H x p m)
  measurable_H : Measurable
    (fun (xpm : Point d × Point d × {m : ℝ // 0 < m}) =>
      let (x, p, m) := xpm
      H x p m)
  continuous_H_pm : ∀ᵐ x ∂cubeMeasure d, ContinuousOn (fun (p, m) => H x p m)
    {pm | 0 < pm.2}
  hasFDerivAt_H_p : ∀ᵐ x ∂cubeMeasure d, ∀ (p : Point d) (m : ℝ), 0 < m →
    HasFDerivAt (fun q : Point d => H x q m) (dotFunctional (DpH x p m)) p
  continuous_DpH_pm : ∀ᵐ x ∂cubeMeasure d, ContinuousOn (fun (p, m) => DpH x p m)
    {pm | 0 < pm.2}

/-- Shared standing assumptions: regularity (H1) and Lasry–Lions monotonicity (A1).
Each theorem adds exactly one of the growth alternatives below. -/
structure HypothesisMonotone
    (H : Point d → Point d → ℝ → ℝ)
    (DpH : Point d → Point d → ℝ → Point d) : Prop
    extends RegularityH H DpH where
  monotone : ∀ᵐ x ∂cubeMeasure d, ∀ p₁ m₁ p₂ m₂, 0 < m₁ → 0 < m₂ →
    0 ≤ (-H x p₁ m₁ + H x p₂ m₂) * (m₁ - m₂)
      + (m₁ • DpH x p₁ m₁ - m₂ • DpH x p₂ m₂) ⬝ (p₁ - p₂)

/-- The three literal bounds in the simple power-growth assumption (A2). -/
structure HypothesisPowerGrowth
    (H : Point d → Point d → ℝ → ℝ)
    (DpH : Point d → Point d → ℝ → Point d) where
  C : ℝ
  α : ℝ
  β : ℝ
  hC : 0 < C
  hα : 1 < α
  hβ : 0 < β
  H_zero_momentum_upper : ∀ᵐ x ∂cubeMeasure d, ∀ m, 0 < m →
    H x (0 : Point d) m ≤ -(m ^ β) / C + C
  DpH_upper : ∀ᵐ x ∂cubeMeasure d, ∀ p m, 0 < m →
    ‖DpH x p m‖ ≤ C * (‖p‖ ^ (α - 1) + m ^ (β - β / α) + 1)
  H_lower : ∀ᵐ x ∂cubeMeasure d, ∀ p m, 0 < m →
    H x p m ≥ (‖p‖ ^ α) / C - C * (m ^ β + 1)

/-- Continuous limiting flux (H3); its value at zero need not vanish. -/
structure ContinuousFluxExtension
    (DpH : Point d → Point d → ℝ → Point d)
    (J : Point d → Point d → ℝ → Point d) : Prop where
  J_of_pos : ∀ x p m, 0 < m → J x p m = m • DpH x p m
  tendsto_at_zero : ∀ᵐ x ∂cubeMeasure d, ∀ p : Point d,
      Tendsto (fun m : ℝ => m • DpH x p m)
        (𝓝[>] (0 : ℝ)) (𝓝 (J x p 0))
  continuous_J : ∀ᵐ x ∂cubeMeasure d, ContinuousOn (fun (p, m) => J x p m)
    {pm | 0 ≤ pm.2}

/-- The three literal congestion-growth bounds and (H3), as in (A3). -/
structure HypothesisCongestionGrowth
    (H : Point d → Point d → ℝ → ℝ)
    (DpH : Point d → Point d → ℝ → Point d)
    (J : Point d → Point d → ℝ → Point d) where
  C : ℝ
  α : ℝ
  β : ℝ
  τ : ℝ
  hC : 0 < C
  hα : 1 < α
  hβ : 0 < β
  hτ : 0 ≤ τ ∧ τ ≤ 1
  flux_extension : ContinuousFluxExtension DpH J
  H_zero_momentum_upper : ∀ᵐ x ∂cubeMeasure d, ∀ m, 0 < m →
    H x (0 : Point d) m ≤ -(m ^ β) / C + C
  DpH_upper : ∀ᵐ x ∂cubeMeasure d, ∀ p m, 0 < m →
    ‖DpH x p m‖
      ≤ C * ((1 / m) + (1 / m ^ τ)) * (‖p‖ ^ (α * (1 + τ / β) - 1))
        + C * ((m ^ (β - β / α)) + 1 / m)
  H_lower : ∀ᵐ x ∂cubeMeasure d, ∀ p m, 0 < m →
    H x p m
      ≥ (1 / C) * (1 / (m ^ τ + 1)) * (‖p‖ ^ (α * (1 + τ / β)))
        - C * (m ^ β + 1)

/-- The three literal weak-growth bounds in (A4). -/
structure HypothesisWeakGrowth
    (H : Point d → Point d → ℝ → ℝ)
    (DpH : Point d → Point d → ℝ → Point d) where
  C : ℝ
  α : ℝ
  β : ℝ
  hC : 0 < C
  hα : 1 < α
  hβ : 0 < β
  f : Point d → ℝ → ℝ
  hf_continuous :
    ContinuousOn (fun (p, m) => f p m)
      {pm | 0 < pm.2}
  H_zero_momentum_upper : ∀ᵐ x ∂cubeMeasure d, ∀ m, 0 < m →
    H x (0 : Point d) m ≤ -(m ^ β) / C + C
  DpH_upper : ∀ᵐ x ∂cubeMeasure d, ∀ p m, 0 < m → ‖DpH x p m‖ ≤ f p m
  H_lower : ∀ᵐ x ∂cubeMeasure d, ∀ p m, 0 < m →
    H x p m ≥ (‖p‖ ^ α) / C - C * (m ^ β + 1)

/-! ## 3. Boundary conventions -/

/-- Extended-real boundary value, possibly +∞. Under the hypotheses the limit
exists for almost every x and every p; this is proved, not asserted by the definition. -/
def Hext
    (H : Point d → Point d → ℝ → ℝ) :
    Point d → Point d → ℝ → WithTop ℝ :=
  fun x p m =>
    if 0 < m then ((H x p m : ℝ) : WithTop ℝ)
    else
      Classical.epsilon
        (fun L : WithTop ℝ =>
          Tendsto (fun m : ℝ => ((H x p m : ℝ) : WithTop ℝ))
            (𝓝[>] (0 : ℝ)) (𝓝 L))

/-- Canonical simple-power flux: m • DpH, hence zero when m = 0. -/
def JsimpleExt
    (DpH : Point d → Point d → ℝ → Point d)
    (x p : Point d) (m : ℝ) : Point d :=
  if 0 < m then m • DpH x p m else 0

end Hamiltonian
open Hamiltonian
open scoped Hamiltonian

/-! ## 4. Solution regularity and the two solution concepts -/

/-- Regularity and nonnegativity required by all three existence theorems. -/
structure SolutionRegularity (α β : ℝ) (m u : Field d) (Du : Gradient d) : Prop where
  density_memLp : MemLpPer (ENNReal.ofReal (betaBar β)) m
  density_nonneg : ∀ᵐ x ∂cubeMeasure d, 0 ≤ m x
  sobolev_gradient : HasSobolevGradient (ENNReal.ofReal (gammaBar α β)) u Du

namespace Solutions.Strong

def IsStrongSolution_HJB (V : Field d) (H : Point d → Point d → ℝ → ℝ)
    (Du : Gradient d) (m u : Field d) : Prop :=
  (∀ᵐ x ∂cubeMeasure d,
    Hext H x (Du x) (m x) ≤ ((V x - u x : ℝ) : WithTop ℝ)) ∧
  (∀ᵐ x ∂cubeMeasure d, 0 < m x →
    Hext H x (Du x) (m x) = ((V x - u x : ℝ) : WithTop ℝ))

def IsStrongSolution_Transport (J : Point d → Point d → ℝ → Point d)
    (Du : Gradient d) (m : Field d) : Prop :=
  Integrable (fun x => J x (Du x) (m x)) (cubeMeasure d) ∧
  ∀ φ : SmoothPeriodic d,
    (∫ x, (m x - 1) * φ x + J x (Du x) (m x)
      ⬝ φ.gradient x ∂cubeMeasure d) = 0

def IsStrongSolution (V : Field d) (H : Point d → Point d → ℝ → ℝ)
    (J : Point d → Point d → ℝ → Point d) (Du : Gradient d) (m u : Field d) : Prop :=
  IsStrongSolution_HJB V H Du m u ∧ IsStrongSolution_Transport J Du m

end Solutions.Strong

namespace Solutions.Weak

structure IsWeakSolutionTestPair (Dυ : Gradient d) (μ υ : Field d) : Prop where
  density_pos_lower_bound : ∃ c : ℝ, 0 < c ∧ ∀ x, c ≤ μ x
  density_memLp : MemLpPer ⊤ μ
  sobolev_gradient : HasSobolevGradient ⊤ υ Dυ

def IsWeakSolution (V : Field d) (H : Point d → Point d → ℝ → ℝ)
    (DpH : Point d → Point d → ℝ → Point d) (Du : Gradient d) (m u : Field d) : Prop :=
  ∀ (Dυ : Gradient d) (μ υ : Field d), IsWeakSolutionTestPair Dυ μ υ →
    0 ≤ ∫ x,
      (-υ x - H x (Dυ x) (μ x) + V x) * (μ x - m x)
        + μ x * (DpH x (Dυ x) (μ x) ⬝ (Dυ x - Du x))
        + (μ x - 1) * (υ x - u x) ∂cubeMeasure d

end Solutions.Weak
open Solutions.Strong Solutions.Weak

/-! Equivalences with the proof library. The compact specification keeps the
same integrability, derivative, solution, and witness-regularity requirements. -/
namespace ComparatorBridge

/-- The proof library indexes derivative families by coordinate first. -/
abbrev gradientToProject (Du : Gradient d) : Fin d → Field d := fun i x => Du x i
abbrev gradientFromProject (Du : Fin d → Field d) : Gradient d := fun x i => Du i x

variable {H : Point d → Point d → ℝ → ℝ}
variable {DpH J : Point d → Point d → ℝ → Point d}

lemma memLp_iff_project {E : Type*} [NormedAddCommGroup E]
    {p : ℝ≥0∞} {f : Point d → E} :
    MemLpPer p f ↔ StationaryMFG.Periodic.MemLpPer p f :=
  ⟨fun h => ⟨h.aestronglyMeasurable, h⟩, fun h => h.2⟩

def smoothToProject (φ : SmoothPeriodic d) : StationaryMFG.Periodic.SmoothPeriodic d :=
  ⟨φ.toFun, φ.smooth, φ.periodic⟩

def smoothFromProject (φ : StationaryMFG.Periodic.SmoothPeriodic d) : SmoothPeriodic d :=
  ⟨φ.toFun, φ.smooth, φ.periodic⟩

lemma weakDeriv_iff_project {i : Fin d} {f g : Field d} :
    HasWeakDerivPer i f g ↔ StationaryMFG.Periodic.HasWeakDerivPer i f g :=
  ⟨fun h => ⟨memLp_iff_project.mp h.1, fun φ => h.2 (smoothFromProject φ)⟩,
   fun h => ⟨memLp_iff_project.mpr h.1, fun φ => h.2 (smoothToProject φ)⟩⟩

lemma dotCLM_eq_project (q : Point d) :
    dotFunctional q = StationaryMFG.Hamiltonian.dotCLMHam q := by
  ext w
  simp [dotFunctional, StationaryMFG.Hamiltonian.dotCLMHam_apply,
    dotProduct]

lemma regularity_iff_project :
    RegularityH H DpH ↔ StationaryMFG.Hamiltonian.Paper.RegularityH H DpH := by
  constructor <;> intro h
  · refine ⟨h.periodic_H, h.measurable_H, h.continuous_H_pm, ?_, h.continuous_DpH_pm⟩
    filter_upwards [h.hasFDerivAt_H_p] with x hx
    intro p m hm
    simpa only [dotCLM_eq_project] using hx p m hm
  · refine ⟨h.periodic_H, h.measurable_H, h.continuous_H_pm, ?_, h.continuous_DpH_pm⟩
    filter_upwards [h.hasFDerivAt_H_p] with x hx
    intro p m hm
    simpa only [dotCLM_eq_project] using hx p m hm

lemma monotoneToProject (h : HypothesisMonotone H DpH) :
    StationaryMFG.Hamiltonian.Paper.HypothesisMonotone H DpH :=
  ⟨regularity_iff_project.mp h.toRegularityH, h.monotone⟩

/-- The growth data are unchanged; H1 is supplied by the shared standing assumptions. -/
def powerEquiv (hreg : RegularityH H DpH) :
    HypothesisPowerGrowth H DpH ≃ StationaryMFG.Hamiltonian.Paper.HypothesisPowerGrowth H DpH where
  toFun h := ⟨regularity_iff_project.mp hreg, h.C, h.α, h.β, h.hC, h.hα, h.hβ,
    h.H_zero_momentum_upper, h.DpH_upper, h.H_lower⟩
  invFun h := ⟨h.C, h.α, h.β, h.hC, h.hα, h.hβ, h.upper, h.DpH_upper, h.lower⟩
  left_inv h := by cases h; rfl
  right_inv h := by cases h; rfl

lemma flux_iff_project :
    ContinuousFluxExtension DpH J ↔ StationaryMFG.Hamiltonian.PaperFluxExtension DpH J :=
  ⟨fun h => ⟨h.J_of_pos, h.tendsto_at_zero, h.continuous_J⟩,
   fun h => ⟨h.J_of_pos, h.tendsto_at_zero, h.continuous_J⟩⟩

def congestionEquiv (hreg : RegularityH H DpH) :
    HypothesisCongestionGrowth H DpH J ≃
      StationaryMFG.Hamiltonian.Paper.HypothesisCongestionGrowth H DpH J where
  toFun h := ⟨regularity_iff_project.mp hreg, h.C, h.α, h.β, h.τ,
    h.hC, h.hα, h.hβ, h.hτ, flux_iff_project.mp h.flux_extension,
    h.H_zero_momentum_upper, h.DpH_upper, h.H_lower⟩
  invFun h := ⟨h.C, h.α, h.β, h.τ, h.hC, h.hα, h.hβ, h.hτ,
    flux_iff_project.mpr h.mDpHat0, h.upper, h.DpH_upper, h.lower⟩
  left_inv h := by cases h; rfl
  right_inv h := by cases h; rfl

def weakEquiv (hreg : RegularityH H DpH) :
    HypothesisWeakGrowth H DpH ≃ StationaryMFG.Hamiltonian.Paper.HypothesisWeakGrowth H DpH where
  toFun h := ⟨regularity_iff_project.mp hreg, h.C, h.α, h.β, h.hC, h.hα, h.hβ,
    h.f, h.hf_continuous, h.H_zero_momentum_upper, h.DpH_upper, h.H_lower⟩
  invFun h := ⟨h.C, h.α, h.β, h.hC, h.hα, h.hβ,
    h.f, h.hf_continuous, h.upper, h.DpH_upper, h.lower⟩
  left_inv h := by cases h; rfl
  right_inv h := by cases h; rfl

lemma strong_iff_project {V m u : Field d} {Du : Gradient d} :
    IsStrongSolution V H J Du m u ↔
      StationaryMFG.Solutions.PaperStrong.IsStrongSolution V H J (gradientToProject Du) m u :=
  ⟨fun h => ⟨h.1, h.2.1, fun φ => h.2.2 (smoothFromProject φ)⟩,
   fun h => ⟨h.1, h.2.1, fun φ => h.2.2 (smoothToProject φ)⟩⟩

/-- Explicit weak gradients give exactly the project's expanded Sobolev conditions. -/
lemma sobolevGradient_iff_project {p : ℝ≥0∞} {u : Field d} {Du : Gradient d} :
    HasSobolevGradient p u Du ↔
      StationaryMFG.Periodic.MemSobolevPer p u ∧
      (∀ i, StationaryMFG.Periodic.HasWeakDerivPer i u (fun x => Du x i)) ∧
      (∀ i, StationaryMFG.Periodic.MemLpPer p (fun x => Du x i)) := by
  constructor
  · intro h
    have hd := fun i => weakDeriv_iff_project.mp (h.weak_deriv i)
    exact ⟨⟨memLp_iff_project.mp h.function_memLp, gradientToProject Du, hd⟩,
      hd, fun i => memLp_iff_project.mp (h.gradient_memLp i)⟩
  · rintro ⟨hu, hd, hlp⟩
    exact ⟨memLp_iff_project.mpr hu.1, fun i => weakDeriv_iff_project.mpr (hd i),
      fun i => memLp_iff_project.mpr (hlp i)⟩

lemma weakTestPair_iff_project {Dυ : Gradient d} {μ υ : Field d} :
    IsWeakSolutionTestPair Dυ μ υ ↔
      StationaryMFG.Solutions.Weak.IsWeakSolutionTestPair (gradientToProject Dυ) μ υ := by
  constructor
  · intro h
    obtain ⟨hu, hd, hlp⟩ := sobolevGradient_iff_project.mp h.sobolev_gradient
    exact ⟨h.density_pos_lower_bound, memLp_iff_project.mp h.density_memLp, hu, hlp, hd⟩
  · intro h
    exact ⟨h.lower, memLp_iff_project.mpr h.μ_linf,
      sobolevGradient_iff_project.mpr ⟨h.υ_sob_linf, h.Dυ_weak, h.Dυ_linf⟩⟩

lemma weakSolution_iff_project {V m u : Field d} {Du : Gradient d} :
    IsWeakSolution V H DpH Du m u ↔
      StationaryMFG.Solutions.Weak.IsWeakSolution V H DpH (gradientToProject Du) m u :=
  ⟨fun h Dυ μ υ ht => h (gradientFromProject Dυ) μ υ (weakTestPair_iff_project.mpr ht),
   fun h Dυ μ υ ht => h (gradientToProject Dυ) μ υ (weakTestPair_iff_project.mp ht)⟩

/-- Exact equivalence with the original, expanded theorem conclusions. -/
lemma solutionRegularity_iff_project {α β : ℝ} {m u : Field d} {Du : Gradient d} :
    SolutionRegularity α β m u Du ↔
      StationaryMFG.Periodic.MemLpPer (ENNReal.ofReal (betaBar β)) m ∧
      StationaryMFG.Periodic.MemSobolevPer (ENNReal.ofReal (gammaBar α β)) u ∧
      (∀ᵐ x ∂cubeMeasure d, 0 ≤ m x) ∧
      (∀ i, StationaryMFG.Periodic.HasWeakDerivPer i u (fun x => Du x i)) ∧
      (∀ i, StationaryMFG.Periodic.MemLpPer (ENNReal.ofReal (gammaBar α β)) (fun x => Du x i)) := by
  constructor
  · intro h
    obtain ⟨hu, hd, hlp⟩ := sobolevGradient_iff_project.mp h.sobolev_gradient
    exact ⟨memLp_iff_project.mp h.density_memLp, hu, h.density_nonneg, hd, hlp⟩
  · rintro ⟨hm, hu, hn, hd, hlp⟩
    exact ⟨memLp_iff_project.mpr hm, hn, sobolevGradient_iff_project.mpr ⟨hu, hd, hlp⟩⟩

end ComparatorBridge

/-! ## 5. The three existence theorems -/

/-- Paper `thm:main-simple.power.growth`: strong existence under simple power growth. -/
theorem Theorems.SimplePower.thm_main_simplePowerGrowth_paper [Fact (0 < d)]
    (V : Field d) (H : Point d → Point d → ℝ → ℝ)
    (DpH : Point d → Point d → ℝ → Point d)
    (hmon : HypothesisMonotone H DpH) (hpow : HypothesisPowerGrowth H DpH)
    (hV : MemLpPer (ENNReal.ofReal (betaBar' hpow.β)) V) (hVPer : IsPeriodic V) :
    ∃ (m u : Field d) (Du : Gradient d),
      IsStrongSolution V H (JsimpleExt DpH) Du m u ∧
      SolutionRegularity hpow.α hpow.β m u Du := by
  let hp := ComparatorBridge.powerEquiv hmon.toRegularityH hpow
  obtain ⟨m, u, Du, hs, hm, hu, hn, hd, hlp⟩ :=
    StationaryMFG.Theorems.SimplePower.thm_main_simplePowerGrowth_faithful
      V H DpH (ComparatorBridge.monotoneToProject hmon) hp
      (ComparatorBridge.memLp_iff_project.mp hV)
  exact ⟨m, u, ComparatorBridge.gradientFromProject Du,
    ComparatorBridge.strong_iff_project.mpr hs,
    ComparatorBridge.solutionRegularity_iff_project.mpr ⟨hm, hu, hn, hd, hlp⟩⟩

/-- Paper `thm:main-congestion.growth`: strong existence under congestion growth. -/
theorem Theorems.Congestion.thm_main_congestion_growth_paper [Fact (0 < d)]
    (V : Field d) (H : Point d → Point d → ℝ → ℝ)
    (DpH J : Point d → Point d → ℝ → Point d)
    (hmon : HypothesisMonotone H DpH) (hcong : HypothesisCongestionGrowth H DpH J)
    (hV : MemLpPer (ENNReal.ofReal (betaBar' hcong.β)) V) (hVPer : IsPeriodic V) :
    ∃ (m u : Field d) (Du : Gradient d),
      IsStrongSolution V H J Du m u ∧
      SolutionRegularity hcong.α hcong.β m u Du := by
  let hc := ComparatorBridge.congestionEquiv hmon.toRegularityH hcong
  obtain ⟨m, u, Du, hs, hm, hu, hn, hd, hlp⟩ :=
    StationaryMFG.Theorems.Congestion.thm_main_congestion_growth_faithful
      V H DpH J (ComparatorBridge.monotoneToProject hmon) hc
      (ComparatorBridge.memLp_iff_project.mp hV) hVPer
  exact ⟨m, u, ComparatorBridge.gradientFromProject Du,
    ComparatorBridge.strong_iff_project.mpr hs,
    ComparatorBridge.solutionRegularity_iff_project.mpr ⟨hm, hu, hn, hd, hlp⟩⟩

/-- Paper `thm:main-weak.power.growth`: weak existence under weak power growth. -/
theorem Theorems.InfimalConvolution.thm_main_weak_power_growth_paper [Fact (0 < d)]
    {H : Point d → Point d → ℝ → ℝ} {DpH : Point d → Point d → ℝ → Point d}
    (V : Field d) (hmon : HypothesisMonotone H DpH) (hweak : HypothesisWeakGrowth H DpH)
    (hV : MemLpPer (ENNReal.ofReal (betaBar' hweak.β)) V) (hVPer : IsPeriodic V) :
    ∃ (m u : Field d) (Du : Gradient d),
      IsWeakSolution V H DpH Du m u ∧
      SolutionRegularity hweak.α hweak.β m u Du := by
  let hw := ComparatorBridge.weakEquiv hmon.toRegularityH hweak
  obtain ⟨m, u, Du, hs, hm, hu, hn, hd, hlp⟩ :=
    StationaryMFG.Theorems.InfimalConvolution.thm_main_weak_power_growth_faithful
      V (ComparatorBridge.monotoneToProject hmon) hw
      (ComparatorBridge.memLp_iff_project.mp hV)
  exact ⟨m, u, ComparatorBridge.gradientFromProject Du,
    ComparatorBridge.weakSolution_iff_project.mpr hs,
    ComparatorBridge.solutionRegularity_iff_project.mpr ⟨hm, hu, hn, hd, hlp⟩⟩

end StationaryMFGChallenge
end
