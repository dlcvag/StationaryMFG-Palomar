module

/-
Copyright (c) 2026 Stationary MFG project. All rights reserved.
Released under Apache 2.0 license as described in the repository LICENSE.
-/
public import Mathlib

/-! Three standalone existence challenges for Ferreira–Gomes–Üçer,
*Solving Mean-Field Games with Monotonicity Methods in Banach Spaces*.
See README.md for representation conventions and verification instructions.
Preserve these definitions and statements when filling the three proof holes. -/

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

def euclideanDot (v w : Point d) : ℝ := ∑ i, v i * w i
scoped infixl:72 " ⬝ " => euclideanDot

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
  sorry

/-- Paper `thm:main-congestion.growth`: strong existence under congestion growth. -/
theorem Theorems.Congestion.thm_main_congestion_growth_paper [Fact (0 < d)]
    (V : Field d) (H : Point d → Point d → ℝ → ℝ)
    (DpH J : Point d → Point d → ℝ → Point d)
    (hmon : HypothesisMonotone H DpH) (hcong : HypothesisCongestionGrowth H DpH J)
    (hV : MemLpPer (ENNReal.ofReal (betaBar' hcong.β)) V) (hVPer : IsPeriodic V) :
    ∃ (m u : Field d) (Du : Gradient d),
      IsStrongSolution V H J Du m u ∧
      SolutionRegularity hcong.α hcong.β m u Du := by
  sorry

/-- Paper `thm:main-weak.power.growth`: weak existence under weak power growth. -/
theorem Theorems.InfimalConvolution.thm_main_weak_power_growth_paper [Fact (0 < d)]
    {H : Point d → Point d → ℝ → ℝ} {DpH : Point d → Point d → ℝ → Point d}
    (V : Field d) (hmon : HypothesisMonotone H DpH) (hweak : HypothesisWeakGrowth H DpH)
    (hV : MemLpPer (ENNReal.ofReal (betaBar' hweak.β)) V) (hVPer : IsPeriodic V) :
    ∃ (m u : Field d) (Du : Gradient d),
      IsWeakSolution V H DpH Du m u ∧
      SolutionRegularity hweak.α hweak.β m u Du := by
  sorry

end StationaryMFGChallenge
end
