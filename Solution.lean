module

/-
Copyright (c) 2026 Stationary MFG project. All rights reserved.
Released under Apache 2.0 license as described in the repository LICENSE.
-/
public import Mathlib
public import StationaryMFG.Theorems.SimplePower.Paper
public import StationaryMFG.Theorems.Congestion.PaperMain
public import StationaryMFG.Theorems.InfimalConvolution.PaperMain


/-!
# Stationary mean-field games: solution

Ferreira, Gomes, Üçer, *Solving Mean-Field Games with Monotonicity Methods
in Banach Spaces*, arXiv:2506.21212. See README.md for the exact target and
verification instructions.

Proof-bearing counterpart of Challenge.lean.
The bridge lemmas identify the standalone definitions with the project definitions.
The three target theorems are checked against Challenge.lean by the Lean Comparator.

## Mathematical conventions

`H` and `DpH` are total Lean functions for convenience; all input assumptions
about them concern positive mass. `RegularityH.hasFDerivAt_H_p` certifies that
`DpH` is the genuine momentum gradient, as required by the notation in (H1).
No independent convexity, FTC, DpH-measurability, or derived-estimate premise is
imposed. In particular, regularity imposes measurability of H only on the
positive-mass domain, not on its arbitrary supplied values at nonpositive mass.

The strong HJB condition uses the extended-real right-limit `Hext`, which can
be +infinity. The existence of this limit follows from monotonicity and is
part of the work required to solve the challenge. Its equality to the supplied
real value `H x p 0` is never assumed. The congestion flux J is a witness for
(H3): it agrees with m DpH for positive mass and with its continuous limiting
extension at zero. It need not vanish at zero. Its measurability is not added
as a premise. Simple growth uses its canonical zero flux at zero; weak growth
needs no boundary-flux assumption, since all weak-test densities are positive.

The coordinate space `Fin d → ℝ` carries Mathlib's sup norm. Norm equivalence
in finite dimension changes the available growth constant C and leaves the
exponents and mathematical class of Hamiltonians unchanged. All three targets
use d>0 and a periodic representative of the torus potential. H is periodic
in x only for positive mass. The half-open cube `[0,1)^d` represents integration
over the torus. `MemLpPer` alone records integrability, not periodicity: restrict
returned functions to that cube and periodize them to obtain torus functions.
The integration-by-parts identities against periodic tests are precisely the
torus weak-derivative identities. `MemSobolevPer` alone supplies L1 derivative
witnesses; each target additionally requires the returned Du to be the weak
gradient of u with every coordinate in the claimed Lp space.

Weak tests use an everywhere positive lower bound on a representative of μ.
This represents ess inf μ > 0: an L-infinity function with positive essential
infimum can be changed on a null set to satisfy the displayed lower bound.
The integrals and all solution conditions depend only on almost-everywhere
classes on the cube.
-/

@[expose] public section


set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal ContDiff

/-! ## Periodic integration, test functions, and weak derivatives -/

namespace StationaryMFGChallenge.Periodic

open MeasureTheory
open scoped ENNReal ContDiff

variable {d : ℕ}

/-- Integer-lattice periodicity, imposed separately from integrability. -/
def IsPeriodic {X : Type*} (f : (Fin d → ℝ) → X) : Prop :=
  ∀ k : Fin d → ℤ, ∀ x, f (x + fun i => (k i : ℝ)) = f x

/-- The half-open fundamental cube `[0,1)^d`. -/
def UnitCube (d : ℕ) : Set (Fin d → ℝ) :=
  Set.pi Set.univ fun _ : Fin d => Set.Ico (0 : ℝ) 1

noncomputable def periodicIntegral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : (Fin d → ℝ) → E) : E :=
  ∫ x in UnitCube d, f x

noncomputable def eLpNormPer {E : Type*} [NormedAddCommGroup E]
    (p : ℝ≥0∞) (f : (Fin d → ℝ) → E) : ℝ≥0∞ :=
  MeasureTheory.eLpNorm f p (MeasureTheory.Measure.restrict volume (UnitCube d))

/-- Bare-function integrability on the cube; this does not assert periodicity. -/
def MemLpPer {E : Type*} [NormedAddCommGroup E]
    (p : ℝ≥0∞) (f : (Fin d → ℝ) → E) : Prop :=
  AEStronglyMeasurable f (MeasureTheory.Measure.restrict volume (UnitCube d)) ∧
    eLpNormPer p f < ⊤

/-- Smooth means `C^∞`, not analytic. -/
structure SmoothPeriodic (d : ℕ) where
  toFun : (Fin d → ℝ) → ℝ
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : ℕ∞ω) toFun
  periodic : IsPeriodic toFun

namespace SmoothPeriodic

instance : CoeFun (SmoothPeriodic d) (fun _ => (Fin d → ℝ) → ℝ) where
  coe := SmoothPeriodic.toFun

/-- The classical partial derivative remains a smooth periodic test function. -/
noncomputable def partialDeriv (i : Fin d) (φ : SmoothPeriodic d) :
    SmoothPeriodic d where
  toFun := fun x =>
    fderiv ℝ (φ : (Fin d → ℝ) → ℝ) x (Pi.basisFun ℝ (Fin d) i)
  smooth := by
    have hle : ((⊤ : ℕ∞) : ℕ∞ω) + 1 ≤ ((⊤ : ℕ∞) : ℕ∞ω) := by
      have h1 : ((⊤ : ℕ∞) : ℕ∞ω) + 1 = ((⊤ : ℕ∞) : ℕ∞ω) := by
        rw [show (1 : ℕ∞ω) = (((1 : ℕ∞) : ℕ∞ω)) from rfl,
            ← WithTop.coe_add]
        simp
      exact le_of_eq h1
    have h₁ : ContDiff ℝ ((⊤ : ℕ∞) : ℕ∞ω)
        (fderiv ℝ (φ : (Fin d → ℝ) → ℝ)) :=
      φ.smooth.fderiv_right (m := ((⊤ : ℕ∞) : ℕ∞ω)) hle
    exact h₁.clm_apply contDiff_const
  periodic := by
    intro k x
    set a : Fin d → ℝ := fun i => (k i : ℝ) with ha
    have hshift : (fun y => (φ : (Fin d → ℝ) → ℝ) (y + a))
        = (φ : (Fin d → ℝ) → ℝ) := by
      funext y
      exact φ.periodic k y
    have hfd : fderiv ℝ (fun y => (φ : (Fin d → ℝ) → ℝ) (y + a)) x
        = fderiv ℝ (φ : (Fin d → ℝ) → ℝ) (x + a) :=
      fderiv_comp_add_right (f := (φ : (Fin d → ℝ) → ℝ)) (a := a) (x := x)
    have hxeq : fderiv ℝ (φ : (Fin d → ℝ) → ℝ) (x + a)
        = fderiv ℝ (φ : (Fin d → ℝ) → ℝ) x := by
      have h := hfd
      rw [hshift] at h
      exact h.symm
    change fderiv ℝ (φ : (Fin d → ℝ) → ℝ) (x + a) (Pi.basisFun ℝ (Fin d) i)
        = fderiv ℝ (φ : (Fin d → ℝ) → ℝ) x (Pi.basisFun ℝ (Fin d) i)
    rw [hxeq]

end SmoothPeriodic

/-- The derivative witness is in `L¹`, with integration by parts against
all smooth periodic test functions. -/
def HasWeakDerivPer (i : Fin d) (f g : (Fin d → ℝ) → ℝ) : Prop :=
  MemLpPer 1 g ∧
    ∀ φ : SmoothPeriodic d,
      periodicIntegral (fun x => g x * (φ : (Fin d → ℝ) → ℝ) x) =
        - periodicIntegral
            (fun x => f x *
              ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x)

/-- As in the original project, this predicate alone puts the function in
`Lᵖ` and its weak derivatives in `L¹`; theorem statements add the required
`Lᵖ` bounds on the explicit derivative family separately. -/
def MemSobolevPer (p : ℝ≥0∞) (f : (Fin d → ℝ) → ℝ) : Prop :=
  MemLpPer p f ∧
    ∃ g : Fin d → ((Fin d → ℝ) → ℝ), ∀ i, HasWeakDerivPer i f (g i)

end StationaryMFGChallenge.Periodic

/-! ## Euclidean pairing and its continuous linear map -/

namespace StationaryMFGChallenge.Hamiltonian

variable {d : ℕ}

def euclideanDot {d : ℕ} (v w : Fin d → ℝ) : ℝ :=
  ∑ i, v i * w i

scoped infixl:72 " ⬝ " => euclideanDot

lemma euclideanDot_le_card_mul_norm
    (q v : Fin d → ℝ) : q ⬝ v ≤ (d : ℝ) * (‖q‖ * ‖v‖) := by
  unfold euclideanDot
  calc ∑ i, q i * v i
      ≤ ∑ _i : Fin d, ‖q‖ * ‖v‖ := by
        refine Finset.sum_le_sum ?_
        intro i _
        calc q i * v i
            ≤ |q i * v i| := le_abs_self _
          _ = |q i| * |v i| := abs_mul _ _
          _ ≤ ‖q‖ * ‖v‖ := by
              have hq : |q i| ≤ ‖q‖ := by
                simpa [Real.norm_eq_abs] using (norm_le_pi_norm q i)
              have hv : |v i| ≤ ‖v‖ := by
                simpa [Real.norm_eq_abs] using (norm_le_pi_norm v i)
              exact mul_le_mul hq hv (abs_nonneg _) (norm_nonneg _)
    _ = (d : ℝ) * (‖q‖ * ‖v‖) := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

/-- Absolute-value form of `euclideanDot_le_card_mul_norm`. -/
lemma abs_euclideanDot_le_card_mul_norm
    (q v : Fin d → ℝ) : |q ⬝ v| ≤ (d : ℝ) * ‖q‖ * ‖v‖ := by
  have h1 := euclideanDot_le_card_mul_norm (d := d) q v
  have h2 := euclideanDot_le_card_mul_norm (d := d) (-q) v
  have hneg : (-q) ⬝ v = -(q ⬝ v) := by
    unfold euclideanDot
    simp [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  rw [hneg] at h2
  -- `(-q) ⬝ v = -q ⬝ v ≤ d * ‖-q‖ * ‖v‖ = d * ‖q‖ * ‖v‖`.
  have hneg_norm : ‖(-q : Fin d → ℝ)‖ = ‖q‖ := by simp
  rw [hneg_norm] at h2
  have hub : q ⬝ v ≤ (d : ℝ) * ‖q‖ * ‖v‖ := by
    have := h1
    nlinarith [norm_nonneg q, norm_nonneg v]
  have hlb : -(q ⬝ v) ≤ (d : ℝ) * ‖q‖ * ‖v‖ := by
    have := h2
    nlinarith [norm_nonneg q, norm_nonneg v]
  exact abs_le.mpr ⟨by linarith, hub⟩

/-- The linear functional `w ↦ q ⬝ w`, with a completed continuity proof. -/
noncomputable def dotCLMHam (q : Fin d → ℝ) :
    (Fin d → ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun w => q ⬝ w
      map_add' := by
        intro x y
        unfold euclideanDot
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl ?_
        intro i _
        simp [Pi.add_apply]
        ring
      map_smul' := by
        intro a x
        unfold euclideanDot
        simp only [RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _
        simp [Pi.smul_apply, smul_eq_mul]
        ring }
    ((d : ℝ) * ‖q‖)
    (by
      intro x
      have hbnd := abs_euclideanDot_le_card_mul_norm (d := d) q x
      simpa [Real.norm_eq_abs] using hbnd)

@[simp] lemma dotCLMHam_apply (q w : Fin d → ℝ) :
    dotCLMHam q w = q ⬝ w := rfl

end StationaryMFGChallenge.Hamiltonian

/-! ## Hamiltonian hypotheses and boundary conventions -/

namespace StationaryMFGChallenge.Hamiltonian

open StationaryMFGChallenge.Periodic
open scoped StationaryMFGChallenge.Hamiltonian

variable {d : ℕ}

/-- Density integrability exponent: β + 1. -/
noncomputable def betaBar (β : ℝ) : ℝ := β + 1

/-- Gradient integrability exponent: α(β + 1)/β. -/
noncomputable def gammaBar (α β : ℝ) : ℝ := α * (β + 1) / β

/-- Conjugate exponent for the potential: (β + 1)/β. -/
noncomputable def betaBar' (β : ℝ) : ℝ := (β + 1) / β

/-- The paper's standing regularity (H1). The derivative field certifies the
meaning of the notation D_pH; it is not an additional smoothness hypothesis.
No values at nonpositive mass occur in this structure. -/
structure RegularityH
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)) : Prop where
  periodic_H : ∀ p m, 0 < m → IsPeriodic (fun x => H x p m)
  measurable_H : Measurable
    (fun (xpm : (Fin d → ℝ) × (Fin d → ℝ) × {m : ℝ // 0 < m}) =>
      H xpm.1 xpm.2.1 xpm.2.2)
  continuous_H_pm :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ContinuousOn (fun (pm : (Fin d → ℝ) × ℝ) => H x pm.1 pm.2)
        {pm | 0 < pm.2}
  hasFDerivAt_H_p :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ (p : Fin d → ℝ) (m : ℝ), 0 < m →
        HasFDerivAt (fun q : Fin d → ℝ => H x q m) (dotCLMHam (DpH x p m)) p
  continuous_DpH_pm :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ContinuousOn (fun (pm : (Fin d → ℝ) × ℝ) => DpH x pm.1 pm.2)
        {pm | 0 < pm.2}

/-- The boundary extension chooses the right-hand limit when the mass is nonpositive. -/
noncomputable def Hext
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ) :
    (Fin d → ℝ) → (Fin d → ℝ) → ℝ → WithTop ℝ :=
  fun x p m =>
    if 0 < m then ((H x p m : ℝ) : WithTop ℝ)
    else
      Classical.epsilon
        (fun L : WithTop ℝ =>
          Tendsto (fun m : ℝ => ((H x p m : ℝ) : WithTop ℝ))
            (𝓝[>] (0 : ℝ)) (𝓝 L))

/-- The continuous limiting flux in (H3). J is a representative of the
extension, with no zero-boundary or additional measurability assumption. -/
structure HypothesismDpHat0
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)) : Prop where
  J_of_pos : ∀ x p m, 0 < m → J x p m = m • DpH x p m
  tendsto_at_zero :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p : Fin d → ℝ,
      Tendsto (fun m : ℝ => m • DpH x p m)
        (𝓝[>] (0 : ℝ)) (𝓝 (J x p 0))
  continuous_J :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ContinuousOn (fun (pm : (Fin d → ℝ) × ℝ) => J x pm.1 pm.2)
        {pm | 0 ≤ pm.2}

/-- Lasry–Lions monotonicity, exactly the standing assumption (A1). -/
structure HypothesisMonotone
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)) : Prop
    extends RegularityH H DpH where
  monotone :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p₁ m₁ p₂ m₂, 0 < m₁ → 0 < m₂ →
        0 ≤ (-H x p₁ m₁ + H x p₂ m₂) * (m₁ - m₂)
              + (m₁ • DpH x p₁ m₁ - m₂ • DpH x p₂ m₂) ⬝ (p₁ - p₂)

/-- The three literal bounds in the simple power-growth assumption (A2). -/
structure HypothesisPowerGrowth
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    extends RegularityH H DpH where
  C : ℝ
  α : ℝ
  β : ℝ
  hC : 0 < C
  hα : 1 < α
  hβ : 0 < β
  upper :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ m, 0 < m → H x (0 : Fin d → ℝ) m ≤ -(m ^ β) / C + C
  DpH_upper :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p m, 0 < m →
        ‖DpH x p m‖ ≤ C * (‖p‖ ^ (α - 1) + m ^ (β - β / α) + 1)
  lower :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p m, 0 < m →
        H x p m ≥ (‖p‖ ^ α) / C - C * (m ^ β + 1)

/-- The three literal congestion-growth bounds and (H3), as in (A3). -/
structure HypothesisCongestionGrowth
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    extends RegularityH H DpH where
  C : ℝ
  α : ℝ
  β : ℝ
  τ : ℝ
  hC : 0 < C
  hα : 1 < α
  hβ : 0 < β
  hτ : 0 ≤ τ ∧ τ ≤ 1
  mDpHat0 : HypothesismDpHat0 DpH J
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

/-- The three literal weak-growth bounds in (A4). -/
structure HypothesisWeakGrowth
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    extends RegularityH H DpH where
  C : ℝ
  α : ℝ
  β : ℝ
  hC : 0 < C
  hα : 1 < α
  hβ : 0 < β
  f : (Fin d → ℝ) → ℝ → ℝ
  hf_continuous :
    ContinuousOn (fun pm : (Fin d → ℝ) × ℝ => f pm.1 pm.2)
      {pm | 0 < pm.2}
  upper :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ m, 0 < m → H x (0 : Fin d → ℝ) m ≤ -(m ^ β) / C + C
  DpH_upper :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p m, 0 < m → ‖DpH x p m‖ ≤ f p m
  lower :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p m, 0 < m →
        H x p m ≥ (‖p‖ ^ α) / C - C * (m ^ β + 1)

/-- Canonical simple-power flux: m • DpH, hence zero when m = 0. -/
def JsimpleExt {d : ℕ}
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (x p : Fin d → ℝ) (m : ℝ) : Fin d → ℝ :=
  if 0 < m then m • DpH x p m else 0

end StationaryMFGChallenge.Hamiltonian

/-! ## Strong solutions -/

namespace StationaryMFGChallenge.Solutions.Strong

open StationaryMFGChallenge.Periodic StationaryMFGChallenge.Hamiltonian
open scoped StationaryMFGChallenge.Hamiltonian

variable {d : ℕ}

def IsStrongSolution_HJB
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ) : Prop :=
  (∀ᵐ x ∂(volume.restrict (UnitCube d)),
      Hext H x (fun i => Du i x) (m x) ≤ ((V x - u x : ℝ) : WithTop ℝ)) ∧
  (∀ᵐ x ∂(volume.restrict (UnitCube d)),
      0 < m x →
        Hext H x (fun i => Du i x) (m x) = ((V x - u x : ℝ) : WithTop ℝ))

def mDpH_Integrable
    (J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m : (Fin d → ℝ) → ℝ) : Prop :=
  Integrable (fun x => J x (fun i => Du i x) (m x))
    (volume.restrict (UnitCube d))

def IsStrongSolution_Transport
    (V : (Fin d → ℝ) → ℝ)
    (J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ) : Prop :=
  let _ := V; let _ := u
  mDpH_Integrable (d := d) J Du m ∧
    ∀ φ : SmoothPeriodic d,
      ∫ x in UnitCube d,
          (m x - 1) * (φ : (Fin d → ℝ) → ℝ) x
            + J x (fun i => Du i x) (m x)
                ⬝ (fun i => (SmoothPeriodic.partialDeriv i φ : (Fin d → ℝ) → ℝ) x)
        ∂(volume : Measure (Fin d → ℝ)) = 0

def IsStrongSolution
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ) : Prop :=
  IsStrongSolution_HJB V H Du m u ∧ IsStrongSolution_Transport V J Du m u

end StationaryMFGChallenge.Solutions.Strong

/-! ## Weak solutions -/

namespace StationaryMFGChallenge.Solutions.Weak

open StationaryMFGChallenge.Periodic StationaryMFGChallenge.Hamiltonian
open scoped StationaryMFGChallenge.Hamiltonian

variable {d : ℕ}

structure IsWeakSolutionTestPair
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (μ υ : (Fin d → ℝ) → ℝ) : Prop where
  lower : ∃ c : ℝ, 0 < c ∧ ∀ x, c ≤ μ x
  μ_linf : MemLpPer (d := d) ⊤ μ
  υ_sob_linf : MemSobolevPer (d := d) ⊤ υ
  Dυ_linf : ∀ i, MemLpPer (d := d) ⊤ (Dυ i)
  Dυ_weak : ∀ i, StationaryMFGChallenge.Periodic.HasWeakDerivPer i υ (Dυ i)

def IsWeakSolution
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ) : Prop :=
  ∀ (Dυ : Fin d → (Fin d → ℝ) → ℝ) (μ υ : (Fin d → ℝ) → ℝ),
    IsWeakSolutionTestPair Dυ μ υ →
    0 ≤ ∫ x in UnitCube d,
          (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (μ x - m x)
            + μ x * (DpH x (fun i => Dυ i x) (μ x)
                      ⬝ (fun i => Dυ i x - Du i x))
            + (μ x - 1) * (υ x - u x)
        ∂(volume : Measure (Fin d → ℝ))

end StationaryMFGChallenge.Solutions.Weak

/-! Bridges from the copied definitions to the project. All these conversions are
proved; no change to the challenge's definitions or theorem types is needed. -/
namespace StationaryMFGChallenge.ComparatorBridge

variable {d : ℕ}
variable {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
variable {DpH J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}

noncomputable def smoothToProject (φ : Periodic.SmoothPeriodic d) :
    StationaryMFG.Periodic.SmoothPeriodic d :=
  ⟨φ.toFun, φ.smooth, φ.periodic⟩

noncomputable def smoothFromProject (φ : StationaryMFG.Periodic.SmoothPeriodic d) :
    Periodic.SmoothPeriodic d :=
  ⟨φ.toFun, φ.smooth, φ.periodic⟩

lemma weakDerivToProject {i : Fin d} {f g : (Fin d → ℝ) → ℝ}
    (h : Periodic.HasWeakDerivPer i f g) :
    StationaryMFG.Periodic.HasWeakDerivPer i f g :=
  ⟨h.1, fun φ => h.2 (smoothFromProject φ)⟩

lemma weakDerivFromProject {i : Fin d} {f g : (Fin d → ℝ) → ℝ}
    (h : StationaryMFG.Periodic.HasWeakDerivPer i f g) :
    Periodic.HasWeakDerivPer i f g :=
  ⟨h.1, fun φ => h.2 (smoothToProject φ)⟩

lemma sobolevToProject {p : ℝ≥0∞} {f : (Fin d → ℝ) → ℝ}
    (h : Periodic.MemSobolevPer p f) :
    StationaryMFG.Periodic.MemSobolevPer p f := by
  rcases h with ⟨hf, g, hg⟩
  exact ⟨hf, g, fun i => weakDerivToProject (hg i)⟩

lemma sobolevFromProject {p : ℝ≥0∞} {f : (Fin d → ℝ) → ℝ}
    (h : StationaryMFG.Periodic.MemSobolevPer p f) :
    Periodic.MemSobolevPer p f := by
  rcases h with ⟨hf, g, hg⟩
  exact ⟨hf, g, fun i => weakDerivFromProject (hg i)⟩

lemma regularityToProject (h : Hamiltonian.RegularityH H DpH) :
    StationaryMFG.Hamiltonian.Paper.RegularityH H DpH :=
  ⟨h.periodic_H, h.measurable_H, h.continuous_H_pm,
    h.hasFDerivAt_H_p, h.continuous_DpH_pm⟩

lemma monotoneToProject (h : Hamiltonian.HypothesisMonotone H DpH) :
    StationaryMFG.Hamiltonian.Paper.HypothesisMonotone H DpH :=
  ⟨regularityToProject h.toRegularityH, h.monotone⟩

noncomputable def powerToProject (h : Hamiltonian.HypothesisPowerGrowth H DpH) :
    StationaryMFG.Hamiltonian.Paper.HypothesisPowerGrowth H DpH :=
  ⟨regularityToProject h.toRegularityH, h.C, h.α, h.β, h.hC, h.hα, h.hβ,
    h.upper, h.DpH_upper, h.lower⟩

lemma fluxToProject (h : Hamiltonian.HypothesismDpHat0 DpH J) :
    StationaryMFG.Hamiltonian.PaperFluxExtension DpH J :=
  ⟨h.J_of_pos, h.tendsto_at_zero, h.continuous_J⟩

noncomputable def congestionToProject
    (h : Hamiltonian.HypothesisCongestionGrowth H DpH J) :
    StationaryMFG.Hamiltonian.Paper.HypothesisCongestionGrowth H DpH J :=
  ⟨regularityToProject h.toRegularityH, h.C, h.α, h.β, h.τ,
    h.hC, h.hα, h.hβ, h.hτ, fluxToProject h.mDpHat0, h.upper, h.DpH_upper, h.lower⟩

noncomputable def weakToProject (h : Hamiltonian.HypothesisWeakGrowth H DpH) :
    StationaryMFG.Hamiltonian.Paper.HypothesisWeakGrowth H DpH :=
  ⟨regularityToProject h.toRegularityH, h.C, h.α, h.β, h.hC, h.hα, h.hβ,
    h.f, h.hf_continuous, h.upper, h.DpH_upper, h.lower⟩

lemma strongFromProject {V m u : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (h : StationaryMFG.Solutions.PaperStrong.IsStrongSolution V H J Du m u) :
    Solutions.Strong.IsStrongSolution V H J Du m u :=
  ⟨h.1, h.2.1, fun φ => h.2.2 (smoothToProject φ)⟩

lemma weakTestPairToProject {Dυ : Fin d → (Fin d → ℝ) → ℝ}
    {μ υ : (Fin d → ℝ) → ℝ}
    (h : Solutions.Weak.IsWeakSolutionTestPair Dυ μ υ) :
    StationaryMFG.Solutions.Weak.IsWeakSolutionTestPair Dυ μ υ :=
  ⟨h.lower, h.μ_linf, sobolevToProject h.υ_sob_linf, h.Dυ_linf,
    fun i => weakDerivToProject (h.Dυ_weak i)⟩

lemma weakSolutionFromProject {V m u : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (h : StationaryMFG.Solutions.Weak.IsWeakSolution V H DpH Du m u) :
    Solutions.Weak.IsWeakSolution V H DpH Du m u :=
  fun Dυ μ υ ht => h Dυ μ υ (weakTestPairToProject ht)

end StationaryMFGChallenge.ComparatorBridge

/-! ## Challenge 1: existence of a strong solution under simple power growth. -/

namespace StationaryMFGChallenge.Theorems.SimplePower

open StationaryMFGChallenge.Periodic StationaryMFGChallenge.Hamiltonian
open StationaryMFGChallenge.Solutions.Strong StationaryMFGChallenge.Solutions.Weak

variable {d : ℕ}

/-- Challenge 1: existence of a strong solution under simple power growth.
The assumptions are those of the manuscript, with the representation choices above. -/

theorem thm_main_simplePowerGrowth_paper
    [Fact (0 < d)]
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hmon : HypothesisMonotone H DpH)
    (hpow : HypothesisPowerGrowth H DpH)
    (hV : Periodic.MemLpPer
            (ENNReal.ofReal (Hamiltonian.betaBar' hpow.β)) V)
    (hVPer : Periodic.IsPeriodic V)
    :
    ∃ (m u : (Fin d → ℝ) → ℝ) (Du : Fin d → (Fin d → ℝ) → ℝ),
      IsStrongSolution V H (StationaryMFGChallenge.Hamiltonian.JsimpleExt DpH) Du m u
        ∧ Periodic.MemLpPer
            (ENNReal.ofReal (Hamiltonian.betaBar hpow.β)) m
        ∧ Periodic.MemSobolevPer
            (ENNReal.ofReal (Hamiltonian.gammaBar hpow.α hpow.β)) u
        ∧ (∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ m x)
        ∧ (∀ i, Periodic.HasWeakDerivPer (d := d) i u (Du i))
        ∧ (∀ i, Periodic.MemLpPer
            (ENNReal.ofReal (Hamiltonian.gammaBar hpow.α hpow.β)) (Du i)) := by
  let hp := ComparatorBridge.powerToProject hpow
  obtain ⟨m, u, Du, hs, hm, hu, hnonneg, hDu, hDulp⟩ :=
    StationaryMFG.Theorems.SimplePower.thm_main_simplePowerGrowth_faithful
      V H DpH (ComparatorBridge.monotoneToProject hmon) hp hV
  exact ⟨m, u, Du, ComparatorBridge.strongFromProject hs, hm,
    ComparatorBridge.sobolevFromProject hu, hnonneg,
    fun i => ComparatorBridge.weakDerivFromProject (hDu i), hDulp⟩

end StationaryMFGChallenge.Theorems.SimplePower

/-! ## Challenge 2: existence of a strong solution under congestion growth. -/

namespace StationaryMFGChallenge.Theorems.Congestion

open StationaryMFGChallenge.Periodic StationaryMFGChallenge.Hamiltonian
open StationaryMFGChallenge.Solutions.Strong StationaryMFGChallenge.Solutions.Weak

variable {d : ℕ}

/-- Challenge 2: existence of a strong solution under congestion growth.
The assumptions are those of the manuscript, with the representation choices above. -/

theorem thm_main_congestion_growth_paper
    [Fact (0 < d)]
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hmon : Hamiltonian.HypothesisMonotone (d := d) H DpH)
    (hcong : Hamiltonian.HypothesisCongestionGrowth (d := d) H DpH J)
    (hV : Periodic.MemLpPer
            (ENNReal.ofReal (StationaryMFGChallenge.Hamiltonian.betaBar' hcong.β)) V)
    (hVPer : Periodic.IsPeriodic V)
    :
    ∃ (m u : (Fin d → ℝ) → ℝ) (Du : Fin d → (Fin d → ℝ) → ℝ),
      Solutions.Strong.IsStrongSolution V H J Du m u
        ∧ Periodic.MemLpPer (ENNReal.ofReal (hcong.β + 1)) m
        ∧ Periodic.MemSobolevPer
            (ENNReal.ofReal
              (StationaryMFGChallenge.Hamiltonian.gammaBar hcong.α hcong.β)) u
        ∧ (∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
              0 ≤ m x)
        ∧ (∀ i, Periodic.HasWeakDerivPer i u (Du i))
        ∧ (∀ i, Periodic.MemLpPer
                  (ENNReal.ofReal
                    (StationaryMFGChallenge.Hamiltonian.gammaBar hcong.α hcong.β))
                  (Du i)) := by
  let hc := ComparatorBridge.congestionToProject hcong
  obtain ⟨m, u, Du, hs, hm, hu, hnonneg, hDu, hDulp⟩ :=
    StationaryMFG.Theorems.Congestion.thm_main_congestion_growth_faithful
      V H DpH J (ComparatorBridge.monotoneToProject hmon) hc hV hVPer
  exact ⟨m, u, Du, ComparatorBridge.strongFromProject hs, hm,
    ComparatorBridge.sobolevFromProject hu, hnonneg,
    fun i => ComparatorBridge.weakDerivFromProject (hDu i), hDulp⟩

end StationaryMFGChallenge.Theorems.Congestion

/-! ## Challenge 3: existence of a weak solution under weak power growth. -/

namespace StationaryMFGChallenge.Theorems.InfimalConvolution

open StationaryMFGChallenge.Periodic StationaryMFGChallenge.Hamiltonian
open StationaryMFGChallenge.Solutions.Strong StationaryMFGChallenge.Solutions.Weak

variable {d : ℕ}

/-- Challenge 3: existence of a weak solution under weak power growth.
The assumptions are those of the manuscript, with the representation choices above. -/

theorem thm_main_weak_power_growth_paper
    [hdFact : Fact (0 < d)]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (V : (Fin d → ℝ) → ℝ)
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hweak.β + 1) / hweak.β)) V)
    (hVPer : Periodic.IsPeriodic V) :
    ∃ (m u : (Fin d → ℝ) → ℝ) (Du : Fin d → (Fin d → ℝ) → ℝ),
      IsWeakSolution V H DpH Du m u
        ∧ MemLpPer (ENNReal.ofReal (hweak.β + 1)) m
        ∧ MemSobolevPer (ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β)) u
        ∧ (∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ m x)
        ∧ (∀ i, HasWeakDerivPer (d := d) i u (Du i))
        ∧ (∀ i, MemLpPer (d := d)
              (ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β)) (Du i)) := by
  let hw := ComparatorBridge.weakToProject hweak
  obtain ⟨m, u, Du, hs, hm, hu, hnonneg, hDu, hDulp⟩ :=
    StationaryMFG.Theorems.InfimalConvolution.thm_main_weak_power_growth_faithful
      V (ComparatorBridge.monotoneToProject hmon) hw hV
  exact ⟨m, u, Du, ComparatorBridge.weakSolutionFromProject hs, hm,
    ComparatorBridge.sobolevFromProject hu, hnonneg,
    fun i => ComparatorBridge.weakDerivFromProject (hDu i), hDulp⟩

end StationaryMFGChallenge.Theorems.InfimalConvolution

end
