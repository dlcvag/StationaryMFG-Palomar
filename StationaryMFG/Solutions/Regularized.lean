module

public import StationaryMFG.Solutions.MFGOperator
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

@[expose] public section

/-!
# The regularized MFG operator `A_ε`

This module defines the **regularized MFG operator** `A_ε` of paper
`Source/FGU-monotone_revised.tex` line 925 (equation `defAepsi`):
```
⟨A_ε[m, u], (η, ν)⟩
   = ∫ (-u - H(x, Du, m) + V(x)) η dx
   + ∫ (m · D_pH(x, Du, m) · Dν + (m - 1) ν) dx
   + ε ∫ (|Du|^{γ̄-2} Du · Dν + |u|^{γ̄-2} u ν) dx.
```
The first two integrals are precisely `Solutions.MFG.mfgOperatorPair` from
`MFGOperator.lean`, so we define `A_ε` by *adding* the third — the
γ̄-Laplacian Gateaux derivative term — to the previously-landed MFG
operator pairing.

Following the bare-function design of `docs/CONVENTIONS.md` §1b, we
represent the operator via its **action** on a test pair `(η, ν, Dν)`,
exactly as `MFGOperator.lean` does for `A`. Concretely we expose:

* `gateauxWpPair γBar Dυ υ Dν ν` — the explicit integral
  `∫ (|Dυ|^{γBar-2} Dυ · Dν + |υ|^{γBar-2} υ ν) dx`. This is the
  Gateaux derivative of `u ↦ (1/γ̄)‖u‖_{W^{1,γ̄}}^{γ̄}` paired against
  `(ν, Dν)` (paper line 934).
* `mfgOperatorEpsPair γBar ε V H DpH Dυ μ υ Dν η ν` — the full
  regularized pairing, defined as
  `mfgOperatorPair V H DpH Dυ μ υ Dν η ν + ε · gateauxWpPair γBar Dυ υ Dν ν`.
* `mfgOperatorEpsPair_zero_eq` — at `ε = 0`, recovers
  `mfgOperatorPair`.
* `mfgOperatorEpsPair_pairing_eq` — the algebraic identity used
  verbatim by Phase 4's `infra:P4-coerc-identity` (line 947): the
  pairing against `((μ, υ) - (m, u))` is the explicit integrand of
  `defAepsi` with `η = μ - m`, `ν = υ - u`, `Dν = Dυ - Du`.

The exponent `γBar : ℝ` and the regularization parameter `ε : ℝ` are
bare reals; positivity / `1 ≤ γBar` constraints are imposed at use
sites in Phase 4.

## Encoding the `|·|^{γ̄-2} ·` factor

We encode `|v|^{γ̄ - 2}` for a Euclidean vector `v : Fin d → ℝ` as
`(v ⬝ v) ^ ((γ̄ - 2) / 2)` (using `Real.rpow`); equivalently
`(‖v‖²)^{(γ̄-2)/2}`. For a scalar `s : ℝ`, `|s|^{γ̄-2}` is `|s|^{γ̄-2}`
via `Real.rpow`. Both definitions are exact when `γ̄ ≥ 2` (the
relevant range, since `γ̄ > 1` and the regularization is used to land
in `W^{1,γ̄}`); the singularity at `v = 0` for `1 < γ̄ < 2` is handled
implicitly by `Real.rpow` (`0 ^ s = 0` for `s > 0`).

## Paper reference

`Source/FGU-monotone_revised.tex`, eq. `defAepsi` (line 925), and the
Gateaux-derivative remark on line 934.
-/

noncomputable section

namespace StationaryMFG
namespace Solutions
namespace MFG

open MeasureTheory Set
open StationaryMFG.Periodic
open StationaryMFG.Hamiltonian
open scoped ENNReal NNReal

variable {d : ℕ}

/-! ## The γ̄-Laplacian Gateaux pairing -/

/-- The scalar weight `|s|^{γBar - 2}`, encoded via `Real.rpow`. -/
@[inline] def absPowMinusTwo (γBar s : ℝ) : ℝ := |s| ^ (γBar - 2)

/-- The vector weight `|v|^{γBar - 2}` for `v : Fin d → ℝ`, encoded as
`(v ⬝ v) ^ ((γBar - 2) / 2) = (‖v‖²)^{(γBar - 2)/2}`. -/
@[inline] def vecAbsPowMinusTwo (γBar : ℝ) (v : Fin d → ℝ) : ℝ :=
  (v ⬝ v) ^ ((γBar - 2) / 2)

/-- **The γ̄-Laplacian Gateaux pairing** of paper line 925, third line:
```
gateauxWpPair γBar Dυ υ Dν ν
   = ∫_{𝕋^d} (|Dυ|^{γBar-2} Dυ · Dν + |υ|^{γBar-2} υ · ν) dx.
```
This is the Gateaux derivative of the convex functional
`u ↦ (1/γ̄)‖u‖_{W^{1,γ̄}}^{γ̄}` paired against the test `(ν, Dν)`
(paper line 934). The factor `ε` is supplied by the caller. -/
def gateauxWpPair (γBar : ℝ)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (υ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (ν : (Fin d → ℝ) → ℝ) : ℝ :=
  ∫ x in UnitCube d,
      vecAbsPowMinusTwo γBar (fun i => Dυ i x)
            * ((fun i => Dυ i x) ⬝ (fun i => Dν i x))
        + absPowMinusTwo γBar (υ x) * (υ x * ν x)
    ∂(volume : Measure (Fin d → ℝ))

/-! ## Bridge: substituting the test pair `(μ, υ) - (m, u)` -/

/-- Substituting the test pair `(η, ν, Dν) = ((μ - m), (υ - u), (Dυ - Du))`
into `gateauxWpPair`, we obtain the explicit integrand displayed at
paper line 925 / 947 (the third line of `defAepsi`). The proof is the
trivial pointwise rewrite `(Dυ - Du) i x = Dυ i x - Du i x`. -/
theorem gateauxWpPair_pairing_eq (γBar : ℝ)
    (Dυ Du : Fin d → (Fin d → ℝ) → ℝ)
    (υ u : (Fin d → ℝ) → ℝ) :
    gateauxWpPair γBar Dυ υ
        (fun i x => Dυ i x - Du i x) (υ - u) =
      ∫ x in UnitCube d,
          vecAbsPowMinusTwo γBar (fun i => Dυ i x)
                * ((fun i => Dυ i x) ⬝ (fun i => Dυ i x - Du i x))
            + absPowMinusTwo γBar (υ x) * (υ x * (υ x - u x))
        ∂(volume : Measure (Fin d → ℝ)) := by
  unfold gateauxWpPair
  refine setIntegral_congr_fun measurableSet_unitCube ?_
  intro x _
  simp [Pi.sub_apply]

/-! ## The regularized MFG operator pairing `A_ε`

We re-introduce the same `V`, `H`, `DpH` ambient datums as in
`MFGOperator.lean` so the consumer signatures line up. -/

variable (V : (Fin d → ℝ) → ℝ)
variable (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
variable (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))

/-- **Pairing of the regularized MFG operator `A_ε(μ, υ)` with a test
pair `(η, ν, Dν)`.**

Implements `defAepsi` (paper line 925) by **adding** the
γ̄-Laplacian Gateaux pairing to `mfgOperatorPair`:
```
⟨A_ε(μ, υ), (η, ν, Dν)⟩ = ⟨A(μ, υ), (η, ν, Dν)⟩
   + ε ∫ (|Dυ|^{γBar-2} Dυ · Dν + |υ|^{γBar-2} υ · ν) dx.
```
Note `γBar : ℝ` and `ε : ℝ` are bare-real parameters; positivity is
imposed at use sites (Phase 4 / Phase 6). -/
def mfgOperatorEpsPair (γBar ε : ℝ)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (μ υ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ) : ℝ :=
  mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ Dν η ν
    + ε * gateauxWpPair γBar Dυ υ Dν ν

/-- **`A_ε` at `ε = 0` recovers `A`.** Specialization that lets Phase 4
unfold the regularized operator into the unregularized one when
passing to the limit `ε → 0`. -/
theorem mfgOperatorEpsPair_zero_eq (γBar : ℝ)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (μ υ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ) :
    mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH) γBar 0 Dυ μ υ Dν η ν
      = mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ Dν η ν := by
  unfold mfgOperatorEpsPair
  simp

/-- **Pairing identity for `A_ε`** (paper line 925, `defAepsi`,
substituted at the test pair `(η, ν, Dν) = (μ - m, υ - u, Dυ - Du)`).

The pairing of `A_ε(μ, υ)` against the difference test pair equals the
explicit integrand displayed in `defAepsi`; this is the form consumed
verbatim by `infra:P4-coerc-identity` (paper line 947) when computing
`⟨A_ε[m, u] - A_ε[1, 0], (m - 1, u)⟩`. The proof reduces to the
unregularized identity (`mfgOperator_pairing_eq`) plus the trivial
pointwise rewrite of the Gateaux term. -/
theorem mfgOperatorEpsPair_pairing_eq (γBar ε : ℝ)
    (Dυ Du : Fin d → (Fin d → ℝ) → ℝ)
    (μ υ m u : (Fin d → ℝ) → ℝ) :
    mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH) γBar ε Dυ μ υ
        (fun i x => Dυ i x - Du i x) (μ - m) (υ - u) =
      (∫ x in UnitCube d,
          (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (μ x - m x)
            + μ x * (DpH x (fun i => Dυ i x) (μ x)
                      ⬝ (fun i => Dυ i x - Du i x))
            + (μ x - 1) * (υ x - u x)
        ∂(volume : Measure (Fin d → ℝ)))
      + ε * (∫ x in UnitCube d,
            vecAbsPowMinusTwo γBar (fun i => Dυ i x)
                  * ((fun i => Dυ i x) ⬝ (fun i => Dυ i x - Du i x))
              + absPowMinusTwo γBar (υ x) * (υ x * (υ x - u x))
          ∂(volume : Measure (Fin d → ℝ))) := by
  unfold mfgOperatorEpsPair
  rw [mfgOperator_pairing_eq (V := V) (H := H) (DpH := DpH)
        Dυ Du μ υ m u,
      gateauxWpPair_pairing_eq γBar Dυ Du υ u]

/-! ## a.e.-congruence for `gateauxWpPair` and `mfgOperatorEpsPair`

These are the ε-form analogues of `mfgOperatorPair_congr_ae` /
`_congr_ae_primal` from `MFGOperator.lean`. They form the second half
of the substitution layer: every Phase-4 closure proof that switches
between an `Lp.coeFn` representative and an `AEPeriodicRep.rep` for
the regularized pairing should call these lemmas. -/

/-- **Test-triple a.e.-congruence** for `gateauxWpPair` (ν, Dν vary). -/
theorem gateauxWpPair_congr_ae (γBar : ℝ)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (υ : (Fin d → ℝ) → ℝ)
    (Dν₁ Dν₂ : Fin d → (Fin d → ℝ) → ℝ)
    (ν₁ ν₂ : (Fin d → ℝ) → ℝ)
    (hDν : ∀ i, Dν₁ i =ᵐ[volume.restrict (UnitCube d)] Dν₂ i)
    (hν : ν₁ =ᵐ[volume.restrict (UnitCube d)] ν₂) :
    gateauxWpPair γBar Dυ υ Dν₁ ν₁ = gateauxWpPair γBar Dυ υ Dν₂ ν₂ := by
  unfold gateauxWpPair
  refine integral_congr_ae ?_
  have hDν' : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ i, Dν₁ i x = Dν₂ i x := by
    rw [ae_all_iff]; exact hDν
  filter_upwards [hν, hDν'] with x hx_ν hx_Dν
  have hpt : (fun i => Dν₁ i x) = (fun i => Dν₂ i x) := by
    funext i; exact hx_Dν i
  rw [hx_ν, hpt]

/-- **Primal-triple a.e.-congruence** for `gateauxWpPair` (Dυ, υ
vary). -/
theorem gateauxWpPair_congr_ae_primal (γBar : ℝ)
    (Dυ₁ Dυ₂ : Fin d → (Fin d → ℝ) → ℝ)
    (υ₁ υ₂ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (ν : (Fin d → ℝ) → ℝ)
    (hDυ : ∀ i, Dυ₁ i =ᵐ[volume.restrict (UnitCube d)] Dυ₂ i)
    (hυ : υ₁ =ᵐ[volume.restrict (UnitCube d)] υ₂) :
    gateauxWpPair γBar Dυ₁ υ₁ Dν ν = gateauxWpPair γBar Dυ₂ υ₂ Dν ν := by
  unfold gateauxWpPair
  refine integral_congr_ae ?_
  have hDυ' : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ i, Dυ₁ i x = Dυ₂ i x := by
    rw [ae_all_iff]; exact hDυ
  filter_upwards [hυ, hDυ'] with x hx_υ hx_Dυ
  have hpt : (fun i => Dυ₁ i x) = (fun i => Dυ₂ i x) := by
    funext i; exact hx_Dυ i
  rw [hx_υ, hpt]

/-- **Test-triple a.e.-congruence** for `mfgOperatorEpsPair`. -/
theorem mfgOperatorEpsPair_congr_ae (γBar ε : ℝ)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (μ υ : (Fin d → ℝ) → ℝ)
    (Dν₁ Dν₂ : Fin d → (Fin d → ℝ) → ℝ)
    (η₁ η₂ ν₁ ν₂ : (Fin d → ℝ) → ℝ)
    (hDν : ∀ i, Dν₁ i =ᵐ[volume.restrict (UnitCube d)] Dν₂ i)
    (hη : η₁ =ᵐ[volume.restrict (UnitCube d)] η₂)
    (hν : ν₁ =ᵐ[volume.restrict (UnitCube d)] ν₂) :
    mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH) γBar ε Dυ μ υ Dν₁ η₁ ν₁
      = mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH) γBar ε Dυ μ υ Dν₂ η₂ ν₂ := by
  unfold mfgOperatorEpsPair
  rw [mfgOperatorPair_congr_ae V H DpH Dυ μ υ Dν₁ Dν₂ η₁ η₂ ν₁ ν₂ hDν hη hν,
      gateauxWpPair_congr_ae γBar Dυ υ Dν₁ Dν₂ ν₁ ν₂ hDν hν]

/-- **Primal-triple a.e.-congruence** for `mfgOperatorEpsPair`. -/
theorem mfgOperatorEpsPair_congr_ae_primal (γBar ε : ℝ)
    (Dυ₁ Dυ₂ : Fin d → (Fin d → ℝ) → ℝ)
    (μ₁ μ₂ υ₁ υ₂ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ)
    (hDυ : ∀ i, Dυ₁ i =ᵐ[volume.restrict (UnitCube d)] Dυ₂ i)
    (hμ : μ₁ =ᵐ[volume.restrict (UnitCube d)] μ₂)
    (hυ : υ₁ =ᵐ[volume.restrict (UnitCube d)] υ₂) :
    mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH) γBar ε Dυ₁ μ₁ υ₁ Dν η ν
      = mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH) γBar ε Dυ₂ μ₂ υ₂ Dν η ν := by
  unfold mfgOperatorEpsPair
  rw [mfgOperatorPair_congr_ae_primal V H DpH Dυ₁ Dυ₂ μ₁ μ₂ υ₁ υ₂ Dν η ν hDυ hμ hυ,
      gateauxWpPair_congr_ae_primal γBar Dυ₁ Dυ₂ υ₁ υ₂ Dν ν hDυ hυ]

/-- **Hamiltonian-carrier a.e.-congruence** for `mfgOperatorEpsPair`
(D2b-2a).

The γ̄-Laplacian Gateaux term `gateauxWpPair` is carrier-free, so the
carrier `(H, DpH)` enters `mfgOperatorEpsPair` only through
`mfgOperatorPair`. Thus the carrier swap reduces to
`mfgOperatorPair_congr_H_ae` (the Gateaux term is unchanged, `rfl`).
The intended use is the `HdeltaK0 ↔ HdeltaPos` swap on the
strict-positivity cone `K_Aepsi`, where the two carriers agree a.e. in
the positive-density integrand. -/
theorem mfgOperatorEpsPair_congr_H_ae (γBar ε : ℝ)
    (H' : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH' : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (μ υ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ)
    (hH : (fun x => H x (fun i => Dυ i x) (μ x))
            =ᵐ[volume.restrict (UnitCube d)]
          (fun x => H' x (fun i => Dυ i x) (μ x)))
    (hDpH : (fun x => DpH x (fun i => Dυ i x) (μ x))
              =ᵐ[volume.restrict (UnitCube d)]
            (fun x => DpH' x (fun i => Dυ i x) (μ x))) :
    mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH) γBar ε Dυ μ υ Dν η ν
      = mfgOperatorEpsPair (V := V) (H := H') (DpH := DpH') γBar ε Dυ μ υ Dν η ν := by
  unfold mfgOperatorEpsPair
  rw [mfgOperatorPair_congr_H_ae V H DpH H' DpH' Dυ μ υ Dν η ν hH hDpH]

/-! ## Sanity-check `example` -/

example
    (γBar ε : ℝ)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (μ υ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ) :
    mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH) γBar ε Dυ μ υ Dν η ν
      = mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH) γBar ε Dυ μ υ Dν η ν :=
  mfgOperatorEpsPair_congr_ae (V := V) (H := H) (DpH := DpH) γBar ε Dυ μ υ Dν Dν η η ν ν
    (fun _ => Filter.EventuallyEq.refl _ _)
    (Filter.EventuallyEq.refl _ _)
    (Filter.EventuallyEq.refl _ _)

/-- **Sanity-check** for the carrier congr: the reflexive instance. -/
example
    (γBar ε : ℝ)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (μ υ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ) :
    mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH) γBar ε Dυ μ υ Dν η ν
      = mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH) γBar ε Dυ μ υ Dν η ν :=
  mfgOperatorEpsPair_congr_H_ae (V := V) (H := H) (DpH := DpH) γBar ε H DpH Dυ μ υ Dν η ν
    (Filter.EventuallyEq.refl _ _)
    (Filter.EventuallyEq.refl _ _)

/-! ## Pointwise scalar/vector power monotonicity (`infra-P4-monotone-power-grad`)

Pointwise monotonicity of the scalar map `t ↦ |t|^{γBar-2} · t` and
the vector map `v ↦ |v|^{γBar-2} · v` for `γBar ≥ 2`. These are the
standard `p`-Laplacian-type inequalities used by the `γBar`-Laplacian
Gateaux derivative `gateauxWpPair`. They are independent of the MFG
content — pure pointwise convex analysis on `ℝ` and `ℝ^d`.

Both follow from the convexity of `t ↦ |t|^γ / γ` (resp.
`v ↦ |v|^γ / γ`); we give direct elementary proofs that avoid the
convex-analysis machinery, by combining monotonicity of
`t ↦ t^{γ-1}` on `[0,∞)` (Mathlib's
`Real.monotoneOn_rpow_Ici_of_exponent_nonneg`) with Cauchy-Schwarz
(`Finset.sum_mul_sq_le_sq_mul_sq`).

Naming follows `docs/TASKS/in_flight/infra-P4-monotone-power-grad.md`:
`rpow_signed_mono_scalar` and `rpow_signed_mono_vec`. -/

/-- The scalar signed power map `t ↦ |t|^{γBar-2} · t`, which is the
Gateaux derivative of `t ↦ |t|^{γBar} / γBar` (modulo the
`γBar = 0` corner). Encoded via `Real.rpow`. -/
@[inline] def signedRpow (γBar t : ℝ) : ℝ := absPowMinusTwo γBar t * t

/-- The vector signed power map `v ↦ |v|^{γBar-2} · v` on `Fin d → ℝ`,
which is the Gateaux derivative of `v ↦ |v|^{γBar} / γBar`. Encoded
coordinate-wise as `vecAbsPowMinusTwo γBar v • v`. -/
@[inline] def vecSignedRpow (γBar : ℝ) (v : Fin d → ℝ) : Fin d → ℝ :=
  fun i => vecAbsPowMinusTwo γBar v * v i

@[simp] lemma signedRpow_zero (γBar : ℝ) : signedRpow γBar 0 = 0 := by
  simp [signedRpow]

@[simp] lemma vecSignedRpow_zero (γBar : ℝ) :
    vecSignedRpow (d := d) γBar 0 = 0 := by
  funext i
  simp [vecSignedRpow]

/-- For `γBar > 1`, on `[0, ∞)` the signed power map agrees with
`t ↦ t^{γBar-1}`. -/
lemma signedRpow_eq_rpow_sub_one_of_nonneg
    {γBar t : ℝ} (hγ : 1 < γBar) (ht : 0 ≤ t) :
    signedRpow γBar t = t ^ (γBar - 1) := by
  rcases eq_or_lt_of_le ht with rfl | ht_pos
  · -- t = 0
    have hexp : 0 < γBar - 1 := by linarith
    simp [signedRpow, absPowMinusTwo, Real.zero_rpow hexp.ne']
  · have habs : |t| = t := abs_of_pos ht_pos
    have hsplit : t ^ (γBar - 1) = t ^ (γBar - 2) * t := by
      have : t ^ (γBar - 2 + 1) = t ^ (γBar - 2) * t ^ (1 : ℝ) :=
        Real.rpow_add ht_pos (γBar - 2) 1
      simpa [show γBar - 2 + 1 = γBar - 1 by ring, Real.rpow_one]
        using this
    simp [signedRpow, absPowMinusTwo, habs, hsplit]

/-- For `γBar > 1`, on `(-∞, 0]` we have `signedRpow γBar t = -(-t)^{γBar-1}`. -/
lemma signedRpow_neg_eq_of_nonpos
    {γBar t : ℝ} (hγ : 1 < γBar) (ht : t ≤ 0) :
    signedRpow γBar t = -((-t) ^ (γBar - 1)) := by
  have hnt : 0 ≤ -t := by linarith
  rcases eq_or_lt_of_le hnt with hnt0 | hnt_pos
  · have ht0 : t = 0 := by linarith [hnt0]
    have hexp : 0 < γBar - 1 := by linarith
    simp [signedRpow, ht0, hexp.ne']
  · have hpos : 0 < -t := hnt_pos
    have habs : |t| = -t := by
      have : t < 0 := by linarith
      simpa [abs_of_neg this]
    have hsplit : (-t) ^ (γBar - 1) = (-t) ^ (γBar - 2) * (-t) := by
      have : (-t) ^ (γBar - 2 + 1) = (-t) ^ (γBar - 2) * (-t) ^ (1 : ℝ) :=
        Real.rpow_add hpos (γBar - 2) 1
      simpa [show γBar - 2 + 1 = γBar - 1 by ring, Real.rpow_one]
        using this
    simp [signedRpow, absPowMinusTwo, habs, hsplit]

/-- `signedRpow γBar t ≥ 0` whenever `t ≥ 0` and `γBar > 1`. -/
lemma signedRpow_nonneg_of_nonneg
    {γBar t : ℝ} (hγ : 1 < γBar) (ht : 0 ≤ t) :
    0 ≤ signedRpow γBar t := by
  rw [signedRpow_eq_rpow_sub_one_of_nonneg hγ ht]
  exact Real.rpow_nonneg ht _

/-- `signedRpow γBar t ≤ 0` whenever `t ≤ 0` and `γBar > 1`. -/
lemma signedRpow_nonpos_of_nonpos
    {γBar t : ℝ} (hγ : 1 < γBar) (ht : t ≤ 0) :
    signedRpow γBar t ≤ 0 := by
  rw [signedRpow_neg_eq_of_nonpos hγ ht]
  have hnt : 0 ≤ -t := by linarith
  have : 0 ≤ (-t) ^ (γBar - 1) := Real.rpow_nonneg hnt _
  linarith

/-- The signed-power map is monotone on `ℝ` for `γBar > 1`. -/
lemma signedRpow_mono {γBar : ℝ} (hγ : 1 < γBar) :
    Monotone (signedRpow γBar) := by
  intro s t hst
  -- Case on the signs of s and t.
  rcases le_or_gt 0 s with hs | hs
  · -- s ≥ 0, hence t ≥ s ≥ 0.
    have ht : 0 ≤ t := le_trans hs hst
    rw [signedRpow_eq_rpow_sub_one_of_nonneg hγ hs,
        signedRpow_eq_rpow_sub_one_of_nonneg hγ ht]
    have hexp : 0 ≤ γBar - 1 := by linarith
    exact Real.rpow_le_rpow hs hst hexp
  · -- s < 0
    rcases le_or_gt 0 t with ht | ht
    · -- s < 0 ≤ t. signedRpow s ≤ 0 ≤ signedRpow t.
      have h1 : signedRpow γBar s ≤ 0 :=
        signedRpow_nonpos_of_nonpos hγ hs.le
      have h2 : 0 ≤ signedRpow γBar t :=
        signedRpow_nonneg_of_nonneg hγ ht
      linarith
    · -- s ≤ t < 0. Use the negative-side identity.
      have hs_le : s ≤ 0 := hs.le
      have ht_le : t ≤ 0 := ht.le
      rw [signedRpow_neg_eq_of_nonpos hγ hs_le,
          signedRpow_neg_eq_of_nonpos hγ ht_le]
      -- Need -(-s)^{γ-1} ≤ -(-t)^{γ-1}, i.e. (-t)^{γ-1} ≤ (-s)^{γ-1}.
      have hnt : 0 ≤ -t := by linarith
      have hns : 0 ≤ -s := by linarith
      have hflip : -t ≤ -s := by linarith
      have hexp : 0 ≤ γBar - 1 := by linarith
      have : (-t) ^ (γBar - 1) ≤ (-s) ^ (γBar - 1) :=
        Real.rpow_le_rpow hnt hflip hexp
      linarith

/-- **Scalar pointwise monotonicity** of the signed-power map.

For `γBar > 1` and any `s, t : ℝ`,
`(|t|^{γBar-2}·t − |s|^{γBar-2}·s) · (t − s) ≥ 0`.

This is the gradient-form of convexity of `t ↦ |t|^{γBar}/γBar`. -/
theorem rpow_signed_mono_scalar
    {γBar : ℝ} (hγ : 1 < γBar) (s t : ℝ) :
    0 ≤ (signedRpow γBar t - signedRpow γBar s) * (t - s) := by
  rcases le_total s t with hst | hts
  · have h1 : signedRpow γBar s ≤ signedRpow γBar t :=
      signedRpow_mono hγ hst
    have h2 : 0 ≤ t - s := by linarith
    have h3 : 0 ≤ signedRpow γBar t - signedRpow γBar s := by linarith
    exact mul_nonneg h3 h2
  · have h1 : signedRpow γBar t ≤ signedRpow γBar s :=
      signedRpow_mono hγ hts
    have h2 : t - s ≤ 0 := by linarith
    have h3 : signedRpow γBar t - signedRpow γBar s ≤ 0 := by linarith
    exact mul_nonneg_of_nonpos_of_nonpos h3 h2

/-! ### Vector form -/

/-- Auxiliary: dot-product of self is nonneg. -/
private lemma euclideanDot_self_nonneg (v : Fin d → ℝ) :
    0 ≤ v ⬝ v := by
  unfold euclideanDot
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)

/-- Auxiliary: `v ⬝ w = w ⬝ v`. -/
private lemma euclideanDot_comm (v w : Fin d → ℝ) :
    v ⬝ w = w ⬝ v := by
  unfold euclideanDot
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- Auxiliary: `v ⬝ (w₁ - w₂) = v ⬝ w₁ - v ⬝ w₂`. -/
private lemma euclideanDot_sub_right (v w₁ w₂ : Fin d → ℝ) :
    v ⬝ (w₁ - w₂) = v ⬝ w₁ - v ⬝ w₂ := by
  unfold euclideanDot
  simp [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- Auxiliary: `(v₁ - v₂) ⬝ w = v₁ ⬝ w - v₂ ⬝ w`. -/
private lemma euclideanDot_sub_left (v₁ v₂ w : Fin d → ℝ) :
    (v₁ - v₂) ⬝ w = v₁ ⬝ w - v₂ ⬝ w := by
  rw [euclideanDot_comm, euclideanDot_sub_right, euclideanDot_comm w v₁,
      euclideanDot_comm w v₂]

/-- Auxiliary: scalar multiplication on the left of the dot product. -/
private lemma euclideanDot_smul_fun_left
    (c : ℝ) (v w : Fin d → ℝ) :
    (fun i => c * v i) ⬝ w = c * (v ⬝ w) := by
  unfold euclideanDot
  simp [mul_assoc, Finset.mul_sum]

/-- **Cauchy-Schwarz** for `euclideanDot`: `(v ⬝ w)² ≤ (v ⬝ v) (w ⬝ w)`. -/
private lemma euclideanDot_sq_le_self_mul_self (v w : Fin d → ℝ) :
    (v ⬝ w) ^ 2 ≤ (v ⬝ v) * (w ⬝ w) := by
  -- Via `Finset.sum_mul_sq_le_sq_mul_sq`.
  have h := Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ)
    (Finset.univ : Finset (Fin d)) v w
  -- h : (∑ i, v i * w i)^2 ≤ (∑ i, v i ^ 2) * (∑ i, w i ^ 2)
  have hvv : v ⬝ v = ∑ i, v i ^ 2 := by
    unfold euclideanDot
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [sq]
  have hww : w ⬝ w = ∑ i, w i ^ 2 := by
    unfold euclideanDot
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [sq]
  have hvw : v ⬝ w = ∑ i, v i * w i := rfl
  rw [hvw, hvv, hww]
  exact h

/-- Cauchy-Schwarz in product form: `v ⬝ w ≤ √(v⬝v) · √(w⬝w)`. -/
private lemma euclideanDot_le_norm_mul_norm (v w : Fin d → ℝ) :
    v ⬝ w ≤ Real.sqrt (v ⬝ v) * Real.sqrt (w ⬝ w) := by
  have h_sq : (v ⬝ w) ^ 2 ≤ (v ⬝ v) * (w ⬝ w) :=
    euclideanDot_sq_le_self_mul_self v w
  have h_sqrt : Real.sqrt ((v ⬝ w) ^ 2) ≤ Real.sqrt ((v ⬝ v) * (w ⬝ w)) :=
    Real.sqrt_le_sqrt h_sq
  have h_abs : Real.sqrt ((v ⬝ w) ^ 2) = |v ⬝ w| := by
    rw [sq_abs (v ⬝ w) |>.symm, Real.sqrt_sq (abs_nonneg _)]
  have h_prod : Real.sqrt ((v ⬝ v) * (w ⬝ w))
      = Real.sqrt (v ⬝ v) * Real.sqrt (w ⬝ w) :=
    Real.sqrt_mul (euclideanDot_self_nonneg v) _
  have h_le_abs : v ⬝ w ≤ |v ⬝ w| := le_abs_self _
  calc v ⬝ w ≤ |v ⬝ w| := h_le_abs
    _ = Real.sqrt ((v ⬝ w) ^ 2) := h_abs.symm
    _ ≤ Real.sqrt ((v ⬝ v) * (w ⬝ w)) := h_sqrt
    _ = Real.sqrt (v ⬝ v) * Real.sqrt (w ⬝ w) := h_prod

/-- For nonneg `r`, `r^{γBar/2}` rewritten as `(r^{(γBar-2)/2}) · r`
when `γBar > 1`. -/
private lemma rpow_split_gamma
    {γBar r : ℝ} (hγ : 1 < γBar) (hr : 0 ≤ r) :
    r ^ ((γBar - 2) / 2) * r = r ^ (γBar / 2) := by
  rcases eq_or_lt_of_le hr with rfl | hpos
  · -- r = 0. LHS = _ * 0 = 0; RHS = 0 ^ (γBar/2) = 0 since γBar/2 > 0.
    have h2 : 0 < γBar / 2 := by linarith
    simp [Real.zero_rpow h2.ne']
  · -- r > 0
    have hsum : (γBar - 2) / 2 + 1 = γBar / 2 := by ring
    have h1 : r ^ ((γBar - 2) / 2 + 1) = r ^ ((γBar - 2) / 2) * r ^ (1 : ℝ) :=
      Real.rpow_add hpos _ 1
    rw [hsum, Real.rpow_one] at h1
    linarith [h1]

/-- Auxiliary: for nonneg `a`, `a^{γBar/2}` is exactly `(a^{1/2})^{γBar}`. -/
private lemma rpow_half_pow_eq
    {γBar a : ℝ} (ha : 0 ≤ a) :
    a ^ (γBar / 2) = (Real.sqrt a) ^ γBar := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ha]
  congr 1
  ring

/-- Vector identity:
`vecAbsPowMinusTwo γBar v · (v ⬝ v) = (Real.sqrt (v ⬝ v))^{γBar}`. -/
private lemma vecAbsPowMinusTwo_mul_self
    {γBar : ℝ} (hγ : 1 < γBar) (v : Fin d → ℝ) :
    vecAbsPowMinusTwo γBar v * (v ⬝ v) = (Real.sqrt (v ⬝ v)) ^ γBar := by
  have hr : 0 ≤ v ⬝ v := euclideanDot_self_nonneg v
  unfold vecAbsPowMinusTwo
  rw [rpow_split_gamma hγ hr, rpow_half_pow_eq hr]

/-- The map `t ↦ t^{γBar - 1}` is monotone on `[0, ∞)` for `γBar ≥ 1`. -/
private lemma rpow_gamma_minus_one_mono
    {γBar : ℝ} (hγ : 1 ≤ γBar) :
    MonotoneOn (fun (x : ℝ) => x ^ (γBar - 1)) (Set.Ici 0) :=
  Real.monotoneOn_rpow_Ici_of_exponent_nonneg (by linarith)

/-- **Vector pointwise monotonicity** of `v ↦ |v|^{γBar-2} · v` on `Fin d → ℝ`.

For `γBar > 1` and any `v, w : Fin d → ℝ`,
`((vecAbsPowMinusTwo γBar v) v − (vecAbsPowMinusTwo γBar w) w) ⬝ (v − w) ≥ 0`.

The proof:
1. Expand the dot product using bilinearity:
   `LHS = a^γ + b^γ − (a^{γ-2} + b^{γ-2}) · (v⬝w)` with
   `a = √(v⬝v)`, `b = √(w⬝w)`.
2. Cauchy-Schwarz: `v⬝w ≤ a · b`. Coefficient `a^{γ-2} + b^{γ-2} ≥ 0`.
3. Conclude `≥ a^γ + b^γ − (a^{γ-2}+b^{γ-2}) a b
            = (a^{γ-1} − b^{γ-1}) (a − b) ≥ 0`
   by monotonicity of `t ↦ t^{γ-1}` on `[0, ∞)` for `γ ≥ 1`. -/
theorem rpow_signed_mono_vec
    {γBar : ℝ} (hγ : 1 < γBar) (v w : Fin d → ℝ) :
    0 ≤ (vecSignedRpow γBar v - vecSignedRpow γBar w) ⬝ (v - w) := by
  -- Step 1: define `a := √(v⬝v)`, `b := √(w⬝w)` and the coefficients
  -- `Av := vecAbsPowMinusTwo γBar v`, `Aw := vecAbsPowMinusTwo γBar w`.
  -- We avoid `set` because it interacts poorly with subsequent `simp`/`rw`
  -- calls in this version of Mathlib.
  let a : ℝ := Real.sqrt (v ⬝ v)
  let b : ℝ := Real.sqrt (w ⬝ w)
  have ha_def : a = Real.sqrt (v ⬝ v) := rfl
  have hb_def : b = Real.sqrt (w ⬝ w) := rfl
  have ha_nn : 0 ≤ a := Real.sqrt_nonneg _
  have hb_nn : 0 ≤ b := Real.sqrt_nonneg _
  have ha_sq : a * a = v ⬝ v :=
    Real.mul_self_sqrt (euclideanDot_self_nonneg v)
  have hb_sq : b * b = w ⬝ w :=
    Real.mul_self_sqrt (euclideanDot_self_nonneg w)
  -- Pointwise dot-product expansion.
  have h_split :
      (vecSignedRpow γBar v - vecSignedRpow γBar w) ⬝ (v - w)
        = vecAbsPowMinusTwo γBar v * (v ⬝ (v - w))
            - vecAbsPowMinusTwo γBar w * (w ⬝ (v - w)) := by
    unfold euclideanDot
    simp only [Pi.sub_apply, vecSignedRpow]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  have hvv_vw : v ⬝ (v - w) = v ⬝ v - v ⬝ w :=
    euclideanDot_sub_right v v w
  have hwv_ww : w ⬝ (v - w) = w ⬝ v - w ⬝ w :=
    euclideanDot_sub_right w v w
  have hwv : w ⬝ v = v ⬝ w := euclideanDot_comm w v
  rw [h_split, hvv_vw, hwv_ww, hwv]
  -- Goal:
  --   0 ≤ vecAbsPowMinusTwo γBar v * (v⬝v - v⬝w)
  --       - vecAbsPowMinusTwo γBar w * (v⬝w - w⬝w)
  -- Coefficient nonnegativity.
  have hAv_nn : 0 ≤ vecAbsPowMinusTwo γBar v := by
    unfold vecAbsPowMinusTwo
    exact Real.rpow_nonneg (euclideanDot_self_nonneg v) _
  have hAw_nn : 0 ≤ vecAbsPowMinusTwo γBar w := by
    unfold vecAbsPowMinusTwo
    exact Real.rpow_nonneg (euclideanDot_self_nonneg w) _
  have hAvAw_nn : 0 ≤ vecAbsPowMinusTwo γBar v + vecAbsPowMinusTwo γBar w :=
    add_nonneg hAv_nn hAw_nn
  -- Identifications.
  have h_Av_self : vecAbsPowMinusTwo γBar v * (v ⬝ v) = a ^ γBar := by
    have := vecAbsPowMinusTwo_mul_self (d := d) (γBar := γBar) hγ v
    -- this : vecAbsPowMinusTwo γBar v * (v⬝v) = (Real.sqrt (v⬝v)) ^ γBar
    exact this
  have h_Aw_self : vecAbsPowMinusTwo γBar w * (w ⬝ w) = b ^ γBar := by
    have := vecAbsPowMinusTwo_mul_self (d := d) (γBar := γBar) hγ w
    exact this
  -- Cauchy-Schwarz in our notation.
  have h_cs : v ⬝ w ≤ a * b := euclideanDot_le_norm_mul_norm v w
  -- vecAbsPowMinusTwo γBar v = a^{γBar-2}.
  have h_Av_eq : vecAbsPowMinusTwo γBar v = a ^ (γBar - 2) := by
    unfold vecAbsPowMinusTwo
    -- (v⬝v)^{(γ-2)/2} = (a*a)^{(γ-2)/2} = a^{γ-2} when a ≥ 0.
    rw [show v ⬝ v = a * a from ha_sq.symm]
    -- Now: (a * a) ^ ((γBar - 2) / 2) = a ^ (γBar - 2).
    rw [show a * a = a ^ (2 : ℝ) by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_cast,
          Real.rpow_natCast]
      ring]
    rw [← Real.rpow_mul ha_nn]
    congr 1
    ring
  have h_Aw_eq : vecAbsPowMinusTwo γBar w = b ^ (γBar - 2) := by
    unfold vecAbsPowMinusTwo
    rw [show w ⬝ w = b * b from hb_sq.symm]
    rw [show b * b = b ^ (2 : ℝ) by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_cast,
          Real.rpow_natCast]
      ring]
    rw [← Real.rpow_mul hb_nn]
    congr 1
    ring
  -- A general split lemma: for t ≥ 0 and γ ≥ 2, t^γ = t^{γ-1} * t.
  have h_pow_split : ∀ {t : ℝ}, 0 ≤ t → t ^ γBar = t ^ (γBar - 1) * t := by
    intro t ht
    rcases eq_or_lt_of_le ht with hte | hpos
    · -- t = 0
      have hpγ : 0 < γBar := by linarith
      have hp1 : 0 < γBar - 1 := by linarith
      rw [← hte, Real.zero_rpow hpγ.ne', Real.zero_rpow hp1.ne']
      ring
    · have h1 : t ^ (γBar - 1 + 1) = t ^ (γBar - 1) * t ^ (1 : ℝ) :=
        Real.rpow_add hpos _ 1
      have hsum : γBar - 1 + 1 = γBar := by ring
      rw [hsum, Real.rpow_one] at h1
      linarith
  -- Similarly t^{γ-2} * t = t^{γ-1}.
  have h_pow_split_2 : ∀ {t : ℝ}, 0 ≤ t → t ^ (γBar - 2) * t = t ^ (γBar - 1) := by
    intro t ht
    rcases eq_or_lt_of_le ht with hte | hpos
    · -- t = 0. LHS = _ * 0 = 0; RHS = 0 ^ (γBar - 1) = 0 since γBar - 1 > 0.
      have hp1 : 0 < γBar - 1 := by linarith
      rw [← hte, mul_zero, Real.zero_rpow hp1.ne']
    · have h1 : t ^ (γBar - 2 + 1) = t ^ (γBar - 2) * t ^ (1 : ℝ) :=
        Real.rpow_add hpos _ 1
      have hsum : γBar - 2 + 1 = γBar - 1 := by ring
      rw [hsum, Real.rpow_one] at h1
      linarith
  have h_a_split : a ^ γBar = a ^ (γBar - 1) * a := h_pow_split ha_nn
  have h_b_split : b ^ γBar = b ^ (γBar - 1) * b := h_pow_split hb_nn
  have h_a_split_2 : a ^ (γBar - 2) * a = a ^ (γBar - 1) := h_pow_split_2 ha_nn
  have h_b_split_2 : b ^ (γBar - 2) * b = b ^ (γBar - 1) := h_pow_split_2 hb_nn
  -- Algebraic identity:
  --   Av*(v⬝v - v⬝w) - Aw*(v⬝w - w⬝w)
  --   = Av*(v⬝v) + Aw*(w⬝w) - (Av + Aw) * (v⬝w)
  -- Substituting our identifications:
  --   = a^γ + b^γ - (a^{γ-2} + b^{γ-2}) * (v⬝w)
  -- and bounded below by `a^γ + b^γ - (a^{γ-2} + b^{γ-2}) * (a*b)`
  -- = (a^{γ-1} - b^{γ-1}) * (a - b) ≥ 0 by Cauchy-Schwarz + monotonicity.
  have h_target_eq :
      vecAbsPowMinusTwo γBar v * (v ⬝ v - v ⬝ w)
        - vecAbsPowMinusTwo γBar w * (v ⬝ w - w ⬝ w)
      = (vecAbsPowMinusTwo γBar v * (v ⬝ v) +
          vecAbsPowMinusTwo γBar w * (w ⬝ w)) -
        (vecAbsPowMinusTwo γBar v + vecAbsPowMinusTwo γBar w) * (v ⬝ w) := by
    ring
  rw [h_target_eq, h_Av_self, h_Aw_self, h_Av_eq, h_Aw_eq]
  -- Goal: 0 ≤ a^γ + b^γ - (a^{γ-2} + b^{γ-2}) * (v⬝w)
  -- Bound (a^{γ-2} + b^{γ-2}) * (v⬝w) ≤ (a^{γ-2} + b^{γ-2}) * (a*b).
  have hCoef_nn : 0 ≤ a ^ (γBar - 2) + b ^ (γBar - 2) := by
    have : 0 ≤ a ^ (γBar - 2) := Real.rpow_nonneg ha_nn _
    have : 0 ≤ b ^ (γBar - 2) := Real.rpow_nonneg hb_nn _
    positivity
  have h_step1 : (a ^ (γBar - 2) + b ^ (γBar - 2)) * (v ⬝ w)
                  ≤ (a ^ (γBar - 2) + b ^ (γBar - 2)) * (a * b) :=
    mul_le_mul_of_nonneg_left h_cs hCoef_nn
  -- Identify:
  -- (a^{γ-2}+b^{γ-2}) * (a*b) = a^{γ-1}*b + a*b^{γ-1}.
  have h_expand : (a ^ (γBar - 2) + b ^ (γBar - 2)) * (a * b)
                    = a ^ (γBar - 1) * b + a * b ^ (γBar - 1) := by
    have : (a ^ (γBar - 2) + b ^ (γBar - 2)) * (a * b)
            = (a ^ (γBar - 2) * a) * b + a * (b ^ (γBar - 2) * b) := by ring
    rw [this, h_a_split_2, h_b_split_2]
  -- Combined identity:
  have h_lower : a ^ γBar + b ^ γBar - (a ^ (γBar - 2) + b ^ (γBar - 2)) * (a * b)
                  = (a ^ (γBar - 1) - b ^ (γBar - 1)) * (a - b) := by
    rw [h_expand, h_a_split, h_b_split]; ring
  -- Monotonicity of t ↦ t^{γ-1} on [0, ∞).
  have h_mono : 0 ≤ (a ^ (γBar - 1) - b ^ (γBar - 1)) * (a - b) := by
    have hexp : 0 ≤ γBar - 1 := by linarith
    rcases le_total a b with hab | hba
    · have h1 : a ^ (γBar - 1) ≤ b ^ (γBar - 1) :=
        Real.rpow_le_rpow ha_nn hab hexp
      have h2 : a - b ≤ 0 := by linarith
      have h3 : a ^ (γBar - 1) - b ^ (γBar - 1) ≤ 0 := by linarith
      exact mul_nonneg_of_nonpos_of_nonpos h3 h2
    · have h1 : b ^ (γBar - 1) ≤ a ^ (γBar - 1) :=
        Real.rpow_le_rpow hb_nn hba hexp
      have h2 : 0 ≤ a - b := by linarith
      have h3 : 0 ≤ a ^ (γBar - 1) - b ^ (γBar - 1) := by linarith
      exact mul_nonneg h3 h2
  have h_low_nn :
      0 ≤ a ^ γBar + b ^ γBar - (a ^ (γBar - 2) + b ^ (γBar - 2)) * (a * b) := by
    rw [h_lower]; exact h_mono
  linarith

/-! ### Continuity of the signed power map under `1 < γBar`

Phase 0b.2a foundation lemmas. The `signedRpow γBar` map is continuous
on all of `ℝ` (and `vecSignedRpow` is continuous on `Fin d → ℝ`)
whenever `1 < γBar`, **including at the origin**, because
`|signedRpow γBar t| = |t| ^ (γBar - 1)` with `γBar - 1 > 0`. This is
the helper consumed by Phase 0b.2b's refactor of
`Theorems/SimplePower/Hemicontinuity.lean`.
-/

/-- For `1 < γBar`, the scalar signed-power map `signedRpow γBar` is
continuous on `ℝ`. The key point is continuity at `0`: even though
`|·|^{γBar-2}` blows up there for `γBar < 2`, multiplication by `t`
absorbs the singularity since `signedRpow γBar t = sign(t) * |t|^{γBar-1}`
in magnitude with `γBar - 1 > 0`. -/
lemma continuous_signedRpow {γBar : ℝ} (hγ : 1 < γBar) :
    Continuous (signedRpow γBar) := by
  -- Rewrite via the case-split into `if 0 ≤ t then t^(γBar-1) else -((-t)^(γBar-1))`.
  have hexp_nn : 0 ≤ γBar - 1 := by linarith
  have hexp_pos : 0 < γBar - 1 := by linarith
  have hrewrite : signedRpow γBar =
      fun t : ℝ => if 0 ≤ t then t ^ (γBar - 1) else -((-t) ^ (γBar - 1)) := by
    funext t
    by_cases ht : 0 ≤ t
    · rw [if_pos ht]
      exact signedRpow_eq_rpow_sub_one_of_nonneg hγ ht
    · rw [if_neg ht]
      have ht_le : t ≤ 0 := le_of_not_ge ht
      exact signedRpow_neg_eq_of_nonpos hγ ht_le
  rw [hrewrite]
  -- Apply `Continuous.if_le` with `f = const 0`, `g = id`,
  -- `f' = (·) ^ (γBar - 1)`, `g' = -((-·) ^ (γBar - 1))`.
  refine Continuous.if_le ?_ ?_ continuous_const continuous_id ?_
  · exact Real.continuous_rpow_const hexp_nn
  · refine Continuous.neg ?_
    exact (Real.continuous_rpow_const hexp_nn).comp continuous_neg
  · -- Boundary: at the unique `t` with `0 = t`, both branches yield `0`.
    intro t ht
    have ht0 : t = 0 := ht.symm
    rw [ht0]
    simp [Real.zero_rpow hexp_pos.ne']

/-- The norm of the vector signed-power map is `‖v‖ ^ (γBar - 1)`. Used
to squeeze `vecSignedRpow γBar v → 0` as `v → 0`. Here `‖v‖` is the
sup-norm `Pi.normedField` on `Fin d → ℝ`, but we state the bound on
each coordinate using `|v i|` and the Euclidean dot-product norm
`Real.sqrt (v ⬝ v)` (which is `√(∑ v_i²)`).

Specifically, on each coordinate
`|vecSignedRpow γBar v i| = (v ⬝ v)^((γBar-2)/2) * |v i|`. -/
private lemma vecSignedRpow_coord_abs_eq
    (γBar : ℝ) (v : Fin d → ℝ) (i : Fin d) :
    |vecSignedRpow γBar v i| = (v ⬝ v) ^ ((γBar - 2) / 2) * |v i| := by
  unfold vecSignedRpow vecAbsPowMinusTwo
  rw [abs_mul]
  have h_nn : 0 ≤ (v ⬝ v) ^ ((γBar - 2) / 2) :=
    Real.rpow_nonneg (Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)) _
  rw [abs_of_nonneg h_nn]

/-- For `1 < γBar`, the vector signed-power map `vecSignedRpow γBar` is
continuous on `Fin d → ℝ`. Continuity away from `v = 0` follows from
`continuousAt_rpow_const` since `v ⬝ v > 0` there. Continuity at
`v = 0` follows by squeeze: each coordinate satisfies
`|vecSignedRpow γBar v i| ≤ (v ⬝ v)^((γBar-1)/2)`, which → 0 since
`γBar - 1 > 0`. -/
lemma continuous_vecSignedRpow {γBar : ℝ} (hγ : 1 < γBar) :
    Continuous (vecSignedRpow (d := d) γBar) := by
  refine continuous_pi (fun i => ?_)
  -- Show continuity of `v ↦ vecSignedRpow γBar v i`.
  refine continuous_iff_continuousAt.mpr (fun v => ?_)
  -- Common pointwise bound: `|vecSignedRpow γBar w i| ≤ (w ⬝ w) ^ ((γBar - 1) / 2)`.
  have hexp_pos : 0 < γBar - 1 := by linarith
  have hexp_h : 0 < (γBar - 1) / 2 := by linarith
  have hbound : ∀ w : Fin d → ℝ,
      |vecSignedRpow γBar w i| ≤ (w ⬝ w) ^ ((γBar - 1) / 2) := by
    intro w
    rw [vecSignedRpow_coord_abs_eq]
    have hww_nn : 0 ≤ w ⬝ w :=
      Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)
    have hcoord_sq : (w i) ^ 2 ≤ w ⬝ w := by
      unfold euclideanDot
      have hi : (w i) ^ 2 = (w i) * (w i) := sq (w i)
      rw [hi]
      exact Finset.single_le_sum
        (f := fun j : Fin d => w j * w j)
        (s := (Finset.univ : Finset (Fin d)))
        (fun j _ => mul_self_nonneg (w j)) (Finset.mem_univ i)
    have h_abs_wi_le : |w i| ≤ (w ⬝ w) ^ ((1 : ℝ) / 2) := by
      have hsq_eq : |w i| = ((w i) ^ 2) ^ ((1 : ℝ) / 2) := by
        rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs]
      rw [hsq_eq]
      exact Real.rpow_le_rpow (sq_nonneg _) hcoord_sq (by norm_num)
    -- `(w⬝w)^((γBar-2)/2) * (w⬝w)^(1/2) = (w⬝w)^((γBar-1)/2)`.
    rcases eq_or_lt_of_le hww_nn with hww0 | hww_pos
    · -- w ⬝ w = 0: both sides zero.
      rw [← hww0]
      have h12_ne : ((1 : ℝ) / 2) ≠ 0 := by norm_num
      have hexph_ne : ((γBar - 1) / 2) ≠ 0 := hexp_h.ne'
      rw [Real.zero_rpow hexph_ne]
      have h_abs_wi_zero : |w i| = 0 := by
        have h1 : |w i| ≤ (0 : ℝ) ^ ((1 : ℝ) / 2) := by
          rw [← hww0] at h_abs_wi_le; exact h_abs_wi_le
        rw [Real.zero_rpow h12_ne] at h1
        exact le_antisymm h1 (abs_nonneg _)
      rw [h_abs_wi_zero, mul_zero]
    · -- w ⬝ w > 0.
      have h_combine :
          (w ⬝ w) ^ ((γBar - 2) / 2) * (w ⬝ w) ^ ((1 : ℝ) / 2)
            = (w ⬝ w) ^ ((γBar - 1) / 2) := by
        rw [← Real.rpow_add hww_pos]
        congr 1; ring
      calc (w ⬝ w) ^ ((γBar - 2) / 2) * |w i|
          ≤ (w ⬝ w) ^ ((γBar - 2) / 2) * (w ⬝ w) ^ ((1 : ℝ) / 2) := by
            exact mul_le_mul_of_nonneg_left h_abs_wi_le
              (Real.rpow_nonneg hww_nn _)
        _ = (w ⬝ w) ^ ((γBar - 1) / 2) := h_combine
  -- Helper: `w ⬝ w ≤ (Fintype.card (Fin d) : ℝ) * ‖w‖^2` where `‖·‖` is sup norm.
  have h_ww_le_card : ∀ w : Fin d → ℝ,
      w ⬝ w ≤ (Fintype.card (Fin d) : ℝ) * ‖w‖ ^ 2 := by
    intro w
    unfold euclideanDot
    have hcoord_le : ∀ j : Fin d, w j * w j ≤ ‖w‖ ^ 2 := by
      intro j
      have habsj : |w j| ≤ ‖w‖ := by
        have := norm_le_pi_norm w j
        rw [Real.norm_eq_abs] at this
        exact this
      have hj_nn : 0 ≤ |w j| := abs_nonneg _
      have hsq : (w j) * (w j) = |w j| ^ 2 := by
        rw [sq_abs]; ring
      rw [hsq]
      exact pow_le_pow_left₀ hj_nn habsj 2
    calc ∑ j, w j * w j
        ≤ ∑ _j : Fin d, ‖w‖ ^ 2 := Finset.sum_le_sum (fun j _ => hcoord_le j)
      _ = (Fintype.card (Fin d) : ℝ) * ‖w‖ ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ]
          ring
  by_cases hv : v = 0
  · -- Continuity at `v = 0`: ε–δ proof using the squeeze.
    rw [hv]
    rw [Metric.continuousAt_iff]
    intros ε hε
    have hzero : vecSignedRpow γBar (0 : Fin d → ℝ) i = 0 := by
      simp [vecSignedRpow_zero]
    set d_card : ℝ := (Fintype.card (Fin d) : ℝ) with hd_card_def
    have hd_nn : 0 ≤ d_card := by
      rw [hd_card_def]; exact_mod_cast Nat.zero_le _
    set θ : ℝ := (ε / 2) ^ (2 / (γBar - 1)) with hθ_def
    have hε2_pos : 0 < ε / 2 := by linarith
    have hθ_pos : 0 < θ := by
      rw [hθ_def]
      exact Real.rpow_pos_of_pos hε2_pos _
    set δ_sq : ℝ := θ / (d_card + 1) with hδsq_def
    have hδsq_pos : 0 < δ_sq := by
      rw [hδsq_def]; exact div_pos hθ_pos (by linarith)
    set δ : ℝ := Real.sqrt δ_sq with hδ_def
    have hδ_pos : 0 < δ := Real.sqrt_pos.mpr hδsq_pos
    refine ⟨δ, hδ_pos, ?_⟩
    intros w hw
    -- `hw : dist w 0 < δ`, i.e. `‖w‖ < δ`.
    rw [dist_zero_right] at hw
    -- `‖w‖^2 ≤ δ_sq`: actually `< δ_sq`.
    have hw_nn : 0 ≤ ‖w‖ := norm_nonneg _
    have hw_sq_lt : ‖w‖ ^ 2 < δ_sq := by
      have hδ_sq_eq : δ ^ 2 = δ_sq := by
        rw [hδ_def, sq, Real.mul_self_sqrt hδsq_pos.le]
      rw [← hδ_sq_eq]
      rcases eq_or_lt_of_le hw_nn with hw0 | hw_pos
      · -- ‖w‖ = 0
        rw [← hw0]; simp
        positivity
      · -- 0 < ‖w‖ < δ
        have h1 : ‖w‖ ^ 2 < δ ^ 2 := by
          have := sq_lt_sq' (by linarith [hδ_pos]) hw
          -- Actually use simpler tool: pow_lt_pow_left
          exact (pow_lt_pow_left₀ hw hw_nn (by norm_num : 2 ≠ 0))
        exact h1
    -- `(d_card + 1) * δ_sq = θ`.
    have h_combine : (d_card + 1) * δ_sq = θ := by
      rw [hδsq_def]; field_simp
    -- `w ⬝ w ≤ d_card * ‖w‖^2 < d_card * δ_sq + δ_sq = (d_card + 1) * δ_sq = θ`.
    have hww_nn : 0 ≤ w ⬝ w :=
      Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)
    have hww_le_θ : w ⬝ w < θ := by
      have h1 : w ⬝ w ≤ d_card * ‖w‖ ^ 2 := h_ww_le_card w
      rcases eq_or_lt_of_le hd_nn with hd0 | hd_pos
      · -- d_card = 0: w ⬝ w ≤ 0 ≤ 0 < θ.
        have hww_zero : w ⬝ w ≤ 0 := by
          have : d_card * ‖w‖ ^ 2 = 0 := by rw [← hd0]; ring
          linarith
        linarith [hθ_pos]
      · -- d_card > 0.
        have h2 : d_card * ‖w‖ ^ 2 < d_card * δ_sq :=
          mul_lt_mul_of_pos_left hw_sq_lt hd_pos
        have h3 : d_card * δ_sq < d_card * δ_sq + δ_sq := by linarith
        have h4 : d_card * δ_sq + δ_sq = (d_card + 1) * δ_sq := by ring
        linarith [h1, h2, h3, h4, h_combine]
    -- Squeeze.
    have hpow_mono : (w ⬝ w) ^ ((γBar - 1) / 2) ≤ θ ^ ((γBar - 1) / 2) :=
      Real.rpow_le_rpow hww_nn hww_le_θ.le hexp_h.le
    have hθ_eval : θ ^ ((γBar - 1) / 2) = ε / 2 := by
      rw [hθ_def, ← Real.rpow_mul hε2_pos.le]
      have h_exp_mul : (2 / (γBar - 1)) * ((γBar - 1) / 2) = 1 := by
        field_simp
      rw [h_exp_mul, Real.rpow_one]
    rw [hzero]
    have h_dist_eq :
        dist (vecSignedRpow γBar w i) 0 = |vecSignedRpow γBar w i| := by
      rw [dist_zero_right, Real.norm_eq_abs]
    rw [h_dist_eq]
    calc |vecSignedRpow γBar w i|
        ≤ (w ⬝ w) ^ ((γBar - 1) / 2) := hbound w
      _ ≤ θ ^ ((γBar - 1) / 2) := hpow_mono
      _ = ε / 2 := hθ_eval
      _ < ε := by linarith
  · -- Continuity at `v ≠ 0`: `v ⬝ v > 0`, so the rpow is continuous.
    have hvv_pos : 0 < v ⬝ v := by
      -- There exists j with v j ≠ 0.
      have hex : ∃ j : Fin d, v j ≠ 0 := by
        by_contra hall
        push_neg at hall
        apply hv
        funext j; exact hall j
      obtain ⟨j, hj⟩ := hex
      have hjsq : 0 < v j * v j := by
        rcases lt_or_gt_of_ne hj with hjneg | hjpos
        · have : v j * v j = (-v j) * (-v j) := by ring
          rw [this]
          exact mul_pos (neg_pos.mpr hjneg) (neg_pos.mpr hjneg)
        · exact mul_pos hjpos hjpos
      unfold euclideanDot
      have hsum_nn : ∀ k : Fin d, 0 ≤ v k * v k := fun k => mul_self_nonneg _
      calc (0 : ℝ) < v j * v j := hjsq
        _ = ∑ k ∈ ({j} : Finset (Fin d)), v k * v k := by simp
        _ ≤ ∑ k, v k * v k :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.subset_univ _) (fun k _ _ => hsum_nn k)
    -- Continuity: `vecSignedRpow γBar v i = (v ⬝ v) ^ ((γBar-2)/2) * v i`.
    show ContinuousAt (fun w : Fin d → ℝ => vecSignedRpow γBar w i) v
    have h_eq : (fun w : Fin d → ℝ => vecSignedRpow γBar w i)
        = fun w => (w ⬝ w) ^ ((γBar - 2) / 2) * w i := by
      funext w; rfl
    rw [h_eq]
    refine ContinuousAt.mul ?_ (continuous_apply i).continuousAt
    -- `w ↦ w ⬝ w` is continuous.
    have hdot_at : ContinuousAt (fun w : Fin d → ℝ => w ⬝ w) v := by
      have hdot_cont : Continuous (fun w : Fin d → ℝ => w ⬝ w) := by
        unfold euclideanDot
        refine continuous_finset_sum _ (fun j _ => ?_)
        exact (continuous_apply j).mul (continuous_apply j)
      exact hdot_cont.continuousAt
    have hrpow_at : ContinuousAt (fun s : ℝ => s ^ ((γBar - 2) / 2)) (v ⬝ v) :=
      Real.continuousAt_rpow_const _ _ (Or.inl hvv_pos.ne')
    -- Compose: (fun w => (w ⬝ w) ^ ((γBar - 2) / 2)) = (fun s => s ^ _) ∘ (fun w => w ⬝ w).
    exact ContinuousAt.comp (g := fun s : ℝ => s ^ ((γBar - 2) / 2))
      (f := fun w : Fin d → ℝ => w ⬝ w) hrpow_at hdot_at

/-! ### Sanity-check `example`s -/

example (γBar : ℝ) (hγ : 1 < γBar) (s t : ℝ) :
    0 ≤ (signedRpow γBar t - signedRpow γBar s) * (t - s) :=
  rpow_signed_mono_scalar hγ s t

example (γBar : ℝ) (hγ : 1 < γBar) (v w : Fin d → ℝ) :
    0 ≤ (vecSignedRpow γBar v - vecSignedRpow γBar w) ⬝ (v - w) :=
  rpow_signed_mono_vec hγ v w

example (γBar : ℝ) (hγ : 1 < γBar) :
    Continuous (signedRpow γBar) := continuous_signedRpow hγ

example {d : ℕ} (γBar : ℝ) (hγ : 1 < γBar) :
    Continuous (vecSignedRpow (d := d) γBar) := continuous_vecSignedRpow hγ

/-! ## V-side a.e.-congruence for `mfgOperatorEpsPair`

This block lives outside the ambient `variable (V : ...)` so that the
potential argument is fully explicit and we can quantify over two
potentials `V₁` and `V₂` simultaneously. -/

section VCongr

variable {d : ℕ}

/-- **Potential-side a.e.-congruence** for `mfgOperatorEpsPair`. If
two potentials `V₁` and `V₂` agree a.e. on the unit cube, the two
ε-form pairings agree. The Gateaux term `gateauxWpPair` does not
depend on `V`, so the proof reduces to the bare-pairing
`mfgOperatorPair_congr_V_ae`. -/
theorem mfgOperatorEpsPair_congr_V_ae
    (V₁ V₂ : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (γBar ε : ℝ)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (μ υ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ)
    (hV : V₁ =ᵐ[volume.restrict (UnitCube d)] V₂) :
    mfgOperatorEpsPair (V := V₁) (H := H) (DpH := DpH) γBar ε Dυ μ υ Dν η ν
      = mfgOperatorEpsPair (V := V₂) (H := H) (DpH := DpH) γBar ε Dυ μ υ Dν η ν := by
  unfold mfgOperatorEpsPair
  rw [mfgOperatorPair_congr_V_ae V₁ V₂ H DpH Dυ μ υ Dν η ν hV]

end VCongr

end MFG
end Solutions
end StationaryMFG
