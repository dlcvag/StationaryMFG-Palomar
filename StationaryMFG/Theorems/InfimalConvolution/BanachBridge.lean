module

public import StationaryMFG.Periodic.LpReflexive
public import StationaryMFG.Theorems.SimplePower.Banach.AbstractLifts
public import StationaryMFG.Theorems.SimplePower.Coercivity.Integrability
public import StationaryMFG.Theorems.SimplePower.BanachBridge
public import StationaryMFG.Theorems.InfimalConvolution.Properties
public import StationaryMFG.Theorems.InfimalConvolution.CoercivityAE

@[expose] public section

/-!
# Banach realisation of `L^{bb}_per × W^{1,gb}_per` at general `(bb, gb)`

This module packages the paper's product space
`X = L^{bb}(𝕋^d;ℝ⁺₀) × W^{1,gb}(𝕋^d)` — the reflexive Banach carrier on
which the abstract Browder–Minty theorem
(`Theorem~\ref{thm:monotone.abstract-weak}`) runs in the weak-growth /
infimal-convolution regularised existence step
(`Proposition~\ref{thm:strongAepsi.delta}`, paper lines 1838-1854) — into a
reusable bundle parameterised on general exponents `(bb, gb)`.

## Why this scope (Theorem 3, Path A drain, child A1a)

The `p = 2` (Hilbert) calibration of this product carrier was discharged in
`StationaryMFG.Periodic.Reflexive` (`lpSobolev_product_isReflexive_two`), and
the general `1 < p < ∞` analytic content — reflexivity of
`L^{bb}_per × W^{1,gb}_per` — already lives in
`StationaryMFG.Periodic.LpReflexive` (`lpSobolev_product_isReflexive`), via
the unit-cube Riesz representation theorem.

What was *missing* for the Theorem-3 drain chain is a uniform **realisation
bundle**: a single structure exposing the Banach carrier `X`, the projection
`toBare : X → (m, u)` onto bare periodic functions, and the constructor
`ofBare` injecting a bare `MemLpPer`/`MemSobolevPer` witness pair into `X`.
Downstream tasks (A1b/A1c/A1d, A2.., A3-A5) build the Path A representation
theorem (`coePos_m_atWitness`) on top of this carrier; collecting the carrier
data behind one structure keeps those tasks uniform across the exponents.

## Design note on `ofBare`

The `MemSobolevPer gb u` predicate only certifies the weak derivatives of `u`
in `L¹` (its existential derivative family carries `MemLpPer 1`), whereas the
Mathlib `SobolevPerLp 1 gb d` realisation needs the derivatives in `L^gb`.
Every downstream consumer of this realisation already carries the explicit
`L^gb`-integrable derivative family (e.g. the `coeMemLp_Du` field of the
Theorem-3 bridge). Accordingly, `ofBare` takes that explicit family `Du`
together with `∀ i, MemLpPer gb (Du i)` as an extra argument — a faithful and
non-lossy version of the task-spec signature.

## Reference

Re-packages `StationaryMFG.Periodic.lpSobolev_product_isReflexive`
(`LpReflexive.lean`); the Hölder-conjugate side exponents are produced
internally from `1 < bb, gb < ∞` via `ENNReal.holderConjugate_iff`.
-/

noncomputable section

namespace StationaryMFG
namespace Periodic

open MeasureTheory NormedSpace
open scoped ENNReal NNReal Topology

variable {d : ℕ}

/-! ## The conjugate exponent, internally produced -/

/-- The Hölder conjugate of `p`, defined as `(1 - p⁻¹)⁻¹`. For `1 < p < ∞`
this is the classical conjugate satisfying `p⁻¹ + q⁻¹ = 1`. -/
def conjExponentENN (p : ℝ≥0∞) : ℝ≥0∞ := (1 - p⁻¹)⁻¹

/-- For `1 < p < ∞`, `conjExponentENN p` is Hölder-conjugate to `p`. -/
theorem holderConjugate_conjExponentENN {p : ℝ≥0∞} (hp : 1 < p) (_hp_fin : p ≠ ⊤) :
    ENNReal.HolderConjugate p (conjExponentENN p) := by
  rw [ENNReal.holderConjugate_iff]
  -- `p⁻¹ + (1 - p⁻¹) = 1`, using `p⁻¹ ≤ 1`.
  have hp_pos : 0 < p := lt_trans one_pos hp
  have hp_inv_le_one : p⁻¹ ≤ 1 := by
    rw [ENNReal.inv_le_one]; exact hp.le
  have hconj_inv : (conjExponentENN p)⁻¹ = 1 - p⁻¹ := by
    unfold conjExponentENN
    rw [inv_inv]
  rw [hconj_inv]
  rw [add_tsub_cancel_of_le hp_inv_le_one]

/-- For `1 < p < ∞`, `conjExponentENN p` is strictly above `1`. -/
theorem one_lt_conjExponentENN {p : ℝ≥0∞} (hp : 1 < p) (hp_fin : p ≠ ⊤) :
    1 < conjExponentENN p := by
  have hp_pos : 0 < p := lt_trans one_pos hp
  -- `p⁻¹ < 1`, so `1 - p⁻¹ < 1` and is positive, hence its inverse is `> 1`.
  have hp_inv_lt_one : p⁻¹ < 1 := by
    rw [ENNReal.inv_lt_one]; exact hp
  have hp_inv_pos : 0 < p⁻¹ := ENNReal.inv_pos.mpr hp_fin
  have hsub_lt_one : 1 - p⁻¹ < 1 := by
    refine ENNReal.sub_lt_self (by norm_num) (by norm_num) hp_inv_pos.ne'
  have hsub_pos : 0 < 1 - p⁻¹ := by
    rw [tsub_pos_iff_lt]; exact hp_inv_lt_one
  unfold conjExponentENN
  rw [ENNReal.lt_inv_iff_lt_inv]
  simpa using hsub_lt_one

/-- For `1 < p < ∞`, `1 ≤ conjExponentENN p`. -/
theorem one_le_conjExponentENN {p : ℝ≥0∞} (hp : 1 < p) (hp_fin : p ≠ ⊤) :
    1 ≤ conjExponentENN p :=
  (one_lt_conjExponentENN hp hp_fin).le

/-! ## The Banach realisation bundle -/

/-- **Banach realisation of `L^{bb}_per × W^{1,gb}_per`.**

A reflexive real Banach carrier `X` together with a projection onto the bare
periodic function pair `(m, u)` and a constructor injecting a bare
`MemLpPer`/`MemSobolevPer` witness into `X`. This is the abstract space on
which the regularised MFG operator `A_ε` is shown monotone-coercive and to
which the Browder–Minty theorem is applied
(`Proposition~\ref{thm:strongAepsi.delta}`). -/
structure BanachRealisation (bb gb : ℝ≥0∞) [Fact (1 ≤ bb)] [Fact (1 ≤ gb)] where
  /-- The Banach carrier. -/
  X : Type
  /-- Normed additive group structure. -/
  [normedAddCommGroup : NormedAddCommGroup X]
  /-- `ℝ`-vector space structure. -/
  [normedSpace : NormedSpace ℝ X]
  /-- Reflexivity of the carrier (needed for weak compactness). -/
  reflexive : Periodic.IsReflexiveNormedSpace X
  /-- Projection onto the bare periodic function pair `(m, u)`. -/
  toBare : X → ((Fin d → ℝ) → ℝ) × ((Fin d → ℝ) → ℝ)
  /-- Inject a bare `(m, u)` pair with `m ∈ L^{bb}_per`, `u ∈ W^{1,gb}_per`
  (with the weak-derivative family `Du` certified in `L^{gb}_per`) into the
  carrier. -/
  ofBare : {m u : (Fin d → ℝ) → ℝ} → {Du : Fin d → (Fin d → ℝ) → ℝ} →
            Periodic.MemLpPer bb m → Periodic.MemSobolevPer gb u →
            (∀ i, Periodic.MemLpPer gb (Du i)) → X
  /-- The `m`-component projection, as a **continuous linear map** onto
  `L^{bb}_per`. This certifies that reading off the first component of an
  element of the carrier is linear and continuous — the structure the
  admissible set `K_ε` needs for its convexity and closedness lemmas. -/
  mProj : X →L[ℝ] Periodic.LpPer bb d
  /-- Coherence: the bare `m`-component read off by `toBare` agrees (a.e. on
  the unit cube) with the coercion of the `mProj` projection. -/
  mProj_toBare : ∀ z : X,
    (toBare z).1
      =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (Periodic.UnitCube d)]
        (⇑(mProj z) : (Fin d → ℝ) → ℝ)
  /-- The `u`-component projection, as a **continuous linear map** onto
  `L^{gb}_per`. This certifies that reading off the value-function
  component of an element of the carrier is linear and continuous — the
  structure the flux/`ε`-Laplacian terms of `A_ε^δ` need to pair against
  the test value `ν` (paper `eq:defAepsi`, line 925). -/
  uProj : X →L[ℝ] Periodic.LpPer gb d
  /-- Coherence: the bare `u`-component read off by `toBare` agrees (a.e. on
  the unit cube) with the coercion of the `uProj` projection. -/
  uProj_toBare : ∀ z : X,
    (toBare z).2
      =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (Periodic.UnitCube d)]
        (⇑(uProj z) : (Fin d → ℝ) → ℝ)
  /-- The **weak-gradient family** projection, as a `Fin d`-indexed family
  of continuous linear maps onto `L^{gb}_per`. The `i`-th map reads off the
  `i`-th weak partial derivative `∂_i u` of the value-function component.
  This is the data the abstract `BanachRealisation` was previously missing:
  the operator's flux term `∫ m D_pH·Dν` and `ε`-Laplacian term
  `ε ∫ |Du|^{γ̄−2} Du·Dν` (paper `eq:defAepsi`, line 925) both pair a test
  element against this Sobolev gradient `Dν`. -/
  DProj : Fin d → (X →L[ℝ] Periodic.LpPer gb d)

attribute [instance] BanachRealisation.normedAddCommGroup BanachRealisation.normedSpace

/-! ## Existence of a realisation at general `(bb, gb)` -/

/-- **Existence of a Banach realisation at general `1 < bb, gb < ∞`.**

The canonical realisation has carrier `X = LpPer bb d × SobolevPerLp 1 gb d`,
reflexive by `lpSobolev_product_isReflexive`. The projection reads off the
function components of the `Lp`/Sobolev pair; the injection bridges via
`MemLpPer.toLp` and `MemSobolevPer.toLpSobolev`. -/
theorem exists_banachRealisation
    {bb gb : ℝ≥0∞} [Fact (1 ≤ bb)] [Fact (1 ≤ gb)]
    (hβ : 1 < bb) (hβ_fin : bb ≠ ⊤)
    (hγ : 1 < gb) (hγ_fin : gb ≠ ⊤) :
    Nonempty (BanachRealisation (d := d) bb gb) := by
  classical
  -- `Fact (1 ≤ ·)` for the conjugates.
  haveI hβ'_conj : ENNReal.HolderConjugate bb (conjExponentENN bb) :=
    holderConjugate_conjExponentENN hβ hβ_fin
  haveI hγ'_conj : ENNReal.HolderConjugate gb (conjExponentENN gb) :=
    holderConjugate_conjExponentENN hγ hγ_fin
  haveI hβ'_fact : Fact (1 ≤ conjExponentENN bb) :=
    ⟨one_le_conjExponentENN hβ hβ_fin⟩
  haveI hγ'_fact : Fact (1 ≤ conjExponentENN gb) :=
    ⟨one_le_conjExponentENN hγ hγ_fin⟩
  -- Reflexivity of the product carrier.
  have hRefl :
      Periodic.IsReflexiveNormedSpace
        (LpPer bb d × SobolevPerLp 1 gb d) :=
    Periodic.lpSobolev_product_isReflexive (d := d)
      bb (conjExponentENN bb) gb (conjExponentENN gb)
      hβ hβ_fin hγ hγ_fin
  refine ⟨{
    X := LpPer bb d × SobolevPerLp 1 gb d
    reflexive := hRefl
    toBare := fun z => (⇑z.1, ⇑z.2.1)
    ofBare := fun {m u Du} hm hu hDu =>
      (hm.toLp, hu.toLpSobolev hDu)
    mProj := ContinuousLinearMap.fst ℝ (LpPer bb d) (SobolevPerLp 1 gb d)
    mProj_toBare := fun _z => Filter.EventuallyEq.rfl
    uProj :=
      (ContinuousLinearMap.fst ℝ (LpPer gb d) (Fin d → LpPer gb d)).comp
        (ContinuousLinearMap.snd ℝ (LpPer bb d) (SobolevPerLp 1 gb d))
    uProj_toBare := fun _z => Filter.EventuallyEq.rfl
    DProj := fun i =>
      (ContinuousLinearMap.proj i).comp
        ((ContinuousLinearMap.snd ℝ (LpPer gb d) (Fin d → LpPer gb d)).comp
          (ContinuousLinearMap.snd ℝ (LpPer bb d) (SobolevPerLp 1 gb d))) }⟩

/-! ## The admissible set `K_ε` inside the realisation carrier

Paper `eq:def-K-epsilon` (referenced by `Proposition~\ref{thm:strongAepsi.delta}`,
line 1838). In the regularised case the admissible set carries only the
sign constraint `m ≥ 0` a.e. — no mass-constraint clipping, since the
regularisation parameter `ε` controls coercivity directly through the
gradient term of `A_ε^δ`. The non-negative cone in `L^{bb}_per` used to
cut out `K_ε` lives in `Theorems/SimplePower/Banach/WeakLimit.lean`
(`nonNegConeLpPer`, with `nonNegConeLpPer_convex` / `nonNegConeLpPer_isClosed`).
-/

open Filter

/-! ### Sanity exercise -/

/-- Sample: at general exponents `1 < bb, gb < ∞`, a Banach realisation of the
paper's product space exists, witnessing the abstract carrier on which
`Proposition~\ref{thm:strongAepsi.delta}` operates. -/
example
    {bb gb : ℝ≥0∞} [Fact (1 ≤ bb)] [Fact (1 ≤ gb)]
    (hβ : 1 < bb) (hβ_fin : bb ≠ ⊤)
    (hγ : 1 < gb) (hγ_fin : gb ≠ ⊤) :
    Nonempty (BanachRealisation (d := d) bb gb) :=
  exists_banachRealisation hβ hβ_fin hγ hγ_fin

end Periodic

/-! ## The regularised operator body `A_ε^δ` (paper `eq:defAepsi.delta`)
(T3 drain A1d, dead-island cleanup)

The regularised operator body `A_ε^δ : X → StrongDual ℝ X` (paper
`eq:defAepsi.delta`) is the existing bounded CLM family `Aepsi_CLM_op`
(`SimplePower/Banach/AbstractLifts.lean`) instantiated at the substituted
data `H ↦ Hdelta hweak ε`, `D_pH ↦ DpHepsilon hweak qE`, gated behind the
per-primal integrability bundle `MFGOpEpsAuxHyps`.

**A1d retargeting note (island retirement).** An earlier draft of this
module carried a concrete-carrier wrapper `Aepsi_delta_op`, an admissible
set `K_Aepsi_delta_concrete`, three analytic bridges
(`Aepsi_delta_op_{monotone,hemicontinuous,coercive}`), and a long
coercivity-analysis block (`Aepsi_delta_op_coercive_of_aprioriBounds` and
its `Hdelta_coercivity_*` feeders). The A1d retargeting routed the genuine
live Browder–Minty context producer
(`aepsiUniformContextK_delta_of_paperHypotheses_pos`, below) directly
through the generic aggregator
`StationaryMFG.Theorems.SimplePower.Banach.aepsiUniformContextK_of_paperHypotheses_min`,
leaving that entire wrapper island with **zero live consumers** (verified
across `StationaryMFG/`). It has therefore been **retired (deleted)**. The
strict (non-`_ae`) chain that T1/T2 depend on lives entirely in
`SimplePower/Banach/` (`Aepsi_CLM_op`, `K0_Aepsi`/`K_Aepsi`,
`isMonotone_Aepsi_CLM`, `isHemicontinuous_Aepsi_CLM`, `isCoerciveAt_Aepsi_CLM`,
`aepsiUniformContextK_of_paperHypotheses_min`) and is untouched.
-/

namespace InfimalConvolution

open StationaryMFG.Hamiltonian
open StationaryMFG.Solutions.MFG
open StationaryMFG.Theorems.SimplePower.Banach
open scoped ENNReal

variable {d : ℕ}
variable {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
variable {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
variable {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
variable [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)]

/-! ### A1d-final step 1, `HdeltaPos` carrier: `…_pos`
(paper `thm:strongAepsi.delta`, `hMeasNeg`-FREE carrier swap)

`aepsiUniformContextK_delta_of_paperHypotheses_pos` is the
**`{m≤0}`-junk-valued carrier** producer: it threads the
`hMeasNeg`-free carrier `HdeltaPos hweak ε` (which coincides with
`Hdelta hweak ε` on the strict-positivity cone `{0<m}`, where every
Browder–Minty consumer evaluates) through the generic K_Aepsi context
aggregator
`StationaryMFG.Theorems.SimplePower.Banach.aepsiUniformContextK_of_paperHypotheses_min`.

The aggregator is fully carrier-generic over its Hamiltonian `H` (an
implicit variable), so the swap to `HdeltaPos hweak ε` is a literal
substitution — all genuine analytic content lives in
`aepsiUniformContextK_of_paperHypotheses_min` and in the substituted-pair
cert producers supplied by the caller.

This is the entry point that lets the deferred A1d discharge child feed
**`hMeasNeg`-free** substituted-pair certs end-to-end: those produce
`HypothesisMonotone`/`RegularityH` on the `HdeltaPos hweak ε` carrier, whose
`measurable_H` field is discharged from `hFormPos` ALONE (no `{m≤0}`
measurability witness) via `HdeltaPos_measurable_of_formPos`. Stating the
ctx on `HdeltaPos` removes the only obstruction to wiring those `_pos`
producers into the live Browder–Minty supply.

No new oracle: the strict-positive cone `K_Aepsi` is the pre-existing
Browder–Minty operator domain (not a new `0 < m_ε` a-priori claim), there is
no `Hext_finite_at_zero`, and no Brouwer / invariance-of-domain. The swap is
observably identical to the `Hdelta` carrier on `{0<m}` by
`HdeltaPos_eq_Hdelta_of_pos`. -/
open StationaryMFG.Periodic StationaryMFG.Theorems.SimplePower in
noncomputable def aepsiUniformContextK_delta_of_paperHypotheses_pos
    {ε : ℝ}
    (hε : 0 < ε)
    (V : (Fin d → ℝ) → ℝ)
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qE : (Fin d → ℝ) × (Fin d → ℝ) × ℝ → (Fin d → ℝ))
    (hmonEps : Hamiltonian.HypothesisMonotone (d := d)
                (HdeltaPos hweak ε) (DpHepsilon hweak qE))
    (hpowEps : Hamiltonian.HypothesisPowerGrowth (d := d)
                (HdeltaPos hweak ε) (DpHepsilon hweak qE))
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (hExp : SimplePowerExponentFacts γBarReal
                (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
                (ENNReal.ofReal βBarReal'))
    (hβBar_eq : βBarReal = hpowEps.β + 1)
    (hγBar_eq : γBarReal = hpowEps.α * (hpowEps.β + 1) / hpowEps.β)
    (hβBar'_eq : βBarReal' = (hpowEps.β + 1) / hpowEps.β)
    (hγBar'_eq : γBarReal' = γBarReal / (γBarReal - 1))
    (hβ : βBarReal.HolderConjugate βBarReal')
    (hγ : γBarReal.HolderConjugate γBarReal')
    (hβTop : ENNReal.ofReal γBarReal ≠ ⊤)
    (hγ'_le_β : ENNReal.ofReal γBarReal' ≤ ENNReal.ofReal βBarReal)
    (C' : ℝ) (hC'_pos : 0 < C')
    (h_upper :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ p mm, 0 < mm →
          HdeltaPos hweak ε x p mm
            ≤ C' * (‖p‖ ^ hpowEps.α + 1) - (mm ^ hpowEps.β) / C')
    (hF_HJB_meas :
      ∀ q : XBanach d βBarReal γBarReal,
        MeasureTheory.AEStronglyMeasurable
          (fun x => -(uOf q x)
              - HdeltaPos hweak ε x (fun i => DuOf q i x) (mOf q x) + V x)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (hF_flux_meas :
      ∀ q : XBanach d βBarReal γBarReal, ∀ i,
        MeasureTheory.AEStronglyMeasurable
          (fun x => mOf q x
              * DpHepsilon hweak qE x (fun j => DuOf q j x) (mOf q x) i)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (hScalarMono :
      ∀ s t : ℝ,
        0 ≤ (absPowMinusTwo γBarReal t * t - absPowMinusTwo γBarReal s * s)
              * (t - s))
    (hVecMono :
      ∀ v w : Fin d → ℝ,
        0 ≤ (vecAbsPowMinusTwo γBarReal v • v - vecAbsPowMinusTwo γBarReal w • w)
              ⬝ (v - w))
    (hγBar_one_lt : 1 < γBarReal)
    (κCoerc : ℝ) (hκCoerc : 1 < κCoerc)
    (lamCoerc : ℝ) (hlamCoerc : 0 < lamCoerc)
    (Ccoerc : ℝ)
    (hbound_residue :
      ∀ᶠ v in (Bornology.cobounded (XBanach d βBarReal γBarReal)
                  ⊓ Filter.principal (K_Aepsi d βBarReal γBarReal)),
        lamCoerc * aepsiCoerciveGauge (βBarReal := βBarReal) (γBarReal := γBarReal)
            κCoerc v - Ccoerc ≤
          mfgOperatorEpsPair (V := V) (H := HdeltaPos hweak ε)
              (DpH := DpHepsilon hweak qE)
              γBarReal ε (fun i => ⇑(v.2.2 i)) (⇑v.1) (⇑v.2.1)
              (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1)
            - mfgOperatorEpsPair (V := V) (H := HdeltaPos hweak ε)
                (DpH := DpHepsilon hweak qE)
                γBarReal ε (fun _ _ => 0) (fun _ => 1) (fun _ => 0)
                (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1))
    (h_slice :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          HdeltaPos hweak ε x p m
            ≤ -(m ^ hpowEps.β) / hpowEps.C + hpowEps.C
              + hpowEps.C * ‖p‖ ^ hpowEps.α
              + hpowEps.C * ‖p‖ * (m ^ (hpowEps.β - hpowEps.β / hpowEps.α) + 1))
    (hReg : RegularityH (d := d) (HdeltaPos hweak ε) (DpHepsilon hweak qE))
    (hγ2 : 1 < γBarReal)
    (hβconj : βBarReal'.HolderConjugate βBarReal)
    (hγconj : γBarReal'.HolderConjugate γBarReal)
    (hSegMin : PaperSection8SegmentResiduesMin
      (d := d) γBarReal βBarReal βBarReal' γBarReal'
      (HdeltaPos hweak ε) (DpHepsilon hweak qE) hpowEps)
    (hF_unreg_meas : ∀ (u v : XBanach d βBarReal γBarReal),
                u ∈ K_Aepsi d βBarReal γBarReal →
                v ∈ K_Aepsi d βBarReal γBarReal →
                ∀ (w : XBanach d βBarReal γBarReal),
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        MeasureTheory.AEStronglyMeasurable
          (fun x => aepsiIntegrandAt_unreg V (HdeltaPos hweak ε)
                      (DpHepsilon hweak qE)
                      (DuOf v) (DuOf u) (mOf v) (mOf u)
                      (uOf v) (uOf u)
                      (fun i => ⇑(w.2.2 i)) (⇑w.1) (⇑w.2.1) x t)
          (MeasureTheory.volume.restrict (UnitCube d)))
    (hF_gat_meas : ∀ (u v : XBanach d βBarReal γBarReal),
                u ∈ K_Aepsi d βBarReal γBarReal →
                v ∈ K_Aepsi d βBarReal γBarReal →
                ∀ (w : XBanach d βBarReal γBarReal),
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        MeasureTheory.AEStronglyMeasurable
          (fun x => aepsiIntegrandAt_gateaux γBarReal
                      (DuOf v) (DuOf u) (uOf v) (uOf u)
                      (fun i => ⇑(w.2.2 i)) (⇑w.2.1) x t)
          (MeasureTheory.volume.restrict (UnitCube d)))
    (auxHypsK0 : ∀ q ∈ K0_Aepsi d βBarReal γBarReal,
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V (HdeltaPos hweak ε) (DpHepsilon hweak qE)
                    (DuOf q) (mOf q) (uOf q))
    (hWeakDerivK0 :
      ∀ q ∈ K0_Aepsi d βBarReal γBarReal,
        ∀ i, HasWeakDerivPer (d := d) i (uOf q) (DuOf q i)) :
    AepsiUniformContextK (d := d) ε V (HdeltaPos hweak ε) (DpHepsilon hweak qE)
      γBarReal βBarReal βBarReal' γBarReal' :=
  aepsiUniformContextK_of_paperHypotheses_min
    (γBarReal := γBarReal) (βBarReal := βBarReal)
    (βBarReal' := βBarReal') (γBarReal' := γBarReal')
    (V := V) (H := HdeltaPos hweak ε) (DpH := DpHepsilon hweak qE)
    hε hmonEps hpowEps hV hExp
    hβBar_eq hγBar_eq hβBar'_eq hγBar'_eq
    hβ hγ hβTop hγ'_le_β
    C' hC'_pos h_upper hF_HJB_meas hF_flux_meas
    hScalarMono hVecMono hγBar_one_lt
    κCoerc hκCoerc lamCoerc hlamCoerc Ccoerc hbound_residue
    h_slice hReg hγ2 hβconj hγconj hSegMin
    hF_unreg_meas hF_gat_meas auxHypsK0 hWeakDerivK0

/-! ### A1d-final step 9: Group-A-internalised ctx producer `…_pos_closed`
(paper `thm:strongAepsi.delta`)

`aepsiUniformContextK_delta_of_paperHypotheses_pos_closed` is the
**Group-A-closed** wrapper around
`aepsiUniformContextK_delta_of_paperHypotheses_pos`. It internalises the
four **immediately-derivable** ctx residues from the substituted-pair
power-growth bundle `hpowEps` and the exponent facts `hExp`, exactly
mirroring the T1 precedent
`StationaryMFG.Theorems.SimplePower.Banach.aepsiUniformContextK_of_paperHypotheses_closed`
(`AssemblyContext.lean`):

* `hReg := hpowEps.toRegularityH` — `HypothesisPowerGrowth extends
  RegularityH`, so the substituted-pair regularity cert is the
  power-growth bundle's parent projection on the `HdeltaPos` carrier;
* `C' := hpowEps.C`, `hC'_pos := hpowEps.hC` — the growth constant;
* `hγBar_one_lt := hExp.γBar_one_lt_real` — `1 < γBarReal`;
* `hβTop := hExp.gammaBar_lt_top.ne` — `ENNReal.ofReal γBarReal ≠ ⊤`.

The remaining residues stay explicit:

* **Group B** (algebra/exponent identifications `hβBar_eq`, `hγBar_eq`,
  `hβBar'_eq`, `hγBar'_eq`, `hβ`, `hγ`, `hγ'_le_β`, `hγ2`, `hβconj`,
  `hγconj`): only true at the paper exponents, not derivable from
  `(hweak, hpowEps, hV, hExp)` at arbitrary type-level exponents.
* **Group C** (paper §8 analytic residues `h_upper`, `hF_HJB_meas`,
  `hF_flux_meas`, `hScalarMono`, `hVecMono`, the coercivity
  `(κCoerc, …, Ccoerc, hbound_residue)`, `h_slice`, `hSegMin`,
  `hF_unreg_meas`, `hF_gat_meas`, `auxHypsK0`, `hWeakDerivK0`):
  paper-residue inputs authorised per CONVENTIONS §1b.

No new oracle / no `0 < m_ε` / no `Hext_finite_at_zero` / no
`hMeasNeg`: this is a pure projection-and-delegation wrapper. The body
forwards to `…_of_paperHypotheses_pos` with the four Group-A fields
filled. Step 10 (the A1d-final rewire) calls this producer and supplies
only `(hweak, qE, hmonEps, hpowEps, hV, hExp)` plus the Group B/C
authorised residues. -/
open StationaryMFG.Periodic StationaryMFG.Theorems.SimplePower in
noncomputable def aepsiUniformContextK_delta_of_paperHypotheses_pos_closed
    {ε : ℝ}
    (hε : 0 < ε)
    (V : (Fin d → ℝ) → ℝ)
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qE : (Fin d → ℝ) × (Fin d → ℝ) × ℝ → (Fin d → ℝ))
    (hmonEps : Hamiltonian.HypothesisMonotone (d := d)
                (HdeltaPos hweak ε) (DpHepsilon hweak qE))
    (hpowEps : Hamiltonian.HypothesisPowerGrowth (d := d)
                (HdeltaPos hweak ε) (DpHepsilon hweak qE))
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (hExp : SimplePowerExponentFacts γBarReal
                (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
                (ENNReal.ofReal βBarReal'))
    (hβBar_eq : βBarReal = hpowEps.β + 1)
    (hγBar_eq : γBarReal = hpowEps.α * (hpowEps.β + 1) / hpowEps.β)
    (hβBar'_eq : βBarReal' = (hpowEps.β + 1) / hpowEps.β)
    (hγBar'_eq : γBarReal' = γBarReal / (γBarReal - 1))
    (hβ : βBarReal.HolderConjugate βBarReal')
    (hγ : γBarReal.HolderConjugate γBarReal')
    (hγ'_le_β : ENNReal.ofReal γBarReal' ≤ ENNReal.ofReal βBarReal)
    (h_upper :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ p mm, 0 < mm →
          HdeltaPos hweak ε x p mm
            ≤ hpowEps.C * (‖p‖ ^ hpowEps.α + 1) - (mm ^ hpowEps.β) / hpowEps.C)
    (hF_HJB_meas :
      ∀ q : XBanach d βBarReal γBarReal,
        MeasureTheory.AEStronglyMeasurable
          (fun x => -(uOf q x)
              - HdeltaPos hweak ε x (fun i => DuOf q i x) (mOf q x) + V x)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (hF_flux_meas :
      ∀ q : XBanach d βBarReal γBarReal, ∀ i,
        MeasureTheory.AEStronglyMeasurable
          (fun x => mOf q x
              * DpHepsilon hweak qE x (fun j => DuOf q j x) (mOf q x) i)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (hScalarMono :
      ∀ s t : ℝ,
        0 ≤ (absPowMinusTwo γBarReal t * t - absPowMinusTwo γBarReal s * s)
              * (t - s))
    (hVecMono :
      ∀ v w : Fin d → ℝ,
        0 ≤ (vecAbsPowMinusTwo γBarReal v • v - vecAbsPowMinusTwo γBarReal w • w)
              ⬝ (v - w))
    (κCoerc : ℝ) (hκCoerc : 1 < κCoerc)
    (lamCoerc : ℝ) (hlamCoerc : 0 < lamCoerc)
    (Ccoerc : ℝ)
    (hbound_residue :
      ∀ᶠ v in (Bornology.cobounded (XBanach d βBarReal γBarReal)
                  ⊓ Filter.principal (K_Aepsi d βBarReal γBarReal)),
        lamCoerc * aepsiCoerciveGauge (βBarReal := βBarReal) (γBarReal := γBarReal)
            κCoerc v - Ccoerc ≤
          mfgOperatorEpsPair (V := V) (H := HdeltaPos hweak ε)
              (DpH := DpHepsilon hweak qE)
              γBarReal ε (fun i => ⇑(v.2.2 i)) (⇑v.1) (⇑v.2.1)
              (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1)
            - mfgOperatorEpsPair (V := V) (H := HdeltaPos hweak ε)
                (DpH := DpHepsilon hweak qE)
                γBarReal ε (fun _ _ => 0) (fun _ => 1) (fun _ => 0)
                (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1))
    (h_slice :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          HdeltaPos hweak ε x p m
            ≤ -(m ^ hpowEps.β) / hpowEps.C + hpowEps.C
              + hpowEps.C * ‖p‖ ^ hpowEps.α
              + hpowEps.C * ‖p‖ * (m ^ (hpowEps.β - hpowEps.β / hpowEps.α) + 1))
    (hγ2 : 1 < γBarReal)
    (hβconj : βBarReal'.HolderConjugate βBarReal)
    (hγconj : γBarReal'.HolderConjugate γBarReal)
    (hSegMin : PaperSection8SegmentResiduesMin
      (d := d) γBarReal βBarReal βBarReal' γBarReal'
      (HdeltaPos hweak ε) (DpHepsilon hweak qE) hpowEps)
    (hF_unreg_meas : ∀ (u v : XBanach d βBarReal γBarReal),
                u ∈ K_Aepsi d βBarReal γBarReal →
                v ∈ K_Aepsi d βBarReal γBarReal →
                ∀ (w : XBanach d βBarReal γBarReal),
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        MeasureTheory.AEStronglyMeasurable
          (fun x => aepsiIntegrandAt_unreg V (HdeltaPos hweak ε)
                      (DpHepsilon hweak qE)
                      (DuOf v) (DuOf u) (mOf v) (mOf u)
                      (uOf v) (uOf u)
                      (fun i => ⇑(w.2.2 i)) (⇑w.1) (⇑w.2.1) x t)
          (MeasureTheory.volume.restrict (UnitCube d)))
    (hF_gat_meas : ∀ (u v : XBanach d βBarReal γBarReal),
                u ∈ K_Aepsi d βBarReal γBarReal →
                v ∈ K_Aepsi d βBarReal γBarReal →
                ∀ (w : XBanach d βBarReal γBarReal),
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        MeasureTheory.AEStronglyMeasurable
          (fun x => aepsiIntegrandAt_gateaux γBarReal
                      (DuOf v) (DuOf u) (uOf v) (uOf u)
                      (fun i => ⇑(w.2.2 i)) (⇑w.2.1) x t)
          (MeasureTheory.volume.restrict (UnitCube d)))
    (auxHypsK0 : ∀ q ∈ K0_Aepsi d βBarReal γBarReal,
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V (HdeltaPos hweak ε) (DpHepsilon hweak qE)
                    (DuOf q) (mOf q) (uOf q))
    (hWeakDerivK0 :
      ∀ q ∈ K0_Aepsi d βBarReal γBarReal,
        ∀ i, HasWeakDerivPer (d := d) i (uOf q) (DuOf q i)) :
    AepsiUniformContextK (d := d) ε V (HdeltaPos hweak ε) (DpHepsilon hweak qE)
      γBarReal βBarReal βBarReal' γBarReal' :=
  -- Group A — derived internally from `hpowEps` (parent `RegularityH`,
  -- growth constant) and `hExp` (`1 < γBarReal`, `γBarReal ≠ ⊤`).
  aepsiUniformContextK_delta_of_paperHypotheses_pos
    (γBarReal := γBarReal) (βBarReal := βBarReal)
    (βBarReal' := βBarReal') (γBarReal' := γBarReal')
    hε V hweak qE hmonEps hpowEps hV hExp
    hβBar_eq hγBar_eq hβBar'_eq hγBar'_eq
    hβ hγ hExp.gammaBar_lt_top.ne hγ'_le_β
    hpowEps.C hpowEps.hC h_upper hF_HJB_meas hF_flux_meas
    hScalarMono hVecMono hExp.γBar_one_lt_real
    κCoerc hκCoerc lamCoerc hlamCoerc Ccoerc hbound_residue
    h_slice hpowEps.toRegularityH hγ2 hβconj hγconj hSegMin
    hF_unreg_meas hF_gat_meas auxHypsK0 hWeakDerivK0

/-! ### D2 Step 1: per-ε `Aepsi` context FAMILY on the `HdeltaPos`/`DpHepsilonFam`
carrier from selector data (paper `thm:strongAepsi.delta`)

`aepsiDeltaPosContextFamily_of_selectorData` lifts the per-ε `_pos_closed` ctx
producer to a **family** indexed by `ε ∈ (0,1]`, with the regularized pair pinned
on the gate-clean carrier `(HdeltaPos hweak ε, DpHepsilonFam hweak qε ε)`. The
power-growth bundle `hpowEps` is read off the selector-derived
`HdeltaPowerEpsData` carrier `powData` (`powData.hpow ε hε hε1`), exactly the
field the Dq4c producer `hdeltaPowerEpsData_of_selector` assembles. The carrier
identity `DpHepsilon hweak (qε ε) = DpHepsilonFam hweak qε ε` is definitional
(`DpHepsilonFam` is a `rfl`-wrapper around `DpHepsilon hweak (qε ε)`), so the
output type lands literally on `DpHepsilonFam hweak qε ε`.

GATE #1 (D2): no `hH_rc0` / `RegularityH (Hdelta …)` / `HypothesisHat0 (Hdelta …)`
/ `hInj` / `qEofMinv`. The carrier is `HdeltaPos`/`DpHepsilonFam` throughout; the
parent `RegularityH` cert is internalised by `_pos_closed` from
`(powData.hpow ε hε hε1).toRegularityH` (the power-growth bundle's parent
projection on the `HdeltaPos` carrier), NOT from a `Hdelta`-carrier `RegularityH`.

**Monotonicity slot `hmonEpsFam`.** The substituted-pair LL-monotonicity on the
carrier is `lem:H.delta.monotone` (paper line 1754), which the paper proves from
the inf-conv subgradient optimality `eq:inf-conv.diff-relation1` plus the
FTC-slice identity `eq:DpHdelta.dotp.minusH`. Neither the subgradient nor the
FTC slice is carried by `InfConvSelectorFamily`/`HdeltaPowerEpsData`/
`HdeltaUniformBounds` (those carry attainment `H_form`, the gradient formula
`DpH_form`, the growth bundle, and the coercive bounds — but not the
optimality/FTC certificates). The earlier `qEofMinv`-based producer of this
monotonicity routed through the canonical minimizer + global injectivity, both
FORBIDDEN by GATE #1 (and now retired). Deriving it
on the abstract selector `qε` needs NEW analysis (a selector-level subgradient +
FTC-slice certificate); that is split into child `D2a-i`
(`…-D2a-i-selector-monotone-on-hdeltapos`). Until that child lands,
`hmonEpsFam` is threaded as the per-ε selector-monotone certificate parameter —
on the gate-clean `HdeltaPos`/`DpHepsilonFam` carrier (NOT a forbidden rider).

**Group B / Group C residues** are passed through per-ε exactly as `_pos_closed`
accepts them (the exponent identifications at the pinned paper exponents, the
paper §8 analytic residues): authorised per CONVENTIONS §1b and the task's
"accepted Group-C riders as needed". -/

/-! ### D2a-i: substituted-pair LL-monotonicity on `HdeltaPos`/`DpHepsilonFam`
from selector data (NO `qEofMinv`/`hInj`)

`substitutedPair_monotone_of_selector_pos` discharges the `hmonEpsFam` slot left
explicit on `aepsiDeltaPosContextFamily_of_selectorData`. Paper
`lem:H.delta.monotone` (line 1754) on the gate-clean carrier
`(HdeltaPos hweak ε, DpHepsilonFam hweak qε ε)`.

The four a.e. certificates `Hepsilon_monotone_generic` reduces to are supplied by
the selector data: attainment `sel.H_form`, gradient formula `sel.DpH_form`,
subgradient optimality `sel.hSub` (paper `eq:inf-conv.diff-relation1`, first
inclusion), and FTC-slice `sel.hFtcSlice` (paper `eq:DpHdelta.dotp.minusH`). The
carrier `RegularityH` is the parent projection
`(powData.hpow ε hε hε1).toRegularityH`. The carrier-to-`Hdelta` bridge is
`HdeltaPos_eq_Hdelta_of_pos`.

GATE #1: NO `hH_rc0` / `RegularityH (Hdelta …)` / `HypothesisHat0 (Hdelta …)` /
`hInj` / `qEofMinv`. The subgradient/FTC certificates are paper-faithful selector
data internalised by the producer `infConvSelectorFamily_of_weakGrowth` from
`(hmon, hweak, hdiff, hmeas)` alone (see `hSub_qMeasFam` / `hFtcSlice_qMeasFam`),
NOT loose riders. -/
theorem substitutedPair_monotone_of_selector_pos
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hMono : Hamiltonian.HypothesisMonotone (d := d) H DpH)
    (qε : QEpsFamily d)
    (sel : InfConvSelectorFamily (H := H) (DpH := DpH) hweak qε)
    (powData : HdeltaPowerEpsData (H := H) (DpH := DpH) hweak qε) :
    ∀ ε, 0 < ε → ε ≤ 1 →
      Hamiltonian.HypothesisMonotone (d := d)
        (HdeltaPos hweak ε) (DpHepsilonFam hweak qε ε) := by
  intro ε hε hε1
  refine Hepsilon_monotone_generic (H := H) (DpH := DpH) hweak hMono hε
    (Hε := fun x p m => HdeltaPos hweak ε x p m)
    (DpHε := DpHepsilonFam hweak qε ε)
    (qOf := fun x p m => qε ε (x, p, m))
    ((powData.hpow ε hε hε1).toRegularityH)
    (fun x p m hm => HdeltaPos_eq_Hdelta_of_pos hweak hm)
    (sel.H_form ε hε)
    (sel.DpH_form ε hε)
    (sel.hSub ε hε)
    ?_
  -- FTC slice on the `HdeltaPos` carrier: on `{0<m}`, `HdeltaPos = Hdelta` (both
  -- at `p` and at `0`), so the selector's `Hdelta`-carrier slice transfers.
  filter_upwards [sel.hFtcSlice ε hε] with x hx
  intro p m hm
  rw [HdeltaPos_eq_Hdelta_of_pos hweak hm, HdeltaPos_eq_Hdelta_of_pos hweak hm]
  exact hx p m hm

open StationaryMFG.Periodic StationaryMFG.Theorems.SimplePower in
noncomputable def aepsiDeltaPosContextFamily_of_selectorData
    (V : (Fin d → ℝ) → ℝ)
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hMono : Hamiltonian.HypothesisMonotone (d := d) H DpH)
    (qε : QEpsFamily d)
    (sel : InfConvSelectorFamily (H := H) (DpH := DpH) hweak qε)
    (powData : HdeltaPowerEpsData (H := H) (DpH := DpH) hweak qε)
    (_uniform : HdeltaUniformBounds (H := H) (DpH := DpH) hweak qε)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (hExp : SimplePowerExponentFacts γBarReal
                (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
                (ENNReal.ofReal βBarReal'))
    -- Group B exponent identities at the pinned paper exponents.
    (hβBar_eq : ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      βBarReal = (powData.hpow ε hε hε1).β + 1)
    (hγBar_eq : ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      γBarReal = (powData.hpow ε hε hε1).α * ((powData.hpow ε hε hε1).β + 1)
        / (powData.hpow ε hε hε1).β)
    (hβBar'_eq : ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      βBarReal' = ((powData.hpow ε hε hε1).β + 1) / (powData.hpow ε hε hε1).β)
    (hγBar'_eq : γBarReal' = γBarReal / (γBarReal - 1))
    (hβ : βBarReal.HolderConjugate βBarReal')
    (hγ : γBarReal.HolderConjugate γBarReal')
    (hγ'_le_β : ENNReal.ofReal γBarReal' ≤ ENNReal.ofReal βBarReal)
    (hγ2 : 1 < γBarReal)
    (hβconj : βBarReal'.HolderConjugate βBarReal)
    (hγconj : γBarReal'.HolderConjugate γBarReal)
    -- Group C analytic residues (paper §8), per-ε on the `HdeltaPos` carrier.
    (h_upper : ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ p mm, 0 < mm →
          HdeltaPos hweak ε x p mm
            ≤ (powData.hpow ε hε hε1).C * (‖p‖ ^ (powData.hpow ε hε hε1).α + 1)
              - (mm ^ (powData.hpow ε hε hε1).β) / (powData.hpow ε hε hε1).C)
    (hF_HJB_meas : ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      ∀ q : XBanach d βBarReal γBarReal,
        MeasureTheory.AEStronglyMeasurable
          (fun x => -(uOf q x)
              - HdeltaPos hweak ε x (fun i => DuOf q i x) (mOf q x) + V x)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (hF_flux_meas : ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      ∀ q : XBanach d βBarReal γBarReal, ∀ i,
        MeasureTheory.AEStronglyMeasurable
          (fun x => mOf q x
              * DpHepsilonFam hweak qε ε x (fun j => DuOf q j x) (mOf q x) i)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (hScalarMono :
      ∀ s t : ℝ,
        0 ≤ (absPowMinusTwo γBarReal t * t - absPowMinusTwo γBarReal s * s)
              * (t - s))
    (hVecMono :
      ∀ v w : Fin d → ℝ,
        0 ≤ (vecAbsPowMinusTwo γBarReal v • v - vecAbsPowMinusTwo γBarReal w • w)
              ⬝ (v - w))
    (κCoerc : ℝ) (hκCoerc : 1 < κCoerc)
    (lamCoerc : ℝ) (hlamCoerc : 0 < lamCoerc)
    (Ccoerc : ℝ)
    (hbound_residue : ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      ∀ᶠ v in (Bornology.cobounded (XBanach d βBarReal γBarReal)
                  ⊓ Filter.principal (K_Aepsi d βBarReal γBarReal)),
        lamCoerc * aepsiCoerciveGauge (βBarReal := βBarReal) (γBarReal := γBarReal)
            κCoerc v - Ccoerc ≤
          mfgOperatorEpsPair (V := V) (H := HdeltaPos hweak ε)
              (DpH := DpHepsilonFam hweak qε ε)
              γBarReal ε (fun i => ⇑(v.2.2 i)) (⇑v.1) (⇑v.2.1)
              (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1)
            - mfgOperatorEpsPair (V := V) (H := HdeltaPos hweak ε)
                (DpH := DpHepsilonFam hweak qε ε)
                γBarReal ε (fun _ _ => 0) (fun _ => 1) (fun _ => 0)
                (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1))
    (h_slice : ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          HdeltaPos hweak ε x p m
            ≤ -(m ^ (powData.hpow ε hε hε1).β) / (powData.hpow ε hε hε1).C
              + (powData.hpow ε hε hε1).C
              + (powData.hpow ε hε hε1).C * ‖p‖ ^ (powData.hpow ε hε hε1).α
              + (powData.hpow ε hε hε1).C * ‖p‖
                * (m ^ ((powData.hpow ε hε hε1).β
                    - (powData.hpow ε hε hε1).β / (powData.hpow ε hε hε1).α) + 1))
    (hSegMin : ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      PaperSection8SegmentResiduesMin
        (d := d) γBarReal βBarReal βBarReal' γBarReal'
        (HdeltaPos hweak ε) (DpHepsilonFam hweak qε ε) (powData.hpow ε hε hε1))
    (hF_unreg_meas : ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      ∀ (u v : XBanach d βBarReal γBarReal),
                u ∈ K_Aepsi d βBarReal γBarReal →
                v ∈ K_Aepsi d βBarReal γBarReal →
                ∀ (w : XBanach d βBarReal γBarReal),
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        MeasureTheory.AEStronglyMeasurable
          (fun x => aepsiIntegrandAt_unreg V (HdeltaPos hweak ε)
                      (DpHepsilonFam hweak qε ε)
                      (DuOf v) (DuOf u) (mOf v) (mOf u)
                      (uOf v) (uOf u)
                      (fun i => ⇑(w.2.2 i)) (⇑w.1) (⇑w.2.1) x t)
          (MeasureTheory.volume.restrict (UnitCube d)))
    (hF_gat_meas : ∀ (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1),
      ∀ (u v : XBanach d βBarReal γBarReal),
                u ∈ K_Aepsi d βBarReal γBarReal →
                v ∈ K_Aepsi d βBarReal γBarReal →
                ∀ (w : XBanach d βBarReal γBarReal),
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        MeasureTheory.AEStronglyMeasurable
          (fun x => aepsiIntegrandAt_gateaux γBarReal
                      (DuOf v) (DuOf u) (uOf v) (uOf u)
                      (fun i => ⇑(w.2.2 i)) (⇑w.2.1) x t)
          (MeasureTheory.volume.restrict (UnitCube d)))
    (auxHypsK0 : ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      ∀ q ∈ K0_Aepsi d βBarReal γBarReal,
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V (HdeltaPos hweak ε) (DpHepsilonFam hweak qε ε)
                    (DuOf q) (mOf q) (uOf q))
    (hWeakDerivK0 :
      ∀ q ∈ K0_Aepsi d βBarReal γBarReal,
        ∀ i, HasWeakDerivPer (d := d) i (uOf q) (DuOf q i)) :
    ∀ ε (hε : 0 < ε) (_hε1 : ε ≤ 1),
      AepsiUniformContextK (d := d) ε V (HdeltaPos hweak ε)
        (DpHepsilonFam hweak qε ε)
        γBarReal βBarReal βBarReal' γBarReal' :=
  fun ε hε hε1 =>
    aepsiUniformContextK_delta_of_paperHypotheses_pos_closed
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      hε V hweak (qε ε)
      (substitutedPair_monotone_of_selector_pos (H := H) (DpH := DpH)
        hweak hMono qε sel powData ε hε hε1)
      (powData.hpow ε hε hε1) hV hExp
      (hβBar_eq ε hε hε1) (hγBar_eq ε hε hε1) (hβBar'_eq ε hε hε1) hγBar'_eq
      hβ hγ hγ'_le_β
      (h_upper ε hε hε1) (hF_HJB_meas ε hε hε1) (hF_flux_meas ε hε hε1)
      hScalarMono hVecMono
      κCoerc hκCoerc lamCoerc hlamCoerc Ccoerc (hbound_residue ε hε hε1)
      (h_slice ε hε hε1) hγ2 hβconj hγconj (hSegMin ε hε hε1)
      (hF_unreg_meas ε hε hε1) (hF_gat_meas ε hε hε1)
      (auxHypsK0 ε hε hε1) hWeakDerivK0

/-! ### D2b-2b: the per-ε `AepsiUniformContextK` family on the `HdeltaK0` carrier

`aepsiDeltaContextFamily_K0_of_selectorData` is the **additive** `HdeltaK0`-keyed
sibling of `aepsiDeltaPosContextFamily_of_selectorData`. It builds the per-ε
`AepsiUniformContextK` on the c4d carrier `HdeltaK0 hweak ε /
DpHepsilon hweak (qε ε)` *without* a `RegularityH (HdeltaK0)` (the global `{m=0}`
`iInf` measurability the c4c/c4d design avoids): the three operator-level fields
(`hMono`/`hHC`/`hCoerc`) are TRANSFERRED from the already-built `HdeltaPos`
context via the D2b-2a carrier-congruence lemma `mfgOperatorEpsPair_congr_H_ae`
(through `Aepsi_CLM_opK_apply_of_mem`) using `HdeltaK0_eq_HdeltaPos_of_pos` on the
strict-positivity cone `K_Aepsi` (where the density `m = ⇑v.1 > 0` a.e., so
`HdeltaK0 = HdeltaPos` a.e. in the operator integrand). The K_Aepsi-indexed
`auxHypsK` is transferred by the same positive-density a.e. congruence. The
non-operator fields (`hReflexive`/`qRef`/`hqRef`/`aux`/`hWeakDeriv`) are
carrier-free or reconstructed on `HdeltaK0` from the `{0<m}`/`{0≤m}`-restricted
inputs (the `K0`-keyed `auxHypsK0`/`hWeakDerivK0` riders — the SAME rider shape
the `HdeltaPos` family already consumes, NOT a new rider).

GATE #1: the produced context carries NO `RegularityH (HdeltaK0)` /
`HypothesisHat0 (HdeltaK0)` / raw `hH_rc0` / `hInj` / `qEofMinv`.
`RegularityH (HdeltaPos)` / `HypothesisPowerGrowth (HdeltaPos)` enter only inside
the internally-built `HdeltaPos` context `ctxPos`. -/

open StationaryMFG.Periodic StationaryMFG.Theorems.SimplePower in
/-- **`MFGOpEpsAuxHyps` carrier-transfer on the strict-positivity cone.** For a
Banach pair `q` whose density is strictly positive a.e. (`q ∈ K_Aepsi`), the
primal aux record on the `HdeltaPos` carrier transfers to the `HdeltaK0`
carrier: the only `H`-dependent field is `hF_HJB`, and on `{0<m}` (where
`m = ⇑q.1`) the two carriers agree (`HdeltaK0_eq_HdeltaPos_of_pos`), so
`F_HJB V (HdeltaK0 …) … =ᵐ F_HJB V (HdeltaPos …) …` and `MemLpPer` transfers via
`MemLpPer.congr_ae_unitCube`. `DpHepsilonFam = DpHepsilon` (defeq), so the
`F_flux`/`F_mass`/`G_*` fields are unchanged. -/
theorem mfgOpEpsAuxHyps_HdeltaK0_of_HdeltaPos_KAepsi
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    (qE : (Fin d → ℝ) × (Fin d → ℝ) × ℝ → (Fin d → ℝ))
    {q : XBanach d βBarReal γBarReal}
    (hq : q ∈ K_Aepsi d βBarReal γBarReal)
    (h : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
            V (HdeltaPos hweak ε) (DpHepsilon hweak qE)
            (DuOf q) (mOf q) (uOf q)) :
    MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
      V (HdeltaK0 hweak ε) (DpHepsilon hweak qE)
      (DuOf q) (mOf q) (uOf q) := by
  -- On `K_Aepsi`, the density `mOf q = ⇑q.1` is `> 0` a.e.
  have hpos : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      0 < mOf q x := hq
  -- `F_HJB` on the two carriers agrees a.e. on `{0<m}`.
  have hFHJB :
      (Banach.F_HJB V (HdeltaPos hweak ε) (DuOf q) (mOf q) (uOf q))
        =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
      (Banach.F_HJB V (HdeltaK0 hweak ε) (DuOf q) (mOf q) (uOf q)) := by
    filter_upwards [hpos] with x hx
    simp only [Banach.F_HJB]
    rw [HdeltaK0_eq_HdeltaPos_of_pos hweak hx]
  refine
    { hβ := h.hβ
      hγ := h.hγ
      hF_HJB := MemLpPer.congr_ae_unitCube h.hF_HJB hFHJB
      hF_flux := h.hF_flux
      hF_mass := h.hF_mass
      hG_grad := h.hG_grad
      hG_val := h.hG_val
      hβTop := h.hβTop }

open StationaryMFG.Periodic StationaryMFG.Theorems.SimplePower in
/-- **`HdeltaPos → Hdelta` aux transfer on `K_Aepsi`.** Sibling of
`mfgOpEpsAuxHyps_HdeltaK0_of_HdeltaPos_KAepsi`. On the strict-positivity cone
`K_Aepsi` (where `mOf q > 0` a.e.) the genuine `Hdelta` and the truncated
`HdeltaPos` carriers agree a.e. in the positive-density integrand, so the only
carrier-sensitive `MFGOpEpsAuxHyps` field (`hF_HJB`, the `Lᵝ'`-membership of
`F_HJB V H …`) transfers verbatim via `HdeltaPos_eq_Hdelta_of_pos`. All other
fields are carrier-free. This is the deferred carrier identification used by the
AE coercivity rider to feed `paperSection8_coercivity_of_AEData`'s `auxHypsK`
(stated on raw `Hdelta`) from the `HdeltaPos`-keyed D2c2c producer
`mfgOpEpsAuxHyps_HdeltaPos_of_AEData`. -/
theorem mfgOpEpsAuxHyps_Hdelta_of_HdeltaPos_KAepsi
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    (DpHc : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    {q : XBanach d βBarReal γBarReal}
    (hq : q ∈ K_Aepsi d βBarReal γBarReal)
    (h : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
            V (HdeltaPos hweak ε) DpHc
            (DuOf q) (mOf q) (uOf q)) :
    MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
      V (Hdelta hweak ε) DpHc
      (DuOf q) (mOf q) (uOf q) := by
  -- On `K_Aepsi`, the density `mOf q = ⇑q.1` is `> 0` a.e.
  have hpos : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      0 < mOf q x := hq
  -- `F_HJB` on the two carriers agrees a.e. on `{0<m}`.
  have hFHJB :
      (Banach.F_HJB V (HdeltaPos hweak ε) (DuOf q) (mOf q) (uOf q))
        =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
      (Banach.F_HJB V (Hdelta hweak ε) (DuOf q) (mOf q) (uOf q)) := by
    filter_upwards [hpos] with x hx
    simp only [Banach.F_HJB]
    rw [HdeltaPos_eq_Hdelta_of_pos hweak hx]
  refine
    { hβ := h.hβ
      hγ := h.hγ
      hF_HJB := MemLpPer.congr_ae_unitCube h.hF_HJB hFHJB
      hF_flux := h.hF_flux
      hF_mass := h.hF_mass
      hG_grad := h.hG_grad
      hG_val := h.hG_val
      hβTop := h.hβTop }

open StationaryMFG.Periodic StationaryMFG.Theorems.SimplePower in
/-- **Operator-level carrier transfer on `K_Aepsi`** (D2b-2a applied). For
`v ∈ K_Aepsi`, the totalized CLM operator on the `HdeltaK0` carrier equals the
one on the `HdeltaPos` carrier, as elements of `StrongDual ℝ X`. Both reduce to
`mfgOperatorEpsPair` via `Aepsi_CLM_opK_apply_of_mem`, then
`mfgOperatorEpsPair_congr_H_ae` swaps the carrier using the positive-density
a.e. agreement `HdeltaK0_eq_HdeltaPos_of_pos`. -/
theorem aepsi_CLM_opK_HdeltaK0_eq_HdeltaPos_on_KAepsi
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    {ε : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    (qE : (Fin d → ℝ) × (Fin d → ℝ) × ℝ → (Fin d → ℝ))
    (auxHypsK0 : ∀ q ∈ K_Aepsi d βBarReal γBarReal,
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V (HdeltaK0 hweak ε) (DpHepsilon hweak qE)
                    (fun i => ⇑(q.2.2 i)) (⇑q.1) (⇑q.2.1))
    (auxHypsPos : ∀ q ∈ K_Aepsi d βBarReal γBarReal,
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V (HdeltaPos hweak ε) (DpHepsilon hweak qE)
                    (fun i => ⇑(q.2.2 i)) (⇑q.1) (⇑q.2.1))
    {v : XBanach d βBarReal γBarReal}
    (hv : v ∈ K_Aepsi d βBarReal γBarReal) :
    Banach.Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        V (HdeltaK0 hweak ε) (DpHepsilon hweak qE) auxHypsK0 ε v
      = Banach.Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        V (HdeltaPos hweak ε) (DpHepsilon hweak qE) auxHypsPos ε v := by
  -- Positive density on `K_Aepsi`.
  have hpos : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      0 < (⇑v.1 : (Fin d → ℝ) → ℝ) x := hv
  -- `H`-side a.e. agreement on `{0<m}`.
  have hH :
      (fun x => HdeltaK0 hweak ε x (fun i => (⇑(v.2.2 i)) x) ((⇑v.1) x))
        =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
      (fun x => HdeltaPos hweak ε x (fun i => (⇑(v.2.2 i)) x) ((⇑v.1) x)) := by
    filter_upwards [hpos] with x hx
    exact HdeltaK0_eq_HdeltaPos_of_pos hweak hx
  -- Extensional equality of the two `StrongDual` operators on `K_Aepsi`.
  apply ContinuousLinearMap.ext
  intro q
  rw [Banach.Aepsi_CLM_opK_apply_of_mem (γBarReal := γBarReal)
        (βBarReal := βBarReal) (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        V (HdeltaK0 hweak ε) (DpHepsilon hweak qE) auxHypsK0 ε hv q,
      Banach.Aepsi_CLM_opK_apply_of_mem (γBarReal := γBarReal)
        (βBarReal := βBarReal) (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        V (HdeltaPos hweak ε) (DpHepsilon hweak qE) auxHypsPos ε hv q]
  exact Solutions.MFG.mfgOperatorEpsPair_congr_H_ae (V := V)
    (H := HdeltaK0 hweak ε) (DpH := DpHepsilon hweak qE)
    γBarReal ε (HdeltaPos hweak ε) (DpHepsilon hweak qE)
    (fun i => ⇑(v.2.2 i)) (⇑v.1) (⇑v.2.1)
    (fun i => ⇑(q.2.2 i)) (⇑q.1) (⇑q.2.1)
    hH (Filter.EventuallyEq.refl _ _)

open StationaryMFG.Periodic StationaryMFG.Theorems.SimplePower in
/-- **D2c-2a: the eight pure-analytic / measurability riders of
`aepsiDeltaContextFamily_K0_of_selectorData`, discharged from `powData`.**

The `HdeltaPos hweak ε`-keyed regularised power-growth bundle
`powData.hpow ε hε hε1`
(`HypothesisPowerGrowth (HdeltaPos hweak ε) (DpHepsilonFam hweak qε ε)`,
delivered by `hdeltaPowerEpsData_of_selector`, Properties.lean) supplies the
strict structure needed by the T1 field producers
`paperSection8_*_of_powerGrowth` / `paperSection8_h{Scalar,Vec}Mono_of_gamma`
(Banach/AssemblyContext.lean, visible here via the transitive
`Coercivity.Integrability → Banach.AssemblyContext` import). This producer
applies them per-`ε` at the regularised carrier, matching exactly the
ε-indexed binder forms `aepsiDeltaContextFamily_K0_of_selectorData` consumes,
so the parent `of_paperHypotheses` (D2c-2d) need not bind these eight riders.

GATE: binds ONLY `powData` / `hV` / `1 < γBarReal`; no `ctx`, no `Pack`/
`Inputs`/`Oracle`, no `hpowEps`-as-binder (the strict per-`ε` bundle is read
off `powData`, the gate-allowed §1b carrier). -/
theorem aepsiDeltaK0_analyticMeasRiders_of_powData
    {γBarReal' : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d)
    (powData : HdeltaPowerEpsData (H := H) (DpH := DpH) hweak qε)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (hγ2 : 1 < γBarReal) :
    -- `h_upper`
    (∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ p mm, 0 < mm →
          HdeltaPos hweak ε x p mm
            ≤ (powData.hpow ε hε hε1).C * (‖p‖ ^ (powData.hpow ε hε hε1).α + 1)
              - (mm ^ (powData.hpow ε hε hε1).β) / (powData.hpow ε hε hε1).C)
    ∧ -- `hF_HJB_meas`
    (∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      ∀ q : XBanach d βBarReal γBarReal,
        MeasureTheory.AEStronglyMeasurable
          (fun x => -(uOf q x)
              - HdeltaPos hweak ε x (fun i => DuOf q i x) (mOf q x) + V x)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    ∧ -- `hF_flux_meas`
    (∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      ∀ q : XBanach d βBarReal γBarReal, ∀ i,
        MeasureTheory.AEStronglyMeasurable
          (fun x => mOf q x
              * DpHepsilonFam hweak qε ε x (fun j => DuOf q j x) (mOf q x) i)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    ∧ -- `hScalarMono`
    (∀ s t : ℝ,
        0 ≤ (absPowMinusTwo γBarReal t * t - absPowMinusTwo γBarReal s * s)
              * (t - s))
    ∧ -- `hVecMono`
    (∀ v w : Fin d → ℝ,
        0 ≤ (vecAbsPowMinusTwo γBarReal v • v - vecAbsPowMinusTwo γBarReal w • w)
              ⬝ (v - w))
    ∧ -- `h_slice`
    (∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          HdeltaPos hweak ε x p m
            ≤ -(m ^ (powData.hpow ε hε hε1).β) / (powData.hpow ε hε hε1).C
              + (powData.hpow ε hε hε1).C
              + (powData.hpow ε hε hε1).C * ‖p‖ ^ (powData.hpow ε hε hε1).α
              + (powData.hpow ε hε hε1).C * ‖p‖
                * (m ^ ((powData.hpow ε hε hε1).β
                    - (powData.hpow ε hε hε1).β / (powData.hpow ε hε hε1).α) + 1))
    ∧ -- `hF_unreg_meas`
    (∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      ∀ (u v : XBanach d βBarReal γBarReal),
                u ∈ K_Aepsi d βBarReal γBarReal →
                v ∈ K_Aepsi d βBarReal γBarReal →
                ∀ (w : XBanach d βBarReal γBarReal),
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        MeasureTheory.AEStronglyMeasurable
          (fun x => aepsiIntegrandAt_unreg V (HdeltaPos hweak ε)
                      (DpHepsilonFam hweak qε ε)
                      (DuOf v) (DuOf u) (mOf v) (mOf u)
                      (uOf v) (uOf u)
                      (fun i => ⇑(w.2.2 i)) (⇑w.1) (⇑w.2.1) x t)
          (MeasureTheory.volume.restrict (UnitCube d)))
    ∧ -- `hF_gat_meas`
    (∀ (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1),
      ∀ (u v : XBanach d βBarReal γBarReal),
                u ∈ K_Aepsi d βBarReal γBarReal →
                v ∈ K_Aepsi d βBarReal γBarReal →
                ∀ (w : XBanach d βBarReal γBarReal),
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        MeasureTheory.AEStronglyMeasurable
          (fun x => aepsiIntegrandAt_gateaux γBarReal
                      (DuOf v) (DuOf u) (uOf v) (uOf u)
                      (fun i => ⇑(w.2.2 i)) (⇑w.2.1) x t)
          (MeasureTheory.volume.restrict (UnitCube d))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun ε hε hε1 =>
      paperSection8_h_upper_of_powerGrowth (powData.hpow ε hε hε1)
  · exact fun ε hε hε1 =>
      paperSection8_hF_HJB_meas_of_powerGrowth
        (γBarReal := γBarReal) (βBarReal := βBarReal)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        (powData.hpow ε hε hε1) hV
  · exact fun ε hε hε1 =>
      paperSection8_hF_flux_meas_of_powerGrowth
        (γBarReal := γBarReal) (βBarReal := βBarReal)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        (V := V) (powData.hpow ε hε hε1)
  · exact paperSection8_hScalarMono_of_gamma hγ2
  · exact paperSection8_hVecMono_of_gamma (d := d) hγ2
  · exact fun ε hε hε1 =>
      paperSection8_hSlice_of_powerGrowth (powData.hpow ε hε hε1)
  · exact fun ε hε hε1 =>
      paperSection8_hF_unreg_meas_of_powerGrowth
        (γBarReal := γBarReal) (βBarReal := βBarReal)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        (powData.hpow ε hε hε1) hV
  · exact fun ε hε hε1 =>
      paperSection8_hF_gat_meas_of_powerGrowth
        (γBarReal := γBarReal) (βBarReal := βBarReal)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')

open StationaryMFG.Periodic StationaryMFG.Theorems.SimplePower in
/-- **D2c-2c: per-`q` `MFGOpEpsAuxHyps` on the `HdeltaPos` carrier from AE data.**

AE sibling of `auxHyps_K0_at_setPaperTriple` (Banach/AssemblyContext.lean):
produces the primal auxiliary-hypotheses record on the `HdeltaPos hweak ε`
carrier for a single non-negativity-cone element `q ∈ K0_Aepsi`, keyed off the
a.e. estimate carrier `HdeltaAEPowerEpsData` (NOT `HypothesisPowerGrowth`).

The two `H`/`DpH`-dependent dominator memberships are discharged via the
`hpow`-free bare dominator keystones `g_dominator_memLp_betaBar'_bare`
(HJB side, at constant `C := Cε := CdeltaEps hweak ε`) and
`flux_dominator_memLpPer_explicit` (flux side), with the pointwise abs/norm
bounds taken from `hAE.H_upper_pointwise_ae`/`hAE.lower_ae` (HJB) and
`hAE.DpH_upper_ae` (flux), all restricted to `{0 < m}` and trivialised at
`m = 0` (where `HdeltaPos … 0 = 0` and `mOf q · DpH … = 0`).

GATE: binds `(hweak, qε, hAE, hV, …)`; NO `powData`, NO
`HypothesisPowerGrowth (HdeltaPos …)`, NO `hqE_per`/`hFormPos`/`hInj`/`hSurj`/
`qEofMinv`. -/
theorem mfgOpEpsAuxHyps_HdeltaPos_of_AEData
    (V : (Fin d → ℝ) → ℝ)
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d)
    (hAE : HdeltaAEPowerEpsData (H := H) (DpH := DpH) hweak qε)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (hβBar_eq : βBarReal = hweak.β + 1)
    (hγBar_eq : γBarReal = hweak.α * (hweak.β + 1) / hweak.β)
    (hβBar'_eq : βBarReal' = (hweak.β + 1) / hweak.β)
    (hγBar'_eq : γBarReal' = γBarReal / (γBarReal - 1))
    (hβ : βBarReal.HolderConjugate βBarReal')
    (hγ : γBarReal.HolderConjugate γBarReal')
    (hβTop : ENNReal.ofReal γBarReal ≠ ⊤)
    (hγ'_le_β : ENNReal.ofReal γBarReal' ≤ ENNReal.ofReal βBarReal)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hF_HJB_meas :
      ∀ q : XBanach d βBarReal γBarReal,
        MeasureTheory.AEStronglyMeasurable
          (fun x => -(uOf q x)
              - HdeltaPos hweak ε x (fun i => DuOf q i x) (mOf q x) + V x)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (hF_flux_meas :
      ∀ q : XBanach d βBarReal γBarReal, ∀ i,
        MeasureTheory.AEStronglyMeasurable
          (fun x => mOf q x
              * DpHepsilonFam hweak qε ε x (fun j => DuOf q j x) (mOf q x) i)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d))) :
    ∀ q ∈ K0_Aepsi d βBarReal γBarReal,
      MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
        V (HdeltaPos hweak ε) (DpHepsilonFam hweak qε ε)
        (DuOf q) (mOf q) (uOf q) := by
  classical
  -- Standing exponent positivity.
  have hα_pos : 0 < hweak.α := lt_trans Real.zero_lt_one hweak.hα
  have hβ_pos : 0 < hweak.β := hweak.hβ
  have hβ1_pos : 0 < hweak.β + 1 := by linarith
  have hγBarReal_pos : 0 < γBarReal := by
    rw [hγBar_eq]; exact div_pos (mul_pos hα_pos hβ1_pos) hβ_pos
  have hγBar_one_lt_real : 1 < γBarReal := by
    rw [hγBar_eq]; rw [lt_div_iff₀ hβ_pos, one_mul]
    have h1 : (1 : ℝ) * (hweak.β + 1) < hweak.α * (hweak.β + 1) :=
      mul_lt_mul_of_pos_right hweak.hα hβ1_pos
    nlinarith [h1]
  -- Per-`ε` constant.
  set Cε : ℝ := CdeltaEps (H := H) (DpH := DpH) hweak ε with hCε_def
  have hCε_pos : 0 < Cε := (cdeltaEps_facts_upper (H := H) (DpH := DpH) hweak hε).1
  intro q hq_K0
  -- `q ∈ K0_Aepsi ⇒ 0 ≤ mOf q a.e.`.
  have hμ_nn :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ mOf q x := hq_K0
  -- `MemLpPer` certificates from the Lp components.
  have hmLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal) (mOf q) :=
    memLpPer_of_lpPer (d := d) q.1
  have huLp : MemLpPer (d := d) (ENNReal.ofReal γBarReal) (uOf q) :=
    memLpPer_of_lpPer (d := d) q.2.1
  have hDuLp : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (DuOf q i) := by
    intro i; exact memLpPer_of_lpPer (d := d) (q.2.2 i)
  -- Reframe regularity at the paper exponents (off `α, β`).
  have hμ_paperBetaBar :
      MemLpPer (d := d) (ENNReal.ofReal (hweak.β + 1)) (mOf q) := by
    rw [← hβBar_eq]; exact hmLp
  have hυ_paperGammaBar :
      MemLpPer (d := d)
        (ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β)) (uOf q) := by
    rw [← hγBar_eq]; exact huLp
  have hDυ_paperGammaBar : ∀ i,
      MemLpPer (d := d)
        (ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β)) (DuOf q i) := by
    intro i; rw [← hγBar_eq]; exact hDuLp i
  have hV_paperBetaBar' :
      MemLpPer (d := d) (ENNReal.ofReal ((hweak.β + 1) / hweak.β)) V := by
    rw [← hβBar'_eq]; exact hV
  -- HJB dominator (bare keystone, constant `C := Cε`).
  have hG_HJB_dom_paper :
      MemLpPer (d := d) (ENNReal.ofReal ((hweak.β + 1) / hweak.β))
        (fun x : (Fin d → ℝ) =>
          Cε * (‖fun i => DuOf q i x‖ ^ hweak.α + 1)
            + Cε * (mOf q x ^ hweak.β + 1)
            + |uOf q x| + |V x|) :=
    Hamiltonian.g_dominator_memLp_betaBar'_bare
      (β := hweak.β) (α := hweak.α) (C := Cε) hweak.hα hweak.hβ
      V (uOf q) (mOf q) (DuOf q)
      hμ_paperBetaBar hυ_paperGammaBar hDυ_paperGammaBar hV_paperBetaBar' hCε_pos
  have hG_HJB_dom :
      MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x : (Fin d → ℝ) =>
          Cε * (‖fun i => DuOf q i x‖ ^ hweak.α + 1)
            + Cε * (mOf q x ^ hweak.β + 1)
            + |uOf q x| + |V x|) := by
    rw [hβBar'_eq]; exact hG_HJB_dom_paper
  -- Flux dominator (bare keystone).
  have hG_flux_dom_paper :
      MemLpPer (d := d)
        (ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β /
          (hweak.α * (hweak.β + 1) / hweak.β - 1)))
        (fun x : (Fin d → ℝ) =>
          Cε * (mOf q x * ‖fun j => DuOf q j x‖ ^ (hweak.α - 1)
                      + mOf q x ^ (1 + hweak.β - hweak.β / hweak.α) + mOf q x)) :=
    Hamiltonian.flux_dominator_memLpPer_explicit
      (α := hweak.α) (β := hweak.β) (C := Cε) hweak.hα hweak.hβ
      (mOf q) (DuOf q) hμ_paperBetaBar hDυ_paperGammaBar
  have hG_flux_dom :
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x : (Fin d → ℝ) =>
          Cε * (mOf q x * ‖fun j => DuOf q j x‖ ^ (hweak.α - 1)
                      + mOf q x ^ (1 + hweak.β - hweak.β / hweak.α) + mOf q x)) := by
    have hγ'_paper_eq :
        γBarReal' = hweak.α * (hweak.β + 1) / hweak.β /
                    (hweak.α * (hweak.β + 1) / hweak.β - 1) := by
      rw [hγBar'_eq, hγBar_eq]
    rw [hγ'_paper_eq]; exact hG_flux_dom_paper
  -- G-side memberships.
  have hG_grad_mem : ∀ i,
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (G_grad γBarReal (DuOf q) i) := by
    intro i
    exact G_grad_memLpPer_gammaBar' hγBar_one_lt_real hγBar'_eq (DuOf q) hDuLp i
  have hG_val_mem :
      MemLpPer (d := d) (ENNReal.ofReal γBarReal') (G_val γBarReal (uOf q)) :=
    G_val_memLpPer_gammaBar' hγBar_one_lt_real hγBar'_eq (uOf q) huLp
  -- ----------------------------------------------------------------------
  -- `hF_HJB`: `‖-u - HdeltaPos + V‖ ≤ G_HJB` a.e. (via two-sided AE bound).
  -- ----------------------------------------------------------------------
  have hF_HJB_bound :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ‖-(uOf q x)
            - HdeltaPos hweak ε x (fun i => DuOf q i x) (mOf q x) + V x‖
          ≤ (1 : ℝ) *
            ‖Cε * (‖fun i => DuOf q i x‖ ^ hweak.α + 1)
              + Cε * (mOf q x ^ hweak.β + 1)
              + |uOf q x| + |V x|‖ := by
    filter_upwards [hAE.H_upper_pointwise_ae ε hε hε1, hAE.lower_ae ε hε hε1,
      hμ_nn] with x hUpx hLowx hxμ
    set p_x : Fin d → ℝ := fun i => DuOf q i x with hp_x
    have hα_p_nn : 0 ≤ ‖p_x‖ ^ hweak.α := Real.rpow_nonneg (norm_nonneg _) _
    have hβ_m_nn : 0 ≤ mOf q x ^ hweak.β := Real.rpow_nonneg hxμ _
    -- The dominator value is nonnegative.
    have hG_nn :
        0 ≤ Cε * (‖p_x‖ ^ hweak.α + 1) + Cε * (mOf q x ^ hweak.β + 1)
              + |uOf q x| + |V x| := by
      have hC1 : 0 ≤ Cε * (‖p_x‖ ^ hweak.α + 1) :=
        mul_nonneg hCε_pos.le (by linarith)
      have hC2 : 0 ≤ Cε * (mOf q x ^ hweak.β + 1) :=
        mul_nonneg hCε_pos.le (by linarith)
      linarith [abs_nonneg (uOf q x), abs_nonneg (V x)]
    have hRHS_norm :
        ‖Cε * (‖fun i => DuOf q i x‖ ^ hweak.α + 1)
          + Cε * (mOf q x ^ hweak.β + 1) + |uOf q x| + |V x|‖
          = Cε * (‖fun i => DuOf q i x‖ ^ hweak.α + 1)
            + Cε * (mOf q x ^ hweak.β + 1) + |uOf q x| + |V x| := by
      rw [Real.norm_eq_abs, abs_of_nonneg hG_nn]
    rw [one_mul, hRHS_norm]
    -- `|HdeltaPos x p_x (m x)| ≤ Cε(‖p_x‖^α+1) + Cε(m^β+1)`.
    have hH_abs :
        |HdeltaPos hweak ε x p_x (mOf q x)|
          ≤ Cε * (‖p_x‖ ^ hweak.α + 1) + Cε * (mOf q x ^ hweak.β + 1) := by
      rcases hxμ.lt_or_eq with hmpos | hmz
      · -- `0 < m`: `HdeltaPos = Hdelta`, two-sided AE bound.
        rw [HdeltaPos_eq_Hdelta_of_pos hweak hmpos]
        have hUp := hUpx p_x (mOf q x) hmpos
        have hLow := hLowx p_x (mOf q x) hmpos
        have hUp' :
            Hdelta hweak ε x p_x (mOf q x)
              ≤ Cε * (‖p_x‖ ^ hweak.α + 1) := by
          have hdiv_nn : 0 ≤ (mOf q x ^ hweak.β) / Cε := div_nonneg hβ_m_nn hCε_pos.le
          linarith [hUp]
        have hLow' :
            -(Cε * (mOf q x ^ hweak.β + 1)) ≤ Hdelta hweak ε x p_x (mOf q x) := by
          have hdiv_nn : 0 ≤ (‖p_x‖ ^ hweak.α) / Cε := div_nonneg hα_p_nn hCε_pos.le
          linarith [hLow]
        have hC1 : 0 ≤ Cε * (‖p_x‖ ^ hweak.α + 1) :=
          mul_nonneg hCε_pos.le (by linarith)
        have hC2 : 0 ≤ Cε * (mOf q x ^ hweak.β + 1) :=
          mul_nonneg hCε_pos.le (by linarith)
        rw [abs_le]
        constructor
        · linarith
        · linarith
      · -- `m = 0`: `HdeltaPos … 0 = 0`.
        have hmzero : mOf q x = 0 := hmz.symm
        have hHzero : HdeltaPos hweak ε x p_x (mOf q x) = 0 := by
          simp [HdeltaPos, hmzero]
        rw [hHzero, abs_zero]
        have hC1 : 0 ≤ Cε * (‖p_x‖ ^ hweak.α + 1) :=
          mul_nonneg hCε_pos.le (by linarith)
        have hC2 : 0 ≤ Cε * (mOf q x ^ hweak.β + 1) :=
          mul_nonneg hCε_pos.le (by linarith)
        linarith
    -- Triangle inequality.
    have htri :
        ‖-(uOf q x) - HdeltaPos hweak ε x p_x (mOf q x) + V x‖
          ≤ |uOf q x| + |HdeltaPos hweak ε x p_x (mOf q x)| + |V x| := by
      rw [Real.norm_eq_abs]
      have h1 : |(-(uOf q x)) - HdeltaPos hweak ε x p_x (mOf q x) + V x|
                ≤ |(-(uOf q x)) - HdeltaPos hweak ε x p_x (mOf q x)| + |V x| :=
        abs_add_le _ _
      have h2 : |(-(uOf q x)) - HdeltaPos hweak ε x p_x (mOf q x)|
                ≤ |-(uOf q x)| + |-(HdeltaPos hweak ε x p_x (mOf q x))| := by
        have hh := abs_add_le (-(uOf q x)) (-(HdeltaPos hweak ε x p_x (mOf q x)))
        have heq : -(uOf q x) + -(HdeltaPos hweak ε x p_x (mOf q x))
                    = (-(uOf q x)) - HdeltaPos hweak ε x p_x (mOf q x) := by ring
        rw [heq] at hh; exact hh
      rw [abs_neg, abs_neg] at h2
      linarith
    linarith [htri, hH_abs]
  have hF_HJB :
      MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x => -(uOf q x)
            - HdeltaPos hweak ε x (fun i => DuOf q i x) (mOf q x) + V x) :=
    MemLp.toMemLpPer (MeasureTheory.MemLp.of_le_mul hG_HJB_dom.toMemLp (hF_HJB_meas q) hF_HJB_bound)
  -- ----------------------------------------------------------------------
  -- `hF_flux i`: `‖m·DpH ⋯ i‖ ≤ G_flux x` a.e. (via `hAE.DpH_upper_ae`).
  -- ----------------------------------------------------------------------
  have hF_flux : ∀ i,
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => mOf q x
            * DpHepsilonFam hweak qε ε x (fun j => DuOf q j x) (mOf q x) i) := by
    intro i
    have hbound :
        ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
          ‖mOf q x
              * DpHepsilonFam hweak qε ε x (fun j => DuOf q j x) (mOf q x) i‖
            ≤ (1 : ℝ) *
              ‖Cε * (mOf q x * ‖fun j => DuOf q j x‖ ^ (hweak.α - 1)
                          + mOf q x ^ (1 + hweak.β - hweak.β / hweak.α)
                          + mOf q x)‖ := by
      filter_upwards [hAE.DpH_upper_ae ε hε hε1, hμ_nn] with x hxDpH hxμ
      set p_x : Fin d → ℝ := fun j => DuOf q j x with hp_x
      have hα1_nn : 0 ≤ ‖p_x‖ ^ (hweak.α - 1) := Real.rpow_nonneg (norm_nonneg _) _
      have hμα_nn : 0 ≤ mOf q x ^ (1 + hweak.β - hweak.β / hweak.α) :=
        Real.rpow_nonneg hxμ _
      have hG_nn :
          0 ≤ Cε * (mOf q x * ‖p_x‖ ^ (hweak.α - 1)
                        + mOf q x ^ (1 + hweak.β - hweak.β / hweak.α) + mOf q x) := by
        apply mul_nonneg hCε_pos.le
        have h1 : 0 ≤ mOf q x * ‖p_x‖ ^ (hweak.α - 1) := mul_nonneg hxμ hα1_nn
        linarith
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hG_nn, one_mul]
      rcases hxμ.lt_or_eq with hxpos | hxz
      · -- `0 < m`: K-strict gradient bound, restricted to coordinate `i`.
        have hb := hxDpH p_x (mOf q x) hxpos
        have hcoord :
            |mOf q x * DpHepsilonFam hweak qε ε x p_x (mOf q x) i|
              ≤ mOf q x * ‖DpHepsilonFam hweak qε ε x p_x (mOf q x)‖ := by
          rw [abs_mul, abs_of_pos hxpos]
          have hi : |DpHepsilonFam hweak qε ε x p_x (mOf q x) i|
                    ≤ ‖DpHepsilonFam hweak qε ε x p_x (mOf q x)‖ :=
            norm_le_pi_norm (DpHepsilonFam hweak qε ε x p_x (mOf q x)) i
          exact mul_le_mul_of_nonneg_left hi hxpos.le
        have hmle :
            mOf q x * ‖DpHepsilonFam hweak qε ε x p_x (mOf q x)‖
              ≤ mOf q x * (Cε * (‖p_x‖ ^ (hweak.α - 1)
                                  + mOf q x ^ (hweak.β - hweak.β / hweak.α) + 1)) :=
          mul_le_mul_of_nonneg_left hb hxpos.le
        have hpow_id : mOf q x * mOf q x ^ (hweak.β - hweak.β / hweak.α)
                        = mOf q x ^ (1 + hweak.β - hweak.β / hweak.α) := by
          have hxone : mOf q x ^ (1 : ℝ) = mOf q x := Real.rpow_one (mOf q x)
          calc mOf q x * mOf q x ^ (hweak.β - hweak.β / hweak.α)
              = mOf q x ^ (1 : ℝ) * mOf q x ^ (hweak.β - hweak.β / hweak.α) := by
                rw [hxone]
            _ = mOf q x ^ ((1 : ℝ) + (hweak.β - hweak.β / hweak.α)) :=
                  (Real.rpow_add hxpos 1 _).symm
            _ = mOf q x ^ (1 + hweak.β - hweak.β / hweak.α) := by ring_nf
        have hrhs_eq :
            mOf q x * (Cε * (‖p_x‖ ^ (hweak.α - 1)
                            + mOf q x ^ (hweak.β - hweak.β / hweak.α) + 1))
              = Cε * (mOf q x * ‖p_x‖ ^ (hweak.α - 1)
                          + mOf q x ^ (1 + hweak.β - hweak.β / hweak.α) + mOf q x) := by
          have hexpand : mOf q x * (Cε * (‖p_x‖ ^ (hweak.α - 1)
                              + mOf q x ^ (hweak.β - hweak.β / hweak.α) + 1))
              = Cε * (mOf q x * ‖p_x‖ ^ (hweak.α - 1)
                          + mOf q x * mOf q x ^ (hweak.β - hweak.β / hweak.α)
                          + mOf q x) := by ring
          rw [hexpand, hpow_id]
        linarith
      · -- `m = 0`: LHS = 0.
        have hmzero : mOf q x = 0 := hxz.symm
        have hLHS :
            mOf q x * DpHepsilonFam hweak qε ε x p_x (mOf q x) i = 0 := by
          rw [hmzero]; ring
        rw [hLHS, abs_zero]; exact hG_nn
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.of_le_mul hG_flux_dom.toMemLp (hF_flux_meas q i) hbound)
  -- `hF_mass`.
  have hF_mass :
      MemLpPer (d := d) (ENNReal.ofReal γBarReal') (fun x => mOf q x - 1) :=
    Hamiltonian.μMinusOne_memLp_of_betaBar (d := d)
      (p := ENNReal.ofReal βBarReal) (q := ENNReal.ofReal γBarReal')
      (mOf q) hmLp hγ'_le_β ENNReal.ofReal_ne_top
  -- Assemble the record.
  exact
    { hβ := hβ
      hγ := hγ
      hF_HJB := hF_HJB
      hF_flux := hF_flux
      hF_mass := hF_mass
      hG_grad := hG_grad_mem
      hG_val := hG_val_mem
      hβTop := hβTop }

open StationaryMFG.Periodic StationaryMFG.Theorems.SimplePower in
/-- **D2c-2c-2: per-`q` `MFGOpEpsAuxHyps` on the GENUINE `HdeltaK0` closed-cone
carrier from AE data.**

Closed-cone sibling of `mfgOpEpsAuxHyps_HdeltaPos_of_AEData`. The `HdeltaPos`
producer trivialises the `hF_HJB` field at the boundary `{m = 0}` using
`HdeltaPos … 0 = 0` (junk value); on the genuine `HdeltaK0` carrier of the
*closed* cone `K0_Aepsi` the boundary value is `HdeltaK0 … 0 = Hdelta(·,·,0)`
(the right-limit value, cf. the T3 D2 carrier-correction memo), which can have
positive measure for `q ∈ K0_Aepsi`. Its two-sided control comes from the
`m = 0⁺` boundary slice:

* upper: `Hdelta_zero_upper_of_selectorFamily`
  (`Hdelta(x,p,0) ≤ Cε·(‖p‖^α+1)`);
* lower: `Hdelta_zero_lower_of_uniformBounds`
  (`‖p‖^α/C0 − C0 ≤ Hdelta(x,p,0)`), reconciled to `Cε` via `hC0_le`.

On the interior `{0 < m}`, `HdeltaK0 = Hdelta` (`HdeltaK0_eq_Hdelta_of_pos`) and
the bound is exactly the `hAE.upper`/`hAE.lower` two-sided estimate, as in the
`HdeltaPos` producer. The flux / mass / G-side fields are identical to the
`HdeltaPos` producer (the `DpH`/`m`/`u` slots are carrier-independent;
`DpHepsilonFam hweak qε ε = DpHepsilon hweak (qε ε)` defeq).

GATE: binds `(hweak, qε, hAE, hUB, sel, hmonBoundary, hdiffBoundary, hC0_le, hV, …)`;
NO `powData`, NO `HypothesisPowerGrowth (HdeltaPos …)`, NO
`hqE_per`/`hFormPos`/`hInj`/`hSurj`/`qEofMinv`. -/
theorem mfgOpEpsAuxHyps_HdeltaK0_of_AEData
    (V : (Fin d → ℝ) → ℝ)
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d)
    (hAE : HdeltaAEPowerEpsData (H := H) (DpH := DpH) hweak qε)
    (hUB : HdeltaUniformBounds (H := H) (DpH := DpH) hweak qε)
    (sel : InfConvSelectorFamily (H := H) (DpH := DpH) hweak qε)
    (hmonBoundary : Hamiltonian.HypothesisMonotone (d := d) H DpH)
    (hdiffBoundary : Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (hβBar_eq : βBarReal = hweak.β + 1)
    (hγBar_eq : γBarReal = hweak.α * (hweak.β + 1) / hweak.β)
    (hβBar'_eq : βBarReal' = (hweak.β + 1) / hweak.β)
    (hγBar'_eq : γBarReal' = γBarReal / (γBarReal - 1))
    (hβ : βBarReal.HolderConjugate βBarReal')
    (hγ : γBarReal.HolderConjugate γBarReal')
    (hβTop : ENNReal.ofReal γBarReal ≠ ⊤)
    (hγ'_le_β : ENNReal.ofReal γBarReal' ≤ ENNReal.ofReal βBarReal)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hC0_le : hUB.C0 ≤ CdeltaEps (H := H) (DpH := DpH) hweak ε)
    (hF_HJB_meas :
      ∀ q : XBanach d βBarReal γBarReal,
        MeasureTheory.AEStronglyMeasurable
          (fun x => -(uOf q x)
              - HdeltaK0 hweak ε x (fun i => DuOf q i x) (mOf q x) + V x)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (hF_flux_meas :
      ∀ q : XBanach d βBarReal γBarReal, ∀ i,
        MeasureTheory.AEStronglyMeasurable
          (fun x => mOf q x
              * DpHepsilonFam hweak qε ε x (fun j => DuOf q j x) (mOf q x) i)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d))) :
    ∀ q ∈ K0_Aepsi d βBarReal γBarReal,
      MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
        V (HdeltaK0 hweak ε) (DpHepsilon hweak (qε ε))
        (DuOf q) (mOf q) (uOf q) := by
  classical
  -- Standing exponent positivity.
  have hα_pos : 0 < hweak.α := lt_trans Real.zero_lt_one hweak.hα
  have hβ_pos : 0 < hweak.β := hweak.hβ
  have hβ1_pos : 0 < hweak.β + 1 := by linarith
  have hγBarReal_pos : 0 < γBarReal := by
    rw [hγBar_eq]; exact div_pos (mul_pos hα_pos hβ1_pos) hβ_pos
  have hγBar_one_lt_real : 1 < γBarReal := by
    rw [hγBar_eq]; rw [lt_div_iff₀ hβ_pos, one_mul]
    have h1 : (1 : ℝ) * (hweak.β + 1) < hweak.α * (hweak.β + 1) :=
      mul_lt_mul_of_pos_right hweak.hα hβ1_pos
    nlinarith [h1]
  -- Per-`ε` constant.
  set Cε : ℝ := CdeltaEps (H := H) (DpH := DpH) hweak ε with hCε_def
  have hCε_pos : 0 < Cε := (cdeltaEps_facts_upper (H := H) (DpH := DpH) hweak hε).1
  have hC0_pos : 0 < hUB.C0 := hUB.hC0
  -- The two-sided boundary slice (`m = 0`) estimates (all-`p`, a.e.-`x`).
  have hZeroUp :=
    Hdelta_zero_upper_of_selectorFamily (H := H) (DpH := DpH)
      hweak hmonBoundary qε sel hAE hε hε1
  have hZeroLow :=
    Hdelta_zero_lower_of_uniformBounds (H := H) (DpH := DpH)
      hweak hmonBoundary qε sel hUB hε hε1
  intro q hq_K0
  -- `q ∈ K0_Aepsi ⇒ 0 ≤ mOf q a.e.`.
  have hμ_nn :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ mOf q x := hq_K0
  -- `MemLpPer` certificates from the Lp components.
  have hmLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal) (mOf q) :=
    memLpPer_of_lpPer (d := d) q.1
  have huLp : MemLpPer (d := d) (ENNReal.ofReal γBarReal) (uOf q) :=
    memLpPer_of_lpPer (d := d) q.2.1
  have hDuLp : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (DuOf q i) := by
    intro i; exact memLpPer_of_lpPer (d := d) (q.2.2 i)
  -- Reframe regularity at the paper exponents (off `α, β`).
  have hμ_paperBetaBar :
      MemLpPer (d := d) (ENNReal.ofReal (hweak.β + 1)) (mOf q) := by
    rw [← hβBar_eq]; exact hmLp
  have hυ_paperGammaBar :
      MemLpPer (d := d)
        (ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β)) (uOf q) := by
    rw [← hγBar_eq]; exact huLp
  have hDυ_paperGammaBar : ∀ i,
      MemLpPer (d := d)
        (ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β)) (DuOf q i) := by
    intro i; rw [← hγBar_eq]; exact hDuLp i
  have hV_paperBetaBar' :
      MemLpPer (d := d) (ENNReal.ofReal ((hweak.β + 1) / hweak.β)) V := by
    rw [← hβBar'_eq]; exact hV
  -- HJB dominator (bare keystone, constant `C := Cε`).
  have hG_HJB_dom_paper :
      MemLpPer (d := d) (ENNReal.ofReal ((hweak.β + 1) / hweak.β))
        (fun x : (Fin d → ℝ) =>
          Cε * (‖fun i => DuOf q i x‖ ^ hweak.α + 1)
            + Cε * (mOf q x ^ hweak.β + 1)
            + |uOf q x| + |V x|) :=
    Hamiltonian.g_dominator_memLp_betaBar'_bare
      (β := hweak.β) (α := hweak.α) (C := Cε) hweak.hα hweak.hβ
      V (uOf q) (mOf q) (DuOf q)
      hμ_paperBetaBar hυ_paperGammaBar hDυ_paperGammaBar hV_paperBetaBar' hCε_pos
  have hG_HJB_dom :
      MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x : (Fin d → ℝ) =>
          Cε * (‖fun i => DuOf q i x‖ ^ hweak.α + 1)
            + Cε * (mOf q x ^ hweak.β + 1)
            + |uOf q x| + |V x|) := by
    rw [hβBar'_eq]; exact hG_HJB_dom_paper
  -- Flux dominator (bare keystone).
  have hG_flux_dom_paper :
      MemLpPer (d := d)
        (ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β /
          (hweak.α * (hweak.β + 1) / hweak.β - 1)))
        (fun x : (Fin d → ℝ) =>
          Cε * (mOf q x * ‖fun j => DuOf q j x‖ ^ (hweak.α - 1)
                      + mOf q x ^ (1 + hweak.β - hweak.β / hweak.α) + mOf q x)) :=
    Hamiltonian.flux_dominator_memLpPer_explicit
      (α := hweak.α) (β := hweak.β) (C := Cε) hweak.hα hweak.hβ
      (mOf q) (DuOf q) hμ_paperBetaBar hDυ_paperGammaBar
  have hG_flux_dom :
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x : (Fin d → ℝ) =>
          Cε * (mOf q x * ‖fun j => DuOf q j x‖ ^ (hweak.α - 1)
                      + mOf q x ^ (1 + hweak.β - hweak.β / hweak.α) + mOf q x)) := by
    have hγ'_paper_eq :
        γBarReal' = hweak.α * (hweak.β + 1) / hweak.β /
                    (hweak.α * (hweak.β + 1) / hweak.β - 1) := by
      rw [hγBar'_eq, hγBar_eq]
    rw [hγ'_paper_eq]; exact hG_flux_dom_paper
  -- G-side memberships.
  have hG_grad_mem : ∀ i,
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (G_grad γBarReal (DuOf q) i) := by
    intro i
    exact G_grad_memLpPer_gammaBar' hγBar_one_lt_real hγBar'_eq (DuOf q) hDuLp i
  have hG_val_mem :
      MemLpPer (d := d) (ENNReal.ofReal γBarReal') (G_val γBarReal (uOf q)) :=
    G_val_memLpPer_gammaBar' hγBar_one_lt_real hγBar'_eq (uOf q) huLp
  -- ----------------------------------------------------------------------
  -- `hF_HJB`: `‖-u - HdeltaK0 + V‖ ≤ G_HJB` a.e. (two-sided AE bound, genuine
  -- boundary value at `m = 0`).
  -- ----------------------------------------------------------------------
  have hF_HJB_bound :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ‖-(uOf q x)
            - HdeltaK0 hweak ε x (fun i => DuOf q i x) (mOf q x) + V x‖
          ≤ (1 : ℝ) *
            ‖Cε * (‖fun i => DuOf q i x‖ ^ hweak.α + 1)
              + Cε * (mOf q x ^ hweak.β + 1)
              + |uOf q x| + |V x|‖ := by
    filter_upwards [hAE.H_upper_pointwise_ae ε hε hε1, hAE.lower_ae ε hε hε1,
      hZeroUp, hZeroLow, hμ_nn] with x hUpx hLowx hxZeroUp hxZeroLow hxμ
    set p_x : Fin d → ℝ := fun i => DuOf q i x with hp_x
    have hα_p_nn : 0 ≤ ‖p_x‖ ^ hweak.α := Real.rpow_nonneg (norm_nonneg _) _
    have hβ_m_nn : 0 ≤ mOf q x ^ hweak.β := Real.rpow_nonneg hxμ _
    -- The dominator value is nonnegative.
    have hG_nn :
        0 ≤ Cε * (‖p_x‖ ^ hweak.α + 1) + Cε * (mOf q x ^ hweak.β + 1)
              + |uOf q x| + |V x| := by
      have hC1 : 0 ≤ Cε * (‖p_x‖ ^ hweak.α + 1) :=
        mul_nonneg hCε_pos.le (by linarith)
      have hC2 : 0 ≤ Cε * (mOf q x ^ hweak.β + 1) :=
        mul_nonneg hCε_pos.le (by linarith)
      linarith [abs_nonneg (uOf q x), abs_nonneg (V x)]
    have hRHS_norm :
        ‖Cε * (‖fun i => DuOf q i x‖ ^ hweak.α + 1)
          + Cε * (mOf q x ^ hweak.β + 1) + |uOf q x| + |V x|‖
          = Cε * (‖fun i => DuOf q i x‖ ^ hweak.α + 1)
            + Cε * (mOf q x ^ hweak.β + 1) + |uOf q x| + |V x| := by
      rw [Real.norm_eq_abs, abs_of_nonneg hG_nn]
    rw [one_mul, hRHS_norm]
    -- `|HdeltaK0 x p_x (m x)| ≤ Cε(‖p_x‖^α+1) + Cε(m^β+1)`.
    have hH_abs :
        |HdeltaK0 hweak ε x p_x (mOf q x)|
          ≤ Cε * (‖p_x‖ ^ hweak.α + 1) + Cε * (mOf q x ^ hweak.β + 1) := by
      have hC1 : 0 ≤ Cε * (‖p_x‖ ^ hweak.α + 1) :=
        mul_nonneg hCε_pos.le (by linarith)
      have hC2 : 0 ≤ Cε * (mOf q x ^ hweak.β + 1) :=
        mul_nonneg hCε_pos.le (by linarith)
      rcases hxμ.lt_or_eq with hmpos | hmz
      · -- `0 < m`: two-sided AE bound.
        rw [HdeltaK0_eq_Hdelta_of_pos hweak hmpos]
        have hUp := hUpx p_x (mOf q x) hmpos
        have hLow := hLowx p_x (mOf q x) hmpos
        have hUp' :
            Hdelta hweak ε x p_x (mOf q x)
              ≤ Cε * (‖p_x‖ ^ hweak.α + 1) := by
          have hdiv_nn : 0 ≤ (mOf q x ^ hweak.β) / Cε := div_nonneg hβ_m_nn hCε_pos.le
          linarith [hUp]
        have hLow' :
            -(Cε * (mOf q x ^ hweak.β + 1)) ≤ Hdelta hweak ε x p_x (mOf q x) := by
          have hdiv_nn : 0 ≤ (‖p_x‖ ^ hweak.α) / Cε := div_nonneg hα_p_nn hCε_pos.le
          linarith [hLow]
        rw [abs_le]
        constructor
        · linarith
        · linarith
      · -- `m = 0`: canonical boundary value, with its two-sided limit bounds.
        have hmzero : mOf q x = 0 := hmz.symm
        rw [hmzero]
        -- `0 ^ β = 0`, so `Cε·(0^β+1) = Cε ≥ 0`.
        have h0β : (0 : ℝ) ^ hweak.β = 0 := Real.zero_rpow (ne_of_gt hβ_pos)
        rw [h0β]
        -- Upper at `m = 0`.
        have hUp0 : HdeltaK0 hweak ε x p_x 0 ≤ Cε * (‖p_x‖ ^ hweak.α + 1) :=
          hxZeroUp p_x
        -- Lower at `m = 0`, reconciled to `Cε` via `hC0_le`.
        have hLow0base : ‖p_x‖ ^ hweak.α / hUB.C0 - hUB.C0 ≤ HdeltaK0 hweak ε x p_x 0 :=
          hxZeroLow p_x
        have hpdiv0_nn : 0 ≤ ‖p_x‖ ^ hweak.α / hUB.C0 :=
          div_nonneg hα_p_nn hC0_pos.le
        have hCε0_nn : 0 ≤ Cε * ((0 : ℝ) + 1) := by positivity
        -- `−Cε(‖p_x‖^α+1) − Cε ≤ −C0 ≤ ‖p_x‖^α/C0 − C0 ≤ Hdelta(x,p_x,0)`.
        have hC0_le_upper : hUB.C0 ≤ Cε * (‖p_x‖ ^ hweak.α + 1) := by
          nlinarith [hα_p_nn, hCε_pos.le, hC0_le]
        rw [abs_le]
        constructor
        · -- `−(Cε(‖p_x‖^α+1) + Cε(0+1)) ≤ Hdelta(x,p_x,0)`.
          have hchain : -hUB.C0 ≤ ‖p_x‖ ^ hweak.α / hUB.C0 - hUB.C0 := by
            linarith [hpdiv0_nn]
          linarith [hC0_le_upper, hchain, hLow0base, hCε0_nn]
        · -- `Hdelta(x,p_x,0) ≤ Cε(‖p_x‖^α+1) + Cε(0+1)`.
          linarith [hUp0, hCε0_nn]
    -- Triangle inequality.
    have htri :
        ‖-(uOf q x) - HdeltaK0 hweak ε x p_x (mOf q x) + V x‖
          ≤ |uOf q x| + |HdeltaK0 hweak ε x p_x (mOf q x)| + |V x| := by
      rw [Real.norm_eq_abs]
      have h1 : |(-(uOf q x)) - HdeltaK0 hweak ε x p_x (mOf q x) + V x|
                ≤ |(-(uOf q x)) - HdeltaK0 hweak ε x p_x (mOf q x)| + |V x| :=
        abs_add_le _ _
      have h2 : |(-(uOf q x)) - HdeltaK0 hweak ε x p_x (mOf q x)|
                ≤ |-(uOf q x)| + |-(HdeltaK0 hweak ε x p_x (mOf q x))| := by
        have hh := abs_add_le (-(uOf q x)) (-(HdeltaK0 hweak ε x p_x (mOf q x)))
        have heq : -(uOf q x) + -(HdeltaK0 hweak ε x p_x (mOf q x))
                    = (-(uOf q x)) - HdeltaK0 hweak ε x p_x (mOf q x) := by ring
        rw [heq] at hh; exact hh
      rw [abs_neg, abs_neg] at h2
      linarith
    linarith [htri, hH_abs]
  have hF_HJB :
      MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x => -(uOf q x)
            - HdeltaK0 hweak ε x (fun i => DuOf q i x) (mOf q x) + V x) :=
    MemLp.toMemLpPer (MeasureTheory.MemLp.of_le_mul hG_HJB_dom.toMemLp (hF_HJB_meas q) hF_HJB_bound)
  -- ----------------------------------------------------------------------
  -- `hF_flux i`: identical to the `HdeltaPos` producer (carrier-independent).
  -- ----------------------------------------------------------------------
  have hF_flux : ∀ i,
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => mOf q x
            * DpHepsilonFam hweak qε ε x (fun j => DuOf q j x) (mOf q x) i) := by
    intro i
    have hbound :
        ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
          ‖mOf q x
              * DpHepsilonFam hweak qε ε x (fun j => DuOf q j x) (mOf q x) i‖
            ≤ (1 : ℝ) *
              ‖Cε * (mOf q x * ‖fun j => DuOf q j x‖ ^ (hweak.α - 1)
                          + mOf q x ^ (1 + hweak.β - hweak.β / hweak.α)
                          + mOf q x)‖ := by
      filter_upwards [hAE.DpH_upper_ae ε hε hε1, hμ_nn] with x hxDpH hxμ
      set p_x : Fin d → ℝ := fun j => DuOf q j x with hp_x
      have hα1_nn : 0 ≤ ‖p_x‖ ^ (hweak.α - 1) := Real.rpow_nonneg (norm_nonneg _) _
      have hμα_nn : 0 ≤ mOf q x ^ (1 + hweak.β - hweak.β / hweak.α) :=
        Real.rpow_nonneg hxμ _
      have hG_nn :
          0 ≤ Cε * (mOf q x * ‖p_x‖ ^ (hweak.α - 1)
                        + mOf q x ^ (1 + hweak.β - hweak.β / hweak.α) + mOf q x) := by
        apply mul_nonneg hCε_pos.le
        have h1 : 0 ≤ mOf q x * ‖p_x‖ ^ (hweak.α - 1) := mul_nonneg hxμ hα1_nn
        linarith
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hG_nn, one_mul]
      rcases hxμ.lt_or_eq with hxpos | hxz
      · -- `0 < m`: K-strict gradient bound, restricted to coordinate `i`.
        have hb := hxDpH p_x (mOf q x) hxpos
        have hcoord :
            |mOf q x * DpHepsilonFam hweak qε ε x p_x (mOf q x) i|
              ≤ mOf q x * ‖DpHepsilonFam hweak qε ε x p_x (mOf q x)‖ := by
          rw [abs_mul, abs_of_pos hxpos]
          have hi : |DpHepsilonFam hweak qε ε x p_x (mOf q x) i|
                    ≤ ‖DpHepsilonFam hweak qε ε x p_x (mOf q x)‖ :=
            norm_le_pi_norm (DpHepsilonFam hweak qε ε x p_x (mOf q x)) i
          exact mul_le_mul_of_nonneg_left hi hxpos.le
        have hmle :
            mOf q x * ‖DpHepsilonFam hweak qε ε x p_x (mOf q x)‖
              ≤ mOf q x * (Cε * (‖p_x‖ ^ (hweak.α - 1)
                                  + mOf q x ^ (hweak.β - hweak.β / hweak.α) + 1)) :=
          mul_le_mul_of_nonneg_left hb hxpos.le
        have hpow_id : mOf q x * mOf q x ^ (hweak.β - hweak.β / hweak.α)
                        = mOf q x ^ (1 + hweak.β - hweak.β / hweak.α) := by
          have hxone : mOf q x ^ (1 : ℝ) = mOf q x := Real.rpow_one (mOf q x)
          calc mOf q x * mOf q x ^ (hweak.β - hweak.β / hweak.α)
              = mOf q x ^ (1 : ℝ) * mOf q x ^ (hweak.β - hweak.β / hweak.α) := by
                rw [hxone]
            _ = mOf q x ^ ((1 : ℝ) + (hweak.β - hweak.β / hweak.α)) :=
                  (Real.rpow_add hxpos 1 _).symm
            _ = mOf q x ^ (1 + hweak.β - hweak.β / hweak.α) := by ring_nf
        have hrhs_eq :
            mOf q x * (Cε * (‖p_x‖ ^ (hweak.α - 1)
                            + mOf q x ^ (hweak.β - hweak.β / hweak.α) + 1))
              = Cε * (mOf q x * ‖p_x‖ ^ (hweak.α - 1)
                          + mOf q x ^ (1 + hweak.β - hweak.β / hweak.α) + mOf q x) := by
          have hexpand : mOf q x * (Cε * (‖p_x‖ ^ (hweak.α - 1)
                              + mOf q x ^ (hweak.β - hweak.β / hweak.α) + 1))
              = Cε * (mOf q x * ‖p_x‖ ^ (hweak.α - 1)
                          + mOf q x * mOf q x ^ (hweak.β - hweak.β / hweak.α)
                          + mOf q x) := by ring
          rw [hexpand, hpow_id]
        linarith
      · -- `m = 0`: LHS = 0.
        have hmzero : mOf q x = 0 := hxz.symm
        have hLHS :
            mOf q x * DpHepsilonFam hweak qε ε x p_x (mOf q x) i = 0 := by
          rw [hmzero]; ring
        rw [hLHS, abs_zero]; exact hG_nn
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.of_le_mul hG_flux_dom.toMemLp (hF_flux_meas q i) hbound)
  -- `hF_mass`.
  have hF_mass :
      MemLpPer (d := d) (ENNReal.ofReal γBarReal') (fun x => mOf q x - 1) :=
    Hamiltonian.μMinusOne_memLp_of_betaBar (d := d)
      (p := ENNReal.ofReal βBarReal) (q := ENNReal.ofReal γBarReal')
      (mOf q) hmLp hγ'_le_β ENNReal.ofReal_ne_top
  -- Assemble the record.
  exact
    { hβ := hβ
      hγ := hγ
      hF_HJB := hF_HJB
      hF_flux := hF_flux
      hF_mass := hF_mass
      hG_grad := hG_grad_mem
      hG_val := hG_val_mem
      hβTop := hβTop }

open StationaryMFG.Periodic StationaryMFG.Theorems.SimplePower in
/-- **D2c-2c: the `auxHypsK0Pos` / `auxHypsK0K0` / `hWeakDerivK0` riders of
`aepsiDeltaContextFamily_K0_of_selectorData`, from AE data.**

The first rider `auxHypsK0Pos` (`HdeltaPos` carrier) is produced by
`mfgOpEpsAuxHyps_HdeltaPos_of_AEData`. The remaining two are accepted structural
carriers (not `hpow` consumers):

* `auxHypsK0K0` (the genuine `HdeltaK0` carrier on the *closed* cone `K0_Aepsi`,
  which includes the boundary `m = 0` where `HdeltaK0 ≠ HdeltaPos`, cf. the T3 D2
  carrier-correction memo) is now GENUINELY DERIVED (D2c-2c-2) via
  `mfgOpEpsAuxHyps_HdeltaK0_of_AEData`, whose `m = 0` boundary uses the genuine
  right-limit value `Hdelta(·,·,0)` controlled two-sidedly by the boundary slice
  `Hdelta_zero_upper_of_selectorFamily` / `Hdelta_zero_lower_of_uniformBounds`
  (reconciled to `Cε` via `hC0_le`). It is NO LONGER an input carrier.
* `hWeakDerivK0` is the per-coordinate weak-derivative tie on `K0_Aepsi` (NOT the
  refined `K0_Aepsi_W` cone, which carries it structurally). On the unrefined
  cone this is a genuine structural residue, exponent-independent and not
  derivable from membership; it is taken as an input carrier (legacy form
  `aepsi_weakDerivTie_of_paperHypotheses_legacy`).

GATE: binds `(hweak, qε, hAE, hUB, sel, hmonBoundary, hdiffBoundary, hC0_le, hV, …)`
plus `hWeakDerivK0`; NO `powData`, NO `HypothesisPowerGrowth (HdeltaPos …)`, NO
`hqE_per`/`hFormPos`/`hInj`/`hSurj`/`qEofMinv`. -/
theorem aepsiDeltaK0_auxK0WeakDerivRiders_of_AEData
    (V : (Fin d → ℝ) → ℝ)
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d)
    (hAE : HdeltaAEPowerEpsData (H := H) (DpH := DpH) hweak qε)
    (hUB : HdeltaUniformBounds (H := H) (DpH := DpH) hweak qε)
    (sel : InfConvSelectorFamily (H := H) (DpH := DpH) hweak qε)
    (hmonBoundary : Hamiltonian.HypothesisMonotone (d := d) H DpH)
    (hdiffBoundary : Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (hβBar_eq : βBarReal = hweak.β + 1)
    (hγBar_eq : γBarReal = hweak.α * (hweak.β + 1) / hweak.β)
    (hβBar'_eq : βBarReal' = (hweak.β + 1) / hweak.β)
    (hγBar'_eq : γBarReal' = γBarReal / (γBarReal - 1))
    (hβ : βBarReal.HolderConjugate βBarReal')
    (hγ : γBarReal.HolderConjugate γBarReal')
    (hβTop : ENNReal.ofReal γBarReal ≠ ⊤)
    (hγ'_le_β : ENNReal.ofReal γBarReal' ≤ ENNReal.ofReal βBarReal)
    (hC0_le : ∀ ε (_hε : 0 < ε) (_hε1 : ε ≤ 1),
      hUB.C0 ≤ CdeltaEps (H := H) (DpH := DpH) hweak ε)
    (hF_HJB_meas : ∀ ε (_hε : 0 < ε) (_hε1 : ε ≤ 1),
      ∀ q : XBanach d βBarReal γBarReal,
        MeasureTheory.AEStronglyMeasurable
          (fun x => -(uOf q x)
              - HdeltaPos hweak ε x (fun i => DuOf q i x) (mOf q x) + V x)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (hF_HJB_meas_K0 : ∀ ε (_hε : 0 < ε) (_hε1 : ε ≤ 1),
      ∀ q : XBanach d βBarReal γBarReal,
        MeasureTheory.AEStronglyMeasurable
          (fun x => -(uOf q x)
              - HdeltaK0 hweak ε x (fun i => DuOf q i x) (mOf q x) + V x)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (hF_flux_meas : ∀ ε (_hε : 0 < ε) (_hε1 : ε ≤ 1),
      ∀ q : XBanach d βBarReal γBarReal, ∀ i,
        MeasureTheory.AEStronglyMeasurable
          (fun x => mOf q x
              * DpHepsilonFam hweak qε ε x (fun j => DuOf q j x) (mOf q x) i)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (hWeakDerivK0 :
      ∀ q ∈ K0_Aepsi d βBarReal γBarReal,
        ∀ i, HasWeakDerivPer (d := d) i (uOf q) (DuOf q i)) :
    -- `auxHypsK0Pos`
    (∀ ε (_hε : 0 < ε) (_hε1 : ε ≤ 1),
      ∀ q ∈ K0_Aepsi d βBarReal γBarReal,
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V (HdeltaPos hweak ε) (DpHepsilonFam hweak qε ε)
                    (DuOf q) (mOf q) (uOf q))
    ∧ -- `auxHypsK0K0`
    (∀ ε (_hε : 0 < ε) (_hε1 : ε ≤ 1),
      ∀ q ∈ K0_Aepsi d βBarReal γBarReal,
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V (HdeltaK0 hweak ε) (DpHepsilon hweak (qε ε))
                    (DuOf q) (mOf q) (uOf q))
    ∧ -- `hWeakDerivK0`
    (∀ q ∈ K0_Aepsi d βBarReal γBarReal,
        ∀ i, HasWeakDerivPer (d := d) i (uOf q) (DuOf q i)) := by
  refine ⟨?_, ?_, hWeakDerivK0⟩
  · intro ε hε hε1
    exact mfgOpEpsAuxHyps_HdeltaPos_of_AEData
      (V := V) (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      hweak qε hAE hV hβBar_eq hγBar_eq hβBar'_eq hγBar'_eq
      hβ hγ hβTop hγ'_le_β hε hε1
      (hF_HJB_meas ε hε hε1) (hF_flux_meas ε hε hε1)
  · intro ε hε hε1
    exact mfgOpEpsAuxHyps_HdeltaK0_of_AEData
      (V := V) (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      hweak qε hAE hUB sel hmonBoundary hdiffBoundary hV
      hβBar_eq hγBar_eq hβBar'_eq hγBar'_eq
      hβ hγ hβTop hγ'_le_β hε hε1 (hC0_le ε hε hε1)
      (hF_HJB_meas_K0 ε hε hε1) (hF_flux_meas ε hε hε1)

open StationaryMFG.Periodic StationaryMFG.Theorems.SimplePower in
/-- **D2c-2b-2-iii: the per-ε coercivity rider on the `HdeltaPos` carrier, from
AE data.**

Final child of D2c2b2. Produces, for each `ε ∈ (0,1]`, the existential coercivity
tuple `∃ lam Ccoerc, 0 < lam ∧ ∀ᶠ v …` in exactly the `hbound_residue`-field shape
that `aepsiDeltaContextFamily_K0_of_selectorData` consumes (the `HdeltaPos hweak ε`
carrier, the `(fun i => ⇑(v.2.2 i), ⇑v.1, ⇑v.2.1)` binder forms), sourced from the
AE data `(hweak, qε, hAE, hExp, conjugacy)` — **NOT** from `powData` /
`HypothesisPowerGrowth (HdeltaPos …)`.

Assembly: `paperSection8_coercivity_of_AEData` (b2ii) supplies the bound on the raw
`Hdelta hweak ε` carrier; its `auxHypsK` input is discharged from the D2c2c
producer `mfgOpEpsAuxHyps_HdeltaPos_of_AEData` (which lives on `HdeltaPos` over
`K0_Aepsi`) by restricting along `K_Aepsi ⊆ K0_Aepsi` and bridging the carrier with
`mfgOpEpsAuxHyps_Hdelta_of_HdeltaPos_KAepsi` (positive-density `HdeltaPos = Hdelta`
on `{0<m}`). The `aux10` constant-`μ ≡ 1` rider is taken on raw `Hdelta` directly
(structural, as in the `hpow`-keyed chain). Finally the raw-`Hdelta` bound is
re-keyed to `HdeltaPos` on the eventual filter — where `v ∈ K_Aepsi` gives `mOf v > 0`
a.e. for the primal term, and the second term's primal `μ ≡ 1 > 0` is everywhere
positive — via `mfgOperatorEpsPair_congr_H_ae`. -/
theorem aepsiDeltaK0_coercivityRider_of_AEData
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (V : (Fin d → ℝ) → ℝ)
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d)
    (hAE : HdeltaAEPowerEpsData (H := H) (DpH := DpH) hweak qε)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (hβBar_eq : βBarReal = hweak.β + 1)
    (hγBar_eq : γBarReal = hweak.α * (hweak.β + 1) / hweak.β)
    (hβBar'_eq : βBarReal' = (hweak.β + 1) / hweak.β)
    (hγBar'_eq : γBarReal' = γBarReal / (γBarReal - 1))
    (hβ : βBarReal.HolderConjugate βBarReal')
    (hγ : γBarReal.HolderConjugate γBarReal')
    (hβTop : ENNReal.ofReal γBarReal ≠ ⊤)
    (hβBarTop : ENNReal.ofReal βBarReal ≠ ⊤)
    (hβ_gt1 : 1 < βBarReal) (hγ_gt1 : 1 < γBarReal)
    (hγ'_le_β : ENNReal.ofReal γBarReal' ≤ ENNReal.ofReal βBarReal)
    (hd_pos : 0 < (d : ℝ))
    (hF_HJB_meas : ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      ∀ q : XBanach d βBarReal γBarReal,
        MeasureTheory.AEStronglyMeasurable
          (fun x => -(uOf q x)
              - HdeltaPos hweak ε x (fun i => DuOf q i x) (mOf q x) + V x)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (hF_flux_meas : ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      ∀ q : XBanach d βBarReal γBarReal, ∀ i,
        MeasureTheory.AEStronglyMeasurable
          (fun x => mOf q x
              * DpHepsilonFam hweak qε ε x (fun j => DuOf q j x) (mOf q x) i)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    -- The constant-`μ ≡ 1` aux on the raw `Hdelta` carrier (structural rider,
    -- as in the `hpow`-keyed coercivity chain).
    (aux10 : ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
        V (Hdelta hweak ε) (DpHepsilonFam hweak qε ε)
        (fun (_ : Fin d) (_ : (Fin d → ℝ)) => (0 : ℝ))
        (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ))) :
    ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      ∃ lamCoerc Ccoerc : ℝ, 0 < lamCoerc ∧
        ∀ᶠ v in (Bornology.cobounded (XBanach d βBarReal γBarReal)
                    ⊓ Filter.principal (K_Aepsi d βBarReal γBarReal)),
          lamCoerc * aepsiCoerciveGauge (βBarReal := βBarReal) (γBarReal := γBarReal)
              (coercivityGaugeExponent βBarReal γBarReal) v - Ccoerc ≤
            mfgOperatorEpsPair (V := V) (H := HdeltaPos hweak ε)
                (DpH := DpHepsilonFam hweak qε ε)
                γBarReal ε (fun i => ⇑(v.2.2 i)) (⇑v.1) (⇑v.2.1)
                (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1)
              - mfgOperatorEpsPair (V := V) (H := HdeltaPos hweak ε)
                  (DpH := DpHepsilonFam hweak qε ε)
                  γBarReal ε (fun _ _ => 0) (fun _ => 1) (fun _ => 0)
                  (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1) := by
  intro ε hε hε1
  -- `auxHypsK` on raw `Hdelta` over `K_Aepsi`: discharge the `HdeltaPos`-keyed
  -- D2c2c producer over `K0_Aepsi`, restrict along `K_Aepsi ⊆ K0_Aepsi`, then
  -- bridge the carrier `HdeltaPos → Hdelta` on the strict-positivity cone.
  have auxHypsPosK0 :=
    mfgOpEpsAuxHyps_HdeltaPos_of_AEData (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      V hweak qε hAE hV hβBar_eq hγBar_eq hβBar'_eq hγBar'_eq hβ hγ hβTop hγ'_le_β
      hε hε1 (hF_HJB_meas ε hε hε1) (hF_flux_meas ε hε hε1)
  have auxHypsK : ∀ q ∈ K_Aepsi d βBarReal γBarReal,
      MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
        V (Hdelta hweak ε) (DpHepsilonFam hweak qε ε)
        (DuOf q) (mOf q) (uOf q) := by
    intro q hq
    exact mfgOpEpsAuxHyps_Hdelta_of_HdeltaPos_KAepsi hweak V
      (DpHepsilonFam hweak qε ε) hq
      (auxHypsPosK0 q (K_Aepsi_subset_K0_Aepsi d βBarReal γBarReal hq))
  -- b2ii: the coercivity bound on the raw `Hdelta` carrier.
  obtain ⟨lam, Ccoerc, hlam, hbnd⟩ :=
    paperSection8_coercivity_of_AEData (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal') (V := V)
      hAE hε hε1 hβBar_eq hγBar_eq hβTop hβBarTop hβ_gt1 hγ_gt1 hd_pos
      auxHypsK (aux10 ε hε hε1)
  refine ⟨lam, Ccoerc, hlam, ?_⟩
  -- Move the `Hdelta`-carried bound to the `HdeltaPos` carrier on the eventual
  -- filter: every `v` lies in `K_Aepsi` (`mOf v > 0` a.e.) for the primal term,
  -- and the second operator's primal `μ ≡ 1 > 0` everywhere.
  rw [Filter.eventually_inf_principal] at hbnd ⊢
  filter_upwards [hbnd] with v hbndv hvMem
  have hbv := hbndv hvMem
  -- Positive density on `K_Aepsi`.
  have hpos : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      0 < (⇑v.1 : (Fin d → ℝ) → ℝ) x := hvMem
  -- Primal-term carrier swap `Hdelta → HdeltaPos` at `μ = mOf v` (a.e. positive).
  have hH1 :
      (fun x => Hdelta hweak ε x (fun i => (⇑(v.2.2 i)) x) ((⇑v.1) x))
        =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
      (fun x => HdeltaPos hweak ε x (fun i => (⇑(v.2.2 i)) x) ((⇑v.1) x)) := by
    filter_upwards [hpos] with x hx
    exact (HdeltaPos_eq_Hdelta_of_pos hweak hx).symm
  have hEq1 :
      mfgOperatorEpsPair (V := V) (H := Hdelta hweak ε)
          (DpH := DpHepsilonFam hweak qε ε)
          γBarReal ε (DuOf v) (mOf v) (uOf v)
            (DuOf v) (mOf v - 1) (uOf v)
        = mfgOperatorEpsPair (V := V) (H := HdeltaPos hweak ε)
            (DpH := DpHepsilonFam hweak qε ε)
            γBarReal ε (DuOf v) (mOf v) (uOf v)
              (DuOf v) (mOf v - 1) (uOf v) :=
    Solutions.MFG.mfgOperatorEpsPair_congr_H_ae (V := V)
      (H := Hdelta hweak ε) (DpH := DpHepsilonFam hweak qε ε)
      γBarReal ε (HdeltaPos hweak ε) (DpHepsilonFam hweak qε ε)
      (DuOf v) (mOf v) (uOf v)
      (DuOf v) (mOf v - 1) (uOf v)
      hH1 (Filter.EventuallyEq.refl _ _)
  -- Second-term carrier swap at the constant primal `μ ≡ 1 > 0` (everywhere).
  have hH2 :
      (fun x => Hdelta hweak ε x (fun i => (0 : ℝ)) ((1 : (Fin d → ℝ) → ℝ) x))
        =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
      (fun x => HdeltaPos hweak ε x (fun i => (0 : ℝ)) ((1 : (Fin d → ℝ) → ℝ) x)) := by
    refine Filter.Eventually.of_forall ?_
    intro x
    exact (HdeltaPos_eq_Hdelta_of_pos hweak (m := (1 : ℝ)) one_pos).symm
  have hEq2 :
      mfgOperatorEpsPair (V := V) (H := Hdelta hweak ε)
          (DpH := DpHepsilonFam hweak qε ε)
          γBarReal ε (fun _ _ => 0) (fun _ => 1) (fun _ => 0)
            (DuOf v) (mOf v - 1) (uOf v)
        = mfgOperatorEpsPair (V := V) (H := HdeltaPos hweak ε)
            (DpH := DpHepsilonFam hweak qε ε)
            γBarReal ε (fun _ _ => 0) (fun _ => 1) (fun _ => 0)
              (DuOf v) (mOf v - 1) (uOf v) :=
    Solutions.MFG.mfgOperatorEpsPair_congr_H_ae (V := V)
      (H := Hdelta hweak ε) (DpH := DpHepsilonFam hweak qε ε)
      γBarReal ε (HdeltaPos hweak ε) (DpHepsilonFam hweak qε ε)
      (fun _ _ => 0) (fun _ => 1) (fun _ => 0)
      (DuOf v) (mOf v - 1) (uOf v)
      hH2 (Filter.EventuallyEq.refl _ _)
  rw [hEq1, hEq2] at hbv
  exact hbv

open StationaryMFG.Periodic StationaryMFG.Theorems.SimplePower in
/-- **D2c-2d-0-b (piece 1): the `K_Aepsi`-indexed `auxHypsK` on the `HdeltaK0`
carrier from AE data.**

The final `HdeltaK0` `AepsiUniformContextK` (assembled by the aggregator child
`…0c`) needs a `K_Aepsi`-indexed primal aux supplier on the genuine `HdeltaK0`
carrier. This is the AE-route producer: the D2c-2c-2 producer
`mfgOpEpsAuxHyps_HdeltaK0_of_AEData` already supplies the per-`q` aux record on
`HdeltaK0` over the *closed* cone `K0_Aepsi`; restricting along
`K_Aepsi ⊆ K0_Aepsi` (`K_Aepsi_subset_K0_Aepsi`) gives the `K_Aepsi`-indexed
supplier in exactly the shape `Aepsi_CLM_opK` / `Aepsi_mono_of_paperHypotheses`
/ `isCoerciveAt_Aepsi_CLM_K_Aepsi` consume.

GATE: binds the SAME AE inputs as `mfgOpEpsAuxHyps_HdeltaK0_of_AEData`; NO
`powData`, NO `HypothesisPowerGrowth (HdeltaPos …)`, NO
`RegularityH (HdeltaPos …)`, NO `hFormPos`/`hqE_per`/`hInj`/`hSurj`/`qEofMinv`. -/
theorem auxHypsK_HdeltaK0_KAepsi_of_AEData
    (V : (Fin d → ℝ) → ℝ)
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d)
    (hAE : HdeltaAEPowerEpsData (H := H) (DpH := DpH) hweak qε)
    (hUB : HdeltaUniformBounds (H := H) (DpH := DpH) hweak qε)
    (sel : InfConvSelectorFamily (H := H) (DpH := DpH) hweak qε)
    (hmonBoundary : Hamiltonian.HypothesisMonotone (d := d) H DpH)
    (hdiffBoundary : Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (hβBar_eq : βBarReal = hweak.β + 1)
    (hγBar_eq : γBarReal = hweak.α * (hweak.β + 1) / hweak.β)
    (hβBar'_eq : βBarReal' = (hweak.β + 1) / hweak.β)
    (hγBar'_eq : γBarReal' = γBarReal / (γBarReal - 1))
    (hβ : βBarReal.HolderConjugate βBarReal')
    (hγ : γBarReal.HolderConjugate γBarReal')
    (hβTop : ENNReal.ofReal γBarReal ≠ ⊤)
    (hγ'_le_β : ENNReal.ofReal γBarReal' ≤ ENNReal.ofReal βBarReal)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hC0_le : hUB.C0 ≤ CdeltaEps (H := H) (DpH := DpH) hweak ε)
    (hF_HJB_meas :
      ∀ q : XBanach d βBarReal γBarReal,
        MeasureTheory.AEStronglyMeasurable
          (fun x => -(uOf q x)
              - HdeltaK0 hweak ε x (fun i => DuOf q i x) (mOf q x) + V x)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (hF_flux_meas :
      ∀ q : XBanach d βBarReal γBarReal, ∀ i,
        MeasureTheory.AEStronglyMeasurable
          (fun x => mOf q x
              * DpHepsilonFam hweak qε ε x (fun j => DuOf q j x) (mOf q x) i)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d))) :
    ∀ q ∈ K_Aepsi d βBarReal γBarReal,
      MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
        V (HdeltaK0 hweak ε) (DpHepsilon hweak (qε ε))
        (fun i => ⇑(q.2.2 i)) (⇑q.1) (⇑q.2.1) := by
  -- Build the closed-cone supplier over `K0_Aepsi` from AE data.
  have hK0 :=
    mfgOpEpsAuxHyps_HdeltaK0_of_AEData
      (V := V) (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      hweak qε hAE hUB sel hmonBoundary hdiffBoundary hV
      hβBar_eq hγBar_eq hβBar'_eq hγBar'_eq
      hβ hγ hβTop hγ'_le_β hε hε1 hC0_le hF_HJB_meas hF_flux_meas
  -- Restrict to `K_Aepsi ⊆ K0_Aepsi`.
  intro q hq
  exact hK0 q (K_Aepsi_subset_K0_Aepsi d βBarReal γBarReal hq)

open StationaryMFG.Periodic StationaryMFG.Theorems.SimplePower in
/-- **D2c-2d-0-b (piece 3): the per-ε coercivity bound on the `HdeltaK0`
carrier, from AE data.**

The aggregator child `…0c` feeds `isCoerciveAt_Aepsi_CLM_K_Aepsi` with a per-ε
existential coercivity bound stated on the *genuine* `HdeltaK0` carrier's
`mfgOperatorEpsPair`. The b2iii rider `aepsiDeltaK0_coercivityRider_of_AEData`
produces exactly this existential on the `HdeltaPos` carrier; here we transfer
the bound `HdeltaPos → HdeltaK0` on the coercive filter
(`cobounded ⊓ principal (K_Aepsi …)`):

* the primal term carries `μ = mOf v`, which is `> 0` a.e. for `v ∈ K_Aepsi`, so
  `HdeltaPos = HdeltaK0` a.e. (`HdeltaK0_eq_HdeltaPos_of_pos`);
* the second term carries the constant primal `μ ≡ 1 > 0` everywhere, so
  `HdeltaPos = HdeltaK0` everywhere there.

Both carrier swaps are by `mfgOperatorEpsPair_congr_H_ae`, mirroring the
`Filter.Tendsto.congr'` block in `aepsiDeltaContextFamily_K0_of_selectorData`'s
`hCoerc` (BanachBridge.lean:2861-2898) and the reverse `Hdelta → HdeltaPos`
transfer inside `aepsiDeltaK0_coercivityRider_of_AEData` itself.

GATE: binds the AE inputs of `aepsiDeltaK0_coercivityRider_of_AEData`; NO
`powData`, NO `HypothesisPowerGrowth (HdeltaPos …)`, NO `RegularityH (HdeltaPos …)`,
NO `hFormPos`/`hqE_per`/`hInj`/`hSurj`/`qEofMinv`. -/
theorem aepsiDeltaK0_coercivityRiderK0_of_AEData
    (V : (Fin d → ℝ) → ℝ)
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d)
    (hAE : HdeltaAEPowerEpsData (H := H) (DpH := DpH) hweak qε)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (hβBar_eq : βBarReal = hweak.β + 1)
    (hγBar_eq : γBarReal = hweak.α * (hweak.β + 1) / hweak.β)
    (hβBar'_eq : βBarReal' = (hweak.β + 1) / hweak.β)
    (hγBar'_eq : γBarReal' = γBarReal / (γBarReal - 1))
    (hβ : βBarReal.HolderConjugate βBarReal')
    (hγ : γBarReal.HolderConjugate γBarReal')
    (hβTop : ENNReal.ofReal γBarReal ≠ ⊤)
    (hβBarTop : ENNReal.ofReal βBarReal ≠ ⊤)
    (hβ_gt1 : 1 < βBarReal) (hγ_gt1 : 1 < γBarReal)
    (hγ'_le_β : ENNReal.ofReal γBarReal' ≤ ENNReal.ofReal βBarReal)
    (hd_pos : 0 < (d : ℝ))
    (hF_HJB_meas : ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      ∀ q : XBanach d βBarReal γBarReal,
        MeasureTheory.AEStronglyMeasurable
          (fun x => -(uOf q x)
              - HdeltaPos hweak ε x (fun i => DuOf q i x) (mOf q x) + V x)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (hF_flux_meas : ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      ∀ q : XBanach d βBarReal γBarReal, ∀ i,
        MeasureTheory.AEStronglyMeasurable
          (fun x => mOf q x
              * DpHepsilonFam hweak qε ε x (fun j => DuOf q j x) (mOf q x) i)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (aux10 : ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
        V (Hdelta hweak ε) (DpHepsilonFam hweak qε ε)
        (fun (_ : Fin d) (_ : (Fin d → ℝ)) => (0 : ℝ))
        (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ))) :
    ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      ∃ lamCoerc Ccoerc : ℝ, 0 < lamCoerc ∧
        ∀ᶠ v in (Bornology.cobounded (XBanach d βBarReal γBarReal)
                    ⊓ Filter.principal (K_Aepsi d βBarReal γBarReal)),
          lamCoerc * aepsiCoerciveGauge (βBarReal := βBarReal) (γBarReal := γBarReal)
              (coercivityGaugeExponent βBarReal γBarReal) v - Ccoerc ≤
            mfgOperatorEpsPair (V := V) (H := HdeltaK0 hweak ε)
                (DpH := DpHepsilon hweak (qε ε))
                γBarReal ε (fun i => ⇑(v.2.2 i)) (⇑v.1) (⇑v.2.1)
                (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1)
              - mfgOperatorEpsPair (V := V) (H := HdeltaK0 hweak ε)
                  (DpH := DpHepsilon hweak (qε ε))
                  γBarReal ε (fun _ _ => 0) (fun _ => 1) (fun _ => 0)
                  (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1) := by
  intro ε hε hε1
  -- The `HdeltaPos`-carrier bound from the b2iii rider.
  obtain ⟨lam, Ccoerc, hlam, hbnd⟩ :=
    aepsiDeltaK0_coercivityRider_of_AEData
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal') (V := V)
      hweak qε hAE hV hβBar_eq hγBar_eq hβBar'_eq hγBar'_eq hβ hγ
      hβTop hβBarTop hβ_gt1 hγ_gt1 hγ'_le_β hd_pos
      hF_HJB_meas hF_flux_meas aux10 ε hε hε1
  refine ⟨lam, Ccoerc, hlam, ?_⟩
  -- Move the bound `HdeltaPos → HdeltaK0` on the eventual filter.
  rw [Filter.eventually_inf_principal] at hbnd ⊢
  filter_upwards [hbnd] with v hbndv hvMem
  have hbv := hbndv hvMem
  -- Positive density on `K_Aepsi`.
  have hpos : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      0 < (⇑v.1 : (Fin d → ℝ) → ℝ) x := hvMem
  -- Primal-term carrier swap `HdeltaPos → HdeltaK0` at `μ = mOf v` (a.e. positive).
  have hH1 :
      (fun x => HdeltaPos hweak ε x (fun i => (⇑(v.2.2 i)) x) ((⇑v.1) x))
        =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
      (fun x => HdeltaK0 hweak ε x (fun i => (⇑(v.2.2 i)) x) ((⇑v.1) x)) := by
    filter_upwards [hpos] with x hx
    exact (HdeltaK0_eq_HdeltaPos_of_pos hweak hx).symm
  have hEq1 :
      mfgOperatorEpsPair (V := V) (H := HdeltaPos hweak ε)
          (DpH := DpHepsilonFam hweak qε ε)
          γBarReal ε (fun i => ⇑(v.2.2 i)) (⇑v.1) (⇑v.2.1)
            (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1)
        = mfgOperatorEpsPair (V := V) (H := HdeltaK0 hweak ε)
            (DpH := DpHepsilon hweak (qε ε))
            γBarReal ε (fun i => ⇑(v.2.2 i)) (⇑v.1) (⇑v.2.1)
              (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1) :=
    Solutions.MFG.mfgOperatorEpsPair_congr_H_ae (V := V)
      (H := HdeltaPos hweak ε) (DpH := DpHepsilonFam hweak qε ε)
      γBarReal ε (HdeltaK0 hweak ε) (DpHepsilon hweak (qε ε))
      (fun i => ⇑(v.2.2 i)) (⇑v.1) (⇑v.2.1)
      (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1)
      hH1 (Filter.EventuallyEq.refl _ _)
  -- Second-term carrier swap at the constant primal `μ ≡ 1 > 0` (everywhere).
  have hH2 :
      (fun x => HdeltaPos hweak ε x (fun i => (0 : ℝ)) ((1 : (Fin d → ℝ) → ℝ) x))
        =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
      (fun x => HdeltaK0 hweak ε x (fun i => (0 : ℝ)) ((1 : (Fin d → ℝ) → ℝ) x)) := by
    refine Filter.Eventually.of_forall ?_
    intro x
    exact (HdeltaK0_eq_HdeltaPos_of_pos hweak (m := (1 : ℝ)) one_pos).symm
  have hEq2 :
      mfgOperatorEpsPair (V := V) (H := HdeltaPos hweak ε)
          (DpH := DpHepsilonFam hweak qε ε)
          γBarReal ε (fun _ _ => 0) (fun _ => 1) (fun _ => 0)
            (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1)
        = mfgOperatorEpsPair (V := V) (H := HdeltaK0 hweak ε)
            (DpH := DpHepsilon hweak (qε ε))
            γBarReal ε (fun _ _ => 0) (fun _ => 1) (fun _ => 0)
              (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1) :=
    Solutions.MFG.mfgOperatorEpsPair_congr_H_ae (V := V)
      (H := HdeltaPos hweak ε) (DpH := DpHepsilonFam hweak qε ε)
      γBarReal ε (HdeltaK0 hweak ε) (DpHepsilon hweak (qε ε))
      (fun _ _ => 0) (fun _ => 1) (fun _ => 0)
      (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1)
      hH2 (Filter.EventuallyEq.refl _ _)
  rw [hEq1, hEq2] at hbv
  exact hbv

open StationaryMFG.Periodic StationaryMFG.Theorems.SimplePower in
/-- **D2b-2b: per-ε `AepsiUniformContextK` family on the `HdeltaK0` carrier.**

The `HdeltaK0`-keyed sibling of `aepsiDeltaPosContextFamily_of_selectorData`. It
consumes the SAME input bundle (built internally into the `HdeltaPos` context
`ctxPos`) plus the `K0`-keyed `auxHypsK0`/`hWeakDerivK0` riders re-keyed on
`HdeltaK0`, and assembles the c4d-target context on `HdeltaK0 hweak ε /
DpHepsilon hweak (qε ε)`. The three operator fields are transferred from
`ctxPos` via `aepsi_CLM_opK_HdeltaK0_eq_HdeltaPos_on_KAepsi`; the `auxHypsK` slot
via `mfgOpEpsAuxHyps_HdeltaK0_of_HdeltaPos_KAepsi`; the K0 `aux` is built from
the `auxHypsK0K0` input.

GATE #1: no `RegularityH (HdeltaK0)`; `RegularityH (HdeltaPos)` only inside
`ctxPos`. -/
noncomputable def aepsiDeltaContextFamily_K0_of_selectorData
    (V : (Fin d → ℝ) → ℝ)
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hMono : Hamiltonian.HypothesisMonotone (d := d) H DpH)
    (qε : QEpsFamily d)
    (sel : InfConvSelectorFamily (H := H) (DpH := DpH) hweak qε)
    (powData : HdeltaPowerEpsData (H := H) (DpH := DpH) hweak qε)
    (uniform : HdeltaUniformBounds (H := H) (DpH := DpH) hweak qε)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (hExp : SimplePowerExponentFacts γBarReal
                (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
                (ENNReal.ofReal βBarReal'))
    (hβBar_eq : ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      βBarReal = (powData.hpow ε hε hε1).β + 1)
    (hγBar_eq : ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      γBarReal = (powData.hpow ε hε hε1).α * ((powData.hpow ε hε hε1).β + 1)
        / (powData.hpow ε hε hε1).β)
    (hβBar'_eq : ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      βBarReal' = ((powData.hpow ε hε hε1).β + 1) / (powData.hpow ε hε hε1).β)
    (hγBar'_eq : γBarReal' = γBarReal / (γBarReal - 1))
    (hβ : βBarReal.HolderConjugate βBarReal')
    (hγ : γBarReal.HolderConjugate γBarReal')
    (hγ'_le_β : ENNReal.ofReal γBarReal' ≤ ENNReal.ofReal βBarReal)
    (hγ2 : 1 < γBarReal)
    (hβconj : βBarReal'.HolderConjugate βBarReal)
    (hγconj : γBarReal'.HolderConjugate γBarReal)
    (h_upper : ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ p mm, 0 < mm →
          HdeltaPos hweak ε x p mm
            ≤ (powData.hpow ε hε hε1).C * (‖p‖ ^ (powData.hpow ε hε hε1).α + 1)
              - (mm ^ (powData.hpow ε hε hε1).β) / (powData.hpow ε hε hε1).C)
    (hF_HJB_meas : ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      ∀ q : XBanach d βBarReal γBarReal,
        MeasureTheory.AEStronglyMeasurable
          (fun x => -(uOf q x)
              - HdeltaPos hweak ε x (fun i => DuOf q i x) (mOf q x) + V x)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (hF_flux_meas : ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      ∀ q : XBanach d βBarReal γBarReal, ∀ i,
        MeasureTheory.AEStronglyMeasurable
          (fun x => mOf q x
              * DpHepsilonFam hweak qε ε x (fun j => DuOf q j x) (mOf q x) i)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (hScalarMono :
      ∀ s t : ℝ,
        0 ≤ (absPowMinusTwo γBarReal t * t - absPowMinusTwo γBarReal s * s)
              * (t - s))
    (hVecMono :
      ∀ v w : Fin d → ℝ,
        0 ≤ (vecAbsPowMinusTwo γBarReal v • v - vecAbsPowMinusTwo γBarReal w • w)
              ⬝ (v - w))
    (κCoerc : ℝ) (hκCoerc : 1 < κCoerc)
    (lamCoerc : ℝ) (hlamCoerc : 0 < lamCoerc)
    (Ccoerc : ℝ)
    (hbound_residue : ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      ∀ᶠ v in (Bornology.cobounded (XBanach d βBarReal γBarReal)
                  ⊓ Filter.principal (K_Aepsi d βBarReal γBarReal)),
        lamCoerc * aepsiCoerciveGauge (βBarReal := βBarReal) (γBarReal := γBarReal)
            κCoerc v - Ccoerc ≤
          mfgOperatorEpsPair (V := V) (H := HdeltaPos hweak ε)
              (DpH := DpHepsilonFam hweak qε ε)
              γBarReal ε (fun i => ⇑(v.2.2 i)) (⇑v.1) (⇑v.2.1)
              (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1)
            - mfgOperatorEpsPair (V := V) (H := HdeltaPos hweak ε)
                (DpH := DpHepsilonFam hweak qε ε)
                γBarReal ε (fun _ _ => 0) (fun _ => 1) (fun _ => 0)
                (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1))
    (h_slice : ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          HdeltaPos hweak ε x p m
            ≤ -(m ^ (powData.hpow ε hε hε1).β) / (powData.hpow ε hε hε1).C
              + (powData.hpow ε hε hε1).C
              + (powData.hpow ε hε hε1).C * ‖p‖ ^ (powData.hpow ε hε hε1).α
              + (powData.hpow ε hε hε1).C * ‖p‖
                * (m ^ ((powData.hpow ε hε hε1).β
                    - (powData.hpow ε hε hε1).β / (powData.hpow ε hε hε1).α) + 1))
    (hSegMin : ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      PaperSection8SegmentResiduesMin
        (d := d) γBarReal βBarReal βBarReal' γBarReal'
        (HdeltaPos hweak ε) (DpHepsilonFam hweak qε ε) (powData.hpow ε hε hε1))
    (hF_unreg_meas : ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      ∀ (u v : XBanach d βBarReal γBarReal),
                u ∈ K_Aepsi d βBarReal γBarReal →
                v ∈ K_Aepsi d βBarReal γBarReal →
                ∀ (w : XBanach d βBarReal γBarReal),
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        MeasureTheory.AEStronglyMeasurable
          (fun x => aepsiIntegrandAt_unreg V (HdeltaPos hweak ε)
                      (DpHepsilonFam hweak qε ε)
                      (DuOf v) (DuOf u) (mOf v) (mOf u)
                      (uOf v) (uOf u)
                      (fun i => ⇑(w.2.2 i)) (⇑w.1) (⇑w.2.1) x t)
          (MeasureTheory.volume.restrict (UnitCube d)))
    (hF_gat_meas : ∀ (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1),
      ∀ (u v : XBanach d βBarReal γBarReal),
                u ∈ K_Aepsi d βBarReal γBarReal →
                v ∈ K_Aepsi d βBarReal γBarReal →
                ∀ (w : XBanach d βBarReal γBarReal),
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        MeasureTheory.AEStronglyMeasurable
          (fun x => aepsiIntegrandAt_gateaux γBarReal
                      (DuOf v) (DuOf u) (uOf v) (uOf u)
                      (fun i => ⇑(w.2.2 i)) (⇑w.2.1) x t)
          (MeasureTheory.volume.restrict (UnitCube d)))
    -- `HdeltaPos`-keyed K0 aux (feeds `ctxPos`).
    (auxHypsK0Pos : ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      ∀ q ∈ K0_Aepsi d βBarReal γBarReal,
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V (HdeltaPos hweak ε) (DpHepsilonFam hweak qε ε)
                    (DuOf q) (mOf q) (uOf q))
    -- `HdeltaK0`-keyed K0 aux (feeds the K0 context `aux` field — SAME rider
    -- shape the `HdeltaPos` family takes, re-keyed on `HdeltaK0`).
    (auxHypsK0K0 : ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      ∀ q ∈ K0_Aepsi d βBarReal γBarReal,
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V (HdeltaK0 hweak ε) (DpHepsilon hweak (qε ε))
                    (DuOf q) (mOf q) (uOf q))
    (hWeakDerivK0 :
      ∀ q ∈ K0_Aepsi d βBarReal γBarReal,
        ∀ i, HasWeakDerivPer (d := d) i (uOf q) (DuOf q i)) :
    ∀ ε (hε : 0 < ε) (_hε1 : ε ≤ 1),
      AepsiUniformContextK (d := d) ε V (HdeltaK0 hweak ε)
        (DpHepsilon hweak (qε ε))
        γBarReal βBarReal βBarReal' γBarReal' :=
  fun ε hε hε1 =>
    -- Build the `HdeltaPos` context internally.
    let ctxPos :=
      aepsiDeltaPosContextFamily_of_selectorData (V := V)
        (γBarReal := γBarReal) (βBarReal := βBarReal)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        hweak hMono qε sel powData uniform hV hExp
        hβBar_eq hγBar_eq hβBar'_eq hγBar'_eq hβ hγ hγ'_le_β hγ2 hβconj hγconj
        h_upper hF_HJB_meas hF_flux_meas hScalarMono hVecMono
        κCoerc hκCoerc lamCoerc hlamCoerc Ccoerc hbound_residue
        h_slice hSegMin hF_unreg_meas hF_gat_meas auxHypsK0Pos hWeakDerivK0
        ε hε hε1
    -- The K_Aepsi-indexed `auxHypsK` on the `HdeltaK0` carrier (transferred
    -- from `ctxPos.auxHypsK` by positive-density a.e. congruence).
    let auxHypsK_K0 : ∀ q ∈ K_Aepsi d βBarReal γBarReal,
        MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
          V (HdeltaK0 hweak ε) (DpHepsilon hweak (qε ε))
          (fun i => ⇑(q.2.2 i)) (⇑q.1) (⇑q.2.1) :=
      fun q hq =>
        mfgOpEpsAuxHyps_HdeltaK0_of_HdeltaPos_KAepsi hweak V (qε ε) hq
          (ctxPos.auxHypsK q hq)
    { hReflexive := ctxPos.hReflexive
      auxHypsK := auxHypsK_K0
      qRef := ctxPos.qRef
      hqRef := ctxPos.hqRef
      aux := Banach.mfgOpEps_uniformAux_of_perPairAuxHyps ε
                (K0_Aepsi d βBarReal γBarReal) (auxHypsK0K0 ε hε hε1)
      hMono := by
        intro v₁ hv₁ v₂ hv₂
        rw [aepsi_CLM_opK_HdeltaK0_eq_HdeltaPos_on_KAepsi hweak V (qε ε)
              auxHypsK_K0 ctxPos.auxHypsK hv₁,
            aepsi_CLM_opK_HdeltaK0_eq_HdeltaPos_on_KAepsi hweak V (qε ε)
              auxHypsK_K0 ctxPos.auxHypsK hv₂]
        exact ctxPos.hMono hv₁ hv₂
      hHC := by
        intro u hu v hv w
        have heqU := aepsi_CLM_opK_HdeltaK0_eq_HdeltaPos_on_KAepsi hweak V (qε ε)
          auxHypsK_K0 ctxPos.auxHypsK hu
        have heqV := aepsi_CLM_opK_HdeltaK0_eq_HdeltaPos_on_KAepsi hweak V (qε ε)
          auxHypsK_K0 ctxPos.auxHypsK hv
        -- The segment composition agrees with the `HdeltaPos` one because the
        -- operator agrees at the two endpoints `u, v ∈ K_Aepsi`; but the
        -- composition evaluates at interior segment points, so we transfer the
        -- hemicontinuity certificate directly through the operator equality on
        -- the WHOLE cone via `Aepsi_CLM_opK_apply_of_mem`-driven congruence.
        have hcont := ctxPos.hHC hu hv w
        refine hcont.congr ?_
        intro t ht
        simp only
        -- At a segment point `(1-t)•u + t•v`, evaluate both operators; they
        -- agree iff that point lies in `K_Aepsi`. Hemicontinuity only requires
        -- continuity of `t ↦ A(seg t) w` on `[0,1]`; we show the two segment
        -- maps are EQUAL as functions of `t` on `[0,1]` by a per-`t` operator
        -- equality (the segment point need not be in `K_Aepsi`, so instead we
        -- compare via the off-domain totalization: both are `0` off `K_Aepsi`
        -- and equal on `K_Aepsi`).
        by_cases hseg : ((1 - t) • u + t • v) ∈ K_Aepsi d βBarReal γBarReal
        · rw [aepsi_CLM_opK_HdeltaK0_eq_HdeltaPos_on_KAepsi hweak V (qε ε)
                auxHypsK_K0 ctxPos.auxHypsK hseg]
          rfl
        · rw [Banach.Aepsi_CLM_opK_eq_zero_of_not_mem (γBarReal := γBarReal)
                (βBarReal := βBarReal) (βBarReal' := βBarReal')
                (γBarReal' := γBarReal') V (HdeltaK0 hweak ε)
                (DpHepsilon hweak (qε ε)) auxHypsK_K0 ε hseg,
              Banach.Aepsi_CLM_opK_eq_zero_of_not_mem (γBarReal := γBarReal)
                (βBarReal := βBarReal) (βBarReal' := βBarReal')
                (γBarReal' := γBarReal') V (HdeltaPos hweak ε)
                (DpHepsilonFam hweak qε ε) ctxPos.auxHypsK ε hseg]
      hCoerc := by
        refine ⟨ctxPos.hqRef, ?_⟩
        -- On the coercive filter, `v ∈ K_Aepsi` eventually, so the K0 operator
        -- agrees with the `HdeltaPos` one; the base point `qRef ∈ K_Aepsi`.
        have hqRefMem : ctxPos.qRef ∈ K_Aepsi d βBarReal γBarReal := ctxPos.hqRef
        have hEqFilter :
            (fun v : XBanach d βBarReal γBarReal =>
                (Banach.Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
                      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                      V (HdeltaPos hweak ε) (DpHepsilonFam hweak qε ε)
                      ctxPos.auxHypsK ε v
                    - Banach.Aepsi_CLM_opK (γBarReal := γBarReal)
                        (βBarReal := βBarReal) (βBarReal' := βBarReal')
                        (γBarReal' := γBarReal') V (HdeltaPos hweak ε)
                        (DpHepsilonFam hweak qε ε) ctxPos.auxHypsK ε ctxPos.qRef)
                  (v - ctxPos.qRef) / ‖v‖)
              =ᶠ[StationaryMFG.Monotone.coerciveFilter
                  (K_Aepsi d βBarReal γBarReal)]
            (fun v : XBanach d βBarReal γBarReal =>
                (Banach.Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
                      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                      V (HdeltaK0 hweak ε) (DpHepsilon hweak (qε ε))
                      auxHypsK_K0 ε v
                    - Banach.Aepsi_CLM_opK (γBarReal := γBarReal)
                        (βBarReal := βBarReal) (βBarReal' := βBarReal')
                        (γBarReal' := γBarReal') V (HdeltaK0 hweak ε)
                        (DpHepsilon hweak (qε ε)) auxHypsK_K0 ε ctxPos.qRef)
                  (v - ctxPos.qRef) / ‖v‖) := by
          rw [StationaryMFG.Monotone.coerciveFilter]
          rw [Filter.eventuallyEq_inf_principal_iff]
          refine Filter.Eventually.of_forall ?_
          intro v hvMem
          rw [aepsi_CLM_opK_HdeltaK0_eq_HdeltaPos_on_KAepsi hweak V (qε ε)
                auxHypsK_K0 ctxPos.auxHypsK hvMem,
              aepsi_CLM_opK_HdeltaK0_eq_HdeltaPos_on_KAepsi hweak V (qε ε)
                auxHypsK_K0 ctxPos.auxHypsK hqRefMem]
          rfl
        exact Filter.Tendsto.congr' hEqFilter ctxPos.hCoerc.2
      hWeakDeriv := hWeakDerivK0 }

/-! ### D2c-2d-0-a: per-`(u,v,w)` `HemicontSegmentDataK0` builder on
`HdeltaK0`/`K_Aepsi` from AE data

`aepsiDeltaK0_hemicontSegmentDataK0_of_AEData` produces, for `u, v ∈ K_Aepsi`
and `w` arbitrary, the per-segment closed-cone DCT bundle
`HemicontSegmentDataK0 V (HdeltaK0 hweak ε) (DpHepsilon hweak (qε ε)) …`
on the `HdeltaK0` carrier, sourced from the AE riders
(`hAE : HdeltaAEPowerEpsData`) plus the exponent-keyed segment residues
(`PaperSection8SegmentResiduesMinExp` at `hweak.α`/`hweak.β`). This is the
`hData` builder feeding the d0 wrapper
`isHemicontinuous_Aepsi_CLM_K_Aepsi_K0`.

GATE: no `powData`, no `HypothesisPowerGrowth (HdeltaPos …)`, no
`RegularityH (HdeltaPos …)`, no `hFormPos`/`hqE_per`/`hInj`/`hSurj`/`qEofMinv`,
no `sorry`/`axiom`.

The construction:

  * `hNonneg` comes from `K_Aepsi_segment_pos` (strict positivity along the
    segment, weakened to non-strict).
  * The dominator `g_unreg` is the natural-form `g_unreg_natural` at the bare
    exponents `hweak.α`/`hweak.β`, constant `CdeltaEps hweak ε`, with the
    H-abs constant `C'` produced from the AE estimates
    `hAE.H_upper_pointwise_ae` / `hAE.lower_ae`. Integrability via
    `g_unreg_natural_integrableOn_min`.
  * The `hF_unreg_bound` field: on `K_Aepsi` the convex combination is
    `> 0` a.e., where the closed-cone integrand `aepsiIntegrandAt_unreg_K0`
    agrees with the strict `aepsiIntegrandAt_unreg`
    (`aepsiIntegrandAt_unreg_K0_eq_unreg_of_pos`); the strict integrand is
    bounded by `g_unreg_natural` via the local exponent-keyed pointwise bound
    derived from the AE H-abs / `m·DpH` dominators.
  * The Gateaux half is carrier-free (`g_gat_natural` + the product-form
    Gateaux bound), identical to the strict bundle. -/

open StationaryMFG.Periodic StationaryMFG.Theorems.SimplePower in
/-- **AE-route segment `H`-abs dominator (exponent-keyed).** The
nonneg-cone analogue of `hemicont_H_abs_dominator`'s existential conclusion
at the bare exponents `hweak.α`/`hweak.β` and constant `CdeltaEps hweak ε`,
derived from `hAE.H_upper_pointwise_ae` (upper) and `hAE.lower_ae` (lower)
on the strict segment `0 < cxComb μ mBar t x`. NO `HypothesisPowerGrowth`. -/
theorem aepsiDeltaK0_segHAbsDominator_of_AEData
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d)
    (hAE : HdeltaAEPowerEpsData (H := H) (DpH := DpH) hweak qε)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (μ mBar : (Fin d → ℝ) → ℝ)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          0 < cxComb μ mBar t x →
            |Hdelta hweak ε x (fun i => cxCombGrad Dυ Dῡ t i x)
                (cxComb μ mBar t x)|
              ≤ C'
                  * (‖fun i => cxCombGrad Dυ Dῡ t i x‖ ^ hweak.α + 1)
                + CdeltaEps (H := H) (DpH := DpH) hweak ε
                  * ((cxComb μ mBar t x) ^ hweak.β + 1) := by
  set Cε : ℝ := CdeltaEps (H := H) (DpH := DpH) hweak ε with hCε_def
  have hCε_pos : 0 < Cε := CdeltaEps_pos (H := H) (DpH := DpH) hweak hε
  refine ⟨Cε, hCε_pos, ?_⟩
  filter_upwards [hAE.H_upper_pointwise_ae ε hε hε1, hAE.lower_ae ε hε hε1]
    with x hUp hLow t _ht hμt_pos
  set p_t : Fin d → ℝ := fun i => cxCombGrad Dυ Dῡ t i x with hpt_def
  set m_t : ℝ := cxComb μ mBar t x with hm_t
  have hpα_nn : 0 ≤ ‖p_t‖ ^ hweak.α := Real.rpow_nonneg (norm_nonneg _) _
  have hmβ_nn : 0 ≤ m_t ^ hweak.β := Real.rpow_nonneg hμt_pos.le _
  -- Upper bound on `Hdelta`.
  have hU : Hdelta hweak ε x p_t m_t
      ≤ Cε * (‖p_t‖ ^ hweak.α + 1) - m_t ^ hweak.β / Cε := hUp p_t m_t hμt_pos
  -- Lower bound on `Hdelta`.
  have hL : ‖p_t‖ ^ hweak.α / Cε - Cε * (m_t ^ hweak.β + 1)
      ≤ Hdelta hweak ε x p_t m_t := hLow p_t m_t hμt_pos
  have hpα_div_nn : 0 ≤ ‖p_t‖ ^ hweak.α / Cε := div_nonneg hpα_nn hCε_pos.le
  have hmβ_div_nn : 0 ≤ m_t ^ hweak.β / Cε := div_nonneg hmβ_nn hCε_pos.le
  have hC1_nn : 0 ≤ Cε * (‖p_t‖ ^ hweak.α + 1) := by
    have : 0 ≤ ‖p_t‖ ^ hweak.α + 1 := by linarith
    exact mul_nonneg hCε_pos.le this
  have hC2_nn : 0 ≤ Cε * (m_t ^ hweak.β + 1) := by
    have : 0 ≤ m_t ^ hweak.β + 1 := by linarith
    exact mul_nonneg hCε_pos.le this
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · -- `-(...) ≤ Hdelta`.
    have hneg : -(Cε * (‖p_t‖ ^ hweak.α + 1)) ≤ 0 := by linarith
    have hlow' : -(Cε * (m_t ^ hweak.β + 1)) ≤ Hdelta hweak ε x p_t m_t := by
      linarith
    linarith
  · -- `Hdelta ≤ (...)`.
    have : -(m_t ^ hweak.β / Cε) ≤ Cε * (m_t ^ hweak.β + 1) := by linarith
    linarith

open StationaryMFG.Periodic StationaryMFG.Theorems.SimplePower in
/-- **AE-route segment `m·DpH` dominator (exponent-keyed).** The analogue of
`hemicont_mDpH_dominator`'s conclusion at the bare exponents and constant
`CdeltaEps hweak ε`, derived from `hAE.DpH_upper_ae` on the strict segment.
NO `HypothesisPowerGrowth`. -/
theorem aepsiDeltaK0_segMDpHDominator_of_AEData
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d)
    (hAE : HdeltaAEPowerEpsData (H := H) (DpH := DpH) hweak qε)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (μ mBar : (Fin d → ℝ) → ℝ)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      ∀ t, 0 < cxComb μ mBar t x →
        ‖cxComb μ mBar t x •
            DpHepsilonFam hweak qε ε x (fun i => cxCombGrad Dυ Dῡ t i x)
              (cxComb μ mBar t x)‖
          ≤ CdeltaEps (H := H) (DpH := DpH) hweak ε
              * (cxComb μ mBar t x
                    * ‖fun i => cxCombGrad Dυ Dῡ t i x‖ ^ (hweak.α - 1)
                  + (cxComb μ mBar t x) ^ (1 + hweak.β - hweak.β / hweak.α)
                  + cxComb μ mBar t x) := by
  set Cε : ℝ := CdeltaEps (H := H) (DpH := DpH) hweak ε with hCε_def
  filter_upwards [hAE.DpH_upper_ae ε hε hε1] with x hx t hμt
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hμt]
  set p_t : Fin d → ℝ := fun i => cxCombGrad Dυ Dῡ t i x with hp_t
  set m_t : ℝ := cxComb μ mBar t x with hm_t
  have hb := hx p_t m_t hμt
  have hμt_le : 0 ≤ m_t := hμt.le
  have hmle :
      m_t * ‖DpHepsilonFam hweak qε ε x p_t m_t‖
        ≤ m_t * (Cε * (‖p_t‖ ^ (hweak.α - 1)
                  + m_t ^ (hweak.β - hweak.β / hweak.α) + 1)) :=
    mul_le_mul_of_nonneg_left hb hμt_le
  have hpow :
      m_t * m_t ^ (hweak.β - hweak.β / hweak.α)
        = m_t ^ (1 + hweak.β - hweak.β / hweak.α) := by
    have hone : m_t ^ (1 : ℝ) = m_t := Real.rpow_one _
    calc m_t * m_t ^ (hweak.β - hweak.β / hweak.α)
        = m_t ^ (1 : ℝ) * m_t ^ (hweak.β - hweak.β / hweak.α) := by rw [hone]
      _ = m_t ^ ((1 : ℝ) + (hweak.β - hweak.β / hweak.α)) :=
            (Real.rpow_add hμt 1 _).symm
      _ = m_t ^ (1 + hweak.β - hweak.β / hweak.α) := by ring_nf
  have hrhs_eq :
      m_t * (Cε * (‖p_t‖ ^ (hweak.α - 1)
              + m_t ^ (hweak.β - hweak.β / hweak.α) + 1))
        = Cε * (m_t * ‖p_t‖ ^ (hweak.α - 1)
                  + m_t ^ (1 + hweak.β - hweak.β / hweak.α) + m_t) := by
    have hexp : m_t * (Cε * (‖p_t‖ ^ (hweak.α - 1)
                  + m_t ^ (hweak.β - hweak.β / hweak.α) + 1))
        = Cε * (m_t * ‖p_t‖ ^ (hweak.α - 1)
                  + m_t * m_t ^ (hweak.β - hweak.β / hweak.α)
                  + m_t) := by ring
    rw [hexp, hpow]
  linarith

open StationaryMFG.Periodic StationaryMFG.Theorems.SimplePower in
/-- **AE-route K0 unreg integrand pointwise bound (exponent-keyed).** Bounds
the *closed-cone* integrand `aepsiIntegrandAt_unreg_K0` by `g_unreg_natural`
at the bare exponents `hweak.α`/`hweak.β`, on the strict segment
`0 < cxComb μ mBar t x` (where the K0 integrand agrees with the strict one).
Sourced from the AE segment dominators above. NO `HypothesisPowerGrowth`. -/
theorem aepsiDeltaK0_unregK0_pointwise_bound_of_AEData
    (V : (Fin d → ℝ) → ℝ)
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d)
    (hAE : HdeltaAEPowerEpsData (H := H) (DpH := DpH) hweak qε)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {C' : ℝ} (hC'_pos : 0 < C')
    (μ mBar υ ῡ : (Fin d → ℝ) → ℝ)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ)
    (hHabs : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < cxComb μ mBar t x →
          |Hdelta hweak ε x (fun i => cxCombGrad Dυ Dῡ t i x)
              (cxComb μ mBar t x)|
            ≤ C' * (‖fun i => cxCombGrad Dυ Dῡ t i x‖ ^ hweak.α + 1)
              + CdeltaEps (H := H) (DpH := DpH) hweak ε
                * ((cxComb μ mBar t x) ^ hweak.β + 1))
    (hmDpH : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ t, 0 < cxComb μ mBar t x →
          ‖cxComb μ mBar t x •
              DpHepsilonFam hweak qε ε x (fun i => cxCombGrad Dυ Dῡ t i x)
                (cxComb μ mBar t x)‖
            ≤ CdeltaEps (H := H) (DpH := DpH) hweak ε
                * (cxComb μ mBar t x
                      * ‖fun i => cxCombGrad Dυ Dῡ t i x‖ ^ (hweak.α - 1)
                    + (cxComb μ mBar t x) ^ (1 + hweak.β - hweak.β / hweak.α)
                    + cxComb μ mBar t x)) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        0 < cxComb μ mBar t x →
          ‖aepsiIntegrandAt_unreg_K0 V (HdeltaK0 hweak ε)
              (DpHepsilon hweak (qε ε))
              Dυ Dῡ μ mBar υ ῡ Dν η ν x t‖
            ≤ g_unreg_natural hweak.α hweak.β
                (CdeltaEps (H := H) (DpH := DpH) hweak ε) C' V
                Dυ Dῡ μ mBar υ ῡ Dν η ν x := by
  set Cε : ℝ := CdeltaEps (H := H) (DpH := DpH) hweak ε with hCε_def
  set H' : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ := HdeltaK0 hweak ε with hH'_def
  set DpH' : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ) :=
    DpHepsilon hweak (qε ε) with hDpH'_def
  have hCε_pos : 0 < Cε := CdeltaEps_pos (H := H) (DpH := DpH) hweak hε
  filter_upwards [hHabs, hmDpH] with x hxH₀ hxmDpH₀ t ht hμt_pos
  -- Transfer the AE dominators from `Hdelta`/`DpHepsilonFam` to the carrier
  -- `HdeltaK0`/`DpHepsilon` on the strict segment (`HdeltaK0 = Hdelta`,
  -- `DpHepsilon = DpHepsilonFam` defeq).
  have hHK0_eq :
      HdeltaK0 hweak ε x (fun i => cxCombGrad Dυ Dῡ t i x) (cxComb μ mBar t x)
        = Hdelta hweak ε x (fun i => cxCombGrad Dυ Dῡ t i x)
            (cxComb μ mBar t x) :=
    HdeltaK0_eq_Hdelta_of_pos hweak hμt_pos
  have hxH : |H' x (fun i => cxCombGrad Dυ Dῡ t i x) (cxComb μ mBar t x)|
      ≤ C' * (‖fun i => cxCombGrad Dυ Dῡ t i x‖ ^ hweak.α + 1)
        + Cε * ((cxComb μ mBar t x) ^ hweak.β + 1) := by
    rw [hH'_def, hHK0_eq]; exact hxH₀ t ht hμt_pos
  have hxmDpH : ∀ s, 0 < cxComb μ mBar s x →
      ‖cxComb μ mBar s x •
          DpH' x (fun i => cxCombGrad Dυ Dῡ s i x) (cxComb μ mBar s x)‖
        ≤ Cε * (cxComb μ mBar s x
              * ‖fun i => cxCombGrad Dυ Dῡ s i x‖ ^ (hweak.α - 1)
            + (cxComb μ mBar s x) ^ (1 + hweak.β - hweak.β / hweak.α)
            + cxComb μ mBar s x) := fun s hs => hxmDpH₀ s hs
  -- On `0 < cxComb`, the K0 integrand equals the strict integrand.
  rw [aepsiIntegrandAt_unreg_K0_eq_unreg_of_pos V H' DpH' Dυ Dῡ μ mBar υ ῡ
        Dν η ν x t hμt_pos]
  set μt : ℝ := cxComb μ mBar t x with hμt_def
  set υt : ℝ := cxComb υ ῡ t x with hυt_def
  set p_t : Fin d → ℝ := fun i => cxCombGrad Dυ Dῡ t i x with hpt_def
  set Δp_t : Fin d → ℝ := fun i => |Dῡ i x| + |Dυ i x| with hΔp_def
  set Δm : ℝ := |mBar x| + |μ x| with hΔm_def
  set Δυ : ℝ := |ῡ x| + |υ x| with hΔυ_def
  have hCpos : 0 < Cε := hCε_pos
  have hα_ge : 1 ≤ hweak.α := hweak.hα.le
  have hαm1_nn : 0 ≤ hweak.α - 1 := by linarith
  have hα_nn : 0 ≤ hweak.α := by linarith
  have hβ_nn : 0 ≤ hweak.β := hweak.hβ.le
  have hΔm_nn : 0 ≤ Δm := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hΔυ_nn : 0 ≤ Δυ := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hΔp_nn : 0 ≤ ‖Δp_t‖ := norm_nonneg _
  have hpt_norm_nn : 0 ≤ ‖p_t‖ := norm_nonneg _
  have h_abs_μt : |μt| ≤ Δm := cxComb_abs_le μ mBar x ht
  have h_abs_υt : |υt| ≤ Δυ := cxComb_abs_le υ ῡ x ht
  have h_norm_pt : ‖p_t‖ ≤ ‖Δp_t‖ := cxCombGrad_norm_le Dυ Dῡ x ht
  have heq_unreg :
      aepsiIntegrandAt_unreg V H' DpH' Dυ Dῡ μ mBar υ ῡ Dν η ν x t
        = (-υt - H' x p_t μt + V x) * η x
          + μt * (DpH' x p_t μt ⬝ (fun i => Dν i x))
          + (μt - 1) * ν x := rfl
  rw [Real.norm_eq_abs, heq_unreg]
  have htri :
      |((-υt - H' x p_t μt + V x) * η x
          + μt * (DpH' x p_t μt ⬝ (fun i => Dν i x)))
        + (μt - 1) * ν x|
        ≤ |(-υt - H' x p_t μt + V x) * η x|
            + |μt * (DpH' x p_t μt ⬝ (fun i => Dν i x))|
            + |(μt - 1) * ν x| := by
    have h1 : |((-υt - H' x p_t μt + V x) * η x
                  + μt * (DpH' x p_t μt ⬝ (fun i => Dν i x)))
                + (μt - 1) * ν x|
              ≤ |(-υt - H' x p_t μt + V x) * η x
                  + μt * (DpH' x p_t μt ⬝ (fun i => Dν i x))|
                + |(μt - 1) * ν x| := abs_add_le _ _
    have h2 : |(-υt - H' x p_t μt + V x) * η x
                + μt * (DpH' x p_t μt ⬝ (fun i => Dν i x))|
              ≤ |(-υt - H' x p_t μt + V x) * η x|
                + |μt * (DpH' x p_t μt ⬝ (fun i => Dν i x))| := abs_add_le _ _
    linarith
  have h_first_split :
      |(-υt - H' x p_t μt + V x) * η x|
        ≤ (|υt| + |H' x p_t μt| + |V x|) * |η x| := by
    rw [abs_mul]
    have htri3 : |-υt - H' x p_t μt + V x|
                  ≤ |υt| + |H' x p_t μt| + |V x| := by
      have hA : |(-υt - H' x p_t μt) + V x|
                  ≤ |(-υt - H' x p_t μt)| + |V x| := abs_add_le _ _
      have hB : |-υt - H' x p_t μt| ≤ |-υt| + |H' x p_t μt| := by
        have := abs_sub (-υt) (H' x p_t μt)
        simpa using this
      have hCneg : |-υt| = |υt| := abs_neg _
      have heq : -υt - H' x p_t μt + V x = (-υt - H' x p_t μt) + V x := by ring
      rw [heq]; linarith
    exact mul_le_mul_of_nonneg_right htri3 (abs_nonneg _)
  have h_dot_split :
      |μt * (DpH' x p_t μt ⬝ (fun i => Dν i x))|
        ≤ ‖μt • DpH' x p_t μt‖ * ∑ i, |Dν i x| := by
    rw [abs_mul]
    have hdot : |DpH' x p_t μt ⬝ (fun i => Dν i x)|
        ≤ ‖DpH' x p_t μt‖ * ∑ i, |Dν i x| := by
      -- `|∑ vᵢ wᵢ| ≤ ∑ |vᵢ||wᵢ| ≤ ∑ ‖v‖|wᵢ| = ‖v‖ · ∑|wᵢ|`.
      have hsum : |∑ i, DpH' x p_t μt i * Dν i x|
          ≤ ∑ i, |DpH' x p_t μt i * Dν i x| := Finset.abs_sum_le_sum_abs _ _
      have hcoord : ∀ i ∈ (Finset.univ : Finset (Fin d)),
          |DpH' x p_t μt i * Dν i x| ≤ ‖DpH' x p_t μt‖ * |Dν i x| := by
        intro i _
        rw [abs_mul]
        have h1 : |DpH' x p_t μt i| ≤ ‖DpH' x p_t μt‖ := by
          have := norm_le_pi_norm (DpH' x p_t μt) i
          rw [Real.norm_eq_abs] at this; exact this
        exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      have hbnd : ∑ i, |DpH' x p_t μt i * Dν i x|
          ≤ ∑ i, ‖DpH' x p_t μt‖ * |Dν i x| := Finset.sum_le_sum hcoord
      have hfact : (∑ i, ‖DpH' x p_t μt‖ * |Dν i x|)
          = ‖DpH' x p_t μt‖ * ∑ i, |Dν i x| := by rw [← Finset.mul_sum]
      have hdef : DpH' x p_t μt ⬝ (fun i => Dν i x)
          = ∑ i, DpH' x p_t μt i * Dν i x := rfl
      rw [hdef]
      linarith [hsum, hbnd, hfact.le, hfact.ge]
    have hμt_abs_nn : 0 ≤ |μt| := abs_nonneg _
    have hbnd1 : |μt| * |DpH' x p_t μt ⬝ (fun i => Dν i x)|
                  ≤ |μt| * (‖DpH' x p_t μt‖ * ∑ i, |Dν i x|) :=
      mul_le_mul_of_nonneg_left hdot hμt_abs_nn
    have hsmul : ‖μt • DpH' x p_t μt‖ = |μt| * ‖DpH' x p_t μt‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    rw [hsmul]
    nlinarith [hbnd1, abs_nonneg μt, norm_nonneg (DpH' x p_t μt),
      Finset.sum_nonneg
        (s := (Finset.univ : Finset (Fin d))) (f := fun i => |Dν i x|)
        (fun _ _ => abs_nonneg (Dν _ x))]
  have h_third_split :
      |(μt - 1) * ν x| ≤ (|μt| + 1) * |ν x| := by
    rw [abs_mul]
    have h1 : |μt - 1| ≤ |μt| + |(1 : ℝ)| := abs_sub _ _
    have h2 : |(1 : ℝ)| = 1 := abs_one
    rw [h2] at h1
    exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  -- Endpoint dominators (from the AE-supplied hypotheses).
  have hH := hxH
  have hmDpHx := hxmDpH t hμt_pos
  have h_pα : ‖p_t‖ ^ hweak.α ≤ ‖Δp_t‖ ^ hweak.α :=
    Real.rpow_le_rpow hpt_norm_nn h_norm_pt hα_nn
  have h_pαm1 : ‖p_t‖ ^ (hweak.α - 1) ≤ ‖Δp_t‖ ^ (hweak.α - 1) :=
    Real.rpow_le_rpow hpt_norm_nn h_norm_pt hαm1_nn
  have hμt_le_abs : μt ≤ |μt| := le_abs_self _
  have h_μt_nn : 0 ≤ μt := hμt_pos.le
  have h_μt_le_Δm : μt ≤ Δm := le_trans hμt_le_abs h_abs_μt
  have h_μtβ : μt ^ hweak.β ≤ Δm ^ hweak.β :=
    Real.rpow_le_rpow h_μt_nn h_μt_le_Δm hβ_nn
  have hβoα_le_β : hweak.β / hweak.α ≤ hweak.β := by
    have hαpos : 0 < hweak.α := lt_trans one_pos hweak.hα
    rw [div_le_iff₀ hαpos]
    have hβpos : 0 ≤ hweak.β := hweak.hβ.le
    have := mul_le_mul_of_nonneg_left hα_ge hβpos
    linarith
  have h_pow_exp_nn : 0 ≤ 1 + hweak.β - hweak.β / hweak.α := by
    have : 0 ≤ hweak.β - hweak.β / hweak.α := by linarith
    linarith
  have h_μt_pow_endpoint :
      μt ^ (1 + hweak.β - hweak.β / hweak.α)
        ≤ Δm ^ (1 + hweak.β - hweak.β / hweak.α) :=
    Real.rpow_le_rpow h_μt_nn h_μt_le_Δm h_pow_exp_nn
  have h_H_endpoint :
      |H' x p_t μt|
        ≤ C' * (‖Δp_t‖ ^ hweak.α + 1) + Cε * (Δm ^ hweak.β + 1) := by
    have hC'_mono : C' * (‖p_t‖ ^ hweak.α + 1) ≤ C' * (‖Δp_t‖ ^ hweak.α + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hC'_pos.le
    have hC_mono : Cε * (μt ^ hweak.β + 1) ≤ Cε * (Δm ^ hweak.β + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hCpos.le
    linarith
  have h_pαm1_nn : 0 ≤ ‖p_t‖ ^ (hweak.α - 1) := Real.rpow_nonneg hpt_norm_nn _
  have h_Δpαm1_nn : 0 ≤ ‖Δp_t‖ ^ (hweak.α - 1) := Real.rpow_nonneg hΔp_nn _
  have h_factor_pow :
      μt * ‖p_t‖ ^ (hweak.α - 1) ≤ Δm * ‖Δp_t‖ ^ (hweak.α - 1) := by
    have step1 : μt * ‖p_t‖ ^ (hweak.α - 1) ≤ μt * ‖Δp_t‖ ^ (hweak.α - 1) :=
      mul_le_mul_of_nonneg_left h_pαm1 h_μt_nn
    have step2 : μt * ‖Δp_t‖ ^ (hweak.α - 1) ≤ Δm * ‖Δp_t‖ ^ (hweak.α - 1) :=
      mul_le_mul_of_nonneg_right h_μt_le_Δm h_Δpαm1_nn
    linarith
  have h_mDpH_endpoint :
      ‖μt • DpH' x p_t μt‖
        ≤ Cε * (Δm * ‖Δp_t‖ ^ (hweak.α - 1)
                  + Δm ^ (1 + hweak.β - hweak.β / hweak.α) + Δm) := by
    have hinner :
        μt * ‖p_t‖ ^ (hweak.α - 1)
            + μt ^ (1 + hweak.β - hweak.β / hweak.α) + μt
          ≤ Δm * ‖Δp_t‖ ^ (hweak.α - 1)
              + Δm ^ (1 + hweak.β - hweak.β / hweak.α) + Δm := by
      linarith
    have := mul_le_mul_of_nonneg_left hinner hCpos.le
    linarith
  have h_sumDν_nn : 0 ≤ ∑ i, |Dν i x| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have h_second_endpoint :
      ‖μt • DpH' x p_t μt‖ * ∑ i, |Dν i x|
        ≤ Cε * (Δm * ‖Δp_t‖ ^ (hweak.α - 1)
                  + Δm ^ (1 + hweak.β - hweak.β / hweak.α) + Δm)
            * (∑ i, |Dν i x|) :=
    mul_le_mul_of_nonneg_right h_mDpH_endpoint h_sumDν_nn
  have h_third_endpoint :
      (|μt| + 1) * |ν x| ≤ (Δm + 1) * |ν x| :=
    mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
  have h_first_endpoint :
      (|υt| + |H' x p_t μt| + |V x|) * |η x|
        ≤ (Δυ + (C' * (‖Δp_t‖ ^ hweak.α + 1) + Cε * (Δm ^ hweak.β + 1)) + |V x|)
            * |η x| :=
    mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
  have hAcc :
      |(-υt - H' x p_t μt + V x) * η x|
        + |μt * (DpH' x p_t μt ⬝ (fun i => Dν i x))|
        + |(μt - 1) * ν x|
      ≤ (Δυ + (C' * (‖Δp_t‖ ^ hweak.α + 1) + Cε * (Δm ^ hweak.β + 1)) + |V x|)
            * |η x|
        + Cε * (Δm * ‖Δp_t‖ ^ (hweak.α - 1)
                  + Δm ^ (1 + hweak.β - hweak.β / hweak.α) + Δm)
            * (∑ i, |Dν i x|)
        + (Δm + 1) * |ν x| := by
    have hA :
        |(-υt - H' x p_t μt + V x) * η x|
          ≤ (Δυ + (C' * (‖Δp_t‖ ^ hweak.α + 1) + Cε * (Δm ^ hweak.β + 1))
              + |V x|) * |η x| := le_trans h_first_split h_first_endpoint
    have hB :
        |μt * (DpH' x p_t μt ⬝ (fun i => Dν i x))|
          ≤ Cε * (Δm * ‖Δp_t‖ ^ (hweak.α - 1)
                  + Δm ^ (1 + hweak.β - hweak.β / hweak.α) + Δm)
              * (∑ i, |Dν i x|) :=
      le_trans h_dot_split h_second_endpoint
    have hC₃ :
        |(μt - 1) * ν x| ≤ (Δm + 1) * |ν x| :=
      le_trans h_third_split h_third_endpoint
    linarith
  have hgoal_distribute :
      (Δυ + (C' * (‖Δp_t‖ ^ hweak.α + 1) + Cε * (Δm ^ hweak.β + 1)) + |V x|)
            * |η x|
        = Δυ * |η x|
          + (C' * (‖Δp_t‖ ^ hweak.α + 1) + Cε * (Δm ^ hweak.β + 1)) * |η x|
          + |V x| * |η x| := by ring
  -- The `g_unreg_natural` RHS unfolds to exactly the accumulated bound.
  have hgoal_eq :
      g_unreg_natural hweak.α hweak.β Cε C' V Dυ Dῡ μ mBar υ ῡ Dν η ν x
        = Δυ * |η x|
          + (C' * (‖Δp_t‖ ^ hweak.α + 1) + Cε * (Δm ^ hweak.β + 1)) * |η x|
          + |V x| * |η x|
          + Cε * (Δm * ‖Δp_t‖ ^ (hweak.α - 1)
                    + Δm ^ (1 + hweak.β - hweak.β / hweak.α) + Δm)
              * (∑ i, |Dν i x|)
          + (Δm + 1) * |ν x| := by
    simp only [g_unreg_natural, hΔp_def, hΔm_def, hΔυ_def]
  rw [hgoal_eq]
  linarith [htri, hAcc, hgoal_distribute.le, hgoal_distribute.ge]

open StationaryMFG.Periodic StationaryMFG.Theorems.SimplePower in
/-- **D2c-2d-0-a: per-`(u,v,w)` `HemicontSegmentDataK0` builder on
`HdeltaK0`/`K_Aepsi` from AE data.** -/
noncomputable def aepsiDeltaK0_hemicontSegmentDataK0_of_AEData
    (V : (Fin d → ℝ) → ℝ)
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d)
    (hAE : HdeltaAEPowerEpsData (H := H) (DpH := DpH) hweak qε)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (hβconj : βBarReal'.HolderConjugate βBarReal)
    (hγconj : γBarReal'.HolderConjugate γBarReal)
    (hγ2 : 1 < γBarReal)
    (hSeg : ∀ (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1),
      PaperSection8SegmentResiduesMinExp
        (d := d) γBarReal βBarReal βBarReal' γBarReal' hweak.α hweak.β)
    -- K0 unreg/Gateaux measurability on `K0_Aepsi` (⊇ `K_Aepsi`), from the
    -- AE analytic/measurability riders.
    (hF_unreg_meas : ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      ∀ (u v : XBanach d βBarReal γBarReal),
                u ∈ K0_Aepsi d βBarReal γBarReal →
                v ∈ K0_Aepsi d βBarReal γBarReal →
                ∀ (w : XBanach d βBarReal γBarReal),
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        MeasureTheory.AEStronglyMeasurable
          (fun x => aepsiIntegrandAt_unreg_K0 V (HdeltaK0 hweak ε)
                      (DpHepsilon hweak (qε ε))
                      (DuOf v) (DuOf u) (mOf v) (mOf u)
                      (uOf v) (uOf u)
                      (fun i => ⇑(w.2.2 i)) (⇑w.1) (⇑w.2.1) x t)
          (MeasureTheory.volume.restrict (UnitCube d)))
    (hF_gat_meas : ∀ (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1),
      ∀ (u v : XBanach d βBarReal γBarReal),
                u ∈ K0_Aepsi d βBarReal γBarReal →
                v ∈ K0_Aepsi d βBarReal γBarReal →
                ∀ (w : XBanach d βBarReal γBarReal),
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        MeasureTheory.AEStronglyMeasurable
          (fun x => aepsiIntegrandAt_gateaux γBarReal
                      (DuOf v) (DuOf u) (uOf v) (uOf u)
                      (fun i => ⇑(w.2.2 i)) (⇑w.2.1) x t)
          (MeasureTheory.volume.restrict (UnitCube d))) :
    ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      ∀ (u v : XBanach d βBarReal γBarReal),
              u ∈ K_Aepsi d βBarReal γBarReal →
              v ∈ K_Aepsi d βBarReal γBarReal →
              ∀ (w : XBanach d βBarReal γBarReal),
        HemicontSegmentDataK0 (d := d)
          V (HdeltaK0 hweak ε) (DpHepsilon hweak (qε ε)) γBarReal
          (DuOf v) (DuOf u) (mOf v) (mOf u) (uOf v) (uOf u)
          (fun i => ⇑(w.2.2 i)) (⇑w.1) (⇑w.2.1) := by
  intro ε hε hε1 u v hu hv w
  classical
  -- `K0`-route abbreviations: `HdeltaK0 = Hdelta` on the strict segment.
  set Cε : ℝ := CdeltaEps (H := H) (DpH := DpH) hweak ε with hCε_def
  -- The strict segment positivity on `K_Aepsi` (weakened to non-strict for
  -- the `hNonneg` field).
  have hPos : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
                ∀ t ∈ Set.Icc (0 : ℝ) 1,
                  0 < cxComb (mOf v) (mOf u) t x :=
    K_Aepsi_segment_pos hv hu
  have hNonneg : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
                  ∀ t ∈ Set.Icc (0 : ℝ) 1,
                    0 ≤ cxComb (mOf v) (mOf u) t x := by
    filter_upwards [hPos] with x hx t ht
    exact (hx t ht).le
  -- The H-abs constant `C'` from the AE estimates. Use `.choose` (not
  -- `obtain`) since the surrounding term eliminates into `Type`.
  set hAbsEx :=
    aepsiDeltaK0_segHAbsDominator_of_AEData (H := H) (DpH := DpH) hweak qε hAE
      hε hε1 (mOf v) (mOf u) (DuOf v) (DuOf u) with hAbsEx_def
  set C' : ℝ := hAbsEx.choose with hC'_def
  have hC'_pos : 0 < C' := hAbsEx.choose_spec.1
  have hHabs := hAbsEx.choose_spec.2
  have hmDpH :=
    aepsiDeltaK0_segMDpHDominator_of_AEData (H := H) (DpH := DpH) hweak qε hAE
      hε hε1 (mOf v) (mOf u) (DuOf v) (DuOf u)
  -- Memberships in `K0_Aepsi`.
  have hu_K0 : u ∈ K0_Aepsi d βBarReal γBarReal :=
    K_Aepsi_subset_K0_Aepsi d βBarReal γBarReal hu
  have hv_K0 : v ∈ K0_Aepsi d βBarReal γBarReal :=
    K_Aepsi_subset_K0_Aepsi d βBarReal γBarReal hv
  -- Unpack the 11 paper-faithful residues.
  obtain ⟨hη, hDν, hν_γ,
          hΔυ, hΔp_pow, hΔm_pow, hΔm_grad, hΔm_endpoint, hΔm,
          hG_grad, hG_val⟩ :=
    (hSeg ε hε hε1).out u v hu hv w
  -- `1 ≤ ENNReal.ofReal γBarReal` for the integrability helper.
  have hγ_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal γBarReal := by
    have h1 : ENNReal.ofReal 1 ≤ ENNReal.ofReal γBarReal :=
      ENNReal.ofReal_le_ofReal hγ2.le
    simpa using h1
  refine
    { hNonneg := hNonneg
      g_unreg := g_unreg_natural hweak.α hweak.β Cε C' V
                  (DuOf v) (DuOf u) (mOf v) (mOf u) (uOf v) (uOf u)
                  (fun i => ⇑(w.2.2 i)) (⇑w.1) (⇑w.2.1)
      g_gat := g_gat_natural γBarReal
                  (DuOf v) (DuOf u) (uOf v) (uOf u)
                  (fun i => ⇑(w.2.2 i)) (⇑w.2.1)
      hg_unreg_int := ?_
      hg_gat_int := ?_
      hF_unreg_meas := ?_
      hF_unreg_bound := ?_
      hF_gat_meas := ?_
      hF_gat_bound := ?_ }
  · -- `hg_unreg_int`: integrability of `g_unreg_natural` at the bare exponents.
    exact g_unreg_natural_integrableOn_min (α := hweak.α) (β := hweak.β)
      (C := Cε) (C' := C') (V := V)
      (Dυ := DuOf v) (Dῡ := DuOf u)
      (μ := mOf v) (mBar := mOf u) (υ := uOf v) (ῡ := uOf u)
      (Dν := fun i => ⇑(w.2.2 i)) (η := ⇑w.1) (ν := ⇑w.2.1)
      hβconj hγconj hγ_one_le hη hDν hν_γ hV hΔυ
      hΔp_pow hΔm_pow hΔm_grad hΔm_endpoint hΔm
  · -- `hg_gat_int`: integrability of `g_gat_natural`.
    exact g_gat_natural_integrableOn (γBar := γBarReal)
      (Dυ := DuOf v) (Dῡ := DuOf u) (υ := uOf v) (ῡ := uOf u)
      (Dν := fun i => ⇑(w.2.2 i)) (ν := ⇑w.2.1) hγconj hDν hν_γ
      hG_grad hG_val
  · -- `hF_unreg_meas`: K0 integrand measurability from the AE rider.
    exact hF_unreg_meas ε hε hε1 u v hu_K0 hv_K0 w
  · -- `hF_unreg_bound`: pointwise bound on the K0 integrand, on the strict
    -- segment (which holds a.e. by `hPos`).
    intro t ht
    have hbnd :=
      aepsiDeltaK0_unregK0_pointwise_bound_of_AEData (H := H) (DpH := DpH)
        V hweak qε hAE hε hε1 hC'_pos
        (mOf v) (mOf u) (uOf v) (uOf u) (DuOf v) (DuOf u)
        (fun i => ⇑(w.2.2 i)) (⇑w.1) (⇑w.2.1) hHabs hmDpH
    filter_upwards [hbnd, hPos] with x hx hposx
    exact hx t ht (hposx t ht)
  · -- `hF_gat_meas`: Gateaux measurability from the AE rider.
    exact hF_gat_meas ε hε hε1 u v hu_K0 hv_K0 w
  · -- `hF_gat_bound`: carrier-free Gateaux bound (product form).
    intro t ht
    have hgat :=
      aepsiIntegrandAt_gateaux_pointwise_bound_product
        (γBar := γBarReal) hγ2
        (DuOf v) (DuOf u) (uOf v) (uOf u)
        (fun i => ⇑(w.2.2 i)) (⇑w.2.1)
    refine MeasureTheory.ae_of_all _ ?_
    intro x
    exact hgat x t ht

open StationaryMFG.Periodic StationaryMFG.Theorems.SimplePower in
/-- **D2c-2d-0-c (helper): the K0/`HdeltaK0`-keyed `aepsiIntegrandAt_unreg_K0`
measurability rider on `K0_Aepsi`, from AE data.**

The `hF_unreg_meas` input shape that `aepsiDeltaK0_hemicontSegmentDataK0_of_AEData`
consumes is keyed on the closed-cone integrand `aepsiIntegrandAt_unreg_K0` over the
genuine `HdeltaK0 hweak ε` carrier. This helper produces the K0 form
DIRECTLY: the `HdeltaK0` composite is AE-measurable on `K0_Aepsi` (where
`cxComb ≥ 0` a.e.) via `aemeasurable_HdeltaK0_comp_of_rc0` (NO congr to `Hdelta`),
the flux composite via `measurable_DpHepsilonFam_of_selector`, fed to
`aestronglyMeasurable_aepsiIntegrandAt_unreg_of_aeMeasH`; finally
`aepsiIntegrandAt_unreg_K0_eq_unreg` (same `H`, pointwise) rewrites the strict
integrand to the `_K0` form. Mirrors BanachBridge.lean:1567-1657.

GATE: binds `(hweak, qε, sel, hMeas, hmonBoundary, hdiffBoundary, hV)`; NO `powData`,
NO `HypothesisPowerGrowth (HdeltaPos …)`, NO `RegularityH (HdeltaPos …)`, NO
`hFormPos`/`hqE_per`/`hInj`/`hSurj`/`qEofMinv`. -/
theorem aepsiDeltaK0_unregK0_meas_of_AEData
    (V : (Fin d → ℝ) → ℝ)
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d)
    (sel : InfConvSelectorFamily (H := H) (DpH := DpH) hweak qε)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (hmonBoundary : Hamiltonian.HypothesisMonotone (d := d) H DpH)
    (hdiffBoundary : Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V) :
    ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      ∀ (u v : XBanach d βBarReal γBarReal),
                u ∈ K0_Aepsi d βBarReal γBarReal →
                v ∈ K0_Aepsi d βBarReal γBarReal →
                ∀ (w : XBanach d βBarReal γBarReal),
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        MeasureTheory.AEStronglyMeasurable
          (fun x => aepsiIntegrandAt_unreg_K0 V (HdeltaK0 hweak ε)
                      (DpHepsilon hweak (qε ε))
                      (DuOf v) (DuOf u) (mOf v) (mOf u)
                      (uOf v) (uOf u)
                      (fun i => ⇑(w.2.2 i)) (⇑w.1) (⇑w.2.1) x t)
          (MeasureTheory.volume.restrict (UnitCube d)) := by
  intro ε hε hε1 u v hu hv w t ht
  have ht0 : (0 : ℝ) ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have hmu_nonneg : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      0 ≤ mOf u x := hu
  have hmv_nonneg : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      0 ≤ mOf v x := hv
  -- AEStronglyMeasurable witnesses for all bare ingredients.
  have hmv_asm : MeasureTheory.AEStronglyMeasurable (mOf v)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    MeasureTheory.Lp.aestronglyMeasurable v.1
  have hmu_asm : MeasureTheory.AEStronglyMeasurable (mOf u)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    MeasureTheory.Lp.aestronglyMeasurable u.1
  have huv_asm : MeasureTheory.AEStronglyMeasurable (uOf v)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    MeasureTheory.Lp.aestronglyMeasurable v.2.1
  have huu_asm : MeasureTheory.AEStronglyMeasurable (uOf u)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    MeasureTheory.Lp.aestronglyMeasurable u.2.1
  have hDuv_asm : ∀ i, MeasureTheory.AEStronglyMeasurable (DuOf v i)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    fun i => MeasureTheory.Lp.aestronglyMeasurable (v.2.2 i)
  have hDuu_asm : ∀ i, MeasureTheory.AEStronglyMeasurable (DuOf u i)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    fun i => MeasureTheory.Lp.aestronglyMeasurable (u.2.2 i)
  have hDuw_asm : ∀ i, MeasureTheory.AEStronglyMeasurable (fun x => ⇑(w.2.2 i) x)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    fun i => MeasureTheory.Lp.aestronglyMeasurable (w.2.2 i)
  have hηw_asm : MeasureTheory.AEStronglyMeasurable (fun x => (⇑w.1) x)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    MeasureTheory.Lp.aestronglyMeasurable w.1
  have hνw_asm : MeasureTheory.AEStronglyMeasurable (fun x => (⇑w.2.1) x)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    MeasureTheory.Lp.aestronglyMeasurable w.2.1
  have hV_asm : MeasureTheory.AEStronglyMeasurable V
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    hV.aestronglyMeasurable
  -- The convex-combination density slot is nonnegative a.e. on `K0_Aepsi`.
  have hμt_nonneg : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      0 ≤ cxComb (mOf v) (mOf u) t x := by
    filter_upwards [hmu_nonneg, hmv_nonneg] with x hxu hxv
    have h1t : (0 : ℝ) ≤ 1 - t := by linarith
    have : 0 ≤ (1 - t) * mOf u x + t * mOf v x :=
      add_nonneg (mul_nonneg h1t hxu) (mul_nonneg ht0 hxv)
    simpa [cxComb] using this
  -- AE composites of the gradient/density slots.
  have hμt_aem : AEMeasurable
      (fun x => cxComb (mOf v) (mOf u) t x)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    StationaryMFG.Theorems.SimplePower.aemeasurable_cxComb_at (d := d) t hmv_asm hmu_asm
  have hpt_aem : AEMeasurable
      (fun x : Fin d → ℝ =>
        (fun i : Fin d => cxCombGrad (DuOf v) (DuOf u) t i x))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    StationaryMFG.Theorems.SimplePower.aemeasurable_cxCombGrad_pi (d := d) t hDuv_asm hDuu_asm
  have htriple : AEMeasurable
      (fun x : Fin d → ℝ =>
        (x, (fun i : Fin d => cxCombGrad (DuOf v) (DuOf u) t i x),
          cxComb (mOf v) (mOf u) t x))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    measurable_id.aemeasurable.prodMk (hpt_aem.prodMk hμt_aem)
  -- H-composite on the genuine `HdeltaK0` carrier.
  have hHK0_ae : AEMeasurable
      (fun x : Fin d → ℝ =>
        HdeltaK0 hweak ε x (fun i => cxCombGrad (DuOf v) (DuOf u) t i x)
          (cxComb (mOf v) (mOf u) t x))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    aemeasurable_HdeltaK0_comp_of_rc0 hweak hMeas hmonBoundary qε sel hε
      hpt_aem hμt_aem hμt_nonneg
  have hDpH_ae : AEMeasurable
      (fun x : Fin d → ℝ =>
        DpHepsilonFam hweak qε ε x
          (fun i => cxCombGrad (DuOf v) (DuOf u) t i x)
          (cxComb (mOf v) (mOf u) t x))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    (measurable_DpHepsilonFam_of_selector hweak qε sel hMeas ε).comp_aemeasurable
      htriple
  -- Strict-cone integrand measurability on `HdeltaK0`, then convert to the K0 form.
  have hStrict := StationaryMFG.Theorems.SimplePower.aestronglyMeasurable_aepsiIntegrandAt_unreg_of_aeMeasH
    (d := d)
    (V := V) (H := HdeltaK0 hweak ε) (DpH := DpHepsilonFam hweak qε ε)
    t hHK0_ae hDpH_ae hmv_asm hmu_asm huv_asm huu_asm hDuv_asm hDuu_asm
    hDuw_asm hηw_asm hνw_asm hV_asm
  refine hStrict.congr ?_
  refine Filter.Eventually.of_forall ?_
  intro x
  exact (aepsiIntegrandAt_unreg_K0_eq_unreg V (HdeltaK0 hweak ε)
    (DpHepsilon hweak (qε ε)) (DuOf v) (DuOf u) (mOf v) (mOf u) (uOf v) (uOf u)
    (fun i => ⇑(w.2.2 i)) (⇑w.1) (⇑w.2.1) x t).symm

open StationaryMFG.Periodic StationaryMFG.Theorems.SimplePower in
/-- **D2c-2d-0-c: the terminal `powData`/`RegularityH`-free per-ε ctx aggregator
on the `HdeltaK0` carrier at bare exponents.**

The final child of D2c2d0. Same conclusion as
`aepsiDeltaContextFamily_K0_of_selectorData` (`∀ ε (hε) (hε1),
AepsiUniformContextK … (HdeltaK0 hweak ε) (DpHepsilon hweak (qε ε)) …`) but with
NO `powData` binder. The structure literal is built DIRECTLY on `HdeltaK0`,
filling every field from the landed AE-route producers (children …0/…0a/…0b/…0b2b
and the helper above). -/
noncomputable def aepsiDeltaContextFamily_K0_of_AEData
    (V : (Fin d → ℝ) → ℝ)
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hMono : Hamiltonian.HypothesisMonotone (d := d) H DpH)
    (qε : QEpsFamily d)
    (sel : InfConvSelectorFamily (H := H) (DpH := DpH) hweak qε)
    (hAE : HdeltaAEPowerEpsData (H := H) (DpH := DpH) hweak qε)
    (hUB : HdeltaUniformBounds (H := H) (DpH := DpH) hweak qε)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (hmonBoundary : Hamiltonian.HypothesisMonotone (d := d) H DpH)
    (hdiffBoundary : Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (hExp : SimplePowerExponentFacts γBarReal
                (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
                (ENNReal.ofReal βBarReal'))
    (hβBar_eq : βBarReal = hweak.β + 1)
    (hγBar_eq : γBarReal = hweak.α * (hweak.β + 1) / hweak.β)
    (hβBar'_eq : βBarReal' = (hweak.β + 1) / hweak.β)
    (hγBar'_eq : γBarReal' = γBarReal / (γBarReal - 1))
    (hβ : βBarReal.HolderConjugate βBarReal')
    (hγ : γBarReal.HolderConjugate γBarReal')
    (hβTop : ENNReal.ofReal γBarReal ≠ ⊤)
    (hβBarTop : ENNReal.ofReal βBarReal ≠ ⊤)
    (hβ_gt1 : 1 < βBarReal) (hγ_gt1 : 1 < γBarReal)
    (hγ'_le_β : ENNReal.ofReal γBarReal' ≤ ENNReal.ofReal βBarReal)
    (hβconj : βBarReal'.HolderConjugate βBarReal)
    (hγconj : γBarReal'.HolderConjugate γBarReal)
    (hd_pos : 0 < (d : ℝ))
    (hScalarMono :
      ∀ s t : ℝ,
        0 ≤ (absPowMinusTwo γBarReal t * t - absPowMinusTwo γBarReal s * s)
              * (t - s))
    (hVecMono :
      ∀ v w : Fin d → ℝ,
        0 ≤ (vecAbsPowMinusTwo γBarReal v • v - vecAbsPowMinusTwo γBarReal w • w)
              ⬝ (v - w))
    (hC0_le : ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      hUB.C0 ≤ CdeltaEps (H := H) (DpH := DpH) hweak ε)
    -- HJB measurability on the `HdeltaPos` carrier (coercivity/aux riders).
    (hF_HJB_meas_Pos : ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      ∀ q : XBanach d βBarReal γBarReal,
        MeasureTheory.AEStronglyMeasurable
          (fun x => -(uOf q x)
              - HdeltaPos hweak ε x (fun i => DuOf q i x) (mOf q x) + V x)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    -- HJB measurability on the genuine `HdeltaK0` carrier (auxHypsK riders).
    (hF_HJB_meas_K0 : ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      ∀ q : XBanach d βBarReal γBarReal,
        MeasureTheory.AEStronglyMeasurable
          (fun x => -(uOf q x)
              - HdeltaK0 hweak ε x (fun i => DuOf q i x) (mOf q x) + V x)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (hF_flux_meas : ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      ∀ q : XBanach d βBarReal γBarReal, ∀ i,
        MeasureTheory.AEStronglyMeasurable
          (fun x => mOf q x
              * DpHepsilonFam hweak qε ε x (fun j => DuOf q j x) (mOf q x) i)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    -- Gateaux integrand measurability on `K0_Aepsi` (hemicont segment data).
    (hF_gat_meas : ∀ (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1),
      ∀ (u v : XBanach d βBarReal γBarReal),
                u ∈ K0_Aepsi d βBarReal γBarReal →
                v ∈ K0_Aepsi d βBarReal γBarReal →
                ∀ (w : XBanach d βBarReal γBarReal),
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        MeasureTheory.AEStronglyMeasurable
          (fun x => aepsiIntegrandAt_gateaux γBarReal
                      (DuOf v) (DuOf u) (uOf v) (uOf u)
                      (fun i => ⇑(w.2.2 i)) (⇑w.2.1) x t)
          (MeasureTheory.volume.restrict (UnitCube d)))
    -- The constant-`μ ≡ 1` aux on the raw `Hdelta` carrier (coercivity rider).
    (aux10 : ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
        V (Hdelta hweak ε) (DpHepsilonFam hweak qε ε)
        (fun (_ : Fin d) (_ : (Fin d → ℝ)) => (0 : ℝ))
        (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ)))
    -- Weak-derivative tie on `K0_Aepsi` (structural input carrier).
    (hWeakDerivK0 :
      ∀ q ∈ K0_Aepsi d βBarReal γBarReal,
        ∀ i, HasWeakDerivPer (d := d) i (uOf q) (DuOf q i)) :
    ∀ ε (hε : 0 < ε) (_hε1 : ε ≤ 1),
      AepsiUniformContextK (d := d) ε V (HdeltaK0 hweak ε)
        (DpHepsilon hweak (qε ε))
        γBarReal βBarReal βBarReal' γBarReal' :=
  fun ε hε hε1 => by
    classical
    -- The `K_Aepsi`-indexed `auxHypsK` on the genuine `HdeltaK0` carrier.
    have auxHypsK :
        ∀ q ∈ K_Aepsi d βBarReal γBarReal,
          MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
            V (HdeltaK0 hweak ε) (DpHepsilon hweak (qε ε))
            (fun i => ⇑(q.2.2 i)) (⇑q.1) (⇑q.2.1) :=
      auxHypsK_HdeltaK0_KAepsi_of_AEData
        (V := V) (γBarReal := γBarReal) (βBarReal := βBarReal)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        hweak qε hAE hUB sel hmonBoundary hdiffBoundary hV
        hβBar_eq hγBar_eq hβBar'_eq hγBar'_eq hβ hγ hβTop hγ'_le_β hε hε1
        (hC0_le ε hε hε1) (hF_HJB_meas_K0 ε hε hε1) (hF_flux_meas ε hε hε1)
    -- Reflexivity (carrier-free), from `hExp` (cf.
    -- `aepsiUniformContextK_of_paperHypotheses`).
    have hReflexive :
        Periodic.IsReflexiveNormedSpace (XBanach d βBarReal γBarReal) := by
      have h_one_lt_βBarReal : (1 : ℝ) < βBarReal := by
        by_contra hle
        push_neg at hle
        have h1 : ENNReal.ofReal βBarReal ≤ (1 : ℝ≥0∞) := by
          calc ENNReal.ofReal βBarReal
              ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal hle
            _ = 1 := ENNReal.ofReal_one
        exact absurd hExp.βBar_one_lt (not_lt_of_ge h1)
      have h_βBarReal_pos : (0 : ℝ) < βBarReal := by linarith
      have h_βBar_toReal_eq : (ENNReal.ofReal βBarReal).toReal = βBarReal :=
        ENNReal.toReal_ofReal h_βBarReal_pos.le
      have h_one_lt_βBar' : (1 : ℝ≥0∞) < ENNReal.ofReal βBarReal' :=
        hExp.betaBar'_one_lt
      have h_βBarReal'_pos : (0 : ℝ) < βBarReal' := by
        by_contra hle
        push_neg at hle
        have h_zero : ENNReal.ofReal βBarReal' = 0 :=
          ENNReal.ofReal_eq_zero.mpr hle
        rw [h_zero] at h_one_lt_βBar'
        exact absurd h_one_lt_βBar' (by simp)
      have h_βBar'_toReal_eq : (ENNReal.ofReal βBarReal').toReal = βBarReal' :=
        ENNReal.toReal_ofReal h_βBarReal'_pos.le
      have h_one_le_βBar' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal βBarReal' :=
        h_one_lt_βBar'.le
      haveI : Fact (1 ≤ ENNReal.ofReal βBarReal') := ⟨h_one_le_βBar'⟩
      have hβConj_real : Real.HolderConjugate βBarReal βBarReal' := by
        have := hExp.βConj
        rw [h_βBar_toReal_eq, h_βBar'_toReal_eq] at this
        exact this
      have hβConj_enn :
          ENNReal.HolderConjugate (ENNReal.ofReal βBarReal)
            (ENNReal.ofReal βBarReal') :=
        Real.HolderConjugate.ennrealOfReal hβConj_real
      haveI : ENNReal.HolderConjugate (ENNReal.ofReal βBarReal)
                (ENNReal.ofReal βBarReal') := hβConj_enn
      have h_one_lt_γBarReal : (1 : ℝ) < γBarReal := hExp.γBar_one_lt_real
      have h_γBarReal_pos : (0 : ℝ) < γBarReal := by linarith
      set γBarPrimeReal : ℝ := γBarReal / (γBarReal - 1) with hγBarPrime_def
      have h_γBar_minus_one_pos : (0 : ℝ) < γBarReal - 1 := by linarith
      have h_γBarPrimeReal_pos : (0 : ℝ) < γBarPrimeReal :=
        div_pos h_γBarReal_pos h_γBar_minus_one_pos
      have h_one_lt_γBarPrimeReal : (1 : ℝ) < γBarPrimeReal := by
        rw [hγBarPrime_def, lt_div_iff₀ h_γBar_minus_one_pos, one_mul]
        linarith
      have h_one_le_γBarPrime : (1 : ℝ≥0∞) ≤ ENNReal.ofReal γBarPrimeReal := by
        have h1 : ENNReal.ofReal 1 ≤ ENNReal.ofReal γBarPrimeReal :=
          ENNReal.ofReal_le_ofReal h_one_lt_γBarPrimeReal.le
        simpa using h1
      haveI : Fact (1 ≤ ENNReal.ofReal γBarPrimeReal) := ⟨h_one_le_γBarPrime⟩
      have h_γBar_toReal_eq :
          (ENNReal.ofReal γBarReal).toReal = γBarReal :=
        ENNReal.toReal_ofReal h_γBarReal_pos.le
      have hγConj_real : Real.HolderConjugate γBarReal γBarPrimeReal := by
        have := hExp.γConj
        rw [h_γBar_toReal_eq] at this
        exact this
      have hγConj_enn :
          ENNReal.HolderConjugate (ENNReal.ofReal γBarReal)
            (ENNReal.ofReal γBarPrimeReal) :=
        Real.HolderConjugate.ennrealOfReal hγConj_real
      haveI : ENNReal.HolderConjugate (ENNReal.ofReal γBarReal)
                (ENNReal.ofReal γBarPrimeReal) := hγConj_enn
      have h_βBar_ne_top : (ENNReal.ofReal βBarReal) ≠ ∞ := ENNReal.ofReal_ne_top
      have h_γBar_ne_top : (ENNReal.ofReal γBarReal) ≠ ∞ := ENNReal.ofReal_ne_top
      exact StationaryMFG.Periodic.lpSobolev_product_isReflexive (d := d)
        (ENNReal.ofReal βBarReal) (ENNReal.ofReal βBarReal')
        (ENNReal.ofReal γBarReal) (ENNReal.ofReal γBarPrimeReal)
        hExp.βBar_one_lt h_βBar_ne_top hExp.gammaBar_one_lt h_γBar_ne_top
    -- The K0 uniform aux record (from `auxHypsK0K0`).
    obtain ⟨_auxHypsK0Pos, auxHypsK0K0, _hWeakDerivK0'⟩ :=
      aepsiDeltaK0_auxK0WeakDerivRiders_of_AEData
        (V := V) (γBarReal := γBarReal) (βBarReal := βBarReal)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        hweak qε hAE hUB sel hmonBoundary hdiffBoundary hV
        hβBar_eq hγBar_eq hβBar'_eq hγBar'_eq hβ hγ hβTop hγ'_le_β
        hC0_le hF_HJB_meas_Pos hF_HJB_meas_K0 hF_flux_meas hWeakDerivK0
    have hAux :
        MFGOpEpsUniformAux (d := d) ε V (HdeltaK0 hweak ε)
          (DpHepsilon hweak (qε ε)) γBarReal βBarReal βBarReal' γBarReal'
          (K0_Aepsi d βBarReal γBarReal) :=
      Banach.mfgOpEps_uniformAux_of_perPairAuxHyps ε
        (K0_Aepsi d βBarReal γBarReal) (auxHypsK0K0 ε hε hε1)
    -- Monotonicity from the bare Lasry–Lions inequality.
    have hMonoLift :
        Monotone.IsMonotone (X := XBanach d βBarReal γBarReal)
          (K_Aepsi d βBarReal γBarReal)
          (Banach.Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
            (βBarReal' := βBarReal') (γBarReal' := γBarReal')
            V (HdeltaK0 hweak ε) (DpHepsilon hweak (qε ε)) auxHypsK ε) :=
      Banach.Aepsi_mono_of_paperHypotheses_of_ll (γBarReal := γBarReal)
        (βBarReal := βBarReal) (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        V (HdeltaK0 hweak ε) (DpHepsilon hweak (qε ε)) auxHypsK
        (llMono_HdeltaK0_of_AEData hweak hMono qε sel hε) hε.le hScalarMono hVecMono
    -- Hemicontinuity via the K0 segment data.
    have hRegK0 :=
      regularityHK0_HdeltaK0_DpHepsilon_of_selector
        hweak hmonBoundary hdiffBoundary qε sel hMeas hAE hε hε1
    have hSeg :
        ∀ (e : ℝ) (_hε : 0 < e) (_hε1 : e ≤ 1),
          PaperSection8SegmentResiduesMinExp
            (d := d) γBarReal βBarReal βBarReal' γBarReal' hweak.α hweak.β :=
      fun _e _he _he1 =>
        Banach.paperSection8_segmentResiduesMinExp_of_exponents
          (d := d) (γBarReal := γBarReal) (βBarReal := βBarReal)
          (βBarReal' := βBarReal') (γBarReal' := γBarReal')
          hweak.α hweak.β hweak.hα hweak.hβ
          hβBar_eq hγBar_eq hβBar'_eq hγBar'_eq
    have hData :=
      aepsiDeltaK0_hemicontSegmentDataK0_of_AEData
        (V := V) (γBarReal := γBarReal) (βBarReal := βBarReal)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        hweak qε hAE hV hβconj hγconj hγ_gt1 hSeg
        (aepsiDeltaK0_unregK0_meas_of_AEData (H := H) (DpH := DpH) V
          hweak qε sel hMeas hmonBoundary hdiffBoundary hV)
        hF_gat_meas
        ε hε hε1
    have hHCLift :
        Monotone.IsHemicontinuous (X := XBanach d βBarReal γBarReal)
          (K_Aepsi d βBarReal γBarReal)
          (Banach.Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
            (βBarReal' := βBarReal') (γBarReal' := γBarReal')
            V (HdeltaK0 hweak ε) (DpHepsilon hweak (qε ε)) auxHypsK ε) :=
      Banach.isHemicontinuous_Aepsi_CLM_K_Aepsi_K0 (γBarReal := γBarReal)
        (βBarReal := βBarReal) (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        V (HdeltaK0 hweak ε) (DpHepsilon hweak (qε ε)) auxHypsK hRegK0 hγ_gt1 hData
    -- Coercivity via the K0 coercivity rider (extract the existential by
    -- `.choose`, since the surrounding term eliminates into `Type`).
    set hCoercEx :=
      aepsiDeltaK0_coercivityRiderK0_of_AEData
        (V := V) (γBarReal := γBarReal) (βBarReal := βBarReal)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        hweak qε hAE hV hβBar_eq hγBar_eq hβBar'_eq hγBar'_eq hβ hγ
        hβTop hβBarTop hβ_gt1 hγ_gt1 hγ'_le_β hd_pos
        hF_HJB_meas_Pos hF_flux_meas aux10 ε hε hε1 with hCoercEx_def
    have hCoercLift :
        Monotone.IsCoerciveAt (X := XBanach d βBarReal γBarReal)
          (K_Aepsi d βBarReal γBarReal)
          (Banach.Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
            (βBarReal' := βBarReal') (γBarReal' := γBarReal')
            V (HdeltaK0 hweak ε) (DpHepsilon hweak (qε ε)) auxHypsK ε)
          (Banach.qRef_simplePower d βBarReal γBarReal) :=
      Banach.Aepsi_coercive_of_paperHypotheses_scaled (γBarReal := γBarReal)
        (βBarReal := βBarReal) (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        V (HdeltaK0 hweak ε) (DpHepsilon hweak (qε ε)) auxHypsK ε
        (Banach.coercivityGaugeExponent βBarReal γBarReal)
        (Banach.one_lt_coercivityGaugeExponent hβ_gt1 hγ_gt1)
        hCoercEx.choose hCoercEx.choose_spec.choose_spec.1
        hCoercEx.choose_spec.choose hCoercEx.choose_spec.choose_spec.2
    exact
      { hReflexive := hReflexive
        auxHypsK := auxHypsK
        qRef := Banach.qRef_simplePower d βBarReal γBarReal
        hqRef := Banach.qRef_simplePower_mem_K_Aepsi d βBarReal γBarReal
        aux := hAux
        hMono := hMonoLift
        hHC := hHCLift
        hCoerc := hCoercLift
        hWeakDeriv := hWeakDerivK0 }

open StationaryMFG.Periodic StationaryMFG.Theorems.SimplePower in
/-- **G7b (binder-free rider variant).** The `auxHypsK0Pos` / `auxHypsK0K0` pair
of `aepsiDeltaK0_auxK0WeakDerivRiders_of_AEData` (BanachBridge.lean:1801),
**without** the `hWeakDerivK0` binder and **without** the discarded third tuple
slot. The existing producer proves these two slots WITHOUT `hWeakDerivK0`
(`refine ⟨?_, ?_, hWeakDerivK0⟩`, line 1857); this is the same body dropping the
last `refine` slot. Used by the refined-cone ctx producer
`aepsiDeltaContextFamily_K0_W_of_AEData`, where `AepsiUniformContextK_W` carries
the weak-derivative tie structurally via `K0_Aepsi_W` membership (so no
`hWeakDeriv` field, hence no `hWeakDerivK0` input). -/
theorem aepsiDeltaK0_auxK0Riders_of_AEData
    (V : (Fin d → ℝ) → ℝ)
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d)
    (hAE : HdeltaAEPowerEpsData (H := H) (DpH := DpH) hweak qε)
    (hUB : HdeltaUniformBounds (H := H) (DpH := DpH) hweak qε)
    (sel : InfConvSelectorFamily (H := H) (DpH := DpH) hweak qε)
    (hmonBoundary : Hamiltonian.HypothesisMonotone (d := d) H DpH)
    (hdiffBoundary : Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (hβBar_eq : βBarReal = hweak.β + 1)
    (hγBar_eq : γBarReal = hweak.α * (hweak.β + 1) / hweak.β)
    (hβBar'_eq : βBarReal' = (hweak.β + 1) / hweak.β)
    (hγBar'_eq : γBarReal' = γBarReal / (γBarReal - 1))
    (hβ : βBarReal.HolderConjugate βBarReal')
    (hγ : γBarReal.HolderConjugate γBarReal')
    (hβTop : ENNReal.ofReal γBarReal ≠ ⊤)
    (hγ'_le_β : ENNReal.ofReal γBarReal' ≤ ENNReal.ofReal βBarReal)
    (hC0_le : ∀ ε (_hε : 0 < ε) (_hε1 : ε ≤ 1),
      hUB.C0 ≤ CdeltaEps (H := H) (DpH := DpH) hweak ε)
    (hF_HJB_meas : ∀ ε (_hε : 0 < ε) (_hε1 : ε ≤ 1),
      ∀ q : XBanach d βBarReal γBarReal,
        MeasureTheory.AEStronglyMeasurable
          (fun x => -(uOf q x)
              - HdeltaPos hweak ε x (fun i => DuOf q i x) (mOf q x) + V x)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (hF_HJB_meas_K0 : ∀ ε (_hε : 0 < ε) (_hε1 : ε ≤ 1),
      ∀ q : XBanach d βBarReal γBarReal,
        MeasureTheory.AEStronglyMeasurable
          (fun x => -(uOf q x)
              - HdeltaK0 hweak ε x (fun i => DuOf q i x) (mOf q x) + V x)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (hF_flux_meas : ∀ ε (_hε : 0 < ε) (_hε1 : ε ≤ 1),
      ∀ q : XBanach d βBarReal γBarReal, ∀ i,
        MeasureTheory.AEStronglyMeasurable
          (fun x => mOf q x
              * DpHepsilonFam hweak qε ε x (fun j => DuOf q j x) (mOf q x) i)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d))) :
    -- `auxHypsK0Pos`
    (∀ ε (_hε : 0 < ε) (_hε1 : ε ≤ 1),
      ∀ q ∈ K0_Aepsi d βBarReal γBarReal,
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V (HdeltaPos hweak ε) (DpHepsilonFam hweak qε ε)
                    (DuOf q) (mOf q) (uOf q))
    ∧ -- `auxHypsK0K0`
    (∀ ε (_hε : 0 < ε) (_hε1 : ε ≤ 1),
      ∀ q ∈ K0_Aepsi d βBarReal γBarReal,
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V (HdeltaK0 hweak ε) (DpHepsilon hweak (qε ε))
                    (DuOf q) (mOf q) (uOf q)) := by
  refine ⟨?_, ?_⟩
  · intro ε hε hε1
    exact mfgOpEpsAuxHyps_HdeltaPos_of_AEData
      (V := V) (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      hweak qε hAE hV hβBar_eq hγBar_eq hβBar'_eq hγBar'_eq
      hβ hγ hβTop hγ'_le_β hε hε1
      (hF_HJB_meas ε hε hε1) (hF_flux_meas ε hε hε1)
  · intro ε hε hε1
    exact mfgOpEpsAuxHyps_HdeltaK0_of_AEData
      (V := V) (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      hweak qε hAE hUB sel hmonBoundary hdiffBoundary hV
      hβBar_eq hγBar_eq hβBar'_eq hγBar'_eq
      hβ hγ hβTop hγ'_le_β hε hε1 (hC0_le ε hε hε1)
      (hF_HJB_meas_K0 ε hε hε1) (hF_flux_meas ε hε hε1)

open StationaryMFG.Periodic StationaryMFG.Theorems.SimplePower in
/-- **G7b: refined-cone (`K0_Aepsi_W`) sibling of
`aepsiDeltaContextFamily_K0_of_AEData`.**

Returns an `AepsiUniformContextK_W` (no `hWeakDeriv` field) instead of an
`AepsiUniformContextK`, and therefore takes **no** `hWeakDerivK0` binder. This is
the T3 analogue of T1's `aepsiUniformContextK_W_of_paperHypotheses_closed_paper_min`
(`SimplePower/Banach/AssemblyContext.lean:10770`): the Browder–Minty fields
(`hMono`/`hHC`/`hCoerc`) are proved on `K_Aepsi` exactly as in the K-form, then
restricted to the refined cone `K_Aepsi_W` via `K_Aepsi_W_subset_K_Aepsi`; the
uniform aux record is `.mono`-restricted from `K0_Aepsi` to `K0_Aepsi_W` via
`K0_Aepsi_W_subset_K0_Aepsi`. The weak-derivative tie is carried structurally by
`K0_Aepsi_W` membership, so it is no longer an input. -/
noncomputable def aepsiDeltaContextFamily_K0_W_of_AEData
    (V : (Fin d → ℝ) → ℝ)
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (hMono : Hamiltonian.HypothesisMonotone (d := d) H DpH)
    (qε : QEpsFamily d)
    (sel : InfConvSelectorFamily (H := H) (DpH := DpH) hweak qε)
    (hAE : HdeltaAEPowerEpsData (H := H) (DpH := DpH) hweak qε)
    (hUB : HdeltaUniformBounds (H := H) (DpH := DpH) hweak qε)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (hmonBoundary : Hamiltonian.HypothesisMonotone (d := d) H DpH)
    (hdiffBoundary : Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (hExp : SimplePowerExponentFacts γBarReal
                (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
                (ENNReal.ofReal βBarReal'))
    (hβBar_eq : βBarReal = hweak.β + 1)
    (hγBar_eq : γBarReal = hweak.α * (hweak.β + 1) / hweak.β)
    (hβBar'_eq : βBarReal' = (hweak.β + 1) / hweak.β)
    (hγBar'_eq : γBarReal' = γBarReal / (γBarReal - 1))
    (hβ : βBarReal.HolderConjugate βBarReal')
    (hγ : γBarReal.HolderConjugate γBarReal')
    (hβTop : ENNReal.ofReal γBarReal ≠ ⊤)
    (hβBarTop : ENNReal.ofReal βBarReal ≠ ⊤)
    (hβ_gt1 : 1 < βBarReal) (hγ_gt1 : 1 < γBarReal)
    (hγ'_le_β : ENNReal.ofReal γBarReal' ≤ ENNReal.ofReal βBarReal)
    (hβconj : βBarReal'.HolderConjugate βBarReal)
    (hγconj : γBarReal'.HolderConjugate γBarReal)
    (hd_pos : 0 < (d : ℝ))
    (hScalarMono :
      ∀ s t : ℝ,
        0 ≤ (absPowMinusTwo γBarReal t * t - absPowMinusTwo γBarReal s * s)
              * (t - s))
    (hVecMono :
      ∀ v w : Fin d → ℝ,
        0 ≤ (vecAbsPowMinusTwo γBarReal v • v - vecAbsPowMinusTwo γBarReal w • w)
              ⬝ (v - w))
    (hC0_le : ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      hUB.C0 ≤ CdeltaEps (H := H) (DpH := DpH) hweak ε)
    (hF_HJB_meas_Pos : ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      ∀ q : XBanach d βBarReal γBarReal,
        MeasureTheory.AEStronglyMeasurable
          (fun x => -(uOf q x)
              - HdeltaPos hweak ε x (fun i => DuOf q i x) (mOf q x) + V x)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (hF_HJB_meas_K0 : ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      ∀ q : XBanach d βBarReal γBarReal,
        MeasureTheory.AEStronglyMeasurable
          (fun x => -(uOf q x)
              - HdeltaK0 hweak ε x (fun i => DuOf q i x) (mOf q x) + V x)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (hF_flux_meas : ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      ∀ q : XBanach d βBarReal γBarReal, ∀ i,
        MeasureTheory.AEStronglyMeasurable
          (fun x => mOf q x
              * DpHepsilonFam hweak qε ε x (fun j => DuOf q j x) (mOf q x) i)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (hF_gat_meas : ∀ (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1),
      ∀ (u v : XBanach d βBarReal γBarReal),
                u ∈ K0_Aepsi d βBarReal γBarReal →
                v ∈ K0_Aepsi d βBarReal γBarReal →
                ∀ (w : XBanach d βBarReal γBarReal),
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        MeasureTheory.AEStronglyMeasurable
          (fun x => aepsiIntegrandAt_gateaux γBarReal
                      (DuOf v) (DuOf u) (uOf v) (uOf u)
                      (fun i => ⇑(w.2.2 i)) (⇑w.2.1) x t)
          (MeasureTheory.volume.restrict (UnitCube d)))
    (aux10 : ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
        V (Hdelta hweak ε) (DpHepsilonFam hweak qε ε)
        (fun (_ : Fin d) (_ : (Fin d → ℝ)) => (0 : ℝ))
        (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ))) :
    ∀ ε (hε : 0 < ε) (_hε1 : ε ≤ 1),
      AepsiUniformContextK_W (d := d) ε V (HdeltaK0 hweak ε)
        (DpHepsilon hweak (qε ε))
        γBarReal βBarReal βBarReal' γBarReal' :=
  fun ε hε hε1 => by
    classical
    -- The `K_Aepsi`-indexed `auxHypsK` on the genuine `HdeltaK0` carrier.
    have auxHypsK :
        ∀ q ∈ K_Aepsi d βBarReal γBarReal,
          MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
            V (HdeltaK0 hweak ε) (DpHepsilon hweak (qε ε))
            (fun i => ⇑(q.2.2 i)) (⇑q.1) (⇑q.2.1) :=
      auxHypsK_HdeltaK0_KAepsi_of_AEData
        (V := V) (γBarReal := γBarReal) (βBarReal := βBarReal)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        hweak qε hAE hUB sel hmonBoundary hdiffBoundary hV
        hβBar_eq hγBar_eq hβBar'_eq hγBar'_eq hβ hγ hβTop hγ'_le_β hε hε1
        (hC0_le ε hε hε1) (hF_HJB_meas_K0 ε hε hε1) (hF_flux_meas ε hε hε1)
    -- Reflexivity (carrier-free), from `hExp` (cf.
    -- `aepsiUniformContextK_of_paperHypotheses`).
    have hReflexive :
        Periodic.IsReflexiveNormedSpace (XBanach d βBarReal γBarReal) := by
      have h_one_lt_βBarReal : (1 : ℝ) < βBarReal := by
        by_contra hle
        push_neg at hle
        have h1 : ENNReal.ofReal βBarReal ≤ (1 : ℝ≥0∞) := by
          calc ENNReal.ofReal βBarReal
              ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal hle
            _ = 1 := ENNReal.ofReal_one
        exact absurd hExp.βBar_one_lt (not_lt_of_ge h1)
      have h_βBarReal_pos : (0 : ℝ) < βBarReal := by linarith
      have h_βBar_toReal_eq : (ENNReal.ofReal βBarReal).toReal = βBarReal :=
        ENNReal.toReal_ofReal h_βBarReal_pos.le
      have h_one_lt_βBar' : (1 : ℝ≥0∞) < ENNReal.ofReal βBarReal' :=
        hExp.betaBar'_one_lt
      have h_βBarReal'_pos : (0 : ℝ) < βBarReal' := by
        by_contra hle
        push_neg at hle
        have h_zero : ENNReal.ofReal βBarReal' = 0 :=
          ENNReal.ofReal_eq_zero.mpr hle
        rw [h_zero] at h_one_lt_βBar'
        exact absurd h_one_lt_βBar' (by simp)
      have h_βBar'_toReal_eq : (ENNReal.ofReal βBarReal').toReal = βBarReal' :=
        ENNReal.toReal_ofReal h_βBarReal'_pos.le
      have h_one_le_βBar' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal βBarReal' :=
        h_one_lt_βBar'.le
      haveI : Fact (1 ≤ ENNReal.ofReal βBarReal') := ⟨h_one_le_βBar'⟩
      have hβConj_real : Real.HolderConjugate βBarReal βBarReal' := by
        have := hExp.βConj
        rw [h_βBar_toReal_eq, h_βBar'_toReal_eq] at this
        exact this
      have hβConj_enn :
          ENNReal.HolderConjugate (ENNReal.ofReal βBarReal)
            (ENNReal.ofReal βBarReal') :=
        Real.HolderConjugate.ennrealOfReal hβConj_real
      haveI : ENNReal.HolderConjugate (ENNReal.ofReal βBarReal)
                (ENNReal.ofReal βBarReal') := hβConj_enn
      have h_one_lt_γBarReal : (1 : ℝ) < γBarReal := hExp.γBar_one_lt_real
      have h_γBarReal_pos : (0 : ℝ) < γBarReal := by linarith
      set γBarPrimeReal : ℝ := γBarReal / (γBarReal - 1) with hγBarPrime_def
      have h_γBar_minus_one_pos : (0 : ℝ) < γBarReal - 1 := by linarith
      have h_γBarPrimeReal_pos : (0 : ℝ) < γBarPrimeReal :=
        div_pos h_γBarReal_pos h_γBar_minus_one_pos
      have h_one_lt_γBarPrimeReal : (1 : ℝ) < γBarPrimeReal := by
        rw [hγBarPrime_def, lt_div_iff₀ h_γBar_minus_one_pos, one_mul]
        linarith
      have h_one_le_γBarPrime : (1 : ℝ≥0∞) ≤ ENNReal.ofReal γBarPrimeReal := by
        have h1 : ENNReal.ofReal 1 ≤ ENNReal.ofReal γBarPrimeReal :=
          ENNReal.ofReal_le_ofReal h_one_lt_γBarPrimeReal.le
        simpa using h1
      haveI : Fact (1 ≤ ENNReal.ofReal γBarPrimeReal) := ⟨h_one_le_γBarPrime⟩
      have h_γBar_toReal_eq :
          (ENNReal.ofReal γBarReal).toReal = γBarReal :=
        ENNReal.toReal_ofReal h_γBarReal_pos.le
      have hγConj_real : Real.HolderConjugate γBarReal γBarPrimeReal := by
        have := hExp.γConj
        rw [h_γBar_toReal_eq] at this
        exact this
      have hγConj_enn :
          ENNReal.HolderConjugate (ENNReal.ofReal γBarReal)
            (ENNReal.ofReal γBarPrimeReal) :=
        Real.HolderConjugate.ennrealOfReal hγConj_real
      haveI : ENNReal.HolderConjugate (ENNReal.ofReal γBarReal)
                (ENNReal.ofReal γBarPrimeReal) := hγConj_enn
      have h_βBar_ne_top : (ENNReal.ofReal βBarReal) ≠ ∞ := ENNReal.ofReal_ne_top
      have h_γBar_ne_top : (ENNReal.ofReal γBarReal) ≠ ∞ := ENNReal.ofReal_ne_top
      exact StationaryMFG.Periodic.lpSobolev_product_isReflexive (d := d)
        (ENNReal.ofReal βBarReal) (ENNReal.ofReal βBarReal')
        (ENNReal.ofReal γBarReal) (ENNReal.ofReal γBarPrimeReal)
        hExp.βBar_one_lt h_βBar_ne_top hExp.gammaBar_one_lt h_γBar_ne_top
    -- The K0 uniform aux record (from `auxHypsK0K0`), restricted to `K0_Aepsi_W`.
    obtain ⟨_auxHypsK0Pos, auxHypsK0K0⟩ :=
      aepsiDeltaK0_auxK0Riders_of_AEData
        (V := V) (γBarReal := γBarReal) (βBarReal := βBarReal)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        hweak qε hAE hUB sel hmonBoundary hdiffBoundary hV
        hβBar_eq hγBar_eq hβBar'_eq hγBar'_eq hβ hγ hβTop hγ'_le_β
        hC0_le hF_HJB_meas_Pos hF_HJB_meas_K0 hF_flux_meas
    have hAux_K0 :
        MFGOpEpsUniformAux (d := d) ε V (HdeltaK0 hweak ε)
          (DpHepsilon hweak (qε ε)) γBarReal βBarReal βBarReal' γBarReal'
          (K0_Aepsi d βBarReal γBarReal) :=
      Banach.mfgOpEps_uniformAux_of_perPairAuxHyps ε
        (K0_Aepsi d βBarReal γBarReal) (auxHypsK0K0 ε hε hε1)
    have hAux :
        MFGOpEpsUniformAux (d := d) ε V (HdeltaK0 hweak ε)
          (DpHepsilon hweak (qε ε)) γBarReal βBarReal βBarReal' γBarReal'
          (K0_Aepsi_W d βBarReal γBarReal) :=
      hAux_K0.mono (K0_Aepsi_W_subset_K0_Aepsi d βBarReal γBarReal)
    -- Monotonicity from the bare Lasry–Lions inequality, on `K_Aepsi`.
    have hMono_K :
        Monotone.IsMonotone (X := XBanach d βBarReal γBarReal)
          (K_Aepsi d βBarReal γBarReal)
          (Banach.Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
            (βBarReal' := βBarReal') (γBarReal' := γBarReal')
            V (HdeltaK0 hweak ε) (DpHepsilon hweak (qε ε)) auxHypsK ε) :=
      Banach.Aepsi_mono_of_paperHypotheses_of_ll (γBarReal := γBarReal)
        (βBarReal := βBarReal) (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        V (HdeltaK0 hweak ε) (DpHepsilon hweak (qε ε)) auxHypsK
        (llMono_HdeltaK0_of_AEData hweak hMono qε sel hε) hε.le hScalarMono hVecMono
    -- Hemicontinuity via the K0 segment data, on `K_Aepsi`.
    have hRegK0 :=
      regularityHK0_HdeltaK0_DpHepsilon_of_selector
        hweak hmonBoundary hdiffBoundary qε sel hMeas hAE hε hε1
    have hSeg :
        ∀ (e : ℝ) (_hε : 0 < e) (_hε1 : e ≤ 1),
          PaperSection8SegmentResiduesMinExp
            (d := d) γBarReal βBarReal βBarReal' γBarReal' hweak.α hweak.β :=
      fun _e _he _he1 =>
        Banach.paperSection8_segmentResiduesMinExp_of_exponents
          (d := d) (γBarReal := γBarReal) (βBarReal := βBarReal)
          (βBarReal' := βBarReal') (γBarReal' := γBarReal')
          hweak.α hweak.β hweak.hα hweak.hβ
          hβBar_eq hγBar_eq hβBar'_eq hγBar'_eq
    have hData :=
      aepsiDeltaK0_hemicontSegmentDataK0_of_AEData
        (V := V) (γBarReal := γBarReal) (βBarReal := βBarReal)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        hweak qε hAE hV hβconj hγconj hγ_gt1 hSeg
        (aepsiDeltaK0_unregK0_meas_of_AEData (H := H) (DpH := DpH) V
          hweak qε sel hMeas hmonBoundary hdiffBoundary hV)
        hF_gat_meas
        ε hε hε1
    have hHC_K :
        Monotone.IsHemicontinuous (X := XBanach d βBarReal γBarReal)
          (K_Aepsi d βBarReal γBarReal)
          (Banach.Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
            (βBarReal' := βBarReal') (γBarReal' := γBarReal')
            V (HdeltaK0 hweak ε) (DpHepsilon hweak (qε ε)) auxHypsK ε) :=
      Banach.isHemicontinuous_Aepsi_CLM_K_Aepsi_K0 (γBarReal := γBarReal)
        (βBarReal := βBarReal) (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        V (HdeltaK0 hweak ε) (DpHepsilon hweak (qε ε)) auxHypsK hRegK0 hγ_gt1 hData
    -- Coercivity via the K0 coercivity rider, on `K_Aepsi` at `qRef_simplePower`.
    set hCoercEx :=
      aepsiDeltaK0_coercivityRiderK0_of_AEData
        (V := V) (γBarReal := γBarReal) (βBarReal := βBarReal)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        hweak qε hAE hV hβBar_eq hγBar_eq hβBar'_eq hγBar'_eq hβ hγ
        hβTop hβBarTop hβ_gt1 hγ_gt1 hγ'_le_β hd_pos
        hF_HJB_meas_Pos hF_flux_meas aux10 ε hε hε1 with hCoercEx_def
    have hCoerc_K :
        Monotone.IsCoerciveAt (X := XBanach d βBarReal γBarReal)
          (K_Aepsi d βBarReal γBarReal)
          (Banach.Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
            (βBarReal' := βBarReal') (γBarReal' := γBarReal')
            V (HdeltaK0 hweak ε) (DpHepsilon hweak (qε ε)) auxHypsK ε)
          (Banach.qRef_simplePower d βBarReal γBarReal) :=
      Banach.Aepsi_coercive_of_paperHypotheses_scaled (γBarReal := γBarReal)
        (βBarReal := βBarReal) (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        V (HdeltaK0 hweak ε) (DpHepsilon hweak (qε ε)) auxHypsK ε
        (Banach.coercivityGaugeExponent βBarReal γBarReal)
        (Banach.one_lt_coercivityGaugeExponent hβ_gt1 hγ_gt1)
        hCoercEx.choose hCoercEx.choose_spec.choose_spec.1
        hCoercEx.choose_spec.choose hCoercEx.choose_spec.choose_spec.2
    -- Base point and its refined-cone membership.
    have hqRef_W :
        Banach.qRef_simplePower d βBarReal γBarReal
          ∈ K_Aepsi_W d βBarReal γBarReal :=
      Banach.qRef_simplePower_mem_K_Aepsi_W d βBarReal γBarReal
    -- Restrict the three Browder–Minty fields from `K_Aepsi` to `K_Aepsi_W`.
    have hMono_W :
        Monotone.IsMonotone (X := XBanach d βBarReal γBarReal)
          (K_Aepsi_W d βBarReal γBarReal)
          (Banach.Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
            (βBarReal' := βBarReal') (γBarReal' := γBarReal')
            V (HdeltaK0 hweak ε) (DpHepsilon hweak (qε ε)) auxHypsK ε) := by
      intro v₁ hv₁ v₂ hv₂
      exact hMono_K (K_Aepsi_W_subset_K_Aepsi d βBarReal γBarReal hv₁)
                    (K_Aepsi_W_subset_K_Aepsi d βBarReal γBarReal hv₂)
    have hHC_W :
        Monotone.IsHemicontinuous (X := XBanach d βBarReal γBarReal)
          (K_Aepsi_W d βBarReal γBarReal)
          (Banach.Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
            (βBarReal' := βBarReal') (γBarReal' := γBarReal')
            V (HdeltaK0 hweak ε) (DpHepsilon hweak (qε ε)) auxHypsK ε) := by
      intro u hu v hv w
      exact hHC_K (K_Aepsi_W_subset_K_Aepsi d βBarReal γBarReal hu)
                  (K_Aepsi_W_subset_K_Aepsi d βBarReal γBarReal hv) w
    have hCoerc_W :
        Monotone.IsCoerciveAt (X := XBanach d βBarReal γBarReal)
          (K_Aepsi_W d βBarReal γBarReal)
          (Banach.Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
            (βBarReal' := βBarReal') (γBarReal' := γBarReal')
            V (HdeltaK0 hweak ε) (DpHepsilon hweak (qε ε)) auxHypsK ε)
          (Banach.qRef_simplePower d βBarReal γBarReal) := by
      refine ⟨hqRef_W, ?_⟩
      have h_filt_le :
          Monotone.coerciveFilter (K_Aepsi_W d βBarReal γBarReal)
            ≤ Monotone.coerciveFilter (K_Aepsi d βBarReal γBarReal) := by
        unfold Monotone.coerciveFilter
        exact inf_le_inf_left _
          (Filter.principal_mono.mpr
            (K_Aepsi_W_subset_K_Aepsi d βBarReal γBarReal))
      exact hCoerc_K.tendsto.mono_left h_filt_le
    exact
      { hReflexive := hReflexive
        auxHypsK := auxHypsK
        qRef := Banach.qRef_simplePower d βBarReal γBarReal
        hqRef := hqRef_W
        aux := hAux
        hMono := hMono_W
        hHC := hHC_W
        hCoerc := hCoerc_W }

/-! ### G4: carrier/rider producers for the public-theorem tier-5 binders

The four ε-family measurability riders `hF_HJB_meas_Pos`, `hF_HJB_meas_K0`,
`hF_flux_meas`, `hF_gat_meas` of `thm_main_weak_power_growth_paper`, each as a
named producer generic in `(hweak, qε, sel)` plus the accepted carriers
`(hMeas, hmonBoundary, hdiffBoundary, hV)`. Unlike the deleted
`aepsiDeltaK0_analyticMeasRiders_of_AEData`, the HJB binders here range over
*all* `q : XBanach` (NO `q ∈ K0_Aepsi` premise, so `mOf q` need not be a.e.
nonnegative); the H-composite measurability is therefore taken from the
all-`m` building blocks `aemeasurable_HdeltaPos_comp_of_selector` /
`aemeasurable_HdeltaK0_comp_of_rc0_allm` (Properties.lean) rather than the
nonneg-restricted `aemeasurable_HdeltaK0_comp_of_rc0`.

GATE: each producer binds only `(hweak, qε, sel, hMeas, hmonBoundary, hdiffBoundary, hV)`;
NO Pack/Inputs/Oracle, NO `powData`/`HypothesisPowerGrowth (HdeltaPos …)`, NO
`hFormPos`/`hqE_per`/`hInj`/`hSurj`/`qEofMinv`, NO
`epsTerms`/`hIdentityRaw`/`hContRaw`/`hResRaw`/`hIA`/`hIBC`/`hstab`/`εseq`. -/

open StationaryMFG.Periodic StationaryMFG.Theorems.SimplePower in
/-- **G4 (1a): `hF_HJB_meas_Pos` producer.** AE-strong measurability of the
HJB integrand `x ↦ −u(x) − HdeltaPos(x, Du(x), m(x)) + V(x)` on the strict-
positivity carrier `HdeltaPos hweak ε`, for *every* `q : XBanach` (no `K0`
premise). The `HdeltaPos`-composite is measurable for arbitrary `m` via
`aemeasurable_HdeltaPos_comp_of_selector`. -/
theorem T3.hF_HJB_meas_Pos_of_selector
    (V : (Fin d → ℝ) → ℝ)
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d)
    (sel : InfConvSelectorFamily (H := H) (DpH := DpH) hweak qε)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V) :
    ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      ∀ q : XBanach d βBarReal γBarReal,
        MeasureTheory.AEStronglyMeasurable
          (fun x => -(uOf q x)
              - HdeltaPos hweak ε x (fun i => DuOf q i x) (mOf q x) + V x)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
  intro ε hε hε1 q
  have hu_aem : AEMeasurable (uOf q)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    (MeasureTheory.Lp.aestronglyMeasurable q.2.1).aemeasurable
  have hm_aem : AEMeasurable (mOf q)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    (MeasureTheory.Lp.aestronglyMeasurable q.1).aemeasurable
  have hDu_aem : AEMeasurable
      (fun x : Fin d → ℝ => fun i : Fin d => DuOf q i x)
      (MeasureTheory.volume.restrict (UnitCube d)) := by
    refine AEMeasurable.of_eval ?_
    intro i; exact (MeasureTheory.Lp.aestronglyMeasurable (q.2.2 i)).aemeasurable
  have hVmeas : AEMeasurable V
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    hV.aestronglyMeasurable.aemeasurable
  have hHPos : AEMeasurable
      (fun x => HdeltaPos hweak ε x (fun i => DuOf q i x) (mOf q x))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    StationaryMFG.InfimalConvolution.aemeasurable_HdeltaPos_comp_of_selector
      hweak hMeas qε sel hε hDu_aem hm_aem
  exact ((hu_aem.neg.sub hHPos).add hVmeas).aestronglyMeasurable

open StationaryMFG.Periodic StationaryMFG.Theorems.SimplePower in
/-- **G4 (1b): `hF_HJB_meas_K0` producer.** AE-strong measurability of the
HJB integrand on the genuine closed-cone carrier `HdeltaK0 hweak ε`, for *every*
`q : XBanach` (no `K0` premise). The `HdeltaK0`-composite is measurable for
arbitrary `m` via `aemeasurable_HdeltaK0_comp_of_rc0_allm`. -/
theorem T3.hF_HJB_meas_K0_of_selector
    (V : (Fin d → ℝ) → ℝ)
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d)
    (sel : InfConvSelectorFamily (H := H) (DpH := DpH) hweak qε)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (hmonBoundary : Hamiltonian.HypothesisMonotone (d := d) H DpH)
    (hdiffBoundary : Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V) :
    ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      ∀ q : XBanach d βBarReal γBarReal,
        MeasureTheory.AEStronglyMeasurable
          (fun x => -(uOf q x)
              - HdeltaK0 hweak ε x (fun i => DuOf q i x) (mOf q x) + V x)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
  intro ε hε hε1 q
  have hu_aem : AEMeasurable (uOf q)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    (MeasureTheory.Lp.aestronglyMeasurable q.2.1).aemeasurable
  have hm_aem : AEMeasurable (mOf q)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    (MeasureTheory.Lp.aestronglyMeasurable q.1).aemeasurable
  have hDu_aem : AEMeasurable
      (fun x : Fin d → ℝ => fun i : Fin d => DuOf q i x)
      (MeasureTheory.volume.restrict (UnitCube d)) := by
    refine AEMeasurable.of_eval ?_
    intro i; exact (MeasureTheory.Lp.aestronglyMeasurable (q.2.2 i)).aemeasurable
  have hVmeas : AEMeasurable V
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    hV.aestronglyMeasurable.aemeasurable
  have hHK0 : AEMeasurable
      (fun x => HdeltaK0 hweak ε x (fun i => DuOf q i x) (mOf q x))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    StationaryMFG.InfimalConvolution.aemeasurable_HdeltaK0_comp_of_rc0_allm
      hweak hMeas hmonBoundary qε sel hε hDu_aem hm_aem
  exact ((hu_aem.neg.sub hHK0).add hVmeas).aestronglyMeasurable

open StationaryMFG.Periodic StationaryMFG.Theorems.SimplePower in
/-- **G4 (1c): `hF_flux_meas` producer.** AE-strong measurability of the flux
integrand `x ↦ m(x) · D_pH^ε(x, Du(x), m(x)) i`, for every `q : XBanach` and
every `i`. The flux composite is measurable via
`measurable_DpHepsilonFam_of_selector`. -/
theorem T3.hF_flux_meas_of_selector
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d)
    (sel : InfConvSelectorFamily (H := H) (DpH := DpH) hweak qε)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH) :
    ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      ∀ q : XBanach d βBarReal γBarReal, ∀ i,
        MeasureTheory.AEStronglyMeasurable
          (fun x => mOf q x
              * DpHepsilonFam hweak qε ε x (fun j => DuOf q j x) (mOf q x) i)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
  intro ε hε hε1 q i
  have hm_aem : AEMeasurable (mOf q)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    (MeasureTheory.Lp.aestronglyMeasurable q.1).aemeasurable
  have hDu_aem : AEMeasurable
      (fun x : Fin d → ℝ => fun j : Fin d => DuOf q j x)
      (MeasureTheory.volume.restrict (UnitCube d)) := by
    refine AEMeasurable.of_eval ?_
    intro j; exact (MeasureTheory.Lp.aestronglyMeasurable (q.2.2 j)).aemeasurable
  have hxpm : AEMeasurable
      (fun x : Fin d → ℝ => (x, (fun j : Fin d => DuOf q j x), mOf q x))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    measurable_id.aemeasurable.prodMk (hDu_aem.prodMk hm_aem)
  have hDpH : AEMeasurable
      (fun x : Fin d → ℝ =>
        DpHepsilonFam hweak qε ε x (fun j => DuOf q j x) (mOf q x))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    (StationaryMFG.InfimalConvolution.measurable_DpHepsilonFam_of_selector
      hweak qε sel hMeas ε).comp_aemeasurable hxpm
  exact (hm_aem.mul (hDpH.eval i)).aestronglyMeasurable

open StationaryMFG.Periodic StationaryMFG.Theorems.SimplePower in
/-- **G4 (1d): `hF_gat_meas` producer.** AE-strong measurability of the
carrier-free Gateaux integrand `aepsiIntegrandAt_gateaux`. Purely a function of
the `XBanach` Lp components (no Hamiltonian carrier), so it needs only the Lp
strong-measurability witnesses; verbatim from the deleted `…_AEData` gat branch. -/
theorem T3.hF_gat_meas_of_selector
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d)
    (sel : InfConvSelectorFamily (H := H) (DpH := DpH) hweak qε) :
    ∀ (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1),
      ∀ (u v : XBanach d βBarReal γBarReal),
                u ∈ K0_Aepsi d βBarReal γBarReal →
                v ∈ K0_Aepsi d βBarReal γBarReal →
                ∀ (w : XBanach d βBarReal γBarReal),
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        MeasureTheory.AEStronglyMeasurable
          (fun x => aepsiIntegrandAt_gateaux γBarReal
                      (DuOf v) (DuOf u) (uOf v) (uOf u)
                      (fun i => ⇑(w.2.2 i)) (⇑w.2.1) x t)
          (MeasureTheory.volume.restrict (UnitCube d)) := by
  intro ε hε hε1 u v _hu _hv w t _ht
  have huv_asm : MeasureTheory.AEStronglyMeasurable (uOf v)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    MeasureTheory.Lp.aestronglyMeasurable v.2.1
  have huu_asm : MeasureTheory.AEStronglyMeasurable (uOf u)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    MeasureTheory.Lp.aestronglyMeasurable u.2.1
  have hDuv_asm : ∀ i, MeasureTheory.AEStronglyMeasurable (DuOf v i)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    fun i => MeasureTheory.Lp.aestronglyMeasurable (v.2.2 i)
  have hDuu_asm : ∀ i, MeasureTheory.AEStronglyMeasurable (DuOf u i)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    fun i => MeasureTheory.Lp.aestronglyMeasurable (u.2.2 i)
  have hDuw_asm : ∀ i, MeasureTheory.AEStronglyMeasurable (fun x => ⇑(w.2.2 i) x)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    fun i => MeasureTheory.Lp.aestronglyMeasurable (w.2.2 i)
  have hνw_asm : MeasureTheory.AEStronglyMeasurable (fun x => (⇑w.2.1) x)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    MeasureTheory.Lp.aestronglyMeasurable w.2.1
  exact aestronglyMeasurable_aepsiIntegrandAt_gateaux
    (d := d) γBarReal
    (Dυ := DuOf v) (Dῡ := DuOf u) (υ := uOf v) (ῡ := uOf u)
    (Dν := fun i => ⇑(w.2.2 i)) (ν := ⇑w.2.1)
    huv_asm huu_asm hDuv_asm hDuu_asm hDuw_asm hνw_asm t

open StationaryMFG.Periodic StationaryMFG.Theorems.SimplePower in
/-- **G4 (7): `hC0_le` producer.** Per-`ε` reconciliation
`hUB.C0 ≤ CdeltaEps hweak ε`, for the *internally-constructed* uniform-bounds
record `hUB := hdeltaUniformBounds_of_selector …` whose constant is
`C0 = 2^α(C+1)`. The inequality `2^α(C+1) ≤ CdeltaEps hweak ε` is exactly
`cdeltaEps_facts_lower`. (Generic over the `hCx` convex-at-zero input, which the
public theorem supplies via `T3.hCx_of_selector`.) -/
theorem T3.hC0_le_of_uniformBounds
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d)
    (sel : InfConvSelectorFamily (H := H) (DpH := DpH) hweak qε)
    (hCx : ∀ ε, 0 < ε → ε ≤ 1 →
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          Hdelta hweak ε x p m
              - (DpHepsilonFam (H := H) (DpH := DpH) hweak qε ε x p m) ⬝ p
            ≤ Hdelta hweak ε x 0 m) :
    ∀ ε : ℝ, ε > 0 →
      (StationaryMFG.InfimalConvolution.hdeltaUniformBounds_of_selector
          hweak qε sel hCx).C0
        ≤ CdeltaEps (H := H) (DpH := DpH) hweak ε := by
  intro ε hε
  -- `(…).C0 = 2^α(C+1)` by definition; the bound is `cdeltaEps_facts_lower`.
  exact (StationaryMFG.InfimalConvolution.cdeltaEps_facts_lower
    (H := H) (DpH := DpH) hweak hε).2

open StationaryMFG.Periodic StationaryMFG.Theorems.SimplePower in
/-- **G4b: `aux10` producer.** The constant-test-triple
`(Du, m, u) = (0, 1, 0)` `MFGOpEpsAuxHyps` record on the **raw `Hdelta hweak ε`**
carrier (the coercivity-side `aux` consumed by
`aepsiDeltaK0_coercivityRiderK0_of_AEData`).

At the constant triple the five primal-side summands collapse:
* `F_mass (fun _ => 1) = fun _ => 0`, `G_grad _ (fun _ _ => 0) i = fun _ => 0`,
  `G_val _ (fun _ => 0) = fun _ => 0` — each is `· * 0`, so `MemLpPer 0`;
* `F_flux DpH 0 1 i x = 1 · DpH(x,0,1)_i` — dominated by the constant
  `C̃_ε := coercivityCdeltaEpsUniform hweak ε` a.e. (`aeData_DpH01_le_at_uniform`
  + `norm_le_pi_norm`);
* `F_HJB V (Hdelta ε) 0 1 0 x = -(0) - Hdelta(x,0,1) + V x` — dominated by
  `C̃_ε + ‖V x‖` a.e. (`aeData_H01_le_at_uniform`).

The constant-slot measurability is internal: the HJB slot via
`aemeasurable_HdeltaPos_comp_of_selector` at `(Du, m) = (0, 1)` (constants ⇒
`AEMeasurable`), congr'd to raw `Hdelta` everywhere through
`HdeltaPos_eq_Hdelta_of_pos one_pos`; the flux slot via
`measurable_DpHepsilonFam_of_selector` composed with `x ↦ (x, 0, 1)`. No
`powData` / `HypothesisPowerGrowth (HdeltaPos …)` / `hFormPos`. -/
theorem T3.mfgOpEpsAuxHyps_const01_Hdelta_of_selector
    (V : (Fin d → ℝ) → ℝ)
    (hweak : HypothesisWeakGrowth (d := d) H DpH)
    (qε : QEpsFamily d)
    (sel : InfConvSelectorFamily (H := H) (DpH := DpH) hweak qε)
    (hAE : HdeltaAEPowerEpsData (H := H) (DpH := DpH) hweak qε)
    (hMeas : Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (hβ : βBarReal.HolderConjugate βBarReal')
    (hγ : γBarReal.HolderConjugate γBarReal')
    (hβTop : ENNReal.ofReal γBarReal ≠ ⊤) :
    ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
        V (Hdelta hweak ε) (DpHepsilonFam hweak qε ε)
        (fun (_ : Fin d) (_ : (Fin d → ℝ)) => (0 : ℝ))
        (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ)) := by
  classical
  intro ε hε hε1
  haveI : MeasureTheory.IsFiniteMeasure
      (MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube (d := d))) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ]; simp⟩
  -- Bridge `(fun i => (0:ℝ)) = (0 : Fin d → ℝ)` (defeq, for the constant slot).
  have hzero : (fun _ : Fin d => (0 : ℝ)) = (0 : Fin d → ℝ) := rfl
  -- The inflated AE constant `C̃_ε`.
  set Ctil : ℝ :=
    StationaryMFG.Theorems.SimplePower.coercivityCdeltaEpsUniform
      (H := H) (DpH := DpH) hweak ε with hCtil
  have hCtil_pos : 0 < Ctil :=
    StationaryMFG.Theorems.SimplePower.coercivityCdeltaEpsUniform_pos
      (H := H) (DpH := DpH) hweak hε
  -- ----- `hF_mass` : `(fun _ => 1) - 1 = 0`. -----
  have hF_mass :
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (StationaryMFG.Theorems.SimplePower.Banach.F_mass
          (fun _ : (Fin d → ℝ) => (1 : ℝ))) := by
    have heq : StationaryMFG.Theorems.SimplePower.Banach.F_mass
          (fun _ : (Fin d → ℝ) => (1 : ℝ))
        = (fun _ : (Fin d → ℝ) => (0 : ℝ)) := by
      funext x; simp [StationaryMFG.Theorems.SimplePower.Banach.F_mass]
    rw [heq]; exact MemLpPer.const (0 : ℝ)
  -- ----- `hG_grad i` : `vecAbsPowMinusTwo γBar 0 * 0 = 0`. -----
  have hG_grad : ∀ i,
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (StationaryMFG.Theorems.SimplePower.Banach.G_grad γBarReal
          (fun (_ : Fin d) (_ : (Fin d → ℝ)) => (0 : ℝ)) i) := by
    intro i
    have heq : StationaryMFG.Theorems.SimplePower.Banach.G_grad γBarReal
          (fun (_ : Fin d) (_ : (Fin d → ℝ)) => (0 : ℝ)) i
        = (fun _ : (Fin d → ℝ) => (0 : ℝ)) := by
      funext x; simp [StationaryMFG.Theorems.SimplePower.Banach.G_grad]
    rw [heq]; exact MemLpPer.const (0 : ℝ)
  -- ----- `hG_val` : `absPowMinusTwo γBar 0 * 0 = 0`. -----
  have hG_val :
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (StationaryMFG.Theorems.SimplePower.Banach.G_val γBarReal
          (fun _ : (Fin d → ℝ) => (0 : ℝ))) := by
    have heq : StationaryMFG.Theorems.SimplePower.Banach.G_val γBarReal
          (fun _ : (Fin d → ℝ) => (0 : ℝ))
        = (fun _ : (Fin d → ℝ) => (0 : ℝ)) := by
      funext x; simp [StationaryMFG.Theorems.SimplePower.Banach.G_val]
    rw [heq]; exact MemLpPer.const (0 : ℝ)
  -- ----- `hF_flux i` : `1 · DpH(x,0,1)_i`, dominated by `C̃_ε`. -----
  -- Measurability of the constant-slot flux composite.
  have hDpH_meas : Measurable
      (fun x : Fin d → ℝ => DpHepsilonFam hweak qε ε x (0 : Fin d → ℝ) (1 : ℝ)) := by
    have hglob := StationaryMFG.InfimalConvolution.measurable_DpHepsilonFam_of_selector
      hweak qε sel hMeas ε
    exact hglob.comp (measurable_id.prodMk
      (measurable_const.prodMk measurable_const))
  have hF_flux : ∀ i,
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (StationaryMFG.Theorems.SimplePower.Banach.F_flux
          (DpHepsilonFam hweak qε ε)
          (fun (_ : Fin d) (_ : (Fin d → ℝ)) => (0 : ℝ))
          (fun _ : (Fin d → ℝ) => (1 : ℝ)) i) := by
    intro i
    have hdom : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun _ : (Fin d → ℝ) => Ctil) := MemLpPer.const Ctil
    have hmeas : MeasureTheory.AEStronglyMeasurable
        (StationaryMFG.Theorems.SimplePower.Banach.F_flux
          (DpHepsilonFam hweak qε ε)
          (fun (_ : Fin d) (_ : (Fin d → ℝ)) => (0 : ℝ))
          (fun _ : (Fin d → ℝ) => (1 : ℝ)) i)
        (MeasureTheory.volume.restrict (UnitCube d)) := by
      have hrw : (StationaryMFG.Theorems.SimplePower.Banach.F_flux
          (DpHepsilonFam hweak qε ε)
          (fun (_ : Fin d) (_ : (Fin d → ℝ)) => (0 : ℝ))
          (fun _ : (Fin d → ℝ) => (1 : ℝ)) i)
          = fun x => (1 : ℝ) *
              DpHepsilonFam hweak qε ε x (0 : Fin d → ℝ) (1 : ℝ) i := by
        funext x
        change (1 : ℝ) * DpHepsilonFam hweak qε ε x (fun _ : Fin d => (0:ℝ)) 1 i
            = (1 : ℝ) * DpHepsilonFam hweak qε ε x (0 : Fin d → ℝ) (1 : ℝ) i
        rw [hzero]
      rw [hrw]
      exact ((measurable_const.mul
        ((measurable_pi_apply i).comp hDpH_meas)).aestronglyMeasurable)
    have hbound : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ‖StationaryMFG.Theorems.SimplePower.Banach.F_flux
            (DpHepsilonFam hweak qε ε)
            (fun (_ : Fin d) (_ : (Fin d → ℝ)) => (0 : ℝ))
            (fun _ : (Fin d → ℝ) => (1 : ℝ)) i x‖
          ≤ (1 : ℝ) * ‖(fun _ : (Fin d → ℝ) => Ctil) x‖ := by
      filter_upwards
        [StationaryMFG.Theorems.SimplePower.aeData_DpH01_le_at_uniform
          hAE hε hε1] with x hx
      have hxC : ‖DpHepsilonFam hweak qε ε x (0 : Fin d → ℝ) (1 : ℝ)‖ ≤ Ctil := by
        rw [hCtil]; exact hx
      have hval : StationaryMFG.Theorems.SimplePower.Banach.F_flux
            (DpHepsilonFam hweak qε ε)
            (fun (_ : Fin d) (_ : (Fin d → ℝ)) => (0 : ℝ))
            (fun _ : (Fin d → ℝ) => (1 : ℝ)) i x
          = DpHepsilonFam hweak qε ε x (0 : Fin d → ℝ) (1 : ℝ) i := by
        change (1 : ℝ) * DpHepsilonFam hweak qε ε x (fun _ : Fin d => (0:ℝ)) 1 i
            = DpHepsilonFam hweak qε ε x (0 : Fin d → ℝ) (1 : ℝ) i
        rw [hzero, one_mul]
      rw [hval, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hCtil_pos, one_mul]
      calc |DpHepsilonFam hweak qε ε x (0 : Fin d → ℝ) (1 : ℝ) i|
          ≤ ‖DpHepsilonFam hweak qε ε x (0 : Fin d → ℝ) (1 : ℝ)‖ := by
            rw [← Real.norm_eq_abs]; exact norm_le_pi_norm _ i
        _ ≤ Ctil := hxC
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.of_le_mul hdom.toMemLp hmeas hbound)
  -- ----- `hF_HJB` : `-(0) - Hdelta(x,0,1) + V x`. -----
  -- Constant-slot HJB measurability: via `HdeltaPos` at `(0,1)`, congr to `Hdelta`.
  have hHdelta01_aem : AEMeasurable
      (fun x : Fin d → ℝ => Hdelta hweak ε x (0 : Fin d → ℝ) (1 : ℝ))
      (MeasureTheory.volume.restrict (UnitCube d)) := by
    have hPos := StationaryMFG.InfimalConvolution.aemeasurable_HdeltaPos_comp_of_selector
      hweak hMeas qε sel hε
      (Du := fun _ : Fin d → ℝ => (0 : Fin d → ℝ))
      (m := fun _ : Fin d → ℝ => (1 : ℝ))
      measurable_const.aemeasurable measurable_const.aemeasurable
    refine hPos.congr ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    exact HdeltaPos_eq_Hdelta_of_pos hweak one_pos
  have hF_HJB :
      MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (StationaryMFG.Theorems.SimplePower.Banach.F_HJB
          V (Hdelta hweak ε)
          (fun (_ : Fin d) (_ : (Fin d → ℝ)) => (0 : ℝ))
          (fun _ : (Fin d → ℝ) => (1 : ℝ)) (fun _ : (Fin d → ℝ) => (0 : ℝ))) := by
    have hdom : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x : (Fin d → ℝ) => Ctil + ‖V x‖) :=
      (MemLpPer.const Ctil).add (MemLp.toMemLpPer (MeasureTheory.MemLp.norm hV.toMemLp))
    -- Canonical-slot rewrite for the `F_HJB` constant triple.
    have hFeq : (StationaryMFG.Theorems.SimplePower.Banach.F_HJB
        V (Hdelta hweak ε)
        (fun (_ : Fin d) (_ : (Fin d → ℝ)) => (0 : ℝ))
        (fun _ : (Fin d → ℝ) => (1 : ℝ)) (fun _ : (Fin d → ℝ) => (0 : ℝ)))
        = fun x => -(0 : ℝ)
            - Hdelta hweak ε x (0 : Fin d → ℝ) (1 : ℝ) + V x := by
      funext x
      change -(0 : ℝ) - Hdelta hweak ε x (fun _ : Fin d => (0:ℝ)) 1 + V x
          = -(0 : ℝ) - Hdelta hweak ε x (0 : Fin d → ℝ) (1 : ℝ) + V x
      rw [hzero]
    have hmeas : MeasureTheory.AEStronglyMeasurable
        (StationaryMFG.Theorems.SimplePower.Banach.F_HJB
          V (Hdelta hweak ε)
          (fun (_ : Fin d) (_ : (Fin d → ℝ)) => (0 : ℝ))
          (fun _ : (Fin d → ℝ) => (1 : ℝ)) (fun _ : (Fin d → ℝ) => (0 : ℝ)))
        (MeasureTheory.volume.restrict (UnitCube d)) := by
      rw [hFeq]
      have hVaem : AEMeasurable V
          (MeasureTheory.volume.restrict (UnitCube d)) := hV.aestronglyMeasurable.aemeasurable
      exact ((aemeasurable_const.sub hHdelta01_aem).add hVaem).aestronglyMeasurable
    have hbound : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ‖StationaryMFG.Theorems.SimplePower.Banach.F_HJB
            V (Hdelta hweak ε)
            (fun (_ : Fin d) (_ : (Fin d → ℝ)) => (0 : ℝ))
            (fun _ : (Fin d → ℝ) => (1 : ℝ))
            (fun _ : (Fin d → ℝ) => (0 : ℝ)) x‖
          ≤ (1 : ℝ) * ‖(fun x : (Fin d → ℝ) => Ctil + ‖V x‖) x‖ := by
      filter_upwards
        [StationaryMFG.Theorems.SimplePower.aeData_H01_le_at_uniform
          hAE hε hε1] with x hx
      have hval : StationaryMFG.Theorems.SimplePower.Banach.F_HJB
            V (Hdelta hweak ε)
            (fun (_ : Fin d) (_ : (Fin d → ℝ)) => (0 : ℝ))
            (fun _ : (Fin d → ℝ) => (1 : ℝ))
            (fun _ : (Fin d → ℝ) => (0 : ℝ)) x
          = -Hdelta hweak ε x (0 : Fin d → ℝ) (1 : ℝ) + V x := by
        change -(0 : ℝ) - Hdelta hweak ε x (fun _ : Fin d => (0:ℝ)) 1 + V x
            = -Hdelta hweak ε x (0 : Fin d → ℝ) (1 : ℝ) + V x
        rw [hzero]; ring
      have hHbnd : |Hdelta hweak ε x (0 : Fin d → ℝ) (1 : ℝ)| ≤ Ctil := by
        rw [hCtil]; exact hx
      have hG_nn : 0 ≤ Ctil + ‖V x‖ := by positivity
      rw [hval, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hG_nn, one_mul]
      have htri : |(-Hdelta hweak ε x (0 : Fin d → ℝ) (1 : ℝ)) + V x|
          ≤ |Hdelta hweak ε x (0 : Fin d → ℝ) (1 : ℝ)| + |V x| := by
        calc |(-Hdelta hweak ε x (0 : Fin d → ℝ) (1 : ℝ)) + V x|
            ≤ |-Hdelta hweak ε x (0 : Fin d → ℝ) (1 : ℝ)| + |V x| := abs_add_le _ _
          _ = |Hdelta hweak ε x (0 : Fin d → ℝ) (1 : ℝ)| + |V x| := by rw [abs_neg]
      have hVabs : |V x| = ‖V x‖ := (Real.norm_eq_abs _).symm
      rw [hVabs] at htri
      linarith [htri, hHbnd]
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.of_le_mul hdom.toMemLp hmeas hbound)
  -- ----- Assemble the record. -----
  exact
    { hβ := hβ
      hγ := hγ
      hF_HJB := hF_HJB
      hF_flux := hF_flux
      hF_mass := hF_mass
      hG_grad := hG_grad
      hG_val := hG_val
      hβTop := hβTop }

end InfimalConvolution

end StationaryMFG
