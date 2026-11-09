module

/-
Copyright (c) 2026 Stationary MFG project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import StationaryMFG.Theorems.SimplePower.Regularized
public import StationaryMFG.Theorems.SimplePower.BanachBridge
public import StationaryMFG.Theorems.InfimalConvolution.Aepsilon
public import StationaryMFG.Theorems.InfimalConvolution.Monotone
public import StationaryMFG.Theorems.InfimalConvolution.BanachBridge

@[expose] public section

/-!
# Existence of a strong VI solution for `A_ε^δ` (paper `thm:strongAepsi.delta`)

This module formalizes Proposition `thm:strongAepsi.delta` of
Ferreira–Gomes–Üçer (`Source/FGU-monotone_revised.tex`, line 1838):

> Under the assumptions of Theorem `thm:main-weak.power.growth`, for
> `0 < ε ≤ 1`, let `A_ε` be the regularized MFG operator
> `eq:defAepsi.delta` (built from `H^ε := Hdelta H ε`). Then there
> exists `(m_ε, u_ε) ∈ L^{β̄}_per(𝕋^d; ℝ⁺_0) × W^{1,γ̄}_per(𝕋^d)`
> such that, for every `(μ, υ) ∈ L^{β̄}_per(𝕋^d; ℝ⁺_0) × W^{1,γ̄}_per(𝕋^d)`,
> `⟨A_ε[m_ε, u_ε], (μ, υ) - (m_ε, u_ε)⟩ ≥ 0`.

## Paper proof outline (lines 1843–1854)

The paper says explicitly: "We follow the same lines of the proofs of
Propositions `thm:strongAepsi` (paper line 1046) and
`thm:weakAepsi.congestion` (paper line 1363)", with the three
substitutions:

1. **Monotonicity** of `A_ε^δ` comes from
   Lemma `lem:H.delta.monotone` (paper line 1754, formalized as
   `StationaryMFG.InfimalConvolution.Hdelta_monotone` in module
   `Theorems/InfimalConvolution/Monotone.lean`), playing the role of
   Assumption `onH.monotone` in the unregularized argument.

2. **Coercivity** of `A_ε^δ` is the same calculation as
   Proposition `prop:coercAepsi` (paper line 856), with the two
   uniform-in-ε estimates `eq:DpHdotpminusH-estimate1` (lower
   Lagrangian) and `eq:assH.lower.simple` (lower Hamiltonian bound)
   replaced by `eq:DpHdelta.dotp.minusH` (paper
   `prop:boundsHepsilon.d`) and `eq:H-epsilon.lower.uniform` (paper
   `prop:boundsHepsilon.c`) respectively.

3. **Hemicontinuity** of `A_ε^δ` is proved as in
   Lemma `paper:lem:hemicont` (paper line 1129), with `H ↦ Hdelta H ε`
   and `D_pH ↦ DpHε`.

The abstract Browder–Minty machinery
(`paper:thm:monotone.abstract-weak`, formalized in
`StationaryMFG.Monotone.AbstractWeak`) plus the hemicontinuous upgrade
(`paper:rmk:hemicontinuous-upgrade`, formalized in
`StationaryMFG.Monotone.HemicontUpgrade`) then produce the strong VI
conclusion, exactly as for paper `thm:strongAepsi`.

## CONVENTIONS §8 statement-first split

Per `docs/CONVENTIONS.md` §8, the *statement* of
`paper:thm:strongAepsi.delta` lands now in **bridge-parameterised**
form, mirroring the already-landed sibling
`Theorems.SimplePower.Regularized.thm_strongAepsi` (paper
`thm:strongAepsi`) and `Theorems.Congestion.Existence.weak_Aeps_congestion_exists`
(paper `thm:weakAepsi.congestion`). The four abstract Phase-4 inputs —
monotonicity, hemicontinuity, coercivity, and convexity+closedness of
`K` — are quantified universally over a Banach realisation `(X, K, A)`
of the bare-function pair `(𝓚, A_ε^δ)`. The concrete
`Periodic.Lp`-quotient bridge from the bare-function pair to
`(X, K, A)` is deferred to a follow-up infra task and is identical in
shape to the open bridge for `thm:strongAepsi`.

## Deliverables

* `exists_strong_solution_Aepsi_delta` (the headline theorem,
  paper-named alias `thm_strongAepsi_delta`) — the bridge-parameterised
  existence theorem; one-line invocation of
  `Theorems.SimplePower.Regularized.strongVI_Aepsi`.

## Paper reference

`Source/FGU-monotone_revised.tex`, line 1838, Proposition
`thm:strongAepsi.delta`.
-/

noncomputable section

namespace StationaryMFG
namespace Theorems
namespace InfimalConvolution

open StationaryMFG.Periodic
open StationaryMFG.Theorems.SimplePower
open StationaryMFG.Solutions.MFG
open MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-! ## Bare-function strong VI for `A_ε^δ` (paper `eq:Aepsistrongineq` at `A_ε^δ`)

`IsStrongVI_Aepsi V H DpH ε m u Du` is the bare-function form of the
strong variational inequality `eq:Aepsistrongineq` evaluated at the
regularised operator `A_ε^δ` (paper `eq:defAepsi.delta`). It records that
the regularised MFG pairing of `A_ε^δ[m, u]` against every admissible
test pair `(μ, υ)` with weak-gradient family `Dυ` is non-negative:
```
⟨A_ε^δ[m, u], (μ, υ) − (m, u)⟩ ≥ 0,    for all admissible (μ, υ).
```
A test triple `(μ, υ, Dυ)` is admissible when `μ ≥ 0` a.e. on the torus,
`μ ∈ L^{β̄}_per`, `υ ∈ W^{1,γ̄}_per` with `L^{γ̄}_per`-integrable
weak-gradient family `Dυ` (so the regularised pairing's flux and
`ε`-Laplacian terms make sense), matching the paper's admissible set
`𝓚 = L^{β̄}_per(𝕋^d; ℝ⁺₀) × W^{1,γ̄}_per(𝕋^d)`.

This is the function-form analog requested by the A1d task spec; it is
formula-package-independent (it takes the already-substituted regularised
Hamiltonian `H` and gradient `DpH` as plain arguments — at the A1d call
site these are `Hdelta hweak ε` and `DpHepsilon hweak qE`). -/
def IsStrongVI_Aepsi
    (bb gb : ℝ≥0∞)
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (γBar ε : ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ) : Prop :=
  ∀ (μ υ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ),
    (∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ μ x) →
    Periodic.MemLpPer bb μ →
    Periodic.MemSobolevPer gb υ →
    (∀ i, Periodic.MemLpPer gb (Dυ i)) →
    (∀ i, Periodic.HasWeakDerivPer i υ (Dυ i)) →
    0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH) γBar ε
          Dυ μ υ
          (fun i x => Dυ i x - Du i x)
          (fun x => μ x - m x) (fun x => υ x - u x)

/-- **Bridge-parameterised assembly of the bare `A_ε^δ` strong solution**
(A1d assembly step, paper `thm:strongAepsi.delta`).

Given a bare-function triple `(m, u, Du)` with `m ∈ L^{β̄}_per`,
`u ∈ W^{1,γ̄}_per` (witnessed via its `L^{γ̄}_per`-integrable weak
gradient `Du`), and the bare-function strong-VI inequality
`IsStrongVI_Aepsi` for the *already-substituted* regularised operator
`A_ε^δ`, package the acceptance-shaped existential.

This is the formula-package-independent half of A1d: it converts the
bare-VI conclusion delivered by the descended Browder–Minty witness
(`exists_banachVI_at_eps_KAepsi`, descended to `K0_Aepsi` via
`K_Aepsi_closure_subset_K0_Aepsi`, then projected to bare functions by
`exists_regularizedBareSolution_K`) into the `(m, u, Du)`-existential of
the task acceptance. The paper-hypotheses-to-bridge wiring that produces
the `IsStrongVI_Aepsi` input from `(hmon, hweak)` for the substituted
pair `(Hdelta hweak ε, DpHepsilon hweak qE)` is the inf-conv
formula-package step (D2-gated; split off as a child task). -/
theorem strongAepsi_delta_bare_of
    {bb gb : ℝ≥0∞}
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (γBar ε : ℝ)
    {m u : (Fin d → ℝ) → ℝ} {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hmLp : Periodic.MemLpPer bb m)
    (huSob : Periodic.MemSobolevPer gb u)
    (hVI : IsStrongVI_Aepsi bb gb V H DpH γBar ε m u Du) :
    ∃ (m' u' : (Fin d → ℝ) → ℝ) (Du' : Fin d → (Fin d → ℝ) → ℝ),
      Periodic.MemLpPer bb m' ∧ Periodic.MemSobolevPer gb u' ∧
      IsStrongVI_Aepsi bb gb V H DpH γBar ε m' u' Du' :=
  ⟨m, u, Du, hmLp, huSob, hVI⟩

/-! ## From the Browder–Minty bare output to the bare strong VI

The genuine Browder–Minty witness for the regularised operator `A_ε^δ`,
descended to `K0_Aepsi` and projected to bare functions, is packaged as a
`StationaryMFG.Theorems.SimplePower.Banach.RegularizedBareSolution`
record (produced by `exists_regularizedBareSolution_K`). Its `hVIeps_set`
field is the **set-form** regularised VI: for every measurable `S` and
nonnegative test density `ρ` (with the `MemLpPer` / `MemSobolevPer`
test-triple certificates), the regularised pairing against the
indicator-modulated test triple `(Dυ, S.indicator ρ, υ)` is non-negative.

Specialising at `S = Set.univ` and `ρ = μ` (so `Set.univ.indicator μ = μ`
by `Set.indicator_univ`) collapses the indicator and yields exactly the
generic-density bare strong VI `IsStrongVI_Aepsi`. This is the
formula-package-independent step 4 of the A1d route
(`exists_regularizedBareSolution_K` → bare `IsStrongVI_Aepsi`); it is a
genuine drain (it converts the set-form VI into the generic-`μ` VI
predicate consumed by `strongAepsi_delta_bare_of`), independent of the
substituted-cert assembly (the deferred design-fork child). -/

open StationaryMFG.Theorems.SimplePower.Banach in
/-- **Bare strong VI `IsStrongVI_Aepsi` from a `RegularizedBareSolution`.**

From the genuine Browder–Minty bare output `sol` for the regularised
operator `A_ε^δ` (the `(m, u, Du)` triple plus the set-form VI
`sol.hVIeps_set`), produce the generic-density bare strong VI
`IsStrongVI_Aepsi` at `(sol.m, sol.u, sol.Du)`. The proof specialises
`sol.hVIeps_set` at `S = Set.univ`, `ρ = μ`, where `Set.univ.indicator μ`
reduces to `μ` (`Set.indicator_univ`), so the indicator-modulated VI
becomes the generic-`μ` VI predicate. -/
theorem isStrongVI_Aepsi_of_regularizedBareSolution
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal') :
    IsStrongVI_Aepsi (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
      V H DpH γBarReal ε sol.m sol.u sol.Du := by
  intro μ υ Dυ hμ_nonneg hμ_Lp hυ_Sob hDυ_Lp hDυ_weak
  -- Specialise the set-form VI at `S = Set.univ`, `ρ = μ`.
  have hIndic : Set.univ.indicator μ = μ := Set.indicator_univ μ
  have h :=
    sol.hVIeps_set Set.univ MeasurableSet.univ μ υ Dυ
      (by simpa [hIndic] using hμ_nonneg)
      (by simpa [hIndic] using hμ_Lp)
      hυ_Sob hDυ_Lp hDυ_weak
  simpa only [hIndic, Pi.sub_def] using h

/-! ## Headline theorem -/

/-- **Existence of a strong VI solution for `A_ε^δ`** (paper
`thm:strongAepsi.delta`, line 1838).

*Bridge-parameterised aggregator.* Under the assumptions of the
weak-growth main theorem `paper:thm:main-weak.power.growth` plus the
four abstract Phase-4 inputs at the Banach realisation `(X, K, A)` of
the bare-function pair `(𝓚, A_ε^δ)`:

* `hA_mono` — monotonicity of `A` on `K` (bridged
  `paper:lem:H.delta.monotone`).
* `hA_hemicont` — hemicontinuity of `A` on `K` (bridged
  `paper:lem:hemicont` with `H ↦ Hdelta H ε`).
* `hA_coerc` — coercivity of `A` on `K` at some `v₀` (bridged
  `paper:prop:coercAepsi` with the `prop:boundsHepsilon.{c,d}`
  substitutions).
* `hK_cvx`, `hK_closed` — convexity and closedness of `K`
  (bridged `𝓚 is convex and closed`).

plus reflexivity of `X` (`Periodic.IsReflexiveNormedSpace X`) and the
`FiniteConvexHullWeakVI` typeclass (the Browder–Minty input from
`paper:thm:monotone.abstract-weak`), there exists `u ∈ K` such that
`∀ v ∈ K, 0 ≤ A u (v - u)`.

Once `(X, K, A)` is bridged to `(L^{β̄}_per × W^{1,γ̄}_per, 𝓚, A_ε^δ)`,
this is exactly paper `eq:Aepsistrongineq` at `A_ε^δ`:
```
⟨A_ε^δ[m_ε, u_ε], (μ, υ) - (m_ε, u_ε)⟩ ≥ 0,    for all (μ, υ) ∈ 𝓚.
```

The proof is a one-line invocation of
`StationaryMFG.Theorems.SimplePower.strongVI_Aepsi`, which itself
chains `monotone_abstract_weak` (Browder–Minty,
`paper:thm:monotone.abstract-weak`) with the closure-lift and the
hemicontinuous upgrade (`paper:rmk:hemicontinuous-upgrade`). The
`Hdelta`-specific content is entirely confined to the bridge
hypotheses, exactly as in the paper proof at line 1843. -/
theorem exists_strong_solution_Aepsi_delta
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [Monotone.FiniteConvexHullWeakVI X]
    (hX : Periodic.IsReflexiveNormedSpace X)
    {K : Set X} (hK_cvx : Convex ℝ K) (hK_closed : IsClosed K)
    {A : X → StrongDual ℝ X}
    (hA_mono : Monotone.IsMonotone K A)
    (hA_hemicont : Monotone.IsHemicontinuous K A)
    {v₀ : X} (hA_coerc : Monotone.IsCoerciveAt K A v₀) :
    ∃ u ∈ K, ∀ v ∈ K, 0 ≤ A u (v - u) :=
  strongVI_Aepsi (X := X) hX hK_cvx hK_closed
    (A := A) hA_mono hA_hemicont (v₀ := v₀) hA_coerc

/-- **Paper-named alias** for `exists_strong_solution_Aepsi_delta`
matching the proposition label `thm:strongAepsi.delta`. Same
bridge-parameterised signature; same conclusion. -/
theorem thm_strongAepsi_delta
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [Monotone.FiniteConvexHullWeakVI X]
    (hX : Periodic.IsReflexiveNormedSpace X)
    {K : Set X} (hK_cvx : Convex ℝ K) (hK_closed : IsClosed K)
    {A : X → StrongDual ℝ X}
    (hA_mono : Monotone.IsMonotone K A)
    (hA_hemicont : Monotone.IsHemicontinuous K A)
    {v₀ : X} (hA_coerc : Monotone.IsCoerciveAt K A v₀) :
    ∃ u ∈ K, ∀ v ∈ K, 0 ≤ A u (v - u) :=
  exists_strong_solution_Aepsi_delta hX hK_cvx hK_closed
    hA_mono hA_hemicont hA_coerc

/-! ## A1d-final step 8c: substituted-pair `hMinty_*` δ-limit families
(paper `thm:strongAepsi.delta`)

The FIVE standalone helper lemmas that produce, at a FIXED `ε > 0` and a
per-`ε` substituted-pair `AepsiUniformContextK`, exactly the per-`ε` slice
`hMinty_* ε hε` consumed by `strongAepsi_deltaK0_family_of_selectorData_ae`
(below), at the substituted regularised pair
`(Hdelta hweak ε, DpHepsilon hweak qE)` with exponents **pinned to the paper
values** (`βBarReal := hpowEps.β + 1`,
`γBarReal := hpowEps.α*(hpowEps.β+1)/hpowEps.β`,
`βBarReal' := (hpowEps.β+1)/hpowEps.β`, `γBarReal' := γBarReal/(γBarReal-1)`).

* The set/signed/transport helpers delegate to the generic, ε-generic,
  Hext-free `_of_rc0` producers
  `paperSection8_hMinty_{set,signed,transport}_of_paperHypotheses_of_rc0`
  (steps 8/8b, SimplePower/BanachBridge), feeding the per-query residue via
  `{set,signed,transport}TendstoResidueOf_of_paperHypotheses` instantiated at
  the substituted pair.
* The probe/triple helpers replicate the bodies of
  `paperSection8_hMinty_signed_user_{probe,triple}_of_paperHypotheses_of_rc0`
  inline at the generic `ε` (those producers are pinned at `paperEpsSeq k`):
  the VI consumer `hVIeps_signed_user_{probe,triple}_of_KAepsi_VI` composed
  with the Hext-free continuity producer
  `signedUser{Probe,Triple}Cont_of_paperHypotheses_of_aestronglyMeasurable_of_rc0`.

Riders (all paper-faithful, no Hext / no `0<m` / no `hMeasNeg`): `hpowEps`
(substituted-pair power growth), `hRegH` (substituted-pair `RegularityH`),
`hH_rc0` (right-continuity of `Hdelta hweak ε` at `m=0⁺`), and `hV_memLp`
(`V ∈ L^{(β+1)/β}_per`, needed by the residue / continuity producers). -/

open StationaryMFG.Theorems.SimplePower.Banach in
/-- **Substituted-pair `hMinty_set` δ-limit slice** (paper
`thm:strongAepsi.delta`). Per-`ε` slice of the `hMinty_set` family at
`(Hdelta hweak ε, DpHepsilon hweak qE)`, pinned exponents. -/
theorem hMinty_set_substitutedPair_of_paperHypotheses_of_rc0
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {ε : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    (hweak : StationaryMFG.Hamiltonian.HypothesisWeakGrowth (d := d) H DpH)
    (qE : (Fin d → ℝ) × (Fin d → ℝ) × ℝ → (Fin d → ℝ))
    (hpowEps : StationaryMFG.Hamiltonian.HypothesisPowerGrowth (d := d)
                (StationaryMFG.InfimalConvolution.Hdelta hweak ε)
                (StationaryMFG.InfimalConvolution.DpHepsilon hweak qE))
    (hRegH : StationaryMFG.Hamiltonian.RegularityH (d := d)
                (StationaryMFG.InfimalConvolution.Hdelta hweak ε)
                (StationaryMFG.InfimalConvolution.DpHepsilon hweak qE))
    (hH_rc0 :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ∀ p : Fin d → ℝ,
          Filter.Tendsto
            (fun m : ℝ => StationaryMFG.InfimalConvolution.Hdelta hweak ε x p m)
            (nhdsWithin (0 : ℝ) (Set.Ioi 0))
            (nhds (StationaryMFG.InfimalConvolution.Hdelta hweak ε x p 0)))
    (hV_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal ((hpowEps.β + 1) / hpowEps.β)) V)
    [Fact (1 ≤ ENNReal.ofReal (hpowEps.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hpowEps.α * (hpowEps.β + 1) / hpowEps.β))]
    (ctx : AepsiUniformContextK (d := d) ε V
              (StationaryMFG.InfimalConvolution.Hdelta hweak ε)
              (StationaryMFG.InfimalConvolution.DpHepsilon hweak qE)
              (hpowEps.α * (hpowEps.β + 1) / hpowEps.β)
              (hpowEps.β + 1)
              ((hpowEps.β + 1) / hpowEps.β)
              ((hpowEps.α * (hpowEps.β + 1) / hpowEps.β)
                / (hpowEps.α * (hpowEps.β + 1) / hpowEps.β - 1)))
    (q : XBanach d (hpowEps.β + 1)
            (hpowEps.α * (hpowEps.β + 1) / hpowEps.β)) :
      q ∈ K0_Aepsi d (hpowEps.β + 1)
              (hpowEps.α * (hpowEps.β + 1) / hpowEps.β) →
      (∀ q' ∈ K_Aepsi d (hpowEps.β + 1)
                (hpowEps.α * (hpowEps.β + 1) / hpowEps.β),
          0 ≤ Aepsi_CLM_opK
                (γBarReal := hpowEps.α * (hpowEps.β + 1) / hpowEps.β)
                (βBarReal := hpowEps.β + 1)
                (βBarReal' := (hpowEps.β + 1) / hpowEps.β)
                (γBarReal' := (hpowEps.α * (hpowEps.β + 1) / hpowEps.β)
                                / (hpowEps.α * (hpowEps.β + 1) / hpowEps.β - 1))
                V (StationaryMFG.InfimalConvolution.Hdelta hweak ε)
                (StationaryMFG.InfimalConvolution.DpHepsilon hweak qE)
                ctx.auxHypsK ε q' (q' - q)) →
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
      ∀ (ρ υ : (Fin d → ℝ) → ℝ)
        (Dυ : Fin d → (Fin d → ℝ) → ℝ),
        (∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
            0 ≤ ρ x) →
        Periodic.MemLpPer (d := d)
          (ENNReal.ofReal (hpowEps.β + 1)) (S.indicator ρ) →
        Periodic.MemSobolevPer (d := d)
          (ENNReal.ofReal (hpowEps.α * (hpowEps.β + 1) / hpowEps.β)) υ →
        (∀ i, Periodic.MemLpPer (d := d)
                (ENNReal.ofReal (hpowEps.α * (hpowEps.β + 1) / hpowEps.β))
                (Dυ i)) →
        (∀ i, Periodic.HasWeakDerivPer (d := d) i υ (Dυ i)) →
          0 ≤ mfgOperatorEpsPair (V := V)
                (H := StationaryMFG.InfimalConvolution.Hdelta hweak ε)
                (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak qE)
                (hpowEps.α * (hpowEps.β + 1) / hpowEps.β) ε
                Dυ (S.indicator ρ) υ
                (fun i x => Dυ i x - DuOf q i x)
                (S.indicator ρ - mOf q)
                (υ - uOf q) :=
  StationaryMFG.Theorems.SimplePower.paperSection8_hMinty_set_of_paperHypotheses_of_rc0
    (V := V) (H := StationaryMFG.InfimalConvolution.Hdelta hweak ε)
    (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak qE)
    hpowEps hRegH hH_rc0 (ε := ε)
    (fun q hq_K0 S hS ρ υ Dυ hρ_nn hSρ_memLp hυ_memSob hDυ_memLp =>
      StationaryMFG.Theorems.SimplePower.setTendstoResidueOf_of_paperHypotheses
        (V := V) (H := StationaryMFG.InfimalConvolution.Hdelta hweak ε)
        (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak qE)
        hpowEps q S hS ρ υ Dυ
        hυ_memSob.1.aestronglyMeasurable
        (fun i => (hDυ_memLp i).aestronglyMeasurable)
        hSρ_memLp hυ_memSob.1 hDυ_memLp hV_memLp hρ_nn)
    ctx q

open StationaryMFG.Theorems.SimplePower.Banach in
/-- **Substituted-pair `hMinty_set` δ-limit slice, re-keyed on the closed-cone
carrier `HdeltaK0`** (paper `thm:strongAepsi.delta`, D2b-1c-ii-c4c-set).

Additive `HdeltaK0`-keyed variant of
`hMinty_set_substitutedPair_of_paperHypotheses_of_rc0`. The conclusion is
keyed on `mfgOperatorEpsPair (H := HdeltaK0 hweak ε)`; the strict entry above
(on `Hdelta`) is left intact for its existing caller. This variant carries NO
loose `RegularityH (Hdelta …)` / `HypothesisHat0 (Hdelta …)` / raw-H `hH_rc0`
binder: the H-side data is supplied INTERNALLY at `H := HdeltaK0` from
* `HdeltaK0_continuousOn_H_pm_of_selectorFamily` (continuity on `{0<m}`
  from the selector-family data),
* `HdeltaK0_rc0_of_selectorFamily` (boundary right-continuity from the
  selector family),
* `aemeasurable_HdeltaK0_comp_of_rc0` (the two H AE composites per residue
  bundle),
and the bare residue supplier
`setTendstoResidueOfBare_of_paperHypotheses_of_aeMeasH` reuses the strict
`HdeltaPos`-keyed dominators (which agree with `HdeltaK0` on the positive
per-`n` slot). The GATE-permitted riders are `hMeas`/`hmonBoundary`/`hdiffBoundary`
(used by the composite/rc0 lemmas) and the `RegularityH (HdeltaPos)`-class
supply `hpowEps` (NOT the forbidden `RegularityH (Hdelta)`). -/
theorem hMinty_set_substitutedPair_of_paperHypotheses_of_rc0_HdeltaK0
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {ε : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    (hweak : StationaryMFG.Hamiltonian.HypothesisWeakGrowth (d := d) H DpH)
    (hε : 0 < ε)
    (qε : StationaryMFG.InfimalConvolution.QEpsFamily d)
    (sel : StationaryMFG.InfimalConvolution.InfConvSelectorFamily
              (H := H) (DpH := DpH) hweak qε)
    (hMeas : StationaryMFG.Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (hmonBoundary : StationaryMFG.Hamiltonian.HypothesisMonotone (d := d) H DpH)
    (hdiffBoundary : StationaryMFG.Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    (hpowEps : StationaryMFG.Hamiltonian.HypothesisPowerGrowth (d := d)
                (StationaryMFG.InfimalConvolution.HdeltaPos hweak ε)
                (StationaryMFG.InfimalConvolution.DpHepsilonFam hweak qε ε))
    (hV_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal ((hpowEps.β + 1) / hpowEps.β)) V)
    [Fact (1 ≤ ENNReal.ofReal (hpowEps.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hpowEps.α * (hpowEps.β + 1) / hpowEps.β))]
    (ctx : AepsiUniformContextK (d := d) ε V
              (StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
              (StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
              (hpowEps.α * (hpowEps.β + 1) / hpowEps.β)
              (hpowEps.β + 1)
              ((hpowEps.β + 1) / hpowEps.β)
              ((hpowEps.α * (hpowEps.β + 1) / hpowEps.β)
                / (hpowEps.α * (hpowEps.β + 1) / hpowEps.β - 1)))
    (q : XBanach d (hpowEps.β + 1)
            (hpowEps.α * (hpowEps.β + 1) / hpowEps.β)) :
      q ∈ K0_Aepsi d (hpowEps.β + 1)
              (hpowEps.α * (hpowEps.β + 1) / hpowEps.β) →
      (∀ q' ∈ K_Aepsi d (hpowEps.β + 1)
                (hpowEps.α * (hpowEps.β + 1) / hpowEps.β),
          0 ≤ Aepsi_CLM_opK
                (γBarReal := hpowEps.α * (hpowEps.β + 1) / hpowEps.β)
                (βBarReal := hpowEps.β + 1)
                (βBarReal' := (hpowEps.β + 1) / hpowEps.β)
                (γBarReal' := (hpowEps.α * (hpowEps.β + 1) / hpowEps.β)
                                / (hpowEps.α * (hpowEps.β + 1) / hpowEps.β - 1))
                V (StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
                (StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
                ctx.auxHypsK ε q' (q' - q)) →
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
      ∀ (ρ υ : (Fin d → ℝ) → ℝ)
        (Dυ : Fin d → (Fin d → ℝ) → ℝ),
        (∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
            0 ≤ ρ x) →
        Periodic.MemLpPer (d := d)
          (ENNReal.ofReal (hpowEps.β + 1)) (S.indicator ρ) →
        Periodic.MemSobolevPer (d := d)
          (ENNReal.ofReal (hpowEps.α * (hpowEps.β + 1) / hpowEps.β)) υ →
        (∀ i, Periodic.MemLpPer (d := d)
                (ENNReal.ofReal (hpowEps.α * (hpowEps.β + 1) / hpowEps.β))
                (Dυ i)) →
        (∀ i, Periodic.HasWeakDerivPer (d := d) i υ (Dυ i)) →
          0 ≤ mfgOperatorEpsPair (V := V)
                (H := StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
                (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
                (hpowEps.α * (hpowEps.β + 1) / hpowEps.β) ε
                Dυ (S.indicator ρ) υ
                (fun i x => Dυ i x - DuOf q i x)
                (S.indicator ρ - mOf q)
                (υ - uOf q) := by
  -- H-side supply at `H := HdeltaK0`, all INTERNAL (no loose `RegularityH(Hdelta)`).
  have hcont_H_pm :=
    StationaryMFG.InfimalConvolution.HdeltaK0_continuousOn_H_pm_of_selectorFamily
      (H := H) (DpH := DpH) hweak qε sel (ε := ε) hε
  have hH_rc0 :=
    StationaryMFG.InfimalConvolution.HdeltaK0_rc0_of_selectorFamily
      (H := H) (DpH := DpH) hweak hmonBoundary qε sel hε
  -- DpH-side data (carrier-independent), from `hpowEps`.
  have hDpH_meas : Measurable
      (fun (xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ) =>
        StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε)
          xpm.1 xpm.2.1 xpm.2.2) :=
    hpowEps.measurable_DpH
  have hcont_DpH_pm :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ContinuousOn (fun (pm : (Fin d → ℝ) × ℝ) =>
            StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε) x pm.1 pm.2)
          {pm | 0 < pm.2} :=
    hpowEps.continuous_DpH_pm
  have hDpH_upper :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ∀ p m, 0 < m →
          ‖StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε) x p m‖
            ≤ hpowEps.C * (‖p‖ ^ (hpowEps.α - 1)
                + m ^ (hpowEps.β - hpowEps.β / hpowEps.α) + 1) :=
    hpowEps.DpH_upper
  exact
    StationaryMFG.Theorems.SimplePower.paperSection8_hMinty_set_of_paperHypotheses_of_rc0_of_aeMeasH
      (V := V) (H := StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
      (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
      hpowEps.hα hpowEps.hβ hDpH_meas hcont_H_pm hcont_DpH_pm hDpH_upper hH_rc0
      (ε := ε)
      (fun q hq_K0 S hS ρ υ Dυ hρ_nn hSρ_memLp hυ_memSob hDυ_memLp =>
        -- The two H AE composites at `H := HdeltaK0` from
        -- `aemeasurable_HdeltaK0_comp_of_rc0`, nonneg of the slot from `hρ_nn`.
        have hSρ_nn : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
            0 ≤ S.indicator ρ x := by
          filter_upwards [hρ_nn] with x hx
          exact Set.indicator_nonneg (fun _ _ => hx) x
        StationaryMFG.Theorems.SimplePower.setTendstoResidueOfBare_of_paperHypotheses_of_aeMeasH
          (V := V)
          (H := StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
          (H' := StationaryMFG.InfimalConvolution.HdeltaPos hweak ε)
          (DpH := StationaryMFG.InfimalConvolution.DpHepsilonFam hweak qε ε)
          hpowEps q S hS ρ υ Dυ
          hυ_memSob.1.aestronglyMeasurable
          (fun i => (hDυ_memLp i).aestronglyMeasurable)
          hSρ_memLp hυ_memSob.1 hDυ_memLp hV_memLp hρ_nn
          (fun n => by
            filter_upwards [hSρ_nn] with x hx
            have hpos : 0 < S.indicator ρ x + 1 / ((n : ℝ) + 1) := by
              have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
              linarith
            exact StationaryMFG.InfimalConvolution.HdeltaK0_eq_HdeltaPos_of_pos
              hweak hpos)
          (fun n =>
            StationaryMFG.InfimalConvolution.aemeasurable_HdeltaK0_comp_of_rc0
              (H := H) (DpH := DpH) hweak hMeas hmonBoundary qε sel hε
              (Du := fun x i => Dυ i x)
              (m := fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1))
              (aemeasurable_pi_iff.mpr
                  (fun i => (hDυ_memLp i).aestronglyMeasurable.aemeasurable))
              ((hSρ_memLp.aestronglyMeasurable.aemeasurable).add aemeasurable_const)
              (by
                filter_upwards [hSρ_nn] with x hx
                have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
                linarith))
          (StationaryMFG.InfimalConvolution.aemeasurable_HdeltaK0_comp_of_rc0
            (H := H) (DpH := DpH) hweak hMeas hmonBoundary qε sel hε
            (Du := fun x i => Dυ i x)
            (m := fun x => S.indicator ρ x)
            (aemeasurable_pi_iff.mpr
                (fun i => (hDυ_memLp i).aestronglyMeasurable.aemeasurable))
            hSρ_memLp.aestronglyMeasurable.aemeasurable
            hSρ_nn))
      ctx q

open StationaryMFG.Theorems.SimplePower.Banach in
/-- **Substituted-pair `hMinty_set` δ-limit slice, re-keyed on the closed-cone
carrier `HdeltaK0`, AE/bare-exponent variant** (paper `thm:strongAepsi.delta`,
D2c-2e-2-set, EXPERT RULING #4 retype rewire).

Additive `_ae` sibling of `hMinty_set_substitutedPair_of_paperHypotheses_of_rc0_HdeltaK0`
that DROPS the strict `hpowEps : HypothesisPowerGrowth (HdeltaPos …)` entirely.
The exponent type-indices are reindexed off the AE carrier's bare exponents
`hweak.β`/`hweak.α` (instead of `hpowEps.β`/`hpowEps.α`), the constant is
`CdeltaEps hweak ε`, and the three a.e. analytic estimates are sourced from the
AE carrier `hAE : HdeltaAEPowerEpsData hweak qε` (`H_upper_pointwise_ae`/
`lower_ae`/`DpH_upper_ae`), transferred from `Hdelta` to the target carrier
`HdeltaK0` on `{0<m}` via `HdeltaK0_eq_Hdelta_of_pos`. The per-query bare residue
supplier is the child-C `_ae` sibling
`setTendstoResidueOfBare_of_paperHypotheses_of_aeMeasH_ae`.

GATE #1: NO `hpowEps`/`HypothesisPowerGrowth(HdeltaPos)`/`RegularityH(HdeltaPos)`/
`hFormPos`/`hqE_per`/`hInj`/`hSurj`/`qEofMinv`. The H-side data is supplied
INTERNALLY at `H := HdeltaK0` from `HdeltaK0_continuousOn_H_pm_of_selectorFamily`,
`HdeltaK0_rc0_of_selectorFamily`, `aemeasurable_HdeltaK0_comp_of_rc0`; the
DpH-side data from `measurable_DpHepsilonFam_of_selector`/
`continuousOn_DpHepsilonFam_of_selector`. The permitted riders are the AE carrier
`hAE` + `hMeas`/`hmonBoundary`/`hdiffBoundary`/`hweak`/`sel`. -/
theorem hMinty_set_substitutedPair_of_paperHypotheses_of_rc0_HdeltaK0_ae
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {ε : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    (hweak : StationaryMFG.Hamiltonian.HypothesisWeakGrowth (d := d) H DpH)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (qε : StationaryMFG.InfimalConvolution.QEpsFamily d)
    (sel : StationaryMFG.InfimalConvolution.InfConvSelectorFamily
              (H := H) (DpH := DpH) hweak qε)
    (hMeas : StationaryMFG.Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (hmonBoundary : StationaryMFG.Hamiltonian.HypothesisMonotone (d := d) H DpH)
    (hdiffBoundary : StationaryMFG.Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    (hAE : StationaryMFG.InfimalConvolution.HdeltaAEPowerEpsData
              (H := H) (DpH := DpH) hweak qε)
    (hV_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal ((hweak.β + 1) / hweak.β)) V)
    [Fact (1 ≤ ENNReal.ofReal (hweak.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β))]
    (ctx : AepsiUniformContextK (d := d) ε V
              (StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
              (StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
              (hweak.α * (hweak.β + 1) / hweak.β)
              (hweak.β + 1)
              ((hweak.β + 1) / hweak.β)
              ((hweak.α * (hweak.β + 1) / hweak.β)
                / (hweak.α * (hweak.β + 1) / hweak.β - 1)))
    (q : XBanach d (hweak.β + 1)
            (hweak.α * (hweak.β + 1) / hweak.β)) :
      q ∈ K0_Aepsi d (hweak.β + 1)
              (hweak.α * (hweak.β + 1) / hweak.β) →
      (∀ q' ∈ K_Aepsi d (hweak.β + 1)
                (hweak.α * (hweak.β + 1) / hweak.β),
          0 ≤ Aepsi_CLM_opK
                (γBarReal := hweak.α * (hweak.β + 1) / hweak.β)
                (βBarReal := hweak.β + 1)
                (βBarReal' := (hweak.β + 1) / hweak.β)
                (γBarReal' := (hweak.α * (hweak.β + 1) / hweak.β)
                                / (hweak.α * (hweak.β + 1) / hweak.β - 1))
                V (StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
                (StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
                ctx.auxHypsK ε q' (q' - q)) →
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
      ∀ (ρ υ : (Fin d → ℝ) → ℝ)
        (Dυ : Fin d → (Fin d → ℝ) → ℝ),
        (∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
            0 ≤ ρ x) →
        Periodic.MemLpPer (d := d)
          (ENNReal.ofReal (hweak.β + 1)) (S.indicator ρ) →
        Periodic.MemSobolevPer (d := d)
          (ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β)) υ →
        (∀ i, Periodic.MemLpPer (d := d)
                (ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β))
                (Dυ i)) →
        (∀ i, Periodic.HasWeakDerivPer (d := d) i υ (Dυ i)) →
          0 ≤ mfgOperatorEpsPair (V := V)
                (H := StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
                (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
                (hweak.α * (hweak.β + 1) / hweak.β) ε
                Dυ (S.indicator ρ) υ
                (fun i x => Dυ i x - DuOf q i x)
                (S.indicator ρ - mOf q)
                (υ - uOf q) := by
  -- Bare AE exponents/constant from the AE carrier.
  have hα : (1 : ℝ) < hweak.α := hweak.hα
  have hβ : (0 : ℝ) < hweak.β := hweak.hβ
  set Cε : ℝ := StationaryMFG.InfimalConvolution.CdeltaEps
                  (H := H) (DpH := DpH) hweak ε with hCε_def
  have hCε : (0 : ℝ) < Cε :=
    (StationaryMFG.InfimalConvolution.cdeltaEps_facts_upper
        (H := H) (DpH := DpH) hweak hε).1
  -- H-side supply at `H := HdeltaK0`, all INTERNAL.
  have hcont_H_pm :=
    StationaryMFG.InfimalConvolution.HdeltaK0_continuousOn_H_pm_of_selectorFamily
      (H := H) (DpH := DpH) hweak qε sel (ε := ε) hε
  have hH_rc0 :=
    StationaryMFG.InfimalConvolution.HdeltaK0_rc0_of_selectorFamily
      (H := H) (DpH := DpH) hweak hmonBoundary qε sel hε
  -- DpH-side data (carrier-independent), from the selector family.
  have hDpH_meas :=
    StationaryMFG.InfimalConvolution.measurable_DpHepsilonFam_of_selector
      (H := H) (DpH := DpH) hweak qε sel hMeas ε
  have hcont_DpH_pm :=
    StationaryMFG.InfimalConvolution.continuousOn_DpHepsilonFam_of_selector
      (H := H) (DpH := DpH) hweak qε sel hε
  -- The DpH upper a.e. estimate (general `p`, `0 < m`) from the AE carrier.
  have hDpH_upper : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
      ∀ p m, 0 < m →
        ‖StationaryMFG.InfimalConvolution.DpHepsilonFam hweak qε ε x p m‖
          ≤ Cε * (‖p‖ ^ (hweak.α - 1)
              + m ^ (hweak.β - hweak.β / hweak.α) + 1) :=
    hAE.DpH_upper_ae ε hε hε1
  exact
    StationaryMFG.Theorems.SimplePower.paperSection8_hMinty_set_of_paperHypotheses_of_rc0_of_aeMeasH
      (V := V) (H := StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
      (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
      hα hβ hDpH_meas hcont_H_pm hcont_DpH_pm hDpH_upper hH_rc0
      (ε := ε)
      (fun q hq_K0 S hS ρ υ Dυ hρ_nn hSρ_memLp hυ_memSob hDυ_memLp =>
        have hSρ_nn : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
            0 ≤ S.indicator ρ x := by
          filter_upwards [hρ_nn] with x hx
          exact Set.indicator_nonneg (fun _ _ => hx) x
        -- The three a.e. estimates on `HdeltaK0` from `hAE` (Hdelta→HdeltaK0
        -- on {0<m} via `HdeltaK0_eq_Hdelta_of_pos`).
        have hH_upper_pt :
            ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
              ∀ p m, 0 < m →
                StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε x p m
                  ≤ Cε * (‖p‖ ^ hweak.α + 1) - (m ^ hweak.β) / Cε := by
          filter_upwards [hAE.H_upper_pointwise_ae ε hε hε1] with x hx
          intro p m hm
          rw [StationaryMFG.InfimalConvolution.HdeltaK0_eq_Hdelta_of_pos hweak hm]
          exact hx p m hm
        have hlower :
            ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
              ∀ p m, 0 < m →
                StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε x p m
                  ≥ (‖p‖ ^ hweak.α) / Cε - Cε * (m ^ hweak.β + 1) := by
          filter_upwards [hAE.lower_ae ε hε hε1] with x hx
          intro p m hm
          rw [StationaryMFG.InfimalConvolution.HdeltaK0_eq_Hdelta_of_pos hweak hm]
          exact hx p m hm
        StationaryMFG.Theorems.SimplePower.setTendstoResidueOfBare_of_paperHypotheses_of_aeMeasH_ae
          (V := V)
          (H := StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
          (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
          (β := hweak.β) (α := hweak.α) (C := Cε)
          hα hβ hCε q S hS ρ υ Dυ
          hυ_memSob.1.aestronglyMeasurable
          (fun i => (hDυ_memLp i).aestronglyMeasurable)
          hSρ_memLp hυ_memSob.1 hDυ_memLp hV_memLp hρ_nn
          hH_upper_pt hlower hDpH_upper
          (fun n =>
            StationaryMFG.InfimalConvolution.aemeasurable_HdeltaK0_comp_of_rc0
              (H := H) (DpH := DpH) hweak hMeas hmonBoundary qε sel hε
              (Du := fun x i => Dυ i x)
              (m := fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1))
              (aemeasurable_pi_iff.mpr
                  (fun i => (hDυ_memLp i).aestronglyMeasurable.aemeasurable))
              ((hSρ_memLp.aestronglyMeasurable.aemeasurable).add aemeasurable_const)
              (by
                filter_upwards [hSρ_nn] with x hx
                have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
                linarith))
          (StationaryMFG.InfimalConvolution.aemeasurable_HdeltaK0_comp_of_rc0
            (H := H) (DpH := DpH) hweak hMeas hmonBoundary qε sel hε
            (Du := fun x i => Dυ i x)
            (m := fun x => S.indicator ρ x)
            (aemeasurable_pi_iff.mpr
                (fun i => (hDυ_memLp i).aestronglyMeasurable.aemeasurable))
            hSρ_memLp.aestronglyMeasurable.aemeasurable
            hSρ_nn))
      ctx q

open StationaryMFG.Theorems.SimplePower.Banach in
/-- **G7c-1: refined-cone (`K0_Aepsi_W`/`K_Aepsi_W`) sibling of
`hMinty_set_substitutedPair_of_paperHypotheses_of_rc0_HdeltaK0_ae`.**

Same statement, but the witness premise is `q ∈ K0_Aepsi_W`, the weak-VI premise
is `∀ q' ∈ K_Aepsi_W`, and the user test pair `(υ, Dυ)` carries an extra
weak-derivative tie `hWeak_υ`. The body reuses the K-form residue prelude
verbatim, evaluates the per-query bare residue bundle `r`, builds the same
operator-continuity certificate `hCont` via
`mfgOperatorEpsPair_tendsto_set_perturbation_…_of_rc0_of_aeMeasH` (cone-agnostic),
and finishes with the refined-cone consumer `hVIeps_set_of_KAepsi_W_VI` instead
of `hVIeps_set_of_KAepsi_VI`. This is the T3 analogue of T1's
`paperSection8_hMinty_set_W_of_paperHypotheses`; it is fed to
`exists_regularizedBareSolution_K_W` by G7c-2. -/
theorem hMinty_set_substitutedPair_of_paperHypotheses_of_rc0_HdeltaK0_W_ae
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {ε : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    (hweak : StationaryMFG.Hamiltonian.HypothesisWeakGrowth (d := d) H DpH)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (qε : StationaryMFG.InfimalConvolution.QEpsFamily d)
    (sel : StationaryMFG.InfimalConvolution.InfConvSelectorFamily
              (H := H) (DpH := DpH) hweak qε)
    (hMeas : StationaryMFG.Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (hmonBoundary : StationaryMFG.Hamiltonian.HypothesisMonotone (d := d) H DpH)
    (hdiffBoundary : StationaryMFG.Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    (hAE : StationaryMFG.InfimalConvolution.HdeltaAEPowerEpsData
              (H := H) (DpH := DpH) hweak qε)
    (hV_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal ((hweak.β + 1) / hweak.β)) V)
    [Fact (1 ≤ ENNReal.ofReal (hweak.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β))]
    (ctx : AepsiUniformContextK_W (d := d) ε V
              (StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
              (StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
              (hweak.α * (hweak.β + 1) / hweak.β)
              (hweak.β + 1)
              ((hweak.β + 1) / hweak.β)
              ((hweak.α * (hweak.β + 1) / hweak.β)
                / (hweak.α * (hweak.β + 1) / hweak.β - 1)))
    (q : XBanach d (hweak.β + 1)
            (hweak.α * (hweak.β + 1) / hweak.β)) :
      q ∈ K0_Aepsi_W d (hweak.β + 1)
              (hweak.α * (hweak.β + 1) / hweak.β) →
      (∀ q' ∈ K_Aepsi_W d (hweak.β + 1)
                (hweak.α * (hweak.β + 1) / hweak.β),
          0 ≤ Aepsi_CLM_opK
                (γBarReal := hweak.α * (hweak.β + 1) / hweak.β)
                (βBarReal := hweak.β + 1)
                (βBarReal' := (hweak.β + 1) / hweak.β)
                (γBarReal' := (hweak.α * (hweak.β + 1) / hweak.β)
                                / (hweak.α * (hweak.β + 1) / hweak.β - 1))
                V (StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
                (StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
                ctx.auxHypsK ε q' (q' - q)) →
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
      ∀ (ρ υ : (Fin d → ℝ) → ℝ)
        (Dυ : Fin d → (Fin d → ℝ) → ℝ),
        (∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
            0 ≤ ρ x) →
        Periodic.MemLpPer (d := d)
          (ENNReal.ofReal (hweak.β + 1)) (S.indicator ρ) →
        Periodic.MemSobolevPer (d := d)
          (ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β)) υ →
        (∀ i, Periodic.MemLpPer (d := d)
                (ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β))
                (Dυ i)) →
        (∀ i, Periodic.HasWeakDerivPer (d := d) i υ (Dυ i)) →
          0 ≤ mfgOperatorEpsPair (V := V)
                (H := StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
                (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
                (hweak.α * (hweak.β + 1) / hweak.β) ε
                Dυ (S.indicator ρ) υ
                (fun i x => Dυ i x - DuOf q i x)
                (S.indicator ρ - mOf q)
                (υ - uOf q) := by
  -- Bare AE exponents/constant from the AE carrier (identical to the K-form).
  have hα : (1 : ℝ) < hweak.α := hweak.hα
  have hβ : (0 : ℝ) < hweak.β := hweak.hβ
  set Cε : ℝ := StationaryMFG.InfimalConvolution.CdeltaEps
                  (H := H) (DpH := DpH) hweak ε with hCε_def
  have hCε : (0 : ℝ) < Cε :=
    (StationaryMFG.InfimalConvolution.cdeltaEps_facts_upper
        (H := H) (DpH := DpH) hweak hε).1
  have hcont_H_pm :=
    StationaryMFG.InfimalConvolution.HdeltaK0_continuousOn_H_pm_of_selectorFamily
      (H := H) (DpH := DpH) hweak qε sel (ε := ε) hε
  have hH_rc0 :=
    StationaryMFG.InfimalConvolution.HdeltaK0_rc0_of_selectorFamily
      (H := H) (DpH := DpH) hweak hmonBoundary qε sel hε
  have hDpH_meas :=
    StationaryMFG.InfimalConvolution.measurable_DpHepsilonFam_of_selector
      (H := H) (DpH := DpH) hweak qε sel hMeas ε
  have hcont_DpH_pm :=
    StationaryMFG.InfimalConvolution.continuousOn_DpHepsilonFam_of_selector
      (H := H) (DpH := DpH) hweak qε sel hε
  have hDpH_upper : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
      ∀ p m, 0 < m →
        ‖StationaryMFG.InfimalConvolution.DpHepsilonFam hweak qε ε x p m‖
          ≤ Cε * (‖p‖ ^ (hweak.α - 1)
              + m ^ (hweak.β - hweak.β / hweak.α) + 1) :=
    hAE.DpH_upper_ae ε hε hε1
  -- `SimplePowerExponentFacts` at the AE-pinned exponents (mirror of the
  -- SimplePower K-form producer's internal `hExp` build).
  have hExp_paper :
      SimplePowerExponentFacts
          (SimplePowerExponentFacts.paperGammaBarReal hweak.α hweak.β)
          (SimplePowerExponentFacts.paperBetaBar hweak.β)
          (SimplePowerExponentFacts.paperGammaBar hweak.α hweak.β)
          (SimplePowerExponentFacts.paperBetaBarPrime hweak.β) :=
    SimplePowerExponentFacts.standardPaper hα hβ
  have hExp :
      SimplePowerExponentFacts (hweak.α * (hweak.β + 1) / hweak.β)
          (ENNReal.ofReal (hweak.β + 1))
          (ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β))
          (ENNReal.ofReal ((hweak.β + 1) / hweak.β)) := by
    have h1 :
        (SimplePowerExponentFacts.paperBetaBar hweak.β)
          = ENNReal.ofReal (hweak.β + 1) := by
      simp [SimplePowerExponentFacts.paperBetaBar]
    have h2 :
        (SimplePowerExponentFacts.paperGammaBar hweak.α hweak.β)
          = ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β) := by
      simp [SimplePowerExponentFacts.paperGammaBar]
    have h3 :
        (SimplePowerExponentFacts.paperBetaBarPrime hweak.β)
          = ENNReal.ofReal ((hweak.β + 1) / hweak.β) := by
      simp [SimplePowerExponentFacts.paperBetaBarPrime]
    have h4 :
        (SimplePowerExponentFacts.paperGammaBarReal hweak.α hweak.β)
          = hweak.α * (hweak.β + 1) / hweak.β := by
      simp [SimplePowerExponentFacts.paperGammaBarReal]
    have := hExp_paper
    rw [h1, h2, h3, h4] at this
    exact this
  -- Bind the W-form premises and descend the witness to `K0_Aepsi`.
  intro hq_K0W hVI S hS ρ υ Dυ hρ_nn hSρ_memLp hυ_memSob hDυ_memLp hWeak_υ
  have hq_K0 : q ∈ K0_Aepsi d (hweak.β + 1)
                  (hweak.α * (hweak.β + 1) / hweak.β) :=
    K0_Aepsi_W_subset_K0_Aepsi d (hweak.β + 1)
      (hweak.α * (hweak.β + 1) / hweak.β) hq_K0W
  -- Per-query bare residue bundle (residue closure body, identical to the
  -- K-form producer's).
  have hSρ_nn : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
      0 ≤ S.indicator ρ x := by
    filter_upwards [hρ_nn] with x hx
    exact Set.indicator_nonneg (fun _ _ => hx) x
  have hH_upper_pt :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ∀ p m, 0 < m →
          StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε x p m
            ≤ Cε * (‖p‖ ^ hweak.α + 1) - (m ^ hweak.β) / Cε := by
    filter_upwards [hAE.H_upper_pointwise_ae ε hε hε1] with x hx
    intro p m hm
    rw [StationaryMFG.InfimalConvolution.HdeltaK0_eq_Hdelta_of_pos hweak hm]
    exact hx p m hm
  have hlower :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ∀ p m, 0 < m →
          StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε x p m
            ≥ (‖p‖ ^ hweak.α) / Cε - Cε * (m ^ hweak.β + 1) := by
    filter_upwards [hAE.lower_ae ε hε hε1] with x hx
    intro p m hm
    rw [StationaryMFG.InfimalConvolution.HdeltaK0_eq_Hdelta_of_pos hweak hm]
    exact hx p m hm
  have r :=
    StationaryMFG.Theorems.SimplePower.setTendstoResidueOfBare_of_paperHypotheses_of_aeMeasH_ae
      (V := V)
      (H := StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
      (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
      (β := hweak.β) (α := hweak.α) (C := Cε)
      hα hβ hCε q S hS ρ υ Dυ
      hυ_memSob.1.aestronglyMeasurable
      (fun i => (hDυ_memLp i).aestronglyMeasurable)
      hSρ_memLp hυ_memSob.1 hDυ_memLp hV_memLp hρ_nn
      hH_upper_pt hlower hDpH_upper
      (fun n =>
        StationaryMFG.InfimalConvolution.aemeasurable_HdeltaK0_comp_of_rc0
          (H := H) (DpH := DpH) hweak hMeas hmonBoundary qε sel hε
          (Du := fun x i => Dυ i x)
          (m := fun x => S.indicator ρ x + 1 / ((n : ℝ) + 1))
          (aemeasurable_pi_iff.mpr
              (fun i => (hDυ_memLp i).aestronglyMeasurable.aemeasurable))
          ((hSρ_memLp.aestronglyMeasurable.aemeasurable).add aemeasurable_const)
          (by
            filter_upwards [hSρ_nn] with x hx
            have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
            linarith))
      (StationaryMFG.InfimalConvolution.aemeasurable_HdeltaK0_comp_of_rc0
        (H := H) (DpH := DpH) hweak hMeas hmonBoundary qε sel hε
        (Du := fun x i => Dυ i x)
        (m := fun x => S.indicator ρ x)
        (aemeasurable_pi_iff.mpr
            (fun i => (hDυ_memLp i).aestronglyMeasurable.aemeasurable))
        hSρ_memLp.aestronglyMeasurable.aemeasurable
        hSρ_nn)
  -- Operator-continuity certificate (cone-agnostic; same as the K-form's
  -- internal `hCont`).
  have hCont :=
    mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses_of_aestronglyMeasurable_of_rc0_of_aeMeasH
      (ε := ε)
      (γBarReal := hweak.α * (hweak.β + 1) / hweak.β)
      (βBarReal := hweak.β + 1)
      (βBarReal' := (hweak.β + 1) / hweak.β)
      (γBarReal' := (hweak.α * (hweak.β + 1) / hweak.β)
                      / (hweak.α * (hweak.β + 1) / hweak.β - 1))
      (C := Cε) (α := hweak.α) (β := hweak.β)
      hα hβ hDpH_meas hcont_H_pm hcont_DpH_pm hDpH_upper hExp hH_rc0
      Dυ υ (uOf q) (DuOf q) (mOf q) V S ρ
      hS r.hρ r.hm r.hV r.hυ r.hu r.hDυ r.hDu hρ_nn hSρ_memLp
      r.hHcomp_ae_n r.hHcomp_ae_lim
      r.Gh r.Eh r.hGh_memLp r.hEh_memLp r.hGh_bd r.hEh_bd
      r.Gf r.Ef r.hGf_memLp r.hEf_memLp r.hGf_bd r.hEf_bd
      r.Gm r.Em r.hGm_memLp r.hEm_memLp r.hGm_bd r.hEm_bd
  -- Refined-cone consumer: `hVIeps_set_of_KAepsi_W_VI` (W-typed `hVI` + the
  -- weak-derivative tie `hWeak_υ`).
  exact hVIeps_set_of_KAepsi_W_VI
    ctx.auxHypsK q hVI S hS ρ υ Dυ hρ_nn
    hSρ_memLp hυ_memSob hDυ_memLp hWeak_υ hCont

open StationaryMFG.Theorems.SimplePower.Banach in
/-- **Substituted-pair `hMinty_signed` δ-limit slice** (paper
`thm:strongAepsi.delta`). -/
theorem hMinty_signed_substitutedPair_of_paperHypotheses_of_rc0
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {ε : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    (hweak : StationaryMFG.Hamiltonian.HypothesisWeakGrowth (d := d) H DpH)
    (qE : (Fin d → ℝ) × (Fin d → ℝ) × ℝ → (Fin d → ℝ))
    (hpowEps : StationaryMFG.Hamiltonian.HypothesisPowerGrowth (d := d)
                (StationaryMFG.InfimalConvolution.Hdelta hweak ε)
                (StationaryMFG.InfimalConvolution.DpHepsilon hweak qE))
    (hRegH : StationaryMFG.Hamiltonian.RegularityH (d := d)
                (StationaryMFG.InfimalConvolution.Hdelta hweak ε)
                (StationaryMFG.InfimalConvolution.DpHepsilon hweak qE))
    (hH_rc0 :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ∀ p : Fin d → ℝ,
          Filter.Tendsto
            (fun m : ℝ => StationaryMFG.InfimalConvolution.Hdelta hweak ε x p m)
            (nhdsWithin (0 : ℝ) (Set.Ioi 0))
            (nhds (StationaryMFG.InfimalConvolution.Hdelta hweak ε x p 0)))
    (hV_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal ((hpowEps.β + 1) / hpowEps.β)) V)
    [Fact (1 ≤ ENNReal.ofReal (hpowEps.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hpowEps.α * (hpowEps.β + 1) / hpowEps.β))]
    (ctx : AepsiUniformContextK (d := d) ε V
              (StationaryMFG.InfimalConvolution.Hdelta hweak ε)
              (StationaryMFG.InfimalConvolution.DpHepsilon hweak qE)
              (hpowEps.α * (hpowEps.β + 1) / hpowEps.β)
              (hpowEps.β + 1)
              ((hpowEps.β + 1) / hpowEps.β)
              ((hpowEps.α * (hpowEps.β + 1) / hpowEps.β)
                / (hpowEps.α * (hpowEps.β + 1) / hpowEps.β - 1)))
    (q : XBanach d (hpowEps.β + 1)
            (hpowEps.α * (hpowEps.β + 1) / hpowEps.β)) :
      q ∈ K0_Aepsi d (hpowEps.β + 1)
              (hpowEps.α * (hpowEps.β + 1) / hpowEps.β) →
      (∀ q' ∈ K_Aepsi d (hpowEps.β + 1)
                (hpowEps.α * (hpowEps.β + 1) / hpowEps.β),
          0 ≤ Aepsi_CLM_opK
                (γBarReal := hpowEps.α * (hpowEps.β + 1) / hpowEps.β)
                (βBarReal := hpowEps.β + 1)
                (βBarReal' := (hpowEps.β + 1) / hpowEps.β)
                (γBarReal' := (hpowEps.α * (hpowEps.β + 1) / hpowEps.β)
                                / (hpowEps.α * (hpowEps.β + 1) / hpowEps.β - 1))
                V (StationaryMFG.InfimalConvolution.Hdelta hweak ε)
                (StationaryMFG.InfimalConvolution.DpHepsilon hweak qE)
                ctx.auxHypsK ε q' (q' - q)) →
      ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)) S < ⊤ →
          0 ≤ mfgOperatorEpsPair (V := V)
                (H := StationaryMFG.InfimalConvolution.Hdelta hweak ε)
                (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak qE)
                (hpowEps.α * (hpowEps.β + 1) / hpowEps.β) ε
                (DuOf q)
                (fun x => mOf q x + σ * mOf q x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                (uOf q)
                (fun _ _ => (0 : ℝ))
                (fun x => σ * mOf q x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                (fun _ => (0 : ℝ)) :=
  StationaryMFG.Theorems.SimplePower.paperSection8_hMinty_signed_of_paperHypotheses_of_rc0
    (V := V) (H := StationaryMFG.InfimalConvolution.Hdelta hweak ε)
    (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak qE)
    hpowEps hRegH hH_rc0 (ε := ε)
    (fun q hq_K0 σ hσ S hS _hSfin =>
      StationaryMFG.Theorems.SimplePower.signedTendstoResidueOf_of_paperHypotheses
        (V := V) (H := StationaryMFG.InfimalConvolution.Hdelta hweak ε)
        (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak qE)
        hpowEps q σ hσ S hS hV_memLp (mem_K0_Aepsi_iff.mp hq_K0))
    ctx q

open StationaryMFG.Theorems.SimplePower.Banach in
/-- **Substituted-pair `hMinty_signed` δ-limit slice, re-keyed on the closed-cone
carrier `HdeltaK0`** (paper `thm:strongAepsi.delta`, D2b-1c-ii-c4c-signed).

Additive `HdeltaK0`-keyed variant of
`hMinty_signed_substitutedPair_of_paperHypotheses_of_rc0`. The conclusion is
keyed on `mfgOperatorEpsPair (H := HdeltaK0 hweak ε)`; the strict entry above
(on `Hdelta`) is left intact for its existing caller. This variant carries NO
loose `RegularityH (Hdelta …)` / `HypothesisHat0 (Hdelta …)` / raw-H `hH_rc0`
binder: the H-side data is supplied INTERNALLY at `H := HdeltaK0` from
`HdeltaK0_continuousOn_H_pm_of_selectorFamily`, `HdeltaK0_rc0_of_selectorFamily`, and
`aemeasurable_HdeltaK0_comp_of_rc0`, and the bare residue supplier
`signedTendstoResidueOfBare_of_paperHypotheses_of_aeMeasH` reuses the strict
`HdeltaPos`-keyed dominators. The GATE-permitted riders are
`hMeas`/`hmonBoundary`/`hdiffBoundary` and the `RegularityH (HdeltaPos)`-class supply
`hpowEps`. -/
theorem hMinty_signed_substitutedPair_of_paperHypotheses_of_rc0_HdeltaK0
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {ε : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    (hweak : StationaryMFG.Hamiltonian.HypothesisWeakGrowth (d := d) H DpH)
    (hε : 0 < ε)
    (qε : StationaryMFG.InfimalConvolution.QEpsFamily d)
    (sel : StationaryMFG.InfimalConvolution.InfConvSelectorFamily
              (H := H) (DpH := DpH) hweak qε)
    (hMeas : StationaryMFG.Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (hmonBoundary : StationaryMFG.Hamiltonian.HypothesisMonotone (d := d) H DpH)
    (hdiffBoundary : StationaryMFG.Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    (hpowEps : StationaryMFG.Hamiltonian.HypothesisPowerGrowth (d := d)
                (StationaryMFG.InfimalConvolution.HdeltaPos hweak ε)
                (StationaryMFG.InfimalConvolution.DpHepsilonFam hweak qε ε))
    (hV_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal ((hpowEps.β + 1) / hpowEps.β)) V)
    [Fact (1 ≤ ENNReal.ofReal (hpowEps.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hpowEps.α * (hpowEps.β + 1) / hpowEps.β))]
    (ctx : AepsiUniformContextK (d := d) ε V
              (StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
              (StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
              (hpowEps.α * (hpowEps.β + 1) / hpowEps.β)
              (hpowEps.β + 1)
              ((hpowEps.β + 1) / hpowEps.β)
              ((hpowEps.α * (hpowEps.β + 1) / hpowEps.β)
                / (hpowEps.α * (hpowEps.β + 1) / hpowEps.β - 1)))
    (q : XBanach d (hpowEps.β + 1)
            (hpowEps.α * (hpowEps.β + 1) / hpowEps.β)) :
      q ∈ K0_Aepsi d (hpowEps.β + 1)
              (hpowEps.α * (hpowEps.β + 1) / hpowEps.β) →
      (∀ q' ∈ K_Aepsi d (hpowEps.β + 1)
                (hpowEps.α * (hpowEps.β + 1) / hpowEps.β),
          0 ≤ Aepsi_CLM_opK
                (γBarReal := hpowEps.α * (hpowEps.β + 1) / hpowEps.β)
                (βBarReal := hpowEps.β + 1)
                (βBarReal' := (hpowEps.β + 1) / hpowEps.β)
                (γBarReal' := (hpowEps.α * (hpowEps.β + 1) / hpowEps.β)
                                / (hpowEps.α * (hpowEps.β + 1) / hpowEps.β - 1))
                V (StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
                (StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
                ctx.auxHypsK ε q' (q' - q)) →
      ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)) S < ⊤ →
          0 ≤ mfgOperatorEpsPair (V := V)
                (H := StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
                (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
                (hpowEps.α * (hpowEps.β + 1) / hpowEps.β) ε
                (DuOf q)
                (fun x => mOf q x + σ * mOf q x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                (uOf q)
                (fun _ _ => (0 : ℝ))
                (fun x => σ * mOf q x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                (fun _ => (0 : ℝ)) := by
  -- H-side supply at `H := HdeltaK0`, all INTERNAL.
  have hcont_H_pm :=
    StationaryMFG.InfimalConvolution.HdeltaK0_continuousOn_H_pm_of_selectorFamily
      (H := H) (DpH := DpH) hweak qε sel (ε := ε) hε
  have hH_rc0 :=
    StationaryMFG.InfimalConvolution.HdeltaK0_rc0_of_selectorFamily
      (H := H) (DpH := DpH) hweak hmonBoundary qε sel hε
  exact
    StationaryMFG.Theorems.SimplePower.paperSection8_hMinty_signed_of_paperHypotheses_of_rc0_of_aeMeasH
      (V := V) (H := StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
      (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
      (C := hpowEps.C) hpowEps.hα hpowEps.hβ hcont_H_pm hH_rc0
      (ε := ε)
      (fun q hq_K0 σ hσ S hS _hSfin =>
        -- The two H AE composites at `H := HdeltaK0` at the signed base, and
        -- the per-`n` `{0<m}` agreement, from the closed-cone helpers.
        have hm_nn : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
            0 ≤ StationaryMFG.Theorems.SimplePower.Banach.mOf q x :=
          mem_K0_Aepsi_iff.mp hq_K0
        -- Nonnegativity of the signed base `mOf q + σ·mOf q·𝟙_S`.
        have hbase_nn : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
            0 ≤ StationaryMFG.Theorems.SimplePower.Banach.mOf q x
                + σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
          filter_upwards [hm_nn] with x hx
          have hind : (0 : ℝ) ≤ S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x ∧
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x ≤ 1 := by
            by_cases hxS : x ∈ S
            · rw [Set.indicator_of_mem hxS]; constructor <;> norm_num
            · rw [Set.indicator_of_notMem hxS]; constructor <;> norm_num
          rcases hσ with hσ1 | hσm1
          · subst hσ1
            have hmul : 0 ≤ StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x :=
              mul_nonneg hx hind.1
            nlinarith [hmul]
          · subst hσm1
            -- `m + (-1)·m·𝟙 = m·(1 - 𝟙) ≥ 0` since `𝟙 ≤ 1`.
            have hfac : StationaryMFG.Theorems.SimplePower.Banach.mOf q x
                + (-1) * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                = StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                    (1 - S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
              ring
            rw [hfac]
            exact mul_nonneg hx (by linarith [hind.2])
        -- AEMeasurability of the signed base `mOf q + σ·mOf q·𝟙_S`.
        have hm_aem : AEMeasurable (StationaryMFG.Theorems.SimplePower.Banach.mOf q)
            (MeasureTheory.volume.restrict (Periodic.UnitCube d)) :=
          ((MeasureTheory.Lp.stronglyMeasurable q.1).measurable).aemeasurable
        have hbase_aem : AEMeasurable
            (fun x => StationaryMFG.Theorems.SimplePower.Banach.mOf q x
              + σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
            (MeasureTheory.volume.restrict (Periodic.UnitCube d)) :=
          hm_aem.add ((hm_aem.const_mul σ).mul
            ((measurable_const.indicator hS).aemeasurable))
        StationaryMFG.Theorems.SimplePower.signedTendstoResidueOfBare_of_paperHypotheses_of_aeMeasH
          (V := V)
          (H := StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
          (H' := StationaryMFG.InfimalConvolution.HdeltaPos hweak ε)
          (DpH := StationaryMFG.InfimalConvolution.DpHepsilonFam hweak qε ε)
          hpowEps q σ hσ S hS hV_memLp hm_nn
          (fun n => by
            filter_upwards [hbase_nn] with x hx
            have hpos : 0 < StationaryMFG.Theorems.SimplePower.Banach.mOf q x
                + σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                + 1 / ((n : ℝ) + 1) := by
              have hone : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
              linarith
            exact StationaryMFG.InfimalConvolution.HdeltaK0_eq_HdeltaPos_of_pos
              hweak hpos)
          (fun n =>
            StationaryMFG.InfimalConvolution.aemeasurable_HdeltaK0_comp_of_rc0
              (H := H) (DpH := DpH) hweak hMeas hmonBoundary qε sel hε
              (Du := fun x i => StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
              (m := fun x => StationaryMFG.Theorems.SimplePower.Banach.mOf q x
                + σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                + 1 / ((n : ℝ) + 1))
              (aemeasurable_pi_iff.mpr
                  (fun i => ((MeasureTheory.Lp.stronglyMeasurable
                    (q.2.2 i)).measurable).aemeasurable))
              (hbase_aem.add aemeasurable_const)
              (by
                filter_upwards [hbase_nn] with x hx
                have hone : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
                linarith))
          (StationaryMFG.InfimalConvolution.aemeasurable_HdeltaK0_comp_of_rc0
            (H := H) (DpH := DpH) hweak hMeas hmonBoundary qε sel hε
            (Du := fun x i => StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
            (m := fun x => StationaryMFG.Theorems.SimplePower.Banach.mOf q x
              + σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
            (aemeasurable_pi_iff.mpr
                (fun i => ((MeasureTheory.Lp.stronglyMeasurable
                  (q.2.2 i)).measurable).aemeasurable))
            hbase_aem
            hbase_nn))
      ctx q

open StationaryMFG.Theorems.SimplePower.Banach in
/-- **Substituted-pair `hMinty_signed` δ-limit slice, re-keyed on the closed-cone
carrier `HdeltaK0`, AE/bare-exponent variant** (paper `thm:strongAepsi.delta`,
D2c-2e-2b-signed retype rewire).

Additive `_ae` sibling of `hMinty_signed_substitutedPair_of_paperHypotheses_of_rc0_HdeltaK0`
that DROPS the strict `hpowEps : HypothesisPowerGrowth (HdeltaPos …)` entirely.
The exponent type-indices are reindexed off the AE carrier's bare exponents
`hweak.β`/`hweak.α`, the constant is `CdeltaEps hweak ε`, and the two a.e.
analytic estimates are sourced from the AE carrier
`hAE : HdeltaAEPowerEpsData hweak qε` (`H_upper_pointwise_ae`/`lower_ae`),
transferred from `Hdelta` to the target carrier `HdeltaK0` on `{0<m}` via
`HdeltaK0_eq_Hdelta_of_pos`. The per-query bare residue supplier is the child-C
`_ae` sibling `signedTendstoResidueOfBare_of_paperHypotheses_of_aeMeasH_ae`.

GATE #1: NO `hpowEps`/`HypothesisPowerGrowth(HdeltaPos)`/`RegularityH(HdeltaPos)`/
`hFormPos`/`hqE_per`/`hInj`/`hSurj`/`qEofMinv`. The H-side data is supplied
INTERNALLY at `H := HdeltaK0`; the permitted riders are the AE carrier `hAE` +
`hMeas`/`hmonBoundary`/`hdiffBoundary`/`hweak`/`sel` + `hε1`. -/
theorem hMinty_signed_substitutedPair_of_paperHypotheses_of_rc0_HdeltaK0_ae
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {ε : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    (hweak : StationaryMFG.Hamiltonian.HypothesisWeakGrowth (d := d) H DpH)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (qε : StationaryMFG.InfimalConvolution.QEpsFamily d)
    (sel : StationaryMFG.InfimalConvolution.InfConvSelectorFamily
              (H := H) (DpH := DpH) hweak qε)
    (hMeas : StationaryMFG.Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (hmonBoundary : StationaryMFG.Hamiltonian.HypothesisMonotone (d := d) H DpH)
    (hdiffBoundary : StationaryMFG.Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    (hAE : StationaryMFG.InfimalConvolution.HdeltaAEPowerEpsData
              (H := H) (DpH := DpH) hweak qε)
    (hV_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal ((hweak.β + 1) / hweak.β)) V)
    [Fact (1 ≤ ENNReal.ofReal (hweak.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β))]
    (ctx : AepsiUniformContextK (d := d) ε V
              (StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
              (StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
              (hweak.α * (hweak.β + 1) / hweak.β)
              (hweak.β + 1)
              ((hweak.β + 1) / hweak.β)
              ((hweak.α * (hweak.β + 1) / hweak.β)
                / (hweak.α * (hweak.β + 1) / hweak.β - 1)))
    (q : XBanach d (hweak.β + 1)
            (hweak.α * (hweak.β + 1) / hweak.β)) :
      q ∈ K0_Aepsi d (hweak.β + 1)
              (hweak.α * (hweak.β + 1) / hweak.β) →
      (∀ q' ∈ K_Aepsi d (hweak.β + 1)
                (hweak.α * (hweak.β + 1) / hweak.β),
          0 ≤ Aepsi_CLM_opK
                (γBarReal := hweak.α * (hweak.β + 1) / hweak.β)
                (βBarReal := hweak.β + 1)
                (βBarReal' := (hweak.β + 1) / hweak.β)
                (γBarReal' := (hweak.α * (hweak.β + 1) / hweak.β)
                                / (hweak.α * (hweak.β + 1) / hweak.β - 1))
                V (StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
                (StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
                ctx.auxHypsK ε q' (q' - q)) →
      ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)) S < ⊤ →
          0 ≤ mfgOperatorEpsPair (V := V)
                (H := StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
                (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
                (hweak.α * (hweak.β + 1) / hweak.β) ε
                (DuOf q)
                (fun x => mOf q x + σ * mOf q x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                (uOf q)
                (fun _ _ => (0 : ℝ))
                (fun x => σ * mOf q x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                (fun _ => (0 : ℝ)) := by
  -- Bare AE exponents/constant from the AE carrier.
  have hα : (1 : ℝ) < hweak.α := hweak.hα
  have hβ : (0 : ℝ) < hweak.β := hweak.hβ
  set Cε : ℝ := StationaryMFG.InfimalConvolution.CdeltaEps
                  (H := H) (DpH := DpH) hweak ε with hCε_def
  have hCε : (0 : ℝ) < Cε :=
    (StationaryMFG.InfimalConvolution.cdeltaEps_facts_upper
        (H := H) (DpH := DpH) hweak hε).1
  -- H-side supply at `H := HdeltaK0`, all INTERNAL.
  have hcont_H_pm :=
    StationaryMFG.InfimalConvolution.HdeltaK0_continuousOn_H_pm_of_selectorFamily
      (H := H) (DpH := DpH) hweak qε sel (ε := ε) hε
  have hH_rc0 :=
    StationaryMFG.InfimalConvolution.HdeltaK0_rc0_of_selectorFamily
      (H := H) (DpH := DpH) hweak hmonBoundary qε sel hε
  exact
    StationaryMFG.Theorems.SimplePower.paperSection8_hMinty_signed_of_paperHypotheses_of_rc0_of_aeMeasH
      (V := V) (H := StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
      (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
      (C := Cε) hα hβ hcont_H_pm hH_rc0
      (ε := ε)
      (fun q hq_K0 σ hσ S hS _hSfin =>
        have hm_nn : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
            0 ≤ StationaryMFG.Theorems.SimplePower.Banach.mOf q x :=
          mem_K0_Aepsi_iff.mp hq_K0
        -- The two a.e. estimates on `HdeltaK0` from `hAE` (Hdelta→HdeltaK0
        -- on {0<m} via `HdeltaK0_eq_Hdelta_of_pos`).
        have hH_upper_pt :
            ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
              ∀ p m, 0 < m →
                StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε x p m
                  ≤ Cε * (‖p‖ ^ hweak.α + 1) - (m ^ hweak.β) / Cε := by
          filter_upwards [hAE.H_upper_pointwise_ae ε hε hε1] with x hx
          intro p m hm
          rw [StationaryMFG.InfimalConvolution.HdeltaK0_eq_Hdelta_of_pos hweak hm]
          exact hx p m hm
        have hlower :
            ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
              ∀ p m, 0 < m →
                StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε x p m
                  ≥ (‖p‖ ^ hweak.α) / Cε - Cε * (m ^ hweak.β + 1) := by
          filter_upwards [hAE.lower_ae ε hε hε1] with x hx
          intro p m hm
          rw [StationaryMFG.InfimalConvolution.HdeltaK0_eq_Hdelta_of_pos hweak hm]
          exact hx p m hm
        -- Nonnegativity of the signed base `mOf q + σ·mOf q·𝟙_S`.
        have hbase_nn : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
            0 ≤ StationaryMFG.Theorems.SimplePower.Banach.mOf q x
                + σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
          filter_upwards [hm_nn] with x hx
          have hind : (0 : ℝ) ≤ S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x ∧
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x ≤ 1 := by
            by_cases hxS : x ∈ S
            · rw [Set.indicator_of_mem hxS]; constructor <;> norm_num
            · rw [Set.indicator_of_notMem hxS]; constructor <;> norm_num
          rcases hσ with hσ1 | hσm1
          · subst hσ1
            have hmul : 0 ≤ StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x :=
              mul_nonneg hx hind.1
            nlinarith [hmul]
          · subst hσm1
            have hfac : StationaryMFG.Theorems.SimplePower.Banach.mOf q x
                + (-1) * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                = StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                    (1 - S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
              ring
            rw [hfac]
            exact mul_nonneg hx (by linarith [hind.2])
        have hm_aem : AEMeasurable (StationaryMFG.Theorems.SimplePower.Banach.mOf q)
            (MeasureTheory.volume.restrict (Periodic.UnitCube d)) :=
          ((MeasureTheory.Lp.stronglyMeasurable q.1).measurable).aemeasurable
        have hbase_aem : AEMeasurable
            (fun x => StationaryMFG.Theorems.SimplePower.Banach.mOf q x
              + σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
            (MeasureTheory.volume.restrict (Periodic.UnitCube d)) :=
          hm_aem.add ((hm_aem.const_mul σ).mul
            ((measurable_const.indicator hS).aemeasurable))
        StationaryMFG.Theorems.SimplePower.signedTendstoResidueOfBare_of_paperHypotheses_of_aeMeasH_ae
          (V := V)
          (H := StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
          (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
          (β := hweak.β) (α := hweak.α) (C := Cε)
          hα hβ hCε q σ hσ S hS hV_memLp hm_nn
          hH_upper_pt hlower
          (fun n =>
            StationaryMFG.InfimalConvolution.aemeasurable_HdeltaK0_comp_of_rc0
              (H := H) (DpH := DpH) hweak hMeas hmonBoundary qε sel hε
              (Du := fun x i => StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
              (m := fun x => StationaryMFG.Theorems.SimplePower.Banach.mOf q x
                + σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                + 1 / ((n : ℝ) + 1))
              (aemeasurable_pi_iff.mpr
                  (fun i => ((MeasureTheory.Lp.stronglyMeasurable
                    (q.2.2 i)).measurable).aemeasurable))
              (hbase_aem.add aemeasurable_const)
              (by
                filter_upwards [hbase_nn] with x hx
                have hone : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
                linarith))
          (StationaryMFG.InfimalConvolution.aemeasurable_HdeltaK0_comp_of_rc0
            (H := H) (DpH := DpH) hweak hMeas hmonBoundary qε sel hε
            (Du := fun x i => StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
            (m := fun x => StationaryMFG.Theorems.SimplePower.Banach.mOf q x
              + σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
            (aemeasurable_pi_iff.mpr
                (fun i => ((MeasureTheory.Lp.stronglyMeasurable
                  (q.2.2 i)).measurable).aemeasurable))
            hbase_aem
            hbase_nn))
      ctx q

open StationaryMFG.Theorems.SimplePower.Banach in
/-- **G7c-1: refined-cone (`K0_Aepsi_W`/`K_Aepsi_W`) sibling of
`hMinty_signed_substitutedPair_of_paperHypotheses_of_rc0_HdeltaK0_ae`.**

W-form signed-family Minty producer. The signed test point inherits its
weak-derivative tie from `q` (its `υ`/`Dυ` factors equal `q`'s), so — unlike
the set family — no extra `hWeak_υ` premise is required. Body reuses the K-form
residue prelude, evaluates the signed bare residue bundle `r`, builds the same
`hCont`, and finishes with `hVIeps_signed_of_KAepsi_W_VI`. -/
theorem hMinty_signed_substitutedPair_of_paperHypotheses_of_rc0_HdeltaK0_W_ae
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {ε : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    (hweak : StationaryMFG.Hamiltonian.HypothesisWeakGrowth (d := d) H DpH)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (qε : StationaryMFG.InfimalConvolution.QEpsFamily d)
    (sel : StationaryMFG.InfimalConvolution.InfConvSelectorFamily
              (H := H) (DpH := DpH) hweak qε)
    (hMeas : StationaryMFG.Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (hmonBoundary : StationaryMFG.Hamiltonian.HypothesisMonotone (d := d) H DpH)
    (hdiffBoundary : StationaryMFG.Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    (hAE : StationaryMFG.InfimalConvolution.HdeltaAEPowerEpsData
              (H := H) (DpH := DpH) hweak qε)
    (hV_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal ((hweak.β + 1) / hweak.β)) V)
    [Fact (1 ≤ ENNReal.ofReal (hweak.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β))]
    (ctx : AepsiUniformContextK_W (d := d) ε V
              (StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
              (StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
              (hweak.α * (hweak.β + 1) / hweak.β)
              (hweak.β + 1)
              ((hweak.β + 1) / hweak.β)
              ((hweak.α * (hweak.β + 1) / hweak.β)
                / (hweak.α * (hweak.β + 1) / hweak.β - 1)))
    (q : XBanach d (hweak.β + 1)
            (hweak.α * (hweak.β + 1) / hweak.β)) :
      q ∈ K0_Aepsi_W d (hweak.β + 1)
              (hweak.α * (hweak.β + 1) / hweak.β) →
      (∀ q' ∈ K_Aepsi_W d (hweak.β + 1)
                (hweak.α * (hweak.β + 1) / hweak.β),
          0 ≤ Aepsi_CLM_opK
                (γBarReal := hweak.α * (hweak.β + 1) / hweak.β)
                (βBarReal := hweak.β + 1)
                (βBarReal' := (hweak.β + 1) / hweak.β)
                (γBarReal' := (hweak.α * (hweak.β + 1) / hweak.β)
                                / (hweak.α * (hweak.β + 1) / hweak.β - 1))
                V (StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
                (StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
                ctx.auxHypsK ε q' (q' - q)) →
      ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)) S < ⊤ →
          0 ≤ mfgOperatorEpsPair (V := V)
                (H := StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
                (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
                (hweak.α * (hweak.β + 1) / hweak.β) ε
                (DuOf q)
                (fun x => mOf q x + σ * mOf q x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                (uOf q)
                (fun _ _ => (0 : ℝ))
                (fun x => σ * mOf q x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                (fun _ => (0 : ℝ)) := by
  have hα : (1 : ℝ) < hweak.α := hweak.hα
  have hβ : (0 : ℝ) < hweak.β := hweak.hβ
  set Cε : ℝ := StationaryMFG.InfimalConvolution.CdeltaEps
                  (H := H) (DpH := DpH) hweak ε with hCε_def
  have hCε : (0 : ℝ) < Cε :=
    (StationaryMFG.InfimalConvolution.cdeltaEps_facts_upper
        (H := H) (DpH := DpH) hweak hε).1
  have hcont_H_pm :=
    StationaryMFG.InfimalConvolution.HdeltaK0_continuousOn_H_pm_of_selectorFamily
      (H := H) (DpH := DpH) hweak qε sel (ε := ε) hε
  have hH_rc0 :=
    StationaryMFG.InfimalConvolution.HdeltaK0_rc0_of_selectorFamily
      (H := H) (DpH := DpH) hweak hmonBoundary qε sel hε
  intro hq_K0W hVI σ hσ S hS hSfin
  have hq_K0 : q ∈ K0_Aepsi d (hweak.β + 1)
                  (hweak.α * (hweak.β + 1) / hweak.β) :=
    K0_Aepsi_W_subset_K0_Aepsi d (hweak.β + 1)
      (hweak.α * (hweak.β + 1) / hweak.β) hq_K0W
  -- Signed bare residue bundle (residue closure body, identical to the K-form).
  have hm_nn : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
      0 ≤ StationaryMFG.Theorems.SimplePower.Banach.mOf q x :=
    mem_K0_Aepsi_iff.mp hq_K0
  have hH_upper_pt :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ∀ p m, 0 < m →
          StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε x p m
            ≤ Cε * (‖p‖ ^ hweak.α + 1) - (m ^ hweak.β) / Cε := by
    filter_upwards [hAE.H_upper_pointwise_ae ε hε hε1] with x hx
    intro p m hm
    rw [StationaryMFG.InfimalConvolution.HdeltaK0_eq_Hdelta_of_pos hweak hm]
    exact hx p m hm
  have hlower :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ∀ p m, 0 < m →
          StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε x p m
            ≥ (‖p‖ ^ hweak.α) / Cε - Cε * (m ^ hweak.β + 1) := by
    filter_upwards [hAE.lower_ae ε hε hε1] with x hx
    intro p m hm
    rw [StationaryMFG.InfimalConvolution.HdeltaK0_eq_Hdelta_of_pos hweak hm]
    exact hx p m hm
  have hbase_nn : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
      0 ≤ StationaryMFG.Theorems.SimplePower.Banach.mOf q x
          + σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
    filter_upwards [hm_nn] with x hx
    have hind : (0 : ℝ) ≤ S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x ∧
        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x ≤ 1 := by
      by_cases hxS : x ∈ S
      · rw [Set.indicator_of_mem hxS]; constructor <;> norm_num
      · rw [Set.indicator_of_notMem hxS]; constructor <;> norm_num
    rcases hσ with hσ1 | hσm1
    · subst hσ1
      have hmul : 0 ≤ StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x :=
        mul_nonneg hx hind.1
      nlinarith [hmul]
    · subst hσm1
      have hfac : StationaryMFG.Theorems.SimplePower.Banach.mOf q x
          + (-1) * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
          = StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
              (1 - S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
        ring
      rw [hfac]
      exact mul_nonneg hx (by linarith [hind.2])
  have hm_aem : AEMeasurable (StationaryMFG.Theorems.SimplePower.Banach.mOf q)
      (MeasureTheory.volume.restrict (Periodic.UnitCube d)) :=
    ((MeasureTheory.Lp.stronglyMeasurable q.1).measurable).aemeasurable
  have hbase_aem : AEMeasurable
      (fun x => StationaryMFG.Theorems.SimplePower.Banach.mOf q x
        + σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
      (MeasureTheory.volume.restrict (Periodic.UnitCube d)) :=
    hm_aem.add ((hm_aem.const_mul σ).mul
      ((measurable_const.indicator hS).aemeasurable))
  have r :=
    StationaryMFG.Theorems.SimplePower.signedTendstoResidueOfBare_of_paperHypotheses_of_aeMeasH_ae
      (V := V)
      (H := StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
      (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
      (β := hweak.β) (α := hweak.α) (C := Cε)
      hα hβ hCε q σ hσ S hS hV_memLp hm_nn
      hH_upper_pt hlower
      (fun n =>
        StationaryMFG.InfimalConvolution.aemeasurable_HdeltaK0_comp_of_rc0
          (H := H) (DpH := DpH) hweak hMeas hmonBoundary qε sel hε
          (Du := fun x i => StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
          (m := fun x => StationaryMFG.Theorems.SimplePower.Banach.mOf q x
            + σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
            + 1 / ((n : ℝ) + 1))
          (aemeasurable_pi_iff.mpr
              (fun i => ((MeasureTheory.Lp.stronglyMeasurable
                (q.2.2 i)).measurable).aemeasurable))
          (hbase_aem.add aemeasurable_const)
          (by
            filter_upwards [hbase_nn] with x hx
            have hone : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
            linarith))
      (StationaryMFG.InfimalConvolution.aemeasurable_HdeltaK0_comp_of_rc0
        (H := H) (DpH := DpH) hweak hMeas hmonBoundary qε sel hε
        (Du := fun x i => StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
        (m := fun x => StationaryMFG.Theorems.SimplePower.Banach.mOf q x
          + σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
        (aemeasurable_pi_iff.mpr
            (fun i => ((MeasureTheory.Lp.stronglyMeasurable
              (q.2.2 i)).measurable).aemeasurable))
        hbase_aem
        hbase_nn)
  have hCont :=
    mfgOperatorEpsPair_tendsto_signed_perturbation_of_paperHypotheses_of_aestronglyMeasurable_of_rc0_of_aeMeasH
      (ε := ε)
      (γBarReal := hweak.α * (hweak.β + 1) / hweak.β)
      (β := hweak.β)
      (H := StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
      (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
      hβ hcont_H_pm hH_rc0
      (DuOf q) (uOf q) (mOf q) V σ hσ S hS
      r.hm r.hV r.hu r.hDu r.hm_memLp r.hm_nn
      r.hHcomp_ae_n r.hHcomp_ae_lim
      r.Gh r.hGh_memLp r.hGh_bd
  exact hVIeps_signed_of_KAepsi_W_VI
    ctx.auxHypsK q hq_K0W hVI σ hσ S hS hSfin hCont

open StationaryMFG.Theorems.SimplePower.Banach in
/-- **Substituted-pair `hMinty_transport` δ-limit slice** (paper
`thm:strongAepsi.delta`). -/
theorem hMinty_transport_substitutedPair_of_paperHypotheses_of_rc0
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {ε : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    (hweak : StationaryMFG.Hamiltonian.HypothesisWeakGrowth (d := d) H DpH)
    (qE : (Fin d → ℝ) × (Fin d → ℝ) × ℝ → (Fin d → ℝ))
    (hpowEps : StationaryMFG.Hamiltonian.HypothesisPowerGrowth (d := d)
                (StationaryMFG.InfimalConvolution.Hdelta hweak ε)
                (StationaryMFG.InfimalConvolution.DpHepsilon hweak qE))
    (hRegH : StationaryMFG.Hamiltonian.RegularityH (d := d)
                (StationaryMFG.InfimalConvolution.Hdelta hweak ε)
                (StationaryMFG.InfimalConvolution.DpHepsilon hweak qE))
    (hH_rc0 :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ∀ p : Fin d → ℝ,
          Filter.Tendsto
            (fun m : ℝ => StationaryMFG.InfimalConvolution.Hdelta hweak ε x p m)
            (nhdsWithin (0 : ℝ) (Set.Ioi 0))
            (nhds (StationaryMFG.InfimalConvolution.Hdelta hweak ε x p 0)))
    (hV_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal ((hpowEps.β + 1) / hpowEps.β)) V)
    [Fact (1 ≤ ENNReal.ofReal (hpowEps.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hpowEps.α * (hpowEps.β + 1) / hpowEps.β))]
    (ctx : AepsiUniformContextK (d := d) ε V
              (StationaryMFG.InfimalConvolution.Hdelta hweak ε)
              (StationaryMFG.InfimalConvolution.DpHepsilon hweak qE)
              (hpowEps.α * (hpowEps.β + 1) / hpowEps.β)
              (hpowEps.β + 1)
              ((hpowEps.β + 1) / hpowEps.β)
              ((hpowEps.α * (hpowEps.β + 1) / hpowEps.β)
                / (hpowEps.α * (hpowEps.β + 1) / hpowEps.β - 1)))
    (q : XBanach d (hpowEps.β + 1)
            (hpowEps.α * (hpowEps.β + 1) / hpowEps.β)) :
      q ∈ K0_Aepsi d (hpowEps.β + 1)
              (hpowEps.α * (hpowEps.β + 1) / hpowEps.β) →
      (∀ q' ∈ K_Aepsi d (hpowEps.β + 1)
                (hpowEps.α * (hpowEps.β + 1) / hpowEps.β),
          0 ≤ Aepsi_CLM_opK
                (γBarReal := hpowEps.α * (hpowEps.β + 1) / hpowEps.β)
                (βBarReal := hpowEps.β + 1)
                (βBarReal' := (hpowEps.β + 1) / hpowEps.β)
                (γBarReal' := (hpowEps.α * (hpowEps.β + 1) / hpowEps.β)
                                / (hpowEps.α * (hpowEps.β + 1) / hpowEps.β - 1))
                V (StationaryMFG.InfimalConvolution.Hdelta hweak ε)
                (StationaryMFG.InfimalConvolution.DpHepsilon hweak qE)
                ctx.auxHypsK ε q' (q' - q)) →
      ∀ (σ υ : (Fin d → ℝ) → ℝ)
        (φ : Fin d → (Fin d → ℝ) → ℝ),
        (∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)), 0 ≤ σ x) →
        Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpowEps.β + 1)) σ →
        Periodic.MemSobolevPer (d := d)
          (ENNReal.ofReal (hpowEps.α * (hpowEps.β + 1) / hpowEps.β)) υ →
        (∀ i, Periodic.MemLpPer (d := d)
                (ENNReal.ofReal (hpowEps.α * (hpowEps.β + 1) / hpowEps.β))
                (φ i)) →
        (∀ i, Periodic.HasWeakDerivPer (d := d) i υ (φ i)) →
          0 ≤ mfgOperatorEpsPair (V := V)
                (H := StationaryMFG.InfimalConvolution.Hdelta hweak ε)
                (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak qE)
                (hpowEps.α * (hpowEps.β + 1) / hpowEps.β) ε
                φ σ υ
                (fun i x => φ i x - DuOf q i x)
                (σ - mOf q)
                (υ - uOf q) :=
  StationaryMFG.Theorems.SimplePower.paperSection8_hMinty_transport_of_paperHypotheses_of_rc0
    (V := V) (H := StationaryMFG.InfimalConvolution.Hdelta hweak ε)
    (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak qE)
    hpowEps hRegH hH_rc0 (ε := ε)
    (fun q _hq_K0 σ υ φ hσ_nn hσ_memLp hυ_memSob hφ_memLp =>
      StationaryMFG.Theorems.SimplePower.transportTendstoResidueOf_of_paperHypotheses
        (V := V) (H := StationaryMFG.InfimalConvolution.Hdelta hweak ε)
        (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak qE)
        hpowEps q σ υ φ
        hσ_memLp.aestronglyMeasurable
        hυ_memSob.1.aestronglyMeasurable
        (fun i => (hφ_memLp i).aestronglyMeasurable)
        hσ_memLp hυ_memSob.1 hφ_memLp hV_memLp hσ_nn)
    ctx q

open StationaryMFG.Theorems.SimplePower.Banach in
/-- **Substituted-pair `hMinty_transport` δ-limit slice, re-keyed on the
closed-cone carrier `HdeltaK0`** (paper `thm:strongAepsi.delta`,
D2b-1c-ii-c4c-transport).

Additive `HdeltaK0`-keyed variant of
`hMinty_transport_substitutedPair_of_paperHypotheses_of_rc0`. The conclusion is
keyed on `mfgOperatorEpsPair (H := HdeltaK0 hweak ε)`; the strict entry above
(on `Hdelta`) is left intact for its existing caller. This variant carries NO
loose `RegularityH (Hdelta …)` / `HypothesisHat0 (Hdelta …)` / raw-H `hH_rc0`
binder: the H-side data is supplied INTERNALLY at `H := HdeltaK0` from
`HdeltaK0_continuousOn_H_pm_of_selectorFamily`, `HdeltaK0_rc0_of_selectorFamily`, and
`aemeasurable_HdeltaK0_comp_of_rc0`, and the bare residue supplier
`transportTendstoResidueOfBare_of_paperHypotheses_of_aeMeasH` reuses the strict
`HdeltaPos`-keyed dominators. The GATE-permitted riders are
`hMeas`/`hmonBoundary`/`hdiffBoundary` and the `RegularityH (HdeltaPos)`-class supply
`hpowEps`. -/
theorem hMinty_transport_substitutedPair_of_paperHypotheses_of_rc0_HdeltaK0
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {ε : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    (hweak : StationaryMFG.Hamiltonian.HypothesisWeakGrowth (d := d) H DpH)
    (hε : 0 < ε)
    (qε : StationaryMFG.InfimalConvolution.QEpsFamily d)
    (sel : StationaryMFG.InfimalConvolution.InfConvSelectorFamily
              (H := H) (DpH := DpH) hweak qε)
    (hMeas : StationaryMFG.Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (hmonBoundary : StationaryMFG.Hamiltonian.HypothesisMonotone (d := d) H DpH)
    (hdiffBoundary : StationaryMFG.Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    (hpowEps : StationaryMFG.Hamiltonian.HypothesisPowerGrowth (d := d)
                (StationaryMFG.InfimalConvolution.HdeltaPos hweak ε)
                (StationaryMFG.InfimalConvolution.DpHepsilonFam hweak qε ε))
    (hV_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal ((hpowEps.β + 1) / hpowEps.β)) V)
    [Fact (1 ≤ ENNReal.ofReal (hpowEps.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hpowEps.α * (hpowEps.β + 1) / hpowEps.β))]
    (ctx : AepsiUniformContextK (d := d) ε V
              (StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
              (StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
              (hpowEps.α * (hpowEps.β + 1) / hpowEps.β)
              (hpowEps.β + 1)
              ((hpowEps.β + 1) / hpowEps.β)
              ((hpowEps.α * (hpowEps.β + 1) / hpowEps.β)
                / (hpowEps.α * (hpowEps.β + 1) / hpowEps.β - 1)))
    (q : XBanach d (hpowEps.β + 1)
            (hpowEps.α * (hpowEps.β + 1) / hpowEps.β)) :
      q ∈ K0_Aepsi d (hpowEps.β + 1)
              (hpowEps.α * (hpowEps.β + 1) / hpowEps.β) →
      (∀ q' ∈ K_Aepsi d (hpowEps.β + 1)
                (hpowEps.α * (hpowEps.β + 1) / hpowEps.β),
          0 ≤ Aepsi_CLM_opK
                (γBarReal := hpowEps.α * (hpowEps.β + 1) / hpowEps.β)
                (βBarReal := hpowEps.β + 1)
                (βBarReal' := (hpowEps.β + 1) / hpowEps.β)
                (γBarReal' := (hpowEps.α * (hpowEps.β + 1) / hpowEps.β)
                                / (hpowEps.α * (hpowEps.β + 1) / hpowEps.β - 1))
                V (StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
                (StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
                ctx.auxHypsK ε q' (q' - q)) →
      ∀ (σ υ : (Fin d → ℝ) → ℝ)
        (φ : Fin d → (Fin d → ℝ) → ℝ),
        (∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)), 0 ≤ σ x) →
        Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpowEps.β + 1)) σ →
        Periodic.MemSobolevPer (d := d)
          (ENNReal.ofReal (hpowEps.α * (hpowEps.β + 1) / hpowEps.β)) υ →
        (∀ i, Periodic.MemLpPer (d := d)
                (ENNReal.ofReal (hpowEps.α * (hpowEps.β + 1) / hpowEps.β))
                (φ i)) →
        (∀ i, Periodic.HasWeakDerivPer (d := d) i υ (φ i)) →
          0 ≤ mfgOperatorEpsPair (V := V)
                (H := StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
                (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
                (hpowEps.α * (hpowEps.β + 1) / hpowEps.β) ε
                φ σ υ
                (fun i x => φ i x - DuOf q i x)
                (σ - mOf q)
                (υ - uOf q) := by
  -- H-side supply at `H := HdeltaK0`, all INTERNAL.
  have hcont_H_pm :=
    StationaryMFG.InfimalConvolution.HdeltaK0_continuousOn_H_pm_of_selectorFamily
      (H := H) (DpH := DpH) hweak qε sel (ε := ε) hε
  have hH_rc0 :=
    StationaryMFG.InfimalConvolution.HdeltaK0_rc0_of_selectorFamily
      (H := H) (DpH := DpH) hweak hmonBoundary qε sel hε
  -- DpH-side data (carrier-independent), from `hpowEps`.
  have hDpH_meas : Measurable
      (fun (xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ) =>
        StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε)
          xpm.1 xpm.2.1 xpm.2.2) :=
    hpowEps.measurable_DpH
  have hcont_DpH_pm :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ContinuousOn (fun (pm : (Fin d → ℝ) × ℝ) =>
            StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε) x pm.1 pm.2)
          {pm | 0 < pm.2} :=
    hpowEps.continuous_DpH_pm
  have hDpH_upper :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ∀ p m, 0 < m →
          ‖StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε) x p m‖
            ≤ hpowEps.C * (‖p‖ ^ (hpowEps.α - 1)
                + m ^ (hpowEps.β - hpowEps.β / hpowEps.α) + 1) :=
    hpowEps.DpH_upper
  exact
    StationaryMFG.Theorems.SimplePower.paperSection8_hMinty_transport_of_paperHypotheses_of_rc0_of_aeMeasH
      (V := V) (H := StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
      (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
      hpowEps.hα hpowEps.hβ hDpH_meas hcont_H_pm hcont_DpH_pm hDpH_upper hH_rc0
      (ε := ε)
      (fun q hq_K0 σ υ φ hσ_nn hσ_memLp hυ_memSob hφ_memLp =>
        StationaryMFG.Theorems.SimplePower.transportTendstoResidueOfBare_of_paperHypotheses_of_aeMeasH
          (V := V)
          (H := StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
          (H' := StationaryMFG.InfimalConvolution.HdeltaPos hweak ε)
          (DpH := StationaryMFG.InfimalConvolution.DpHepsilonFam hweak qε ε)
          hpowEps q σ υ φ
          hσ_memLp.aestronglyMeasurable
          hυ_memSob.1.aestronglyMeasurable
          (fun i => (hφ_memLp i).aestronglyMeasurable)
          hσ_memLp hυ_memSob.1 hφ_memLp hV_memLp hσ_nn
          (fun n => by
            filter_upwards [hσ_nn] with x hx
            have hpos : 0 < σ x + 1 / ((n : ℝ) + 1) := by
              have hone : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
              linarith
            exact StationaryMFG.InfimalConvolution.HdeltaK0_eq_HdeltaPos_of_pos
              hweak hpos)
          (fun n =>
            StationaryMFG.InfimalConvolution.aemeasurable_HdeltaK0_comp_of_rc0
              (H := H) (DpH := DpH) hweak hMeas hmonBoundary qε sel hε
              (Du := fun x i => φ i x)
              (m := fun x => σ x + 1 / ((n : ℝ) + 1))
              (aemeasurable_pi_iff.mpr
                  (fun i => (hφ_memLp i).aestronglyMeasurable.aemeasurable))
              ((hσ_memLp.aestronglyMeasurable.aemeasurable).add aemeasurable_const)
              (by
                filter_upwards [hσ_nn] with x hx
                have hone : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
                linarith))
          (StationaryMFG.InfimalConvolution.aemeasurable_HdeltaK0_comp_of_rc0
            (H := H) (DpH := DpH) hweak hMeas hmonBoundary qε sel hε
            (Du := fun x i => φ i x)
            (m := fun x => σ x)
            (aemeasurable_pi_iff.mpr
                (fun i => (hφ_memLp i).aestronglyMeasurable.aemeasurable))
            hσ_memLp.aestronglyMeasurable.aemeasurable
            hσ_nn))
      ctx q

open StationaryMFG.Theorems.SimplePower.Banach in
/-- **Substituted-pair `hMinty_transport` δ-limit slice, re-keyed on the
closed-cone carrier `HdeltaK0`, AE/bare-exponent variant** (paper
`thm:strongAepsi.delta`, D2c-2e-2b-transport retype rewire).

Additive `_ae` sibling of
`hMinty_transport_substitutedPair_of_paperHypotheses_of_rc0_HdeltaK0` that DROPS
the strict `hpowEps : HypothesisPowerGrowth (HdeltaPos …)` entirely. The exponent
type-indices are reindexed off the AE carrier's bare exponents `hweak.β`/`hweak.α`,
the constant is `CdeltaEps hweak ε`, and the three a.e. analytic estimates are
sourced from the AE carrier `hAE : HdeltaAEPowerEpsData hweak qε`
(`H_upper_pointwise_ae`/`lower_ae`/`DpH_upper_ae`), transferred from `Hdelta` to
the target carrier `HdeltaK0` on `{0<m}` via `HdeltaK0_eq_Hdelta_of_pos`. The
per-query bare residue supplier is the child-C `_ae` sibling
`transportTendstoResidueOfBare_of_paperHypotheses_of_aeMeasH_ae`.

GATE #1: NO `hpowEps`/`HypothesisPowerGrowth(HdeltaPos)`/`RegularityH(HdeltaPos)`/
`hFormPos`/`hqE_per`/`hInj`/`hSurj`/`qEofMinv`. The H-side data is supplied
INTERNALLY at `H := HdeltaK0`; the DpH-side data from
`measurable_DpHepsilonFam_of_selector`/`continuousOn_DpHepsilonFam_of_selector`;
the permitted riders are the AE carrier `hAE` + `hMeas`/`hmonBoundary`/`hdiffBoundary`/
`hweak`/`sel` + `hε1`. -/
theorem hMinty_transport_substitutedPair_of_paperHypotheses_of_rc0_HdeltaK0_ae
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {ε : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    (hweak : StationaryMFG.Hamiltonian.HypothesisWeakGrowth (d := d) H DpH)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (qε : StationaryMFG.InfimalConvolution.QEpsFamily d)
    (sel : StationaryMFG.InfimalConvolution.InfConvSelectorFamily
              (H := H) (DpH := DpH) hweak qε)
    (hMeas : StationaryMFG.Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (hmonBoundary : StationaryMFG.Hamiltonian.HypothesisMonotone (d := d) H DpH)
    (hdiffBoundary : StationaryMFG.Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    (hAE : StationaryMFG.InfimalConvolution.HdeltaAEPowerEpsData
              (H := H) (DpH := DpH) hweak qε)
    (hV_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal ((hweak.β + 1) / hweak.β)) V)
    [Fact (1 ≤ ENNReal.ofReal (hweak.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β))]
    (ctx : AepsiUniformContextK (d := d) ε V
              (StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
              (StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
              (hweak.α * (hweak.β + 1) / hweak.β)
              (hweak.β + 1)
              ((hweak.β + 1) / hweak.β)
              ((hweak.α * (hweak.β + 1) / hweak.β)
                / (hweak.α * (hweak.β + 1) / hweak.β - 1)))
    (q : XBanach d (hweak.β + 1)
            (hweak.α * (hweak.β + 1) / hweak.β)) :
      q ∈ K0_Aepsi d (hweak.β + 1)
              (hweak.α * (hweak.β + 1) / hweak.β) →
      (∀ q' ∈ K_Aepsi d (hweak.β + 1)
                (hweak.α * (hweak.β + 1) / hweak.β),
          0 ≤ Aepsi_CLM_opK
                (γBarReal := hweak.α * (hweak.β + 1) / hweak.β)
                (βBarReal := hweak.β + 1)
                (βBarReal' := (hweak.β + 1) / hweak.β)
                (γBarReal' := (hweak.α * (hweak.β + 1) / hweak.β)
                                / (hweak.α * (hweak.β + 1) / hweak.β - 1))
                V (StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
                (StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
                ctx.auxHypsK ε q' (q' - q)) →
      ∀ (σ υ : (Fin d → ℝ) → ℝ)
        (φ : Fin d → (Fin d → ℝ) → ℝ),
        (∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)), 0 ≤ σ x) →
        Periodic.MemLpPer (d := d) (ENNReal.ofReal (hweak.β + 1)) σ →
        Periodic.MemSobolevPer (d := d)
          (ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β)) υ →
        (∀ i, Periodic.MemLpPer (d := d)
                (ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β))
                (φ i)) →
        (∀ i, Periodic.HasWeakDerivPer (d := d) i υ (φ i)) →
          0 ≤ mfgOperatorEpsPair (V := V)
                (H := StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
                (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
                (hweak.α * (hweak.β + 1) / hweak.β) ε
                φ σ υ
                (fun i x => φ i x - DuOf q i x)
                (σ - mOf q)
                (υ - uOf q) := by
  -- Bare AE exponents/constant from the AE carrier.
  have hα : (1 : ℝ) < hweak.α := hweak.hα
  have hβ : (0 : ℝ) < hweak.β := hweak.hβ
  set Cε : ℝ := StationaryMFG.InfimalConvolution.CdeltaEps
                  (H := H) (DpH := DpH) hweak ε with hCε_def
  have hCε : (0 : ℝ) < Cε :=
    (StationaryMFG.InfimalConvolution.cdeltaEps_facts_upper
        (H := H) (DpH := DpH) hweak hε).1
  -- H-side supply at `H := HdeltaK0`, all INTERNAL.
  have hcont_H_pm :=
    StationaryMFG.InfimalConvolution.HdeltaK0_continuousOn_H_pm_of_selectorFamily
      (H := H) (DpH := DpH) hweak qε sel (ε := ε) hε
  have hH_rc0 :=
    StationaryMFG.InfimalConvolution.HdeltaK0_rc0_of_selectorFamily
      (H := H) (DpH := DpH) hweak hmonBoundary qε sel hε
  -- DpH-side data (carrier-independent), from the selector family.
  have hDpH_meas :=
    StationaryMFG.InfimalConvolution.measurable_DpHepsilonFam_of_selector
      (H := H) (DpH := DpH) hweak qε sel hMeas ε
  have hcont_DpH_pm :=
    StationaryMFG.InfimalConvolution.continuousOn_DpHepsilonFam_of_selector
      (H := H) (DpH := DpH) hweak qε sel hε
  -- The DpH upper a.e. estimate (general `p`, `0 < m`) from the AE carrier.
  have hDpH_upper : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
      ∀ p m, 0 < m →
        ‖StationaryMFG.InfimalConvolution.DpHepsilonFam hweak qε ε x p m‖
          ≤ Cε * (‖p‖ ^ (hweak.α - 1)
              + m ^ (hweak.β - hweak.β / hweak.α) + 1) :=
    hAE.DpH_upper_ae ε hε hε1
  exact
    StationaryMFG.Theorems.SimplePower.paperSection8_hMinty_transport_of_paperHypotheses_of_rc0_of_aeMeasH
      (V := V) (H := StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
      (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
      hα hβ hDpH_meas hcont_H_pm hcont_DpH_pm hDpH_upper hH_rc0
      (ε := ε)
      (fun q hq_K0 σ υ φ hσ_nn hσ_memLp hυ_memSob hφ_memLp =>
        -- The three a.e. estimates on `HdeltaK0` from `hAE` (Hdelta→HdeltaK0
        -- on {0<m} via `HdeltaK0_eq_Hdelta_of_pos`).
        have hH_upper_pt :
            ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
              ∀ p m, 0 < m →
                StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε x p m
                  ≤ Cε * (‖p‖ ^ hweak.α + 1) - (m ^ hweak.β) / Cε := by
          filter_upwards [hAE.H_upper_pointwise_ae ε hε hε1] with x hx
          intro p m hm
          rw [StationaryMFG.InfimalConvolution.HdeltaK0_eq_Hdelta_of_pos hweak hm]
          exact hx p m hm
        have hlower :
            ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
              ∀ p m, 0 < m →
                StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε x p m
                  ≥ (‖p‖ ^ hweak.α) / Cε - Cε * (m ^ hweak.β + 1) := by
          filter_upwards [hAE.lower_ae ε hε hε1] with x hx
          intro p m hm
          rw [StationaryMFG.InfimalConvolution.HdeltaK0_eq_Hdelta_of_pos hweak hm]
          exact hx p m hm
        StationaryMFG.Theorems.SimplePower.transportTendstoResidueOfBare_of_paperHypotheses_of_aeMeasH_ae
          (V := V)
          (H := StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
          (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
          (β := hweak.β) (α := hweak.α) (C := Cε)
          hα hβ hCε q σ υ φ
          hσ_memLp.aestronglyMeasurable
          hυ_memSob.1.aestronglyMeasurable
          (fun i => (hφ_memLp i).aestronglyMeasurable)
          hσ_memLp hυ_memSob.1 hφ_memLp hV_memLp hσ_nn
          hH_upper_pt hlower hDpH_upper
          (fun n =>
            StationaryMFG.InfimalConvolution.aemeasurable_HdeltaK0_comp_of_rc0
              (H := H) (DpH := DpH) hweak hMeas hmonBoundary qε sel hε
              (Du := fun x i => φ i x)
              (m := fun x => σ x + 1 / ((n : ℝ) + 1))
              (aemeasurable_pi_iff.mpr
                  (fun i => (hφ_memLp i).aestronglyMeasurable.aemeasurable))
              ((hσ_memLp.aestronglyMeasurable.aemeasurable).add aemeasurable_const)
              (by
                filter_upwards [hσ_nn] with x hx
                have hone : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
                linarith))
          (StationaryMFG.InfimalConvolution.aemeasurable_HdeltaK0_comp_of_rc0
            (H := H) (DpH := DpH) hweak hMeas hmonBoundary qε sel hε
            (Du := fun x i => φ i x)
            (m := fun x => σ x)
            (aemeasurable_pi_iff.mpr
                (fun i => (hφ_memLp i).aestronglyMeasurable.aemeasurable))
            hσ_memLp.aestronglyMeasurable.aemeasurable
            hσ_nn))
      ctx q

open StationaryMFG.Theorems.SimplePower.Banach in
/-- **G7c-1: refined-cone (`K0_Aepsi_W`/`K_Aepsi_W`) sibling of
`hMinty_transport_substitutedPair_of_paperHypotheses_of_rc0_HdeltaK0_ae`.**

W-form transport-family Minty producer. The transport test pair `(υ, φ)` is
user-supplied, so an extra weak-derivative tie `hWeak_υ` is required (as in the
set family). Body reuses the K-form residue prelude, evaluates the transport
bare residue bundle `r`, builds the same `hCont`, and finishes with
`hVIeps_transport_of_KAepsi_W_VI`. -/
theorem hMinty_transport_substitutedPair_of_paperHypotheses_of_rc0_HdeltaK0_W_ae
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {ε : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    (hweak : StationaryMFG.Hamiltonian.HypothesisWeakGrowth (d := d) H DpH)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (qε : StationaryMFG.InfimalConvolution.QEpsFamily d)
    (sel : StationaryMFG.InfimalConvolution.InfConvSelectorFamily
              (H := H) (DpH := DpH) hweak qε)
    (hMeas : StationaryMFG.Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (hmonBoundary : StationaryMFG.Hamiltonian.HypothesisMonotone (d := d) H DpH)
    (hdiffBoundary : StationaryMFG.Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    (hAE : StationaryMFG.InfimalConvolution.HdeltaAEPowerEpsData
              (H := H) (DpH := DpH) hweak qε)
    (hV_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal ((hweak.β + 1) / hweak.β)) V)
    [Fact (1 ≤ ENNReal.ofReal (hweak.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β))]
    (ctx : AepsiUniformContextK_W (d := d) ε V
              (StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
              (StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
              (hweak.α * (hweak.β + 1) / hweak.β)
              (hweak.β + 1)
              ((hweak.β + 1) / hweak.β)
              ((hweak.α * (hweak.β + 1) / hweak.β)
                / (hweak.α * (hweak.β + 1) / hweak.β - 1)))
    (q : XBanach d (hweak.β + 1)
            (hweak.α * (hweak.β + 1) / hweak.β)) :
      q ∈ K0_Aepsi_W d (hweak.β + 1)
              (hweak.α * (hweak.β + 1) / hweak.β) →
      (∀ q' ∈ K_Aepsi_W d (hweak.β + 1)
                (hweak.α * (hweak.β + 1) / hweak.β),
          0 ≤ Aepsi_CLM_opK
                (γBarReal := hweak.α * (hweak.β + 1) / hweak.β)
                (βBarReal := hweak.β + 1)
                (βBarReal' := (hweak.β + 1) / hweak.β)
                (γBarReal' := (hweak.α * (hweak.β + 1) / hweak.β)
                                / (hweak.α * (hweak.β + 1) / hweak.β - 1))
                V (StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
                (StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
                ctx.auxHypsK ε q' (q' - q)) →
      ∀ (σ υ : (Fin d → ℝ) → ℝ)
        (φ : Fin d → (Fin d → ℝ) → ℝ),
        (∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)), 0 ≤ σ x) →
        Periodic.MemLpPer (d := d) (ENNReal.ofReal (hweak.β + 1)) σ →
        Periodic.MemSobolevPer (d := d)
          (ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β)) υ →
        (∀ i, Periodic.MemLpPer (d := d)
                (ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β))
                (φ i)) →
        (∀ i, Periodic.HasWeakDerivPer (d := d) i υ (φ i)) →
          0 ≤ mfgOperatorEpsPair (V := V)
                (H := StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
                (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
                (hweak.α * (hweak.β + 1) / hweak.β) ε
                φ σ υ
                (fun i x => φ i x - DuOf q i x)
                (σ - mOf q)
                (υ - uOf q) := by
  have hα : (1 : ℝ) < hweak.α := hweak.hα
  have hβ : (0 : ℝ) < hweak.β := hweak.hβ
  set Cε : ℝ := StationaryMFG.InfimalConvolution.CdeltaEps
                  (H := H) (DpH := DpH) hweak ε with hCε_def
  have hCε : (0 : ℝ) < Cε :=
    (StationaryMFG.InfimalConvolution.cdeltaEps_facts_upper
        (H := H) (DpH := DpH) hweak hε).1
  have hcont_H_pm :=
    StationaryMFG.InfimalConvolution.HdeltaK0_continuousOn_H_pm_of_selectorFamily
      (H := H) (DpH := DpH) hweak qε sel (ε := ε) hε
  have hH_rc0 :=
    StationaryMFG.InfimalConvolution.HdeltaK0_rc0_of_selectorFamily
      (H := H) (DpH := DpH) hweak hmonBoundary qε sel hε
  have hDpH_meas :=
    StationaryMFG.InfimalConvolution.measurable_DpHepsilonFam_of_selector
      (H := H) (DpH := DpH) hweak qε sel hMeas ε
  have hcont_DpH_pm :=
    StationaryMFG.InfimalConvolution.continuousOn_DpHepsilonFam_of_selector
      (H := H) (DpH := DpH) hweak qε sel hε
  have hDpH_upper : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
      ∀ p m, 0 < m →
        ‖StationaryMFG.InfimalConvolution.DpHepsilonFam hweak qε ε x p m‖
          ≤ Cε * (‖p‖ ^ (hweak.α - 1)
              + m ^ (hweak.β - hweak.β / hweak.α) + 1) :=
    hAE.DpH_upper_ae ε hε hε1
  have hExp_paper :
      SimplePowerExponentFacts
          (SimplePowerExponentFacts.paperGammaBarReal hweak.α hweak.β)
          (SimplePowerExponentFacts.paperBetaBar hweak.β)
          (SimplePowerExponentFacts.paperGammaBar hweak.α hweak.β)
          (SimplePowerExponentFacts.paperBetaBarPrime hweak.β) :=
    SimplePowerExponentFacts.standardPaper hα hβ
  have hExp :
      SimplePowerExponentFacts (hweak.α * (hweak.β + 1) / hweak.β)
          (ENNReal.ofReal (hweak.β + 1))
          (ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β))
          (ENNReal.ofReal ((hweak.β + 1) / hweak.β)) := by
    have h1 :
        (SimplePowerExponentFacts.paperBetaBar hweak.β)
          = ENNReal.ofReal (hweak.β + 1) := by
      simp [SimplePowerExponentFacts.paperBetaBar]
    have h2 :
        (SimplePowerExponentFacts.paperGammaBar hweak.α hweak.β)
          = ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β) := by
      simp [SimplePowerExponentFacts.paperGammaBar]
    have h3 :
        (SimplePowerExponentFacts.paperBetaBarPrime hweak.β)
          = ENNReal.ofReal ((hweak.β + 1) / hweak.β) := by
      simp [SimplePowerExponentFacts.paperBetaBarPrime]
    have h4 :
        (SimplePowerExponentFacts.paperGammaBarReal hweak.α hweak.β)
          = hweak.α * (hweak.β + 1) / hweak.β := by
      simp [SimplePowerExponentFacts.paperGammaBarReal]
    have := hExp_paper
    rw [h1, h2, h3, h4] at this
    exact this
  intro hq_K0W hVI σ υ φ hσ_nn hσ_memLp hυ_memSob hφ_memLp hWeak_υ
  have hq_K0 : q ∈ K0_Aepsi d (hweak.β + 1)
                  (hweak.α * (hweak.β + 1) / hweak.β) :=
    K0_Aepsi_W_subset_K0_Aepsi d (hweak.β + 1)
      (hweak.α * (hweak.β + 1) / hweak.β) hq_K0W
  -- Transport bare residue bundle (residue closure body, identical to K-form).
  have hH_upper_pt :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ∀ p m, 0 < m →
          StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε x p m
            ≤ Cε * (‖p‖ ^ hweak.α + 1) - (m ^ hweak.β) / Cε := by
    filter_upwards [hAE.H_upper_pointwise_ae ε hε hε1] with x hx
    intro p m hm
    rw [StationaryMFG.InfimalConvolution.HdeltaK0_eq_Hdelta_of_pos hweak hm]
    exact hx p m hm
  have hlower :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ∀ p m, 0 < m →
          StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε x p m
            ≥ (‖p‖ ^ hweak.α) / Cε - Cε * (m ^ hweak.β + 1) := by
    filter_upwards [hAE.lower_ae ε hε hε1] with x hx
    intro p m hm
    rw [StationaryMFG.InfimalConvolution.HdeltaK0_eq_Hdelta_of_pos hweak hm]
    exact hx p m hm
  have r :=
    StationaryMFG.Theorems.SimplePower.transportTendstoResidueOfBare_of_paperHypotheses_of_aeMeasH_ae
      (V := V)
      (H := StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
      (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
      (β := hweak.β) (α := hweak.α) (C := Cε)
      hα hβ hCε q σ υ φ
      hσ_memLp.aestronglyMeasurable
      hυ_memSob.1.aestronglyMeasurable
      (fun i => (hφ_memLp i).aestronglyMeasurable)
      hσ_memLp hυ_memSob.1 hφ_memLp hV_memLp hσ_nn
      hH_upper_pt hlower hDpH_upper
      (fun n =>
        StationaryMFG.InfimalConvolution.aemeasurable_HdeltaK0_comp_of_rc0
          (H := H) (DpH := DpH) hweak hMeas hmonBoundary qε sel hε
          (Du := fun x i => φ i x)
          (m := fun x => σ x + 1 / ((n : ℝ) + 1))
          (aemeasurable_pi_iff.mpr
              (fun i => (hφ_memLp i).aestronglyMeasurable.aemeasurable))
          ((hσ_memLp.aestronglyMeasurable.aemeasurable).add aemeasurable_const)
          (by
            filter_upwards [hσ_nn] with x hx
            have hone : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
            linarith))
      (StationaryMFG.InfimalConvolution.aemeasurable_HdeltaK0_comp_of_rc0
        (H := H) (DpH := DpH) hweak hMeas hmonBoundary qε sel hε
        (Du := fun x i => φ i x)
        (m := fun x => σ x)
        (aemeasurable_pi_iff.mpr
            (fun i => (hφ_memLp i).aestronglyMeasurable.aemeasurable))
        hσ_memLp.aestronglyMeasurable.aemeasurable
        hσ_nn)
  have hCont :=
    mfgOperatorEpsPair_tendsto_transport_perturbation_of_paperHypotheses_of_aestronglyMeasurable_of_rc0_of_aeMeasH
      (ε := ε)
      (γBarReal := hweak.α * (hweak.β + 1) / hweak.β)
      (βBarReal := hweak.β + 1)
      (βBarReal' := (hweak.β + 1) / hweak.β)
      (γBarReal' := (hweak.α * (hweak.β + 1) / hweak.β)
                      / (hweak.α * (hweak.β + 1) / hweak.β - 1))
      (C := Cε) (α := hweak.α) (β := hweak.β)
      hα hβ hDpH_meas hcont_H_pm hcont_DpH_pm hDpH_upper hExp hH_rc0
      φ υ (uOf q) (DuOf q) (mOf q) V σ
      r.hσ r.hm r.hV r.hυ r.hu r.hφ r.hDu hσ_nn hσ_memLp
      r.hHcomp_ae_n r.hHcomp_ae_lim
      r.Gh r.Eh r.hGh_memLp r.hEh_memLp r.hGh_bd r.hEh_bd
      r.Gf r.Ef r.hGf_memLp r.hEf_memLp r.hGf_bd r.hEf_bd
      r.Gm r.Em r.hGm_memLp r.hEm_memLp r.hGm_bd r.hEm_bd
  exact hVIeps_transport_of_KAepsi_W_VI
    ctx.auxHypsK q hVI σ υ φ hσ_nn
    hσ_memLp hυ_memSob hφ_memLp hWeak_υ hCont

open StationaryMFG.Theorems.SimplePower.Banach in
/-- **Substituted-pair `hMinty_signed_user_probe` δ-limit slice** (paper
`thm:strongAepsi.delta`). Body replicated from
`paperSection8_hMinty_signed_user_probe_of_paperHypotheses_of_rc0` at the
generic `ε` (that producer is pinned at `paperEpsSeq k`). -/
theorem hMinty_signed_user_probe_substitutedPair_of_paperHypotheses_of_rc0
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {ε : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    (hweak : StationaryMFG.Hamiltonian.HypothesisWeakGrowth (d := d) H DpH)
    (qE : (Fin d → ℝ) × (Fin d → ℝ) × ℝ → (Fin d → ℝ))
    (hpowEps : StationaryMFG.Hamiltonian.HypothesisPowerGrowth (d := d)
                (StationaryMFG.InfimalConvolution.Hdelta hweak ε)
                (StationaryMFG.InfimalConvolution.DpHepsilon hweak qE))
    (hRegH : StationaryMFG.Hamiltonian.RegularityH (d := d)
                (StationaryMFG.InfimalConvolution.Hdelta hweak ε)
                (StationaryMFG.InfimalConvolution.DpHepsilon hweak qE))
    (hH_rc0 :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ∀ p : Fin d → ℝ,
          Filter.Tendsto
            (fun m : ℝ => StationaryMFG.InfimalConvolution.Hdelta hweak ε x p m)
            (nhdsWithin (0 : ℝ) (Set.Ioi 0))
            (nhds (StationaryMFG.InfimalConvolution.Hdelta hweak ε x p 0)))
    (hV_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal ((hpowEps.β + 1) / hpowEps.β)) V)
    [Fact (1 ≤ ENNReal.ofReal (hpowEps.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hpowEps.α * (hpowEps.β + 1) / hpowEps.β))]
    (ctx : AepsiUniformContextK (d := d) ε V
              (StationaryMFG.InfimalConvolution.Hdelta hweak ε)
              (StationaryMFG.InfimalConvolution.DpHepsilon hweak qE)
              (hpowEps.α * (hpowEps.β + 1) / hpowEps.β)
              (hpowEps.β + 1)
              ((hpowEps.β + 1) / hpowEps.β)
              ((hpowEps.α * (hpowEps.β + 1) / hpowEps.β)
                / (hpowEps.α * (hpowEps.β + 1) / hpowEps.β - 1)))
    (q : XBanach d (hpowEps.β + 1)
            (hpowEps.α * (hpowEps.β + 1) / hpowEps.β)) :
      q ∈ K0_Aepsi d (hpowEps.β + 1)
              (hpowEps.α * (hpowEps.β + 1) / hpowEps.β) →
      (∀ q' ∈ K_Aepsi d (hpowEps.β + 1)
                (hpowEps.α * (hpowEps.β + 1) / hpowEps.β),
          0 ≤ Aepsi_CLM_opK
                (γBarReal := hpowEps.α * (hpowEps.β + 1) / hpowEps.β)
                (βBarReal := hpowEps.β + 1)
                (βBarReal' := (hpowEps.β + 1) / hpowEps.β)
                (γBarReal' := (hpowEps.α * (hpowEps.β + 1) / hpowEps.β)
                                / (hpowEps.α * (hpowEps.β + 1) / hpowEps.β - 1))
                V (StationaryMFG.InfimalConvolution.Hdelta hweak ε)
                (StationaryMFG.InfimalConvolution.DpHepsilon hweak qE)
                ctx.auxHypsK ε q' (q' - q)) →
      ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)) S < ⊤ →
      ∀ (υ : (Fin d → ℝ) → ℝ)
        (Dυ : Fin d → (Fin d → ℝ) → ℝ),
        Periodic.MemSobolevPer (d := d)
          (ENNReal.ofReal (hpowEps.α * (hpowEps.β + 1) / hpowEps.β)) υ →
        (∀ i, Periodic.MemLpPer (d := d)
                (ENNReal.ofReal (hpowEps.α * (hpowEps.β + 1) / hpowEps.β))
                (Dυ i)) →
        (∀ i, Periodic.HasWeakDerivPer (d := d) i υ (Dυ i)) →
          0 ≤ mfgOperatorEpsPair (V := V)
                (H := StationaryMFG.InfimalConvolution.Hdelta hweak ε)
                (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak qE)
                (hpowEps.α * (hpowEps.β + 1) / hpowEps.β) ε
                Dυ
                (fun x => mOf q x + σ * mOf q x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                υ
                (fun i x => Dυ i x - DuOf q i x)
                (fun x => σ * mOf q x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                (fun x => υ x - uOf q x) := by
  intro hq_K0 hVI σ hσ S hS _hSfin υ Dυ hυ_memSob hDυ_memLp _hWeak_υ
  exact hVIeps_signed_user_probe_of_KAepsi_VI
    ctx.auxHypsK q hq_K0 hVI σ hσ S hS _hSfin υ Dυ hυ_memSob hDυ_memLp
    (StationaryMFG.Theorems.SimplePower.signedUserProbeCont_of_paperHypotheses_of_aestronglyMeasurable_of_rc0
      (V := V) (H := StationaryMFG.InfimalConvolution.Hdelta hweak ε)
      (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak qE)
      hpowEps hRegH hH_rc0 (ε := ε)
      q hq_K0 σ hσ S hS υ Dυ hυ_memSob.1 hDυ_memLp hV_memLp)

open StationaryMFG.Theorems.SimplePower.Banach in
/-- **Substituted-pair `hMinty_signed_user_triple` δ-limit slice** (paper
`thm:strongAepsi.delta`). Body replicated from
`paperSection8_hMinty_signed_user_triple_of_paperHypotheses_of_rc0` at the
generic `ε`. -/
theorem hMinty_signed_user_triple_substitutedPair_of_paperHypotheses_of_rc0
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {ε : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    (hweak : StationaryMFG.Hamiltonian.HypothesisWeakGrowth (d := d) H DpH)
    (qE : (Fin d → ℝ) × (Fin d → ℝ) × ℝ → (Fin d → ℝ))
    (hpowEps : StationaryMFG.Hamiltonian.HypothesisPowerGrowth (d := d)
                (StationaryMFG.InfimalConvolution.Hdelta hweak ε)
                (StationaryMFG.InfimalConvolution.DpHepsilon hweak qE))
    (hRegH : StationaryMFG.Hamiltonian.RegularityH (d := d)
                (StationaryMFG.InfimalConvolution.Hdelta hweak ε)
                (StationaryMFG.InfimalConvolution.DpHepsilon hweak qE))
    (hH_rc0 :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ∀ p : Fin d → ℝ,
          Filter.Tendsto
            (fun m : ℝ => StationaryMFG.InfimalConvolution.Hdelta hweak ε x p m)
            (nhdsWithin (0 : ℝ) (Set.Ioi 0))
            (nhds (StationaryMFG.InfimalConvolution.Hdelta hweak ε x p 0)))
    (hV_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal ((hpowEps.β + 1) / hpowEps.β)) V)
    [Fact (1 ≤ ENNReal.ofReal (hpowEps.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hpowEps.α * (hpowEps.β + 1) / hpowEps.β))]
    (ctx : AepsiUniformContextK (d := d) ε V
              (StationaryMFG.InfimalConvolution.Hdelta hweak ε)
              (StationaryMFG.InfimalConvolution.DpHepsilon hweak qE)
              (hpowEps.α * (hpowEps.β + 1) / hpowEps.β)
              (hpowEps.β + 1)
              ((hpowEps.β + 1) / hpowEps.β)
              ((hpowEps.α * (hpowEps.β + 1) / hpowEps.β)
                / (hpowEps.α * (hpowEps.β + 1) / hpowEps.β - 1)))
    (q : XBanach d (hpowEps.β + 1)
            (hpowEps.α * (hpowEps.β + 1) / hpowEps.β)) :
      q ∈ K0_Aepsi d (hpowEps.β + 1)
              (hpowEps.α * (hpowEps.β + 1) / hpowEps.β) →
      (∀ q' ∈ K_Aepsi d (hpowEps.β + 1)
                (hpowEps.α * (hpowEps.β + 1) / hpowEps.β),
          0 ≤ Aepsi_CLM_opK
                (γBarReal := hpowEps.α * (hpowEps.β + 1) / hpowEps.β)
                (βBarReal := hpowEps.β + 1)
                (βBarReal' := (hpowEps.β + 1) / hpowEps.β)
                (γBarReal' := (hpowEps.α * (hpowEps.β + 1) / hpowEps.β)
                                / (hpowEps.α * (hpowEps.β + 1) / hpowEps.β - 1))
                V (StationaryMFG.InfimalConvolution.Hdelta hweak ε)
                (StationaryMFG.InfimalConvolution.DpHepsilon hweak qE)
                ctx.auxHypsK ε q' (q' - q)) →
      ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)) S < ⊤ →
      ∀ (μ υ : (Fin d → ℝ) → ℝ)
        (Dυ : Fin d → (Fin d → ℝ) → ℝ),
        (∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)), 0 ≤ μ x) →
        Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpowEps.β + 1)) μ →
        Periodic.MemSobolevPer (d := d)
          (ENNReal.ofReal (hpowEps.α * (hpowEps.β + 1) / hpowEps.β)) υ →
        (∀ i, Periodic.MemLpPer (d := d)
                (ENNReal.ofReal (hpowEps.α * (hpowEps.β + 1) / hpowEps.β))
                (Dυ i)) →
        (∀ i, Periodic.HasWeakDerivPer (d := d) i υ (Dυ i)) →
          0 ≤ mfgOperatorEpsPair (V := V)
                (H := StationaryMFG.InfimalConvolution.Hdelta hweak ε)
                (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak qE)
                (hpowEps.α * (hpowEps.β + 1) / hpowEps.β) ε
                Dυ
                (fun x => μ x + σ * μ x *
                              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                υ
                (fun i x => Dυ i x - DuOf q i x)
                (fun x => (μ x + σ * μ x *
                              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                          - mOf q x)
                (fun x => υ x - uOf q x) := by
  intro hq_K0 hVI σ hσ S hS _hSfin μ υ Dυ hμ_nn hμ_memLp hυ_memSob hDυ_memLp _hWeak_υ
  exact hVIeps_signed_user_triple_of_KAepsi_VI
    ctx.auxHypsK q hq_K0 hVI σ hσ S hS _hSfin μ υ Dυ
    hμ_nn hμ_memLp hυ_memSob hDυ_memLp
    (StationaryMFG.Theorems.SimplePower.signedUserTripleCont_of_paperHypotheses_of_aestronglyMeasurable_of_rc0
      (V := V) (H := StationaryMFG.InfimalConvolution.Hdelta hweak ε)
      (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak qE)
      hpowEps hRegH hH_rc0 (ε := ε)
      q hq_K0 σ hσ S hS μ υ Dυ hμ_nn hμ_memLp hυ_memSob.1 hDυ_memLp hV_memLp)

open StationaryMFG.Theorems.SimplePower.Banach in
/-- **Substituted-pair `hMinty_signed_user_probe` δ-limit slice, re-keyed on the
closed-cone carrier `HdeltaK0`** (paper `thm:strongAepsi.delta`,
D2b-1c-ii-c4c-probe).

Additive `HdeltaK0`-keyed variant of
`hMinty_signed_user_probe_substitutedPair_of_paperHypotheses_of_rc0`. The
conclusion is keyed on `mfgOperatorEpsPair (H := HdeltaK0 hweak ε)`; the strict
entry above (on `Hdelta`) is left intact for its existing caller. This variant
carries NO loose `RegularityH (Hdelta …)` / `HypothesisHat0 (Hdelta …)` / raw-H
`hH_rc0` binder: the H-side data is supplied INTERNALLY at `H := HdeltaK0` from
`HdeltaK0_continuousOn_H_pm_of_selectorFamily`, `HdeltaK0_rc0_of_selectorFamily`, and
`aemeasurable_HdeltaK0_comp_of_rc0`, and the bare residue supplier reuses the
TRANSPORT keystone `transportTendstoResidueOfBare_of_paperHypotheses_of_aeMeasH`
at the probe transport density `σ_fn := mOf q + σ·mOf q·𝟙_S` over the strict
`HdeltaPos`-keyed dominators (the probe `_of_aeMeasH` producer routes through
the transport keystone). The GATE-permitted riders are
`hMeas`/`hmonBoundary`/`hdiffBoundary` and the `RegularityH (HdeltaPos)`-class supply
`hpowEps`. -/
theorem hMinty_signed_user_probe_substitutedPair_of_paperHypotheses_of_rc0_HdeltaK0
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {ε : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    (hweak : StationaryMFG.Hamiltonian.HypothesisWeakGrowth (d := d) H DpH)
    (hε : 0 < ε)
    (qε : StationaryMFG.InfimalConvolution.QEpsFamily d)
    (sel : StationaryMFG.InfimalConvolution.InfConvSelectorFamily
              (H := H) (DpH := DpH) hweak qε)
    (hMeas : StationaryMFG.Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (hmonBoundary : StationaryMFG.Hamiltonian.HypothesisMonotone (d := d) H DpH)
    (hdiffBoundary : StationaryMFG.Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    (hpowEps : StationaryMFG.Hamiltonian.HypothesisPowerGrowth (d := d)
                (StationaryMFG.InfimalConvolution.HdeltaPos hweak ε)
                (StationaryMFG.InfimalConvolution.DpHepsilonFam hweak qε ε))
    (hV_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal ((hpowEps.β + 1) / hpowEps.β)) V)
    [Fact (1 ≤ ENNReal.ofReal (hpowEps.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hpowEps.α * (hpowEps.β + 1) / hpowEps.β))]
    (ctx : AepsiUniformContextK (d := d) ε V
              (StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
              (StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
              (hpowEps.α * (hpowEps.β + 1) / hpowEps.β)
              (hpowEps.β + 1)
              ((hpowEps.β + 1) / hpowEps.β)
              ((hpowEps.α * (hpowEps.β + 1) / hpowEps.β)
                / (hpowEps.α * (hpowEps.β + 1) / hpowEps.β - 1)))
    (q : XBanach d (hpowEps.β + 1)
            (hpowEps.α * (hpowEps.β + 1) / hpowEps.β)) :
      q ∈ K0_Aepsi d (hpowEps.β + 1)
              (hpowEps.α * (hpowEps.β + 1) / hpowEps.β) →
      (∀ q' ∈ K_Aepsi d (hpowEps.β + 1)
                (hpowEps.α * (hpowEps.β + 1) / hpowEps.β),
          0 ≤ Aepsi_CLM_opK
                (γBarReal := hpowEps.α * (hpowEps.β + 1) / hpowEps.β)
                (βBarReal := hpowEps.β + 1)
                (βBarReal' := (hpowEps.β + 1) / hpowEps.β)
                (γBarReal' := (hpowEps.α * (hpowEps.β + 1) / hpowEps.β)
                                / (hpowEps.α * (hpowEps.β + 1) / hpowEps.β - 1))
                V (StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
                (StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
                ctx.auxHypsK ε q' (q' - q)) →
      ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)) S < ⊤ →
      ∀ (υ : (Fin d → ℝ) → ℝ)
        (Dυ : Fin d → (Fin d → ℝ) → ℝ),
        Periodic.MemSobolevPer (d := d)
          (ENNReal.ofReal (hpowEps.α * (hpowEps.β + 1) / hpowEps.β)) υ →
        (∀ i, Periodic.MemLpPer (d := d)
                (ENNReal.ofReal (hpowEps.α * (hpowEps.β + 1) / hpowEps.β))
                (Dυ i)) →
        (∀ i, Periodic.HasWeakDerivPer (d := d) i υ (Dυ i)) →
          0 ≤ mfgOperatorEpsPair (V := V)
                (H := StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
                (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
                (hpowEps.α * (hpowEps.β + 1) / hpowEps.β) ε
                Dυ
                (fun x => mOf q x + σ * mOf q x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                υ
                (fun i x => Dυ i x - DuOf q i x)
                (fun x => σ * mOf q x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                (fun x => υ x - uOf q x) := by
  -- H-side supply at `H := HdeltaK0`, all INTERNAL.
  have hcont_H_pm :=
    StationaryMFG.InfimalConvolution.HdeltaK0_continuousOn_H_pm_of_selectorFamily
      (H := H) (DpH := DpH) hweak qε sel (ε := ε) hε
  have hH_rc0 :=
    StationaryMFG.InfimalConvolution.HdeltaK0_rc0_of_selectorFamily
      (H := H) (DpH := DpH) hweak hmonBoundary qε sel hε
  -- DpH-side data (carrier-independent), from `hpowEps`.
  have hDpH_meas : Measurable
      (fun (xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ) =>
        StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε)
          xpm.1 xpm.2.1 xpm.2.2) :=
    hpowEps.measurable_DpH
  have hcont_DpH_pm :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ContinuousOn (fun (pm : (Fin d → ℝ) × ℝ) =>
            StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε) x pm.1 pm.2)
          {pm | 0 < pm.2} :=
    hpowEps.continuous_DpH_pm
  have hDpH_upper :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ∀ p m, 0 < m →
          ‖StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε) x p m‖
            ≤ hpowEps.C * (‖p‖ ^ (hpowEps.α - 1)
                + m ^ (hpowEps.β - hpowEps.β / hpowEps.α) + 1) :=
    hpowEps.DpH_upper
  exact
    StationaryMFG.Theorems.SimplePower.paperSection8_hMinty_signed_user_probe_of_paperHypotheses_of_rc0_of_aeMeasH
      (V := V) (H := StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
      (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
      hpowEps.hα hpowEps.hβ hDpH_meas hcont_H_pm hcont_DpH_pm hDpH_upper hH_rc0
      (ε := ε)
      (fun q hq_K0 σ hσ S hS _hSfin υ Dυ hυ_memSob hDυ_memLp =>
        -- Build the probe transport density `σ_fn := mOf q + σ·mOf q·𝟙_S`,
        -- with its a.e.-nonnegativity and `L^{β+1}` membership (from `mOf q`),
        -- then supply the transport residue at `HdeltaK0` over `HdeltaPos`.
        have hm_memLp : Periodic.MemLpPer (d := d)
            (ENNReal.ofReal (hpowEps.β + 1))
            (StationaryMFG.Theorems.SimplePower.Banach.mOf q) :=
          StationaryMFG.Theorems.SimplePower.Banach.memLpPer_of_lpPer (d := d) q.1
        have hm_nn : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
            0 ≤ StationaryMFG.Theorems.SimplePower.Banach.mOf q x :=
          mem_K0_Aepsi_iff.mp hq_K0
        have hσ_fn_nn :
            ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
              0 ≤ StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
                    σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
          filter_upwards [hm_nn] with x hxnn
          have hfactor_nn :
              0 ≤ 1 + σ * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
            have hσ_lb : (-1 : ℝ) ≤ σ := by rcases hσ with h | h <;> simp [h]
            by_cases hxS : x ∈ S
            · rw [Set.indicator_of_mem hxS]; simp only [mul_one]; linarith
            · rw [Set.indicator_of_notMem hxS]; simp
          have h_eq :
              StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
                  σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                = StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                    (1 + σ * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
            ring
          rw [h_eq]; exact mul_nonneg hxnn hfactor_nn
        have hsmul : Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpowEps.β + 1))
            (fun x => σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x) := by
          have := hm_memLp.const_smul (𝕜 := ℝ) σ
          have heq : (σ • (StationaryMFG.Theorems.SimplePower.Banach.mOf q :
                        (Fin d → ℝ) → ℝ))
                      = fun x =>
                          σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x :=
            rfl
          rw [heq] at this; exact this
        have hSind : Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpowEps.β + 1))
            (S.indicator
              (fun x => σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x)) :=
          Periodic.MemLp.toMemLpPer (MeasureTheory.MemLp.indicator hS.nullMeasurableSet hsmul.toMemLp)
        have hInd_funEq :
            (S.indicator
                (fun x => σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x) :
                (Fin d → ℝ) → ℝ)
              = fun x => σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
          funext x
          by_cases hx : x ∈ S
          · simp [Set.indicator_of_mem hx]
          · simp [Set.indicator_of_notMem hx]
        have hInd_memLp : Periodic.MemLpPer (d := d)
            (ENNReal.ofReal (hpowEps.β + 1))
            (fun x => σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
          rw [← hInd_funEq]; exact hSind
        have hσ_fn_memLp : Periodic.MemLpPer (d := d)
            (ENNReal.ofReal (hpowEps.β + 1))
            (fun x => StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
                σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) :=
          Periodic.MemLpPer.add hm_memLp hInd_memLp
        StationaryMFG.Theorems.SimplePower.transportTendstoResidueOfBare_of_paperHypotheses_of_aeMeasH
          (V := V)
          (H := StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
          (H' := StationaryMFG.InfimalConvolution.HdeltaPos hweak ε)
          (DpH := StationaryMFG.InfimalConvolution.DpHepsilonFam hweak qε ε)
          hpowEps q
          (fun x => StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
              σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          υ Dυ
          hσ_fn_memLp.aestronglyMeasurable
          hυ_memSob.1.aestronglyMeasurable
          (fun i => (hDυ_memLp i).aestronglyMeasurable)
          hσ_fn_memLp hυ_memSob.1 hDυ_memLp hV_memLp hσ_fn_nn
          (fun n => by
            filter_upwards [hσ_fn_nn] with x hx
            have hpos : 0 < StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
                  σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                + 1 / ((n : ℝ) + 1) := by
              have hone : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
              linarith
            exact StationaryMFG.InfimalConvolution.HdeltaK0_eq_HdeltaPos_of_pos
              hweak hpos)
          (fun n =>
            StationaryMFG.InfimalConvolution.aemeasurable_HdeltaK0_comp_of_rc0
              (H := H) (DpH := DpH) hweak hMeas hmonBoundary qε sel hε
              (Du := fun x i => Dυ i x)
              (m := fun x => StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
                  σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                + 1 / ((n : ℝ) + 1))
              (aemeasurable_pi_iff.mpr
                  (fun i => (hDυ_memLp i).aestronglyMeasurable.aemeasurable))
              (hσ_fn_memLp.aestronglyMeasurable.aemeasurable.add aemeasurable_const)
              (by
                filter_upwards [hσ_fn_nn] with x hx
                have hone : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
                linarith))
          (StationaryMFG.InfimalConvolution.aemeasurable_HdeltaK0_comp_of_rc0
            (H := H) (DpH := DpH) hweak hMeas hmonBoundary qε sel hε
            (Du := fun x i => Dυ i x)
            (m := fun x => StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
                σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
            (aemeasurable_pi_iff.mpr
                (fun i => (hDυ_memLp i).aestronglyMeasurable.aemeasurable))
            hσ_fn_memLp.aestronglyMeasurable.aemeasurable
            hσ_fn_nn))
      ctx q

open StationaryMFG.Theorems.SimplePower.Banach in
/-- **Substituted-pair `hMinty_signed_user_triple` δ-limit slice, re-keyed on the
closed-cone carrier `HdeltaK0`** (paper `thm:strongAepsi.delta`,
D2b-1c-ii-c4c-triple).

Additive `HdeltaK0`-keyed variant of
`hMinty_signed_user_triple_substitutedPair_of_paperHypotheses_of_rc0`. The
conclusion is keyed on `mfgOperatorEpsPair (H := HdeltaK0 hweak ε)`; the strict
entry above (on `Hdelta`) is left intact for its existing caller. This variant
carries NO loose `RegularityH (Hdelta …)` / `HypothesisHat0 (Hdelta …)` / raw-H
`hH_rc0` binder: the H-side data is supplied INTERNALLY at `H := HdeltaK0` from
`HdeltaK0_continuousOn_H_pm_of_selectorFamily`, `HdeltaK0_rc0_of_selectorFamily`, and
`aemeasurable_HdeltaK0_comp_of_rc0`, and the bare residue supplier reuses the
TRANSPORT keystone `transportTendstoResidueOfBare_of_paperHypotheses_of_aeMeasH`
at the triple transport density `σ_fn := μ + σ·μ·𝟙_S` over the strict
`HdeltaPos`-keyed dominators (the triple `_of_aeMeasH` producer routes through
the transport keystone). The GATE-permitted riders are
`hMeas`/`hmonBoundary`/`hdiffBoundary` and the `RegularityH (HdeltaPos)`-class supply
`hpowEps`. -/
theorem hMinty_signed_user_triple_substitutedPair_of_paperHypotheses_of_rc0_HdeltaK0
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {ε : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    (hweak : StationaryMFG.Hamiltonian.HypothesisWeakGrowth (d := d) H DpH)
    (hε : 0 < ε)
    (qε : StationaryMFG.InfimalConvolution.QEpsFamily d)
    (sel : StationaryMFG.InfimalConvolution.InfConvSelectorFamily
              (H := H) (DpH := DpH) hweak qε)
    (hMeas : StationaryMFG.Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (hmonBoundary : StationaryMFG.Hamiltonian.HypothesisMonotone (d := d) H DpH)
    (hdiffBoundary : StationaryMFG.Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    (hpowEps : StationaryMFG.Hamiltonian.HypothesisPowerGrowth (d := d)
                (StationaryMFG.InfimalConvolution.HdeltaPos hweak ε)
                (StationaryMFG.InfimalConvolution.DpHepsilonFam hweak qε ε))
    (hV_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal ((hpowEps.β + 1) / hpowEps.β)) V)
    [Fact (1 ≤ ENNReal.ofReal (hpowEps.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hpowEps.α * (hpowEps.β + 1) / hpowEps.β))]
    (ctx : AepsiUniformContextK (d := d) ε V
              (StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
              (StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
              (hpowEps.α * (hpowEps.β + 1) / hpowEps.β)
              (hpowEps.β + 1)
              ((hpowEps.β + 1) / hpowEps.β)
              ((hpowEps.α * (hpowEps.β + 1) / hpowEps.β)
                / (hpowEps.α * (hpowEps.β + 1) / hpowEps.β - 1)))
    (q : XBanach d (hpowEps.β + 1)
            (hpowEps.α * (hpowEps.β + 1) / hpowEps.β)) :
      q ∈ K0_Aepsi d (hpowEps.β + 1)
              (hpowEps.α * (hpowEps.β + 1) / hpowEps.β) →
      (∀ q' ∈ K_Aepsi d (hpowEps.β + 1)
                (hpowEps.α * (hpowEps.β + 1) / hpowEps.β),
          0 ≤ Aepsi_CLM_opK
                (γBarReal := hpowEps.α * (hpowEps.β + 1) / hpowEps.β)
                (βBarReal := hpowEps.β + 1)
                (βBarReal' := (hpowEps.β + 1) / hpowEps.β)
                (γBarReal' := (hpowEps.α * (hpowEps.β + 1) / hpowEps.β)
                                / (hpowEps.α * (hpowEps.β + 1) / hpowEps.β - 1))
                V (StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
                (StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
                ctx.auxHypsK ε q' (q' - q)) →
      ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)) S < ⊤ →
      ∀ (μ υ : (Fin d → ℝ) → ℝ)
        (Dυ : Fin d → (Fin d → ℝ) → ℝ),
        (∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)), 0 ≤ μ x) →
        Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpowEps.β + 1)) μ →
        Periodic.MemSobolevPer (d := d)
          (ENNReal.ofReal (hpowEps.α * (hpowEps.β + 1) / hpowEps.β)) υ →
        (∀ i, Periodic.MemLpPer (d := d)
                (ENNReal.ofReal (hpowEps.α * (hpowEps.β + 1) / hpowEps.β))
                (Dυ i)) →
        (∀ i, Periodic.HasWeakDerivPer (d := d) i υ (Dυ i)) →
          0 ≤ mfgOperatorEpsPair (V := V)
                (H := StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
                (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
                (hpowEps.α * (hpowEps.β + 1) / hpowEps.β) ε
                Dυ
                (fun x => μ x + σ * μ x *
                              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                υ
                (fun i x => Dυ i x - DuOf q i x)
                (fun x => (μ x + σ * μ x *
                              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                          - mOf q x)
                (fun x => υ x - uOf q x) := by
  -- H-side supply at `H := HdeltaK0`, all INTERNAL.
  have hcont_H_pm :=
    StationaryMFG.InfimalConvolution.HdeltaK0_continuousOn_H_pm_of_selectorFamily
      (H := H) (DpH := DpH) hweak qε sel (ε := ε) hε
  have hH_rc0 :=
    StationaryMFG.InfimalConvolution.HdeltaK0_rc0_of_selectorFamily
      (H := H) (DpH := DpH) hweak hmonBoundary qε sel hε
  -- DpH-side data (carrier-independent), from `hpowEps`.
  have hDpH_meas : Measurable
      (fun (xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ) =>
        StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε)
          xpm.1 xpm.2.1 xpm.2.2) :=
    hpowEps.measurable_DpH
  have hcont_DpH_pm :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ContinuousOn (fun (pm : (Fin d → ℝ) × ℝ) =>
            StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε) x pm.1 pm.2)
          {pm | 0 < pm.2} :=
    hpowEps.continuous_DpH_pm
  have hDpH_upper :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ∀ p m, 0 < m →
          ‖StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε) x p m‖
            ≤ hpowEps.C * (‖p‖ ^ (hpowEps.α - 1)
                + m ^ (hpowEps.β - hpowEps.β / hpowEps.α) + 1) :=
    hpowEps.DpH_upper
  exact
    StationaryMFG.Theorems.SimplePower.paperSection8_hMinty_signed_user_triple_of_paperHypotheses_of_rc0_of_aeMeasH
      (V := V) (H := StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
      (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
      hpowEps.hα hpowEps.hβ hDpH_meas hcont_H_pm hcont_DpH_pm hDpH_upper hH_rc0
      (ε := ε)
      (fun q _hq_K0 σ hσ S hS _hSfin μ υ Dυ hμ_nn hμ_memLp hυ_memSob hDυ_memLp =>
        -- Build the triple transport density `σ_fn := μ + σ·μ·𝟙_S`, with its
        -- a.e.-nonnegativity and `L^{β+1}` membership (from the user `μ`), then
        -- supply the transport residue at `HdeltaK0` over `HdeltaPos`.
        have hσ_fn_nn :
            ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
              0 ≤ μ x + σ * μ x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
          filter_upwards [hμ_nn] with x hxnn
          have hfactor_nn :
              0 ≤ 1 + σ * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
            have hσ_lb : (-1 : ℝ) ≤ σ := by rcases hσ with h | h <;> simp [h]
            by_cases hxS : x ∈ S
            · rw [Set.indicator_of_mem hxS]; simp only [mul_one]; linarith
            · rw [Set.indicator_of_notMem hxS]; simp
          have h_eq :
              μ x + σ * μ x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                = μ x *
                    (1 + σ * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
            ring
          rw [h_eq]; exact mul_nonneg hxnn hfactor_nn
        have hsmul : Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpowEps.β + 1))
            (fun x => σ * μ x) := by
          have := hμ_memLp.const_smul (𝕜 := ℝ) σ
          have heq : (σ • (μ : (Fin d → ℝ) → ℝ)) = fun x => σ * μ x := rfl
          rw [heq] at this; exact this
        have hSind : Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpowEps.β + 1))
            (S.indicator (fun x => σ * μ x)) :=
          Periodic.MemLp.toMemLpPer (MeasureTheory.MemLp.indicator hS.nullMeasurableSet hsmul.toMemLp)
        have hInd_funEq :
            (S.indicator (fun x => σ * μ x) : (Fin d → ℝ) → ℝ)
              = fun x => σ * μ x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
          funext x
          by_cases hx : x ∈ S
          · simp [Set.indicator_of_mem hx]
          · simp [Set.indicator_of_notMem hx]
        have hInd_memLp : Periodic.MemLpPer (d := d)
            (ENNReal.ofReal (hpowEps.β + 1))
            (fun x => σ * μ x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
          rw [← hInd_funEq]; exact hSind
        have hσ_fn_memLp : Periodic.MemLpPer (d := d)
            (ENNReal.ofReal (hpowEps.β + 1))
            (fun x => μ x + σ * μ x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) :=
          Periodic.MemLpPer.add hμ_memLp hInd_memLp
        StationaryMFG.Theorems.SimplePower.transportTendstoResidueOfBare_of_paperHypotheses_of_aeMeasH
          (V := V)
          (H := StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
          (H' := StationaryMFG.InfimalConvolution.HdeltaPos hweak ε)
          (DpH := StationaryMFG.InfimalConvolution.DpHepsilonFam hweak qε ε)
          hpowEps q
          (fun x => μ x + σ * μ x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          υ Dυ
          hσ_fn_memLp.aestronglyMeasurable
          hυ_memSob.1.aestronglyMeasurable
          (fun i => (hDυ_memLp i).aestronglyMeasurable)
          hσ_fn_memLp hυ_memSob.1 hDυ_memLp hV_memLp hσ_fn_nn
          (fun n => by
            filter_upwards [hσ_fn_nn] with x hx
            have hpos : 0 < μ x + σ * μ x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                + 1 / ((n : ℝ) + 1) := by
              have hone : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
              linarith
            exact StationaryMFG.InfimalConvolution.HdeltaK0_eq_HdeltaPos_of_pos
              hweak hpos)
          (fun n =>
            StationaryMFG.InfimalConvolution.aemeasurable_HdeltaK0_comp_of_rc0
              (H := H) (DpH := DpH) hweak hMeas hmonBoundary qε sel hε
              (Du := fun x i => Dυ i x)
              (m := fun x => μ x + σ * μ x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                + 1 / ((n : ℝ) + 1))
              (aemeasurable_pi_iff.mpr
                  (fun i => (hDυ_memLp i).aestronglyMeasurable.aemeasurable))
              (hσ_fn_memLp.aestronglyMeasurable.aemeasurable.add aemeasurable_const)
              (by
                filter_upwards [hσ_fn_nn] with x hx
                have hone : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
                linarith))
          (StationaryMFG.InfimalConvolution.aemeasurable_HdeltaK0_comp_of_rc0
            (H := H) (DpH := DpH) hweak hMeas hmonBoundary qε sel hε
            (Du := fun x i => Dυ i x)
            (m := fun x => μ x + σ * μ x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
            (aemeasurable_pi_iff.mpr
                (fun i => (hDυ_memLp i).aestronglyMeasurable.aemeasurable))
            hσ_fn_memLp.aestronglyMeasurable.aemeasurable
            hσ_fn_nn))
      ctx q

open StationaryMFG.Theorems.SimplePower.Banach in
/-- **Substituted-pair `hMinty_signed_user_probe` δ-limit slice, re-keyed on the
closed-cone carrier `HdeltaK0`, AE/bare-exponent variant** (paper
`thm:strongAepsi.delta`, D2c-2e-2c-probe retype rewire).

Additive `_ae` sibling of
`hMinty_signed_user_probe_substitutedPair_of_paperHypotheses_of_rc0_HdeltaK0` that
DROPS the strict `hpowEps : HypothesisPowerGrowth (HdeltaPos …)` entirely. The
exponent type-indices are reindexed off the AE carrier's bare exponents
`hweak.β`/`hweak.α`, the constant is `CdeltaEps hweak ε`, and the three a.e.
analytic estimates are sourced from the AE carrier
`hAE : HdeltaAEPowerEpsData hweak qε` (`H_upper_pointwise_ae`/`lower_ae`/
`DpH_upper_ae`), transferred from `Hdelta` to the target carrier `HdeltaK0` on
`{0<m}` via `HdeltaK0_eq_Hdelta_of_pos`. The per-query bare residue supplier is
the child-C `_ae` sibling
`transportTendstoResidueOfBare_of_paperHypotheses_of_aeMeasH_ae` at the probe
transport density `σ_fn := mOf q + σ·mOf q·𝟙_S`.

GATE #1: NO `hpowEps`/`HypothesisPowerGrowth(HdeltaPos)`/`RegularityH(HdeltaPos)`/
`hFormPos`/`hqE_per`/`hInj`/`hSurj`/`qEofMinv`. The H-side data is supplied
INTERNALLY at `H := HdeltaK0`; the DpH-side data from
`measurable_DpHepsilonFam_of_selector`/`continuousOn_DpHepsilonFam_of_selector`;
the permitted riders are the AE carrier `hAE` + `hMeas`/`hmonBoundary`/`hdiffBoundary`/
`hweak`/`sel` + `hε1`. -/
theorem hMinty_signed_user_probe_substitutedPair_of_paperHypotheses_of_rc0_HdeltaK0_ae
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {ε : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    (hweak : StationaryMFG.Hamiltonian.HypothesisWeakGrowth (d := d) H DpH)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (qε : StationaryMFG.InfimalConvolution.QEpsFamily d)
    (sel : StationaryMFG.InfimalConvolution.InfConvSelectorFamily
              (H := H) (DpH := DpH) hweak qε)
    (hMeas : StationaryMFG.Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (hmonBoundary : StationaryMFG.Hamiltonian.HypothesisMonotone (d := d) H DpH)
    (hdiffBoundary : StationaryMFG.Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    (hAE : StationaryMFG.InfimalConvolution.HdeltaAEPowerEpsData
              (H := H) (DpH := DpH) hweak qε)
    (hV_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal ((hweak.β + 1) / hweak.β)) V)
    [Fact (1 ≤ ENNReal.ofReal (hweak.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β))]
    (ctx : AepsiUniformContextK (d := d) ε V
              (StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
              (StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
              (hweak.α * (hweak.β + 1) / hweak.β)
              (hweak.β + 1)
              ((hweak.β + 1) / hweak.β)
              ((hweak.α * (hweak.β + 1) / hweak.β)
                / (hweak.α * (hweak.β + 1) / hweak.β - 1)))
    (q : XBanach d (hweak.β + 1)
            (hweak.α * (hweak.β + 1) / hweak.β)) :
      q ∈ K0_Aepsi d (hweak.β + 1)
              (hweak.α * (hweak.β + 1) / hweak.β) →
      (∀ q' ∈ K_Aepsi d (hweak.β + 1)
                (hweak.α * (hweak.β + 1) / hweak.β),
          0 ≤ Aepsi_CLM_opK
                (γBarReal := hweak.α * (hweak.β + 1) / hweak.β)
                (βBarReal := hweak.β + 1)
                (βBarReal' := (hweak.β + 1) / hweak.β)
                (γBarReal' := (hweak.α * (hweak.β + 1) / hweak.β)
                                / (hweak.α * (hweak.β + 1) / hweak.β - 1))
                V (StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
                (StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
                ctx.auxHypsK ε q' (q' - q)) →
      ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)) S < ⊤ →
      ∀ (υ : (Fin d → ℝ) → ℝ)
        (Dυ : Fin d → (Fin d → ℝ) → ℝ),
        Periodic.MemSobolevPer (d := d)
          (ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β)) υ →
        (∀ i, Periodic.MemLpPer (d := d)
                (ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β))
                (Dυ i)) →
        (∀ i, Periodic.HasWeakDerivPer (d := d) i υ (Dυ i)) →
          0 ≤ mfgOperatorEpsPair (V := V)
                (H := StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
                (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
                (hweak.α * (hweak.β + 1) / hweak.β) ε
                Dυ
                (fun x => mOf q x + σ * mOf q x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                υ
                (fun i x => Dυ i x - DuOf q i x)
                (fun x => σ * mOf q x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                (fun x => υ x - uOf q x) := by
  -- Bare AE exponents/constant from the AE carrier.
  have hα : (1 : ℝ) < hweak.α := hweak.hα
  have hβ : (0 : ℝ) < hweak.β := hweak.hβ
  set Cε : ℝ := StationaryMFG.InfimalConvolution.CdeltaEps
                  (H := H) (DpH := DpH) hweak ε with hCε_def
  have hCε : (0 : ℝ) < Cε :=
    (StationaryMFG.InfimalConvolution.cdeltaEps_facts_upper
        (H := H) (DpH := DpH) hweak hε).1
  -- H-side supply at `H := HdeltaK0`, all INTERNAL.
  have hcont_H_pm :=
    StationaryMFG.InfimalConvolution.HdeltaK0_continuousOn_H_pm_of_selectorFamily
      (H := H) (DpH := DpH) hweak qε sel (ε := ε) hε
  have hH_rc0 :=
    StationaryMFG.InfimalConvolution.HdeltaK0_rc0_of_selectorFamily
      (H := H) (DpH := DpH) hweak hmonBoundary qε sel hε
  -- DpH-side data (carrier-independent), from the selector family.
  have hDpH_meas :=
    StationaryMFG.InfimalConvolution.measurable_DpHepsilonFam_of_selector
      (H := H) (DpH := DpH) hweak qε sel hMeas ε
  have hcont_DpH_pm :=
    StationaryMFG.InfimalConvolution.continuousOn_DpHepsilonFam_of_selector
      (H := H) (DpH := DpH) hweak qε sel hε
  -- The DpH upper a.e. estimate (general `p`, `0 < m`) from the AE carrier.
  have hDpH_upper : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
      ∀ p m, 0 < m →
        ‖StationaryMFG.InfimalConvolution.DpHepsilonFam hweak qε ε x p m‖
          ≤ Cε * (‖p‖ ^ (hweak.α - 1)
              + m ^ (hweak.β - hweak.β / hweak.α) + 1) :=
    hAE.DpH_upper_ae ε hε hε1
  exact
    StationaryMFG.Theorems.SimplePower.paperSection8_hMinty_signed_user_probe_of_paperHypotheses_of_rc0_of_aeMeasH
      (V := V) (H := StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
      (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
      hα hβ hDpH_meas hcont_H_pm hcont_DpH_pm hDpH_upper hH_rc0
      (ε := ε)
      (fun q hq_K0 σ hσ S hS _hSfin υ Dυ hυ_memSob hDυ_memLp =>
        -- The three a.e. estimates on `HdeltaK0` from `hAE` (Hdelta→HdeltaK0
        -- on {0<m} via `HdeltaK0_eq_Hdelta_of_pos`).
        have hH_upper_pt :
            ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
              ∀ p m, 0 < m →
                StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε x p m
                  ≤ Cε * (‖p‖ ^ hweak.α + 1) - (m ^ hweak.β) / Cε := by
          filter_upwards [hAE.H_upper_pointwise_ae ε hε hε1] with x hx
          intro p m hm
          rw [StationaryMFG.InfimalConvolution.HdeltaK0_eq_Hdelta_of_pos hweak hm]
          exact hx p m hm
        have hlower :
            ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
              ∀ p m, 0 < m →
                StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε x p m
                  ≥ (‖p‖ ^ hweak.α) / Cε - Cε * (m ^ hweak.β + 1) := by
          filter_upwards [hAE.lower_ae ε hε hε1] with x hx
          intro p m hm
          rw [StationaryMFG.InfimalConvolution.HdeltaK0_eq_Hdelta_of_pos hweak hm]
          exact hx p m hm
        -- Build the probe transport density `σ_fn := mOf q + σ·mOf q·𝟙_S`,
        -- with its a.e.-nonnegativity and `L^{β+1}` membership (from `mOf q`),
        -- then supply the transport residue at `HdeltaK0`.
        have hm_memLp : Periodic.MemLpPer (d := d)
            (ENNReal.ofReal (hweak.β + 1))
            (StationaryMFG.Theorems.SimplePower.Banach.mOf q) :=
          StationaryMFG.Theorems.SimplePower.Banach.memLpPer_of_lpPer (d := d) q.1
        have hm_nn : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
            0 ≤ StationaryMFG.Theorems.SimplePower.Banach.mOf q x :=
          mem_K0_Aepsi_iff.mp hq_K0
        have hσ_fn_nn :
            ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
              0 ≤ StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
                    σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
          filter_upwards [hm_nn] with x hxnn
          have hfactor_nn :
              0 ≤ 1 + σ * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
            have hσ_lb : (-1 : ℝ) ≤ σ := by rcases hσ with h | h <;> simp [h]
            by_cases hxS : x ∈ S
            · rw [Set.indicator_of_mem hxS]; simp only [mul_one]; linarith
            · rw [Set.indicator_of_notMem hxS]; simp
          have h_eq :
              StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
                  σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                = StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                    (1 + σ * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
            ring
          rw [h_eq]; exact mul_nonneg hxnn hfactor_nn
        have hsmul : Periodic.MemLpPer (d := d) (ENNReal.ofReal (hweak.β + 1))
            (fun x => σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x) := by
          have := hm_memLp.const_smul (𝕜 := ℝ) σ
          have heq : (σ • (StationaryMFG.Theorems.SimplePower.Banach.mOf q :
                        (Fin d → ℝ) → ℝ))
                      = fun x =>
                          σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x :=
            rfl
          rw [heq] at this; exact this
        have hSind : Periodic.MemLpPer (d := d) (ENNReal.ofReal (hweak.β + 1))
            (S.indicator
              (fun x => σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x)) :=
          Periodic.MemLp.toMemLpPer (MeasureTheory.MemLp.indicator hS.nullMeasurableSet hsmul.toMemLp)
        have hInd_funEq :
            (S.indicator
                (fun x => σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x) :
                (Fin d → ℝ) → ℝ)
              = fun x => σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
          funext x
          by_cases hx : x ∈ S
          · simp [Set.indicator_of_mem hx]
          · simp [Set.indicator_of_notMem hx]
        have hInd_memLp : Periodic.MemLpPer (d := d)
            (ENNReal.ofReal (hweak.β + 1))
            (fun x => σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
          rw [← hInd_funEq]; exact hSind
        have hσ_fn_memLp : Periodic.MemLpPer (d := d)
            (ENNReal.ofReal (hweak.β + 1))
            (fun x => StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
                σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) :=
          Periodic.MemLpPer.add hm_memLp hInd_memLp
        StationaryMFG.Theorems.SimplePower.transportTendstoResidueOfBare_of_paperHypotheses_of_aeMeasH_ae
          (V := V)
          (H := StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
          (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
          (β := hweak.β) (α := hweak.α) (C := Cε)
          hα hβ hCε q
          (fun x => StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
              σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          υ Dυ
          hσ_fn_memLp.aestronglyMeasurable
          hυ_memSob.1.aestronglyMeasurable
          (fun i => (hDυ_memLp i).aestronglyMeasurable)
          hσ_fn_memLp hυ_memSob.1 hDυ_memLp hV_memLp hσ_fn_nn
          hH_upper_pt hlower hDpH_upper
          (fun n =>
            StationaryMFG.InfimalConvolution.aemeasurable_HdeltaK0_comp_of_rc0
              (H := H) (DpH := DpH) hweak hMeas hmonBoundary qε sel hε
              (Du := fun x i => Dυ i x)
              (m := fun x => StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
                  σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                + 1 / ((n : ℝ) + 1))
              (aemeasurable_pi_iff.mpr
                  (fun i => (hDυ_memLp i).aestronglyMeasurable.aemeasurable))
              (hσ_fn_memLp.aestronglyMeasurable.aemeasurable.add aemeasurable_const)
              (by
                filter_upwards [hσ_fn_nn] with x hx
                have hone : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
                linarith))
          (StationaryMFG.InfimalConvolution.aemeasurable_HdeltaK0_comp_of_rc0
            (H := H) (DpH := DpH) hweak hMeas hmonBoundary qε sel hε
            (Du := fun x i => Dυ i x)
            (m := fun x => StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
                σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
            (aemeasurable_pi_iff.mpr
                (fun i => (hDυ_memLp i).aestronglyMeasurable.aemeasurable))
            hσ_fn_memLp.aestronglyMeasurable.aemeasurable
            hσ_fn_nn))
      ctx q

open StationaryMFG.Theorems.SimplePower.Banach in
/-- **G7c-1: refined-cone (`K0_Aepsi_W`/`K_Aepsi_W`) sibling of
`hMinty_signed_user_probe_substitutedPair_of_paperHypotheses_of_rc0_HdeltaK0_ae`.**

W-form signed-family user-probe Minty producer. Body replicates the K-form
residue prelude + the SimplePower probe producer's `σ_fn`/`hCont`/limit-mass
congruence (`mfgOperatorEpsPair_congr_ae`), then finishes with
`hVIeps_signed_user_probe_of_KAepsi_W_VI` (which takes the W-typed `hVI` plus
the test-pair weak-derivative tie `hWeak_υ`). -/
theorem hMinty_signed_user_probe_substitutedPair_of_paperHypotheses_of_rc0_HdeltaK0_W_ae
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {ε : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    (hweak : StationaryMFG.Hamiltonian.HypothesisWeakGrowth (d := d) H DpH)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (qε : StationaryMFG.InfimalConvolution.QEpsFamily d)
    (sel : StationaryMFG.InfimalConvolution.InfConvSelectorFamily
              (H := H) (DpH := DpH) hweak qε)
    (hMeas : StationaryMFG.Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (hmonBoundary : StationaryMFG.Hamiltonian.HypothesisMonotone (d := d) H DpH)
    (hdiffBoundary : StationaryMFG.Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    (hAE : StationaryMFG.InfimalConvolution.HdeltaAEPowerEpsData
              (H := H) (DpH := DpH) hweak qε)
    (hV_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal ((hweak.β + 1) / hweak.β)) V)
    [Fact (1 ≤ ENNReal.ofReal (hweak.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β))]
    (ctx : AepsiUniformContextK_W (d := d) ε V
              (StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
              (StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
              (hweak.α * (hweak.β + 1) / hweak.β)
              (hweak.β + 1)
              ((hweak.β + 1) / hweak.β)
              ((hweak.α * (hweak.β + 1) / hweak.β)
                / (hweak.α * (hweak.β + 1) / hweak.β - 1)))
    (q : XBanach d (hweak.β + 1)
            (hweak.α * (hweak.β + 1) / hweak.β)) :
      q ∈ K0_Aepsi_W d (hweak.β + 1)
              (hweak.α * (hweak.β + 1) / hweak.β) →
      (∀ q' ∈ K_Aepsi_W d (hweak.β + 1)
                (hweak.α * (hweak.β + 1) / hweak.β),
          0 ≤ Aepsi_CLM_opK
                (γBarReal := hweak.α * (hweak.β + 1) / hweak.β)
                (βBarReal := hweak.β + 1)
                (βBarReal' := (hweak.β + 1) / hweak.β)
                (γBarReal' := (hweak.α * (hweak.β + 1) / hweak.β)
                                / (hweak.α * (hweak.β + 1) / hweak.β - 1))
                V (StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
                (StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
                ctx.auxHypsK ε q' (q' - q)) →
      ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)) S < ⊤ →
      ∀ (υ : (Fin d → ℝ) → ℝ)
        (Dυ : Fin d → (Fin d → ℝ) → ℝ),
        Periodic.MemSobolevPer (d := d)
          (ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β)) υ →
        (∀ i, Periodic.MemLpPer (d := d)
                (ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β))
                (Dυ i)) →
        (∀ i, Periodic.HasWeakDerivPer (d := d) i υ (Dυ i)) →
          0 ≤ mfgOperatorEpsPair (V := V)
                (H := StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
                (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
                (hweak.α * (hweak.β + 1) / hweak.β) ε
                Dυ
                (fun x => mOf q x + σ * mOf q x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                υ
                (fun i x => Dυ i x - DuOf q i x)
                (fun x => σ * mOf q x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                (fun x => υ x - uOf q x) := by
  have hα : (1 : ℝ) < hweak.α := hweak.hα
  have hβ : (0 : ℝ) < hweak.β := hweak.hβ
  set Cε : ℝ := StationaryMFG.InfimalConvolution.CdeltaEps
                  (H := H) (DpH := DpH) hweak ε with hCε_def
  have hCε : (0 : ℝ) < Cε :=
    (StationaryMFG.InfimalConvolution.cdeltaEps_facts_upper
        (H := H) (DpH := DpH) hweak hε).1
  have hcont_H_pm :=
    StationaryMFG.InfimalConvolution.HdeltaK0_continuousOn_H_pm_of_selectorFamily
      (H := H) (DpH := DpH) hweak qε sel (ε := ε) hε
  have hH_rc0 :=
    StationaryMFG.InfimalConvolution.HdeltaK0_rc0_of_selectorFamily
      (H := H) (DpH := DpH) hweak hmonBoundary qε sel hε
  have hDpH_meas :=
    StationaryMFG.InfimalConvolution.measurable_DpHepsilonFam_of_selector
      (H := H) (DpH := DpH) hweak qε sel hMeas ε
  have hcont_DpH_pm :=
    StationaryMFG.InfimalConvolution.continuousOn_DpHepsilonFam_of_selector
      (H := H) (DpH := DpH) hweak qε sel hε
  have hDpH_upper : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
      ∀ p m, 0 < m →
        ‖StationaryMFG.InfimalConvolution.DpHepsilonFam hweak qε ε x p m‖
          ≤ Cε * (‖p‖ ^ (hweak.α - 1)
              + m ^ (hweak.β - hweak.β / hweak.α) + 1) :=
    hAE.DpH_upper_ae ε hε hε1
  have hExp_paper :
      SimplePowerExponentFacts
          (SimplePowerExponentFacts.paperGammaBarReal hweak.α hweak.β)
          (SimplePowerExponentFacts.paperBetaBar hweak.β)
          (SimplePowerExponentFacts.paperGammaBar hweak.α hweak.β)
          (SimplePowerExponentFacts.paperBetaBarPrime hweak.β) :=
    SimplePowerExponentFacts.standardPaper hα hβ
  have hExp :
      SimplePowerExponentFacts (hweak.α * (hweak.β + 1) / hweak.β)
          (ENNReal.ofReal (hweak.β + 1))
          (ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β))
          (ENNReal.ofReal ((hweak.β + 1) / hweak.β)) := by
    have h1 :
        (SimplePowerExponentFacts.paperBetaBar hweak.β)
          = ENNReal.ofReal (hweak.β + 1) := by
      simp [SimplePowerExponentFacts.paperBetaBar]
    have h2 :
        (SimplePowerExponentFacts.paperGammaBar hweak.α hweak.β)
          = ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β) := by
      simp [SimplePowerExponentFacts.paperGammaBar]
    have h3 :
        (SimplePowerExponentFacts.paperBetaBarPrime hweak.β)
          = ENNReal.ofReal ((hweak.β + 1) / hweak.β) := by
      simp [SimplePowerExponentFacts.paperBetaBarPrime]
    have h4 :
        (SimplePowerExponentFacts.paperGammaBarReal hweak.α hweak.β)
          = hweak.α * (hweak.β + 1) / hweak.β := by
      simp [SimplePowerExponentFacts.paperGammaBarReal]
    have := hExp_paper
    rw [h1, h2, h3, h4] at this
    exact this
  intro hq_K0W hVI σ hσ S hS hSfin υ Dυ hυ_memSob hDυ_memLp hWeak_υ
  have hq_K0 : q ∈ K0_Aepsi d (hweak.β + 1)
                  (hweak.α * (hweak.β + 1) / hweak.β) :=
    K0_Aepsi_W_subset_K0_Aepsi d (hweak.β + 1)
      (hweak.α * (hweak.β + 1) / hweak.β) hq_K0W
  -- Probe transport density `σ_fn := mOf q + σ·mOf q·𝟙_S`.
  set σ_fn : (Fin d → ℝ) → ℝ :=
    fun x => mOf q x + σ * mOf q x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
    with hσ_fn_def
  have hm_memLp : Periodic.MemLpPer (d := d)
      (ENNReal.ofReal (hweak.β + 1)) (mOf q) :=
    memLpPer_of_lpPer (d := d) q.1
  have hm_nn : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
      0 ≤ mOf q x := mem_K0_Aepsi_iff.mp hq_K0
  have hσ_lb : (-1 : ℝ) ≤ σ := by rcases hσ with h | h <;> simp [h]
  have hσ_ub : σ ≤ 1 := by rcases hσ with h | h <;> simp [h]
  have hσ_fn_nn :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        0 ≤ σ_fn x := by
    filter_upwards [hm_nn] with x hxnn
    have hfactor_nn :
        0 ≤ 1 + σ * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
      by_cases hxS : x ∈ S
      · rw [Set.indicator_of_mem hxS]; simp only [mul_one]; linarith
      · rw [Set.indicator_of_notMem hxS]; simp
    change 0 ≤ mOf q x + σ * mOf q x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
    have h_eq :
        mOf q x + σ * mOf q x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
          = mOf q x * (1 + σ * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
      ring
    rw [h_eq]; exact mul_nonneg hxnn hfactor_nn
  have hsmul : Periodic.MemLpPer (d := d) (ENNReal.ofReal (hweak.β + 1))
      (fun x => σ * mOf q x) := by
    have := hm_memLp.const_smul (𝕜 := ℝ) σ
    have heq : (σ • (mOf q : (Fin d → ℝ) → ℝ))
                = fun x => σ * mOf q x := rfl
    rw [heq] at this; exact this
  have hSind : Periodic.MemLpPer (d := d) (ENNReal.ofReal (hweak.β + 1))
      (S.indicator (fun x => σ * mOf q x)) :=
    Periodic.MemLp.toMemLpPer (MeasureTheory.MemLp.indicator hS.nullMeasurableSet hsmul.toMemLp)
  have hInd_funEq :
      (S.indicator (fun x => σ * mOf q x) : (Fin d → ℝ) → ℝ)
        = fun x => σ * mOf q x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
    funext x
    by_cases hx : x ∈ S
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have hInd_memLp : Periodic.MemLpPer (d := d)
      (ENNReal.ofReal (hweak.β + 1))
      (fun x => σ * mOf q x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
    rw [← hInd_funEq]; exact hSind
  have hσ_fn_memLp : Periodic.MemLpPer (d := d)
      (ENNReal.ofReal (hweak.β + 1)) σ_fn := by
    have := Periodic.MemLpPer.add hm_memLp hInd_memLp
    simpa only [hσ_fn_def, Pi.add_def] using this
  -- Probe transport residue bundle at `σ_fn` (residue closure body, identical
  -- to the K-form producer's).
  have hH_upper_pt :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ∀ p m, 0 < m →
          StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε x p m
            ≤ Cε * (‖p‖ ^ hweak.α + 1) - (m ^ hweak.β) / Cε := by
    filter_upwards [hAE.H_upper_pointwise_ae ε hε hε1] with x hx
    intro p m hm
    rw [StationaryMFG.InfimalConvolution.HdeltaK0_eq_Hdelta_of_pos hweak hm]
    exact hx p m hm
  have hlower :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ∀ p m, 0 < m →
          StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε x p m
            ≥ (‖p‖ ^ hweak.α) / Cε - Cε * (m ^ hweak.β + 1) := by
    filter_upwards [hAE.lower_ae ε hε hε1] with x hx
    intro p m hm
    rw [StationaryMFG.InfimalConvolution.HdeltaK0_eq_Hdelta_of_pos hweak hm]
    exact hx p m hm
  have r :=
    StationaryMFG.Theorems.SimplePower.transportTendstoResidueOfBare_of_paperHypotheses_of_aeMeasH_ae
      (V := V)
      (H := StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
      (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
      (β := hweak.β) (α := hweak.α) (C := Cε)
      hα hβ hCε q σ_fn υ Dυ
      hσ_fn_memLp.aestronglyMeasurable
      hυ_memSob.1.aestronglyMeasurable
      (fun i => (hDυ_memLp i).aestronglyMeasurable)
      hσ_fn_memLp hυ_memSob.1 hDυ_memLp hV_memLp hσ_fn_nn
      hH_upper_pt hlower hDpH_upper
      (fun n =>
        StationaryMFG.InfimalConvolution.aemeasurable_HdeltaK0_comp_of_rc0
          (H := H) (DpH := DpH) hweak hMeas hmonBoundary qε sel hε
          (Du := fun x i => Dυ i x)
          (m := fun x => σ_fn x + 1 / ((n : ℝ) + 1))
          (aemeasurable_pi_iff.mpr
              (fun i => (hDυ_memLp i).aestronglyMeasurable.aemeasurable))
          (hσ_fn_memLp.aestronglyMeasurable.aemeasurable.add aemeasurable_const)
          (by
            filter_upwards [hσ_fn_nn] with x hx
            have hone : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
            linarith))
      (StationaryMFG.InfimalConvolution.aemeasurable_HdeltaK0_comp_of_rc0
        (H := H) (DpH := DpH) hweak hMeas hmonBoundary qε sel hε
        (Du := fun x i => Dυ i x)
        (m := σ_fn)
        (aemeasurable_pi_iff.mpr
            (fun i => (hDυ_memLp i).aestronglyMeasurable.aemeasurable))
        hσ_fn_memLp.aestronglyMeasurable.aemeasurable
        hσ_fn_nn)
  have hCont :=
    mfgOperatorEpsPair_tendsto_transport_perturbation_of_paperHypotheses_of_aestronglyMeasurable_of_rc0_of_aeMeasH
      (ε := ε)
      (γBarReal := hweak.α * (hweak.β + 1) / hweak.β)
      (βBarReal := hweak.β + 1)
      (βBarReal' := (hweak.β + 1) / hweak.β)
      (γBarReal' := (hweak.α * (hweak.β + 1) / hweak.β)
                      / (hweak.α * (hweak.β + 1) / hweak.β - 1))
      (C := Cε) (α := hweak.α) (β := hweak.β)
      (H := StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
      (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
      hα hβ hDpH_meas hcont_H_pm hcont_DpH_pm hDpH_upper hExp hH_rc0
      Dυ υ (uOf q) (DuOf q) (mOf q) V σ_fn
      r.hσ r.hm r.hV r.hυ r.hu r.hφ r.hDu hσ_fn_nn hσ_fn_memLp
      r.hHcomp_ae_n r.hHcomp_ae_lim
      r.Gh r.Eh r.hGh_memLp r.hEh_memLp r.hGh_bd r.hEh_bd
      r.Gf r.Ef r.hGf_memLp r.hEf_memLp r.hGf_bd r.hEf_bd
      r.Gm r.Em r.hGm_memLp r.hEm_memLp r.hGm_bd r.hEm_bd
  -- Rewrite the limit operator's mass-difference from `σ_fn - mOf q` to the
  -- cancelled form `σ·mOf q·𝟙_S`.
  have hη_lim_eq :
      (σ_fn - mOf q)
        =ᵐ[MeasureTheory.volume.restrict (Periodic.UnitCube d)]
      (fun x => σ * mOf q x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    change σ_fn x - mOf q x
        = σ * mOf q x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
    simp only [hσ_fn_def]; ring
  have hLim_eq :
      mfgOperatorEpsPair (V := V)
          (H := StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
          (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
          (hweak.α * (hweak.β + 1) / hweak.β) ε
          Dυ σ_fn υ
          (fun i x => Dυ i x - DuOf q i x)
          (σ_fn - mOf q)
          (υ - uOf q)
      =
      mfgOperatorEpsPair (V := V)
          (H := StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
          (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
          (hweak.α * (hweak.β + 1) / hweak.β) ε
          Dυ σ_fn υ
          (fun i x => Dυ i x - DuOf q i x)
          (fun x => σ * mOf q x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          (υ - uOf q) :=
    StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_congr_ae
      (V := V) (H := StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
      (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
      (hweak.α * (hweak.β + 1) / hweak.β) ε
      Dυ σ_fn υ
      (fun i x => Dυ i x - DuOf q i x)
      (fun i x => Dυ i x - DuOf q i x)
      (σ_fn - mOf q)
      (fun x => σ * mOf q x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
      (υ - uOf q)
      (υ - uOf q)
      (fun _ => Filter.EventuallyEq.rfl) hη_lim_eq Filter.EventuallyEq.rfl
  rw [hLim_eq] at hCont
  exact hVIeps_signed_user_probe_of_KAepsi_W_VI
    ctx.auxHypsK q hq_K0W hVI σ hσ S hS hSfin υ Dυ hυ_memSob hDυ_memLp
    hWeak_υ hCont

open StationaryMFG.Theorems.SimplePower.Banach in
/-- **Substituted-pair `hMinty_signed_user_triple` δ-limit slice, re-keyed on the
closed-cone carrier `HdeltaK0`, AE/bare-exponent variant** (paper
`thm:strongAepsi.delta`, D2c-2e-2c-triple retype rewire).

Additive `_ae` sibling of
`hMinty_signed_user_triple_substitutedPair_of_paperHypotheses_of_rc0_HdeltaK0` that
DROPS the strict `hpowEps : HypothesisPowerGrowth (HdeltaPos …)` entirely. The
exponent type-indices are reindexed off `hweak.β`/`hweak.α`, the constant is
`CdeltaEps hweak ε`, and the three a.e. analytic estimates are sourced from the
AE carrier `hAE : HdeltaAEPowerEpsData hweak qε`, transferred from `Hdelta` to
`HdeltaK0` on `{0<m}` via `HdeltaK0_eq_Hdelta_of_pos`. The per-query bare residue
supplier is `transportTendstoResidueOfBare_of_paperHypotheses_of_aeMeasH_ae` at
the triple transport density `σ_fn := μ + σ·μ·𝟙_S`.

GATE #1: identical to the probe `_ae` sibling above. -/
theorem hMinty_signed_user_triple_substitutedPair_of_paperHypotheses_of_rc0_HdeltaK0_ae
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {ε : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    (hweak : StationaryMFG.Hamiltonian.HypothesisWeakGrowth (d := d) H DpH)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (qε : StationaryMFG.InfimalConvolution.QEpsFamily d)
    (sel : StationaryMFG.InfimalConvolution.InfConvSelectorFamily
              (H := H) (DpH := DpH) hweak qε)
    (hMeas : StationaryMFG.Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (hmonBoundary : StationaryMFG.Hamiltonian.HypothesisMonotone (d := d) H DpH)
    (hdiffBoundary : StationaryMFG.Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    (hAE : StationaryMFG.InfimalConvolution.HdeltaAEPowerEpsData
              (H := H) (DpH := DpH) hweak qε)
    (hV_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal ((hweak.β + 1) / hweak.β)) V)
    [Fact (1 ≤ ENNReal.ofReal (hweak.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β))]
    (ctx : AepsiUniformContextK (d := d) ε V
              (StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
              (StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
              (hweak.α * (hweak.β + 1) / hweak.β)
              (hweak.β + 1)
              ((hweak.β + 1) / hweak.β)
              ((hweak.α * (hweak.β + 1) / hweak.β)
                / (hweak.α * (hweak.β + 1) / hweak.β - 1)))
    (q : XBanach d (hweak.β + 1)
            (hweak.α * (hweak.β + 1) / hweak.β)) :
      q ∈ K0_Aepsi d (hweak.β + 1)
              (hweak.α * (hweak.β + 1) / hweak.β) →
      (∀ q' ∈ K_Aepsi d (hweak.β + 1)
                (hweak.α * (hweak.β + 1) / hweak.β),
          0 ≤ Aepsi_CLM_opK
                (γBarReal := hweak.α * (hweak.β + 1) / hweak.β)
                (βBarReal := hweak.β + 1)
                (βBarReal' := (hweak.β + 1) / hweak.β)
                (γBarReal' := (hweak.α * (hweak.β + 1) / hweak.β)
                                / (hweak.α * (hweak.β + 1) / hweak.β - 1))
                V (StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
                (StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
                ctx.auxHypsK ε q' (q' - q)) →
      ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)) S < ⊤ →
      ∀ (μ υ : (Fin d → ℝ) → ℝ)
        (Dυ : Fin d → (Fin d → ℝ) → ℝ),
        (∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)), 0 ≤ μ x) →
        Periodic.MemLpPer (d := d) (ENNReal.ofReal (hweak.β + 1)) μ →
        Periodic.MemSobolevPer (d := d)
          (ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β)) υ →
        (∀ i, Periodic.MemLpPer (d := d)
                (ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β))
                (Dυ i)) →
        (∀ i, Periodic.HasWeakDerivPer (d := d) i υ (Dυ i)) →
          0 ≤ mfgOperatorEpsPair (V := V)
                (H := StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
                (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
                (hweak.α * (hweak.β + 1) / hweak.β) ε
                Dυ
                (fun x => μ x + σ * μ x *
                              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                υ
                (fun i x => Dυ i x - DuOf q i x)
                (fun x => (μ x + σ * μ x *
                              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                          - mOf q x)
                (fun x => υ x - uOf q x) := by
  -- Bare AE exponents/constant from the AE carrier.
  have hα : (1 : ℝ) < hweak.α := hweak.hα
  have hβ : (0 : ℝ) < hweak.β := hweak.hβ
  set Cε : ℝ := StationaryMFG.InfimalConvolution.CdeltaEps
                  (H := H) (DpH := DpH) hweak ε with hCε_def
  have hCε : (0 : ℝ) < Cε :=
    (StationaryMFG.InfimalConvolution.cdeltaEps_facts_upper
        (H := H) (DpH := DpH) hweak hε).1
  -- H-side supply at `H := HdeltaK0`, all INTERNAL.
  have hcont_H_pm :=
    StationaryMFG.InfimalConvolution.HdeltaK0_continuousOn_H_pm_of_selectorFamily
      (H := H) (DpH := DpH) hweak qε sel (ε := ε) hε
  have hH_rc0 :=
    StationaryMFG.InfimalConvolution.HdeltaK0_rc0_of_selectorFamily
      (H := H) (DpH := DpH) hweak hmonBoundary qε sel hε
  -- DpH-side data (carrier-independent), from the selector family.
  have hDpH_meas :=
    StationaryMFG.InfimalConvolution.measurable_DpHepsilonFam_of_selector
      (H := H) (DpH := DpH) hweak qε sel hMeas ε
  have hcont_DpH_pm :=
    StationaryMFG.InfimalConvolution.continuousOn_DpHepsilonFam_of_selector
      (H := H) (DpH := DpH) hweak qε sel hε
  -- The DpH upper a.e. estimate (general `p`, `0 < m`) from the AE carrier.
  have hDpH_upper : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
      ∀ p m, 0 < m →
        ‖StationaryMFG.InfimalConvolution.DpHepsilonFam hweak qε ε x p m‖
          ≤ Cε * (‖p‖ ^ (hweak.α - 1)
              + m ^ (hweak.β - hweak.β / hweak.α) + 1) :=
    hAE.DpH_upper_ae ε hε hε1
  exact
    StationaryMFG.Theorems.SimplePower.paperSection8_hMinty_signed_user_triple_of_paperHypotheses_of_rc0_of_aeMeasH
      (V := V) (H := StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
      (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
      hα hβ hDpH_meas hcont_H_pm hcont_DpH_pm hDpH_upper hH_rc0
      (ε := ε)
      (fun q _hq_K0 σ hσ S hS _hSfin μ υ Dυ hμ_nn hμ_memLp hυ_memSob hDυ_memLp =>
        -- The three a.e. estimates on `HdeltaK0` from `hAE`.
        have hH_upper_pt :
            ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
              ∀ p m, 0 < m →
                StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε x p m
                  ≤ Cε * (‖p‖ ^ hweak.α + 1) - (m ^ hweak.β) / Cε := by
          filter_upwards [hAE.H_upper_pointwise_ae ε hε hε1] with x hx
          intro p m hm
          rw [StationaryMFG.InfimalConvolution.HdeltaK0_eq_Hdelta_of_pos hweak hm]
          exact hx p m hm
        have hlower :
            ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
              ∀ p m, 0 < m →
                StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε x p m
                  ≥ (‖p‖ ^ hweak.α) / Cε - Cε * (m ^ hweak.β + 1) := by
          filter_upwards [hAE.lower_ae ε hε hε1] with x hx
          intro p m hm
          rw [StationaryMFG.InfimalConvolution.HdeltaK0_eq_Hdelta_of_pos hweak hm]
          exact hx p m hm
        -- Build the triple transport density `σ_fn := μ + σ·μ·𝟙_S`.
        have hσ_fn_nn :
            ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
              0 ≤ μ x + σ * μ x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
          filter_upwards [hμ_nn] with x hxnn
          have hfactor_nn :
              0 ≤ 1 + σ * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
            have hσ_lb : (-1 : ℝ) ≤ σ := by rcases hσ with h | h <;> simp [h]
            by_cases hxS : x ∈ S
            · rw [Set.indicator_of_mem hxS]; simp only [mul_one]; linarith
            · rw [Set.indicator_of_notMem hxS]; simp
          have h_eq :
              μ x + σ * μ x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                = μ x *
                    (1 + σ * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
            ring
          rw [h_eq]; exact mul_nonneg hxnn hfactor_nn
        have hsmul : Periodic.MemLpPer (d := d) (ENNReal.ofReal (hweak.β + 1))
            (fun x => σ * μ x) := by
          have := hμ_memLp.const_smul (𝕜 := ℝ) σ
          have heq : (σ • (μ : (Fin d → ℝ) → ℝ)) = fun x => σ * μ x := rfl
          rw [heq] at this; exact this
        have hSind : Periodic.MemLpPer (d := d) (ENNReal.ofReal (hweak.β + 1))
            (S.indicator (fun x => σ * μ x)) :=
          Periodic.MemLp.toMemLpPer (MeasureTheory.MemLp.indicator hS.nullMeasurableSet hsmul.toMemLp)
        have hInd_funEq :
            (S.indicator (fun x => σ * μ x) : (Fin d → ℝ) → ℝ)
              = fun x => σ * μ x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
          funext x
          by_cases hx : x ∈ S
          · simp [Set.indicator_of_mem hx]
          · simp [Set.indicator_of_notMem hx]
        have hInd_memLp : Periodic.MemLpPer (d := d)
            (ENNReal.ofReal (hweak.β + 1))
            (fun x => σ * μ x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
          rw [← hInd_funEq]; exact hSind
        have hσ_fn_memLp : Periodic.MemLpPer (d := d)
            (ENNReal.ofReal (hweak.β + 1))
            (fun x => μ x + σ * μ x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) :=
          Periodic.MemLpPer.add hμ_memLp hInd_memLp
        StationaryMFG.Theorems.SimplePower.transportTendstoResidueOfBare_of_paperHypotheses_of_aeMeasH_ae
          (V := V)
          (H := StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
          (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
          (β := hweak.β) (α := hweak.α) (C := Cε)
          hα hβ hCε q
          (fun x => μ x + σ * μ x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          υ Dυ
          hσ_fn_memLp.aestronglyMeasurable
          hυ_memSob.1.aestronglyMeasurable
          (fun i => (hDυ_memLp i).aestronglyMeasurable)
          hσ_fn_memLp hυ_memSob.1 hDυ_memLp hV_memLp hσ_fn_nn
          hH_upper_pt hlower hDpH_upper
          (fun n =>
            StationaryMFG.InfimalConvolution.aemeasurable_HdeltaK0_comp_of_rc0
              (H := H) (DpH := DpH) hweak hMeas hmonBoundary qε sel hε
              (Du := fun x i => Dυ i x)
              (m := fun x => μ x + σ * μ x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                + 1 / ((n : ℝ) + 1))
              (aemeasurable_pi_iff.mpr
                  (fun i => (hDυ_memLp i).aestronglyMeasurable.aemeasurable))
              (hσ_fn_memLp.aestronglyMeasurable.aemeasurable.add aemeasurable_const)
              (by
                filter_upwards [hσ_fn_nn] with x hx
                have hone : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
                linarith))
          (StationaryMFG.InfimalConvolution.aemeasurable_HdeltaK0_comp_of_rc0
            (H := H) (DpH := DpH) hweak hMeas hmonBoundary qε sel hε
            (Du := fun x i => Dυ i x)
            (m := fun x => μ x + σ * μ x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
            (aemeasurable_pi_iff.mpr
                (fun i => (hDυ_memLp i).aestronglyMeasurable.aemeasurable))
            hσ_fn_memLp.aestronglyMeasurable.aemeasurable
            hσ_fn_nn))
      ctx q

open StationaryMFG.Theorems.SimplePower.Banach in
/-- **G7c-1: refined-cone (`K0_Aepsi_W`/`K_Aepsi_W`) sibling of
`hMinty_signed_user_triple_substitutedPair_of_paperHypotheses_of_rc0_HdeltaK0_ae`.**

W-form signed-family user-triple Minty producer. Body replicates the K-form
residue prelude + the SimplePower triple producer's `σ_fn`/`hCont` build, then
finishes with `hVIeps_signed_user_triple_of_KAepsi_W_VI` (W-typed `hVI` + the
test-pair weak-derivative tie `hWeak_υ`; the limit mass-difference stays in the
uncancelled form `σ_fn - mOf q`, so no `mfgOperatorEpsPair_congr_ae` rewrite is
needed). -/
theorem hMinty_signed_user_triple_substitutedPair_of_paperHypotheses_of_rc0_HdeltaK0_W_ae
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {ε : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    (hweak : StationaryMFG.Hamiltonian.HypothesisWeakGrowth (d := d) H DpH)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (qε : StationaryMFG.InfimalConvolution.QEpsFamily d)
    (sel : StationaryMFG.InfimalConvolution.InfConvSelectorFamily
              (H := H) (DpH := DpH) hweak qε)
    (hMeas : StationaryMFG.Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (hmonBoundary : StationaryMFG.Hamiltonian.HypothesisMonotone (d := d) H DpH)
    (hdiffBoundary : StationaryMFG.Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    (hAE : StationaryMFG.InfimalConvolution.HdeltaAEPowerEpsData
              (H := H) (DpH := DpH) hweak qε)
    (hV_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal ((hweak.β + 1) / hweak.β)) V)
    [Fact (1 ≤ ENNReal.ofReal (hweak.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β))]
    (ctx : AepsiUniformContextK_W (d := d) ε V
              (StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
              (StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
              (hweak.α * (hweak.β + 1) / hweak.β)
              (hweak.β + 1)
              ((hweak.β + 1) / hweak.β)
              ((hweak.α * (hweak.β + 1) / hweak.β)
                / (hweak.α * (hweak.β + 1) / hweak.β - 1)))
    (q : XBanach d (hweak.β + 1)
            (hweak.α * (hweak.β + 1) / hweak.β)) :
      q ∈ K0_Aepsi_W d (hweak.β + 1)
              (hweak.α * (hweak.β + 1) / hweak.β) →
      (∀ q' ∈ K_Aepsi_W d (hweak.β + 1)
                (hweak.α * (hweak.β + 1) / hweak.β),
          0 ≤ Aepsi_CLM_opK
                (γBarReal := hweak.α * (hweak.β + 1) / hweak.β)
                (βBarReal := hweak.β + 1)
                (βBarReal' := (hweak.β + 1) / hweak.β)
                (γBarReal' := (hweak.α * (hweak.β + 1) / hweak.β)
                                / (hweak.α * (hweak.β + 1) / hweak.β - 1))
                V (StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
                (StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
                ctx.auxHypsK ε q' (q' - q)) →
      ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)) S < ⊤ →
      ∀ (μ υ : (Fin d → ℝ) → ℝ)
        (Dυ : Fin d → (Fin d → ℝ) → ℝ),
        (∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)), 0 ≤ μ x) →
        Periodic.MemLpPer (d := d) (ENNReal.ofReal (hweak.β + 1)) μ →
        Periodic.MemSobolevPer (d := d)
          (ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β)) υ →
        (∀ i, Periodic.MemLpPer (d := d)
                (ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β))
                (Dυ i)) →
        (∀ i, Periodic.HasWeakDerivPer (d := d) i υ (Dυ i)) →
          0 ≤ mfgOperatorEpsPair (V := V)
                (H := StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
                (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
                (hweak.α * (hweak.β + 1) / hweak.β) ε
                Dυ
                (fun x => μ x + σ * μ x *
                              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                υ
                (fun i x => Dυ i x - DuOf q i x)
                (fun x => (μ x + σ * μ x *
                              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                          - mOf q x)
                (fun x => υ x - uOf q x) := by
  have hα : (1 : ℝ) < hweak.α := hweak.hα
  have hβ : (0 : ℝ) < hweak.β := hweak.hβ
  set Cε : ℝ := StationaryMFG.InfimalConvolution.CdeltaEps
                  (H := H) (DpH := DpH) hweak ε with hCε_def
  have hCε : (0 : ℝ) < Cε :=
    (StationaryMFG.InfimalConvolution.cdeltaEps_facts_upper
        (H := H) (DpH := DpH) hweak hε).1
  have hcont_H_pm :=
    StationaryMFG.InfimalConvolution.HdeltaK0_continuousOn_H_pm_of_selectorFamily
      (H := H) (DpH := DpH) hweak qε sel (ε := ε) hε
  have hH_rc0 :=
    StationaryMFG.InfimalConvolution.HdeltaK0_rc0_of_selectorFamily
      (H := H) (DpH := DpH) hweak hmonBoundary qε sel hε
  have hDpH_meas :=
    StationaryMFG.InfimalConvolution.measurable_DpHepsilonFam_of_selector
      (H := H) (DpH := DpH) hweak qε sel hMeas ε
  have hcont_DpH_pm :=
    StationaryMFG.InfimalConvolution.continuousOn_DpHepsilonFam_of_selector
      (H := H) (DpH := DpH) hweak qε sel hε
  have hDpH_upper : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
      ∀ p m, 0 < m →
        ‖StationaryMFG.InfimalConvolution.DpHepsilonFam hweak qε ε x p m‖
          ≤ Cε * (‖p‖ ^ (hweak.α - 1)
              + m ^ (hweak.β - hweak.β / hweak.α) + 1) :=
    hAE.DpH_upper_ae ε hε hε1
  have hExp_paper :
      SimplePowerExponentFacts
          (SimplePowerExponentFacts.paperGammaBarReal hweak.α hweak.β)
          (SimplePowerExponentFacts.paperBetaBar hweak.β)
          (SimplePowerExponentFacts.paperGammaBar hweak.α hweak.β)
          (SimplePowerExponentFacts.paperBetaBarPrime hweak.β) :=
    SimplePowerExponentFacts.standardPaper hα hβ
  have hExp :
      SimplePowerExponentFacts (hweak.α * (hweak.β + 1) / hweak.β)
          (ENNReal.ofReal (hweak.β + 1))
          (ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β))
          (ENNReal.ofReal ((hweak.β + 1) / hweak.β)) := by
    have h1 :
        (SimplePowerExponentFacts.paperBetaBar hweak.β)
          = ENNReal.ofReal (hweak.β + 1) := by
      simp [SimplePowerExponentFacts.paperBetaBar]
    have h2 :
        (SimplePowerExponentFacts.paperGammaBar hweak.α hweak.β)
          = ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β) := by
      simp [SimplePowerExponentFacts.paperGammaBar]
    have h3 :
        (SimplePowerExponentFacts.paperBetaBarPrime hweak.β)
          = ENNReal.ofReal ((hweak.β + 1) / hweak.β) := by
      simp [SimplePowerExponentFacts.paperBetaBarPrime]
    have h4 :
        (SimplePowerExponentFacts.paperGammaBarReal hweak.α hweak.β)
          = hweak.α * (hweak.β + 1) / hweak.β := by
      simp [SimplePowerExponentFacts.paperGammaBarReal]
    have := hExp_paper
    rw [h1, h2, h3, h4] at this
    exact this
  intro hq_K0W hVI σ hσ S hS hSfin μ υ Dυ hμ_nn hμ_memLp hυ_memSob hDυ_memLp hWeak_υ
  have hq_K0 : q ∈ K0_Aepsi d (hweak.β + 1)
                  (hweak.α * (hweak.β + 1) / hweak.β) :=
    K0_Aepsi_W_subset_K0_Aepsi d (hweak.β + 1)
      (hweak.α * (hweak.β + 1) / hweak.β) hq_K0W
  -- Triple transport density `σ_fn := μ + σ·μ·𝟙_S`.
  set σ_fn : (Fin d → ℝ) → ℝ :=
    fun x => μ x + σ * μ x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
    with hσ_fn_def
  have hσ_fn_nn :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        0 ≤ σ_fn x := by
    filter_upwards [hμ_nn] with x hxnn
    have hfactor_nn :
        0 ≤ 1 + σ * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
      have hσ_lb : (-1 : ℝ) ≤ σ := by rcases hσ with h | h <;> simp [h]
      by_cases hxS : x ∈ S
      · rw [Set.indicator_of_mem hxS]; simp only [mul_one]; linarith
      · rw [Set.indicator_of_notMem hxS]; simp
    change 0 ≤ μ x + σ * μ x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
    have h_eq :
        μ x + σ * μ x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
          = μ x * (1 + σ * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
      ring
    rw [h_eq]; exact mul_nonneg hxnn hfactor_nn
  have hsmul : Periodic.MemLpPer (d := d) (ENNReal.ofReal (hweak.β + 1))
      (fun x => σ * μ x) := by
    have := hμ_memLp.const_smul (𝕜 := ℝ) σ
    have heq : (σ • (μ : (Fin d → ℝ) → ℝ)) = fun x => σ * μ x := rfl
    rw [heq] at this; exact this
  have hSind : Periodic.MemLpPer (d := d) (ENNReal.ofReal (hweak.β + 1))
      (S.indicator (fun x => σ * μ x)) :=
    Periodic.MemLp.toMemLpPer (MeasureTheory.MemLp.indicator hS.nullMeasurableSet hsmul.toMemLp)
  have hInd_funEq :
      (S.indicator (fun x => σ * μ x) : (Fin d → ℝ) → ℝ)
        = fun x => σ * μ x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
    funext x
    by_cases hx : x ∈ S
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have hInd_memLp : Periodic.MemLpPer (d := d)
      (ENNReal.ofReal (hweak.β + 1))
      (fun x => σ * μ x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
    rw [← hInd_funEq]; exact hSind
  have hσ_fn_memLp : Periodic.MemLpPer (d := d)
      (ENNReal.ofReal (hweak.β + 1)) σ_fn := by
    have := Periodic.MemLpPer.add hμ_memLp hInd_memLp
    simpa only [hσ_fn_def, Pi.add_def] using this
  have hH_upper_pt :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ∀ p m, 0 < m →
          StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε x p m
            ≤ Cε * (‖p‖ ^ hweak.α + 1) - (m ^ hweak.β) / Cε := by
    filter_upwards [hAE.H_upper_pointwise_ae ε hε hε1] with x hx
    intro p m hm
    rw [StationaryMFG.InfimalConvolution.HdeltaK0_eq_Hdelta_of_pos hweak hm]
    exact hx p m hm
  have hlower :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ∀ p m, 0 < m →
          StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε x p m
            ≥ (‖p‖ ^ hweak.α) / Cε - Cε * (m ^ hweak.β + 1) := by
    filter_upwards [hAE.lower_ae ε hε hε1] with x hx
    intro p m hm
    rw [StationaryMFG.InfimalConvolution.HdeltaK0_eq_Hdelta_of_pos hweak hm]
    exact hx p m hm
  have r :=
    StationaryMFG.Theorems.SimplePower.transportTendstoResidueOfBare_of_paperHypotheses_of_aeMeasH_ae
      (V := V)
      (H := StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
      (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
      (β := hweak.β) (α := hweak.α) (C := Cε)
      hα hβ hCε q σ_fn υ Dυ
      hσ_fn_memLp.aestronglyMeasurable
      hυ_memSob.1.aestronglyMeasurable
      (fun i => (hDυ_memLp i).aestronglyMeasurable)
      hσ_fn_memLp hυ_memSob.1 hDυ_memLp hV_memLp hσ_fn_nn
      hH_upper_pt hlower hDpH_upper
      (fun n =>
        StationaryMFG.InfimalConvolution.aemeasurable_HdeltaK0_comp_of_rc0
          (H := H) (DpH := DpH) hweak hMeas hmonBoundary qε sel hε
          (Du := fun x i => Dυ i x)
          (m := fun x => σ_fn x + 1 / ((n : ℝ) + 1))
          (aemeasurable_pi_iff.mpr
              (fun i => (hDυ_memLp i).aestronglyMeasurable.aemeasurable))
          (hσ_fn_memLp.aestronglyMeasurable.aemeasurable.add aemeasurable_const)
          (by
            filter_upwards [hσ_fn_nn] with x hx
            have hone : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
            linarith))
      (StationaryMFG.InfimalConvolution.aemeasurable_HdeltaK0_comp_of_rc0
        (H := H) (DpH := DpH) hweak hMeas hmonBoundary qε sel hε
        (Du := fun x i => Dυ i x)
        (m := σ_fn)
        (aemeasurable_pi_iff.mpr
            (fun i => (hDυ_memLp i).aestronglyMeasurable.aemeasurable))
        hσ_fn_memLp.aestronglyMeasurable.aemeasurable
        hσ_fn_nn)
  have hCont :=
    mfgOperatorEpsPair_tendsto_transport_perturbation_of_paperHypotheses_of_aestronglyMeasurable_of_rc0_of_aeMeasH
      (ε := ε)
      (γBarReal := hweak.α * (hweak.β + 1) / hweak.β)
      (βBarReal := hweak.β + 1)
      (βBarReal' := (hweak.β + 1) / hweak.β)
      (γBarReal' := (hweak.α * (hweak.β + 1) / hweak.β)
                      / (hweak.α * (hweak.β + 1) / hweak.β - 1))
      (C := Cε) (α := hweak.α) (β := hweak.β)
      (H := StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
      (DpH := StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
      hα hβ hDpH_meas hcont_H_pm hcont_DpH_pm hDpH_upper hExp hH_rc0
      Dυ υ (uOf q) (DuOf q) (mOf q) V σ_fn
      r.hσ r.hm r.hV r.hυ r.hu r.hφ r.hDu hσ_fn_nn hσ_fn_memLp
      r.hHcomp_ae_n r.hHcomp_ae_lim
      r.Gh r.Eh r.hGh_memLp r.hEh_memLp r.hGh_bd r.hEh_bd
      r.Gf r.Ef r.hGf_memLp r.hEf_memLp r.hGf_bd r.hEf_bd
      r.Gm r.Em r.hGm_memLp r.hEm_memLp r.hGm_bd r.hEm_bd
  exact hVIeps_signed_user_triple_of_KAepsi_W_VI
    ctx.auxHypsK q hVI σ hσ S hS hSfin μ υ Dυ
    hμ_nn hμ_memLp hυ_memSob hDυ_memLp hWeak_υ hCont

open StationaryMFG.Theorems.SimplePower.Banach in
/-- **D2c-2d: the `HdeltaK0` strong-VI `∀ ε`-family producer at fixed
(ε-uniform) exponents, with the nonneg `0 ≤ᵐ m` rider, AE/bare-exponent
variant** (paper `thm:strongAepsi.delta`, D2c-2e-2d).

The `_ae` `∀ ε`-family producer that DROPS
the strict `hpowEps : ∀ ε, HypothesisPowerGrowth (HdeltaPos …)` entirely. The
per-`ε` substituted-pair context `ctx`, the `Fact` Props, `hV_memLp`, and the
ε-uniformity exponent equalities are all reindexed off the AE carrier's bare
exponents `hweak.β`/`hweak.α` (which are themselves ε-independent — the
ε-uniformity is automatic). The five `hMinty_*_…_HdeltaK0` δ-limit families are
discharged in-body via the `_ae` c4c wrappers, fed `hAE`/`hε1` in place of
`hpowEps`.

**Dependent-motive hazard, avoided.** We keep all INPUTS (`ctx`, the `Fact`s,
`hV_memLp`) at the AE-pinned exponents (zero transport through the dependent
context type); we rewrite ONLY the output existential — whose exponents are plain
`ℝ≥0∞`/`ℝ` arguments of `MemLpPer`/`MemSobolevPer`/`IsStrongVI_Aepsi`, not type
indices — back to the fixed `βBarReal`/`γBarReal` via the equalities.

GATE #1: NO `hpowEps`/`HypothesisPowerGrowth(HdeltaPos)`/`RegularityH(HdeltaPos)`/
`hFormPos`/`hqE_per`/`hInj`/`hSurj`/`qEofMinv`. Permitted riders are the AE carrier
`hAE` + `hε1` + `hMeas`/`hmonBoundary`/`hdiffBoundary`/`hweak`/`sel` + exponent facts. -/
theorem strongAepsi_deltaK0_family_of_selectorData_ae
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {βBarReal γBarReal : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    (hweak : StationaryMFG.Hamiltonian.HypothesisWeakGrowth (d := d) H DpH)
    (qε : StationaryMFG.InfimalConvolution.QEpsFamily d)
    (sel : StationaryMFG.InfimalConvolution.InfConvSelectorFamily
              (H := H) (DpH := DpH) hweak qε)
    (hMeas : StationaryMFG.Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (hmonBoundary : StationaryMFG.Hamiltonian.HypothesisMonotone (d := d) H DpH)
    (hdiffBoundary : StationaryMFG.Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    (hAE : StationaryMFG.InfimalConvolution.HdeltaAEPowerEpsData
              (H := H) (DpH := DpH) hweak qε)
    -- ε-uniformity of the exponents off the ε-independent AE carrier exponents.
    (hβBar_eq : ∀ (ε : ℝ), ε > 0 → βBarReal = hweak.β + 1)
    (hγBar_eq : ∀ (ε : ℝ), ε > 0 →
      γBarReal = hweak.α * (hweak.β + 1) / hweak.β)
    (hV_memLp : ∀ (ε : ℝ), ε > 0 → Periodic.MemLpPer (d := d)
        (ENNReal.ofReal ((hweak.β + 1) / hweak.β)) V)
    -- Per-`ε` pinned `Fact` Props (supplied as instances inside the body).
    (hFactβ : ∀ (ε : ℝ), ε > 0 → (1 : ℝ≥0∞) ≤ ENNReal.ofReal (hweak.β + 1))
    (hFactγ : ∀ (ε : ℝ), ε > 0 →
      (1 : ℝ≥0∞) ≤
        ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β))
    -- Per-`ε` substituted-pair Browder–Minty context on the `HdeltaK0` carrier,
    -- at the AE-pinned exponents.
    (ctx : ∀ ε (hε : 0 < ε) (_hε1 : ε ≤ 1),
      haveI : Fact (1 ≤ ENNReal.ofReal (hweak.β + 1)) := ⟨hFactβ ε hε⟩
      haveI : Fact (1 ≤ ENNReal.ofReal
                      (hweak.α * (hweak.β + 1) / hweak.β)) :=
        ⟨hFactγ ε hε⟩
      AepsiUniformContextK_W (d := d) ε V
              (StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
              (StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
              (hweak.α * (hweak.β + 1) / hweak.β)
              (hweak.β + 1)
              ((hweak.β + 1) / hweak.β)
              ((hweak.α * (hweak.β + 1) / hweak.β)
                / (hweak.α * (hweak.β + 1) / hweak.β - 1))) :
    ∀ ε (hε : 0 < ε) (_hε1 : ε ≤ 1),
      ∃ (m u : (Fin d → ℝ) → ℝ) (Du : Fin d → (Fin d → ℝ) → ℝ),
      Periodic.MemLpPer (ENNReal.ofReal βBarReal) m ∧
      Periodic.MemSobolevPer (ENNReal.ofReal γBarReal) u ∧
      (∀ i, Periodic.MemLpPer (ENNReal.ofReal γBarReal) (Du i)) ∧
      (∀ i, Periodic.HasWeakDerivPer i u (Du i)) ∧
      IsStrongVI_Aepsi (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
        V (StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
        (StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
        γBarReal ε m u Du ∧
      (∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)), 0 ≤ m x) := by
  intro ε hε hε1
  -- Per-`ε` pinned `Fact` instances.
  haveI : Fact (1 ≤ ENNReal.ofReal (hweak.β + 1)) := ⟨hFactβ ε hε⟩
  haveI : Fact (1 ≤ ENNReal.ofReal
                  (hweak.α * (hweak.β + 1) / hweak.β)) :=
    ⟨hFactγ ε hε⟩
  -- Re-run the underlying assembly to bind the same `(m, u, Du)` AND its
  -- `hmNonneg`. The five `hMinty_*_…_HdeltaK0` δ-limit families are discharged
  -- via the c4c HdeltaK0-keyed `_ae` substituted-pair wrappers (all Hext-free).
  obtain ⟨sol⟩ := exists_regularizedBareSolution_K_W hε (ctx ε hε hε1)
    (hMinty_set_substitutedPair_of_paperHypotheses_of_rc0_HdeltaK0_W_ae
      V hweak hε hε1 qε sel hMeas hmonBoundary hdiffBoundary hAE (hV_memLp ε hε)
      (ctx ε hε hε1))
    (hMinty_signed_substitutedPair_of_paperHypotheses_of_rc0_HdeltaK0_W_ae
      V hweak hε hε1 qε sel hMeas hmonBoundary hdiffBoundary hAE (hV_memLp ε hε)
      (ctx ε hε hε1))
    (hMinty_transport_substitutedPair_of_paperHypotheses_of_rc0_HdeltaK0_W_ae
      V hweak hε hε1 qε sel hMeas hmonBoundary hdiffBoundary hAE (hV_memLp ε hε)
      (ctx ε hε hε1))
    (hMinty_signed_user_probe_substitutedPair_of_paperHypotheses_of_rc0_HdeltaK0_W_ae
      V hweak hε hε1 qε sel hMeas hmonBoundary hdiffBoundary hAE (hV_memLp ε hε)
      (ctx ε hε hε1))
    (hMinty_signed_user_triple_substitutedPair_of_paperHypotheses_of_rc0_HdeltaK0_W_ae
      V hweak hε hε1 qε sel hMeas hmonBoundary hdiffBoundary hAE (hV_memLp ε hε)
      (ctx ε hε hε1))
  have huSob : Periodic.MemSobolevPer
      (ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β))
      sol.u :=
    ⟨sol.huLp, sol.Du, sol.hWeakDeriv⟩
  have hVI := isStrongVI_Aepsi_of_regularizedBareSolution sol
  -- Transport the OUTPUT existential to the fixed exponents via the equalities.
  -- The `Du`-Lp / weak-derivative facts come straight off the bare solution
  -- (`sol.hDuLp`, `sol.hWeakDeriv`), with the Lp facts reindexed to the fixed
  -- `γBarReal` via `hγBar_eq`.
  refine ⟨sol.m, sol.u, sol.Du, ?_, ?_, ?_, ?_, ?_, sol.hmNonneg⟩
  · rw [hβBar_eq ε hε]; exact sol.hmLp
  · rw [hγBar_eq ε hε]; exact huSob
  · intro i; rw [hγBar_eq ε hε]; exact sol.hDuLp i
  · intro i; exact sol.hWeakDeriv i
  · rw [hβBar_eq ε hε, hγBar_eq ε hε]; exact hVI

/-! ## Sanity-check `example`

A trivial 1D bridge `(X := ℝ, K := {0}, A := 0, v₀ := 0)` collapses
every hypothesis to a tautology (singleton domain ⇒ trivial coercivity;
the zero operator is monotone and hemicontinuous; `{0}` is both convex
and closed). The conclusion is the trivial strong VI `0 ≤ 0` at `u = 0`,
mirroring the sibling unit tests in `Theorems.SimplePower.Regularized`
and `Theorems.Congestion.Existence`. -/

example
    [Monotone.FiniteConvexHullWeakVI ℝ]
    (hℝ : Periodic.IsReflexiveNormedSpace ℝ) :
    ∃ u ∈ ({0} : Set ℝ), ∀ v ∈ ({0} : Set ℝ),
      0 ≤ (fun _ => (0 : StrongDual ℝ ℝ)) u (v - u) :=
  exists_strong_solution_Aepsi_delta (X := ℝ) hℝ
    (K := ({0} : Set ℝ))
    (convex_singleton 0)
    (isClosed_singleton)
    (A := fun _ => (0 : StrongDual ℝ ℝ))
    (Monotone.isMonotone_zero _)
    (Monotone.isHemicontinuous_zero _)
    (v₀ := 0)
    (Monotone.isCoerciveAt_of_bounded_domain Bornology.isBounded_singleton _ rfl)

/-! ## Canonical closed-cone carrier

The regularized strong VI is retained on `HdeltaK0`. At zero mass this
carrier uses the finite right-hand limit of the regularized Hamiltonian;
it is not identified with the arbitrary raw value `Hdelta ... 0`.
-/

/-! ## The regularized strong-VI family -/

/-- An epsilon-uniform family of regularized solutions, with all integrability
and weak-gradient certificates. The VI uses `HdeltaK0` throughout, including
its canonical finite value at zero mass. -/
structure T3RegularizedStrongFamily
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (V : (Fin d → ℝ) → ℝ)
    (hweak : StationaryMFG.Hamiltonian.HypothesisWeakGrowth (d := d) H DpH)
    (qε : StationaryMFG.InfimalConvolution.QEpsFamily d)
    (βBarReal γBarReal : ℝ) where
  /-- The per-`ε` regularised solution mass. -/
  m : ℝ → (Fin d → ℝ) → ℝ
  /-- The per-`ε` regularised value function. -/
  u : ℝ → (Fin d → ℝ) → ℝ
  /-- The per-`ε` weak gradient of `u ε`. -/
  Du : ℝ → Fin d → (Fin d → ℝ) → ℝ
  /-- `m ε ∈ L^{β̄}_per` at the ε-uniform exponent. -/
  hmLp : ∀ ε, 0 < ε → ε ≤ 1 → Periodic.MemLpPer (ENNReal.ofReal βBarReal) (m ε)
  /-- `u ε ∈ W^{1,γ̄}_per` at the ε-uniform exponent. -/
  huSob : ∀ ε, 0 < ε → ε ≤ 1 →
    Periodic.MemSobolevPer (ENNReal.ofReal γBarReal) (u ε)
  /-- Each weak-gradient component `Du ε i ∈ L^{γ̄}_per` at the ε-uniform
  exponent. This is the per-`ε`, per-coordinate `Du`-Lp regularity that the
  a-priori engine `apriori_uniform_bound_of_strongVI_family_coercive`
  consumes as `hDu_lpFam`. -/
  hDuLp : ∀ ε, 0 < ε → ε ≤ 1 →
    ∀ i, Periodic.MemLpPer (ENNReal.ofReal γBarReal) (Du ε i)
  /-- `Du ε i` is the `i`-th periodic weak derivative of `u ε`. This is the
  per-`ε`, per-coordinate weak-derivative regularity that the a-priori engine
  consumes as `hDu_weakFam`. -/
  hDuWeak : ∀ ε, 0 < ε → ε ≤ 1 →
    ∀ i, Periodic.HasWeakDerivPer i (u ε) (Du ε i)
  /-- `m ε ≥ 0` a.e. on the torus. -/
  hmNonneg : ∀ ε, 0 < ε → ε ≤ 1 →
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)), 0 ≤ m ε x
  /-- The bare strong VI on the canonical closed-cone carrier. -/
  hVI : ∀ ε, 0 < ε → ε ≤ 1 →
    IsStrongVI_Aepsi (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
      V (StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
      (StationaryMFG.InfimalConvolution.DpHepsilonFam hweak qε ε)
      γBarReal ε (m ε) (u ε) (Du ε)

/-- Package the closed-cone solutions for `0 < ε ≤ 1`, retaining their
canonical Hamiltonian carrier and every solution certificate. -/
noncomputable def T3RegularizedStrongFamily.of_deltaK0_family_le_one
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {βBarReal γBarReal : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    (hweak : StationaryMFG.Hamiltonian.HypothesisWeakGrowth (d := d) H DpH)
    (qε : StationaryMFG.InfimalConvolution.QEpsFamily d)
    (hfam : ∀ ε (hε : 0 < ε) (_hε1 : ε ≤ 1), ∃ (m u : (Fin d → ℝ) → ℝ)
        (Du : Fin d → (Fin d → ℝ) → ℝ),
        Periodic.MemLpPer (ENNReal.ofReal βBarReal) m ∧
        Periodic.MemSobolevPer (ENNReal.ofReal γBarReal) u ∧
        (∀ i, Periodic.MemLpPer (ENNReal.ofReal γBarReal) (Du i)) ∧
        (∀ i, Periodic.HasWeakDerivPer i u (Du i)) ∧
        IsStrongVI_Aepsi (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
          V (StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
          (StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
          γBarReal ε m u Du ∧
        (∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)), 0 ≤ m x)) :
    T3RegularizedStrongFamily V hweak qε βBarReal γBarReal := by
  classical
  -- Repackage the gated `hfam` as a single existential over the conjunction
  -- `0 < ε ∧ ε ≤ 1`, then `choose!` the per-`ε` data (junk outside the regime).
  have hfam' : ∀ ε, ∃ (m u : (Fin d → ℝ) → ℝ)
      (Du : Fin d → (Fin d → ℝ) → ℝ),
      (0 < ε → ε ≤ 1 →
        Periodic.MemLpPer (ENNReal.ofReal βBarReal) m ∧
        Periodic.MemSobolevPer (ENNReal.ofReal γBarReal) u ∧
        (∀ i, Periodic.MemLpPer (ENNReal.ofReal γBarReal) (Du i)) ∧
        (∀ i, Periodic.HasWeakDerivPer i u (Du i)) ∧
        IsStrongVI_Aepsi (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
          V (StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε)
          (StationaryMFG.InfimalConvolution.DpHepsilon hweak (qε ε))
          γBarReal ε m u Du ∧
        (∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)), 0 ≤ m x)) := by
    intro ε
    by_cases hε : 0 < ε
    · by_cases hε1 : ε ≤ 1
      · obtain ⟨m, u, Du, h⟩ := hfam ε hε hε1
        exact ⟨m, u, Du, fun _ _ => h⟩
      · exact ⟨0, 0, fun _ => 0, fun _ h => absurd h hε1⟩
    · exact ⟨0, 0, fun _ => 0, fun h => absurd h hε⟩
  choose m u Du hpack using hfam'
  refine
    { m := m
      u := u
      Du := Du
      hmLp := fun ε hε hε1 => (hpack ε hε hε1).1
      huSob := fun ε hε hε1 => (hpack ε hε hε1).2.1
      hDuLp := fun ε hε hε1 => (hpack ε hε hε1).2.2.1
      hDuWeak := fun ε hε hε1 => (hpack ε hε hε1).2.2.2.1
      hmNonneg := fun ε hε hε1 => (hpack ε hε hε1).2.2.2.2.2
      hVI := fun ε hε hε1 => (hpack ε hε hε1).2.2.2.2.1 }

open StationaryMFG.Theorems.SimplePower.Banach in
/-- **D2c-2d (final assembly): `T3RegularizedStrongFamily.of_paperHypotheses`
(AE / bare-exponent route).** (paper `thm:strongAepsi.delta`).

The genuinely-mechanical two-step assembly that closes the D2c2d chain:

```
aepsiDeltaContextFamily_K0_of_AEData          (BanachBridge.lean:3819)
  → strongAepsi_deltaK0_family_of_selectorData_ae   (Existence.lean:3480)
  → T3RegularizedStrongFamily.of_deltaK0_family_le_one  (Existence.lean:4089)
```

producing the canonical-`HdeltaK0` strong-VI family on the paper
regularization regime `0 < ε ≤ 1`, indexed by the supplied selector family
`qε` (returned directly on `qε`, NOT existentially repackaged, so the
downstream side-data/stabilisation carriers stay aligned to the SAME `qε`).

The exponents are pinned to the paper formulas (`eq:gamma`): `β̄ = β + 1`,
`γ̄ = α·(β+1)/β`, `β̄' = (β+1)/β`, `γ̄' = γ̄/(γ̄-1)`, read off `hweak`. The
binder list is exactly the seven base Theorem-3 riders plus the accepted
AE-route carriers (`sel`/`hAE`/`hUB`/`hExp`) and the documented AE
measurability inputs consumed by the `HdeltaK0` ctx aggregator — NO `ctx`,
NO `*Pack`/`*Inputs`/`*Oracle`, NO `fam`-as-binder, NO `powData`/`hpowEps`,
NO `RegularityH(HdeltaPos)`, NO `hqE_per`/`hFormPos`/`hInj`/`hSurj`/`qEofMinv`. -/
noncomputable def T3RegularizedStrongFamily.of_paperHypotheses
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (V : (Fin d → ℝ) → ℝ)
    -- Paper Theorem 3 base hypotheses.
    (hweak : StationaryMFG.Hamiltonian.HypothesisWeakGrowth (d := d) H DpH)
    (hMono : StationaryMFG.Hamiltonian.HypothesisMonotone (d := d) H DpH)
    (hMeas : StationaryMFG.Hamiltonian.HypothesisDpHMeasurable (d := d) H DpH)
    (hmonBoundary : StationaryMFG.Hamiltonian.HypothesisMonotone (d := d) H DpH)
    (hdiffBoundary : StationaryMFG.Hamiltonian.HypothesisHpDifferentiable (d := d) H DpH)
    -- Accepted AE-route carriers (NOT `powData`).
    (qε : StationaryMFG.InfimalConvolution.QEpsFamily d)
    (sel : StationaryMFG.InfimalConvolution.InfConvSelectorFamily
              (H := H) (DpH := DpH) hweak qε)
    (hAE : StationaryMFG.InfimalConvolution.HdeltaAEPowerEpsData
              (H := H) (DpH := DpH) hweak qε)
    (hUB : StationaryMFG.InfimalConvolution.HdeltaUniformBounds
              (H := H) (DpH := DpH) hweak qε)
    -- `V`-integrability at the conjugate exponent `β̄' = (β+1)/β`.
    (hV : Periodic.MemLpPer (d := d)
            (ENNReal.ofReal ((hweak.β + 1) / hweak.β)) V)
    -- The bundled exponent/Hölder facts at the paper formulas.
    (hExp : SimplePowerExponentFacts
                (hweak.α * (hweak.β + 1) / hweak.β)
                (ENNReal.ofReal (hweak.β + 1))
                (ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β))
                (ENNReal.ofReal ((hweak.β + 1) / hweak.β)))
    (hβ : (hweak.β + 1).HolderConjugate ((hweak.β + 1) / hweak.β))
    (hγ : (hweak.α * (hweak.β + 1) / hweak.β).HolderConjugate
            ((hweak.α * (hweak.β + 1) / hweak.β)
              / (hweak.α * (hweak.β + 1) / hweak.β - 1)))
    (hβTop : ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β) ≠ ⊤)
    (hβBarTop : ENNReal.ofReal (hweak.β + 1) ≠ ⊤)
    (hβ_gt1 : 1 < hweak.β + 1) (hγ_gt1 : 1 < hweak.α * (hweak.β + 1) / hweak.β)
    (hγ'_le_β : ENNReal.ofReal ((hweak.α * (hweak.β + 1) / hweak.β)
                  / (hweak.α * (hweak.β + 1) / hweak.β - 1))
                ≤ ENNReal.ofReal (hweak.β + 1))
    (hβconj : ((hweak.β + 1) / hweak.β).HolderConjugate (hweak.β + 1))
    (hγconj : ((hweak.α * (hweak.β + 1) / hweak.β)
                / (hweak.α * (hweak.β + 1) / hweak.β - 1)).HolderConjugate
              (hweak.α * (hweak.β + 1) / hweak.β))
    (hd_pos : 0 < (d : ℝ))
    (hScalarMono :
      ∀ s t : ℝ,
        0 ≤ (StationaryMFG.Solutions.MFG.absPowMinusTwo
                (hweak.α * (hweak.β + 1) / hweak.β) t * t
              - StationaryMFG.Solutions.MFG.absPowMinusTwo
                (hweak.α * (hweak.β + 1) / hweak.β) s * s)
              * (t - s))
    (hVecMono :
      ∀ v w : Fin d → ℝ,
        0 ≤ dotProduct
              (StationaryMFG.Solutions.MFG.vecAbsPowMinusTwo
                (hweak.α * (hweak.β + 1) / hweak.β) v • v
              - StationaryMFG.Solutions.MFG.vecAbsPowMinusTwo
                (hweak.α * (hweak.β + 1) / hweak.β) w • w)
              (v - w))
    (hC0_le : ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      hUB.C0 ≤ StationaryMFG.InfimalConvolution.CdeltaEps
                  (H := H) (DpH := DpH) hweak ε)
    (hF_HJB_meas_Pos : ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      ∀ q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
              (hweak.β + 1) (hweak.α * (hweak.β + 1) / hweak.β),
        MeasureTheory.AEStronglyMeasurable
          (fun x => -(StationaryMFG.Theorems.SimplePower.Banach.uOf q x)
              - StationaryMFG.InfimalConvolution.HdeltaPos hweak ε x
                  (fun i => StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
                  (StationaryMFG.Theorems.SimplePower.Banach.mOf q x) + V x)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (Periodic.UnitCube d)))
    (hF_HJB_meas_K0 : ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      ∀ q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
              (hweak.β + 1) (hweak.α * (hweak.β + 1) / hweak.β),
        MeasureTheory.AEStronglyMeasurable
          (fun x => -(StationaryMFG.Theorems.SimplePower.Banach.uOf q x)
              - StationaryMFG.InfimalConvolution.HdeltaK0 hweak ε x
                  (fun i => StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
                  (StationaryMFG.Theorems.SimplePower.Banach.mOf q x) + V x)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (Periodic.UnitCube d)))
    (hF_flux_meas : ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      ∀ q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
              (hweak.β + 1) (hweak.α * (hweak.β + 1) / hweak.β), ∀ i,
        MeasureTheory.AEStronglyMeasurable
          (fun x => StationaryMFG.Theorems.SimplePower.Banach.mOf q x
              * StationaryMFG.InfimalConvolution.DpHepsilonFam hweak qε ε x
                  (fun j => StationaryMFG.Theorems.SimplePower.Banach.DuOf q j x)
                  (StationaryMFG.Theorems.SimplePower.Banach.mOf q x) i)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (Periodic.UnitCube d)))
    (hF_gat_meas : ∀ (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1),
      ∀ (u v : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
                (hweak.β + 1) (hweak.α * (hweak.β + 1) / hweak.β)),
                u ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi d
                      (hweak.β + 1) (hweak.α * (hweak.β + 1) / hweak.β) →
                v ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi d
                      (hweak.β + 1) (hweak.α * (hweak.β + 1) / hweak.β) →
                ∀ (w : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
                        (hweak.β + 1) (hweak.α * (hweak.β + 1) / hweak.β)),
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        MeasureTheory.AEStronglyMeasurable
          (fun x => StationaryMFG.Theorems.SimplePower.aepsiIntegrandAt_gateaux
                      (hweak.α * (hweak.β + 1) / hweak.β)
                      (StationaryMFG.Theorems.SimplePower.Banach.DuOf v)
                      (StationaryMFG.Theorems.SimplePower.Banach.DuOf u)
                      (StationaryMFG.Theorems.SimplePower.Banach.uOf v)
                      (StationaryMFG.Theorems.SimplePower.Banach.uOf u)
                      (fun i => ⇑(w.2.2 i)) (⇑w.2.1) x t)
          (MeasureTheory.volume.restrict (Periodic.UnitCube d)))
    (aux10 : ∀ ε (hε : 0 < ε) (hε1 : ε ≤ 1),
      StationaryMFG.Theorems.SimplePower.Banach.MFGOpEpsAuxHyps (d := d)
        (hweak.α * (hweak.β + 1) / hweak.β) (hweak.β + 1)
        ((hweak.β + 1) / hweak.β)
        ((hweak.α * (hweak.β + 1) / hweak.β)
          / (hweak.α * (hweak.β + 1) / hweak.β - 1))
        V (StationaryMFG.InfimalConvolution.Hdelta hweak ε)
        (StationaryMFG.InfimalConvolution.DpHepsilonFam hweak qε ε)
        (fun (_ : Fin d) (_ : (Fin d → ℝ)) => (0 : ℝ))
        (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ))) :
    T3RegularizedStrongFamily V hweak qε
            (hweak.β + 1) (hweak.α * (hweak.β + 1) / hweak.β) := by
  classical
  -- Pinned `Fact` instances at the paper exponents.
  have hFactβ : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (hweak.β + 1) := by
    have h1 : ENNReal.ofReal 1 ≤ ENNReal.ofReal (hweak.β + 1) :=
      ENNReal.ofReal_le_ofReal hβ_gt1.le
    simpa using h1
  have hFactγ : (1 : ℝ≥0∞) ≤
      ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β) := by
    have h1 : ENNReal.ofReal 1 ≤
        ENNReal.ofReal (hweak.α * (hweak.β + 1) / hweak.β) :=
      ENNReal.ofReal_le_ofReal hγ_gt1.le
    simpa using h1
  haveI : Fact (1 ≤ ENNReal.ofReal (hweak.β + 1)) := ⟨hFactβ⟩
  haveI : Fact (1 ≤ ENNReal.ofReal
                  (hweak.α * (hweak.β + 1) / hweak.β)) := ⟨hFactγ⟩
  -- Step 1: the `powData`/`RegularityH`-free per-`ε` ctx aggregator on `HdeltaK0`,
  -- on the REFINED cone `K0_Aepsi_W` (carries the weak-derivative tie
  -- structurally; no `hWeakDerivK0` binder).
  have ctx := StationaryMFG.InfimalConvolution.aepsiDeltaContextFamily_K0_W_of_AEData
      (γBarReal := hweak.α * (hweak.β + 1) / hweak.β)
      (βBarReal := hweak.β + 1)
      (βBarReal' := (hweak.β + 1) / hweak.β)
      (γBarReal' := (hweak.α * (hweak.β + 1) / hweak.β)
        / (hweak.α * (hweak.β + 1) / hweak.β - 1))
      V hweak hMono qε sel hAE hUB hMeas hmonBoundary hdiffBoundary hV hExp
      rfl rfl rfl rfl hβ hγ hβTop hβBarTop hβ_gt1 hγ_gt1 hγ'_le_β hβconj hγconj
      hd_pos hScalarMono hVecMono hC0_le hF_HJB_meas_Pos hF_HJB_meas_K0
      hF_flux_meas hF_gat_meas aux10
  -- Step 2: the AE per-`ε` strong-VI family on the closed cone `HdeltaK0`.
  have hfam := strongAepsi_deltaK0_family_of_selectorData_ae
      (βBarReal := hweak.β + 1)
      (γBarReal := hweak.α * (hweak.β + 1) / hweak.β)
      V hweak qε sel hMeas hmonBoundary hdiffBoundary hAE
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => hV)
      (fun _ _ => hFactβ) (fun _ _ => hFactγ) ctx
  -- Step 3: package into the canonical `HdeltaK0` family on the input `qε` itself
  -- (the index is the supplied selector family, kept explicit so the downstream
  -- side-data / stabilisation carriers stay aligned to the SAME `qε`).
  exact T3RegularizedStrongFamily.of_deltaK0_family_le_one V hweak qε hfam

/-! `HdeltaPos` is used only on strictly positive mass. The final
regularized VI and its limit-passage estimates retain `HdeltaK0`, whose
zero-mass value is the regularized right-hand limit. -/

end InfimalConvolution
end Theorems
end StationaryMFG

end
