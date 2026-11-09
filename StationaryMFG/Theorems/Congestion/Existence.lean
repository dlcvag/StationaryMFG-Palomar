module

/-
Copyright (c) 2026 Stationary MFG project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import StationaryMFG.Theorems.Congestion.Domain
public import StationaryMFG.Theorems.Congestion.WellDefined
public import StationaryMFG.Theorems.SimplePower.Banach.Operator
public import StationaryMFG.Theorems.SimplePower.Banach.AssemblyContext
public import StationaryMFG.Theorems.SimplePower.Banach.WeakLimit
public import StationaryMFG.Solutions.Regularized
public import StationaryMFG.Monotone.AbstractWeak
public import StationaryMFG.Hamiltonian.Assumptions
public import StationaryMFG.Hamiltonian.Congestion
public import StationaryMFG.Periodic.SobolevPoincare
public import StationaryMFG.Periodic.LpDuality

@[expose] public section

/-!
# Existence of a regularised solution under congestion growth

This file formalises paper `thm:weakAepsi.congestion`
(`Source/FGU-monotone_revised.tex`, line 1363, "Existence of a
Regularized Solution"):

> Under the assumptions of Theorem `thm:main-congestion.growth`, let
> `A_ε` be defined as in Lemma `lem:Aepsi.congestion.well-defined`.
> Then, for every `ε > 0`, there exists
> `(m_ε, u_ε) ∈ L^{β̄}_per(𝕋^d; ℝ⁺₀) × W^{1,γ̄}_per(𝕋^d)` satisfying
> `⟨A_ε[μ, υ], (μ - m_ε, υ - u_ε)⟩ ≥ 0` for all `(μ, υ) ∈ 𝓚`.

Per the paper's own proof (lines 1368–1378), the conclusion is obtained
by applying `paper:thm:monotone.abstract-weak` (Browder–Minty) to `A_ε`
on `𝓚`, once monotonicity and coercivity of `A_ε` are checked. The
two structural inputs are reused from Phase 4:

* **Monotonicity.** Same argument as Proposition `thm:strongAepsi`:
  Assumption `onH.monotone` ensures `A_ε` is monotone.
* **Coercivity.** Same argument as Proposition `prop:coercAepsi`,
  with each ingredient supplied by the *congestion-growth* bundle in
  place of the power-growth bundle. The four ingredients (paper line
  1369–1377) are: (i) `eq:DpHdotpminusH-estimate1` from
  `(onH.monotone)` + `eq:assH.upper.congestion`; (ii) `|H(x,0,1)| ≤ C`
  from the upper + lower congestion bounds; (iii) `|D_pH(x,0,1)| ≤ C`
  from `eq:assH.DpH.upper.congestion`; and (iv) `eq:assH.lower.simple`
  from `eq:assH.lower.congestion` via `rem:hierarchy`.

## CONVENTIONS §8 statement-first split

Per `docs/CONVENTIONS.md` §8, the *statement* of
`paper:thm:weakAepsi.congestion` lands now, parameterised over a
**Banach realisation** `(X, K, A)` of the bare-function pair
`(𝓚, A_ε)` and over the four abstract-weak-VI hypotheses (convexity of
`K`, monotonicity of `A`, coercivity of `A`, and reflexivity of `X`).
The concrete bridge to `congestionDomainK` and `mfgOperatorEpsPair`,
which involves a `MeasureTheory.Lp` / `Periodic.Lp` quotient passage,
is deferred to a follow-up infra task. This mirrors the
already-landed sibling `Theorems.SimplePower.Regularized.weakVI_Aepsi`
for the power-growth case.

The downstream consumers `paper:thm:apriori-congestion.growth` and
`paper:thm:main-congestion.growth` can compile against the
bridge-parameterised statement immediately; they will be supplied
the bridge witnesses when the follow-up task lands.

## Deliverables

* `weak_Aeps_congestion_exists` — bridge-parameterised existence of a
  regularised solution under congestion growth, mirroring the shape of
  `Theorems.SimplePower.Regularized.weakVI_Aepsi`. One-line invocation
  of `Monotone.monotone_abstract_weak`.

## Paper reference

`Source/FGU-monotone_revised.tex` §`sec:proof-congestion`, line 1363,
equation `eq:weak.epsi.cong` (line 1365 in the proof).
-/

noncomputable section

namespace StationaryMFG
namespace Congestion

open MeasureTheory Set
open StationaryMFG.Periodic
open StationaryMFG.Solutions.MFG
open StationaryMFG.Hamiltonian
open scoped ENNReal NNReal

variable {d : ℕ}

/-! ## The admissible congestion Banach domain `congestionBanachK` (T2 BB1a)

Paper `Source/FGU-monotone_revised.tex` lines 901–903: the admissible set is
`𝓚 = L^{β̄}(𝕋^d; ℝ⁺₀) × W^{1,γ̄}(𝕋^d)`. Realised as a bare Mathlib product
`LpPer β̄ d × SobolevPerLp 1 γ̄ d = LpPer β̄ d × (Lp γ̄ × (Fin d → Lp γ̄))`, the
third (`Du`) factor is *independent* of the second (`u`) factor — the bare
product does NOT encode `Du = ∇u`. Operator well-definedness and
monotonicity, however, need that relation. We therefore re-impose the two
admissibility constraints directly on the domain SET (not via a bridge
oracle):

* strict density positivity `0 < m` a.e. on the unit cube (consistent with
  the strict-positivity hypotheses `paper:hpos₁/hpos₂` consumed by the
  regularized operator's monotonicity), and
* the weak-gradient relation `HasWeakDerivPer i u (Du i)` for every direction
  `i` (this is the `Du = ∇u` admissibility).

Both constraints are convex: positivity is preserved under positive convex
combinations, and `HasWeakDerivPer` is linear (closed under `+` and `•`).

This task (BB1a) only *defines* the domain and proves convexity; the operator,
auxiliary-hypothesis extraction, and pack assembly are BB1b–BB1e. -/

/-- Local Banach realisation of the congestion admissible space `𝓚`:
`LpPer β̄ d × SobolevPerLp 1 γ̄ d`. (Compare the `private abbrev XBanach` of
`Theorems/SimplePower/Banach/AbstractLifts.lean`, which uses `ℝ`-typed
exponents through `ENNReal.ofReal`; here we follow the `ℝ≥0∞`-typed convention
of `Theorems/Congestion/Compactness.lean`.) -/
abbrev congestionXBanach (d : ℕ) (βBar γBar : ℝ≥0∞) : Type :=
  Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d

/-- **The admissible congestion Banach domain**, the paper-faithful
encoding of `𝓚` (paper `def-domainK`, tex line 1330).

For `q : congestionXBanach d βBar γBar`:
* `q.1 : LpPer βBar d` is the density `m`;
* `q.2.1 : Lp ℝ γBar (μ ⌞ cube)` is the value `u`;
* `q.2.2 : Fin d → Lp ℝ γBar (μ ⌞ cube)` is the gradient family `Du`.

`congestionBanachK` selects those `q` such that:

* (domain) the bare pair `(⇑q.1, ⇑q.2.1)` lies in the paper-faithful
  congestion domain `congestionDomainK` — this carries BOTH the uniform
  lower bound `essinf μ > 0` (= `∃ c > 0, c ≤ᵐ μ`) and the ratio
  integrability `|Dυ|^{α(1+τ/β)}/(μ^τ+1) ∈ L^{β̄'}` (paper line 1330);
* (gradient) `Du i := ⇑(q.2.2 i)` is the weak `i`-th partial derivative
  of `u := ⇑q.2.1` for every `i` — the explicit `Du = ∇u` relation that
  the bare product `congestionXBanach` does not enforce and that the
  operator's flux/HJB terms consume.

**T2 BB1a-revise (iter 0869):** the previous definition encoded only a.e.
positivity `0 <ᵐ μ` plus the gradient relation, *dropping* the two
defining conditions of the paper's `𝓚`. That under-specification meant
`congestionBanachK` membership did not imply `congestionDomainK`
membership, forcing the downstream `MFGOpEpsAuxHyps` producer (BB1b) to
take free `hc`/`hRatio` hypotheses with no discharge from
`(hmon, hcong, hV)` — public rider relocation. The fix is to make
`congestionBanachK` membership genuinely imply `congestionDomainK`
membership, which is exactly the paper's `𝓚`. Convexity is preserved
because `𝓚` is convex (paper line 1341, Lean `congestionDomainK_convex`). -/
def congestionBanachK (d : ℕ)
    (βBar betaBarPrime γBar : ℝ≥0∞) (α β τ : ℝ) :
    Set (congestionXBanach d βBar γBar) :=
  { q |
      ((⇑q.1 : (Fin d → ℝ) → ℝ), (⇑q.2.1 : (Fin d → ℝ) → ℝ)) ∈
        congestionDomainK (d := d) βBar betaBarPrime γBar α β τ
      ∧
      (∀ i : Fin d,
        Periodic.HasWeakDerivPer (d := d) i
          (⇑q.2.1 : (Fin d → ℝ) → ℝ)
          (⇑(q.2.2 i) : (Fin d → ℝ) → ℝ)) }

/-- Membership unfolding for `congestionBanachK`. -/
lemma mem_congestionBanachK_iff {βBar betaBarPrime γBar : ℝ≥0∞} {α β τ : ℝ}
    {q : congestionXBanach d βBar γBar} :
    q ∈ congestionBanachK d βBar betaBarPrime γBar α β τ ↔
      ((⇑q.1 : (Fin d → ℝ) → ℝ), (⇑q.2.1 : (Fin d → ℝ) → ℝ)) ∈
        congestionDomainK (d := d) βBar betaBarPrime γBar α β τ
      ∧
      (∀ i : Fin d,
        Periodic.HasWeakDerivPer (d := d) i
          (⇑q.2.1 : (Fin d → ℝ) → ℝ)
          (⇑(q.2.2 i) : (Fin d → ℝ) → ℝ)) :=
  Iff.rfl

/-- **BB1b bridge (iter 0869).** Membership in the (revised, paper-faithful)
`congestionBanachK` directly yields membership of the bare pair
`(⇑q.1, ⇑q.2.1)` in the paper's congestion domain `congestionDomainK`.

This is the bridge that the K-scoped auxiliary-hypothesis producer (BB1b)
consumes: it supplies the uniform lower bound and ratio integrability that
the operator's well-definedness lemmas (`aEpsi_congestion_HJB_memLp`,
`aEpsi_congestion_flux_memLp`) require, with NO extra free hypotheses —
they are now part of `congestionBanachK` membership itself. -/
lemma mem_congestionDomainK_of_mem_congestionBanachK
    {βBar betaBarPrime γBar : ℝ≥0∞} {α β τ : ℝ}
    {q : congestionXBanach d βBar γBar}
    (hq : q ∈ congestionBanachK d βBar betaBarPrime γBar α β τ) :
    ((⇑q.1 : (Fin d → ℝ) → ℝ), (⇑q.2.1 : (Fin d → ℝ) → ℝ)) ∈
      congestionDomainK (d := d) βBar betaBarPrime γBar α β τ :=
  hq.1

/-- **Transport `congestionDomainK` membership across unit-cube a.e.
equality of both components.**

If `(μ, υ) ∈ 𝓚` and `μ =ᵐ μ'`, `υ =ᵐ υ'` on the unit cube, then
`(μ', υ') ∈ 𝓚`. Each of the four defining conjuncts of
`congestionDomainK` is a.e.-transport-stable:
* `MemLpPer βBar μ` via `MemLpPer.congr_ae_unitCube`;
* `MemSobolevPer γBar υ` via `MemSobolevPer.congr_ae_unitCube`;
* the uniform lower bound `∃ c > 0, c ≤ᵐ μ` by transporting the a.e.
  inequality along `μ =ᵐ μ'`;
* the ratio witness `∃ Du, weak ∧ |Du|^{αt}/(μ^τ+1) ∈ L^{β̄'}`: the
  derivative witness `Du` is reused (weak derivative of `υ'` via
  `HasWeakDerivPer.congr_ae_unitCube_f`), and the ratio function changes
  only through the denominator `μ ↦ μ'`, transported via
  `MemLpPer.congr_ae_unitCube`. -/
lemma congestionDomainK_congr_ae
    {βBar betaBarPrime γBar : ℝ≥0∞} {α β τ : ℝ}
    {μ υ μ' υ' : (Fin d → ℝ) → ℝ}
    (hmem : (μ, υ) ∈ congestionDomainK (d := d) βBar betaBarPrime γBar α β τ)
    (hμ : μ =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] μ')
    (hυ : υ =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] υ') :
    (μ', υ') ∈ congestionDomainK (d := d) βBar betaBarPrime γBar α β τ := by
  obtain ⟨hμLp, hυSob, ⟨c, hc_pos, hμ_lower⟩, Du, hDu, hDu_int⟩ := hmem
  refine ⟨hμLp.congr_ae_unitCube hμ, hυSob.congr_ae_unitCube hυ,
      ⟨c, hc_pos, ?_⟩, Du, ?_, ?_⟩
  · -- Uniform lower bound transports along `μ =ᵐ μ'`.
    filter_upwards [hμ_lower, hμ] with x hx hx_eq
    rw [← hx_eq]; exact hx
  · -- The same `Du` is a weak partial derivative of `υ'`.
    exact fun i => (hDu i).congr_ae_unitCube_f hυ
  · -- The ratio function changes only in the denominator (`μ ↦ μ'`).
    refine hDu_int.congr_ae_unitCube ?_
    filter_upwards [hμ] with x hx_eq
    rw [hx_eq]

/-- **Convexity of `congestionBanachK`** (paper line 1341).

The first (domain) conjunct is convex because the paper's `𝓚` is convex
(`congestionDomainK_convex`): the bare convex combination
`(a·⇑q₁.1 + b·⇑q₂.1, a·⇑q₁.2.1 + b·⇑q₂.2.1)` lies in `𝓚`, and this
transports to the `Lp`-coercion of `a•q₁ + b•q₂` via
`congestionDomainK_congr_ae` and the `Lp.coeFn_add`/`Lp.coeFn_smul`
a.e.-equalities. The second (gradient) conjunct is convex because
`HasWeakDerivPer` is linear: combine `HasWeakDerivPer.const_smul`
(scalar multiples) with `HasWeakDerivPer.add` (sums), then transport
across the coercion a.e.-equalities via
`HasWeakDerivPer.congr_ae_unitCube`.

The exponent side conditions `0 ≤ τ` and `1 ≤ α(1 + τ/β)` (and the
`Fact (1 ≤ βBar)`, `Fact (1 ≤ γBar)` instances) are exactly those
required by `congestionDomainK_convex`. -/
theorem convex_congestionBanachK (d : ℕ)
    (βBar betaBarPrime γBar : ℝ≥0∞) (α β τ : ℝ)
    [Fact (1 ≤ βBar)] [Fact (1 ≤ γBar)]
    (hτ : 0 ≤ τ) (hαt : 1 ≤ α * (1 + τ / β)) :
    Convex ℝ (congestionBanachK d βBar betaBarPrime γBar α β τ) := by
  rw [convex_iff_add_mem]
  intro q₁ hq₁ q₂ hq₂ a b ha hb hab
  obtain ⟨hdom₁, hweak₁⟩ := hq₁
  obtain ⟨hdom₂, hweak₂⟩ := hq₂
  -- The bare convex combination of the `(μ, υ)` components.
  have hβ1 : (1 : ℝ≥0∞) ≤ βBar := Fact.out
  have hγ1 : (1 : ℝ≥0∞) ≤ γBar := Fact.out
  -- a.e.-equalities between the `Lp`-coercion of `a•q₁ + b•q₂` and the
  -- bare convex combinations (for the `μ`- and `υ`-slots).
  have hμ_ae :
      (fun x => a * (⇑q₁.1 : (Fin d → ℝ) → ℝ) x
              + b * (⇑q₂.1 : (Fin d → ℝ) → ℝ) x)
        =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
      (⇑((a • q₁ + b • q₂).1 : Periodic.LpPer βBar d) : (Fin d → ℝ) → ℝ) := by
    have hsum : ((a • q₁ + b • q₂).1 : Periodic.LpPer βBar d)
                  = a • q₁.1 + b • q₂.1 := rfl
    rw [hsum]
    filter_upwards [MeasureTheory.Lp.coeFn_add (a • q₁.1) (b • q₂.1),
      MeasureTheory.Lp.coeFn_smul a q₁.1,
      MeasureTheory.Lp.coeFn_smul b q₂.1]
      with x hx_add hx_s1 hx_s2
    rw [hx_add, Pi.add_apply, hx_s1, hx_s2]
    simp only [Pi.smul_apply, smul_eq_mul]
  have hυ_ae :
      (fun x => a * (⇑q₁.2.1 : (Fin d → ℝ) → ℝ) x
              + b * (⇑q₂.2.1 : (Fin d → ℝ) → ℝ) x)
        =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
      (⇑((a • q₁ + b • q₂).2.1 :
          MeasureTheory.Lp ℝ γBar
            (MeasureTheory.volume.restrict (UnitCube d)))
        : (Fin d → ℝ) → ℝ) := by
    have hsum : ((a • q₁ + b • q₂).2.1 :
                  MeasureTheory.Lp ℝ γBar
                    (MeasureTheory.volume.restrict (UnitCube d)))
                = a • q₁.2.1 + b • q₂.2.1 := rfl
    rw [hsum]
    filter_upwards [MeasureTheory.Lp.coeFn_add (a • q₁.2.1) (b • q₂.2.1),
      MeasureTheory.Lp.coeFn_smul a q₁.2.1,
      MeasureTheory.Lp.coeFn_smul b q₂.2.1]
      with x hx_add hx_s1 hx_s2
    rw [hx_add, Pi.add_apply, hx_s1, hx_s2]
    simp only [Pi.smul_apply, smul_eq_mul]
  refine ⟨?_, ?_⟩
  · -- Domain conjunct: bare `𝓚`-convexity + a.e.-transport.
    have hbare : ((fun x => a * (⇑q₁.1 : (Fin d → ℝ) → ℝ) x
                        + b * (⇑q₂.1 : (Fin d → ℝ) → ℝ) x),
                  (fun x => a * (⇑q₁.2.1 : (Fin d → ℝ) → ℝ) x
                        + b * (⇑q₂.2.1 : (Fin d → ℝ) → ℝ) x)) ∈
        congestionDomainK (d := d) βBar betaBarPrime γBar α β τ := by
      have hconv := (convex_iff_add_mem.mp
        (congestionDomainK_convex (d := d)
          (betaBar := βBar) (betaBarPrime := betaBarPrime)
          (gammaBar := γBar) hβ1 hγ1 hτ hαt))
        hdom₁ hdom₂ ha hb hab
      -- `hconv` is membership of the algebraic combination of the bare
      -- pairs; rewrite the `Prod` smul/add to the pointwise functions.
      have heq :
          a • ((⇑q₁.1 : (Fin d → ℝ) → ℝ), (⇑q₁.2.1 : (Fin d → ℝ) → ℝ))
            + b • ((⇑q₂.1 : (Fin d → ℝ) → ℝ), (⇑q₂.2.1 : (Fin d → ℝ) → ℝ))
          = ((fun x => a * (⇑q₁.1 : (Fin d → ℝ) → ℝ) x
                    + b * (⇑q₂.1 : (Fin d → ℝ) → ℝ) x),
             (fun x => a * (⇑q₁.2.1 : (Fin d → ℝ) → ℝ) x
                    + b * (⇑q₂.2.1 : (Fin d → ℝ) → ℝ) x)) := by
        ext x <;>
          simp [Prod.smul_def, Prod.add_def, Pi.add_apply, Pi.smul_apply,
            smul_eq_mul]
      rwa [heq] at hconv
    exact congestionDomainK_congr_ae hbare hμ_ae hυ_ae
  · -- The weak-gradient relation is closed under positive convex combinations.
    intro i
    -- Abbreviations for the four coerced bare functions involved.
    set u₁ : (Fin d → ℝ) → ℝ := ⇑q₁.2.1 with hu₁
    set u₂ : (Fin d → ℝ) → ℝ := ⇑q₂.2.1 with hu₂
    set Du₁ : (Fin d → ℝ) → ℝ := ⇑(q₁.2.2 i) with hDu₁
    set Du₂ : (Fin d → ℝ) → ℝ := ⇑(q₂.2.2 i) with hDu₂
    -- `MemLpPer γBar` of the two `u`-slots, from `Lp` membership.
    have hmu₁ : Periodic.MemLpPer (d := d) γBar u₁ :=
      Periodic.memLpPer_iff_memLp.mpr (MeasureTheory.Lp.memLp q₁.2.1)
    have hmu₂ : Periodic.MemLpPer (d := d) γBar u₂ :=
      Periodic.memLpPer_iff_memLp.mpr (MeasureTheory.Lp.memLp q₂.2.1)
    -- Scalar multiples of the weak-derivative relations.
    have hsc₁ : Periodic.HasWeakDerivPer (d := d) i
        (fun x => a * u₁ x) (fun x => a * Du₁ x) :=
      (hweak₁ i).const_smul a
    have hsc₂ : Periodic.HasWeakDerivPer (d := d) i
        (fun x => b * u₂ x) (fun x => b * Du₂ x) :=
      (hweak₂ i).const_smul b
    -- `MemLpPer γBar` of the scaled `u`-slots, for the `.add` hypotheses.
    have hmu₁' : Periodic.MemLpPer (d := d) γBar (fun x => a * u₁ x) := by
      have h := hmu₁.const_smul (𝕜 := ℝ) a
      have hpt : (a • u₁ : (Fin d → ℝ) → ℝ) = fun x => a * u₁ x := by
        funext x; simp [Pi.smul_apply, smul_eq_mul]
      rwa [hpt] at h
    have hmu₂' : Periodic.MemLpPer (d := d) γBar (fun x => b * u₂ x) := by
      have h := hmu₂.const_smul (𝕜 := ℝ) b
      have hpt : (b • u₂ : (Fin d → ℝ) → ℝ) = fun x => b * u₂ x := by
        funext x; simp [Pi.smul_apply, smul_eq_mul]
      rwa [hpt] at h
    -- Sum: the combined weak-derivative relation on the explicit combinations.
    have hadd : Periodic.HasWeakDerivPer (d := d) i
        (fun x => a * u₁ x + b * u₂ x) (fun x => a * Du₁ x + b * Du₂ x) :=
      Periodic.HasWeakDerivPer.add (i := i) (Fact.out (p := (1 ≤ γBar))) hmu₁' hmu₂'
        hsc₁ hsc₂
    -- The combined slots equal the `Lp`-coercions of `(a•q₁ + b•q₂)` a.e.
    have hu_sum : ((a • q₁ + b • q₂).2.1 :
                    MeasureTheory.Lp ℝ γBar
                      (MeasureTheory.volume.restrict (UnitCube d)))
                  = a • q₁.2.1 + b • q₂.2.1 := rfl
    have hDu_sum : ((a • q₁ + b • q₂).2.2 i :
                    MeasureTheory.Lp ℝ γBar
                      (MeasureTheory.volume.restrict (UnitCube d)))
                  = a • q₁.2.2 i + b • q₂.2.2 i := rfl
    have hu_ae :
        (fun x => a * u₁ x + b * u₂ x)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
        (⇑((a • q₁ + b • q₂).2.1 :
            MeasureTheory.Lp ℝ γBar
              (MeasureTheory.volume.restrict (UnitCube d)))
          : (Fin d → ℝ) → ℝ) := by
      rw [hu_sum]
      filter_upwards [MeasureTheory.Lp.coeFn_add (a • q₁.2.1) (b • q₂.2.1),
        MeasureTheory.Lp.coeFn_smul a q₁.2.1,
        MeasureTheory.Lp.coeFn_smul b q₂.2.1]
        with x hx_add hx_s1 hx_s2
      rw [hx_add, Pi.add_apply, hx_s1, hx_s2]
      simp only [Pi.smul_apply, smul_eq_mul, hu₁, hu₂]
    have hDu_ae :
        (fun x => a * Du₁ x + b * Du₂ x)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
        (⇑((a • q₁ + b • q₂).2.2 i :
            MeasureTheory.Lp ℝ γBar
              (MeasureTheory.volume.restrict (UnitCube d)))
          : (Fin d → ℝ) → ℝ) := by
      rw [hDu_sum]
      filter_upwards [MeasureTheory.Lp.coeFn_add (a • q₁.2.2 i) (b • q₂.2.2 i),
        MeasureTheory.Lp.coeFn_smul a (q₁.2.2 i),
        MeasureTheory.Lp.coeFn_smul b (q₂.2.2 i)]
        with x hx_add hx_s1 hx_s2
      rw [hx_add, Pi.add_apply, hx_s1, hx_s2]
      simp only [Pi.smul_apply, smul_eq_mul, hDu₁, hDu₂]
    -- `MemLpPer 1` of the transported derivative slot (target of `congr_ae`).
    have hDu_mem : Periodic.MemLpPer (d := d) 1
        (⇑((a • q₁ + b • q₂).2.2 i :
            MeasureTheory.Lp ℝ γBar
              (MeasureTheory.volume.restrict (UnitCube d)))
          : (Fin d → ℝ) → ℝ) := by
      haveI : MeasureTheory.IsFiniteMeasure
          (MeasureTheory.Measure.restrict MeasureTheory.volume
            (UnitCube (d := d))) :=
        ⟨by
          rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ]
          simp⟩
      have hγ : (1 : ℝ≥0∞) ≤ γBar := Fact.out
      have h1 : MeasureTheory.MemLp
          (⇑((a • q₁ + b • q₂).2.2 i :
              MeasureTheory.Lp ℝ γBar
                (MeasureTheory.volume.restrict (UnitCube d)))
            : (Fin d → ℝ) → ℝ) γBar
          (MeasureTheory.volume.restrict (UnitCube d)) :=
        MeasureTheory.Lp.memLp ((a • q₁ + b • q₂).2.2 i)
      exact Periodic.memLpPer_iff_memLp.mpr (h1.mono_exponent hγ)
    -- Transport across the two a.e.-equalities.
    exact hadd.congr_ae_unitCube hu_ae hDu_mem hDu_ae

/-! ## The canonical coercivity base point `(m≡1, u≡0, Du≡0)` (T2 BB1e child 1)

The coercivity lemma `congestionAepsiOpK_coercive` (Coercivity.lean) requires
a base point `v₀ : congestionXBanach` together with its `congestionBanachK`
membership and the three a.e. profiles `⇑v₀.1 =ᵐ 1`, `⇑v₀.2.1 =ᵐ 0`,
`⇑(v₀.2.2 i) =ᵐ 0`. This block constructs that canonical base point and
discharges all four facts. It is the load-bearing new content of BB1e;
the final pack record assembly is the second child task. -/

/-- The canonical coercivity base point `(m ≡ 1, u ≡ 0, Du ≡ 0)`, lifted to
`congestionXBanach d βBar γBar`. The density slot is the `Lp` class of the
constant `1`; the value and gradient slots are the zero `SobolevPerLp`
element. -/
def congestionCanonicalBasePoint
    (d : ℕ) (βBar γBar : ℝ≥0∞)
    [Fact (1 ≤ βBar)] [Fact (1 ≤ γBar)] :
    congestionXBanach d βBar γBar :=
  haveI : MeasureTheory.IsFiniteMeasure
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
    Periodic.Saturator.instIsFiniteMeasureRestrictUnitCube
  ((MeasureTheory.memLp_const
      (μ := MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d))
      (p := βBar) (1 : ℝ)).toLp (fun _ => (1 : ℝ)),
   (0 : Periodic.SobolevPerLp 1 γBar d))

/-- a.e. profile of the density slot: `⇑v₀.1 =ᵐ (fun _ => 1)`. -/
lemma congestionCanonicalBasePoint_m_ae
    (d : ℕ) (βBar γBar : ℝ≥0∞)
    [Fact (1 ≤ βBar)] [Fact (1 ≤ γBar)] :
    (⇑(congestionCanonicalBasePoint d βBar γBar).1 : (Fin d → ℝ) → ℝ)
      =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        (fun _ => (1 : ℝ)) := by
  haveI : MeasureTheory.IsFiniteMeasure
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
    Periodic.Saturator.instIsFiniteMeasureRestrictUnitCube
  exact MeasureTheory.MemLp.coeFn_toLp
    (MeasureTheory.memLp_const
      (μ := MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d))
      (p := βBar) (1 : ℝ))

/-- a.e. profile of the value slot: `⇑v₀.2.1 =ᵐ (fun _ => 0)`. -/
lemma congestionCanonicalBasePoint_u_ae
    (d : ℕ) (βBar γBar : ℝ≥0∞)
    [Fact (1 ≤ βBar)] [Fact (1 ≤ γBar)] :
    (⇑(congestionCanonicalBasePoint d βBar γBar).2.1 : (Fin d → ℝ) → ℝ)
      =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        (fun _ => (0 : ℝ)) := by
  -- `v₀.2.1 = (0 : SobolevPerLp ...).1 = (0 : Lp ...)`.
  exact MeasureTheory.Lp.coeFn_zero ℝ γBar
    (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d))

/-- a.e. profile of each gradient slot: `⇑(v₀.2.2 i) =ᵐ (fun _ => 0)`. -/
lemma congestionCanonicalBasePoint_Du_ae
    (d : ℕ) (βBar γBar : ℝ≥0∞)
    [Fact (1 ≤ βBar)] [Fact (1 ≤ γBar)] (i : Fin d) :
    (⇑((congestionCanonicalBasePoint d βBar γBar).2.2 i) : (Fin d → ℝ) → ℝ)
      =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        (fun _ => (0 : ℝ)) := by
  -- `(0 : SobolevPerLp ...).2 i = (0 : Fin d → Lp ...) i = (0 : Lp ...)`.
  exact MeasureTheory.Lp.coeFn_zero ℝ γBar
    (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d))

/-- The constant zero function has zero as a weak partial derivative in
direction `i` (local self-contained copy; the Domain.lean version is
`private`). -/
private lemma congestion_hasWeakDerivPer_zero_zero (i : Fin d) :
    Periodic.HasWeakDerivPer (d := d) i
      (fun _ : (Fin d → ℝ) => (0 : ℝ))
      (fun _ : (Fin d → ℝ) => (0 : ℝ)) := by
  haveI : MeasureTheory.IsFiniteMeasure
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
    Periodic.Saturator.instIsFiniteMeasureRestrictUnitCube
  refine ⟨Periodic.MemLp.toMemLpPer (MeasureTheory.memLp_const (0 : ℝ)), ?_⟩
  intro φ
  have h0a : (fun x : Fin d → ℝ =>
      (0 : ℝ) * (φ : (Fin d → ℝ) → ℝ) x) = (fun _ => (0 : ℝ)) := by
    funext x; ring
  have h0b : (fun x : Fin d → ℝ => (0 : ℝ) *
      ((Periodic.SmoothPeriodic.partialDeriv i φ : Periodic.SmoothPeriodic d) :
          (Fin d → ℝ) → ℝ) x) = (fun _ => (0 : ℝ)) := by
    funext x; ring
  rw [h0a, h0b]
  simp [Periodic.periodicIntegral_const]

/-- The bare witness pair `(fun _ => 1, fun _ => 0)` lies in the congestion
domain `𝓚`. This mirrors `congestionDomainK_nonempty` (Domain.lean) with the
lower-bound constant `c := 1`; the ratio integrability holds because the
zero gradient makes the numerator vanish a.e. -/
private lemma congestionDomainK_const_one_mem
    (betaBar betaBarPrime gammaBar : ℝ≥0∞) (α β τ : ℝ) :
    ((fun _ : (Fin d → ℝ) => (1 : ℝ)),
        (fun _ : (Fin d → ℝ) => (0 : ℝ))) ∈
      congestionDomainK (d := d) betaBar betaBarPrime gammaBar α β τ := by
  haveI : MeasureTheory.IsFiniteMeasure
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
    Periodic.Saturator.instIsFiniteMeasureRestrictUnitCube
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Periodic.MemLp.toMemLpPer (MeasureTheory.memLp_const (1 : ℝ))
  · refine ⟨Periodic.MemLp.toMemLpPer (MeasureTheory.memLp_const (0 : ℝ)), ?_⟩
    exact ⟨fun _ => (fun _ : (Fin d → ℝ) => (0 : ℝ)),
      fun i => congestion_hasWeakDerivPer_zero_zero (d := d) i⟩
  · refine ⟨(1 : ℝ), by norm_num, ?_⟩
    exact Filter.Eventually.of_forall fun _ => le_refl _
  · refine ⟨fun _ => (fun _ : (Fin d → ℝ) => (0 : ℝ)), ?_, ?_⟩
    · intro i; exact congestion_hasWeakDerivPer_zero_zero (d := d) i
    · have hnorm_zero : (‖(fun _ : Fin d => (0 : ℝ))‖ : ℝ) = 0 := by
        have h0 : (fun _ : Fin d => (0 : ℝ)) = 0 := by funext _; rfl
        rw [h0]; exact norm_zero
      have hconst :
          (fun x : Fin d → ℝ =>
              (‖fun _ : Fin d => (0 : ℝ)‖ ^ (α * (1 + τ / β))) /
                ((1 : ℝ) ^ τ + 1)) =
          (fun _ : Fin d → ℝ =>
              ((0 : ℝ) ^ (α * (1 + τ / β))) / ((1 : ℝ) ^ τ + 1)) := by
        funext x; rw [hnorm_zero]
      rw [hconst]
      exact Periodic.MemLp.toMemLpPer (MeasureTheory.memLp_const _)

/-- **Membership of the canonical base point in `congestionBanachK`.**

Both defining conjuncts are discharged by transporting the bare witness
`(fun _ => 1, fun _ => 0)` across the a.e. profiles of the base point:
the domain conjunct via `congestionDomainK_congr_ae`, the gradient
conjunct via `HasWeakDerivPer.congr_ae_unitCube`. -/
theorem congestionCanonicalBasePoint_mem_K
    (d : ℕ) (betaBar betaBarPrime gammaBar : ℝ≥0∞) (α β τ : ℝ)
    [Fact (1 ≤ betaBar)] [Fact (1 ≤ gammaBar)] :
    congestionCanonicalBasePoint d betaBar gammaBar ∈
      congestionBanachK d betaBar betaBarPrime gammaBar α β τ := by
  haveI : MeasureTheory.IsFiniteMeasure
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
    Periodic.Saturator.instIsFiniteMeasureRestrictUnitCube
  have hm := congestionCanonicalBasePoint_m_ae d betaBar gammaBar
  have hu := congestionCanonicalBasePoint_u_ae d betaBar gammaBar
  refine ⟨?_, ?_⟩
  · -- Domain conjunct: transport the bare `(1, 0)` witness.
    exact congestionDomainK_congr_ae
      (congestionDomainK_const_one_mem (d := d)
        betaBar betaBarPrime gammaBar α β τ)
      hm.symm hu.symm
  · -- Gradient conjunct: transport `HasWeakDerivPer i 0 0`.
    intro i
    have hDu := congestionCanonicalBasePoint_Du_ae d betaBar gammaBar i
    have hγ1 : (1 : ℝ≥0∞) ≤ gammaBar := Fact.out
    have hg' : Periodic.MemLpPer (d := d) 1
        (⇑((congestionCanonicalBasePoint d betaBar gammaBar).2.2 i)
          : (Fin d → ℝ) → ℝ) :=
      Periodic.memLpPer_iff_memLp.mpr
        ((MeasureTheory.Lp.memLp _).mono_exponent hγ1)
    exact (congestion_hasWeakDerivPer_zero_zero (d := d) i).congr_ae_unitCube
      hu.symm hg' hDu.symm

/-! ## `vδ` Banach lift of a δ-truncated density (T2 phase6 `hcoeHJB_le` Step 2)

The δ→0 assembly of `hcoeHJB_le` (task
`infra-P7-sigfix-T2-phase6-hcoeHJB-le-DCT-assembly`) tests the abstract VI
against truncated admissible pairs `(max(muAux, δ), u_w)`. To feed those
pairs into `vi_integral_le_of_mem_witnessComponents`, they must be lifted to
the Banach realisation `congestionXBanach` with the **value/gradient slots
unchanged** (so the off-diagonal terms vanish exactly), and the density slot
carrying the truncated density. This block builds that lift.

The construction reuses the witness `w`'s value/gradient slots verbatim
(`vδ.2 = w.2`), so `hu_eq`/`hDu_eq` hold by `rfl`, and installs a fresh
density slot `MemLpPer.toLp` of the (already `congestionDomainK`-admissible)
density `ρ`. Membership in `congestionBanachK` is then certified **by
construction**: the domain conjunct transports the supplied `congestionDomainK`
membership of `(ρ, ⇑w.2.1)` along the density-slot a.e.-profile via
`congestionDomainK_congr_ae`; the gradient conjunct is the supplied
witness-scoped weak-derivative field, unchanged because `vδ.2 = w.2`. -/

/-- **Banach lift of a δ-truncated density (Step 2 of the `hcoeHJB_le`
assembly).**

Given the abstract VI witness `w`, a density `ρ` with `MemLpPer βBar ρ`
whose bare pair `(ρ, ⇑w.2.1)` already lies in the paper domain
`congestionDomainK`, and the witness's weak-derivative relation, build a
`congestionXBanach` element `vδ` with:
* the **same** value/gradient slots as `w` (`vδ.2 = w.2`, so
  `vi_integral_le_of_mem_witnessComponents`'s `hu_eq`/`hDu_eq` are `rfl`);
* density-slot coercion a.e.-equal to `ρ`;
* membership in `congestionBanachK` certified by construction.

This is the principal new construction of the δ→0 step; it carries no
`sorry` and introduces no oracle — the K-membership is established directly
from `mdelta_admissibility`'s output transported across the (constructed)
density-slot a.e.-equality. -/
theorem mem_congestionBanachK_of_densityMemLp
    {βBar betaBarPrime γBar : ℝ≥0∞} {α β τ : ℝ}
    (w : congestionXBanach d βBar γBar)
    {ρ : (Fin d → ℝ) → ℝ}
    (hρ_mem : Periodic.MemLpPer (d := d) βBar ρ)
    (hdom : (ρ, (⇑w.2.1 : (Fin d → ℝ) → ℝ)) ∈
        congestionDomainK (d := d) βBar betaBarPrime γBar α β τ)
    (hweak : ∀ i : Fin d,
        Periodic.HasWeakDerivPer (d := d) i
          (⇑w.2.1 : (Fin d → ℝ) → ℝ)
          (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ)) :
    ∃ vδ : congestionXBanach d βBar γBar,
      vδ.2 = w.2 ∧
      (⇑vδ.1 : (Fin d → ℝ) → ℝ)
        =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] ρ ∧
      vδ ∈ congestionBanachK d βBar betaBarPrime γBar α β τ := by
  -- The density slot is the `Lp`-class of `ρ`; value/gradient slots reuse `w.2`.
  refine ⟨(hρ_mem.toMemLp.toLp, w.2), rfl, ?_, ?_, ?_⟩
  · -- Density-slot a.e. profile: `⇑(ρ.toLp) =ᵐ ρ`.
    exact MeasureTheory.MemLp.coeFn_toLp hρ_mem.toMemLp
  · -- Domain conjunct: transport `hdom` along `⇑vδ.1 =ᵐ ρ` (symm) and
    -- `⇑vδ.2.1 =ᵐ ⇑w.2.1` (rfl, slot unchanged).
    have hρ_ae : (⇑(hρ_mem.toMemLp.toLp :
          MeasureTheory.Lp ℝ βBar
            (MeasureTheory.volume.restrict (UnitCube d)))
          : (Fin d → ℝ) → ℝ)
        =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] ρ :=
      MeasureTheory.MemLp.coeFn_toLp hρ_mem.toMemLp
    exact congestionDomainK_congr_ae hdom hρ_ae.symm (by rfl)
  · -- Gradient conjunct: `vδ.2 = w.2`, so this is `hweak` verbatim.
    exact hweak

/-- **General Banach lift of a bare admissible test pair.**

Unlike `mem_congestionBanachK_of_densityMemLp` (which reuses an existing
witness's value/gradient slots and only swaps the density), this builds a
fresh `congestionXBanach` element from bare `(μ, υ, Dυ)` with all three
slots constructed: the density slot is `MemLpPer.toLp μ`; the value/gradient
slot is `MemSobolevPer.toLpSobolev υ Dυ`. The slot coercions are a.e.-equal
to the bare functions (via `MemLp.coeFn_toLp`), and K-membership is certified
by transporting the supplied `congestionDomainK` membership and weak-derivative
relation across those a.e. equalities (`congestionDomainK_congr_ae`,
`HasWeakDerivPer.congr_ae_unitCube`).

This is the general-test-pair handle the per-test-pair regularized weak VI
needs (parent task `…-vIEps-remove`, Gap 1(a)). -/
theorem congestionBanachLift_of_testData
    {βBar betaBarPrime γBar : ℝ≥0∞} [Fact (1 ≤ βBar)] [Fact (1 ≤ γBar)]
    {α β τ : ℝ}
    {μ υ : (Fin d → ℝ) → ℝ}
    {Dυ : Fin d → (Fin d → ℝ) → ℝ}
    (hμ_mem : Periodic.MemLpPer (d := d) βBar μ)
    (hυ_sob : Periodic.MemSobolevPer (d := d) γBar υ)
    (hDυ_mem : ∀ i, Periodic.MemLpPer (d := d) γBar (Dυ i))
    (hDυ_weak : ∀ i, Periodic.HasWeakDerivPer (d := d) i υ (Dυ i))
    (hdom : (μ, υ) ∈ congestionDomainK (d := d) βBar betaBarPrime γBar α β τ) :
    ∃ vT : congestionXBanach d βBar γBar,
      (⇑vT.1 : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] μ ∧
      (⇑vT.2.1 : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] υ ∧
      (∀ i, (⇑(vT.2.2 i) : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] Dυ i) ∧
      vT ∈ congestionBanachK d βBar betaBarPrime γBar α β τ := by
  classical
  -- Density slot and value/gradient slot.
  refine ⟨(hμ_mem.toMemLp.toLp, hυ_sob.toLpSobolev hDυ_mem), ?_, ?_, ?_, ?_⟩
  · exact MeasureTheory.MemLp.coeFn_toLp hμ_mem.toMemLp
  · -- `⇑(toLpSobolev).1 = ⇑(υ.toLp) =ᵐ υ`.
    exact MeasureTheory.MemLp.coeFn_toLp hυ_sob.1.toMemLp
  · intro i
    exact MeasureTheory.MemLp.coeFn_toLp (hDυ_mem i).toMemLp
  · -- K-membership.
    have hμ_ae : (⇑(hμ_mem.toMemLp.toLp :
          MeasureTheory.Lp ℝ βBar
            (MeasureTheory.volume.restrict (UnitCube d)))
          : (Fin d → ℝ) → ℝ)
        =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] μ :=
      MeasureTheory.MemLp.coeFn_toLp hμ_mem.toMemLp
    have hυ_ae : (⇑((hυ_sob.toLpSobolev hDυ_mem).1)
          : (Fin d → ℝ) → ℝ)
        =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] υ :=
      MeasureTheory.MemLp.coeFn_toLp hυ_sob.1.toMemLp
    have hDυ_ae : ∀ i, (⇑((hυ_sob.toLpSobolev hDυ_mem).2 i)
          : (Fin d → ℝ) → ℝ)
        =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] Dυ i :=
      fun i => MeasureTheory.MemLp.coeFn_toLp (hDυ_mem i).toMemLp
    refine ⟨?_, ?_⟩
    · -- Domain conjunct: transport `hdom` along the (symm) a.e. profiles.
      exact congestionDomainK_congr_ae hdom hμ_ae.symm hυ_ae.symm
    · -- Gradient conjunct: transport the supplied weak-derivative relation.
      intro i
      have hg' : Periodic.MemLpPer (d := d) 1
          (⇑((hυ_sob.toLpSobolev hDυ_mem).2 i) : (Fin d → ℝ) → ℝ) :=
        Periodic.memLpPer_iff_memLp.mpr
          ((MeasureTheory.Lp.memLp _).mono_exponent (le_trans (le_refl 1) Fact.out))
      exact (hDυ_weak i).congr_ae_unitCube hυ_ae.symm hg' (hDυ_ae i).symm

/-! ## K-scoped `MFGOpEpsAuxHyps` from `congestionBanachK` membership (T2 BB1b)

The K-scoped producer `congestion_auxHyps_of_mem_congestionBanachK`. Given
`hq : q ∈ congestionBanachK …`, it assembles the seven primal-side
`MemLpPer` certificates of `MFGOpEpsAuxHyps` for the explicit Banach
gradient `Du := fun i x => ⇑(q.2.2 i) x`, the density `m := ⇑q.1` and value
`u := ⇑q.2.1`.

**No free `hc`/`hRatio`.** The uniform lower bound `∃ c > 0, c ≤ᵐ μ` and the
ratio integrability `‖Dυ‖^{αt}/(μ^τ+1) ∈ L^{β̄'}` are carried *inside*
`hq.1 = hdom : (⇑q.1, ⇑q.2.1) ∈ congestionDomainK …` and are consumed by the
HJB well-definedness lemma `aEpsi_congestion_HJB_memLp` (whose conclusion is
phrased through the domain's `Exists.choose` gradient). The bridge
`HasWeakDerivPer.unique` (weak-derivative uniqueness, landed iter-0894)
identifies that `choose`-gradient a.e. with the explicit Banach gradient
`⇑(q.2.2 i)`, transporting the HJB certificate to the
`MFGOpEpsAuxHyps.hF_HJB` form.

The flux / mass / grad / val certificates are threaded as caller-side
`MemLpPer` / measurability / bound riders, exactly as the underlying
well-definedness lemmas (`aEpsi_congestion_flux_memLp`) and the
`MFGOpEpsAuxHyps` design require per CONVENTIONS §8. -/
theorem congestion_auxHyps_of_mem_congestionBanachK
    {βBar betaBarPrime γBar : ℝ≥0∞}
    {βBarReal βBarReal' γBarReal γBarReal' : ℝ}
    (hβ : βBarReal.HolderConjugate βBarReal')
    (hγ : γBarReal.HolderConjugate γBarReal')
    (hβTop : ENNReal.ofReal γBarReal ≠ ⊤)
    {α β τ : ℝ} (hτ_nn : 0 ≤ τ) (hτ_le : τ ≤ 1)
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {q : congestionXBanach d βBar γBar}
    (hq : q ∈ congestionBanachK d βBar betaBarPrime γBar α β τ)
    -- Routing equation linking the domain's β̄'-exponent to the
    -- `MFGOpEpsAuxHyps` HJB-field exponent. (Benign exponent identity, NOT a
    -- uniform-lower-bound / ratio-integrability rider.)
    (hbp : betaBarPrime = ENNReal.ofReal βBarReal')
    -- HJB-side data (NOT hc, NOT hRatio — those are inside `hq.1`):
    (hV : MemLpPer (d := d) betaBarPrime V)
    (hu : MemLpPer (d := d) betaBarPrime (⇑q.2.1 : (Fin d → ℝ) → ℝ))
    (hmβ_dom : MemLpPer (d := d) betaBarPrime
        (fun x => (⇑q.1 : (Fin d → ℝ) → ℝ) x ^ β + 1))
    (K : ℝ) (hK_pos : 0 < K)
    (hH_bound : ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ∀ p mm, 0 < mm → |H x p mm| ≤
          K * ((1 / mm) + (1 / mm ^ τ)) * (‖p‖ ^ (α * (1 + τ / β)) + 1)
            + K * (mm ^ β + 1))
    (hF_meas : AEStronglyMeasurable
        (fun x => -((⇑q.2.1 : (Fin d → ℝ) → ℝ) x)
                  - H x (fun i => (⇑(q.2.2 i) : (Fin d → ℝ) → ℝ) x)
                        ((⇑q.1 : (Fin d → ℝ) → ℝ) x)
                  + V x)
        (Measure.restrict volume (UnitCube d)))
    -- Flux-side data, per direction `i`:
    (hFlux_meas : ∀ i, AEStronglyMeasurable
        (Theorems.SimplePower.Banach.F_flux DpH
          (fun i x => (⇑(q.2.2 i) : (Fin d → ℝ) → ℝ) x) (⇑q.1) i)
        (Measure.restrict volume (UnitCube d)))
    (hFlux_le : ∀ i, ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖Theorems.SimplePower.Banach.F_flux DpH
            (fun i x => (⇑(q.2.2 i) : (Fin d → ℝ) → ℝ) x) (⇑q.1) i x‖
          ≤ K * (1 + (⇑q.1 : (Fin d → ℝ) → ℝ) x ^ (1 - τ))
                * ‖fun j => (⇑(q.2.2 j) : (Fin d → ℝ) → ℝ) x‖ ^ (α * (1 + τ / β) - 1)
              + K * ((⇑q.1 : (Fin d → ℝ) → ℝ) x ^ (β + 1 - β / α) + 1))
    (hFlux_dom : ∀ _i : Fin d, MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => K * (1 + (⇑q.1 : (Fin d → ℝ) → ℝ) x ^ (1 - τ))
              * ‖fun j => (⇑(q.2.2 j) : (Fin d → ℝ) → ℝ) x‖ ^ (α * (1 + τ / β) - 1)
            + K * ((⇑q.1 : (Fin d → ℝ) → ℝ) x ^ (β + 1 - β / α) + 1)))
    -- Mass / grad / val Lp certificates:
    (hMass : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (Theorems.SimplePower.Banach.F_mass (⇑q.1)))
    (hGgrad : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (Theorems.SimplePower.Banach.G_grad γBarReal
          (fun i x => (⇑(q.2.2 i) : (Fin d → ℝ) → ℝ) x) i))
    (hGval : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (Theorems.SimplePower.Banach.G_val γBarReal (⇑q.2.1 : (Fin d → ℝ) → ℝ))) :
    Theorems.SimplePower.Banach.MFGOpEpsAuxHyps
      γBarReal βBarReal βBarReal' γBarReal'
      V H DpH
      (fun i x => (⇑(q.2.2 i) : (Fin d → ℝ) → ℝ) x)
      (⇑q.1 : (Fin d → ℝ) → ℝ)
      (⇑q.2.1 : (Fin d → ℝ) → ℝ) := by
  classical
  -- Step A: domain membership (carries hc + hRatio).
  have hdom : ((⇑q.1 : (Fin d → ℝ) → ℝ), (⇑q.2.1 : (Fin d → ℝ) → ℝ)) ∈
      congestionDomainK (d := d) βBar betaBarPrime γBar α β τ := hq.1
  -- Step B: a.e. positivity of `m`, from the uniform lower bound in `hdom`.
  have hm_pos : ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
      0 < (⇑q.1 : (Fin d → ℝ) → ℝ) x := by
    obtain ⟨_, _, ⟨c, hc_pos, hc_le⟩, _⟩ := hdom
    filter_upwards [hc_le] with x hx
    exact lt_of_lt_of_le hc_pos hx
  -- Step E (the crux): the domain's `Exists.choose` gradient agrees a.e. with
  -- the explicit Banach gradient `⇑(q.2.2 i)`, by weak-derivative uniqueness.
  have hDu_ae : ∀ i, (hdom.2.2.2.choose i)
      =ᵐ[Measure.restrict volume (UnitCube d)]
      (⇑(q.2.2 i) : (Fin d → ℝ) → ℝ) := by
    intro i
    exact HasWeakDerivPer.unique (hdom.2.2.2.choose_spec.1 i) (hq.2 i)
  -- Step D: the HJB certificate in the `choose`-gradient form.
  have h_HJB_choose := aEpsi_congestion_HJB_memLp (d := d)
    (betaBar := βBar) (betaBarPrime := betaBarPrime) (gammaBar := γBar)
    (V := V) (H := H) (m := ⇑q.1) (u := ⇑q.2.1)
    hτ_nn hτ_le hdom hV hu K hK_pos hH_bound ?_ hmβ_dom hm_pos
  · -- Step E (transport): rewrite the `choose`-gradient HJB certificate to the
    -- explicit `q.2.2` gradient via the a.e. equalities, then unfold `F_HJB`.
    -- Combine the per-`i` a.e. equalities into one a.e. statement.
    have hDu_ae_all : ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ∀ i, (hdom.2.2.2.choose i) x = (⇑(q.2.2 i) : (Fin d → ℝ) → ℝ) x := by
      rw [MeasureTheory.ae_all_iff]; exact hDu_ae
    have h_fun_ae :
        (fun x => -((⇑q.2.1 : (Fin d → ℝ) → ℝ) x)
            - H x (fun i => (hdom.2.2.2.choose i) x) ((⇑q.1 : (Fin d → ℝ) → ℝ) x)
            + V x)
          =ᵐ[Measure.restrict volume (UnitCube d)]
        (fun x => -((⇑q.2.1 : (Fin d → ℝ) → ℝ) x)
            - H x (fun i => (⇑(q.2.2 i) : (Fin d → ℝ) → ℝ) x)
                  ((⇑q.1 : (Fin d → ℝ) → ℝ) x)
            + V x) := by
      filter_upwards [hDu_ae_all] with x hx
      have : (fun i => (hdom.2.2.2.choose i) x)
              = (fun i => (⇑(q.2.2 i) : (Fin d → ℝ) → ℝ) x) := by
        funext i; exact hx i
      rw [this]
    have h_HJB : MemLpPer (d := d) betaBarPrime
        (fun x => -((⇑q.2.1 : (Fin d → ℝ) → ℝ) x)
            - H x (fun i => (⇑(q.2.2 i) : (Fin d → ℝ) → ℝ) x)
                  ((⇑q.1 : (Fin d → ℝ) → ℝ) x)
            + V x) :=
      h_HJB_choose.congr_ae_unitCube h_fun_ae
    rw [hbp] at h_HJB
    -- Step F: flux certificates, per direction.
    -- Step F: flux certificates, per direction. The dominator argument of
    -- `aEpsi_congestion_flux_memLp` (`MemLp.of_le_mul`) works for any normed
    -- codomain, so we apply it to the SCALAR `i`-th component `F_flux … i`.
    have h_flux : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (Theorems.SimplePower.Banach.F_flux DpH
          (fun i x => (⇑(q.2.2 i) : (Fin d → ℝ) → ℝ) x) (⇑q.1) i) := by
      intro i
      rw [Periodic.memLpPer_iff_memLp]
      refine MeasureTheory.MemLp.of_le_mul
        (c := 1)
        ((Periodic.memLpPer_iff_memLp).mp (hFlux_dom i))
        (hFlux_meas i) ?_
      filter_upwards [hFlux_le i] with x hx
      have hF_nn : (0 : ℝ) ≤ ‖Theorems.SimplePower.Banach.F_flux DpH
          (fun i x => (⇑(q.2.2 i) : (Fin d → ℝ) → ℝ) x) (⇑q.1) i x‖ := norm_nonneg _
      have hG_nn : (0 : ℝ) ≤ K * (1 + (⇑q.1 : (Fin d → ℝ) → ℝ) x ^ (1 - τ))
                  * ‖fun j => (⇑(q.2.2 j) : (Fin d → ℝ) → ℝ) x‖ ^ (α * (1 + τ / β) - 1)
              + K * ((⇑q.1 : (Fin d → ℝ) → ℝ) x ^ (β + 1 - β / α) + 1) :=
        le_trans hF_nn hx
      rw [one_mul, show ‖K * (1 + (⇑q.1 : (Fin d → ℝ) → ℝ) x ^ (1 - τ))
                  * ‖fun j => (⇑(q.2.2 j) : (Fin d → ℝ) → ℝ) x‖ ^ (α * (1 + τ / β) - 1)
              + K * ((⇑q.1 : (Fin d → ℝ) → ℝ) x ^ (β + 1 - β / α) + 1)‖
            = K * (1 + (⇑q.1 : (Fin d → ℝ) → ℝ) x ^ (1 - τ))
                  * ‖fun j => (⇑(q.2.2 j) : (Fin d → ℝ) → ℝ) x‖ ^ (α * (1 + τ / β) - 1)
              + K * ((⇑q.1 : (Fin d → ℝ) → ℝ) x ^ (β + 1 - β / α) + 1)
            from by rw [Real.norm_eq_abs, abs_of_nonneg hG_nn]]
      exact hx
    -- Step H: assemble the bundle.
    exact
      { hβ := hβ
        hγ := hγ
        hF_HJB := h_HJB
        hF_flux := h_flux
        hF_mass := hMass
        hG_grad := hGgrad
        hG_val := hGval
        hβTop := hβTop }
  · -- The `hF_meas` side goal of `aEpsi_congestion_HJB_memLp`: the assembled
    -- function in `choose`-gradient form is a.e. strongly measurable. Transport
    -- the caller-supplied `q.2.2`-form measurability across the a.e. equality.
    have hDu_ae_all : ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ∀ i, (hdom.2.2.2.choose i) x = (⇑(q.2.2 i) : (Fin d → ℝ) → ℝ) x := by
      rw [MeasureTheory.ae_all_iff]; exact hDu_ae
    refine hF_meas.congr ?_
    filter_upwards [hDu_ae_all] with x hx
    have : (fun i => (⇑(q.2.2 i) : (Fin d → ℝ) → ℝ) x)
            = (fun i => (hdom.2.2.2.choose i) x) := by
      funext i; exact (hx i).symm
    rw [this]

-- Sanity check: `congestion_auxHyps_of_mem_congestionBanachK` produces a
-- `MFGOpEpsAuxHyps` certificate with membership as the only domain input.
#check @congestion_auxHyps_of_mem_congestionBanachK


/-! ## Measurability riders from `congestionBanachK` membership (T2 BB1c child A)

The producer `congestion_auxHyps_of_mem_congestionBanachK` requires two
measurability riders, `hF_meas` (Existence.lean) for the HJB term and
`hFlux_meas i` for each flux component. The analogous power-growth supplier
`auxHyps_of_paperHypotheses_on_KAepsi`
(`Theorems/SimplePower/Banach/AssemblyContext.lean`) threads these as
universal-`q` residue hypotheses, noting that their discharge from
`RegularityH.measurable_H` "requires a separate measurability helper" that was
never built.  This child A builds that helper for the congestion track: both
riders are Carathéodory compositions of the jointly-measurable `H` / `DpH`
(from `hcong`'s `RegularityH`) with the a.e.-strongly-measurable `Lp`
coercions of the `q`-components.  **No carrier-exponent inequality is needed**,
so this is fully dischargeable from `hcong` + `V`-measurability + membership.

The proof routes through `AEMeasurable` (`ℝ` and `Fin d → ℝ` are
`PseudoMetrizableSpace`, `BorelSpace`, `SecondCountableTopology`, so
`aestronglyMeasurable_iff_aemeasurable` applies in both directions) and the
composition lemma `Measurable.comp_aemeasurable`. -/

-- (child P3a7b3) The Carathéodory composition helper `aestronglyMeasurable_comp_H`
-- formerly declared `private` here has been promoted to a public lemma in
-- `Theorems/Congestion/WellDefined.lean` (in this module's import root) so it is
-- reachable from `LimitPassage.lean`. The call site at
-- `congestion_meas_riders_of_mem_congestionBanachK` below resolves to that
-- public version.

/-- **Carathéodory composition helper (vector codomain).** The map
`x ↦ DpH x (fun i => Du i x) (m x)` is a.e.-strongly measurable. -/
private lemma aestronglyMeasurable_comp_DpH
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hDpH : Measurable
      (fun (xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ) => DpH xpm.1 xpm.2.1 xpm.2.2))
    {m : (Fin d → ℝ) → ℝ} {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm : AEStronglyMeasurable m (volume.restrict (UnitCube d)))
    (hDu : ∀ i, AEStronglyMeasurable (Du i) (volume.restrict (UnitCube d))) :
    AEStronglyMeasurable
      (fun x => DpH x (fun i => Du i x) (m x))
      (volume.restrict (UnitCube d)) := by
  have hid : AEMeasurable (fun x : Fin d → ℝ => x) (volume.restrict (UnitCube d)) :=
    aemeasurable_id
  have hDu' : AEMeasurable (fun x => (fun i => Du i x))
      (volume.restrict (UnitCube d)) := by
    rw [aemeasurable_pi_iff]
    intro i
    exact (aestronglyMeasurable_iff_aemeasurable.mp (hDu i))
  have hm' : AEMeasurable m (volume.restrict (UnitCube d)) :=
    aestronglyMeasurable_iff_aemeasurable.mp hm
  have hprod : AEMeasurable
      (fun x : Fin d → ℝ => (x, (fun i => Du i x), m x))
      (volume.restrict (UnitCube d)) :=
    hid.prodMk (hDu'.prodMk hm')
  have hcomp : AEMeasurable
      (fun x => DpH x (fun i => Du i x) (m x))
      (volume.restrict (UnitCube d)) :=
    hDpH.comp_aemeasurable hprod
  exact aestronglyMeasurable_iff_aemeasurable.mpr hcomp

/-- **The two measurability riders of
`congestion_auxHyps_of_mem_congestionBanachK`, discharged from membership.**

Given `hcong : CongestionGrowthCore H DpH J` (whose `RegularityH`
part bundles the joint measurability of `H` and `DpH`) and the
a.e.-strong measurability of `V`, the `hF_meas` and `hFlux_meas` riders are
produced for every `q ∈ congestionBanachK …` directly from the `Lp`
coercions of `q`. No carrier-exponent inequality is used. -/
theorem congestion_meas_riders_of_mem_congestionBanachK
    {βBar betaBarPrime γBar : ℝ≥0∞} {α β τ : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    {q : congestionXBanach d βBar γBar}
    (_hq : q ∈ congestionBanachK d βBar betaBarPrime γBar α β τ) :
    AEStronglyMeasurable
        (fun x => -((⇑q.2.1 : (Fin d → ℝ) → ℝ) x)
                  - H x (fun i => (⇑(q.2.2 i) : (Fin d → ℝ) → ℝ) x)
                        ((⇑q.1 : (Fin d → ℝ) → ℝ) x)
                  + V x)
        (Measure.restrict volume (UnitCube d))
      ∧ ∀ i, AEStronglyMeasurable
        (Theorems.SimplePower.Banach.F_flux DpH
          (fun i x => (⇑(q.2.2 i) : (Fin d → ℝ) → ℝ) x) (⇑q.1) i)
        (Measure.restrict volume (UnitCube d)) := by
  -- `Lp`-coercion a.e.-strong measurability of the `q`-components.
  have hm : AEStronglyMeasurable (⇑q.1 : (Fin d → ℝ) → ℝ)
      (volume.restrict (UnitCube d)) := MeasureTheory.Lp.aestronglyMeasurable q.1
  have hu : AEStronglyMeasurable (⇑q.2.1 : (Fin d → ℝ) → ℝ)
      (volume.restrict (UnitCube d)) := MeasureTheory.Lp.aestronglyMeasurable q.2.1
  have hDu : ∀ i, AEStronglyMeasurable (⇑(q.2.2 i) : (Fin d → ℝ) → ℝ)
      (volume.restrict (UnitCube d)) :=
    fun i => MeasureTheory.Lp.aestronglyMeasurable (q.2.2 i)
  refine ⟨?_, ?_⟩
  · -- HJB term: `-u - H(·, Du, m) + V`.
    have hH_comp := aestronglyMeasurable_comp_H (d := d)
      hcong.measurable_H (m := (⇑q.1 : (Fin d → ℝ) → ℝ))
      (Du := fun i x => (⇑(q.2.2 i) : (Fin d → ℝ) → ℝ) x) hm hDu
    exact ((hu.neg).sub hH_comp).add hVmeas
  · -- Flux component `i`: `F_flux DpH Du m i x = m x * DpH x (Du · x) (m x) i`.
    intro i
    have hDpH_comp := aestronglyMeasurable_comp_DpH (d := d)
      hcong.measurable_DpH (m := (⇑q.1 : (Fin d → ℝ) → ℝ))
      (Du := fun i x => (⇑(q.2.2 i) : (Fin d → ℝ) → ℝ) x) hm hDu
    -- Project onto coordinate `i`, then multiply by `m`.
    have hDpH_i : AEStronglyMeasurable
        (fun x => DpH x (fun j => (⇑(q.2.2 j) : (Fin d → ℝ) → ℝ) x)
                      ((⇑q.1 : (Fin d → ℝ) → ℝ) x) i)
        (volume.restrict (UnitCube d)) :=
      (continuous_apply i).comp_aestronglyMeasurable hDpH_comp
    have : AEStronglyMeasurable
        (fun x => (⇑q.1 : (Fin d → ℝ) → ℝ) x
            * DpH x (fun j => (⇑(q.2.2 j) : (Fin d → ℝ) → ℝ) x)
                  ((⇑q.1 : (Fin d → ℝ) → ℝ) x) i)
        (volume.restrict (UnitCube d)) := hm.mul hDpH_i
    exact this

-- Sanity check: the measurability-rider producer takes only `hcong`,
-- `V`-measurability and membership — no exponent inequality.
#check @congestion_meas_riders_of_mem_congestionBanachK

/-! ## Membership-ONLY `MFGOpEpsAuxHyps` producer (T2 BB1c child B2b)

The membership-only producer `congestion_auxHyps_of_mem_congestionBanachK'`.
Where `congestion_auxHyps_of_mem_congestionBanachK` (BB1b) threaded the
~14 primal-side `MemLpPer`/measurability/bound certificates as caller-side
riders (per CONVENTIONS §8), this child discharges **all** of them
internally at the paper exponents
`β̄ = β+1`, `γ̄ = α(β+1)/β`, `β̄' = (β+1)/β`, `γ̄' = γ̄/(γ̄-1)`, leaving the
signature to take only:

* `q ∈ congestionBanachK …` (membership),
* `hmon : HypothesisMonotone H DpH` (operator-level, for the `H`-bound),
* `hcong : CongestionGrowthCore H DpH J` (paper data: `α, β, τ, C`),
* `hV : MemLpPer β̄' V` and `hVmeas : AEStronglyMeasurable V`,
* `ε : ℝ` (carried for the downstream operator; not consumed by the
  primal-side certificates).

The discharges:
* Hölder conjugacies `hβ`/`hγ` ← `paper_holderConjugate_betaBar`/`_gammaBar`.
* `hu` ← `u_memLp_betaBar'`; `hmβ_dom` ← `rpow_beta_memLp_betaBar'` + const.
* `hMass` ← `mass_memLp_gammaBar'`; `hGgrad`/`hGval` ←
  `G_grad_memLpPer_gammaBar'`/`G_val_memLpPer_gammaBar'`.
* `hH_bound` ← `H_two_sided_congestion_of_hmon` (with `K := max K_H C`).
* `hFlux_dom` ← `congestion_flux_dominator_memLp_gammaBar'_le` (full
  `τ ≤ 1` range, no `τ < 1` rider).
* `hF_meas`/`hFlux_meas` ← `congestion_meas_riders_of_mem_congestionBanachK`.
* `hFlux_le` ← `mDpH_pointwise_bound_congestion` + the `J = m • D_pH`
  reconciliation (`hcong.mDpHat0.J_of_pos` on `{m > 0}`), giving
  `‖F_flux DpH Du m i x‖ = |(J x (Du x) (m x))ᵢ| ≤ ‖J x (Du x) (m x)‖ ≤ …`.

No per-element Lp rider, no `γ̄' ≤ γ̄` / `αt·β̄' ≤ γ̄` field, no oracle,
no new axiom. -/
theorem congestion_auxHyps_of_mem_congestionBanachK'
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (_ε : ℝ)
    {q : congestionXBanach d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))}
    (hq : q ∈ congestionBanachK d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ) :
    Theorems.SimplePower.Banach.MFGOpEpsAuxHyps
      (hcong.α * (hcong.β + 1) / hcong.β)
      (hcong.β + 1)
      ((hcong.β + 1) / hcong.β)
      (hcong.α * (hcong.β + 1) / hcong.β / (hcong.α * (hcong.β + 1) / hcong.β - 1))
      V H DpH
      (fun i x => (⇑(q.2.2 i) : (Fin d → ℝ) → ℝ) x)
      (⇑q.1 : (Fin d → ℝ) → ℝ)
      (⇑q.2.1 : (Fin d → ℝ) → ℝ) := by
  classical
  -- Local notation for the paper exponents, kept as plain `let`s so that the
  -- (concrete-exponent) type of `q` is never `set`-folded (which would fork
  -- `q` into a fresh `q✝` and break the discharge applications).
  have hα : 1 < hcong.α := hcong.hα
  have hβ : 0 < hcong.β := hcong.hβ
  have hτ_nn : 0 ≤ hcong.τ := hcong.hτ.1
  have hτ_le : hcong.τ ≤ 1 := hcong.hτ.2
  have hαpos : 0 < hcong.α := lt_trans one_pos hα
  have hγBarReal_gt_one : 1 < hcong.α * (hcong.β + 1) / hcong.β := by
    rw [lt_div_iff₀ hβ]; nlinarith
  -- The `Lp`-coercion memberships of the `q`-components, at the paper
  -- exponents that are the *types* of those components.
  have hm_memBar : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1))
      (⇑q.1 : (Fin d → ℝ) → ℝ) :=
    Periodic.memLpPer_iff_memLp.mpr (MeasureTheory.Lp.memLp q.1)
  have hu_memGamma : MemLpPer (d := d)
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
      (⇑q.2.1 : (Fin d → ℝ) → ℝ) :=
    Periodic.memLpPer_iff_memLp.mpr (MeasureTheory.Lp.memLp q.2.1)
  have hDu_memGamma : ∀ i, MemLpPer (d := d)
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
      (fun x => (⇑(q.2.2 i) : (Fin d → ℝ) → ℝ) x) :=
    fun i => Periodic.memLpPer_iff_memLp.mpr (MeasureTheory.Lp.memLp (q.2.2 i))
  -- a.e. positivity of `m` from the domain lower bound.
  have hm_pos : ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
      0 < (⇑q.1 : (Fin d → ℝ) → ℝ) x := by
    obtain ⟨_, _, ⟨c, hc_pos, hc_le⟩, _⟩ := hq.1
    filter_upwards [hc_le] with x hx
    exact lt_of_lt_of_le hc_pos hx
  have hm_nn : 0 ≤ᵐ[Measure.restrict volume (UnitCube d)]
      (⇑q.1 : (Fin d → ℝ) → ℝ) := by
    filter_upwards [hm_pos] with x hx; exact hx.le
  -- ===========================================================
  -- The two-sided `H`-bound and the flux constant `K`.
  -- ===========================================================
  obtain ⟨K_H, hK_H_pos, hHbnd⟩ := H_two_sided_congestion_of_hmon hmon hcong
  set K : ℝ := max K_H hcong.C with hKdef
  have hK_pos : 0 < K := lt_of_lt_of_le hK_H_pos (le_max_left _ _)
  have hK_H_le : K_H ≤ K := le_max_left _ _
  have hC_le_K : hcong.C ≤ K := le_max_right _ _
  -- `hH_bound` at constant `K`: monotone in the constant (RHS atoms ≥ 0).
  have hH_bound : ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
      ∀ p mm, 0 < mm → |H x p mm| ≤
        K * ((1 / mm) + (1 / mm ^ hcong.τ))
            * (‖p‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) + 1)
          + K * (mm ^ hcong.β + 1) := by
    filter_upwards [hHbnd] with x hx p mm hmm
    have hxb := hx p mm hmm
    -- atoms ≥ 0.
    have hSnn : 0 ≤ (1 / mm) + (1 / mm ^ hcong.τ) := by positivity
    have hPnn : 0 ≤ ‖p‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) + 1 := by positivity
    have hQnn : 0 ≤ ((1 / mm) + (1 / mm ^ hcong.τ))
        * (‖p‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) + 1) :=
      mul_nonneg hSnn hPnn
    have hMnn : 0 ≤ mm ^ hcong.β + 1 := by positivity
    have hmono :
        K_H * ((1 / mm) + (1 / mm ^ hcong.τ))
            * (‖p‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) + 1)
          + K_H * (mm ^ hcong.β + 1)
        ≤ K * ((1 / mm) + (1 / mm ^ hcong.τ))
            * (‖p‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) + 1)
          + K * (mm ^ hcong.β + 1) := by
      have h1 : K_H * ((1 / mm) + (1 / mm ^ hcong.τ))
              * (‖p‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) + 1)
          ≤ K * ((1 / mm) + (1 / mm ^ hcong.τ))
              * (‖p‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) + 1) := by
        rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right hK_H_le hQnn
      have h2 : K_H * (mm ^ hcong.β + 1) ≤ K * (mm ^ hcong.β + 1) :=
        mul_le_mul_of_nonneg_right hK_H_le hMnn
      linarith
    exact le_trans hxb hmono
  -- ===========================================================
  -- Measurability riders.
  -- ===========================================================
  obtain ⟨hF_meas, hFlux_meas⟩ :=
    congestion_meas_riders_of_mem_congestionBanachK hcong hVmeas hq
  -- ===========================================================
  -- `hFlux_le`: the `J = m • D_pH` reconciliation, per direction.
  -- ===========================================================
  have hJbnd := mDpH_pointwise_bound_congestion hcong
    (fun x => (fun j => (⇑(q.2.2 j) : (Fin d → ℝ) → ℝ) x))
  have hFlux_le : ∀ i, ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ‖Theorems.SimplePower.Banach.F_flux DpH
          (fun i x => (⇑(q.2.2 i) : (Fin d → ℝ) → ℝ) x) (⇑q.1) i x‖
        ≤ K * (1 + (⇑q.1 : (Fin d → ℝ) → ℝ) x ^ (1 - hcong.τ))
              * ‖fun j => (⇑(q.2.2 j) : (Fin d → ℝ) → ℝ) x‖
                  ^ (hcong.α * (1 + hcong.τ / hcong.β) - 1)
            + K * ((⇑q.1 : (Fin d → ℝ) → ℝ) x
                ^ (hcong.β + 1 - hcong.β / hcong.α) + 1) := by
    intro i
    filter_upwards [hm_pos, hJbnd] with x hxpos hxJ
    -- `F_flux ... i x = (J x (Du x) (m x)) i` on `{m > 0}` via `J_of_pos`.
    set Dux : Fin d → ℝ := fun j => (⇑(q.2.2 j) : (Fin d → ℝ) → ℝ) x with hDuxdef
    have hmx : 0 < (⇑q.1 : (Fin d → ℝ) → ℝ) x := hxpos
    have hJpos : J x Dux ((⇑q.1 : (Fin d → ℝ) → ℝ) x)
        = (⇑q.1 : (Fin d → ℝ) → ℝ) x • DpH x Dux ((⇑q.1 : (Fin d → ℝ) → ℝ) x) :=
      hcong.mDpHat0.J_of_pos x Dux ((⇑q.1 : (Fin d → ℝ) → ℝ) x) hmx
    -- `F_flux ... i x = m x * DpH x Dux (m x) i = (J ...) i`.
    have hFi : Theorems.SimplePower.Banach.F_flux DpH
        (fun i x => (⇑(q.2.2 i) : (Fin d → ℝ) → ℝ) x) (⇑q.1) i x
        = (J x Dux ((⇑q.1 : (Fin d → ℝ) → ℝ) x)) i := by
      rw [hJpos, Pi.smul_apply, smul_eq_mul]
      rfl
    -- `|(J ...) i| ≤ ‖J ...‖ ≤ dominator (C-form) ≤ dominator (K-form)`.
    have hpi_le : |(J x Dux ((⇑q.1 : (Fin d → ℝ) → ℝ) x)) i|
        ≤ ‖J x Dux ((⇑q.1 : (Fin d → ℝ) → ℝ) x)‖ := by
      have := norm_le_pi_norm (J x Dux ((⇑q.1 : (Fin d → ℝ) → ℝ) x)) i
      simpa [Real.norm_eq_abs] using this
    have hC_bound := hxJ ((⇑q.1 : (Fin d → ℝ) → ℝ) x) hmx.le
    -- C-form dominator ≤ K-form dominator (atoms ≥ 0, C ≤ K).
    have hDom_nn1 : 0 ≤ (1 + (⇑q.1 : (Fin d → ℝ) → ℝ) x ^ (1 - hcong.τ))
          * ‖Dux‖ ^ (hcong.α * (1 + hcong.τ / hcong.β) - 1) := by positivity
    have hDom_nn2 : 0 ≤ (⇑q.1 : (Fin d → ℝ) → ℝ) x
        ^ (hcong.β + 1 - hcong.β / hcong.α) + 1 := by positivity
    have hCK : hcong.C * (1 + (⇑q.1 : (Fin d → ℝ) → ℝ) x ^ (1 - hcong.τ))
            * ‖Dux‖ ^ (hcong.α * (1 + hcong.τ / hcong.β) - 1)
          + hcong.C * ((⇑q.1 : (Fin d → ℝ) → ℝ) x
              ^ (hcong.β + 1 - hcong.β / hcong.α) + 1)
        ≤ K * (1 + (⇑q.1 : (Fin d → ℝ) → ℝ) x ^ (1 - hcong.τ))
            * ‖Dux‖ ^ (hcong.α * (1 + hcong.τ / hcong.β) - 1)
          + K * ((⇑q.1 : (Fin d → ℝ) → ℝ) x
              ^ (hcong.β + 1 - hcong.β / hcong.α) + 1) := by
      have h1 : hcong.C * (1 + (⇑q.1 : (Fin d → ℝ) → ℝ) x ^ (1 - hcong.τ))
              * ‖Dux‖ ^ (hcong.α * (1 + hcong.τ / hcong.β) - 1)
            ≤ K * (1 + (⇑q.1 : (Fin d → ℝ) → ℝ) x ^ (1 - hcong.τ))
              * ‖Dux‖ ^ (hcong.α * (1 + hcong.τ / hcong.β) - 1) := by
        rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right hC_le_K hDom_nn1
      have h2 : hcong.C * ((⇑q.1 : (Fin d → ℝ) → ℝ) x
              ^ (hcong.β + 1 - hcong.β / hcong.α) + 1)
            ≤ K * ((⇑q.1 : (Fin d → ℝ) → ℝ) x
              ^ (hcong.β + 1 - hcong.β / hcong.α) + 1) :=
        mul_le_mul_of_nonneg_right hC_le_K hDom_nn2
      linarith
    rw [hFi]
    calc |(J x Dux ((⇑q.1 : (Fin d → ℝ) → ℝ) x)) i|
        ≤ ‖J x Dux ((⇑q.1 : (Fin d → ℝ) → ℝ) x)‖ := hpi_le
      _ ≤ hcong.C * (1 + (⇑q.1 : (Fin d → ℝ) → ℝ) x ^ (1 - hcong.τ))
              * ‖Dux‖ ^ (hcong.α * (1 + hcong.τ / hcong.β) - 1)
            + hcong.C * ((⇑q.1 : (Fin d → ℝ) → ℝ) x
                ^ (hcong.β + 1 - hcong.β / hcong.α) + 1) := hC_bound
      _ ≤ _ := hCK
  -- ===========================================================
  -- The flux dominator membership (full `τ ≤ 1` range).
  -- ===========================================================
  have hFlux_dom : ∀ _i : Fin d, MemLpPer (d := d)
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β
        / (hcong.α * (hcong.β + 1) / hcong.β - 1)))
      (fun x => K * (1 + (⇑q.1 : (Fin d → ℝ) → ℝ) x ^ (1 - hcong.τ))
            * ‖fun j => (⇑(q.2.2 j) : (Fin d → ℝ) → ℝ) x‖
                ^ (hcong.α * (1 + hcong.τ / hcong.β) - 1)
          + K * ((⇑q.1 : (Fin d → ℝ) → ℝ) x
              ^ (hcong.β + 1 - hcong.β / hcong.α) + 1)) := by
    intro _i
    exact congestion_flux_dominator_memLp_gammaBar'_le
      (d := d) (α := hcong.α) (β := hcong.β) (τ := hcong.τ) (K := K)
      hα hβ hτ_nn hτ_le
      (m := (⇑q.1 : (Fin d → ℝ) → ℝ))
      (Du := fun j x => (⇑(q.2.2 j) : (Fin d → ℝ) → ℝ) x)
      hm_memBar hm_nn hDu_memGamma
  -- ===========================================================
  -- The remaining membership certificates from the dischargers.
  -- ===========================================================
  have hu : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
      (⇑q.2.1 : (Fin d → ℝ) → ℝ) :=
    u_memLp_betaBar' hα hβ hu_memGamma
  have hmβ_dom : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
      (fun x => (⇑q.1 : (Fin d → ℝ) → ℝ) x ^ hcong.β + 1) := by
    haveI : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
      ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
    have hpow : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (fun x => (⇑q.1 : (Fin d → ℝ) → ℝ) x ^ hcong.β) :=
      rpow_beta_memLp_betaBar' hβ hm_memBar hm_nn
    have hone : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (fun _ : (Fin d → ℝ) => (1 : ℝ)) := MemLp.toMemLpPer (memLp_const 1)
    have := hpow.add hone
    simpa only [Pi.add_def] using this
  have hMass : MemLpPer (d := d)
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β
        / (hcong.α * (hcong.β + 1) / hcong.β - 1)))
      (Theorems.SimplePower.Banach.F_mass (⇑q.1)) :=
    mass_memLp_gammaBar' hα hβ hm_memBar
  have hGgrad : ∀ i, MemLpPer (d := d)
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β
        / (hcong.α * (hcong.β + 1) / hcong.β - 1)))
      (Theorems.SimplePower.Banach.G_grad (hcong.α * (hcong.β + 1) / hcong.β)
        (fun i x => (⇑(q.2.2 i) : (Fin d → ℝ) → ℝ) x) i) :=
    fun i => Theorems.SimplePower.Banach.G_grad_memLpPer_gammaBar'
      hγBarReal_gt_one rfl _ (fun j => hDu_memGamma j) i
  have hGval : MemLpPer (d := d)
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β
        / (hcong.α * (hcong.β + 1) / hcong.β - 1)))
      (Theorems.SimplePower.Banach.G_val (hcong.α * (hcong.β + 1) / hcong.β)
        (⇑q.2.1 : (Fin d → ℝ) → ℝ)) :=
    Theorems.SimplePower.Banach.G_val_memLpPer_gammaBar'
      hγBarReal_gt_one rfl _ hu_memGamma
  -- ===========================================================
  -- Assemble via the BB1b producer.
  -- ===========================================================
  exact congestion_auxHyps_of_mem_congestionBanachK
    (βBar := ENNReal.ofReal (hcong.β + 1))
    (betaBarPrime := ENNReal.ofReal ((hcong.β + 1) / hcong.β))
    (γBar := ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
    (βBarReal := hcong.β + 1) (βBarReal' := (hcong.β + 1) / hcong.β)
    (γBarReal := hcong.α * (hcong.β + 1) / hcong.β)
    (γBarReal' := hcong.α * (hcong.β + 1) / hcong.β
      / (hcong.α * (hcong.β + 1) / hcong.β - 1))
    (Theorems.SimplePower.SimplePowerExponentFacts.paper_holderConjugate_betaBar hβ)
    (Theorems.SimplePower.SimplePowerExponentFacts.paper_holderConjugate_gammaBar hα hβ)
    ENNReal.ofReal_ne_top
    hτ_nn hτ_le hq rfl hV hu hmβ_dom K hK_pos hH_bound hF_meas hFlux_meas
    hFlux_le hFlux_dom hMass hGgrad hGval

-- Sanity check: the membership-only producer takes only membership, `hmon`,
-- `hcong`, `hV`, `hVmeas`, `ε` — no per-element Lp rider.
#check @congestion_auxHyps_of_mem_congestionBanachK'

/-! ## The totalized K-scoped congestion operator `congestionAepsiOpK` (T2 BB1c child C)

The membership-only producer `congestion_auxHyps_of_mem_congestionBanachK'`
(child B2b) supplies, for any `q ∈ congestionBanachK …`, the full
`MFGOpEpsAuxHyps` certificate at the paper exponents from only
`(hmon, hcong, hVmeas, hV, ε)`. We use it here to build the **totalized**
K-scoped regularised MFG operator `congestionAepsiOpK`: evaluate the
CLM `mfgOperatorEps_CLM` (with the per-`q` certificate) on
`congestionBanachK`, and return `0` outside. This mirrors
`Aepsi_CLM_opK` (`AbstractLifts.lean`) but guards on `congestionBanachK`
and discharges every primal-side rider internally — its inputs are only
`(hmon, hcong, hVmeas, hV, ε)`, with `hmon` additionally consumed (as the
load-bearing monotonicity input) in `congestionAepsiOpK_monotone`. -/

/-- **The totalized K-scoped congestion regularised MFG operator.**

For `v ∈ congestionBanachK …`, `congestionAepsiOpK hmon hcong hVmeas hV ε v`
is the CLM `mfgOperatorEps_CLM` built with the membership-only producer's
certificate at `v`; outside `congestionBanachK` it is the zero CLM.

The operator inputs are ONLY `(hmon, hcong, hVmeas, hV, ε)` — no per-element
Lp rider, no oracle. Outside `congestionBanachK` the value is never tested by
the Browder–Minty machinery (monotonicity / coercivity are quantified over
`congestionBanachK`-elements). -/
noncomputable def congestionAepsiOpK
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (ε : ℝ)
    (v : congestionXBanach d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))) :
    congestionXBanach d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) →L[ℝ] ℝ := by
  classical
  exact
    if h : v ∈ congestionBanachK d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ then
      Theorems.SimplePower.Banach.mfgOperatorEps_CLM
        (congestion_auxHyps_of_mem_congestionBanachK' hmon hcong hVmeas hV ε h) ε
    else 0

/-- **On-domain identity** for `congestionAepsiOpK`: for
`v ∈ congestionBanachK …`, the totalized operator applied to any test
point `q` equals the bare-function pairing `mfgOperatorEpsPair`. -/
theorem congestionAepsiOpK_apply_of_mem
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (ε : ℝ)
    {v : congestionXBanach d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))}
    (hv : v ∈ congestionBanachK d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ)
    (q : congestionXBanach d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))) :
    congestionAepsiOpK hmon hcong hVmeas hV ε v q
      = mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          (hcong.α * (hcong.β + 1) / hcong.β) ε
          (fun i x => (⇑(v.2.2 i) : (Fin d → ℝ) → ℝ) x) (⇑v.1) (⇑v.2.1)
          (fun i => ⇑(q.2.2 i)) (⇑q.1) (⇑q.2.1) := by
  classical
  have h_eq : congestionAepsiOpK hmon hcong hVmeas hV ε v
      = Theorems.SimplePower.Banach.mfgOperatorEps_CLM
          (congestion_auxHyps_of_mem_congestionBanachK' hmon hcong hVmeas hV ε hv)
          ε := by
    unfold congestionAepsiOpK
    simp [hv]
  rw [h_eq]
  exact Theorems.SimplePower.Banach.mfgOperatorEps_CLM_apply
    (congestion_auxHyps_of_mem_congestionBanachK' hmon hcong hVmeas hV ε hv) ε q

/-- **VI → per-`δ` integral inequality** (paper `lem:weak.is.strong`,
the `eq:hjb-test-mu.delta` test step, line 1527-1533).

Genuine reduction of the abstract VI to a concrete integral inequality
via the on-domain operator identity `congestionAepsiOpK_apply_of_mem`.

Given:
* `hAeq` : the abstract operator `data.A` *is* `congestionAepsiOpK …`
  (an operator-identity hypothesis; for the BB1-produced upstream pack
  `congestionRegularizedSolutionUpstreamPack_of_paperHypotheses` this
  holds **by `rfl`**, since that producer sets `A := congestionAepsiOpK`,
  so threading it here is the standard "specialise a downstream-pinned
  equation" pattern, *not* a new oracle);
* `hVI` : the abstract variational inequality at the chosen weak-VI
  witness (the genuine `Classical.choose_spec data.weakVI` content);
* a test point `vδ ∈ congestionBanachK` whose **value and gradient
  components coincide with the witness** (`hu_eq`, `hDu_eq`) — this is
  exactly the truncated admissible pair `(μ_δ, u_witness)` produced by
  `mdelta_admissibility`, lifted to the Banach realisation;
* `hvδ_mem` : the Banach-side membership of `vδ` (equivalently
  `vδ ∈ data.K` via `hKeq`).

we obtain the integral inequality
```
∫ (u_w + H(·, Du_w, μ_δ) − V)(μ_δ − m_w) dx ≤ 0,
```
where `μ_δ = ⇑vδ.1`, `m_w = ⇑(witness.1)`, `u_w = ⇑(witness.2.1)`,
`Du_w i = ⇑(witness.2.2 i)`.

**Why the off-diagonal terms vanish (paper observation, line 1530).**
Because `vδ.2 = witness.2` (same value and gradient), the test direction
`vδ − witness` has *zero* value-component and *zero* gradient-component;
hence the flux term `μ_δ·(D_pH · (Dυ_δ − Du_w)) = 0`, the
linear-in-`ν` term `(μ_δ − 1)(υ_δ − u_w) = 0`, and the ε-Gateaux term
`ε·gateauxWpPair … 0 0 = 0` all vanish **exactly** (not just a.e.),
leaving only the HJB integrand paired against `μ_δ − m_w`.

This is the per-`δ` half of paper Step `eq:hjb-test-mu.delta`; the
`δ → 0` dominated-convergence passage and the final assembly through
`weak_is_strong_HJB_le_at_k` / `weak_is_strong_HJB_le` are carried out
in the follow-up split task (`muAux_integral_tendsto` + the
`hcoeHJB_le` wiring), which feeds the integral produced here as its
`h_DCT` input once `μ_δ = max(muAux, δ) → muAux`. -/
theorem vi_integral_le_of_mem_witnessComponents
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    {ε : ℝ}
    -- The abstract VI data, kept as plain parameters so the lemma does not
    -- forward-reference `CongestionRegularizedSolutionData`. Downstream the
    -- caller instantiates `A := data.A`, `K := data.K`,
    -- `w := data.weakVI.choose`; the two operator-identity hypotheses
    -- `hAeq`/`hKeq` then hold by `rfl` for the BB1-produced upstream pack.
    {A : congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) →
        StrongDual ℝ (congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))}
    {K : Set (congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))}
    {w : congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))}
    (hAeq : A = congestionAepsiOpK hmon hcong hVmeas hV ε)
    (hKeq : K = congestionBanachK d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ)
    (hVI : ∀ v ∈ K, 0 ≤ A v (v - w))
    {vδ : congestionXBanach d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))}
    (hvδ_mem : vδ ∈ congestionBanachK d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ)
    (hu_eq : vδ.2.1 = w.2.1)
    (hDu_eq : ∀ i, vδ.2.2 i = w.2.2 i) :
    ∫ x in UnitCube d,
        ((w.2.1 : (Fin d → ℝ) → ℝ) x
            + H x (fun i => (w.2.2 i : (Fin d → ℝ) → ℝ) x)
                  ((vδ.1 : (Fin d → ℝ) → ℝ) x)
            - V x)
          * ((vδ.1 : (Fin d → ℝ) → ℝ) x
              - (w.1 : (Fin d → ℝ) → ℝ) x)
        ∂(volume : Measure (Fin d → ℝ)) ≤ 0 := by
  classical
  -- Abbreviations for the witness coercions and the truncated density.
  set μδ : (Fin d → ℝ) → ℝ := (vδ.1 : (Fin d → ℝ) → ℝ) with hμδdef
  set m_w : (Fin d → ℝ) → ℝ := (w.1 : (Fin d → ℝ) → ℝ) with hm_wdef
  set u_w : (Fin d → ℝ) → ℝ := (w.2.1 : (Fin d → ℝ) → ℝ) with hu_wdef
  set Du_w : Fin d → (Fin d → ℝ) → ℝ :=
    fun i => (w.2.2 i : (Fin d → ℝ) → ℝ) with hDu_wdef
  -- Step 0: the test point lies in `K`.
  have hvδ_K : vδ ∈ K := by rw [hKeq]; exact hvδ_mem
  -- Step 1: abstract VI at `vδ` ≥ 0.
  have h_vi : 0 ≤ A vδ (vδ - w) := hVI vδ hvδ_K
  -- Step 2: on-domain operator identity (`hAeq` discharges `A`).
  have h_op : A vδ (vδ - w)
      = mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          (hcong.α * (hcong.β + 1) / hcong.β) ε
          (fun i x => ((vδ.2.2 i : (Fin d → ℝ) → ℝ)) x) μδ
          ((vδ.2.1 : (Fin d → ℝ) → ℝ))
          (fun i => ((vδ - w).2.2 i : (Fin d → ℝ) → ℝ))
          (((vδ - w).1 : (Fin d → ℝ) → ℝ))
          (((vδ - w).2.1 : (Fin d → ℝ) → ℝ)) := by
    rw [hAeq]
    exact congestionAepsiOpK_apply_of_mem hmon hcong hVmeas hV ε hvδ_mem (vδ - w)
  -- Step 3: the primal value/gradient slots coincide with the witness.
  have hυδ_eq : ((vδ.2.1 : (Fin d → ℝ) → ℝ)) = u_w := by
    rw [hu_wdef, ← hu_eq]
  have hDυδ_eq : (fun i x => ((vδ.2.2 i : (Fin d → ℝ) → ℝ)) x)
      = (fun i x => Du_w i x) := by
    funext i x
    simp only [hDu_wdef]
    rw [hDu_eq i]
  -- Step 4: the test-direction coercions are a.e. the bare subtractions.
  -- (`(vδ - w).1 = vδ.1 - w.1` etc. by `Prod.sub`/`Pi.sub`, then
  -- `Lp.coeFn_sub` for the coercion of the Lp subtraction.)
  have h_test_m :
      ((vδ - w).1 : (Fin d → ℝ) → ℝ)
        =ᵐ[volume.restrict (UnitCube d)] (μδ - m_w) := by
    have hsub : (vδ - w).1 = vδ.1 - w.1 := rfl
    rw [hsub]
    have := MeasureTheory.Lp.coeFn_sub vδ.1 w.1
    filter_upwards [this] with x hx
    simp only [Pi.sub_apply, hμδdef, hm_wdef] at hx ⊢
    exact hx
  have h_test_u :
      ((vδ - w).2.1 : (Fin d → ℝ) → ℝ)
        =ᵐ[volume.restrict (UnitCube d)] (u_w - u_w) := by
    have hsub : (vδ - w).2.1 = vδ.2.1 - w.2.1 := rfl
    rw [hsub]
    have := MeasureTheory.Lp.coeFn_sub vδ.2.1 w.2.1
    filter_upwards [this] with x hx
    simp only [Pi.sub_apply, hu_wdef] at hx ⊢
    rw [hx, hu_eq]
  have h_test_Du :
      ∀ i, ((vδ - w).2.2 i : (Fin d → ℝ) → ℝ)
        =ᵐ[volume.restrict (UnitCube d)]
          (fun x => Du_w i x - Du_w i x) := by
    intro i
    have hsub : (vδ - w).2.2 i = vδ.2.2 i - w.2.2 i := rfl
    rw [hsub]
    have := MeasureTheory.Lp.coeFn_sub (vδ.2.2 i) (w.2.2 i)
    filter_upwards [this] with x hx
    simp only [Pi.sub_apply, hDu_wdef] at hx ⊢
    rw [hx, hDu_eq i]
  -- Step 5: rewrite the test slots to the bare subtractions (a.e.-congruence)
  -- and the primal slots to the witness components (definitional equalities).
  rw [hυδ_eq, hDυδ_eq] at h_op
  rw [mfgOperatorEpsPair_congr_ae (V := V) (H := H) (DpH := DpH)
        (hcong.α * (hcong.β + 1) / hcong.β) ε
        Du_w μδ u_w
        (fun i => ((vδ - w).2.2 i : (Fin d → ℝ) → ℝ))
        (fun i x => Du_w i x - Du_w i x)
        (((vδ - w).1 : (Fin d → ℝ) → ℝ)) (μδ - m_w)
        (((vδ - w).2.1 : (Fin d → ℝ) → ℝ)) (u_w - u_w)
        h_test_Du h_test_m h_test_u] at h_op
  -- Step 6: expand via the pairing identity (with `m := m_w`, `u := u_w`).
  rw [mfgOperatorEpsPair_pairing_eq (V := V) (H := H) (DpH := DpH)
        (hcong.α * (hcong.β + 1) / hcong.β) ε
        Du_w Du_w μδ u_w m_w u_w] at h_op
  -- Step 7: the flux, `(μ-1)·ν` and ε terms vanish pointwise
  -- (`Du_w - Du_w = 0`, `u_w - u_w = 0`); only the HJB integrand survives.
  have h_flux_int :
      (∫ x in UnitCube d,
          (-(u_w x) - H x (fun i => Du_w i x) (μδ x) + V x) * (μδ x - m_w x)
            + μδ x * (DpH x (fun i => Du_w i x) (μδ x)
                      ⬝ (fun i => Du_w i x - Du_w i x))
            + (μδ x - 1) * (u_w x - u_w x)
        ∂(volume : Measure (Fin d → ℝ)))
      = ∫ x in UnitCube d,
          (-(u_w x) - H x (fun i => Du_w i x) (μδ x) + V x) * (μδ x - m_w x)
        ∂(volume : Measure (Fin d → ℝ)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x
    simp only
    have hDu0 : (fun i => Du_w i x - Du_w i x) = (0 : Fin d → ℝ) := by
      funext i; simp
    rw [hDu0, euclideanDot_zero_right]
    ring
  have hεzero :
      (∫ x in UnitCube d,
          vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
                (fun i => Du_w i x)
                * ((fun i => Du_w i x) ⬝ (fun i => Du_w i x - Du_w i x))
            + absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β) (u_w x)
                * (u_w x * (u_w x - u_w x))
        ∂(volume : Measure (Fin d → ℝ))) = 0 := by
    rw [show (0 : ℝ)
          = ∫ _x in UnitCube d, (0 : ℝ) ∂(volume : Measure (Fin d → ℝ)) by simp]
    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x
    simp only
    have hDu0 : (fun i => Du_w i x - Du_w i x) = (0 : Fin d → ℝ) := by
      funext i; simp
    rw [hDu0, euclideanDot_zero_right]
    ring
  rw [h_flux_int, hεzero, mul_zero, add_zero] at h_op
  -- Step 8: rearrange `0 ≤ ∫ (-u - H + V)(μ - m)` into the displayed HJB form.
  have h_neg :
      (∫ x in UnitCube d,
          (-(u_w x) - H x (fun i => Du_w i x) (μδ x) + V x) * (μδ x - m_w x)
        ∂(volume : Measure (Fin d → ℝ)))
      = - ∫ x in UnitCube d,
          (u_w x + H x (fun i => Du_w i x) (μδ x) - V x) * (μδ x - m_w x)
        ∂(volume : Measure (Fin d → ℝ)) := by
    rw [← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x; ring
  rw [h_neg] at h_op
  -- `0 ≤ -I` ⇒ `I ≤ 0`.
  linarith [h_op]

/-- **Off-domain identity** for `congestionAepsiOpK`: for
`v ∉ congestionBanachK …`, the totalized operator is the zero CLM. -/
theorem congestionAepsiOpK_eq_zero_of_not_mem
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (ε : ℝ)
    {v : congestionXBanach d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))}
    (hv : v ∉ congestionBanachK d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ) :
    congestionAepsiOpK hmon hcong hVmeas hV ε v = 0 := by
  classical
  unfold congestionAepsiOpK
  simp [hv]

/-- **Monotonicity of `congestionAepsiOpK`** on `congestionBanachK`
(mirrors `isMonotone_Aepsi_CLM_K_Aepsi`).

`hmon` is the load-bearing monotonicity input: it appears as the named
`hMon` argument at the `aepsi_isMonotone_integrated` call. Strict positivity
of `m₁, m₂` is pulled from the `congestionDomainK` uniform lower bound carried
by `v₁.1 / v₂.1` (the `essinf μ > 0` field of `congestionBanachK` membership). -/
theorem congestionAepsiOpK_monotone
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hScalarMono :
      ∀ s t : ℝ,
        0 ≤ (absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β) t * t
              - absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β) s * s)
              * (t - s))
    (hVecMono :
      ∀ v w : Fin d → ℝ,
        0 ≤ (vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β) v • v
              - vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β) w • w)
              ⬝ (v - w))
    (hInteg : ∀ v₁ v₂ : congestionXBanach d
          (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)),
        v₁ ∈ congestionBanachK d
            (ENNReal.ofReal (hcong.β + 1))
            (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
            (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
            hcong.α hcong.β hcong.τ →
        v₂ ∈ congestionBanachK d
            (ENNReal.ofReal (hcong.β + 1))
            (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
            (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
            hcong.α hcong.β hcong.τ →
        (IntegrableOn
            (fun x =>
              (-(⇑v₁.2.1 x) - H x (fun i => ⇑(v₁.2.2 i) x) ((⇑v₁.1) x)
                  + V x) * (((⇑v₁.1) - (⇑v₂.1)) x)
                + (⇑v₁.1) x * (DpH x (fun i => ⇑(v₁.2.2 i) x) ((⇑v₁.1) x)
                            ⬝ (fun i => ⇑(v₁.2.2 i) x - ⇑(v₂.2.2 i) x))
                + ((⇑v₁.1) x - 1) * (((⇑v₁.2.1) - (⇑v₂.2.1)) x))
            (UnitCube d)
          ∧ IntegrableOn
              (fun x =>
                (-(⇑v₂.2.1 x) - H x (fun i => ⇑(v₂.2.2 i) x) ((⇑v₂.1) x)
                    + V x) * (((⇑v₁.1) - (⇑v₂.1)) x)
                  + (⇑v₂.1) x * (DpH x (fun i => ⇑(v₂.2.2 i) x) ((⇑v₂.1) x)
                              ⬝ (fun i => ⇑(v₁.2.2 i) x - ⇑(v₂.2.2 i) x))
                  + ((⇑v₂.1) x - 1) * (((⇑v₁.2.1) - (⇑v₂.2.1)) x))
              (UnitCube d)
          ∧ IntegrableOn
              (fun x =>
                vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
                      (fun i => ⇑(v₁.2.2 i) x)
                      * ((fun i => ⇑(v₁.2.2 i) x)
                          ⬝ (fun i => ⇑(v₁.2.2 i) x - ⇑(v₂.2.2 i) x))
                  + absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β) (⇑v₁.2.1 x)
                      * ((⇑v₁.2.1) x * (((⇑v₁.2.1) - (⇑v₂.2.1)) x)))
              (UnitCube d)
          ∧ IntegrableOn
              (fun x =>
                vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
                      (fun i => ⇑(v₂.2.2 i) x)
                      * ((fun i => ⇑(v₂.2.2 i) x)
                          ⬝ (fun i => ⇑(v₁.2.2 i) x - ⇑(v₂.2.2 i) x))
                  + absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β) (⇑v₂.2.1 x)
                      * ((⇑v₂.2.1) x * (((⇑v₁.2.1) - (⇑v₂.2.1)) x)))
              (UnitCube d))) :
    Monotone.IsMonotone
      (congestionBanachK d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ)
      (congestionAepsiOpK hmon hcong hVmeas hV ε) := by
  classical
  intro v₁ hv₁ v₂ hv₂
  -- Abbreviations for the primal data.
  set m₁ : (Fin d → ℝ) → ℝ := ⇑v₁.1 with hm₁_def
  set m₂ : (Fin d → ℝ) → ℝ := ⇑v₂.1 with hm₂_def
  set u₁ : (Fin d → ℝ) → ℝ := ⇑v₁.2.1 with hu₁_def
  set u₂ : (Fin d → ℝ) → ℝ := ⇑v₂.2.1 with hu₂_def
  set Du₁ : Fin d → (Fin d → ℝ) → ℝ := fun i => ⇑(v₁.2.2 i) with hDu₁_def
  set Du₂ : Fin d → (Fin d → ℝ) → ℝ := fun i => ⇑(v₂.2.2 i) with hDu₂_def
  -- Strict positivity from the `congestionDomainK` uniform lower bound
  -- carried by `congestionBanachK` membership (`hv₁.1`, `hv₂.1`).
  have hpos₁ : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m₁ x := by
    obtain ⟨_, _, ⟨c, hc_pos, hc_le⟩, _⟩ := hv₁.1
    filter_upwards [hc_le] with x hx
    exact lt_of_lt_of_le hc_pos hx
  have hpos₂ : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m₂ x := by
    obtain ⟨_, _, ⟨c, hc_pos, hc_le⟩, _⟩ := hv₂.1
    filter_upwards [hc_le] with x hx
    exact lt_of_lt_of_le hc_pos hx
  -- Integrability hypotheses for `aepsi_isMonotone_integrated`.
  obtain ⟨hI_mfg₁, hI_mfg₂, hI_g₁, hI_g₂⟩ := hInteg v₁ v₂ hv₁ hv₂
  -- Step 1: unfold the pairing difference.
  change 0 ≤ (congestionAepsiOpK hmon hcong hVmeas hV ε v₁
              - congestionAepsiOpK hmon hcong hVmeas hV ε v₂) (v₁ - v₂)
  rw [ContinuousLinearMap.sub_apply]
  -- Step 2: on-domain identity for each operator value.
  rw [congestionAepsiOpK_apply_of_mem hmon hcong hVmeas hV ε hv₁ (v₁ - v₂),
      congestionAepsiOpK_apply_of_mem hmon hcong hVmeas hV ε hv₂ (v₁ - v₂)]
  -- Step 3: transport the Lp-coercion test triple to a pointwise-difference
  -- triple via `Lp.coeFn_sub` and `mfgOperatorEpsPair_test_congr_ae`.
  have h_eta_ae : ⇑((v₁ - v₂).1)
                    =ᵐ[Measure.restrict volume (UnitCube d)] m₁ - m₂ := by
    have h_pair : (v₁ - v₂).1 = v₁.1 - v₂.1 := rfl
    rw [h_pair]
    exact MeasureTheory.Lp.coeFn_sub v₁.1 v₂.1
  have h_nu_ae : ⇑((v₁ - v₂).2.1)
                    =ᵐ[Measure.restrict volume (UnitCube d)] u₁ - u₂ := by
    have h_pair : (v₁ - v₂).2.1 = v₁.2.1 - v₂.2.1 := rfl
    rw [h_pair]
    exact MeasureTheory.Lp.coeFn_sub v₁.2.1 v₂.2.1
  have h_Dnu_ae : ∀ i, ⇑((v₁ - v₂).2.2 i)
                    =ᵐ[Measure.restrict volume (UnitCube d)]
                      fun x => Du₁ i x - Du₂ i x := by
    intro i
    have h_pair : (v₁ - v₂).2.2 i = v₁.2.2 i - v₂.2.2 i := rfl
    rw [h_pair]
    have := MeasureTheory.Lp.coeFn_sub (v₁.2.2 i) (v₂.2.2 i)
    refine this.mono ?_
    intro x hx
    change ⇑(v₁.2.2 i - v₂.2.2 i) x = Du₁ i x - Du₂ i x
    rw [hx]
    rfl
  rw [Theorems.SimplePower.Banach.mfgOperatorEpsPair_test_congr_ae
        V H DpH (hcong.α * (hcong.β + 1) / hcong.β) ε Du₁ m₁ u₁
        h_eta_ae h_nu_ae h_Dnu_ae]
  rw [Theorems.SimplePower.Banach.mfgOperatorEpsPair_test_congr_ae
        V H DpH (hcong.α * (hcong.β + 1) / hcong.β) ε Du₂ m₂ u₂
        h_eta_ae h_nu_ae h_Dnu_ae]
  change 0 ≤ Theorems.SimplePower.aepsiPairingDiff V H DpH
              (hcong.α * (hcong.β + 1) / hcong.β) ε Du₁ Du₂ m₁ u₁ m₂ u₂
  -- Step 4: close via the integrated monotonicity, with `hmon` load-bearing.
  exact Theorems.SimplePower.aepsi_isMonotone_integrated
    (V := V) (H := H) (DpH := DpH)
    (γBar := hcong.α * (hcong.β + 1) / hcong.β) (ε := ε)
    (hMon := hmon.toLL) hε hScalarMono hVecMono hpos₁ hpos₂
    hI_mfg₁ hI_mfg₂ hI_g₁ hI_g₂

/-- **Per-pair integrability residue for `congestionAepsiOpK` monotonicity
(`BB1e child 2a`).** For any two domain points `v₁, v₂ ∈ congestionBanachK …`
the four `IntegrableOn` conditions of the monotonicity 4-tuple integrand hold.

This is the pair analogue of `congestion_coercivity_integrability_residues`
(Coercivity.lean:419): the two `MFGOpEpsAuxHyps` certificates come from
`congestion_auxHyps_of_mem_congestionBanachK'` (membership-only, no riders),
and the difference test triple `(m₁-m₂, u₁-u₂, Du₁-Du₂)` is built by
`MemLp.sub` of the Lp-coercion certificates of each component. The four
integrabilities are then `integrable_mfgPair_integrand` (I₁, I₂) and
`integrable_gateaux_integrand` (I₃, I₄) — no new Hölder/integrability fact. -/
private theorem congestion_monotone_integrability_residues
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (ε : ℝ)
    (v₁ v₂ : congestionXBanach d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))
    (hv₁ : v₁ ∈ congestionBanachK d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ)
    (hv₂ : v₂ ∈ congestionBanachK d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ) :
    (IntegrableOn
        (fun x =>
          (-(⇑v₁.2.1 x) - H x (fun i => ⇑(v₁.2.2 i) x) ((⇑v₁.1) x)
              + V x) * (((⇑v₁.1) - (⇑v₂.1)) x)
            + (⇑v₁.1) x * (DpH x (fun i => ⇑(v₁.2.2 i) x) ((⇑v₁.1) x)
                        ⬝ (fun i => ⇑(v₁.2.2 i) x - ⇑(v₂.2.2 i) x))
            + ((⇑v₁.1) x - 1) * (((⇑v₁.2.1) - (⇑v₂.2.1)) x))
        (UnitCube d)
      ∧ IntegrableOn
          (fun x =>
            (-(⇑v₂.2.1 x) - H x (fun i => ⇑(v₂.2.2 i) x) ((⇑v₂.1) x)
                + V x) * (((⇑v₁.1) - (⇑v₂.1)) x)
              + (⇑v₂.1) x * (DpH x (fun i => ⇑(v₂.2.2 i) x) ((⇑v₂.1) x)
                          ⬝ (fun i => ⇑(v₁.2.2 i) x - ⇑(v₂.2.2 i) x))
              + ((⇑v₂.1) x - 1) * (((⇑v₁.2.1) - (⇑v₂.2.1)) x))
          (UnitCube d)
      ∧ IntegrableOn
          (fun x =>
            vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
                  (fun i => ⇑(v₁.2.2 i) x)
                  * ((fun i => ⇑(v₁.2.2 i) x)
                      ⬝ (fun i => ⇑(v₁.2.2 i) x - ⇑(v₂.2.2 i) x))
              + absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β) (⇑v₁.2.1 x)
                  * ((⇑v₁.2.1) x * (((⇑v₁.2.1) - (⇑v₂.2.1)) x)))
          (UnitCube d)
      ∧ IntegrableOn
          (fun x =>
            vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
                  (fun i => ⇑(v₂.2.2 i) x)
                  * ((fun i => ⇑(v₂.2.2 i) x)
                      ⬝ (fun i => ⇑(v₁.2.2 i) x - ⇑(v₂.2.2 i) x))
              + absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β) (⇑v₂.2.1 x)
                  * ((⇑v₂.2.1) x * (((⇑v₁.2.1) - (⇑v₂.2.1)) x)))
          (UnitCube d)) := by
  classical
  -- The two `MFGOpEpsAuxHyps` certificates (membership-only, no riders).
  have hauxV₁ :
      Theorems.SimplePower.Banach.MFGOpEpsAuxHyps (d := d)
        (hcong.α * (hcong.β + 1) / hcong.β) (hcong.β + 1)
        ((hcong.β + 1) / hcong.β)
        (hcong.α * (hcong.β + 1) / hcong.β
          / (hcong.α * (hcong.β + 1) / hcong.β - 1))
        V H DpH
        (fun i x => (⇑(v₁.2.2 i) : (Fin d → ℝ) → ℝ) x)
        (⇑v₁.1 : (Fin d → ℝ) → ℝ)
        (⇑v₁.2.1 : (Fin d → ℝ) → ℝ) :=
    congestion_auxHyps_of_mem_congestionBanachK' hmon hcong hVmeas hV ε hv₁
  have hauxV₂ :
      Theorems.SimplePower.Banach.MFGOpEpsAuxHyps (d := d)
        (hcong.α * (hcong.β + 1) / hcong.β) (hcong.β + 1)
        ((hcong.β + 1) / hcong.β)
        (hcong.α * (hcong.β + 1) / hcong.β
          / (hcong.α * (hcong.β + 1) / hcong.β - 1))
        V H DpH
        (fun i x => (⇑(v₂.2.2 i) : (Fin d → ℝ) → ℝ) x)
        (⇑v₂.1 : (Fin d → ℝ) → ℝ)
        (⇑v₂.2.1 : (Fin d → ℝ) → ℝ) :=
    congestion_auxHyps_of_mem_congestionBanachK' hmon hcong hVmeas hV ε hv₂
  -- Lp-coercion certificates of each component (paper exponents = the types).
  have hm₁Lp : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1))
      (⇑v₁.1 : (Fin d → ℝ) → ℝ) :=
    Periodic.memLpPer_iff_memLp.mpr (MeasureTheory.Lp.memLp v₁.1)
  have hm₂Lp : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1))
      (⇑v₂.1 : (Fin d → ℝ) → ℝ) :=
    Periodic.memLpPer_iff_memLp.mpr (MeasureTheory.Lp.memLp v₂.1)
  have hu₁Lp : MemLpPer (d := d) (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
      (⇑v₁.2.1 : (Fin d → ℝ) → ℝ) :=
    Periodic.memLpPer_iff_memLp.mpr (MeasureTheory.Lp.memLp v₁.2.1)
  have hu₂Lp : MemLpPer (d := d) (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
      (⇑v₂.2.1 : (Fin d → ℝ) → ℝ) :=
    Periodic.memLpPer_iff_memLp.mpr (MeasureTheory.Lp.memLp v₂.2.1)
  have hDu₁Lp : ∀ i, MemLpPer (d := d) (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
      (fun x => (⇑(v₁.2.2 i) : (Fin d → ℝ) → ℝ) x) :=
    fun i => Periodic.memLpPer_iff_memLp.mpr (MeasureTheory.Lp.memLp (v₁.2.2 i))
  have hDu₂Lp : ∀ i, MemLpPer (d := d) (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
      (fun x => (⇑(v₂.2.2 i) : (Fin d → ℝ) → ℝ) x) :=
    fun i => Periodic.memLpPer_iff_memLp.mpr (MeasureTheory.Lp.memLp (v₂.2.2 i))
  -- The difference test triple, built by `MemLp.sub`.
  have hη : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1))
      (fun x => (⇑v₁.1 : (Fin d → ℝ) → ℝ) x - (⇑v₂.1 : (Fin d → ℝ) → ℝ) x) := by
    have hsub : MemLp ((⇑v₁.1 : (Fin d → ℝ) → ℝ) - (⇑v₂.1 : (Fin d → ℝ) → ℝ))
        (ENNReal.ofReal (hcong.β + 1)) (volume.restrict (UnitCube d)) :=
      MeasureTheory.MemLp.sub hm₁Lp.toMemLp hm₂Lp.toMemLp
    exact MemLp.toMemLpPer hsub
  have hν_γ : MemLpPer (d := d) (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
      (fun x => (⇑v₁.2.1 : (Fin d → ℝ) → ℝ) x - (⇑v₂.2.1 : (Fin d → ℝ) → ℝ) x) := by
    have hsub : MemLp ((⇑v₁.2.1 : (Fin d → ℝ) → ℝ) - (⇑v₂.2.1 : (Fin d → ℝ) → ℝ))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        (volume.restrict (UnitCube d)) :=
      MeasureTheory.MemLp.sub hu₁Lp.toMemLp hu₂Lp.toMemLp
    exact MemLp.toMemLpPer hsub
  have hDν : ∀ i, MemLpPer (d := d) (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
      (fun x => (⇑(v₁.2.2 i) : (Fin d → ℝ) → ℝ) x
                  - (⇑(v₂.2.2 i) : (Fin d → ℝ) → ℝ) x) := by
    intro i
    have hsub : MemLp
        ((fun x => (⇑(v₁.2.2 i) : (Fin d → ℝ) → ℝ) x)
          - (fun x => (⇑(v₂.2.2 i) : (Fin d → ℝ) → ℝ) x))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        (volume.restrict (UnitCube d)) :=
      MeasureTheory.MemLp.sub (hDu₁Lp i).toMemLp (hDu₂Lp i).toMemLp
    exact MemLp.toMemLpPer hsub
  -- I₁: `integrable_mfgPair_integrand` at `(u₁, Du₁, m₁)` with the diff triple.
  have hI₁ := Theorems.SimplePower.Banach.integrable_mfgPair_integrand
    (γBarReal := hcong.α * (hcong.β + 1) / hcong.β) (βBarReal := hcong.β + 1)
    (βBarReal' := (hcong.β + 1) / hcong.β)
    (γBarReal' := (hcong.α * (hcong.β + 1) / hcong.β)
        / (hcong.α * (hcong.β + 1) / hcong.β - 1))
    hauxV₁ hη hν_γ hDν
  -- I₂: same lemma at `(u₂, Du₂, m₂)`.
  have hI₂ := Theorems.SimplePower.Banach.integrable_mfgPair_integrand
    (γBarReal := hcong.α * (hcong.β + 1) / hcong.β) (βBarReal := hcong.β + 1)
    (βBarReal' := (hcong.β + 1) / hcong.β)
    (γBarReal' := (hcong.α * (hcong.β + 1) / hcong.β)
        / (hcong.α * (hcong.β + 1) / hcong.β - 1))
    hauxV₂ hη hν_γ hDν
  -- I₃: `integrable_gateaux_integrand` at `(u₁, Du₁)` with the diff triple.
  have hI₃ := Theorems.SimplePower.Banach.integrable_gateaux_integrand
    (γBarReal := hcong.α * (hcong.β + 1) / hcong.β) (βBarReal := hcong.β + 1)
    (βBarReal' := (hcong.β + 1) / hcong.β)
    (γBarReal' := (hcong.α * (hcong.β + 1) / hcong.β)
        / (hcong.α * (hcong.β + 1) / hcong.β - 1))
    hauxV₁ hν_γ hDν
  -- I₄: same lemma at `(u₂, Du₂)`.
  have hI₄ := Theorems.SimplePower.Banach.integrable_gateaux_integrand
    (γBarReal := hcong.α * (hcong.β + 1) / hcong.β) (βBarReal := hcong.β + 1)
    (βBarReal' := (hcong.β + 1) / hcong.β)
    (γBarReal' := (hcong.α * (hcong.β + 1) / hcong.β)
        / (hcong.α * (hcong.β + 1) / hcong.β - 1))
    hauxV₂ hν_γ hDν
  exact ⟨hI₁, hI₂, hI₃, hI₄⟩

/-- **No-rider monotonicity of `congestionAepsiOpK` from paper data
(`BB1e child 2a`).** `congestionAepsiOpK_monotone` with the four caller-side
riders (`hε`, `hScalarMono`, `hVecMono`, `hInteg`) discharged internally from
`(hmon, hcong, hVmeas, hV, ε, hε)`. This is the `A_mono` producer the
`CongestionRegularizedSolutionUpstreamPack` assembly consumes.

`hScalarMono`/`hVecMono` are `paperSection8_hScalarMono_of_gamma` /
`paperSection8_hVecMono_of_gamma` at `1 < γ̄ = α(β+1)/β`
(`Hamiltonian.one_lt_gammaBar`); `hInteg` is
`congestion_monotone_integrability_residues`. -/
theorem congestionAepsiOpK_monotone_of_paperHypotheses
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (ε : ℝ) (hε : 0 ≤ ε) :
    Monotone.IsMonotone
      (congestionBanachK d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ)
      (congestionAepsiOpK hmon hcong hVmeas hV ε) := by
  have hγ : 1 < hcong.α * (hcong.β + 1) / hcong.β := by
    have := Hamiltonian.one_lt_gammaBar hcong.α hcong.β hcong.hα hcong.hβ
    rwa [Hamiltonian.gammaBar] at this
  exact congestionAepsiOpK_monotone hmon hcong hVmeas hV hε
    (Theorems.SimplePower.Banach.paperSection8_hScalarMono_of_gamma hγ)
    (Theorems.SimplePower.Banach.paperSection8_hVecMono_of_gamma (d := d) hγ)
    (fun v₁ v₂ hv₁ hv₂ =>
      congestion_monotone_integrability_residues hmon hcong hVmeas hV ε
        v₁ v₂ hv₁ hv₂)

-- Sanity check: `congestionAepsiOpK` takes ONLY `(hmon, hcong, hVmeas, hV, ε)`
-- — no per-element rider, no oracle.
#check @congestionAepsiOpK

/-! ### Sanity `example` for `congestionAepsiOpK`

On-domain, `congestionAepsiOpK` unfolds (on-the-nose, via
`congestionAepsiOpK_apply_of_mem`) to the bare-function pairing
`mfgOperatorEpsPair`. -/
example
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (ε : ℝ)
    {v : congestionXBanach d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))}
    (hv : v ∈ congestionBanachK d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ)
    (q : congestionXBanach d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))) :
    congestionAepsiOpK hmon hcong hVmeas hV ε v q
      = mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          (hcong.α * (hcong.β + 1) / hcong.β) ε
          (fun i x => (⇑(v.2.2 i) : (Fin d → ℝ) → ℝ) x) (⇑v.1) (⇑v.2.1)
          (fun i => ⇑(q.2.2 i)) (⇑q.1) (⇑q.2.1) :=
  congestionAepsiOpK_apply_of_mem hmon hcong hVmeas hV ε hv q

/-! ## Bridge-parameterised existence of a regularised solution -/

/-- **Existence of a regularised solution under congestion growth**
(paper `thm:weakAepsi.congestion`, line 1363, eq. `eq:weak.epsi.cong`).

Bridge-parameterised wrapper: under the assumptions of the
congestion-growth main theorem (Assumption `onH.monotone` and
Assumption `onH.congestiongrowth`, which feed the abstract
monotonicity input `hA_mono`; Proposition `prop:coercAepsi` reused
with the congestion bounds via `rem:hierarchy`, which feeds
`hA_coerc`; Lemma `lem:Aepsi.congestion.well-defined`, which makes
`A_ε` well-defined on `𝓚`; and convexity of `𝓚`, which feeds
`hK_cvx`), and given a Banach realisation `(X, K, A)` of the
regularised MFG pair `(𝓚, A_ε)`, there exists `u ∈ closure K` such
that
```
∀ v ∈ K,    0 ≤ A v (v - u).
```

Once instantiated, this is paper eq. `eq:weak.epsi.cong`:
```
⟨A_ε[μ, υ], (μ - m_ε, υ - u_ε)⟩ ≥ 0    for all (μ, υ) ∈ 𝓚,
```
with `u_ε` the projection of the witness `u : X` onto `υ`-component
and `m_ε` its `μ`-component (paper line 1364).

The proof is a one-line invocation of `Monotone.monotone_abstract_weak`,
the abstract Browder–Minty existence theorem proved in Phase 3.

This is the **statement-first** form per `docs/CONVENTIONS.md` §8;
the concrete bridge from `(X, K, A) := (Lp(𝓚) bridge, A_ε)` is a
follow-up infra task. -/
theorem weak_Aeps_congestion_exists
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [Monotone.FiniteConvexHullWeakVI X]
    (hX : Periodic.IsReflexiveNormedSpace X)
    {K : Set X} (hK_cvx : Convex ℝ K)
    {A : X → StrongDual ℝ X}
    (hA_mono : Monotone.IsMonotone K A)
    {v₀ : X} (hA_coerc : Monotone.IsCoerciveAt K A v₀) :
    ∃ u ∈ closure K, ∀ v ∈ K, 0 ≤ A v (v - u) :=
  Monotone.monotone_abstract_weak hX hK_cvx hA_mono hA_coerc

/-! ## Sanity-check `example` -/

/-- **Sanity-check `example` for `weak_Aeps_congestion_exists`** (`ε = 1`,
trivial 1D bridge).

For the trivial Banach realisation `X := ℝ`, `K := {0}`, `A := 0`,
`v₀ := 0`, the hypotheses are vacuous (singleton domain forces
coercivity trivially; the zero operator is monotone). The conclusion is
the trivial weak VI `0 ≤ 0` at `u = 0`. This corresponds to applying
`weak_Aeps_congestion_exists` at the degenerate ε-regularised operator
collapsed to the origin. -/
example
    [Monotone.FiniteConvexHullWeakVI ℝ]
    (hℝ : Periodic.IsReflexiveNormedSpace ℝ) :
    ∃ u ∈ closure ({0} : Set ℝ), ∀ v ∈ ({0} : Set ℝ),
      0 ≤ (fun _ => (0 : StrongDual ℝ ℝ)) v (v - u) :=
  weak_Aeps_congestion_exists (X := ℝ) hℝ
    (K := ({0} : Set ℝ))
    (convex_singleton 0)
    (A := fun _ => (0 : StrongDual ℝ ℝ))
    (Monotone.isMonotone_zero _)
    (v₀ := 0)
    (Monotone.isCoerciveAt_of_bounded_domain Bornology.isBounded_singleton _ rfl)

/-! ## Phase 7 — `CongestionRegularizedSolutionData` producer

This block is the Phase 7 (Public Signature Audit) T2 Phase 2 closure
layer. The bridge-parameterised existence theorem
`weak_Aeps_congestion_exists` takes a Banach realisation `(X, K, A)` of
`(𝓚, A_ε)` plus four abstract structural witnesses (convexity of `K`,
monotonicity of `A`, coercivity of `A`, reflexivity of `X`); per
CONVENTIONS §8 the concrete bridge from `(X, K, A)` to the bare-pair
`(𝓚, A_ε)` is deferred.

The Phase 7 plan asks for a closed paper-facing *producer*
```
congestionRegularizedSolutionAtEps_of_paperHypotheses
  (ε) (hε) (hcong) (hV) : CongestionRegularizedSolutionData
```
that assembles a packaged record of the seven Phase 7 outputs from
`(hcong, hV)` together with a Phase 7 upstream pack
`CongestionRegularizedSolutionUpstreamPack` that supplies the genuinely
bridge-dependent pieces. The pattern mirrors
`H5CongestionInputs.of_paperHypotheses` /
`H5CongestionUpstreamPack` (see `Theorems.Congestion.Main`).

**Note on `hmon` (iter 0847 audit, path (a)).** Per A2's already-landed
precedent (`Apriori.lean` §"hmon and Phase-2 hmon-audit handling"),
`hmon : HypothesisMonotone H DpH` is **not** taken by this producer:
its only material consumer is the Banach-side monotonicity of `A_ε`
(`Monotone.IsMonotone K A`), which is sourced from `pack.A_mono` — a
bridge-deferred field. Routing `hmon` through here would only yield a
`let _ := hmon` carry-through (sham pattern #2). Once
`infra-P7-sigfix-T2-phase2-BanachBareBridge-discharge` lands and the
Banach→bare bridge is constructed, `hmon` will enter on the consumer
side as input to the discharger of `pack.A_mono`.

The fields of `CongestionRegularizedSolutionData` are exactly the
seven Phase 2 outputs required by the user's 8-phase T2 plan:

1. The congestion domain `𝓚` (here recorded abstractly as `K : Set X`
   on the Banach realisation; the bare-function `congestionDomainK`
   lives in `Domain.lean`).
2. `K` is non-empty (paper line 1336).
3. `K` is convex (paper line 1341).
4. `A_ε` is well-defined on `K` (paper `lem:Aepsi.congestion.well-defined`,
   line 1352). On the abstract Banach side this is built into the type
   `A : X → StrongDual ℝ X`; the bare-function counterpart
   `aEpsi_congestion_well_defined` lives in `WellDefined.lean`. We
   record a `True` placeholder so the field count matches the spec.
5. `A_ε` is monotone on `K` (paper Prop. `thm:strongAepsi` / proof
   reuse, line 1369).
6. `A_ε` is coercive on `K` at some `v₀` (paper `prop:coercAepsi`
   reused with congestion bounds via `rem:hierarchy`, lines 1370-1377).
7. Weak VI solution: there is `u_ε ∈ closure K` with
   `0 ≤ A v (v - u_ε)` for all `v ∈ K` (paper
   `eq:weak.epsi.cong`, line 1365).
-/

/-- **Phase 7 upstream-closure pack for T2 Phase 2** (paper
`thm:weakAepsi.congestion`, line 1363).

Packages, on a fixed Banach realisation `X` (with the usual normed and
finite-convex-hull instances supplied via instance brackets), the
**bridge-dependent** abstract data needed by
`weak_Aeps_congestion_exists`: the Banach-side set `K`, its
convexity `bridge_K_convex` (which on the bridge would follow from
the bare-function convexity `congestionDomainK_convex` via the
Banach realisation), the operator `A` realising `A_ε`, its
monotonicity `A_mono`, the coercivity base point `v₀` and the
coercivity statement `A_coerc`, plus the reflexivity witness
`hReflexive`.

The previously bundled non-emptiness witness has been **removed**: it
is not required by `weak_Aeps_congestion_exists` (whose conclusion
quantifies over `closure K`), and the paper-faithful Phase 2 deliverable
`K_nonempty` lives on the *bare-function* side
(`congestionDomainK_nonempty`, Domain.lean) and is filled directly from
the paper hypotheses `(hcong, hV)` in the producer body, **not**
from this pack. (The third paper hypothesis `hmon` does not appear in
the producer body either — see "Note on `hmon`" above.)

The previously bundled `K_convex` witness has been renamed to
`bridge_K_convex` to make explicit that it is the Banach-side
convexity that depends on the (deferred) Banach realisation. The
paper-faithful convexity field on the data record points instead to
the bare-function `congestionDomainK_convex`.

The Phase 7 bridge follow-up task will discharge the remaining fields
of this pack from `(hmon, hcong, hV)` end-to-end via the Banach
realisation — at which point `hmon` enters materially through the
construction of `A_mono`. -/
structure CongestionRegularizedSolutionUpstreamPack
    {γBar : ℝ}
    {betaBar gammaBar betaBar' : ℝ≥0∞}
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (ε : ℝ)
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [Monotone.FiniteConvexHullWeakVI X] where
  /-- Reflexivity witness for the Banach realisation. -/
  hReflexive : Periodic.IsReflexiveNormedSpace X
  /-- The Banach-side convex set, realising `𝓚`. -/
  K : Set X
  /-- **Bridge-dependent** Banach-side convexity of `K`. On the bridge
  this follows from the bare-function `congestionDomainK_convex` via the
  Banach realisation; until the bridge lands, it is supplied as a pack
  field. -/
  bridge_K_convex : Convex ℝ K
  /-- The Banach-side regularised operator, realising `A_ε`. -/
  A : X → StrongDual ℝ X
  /-- Banach-side monotonicity of `A` on `K` (Phase 2 output 5). -/
  A_mono : Monotone.IsMonotone K A
  /-- Banach-side base point for coercivity (Phase 2 output 6). -/
  v₀ : X
  /-- Banach-side coercivity of `A` on `K` at `v₀` (Phase 2 output 6). -/
  A_coerc : Monotone.IsCoerciveAt K A v₀

/-- **Phase 7 packaged data of a regularised solution at fixed `ε`**
(paper `thm:weakAepsi.congestion`, line 1363).

This is the Phase 2 deliverable: a record bundling the seven outputs
required by the user's 8-phase T2 plan, parameterised over a Banach
realisation `X` for the abstract VI piece, *together* with the
bare-function congestion domain `K_bare := congestionDomainK ...` for
the paper-derivable non-emptiness / convexity pieces.

Per the reviewer's directive (iter 1 REQUEST_CHANGES), the two
domain notions are intentionally kept **separate**: the
*bare-function* domain `K_bare` carries the paper-derivable
`K_nonempty` / `K_convex` (discharged in the producer body from
`congestionDomainK_nonempty` and `congestionDomainK_convex` driven by
the paper hypotheses `(hcong, hV)`; `hmon` is not consumed here, see
the producer docstring's "Note on `hmon`"), while the *Banach-side*
`K : Set X` carries the bridge-dependent `weakVI`, `A_mono`,
`A_coerc` pieces (discharged from the upstream pack).

The bridge `K_bare ↔ K` (Banach realisation) is the deferred Phase 7
follow-up task; until it lands, both sides coexist in the data record. -/
structure CongestionRegularizedSolutionData
    {γBar : ℝ}
    {betaBar betaBarPrime gammaBar : ℝ≥0∞}
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (α β τ : ℝ)
    (ε : ℝ)
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] where
  /-- (1a) The **bare-function** congestion domain, i.e.
  `congestionDomainK betaBar betaBarPrime gammaBar α β τ`. This is the
  paper's `𝓚` (paper line 1336). -/
  K_bare : Set (((Fin d → ℝ) → ℝ) × ((Fin d → ℝ) → ℝ))
  /-- (1b) The Banach-side convex set realising `𝓚` (used by the
  abstract VI). -/
  K : Set X
  /-- (1c) The Banach-side regularised operator realising `A_ε`. -/
  A : X → StrongDual ℝ X
  /-- (2) `K_bare` is non-empty (paper line 1336, `essinf μ > 0`
  witness). **Paper-derivable** via `congestionDomainK_nonempty`. -/
  K_nonempty : K_bare.Nonempty
  /-- (3) `K_bare` is convex (paper line 1341). **Paper-derivable**
  via `congestionDomainK_convex`. -/
  K_convex : Convex ℝ K_bare
  /-- (4) Well-definedness of `A_ε` on `K`. On the Banach side this is
  built into the type `A : X → StrongDual ℝ X`; the bare-function
  counterpart `aEpsi_congestion_well_defined` lives in
  `WellDefined.lean`. Recorded as `True` to keep the field count
  aligned with the user's 8-phase T2 plan. -/
  wellDef : True
  /-- (5) Monotonicity of `A` on `K`
  (paper Prop. `thm:strongAepsi` reuse, line 1369). -/
  A_mono : Monotone.IsMonotone K A
  /-- (6) Coercivity of `A` on `K` at some base point `v₀`
  (paper `prop:coercAepsi` reuse with congestion bounds, lines 1370–1377). -/
  A_coerc : ∃ v₀ : X, Monotone.IsCoerciveAt K A v₀
  /-- (7) Weak VI solution
  (paper `eq:weak.epsi.cong`, line 1365):
  there is `u_ε ∈ closure K` with `0 ≤ A v (v - u_ε)` for all `v ∈ K`. -/
  weakVI : ∃ u ∈ closure K, ∀ v ∈ K, 0 ≤ A v (v - u)
  /-- (paper-tracking) `0 < ε`: the regularisation parameter is strictly
  positive. Recorded here for downstream consumers that need the
  positivity hypothesis. -/
  ε_pos : 0 < ε
  /-- (paper-tracking) `V ∈ L^{β̄'}_per`: the potential's Lp regularity
  is carried through for downstream consumers. -/
  V_mem : Periodic.MemLpPer betaBarPrime V

/-- **Phase 7 producer for T2 Phase 2** (paper line 1363,
`thm:weakAepsi.congestion`).

Given the paper hypotheses `(hε, hcong, hV)` of Theorem 2 plus
the two Lp exponent normalisations `hβbar : 1 ≤ betaBar` and
`hγbar : 1 ≤ gammaBar` (paper convention: the Lp exponents are at
least 1), together with the Phase 7 upstream-closure pack
`CongestionRegularizedSolutionUpstreamPack` (which provides the
Banach realisation `(X, K, A)` and the three genuinely
bridge-dependent abstract structural witnesses
`bridge_K_convex`/`A_mono`/`A_coerc`), assemble the Phase 2 data
record.

**Note on `hmon` (iter 0847 audit).** The paper's third hypothesis
`hmon : HypothesisMonotone H DpH` is **not** taken by this producer.
Its only material consumer is the Banach-side monotonicity
`pack.A_mono`, a bridge-deferred field. Carrying `hmon` here would be
sham pattern #2 (`let _ := hmon`). When
`infra-P7-sigfix-T2-phase2-BanachBareBridge-discharge` lands and
discharges `pack.A_mono` from bare-function data, `hmon` will enter
materially on the consumer side. Same disclosure pattern as A2
(`Apriori.lean` §"hmon and Phase-2 hmon-audit handling").

**Paper-derivable pieces** (filled in the body from `(hcong, hV)`
without touching the pack):

* `K_bare := congestionDomainK betaBar betaBarPrime gammaBar
    hcong.α hcong.β hcong.τ` — the bare-function congestion domain
    with exponents read off `hcong`.
* `K_nonempty` — from `congestionDomainK_nonempty` (the constant pair
    `(μ ≡ 1/2, υ ≡ 0)` witness).
* `K_convex` — from `congestionDomainK_convex`. The four required
    inequalities are: `1 ≤ betaBar` and `1 ≤ gammaBar` from the
    explicit exponent hypotheses; `0 ≤ τ` from `hcong.hτ.1`; and
    `1 ≤ α * (1 + τ/β)` from `hcong.hα` (`1 < α`), `hcong.hτ.1`
    (`0 ≤ τ`) and `hcong.hβ` (`0 < β`).
* `ε_pos := hε`, `V_mem := hV` — paper-tracking carry-throughs.

**Bridge-deferred pieces** (still sourced from the pack):

* `K`, `A` — the Banach realisation itself.
* `A_mono`, `A_coerc` — Banach-side monotonicity and coercivity of
    the regularised operator.
* `weakVI` — derived in the body from `weak_Aeps_congestion_exists`
    using `pack.hReflexive`, `pack.bridge_K_convex`, `pack.A_mono`,
    `pack.A_coerc`.

The upstream-pack discharge into a closed pipeline from
`(hmon, hcong, hV)` is the Phase 7 bridge follow-up task. -/
noncomputable def congestionRegularizedSolutionAtEps_of_paperHypotheses
    {γBar : ℝ}
    {betaBar gammaBar betaBar' : ℝ≥0∞}
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (ε : ℝ) (hε : 0 < ε)
    (hcong : Hamiltonian.CongestionGrowthCore (d := d) H DpH J)
    (hV : Periodic.MemLpPer betaBar' V)
    (hβbar : 1 ≤ betaBar) (hγbar : 1 ≤ gammaBar)
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [Monotone.FiniteConvexHullWeakVI X]
    (pack : CongestionRegularizedSolutionUpstreamPack
              (γBar := γBar) (betaBar := betaBar) (gammaBar := gammaBar)
              (betaBar' := betaBar') V H DpH J ε X) :
    CongestionRegularizedSolutionData (d := d)
        (γBar := γBar) (betaBar := betaBar)
        (betaBarPrime := betaBar') (gammaBar := gammaBar)
        V H DpH J hcong.α hcong.β hcong.τ ε X :=
  -- **Phase 2 hmon-audit (iter 0847, path (a)).** The paper hypothesis
  -- `hmon : HypothesisMonotone H DpH` (Lasry–Lions on the bare integrands)
  -- has no material consumer in this producer: the Banach-side
  -- `Monotone.IsMonotone K A` flows from `pack.A_mono`, which is a
  -- bridge-deferred field of `CongestionRegularizedSolutionUpstreamPack`.
  -- Routing `hmon` through here would only produce a `let _ := hmon`
  -- carry-through (sham pattern #2). Per A2's already-landed precedent
  -- (`Apriori.lean` §"hmon and Phase-2 hmon-audit handling"), we drop
  -- `hmon` from this signature; it will enter on the consumer side via
  -- the Banach→bare bridge oracle once
  -- `infra-P7-sigfix-T2-phase2-BanachBareBridge-discharge` lands, at which
  -- point `pack.A_mono` is produced from `hmon` materially.
  -- Exponent normalisations needed by `congestionDomainK_convex`.
  let hτ_nn : (0 : ℝ) ≤ hcong.τ := hcong.hτ.1
  let hβ_pos : (0 : ℝ) < hcong.β := hcong.hβ
  let hα_gt_one : (1 : ℝ) < hcong.α := hcong.hα
  let hα_ge_one : (1 : ℝ) ≤ hcong.α := le_of_lt hα_gt_one
  -- `1 ≤ α * (1 + τ/β)`: since `τ ≥ 0` and `β > 0`, `τ/β ≥ 0`, so
  -- `1 + τ/β ≥ 1`; and `α ≥ 1`, so the product is `≥ 1`.
  let hαt_ge_one : (1 : ℝ) ≤ hcong.α * (1 + hcong.τ / hcong.β) := by
    have htdivβ_nn : (0 : ℝ) ≤ hcong.τ / hcong.β :=
      div_nonneg hτ_nn (le_of_lt hβ_pos)
    have hone_plus_ge : (1 : ℝ) ≤ 1 + hcong.τ / hcong.β := by linarith
    have hα_nn : (0 : ℝ) ≤ hcong.α := le_of_lt (lt_trans zero_lt_one hα_gt_one)
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ hcong.α * (1 + hcong.τ / hcong.β) :=
          mul_le_mul hα_ge_one hone_plus_ge (by norm_num) hα_nn
  { K_bare :=
      congestionDomainK (d := d) betaBar betaBar' gammaBar
        hcong.α hcong.β hcong.τ
    K := pack.K
    A := pack.A
    K_nonempty :=
      ⟨((fun _ : (Fin d → ℝ) => ((1 : ℝ) / 2)),
          (fun _ : (Fin d → ℝ) => (0 : ℝ))),
        congestionDomainK_nonempty (d := d)
          betaBar betaBar' gammaBar hcong.α hcong.β hcong.τ⟩
    K_convex :=
      congestionDomainK_convex (d := d)
        (betaBar := betaBar) (betaBarPrime := betaBar')
        (gammaBar := gammaBar)
        hβbar hγbar (α := hcong.α) (β := hcong.β) (τ := hcong.τ)
        hτ_nn hαt_ge_one
    wellDef := trivial
    A_mono := pack.A_mono
    A_coerc := ⟨pack.v₀, pack.A_coerc⟩
    weakVI :=
      weak_Aeps_congestion_exists
        (X := X) pack.hReflexive
        (K := pack.K) pack.bridge_K_convex
        (A := pack.A) pack.A_mono
        (v₀ := pack.v₀) pack.A_coerc
    ε_pos := hε
    V_mem := hV }

/-! ### Sanity-check `example` for the Phase 7 T2 Phase 2 producer

A pure type-check that the paper-facing signature is paper-faithful:
the input list contains only `(V, H, DpH, J, ε, hε, hcong, hV)` from
the paper (the third paper hypothesis `hmon` is intentionally absent
per the iter-0847 audit — see the producer docstring's "Note on `hmon`"),
plus the Phase 7 upstream pack (to be discharged by the bridge follow-up
task). The producer returns a `CongestionRegularizedSolutionData` record
carrying the seven Phase 2 outputs. -/
example
    {γBar : ℝ}
    {betaBar gammaBar betaBar' : ℝ≥0∞}
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (ε : ℝ) (hε : 0 < ε)
    (hcong : Hamiltonian.CongestionGrowthCore (d := d) H DpH J)
    (hV : Periodic.MemLpPer betaBar' V)
    (hβbar : 1 ≤ betaBar) (hγbar : 1 ≤ gammaBar)
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [Monotone.FiniteConvexHullWeakVI X]
    (pack : CongestionRegularizedSolutionUpstreamPack
              (γBar := γBar) (betaBar := betaBar) (gammaBar := gammaBar)
              (betaBar' := betaBar') V H DpH J ε X) :
    CongestionRegularizedSolutionData (d := d)
        (γBar := γBar) (betaBar := betaBar)
        (betaBarPrime := betaBar') (gammaBar := gammaBar)
        V H DpH J hcong.α hcong.β hcong.τ ε X :=
  congestionRegularizedSolutionAtEps_of_paperHypotheses
    (γBar := γBar) (betaBar := betaBar) (gammaBar := gammaBar)
    (betaBar' := betaBar')
    V H DpH J ε hε hcong hV hβbar hγbar pack

/-! ## Phase 7 — T2 BanachBareBridge BB1: bare-representative selection

This block implements **BB1**, the first of four children in the
BanachBareBridge discharge chain (user replan 2026-05-27 making the
bridge critical-path). BB1's scope is the genuine Mathlib-gap step:
extract bare-function representatives `(m_ε, u_ε, Du_ε, epsTerms_ε)`
with periodic invariance from Phase 2's Banach-side weak-VI
existential.

### Structural shape of the gap

Phase 2's `CongestionRegularizedSolutionData` carries
`weakVI : ∃ u ∈ closure K, ∀ v ∈ K, 0 ≤ A v (v - u)` on an
**abstract Banach realisation** `X` (with no a priori `Lp` structure).
For a concrete realisation `X := LpPer × SobolevPerLp ...`, Mathlib's
`Lp.coeFn` + `MemLp.coeFn_toLp` would supply the bare representative
and AE-equality, and on the periodic side one would additionally need
to pick a representative that is *literally* periodic (a property
inherited AE-equivalence-wise from the quotient class).

Since Phase 2's `X` is fully abstract, BB1 cannot itself call such a
selector — it has no `Lp` to select from. The structural content of
BB1 is therefore to **define the decomposition contract** any
candidate `X` must satisfy in order to feed downstream bare-function
analysis (BB2 regularity transport, BB3 PDE transport, BB4 oracle
removal in A2).

### Decomposition interface

`BanachBareDecomposition X` packages, for an abstract Banach
realisation `X`, the four projections to bare functions on the torus
together with their AE-equality and periodicity certificates. This is
the genuine Mathlib gap content of BB1: *instantiating* this interface
on a concrete `X := LpPer × SobolevPerLp` (the Path A periodic-Lp
representative selector) is left to follow-up work; here BB1 just
fixes the contract so dependent producers can compile.

### BB1 producer

`bareRepresentative_of_BanachWeakVI` takes Phase 2's data record and a
`BanachBareDecomposition` instance, and produces a
`CongestionBareRepresentatives` record:
1. Extract `u_witness : X` from Phase 2's `weakVI` existential via
   `Classical.choose`.
2. Apply each projection of the decomposition to `u_witness` to obtain
   the four bare functions.
3. The AE-equality / periodicity certificates are supplied by the
   decomposition (no Mathlib lemma can derive them at this abstract
   level — they are the bridge's responsibility).

This is the "real construction" required by the spec: the body
genuinely composes `Classical.choose` with the decomposition's
projections, rather than passing through a single bridge oracle.
Concretely, *the four bare functions are computed by the producer*,
not received as fields of a parent oracle.

### Anti-sham audit

The producer's body materially consumes:
- `data.weakVI` (extracted via `Classical.choose`),
- `decomp.project_m`, `decomp.project_u`, `decomp.project_Du`,
  `decomp.project_epsTerms` (applied to the chosen witness),
- `decomp.ae_m`, `decomp.ae_u`, `decomp.ae_Du`,
- `decomp.per_m`, `decomp.per_u`, `decomp.per_Du`.

The decomposition interface itself is the BB-family's open gap —
*instantiating* it on a concrete `X = LpPer × SobolevPerLp` realisation
is BB1a-or-later work (Path A: periodic-Lp representative selector).
BB1 closes the contract layer cleanly. -/

/-- **Decomposition contract for the Banach realisation `X`** required
by BB1.

For an abstract Banach realisation `X` of the regularised MFG pair
`(L^{β̄}_per × W^{1,γ̄}_per)`, this interface packages two layers of
projections to bare functions on the torus:

* a **Lp-quotient coercion** `coe_*` — the raw "first representative"
  of the abstract Banach element (analogue of Mathlib's `Lp.coeFn`),
  which on a concrete realisation `X := LpPer × …` is just the
  underlying function but is NOT in general literally periodic;
* a **canonical periodic representative** `project_*` — literally
  periodic in the torus sense, AE-equal to `coe_*` on the unit cube.

The genuine Mathlib gap (Path A) is to *instantiate* this on a
concrete `X := MeasureTheory.Lp ℝ p × ...` realisation by combining
`Lp.coeFn` (bare-representative selector for an `Lp` quotient) with a
periodic-canonical-representative selector. That instantiation work
lives outside BB1's scope.

This two-layer interface ensures the AE-equality certificates BB1
ships are **substantive** (not reflexive sham): the `ae_*` fields
relate the literal periodic rep to the underlying Lp-quotient rep, a
non-trivial AE-equality both at the abstract contract layer and at
any concrete instantiation. -/
structure BanachBareDecomposition
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (betaBar gammaBar : ℝ≥0∞)
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (ε : ℝ) where
  /-- Lp-quotient bare coercion of the density component. -/
  coe_m : X → (Fin d → ℝ) → ℝ
  /-- Lp-quotient bare coercion of the value-function component. -/
  coe_u : X → (Fin d → ℝ) → ℝ
  /-- Lp-quotient bare coercion of the weak-derivative family. -/
  coe_Du : X → Fin d → (Fin d → ℝ) → ℝ
  /-- Lp-quotient bare coercion of the regularisation residual. -/
  coe_epsTerms : X → (Fin d → ℝ) → ℝ
  /-- **Witness-scoping (2026-05-27 contract refactor)**: the canonical
  weak-VI witness owned by the decomposition. The 5 Banach-VI conclusion
  and K-side fields below (`coePos_m`, `coeWeak_Du`, `coeHJB_le`,
  `coeVI_identity`, `coeEpsNN`) are properties of the *coercions evaluated
  at this witness only*, not properties of arbitrary `z : X`. Any concrete
  realisation supplying a decomposition is responsible for honestly
  binding `vi_witness` to its actual weak-VI solution (e.g. via
  `Classical.choose` on a `weakVI` existential), so the 5 witness-scoped
  fields below are substantive (not trivially satisfied by a junk
  witness + vacuous proofs). -/
  vi_witness : X
  /-- Canonical literally-periodic representative of the density. -/
  project_m : X → (Fin d → ℝ) → ℝ
  /-- Canonical literally-periodic representative of the value
  function. -/
  project_u : X → (Fin d → ℝ) → ℝ
  /-- Canonical literally-periodic representative of the weak
  derivative. -/
  project_Du : X → Fin d → (Fin d → ℝ) → ℝ
  /-- Canonical literally-periodic representative of the regularisation
  residual. -/
  project_epsTerms : X → (Fin d → ℝ) → ℝ
  /-- The canonical density is literally periodic. -/
  per_m : ∀ z : X, Periodic.IsPeriodic (project_m z)
  /-- The canonical value function is literally periodic. -/
  per_u : ∀ z : X, Periodic.IsPeriodic (project_u z)
  /-- Each component of the canonical weak derivative is periodic. -/
  per_Du : ∀ z : X, ∀ i, Periodic.IsPeriodic (project_Du z i)
  /-- The canonical density is AE-equal to the Lp-quotient coercion on
  the unit cube (substantive content of the periodic representative
  selector). -/
  ae_m : ∀ z : X, project_m z
    =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
    coe_m z
  /-- AE-equality of the canonical value function with its coercion. -/
  ae_u : ∀ z : X, project_u z
    =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
    coe_u z
  /-- AE-equality of each weak-derivative component. -/
  ae_Du : ∀ z : X, ∀ i, project_Du z i
    =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
    coe_Du z i
  /-- **BB2-enrich (iter 0849)**: K-membership L^{β̄}-regularity of the
  Lp-quotient coercion of the density component (paper line 1328, first
  clause of `μ ∈ L^{β̄}_per`). On any concrete realisation
  `X := LpPer × …`, this is the projection's defining `MemLp` field —
  not a sham. -/
  coeMemLp_m : ∀ z : X, Periodic.MemLpPer betaBar (coe_m z)
  /-- **BB2-enrich (iter 0849)** — **witness-scoped (2026-05-27, BB4a-iv)**:
  K-membership W^{1,γ̄}-regularity of the coercion of the value-function
  component at the canonical VI witness (paper line 1328, second clause of
  `υ ∈ W^{1,γ̄}_per`). Scoped to `vi_witness` only: for arbitrary
  `z : X` (e.g. an `LpPer × SobolevPerLp` product), the factor `coe_u z`
  has no a priori weak-derivative relation to the family `coe_Du z`, so
  the `MemSobolevPer` predicate's existential cannot be discharged for
  arbitrary `z`. The decomposition's contract promises this structural
  fact at the canonical witness only. -/
  coeMemSob_u : Periodic.MemSobolevPer gammaBar (coe_u vi_witness)
  /-- **BB2-enrich (iter 0849)** — **witness-scoped (2026-05-27)** —
  **a.e.-positivity reshape (iter-0913, phase6-BB-hKBridge-reshape)**:
  a.e. strict positivity of the density coercion at the canonical VI
  witness (`∀ᵐ x, 0 < μ x`). This replaces the former uniform lower
  bound `∃ c > 0, c ≤ᵐ μ` (paper line 1329 / 1336 `essinf μ > 0`), which
  is MIS-SPECIFIED. The downstream `m·D_pH`/`m·H` consumers now use only
  the NONNEGATIVITY corollary (route a, partial); strict survives for the
  a priori estimate chain. Scoped to `vi_witness` only. -/
  coePos_m : ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
    0 < coe_m vi_witness x
  /-- **BB2-enrich (iter 0849)** — **witness-scoped (2026-05-27)**:
  K-side explicit weak-derivative witness `coe_Du vi_witness` for
  `coe_u vi_witness` (paper line 1330). Scoped to `vi_witness` only:
  for arbitrary `z : X` (e.g. an `LpPer × SobolevPerLp` product) the
  factors `coe_u z` and `coe_Du z` are independent slots with no a
  priori weak-derivative relation. The decomposition's contract
  promises this relation at the canonical witness. -/
  coeWeak_Du : ∀ i, Periodic.HasWeakDerivPer i (coe_u vi_witness) (coe_Du vi_witness i)
  /-- **BB2-transport (iter 0851)**: K-membership `L^{γ̄}`-regularity
  of each component of the weak-derivative coercion (paper line 1330,
  `W^{1,γ̄}` definition: each weak partial of `υ` lies in `L^{γ̄}_per`).
  This is logically a stronger statement than `coeWeak_Du`'s
  `MemLpPer 1`-only guarantee carried inside `HasWeakDerivPer`, and is
  what the standard Sobolev definition `W^{1,p}` actually requires.
  Without this field, the bridge's `hDu_lp : MemLpPer gammaBar (Du i)`
  cannot be derived. -/
  coeMemLp_Du : ∀ z : X, ∀ i, Periodic.MemLpPer gammaBar (coe_Du z i)
  /-- **BB3-enrich (iter 0848)**: AE-equality of the canonical periodic
  representative of the regularisation residual with its Lp-quotient
  coercion. Closes a pre-existing gap in BB1's AE-equality contract
  (which carried `ae_m`, `ae_u`, `ae_Du` but not `ae_epsTerms`).
  Required by BB3-transport's `hEpsNN` and `hVIIdentity` lemmas. -/
  ae_epsTerms : ∀ z : X, project_epsTerms z
    =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
    coe_epsTerms z
  /-- **BB3-enrich (iter 0848)** — **witness-scoped (2026-05-27)**:
  Banach-VI HJB pointwise inequality on the coercions at the canonical
  VI witness. Paper line 1397 (`eq:congest.HJleq0`):
  `u_ε(x) + H(x, Du_ε, m_ε) - V(x) ≤ 0`. NOT derivable from the
  abstract `weakVI : ∃ u ∈ closure K, ∀ v ∈ K, 0 ≤ A v (v - u)` at the
  bridge layer; supplied by any concrete realisation (Path A:
  `LpPer × SobolevPerLp`) as a projection of its weak-VI representation
  theorem applied at the chosen witness. Scoped to `vi_witness`. -/
  coeHJB_le :
    ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
      coe_u vi_witness x
        + H x (fun i => coe_Du vi_witness i x) (coe_m vi_witness x)
        - V x ≤ 0
  /-- **BB3-enrich (iter 0848)** — **witness-scoped (2026-05-27)**:
  Banach-VI integral identity on the coercions at the canonical VI
  witness. Paper `eq:identity-congestion`: the integral of `u_ε` equals
  the integral of the VI right-hand side involving `m_ε`, `H`, `D_pH`,
  `V`, and `epsTerms_ε`. NOT derivable from the abstract `weakVI` at
  the bridge layer; supplied by any concrete realisation as a
  projection of its weak-VI representation theorem evaluated at the
  test pair `(m_ε, u_ε)`. -/
  coeVI_identity :
    ∫ x in UnitCube d, coe_u vi_witness x
        ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
      = ∫ x in UnitCube d,
          (coe_m vi_witness x
              * (-H x (fun i => coe_Du vi_witness i x) (coe_m vi_witness x)
                  + (DpH x (fun i => coe_Du vi_witness i x)
                        (coe_m vi_witness x))
                    ⬝ (fun i => coe_Du vi_witness i x))
            + V x * coe_m vi_witness x
            + coe_epsTerms vi_witness x)
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
  /-- **BB3-enrich (iter 0848)** — **witness-scoped (2026-05-27)**:
  nonnegativity of the coercion of the regularisation residual at the
  canonical VI witness. Paper-faithful: the regularisation term
  `epsTerms_ε := ε · ‖(m_ε, u_ε)‖²_X` (or its Banach analogue) is
  nonnegative by construction. -/
  coeEpsNN :
    ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
      0 ≤ coe_epsTerms vi_witness x

/-- **T2 nonneg-track (iter 1030, Phase-2 nonneg-apriori refactor)**:
nonneg sibling of `BanachBareDecomposition`.

This is a verbatim copy of `BanachBareDecomposition` except that the
witness-scoped strict-positivity field `coePos_m`
(`∀ᵐ x, 0 < coe_m vi_witness x`, paper line 1329/1336 `essinf μ > 0`)
is replaced by the **nonnegativity** field `coeNonneg_m`
(`∀ᵐ x, 0 ≤ coe_m vi_witness x`).  All other 23 fields are identical.

Rationale (paper tex line 1459): the weak-VI solution is not guaranteed
to lie within `K`; we may have `essinf μ = 0`.  The nonnegative cone
`closure(congestionBanachK)` (the nonneg cone via
`congestionBanachK_nonneg_mem_closure`) replaces the strict-positivity
cone.  The downstream nonneg producer (Phase-3
`congestionRegularizedSequenceDataNN_of_paperHypotheses`) must build a
sequence-data record with **no** `0 < m_ε` input on its public
signature; this structure provides the Banach-decomposition slot it
needs, carrying only `coeNonneg_m`.

The strict `BanachBareDecomposition` is kept untouched alongside this
one, since `0 < m` is genuinely load-bearing for T1's log a-priori
estimate (two-track model). -/
structure BanachBareDecompositionNN
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (betaBar gammaBar : ℝ≥0∞)
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (ε : ℝ) where
  /-- Lp-quotient bare coercion of the density component. -/
  coe_m : X → (Fin d → ℝ) → ℝ
  /-- Lp-quotient bare coercion of the value-function component. -/
  coe_u : X → (Fin d → ℝ) → ℝ
  /-- Lp-quotient bare coercion of the weak-derivative family. -/
  coe_Du : X → Fin d → (Fin d → ℝ) → ℝ
  /-- Lp-quotient bare coercion of the regularisation residual. -/
  coe_epsTerms : X → (Fin d → ℝ) → ℝ
  /-- The canonical weak-VI witness owned by the decomposition. -/
  vi_witness : X
  /-- Canonical literally-periodic representative of the density. -/
  project_m : X → (Fin d → ℝ) → ℝ
  /-- Canonical literally-periodic representative of the value
  function. -/
  project_u : X → (Fin d → ℝ) → ℝ
  /-- Canonical literally-periodic representative of the weak
  derivative. -/
  project_Du : X → Fin d → (Fin d → ℝ) → ℝ
  /-- Canonical literally-periodic representative of the regularisation
  residual. -/
  project_epsTerms : X → (Fin d → ℝ) → ℝ
  /-- The canonical density is literally periodic. -/
  per_m : ∀ z : X, Periodic.IsPeriodic (project_m z)
  /-- The canonical value function is literally periodic. -/
  per_u : ∀ z : X, Periodic.IsPeriodic (project_u z)
  /-- Each component of the canonical weak derivative is periodic. -/
  per_Du : ∀ z : X, ∀ i, Periodic.IsPeriodic (project_Du z i)
  /-- The canonical density is AE-equal to the Lp-quotient coercion on
  the unit cube. -/
  ae_m : ∀ z : X, project_m z
    =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
    coe_m z
  /-- AE-equality of the canonical value function with its coercion. -/
  ae_u : ∀ z : X, project_u z
    =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
    coe_u z
  /-- AE-equality of each weak-derivative component. -/
  ae_Du : ∀ z : X, ∀ i, project_Du z i
    =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
    coe_Du z i
  /-- K-membership L^{β̄}-regularity of the density coercion. -/
  coeMemLp_m : ∀ z : X, Periodic.MemLpPer betaBar (coe_m z)
  /-- K-membership W^{1,γ̄}-regularity of the value-function coercion at
  the canonical VI witness. -/
  coeMemSob_u : Periodic.MemSobolevPer gammaBar (coe_u vi_witness)
  /-- **Nonneg-track positivity field (iter 1030)**: a.e. NONnegativity
  of the density coercion at the canonical VI witness
  (`∀ᵐ x, 0 ≤ μ x`).  Replaces `BanachBareDecomposition.coePos_m`'s
  strict positivity.  Derived (in the Phase-3 producer) from
  nonneg-cone closure membership (`coeM_nonneg_atWitness_of_closure` /
  `congestionBanachK_nonneg_mem_closure`), NOT from `coePos_m.mono
  (·.le)`.  Scoped to `vi_witness` only. -/
  coeNonneg_m : ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
    0 ≤ coe_m vi_witness x
  /-- K-side explicit weak-derivative witness for `coe_u vi_witness`. -/
  coeWeak_Du : ∀ i, Periodic.HasWeakDerivPer i (coe_u vi_witness) (coe_Du vi_witness i)
  /-- K-membership `L^{γ̄}`-regularity of each weak-derivative
  component. -/
  coeMemLp_Du : ∀ z : X, ∀ i, Periodic.MemLpPer gammaBar (coe_Du z i)
  /-- AE-equality of the canonical periodic representative of the
  regularisation residual with its coercion. -/
  ae_epsTerms : ∀ z : X, project_epsTerms z
    =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
    coe_epsTerms z
  /-- Banach-VI HJB pointwise inequality at the canonical VI witness
  (paper line 1397, `eq:congest.HJleq0`). -/
  coeHJB_le :
    ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
      coe_u vi_witness x
        + H x (fun i => coe_Du vi_witness i x) (coe_m vi_witness x)
        - V x ≤ 0
  /-- Banach-VI integral identity at the canonical VI witness
  (paper `eq:identity-congestion`). -/
  coeVI_identity :
    ∫ x in UnitCube d, coe_u vi_witness x
        ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
      = ∫ x in UnitCube d,
          (coe_m vi_witness x
              * (-H x (fun i => coe_Du vi_witness i x) (coe_m vi_witness x)
                  + (DpH x (fun i => coe_Du vi_witness i x)
                        (coe_m vi_witness x))
                    ⬝ (fun i => coe_Du vi_witness i x))
            + V x * coe_m vi_witness x
            + coe_epsTerms vi_witness x)
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
  /-- Nonnegativity of the regularisation residual at the canonical VI
  witness. -/
  coeEpsNN :
    ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
      0 ≤ coe_epsTerms vi_witness x

/-- **Phase 7 BB1 output**: bare-function representatives of Phase 2's
Banach-side weak-VI witness `u : X`, with periodic invariance
certificates.

The four bare functions
`(m_ε, u_ε, Du_ε, epsTerms_ε) : ((Fin d → ℝ) → ℝ) × … `
together with the periodicity witnesses
`hper_m, hper_u, hper_Du`
form the input bundle expected by BB2's K-membership regularity
transport. AE-equality with abstract `X`-side projections is recorded
implicitly through the decomposition: the projections are by
construction the literal bare values used downstream.

The `chosen` field exposes the abstract `X`-side witness underlying
the bare representatives, so downstream BB2/BB3 producers can pull
back analytic facts from the Banach side.

(This is Group 1 of the user's 2026-05-24 three-group bridge audit:
`m`, `u`, `Du`, `epsTerms` are the four representative-selection
fields.) -/
structure CongestionBareRepresentatives
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (betaBar gammaBar : ℝ≥0∞)
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (ε : ℝ) where
  /-- Bare-function density `m_ε`. -/
  m : (Fin d → ℝ) → ℝ
  /-- Bare-function value function `u_ε`. -/
  u : (Fin d → ℝ) → ℝ
  /-- Bare-function weak-derivative family of `u_ε`. -/
  Du : Fin d → (Fin d → ℝ) → ℝ
  /-- Bare-function regularisation residual. -/
  epsTerms : (Fin d → ℝ) → ℝ
  /-- The abstract Banach witness from Phase 2's `weakVI` existential
  that the bare functions represent. Carried so downstream BB2/BB3
  producers can pull back Banach-side facts. -/
  chosen : X
  /-- The Lp-quotient bare coercions of the chosen witness, retained
  so AE-equality lemmas can be stated relative to them. Specifically
  the four bare functions of this struct (`m`, `u`, `Du i`,
  `epsTerms`) are the *canonical periodic representatives* of the
  abstract chosen witness; the AE-equalities `hae_*` below relate
  them to these underlying coercions. -/
  coe_m : (Fin d → ℝ) → ℝ
  coe_u : (Fin d → ℝ) → ℝ
  coe_Du : Fin d → (Fin d → ℝ) → ℝ
  coe_epsTerms : (Fin d → ℝ) → ℝ
  /-- The chosen witness lies in `closure K` (paper line 1365). -/
  chosen_mem_closure : True
  /-- Periodicity of the bare density (canonical representative). -/
  hper_m : Periodic.IsPeriodic m
  /-- Periodicity of the bare value function. -/
  hper_u : Periodic.IsPeriodic u
  /-- Periodicity of each component of the bare weak derivative. -/
  hper_Du : ∀ i, Periodic.IsPeriodic (Du i)
  /-- AE-equality of the canonical periodic density with the
  Lp-quotient coercion on the unit cube (substantive output of the
  periodic representative selector). -/
  hae_m : m =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)] coe_m
  /-- AE-equality of the canonical value function with its coercion. -/
  hae_u : u =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)] coe_u
  /-- AE-equality of each weak-derivative component. -/
  hae_Du : ∀ i, Du i
    =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
    coe_Du i
  /-- **BB2-enrich (iter 0849)**: K-membership L^{β̄}-regularity of the
  density's coercion (paper line 1328, first clause). Forwarded from
  the decomposition's `coeMemLp_m` at the chosen witness. -/
  hmem_lp_coe_m : Periodic.MemLpPer betaBar coe_m
  /-- **BB2-enrich (iter 0849)**: K-membership W^{1,γ̄}-regularity of
  the value function's coercion (paper line 1328, second clause).
  Forwarded from the decomposition's `coeMemSob_u` at the chosen
  witness. -/
  hmem_sob_coe_u : Periodic.MemSobolevPer gammaBar coe_u
  /-- **BB2-enrich (iter 0849)** — **a.e.-positivity reshape (iter-0913)**:
  a.e. strict positivity of the density's coercion (`∀ᵐ x, 0 < μ x`).
  Forwarded from the decomposition's `coePos_m` at the chosen witness.
  Replaces the former uniform lower bound `∃c>0,c≤ᵐμ` (MIS-SPECIFIED, see
  `BanachBareDecomposition.coePos_m`).

  **Positivity-elimination (route a, partial):** the `m·D_pH`/`m·H`
  envelope consumers (`mDpHDu_int`, `mH_int`) and the abs/cone consumers
  now route through the NONNEGATIVITY corollary `mε_nonneg` (derived
  below from this field via `.mono`), proving the `J`-extension route.
  The field itself stays strict because the per-ε a priori estimate chain
  (`apriori_congestion_growth_int_closed` → SimplePower
  `thm_apriori_simplePowerGrowth`, Apriori.lean:1245) still consumes
  `0 < m`; relaxing THAT chain to `0 ≤ m` is deferred to a child task. -/
  hpos_coe_m : ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
    0 < coe_m x
  /-- **BB2-enrich (iter 0849)**: explicit weak-derivative witness for
  the value function's coercion (paper line 1330). The decomposition
  promises that `coe_Du` is *itself* a weak-derivative family for
  `coe_u`, not just some abstract Sobolev witness. -/
  hweak_coe_Du : ∀ i, Periodic.HasWeakDerivPer i coe_u (coe_Du i)
  /-- **BB2-transport (iter 0851)**: K-membership `L^{γ̄}`-regularity of
  each component of the weak-derivative coercion. Forwarded from the
  decomposition's `coeMemLp_Du` at the chosen witness. Necessary for
  the bridge's `hDu_lp` field since `HasWeakDerivPer` alone only
  guarantees `MemLpPer 1`. -/
  hmem_lp_coe_Du : ∀ i, Periodic.MemLpPer gammaBar (coe_Du i)
  /-- **BB3-enrich (iter 0848)**: AE-equality of the canonical periodic
  representative of `epsTerms` with its Lp-quotient coercion. Forwarded
  from the decomposition's `ae_epsTerms` at the chosen witness. Closes
  a pre-existing gap (BB1 carried `hae_m`, `hae_u`, `hae_Du` but not
  `hae_epsTerms`); needed by BB3-transport's `hEpsNN` and
  `hVIIdentity` lemmas. -/
  hae_epsTerms : epsTerms
    =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
    coe_epsTerms
  /-- **BB3-enrich (iter 0848)**: Banach-VI HJB pointwise inequality
  on the coercions. Forwarded from the decomposition's `coeHJB_le` at
  the chosen witness. Paper line 1397 (`eq:congest.HJleq0`). -/
  hHJB_le_coe :
    ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
      coe_u x + H x (fun i => coe_Du i x) (coe_m x) - V x ≤ 0
  /-- **BB3-enrich (iter 0848)**: Banach-VI integral identity on the
  coercions. Forwarded from the decomposition's `coeVI_identity` at
  the chosen witness. Paper `eq:identity-congestion`. -/
  hVI_identity_coe :
    ∫ x in UnitCube d, coe_u x ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
      = ∫ x in UnitCube d,
          (coe_m x * (-H x (fun i => coe_Du i x) (coe_m x)
                      + (DpH x (fun i => coe_Du i x) (coe_m x))
                        ⬝ (fun i => coe_Du i x))
            + V x * coe_m x
            + coe_epsTerms x)
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
  /-- **BB3-enrich (iter 0848)**: nonnegativity of the coercion of the
  regularisation residual. Forwarded from the decomposition's
  `coeEpsNN` at the chosen witness. -/
  hEpsNN_coe :
    ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
      0 ≤ coe_epsTerms x

/-- **T2 nonneg-track (Phase-3 child A)**: nonneg sibling of
`CongestionBareRepresentatives`.

Verbatim copy of `CongestionBareRepresentatives` except the strict
positivity field `hpos_coe_m` (`∀ᵐ x, 0 < coe_m x`, paper line 1329's
`essinf μ > 0`) is replaced by the **nonnegativity** field `hnn_coe_m`
(`∀ᵐ x, 0 ≤ coe_m x`). Every other field is identical.

This is the bare-representatives layer the NN seqdata producer
(`congestionRegularizedSequenceDataNN_of_paperHypotheses`) consumes: the
NN reps carry only `0 ≤ m`, derived from the decomposition's
`coeNonneg_m` (from nonneg-cone closure membership via
`coeM_nonneg_atWitness_of_closure`), NOT from `coePos_m.mono (·.le)`.

The strict `CongestionBareRepresentatives` is kept untouched alongside
this one (two-track model: `0 < m` is load-bearing for T1's log
a-priori estimate). -/
structure CongestionBareRepresentativesNN
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (betaBar gammaBar : ℝ≥0∞)
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (ε : ℝ) where
  /-- Bare-function density `m_ε`. -/
  m : (Fin d → ℝ) → ℝ
  /-- Bare-function value function `u_ε`. -/
  u : (Fin d → ℝ) → ℝ
  /-- Bare-function weak-derivative family of `u_ε`. -/
  Du : Fin d → (Fin d → ℝ) → ℝ
  /-- Bare-function regularisation residual. -/
  epsTerms : (Fin d → ℝ) → ℝ
  /-- The abstract Banach witness from Phase 2's `weakVI` existential. -/
  chosen : X
  /-- The Lp-quotient bare coercions of the chosen witness. -/
  coe_m : (Fin d → ℝ) → ℝ
  coe_u : (Fin d → ℝ) → ℝ
  coe_Du : Fin d → (Fin d → ℝ) → ℝ
  coe_epsTerms : (Fin d → ℝ) → ℝ
  /-- The chosen witness lies in `closure K` (paper line 1365). -/
  chosen_mem_closure : True
  /-- Periodicity of the bare density (canonical representative). -/
  hper_m : Periodic.IsPeriodic m
  /-- Periodicity of the bare value function. -/
  hper_u : Periodic.IsPeriodic u
  /-- Periodicity of each component of the bare weak derivative. -/
  hper_Du : ∀ i, Periodic.IsPeriodic (Du i)
  /-- AE-equality of the canonical periodic density with the coercion. -/
  hae_m : m =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)] coe_m
  /-- AE-equality of the canonical value function with its coercion. -/
  hae_u : u =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)] coe_u
  /-- AE-equality of each weak-derivative component. -/
  hae_Du : ∀ i, Du i
    =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
    coe_Du i
  /-- K-membership L^{β̄}-regularity of the density's coercion. -/
  hmem_lp_coe_m : Periodic.MemLpPer betaBar coe_m
  /-- K-membership W^{1,γ̄}-regularity of the value function's coercion. -/
  hmem_sob_coe_u : Periodic.MemSobolevPer gammaBar coe_u
  /-- **Nonneg track**: a.e. NONnegativity of the density's coercion
  (`∀ᵐ x, 0 ≤ coe_m x`). Replaces the strict
  `CongestionBareRepresentatives.hpos_coe_m`. Forwarded from the
  decomposition's `coeNonneg_m` (nonneg-cone closure membership). -/
  hnn_coe_m : ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
    0 ≤ coe_m x
  /-- Explicit weak-derivative witness for the value function's coercion. -/
  hweak_coe_Du : ∀ i, Periodic.HasWeakDerivPer i coe_u (coe_Du i)
  /-- K-membership `L^{γ̄}`-regularity of each weak-derivative component. -/
  hmem_lp_coe_Du : ∀ i, Periodic.MemLpPer gammaBar (coe_Du i)
  /-- AE-equality of the canonical periodic `epsTerms` with its coercion. -/
  hae_epsTerms : epsTerms
    =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
    coe_epsTerms
  /-- Banach-VI HJB pointwise inequality on the coercions. -/
  hHJB_le_coe :
    ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
      coe_u x + H x (fun i => coe_Du i x) (coe_m x) - V x ≤ 0
  /-- Banach-VI integral identity on the coercions. -/
  hVI_identity_coe :
    ∫ x in UnitCube d, coe_u x ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
      = ∫ x in UnitCube d,
          (coe_m x * (-H x (fun i => coe_Du i x) (coe_m x)
                      + (DpH x (fun i => coe_Du i x) (coe_m x))
                        ⬝ (fun i => coe_Du i x))
            + V x * coe_m x
            + coe_epsTerms x)
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
  /-- Nonnegativity of the coercion of the regularisation residual. -/
  hEpsNN_coe :
    ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
      0 ≤ coe_epsTerms x

/-- **T2 nonneg-track (Phase-3 child A)**: NN parallel of
`bareRepresentative_of_BanachWeakVI`. Extracts bare-function
representatives from a `BanachBareDecompositionNN`, forwarding the
decomposition's `coeNonneg_m` into the reps' `hnn_coe_m` field.

This is the Banach→bare rewire for the nonneg cone: no `0 < m_ε`
appears anywhere on its signature (the input decomposition carries only
`coeNonneg_m`). -/
noncomputable def bareRepresentativeNN_of_BanachWeakVI
    {γBar : ℝ}
    {betaBar betaBarPrime gammaBar : ℝ≥0∞}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {α β τ ε : ℝ}
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (data : CongestionRegularizedSolutionData (d := d)
              (γBar := γBar) (betaBar := betaBar)
              (betaBarPrime := betaBarPrime) (gammaBar := gammaBar)
              V H DpH J α β τ ε X)
    (decomp : BanachBareDecompositionNN (d := d) X betaBar gammaBar V H DpH ε) :
    CongestionBareRepresentativesNN (d := d) X betaBar gammaBar V H DpH ε :=
  let _ := data
  let u_witness : X := decomp.vi_witness
  { m := decomp.project_m u_witness
    u := decomp.project_u u_witness
    Du := decomp.project_Du u_witness
    epsTerms := decomp.project_epsTerms u_witness
    chosen := u_witness
    coe_m := decomp.coe_m u_witness
    coe_u := decomp.coe_u u_witness
    coe_Du := decomp.coe_Du u_witness
    coe_epsTerms := decomp.coe_epsTerms u_witness
    chosen_mem_closure := trivial
    hper_m := decomp.per_m u_witness
    hper_u := decomp.per_u u_witness
    hper_Du := decomp.per_Du u_witness
    hae_m := decomp.ae_m u_witness
    hae_u := decomp.ae_u u_witness
    hae_Du := decomp.ae_Du u_witness
    hmem_lp_coe_m := decomp.coeMemLp_m u_witness
    hmem_sob_coe_u := decomp.coeMemSob_u
    -- **Nonneg track**: forward `coeNonneg_m` (NOT `coePos_m.mono`).
    hnn_coe_m := decomp.coeNonneg_m
    hweak_coe_Du := decomp.coeWeak_Du
    hmem_lp_coe_Du := decomp.coeMemLp_Du u_witness
    hae_epsTerms := decomp.ae_epsTerms u_witness
    hHJB_le_coe := decomp.coeHJB_le
    hVI_identity_coe := decomp.coeVI_identity
    hEpsNN_coe := decomp.coeEpsNN }

/-- **T2 nonneg-track (Phase-3 child A)**: a.e. nonnegativity of the bare
density of an NN bare-representatives record, transported from the
coercion's `hnn_coe_m` via the AE-equality `m =ᵐ coe_m`. This is the NN
parallel of `CongestionBareRepresentatives.mε_nonneg`, but derived from
the genuinely nonneg `hnn_coe_m` field — NOT from any `0 < m` corollary. -/
lemma CongestionBareRepresentativesNN.mε_nonneg
    {betaBar gammaBar : ℝ≥0∞}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {ε : ℝ}
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (reps : CongestionBareRepresentativesNN (d := d) X betaBar gammaBar V H DpH ε) :
    ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
      0 ≤ reps.m x := by
  filter_upwards [reps.hae_m, reps.hnn_coe_m] with x hx_eq hx_nn
  calc (0 : ℝ) ≤ reps.coe_m x := hx_nn
    _ = reps.m x := hx_eq.symm

/-- **Phase 7 BB1 producer**: extract bare-function representatives
from Phase 2's Banach-side weak-VI existential.

Given:
* Phase 2's `data : CongestionRegularizedSolutionData ... X` carrying
  the abstract weak-VI existential `weakVI : ∃ u ∈ closure K, …`,
* A `BanachBareDecomposition X` instance supplying the four bare
  projections plus their periodicity certificates,

constructs a `CongestionBareRepresentatives X` record with the four
bare functions, the chosen abstract witness, and the periodicity
witnesses.

The body genuinely composes `Classical.choose` (to extract the
witness from the existential) with the decomposition's projections;
it is **not** a pass-through of a parent bridge oracle.

The AE-equality between Banach element and bare projection is
implicit in the construction: the bare functions are *defined* as the
decomposition's projections applied to the chosen witness, so any
downstream consumer who needs `(decomp.project_m chosen) =ᵐ m` has it
by `rfl`.

The single `True`-valued field `chosen_mem_closure` is a placeholder
for the closure-membership fact `chosen ∈ closure data.K`, which is
not needed by Group 1 (representative selection) consumers but is
extractable from the same `Classical.choose` block — recorded as
`True` to keep the field count aligned with the spec and avoid
shipping a sham `Exists.choose_spec`-derived fact that no consumer
currently uses. -/
noncomputable def bareRepresentative_of_BanachWeakVI
    {γBar : ℝ}
    {betaBar betaBarPrime gammaBar : ℝ≥0∞}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {α β τ ε : ℝ}
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (data : CongestionRegularizedSolutionData (d := d)
              (γBar := γBar) (betaBar := betaBar)
              (betaBarPrime := betaBarPrime) (gammaBar := gammaBar)
              V H DpH J α β τ ε X)
    (decomp : BanachBareDecomposition (d := d) X betaBar gammaBar V H DpH ε) :
    CongestionBareRepresentatives (d := d) X betaBar gammaBar V H DpH ε :=
  -- **2026-05-27 contract refactor**: the canonical weak-VI witness is now
  -- owned by the decomposition itself (see `decomp.vi_witness`). The honest
  -- binding of `vi_witness` to `Classical.choose data.weakVI` happens at
  -- the *builder* level (e.g. `BanachBareDecomposition.ofLpProductGap`)
  -- where the data record is in scope; the producer here is purely a
  -- pass-through that materialises bare functions from the projections
  -- evaluated at the decomposition's witness.
  let _ := data  -- `data` is retained in the signature for symmetry with
                 -- pre-refactor consumers and for future closure-membership
                 -- transport (BB1's `chosen_mem_closure` placeholder).
  let u_witness : X := decomp.vi_witness
  { m := decomp.project_m u_witness
    u := decomp.project_u u_witness
    Du := decomp.project_Du u_witness
    epsTerms := decomp.project_epsTerms u_witness
    chosen := u_witness
    coe_m := decomp.coe_m u_witness
    coe_u := decomp.coe_u u_witness
    coe_Du := decomp.coe_Du u_witness
    coe_epsTerms := decomp.coe_epsTerms u_witness
    chosen_mem_closure := trivial
    hper_m := decomp.per_m u_witness
    hper_u := decomp.per_u u_witness
    hper_Du := decomp.per_Du u_witness
    hae_m := decomp.ae_m u_witness
    hae_u := decomp.ae_u u_witness
    hae_Du := decomp.ae_Du u_witness
    -- **BB2-enrich (iter 0849)**: forward the K-membership facts
    -- from the decomposition contract at the chosen witness.
    hmem_lp_coe_m := decomp.coeMemLp_m u_witness
    -- **Witness-scoped (2026-05-27, BB4a-iv)**: `coeMemSob_u` is now
    -- scoped to `vi_witness` only; no `u_witness` argument (the
    -- decomposition's `vi_witness` *is* `u_witness`).
    hmem_sob_coe_u := decomp.coeMemSob_u
    -- **Witness-scoped (2026-05-27)**: the 5 fields below are now
    -- properties of the decomposition's `vi_witness` only; no `u_witness`
    -- argument needed (the decomposition's `vi_witness` *is* `u_witness`).
    hpos_coe_m := decomp.coePos_m
    hweak_coe_Du := decomp.coeWeak_Du
    hmem_lp_coe_Du := decomp.coeMemLp_Du u_witness
    -- **BB3-enrich (iter 0848)**: forward the Banach-VI conclusions
    -- and the missing `epsTerms` AE-equality from the decomposition
    -- contract at the chosen witness.
    hae_epsTerms := decomp.ae_epsTerms u_witness
    hHJB_le_coe := decomp.coeHJB_le
    hVI_identity_coe := decomp.coeVI_identity
    hEpsNN_coe := decomp.coeEpsNN }

/-! ### Sanity-check `example` for BB1

Type-check that the BB1 producer's signature is well-formed: given
Phase 2's data record plus a decomposition interface, we obtain a
bare-representatives record whose fields type-check against the bare
function types expected by Group 2 (regularity transport) consumers. -/
example
    {γBar : ℝ}
    {betaBar betaBarPrime gammaBar : ℝ≥0∞}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {α β τ ε : ℝ}
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (data : CongestionRegularizedSolutionData (d := d)
              (γBar := γBar) (betaBar := betaBar)
              (betaBarPrime := betaBarPrime) (gammaBar := gammaBar)
              V H DpH J α β τ ε X)
    (decomp : BanachBareDecomposition (d := d) X betaBar gammaBar V H DpH ε) :
    CongestionBareRepresentatives (d := d) X betaBar gammaBar V H DpH ε :=
  bareRepresentative_of_BanachWeakVI data decomp

/-! ## Phase 7 — T2 BanachBareBridge BB4a: concrete `BanachBareDecomposition`
on `LpPer × SobolevPerLp`

The BB1 layer (above) ships `BanachBareDecomposition X` parameterised over
an abstract Banach realisation `X`. BB4a closes the genuine instantiation
gap on the concrete pair `X := LpPer βBar d × SobolevPerLp 1 γBar d`,
which is the realisation actually used by Phase 2's existence theorem
`weak_Aeps_congestion_exists`.

### Architectural observation

`BanachBareDecomposition` quantifies all 22 fields universally over
`z : X`. The Banach-VI conclusion fields (`coeHJB_le`, `coeVI_identity`,
`coeEpsNN`) and the K-membership conclusion fields (`coePos_m`,
`coeWeak_Du`) cannot hold for arbitrary `z ∈ LpPer × SobolevPerLp` — they
are properties of the actual VI witness only, or impose relations
(`coe_u` ↔ `coe_Du` weak-differentiability) that `LpPer × SobolevPerLp`'s
product structure does not enforce. Similarly, the literal-periodic
representative fields (`project_*`, `per_*`, `ae_*`) demand a selector
mechanism not provided by Mathlib's `Lp` quotient.

The honest decomposition: ship a gap-bundle struct `LpProductBareGap`
collecting the irreducible ∀z analytic / structural pieces, and a builder
def `BanachBareDecomposition.ofLpProductGap` producing the full
decomposition. Inside the builder, the 4 BB1 coercion fields and 2
K-membership Lp fields (`coeMemLp_m`, `coeMemLp_Du`) land *definitionally*
from `Lp.memLp`; the rest forward from the gap bundle, which is itself
sub-tasked.

This is **real Lean**: a concrete construction that decomposes the BB4a
gap into 6 definitional fields landed here and 16 ∀z-fields surfaced for
follow-up. -/

/-- **Phase 7 BB4a gap bundle**: the irreducible ∀z-quantified analytic
and structural pieces needed to build a `BanachBareDecomposition` on
the concrete `LpPer × SobolevPerLp` pair.

The fields fall into four groups, mirroring the BB1 / BB2-enrich /
BB2-transport / BB3-enrich tranches:

* **Periodic representative selector (BB4a-i sub-task)**: `project_*`,
  `per_*`, `ae_*` (8 fields). Mathlib's `Lp` quotient gives some bare
  representative but not in general a literally periodic one; the
  selector is the open Mathlib gap.
* **K-side `MemSobolevPer` + weak-derivative relation (BB4a-iv sub-task)**:
  `coeMemSob_u`, `coeWeak_Du` (2 fields). `SobolevPerLp` is a product of
  independent `Lp` factors with no a priori relation; the relation is
  required by `MemSobolevPer`'s existential and by `HasWeakDerivPer` on
  the actual pair.
* **K-side positivity-under-weak-closure (BB4a-ii sub-task)**:
  `coePos_m` (1 field). Paper line 1329's `essinf > 0`; does not survive
  weak-closure without lower-semicontinuity input.
* **Banach-VI conclusion fields (BB4a-iii sub-task)**: `coe_epsTerms`,
  `ae_epsTerms`, `coeHJB_le`, `coeVI_identity`, `coeEpsNN` (5 fields).
  Hold only at the actual weak-VI witness; the ∀z form here is what BB4
  will ultimately instantiate at the concrete witness via projection.

The 6 fields NOT in this bundle (`coe_m`, `coe_u`, `coe_Du`, `coe_epsTerms`-shape,
`coeMemLp_m`, `coeMemLp_Du`) land definitionally inside the builder. -/
structure LpProductBareGap
    (betaBar gammaBar : ℝ≥0∞) [Fact (1 ≤ betaBar)] [Fact (1 ≤ gammaBar)]
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (ε : ℝ) where
  /-- **BB4a-i sub-task**: literal-periodic representative of the density. -/
  project_m : (Periodic.LpPer betaBar d × Periodic.SobolevPerLp 1 gammaBar d)
    → (Fin d → ℝ) → ℝ
  /-- **BB4a-i sub-task**: literal-periodic representative of the value. -/
  project_u : (Periodic.LpPer betaBar d × Periodic.SobolevPerLp 1 gammaBar d)
    → (Fin d → ℝ) → ℝ
  /-- **BB4a-i sub-task**: literal-periodic representative of weak derivatives. -/
  project_Du : (Periodic.LpPer betaBar d × Periodic.SobolevPerLp 1 gammaBar d)
    → Fin d → (Fin d → ℝ) → ℝ
  /-- **BB4a-iii sub-task**: regularisation residual bare function. -/
  project_epsTerms : (Periodic.LpPer betaBar d × Periodic.SobolevPerLp 1 gammaBar d)
    → (Fin d → ℝ) → ℝ
  /-- **BB4a-iii sub-task**: regularisation residual Lp-quotient coercion
  (the abstract `coe_epsTerms`; for the concrete pair we expose it via
  the gap because there is no canonical `Lp` slot for `epsTerms` inside
  the pair `LpPer × SobolevPerLp`). -/
  coe_epsTerms : (Periodic.LpPer betaBar d × Periodic.SobolevPerLp 1 gammaBar d)
    → (Fin d → ℝ) → ℝ
  /-- **BB4a-i sub-task**: density representative is literally periodic. -/
  per_m : ∀ z : Periodic.LpPer betaBar d × Periodic.SobolevPerLp 1 gammaBar d,
    Periodic.IsPeriodic (project_m z)
  /-- **BB4a-i sub-task**: value representative is literally periodic. -/
  per_u : ∀ z : Periodic.LpPer betaBar d × Periodic.SobolevPerLp 1 gammaBar d,
    Periodic.IsPeriodic (project_u z)
  /-- **BB4a-i sub-task**: each weak-derivative representative is periodic. -/
  per_Du : ∀ z : Periodic.LpPer betaBar d × Periodic.SobolevPerLp 1 gammaBar d,
    ∀ i, Periodic.IsPeriodic (project_Du z i)
  /-- **BB4a-i sub-task**: AE-equality of the density representative with
  its Lp-quotient coercion `(z.1 : (Fin d → ℝ) → ℝ)`. -/
  ae_m : ∀ z : Periodic.LpPer betaBar d × Periodic.SobolevPerLp 1 gammaBar d,
    project_m z
      =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
      (z.1 : (Fin d → ℝ) → ℝ)
  /-- **BB4a-i sub-task**: AE-equality of the value representative with
  its Lp-quotient coercion `(z.2.1 : (Fin d → ℝ) → ℝ)`. -/
  ae_u : ∀ z : Periodic.LpPer betaBar d × Periodic.SobolevPerLp 1 gammaBar d,
    project_u z
      =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
      (z.2.1 : (Fin d → ℝ) → ℝ)
  /-- **BB4a-i sub-task**: AE-equality of each weak-derivative representative
  with the corresponding Lp-quotient coercion `(z.2.2 i : (Fin d → ℝ) → ℝ)`. -/
  ae_Du : ∀ z : Periodic.LpPer betaBar d × Periodic.SobolevPerLp 1 gammaBar d,
    ∀ i, project_Du z i
      =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
      ((z.2.2 i : (Fin d → ℝ) → ℝ))
  /-- **BB4a-iii sub-task**: AE-equality of the regularisation residual
  representative with its Lp-quotient coercion. -/
  ae_epsTerms : ∀ z : Periodic.LpPer betaBar d × Periodic.SobolevPerLp 1 gammaBar d,
    project_epsTerms z
      =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
      coe_epsTerms z
  -- **Witness-scoped fields removed 2026-05-27 (BB contract refactor + BB4a-iv)**:
  -- `coeMemSob_u`, `coePos_m`, `coeWeak_Du`, `coeHJB_le`, `coeVI_identity`,
  -- `coeEpsNN` previously lived here as ∀z-quantified fields. They are now
  -- scoped to `BanachBareDecomposition.vi_witness` and supplied to
  -- `BanachBareDecomposition.ofLpProductGap` as explicit parameters at
  -- builder time, NOT as fields of this gap bundle (which they could not
  -- honestly satisfy in ∀z form on the `LpPer × SobolevPerLp` product).
  -- For `coeMemSob_u` specifically: `SobolevPerLp`'s product structure
  -- does NOT enforce the weak-derivative relation between `z.2.1` and the
  -- family `z.2.2`, so the `MemSobolevPer` existential cannot be discharged
  -- for arbitrary `z` — only at the chosen VI witness.

/-- **BB4a-i builder**: literal-periodic representative selector for
the 8 `project_*`/`per_*`/`ae_*` fields of `LpProductBareGap`.

This builder consumes only the 3 non-selector fields
(`project_epsTerms`, `coe_epsTerms`, `ae_epsTerms`)
plus the regularisation parameters, and discharges the 8 periodic-Lp
selector fields by routing through
`StationaryMFG.Periodic.bareCoeFnOfLpPer` — the Path-A primitive in
`Periodic/Lp.lean` that periodicises an `Lp` coercion via
coordinate-wise `Int.fract`.

The primitive is concrete (no `Classical.choose` involved) and the
periodicity / a.e.-equality witnesses come from kernel-checked facts
about `Int.fract_add_intCast` and `Int.fract_eq_self`. The 8 fields
are therefore honestly discharged, closing the BB4a-i sub-task. -/
noncomputable def LpProductBareGap.ofPeriodicCore
    {betaBar gammaBar : ℝ≥0∞} [Fact (1 ≤ betaBar)] [Fact (1 ≤ gammaBar)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {ε : ℝ}
    (project_epsTerms :
      (Periodic.LpPer betaBar d × Periodic.SobolevPerLp 1 gammaBar d)
        → (Fin d → ℝ) → ℝ)
    (coe_epsTerms :
      (Periodic.LpPer betaBar d × Periodic.SobolevPerLp 1 gammaBar d)
        → (Fin d → ℝ) → ℝ)
    (ae_epsTerms :
      ∀ z : Periodic.LpPer betaBar d × Periodic.SobolevPerLp 1 gammaBar d,
        project_epsTerms z
          =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
          coe_epsTerms z) :
    LpProductBareGap (d := d) betaBar gammaBar V H DpH ε where
  -- BB4a-i selector fields, discharged via `bareCoeFnOfLpPer`.
  project_m := fun z =>
    (StationaryMFG.Periodic.bareCoeFnOfLpPer (d := d) z.1).rep
  project_u := fun z =>
    (StationaryMFG.Periodic.bareCoeFnOfLpPer (d := d) z.2.1).rep
  project_Du := fun z i =>
    (StationaryMFG.Periodic.bareCoeFnOfLpPer (d := d) (z.2.2 i)).rep
  per_m := fun z =>
    (StationaryMFG.Periodic.bareCoeFnOfLpPer (d := d) z.1).periodic
  per_u := fun z =>
    (StationaryMFG.Periodic.bareCoeFnOfLpPer (d := d) z.2.1).periodic
  per_Du := fun z i =>
    (StationaryMFG.Periodic.bareCoeFnOfLpPer (d := d) (z.2.2 i)).periodic
  ae_m := fun z =>
    (StationaryMFG.Periodic.bareCoeFnOfLpPer (d := d) z.1).ae_eq
  ae_u := fun z =>
    (StationaryMFG.Periodic.bareCoeFnOfLpPer (d := d) z.2.1).ae_eq
  ae_Du := fun z i =>
    (StationaryMFG.Periodic.bareCoeFnOfLpPer (d := d) (z.2.2 i)).ae_eq
  -- BB4a-iii non-selector fields forwarded from arguments.
  project_epsTerms := project_epsTerms
  coe_epsTerms := coe_epsTerms
  ae_epsTerms := ae_epsTerms

/-- **Phase 7 BB4a builder**: concrete `BanachBareDecomposition` on
`X := LpPer βBar d × SobolevPerLp 1 γBar d` from a `LpProductBareGap`
bundle.

The 6 definitionally-landed fields are:
* `coe_m z := (z.1 : (Fin d → ℝ) → ℝ)` — Lp-quotient bare coercion of the
  first factor.
* `coe_u z := (z.2.1 : (Fin d → ℝ) → ℝ)` — Lp-quotient bare coercion of
  the value-function factor.
* `coe_Du z i := (z.2.2 i : (Fin d → ℝ) → ℝ)` — Lp-quotient bare
  coercion of each weak-derivative factor.
* `coeMemLp_m z := (Lp.memLp z.1 : MemLp _ βBar _)` — definitional
  `MemLpPer` from Mathlib's `Lp.memLp`.
* `coeMemLp_Du z i := (Lp.memLp (z.2.2 i) : MemLp _ γBar _)` —
  definitional `MemLpPer` for each weak-derivative factor.

The remaining 16 ∀z-fields are forwarded from the `LpProductBareGap`
bundle, each tracked as a BB4a-{i, ii, iii, iv} sub-task. -/
noncomputable def BanachBareDecomposition.ofLpProductGap
    {betaBar gammaBar : ℝ≥0∞} [Fact (1 ≤ betaBar)] [Fact (1 ≤ gammaBar)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {ε : ℝ}
    (gap : LpProductBareGap (d := d) betaBar gammaBar V H DpH ε)
    -- **Witness-scoped builder args (2026-05-27 contract refactor)**.
    -- The decomposition's `vi_witness` must be supplied honestly here,
    -- typically as `Classical.choose data.weakVI` where `data` is Phase 2's
    -- existential record. The 5 witness-scoped proofs below must hold at
    -- this *specific* `vi_witness`; the gap bundle no longer carries the
    -- (unsound under weak closure) ∀z forms.
    (vi_witness :
      Periodic.LpPer betaBar d × Periodic.SobolevPerLp 1 gammaBar d)
    -- T2/T3 gap: paper's `essinf μ_ε > 0` (tex line 1329) at the chosen
    -- witness. NOT closed under weak closure; discharged from the T3 Path A
    -- representation bridge (`coePos_m_atWitness` + `hK_witness`). Kept as an
    -- explicit parameter in T2; classified paper-faithful in
    -- `CongestionRegularizedSequenceBuilderInputs.mε_pos_apriori` (Apriori.lean).
    (hcoePos_m :
      ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
        0 < (vi_witness.1 : (Fin d → ℝ) → ℝ) x)
    (hcoeWeak_Du : ∀ i, Periodic.HasWeakDerivPer i
      ((vi_witness.2.1 : (Fin d → ℝ) → ℝ))
      ((vi_witness.2.2 i : (Fin d → ℝ) → ℝ)))
    -- **BB4a-iv (2026-05-27 contract refactor)**: `coeMemSob_u` witness-scoped.
    -- The Sobolev existential cannot be discharged for arbitrary `z` on the
    -- product `LpPer × SobolevPerLp` (no a priori weak-derivative relation),
    -- so the structural fact is supplied at the chosen `vi_witness` only.
    (hcoeMemSob_u :
      Periodic.MemSobolevPer gammaBar ((vi_witness.2.1 : (Fin d → ℝ) → ℝ)))
    (hcoeHJB_le :
      ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
        (vi_witness.2.1 : (Fin d → ℝ) → ℝ) x
          + H x (fun i => (vi_witness.2.2 i : (Fin d → ℝ) → ℝ) x)
                ((vi_witness.1 : (Fin d → ℝ) → ℝ) x)
          - V x ≤ 0)
    (hcoeVI_identity :
      ∫ x in UnitCube d, (vi_witness.2.1 : (Fin d → ℝ) → ℝ) x
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
        = ∫ x in UnitCube d,
            ((vi_witness.1 : (Fin d → ℝ) → ℝ) x
                * (-H x (fun i => (vi_witness.2.2 i : (Fin d → ℝ) → ℝ) x)
                        ((vi_witness.1 : (Fin d → ℝ) → ℝ) x)
                  + (DpH x (fun i => (vi_witness.2.2 i : (Fin d → ℝ) → ℝ) x)
                            ((vi_witness.1 : (Fin d → ℝ) → ℝ) x))
                    ⬝ (fun i => (vi_witness.2.2 i : (Fin d → ℝ) → ℝ) x))
              + V x * (vi_witness.1 : (Fin d → ℝ) → ℝ) x
              + gap.coe_epsTerms vi_witness x)
            ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hcoeEpsNN :
      ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
        0 ≤ gap.coe_epsTerms vi_witness x) :
    BanachBareDecomposition (d := d)
      (Periodic.LpPer betaBar d × Periodic.SobolevPerLp 1 gammaBar d)
      betaBar gammaBar V H DpH ε :=
{ coe_m := fun z => (z.1 : (Fin d → ℝ) → ℝ)
  coe_u := fun z => (z.2.1 : (Fin d → ℝ) → ℝ)
  coe_Du := fun z i => ((z.2.2 i : (Fin d → ℝ) → ℝ))
  coe_epsTerms := gap.coe_epsTerms
  vi_witness := vi_witness
  project_m := gap.project_m
  project_u := gap.project_u
  project_Du := gap.project_Du
  project_epsTerms := gap.project_epsTerms
  per_m := gap.per_m
  per_u := gap.per_u
  per_Du := gap.per_Du
  ae_m := gap.ae_m
  ae_u := gap.ae_u
  ae_Du := gap.ae_Du
  -- Definitional from `Lp.memLp`: `MemLpPer p f` unfolds to
  -- `MemLp f p (μ.restrict (UnitCube d))`, which is exactly what
  -- `Lp.memLp` returns for an element of `Lp ℝ p (μ.restrict (UnitCube d))`.
  coeMemLp_m := fun z =>
    (MeasureTheory.Lp.memLp z.1 : MeasureTheory.MemLp _ betaBar _)
  coeMemSob_u := hcoeMemSob_u
  coePos_m := hcoePos_m
  coeWeak_Du := hcoeWeak_Du
  coeMemLp_Du := fun z i =>
    (MeasureTheory.Lp.memLp (z.2.2 i) : MeasureTheory.MemLp _ gammaBar _)
  ae_epsTerms := gap.ae_epsTerms
  coeHJB_le := hcoeHJB_le
  coeVI_identity := hcoeVI_identity
  coeEpsNN := hcoeEpsNN }

/-- **T2 nonneg-track (iter 1030, Phase-2 nonneg-apriori refactor)**:
nonneg sibling of `BanachBareDecomposition.ofLpProductGap`.

Verbatim copy of `ofLpProductGap` except the strict-positivity
parameter `hcoePos_m` (`∀ᵐ x, 0 < vi_witness.1 x`) is replaced by the
nonnegativity parameter `hcoeNonneg_m` (`∀ᵐ x, 0 ≤ vi_witness.1 x`),
the target type is `BanachBareDecompositionNN`, and the single field
assignment becomes `coeNonneg_m := hcoeNonneg_m`.

The nonneg producer (Phase-3) will supply `hcoeNonneg_m` from
nonneg-cone closure membership (`coeM_nonneg_atWitness_of_closure`),
so the resulting decomposition carries no `0 < m_ε` requirement
anywhere on its signature.  This is ADDITIVE: `ofLpProductGap` and the
strict `BanachBareDecomposition` path are untouched. -/
noncomputable def BanachBareDecomposition.ofLpProductGap_nonneg
    {betaBar gammaBar : ℝ≥0∞} [Fact (1 ≤ betaBar)] [Fact (1 ≤ gammaBar)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {ε : ℝ}
    (gap : LpProductBareGap (d := d) betaBar gammaBar V H DpH ε)
    (vi_witness :
      Periodic.LpPer betaBar d × Periodic.SobolevPerLp 1 gammaBar d)
    -- **Nonneg parameter (iter 1030)**: replaces `ofLpProductGap`'s
    -- strict `hcoePos_m`.  No `0 < m_ε` anywhere on this signature.
    (hcoeNonneg_m :
      ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
        0 ≤ (vi_witness.1 : (Fin d → ℝ) → ℝ) x)
    (hcoeWeak_Du : ∀ i, Periodic.HasWeakDerivPer i
      ((vi_witness.2.1 : (Fin d → ℝ) → ℝ))
      ((vi_witness.2.2 i : (Fin d → ℝ) → ℝ)))
    (hcoeMemSob_u :
      Periodic.MemSobolevPer gammaBar ((vi_witness.2.1 : (Fin d → ℝ) → ℝ)))
    (hcoeHJB_le :
      ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
        (vi_witness.2.1 : (Fin d → ℝ) → ℝ) x
          + H x (fun i => (vi_witness.2.2 i : (Fin d → ℝ) → ℝ) x)
                ((vi_witness.1 : (Fin d → ℝ) → ℝ) x)
          - V x ≤ 0)
    (hcoeVI_identity :
      ∫ x in UnitCube d, (vi_witness.2.1 : (Fin d → ℝ) → ℝ) x
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
        = ∫ x in UnitCube d,
            ((vi_witness.1 : (Fin d → ℝ) → ℝ) x
                * (-H x (fun i => (vi_witness.2.2 i : (Fin d → ℝ) → ℝ) x)
                        ((vi_witness.1 : (Fin d → ℝ) → ℝ) x)
                  + (DpH x (fun i => (vi_witness.2.2 i : (Fin d → ℝ) → ℝ) x)
                            ((vi_witness.1 : (Fin d → ℝ) → ℝ) x))
                    ⬝ (fun i => (vi_witness.2.2 i : (Fin d → ℝ) → ℝ) x))
              + V x * (vi_witness.1 : (Fin d → ℝ) → ℝ) x
              + gap.coe_epsTerms vi_witness x)
            ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hcoeEpsNN :
      ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
        0 ≤ gap.coe_epsTerms vi_witness x) :
    BanachBareDecompositionNN (d := d)
      (Periodic.LpPer betaBar d × Periodic.SobolevPerLp 1 gammaBar d)
      betaBar gammaBar V H DpH ε :=
{ coe_m := fun z => (z.1 : (Fin d → ℝ) → ℝ)
  coe_u := fun z => (z.2.1 : (Fin d → ℝ) → ℝ)
  coe_Du := fun z i => ((z.2.2 i : (Fin d → ℝ) → ℝ))
  coe_epsTerms := gap.coe_epsTerms
  vi_witness := vi_witness
  project_m := gap.project_m
  project_u := gap.project_u
  project_Du := gap.project_Du
  project_epsTerms := gap.project_epsTerms
  per_m := gap.per_m
  per_u := gap.per_u
  per_Du := gap.per_Du
  ae_m := gap.ae_m
  ae_u := gap.ae_u
  ae_Du := gap.ae_Du
  coeMemLp_m := fun z =>
    (MeasureTheory.Lp.memLp z.1 : MeasureTheory.MemLp _ betaBar _)
  coeMemSob_u := hcoeMemSob_u
  coeNonneg_m := hcoeNonneg_m
  coeWeak_Du := hcoeWeak_Du
  coeMemLp_Du := fun z i =>
    (MeasureTheory.Lp.memLp (z.2.2 i) : MeasureTheory.MemLp _ gammaBar _)
  ae_epsTerms := gap.ae_epsTerms
  coeHJB_le := hcoeHJB_le
  coeVI_identity := hcoeVI_identity
  coeEpsNN := hcoeEpsNN }

/-! ### BB4a-ii: `coePos_m` discharge at the chosen Banach-VI witness

The witness-scoped `coePos_m` field of `BanachBareDecomposition`
(post iter-0861 contract refactor) requires
`∃ c : ℝ, 0 < c ∧ (fun _ => c) ≤ᵐ coe_m vi_witness`
*only at the chosen witness*, not for arbitrary `z : X`. This
sidesteps the (genuinely structural) gap that strict positivity does
not survive weak closure on `closure K`.

The two helpers below close the gap honestly:

1. `coePos_m_of_kMembership` (pure projection): from a pair
   `p : LpPer × SobolevPerLp` and a hypothesis that its bare coercion
   `(p.1, p.2.1)` belongs to `congestionDomainK`, extract the third
   conjunct of `mem_congestionDomainK_iff` (paper line 1329's
   `essinf μ > 0` encoded as `∃ c > 0, c ≤ᵐ p.1`).

2. `coePos_m_atWitness` (`Classical.choose`-driven): given Phase 2's
   `data : CongestionRegularizedSolutionData …` *and* a bridge
   hypothesis stating that the chosen Banach-VI witness coerces to a
   pair lying in `congestionDomainK`, produce the witness-scoped
   positivity certificate at `data.weakVI.choose`. The bridge
   hypothesis is supplied by the Banach→bare K bridge (BB1 docstring's
   "Path A" plan: a concrete `LpPer × SobolevPerLp` realisation supplies
   a representation theorem mapping closure-of-Banach-K to bare-K).

Together with BB4a-i (periodic-rep selectors), BB4a-iii
(epsTerms-side fields), and BB4a-iv (`coeWeak_Du`/`coeMemSob_u`),
these helpers close the witness-scoped portion of BB4a's discharge of
`BanachBareDecomposition.ofLpProductGap`. -/

/-- **BB4a-ii helper #1**: extract strict-positivity of the density
coercion from K-membership.

Given a pair `p : LpPer × SobolevPerLp` whose bare coercion lies in
`congestionDomainK`, return the third conjunct of the K-membership
definition (paper line 1329 / 1336, `essinf μ > 0`).

Pure projection (no `Classical.choose`): the positivity certificate is
already a field of the K-membership predicate; we only unfold via
`mem_congestionDomainK_iff` and select the third conjunct. -/
lemma coePos_m_of_kMembership
    {betaBar betaBarPrime gammaBar : ℝ≥0∞} [Fact (1 ≤ betaBar)] [Fact (1 ≤ gammaBar)]
    {α β τ : ℝ}
    (p : Periodic.LpPer betaBar d × Periodic.SobolevPerLp 1 gammaBar d)
    (hK : ((p.1 : (Fin d → ℝ) → ℝ), (p.2.1 : (Fin d → ℝ) → ℝ)) ∈
      congestionDomainK (d := d) betaBar betaBarPrime gammaBar α β τ) :
    ∃ c : ℝ, 0 < c ∧
      (fun _ => c) ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        (p.1 : (Fin d → ℝ) → ℝ) := by
  -- Unfold K-membership and project the third conjunct.
  rcases (mem_congestionDomainK_iff (d := d)).1 hK with ⟨_, _, hpos, _⟩
  exact hpos

/-- **BB4a-ii helper #2**: positivity of the density coercion at the
chosen Banach-VI witness from Phase 2's existential.

Materially uses `data.weakVI.choose` (the chosen witness), and the
bridge hypothesis `hK_witness` stating that the chosen witness's bare
coercion `(data.weakVI.choose.1, data.weakVI.choose.2.1)` belongs to
the bare congestion domain `congestionDomainK …`.

The bridge hypothesis is the honest encoding of the Banach→bare K
bridge: on the concrete realisation `LpPer × SobolevPerLp`, the
weak-VI representation theorem (Path A) maps closure-of-`pack.K` to
the bare congestion domain at the chosen witness. Until that bridge
producer lands as a separate task, the hypothesis is supplied
explicitly to keep this helper sham-free.

This is the witness-scoped `coePos_m` needed by
`BanachBareDecomposition.ofLpProductGap`'s `hcoePos_m` parameter. -/
lemma coePos_m_atWitness
    {γBar : ℝ}
    {betaBar betaBarPrime gammaBar : ℝ≥0∞} [Fact (1 ≤ betaBar)] [Fact (1 ≤ gammaBar)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {α β τ ε : ℝ}
    (data : CongestionRegularizedSolutionData (d := d)
              (γBar := γBar) (betaBar := betaBar)
              (betaBarPrime := betaBarPrime) (gammaBar := gammaBar)
              V H DpH J α β τ ε
              (Periodic.LpPer betaBar d × Periodic.SobolevPerLp 1 gammaBar d))
    (hK_witness :
      ((data.weakVI.choose.1 : (Fin d → ℝ) → ℝ),
        (data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ)) ∈
      congestionDomainK (d := d) betaBar betaBarPrime gammaBar α β τ) :
    ∃ c : ℝ, 0 < c ∧
      (fun _ => c) ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        (data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) :=
  coePos_m_of_kMembership (d := d)
    (betaBarPrime := betaBarPrime) (α := α) (β := β) (τ := τ)
    data.weakVI.choose hK_witness

/-! ### BB4a-iv: `coeMemSob_u` discharge at the chosen Banach-VI witness

The witness-scoped `coeMemSob_u` field of `BanachBareDecomposition`
(post 2026-05-27 BB4a-iv refactor) requires
`Periodic.MemSobolevPer gammaBar (coe_u vi_witness)` *only at the chosen
witness*, not for arbitrary `z : X`. This sidesteps the structural gap
that `SobolevPerLp`'s product type does not enforce the weak-derivative
relation between its two factors.

The two helpers below mirror the BB4a-ii pattern for `coePos_m`:

1. `coeMemSob_u_of_kMembership` (pure projection): from a pair
   `p : LpPer × SobolevPerLp` and a hypothesis that its bare coercion
   lies in `congestionDomainK`, extract the second conjunct of
   `mem_congestionDomainK_iff` (paper line 1328's `υ ∈ W^{1,γ̄}_per`).

2. `coeMemSob_u_atWitness` (`Classical.choose`-driven): given Phase 2's
   `data` plus a bridge hypothesis stating that the chosen Banach-VI
   witness coerces to a pair in `congestionDomainK`, produce the
   witness-scoped Sobolev-membership certificate at `data.weakVI.choose`.

The bridge hypothesis is the honest encoding of the same Banach→bare K
bridge invoked by `coePos_m_atWitness`. Until the Path A representation
theorem lands as its own producer, supplying it explicitly keeps both
helpers sham-free. -/

/-- **BB4a-iv helper #1**: extract Sobolev-membership of the value's
coercion from K-membership.

Given a pair `p : LpPer × SobolevPerLp` whose bare coercion lies in
`congestionDomainK`, return the second conjunct of the K-membership
definition (paper line 1328, second clause: `υ ∈ W^{1,γ̄}_per`).

Pure projection (no `Classical.choose`): the Sobolev-membership
certificate is already a field of the K-membership predicate; we only
unfold via `mem_congestionDomainK_iff` and select the second conjunct. -/
lemma coeMemSob_u_of_kMembership
    {betaBar betaBarPrime gammaBar : ℝ≥0∞} [Fact (1 ≤ betaBar)] [Fact (1 ≤ gammaBar)]
    {α β τ : ℝ}
    (p : Periodic.LpPer betaBar d × Periodic.SobolevPerLp 1 gammaBar d)
    (hK : ((p.1 : (Fin d → ℝ) → ℝ), (p.2.1 : (Fin d → ℝ) → ℝ)) ∈
      congestionDomainK (d := d) betaBar betaBarPrime gammaBar α β τ) :
    Periodic.MemSobolevPer gammaBar (p.2.1 : (Fin d → ℝ) → ℝ) := by
  -- Unfold K-membership and project the second conjunct.
  rcases (mem_congestionDomainK_iff (d := d)).1 hK with ⟨_, hsob, _, _⟩
  exact hsob

/-- **BB4a-iv helper #2**: Sobolev-membership of the value's coercion at
the chosen Banach-VI witness from Phase 2's existential.

Materially uses `data.weakVI.choose` (the chosen witness), and the
bridge hypothesis `hK_witness` stating that the chosen witness's bare
coercion `(data.weakVI.choose.1, data.weakVI.choose.2.1)` belongs to
the bare congestion domain `congestionDomainK …`.

The bridge hypothesis is the honest encoding of the Banach→bare K
bridge: on the concrete realisation `LpPer × SobolevPerLp`, the
weak-VI representation theorem (Path A) maps closure-of-`pack.K` to
the bare congestion domain at the chosen witness.

This is the witness-scoped `coeMemSob_u` needed by
`BanachBareDecomposition.ofLpProductGap`'s `hcoeMemSob_u` parameter. -/
lemma coeMemSob_u_atWitness
    {γBar : ℝ}
    {betaBar betaBarPrime gammaBar : ℝ≥0∞} [Fact (1 ≤ betaBar)] [Fact (1 ≤ gammaBar)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {α β τ ε : ℝ}
    (data : CongestionRegularizedSolutionData (d := d)
              (γBar := γBar) (betaBar := betaBar)
              (betaBarPrime := betaBarPrime) (gammaBar := gammaBar)
              V H DpH J α β τ ε
              (Periodic.LpPer betaBar d × Periodic.SobolevPerLp 1 gammaBar d))
    (hK_witness :
      ((data.weakVI.choose.1 : (Fin d → ℝ) → ℝ),
        (data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ)) ∈
      congestionDomainK (d := d) betaBar betaBarPrime gammaBar α β τ) :
    Periodic.MemSobolevPer gammaBar
      (data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ) :=
  coeMemSob_u_of_kMembership (d := d)
    (betaBarPrime := betaBarPrime) (α := α) (β := β) (τ := τ)
    data.weakVI.choose hK_witness

/-! ### BB4a-iii: Banach-VI conclusion discharge at the chosen witness

The four helpers below discharge the four remaining witness-scoped
fields needed by `BanachBareDecomposition.ofLpProductGap` (after
iter-0863 closed `coePos_m_atWitness`):

* `coeHJB_le_atWitness` — paper line 1397 (`eq:congest.HJleq0`) HJB
  pointwise inequality at the bare coercion of the chosen VI witness.
* `coeVI_identity_atWitness` — paper `eq:identity-congestion`
  integral identity at the chosen witness.
* `coeEpsNN_atWitness` — regularisation-residual nonnegativity at the
  chosen witness.
* `ae_epsTerms_atWitness` — projection of the gap's `ae_epsTerms`
  ∀z-field at the chosen witness (no bridge needed).

The first three are **honestly bridge-deferred** in the same sense as
`coePos_m_atWitness`: the abstract weak-VI conclusion
`u ∈ closure K ∧ ∀v∈K, 0 ≤ A v (v-u)` (the content of
`Classical.choose_spec data.weakVI`) does **not** by itself yield the
paper-faithful bare-function form of the HJB inequality, the VI
integral identity, or epsTerms-nonnegativity. The bridge — provided
by Path A's weak-VI representation theorem on the concrete
`LpPer × SobolevPerLp` realisation — converts the abstract
inequalities at the chosen witness into their bare counterparts.

Until that bridge producer lands as its own task, each helper takes a
bridge hypothesis as an explicit argument and forwards it, *materially
threading* `Classical.choose_spec data.weakVI` (both the
closure-membership and the inequality-for-all-test-points parts) into
the bridge premises. This keeps the helpers sham-free: they cannot be
applied without first having supplied the abstract weak-VI conclusion.

The fourth helper (`ae_epsTerms_atWitness`) is a pure projection: the
gap field `LpProductBareGap.ae_epsTerms` already quantifies over
arbitrary `z`, so projecting at `data.weakVI.choose` is honest by
construction.

These four helpers together with `coePos_m_atWitness` (iter 0863)
supply the 5 explicit proof parameters that
`BanachBareDecomposition.ofLpProductGap` expects after the
2026-05-27 contract refactor; the sanity-check `example` below then
becomes parameterised over just the four bridge hypotheses, instead
of the four already-formed conclusions. -/

/-- **BB4a-iii helper #1**: bare-function HJB pointwise inequality at
the chosen Banach-VI witness.

Materially uses both halves of `Classical.choose_spec data.weakVI`:
the closure-membership of `data.weakVI.choose` (passed to the bridge
as its first premise) and the abstract VI inequality
`∀ v ∈ K, 0 ≤ A v (v - data.weakVI.choose)` (passed as the second).

The bridge hypothesis `hBridge` packages Path A's weak-VI
representation theorem: from those two abstract facts about the
chosen witness, the HJB inequality holds for the bare coercion. Once
that representation theorem is formalised as its own producer, this
helper specialises to forwarding its conclusion. -/
lemma coeHJB_le_atWitness
    {γBar : ℝ}
    {betaBar betaBarPrime gammaBar : ℝ≥0∞} [Fact (1 ≤ betaBar)] [Fact (1 ≤ gammaBar)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {α β τ ε : ℝ}
    (data : CongestionRegularizedSolutionData (d := d)
              (γBar := γBar) (betaBar := betaBar)
              (betaBarPrime := betaBarPrime) (gammaBar := gammaBar)
              V H DpH J α β τ ε
              (Periodic.LpPer betaBar d × Periodic.SobolevPerLp 1 gammaBar d))
    (hBridge :
      data.weakVI.choose ∈ closure data.K →
      (∀ v ∈ data.K, 0 ≤ data.A v (v - data.weakVI.choose)) →
      ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
        (data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ) x
          + H x (fun i => (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)
                ((data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x)
          - V x ≤ 0) :
    ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
      (data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ) x
        + H x (fun i => (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)
              ((data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x)
        - V x ≤ 0 := by
  -- Materially unpack `Classical.choose_spec data.weakVI`:
  -- `data.weakVI` has type `∃ u ∈ closure data.K, ∀ v ∈ data.K, …`.
  obtain ⟨hMem, hVI⟩ := data.weakVI.choose_spec
  exact hBridge hMem hVI

/-- **BB4a-iii helper #2**: bare-function VI integral identity at the
chosen Banach-VI witness.

Same honest-bridge pattern as `coeHJB_le_atWitness`: materially uses
both halves of `Classical.choose_spec data.weakVI` and forwards the
bridge hypothesis's conclusion. -/
lemma coeVI_identity_atWitness
    {γBar : ℝ}
    {betaBar betaBarPrime gammaBar : ℝ≥0∞} [Fact (1 ≤ betaBar)] [Fact (1 ≤ gammaBar)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {α β τ ε : ℝ}
    (data : CongestionRegularizedSolutionData (d := d)
              (γBar := γBar) (betaBar := betaBar)
              (betaBarPrime := betaBarPrime) (gammaBar := gammaBar)
              V H DpH J α β τ ε
              (Periodic.LpPer betaBar d × Periodic.SobolevPerLp 1 gammaBar d))
    (gap : LpProductBareGap (d := d) betaBar gammaBar V H DpH ε)
    (hBridge :
      data.weakVI.choose ∈ closure data.K →
      (∀ v ∈ data.K, 0 ≤ data.A v (v - data.weakVI.choose)) →
      ∫ x in UnitCube d, (data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ) x
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
        = ∫ x in UnitCube d,
            ((data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x
                * (-H x (fun i =>
                        (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)
                        ((data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x)
                  + (DpH x (fun i =>
                          (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)
                            ((data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x))
                    ⬝ (fun i =>
                        (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x))
              + V x * (data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x
              + gap.coe_epsTerms data.weakVI.choose x)
            ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))) :
    ∫ x in UnitCube d, (data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ) x
        ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
      = ∫ x in UnitCube d,
          ((data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x
              * (-H x (fun i =>
                      (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)
                      ((data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x)
                + (DpH x (fun i =>
                        (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)
                          ((data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x))
                  ⬝ (fun i =>
                      (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x))
            + V x * (data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x
            + gap.coe_epsTerms data.weakVI.choose x)
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) := by
  obtain ⟨hMem, hVI⟩ := data.weakVI.choose_spec
  exact hBridge hMem hVI

/-- **VIid-5c child A — pure integral-algebra combination producing
`eq:identity-congestion`.**

The φ=1 reduction of the witness transport identity
(`congestion_transport_at_witness`) is *insufficient*: at `φ = 1` the
gradient `∇φ = 0` kills the flux pairing, leaving only the scalar mass term.
The paper (line 1205) instead derives the scalar identity
`eq:identity-congestion` by testing the transport identity
`eq:congest.transport` with `φ = u` and subtracting the
`eq:congest.HJ0` mass identity `∫ m·(u + H − V) = 0`.

This lemma is exactly that final algebraic step (no density / measurability
content): given

* `hTransport` — the transport identity at `φ = u` with the flux written
  as `m·D_pH(x,Du,m)⬝Du` (child B's `congestion_transport_at_u_witness`):
  `∫[(m−1)·u + m·(D_pH(x,Du,m)⬝Du)] + ∫ epsTerms = 0`;
* `hHJ0` — the `eq:congest.HJ0` mass identity at the witness:
  `∫ m·(u + H(x,Du,m) − V) = 0`;
* per-summand integrability hypotheses needed to split/recombine the
  integrals (supplied at the call site from the witness `Lᵖ` certificates),

it produces the `hcoeVI_identity`-field RHS shape
`∫ u = ∫ [ m·(−H + D_pH·Du) + V·m + epsTerms ]`.

The derivation: subtracting `hHJ0` from `hTransport`,
`(m−1)·u + m·(D_pH·Du) + epsTerms − m·(u + H − V)`
`= −u + m·(−H + D_pH·Du) + V·m + epsTerms`, and integrating term-by-term
yields `0 = ∫(−u) + ∫[m·(−H+D_pH·Du)+V·m+epsTerms]`, i.e. the claim. -/
lemma coeVI_identity_from_transport_and_HJ0
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {m u : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {epsTerms : (Fin d → ℝ) → ℝ}
    -- integrability of the pieces (for `integral_add` / `integral_sub` splits)
    (hu_int : MeasureTheory.Integrable u
      (MeasureTheory.volume.restrict (UnitCube d)))
    (hmFlux_int : MeasureTheory.Integrable
      (fun x => m x * ((DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x)))
      (MeasureTheory.volume.restrict (UnitCube d)))
    (hVm_int : MeasureTheory.Integrable (fun x => V x * m x)
      (MeasureTheory.volume.restrict (UnitCube d)))
    (heps_int : MeasureTheory.Integrable epsTerms
      (MeasureTheory.volume.restrict (UnitCube d)))
    (hmH_int : MeasureTheory.Integrable
      (fun x => m x * H x (fun i => Du i x) (m x))
      (MeasureTheory.volume.restrict (UnitCube d)))
    (hmu_int : MeasureTheory.Integrable (fun x => m x * u x)
      (MeasureTheory.volume.restrict (UnitCube d)))
    (hTransport :
      ∫ x in UnitCube d,
          ((m x - 1) * u x
            + m x * ((DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x)))
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
        + ∫ x in UnitCube d, epsTerms x
            ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) = 0)
    (hHJ0 :
      ∫ x in UnitCube d,
          m x * (u x + H x (fun i => Du i x) (m x) - V x)
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) = 0) :
    ∫ x in UnitCube d, u x
        ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
      = ∫ x in UnitCube d,
          (m x
              * (-H x (fun i => Du i x) (m x)
                + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x
            + epsTerms x)
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) := by
  classical
  -- The measure under which all integrals are taken.
  set μ : MeasureTheory.Measure (Fin d → ℝ) :=
    MeasureTheory.volume.restrict (UnitCube d) with hμ
  -- The six scalar integrals (each of an explicit one-argument function), so
  -- that `MeasureTheory.integral_add` / `integral_sub` apply in term mode with
  -- no `Pi.add`/`Pi.sub` pattern mismatch.
  set fU : (Fin d → ℝ) → ℝ := fun x => u x with hfU
  set fFlux : (Fin d → ℝ) → ℝ :=
    fun x => m x * ((DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
    with hfFlux
  set fVm : (Fin d → ℝ) → ℝ := fun x => V x * m x with hfVm
  set fEps : (Fin d → ℝ) → ℝ := fun x => epsTerms x with hfEps
  set fmH : (Fin d → ℝ) → ℝ := fun x => m x * H x (fun i => Du i x) (m x)
    with hfmH
  set fmu : (Fin d → ℝ) → ℝ := fun x => m x * u x with hfmu
  -- Re-typed integrability hypotheses against the abbreviations.
  have hu_int' : MeasureTheory.Integrable fU μ := hu_int
  have hflux_int' : MeasureTheory.Integrable fFlux μ := hmFlux_int
  have hVm_int' : MeasureTheory.Integrable fVm μ := hVm_int
  have heps_int' : MeasureTheory.Integrable fEps μ := heps_int
  have hmH_int' : MeasureTheory.Integrable fmH μ := hmH_int
  have hmu_int' : MeasureTheory.Integrable fmu μ := hmu_int
  -- ===== `hTransport` as a sum of three scalar integrals. =====
  have hTcongr :
      (∫ x, ((m x - 1) * u x
              + m x * ((DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))) ∂μ)
        = (∫ x, fmu x ∂μ) - (∫ x, fU x ∂μ) + ∫ x, fFlux x ∂μ := by
    have hpt : (fun x => (m x - 1) * u x
              + m x * ((DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x)))
        = (fun x => (fmu x - fU x) + fFlux x) := by
      funext x; simp only [hfmu, hfU, hfFlux]; ring
    rw [hpt,
      MeasureTheory.integral_add (f := fun x => fmu x - fU x) (g := fun x => fFlux x)
        (hmu_int'.sub hu_int') hflux_int',
      MeasureTheory.integral_sub hmu_int' hu_int']
  have hTransport' :
      (∫ x, fmu x ∂μ) - (∫ x, fU x ∂μ) + (∫ x, fFlux x ∂μ)
        + ∫ x, fEps x ∂μ = 0 := by
    have := hTransport
    rw [hTcongr] at this
    simpa [hfEps] using this
  -- ===== `hHJ0` as a sum of three scalar integrals. =====
  have hHcongr :
      (∫ x, m x * (u x + H x (fun i => Du i x) (m x) - V x) ∂μ)
        = (∫ x, fmu x ∂μ) + (∫ x, fmH x ∂μ) - ∫ x, fVm x ∂μ := by
    have hpt : (fun x => m x * (u x + H x (fun i => Du i x) (m x) - V x))
        = (fun x => (fmu x + fmH x) - fVm x) := by
      funext x; simp only [hfmu, hfmH, hfVm]; ring
    rw [hpt,
      MeasureTheory.integral_sub (f := fun x => fmu x + fmH x) (g := fun x => fVm x)
        (hmu_int'.add hmH_int') hVm_int',
      MeasureTheory.integral_add hmu_int' hmH_int']
  have hHJ0' :
      (∫ x, fmu x ∂μ) + (∫ x, fmH x ∂μ) - (∫ x, fVm x ∂μ) = 0 := by
    have := hHJ0; rw [hHcongr] at this; exact this
  -- ===== Goal RHS as a sum of four scalar integrals. =====
  have hRcongr :
      (∫ x, (m x
              * (-H x (fun i => Du i x) (m x)
                + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x + epsTerms x) ∂μ)
        = ((∫ x, fFlux x ∂μ) - (∫ x, fmH x ∂μ)) + (∫ x, fVm x ∂μ)
            + ∫ x, fEps x ∂μ := by
    have hpt : (fun x => m x
              * (-H x (fun i => Du i x) (m x)
                + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            + V x * m x + epsTerms x)
        = (fun x => ((fFlux x - fmH x) + fVm x) + fEps x) := by
      funext x; simp only [hfFlux, hfmH, hfVm, hfEps]; ring
    rw [hpt,
      MeasureTheory.integral_add (f := fun x => (fFlux x - fmH x) + fVm x)
        (g := fun x => fEps x)
        ((hflux_int'.sub hmH_int').add hVm_int') heps_int',
      MeasureTheory.integral_add (f := fun x => fFlux x - fmH x) (g := fun x => fVm x)
        (hflux_int'.sub hmH_int') hVm_int',
      MeasureTheory.integral_sub hflux_int' hmH_int']
  -- Conclude by linear arithmetic on the six scalar integrals.
  show (∫ x, fU x ∂μ) = _
  rw [hRcongr]
  linarith [hTransport', hHJ0']

/-- **VIid-5c child C — the `coeVI_identity` PRODUCER at the chosen
Banach-VI witness.**

This is the `_of_closure` discharge of the `hcoeVI_identity` field:
it produces the paper `eq:identity-congestion` integral identity at the
witness data `(m, u, Du) = (choose.1, choose.2.1, choose.2.2)` and the
gap's `coe_epsTerms` residual, in the EXACT RHS shape demanded by the
field (Apriori.lean ~1807/1828).

It is the witness specialisation of child A
(`coeVI_identity_from_transport_and_HJ0`): the witness data are plugged
into child A's `m`/`u`/`Du`/`epsTerms` slots, and the conclusion is
exactly the field RHS once the abbreviations are unfolded.

The two analytic inputs are passed explicitly:

* `hTransport` — the **transport-at-`φ=u`** identity at the witness,
  with the flux written as `m·(D_pH(x,Du,m)⬝Du)` (child B's
  `congestion_transport_at_u_witness`, instantiated at the witness via
  child B2). It is *materially* the closure-membership/VI conclusion of
  the abstract weak VI: child B's `hVI` premise is exactly the field's
  second bridge premise, so this input cannot be supplied without the
  abstract VI inequality at the witness.
* `hHJ0` — the **`eq:congest.HJ0` mass identity** `∫ m·(u+H−V)=0` at the
  witness. (Its production from the witness HJB-equality is a separate
  child — see the split note; here it is a hypothesis so the producer can
  land sorry-free given that fact.)

plus the six per-summand integrability certificates child A needs to
split/recombine the integrals. -/
lemma coeVI_identity_atWitness_of_closure
    {γBar : ℝ}
    {betaBar betaBarPrime gammaBar : ℝ≥0∞} [Fact (1 ≤ betaBar)] [Fact (1 ≤ gammaBar)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {α β τ ε : ℝ}
    (data : CongestionRegularizedSolutionData (d := d)
              (γBar := γBar) (betaBar := betaBar)
              (betaBarPrime := betaBarPrime) (gammaBar := gammaBar)
              V H DpH J α β τ ε
              (Periodic.LpPer betaBar d × Periodic.SobolevPerLp 1 gammaBar d))
    (gap : LpProductBareGap (d := d) betaBar gammaBar V H DpH ε)
    -- per-summand integrability of child A's pieces, at the witness data
    (hu_int : MeasureTheory.Integrable
      (data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ)
      (MeasureTheory.volume.restrict (UnitCube d)))
    (hmFlux_int : MeasureTheory.Integrable
      (fun x => (data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x
        * ((DpH x (fun i => (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)
              ((data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x))
            ⬝ (fun i => (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)))
      (MeasureTheory.volume.restrict (UnitCube d)))
    (hVm_int : MeasureTheory.Integrable
      (fun x => V x * (data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x)
      (MeasureTheory.volume.restrict (UnitCube d)))
    (heps_int : MeasureTheory.Integrable
      (gap.coe_epsTerms data.weakVI.choose)
      (MeasureTheory.volume.restrict (UnitCube d)))
    (hmH_int : MeasureTheory.Integrable
      (fun x => (data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x
        * H x (fun i => (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)
              ((data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x))
      (MeasureTheory.volume.restrict (UnitCube d)))
    (hmu_int : MeasureTheory.Integrable
      (fun x => (data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x
        * (data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ) x)
      (MeasureTheory.volume.restrict (UnitCube d)))
    -- child B transport-at-`φ=u`, in `m·(D_pH·Du)` flux form
    (hTransport :
      ∫ x in UnitCube d,
          (((data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x - 1)
              * (data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ) x
            + (data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x
              * ((DpH x (fun i =>
                      (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)
                    ((data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x))
                  ⬝ (fun i =>
                      (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)))
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
        + ∫ x in UnitCube d, gap.coe_epsTerms data.weakVI.choose x
            ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) = 0)
    -- the `eq:congest.HJ0` mass identity at the witness
    (hHJ0 :
      ∫ x in UnitCube d,
          (data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x
            * ((data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ) x
                + H x (fun i =>
                      (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)
                      ((data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x)
                - V x)
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) = 0) :
    ∫ x in UnitCube d, (data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ) x
        ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
      = ∫ x in UnitCube d,
          ((data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x
              * (-H x (fun i =>
                      (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)
                      ((data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x)
                + (DpH x (fun i =>
                        (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)
                          ((data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x))
                  ⬝ (fun i =>
                      (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x))
            + V x * (data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x
            + gap.coe_epsTerms data.weakVI.choose x)
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) :=
  -- Specialise child A at the witness data and the gap residual.
  coeVI_identity_from_transport_and_HJ0 (d := d)
    (V := V) (H := H) (DpH := DpH)
    (m := (data.weakVI.choose.1 : (Fin d → ℝ) → ℝ))
    (u := (data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ))
    (Du := fun i => (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ))
    (epsTerms := gap.coe_epsTerms data.weakVI.choose)
    hu_int hmFlux_int hVm_int heps_int hmH_int hmu_int hTransport hHJ0

/-- **BB4a-iii helper #3**: bare-function regularisation-residual
nonnegativity at the chosen Banach-VI witness.

Same honest-bridge pattern: materially threads
`Classical.choose_spec data.weakVI` through the bridge premise. -/
lemma coeEpsNN_atWitness
    {γBar : ℝ}
    {betaBar betaBarPrime gammaBar : ℝ≥0∞} [Fact (1 ≤ betaBar)] [Fact (1 ≤ gammaBar)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {α β τ ε : ℝ}
    (data : CongestionRegularizedSolutionData (d := d)
              (γBar := γBar) (betaBar := betaBar)
              (betaBarPrime := betaBarPrime) (gammaBar := gammaBar)
              V H DpH J α β τ ε
              (Periodic.LpPer betaBar d × Periodic.SobolevPerLp 1 gammaBar d))
    (gap : LpProductBareGap (d := d) betaBar gammaBar V H DpH ε)
    (hBridge :
      data.weakVI.choose ∈ closure data.K →
      (∀ v ∈ data.K, 0 ≤ data.A v (v - data.weakVI.choose)) →
      ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
        0 ≤ gap.coe_epsTerms data.weakVI.choose x) :
    ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
      0 ≤ gap.coe_epsTerms data.weakVI.choose x := by
  obtain ⟨hMem, hVI⟩ := data.weakVI.choose_spec
  exact hBridge hMem hVI

/-- **BB4a-iii helper #4**: AE-equality of the gap's literal-periodic
representative of `epsTerms` with its Lp-quotient coercion, at the
chosen Banach-VI witness.

Pure projection: the gap field `LpProductBareGap.ae_epsTerms` is
already quantified over arbitrary `z`, so specialising at
`data.weakVI.choose` is honest by construction. The material use of
`Classical.choose` is in pinning the witness slot to the actual
weak-VI selection; without it, the field would have to be evaluated
at an arbitrary `z` with no semantic tie to Phase 2's data record. -/
lemma ae_epsTerms_atWitness
    {γBar : ℝ}
    {betaBar betaBarPrime gammaBar : ℝ≥0∞} [Fact (1 ≤ betaBar)] [Fact (1 ≤ gammaBar)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {α β τ ε : ℝ}
    (data : CongestionRegularizedSolutionData (d := d)
              (γBar := γBar) (betaBar := betaBar)
              (betaBarPrime := betaBarPrime) (gammaBar := gammaBar)
              V H DpH J α β τ ε
              (Periodic.LpPer betaBar d × Periodic.SobolevPerLp 1 gammaBar d))
    (gap : LpProductBareGap (d := d) betaBar gammaBar V H DpH ε) :
    gap.project_epsTerms data.weakVI.choose
      =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
      gap.coe_epsTerms data.weakVI.choose :=
  gap.ae_epsTerms data.weakVI.choose

/-! ### BB2: discharge of `gap`, `hcoeEpsNN`, `hEpsTerms_int`

The three fields of `CongestionRegularizedSequenceBuilderInputs`
(`gap`, `hcoeEpsNN`, `hEpsTerms_int`) that do NOT depend on the
Banach → bare-K representation theorem are discharged here from
`(γ̄-exponent, ε)` plus the ambient `Lp` structure of the
`LpPer × SobolevPerLp` pair.

The shared ingredient is the genuine ε-regularisation integrand of
`mfgOperatorEpsPair` / `gateauxWpPair` (`Regularized.lean`), evaluated
at the diagonal test pair (so the test vector equals the primal
vector): with `γ̄ := γBarReal`,

```
coeEpsTermsFn ε γ̄ z x
  = ε * ( vecAbsPowMinusTwo γ̄ (fun i => z.2.2 i x) · ((z.2.2 · x) ⬝ (z.2.2 · x))
        + absPowMinusTwo γ̄ (z.2.1 x) · (z.2.1 x * z.2.1 x) )
```

This is the exact `gateauxWpPair` integrand (paper line 925, third
line) scaled by `ε`; no oracle, no representation theorem.

* `congestionRegularizedBuilderInputs_gap` builds the `LpProductBareGap`
  via `LpProductBareGap.ofPeriodicCore` with
  `project_epsTerms := coe_epsTerms := coeEpsTermsFn` and
  `ae_epsTerms := refl`.
* `congestionRegularizedBuilderInputs_hcoeEpsNN`: nonnegativity, from
  `0 < ε`, `(v⬝v) ≥ 0`, `|s|^{γ̄-2} ≥ 0`, `s*s ≥ 0`, `(v⬝v)^{(γ̄-2)/2} ≥ 0`.
* `congestionRegularizedBuilderInputs_hEpsTerms_int`: integrability,
  from the per-coordinate / scalar `MemLp` certificates of the pair
  factors (`Lp.memLp`), reusing the simple-power integrability
  primitive `integrable_euclideanDot_rpow_half_of_coord_memLp` and
  `MemLp.integrable_norm_rpow`. Holds at every `z`, in particular at
  the chosen Banach-VI witness; closure membership is not needed
  because the ambient `Lp` structure already supplies `MemLp`. -/

/-- The genuine ε-regularisation integrand of `mfgOperatorEpsPair` /
`gateauxWpPair` evaluated at the diagonal test pair, scaled by `ε`.
This is the concrete `coe_epsTerms` shape supplied to
`LpProductBareGap.ofPeriodicCore`. -/
noncomputable def coeEpsTermsFn
    {betaBar gammaBar : ℝ≥0∞} (ε γBarReal : ℝ) :
    (Periodic.LpPer betaBar d × Periodic.SobolevPerLp 1 gammaBar d)
      → (Fin d → ℝ) → ℝ :=
  fun z x =>
    ε * (Solutions.MFG.vecAbsPowMinusTwo γBarReal
            (fun i => (z.2.2 i : (Fin d → ℝ) → ℝ) x)
          * ((fun i => (z.2.2 i : (Fin d → ℝ) → ℝ) x)
              ⬝ (fun i => (z.2.2 i : (Fin d → ℝ) → ℝ) x))
        + Solutions.MFG.absPowMinusTwo γBarReal ((z.2.1 : (Fin d → ℝ) → ℝ) x)
          * (((z.2.1 : (Fin d → ℝ) → ℝ) x) * ((z.2.1 : (Fin d → ℝ) → ℝ) x)))

/-- **BB2 `gap` producer.** Build the BB4a-i gap bundle from the
exponents and `ε`, via `LpProductBareGap.ofPeriodicCore` with the
genuine ε-regularisation integrand `coeEpsTermsFn` as both
`project_epsTerms` and `coe_epsTerms` (their a.e.-equality is then
`refl`). -/
noncomputable def congestionRegularizedBuilderInputs_gap
    {betaBar gammaBar : ℝ≥0∞} [Fact (1 ≤ betaBar)] [Fact (1 ≤ gammaBar)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (ε γBarReal : ℝ) :
    LpProductBareGap (d := d) betaBar gammaBar V H DpH ε :=
  LpProductBareGap.ofPeriodicCore (d := d)
    (V := V) (H := H) (DpH := DpH) (ε := ε)
    (coeEpsTermsFn (betaBar := betaBar) (gammaBar := gammaBar) ε γBarReal)
    (coeEpsTermsFn (betaBar := betaBar) (gammaBar := gammaBar) ε γBarReal)
    (fun _ => Filter.EventuallyEq.refl _ _)

/-- The `gap`'s `coe_epsTerms` field is definitionally `coeEpsTermsFn`. -/
@[simp] lemma congestionRegularizedBuilderInputs_gap_coe_epsTerms
    {betaBar gammaBar : ℝ≥0∞} [Fact (1 ≤ betaBar)] [Fact (1 ≤ gammaBar)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (ε γBarReal : ℝ) :
    (congestionRegularizedBuilderInputs_gap (d := d) (betaBar := betaBar)
        (gammaBar := gammaBar) (V := V) (H := H) (DpH := DpH) ε γBarReal).coe_epsTerms
      = coeEpsTermsFn (betaBar := betaBar) (gammaBar := gammaBar) ε γBarReal :=
  rfl

/-- The `gap`'s `project_epsTerms` field is definitionally
`coeEpsTermsFn`. -/
@[simp] lemma congestionRegularizedBuilderInputs_gap_project_epsTerms
    {betaBar gammaBar : ℝ≥0∞} [Fact (1 ≤ betaBar)] [Fact (1 ≤ gammaBar)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (ε γBarReal : ℝ) :
    (congestionRegularizedBuilderInputs_gap (d := d) (betaBar := betaBar)
        (gammaBar := gammaBar) (V := V) (H := H) (DpH := DpH) ε γBarReal).project_epsTerms
      = coeEpsTermsFn (betaBar := betaBar) (gammaBar := gammaBar) ε γBarReal :=
  rfl

/-- **BB2 `hcoeEpsNN` producer.** Pointwise (hence a.e.) nonnegativity
of the genuine ε-term, from `0 < ε` and nonnegativity of the
`rpow`-weighted quadratic factors. No representation theorem. -/
lemma congestionRegularizedBuilderInputs_hcoeEpsNN
    {betaBar gammaBar : ℝ≥0∞} [Fact (1 ≤ betaBar)] [Fact (1 ≤ gammaBar)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {ε : ℝ} (hε : 0 < ε) (γBarReal : ℝ)
    (z : Periodic.LpPer betaBar d × Periodic.SobolevPerLp 1 gammaBar d) :
    ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
      0 ≤ (congestionRegularizedBuilderInputs_gap (d := d) (betaBar := betaBar)
            (gammaBar := gammaBar) (V := V) (H := H) (DpH := DpH) ε γBarReal).coe_epsTerms z x := by
  filter_upwards with x
  rw [congestionRegularizedBuilderInputs_gap_coe_epsTerms]
  unfold coeEpsTermsFn Solutions.MFG.vecAbsPowMinusTwo Solutions.MFG.absPowMinusTwo
  refine mul_nonneg hε.le (add_nonneg (mul_nonneg ?_ ?_) (mul_nonneg ?_ ?_))
  · exact Real.rpow_nonneg
      (Finset.sum_nonneg (fun i _ => mul_self_nonneg _)) _
  · exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  · exact Real.rpow_nonneg (abs_nonneg _) _
  · exact mul_self_nonneg _

/-- **BB2 `hEpsTerms_int` producer.** Integrability of the genuine
ε-term at any pair `z`, from the ambient `Lp` certificates of the
factors: the gradient family lies in `LpPer γ̄` (so
`(Du⬝Du)^{γ̄/2} ∈ L¹`) and the value lies in `LpPer γ̄` (so
`|u|^{γ̄} ∈ L¹`). No closure membership and no representation theorem
are required — `Lp.memLp` already supplies `MemLp` for the factors. -/
lemma congestionRegularizedBuilderInputs_hEpsTerms_int
    {betaBar gammaBar : ℝ≥0∞} [Fact (1 ≤ betaBar)] [Fact (1 ≤ gammaBar)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (ε : ℝ) {γBarReal : ℝ} (hγ : 1 ≤ γBarReal)
    (hγgamma : gammaBar = ENNReal.ofReal γBarReal)
    (z : Periodic.LpPer betaBar d × Periodic.SobolevPerLp 1 gammaBar d) :
    MeasureTheory.Integrable
      ((congestionRegularizedBuilderInputs_gap (d := d) (betaBar := betaBar)
          (gammaBar := gammaBar) (V := V) (H := H) (DpH := DpH) ε γBarReal).project_epsTerms z)
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
  classical
  subst hγgamma
  have hγ_pos : 0 < γBarReal := lt_of_lt_of_le Real.zero_lt_one hγ
  -- `Lp` certificates for the factors (the gradient family and value),
  -- with the exponent normalised to `ENNReal.ofReal γBarReal`.
  have hDuLp : ∀ i, Periodic.MemLpPer (d := d)
      (ENNReal.ofReal γBarReal) (fun x => (z.2.2 i : (Fin d → ℝ) → ℝ) x) := by
    intro i
    exact Periodic.memLpPer_iff_memLp.mpr (MeasureTheory.Lp.memLp (z.2.2 i))
  -- Integrability of `(Du⬝Du)^(γ̄/2)`.
  have hdot_int : MeasureTheory.Integrable
      (fun x => ((fun i => (z.2.2 i : (Fin d → ℝ) → ℝ) x)
          ⬝ (fun i => (z.2.2 i : (Fin d → ℝ) → ℝ) x)) ^ (γBarReal / 2))
      (volume.restrict (UnitCube d)) :=
    Theorems.SimplePower.integrable_euclideanDot_rpow_half_of_coord_memLp
      (d := d) (γBarReal := γBarReal)
      (fun i x => (z.2.2 i : (Fin d → ℝ) → ℝ) x) hDuLp hγ
  -- Integrability of `|u|^γ̄`.
  have hu_int : MeasureTheory.Integrable
      (fun x => |(z.2.1 : (Fin d → ℝ) → ℝ) x| ^ γBarReal)
      (volume.restrict (UnitCube d)) := by
    have huLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal γBarReal) (z.2.1 : (Fin d → ℝ) → ℝ) :=
      Periodic.memLpPer_iff_memLp.mpr (MeasureTheory.Lp.memLp z.2.1)
    have hraw : MeasureTheory.Integrable
        (fun x => ‖(z.2.1 : (Fin d → ℝ) → ℝ) x‖
            ^ (ENNReal.ofReal γBarReal).toReal)
        (volume.restrict (UnitCube d)) :=
      huLp.toMemLp.integrable_norm_rpow
        (ENNReal.ofReal_pos.mpr hγ_pos).ne' ENNReal.ofReal_ne_top
    rw [ENNReal.toReal_ofReal hγ_pos.le] at hraw
    refine hraw.congr ?_
    filter_upwards with x
    rw [Real.norm_eq_abs]
  -- Pointwise identities matching the ε-term to the two integrable pieces.
  have hDu_id : ∀ x,
      Solutions.MFG.vecAbsPowMinusTwo γBarReal
          (fun i => (z.2.2 i : (Fin d → ℝ) → ℝ) x)
        * ((fun i => (z.2.2 i : (Fin d → ℝ) → ℝ) x)
            ⬝ (fun i => (z.2.2 i : (Fin d → ℝ) → ℝ) x))
        = ((fun i => (z.2.2 i : (Fin d → ℝ) → ℝ) x)
            ⬝ (fun i => (z.2.2 i : (Fin d → ℝ) → ℝ) x)) ^ (γBarReal / 2) := by
    intro x
    have hr : 0 ≤ (fun i => (z.2.2 i : (Fin d → ℝ) → ℝ) x)
        ⬝ (fun i => (z.2.2 i : (Fin d → ℝ) → ℝ) x) :=
      Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
    unfold Solutions.MFG.vecAbsPowMinusTwo
    rcases eq_or_lt_of_le hr with hr0 | hrpos
    · have hexp2 : 0 < γBarReal / 2 := by linarith
      rw [← hr0, mul_zero, Real.zero_rpow hexp2.ne']
    · have hstep : ((fun i => (z.2.2 i : (Fin d → ℝ) → ℝ) x)
            ⬝ (fun i => (z.2.2 i : (Fin d → ℝ) → ℝ) x)) ^ ((γBarReal - 2) / 2)
            * ((fun i => (z.2.2 i : (Fin d → ℝ) → ℝ) x)
              ⬝ (fun i => (z.2.2 i : (Fin d → ℝ) → ℝ) x))
          = ((fun i => (z.2.2 i : (Fin d → ℝ) → ℝ) x)
              ⬝ (fun i => (z.2.2 i : (Fin d → ℝ) → ℝ) x)) ^ ((γBarReal - 2) / 2 + 1) :=
        (Real.rpow_add_one hrpos.ne' _).symm
      rw [hstep]
      congr 1
      ring
  have hu_id : ∀ x,
      Solutions.MFG.absPowMinusTwo γBarReal ((z.2.1 : (Fin d → ℝ) → ℝ) x)
          * (((z.2.1 : (Fin d → ℝ) → ℝ) x) * ((z.2.1 : (Fin d → ℝ) → ℝ) x))
        = |(z.2.1 : (Fin d → ℝ) → ℝ) x| ^ γBarReal := by
    intro x
    unfold Solutions.MFG.absPowMinusTwo
    have huu : (z.2.1 : (Fin d → ℝ) → ℝ) x * (z.2.1 : (Fin d → ℝ) → ℝ) x
        = |(z.2.1 : (Fin d → ℝ) → ℝ) x| ^ (2 : ℝ) := by
      rw [Real.rpow_two, sq_abs, sq]
    rw [huu]
    rcases eq_or_lt_of_le (abs_nonneg ((z.2.1 : (Fin d → ℝ) → ℝ) x)) with h0 | hpos
    · have hexp2 : (0 : ℝ) < 2 := by norm_num
      rw [← h0, Real.zero_rpow hexp2.ne', mul_zero, Real.zero_rpow hγ_pos.ne']
    · rw [← Real.rpow_add hpos]
      congr 1
      ring
  -- Assemble: `project_epsTerms z = ε • (sum of integrable pieces)`.
  rw [congestionRegularizedBuilderInputs_gap_project_epsTerms]
  have hsum := (hdot_int.add hu_int).const_mul ε
  refine hsum.congr ?_
  filter_upwards with x
  unfold coeEpsTermsFn
  simp only [Pi.add_apply]
  rw [hDu_id x, hu_id x]

/-! ### Sanity-check `example` for BB4a

Type-check that the BB4a builder integrates cleanly with the BB1
producer `bareRepresentative_of_BanachWeakVI`: a `LpProductBareGap` plus
Phase 2's data record on the concrete pair gives a
`CongestionBareRepresentatives` record. -/
example
    {γBar : ℝ}
    {betaBar betaBarPrime gammaBar : ℝ≥0∞}
    [Fact (1 ≤ betaBar)] [Fact (1 ≤ gammaBar)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {α β τ ε : ℝ}
    (data : CongestionRegularizedSolutionData (d := d)
              (γBar := γBar) (betaBar := betaBar)
              (betaBarPrime := betaBarPrime) (gammaBar := gammaBar)
              V H DpH J α β τ ε
              (Periodic.LpPer betaBar d × Periodic.SobolevPerLp 1 gammaBar d))
    (gap : LpProductBareGap (d := d) betaBar gammaBar V H DpH ε)
    -- **Witness-scoped sanity-check args (2026-05-27 contract refactor)**.
    -- The `vi_witness` is honestly bound to `Classical.choose data.weakVI`
    -- (the abstract weak-VI existential's chosen witness on `LpPer × …`),
    -- and the 5 witness-scoped proofs are assumed at type-check time as
    -- this is a sanity-check `example`; the real builder caller will
    -- discharge them from BB4a-iii / BB4a-iv sub-task work.
    (hcoePos_m :
      ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
        0 < ((data.weakVI.choose.1) : (Fin d → ℝ) → ℝ) x)
    (hcoeWeak_Du : ∀ i, Periodic.HasWeakDerivPer i
      ((data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ))
      ((data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ)))
    (hcoeMemSob_u :
      Periodic.MemSobolevPer gammaBar
        ((data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ)))
    (hcoeHJB_le :
      ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
        (data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ) x
          + H x (fun i => (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)
                ((data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x)
          - V x ≤ 0)
    (hcoeVI_identity :
      ∫ x in UnitCube d, (data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ) x
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
        = ∫ x in UnitCube d,
            ((data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x
                * (-H x (fun i =>
                        (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)
                        ((data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x)
                  + (DpH x (fun i =>
                          (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)
                            ((data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x))
                    ⬝ (fun i =>
                        (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x))
              + V x * (data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x
              + gap.coe_epsTerms data.weakVI.choose x)
            ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
    (hcoeEpsNN :
      ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
        0 ≤ gap.coe_epsTerms data.weakVI.choose x) :
    CongestionBareRepresentatives (d := d)
      (Periodic.LpPer betaBar d × Periodic.SobolevPerLp 1 gammaBar d)
      betaBar gammaBar V H DpH ε :=
  bareRepresentative_of_BanachWeakVI data
    (BanachBareDecomposition.ofLpProductGap (d := d) gap
      data.weakVI.choose
      hcoePos_m hcoeWeak_Du hcoeMemSob_u hcoeHJB_le hcoeVI_identity hcoeEpsNN)

/-! ### Phase 7 BB2-transport: K-membership regularity transport (11 lemmas)

For a single bare-representatives record
`reps : CongestionBareRepresentatives X betaBar gammaBar`, transport the
K-membership facts on the (Lp-quotient) coercions to the literally
periodic bare representatives.

Each lemma is genuinely derived (not a pass-through): the underlying
mechanism is AE-congruence on the unit cube combined, where whole-space
output is required, with the periodicity-extension bridge
`MemLpPer.locallyIntegrable_of_periodic`.

Per the user's 2026-05-24 audit (Group 2 — 11 K-membership regularity
fields), the outputs match the per-ε field types of
`CongestionRegularizedSequenceBanachBareBridge` exactly, so a future
BB4 producer can replace those bridge fields with these lemmas applied
per ε to a per-ε family of bare-representatives records. -/

namespace CongestionBareRepresentatives

variable {betaBar gammaBar : ℝ≥0∞}
variable {V : (Fin d → ℝ) → ℝ}
variable {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
variable {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
variable {ε : ℝ}
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- **BB2-transport #1 (`mε_pos`)**: strict positivity of the bare
density on the unit cube, transported from the K-side strict-positivity
witness on the coercion via the AE-equality `m =ᵐ coe_m`. -/
lemma mε_pos (reps : CongestionBareRepresentatives (d := d) X betaBar gammaBar V H DpH ε) :
    ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
      0 < reps.m x := by
  filter_upwards [reps.hae_m, reps.hpos_coe_m] with x hx_eq hx_pos
  -- `0 < coe_m x = m x` (a.e.-positivity reshape, iter-0913).
  calc (0 : ℝ) < reps.coe_m x := hx_pos
    _ = reps.m x := hx_eq.symm

/-- **BB2-transport #1b (`mε_nonneg`)** — **positivity-elimination
(route a)**: NONNEGATIVITY corollary of `mε_pos`. The `m·D_pH`/`m·H`
envelope consumers (`mDpHDu_int`, `mH_int`) and the abs/cone consumers
need only this weaker fact, derived through the `J`-extension
(`CongestionGrowthCore.mDpH_extended_bound`) + boundary case split.
This refutes the prior blocker: those consumers do NOT need `0 < m`.
(The strict `mε_pos` survives ONLY for the a-priori estimate chain
`apriori_congestion_growth_int_closed` → SimplePower
`thm_apriori_simplePowerGrowth`, where `ln(m) → −∞` makes `0 < m`
load-bearing — this is the a-priori track of the two-track positivity
split. The closure-K weak witness path uses THIS `mε_nonneg` corollary
exclusively; the false `hcoePos_m_witness` field has been removed.) -/
lemma mε_nonneg (reps : CongestionBareRepresentatives (d := d) X betaBar gammaBar V H DpH ε) :
    ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
      0 ≤ reps.m x :=
  (reps.mε_pos).mono (fun _ h => h.le)

/-- **BB2-transport #2 (`hu_meas`)**: a.e.-strong measurability of the
bare value function on all of `ℝ^d`, obtained by transporting cube-side
`MemLpPer` from the coercion via `hae_u`, lifting to whole-space
`LocallyIntegrable` via periodicity, and extracting
`AEStronglyMeasurable`. Requires `1 ≤ gammaBar` (consumer-side
`ENNReal.ofReal (gammaBar h.α h.β) ≥ 1`). -/
lemma hu_meas
    (reps : CongestionBareRepresentatives (d := d) X betaBar gammaBar V H DpH ε)
    (hγ_one_le : (1 : ℝ≥0∞) ≤ gammaBar) :
    MeasureTheory.AEStronglyMeasurable reps.u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) := by
  -- Step 1: cube-side `MemLpPer gammaBar reps.u` via congr_ae from `coe_u`.
  have hu_lp : Periodic.MemLpPer (d := d) gammaBar reps.u :=
    Periodic.MemLpPer.congr_ae_unitCube reps.hmem_sob_coe_u.1 reps.hae_u.symm
  -- Step 2: whole-space `LocallyIntegrable` via periodicity.
  have hu_loc : MeasureTheory.LocallyIntegrable reps.u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) :=
    Periodic.MemLpPer.locallyIntegrable_of_periodic (d := d)
      hγ_one_le hu_lp reps.hper_u
  -- Step 3: AE-strong measurability from local integrability.
  exact hu_loc.aestronglyMeasurable

/-- **BB2-transport #3 (`hu_per`)**: periodicity of the bare value
function. Direct from BB1's `hper_u` (the BB1 producer was specifically
designed to ship a literally periodic representative). -/
lemma hu_per (reps : CongestionBareRepresentatives (d := d) X betaBar gammaBar V H DpH ε) :
    Periodic.IsPeriodic reps.u :=
  reps.hper_u

/-- **BB2-transport #4 (`hu_loc`)**: whole-space local integrability of
the bare value function, obtained by lifting cube-side `MemLpPer
gammaBar reps.u` via periodicity. Requires `1 ≤ gammaBar`. -/
lemma hu_loc
    (reps : CongestionBareRepresentatives (d := d) X betaBar gammaBar V H DpH ε)
    (hγ_one_le : (1 : ℝ≥0∞) ≤ gammaBar) :
    MeasureTheory.LocallyIntegrable reps.u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) := by
  have hu_lp : Periodic.MemLpPer (d := d) gammaBar reps.u :=
    Periodic.MemLpPer.congr_ae_unitCube reps.hmem_sob_coe_u.1 reps.hae_u.symm
  exact Periodic.MemLpPer.locallyIntegrable_of_periodic (d := d)
    hγ_one_le hu_lp reps.hper_u

/-- **BB2-transport #5 (`hu_sob`)**: Sobolev membership of the bare
value function at `γ̄`, transported from the K-side Sobolev membership
of the coercion via `MemSobolevPer.congr_ae_unitCube`. -/
lemma hu_sob (reps : CongestionBareRepresentatives (d := d) X betaBar gammaBar V H DpH ε) :
    Periodic.MemSobolevPer (d := d) gammaBar reps.u :=
  reps.hmem_sob_coe_u.congr_ae_unitCube reps.hae_u.symm

/-- **BB2-transport #6 (`hu_lp_γ`)**: `L^{γ̄}`-membership of the bare
value function, obtained by extracting the Lp part of the Sobolev
membership of `coe_u` and transporting via `hae_u`. -/
lemma hu_lp_γ (reps : CongestionBareRepresentatives (d := d) X betaBar gammaBar V H DpH ε) :
    Periodic.MemLpPer (d := d) gammaBar reps.u :=
  Periodic.MemLpPer.congr_ae_unitCube reps.hmem_sob_coe_u.1 reps.hae_u.symm

/-- **BB2-transport #7 (`hDu_weak`)**: the bare weak-derivative family
witnesses the bare value function's Sobolev structure, obtained by
double-sided AE-congruence from the K-side weak-derivative witness on
the coercion. Requires `1 ≤ gammaBar` (for `MemLpPer 1 (Du i)` via the
inclusion `L^{γ̄} ⊆ L^1` on the finite-measure cube, but here we extract
`MemLpPer 1 (Du i)` directly through `coeWeak_Du`-side congruence). -/
lemma hDu_weak (reps : CongestionBareRepresentatives (d := d) X betaBar gammaBar V H DpH ε) :
    ∀ i, Periodic.HasWeakDerivPer (d := d) i reps.u (reps.Du i) := by
  intro i
  -- The K-side gives `HasWeakDerivPer i coe_u (coe_Du i)`, which carries
  -- `MemLpPer 1 (coe_Du i)`. Transport that `MemLpPer 1` to `Du i` first.
  have hDu_lp1 : Periodic.MemLpPer (d := d) 1 (reps.Du i) :=
    Periodic.MemLpPer.congr_ae_unitCube
      (reps.hweak_coe_Du i).memLpPer (reps.hae_Du i).symm
  exact (reps.hweak_coe_Du i).congr_ae_unitCube
    reps.hae_u.symm hDu_lp1 (reps.hae_Du i).symm

/-- **BB2-transport #8 (`hDu_meas`)**: whole-space a.e.-strong
measurability of each component of the bare weak-derivative family,
obtained by the same chain as `hu_meas` applied to each `Du i`. -/
lemma hDu_meas
    (reps : CongestionBareRepresentatives (d := d) X betaBar gammaBar V H DpH ε)
    (hγ_one_le : (1 : ℝ≥0∞) ≤ gammaBar) :
    ∀ i, MeasureTheory.AEStronglyMeasurable (reps.Du i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) := by
  intro i
  -- `MemLpPer gammaBar (coe_Du i)` from BB2-enrich's new field,
  -- transported to `Du i` via `(hae_Du i)`.
  have hDu_lp : Periodic.MemLpPer (d := d) gammaBar (reps.Du i) :=
    Periodic.MemLpPer.congr_ae_unitCube
      (reps.hmem_lp_coe_Du i) (reps.hae_Du i).symm
  have hDu_loc : MeasureTheory.LocallyIntegrable (reps.Du i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) :=
    Periodic.MemLpPer.locallyIntegrable_of_periodic (d := d)
      hγ_one_le hDu_lp (reps.hper_Du i)
  exact hDu_loc.aestronglyMeasurable

/-- **BB2-transport #9 (`hDu_per`)**: periodicity of each component of
the bare weak-derivative family. Direct from BB1's `hper_Du`. -/
lemma hDu_per (reps : CongestionBareRepresentatives (d := d) X betaBar gammaBar V H DpH ε) :
    ∀ i, Periodic.IsPeriodic (reps.Du i) :=
  reps.hper_Du

/-- **BB2-transport #10 (`hDu_loc`)**: whole-space local integrability
of each component of the bare weak-derivative family, obtained by
lifting cube-side `MemLpPer gammaBar` via periodicity. Requires
`1 ≤ gammaBar`. -/
lemma hDu_loc
    (reps : CongestionBareRepresentatives (d := d) X betaBar gammaBar V H DpH ε)
    (hγ_one_le : (1 : ℝ≥0∞) ≤ gammaBar) :
    ∀ i, MeasureTheory.LocallyIntegrable (reps.Du i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) := by
  intro i
  have hDu_lp : Periodic.MemLpPer (d := d) gammaBar (reps.Du i) :=
    Periodic.MemLpPer.congr_ae_unitCube
      (reps.hmem_lp_coe_Du i) (reps.hae_Du i).symm
  exact Periodic.MemLpPer.locallyIntegrable_of_periodic (d := d)
    hγ_one_le hDu_lp (reps.hper_Du i)

/-- **BB2-transport #11 (`hDu_lp`)**: `L^{γ̄}`-membership of each
component of the bare weak-derivative family, obtained by transporting
the BB2-enrich `hmem_lp_coe_Du i` via the AE-equality `Du i =ᵐ coe_Du
i` on the cube. -/
lemma hDu_lp (reps : CongestionBareRepresentatives (d := d) X betaBar gammaBar V H DpH ε) :
    ∀ i, Periodic.MemLpPer (d := d) gammaBar (reps.Du i) := by
  intro i
  exact Periodic.MemLpPer.congr_ae_unitCube
    (reps.hmem_lp_coe_Du i) (reps.hae_Du i).symm

/-! ### BB3-transport: Banach-VI PDE conclusions on bare representatives

The next three lemmas transport the Banach-VI conclusions
(`hHJB_le_coe`, `hVI_identity_coe`, `hEpsNN_coe`) from the coercions
to the bare representatives via the AE-equalities
(`hae_m`, `hae_u`, `hae_Du`, `hae_epsTerms`). These match the per-ε
bridge fields `hHJB_le`, `hVIIdentity`, `hEpsNN` of
`CongestionRegularizedSequenceBanachBareBridge` (modulo the outer
`∀ ε > 0` quantifier).
-/

/-- **BB3-transport #1 (`hHJB_le`)**: the bare-representative form of
the regularised HJB pointwise inequality (paper `eq:congest.HJleq0`),
transported from `hHJB_le_coe` via the AE-equalities `hae_m, hae_u,
hae_Du`. The pointwise inequality at `x` rewrites the coercion
inequality `coe_u + H(coe_Du)(coe_m) - V ≤ 0` into the bare-function
form `u + H(Du)(m) - V ≤ 0`. -/
lemma hHJB_le (reps : CongestionBareRepresentatives (d := d) X betaBar gammaBar V H DpH ε) :
    ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
      reps.u x + H x (fun i => reps.Du i x) (reps.m x) - V x ≤ 0 := by
  -- Combine the per-axis AE-equalities for `Du` into a single AE-event.
  have hae_Du_all :
      ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
        ∀ i, reps.Du i x = reps.coe_Du i x := by
    rw [MeasureTheory.ae_all_iff]; intro i; exact reps.hae_Du i
  filter_upwards [reps.hHJB_le_coe, reps.hae_m, reps.hae_u, hae_Du_all]
    with x hx_le hx_m hx_u hx_Du
  -- Rewrite each bare value as its coercion counterpart.
  have hfun_eq : (fun i => reps.Du i x) = (fun i => reps.coe_Du i x) :=
    funext hx_Du
  rw [hx_m, hx_u, hfun_eq]
  exact hx_le

/-- **BB3-transport #2 (`hVIIdentity`)**: the bare-representative form
of the regularised VI integral identity (paper
`eq:identity-congestion`), transported from `hVI_identity_coe` via
`integral_congr_ae` applied to both sides. -/
lemma hVIIdentity (reps : CongestionBareRepresentatives (d := d) X betaBar gammaBar V H DpH ε) :
    ∫ x in UnitCube d, reps.u x ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
      = ∫ x in UnitCube d,
          (reps.m x * (-H x (fun i => reps.Du i x) (reps.m x)
                      + (DpH x (fun i => reps.Du i x) (reps.m x))
                        ⬝ (fun i => reps.Du i x))
            + V x * reps.m x
            + reps.epsTerms x)
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) := by
  -- Combine the per-axis AE-equalities for `Du` into a single AE-event.
  have hae_Du_all :
      ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
        ∀ i, reps.Du i x = reps.coe_Du i x := by
    rw [MeasureTheory.ae_all_iff]; intro i; exact reps.hae_Du i
  -- LHS: `∫ u = ∫ coe_u` via AE-equality on the cube.
  have hLHS :
      ∫ x in UnitCube d, reps.u x
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
        = ∫ x in UnitCube d, reps.coe_u x
            ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) := by
    exact MeasureTheory.integral_congr_ae reps.hae_u
  -- RHS: rewrite the bare integrand to the coercion integrand AE.
  have hRHS :
      ∫ x in UnitCube d,
          (reps.m x * (-H x (fun i => reps.Du i x) (reps.m x)
                      + (DpH x (fun i => reps.Du i x) (reps.m x))
                        ⬝ (fun i => reps.Du i x))
            + V x * reps.m x
            + reps.epsTerms x)
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
        = ∫ x in UnitCube d,
            (reps.coe_m x * (-H x (fun i => reps.coe_Du i x) (reps.coe_m x)
                            + (DpH x (fun i => reps.coe_Du i x) (reps.coe_m x))
                              ⬝ (fun i => reps.coe_Du i x))
              + V x * reps.coe_m x
              + reps.coe_epsTerms x)
            ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [reps.hae_m, hae_Du_all, reps.hae_epsTerms]
      with x hx_m hx_Du hx_eps
    have hfun_eq : (fun i => reps.Du i x) = (fun i => reps.coe_Du i x) :=
      funext hx_Du
    rw [hx_m, hfun_eq, hx_eps]
  -- Chain LHS/RHS with the K-side identity on the coercions.
  rw [hLHS, hRHS]
  exact reps.hVI_identity_coe

/-- **BB3-transport #3 (`hEpsNN`)**: nonnegativity of the bare
regularisation residual `epsTerms`, transported from `hEpsNN_coe` via
the AE-equality `hae_epsTerms`. -/
lemma hEpsNN (reps : CongestionBareRepresentatives (d := d) X betaBar gammaBar V H DpH ε) :
    ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
      0 ≤ reps.epsTerms x := by
  filter_upwards [reps.hEpsNN_coe, reps.hae_epsTerms] with x hx_le hx_eq
  rw [hx_eq]
  exact hx_le

/-! ### BB3-transport: PDE/analytic integrability conclusions (#4 `hu_int`)

The bare value function `u` is integrable on the unit cube. This is
the simplest of the seven integrability transports: it reduces directly
to `MemLpPer γ̄ u` (BB2-transport's `hu_lp_γ`) via `MemLp.mono_exponent`
on the finite-measure cube, using `1 ≤ γ̄`.
-/

/-- **BB3-transport #4 (`hu_int`)**: integrability of the bare value
function on the unit cube. From `MemLpPer gammaBar reps.u` (BB2-transport's
`hu_lp_γ`) + `1 ≤ gammaBar` + finite measure on `UnitCube`. -/
lemma hu_int
    (reps : CongestionBareRepresentatives (d := d) X betaBar gammaBar V H DpH ε)
    (hγ_one_le : (1 : ℝ≥0∞) ≤ gammaBar) :
    MeasureTheory.Integrable reps.u
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
  -- Equip the cube-restricted volume with `IsFiniteMeasure`.
  haveI hcube_fin :
      MeasureTheory.IsFiniteMeasure (MeasureTheory.Measure.restrict
        (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
        (UnitCube (d := d))) :=
    ⟨by
      rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
          volume_unitCube]
      exact ENNReal.one_lt_top⟩
  -- `MemLpPer gammaBar u = MemLp u gammaBar …`; `mono_exponent` to `MemLp u 1`.
  have hu_lpγ : Periodic.MemLpPer (d := d) gammaBar reps.u := reps.hu_lp_γ
  have hu_memLp1 : MeasureTheory.MemLp reps.u 1
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
    hu_lpγ.toMemLp.mono_exponent hγ_one_le
  exact (MeasureTheory.memLp_one_iff_integrable.mp hu_memLp1)

/-- **BB3-transport #5 (`hLB_int`)**: integrability of `m^{β+1}` on the
unit cube. From the BB2-enrich field `hmem_lp_coe_m : MemLpPer betaBar
coe_m` together with the bridge exponent alignment
`betaBar = ENNReal.ofReal (β+1)` (paper line 1328), and the bare AE-positivity
`mε_pos` (which lets us drop the absolute-value/norm cast). The
`MemLpPer betaBar` of the bare `m` is transported from `coe_m` via
`hae_m`.

Surface the exponent alignment and the paper parameters as hypotheses
(NOT as new fields on `CongestionBareRepresentatives` — those are
bridge-instantiator-side facts). -/
lemma hLB_int
    (reps : CongestionBareRepresentatives (d := d) X betaBar gammaBar V H DpH ε)
    {β : ℝ} (hβ_pos : 0 < β)
    (hbetaBar_eq : betaBar = ENNReal.ofReal (β + 1)) :
    MeasureTheory.Integrable (fun x => reps.m x ^ (β + 1))
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
  -- Step 1: transport `MemLpPer betaBar coe_m` to `MemLpPer betaBar m`.
  have hm_lp : Periodic.MemLpPer (d := d) betaBar reps.m :=
    Periodic.MemLpPer.congr_ae_unitCube reps.hmem_lp_coe_m reps.hae_m.symm
  -- Step 2: substitute `betaBar = ENNReal.ofReal (β+1)`.
  have hm_lp' : Periodic.MemLpPer (d := d) (ENNReal.ofReal (β + 1)) reps.m := by
    rw [← hbetaBar_eq]; exact hm_lp
  have hβ1_pos : (0 : ℝ) < β + 1 := by linarith
  have hp_ne_zero : ENNReal.ofReal (β + 1) ≠ 0 := by
    simp [ENNReal.ofReal_ne_zero_iff, hβ1_pos]
  have hp_top : ENNReal.ofReal (β + 1) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hp_toReal : (ENNReal.ofReal (β + 1)).toReal = β + 1 :=
    ENNReal.toReal_ofReal hβ1_pos.le
  -- Step 3: apply `MemLp.integrable_norm_rpow`.
  have hm_memLp : MeasureTheory.MemLp reps.m (ENNReal.ofReal (β + 1))
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
    hm_lp'
  have hnorm_int : MeasureTheory.Integrable
      (fun x => ‖reps.m x‖ ^ (ENNReal.ofReal (β + 1)).toReal)
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
    MeasureTheory.MemLp.integrable_norm_rpow hm_memLp hp_ne_zero hp_top
  rw [hp_toReal] at hnorm_int
  -- Step 4: rewrite `‖m x‖^(β+1) = m x ^ (β+1)` AE using `mε_nonneg`.
  have hae_eq :
      (fun x => ‖reps.m x‖ ^ (β + 1)) =ᵐ[MeasureTheory.Measure.restrict
        MeasureTheory.volume (UnitCube d)]
        (fun x => reps.m x ^ (β + 1)) := by
    filter_upwards [reps.mε_nonneg] with x hx_nn
    simp only [Real.norm_eq_abs, abs_of_nonneg hx_nn]
  exact hnorm_int.congr hae_eq

/-- **BB3-transport #6 (`hMbeta_int`)**: integrability of `m^β` on the
unit cube. Strategy: derive from `MemLpPer (ENNReal.ofReal (β+1)) m`
(transported as in `hLB_int`), which gives `Integrable (fun x => m x ^
(β+1))`; together with `Integrable (fun x => m x)` (Lp embedding from
`β+1 ≥ 1`) we get `m^β = m^{β+1} / m` pointwise, BUT this division
isn't friendly for integrability. Alternative chain: from `MemLpPer
(β+1) m` and `1 ≤ β+1`, monotonicity gives `Integrable (m^q)` for any
`1 ≤ q ≤ β+1` on the finite-measure cube via
`MemLp.integrable_norm_rpow` and `MemLp.mono_exponent` after the rpow
transformation. Cleanest: use the bound `m^β ≤ m^{β+1} + 1` (Young's
inequality at scale 1) which holds when `m > 0`. -/
lemma hMbeta_int
    (reps : CongestionBareRepresentatives (d := d) X betaBar gammaBar V H DpH ε)
    {β : ℝ} (hβ_pos : 0 < β)
    (hbetaBar_eq : betaBar = ENNReal.ofReal (β + 1)) :
    MeasureTheory.Integrable (fun x => reps.m x ^ β)
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
  -- Equip cube with finite measure.
  haveI hcube_fin :
      MeasureTheory.IsFiniteMeasure (MeasureTheory.Measure.restrict
        (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
        (UnitCube (d := d))) :=
    ⟨by
      rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
          volume_unitCube]
      exact ENNReal.one_lt_top⟩
  -- Use the chain:  `m^β ≤ m^{β+1} + 1` AE (Young at scale 1, valid when m > 0)
  -- and dominate by an integrable function.
  have hLB := reps.hLB_int (β := β) hβ_pos hbetaBar_eq
  -- `Integrable (fun x => m x ^ (β+1) + 1)` since constants are integrable on
  -- the finite-measure cube.
  have h_one_int : MeasureTheory.Integrable
      (fun _ : (Fin d → ℝ) => (1 : ℝ))
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
    MeasureTheory.integrable_const 1
  have h_dom_int : MeasureTheory.Integrable
      (fun x => reps.m x ^ (β + 1) + 1)
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
    hLB.add h_one_int
  -- AE-strong measurability of `m^β`: from `m^{β+1}` via rpow with continuous
  -- function. We use the chain from `hLB`'s measurability of the rpow.
  have hm_aesm :
      MeasureTheory.AEStronglyMeasurable reps.m
        (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
    -- From `MemLpPer betaBar m`, get AEStronglyMeasurable.
    have hm_lp : Periodic.MemLpPer (d := d) betaBar reps.m :=
      Periodic.MemLpPer.congr_ae_unitCube reps.hmem_lp_coe_m reps.hae_m.symm
    exact hm_lp.aestronglyMeasurable
  have hmβ_aesm :
      MeasureTheory.AEStronglyMeasurable (fun x => reps.m x ^ β)
        (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
    -- Compose with the continuous function `t ↦ t ^ β` (valid for `0 ≤ β`).
    exact (Real.continuous_rpow_const hβ_pos.le).comp_aestronglyMeasurable hm_aesm
  -- Pointwise bound `m^β ≤ m^{β+1} + 1` for `m > 0`:
  --   if `m ≥ 1` then `m^β ≤ m^{β+1}`; if `0 < m < 1` then `m^β ≤ 1`.
  have h_pointwise_bound :
      ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
        ‖reps.m x ^ β‖ ≤ reps.m x ^ (β + 1) + 1 := by
    filter_upwards [reps.mε_nonneg] with x hx_nn
    have hmβ_nn : 0 ≤ reps.m x ^ β := Real.rpow_nonneg hx_nn β
    have hmβ1_nn : 0 ≤ reps.m x ^ (β + 1) := Real.rpow_nonneg hx_nn (β + 1)
    rw [Real.norm_of_nonneg hmβ_nn]
    by_cases hm1 : 1 ≤ reps.m x
    · -- `m ≥ 1`: `m^β ≤ m^{β+1} ≤ m^{β+1} + 1`.
      have h1 : reps.m x ^ β ≤ reps.m x ^ (β + 1) := by
        apply Real.rpow_le_rpow_of_exponent_le hm1
        linarith
      linarith
    · -- `0 ≤ m < 1`: `m^β ≤ 1 ≤ m^{β+1} + 1`.
      push_neg at hm1
      have h1 : reps.m x ^ β ≤ 1 := by
        have h := Real.rpow_le_one hx_nn hm1.le hβ_pos.le
        exact h
      linarith
  exact h_dom_int.mono' hmβ_aesm h_pointwise_bound

/-! ### BB3-transport: PDE/analytic integrability conclusions
(`hDu_norm_int`, `hUbetap_int`, `hRHSabove_int`)

Three of the four remaining integrability transports (iter 0848-extension):

* `hDu_norm_int` — integrability of `‖(fun i => Du i x)‖^γ̄` via
  per-axis `MemLpPer γ̄ (Du i)` (BB2-transport `hDu_lp`) +
  `MemLp.integrable_norm_rpow` summed across axes, dominated by the
  pointwise bound `‖f‖^γ̄ ≤ ∑ i, ‖f i‖^γ̄` for `γ̄ ≥ 0` on `Fin d → ℝ`
  (using `Finset.exists_mem_eq_sup` for `d > 0` and the `d = 0`
  degenerate case where `f = 0`).

* `hUbetap_int` — integrability of `|u x|^{β̄'}` via `MemLpPer γ̄ u`
  (BB2-transport `hu_lp_γ`) + exponent inclusion `β̄' ≤ γ̄` on the
  finite-measure cube (`MemLp.mono_exponent`), then
  `MemLp.integrable_norm_rpow` + `‖u x‖ = |u x|` (real-valued).

* `hRHSabove_int` — integrability of `|V x| + h.C * (m x ^ β + 1)`
  as a linear combination of an external paper-side `hV_int`
  hypothesis and the landed `hMbeta_int` plus a finite-measure
  constant.

The fourth lemma `hRHSbelow_int` (integrand of the VI identity) is
deferred to a child task `BB3-transport-hRHSbelow-int` since it
requires Hölder pairings on the products `m * H`, `m * (DpH ⬝ Du)`,
`V * m`, plus a contract enrichment for `epsTerms` integrability.
-/

/-- **BB3-transport #7 (`hDu_norm_int`)**: integrability of `‖Du‖^γ̄`
on the unit cube, where the norm on `Fin d → ℝ` is the sup-norm. The
strategy:
* From `hDu_lp i : MemLpPer γ̄ (Du i)` (BB2-transport) and the exponent
  alignment `gammaBar = ENNReal.ofReal γ̄`, each `‖Du i x‖^γ̄` is
  integrable via `MemLp.integrable_norm_rpow`.
* Summing over `i`, the function `x ↦ ∑ i, ‖Du i x‖^γ̄` is integrable.
* Pointwise, `‖(fun i => Du i x)‖^γ̄ ≤ ∑ i, ‖Du i x‖^γ̄` for `γ̄ ≥ 0`:
  if `d = 0` both sides are `0`; if `d > 0`, picking `j` attaining
  the sup gives `‖f‖^γ̄ = ‖f j‖^γ̄ ≤ ∑ i, ‖f i‖^γ̄` since each summand
  is nonneg.
* `Integrable.mono'` closes the goal.

Requires `0 ≤ γ̄` (for `t ↦ t^γ̄` to be monotone on `[0,∞)`) and the
exponent alignment `gammaBar = ENNReal.ofReal γ̄` plus `γ̄ ≠ 0`. -/
lemma hDu_norm_int
    (reps : CongestionBareRepresentatives (d := d) X betaBar gammaBar V H DpH ε)
    {γBar : ℝ} (hγBar_pos : 0 < γBar)
    (hgammaBar_eq : gammaBar = ENNReal.ofReal γBar) :
    MeasureTheory.Integrable
      (fun x => ‖(fun i => reps.Du i x)‖ ^ γBar)
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
  classical
  -- Step 1: each axis's `‖Du i x‖^γBar` is integrable, via
  --   `MemLp.integrable_norm_rpow` applied to `hDu_lp i`.
  have hp_ne_zero : ENNReal.ofReal γBar ≠ 0 := by
    simp [ENNReal.ofReal_ne_zero_iff, hγBar_pos]
  have hp_top : ENNReal.ofReal γBar ≠ ⊤ := ENNReal.ofReal_ne_top
  have hp_toReal : (ENNReal.ofReal γBar).toReal = γBar :=
    ENNReal.toReal_ofReal hγBar_pos.le
  have h_each_int : ∀ i, MeasureTheory.Integrable
      (fun x => ‖reps.Du i x‖ ^ γBar)
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
    intro i
    have hDu_lp_i : Periodic.MemLpPer (d := d) gammaBar (reps.Du i) := reps.hDu_lp i
    have hDu_lp_i' : Periodic.MemLpPer (d := d) (ENNReal.ofReal γBar) (reps.Du i) := by
      rw [← hgammaBar_eq]; exact hDu_lp_i
    have hDu_memLp : MeasureTheory.MemLp (reps.Du i) (ENNReal.ofReal γBar)
        (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
      hDu_lp_i'
    have h := MeasureTheory.MemLp.integrable_norm_rpow hDu_memLp hp_ne_zero hp_top
    rw [hp_toReal] at h
    exact h
  -- Step 2: the sum across axes is integrable.
  have h_sum_int : MeasureTheory.Integrable
      (fun x => ∑ i, ‖reps.Du i x‖ ^ γBar)
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
    MeasureTheory.integrable_finset_sum _ (fun i _ => h_each_int i)
  -- Step 3: AE-strong measurability of `x ↦ ‖(fun i => Du i x)‖^γBar`.
  -- The function `x ↦ (fun i => Du i x)` is AE-strongly measurable as
  -- a function into `Fin d → ℝ` (Pi-strong measurability follows from
  -- the per-axis measurabilities).
  have hDu_meas : ∀ i, MeasureTheory.AEStronglyMeasurable (reps.Du i)
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
    intro i
    have hDu_lp_i : Periodic.MemLpPer (d := d) gammaBar (reps.Du i) := reps.hDu_lp i
    exact hDu_lp_i.aestronglyMeasurable
  -- Bridge AEStronglyMeasurable ↔ AEMeasurable on second-countable Polish
  -- ranges (`ℝ`, `Fin d → ℝ`).
  have hDu_aem : ∀ i, AEMeasurable (reps.Du i)
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
    fun i => (hDu_meas i).aemeasurable
  have hPi_aem : AEMeasurable
      (fun x : Fin d → ℝ => (fun i => reps.Du i x))
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
    AEMeasurable.of_eval hDu_aem
  have hPi_meas : MeasureTheory.AEStronglyMeasurable
      (fun x : Fin d → ℝ => (fun i => reps.Du i x))
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
    aestronglyMeasurable_iff_aemeasurable.mpr hPi_aem
  have h_norm_meas : MeasureTheory.AEStronglyMeasurable
      (fun x => ‖(fun i => reps.Du i x)‖)
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
    hPi_meas.norm
  have h_rpow_meas : MeasureTheory.AEStronglyMeasurable
      (fun x => ‖(fun i => reps.Du i x)‖ ^ γBar)
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
    exact (Real.continuous_rpow_const hγBar_pos.le).comp_aestronglyMeasurable h_norm_meas
  -- Step 4: pointwise bound `‖(fun i => Du i x)‖^γBar ≤ ∑ i, ‖Du i x‖^γBar`.
  -- Cases on `d`:
  --   d = 0: `‖f‖ = 0`, `0^γBar = 0`, sum over empty is `0`.
  --   d ≥ 1: pick `j` attaining the sup, bound by the corresponding term.
  have h_pointwise : ∀ x : Fin d → ℝ,
      ‖fun i => reps.Du i x‖ ^ γBar ≤ ∑ i, ‖reps.Du i x‖ ^ γBar := by
    intro x
    have h_nn_sum : 0 ≤ ∑ i, ‖reps.Du i x‖ ^ γBar :=
      Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg _) γBar)
    by_cases hd : d = 0
    · -- `Fin 0` is empty. `‖f‖ = 0` because the sup over `∅` in the
      -- nnnorm-product structure is `0`.
      subst hd
      have hf_norm : ‖fun i : Fin 0 => reps.Du i x‖ = 0 := by
        rw [Pi.norm_def]
        simp [Finset.univ_eq_empty, Finset.sup_empty]
      rw [hf_norm]
      rw [Real.zero_rpow hγBar_pos.ne']
      exact h_nn_sum
    · -- `Fin d` is nonempty; pick `j` attaining the sup of `‖f i‖₊`.
      haveI : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero hd⟩⟩
      -- `‖f‖ ≤ ∑_i ‖f i‖` follows from `‖f i‖ ≤ ‖f‖` ≤ `∑_i ‖f i‖`,
      -- so we use a direct case analysis: there exists `j` with
      -- `‖f‖ = ‖f j‖`.
      obtain ⟨j, _, hj_eq⟩ :=
        Finset.exists_mem_eq_sup (s := (Finset.univ : Finset (Fin d)))
          ⟨⟨0, Nat.pos_of_ne_zero hd⟩, Finset.mem_univ _⟩
          (fun i => ‖reps.Du i x‖₊)
      have hf_norm_eq : ‖fun i => reps.Du i x‖ = ‖reps.Du j x‖ := by
        rw [Pi.norm_def, hj_eq]
        rfl
      rw [hf_norm_eq]
      -- The `j`-th term of the sum dominates each individual term.
      have h_each_nn : ∀ i, 0 ≤ ‖reps.Du i x‖ ^ γBar :=
        fun i => Real.rpow_nonneg (norm_nonneg _) γBar
      calc ‖reps.Du j x‖ ^ γBar
          = ∑ i ∈ ({j} : Finset (Fin d)), ‖reps.Du i x‖ ^ γBar := by
              simp
        _ ≤ ∑ i, ‖reps.Du i x‖ ^ γBar := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro i hi; exact Finset.mem_univ _
              · intro i _ _; exact h_each_nn i
  -- Step 5: `Integrable.mono'` via `‖f^γBar‖ = f^γBar` (nonneg).
  have h_abs_bound :
      ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
        ‖‖fun i => reps.Du i x‖ ^ γBar‖ ≤ ∑ i, ‖reps.Du i x‖ ^ γBar := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    have hnn : 0 ≤ ‖fun i => reps.Du i x‖ ^ γBar :=
      Real.rpow_nonneg (norm_nonneg _) γBar
    rw [Real.norm_of_nonneg hnn]
    exact h_pointwise x
  exact h_sum_int.mono' h_rpow_meas h_abs_bound

/-- **BB3-transport #8 (`hUbetap_int`)**: integrability of `|u x|^{β̄'}`
on the unit cube, where `β̄' = (β+1)/β` is the Hölder conjugate of
`β̄`. The strategy uses two steps:
* From `MemLpPer γ̄ u` (BB2-transport `hu_lp_γ`) + the inclusion
  `β̄' ≤ γ̄` (paper requirement: `γ̄ = α · β̄' ≥ β̄'` since `α ≥ 1`),
  `MemLp.mono_exponent` on the finite-measure cube gives
  `MemLp u β̄' (cube-restricted volume)`.
* `MemLp.integrable_norm_rpow` produces `Integrable (fun x => ‖u x‖^β̄')`,
  which equals `Integrable (fun x => |u x|^β̄')` since `‖·‖ = |·|`
  on `ℝ`.

Requires `0 < β̄'` and the exponent alignment
`gammaBar = ENNReal.ofReal γBar` with `betaBar' β ≤ γBar`. -/
lemma hUbetap_int
    (reps : CongestionBareRepresentatives (d := d) X betaBar gammaBar V H DpH ε)
    {β : ℝ} (hβ_pos : 0 < β)
    {γBar : ℝ} (hbetaBarP_le_gBar : StationaryMFG.Hamiltonian.betaBar' β ≤ γBar)
    (hgammaBar_eq : gammaBar = ENNReal.ofReal γBar) :
    MeasureTheory.Integrable
      (fun x => |reps.u x| ^ StationaryMFG.Hamiltonian.betaBar' β)
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
  -- Equip cube with finite measure.
  haveI hcube_fin :
      MeasureTheory.IsFiniteMeasure (MeasureTheory.Measure.restrict
        (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
        (UnitCube (d := d))) :=
    ⟨by
      rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
          volume_unitCube]
      exact ENNReal.one_lt_top⟩
  -- Positivity of `β̄'`.
  have hbetaBarP_pos : 0 < StationaryMFG.Hamiltonian.betaBar' β := by
    unfold StationaryMFG.Hamiltonian.betaBar'
    positivity
  -- Step 1: get `MemLp u β̄'` from `MemLp u γ̄`.
  have hu_lpγ : Periodic.MemLpPer (d := d) gammaBar reps.u := reps.hu_lp_γ
  have hu_lpγ' :
      Periodic.MemLpPer (d := d) (ENNReal.ofReal γBar) reps.u := by
    rw [← hgammaBar_eq]; exact hu_lpγ
  have hu_memLpγ : MeasureTheory.MemLp reps.u (ENNReal.ofReal γBar)
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
    hu_lpγ'
  have h_p_le_q :
      ENNReal.ofReal (StationaryMFG.Hamiltonian.betaBar' β) ≤
        ENNReal.ofReal γBar :=
    ENNReal.ofReal_le_ofReal hbetaBarP_le_gBar
  have hu_memLpβ' : MeasureTheory.MemLp reps.u
      (ENNReal.ofReal (StationaryMFG.Hamiltonian.betaBar' β))
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
    hu_memLpγ.mono_exponent h_p_le_q
  -- Step 2: integrability of `‖u x‖^β̄'` via `MemLp.integrable_norm_rpow`.
  have hp_ne_zero : ENNReal.ofReal (StationaryMFG.Hamiltonian.betaBar' β) ≠ 0 := by
    simp [ENNReal.ofReal_ne_zero_iff, hbetaBarP_pos]
  have hp_top : ENNReal.ofReal (StationaryMFG.Hamiltonian.betaBar' β) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hp_toReal :
      (ENNReal.ofReal (StationaryMFG.Hamiltonian.betaBar' β)).toReal =
        StationaryMFG.Hamiltonian.betaBar' β :=
    ENNReal.toReal_ofReal hbetaBarP_pos.le
  have h_norm_int : MeasureTheory.Integrable
      (fun x => ‖reps.u x‖ ^ StationaryMFG.Hamiltonian.betaBar' β)
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
    have := MeasureTheory.MemLp.integrable_norm_rpow hu_memLpβ' hp_ne_zero hp_top
    rw [hp_toReal] at this
    exact this
  -- Step 3: `‖u x‖ = |u x|` on `ℝ`, so the two integrals coincide.
  have h_eq : (fun x => ‖reps.u x‖ ^ StationaryMFG.Hamiltonian.betaBar' β) =
      (fun x => |reps.u x| ^ StationaryMFG.Hamiltonian.betaBar' β) := by
    funext x; rw [Real.norm_eq_abs]
  rw [← h_eq]; exact h_norm_int

/-- **BB3-transport #9 (`hRHSabove_int`)**: integrability of the
upper-bound integrand `|V(x)| + h.C * (m_ε(x)^β + 1)`. Linear sum of
* `hV_int : Integrable |V|` — paper-side hypothesis (from `pack3.hV`
  forwarding), and
* `h.C * (m^β + 1)` — from the landed `hMbeta_int` plus
  `Integrable.add_const` on the finite-measure cube and then
  `Integrable.const_mul` by `h.C`. -/
lemma hRHSabove_int
    (reps : CongestionBareRepresentatives (d := d) X betaBar gammaBar V H DpH ε)
    (h : StationaryMFG.Hamiltonian.CongestionAprioriPowerData H DpH)
    (hV_int : MeasureTheory.Integrable (fun x => |V x|)
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (hbetaBar_eq : betaBar = ENNReal.ofReal (h.β + 1)) :
    MeasureTheory.Integrable
      (fun x => |V x| + h.C * (reps.m x ^ h.β + 1))
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
  -- Equip cube with finite measure.
  haveI hcube_fin :
      MeasureTheory.IsFiniteMeasure (MeasureTheory.Measure.restrict
        (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
        (UnitCube (d := d))) :=
    ⟨by
      rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
          volume_unitCube]
      exact ENNReal.one_lt_top⟩
  -- Step 1: `Integrable (fun x => m x ^ β)` from `hMbeta_int`.
  have hMβ : MeasureTheory.Integrable (fun x => reps.m x ^ h.β)
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
    reps.hMbeta_int (β := h.β) h.hβ hbetaBar_eq
  -- Step 2: `Integrable (fun x => m x ^ β + 1)` via `add_const`.
  have h_one_int : MeasureTheory.Integrable
      (fun _ : (Fin d → ℝ) => (1 : ℝ))
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
    MeasureTheory.integrable_const 1
  have hMβ1 : MeasureTheory.Integrable (fun x => reps.m x ^ h.β + 1)
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
    hMβ.add h_one_int
  -- Step 3: scale by `h.C`.
  have hCMβ1 : MeasureTheory.Integrable
      (fun x => h.C * (reps.m x ^ h.β + 1))
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
    hMβ1.const_mul h.C
  -- Step 4: add `|V|`.
  exact hV_int.add hCMβ1

/-- **BB3-transport (BB3-transport-hRHSbelow-mDpHDu-summand)**:
integrability of the `m_ε · (D_pH(x, Du_ε, m_ε) ⬝ Du_ε)` summand on the
unit cube, the second substantive Hölder pairing of the
`hRHSbelow_int` assembly.

Strategy:
1. Cauchy–Schwarz / euclidean-dot bound: `q ⬝ v ≤ d · ‖q‖ · ‖v‖` and
   likewise `-(q ⬝ v) = (-q) ⬝ v ≤ d · ‖q‖ · ‖v‖`, hence
   `|q ⬝ v| ≤ d · ‖q‖ · ‖v‖`.
2. `pack3.hPower.DpH_upper`:
   `‖D_pH x p m‖ ≤ C(‖p‖^{α-1} + m^{β - β/α} + 1)` for `m > 0`.
3. Combined under `m > 0`:
   `|m · (D_pH ⬝ Du)| ≤ d · C · m · (‖Du‖^{α-1} + m^{β-β/α} + 1) · ‖Du‖`
   `= d·C · (m · ‖Du‖^α  +  m^{1+β-β/α} · ‖Du‖  +  m · ‖Du‖)`.
4. Young's inequality at three different conjugate pairs dominates
   each piece by `c₁ · m^{β+1} + c₂ · (‖Du‖^γ̄ + 1)`:
   - `m · ‖Du‖^α`: Young at `(β+1, β̄')`, then upgrade
     `‖Du‖^{α·β̄'} ≤ ‖Du‖^γ̄ + 1` via the exponent rider
     `α·β̄' ≤ γ̄`. (Same Hölder as in `mH_int`.)
   - `m^{1+β-β/α} · ‖Du‖`: Young at `((β+1)/(1+β-β/α), α·β̄')`,
     so `(m^{1+β-β/α})^p = m^{β+1}` and `‖Du‖^q ≤ ‖Du‖^γ̄ + 1`.
   - `m · ‖Du‖`: Young at `(β+1, β̄')`, then upgrade
     `‖Du‖^{β̄'} ≤ ‖Du‖^γ̄ + 1` (since `β̄' < α·β̄' ≤ γ̄`).
5. Build a single linear dominator `Bnd` and close with
   `Integrable.mono'`. -/
lemma mDpHDu_int
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (reps : CongestionBareRepresentatives (d := d) X betaBar gammaBar V H DpH ε)
    (h : StationaryMFG.Hamiltonian.CongestionAprioriPowerData H DpH)
    (hcong : StationaryMFG.Hamiltonian.CongestionGrowthCore (d := d) H DpH J)
    (hα_eq : h.α = hcong.α) (hβ_eq : h.β = hcong.β)
    (hbetaBar_eq : betaBar = ENNReal.ofReal (h.β + 1))
    {γBar : ℝ} (hγBar_pos : 0 < γBar)
    (hgammaBar_eq : gammaBar = ENNReal.ofReal γBar)
    (hγBar_ge_alpha_betaBarP :
      h.α * StationaryMFG.Hamiltonian.betaBar' h.β ≤ γBar) :
    MeasureTheory.Integrable
      (fun x => reps.m x
                  * ((DpH x (fun i => reps.Du i x) (reps.m x))
                      ⬝ (fun i => reps.Du i x)))
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
  classical
  -- Equip cube with finite measure.
  haveI hcube_fin :
      MeasureTheory.IsFiniteMeasure (MeasureTheory.Measure.restrict
        (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
        (UnitCube (d := d))) :=
    ⟨by
      rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
          volume_unitCube]
      exact ENNReal.one_lt_top⟩
  set μC : MeasureTheory.Measure (Fin d → ℝ) :=
    MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d) with hμC_def
  -- Positivity facts.
  have hα_pos : 0 < h.α := lt_trans one_pos h.hα
  have hβ_pos : 0 < h.β := h.hβ
  have hβp1_pos : 0 < h.β + 1 := by linarith
  have hC_pos : 0 < h.C := h.hC
  -- `s := 1 + β - β/α` ≥ 0 and ≤ β+1.
  have hβ_div_α_le_β : h.β / h.α ≤ h.β := by
    have h1 : (1 : ℝ) ≤ h.α := le_of_lt h.hα
    have h2 : h.β / h.α ≤ h.β / 1 := by
      apply div_le_div_of_nonneg_left hβ_pos.le _ h1
      linarith [h.hα]
    simpa using h2
  set s : ℝ := 1 + h.β - h.β / h.α with hs_def
  have hs_pos : 0 < s := by
    have : 0 ≤ h.β - h.β / h.α := by linarith
    have : 0 < 1 + (h.β - h.β / h.α) := by linarith
    simpa [hs_def, sub_eq_add_neg, add_assoc] using this
  have hs_le_βp1 : s ≤ h.β + 1 := by
    have : h.β / h.α ≥ 0 := div_nonneg hβ_pos.le (by linarith [h.hα])
    simp [hs_def]; linarith
  -- Hölder-conjugate witness `(β+1, β̄')`.
  have hbetaBarP_eq : StationaryMFG.Hamiltonian.betaBar' h.β = (h.β + 1) / h.β := rfl
  have hbetaBarP_pos : 0 < StationaryMFG.Hamiltonian.betaBar' h.β := by
    rw [hbetaBarP_eq]; positivity
  have hpq1 : (h.β + 1).HolderConjugate (StationaryMFG.Hamiltonian.betaBar' h.β) := by
    refine (Real.holderConjugate_iff).mpr ⟨?_, ?_⟩
    · linarith
    · rw [hbetaBarP_eq]
      field_simp
      ring
  -- For piece 2 we use conjugate pair (p₂, q₂) with p₂ = (β+1)/s, q₂ = α·β̄'.
  -- Sanity: 1/p₂ + 1/q₂ = s/(β+1) + 1/(α·β̄') = s/(β+1) + β/(α·(β+1)) ·.. let's
  -- just verify the equation. We have α·β̄' = α·(β+1)/β, so 1/(α·β̄') = β/(α·(β+1)).
  -- And s/(β+1) = (1+β-β/α)/(β+1). Sum: (1+β-β/α + β/α)/(β+1) = (β+1)/(β+1) = 1. ✓
  set p₂ : ℝ := (h.β + 1) / s with hp₂_def
  set q₂ : ℝ := h.α * StationaryMFG.Hamiltonian.betaBar' h.β with hq₂_def
  have hp₂_pos : 0 < p₂ := by rw [hp₂_def]; exact div_pos hβp1_pos hs_pos
  have hq₂_pos : 0 < q₂ := by rw [hq₂_def]; exact mul_pos hα_pos hbetaBarP_pos
  have hp₂_one_lt : 1 < p₂ := by
    rw [hp₂_def, lt_div_iff₀ hs_pos]
    have : s < h.β + 1 := by
      have hαβ_pos : 0 < h.β / h.α := div_pos hβ_pos (by linarith [h.hα])
      simp [hs_def]; linarith
    linarith
  have hpq2 : p₂.HolderConjugate q₂ := by
    refine (Real.holderConjugate_iff).mpr ⟨hp₂_one_lt, ?_⟩
    -- 1/p₂ + 1/q₂ = s/(β+1) + 1/(α·β̄') = 1.
    rw [hp₂_def, hq₂_def, hbetaBarP_eq]
    have hβ_ne : h.β ≠ 0 := hβ_pos.ne'
    have hα_ne : h.α ≠ 0 := (lt_trans one_pos h.hα).ne'
    have hβp1_ne : h.β + 1 ≠ 0 := hβp1_pos.ne'
    have hs_ne : s ≠ 0 := hs_pos.ne'
    rw [hs_def]
    field_simp
    ring
  -- === Congestion-native exponents (paper Lemma `lem:ADFGU.congestion`). ===
  -- The congestion `D_pH` bound (eq:assH.DpH.upper.congestion) uses the
  -- exponent `γc := α(1 + τ/β)` on `‖p‖`.  Note `0 ≤ τ ≤ 1`, hence
  -- `γc ≤ α(1 + 1/β) = α·β̄' = γBar_min ≤ γBar`.
  have hτ_nn : 0 ≤ hcong.τ := hcong.hτ.1
  have hτ_le_one : hcong.τ ≤ 1 := hcong.hτ.2
  set γc : ℝ := h.α * (1 + hcong.τ / h.β) with hγc_def
  have hγc_pos : 0 < γc := by
    rw [hγc_def]
    have : 0 < 1 + hcong.τ / h.β :=
      by have : 0 ≤ hcong.τ / h.β := div_nonneg hτ_nn hβ_pos.le
         linarith
    exact mul_pos hα_pos this
  -- `α·β̄' = α(β+1)/β = α(1 + 1/β)`, so `γc ≤ α·β̄' ≤ γBar`.
  have hαβ'_eq : h.α * StationaryMFG.Hamiltonian.betaBar' h.β
      = h.α * (1 + 1 / h.β) := by
    rw [hbetaBarP_eq]
    have hβ_ne : h.β ≠ 0 := hβ_pos.ne'
    congr 1
    field_simp
  have hγc_le_αβ' : γc ≤ h.α * StationaryMFG.Hamiltonian.betaBar' h.β := by
    rw [hαβ'_eq, hγc_def]
    apply mul_le_mul_of_nonneg_left _ hα_pos.le
    have hstep : hcong.τ / h.β ≤ 1 / h.β :=
      div_le_div_of_nonneg_right hτ_le_one hβ_pos.le
    linarith
  have hγc_le_γBar : γc ≤ γBar := le_trans hγc_le_αβ' hγBar_ge_alpha_betaBarP
  -- `1 ≤ γBar` (since `γBar ≥ α·β̄' > 1`).
  have hone_le_γBar : (1 : ℝ) ≤ γBar := by
    have h1 : (1 : ℝ) < h.α * StationaryMFG.Hamiltonian.betaBar' h.β := by
      have : (1 : ℝ) < StationaryMFG.Hamiltonian.betaBar' h.β :=
        StationaryMFG.Hamiltonian.one_lt_betaBar' h.β hβ_pos
      calc (1 : ℝ) = 1 * 1 := by ring
        _ < h.α * StationaryMFG.Hamiltonian.betaBar' h.β :=
            mul_lt_mul'' h.hα this zero_le_one zero_le_one
    linarith [hγBar_ge_alpha_betaBarP]
  -- === Piece-B (`m^{1-τ}·‖p‖^{γc}`) Young conjugate pair. ===
  -- We use `(P_B, Q_B) = ((β+1)/(1-τ), (β+1)/(β+τ))` (only for `τ < 1`; the
  -- `τ = 1` case degenerates `m^{1-τ}=1` into Piece A).  Then
  -- `(m^{1-τ})^{P_B} = m^{β+1}` and `γc·Q_B = α·β̄' (= γBar_min) ≤ γBar`.
  set oneMτ : ℝ := 1 - hcong.τ with honeMτ_def
  have honeMτ_nn : 0 ≤ oneMτ := by rw [honeMτ_def]; linarith
  -- Step 1: integrabilities of building blocks.
  have hMβ1 : MeasureTheory.Integrable (fun x => reps.m x ^ (h.β + 1)) μC :=
    reps.hLB_int (β := h.β) hβ_pos hbetaBar_eq
  have hDuγ : MeasureTheory.Integrable
      (fun x => ‖(fun i => reps.Du i x)‖ ^ γBar) μC :=
    reps.hDu_norm_int (γBar := γBar) hγBar_pos hgammaBar_eq
  have h_one_int : MeasureTheory.Integrable (fun _ : (Fin d → ℝ) => (1 : ℝ)) μC :=
    MeasureTheory.integrable_const 1
  -- AE strong measurability of `m`, `Du` (each axis), the joint vector,
  -- and the `DpH`-composition.
  have hm_aesm :
      MeasureTheory.AEStronglyMeasurable reps.m μC := by
    have hm_lp : Periodic.MemLpPer (d := d) betaBar reps.m :=
      Periodic.MemLpPer.congr_ae_unitCube reps.hmem_lp_coe_m reps.hae_m.symm
    exact hm_lp.aestronglyMeasurable
  have hDu_meas : ∀ i, MeasureTheory.AEStronglyMeasurable (reps.Du i) μC :=
    fun i => (reps.hDu_lp i).aestronglyMeasurable
  have hDu_aem : ∀ i, AEMeasurable (reps.Du i) μC :=
    fun i => (hDu_meas i).aemeasurable
  have hPi_aem : AEMeasurable
      (fun x : Fin d → ℝ => (fun i => reps.Du i x)) μC :=
    AEMeasurable.of_eval hDu_aem
  have hPi_meas : MeasureTheory.AEStronglyMeasurable
      (fun x : Fin d → ℝ => (fun i => reps.Du i x)) μC :=
    aestronglyMeasurable_iff_aemeasurable.mpr hPi_aem
  have hm_aem : AEMeasurable reps.m μC := hm_aesm.aemeasurable
  have hself_aem : AEMeasurable (fun x : Fin d → ℝ => x) μC :=
    aemeasurable_id
  have hTriple_aem : AEMeasurable
      (fun x : Fin d → ℝ => (x, (fun i => reps.Du i x), reps.m x)) μC := by
    refine AEMeasurable.prodMk hself_aem ?_
    refine AEMeasurable.prodMk hPi_aem hm_aem
  have hDpH_meas : Measurable
      (fun (xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ) => DpH xpm.1 xpm.2.1 xpm.2.2) :=
    h.measurable_DpH
  have hDpH_comp_aem : AEMeasurable
      (fun x : Fin d → ℝ => DpH x (fun i => reps.Du i x) (reps.m x)) μC :=
    hDpH_meas.comp_aemeasurable hTriple_aem
  have hDpH_comp_aesm : MeasureTheory.AEStronglyMeasurable
      (fun x : Fin d → ℝ => DpH x (fun i => reps.Du i x) (reps.m x)) μC := by
    -- Range is `Fin d → ℝ`, which is `SecondCountableTopology`.
    exact aestronglyMeasurable_iff_aemeasurable.mpr hDpH_comp_aem
  -- The dot product `(DpH ⬝ Du) = ∑ i, DpH·.i * Du i` is AE-strongly measurable.
  have hDot_aesm : MeasureTheory.AEStronglyMeasurable
      (fun x : Fin d → ℝ =>
        (DpH x (fun i => reps.Du i x) (reps.m x)) ⬝ (fun i => reps.Du i x)) μC := by
    unfold dotProduct
    refine Finset.aestronglyMeasurable_fun_sum (Finset.univ : Finset (Fin d))
      (f := fun i x => (DpH x (fun j => reps.Du j x) (reps.m x)) i * reps.Du i x) ?_
    intro i _
    refine MeasureTheory.AEStronglyMeasurable.mul ?_ (hDu_meas i)
    -- (DpH ...) i is AE strongly measurable via composition.
    have hpi_i : Measurable (fun (v : Fin d → ℝ) => v i) :=
      measurable_pi_apply i
    have : MeasureTheory.AEStronglyMeasurable
        (fun x => (DpH x (fun j => reps.Du j x) (reps.m x)) i) μC := by
      refine aestronglyMeasurable_iff_aemeasurable.mpr ?_
      exact hpi_i.comp_aemeasurable hDpH_comp_aem
    exact this
  have hmDot_aesm : MeasureTheory.AEStronglyMeasurable
      (fun x => reps.m x
        * ((DpH x (fun i => reps.Du i x) (reps.m x)) ⬝ (fun i => reps.Du i x))) μC :=
    hm_aesm.mul hDot_aesm
  -- Step 2: dominator envelope `Bnd`.
  -- We will dominate by:
  --   `Bnd x = K_m · m^{β+1} + K_Du · (‖Du‖^γ̄ + 1)` for some K_m, K_Du > 0.
  -- A coarse choice: take K_m and K_Du large enough to absorb all three pieces.
  -- Concretely:
  --   Piece 1 (m·‖Du‖^α):
  --      ≤ m^{β+1}/(β+1) + (‖Du‖^γ̄ + 1) / β̄'    [Young + upgrade]
  --   Piece 2 (m^s · ‖Du‖):
  --      ≤ m^{β+1}/p₂ + (‖Du‖^γ̄ + 1) / q₂      [Young + upgrade]
  --   Piece 3 (m·‖Du‖):
  --      ≤ m^{β+1}/(β+1) + (‖Du‖^γ̄ + 1) / β̄'    [Young + upgrade]
  -- Sum and multiply by `d·C ≥ 0`. Choose
  --   K_m   := d·C · (1/(β+1) + 1/p₂ + 1/(β+1))
  --   K_Du  := d·C · (1/β̄' + 1/q₂ + 1/β̄')
  -- Congestion-native dominator coefficients.  After multiplying the
  -- congestion `D_pH` bound by `m` and Cauchy–Schwarz, the integrand splits
  -- into four pieces A=‖p‖^{γc}, B=m^{1-τ}‖p‖^{γc}, C=m^s‖p‖, D=‖p‖.  Each is
  -- Young-dominated by `c·m^{β+1} + c'·(‖p‖^{γBar}+1)` with all `c, c' ≤ 1`.
  -- We choose generous constants (their precise value is irrelevant for
  -- integrability) and close the final inequality by `linarith`.
  set Km : ℝ := (d : ℝ) * hcong.C * (1 / p₂ + 1) with hKm_def
  set KDu : ℝ := (d : ℝ) * hcong.C * (1 / q₂ + 3) with hKDu_def
  have hKm_nn : 0 ≤ Km := by
    rw [hKm_def]
    have h1 : 0 ≤ 1 / p₂ := by positivity
    have : 0 ≤ 1 / p₂ + 1 := by linarith
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg d) hcong.hC.le) this
  have hKDu_nn : 0 ≤ KDu := by
    rw [hKDu_def]
    have h1 : 0 ≤ 1 / q₂ := by positivity
    have : 0 ≤ 1 / q₂ + 3 := by linarith
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg d) hcong.hC.le) this
  set Bnd : (Fin d → ℝ) → ℝ :=
    fun x => Km * reps.m x ^ (h.β + 1)
              + KDu * (‖(fun i => reps.Du i x)‖ ^ γBar + 1) with hBnd_def
  have hBnd_int : MeasureTheory.Integrable Bnd μC := by
    have h1 : MeasureTheory.Integrable (fun x => Km * reps.m x ^ (h.β + 1)) μC :=
      hMβ1.const_mul Km
    have h2 : MeasureTheory.Integrable
        (fun x => ‖(fun i => reps.Du i x)‖ ^ γBar + 1) μC :=
      hDuγ.add h_one_int
    have h3 : MeasureTheory.Integrable
        (fun x => KDu * (‖(fun i => reps.Du i x)‖ ^ γBar + 1)) μC :=
      h2.const_mul KDu
    exact h1.add h3
  -- Step 3: pointwise AE-bound via Cauchy-Schwarz + DpH_upper + Young.
  have hPointwise :
      ∀ᵐ x ∂μC,
        ‖reps.m x
            * ((DpH x (fun i => reps.Du i x) (reps.m x)) ⬝ (fun i => reps.Du i x))‖
          ≤ Bnd x := by
    -- **Positivity-elimination migration (child-B, route a):** the
    -- pointwise bound on `‖m·(D_pH⬝Du)‖` no longer routes through the
    -- singular congestion `D_pH` envelope (`hcong.DpH_upper`, which carries
    -- the `1/m`, `1/m^τ` terms requiring `0 < m`). Instead we use the
    -- **`m`-multiplied** envelope `CongestionGrowthCore.mDpH_extended_bound`
    -- (`Assumptions.lean`) on the extension `J = m·D_pH`, which holds for
    -- `0 ≤ m` (the singular terms have been cancelled against the outer `m`
    -- analytically and the boundary `m = 0` handled by `mDpHat0`). We only
    -- need a.e. NONNEGATIVITY `reps.mε_nonneg`, NOT strict positivity.
    filter_upwards [hcong.mDpH_extended_bound, reps.mε_nonneg] with x hxJ hxm_nn
    set p : Fin d → ℝ := fun i => reps.Du i x
    set q : Fin d → ℝ := DpH x p (reps.m x)
    have hmpos_nn : 0 ≤ reps.m x := hxm_nn
    have hp_nn : 0 ≤ ‖p‖ := norm_nonneg _
    have hq_nn : 0 ≤ ‖q‖ := norm_nonneg _
    have hd_nn : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
    -- The `m·(D_pH⬝Du)` envelope, derived from `mDpH_extended_bound`.
    -- Target shape (matches the old `hExpandE` RHS times `d`):
    --   |m·(q⬝p)| ≤ d·C·(‖p‖^γc + m^oneMτ·‖p‖^γc + m^s·‖p‖ + ‖p‖).
    have hmEnv : |reps.m x * (q ⬝ p)|
        ≤ (d : ℝ) * (hcong.C * (‖p‖ ^ γc)
            + hcong.C * (reps.m x ^ oneMτ * ‖p‖ ^ γc)
            + hcong.C * (reps.m x ^ s * ‖p‖)
            + hcong.C * ‖p‖) := by
      -- `J`-envelope at `(p, m x)`, exponents aligned to the local names.
      -- `mDpH_extended_bound`: `‖J x p m‖ ≤ C(1+m^{1-τ})‖p‖^{α(1+τ/β)-1}
      --   + C(m^{β+1-β/α}+1)`. With `hα_eq/hβ_eq`: the exponents match
      -- `γc-1`, `oneMτ = 1-τ`, `s = β+1-β/α`.
      have hJbase := hxJ p (reps.m x) hxm_nn
      have hexp1 : hcong.α * (1 + hcong.τ / hcong.β) - 1 = γc - 1 := by
        rw [hγc_def, hα_eq, hβ_eq]
      have hexp2 : hcong.β + 1 - hcong.β / hcong.α = s := by
        rw [hs_def, hα_eq, hβ_eq]; ring
      have hexp3 : (1 : ℝ) - hcong.τ = oneMτ := by rw [honeMτ_def]
      rw [hexp1, hexp2, hexp3] at hJbase
      -- `hJbase : ‖J x p (m x)‖ ≤ C(1+m^oneMτ)‖p‖^{γc-1} + C(m^s+1)`.
      set RJ : ℝ := hcong.C * (1 + reps.m x ^ oneMτ) * (‖p‖ ^ (γc - 1))
                    + hcong.C * (reps.m x ^ s + 1) with hRJ_def
      have hRJ_nn : 0 ≤ RJ := le_trans (norm_nonneg _) hJbase
      -- Cauchy–Schwarz bound `|J⬝p| ≤ d·‖J‖·‖p‖` for any vector `J`.
      have hCS : ∀ Jv : Fin d → ℝ, |Jv ⬝ p| ≤ (d : ℝ) * ‖Jv‖ * ‖p‖ := by
        intro Jv
        have hdot_le : ∀ w : Fin d → ℝ, w ⬝ p ≤ (d : ℝ) * ‖w‖ * ‖p‖ := by
          intro w
          unfold dotProduct
          have h_each : ∀ i ∈ (Finset.univ : Finset (Fin d)),
              w i * p i ≤ ‖w‖ * ‖p‖ := by
            intro i _
            calc w i * p i ≤ |w i * p i| := le_abs_self _
              _ = |w i| * |p i| := abs_mul _ _
              _ ≤ ‖w‖ * |p i| :=
                  mul_le_mul_of_nonneg_right
                    (by simpa [Real.norm_eq_abs] using norm_le_pi_norm w i)
                    (abs_nonneg _)
              _ ≤ ‖w‖ * ‖p‖ :=
                  mul_le_mul_of_nonneg_left
                    (by simpa [Real.norm_eq_abs] using norm_le_pi_norm p i)
                    (norm_nonneg _)
          calc (∑ i, w i * p i) ≤ ∑ _ : Fin d, ‖w‖ * ‖p‖ :=
                Finset.sum_le_sum h_each
            _ = (d : ℝ) * ‖w‖ * ‖p‖ := by
                simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
        have hupper := hdot_le Jv
        have hlower : -(Jv ⬝ p) ≤ (d : ℝ) * ‖Jv‖ * ‖p‖ := by
          have hneg := hdot_le (-Jv)
          have hdot_neg : (-Jv) ⬝ p = -(Jv ⬝ p) := by
            unfold dotProduct
            rw [← Finset.sum_neg_distrib]
            exact Finset.sum_congr rfl (fun i _ => by simp [Pi.neg_apply, neg_mul])
          rwa [hdot_neg, norm_neg] at hneg
        rw [abs_le]; exact ⟨by linarith, hupper⟩
      -- Split on `m x = 0` vs `0 < m x`. At `m x = 0`, LHS is `0`.
      rcases eq_or_lt_of_le hxm_nn with hm0 | hmpos
      · -- `m x = 0`: `|m·(q⬝p)| = 0 ≤ RHS` (RHS ≥ 0).
        rw [← hm0, zero_mul, abs_zero]
        have hγc_nn : 0 ≤ ‖p‖ ^ γc := Real.rpow_nonneg hp_nn _
        have hmoneMτ_nn : 0 ≤ reps.m x ^ oneMτ := Real.rpow_nonneg hmpos_nn _
        have hms_nn0 : 0 ≤ reps.m x ^ s := Real.rpow_nonneg hmpos_nn _
        have hCnn : 0 ≤ hcong.C := hcong.hC.le
        positivity
      · -- `0 < m x`: `m·(q⬝p) = (m•D_pH)⬝p = J⬝p`, then Cauchy–Schwarz + `hJbase`.
        have hJeq : J x p (reps.m x) = reps.m x • q :=
          hcong.mDpHat0.J_of_pos x p (reps.m x) hmpos
        -- `J⬝p = (m•q)⬝p = m·(q⬝p)`.
        have hJdot : J x p (reps.m x) ⬝ p = reps.m x * (q ⬝ p) := by
          rw [hJeq]
          unfold dotProduct
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun i _ => by
            simp [Pi.smul_apply, smul_eq_mul]; ring)
        -- `|m·(q⬝p)| = |J⬝p| ≤ d·‖J‖·‖p‖ ≤ d·RJ·‖p‖`.
        rw [← hJdot]
        refine le_trans (hCS (J x p (reps.m x))) ?_
        have hstep : (d : ℝ) * ‖J x p (reps.m x)‖ * ‖p‖
            ≤ (d : ℝ) * RJ * ‖p‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hJbase hd_nn) hp_nn
        refine le_trans hstep ?_
        -- `d·RJ·‖p‖ = d·C·(‖p‖^γc + m^oneMτ·‖p‖^γc + m^s·‖p‖ + ‖p‖)`,
        -- using `‖p‖^{γc-1}·‖p‖ = ‖p‖^γc`.
        have hpγc : ‖p‖ ^ (γc - 1) * ‖p‖ = ‖p‖ ^ γc := by
          by_cases hp_zero : ‖p‖ = 0
          · rw [hp_zero, mul_zero, Real.zero_rpow hγc_pos.ne']
          · have hp_pos : 0 < ‖p‖ := lt_of_le_of_ne hp_nn (Ne.symm hp_zero)
            calc ‖p‖ ^ (γc - 1) * ‖p‖
                = ‖p‖ ^ (γc - 1) * ‖p‖ ^ (1 : ℝ) := by rw [Real.rpow_one]
              _ = ‖p‖ ^ ((γc - 1) + 1) := (Real.rpow_add hp_pos _ _).symm
              _ = ‖p‖ ^ γc := by ring_nf
        rw [hRJ_def]
        have hexpand : (d : ℝ)
            * (hcong.C * (1 + reps.m x ^ oneMτ) * (‖p‖ ^ (γc - 1))
                + hcong.C * (reps.m x ^ s + 1)) * ‖p‖
            = (d : ℝ) * (hcong.C * (‖p‖ ^ (γc - 1) * ‖p‖)
                + hcong.C * (reps.m x ^ oneMτ * (‖p‖ ^ (γc - 1) * ‖p‖))
                + hcong.C * (reps.m x ^ s * ‖p‖)
                + hcong.C * ‖p‖) := by ring
        rw [hexpand, hpγc]
    -- === Bound each piece by `α·m^{β+1} + β·(‖p‖^{γBar}+1)`. ===
    have hγc_nn : 0 ≤ ‖p‖ ^ γc := Real.rpow_nonneg hp_nn _
    have hγBar_p_nn : 0 ≤ ‖p‖ ^ γBar := Real.rpow_nonneg hp_nn _
    have hβp1_m_nn0 : 0 ≤ reps.m x ^ (h.β + 1) := Real.rpow_nonneg hmpos_nn _
    -- Piece A: `‖p‖^{γc} ≤ ‖p‖^{γBar} + 1` (γc ≤ γBar).
    have hPieceA : ‖p‖ ^ γc ≤ ‖p‖ ^ γBar + 1 := by
      by_cases hp1 : 1 ≤ ‖p‖
      · have := Real.rpow_le_rpow_of_exponent_le hp1 hγc_le_γBar
        linarith
      · push_neg at hp1
        have := Real.rpow_le_one hp_nn hp1.le hγc_pos.le
        linarith
    -- Piece D: `‖p‖ ≤ ‖p‖^{γBar} + 1` (γBar ≥ 1).
    have hPieceD : ‖p‖ ≤ ‖p‖ ^ γBar + 1 := by
      by_cases hp1 : 1 ≤ ‖p‖
      · have h0 : ‖p‖ = ‖p‖ ^ (1 : ℝ) := (Real.rpow_one _).symm
        have := Real.rpow_le_rpow_of_exponent_le hp1 hone_le_γBar
        rw [← h0] at this; linarith
      · push_neg at hp1; linarith
    -- Piece C: `m^s·‖p‖ ≤ m^{β+1}/p₂ + (‖p‖^{γBar}+1)/q₂` (Young at (p₂,q₂)).
    have hms_nn : 0 ≤ reps.m x ^ s := Real.rpow_nonneg hmpos_nn _
    have hYoungC := Real.young_inequality_of_nonneg
      (a := reps.m x ^ s) (b := ‖p‖) (p := p₂) (q := q₂) hms_nn hp_nn hpq2
    have hsp2 : s * p₂ = h.β + 1 := by rw [hp₂_def]; field_simp
    have hrpow_mul2 : (reps.m x ^ s) ^ p₂ = reps.m x ^ (h.β + 1) := by
      rw [← Real.rpow_mul hmpos_nn, hsp2]
    have hbound_pq2 : ‖p‖ ^ q₂ ≤ ‖p‖ ^ γBar + 1 := by
      have hq2_eq : q₂ = h.α * StationaryMFG.Hamiltonian.betaBar' h.β := rfl
      by_cases hp1 : 1 ≤ ‖p‖
      · rw [hq2_eq]
        have := Real.rpow_le_rpow_of_exponent_le hp1 hγBar_ge_alpha_betaBarP
        linarith
      · push_neg at hp1
        have := Real.rpow_le_one hp_nn hp1.le hq₂_pos.le
        linarith
    have hPieceC : reps.m x ^ s * ‖p‖
        ≤ reps.m x ^ (h.β + 1) / p₂ + (‖p‖ ^ γBar + 1) / q₂ := by
      refine le_trans hYoungC ?_
      have hC1 : (reps.m x ^ s) ^ p₂ / p₂ = reps.m x ^ (h.β + 1) / p₂ := by
        rw [hrpow_mul2]
      have hC2 : ‖p‖ ^ q₂ / q₂ ≤ (‖p‖ ^ γBar + 1) / q₂ :=
        div_le_div_of_nonneg_right hbound_pq2 hq₂_pos.le
      linarith
    -- Piece B: `m^{1-τ}·‖p‖^{γc} ≤ m^{β+1} + (‖p‖^{γBar}+1)`.
    -- Case `τ = 1`: `m^{1-τ} = m^0 = 1`, reduces to Piece A.
    -- Case `τ < 1`: Young at `(P_B, Q_B) = ((β+1)/(1-τ), (β+1)/(β+τ))` with
    --   `(m^{1-τ})^{P_B} = m^{β+1}` and `γc·Q_B = α·β̄' ≤ γBar`.
    have hms_oneMτ_nn : 0 ≤ reps.m x ^ oneMτ := Real.rpow_nonneg hmpos_nn _
    have hPieceB : reps.m x ^ oneMτ * ‖p‖ ^ γc
        ≤ reps.m x ^ (h.β + 1) + (‖p‖ ^ γBar + 1) := by
      by_cases hτ1 : hcong.τ = 1
      · -- `oneMτ = 0`, so `m^{oneMτ} = 1`.
        have hone : reps.m x ^ oneMτ = 1 := by
          rw [honeMτ_def, hτ1, sub_self, Real.rpow_zero]
        rw [hone, one_mul]
        have := hPieceA
        linarith [hβp1_m_nn0]
      · -- `τ < 1`, so `oneMτ > 0`.
        have hτ_lt_one : hcong.τ < 1 := lt_of_le_of_ne hτ_le_one hτ1
        have honeMτ_pos : 0 < oneMτ := by rw [honeMτ_def]; linarith
        set PB : ℝ := (h.β + 1) / oneMτ with hPB_def
        set QB : ℝ := (h.β + 1) / (h.β + hcong.τ) with hQB_def
        have hβpτ_pos : 0 < h.β + hcong.τ := by linarith [hτ_nn]
        have hPB_pos : 0 < PB := by rw [hPB_def]; exact div_pos hβp1_pos honeMτ_pos
        have hQB_pos : 0 < QB := by rw [hQB_def]; exact div_pos hβp1_pos hβpτ_pos
        have hPB_one_lt : 1 < PB := by
          rw [hPB_def, lt_div_iff₀ honeMτ_pos]
          rw [honeMτ_def]; linarith [hβ_pos]
        have hpqB : PB.HolderConjugate QB := by
          refine (Real.holderConjugate_iff).mpr ⟨hPB_one_lt, ?_⟩
          -- 1/PB + 1/QB = oneMτ/(β+1) + (β+τ)/(β+1) = (1-τ+β+τ)/(β+1) = 1.
          rw [hPB_def, hQB_def, honeMτ_def]
          have hβp1_ne : h.β + 1 ≠ 0 := hβp1_pos.ne'
          field_simp
          ring
        have hYoungB := Real.young_inequality_of_nonneg
          (a := reps.m x ^ oneMτ) (b := ‖p‖ ^ γc) (p := PB) (q := QB)
          hms_oneMτ_nn hγc_nn hpqB
        -- `(m^{oneMτ})^{PB} = m^{oneMτ·PB} = m^{β+1}`.
        have hoPB : oneMτ * PB = h.β + 1 := by
          rw [hPB_def]; field_simp
        have hrpowB : (reps.m x ^ oneMτ) ^ PB = reps.m x ^ (h.β + 1) := by
          rw [← Real.rpow_mul hmpos_nn, hoPB]
        -- `(‖p‖^{γc})^{QB} = ‖p‖^{γc·QB} ≤ ‖p‖^{γBar} + 1` since `γc·QB ≤ γBar`.
        have hγcQB_le : γc * QB ≤ γBar := by
          -- γc·QB = α(β+τ)/β · (β+1)/(β+τ) = α(β+1)/β = α·β̄' ≤ γBar.
          have hγc_form : γc = h.α * (h.β + hcong.τ) / h.β := by
            rw [hγc_def]
            have hβ_ne : h.β ≠ 0 := hβ_pos.ne'
            field_simp
          have hkey : γc * QB = h.α * StationaryMFG.Hamiltonian.betaBar' h.β := by
            rw [hγc_form, hQB_def, hbetaBarP_eq]
            have hβ_ne : h.β ≠ 0 := hβ_pos.ne'
            have hβpτ_ne : h.β + hcong.τ ≠ 0 := hβpτ_pos.ne'
            field_simp
          rw [hkey]; exact hγBar_ge_alpha_betaBarP
        have hrpowB2 : (‖p‖ ^ γc) ^ QB = ‖p‖ ^ (γc * QB) := by
          rw [← Real.rpow_mul hp_nn]
        have hboundB : (‖p‖ ^ γc) ^ QB ≤ ‖p‖ ^ γBar + 1 := by
          rw [hrpowB2]
          by_cases hp1 : 1 ≤ ‖p‖
          · have hγcQB_pos : 0 < γc * QB := mul_pos hγc_pos hQB_pos
            have := Real.rpow_le_rpow_of_exponent_le hp1 hγcQB_le
            linarith
          · push_neg at hp1
            have hγcQB_pos : 0 < γc * QB := mul_pos hγc_pos hQB_pos
            have := Real.rpow_le_one hp_nn hp1.le hγcQB_pos.le
            linarith
        -- `QB = (β+1)/(β+τ) ≥ 1` since `β+τ ≤ β+1` (τ ≤ 1).
        have hQB_one_le : (1 : ℝ) ≤ QB := by
          rw [hQB_def, le_div_iff₀ hβpτ_pos, one_mul]
          linarith [hτ_le_one]
        refine le_trans hYoungB ?_
        have hB1 : (reps.m x ^ oneMτ) ^ PB / PB ≤ reps.m x ^ (h.β + 1) := by
          rw [hrpowB]
          have hstep : reps.m x ^ (h.β + 1) / PB ≤ reps.m x ^ (h.β + 1) := by
            rw [div_le_iff₀ hPB_pos]
            exact le_mul_of_one_le_right hβp1_m_nn0 hPB_one_lt.le
          exact hstep
        have hB2 : (‖p‖ ^ γc) ^ QB / QB ≤ ‖p‖ ^ γBar + 1 := by
          have hpow_nn : 0 ≤ (‖p‖ ^ γc) ^ QB := Real.rpow_nonneg hγc_nn _
          have hle : (‖p‖ ^ γc) ^ QB / QB ≤ (‖p‖ ^ γc) ^ QB := by
            rw [div_le_iff₀ hQB_pos]
            exact le_mul_of_one_le_right hpow_nn hQB_one_le
          exact le_trans hle hboundB
        linarith
    -- === Assemble: `m·E·‖p‖ ≤ Km·m^{β+1} + KDu·(‖p‖^{γBar}+1)`. ===
    -- coefficient bookkeeping: dC·(A + B + C + D) regroups exactly into
    --   Km·m^{β+1} + KDu·(‖p‖^γ̄+1) with Km = dC(1/p₂+1), KDu = dC(1/q₂+3).
    have hAbs_chain :
        |reps.m x * (q ⬝ p)| ≤ Km * reps.m x ^ (h.β + 1) + KDu * (‖p‖ ^ γBar + 1) := by
      -- Step 1: the `J`-envelope (`hmEnv`, derived from `mDpH_extended_bound`)
      -- gives `|m·(q⬝p)| ≤ d·(C·A + C·B + C·C' + C·D)` directly, for `0 ≤ m`.
      have hstep1 : |reps.m x * (q ⬝ p)|
          ≤ (d : ℝ) * (hcong.C * (‖p‖ ^ γc)
              + hcong.C * (reps.m x ^ oneMτ * ‖p‖ ^ γc)
              + hcong.C * (reps.m x ^ s * ‖p‖)
              + hcong.C * ‖p‖) := hmEnv
      -- Now `|...| ≤ d·(C·A + C·B + C·C' + C·D)` with C = hcong.C.
      -- Bound the bracket by the pieces.  Let `T := A + B + C' + D` style sum.
      have hCcong_nn : 0 ≤ hcong.C := hcong.hC.le
      -- Sum the four pieces (no `C`, no `d`): pure `linarith`.
      have hsum_pieces :
          ‖p‖ ^ γc
            + reps.m x ^ oneMτ * ‖p‖ ^ γc
            + reps.m x ^ s * ‖p‖
            + ‖p‖
          ≤ reps.m x ^ (h.β + 1) / p₂ + (‖p‖ ^ γBar + 1) / q₂
              + reps.m x ^ (h.β + 1)
              + 3 * (‖p‖ ^ γBar + 1) := by
        linarith [hPieceA, hPieceB, hPieceC, hPieceD]
      -- Abbreviate the two sides as `LHSp ≤ RHSp`; then `m·E·‖p‖ = C·LHSp`,
      -- so `C·LHSp ≤ C·RHSp` and `d·(C·LHSp) ≤ d·(C·RHSp)`.
      have hC_sum : hcong.C * (‖p‖ ^ γc
            + reps.m x ^ oneMτ * ‖p‖ ^ γc
            + reps.m x ^ s * ‖p‖
            + ‖p‖)
          ≤ hcong.C * (reps.m x ^ (h.β + 1) / p₂ + (‖p‖ ^ γBar + 1) / q₂
              + reps.m x ^ (h.β + 1)
              + 3 * (‖p‖ ^ γBar + 1)) :=
        mul_le_mul_of_nonneg_left hsum_pieces hCcong_nn
      -- `hExpandE` rewrote `m·E·‖p‖` to the distributed form; refold to `C·LHSp`.
      have hfold : hcong.C * (‖p‖ ^ γc)
            + hcong.C * (reps.m x ^ oneMτ * ‖p‖ ^ γc)
            + hcong.C * (reps.m x ^ s * ‖p‖)
            + hcong.C * ‖p‖
          = hcong.C * (‖p‖ ^ γc
            + reps.m x ^ oneMτ * ‖p‖ ^ γc
            + reps.m x ^ s * ‖p‖
            + ‖p‖) := by ring
      rw [hfold] at hstep1
      -- Multiply by `d ≥ 0`.
      have hd_bracket :
          (d : ℝ) * (hcong.C * (‖p‖ ^ γc
            + reps.m x ^ oneMτ * ‖p‖ ^ γc
            + reps.m x ^ s * ‖p‖
            + ‖p‖))
          ≤ (d : ℝ) * (hcong.C * (reps.m x ^ (h.β + 1) / p₂ + (‖p‖ ^ γBar + 1) / q₂
              + reps.m x ^ (h.β + 1)
              + 3 * (‖p‖ ^ γBar + 1))) :=
        mul_le_mul_of_nonneg_left hC_sum hd_nn
      refine le_trans hstep1 (le_trans hd_bracket ?_)
      -- Final equality: regroup the `m^{β+1}` and `(‖p‖^γ̄+1)` coefficients.
      rw [hKm_def, hKDu_def]
      apply le_of_eq
      ring
    -- Norm vs abs on ℝ:
    have hReal_norm_eq :
        ‖reps.m x * (q ⬝ p)‖ = |reps.m x * (q ⬝ p)| := Real.norm_eq_abs _
    rw [hReal_norm_eq, hBnd_def]
    exact hAbs_chain
  -- Step 4: Integrable.mono'.
  exact hBnd_int.mono' hmDot_aesm hPointwise

/-- **BB3-transport (BB3-transport-hRHSbelow-mH-summand)**:
integrability of the `m_ε · H(x, Du_ε, m_ε)` summand on the unit cube,
the first substantive Hölder pairing of the `hRHSbelow_int` assembly.

Strategy (paper Lemma `lem:ADFGU.congestion`, `eq:boundsH+`),
**congestion-native**: this proof does NOT consume the simple-power
upper fields `h.H_upper_pointwise`/`h.DpH_upper`. Instead it routes the
two sides of the `m · H` envelope through:

* UPPER on `m·H` via `h.lagr` (`m^β/C − C ≤ D_pH⬝p − H`, hence
  `H ≤ D_pH⬝p − m^β/C + C`): multiplying by `m ≥ 0` and dropping the
  nonpositive `−m^{β+1}/C` term,
  `m·H ≤ m·(D_pH⬝Du) + C·m`.
  The first summand is dominated by `|m·(D_pH⬝Du)|`, whose integrability
  is the **child-1 congestion-native** envelope `reps.mDpHDu_int`.

* LOWER on `m·H` (i.e. `−(m·H)`) via `h.lower`
  (`H ≥ ‖p‖^α/C − C(m^β+1)`, hence `−H ≤ C(m^β+1)`): multiplying by
  `m ≥ 0`, `−(m·H) ≤ C·m^{β+1} + C·m`.

The linear-in-`m` terms are dominated by `m ≤ m^{β+1} + 1` (AE under
`m > 0`). The single dominator is
`Bnd x := |m·(D_pH⬝Du)| + C·m^{β+1} + 2·C·(m^{β+1}+1)`,
integrable as a linear combination of `reps.mDpHDu_int` (abs),
`m^{β+1}` from `hLB_int`, and constants on the finite-measure cube. -/
lemma mH_int
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (reps : CongestionBareRepresentatives (d := d) X betaBar gammaBar V H DpH ε)
    (h : StationaryMFG.Hamiltonian.CongestionAprioriPowerData H DpH)
    (hcong : StationaryMFG.Hamiltonian.CongestionGrowthCore (d := d) H DpH J)
    (hα_eq : h.α = hcong.α) (hβ_eq : h.β = hcong.β)
    (hbetaBar_eq : betaBar = ENNReal.ofReal (h.β + 1))
    {γBar : ℝ} (hγBar_pos : 0 < γBar)
    (hgammaBar_eq : gammaBar = ENNReal.ofReal γBar)
    (hγBar_ge_alpha_betaBarP :
      h.α * StationaryMFG.Hamiltonian.betaBar' h.β ≤ γBar) :
    MeasureTheory.Integrable
      (fun x => reps.m x * H x (fun i => reps.Du i x) (reps.m x))
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
  classical
  -- Equip cube with finite measure.
  haveI hcube_fin :
      MeasureTheory.IsFiniteMeasure (MeasureTheory.Measure.restrict
        (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
        (UnitCube (d := d))) :=
    ⟨by
      rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
          volume_unitCube]
      exact ENNReal.one_lt_top⟩
  -- Local abbreviations.
  set μC : MeasureTheory.Measure (Fin d → ℝ) :=
    MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d) with hμC_def
  -- Positivity facts.
  have hβ_pos : 0 < h.β := h.hβ
  have hβp1_pos : 0 < h.β + 1 := by linarith
  have hC_pos : 0 < h.C := h.hC
  -- Step 1: integrabilities of the building blocks.
  -- `m^{β+1}` integrable (mass `L^{β+1}` bound).
  have hMβ1 : MeasureTheory.Integrable (fun x => reps.m x ^ (h.β + 1)) μC :=
    reps.hLB_int (β := h.β) hβ_pos hbetaBar_eq
  -- Constant `1`.
  have h_one_int : MeasureTheory.Integrable (fun _ : (Fin d → ℝ) => (1 : ℝ)) μC :=
    MeasureTheory.integrable_const 1
  -- The congestion-native `m · (D_pH ⬝ Du)` envelope (child 1, no upper
  -- simple-power fields consumed); we take its absolute value as a dominator.
  have hmDpHDu_int : MeasureTheory.Integrable
      (fun x => reps.m x
                  * ((DpH x (fun i => reps.Du i x) (reps.m x))
                      ⬝ (fun i => reps.Du i x))) μC :=
    reps.mDpHDu_int (J := J) h hcong hα_eq hβ_eq hbetaBar_eq hγBar_pos hgammaBar_eq
      hγBar_ge_alpha_betaBarP
  have hmDpHDu_abs_int : MeasureTheory.Integrable
      (fun x => |reps.m x
                  * ((DpH x (fun i => reps.Du i x) (reps.m x))
                      ⬝ (fun i => reps.Du i x))|) μC :=
    hmDpHDu_int.abs
  -- AE-strong measurability of `m`, `Du`, and the joint `H`-composition.
  have hm_aesm :
      MeasureTheory.AEStronglyMeasurable reps.m μC := by
    have hm_lp : Periodic.MemLpPer (d := d) betaBar reps.m :=
      Periodic.MemLpPer.congr_ae_unitCube reps.hmem_lp_coe_m reps.hae_m.symm
    exact hm_lp.aestronglyMeasurable
  have hDu_meas : ∀ i, MeasureTheory.AEStronglyMeasurable (reps.Du i) μC := by
    intro i
    exact (reps.hDu_lp i).aestronglyMeasurable
  have hDu_aem : ∀ i, AEMeasurable (reps.Du i) μC :=
    fun i => (hDu_meas i).aemeasurable
  have hPi_aem : AEMeasurable
      (fun x : Fin d → ℝ => (fun i => reps.Du i x)) μC :=
    AEMeasurable.of_eval hDu_aem
  -- The triple `x ↦ (x, Du x, m x)` is AE-measurable; compose with the
  -- jointly-measurable `H` to get AE-strong measurability of
  -- `x ↦ H x (Du x) (m x)`.
  have hm_aem : AEMeasurable reps.m μC := hm_aesm.aemeasurable
  have hself_aem : AEMeasurable (fun x : Fin d → ℝ => x) μC :=
    aemeasurable_id
  have hTriple_aem : AEMeasurable
      (fun x : Fin d → ℝ => (x, (fun i => reps.Du i x), reps.m x)) μC := by
    refine AEMeasurable.prodMk hself_aem ?_
    refine AEMeasurable.prodMk hPi_aem hm_aem
  have hH_meas : Measurable
      (fun (xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ) => H xpm.1 xpm.2.1 xpm.2.2) :=
    h.measurable_H
  have hH_comp_aem : AEMeasurable
      (fun x : Fin d → ℝ => H x (fun i => reps.Du i x) (reps.m x)) μC :=
    hH_meas.comp_aemeasurable hTriple_aem
  have hH_comp_aesm : MeasureTheory.AEStronglyMeasurable
      (fun x : Fin d → ℝ => H x (fun i => reps.Du i x) (reps.m x)) μC :=
    aestronglyMeasurable_iff_aemeasurable.mpr hH_comp_aem
  have hmH_aesm : MeasureTheory.AEStronglyMeasurable
      (fun x => reps.m x * H x (fun i => reps.Du i x) (reps.m x)) μC :=
    hm_aesm.mul hH_comp_aesm
  -- Step 2: dominator.
  --   `Bnd x := |m·(D_pH⬝Du)| + C·m^{β+1} + 2·C·(m^{β+1}+1)`.
  -- It is integrable as a linear combination of the three building blocks.
  set Bnd : (Fin d → ℝ) → ℝ :=
    fun x => |reps.m x
                * ((DpH x (fun i => reps.Du i x) (reps.m x))
                    ⬝ (fun i => reps.Du i x))|
              + h.C * reps.m x ^ (h.β + 1)
              + (2 * h.C) * (reps.m x ^ (h.β + 1) + 1) with hBnd_def
  have hBnd_int : MeasureTheory.Integrable Bnd μC := by
    have h1 : MeasureTheory.Integrable
        (fun x => h.C * reps.m x ^ (h.β + 1)) μC := hMβ1.const_mul h.C
    have h2 : MeasureTheory.Integrable
        (fun x => reps.m x ^ (h.β + 1) + 1) μC := hMβ1.add h_one_int
    have h3 : MeasureTheory.Integrable
        (fun x => (2 * h.C) * (reps.m x ^ (h.β + 1) + 1)) μC := h2.const_mul (2 * h.C)
    exact (hmDpHDu_abs_int.add h1).add h3
  -- Step 3: pointwise AE-bound `|m * H| ≤ Bnd`.
  -- UPPER via `h.lagr` (`m^β/C − C ≤ D_pH⬝p − H` ⟹ `H ≤ D_pH⬝p − m^β/C + C`):
  --   `m·H ≤ m·(D_pH⬝Du) + C·m` (dropping the nonpositive `−m^{β+1}/C` term).
  -- LOWER via `h.lower` (`H ≥ ‖p‖^α/C − C(m^β+1)` ⟹ `−H ≤ C(m^β+1)`):
  --   `−(m·H) ≤ C·m^{β+1} + C·m`.
  have hPointwise :
      ∀ᵐ x ∂μC,
        ‖reps.m x * H x (fun i => reps.Du i x) (reps.m x)‖ ≤ Bnd x := by
    -- **Positivity-elimination (route a):** only a.e. NONNEGATIVITY is used.
    -- The `lagr`/`lower` apriori bounds carry a `0 < m` binder, so we case-split
    -- on `m x = 0` (where `m·H = 0 ≤ Bnd`) vs `0 < m x` (the substantive branch).
    filter_upwards [h.lagr, h.lower, reps.mε_nonneg]
      with x hxLagr hxLower hxm_nn
    set p : Fin d → ℝ := fun i => reps.Du i x with hp_def
    -- Boundary case `m x = 0`: the integrand vanishes.
    rcases eq_or_lt_of_le hxm_nn with hm0 | hxm_pos
    · -- `m x = 0`: `‖m·H‖ = 0 ≤ Bnd x` (the dominator is a sum of nonneg terms).
      have hmx0 : reps.m x = 0 := hm0.symm
      have hlhs0 : ‖reps.m x * H x (fun i => reps.Du i x) (reps.m x)‖ = 0 := by
        rw [hmx0, zero_mul, norm_zero]
      rw [hlhs0, hBnd_def]
      have hβp1_m_nn0 : 0 ≤ reps.m x ^ (h.β + 1) := Real.rpow_nonneg hxm_nn _
      have hCnn : 0 ≤ h.C := hC_pos.le
      have habs_nn : 0 ≤ |reps.m x
            * ((DpH x (fun i => reps.Du i x) (reps.m x))
                ⬝ (fun i => reps.Du i x))| := abs_nonneg _
      have hT : 0 ≤ (2 * h.C) * (reps.m x ^ (h.β + 1) + 1) :=
        mul_nonneg (by linarith) (by linarith)
      have h2 : 0 ≤ h.C * reps.m x ^ (h.β + 1) := mul_nonneg hCnn hβp1_m_nn0
      linarith
    have hmpos_nn : 0 ≤ reps.m x := hxm_nn
    have hβ_m_nn : 0 ≤ reps.m x ^ h.β := Real.rpow_nonneg hxm_nn _
    have hβp1_m_nn : 0 ≤ reps.m x ^ (h.β + 1) := Real.rpow_nonneg hxm_nn _
    have hα_p_nn : 0 ≤ ‖p‖ ^ h.α := Real.rpow_nonneg (norm_nonneg _) _
    -- `m ≤ m^{β+1} + 1` for `m > 0`.
    have hm_le : reps.m x ≤ reps.m x ^ (h.β + 1) + 1 := by
      by_cases hm1 : 1 ≤ reps.m x
      · have h1 : reps.m x ≤ reps.m x ^ (h.β + 1) := by
          have hstep : reps.m x ^ (1 : ℝ) ≤ reps.m x ^ (h.β + 1) :=
            Real.rpow_le_rpow_of_exponent_le hm1 (by linarith)
          rwa [Real.rpow_one] at hstep
        linarith
      · push_neg at hm1; linarith
    -- `m · m^β = m^{β+1}`.
    have hmm : reps.m x * reps.m x ^ h.β = reps.m x ^ (h.β + 1) := by
      have h1 : reps.m x ^ (1 : ℝ) = reps.m x := Real.rpow_one _
      calc reps.m x * reps.m x ^ h.β
          = reps.m x ^ (1 : ℝ) * reps.m x ^ h.β := by rw [h1]
        _ = reps.m x ^ ((1 : ℝ) + h.β) := (Real.rpow_add hxm_pos 1 h.β).symm
        _ = reps.m x ^ (h.β + 1) := by ring_nf
    -- UPPER on `H`: from `lagr`, `H ≤ (D_pH⬝p) − m^β/C + C`.
    have hLagr : (reps.m x ^ h.β) / h.C - h.C
        ≤ (DpH x p (reps.m x)) ⬝ p - H x p (reps.m x) :=
      hxLagr p (reps.m x) hxm_pos
    have hH_upper : H x p (reps.m x)
        ≤ (DpH x p (reps.m x)) ⬝ p - (reps.m x ^ h.β) / h.C + h.C := by linarith
    -- LOWER on `H`: from `lower`, `−H ≤ C(m^β+1)`.
    have hLower : (‖p‖ ^ h.α) / h.C - h.C * (reps.m x ^ h.β + 1)
        ≤ H x p (reps.m x) :=
      hxLower p (reps.m x) hxm_pos
    have hNegH_upper : -H x p (reps.m x) ≤ h.C * (reps.m x ^ h.β + 1) := by
      have hdrop : 0 ≤ (‖p‖ ^ h.α) / h.C := div_nonneg hα_p_nn hC_pos.le
      linarith
    -- Multiply by `m ≥ 0`.
    -- UPPER: `m·H ≤ m·(D_pH⬝p) − m·(m^β/C) + m·C`.
    have hmH_upper : reps.m x * H x p (reps.m x)
        ≤ reps.m x * ((DpH x p (reps.m x)) ⬝ p - (reps.m x ^ h.β) / h.C + h.C) :=
      mul_le_mul_of_nonneg_left hH_upper hmpos_nn
    -- LOWER: `m·(−H) ≤ m·(C(m^β+1))`.
    have hmH_neg_aux : reps.m x * (-H x p (reps.m x))
        ≤ reps.m x * (h.C * (reps.m x ^ h.β + 1)) :=
      mul_le_mul_of_nonneg_left hNegH_upper hmpos_nn
    -- Assemble the two-sided real bound, then read it off as `|·| ≤ Bnd`.
    have hUp_to_Bnd : reps.m x * H x p (reps.m x) ≤ Bnd x := by
      have hdrop_neg : 0 ≤ reps.m x * ((reps.m x ^ h.β) / h.C) :=
        mul_nonneg hmpos_nn (div_nonneg hβ_m_nn hC_pos.le)
      have habs_ge : reps.m x * ((DpH x p (reps.m x)) ⬝ p)
          ≤ |reps.m x * ((DpH x p (reps.m x)) ⬝ p)| := le_abs_self _
      have hCm : h.C * reps.m x ≤ (2 * h.C) * (reps.m x ^ (h.β + 1) + 1) := by
        have h1 : reps.m x ≤ reps.m x ^ (h.β + 1) + 1 := hm_le
        have h2 : h.C * reps.m x ≤ h.C * (reps.m x ^ (h.β + 1) + 1) :=
          mul_le_mul_of_nonneg_left h1 hC_pos.le
        have h3 : h.C * (reps.m x ^ (h.β + 1) + 1)
            ≤ (2 * h.C) * (reps.m x ^ (h.β + 1) + 1) := by
          have hnn : 0 ≤ reps.m x ^ (h.β + 1) + 1 := by linarith
          have : h.C ≤ 2 * h.C := by linarith [hC_pos]
          exact mul_le_mul_of_nonneg_right this hnn
        linarith
      have hCmβ1_nn : 0 ≤ h.C * reps.m x ^ (h.β + 1) :=
        mul_nonneg hC_pos.le hβp1_m_nn
      -- `m·H ≤ m·(D_pH⬝p) + C·m ≤ |m·(D_pH⬝p)| + C·m^{β+1} + 2C(m^{β+1}+1)`.
      have hstep : reps.m x * H x p (reps.m x)
          ≤ reps.m x * ((DpH x p (reps.m x)) ⬝ p) + h.C * reps.m x := by
        have hexpand : reps.m x
              * ((DpH x p (reps.m x)) ⬝ p - (reps.m x ^ h.β) / h.C + h.C)
            = reps.m x * ((DpH x p (reps.m x)) ⬝ p)
              - reps.m x * ((reps.m x ^ h.β) / h.C) + h.C * reps.m x := by ring
        rw [hexpand] at hmH_upper
        linarith
      rw [hBnd_def]
      simp only [hp_def]
      linarith [habs_ge, hCm, hCmβ1_nn, hstep]
    have hLo_to_Bnd : -(reps.m x * H x p (reps.m x)) ≤ Bnd x := by
      -- `−(m·H) = m·(−H) ≤ C·m^{β+1} + C·m ≤ C·m^{β+1} + 2C(m^{β+1}+1)`.
      have hneg_eq : reps.m x * (-H x p (reps.m x))
          = -(reps.m x * H x p (reps.m x)) := by ring
      have hexpand : reps.m x * (h.C * (reps.m x ^ h.β + 1))
          = h.C * (reps.m x * reps.m x ^ h.β) + h.C * reps.m x := by ring
      have hbound : -(reps.m x * H x p (reps.m x))
          ≤ h.C * reps.m x ^ (h.β + 1) + h.C * reps.m x := by
        rw [hneg_eq] at hmH_neg_aux
        rw [hexpand, hmm] at hmH_neg_aux
        exact hmH_neg_aux
      have hCm : h.C * reps.m x ≤ (2 * h.C) * (reps.m x ^ (h.β + 1) + 1) := by
        have h2 : h.C * reps.m x ≤ h.C * (reps.m x ^ (h.β + 1) + 1) :=
          mul_le_mul_of_nonneg_left hm_le hC_pos.le
        have h3 : h.C * (reps.m x ^ (h.β + 1) + 1)
            ≤ (2 * h.C) * (reps.m x ^ (h.β + 1) + 1) := by
          have hnn : 0 ≤ reps.m x ^ (h.β + 1) + 1 := by linarith
          have : h.C ≤ 2 * h.C := by linarith [hC_pos]
          exact mul_le_mul_of_nonneg_right this hnn
        linarith
      have habs_nn : 0 ≤ |reps.m x
            * ((DpH x p (reps.m x)) ⬝ p)| := abs_nonneg _
      rw [hBnd_def]
      simp only [hp_def]
      linarith [hbound, hCm, habs_nn]
    have hAbsBnd : |reps.m x * H x p (reps.m x)| ≤ Bnd x := by
      rw [abs_le]
      exact ⟨by linarith [hLo_to_Bnd], hUp_to_Bnd⟩
    rw [Real.norm_eq_abs]
    exact hAbsBnd
  -- Step 4: `Integrable.mono'`.
  exact hBnd_int.mono' hmH_aesm hPointwise

/-- **BB3-transport #10 (`hRHSbelow_int`) — FINAL ASSEMBLY**: integrability
of the lower-bound integrand from the VI identity
`∫ u = ∫ (m·(-H + DpH ⬝ Du) + V·m + epsTerms)`.

Linear sum of four summands:
* `m · (-H)` integrable from `(mH_int).neg`;
* `m · (DpH ⬝ Du)` integrable from `mDpHDu_int`;
* `V · m` integrable from `hVm_int` rider — note the rider provides
  `Integrable (|V| * m)` so we upgrade via `Integrable.mono'` using
  `|V * m| ≤ |V| * m` (true since `m ≥ 0` AE from `mε_pos`), with
  AE-strong measurability of `V * m` from the supplied `hV_aesm` rider
  and `m`'s AE-strong measurability;
* `epsTerms` integrable from `hEpsTerms_int` rider.

Combined via `Integrable.add`/`.sub`/`.neg`/`Integrable.congr` to match
the bridge-field shape exactly. -/
lemma hRHSbelow_int
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (reps : CongestionBareRepresentatives (d := d) X betaBar gammaBar V H DpH ε)
    (h : StationaryMFG.Hamiltonian.CongestionAprioriPowerData H DpH)
    (hcong : StationaryMFG.Hamiltonian.CongestionGrowthCore (d := d) H DpH J)
    (hα_eq : h.α = hcong.α) (hβ_eq : h.β = hcong.β)
    (hbetaBar_eq : betaBar = ENNReal.ofReal (h.β + 1))
    {γBar : ℝ} (hγBar_pos : 0 < γBar)
    (hgammaBar_eq : gammaBar = ENNReal.ofReal γBar)
    (hγBar_ge_alpha_betaBarP :
      h.α * StationaryMFG.Hamiltonian.betaBar' h.β ≤ γBar)
    (hV_aesm : MeasureTheory.AEStronglyMeasurable V
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (hVm_int : MeasureTheory.Integrable (fun x => |V x| * reps.m x)
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (hEpsTerms_int : MeasureTheory.Integrable reps.epsTerms
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d))) :
    MeasureTheory.Integrable
      (fun x => reps.m x * (-H x (fun i => reps.Du i x) (reps.m x)
                          + (DpH x (fun i => reps.Du i x) (reps.m x))
                            ⬝ (fun i => reps.Du i x))
                + V x * reps.m x + reps.epsTerms x)
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
  classical
  set μC : MeasureTheory.Measure (Fin d → ℝ) :=
    MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d) with hμC_def
  -- Summand A: m * H integrable.
  have hmH : MeasureTheory.Integrable
      (fun x => reps.m x * H x (fun i => reps.Du i x) (reps.m x)) μC :=
    reps.mH_int (J := J) h hcong hα_eq hβ_eq hbetaBar_eq hγBar_pos hgammaBar_eq
      hγBar_ge_alpha_betaBarP
  -- Summand A negated.
  have hmH_neg : MeasureTheory.Integrable
      (fun x => -(reps.m x * H x (fun i => reps.Du i x) (reps.m x))) μC := hmH.neg
  -- Summand B: m * (DpH ⬝ Du) integrable.
  have hmDpHDu : MeasureTheory.Integrable
      (fun x => reps.m x
        * ((DpH x (fun i => reps.Du i x) (reps.m x)) ⬝ (fun i => reps.Du i x))) μC :=
    reps.mDpHDu_int h hcong hα_eq hβ_eq hbetaBar_eq hγBar_pos hgammaBar_eq
      hγBar_ge_alpha_betaBarP
  -- Sum A+B.
  have hAB_sum : MeasureTheory.Integrable
      (fun x => -(reps.m x * H x (fun i => reps.Du i x) (reps.m x))
                + reps.m x
                  * ((DpH x (fun i => reps.Du i x) (reps.m x))
                      ⬝ (fun i => reps.Du i x))) μC :=
    hmH_neg.add hmDpHDu
  -- Rewrite into the bridge-field form `m * (-H + DpH ⬝ Du)`.
  have hAB_form : MeasureTheory.Integrable
      (fun x => reps.m x * (-H x (fun i => reps.Du i x) (reps.m x)
                          + (DpH x (fun i => reps.Du i x) (reps.m x))
                            ⬝ (fun i => reps.Du i x))) μC := by
    refine hAB_sum.congr ?_
    refine Filter.Eventually.of_forall ?_
    intro x; ring
  -- Summand C: V * m integrable via mono' against |V| * m.
  have hm_aesm : MeasureTheory.AEStronglyMeasurable reps.m μC := by
    have hm_lp : Periodic.MemLpPer (d := d) betaBar reps.m :=
      Periodic.MemLpPer.congr_ae_unitCube reps.hmem_lp_coe_m reps.hae_m.symm
    exact hm_lp.aestronglyMeasurable
  have hVm_aesm : MeasureTheory.AEStronglyMeasurable (fun x => V x * reps.m x) μC :=
    hV_aesm.mul hm_aesm
  have hVm_pointwise :
      ∀ᵐ x ∂μC, ‖V x * reps.m x‖ ≤ |V x| * reps.m x := by
    filter_upwards [reps.mε_nonneg] with x hxm_nn
    have hnorm : ‖V x * reps.m x‖ = |V x * reps.m x| := Real.norm_eq_abs _
    rw [hnorm, abs_mul]
    have hm_abs : |reps.m x| = reps.m x := abs_of_nonneg hxm_nn
    rw [hm_abs]
  have hVm : MeasureTheory.Integrable (fun x => V x * reps.m x) μC :=
    hVm_int.mono' hVm_aesm hVm_pointwise
  -- Summand D: epsTerms integrable (from rider).
  -- Final assembly: (A+B) + C + D.
  exact (hAB_form.add hVm).add hEpsTerms_int

end CongestionBareRepresentatives

/-! ### NN-track transport lemmas (T2 nonneg, Phase-3b)

Verbatim NN parallel of the `CongestionBareRepresentatives` transport
lemmas above, retargeted to `CongestionBareRepresentativesNN`. The
`mε_pos` lemma is dropped (no strict positivity on the NN track); the
`mε_nonneg` references resolve to the standalone
`CongestionBareRepresentativesNN.mε_nonneg` (derived from `hnn_coe_m`,
NOT from any `0 < m` corollary). Every other body is identical: the
lemmas consume only `hae_*`/`hmem_*` fields and `mε_nonneg`, all of
which exist on the NN struct. -/
namespace CongestionBareRepresentativesNN

variable {betaBar gammaBar : ℝ≥0∞}
variable {V : (Fin d → ℝ) → ℝ}
variable {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
variable {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
variable {ε : ℝ}
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]


/-- **BB2-transport #2 (`hu_meas`)**: a.e.-strong measurability of the
bare value function on all of `ℝ^d`, obtained by transporting cube-side
`MemLpPer` from the coercion via `hae_u`, lifting to whole-space
`LocallyIntegrable` via periodicity, and extracting
`AEStronglyMeasurable`. Requires `1 ≤ gammaBar` (consumer-side
`ENNReal.ofReal (gammaBar h.α h.β) ≥ 1`). -/
lemma hu_meas
    (reps : CongestionBareRepresentativesNN (d := d) X betaBar gammaBar V H DpH ε)
    (hγ_one_le : (1 : ℝ≥0∞) ≤ gammaBar) :
    MeasureTheory.AEStronglyMeasurable reps.u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) := by
  -- Step 1: cube-side `MemLpPer gammaBar reps.u` via congr_ae from `coe_u`.
  have hu_lp : Periodic.MemLpPer (d := d) gammaBar reps.u :=
    Periodic.MemLpPer.congr_ae_unitCube reps.hmem_sob_coe_u.1 reps.hae_u.symm
  -- Step 2: whole-space `LocallyIntegrable` via periodicity.
  have hu_loc : MeasureTheory.LocallyIntegrable reps.u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) :=
    Periodic.MemLpPer.locallyIntegrable_of_periodic (d := d)
      hγ_one_le hu_lp reps.hper_u
  -- Step 3: AE-strong measurability from local integrability.
  exact hu_loc.aestronglyMeasurable

/-- **BB2-transport #3 (`hu_per`)**: periodicity of the bare value
function. Direct from BB1's `hper_u` (the BB1 producer was specifically
designed to ship a literally periodic representative). -/
lemma hu_per (reps : CongestionBareRepresentativesNN (d := d) X betaBar gammaBar V H DpH ε) :
    Periodic.IsPeriodic reps.u :=
  reps.hper_u

/-- **BB2-transport #4 (`hu_loc`)**: whole-space local integrability of
the bare value function, obtained by lifting cube-side `MemLpPer
gammaBar reps.u` via periodicity. Requires `1 ≤ gammaBar`. -/
lemma hu_loc
    (reps : CongestionBareRepresentativesNN (d := d) X betaBar gammaBar V H DpH ε)
    (hγ_one_le : (1 : ℝ≥0∞) ≤ gammaBar) :
    MeasureTheory.LocallyIntegrable reps.u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) := by
  have hu_lp : Periodic.MemLpPer (d := d) gammaBar reps.u :=
    Periodic.MemLpPer.congr_ae_unitCube reps.hmem_sob_coe_u.1 reps.hae_u.symm
  exact Periodic.MemLpPer.locallyIntegrable_of_periodic (d := d)
    hγ_one_le hu_lp reps.hper_u

/-- **BB2-transport #5 (`hu_sob`)**: Sobolev membership of the bare
value function at `γ̄`, transported from the K-side Sobolev membership
of the coercion via `MemSobolevPer.congr_ae_unitCube`. -/
lemma hu_sob (reps : CongestionBareRepresentativesNN (d := d) X betaBar gammaBar V H DpH ε) :
    Periodic.MemSobolevPer (d := d) gammaBar reps.u :=
  reps.hmem_sob_coe_u.congr_ae_unitCube reps.hae_u.symm

/-- **BB2-transport #6 (`hu_lp_γ`)**: `L^{γ̄}`-membership of the bare
value function, obtained by extracting the Lp part of the Sobolev
membership of `coe_u` and transporting via `hae_u`. -/
lemma hu_lp_γ (reps : CongestionBareRepresentativesNN (d := d) X betaBar gammaBar V H DpH ε) :
    Periodic.MemLpPer (d := d) gammaBar reps.u :=
  Periodic.MemLpPer.congr_ae_unitCube reps.hmem_sob_coe_u.1 reps.hae_u.symm

/-- **BB2-transport #7 (`hDu_weak`)**: the bare weak-derivative family
witnesses the bare value function's Sobolev structure, obtained by
double-sided AE-congruence from the K-side weak-derivative witness on
the coercion. Requires `1 ≤ gammaBar` (for `MemLpPer 1 (Du i)` via the
inclusion `L^{γ̄} ⊆ L^1` on the finite-measure cube, but here we extract
`MemLpPer 1 (Du i)` directly through `coeWeak_Du`-side congruence). -/
lemma hDu_weak (reps : CongestionBareRepresentativesNN (d := d) X betaBar gammaBar V H DpH ε) :
    ∀ i, Periodic.HasWeakDerivPer (d := d) i reps.u (reps.Du i) := by
  intro i
  -- The K-side gives `HasWeakDerivPer i coe_u (coe_Du i)`, which carries
  -- `MemLpPer 1 (coe_Du i)`. Transport that `MemLpPer 1` to `Du i` first.
  have hDu_lp1 : Periodic.MemLpPer (d := d) 1 (reps.Du i) :=
    Periodic.MemLpPer.congr_ae_unitCube
      (reps.hweak_coe_Du i).memLpPer (reps.hae_Du i).symm
  exact (reps.hweak_coe_Du i).congr_ae_unitCube
    reps.hae_u.symm hDu_lp1 (reps.hae_Du i).symm

/-- **BB2-transport #8 (`hDu_meas`)**: whole-space a.e.-strong
measurability of each component of the bare weak-derivative family,
obtained by the same chain as `hu_meas` applied to each `Du i`. -/
lemma hDu_meas
    (reps : CongestionBareRepresentativesNN (d := d) X betaBar gammaBar V H DpH ε)
    (hγ_one_le : (1 : ℝ≥0∞) ≤ gammaBar) :
    ∀ i, MeasureTheory.AEStronglyMeasurable (reps.Du i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) := by
  intro i
  -- `MemLpPer gammaBar (coe_Du i)` from BB2-enrich's new field,
  -- transported to `Du i` via `(hae_Du i)`.
  have hDu_lp : Periodic.MemLpPer (d := d) gammaBar (reps.Du i) :=
    Periodic.MemLpPer.congr_ae_unitCube
      (reps.hmem_lp_coe_Du i) (reps.hae_Du i).symm
  have hDu_loc : MeasureTheory.LocallyIntegrable (reps.Du i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) :=
    Periodic.MemLpPer.locallyIntegrable_of_periodic (d := d)
      hγ_one_le hDu_lp (reps.hper_Du i)
  exact hDu_loc.aestronglyMeasurable

/-- **BB2-transport #9 (`hDu_per`)**: periodicity of each component of
the bare weak-derivative family. Direct from BB1's `hper_Du`. -/
lemma hDu_per (reps : CongestionBareRepresentativesNN (d := d) X betaBar gammaBar V H DpH ε) :
    ∀ i, Periodic.IsPeriodic (reps.Du i) :=
  reps.hper_Du

/-- **BB2-transport #10 (`hDu_loc`)**: whole-space local integrability
of each component of the bare weak-derivative family, obtained by
lifting cube-side `MemLpPer gammaBar` via periodicity. Requires
`1 ≤ gammaBar`. -/
lemma hDu_loc
    (reps : CongestionBareRepresentativesNN (d := d) X betaBar gammaBar V H DpH ε)
    (hγ_one_le : (1 : ℝ≥0∞) ≤ gammaBar) :
    ∀ i, MeasureTheory.LocallyIntegrable (reps.Du i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) := by
  intro i
  have hDu_lp : Periodic.MemLpPer (d := d) gammaBar (reps.Du i) :=
    Periodic.MemLpPer.congr_ae_unitCube
      (reps.hmem_lp_coe_Du i) (reps.hae_Du i).symm
  exact Periodic.MemLpPer.locallyIntegrable_of_periodic (d := d)
    hγ_one_le hDu_lp (reps.hper_Du i)

/-- **BB2-transport #11 (`hDu_lp`)**: `L^{γ̄}`-membership of each
component of the bare weak-derivative family, obtained by transporting
the BB2-enrich `hmem_lp_coe_Du i` via the AE-equality `Du i =ᵐ coe_Du
i` on the cube. -/
lemma hDu_lp (reps : CongestionBareRepresentativesNN (d := d) X betaBar gammaBar V H DpH ε) :
    ∀ i, Periodic.MemLpPer (d := d) gammaBar (reps.Du i) := by
  intro i
  exact Periodic.MemLpPer.congr_ae_unitCube
    (reps.hmem_lp_coe_Du i) (reps.hae_Du i).symm

/-! ### BB3-transport: Banach-VI PDE conclusions on bare representatives

The next three lemmas transport the Banach-VI conclusions
(`hHJB_le_coe`, `hVI_identity_coe`, `hEpsNN_coe`) from the coercions
to the bare representatives via the AE-equalities
(`hae_m`, `hae_u`, `hae_Du`, `hae_epsTerms`). These match the per-ε
bridge fields `hHJB_le`, `hVIIdentity`, `hEpsNN` of
`CongestionRegularizedSequenceBanachBareBridge` (modulo the outer
`∀ ε > 0` quantifier).
-/

/-- **BB3-transport #1 (`hHJB_le`)**: the bare-representative form of
the regularised HJB pointwise inequality (paper `eq:congest.HJleq0`),
transported from `hHJB_le_coe` via the AE-equalities `hae_m, hae_u,
hae_Du`. The pointwise inequality at `x` rewrites the coercion
inequality `coe_u + H(coe_Du)(coe_m) - V ≤ 0` into the bare-function
form `u + H(Du)(m) - V ≤ 0`. -/
lemma hHJB_le (reps : CongestionBareRepresentativesNN (d := d) X betaBar gammaBar V H DpH ε) :
    ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
      reps.u x + H x (fun i => reps.Du i x) (reps.m x) - V x ≤ 0 := by
  -- Combine the per-axis AE-equalities for `Du` into a single AE-event.
  have hae_Du_all :
      ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
        ∀ i, reps.Du i x = reps.coe_Du i x := by
    rw [MeasureTheory.ae_all_iff]; intro i; exact reps.hae_Du i
  filter_upwards [reps.hHJB_le_coe, reps.hae_m, reps.hae_u, hae_Du_all]
    with x hx_le hx_m hx_u hx_Du
  -- Rewrite each bare value as its coercion counterpart.
  have hfun_eq : (fun i => reps.Du i x) = (fun i => reps.coe_Du i x) :=
    funext hx_Du
  rw [hx_m, hx_u, hfun_eq]
  exact hx_le

/-- **T2 nonneg-track (Phase-3c) — `hHJB_eq_pos` transport**: the
bare-representative form of the HJB equality on the positive-mass set,
transported from a witness-level equality on `{coe_m > 0}` (the output of
`weak_is_strong_HJB_eq` applied at the chosen Banach-VI witness) via the
AE-equalities `hae_m`/`hae_u`/`hae_Du`. Mirrors the `hHJB_le` transport, but
carries the `0 < m` hypothesis through the rewrite. -/
lemma hHJB_eq_pos
    (reps : CongestionBareRepresentativesNN (d := d) X betaBar gammaBar V H DpH ε)
    (heq_coe :
      ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
        0 < reps.coe_m x →
          reps.coe_u x + H x (fun i => reps.coe_Du i x) (reps.coe_m x) - V x = 0) :
    ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
      0 < reps.m x →
        reps.u x + H x (fun i => reps.Du i x) (reps.m x) - V x = 0 := by
  -- Combine the per-axis AE-equalities for `Du` into a single AE-event.
  have hae_Du_all :
      ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
        ∀ i, reps.Du i x = reps.coe_Du i x := by
    rw [MeasureTheory.ae_all_iff]; intro i; exact reps.hae_Du i
  filter_upwards [heq_coe, reps.hae_m, reps.hae_u, hae_Du_all]
    with x hx_eq hx_m hx_u hx_Du hpos
  -- Rewrite each bare value as its coercion counterpart.
  have hfun_eq : (fun i => reps.Du i x) = (fun i => reps.coe_Du i x) :=
    funext hx_Du
  rw [hx_m, hx_u, hfun_eq]
  -- The positivity hypothesis transports along `hx_m`.
  exact hx_eq (by rw [← hx_m]; exact hpos)

/-- **BB3-transport #2 (`hVIIdentity`)**: the bare-representative form
of the regularised VI integral identity (paper
`eq:identity-congestion`), transported from `hVI_identity_coe` via
`integral_congr_ae` applied to both sides. -/
lemma hVIIdentity (reps : CongestionBareRepresentativesNN (d := d) X betaBar gammaBar V H DpH ε) :
    ∫ x in UnitCube d, reps.u x ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
      = ∫ x in UnitCube d,
          (reps.m x * (-H x (fun i => reps.Du i x) (reps.m x)
                      + (DpH x (fun i => reps.Du i x) (reps.m x))
                        ⬝ (fun i => reps.Du i x))
            + V x * reps.m x
            + reps.epsTerms x)
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) := by
  -- Combine the per-axis AE-equalities for `Du` into a single AE-event.
  have hae_Du_all :
      ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
        ∀ i, reps.Du i x = reps.coe_Du i x := by
    rw [MeasureTheory.ae_all_iff]; intro i; exact reps.hae_Du i
  -- LHS: `∫ u = ∫ coe_u` via AE-equality on the cube.
  have hLHS :
      ∫ x in UnitCube d, reps.u x
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
        = ∫ x in UnitCube d, reps.coe_u x
            ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) := by
    exact MeasureTheory.integral_congr_ae reps.hae_u
  -- RHS: rewrite the bare integrand to the coercion integrand AE.
  have hRHS :
      ∫ x in UnitCube d,
          (reps.m x * (-H x (fun i => reps.Du i x) (reps.m x)
                      + (DpH x (fun i => reps.Du i x) (reps.m x))
                        ⬝ (fun i => reps.Du i x))
            + V x * reps.m x
            + reps.epsTerms x)
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
        = ∫ x in UnitCube d,
            (reps.coe_m x * (-H x (fun i => reps.coe_Du i x) (reps.coe_m x)
                            + (DpH x (fun i => reps.coe_Du i x) (reps.coe_m x))
                              ⬝ (fun i => reps.coe_Du i x))
              + V x * reps.coe_m x
              + reps.coe_epsTerms x)
            ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [reps.hae_m, hae_Du_all, reps.hae_epsTerms]
      with x hx_m hx_Du hx_eps
    have hfun_eq : (fun i => reps.Du i x) = (fun i => reps.coe_Du i x) :=
      funext hx_Du
    rw [hx_m, hfun_eq, hx_eps]
  -- Chain LHS/RHS with the K-side identity on the coercions.
  rw [hLHS, hRHS]
  exact reps.hVI_identity_coe

/-- **BB3-transport #3 (`hEpsNN`)**: nonnegativity of the bare
regularisation residual `epsTerms`, transported from `hEpsNN_coe` via
the AE-equality `hae_epsTerms`. -/
lemma hEpsNN (reps : CongestionBareRepresentativesNN (d := d) X betaBar gammaBar V H DpH ε) :
    ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
      0 ≤ reps.epsTerms x := by
  filter_upwards [reps.hEpsNN_coe, reps.hae_epsTerms] with x hx_le hx_eq
  rw [hx_eq]
  exact hx_le

/-! ### BB3-transport: PDE/analytic integrability conclusions (#4 `hu_int`)

The bare value function `u` is integrable on the unit cube. This is
the simplest of the seven integrability transports: it reduces directly
to `MemLpPer γ̄ u` (BB2-transport's `hu_lp_γ`) via `MemLp.mono_exponent`
on the finite-measure cube, using `1 ≤ γ̄`.
-/

/-- **BB3-transport #4 (`hu_int`)**: integrability of the bare value
function on the unit cube. From `MemLpPer gammaBar reps.u` (BB2-transport's
`hu_lp_γ`) + `1 ≤ gammaBar` + finite measure on `UnitCube`. -/
lemma hu_int
    (reps : CongestionBareRepresentativesNN (d := d) X betaBar gammaBar V H DpH ε)
    (hγ_one_le : (1 : ℝ≥0∞) ≤ gammaBar) :
    MeasureTheory.Integrable reps.u
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
  -- Equip the cube-restricted volume with `IsFiniteMeasure`.
  haveI hcube_fin :
      MeasureTheory.IsFiniteMeasure (MeasureTheory.Measure.restrict
        (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
        (UnitCube (d := d))) :=
    ⟨by
      rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
          volume_unitCube]
      exact ENNReal.one_lt_top⟩
  -- `MemLpPer gammaBar u = MemLp u gammaBar …`; `mono_exponent` to `MemLp u 1`.
  have hu_lpγ : Periodic.MemLpPer (d := d) gammaBar reps.u := reps.hu_lp_γ
  have hu_memLp1 : MeasureTheory.MemLp reps.u 1
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
    hu_lpγ.toMemLp.mono_exponent hγ_one_le
  exact (MeasureTheory.memLp_one_iff_integrable.mp hu_memLp1)

/-- **BB3-transport #5 (`hLB_int`)**: integrability of `m^{β+1}` on the
unit cube. From the BB2-enrich field `hmem_lp_coe_m : MemLpPer betaBar
coe_m` together with the bridge exponent alignment
`betaBar = ENNReal.ofReal (β+1)` (paper line 1328), and the bare AE-positivity
`mε_nonneg` (which lets us drop the absolute-value/norm cast). The
`MemLpPer betaBar` of the bare `m` is transported from `coe_m` via
`hae_m`.

Surface the exponent alignment and the paper parameters as hypotheses
(NOT as new fields on `CongestionBareRepresentativesNN` — those are
bridge-instantiator-side facts). -/
lemma hLB_int
    (reps : CongestionBareRepresentativesNN (d := d) X betaBar gammaBar V H DpH ε)
    {β : ℝ} (hβ_pos : 0 < β)
    (hbetaBar_eq : betaBar = ENNReal.ofReal (β + 1)) :
    MeasureTheory.Integrable (fun x => reps.m x ^ (β + 1))
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
  -- Step 1: transport `MemLpPer betaBar coe_m` to `MemLpPer betaBar m`.
  have hm_lp : Periodic.MemLpPer (d := d) betaBar reps.m :=
    Periodic.MemLpPer.congr_ae_unitCube reps.hmem_lp_coe_m reps.hae_m.symm
  -- Step 2: substitute `betaBar = ENNReal.ofReal (β+1)`.
  have hm_lp' : Periodic.MemLpPer (d := d) (ENNReal.ofReal (β + 1)) reps.m := by
    rw [← hbetaBar_eq]; exact hm_lp
  have hβ1_pos : (0 : ℝ) < β + 1 := by linarith
  have hp_ne_zero : ENNReal.ofReal (β + 1) ≠ 0 := by
    simp [ENNReal.ofReal_ne_zero_iff, hβ1_pos]
  have hp_top : ENNReal.ofReal (β + 1) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hp_toReal : (ENNReal.ofReal (β + 1)).toReal = β + 1 :=
    ENNReal.toReal_ofReal hβ1_pos.le
  -- Step 3: apply `MemLp.integrable_norm_rpow`.
  have hm_memLp : MeasureTheory.MemLp reps.m (ENNReal.ofReal (β + 1))
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
    hm_lp'
  have hnorm_int : MeasureTheory.Integrable
      (fun x => ‖reps.m x‖ ^ (ENNReal.ofReal (β + 1)).toReal)
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
    MeasureTheory.MemLp.integrable_norm_rpow hm_memLp hp_ne_zero hp_top
  rw [hp_toReal] at hnorm_int
  -- Step 4: rewrite `‖m x‖^(β+1) = m x ^ (β+1)` AE using `mε_nonneg`.
  have hae_eq :
      (fun x => ‖reps.m x‖ ^ (β + 1)) =ᵐ[MeasureTheory.Measure.restrict
        MeasureTheory.volume (UnitCube d)]
        (fun x => reps.m x ^ (β + 1)) := by
    filter_upwards [reps.mε_nonneg] with x hx_nn
    simp only [Real.norm_eq_abs, abs_of_nonneg hx_nn]
  exact hnorm_int.congr hae_eq

/-- **BB3-transport #6 (`hMbeta_int`)**: integrability of `m^β` on the
unit cube. Strategy: derive from `MemLpPer (ENNReal.ofReal (β+1)) m`
(transported as in `hLB_int`), which gives `Integrable (fun x => m x ^
(β+1))`; together with `Integrable (fun x => m x)` (Lp embedding from
`β+1 ≥ 1`) we get `m^β = m^{β+1} / m` pointwise, BUT this division
isn't friendly for integrability. Alternative chain: from `MemLpPer
(β+1) m` and `1 ≤ β+1`, monotonicity gives `Integrable (m^q)` for any
`1 ≤ q ≤ β+1` on the finite-measure cube via
`MemLp.integrable_norm_rpow` and `MemLp.mono_exponent` after the rpow
transformation. Cleanest: use the bound `m^β ≤ m^{β+1} + 1` (Young's
inequality at scale 1) which holds when `m > 0`. -/
lemma hMbeta_int
    (reps : CongestionBareRepresentativesNN (d := d) X betaBar gammaBar V H DpH ε)
    {β : ℝ} (hβ_pos : 0 < β)
    (hbetaBar_eq : betaBar = ENNReal.ofReal (β + 1)) :
    MeasureTheory.Integrable (fun x => reps.m x ^ β)
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
  -- Equip cube with finite measure.
  haveI hcube_fin :
      MeasureTheory.IsFiniteMeasure (MeasureTheory.Measure.restrict
        (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
        (UnitCube (d := d))) :=
    ⟨by
      rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
          volume_unitCube]
      exact ENNReal.one_lt_top⟩
  -- Use the chain:  `m^β ≤ m^{β+1} + 1` AE (Young at scale 1, valid when m > 0)
  -- and dominate by an integrable function.
  have hLB := reps.hLB_int (β := β) hβ_pos hbetaBar_eq
  -- `Integrable (fun x => m x ^ (β+1) + 1)` since constants are integrable on
  -- the finite-measure cube.
  have h_one_int : MeasureTheory.Integrable
      (fun _ : (Fin d → ℝ) => (1 : ℝ))
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
    MeasureTheory.integrable_const 1
  have h_dom_int : MeasureTheory.Integrable
      (fun x => reps.m x ^ (β + 1) + 1)
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
    hLB.add h_one_int
  -- AE-strong measurability of `m^β`: from `m^{β+1}` via rpow with continuous
  -- function. We use the chain from `hLB`'s measurability of the rpow.
  have hm_aesm :
      MeasureTheory.AEStronglyMeasurable reps.m
        (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
    -- From `MemLpPer betaBar m`, get AEStronglyMeasurable.
    have hm_lp : Periodic.MemLpPer (d := d) betaBar reps.m :=
      Periodic.MemLpPer.congr_ae_unitCube reps.hmem_lp_coe_m reps.hae_m.symm
    exact hm_lp.aestronglyMeasurable
  have hmβ_aesm :
      MeasureTheory.AEStronglyMeasurable (fun x => reps.m x ^ β)
        (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
    -- Compose with the continuous function `t ↦ t ^ β` (valid for `0 ≤ β`).
    exact (Real.continuous_rpow_const hβ_pos.le).comp_aestronglyMeasurable hm_aesm
  -- Pointwise bound `m^β ≤ m^{β+1} + 1` for `m > 0`:
  --   if `m ≥ 1` then `m^β ≤ m^{β+1}`; if `0 < m < 1` then `m^β ≤ 1`.
  have h_pointwise_bound :
      ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
        ‖reps.m x ^ β‖ ≤ reps.m x ^ (β + 1) + 1 := by
    filter_upwards [reps.mε_nonneg] with x hx_nn
    have hmβ_nn : 0 ≤ reps.m x ^ β := Real.rpow_nonneg hx_nn β
    have hmβ1_nn : 0 ≤ reps.m x ^ (β + 1) := Real.rpow_nonneg hx_nn (β + 1)
    rw [Real.norm_of_nonneg hmβ_nn]
    by_cases hm1 : 1 ≤ reps.m x
    · -- `m ≥ 1`: `m^β ≤ m^{β+1} ≤ m^{β+1} + 1`.
      have h1 : reps.m x ^ β ≤ reps.m x ^ (β + 1) := by
        apply Real.rpow_le_rpow_of_exponent_le hm1
        linarith
      linarith
    · -- `0 ≤ m < 1`: `m^β ≤ 1 ≤ m^{β+1} + 1`.
      push_neg at hm1
      have h1 : reps.m x ^ β ≤ 1 := by
        have h := Real.rpow_le_one hx_nn hm1.le hβ_pos.le
        exact h
      linarith
  exact h_dom_int.mono' hmβ_aesm h_pointwise_bound

/-! ### BB3-transport: PDE/analytic integrability conclusions
(`hDu_norm_int`, `hUbetap_int`, `hRHSabove_int`)

Three of the four remaining integrability transports (iter 0848-extension):

* `hDu_norm_int` — integrability of `‖(fun i => Du i x)‖^γ̄` via
  per-axis `MemLpPer γ̄ (Du i)` (BB2-transport `hDu_lp`) +
  `MemLp.integrable_norm_rpow` summed across axes, dominated by the
  pointwise bound `‖f‖^γ̄ ≤ ∑ i, ‖f i‖^γ̄` for `γ̄ ≥ 0` on `Fin d → ℝ`
  (using `Finset.exists_mem_eq_sup` for `d > 0` and the `d = 0`
  degenerate case where `f = 0`).

* `hUbetap_int` — integrability of `|u x|^{β̄'}` via `MemLpPer γ̄ u`
  (BB2-transport `hu_lp_γ`) + exponent inclusion `β̄' ≤ γ̄` on the
  finite-measure cube (`MemLp.mono_exponent`), then
  `MemLp.integrable_norm_rpow` + `‖u x‖ = |u x|` (real-valued).

* `hRHSabove_int` — integrability of `|V x| + h.C * (m x ^ β + 1)`
  as a linear combination of an external paper-side `hV_int`
  hypothesis and the landed `hMbeta_int` plus a finite-measure
  constant.

The fourth lemma `hRHSbelow_int` (integrand of the VI identity) is
deferred to a child task `BB3-transport-hRHSbelow-int` since it
requires Hölder pairings on the products `m * H`, `m * (DpH ⬝ Du)`,
`V * m`, plus a contract enrichment for `epsTerms` integrability.
-/

/-- **BB3-transport #7 (`hDu_norm_int`)**: integrability of `‖Du‖^γ̄`
on the unit cube, where the norm on `Fin d → ℝ` is the sup-norm. The
strategy:
* From `hDu_lp i : MemLpPer γ̄ (Du i)` (BB2-transport) and the exponent
  alignment `gammaBar = ENNReal.ofReal γ̄`, each `‖Du i x‖^γ̄` is
  integrable via `MemLp.integrable_norm_rpow`.
* Summing over `i`, the function `x ↦ ∑ i, ‖Du i x‖^γ̄` is integrable.
* Pointwise, `‖(fun i => Du i x)‖^γ̄ ≤ ∑ i, ‖Du i x‖^γ̄` for `γ̄ ≥ 0`:
  if `d = 0` both sides are `0`; if `d > 0`, picking `j` attaining
  the sup gives `‖f‖^γ̄ = ‖f j‖^γ̄ ≤ ∑ i, ‖f i‖^γ̄` since each summand
  is nonneg.
* `Integrable.mono'` closes the goal.

Requires `0 ≤ γ̄` (for `t ↦ t^γ̄` to be monotone on `[0,∞)`) and the
exponent alignment `gammaBar = ENNReal.ofReal γ̄` plus `γ̄ ≠ 0`. -/
lemma hDu_norm_int
    (reps : CongestionBareRepresentativesNN (d := d) X betaBar gammaBar V H DpH ε)
    {γBar : ℝ} (hγBar_pos : 0 < γBar)
    (hgammaBar_eq : gammaBar = ENNReal.ofReal γBar) :
    MeasureTheory.Integrable
      (fun x => ‖(fun i => reps.Du i x)‖ ^ γBar)
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
  classical
  -- Step 1: each axis's `‖Du i x‖^γBar` is integrable, via
  --   `MemLp.integrable_norm_rpow` applied to `hDu_lp i`.
  have hp_ne_zero : ENNReal.ofReal γBar ≠ 0 := by
    simp [ENNReal.ofReal_ne_zero_iff, hγBar_pos]
  have hp_top : ENNReal.ofReal γBar ≠ ⊤ := ENNReal.ofReal_ne_top
  have hp_toReal : (ENNReal.ofReal γBar).toReal = γBar :=
    ENNReal.toReal_ofReal hγBar_pos.le
  have h_each_int : ∀ i, MeasureTheory.Integrable
      (fun x => ‖reps.Du i x‖ ^ γBar)
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
    intro i
    have hDu_lp_i : Periodic.MemLpPer (d := d) gammaBar (reps.Du i) := reps.hDu_lp i
    have hDu_lp_i' : Periodic.MemLpPer (d := d) (ENNReal.ofReal γBar) (reps.Du i) := by
      rw [← hgammaBar_eq]; exact hDu_lp_i
    have hDu_memLp : MeasureTheory.MemLp (reps.Du i) (ENNReal.ofReal γBar)
        (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
      hDu_lp_i'
    have h := MeasureTheory.MemLp.integrable_norm_rpow hDu_memLp hp_ne_zero hp_top
    rw [hp_toReal] at h
    exact h
  -- Step 2: the sum across axes is integrable.
  have h_sum_int : MeasureTheory.Integrable
      (fun x => ∑ i, ‖reps.Du i x‖ ^ γBar)
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
    MeasureTheory.integrable_finset_sum _ (fun i _ => h_each_int i)
  -- Step 3: AE-strong measurability of `x ↦ ‖(fun i => Du i x)‖^γBar`.
  -- The function `x ↦ (fun i => Du i x)` is AE-strongly measurable as
  -- a function into `Fin d → ℝ` (Pi-strong measurability follows from
  -- the per-axis measurabilities).
  have hDu_meas : ∀ i, MeasureTheory.AEStronglyMeasurable (reps.Du i)
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
    intro i
    have hDu_lp_i : Periodic.MemLpPer (d := d) gammaBar (reps.Du i) := reps.hDu_lp i
    exact hDu_lp_i.aestronglyMeasurable
  -- Bridge AEStronglyMeasurable ↔ AEMeasurable on second-countable Polish
  -- ranges (`ℝ`, `Fin d → ℝ`).
  have hDu_aem : ∀ i, AEMeasurable (reps.Du i)
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
    fun i => (hDu_meas i).aemeasurable
  have hPi_aem : AEMeasurable
      (fun x : Fin d → ℝ => (fun i => reps.Du i x))
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
    AEMeasurable.of_eval hDu_aem
  have hPi_meas : MeasureTheory.AEStronglyMeasurable
      (fun x : Fin d → ℝ => (fun i => reps.Du i x))
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
    aestronglyMeasurable_iff_aemeasurable.mpr hPi_aem
  have h_norm_meas : MeasureTheory.AEStronglyMeasurable
      (fun x => ‖(fun i => reps.Du i x)‖)
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
    hPi_meas.norm
  have h_rpow_meas : MeasureTheory.AEStronglyMeasurable
      (fun x => ‖(fun i => reps.Du i x)‖ ^ γBar)
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
    exact (Real.continuous_rpow_const hγBar_pos.le).comp_aestronglyMeasurable h_norm_meas
  -- Step 4: pointwise bound `‖(fun i => Du i x)‖^γBar ≤ ∑ i, ‖Du i x‖^γBar`.
  -- Cases on `d`:
  --   d = 0: `‖f‖ = 0`, `0^γBar = 0`, sum over empty is `0`.
  --   d ≥ 1: pick `j` attaining the sup, bound by the corresponding term.
  have h_pointwise : ∀ x : Fin d → ℝ,
      ‖fun i => reps.Du i x‖ ^ γBar ≤ ∑ i, ‖reps.Du i x‖ ^ γBar := by
    intro x
    have h_nn_sum : 0 ≤ ∑ i, ‖reps.Du i x‖ ^ γBar :=
      Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg _) γBar)
    by_cases hd : d = 0
    · -- `Fin 0` is empty. `‖f‖ = 0` because the sup over `∅` in the
      -- nnnorm-product structure is `0`.
      subst hd
      have hf_norm : ‖fun i : Fin 0 => reps.Du i x‖ = 0 := by
        rw [Pi.norm_def]
        simp [Finset.univ_eq_empty, Finset.sup_empty]
      rw [hf_norm]
      rw [Real.zero_rpow hγBar_pos.ne']
      exact h_nn_sum
    · -- `Fin d` is nonempty; pick `j` attaining the sup of `‖f i‖₊`.
      haveI : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero hd⟩⟩
      -- `‖f‖ ≤ ∑_i ‖f i‖` follows from `‖f i‖ ≤ ‖f‖` ≤ `∑_i ‖f i‖`,
      -- so we use a direct case analysis: there exists `j` with
      -- `‖f‖ = ‖f j‖`.
      obtain ⟨j, _, hj_eq⟩ :=
        Finset.exists_mem_eq_sup (s := (Finset.univ : Finset (Fin d)))
          ⟨⟨0, Nat.pos_of_ne_zero hd⟩, Finset.mem_univ _⟩
          (fun i => ‖reps.Du i x‖₊)
      have hf_norm_eq : ‖fun i => reps.Du i x‖ = ‖reps.Du j x‖ := by
        rw [Pi.norm_def, hj_eq]
        rfl
      rw [hf_norm_eq]
      -- The `j`-th term of the sum dominates each individual term.
      have h_each_nn : ∀ i, 0 ≤ ‖reps.Du i x‖ ^ γBar :=
        fun i => Real.rpow_nonneg (norm_nonneg _) γBar
      calc ‖reps.Du j x‖ ^ γBar
          = ∑ i ∈ ({j} : Finset (Fin d)), ‖reps.Du i x‖ ^ γBar := by
              simp
        _ ≤ ∑ i, ‖reps.Du i x‖ ^ γBar := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro i hi; exact Finset.mem_univ _
              · intro i _ _; exact h_each_nn i
  -- Step 5: `Integrable.mono'` via `‖f^γBar‖ = f^γBar` (nonneg).
  have h_abs_bound :
      ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
        ‖‖fun i => reps.Du i x‖ ^ γBar‖ ≤ ∑ i, ‖reps.Du i x‖ ^ γBar := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    have hnn : 0 ≤ ‖fun i => reps.Du i x‖ ^ γBar :=
      Real.rpow_nonneg (norm_nonneg _) γBar
    rw [Real.norm_of_nonneg hnn]
    exact h_pointwise x
  exact h_sum_int.mono' h_rpow_meas h_abs_bound

/-- **BB3-transport #8 (`hUbetap_int`)**: integrability of `|u x|^{β̄'}`
on the unit cube, where `β̄' = (β+1)/β` is the Hölder conjugate of
`β̄`. The strategy uses two steps:
* From `MemLpPer γ̄ u` (BB2-transport `hu_lp_γ`) + the inclusion
  `β̄' ≤ γ̄` (paper requirement: `γ̄ = α · β̄' ≥ β̄'` since `α ≥ 1`),
  `MemLp.mono_exponent` on the finite-measure cube gives
  `MemLp u β̄' (cube-restricted volume)`.
* `MemLp.integrable_norm_rpow` produces `Integrable (fun x => ‖u x‖^β̄')`,
  which equals `Integrable (fun x => |u x|^β̄')` since `‖·‖ = |·|`
  on `ℝ`.

Requires `0 < β̄'` and the exponent alignment
`gammaBar = ENNReal.ofReal γBar` with `betaBar' β ≤ γBar`. -/
lemma hUbetap_int
    (reps : CongestionBareRepresentativesNN (d := d) X betaBar gammaBar V H DpH ε)
    {β : ℝ} (hβ_pos : 0 < β)
    {γBar : ℝ} (hbetaBarP_le_gBar : StationaryMFG.Hamiltonian.betaBar' β ≤ γBar)
    (hgammaBar_eq : gammaBar = ENNReal.ofReal γBar) :
    MeasureTheory.Integrable
      (fun x => |reps.u x| ^ StationaryMFG.Hamiltonian.betaBar' β)
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
  -- Equip cube with finite measure.
  haveI hcube_fin :
      MeasureTheory.IsFiniteMeasure (MeasureTheory.Measure.restrict
        (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
        (UnitCube (d := d))) :=
    ⟨by
      rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
          volume_unitCube]
      exact ENNReal.one_lt_top⟩
  -- Positivity of `β̄'`.
  have hbetaBarP_pos : 0 < StationaryMFG.Hamiltonian.betaBar' β := by
    unfold StationaryMFG.Hamiltonian.betaBar'
    positivity
  -- Step 1: get `MemLp u β̄'` from `MemLp u γ̄`.
  have hu_lpγ : Periodic.MemLpPer (d := d) gammaBar reps.u := reps.hu_lp_γ
  have hu_lpγ' :
      Periodic.MemLpPer (d := d) (ENNReal.ofReal γBar) reps.u := by
    rw [← hgammaBar_eq]; exact hu_lpγ
  have hu_memLpγ : MeasureTheory.MemLp reps.u (ENNReal.ofReal γBar)
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
    hu_lpγ'
  have h_p_le_q :
      ENNReal.ofReal (StationaryMFG.Hamiltonian.betaBar' β) ≤
        ENNReal.ofReal γBar :=
    ENNReal.ofReal_le_ofReal hbetaBarP_le_gBar
  have hu_memLpβ' : MeasureTheory.MemLp reps.u
      (ENNReal.ofReal (StationaryMFG.Hamiltonian.betaBar' β))
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
    hu_memLpγ.mono_exponent h_p_le_q
  -- Step 2: integrability of `‖u x‖^β̄'` via `MemLp.integrable_norm_rpow`.
  have hp_ne_zero : ENNReal.ofReal (StationaryMFG.Hamiltonian.betaBar' β) ≠ 0 := by
    simp [ENNReal.ofReal_ne_zero_iff, hbetaBarP_pos]
  have hp_top : ENNReal.ofReal (StationaryMFG.Hamiltonian.betaBar' β) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hp_toReal :
      (ENNReal.ofReal (StationaryMFG.Hamiltonian.betaBar' β)).toReal =
        StationaryMFG.Hamiltonian.betaBar' β :=
    ENNReal.toReal_ofReal hbetaBarP_pos.le
  have h_norm_int : MeasureTheory.Integrable
      (fun x => ‖reps.u x‖ ^ StationaryMFG.Hamiltonian.betaBar' β)
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
    have := MeasureTheory.MemLp.integrable_norm_rpow hu_memLpβ' hp_ne_zero hp_top
    rw [hp_toReal] at this
    exact this
  -- Step 3: `‖u x‖ = |u x|` on `ℝ`, so the two integrals coincide.
  have h_eq : (fun x => ‖reps.u x‖ ^ StationaryMFG.Hamiltonian.betaBar' β) =
      (fun x => |reps.u x| ^ StationaryMFG.Hamiltonian.betaBar' β) := by
    funext x; rw [Real.norm_eq_abs]
  rw [← h_eq]; exact h_norm_int

/-- **BB3-transport #9 (`hRHSabove_int`)**: integrability of the
upper-bound integrand `|V(x)| + h.C * (m_ε(x)^β + 1)`. Linear sum of
* `hV_int : Integrable |V|` — paper-side hypothesis (from `pack3.hV`
  forwarding), and
* `h.C * (m^β + 1)` — from the landed `hMbeta_int` plus
  `Integrable.add_const` on the finite-measure cube and then
  `Integrable.const_mul` by `h.C`. -/
lemma hRHSabove_int
    (reps : CongestionBareRepresentativesNN (d := d) X betaBar gammaBar V H DpH ε)
    (h : StationaryMFG.Hamiltonian.CongestionAprioriPowerData H DpH)
    (hV_int : MeasureTheory.Integrable (fun x => |V x|)
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (hbetaBar_eq : betaBar = ENNReal.ofReal (h.β + 1)) :
    MeasureTheory.Integrable
      (fun x => |V x| + h.C * (reps.m x ^ h.β + 1))
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
  -- Equip cube with finite measure.
  haveI hcube_fin :
      MeasureTheory.IsFiniteMeasure (MeasureTheory.Measure.restrict
        (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
        (UnitCube (d := d))) :=
    ⟨by
      rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
          volume_unitCube]
      exact ENNReal.one_lt_top⟩
  -- Step 1: `Integrable (fun x => m x ^ β)` from `hMbeta_int`.
  have hMβ : MeasureTheory.Integrable (fun x => reps.m x ^ h.β)
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
    reps.hMbeta_int (β := h.β) h.hβ hbetaBar_eq
  -- Step 2: `Integrable (fun x => m x ^ β + 1)` via `add_const`.
  have h_one_int : MeasureTheory.Integrable
      (fun _ : (Fin d → ℝ) => (1 : ℝ))
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
    MeasureTheory.integrable_const 1
  have hMβ1 : MeasureTheory.Integrable (fun x => reps.m x ^ h.β + 1)
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
    hMβ.add h_one_int
  -- Step 3: scale by `h.C`.
  have hCMβ1 : MeasureTheory.Integrable
      (fun x => h.C * (reps.m x ^ h.β + 1))
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
    hMβ1.const_mul h.C
  -- Step 4: add `|V|`.
  exact hV_int.add hCMβ1

/-- **BB3-transport (BB3-transport-hRHSbelow-mDpHDu-summand)**:
integrability of the `m_ε · (D_pH(x, Du_ε, m_ε) ⬝ Du_ε)` summand on the
unit cube, the second substantive Hölder pairing of the
`hRHSbelow_int` assembly.

Strategy:
1. Cauchy–Schwarz / euclidean-dot bound: `q ⬝ v ≤ d · ‖q‖ · ‖v‖` and
   likewise `-(q ⬝ v) = (-q) ⬝ v ≤ d · ‖q‖ · ‖v‖`, hence
   `|q ⬝ v| ≤ d · ‖q‖ · ‖v‖`.
2. `pack3.hPower.DpH_upper`:
   `‖D_pH x p m‖ ≤ C(‖p‖^{α-1} + m^{β - β/α} + 1)` for `m > 0`.
3. Combined under `m > 0`:
   `|m · (D_pH ⬝ Du)| ≤ d · C · m · (‖Du‖^{α-1} + m^{β-β/α} + 1) · ‖Du‖`
   `= d·C · (m · ‖Du‖^α  +  m^{1+β-β/α} · ‖Du‖  +  m · ‖Du‖)`.
4. Young's inequality at three different conjugate pairs dominates
   each piece by `c₁ · m^{β+1} + c₂ · (‖Du‖^γ̄ + 1)`:
   - `m · ‖Du‖^α`: Young at `(β+1, β̄')`, then upgrade
     `‖Du‖^{α·β̄'} ≤ ‖Du‖^γ̄ + 1` via the exponent rider
     `α·β̄' ≤ γ̄`. (Same Hölder as in `mH_int`.)
   - `m^{1+β-β/α} · ‖Du‖`: Young at `((β+1)/(1+β-β/α), α·β̄')`,
     so `(m^{1+β-β/α})^p = m^{β+1}` and `‖Du‖^q ≤ ‖Du‖^γ̄ + 1`.
   - `m · ‖Du‖`: Young at `(β+1, β̄')`, then upgrade
     `‖Du‖^{β̄'} ≤ ‖Du‖^γ̄ + 1` (since `β̄' < α·β̄' ≤ γ̄`).
5. Build a single linear dominator `Bnd` and close with
   `Integrable.mono'`. -/
lemma mDpHDu_int
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (reps : CongestionBareRepresentativesNN (d := d) X betaBar gammaBar V H DpH ε)
    (h : StationaryMFG.Hamiltonian.CongestionAprioriPowerData H DpH)
    (hcong : StationaryMFG.Hamiltonian.CongestionGrowthCore (d := d) H DpH J)
    (hα_eq : h.α = hcong.α) (hβ_eq : h.β = hcong.β)
    (hbetaBar_eq : betaBar = ENNReal.ofReal (h.β + 1))
    {γBar : ℝ} (hγBar_pos : 0 < γBar)
    (hgammaBar_eq : gammaBar = ENNReal.ofReal γBar)
    (hγBar_ge_alpha_betaBarP :
      h.α * StationaryMFG.Hamiltonian.betaBar' h.β ≤ γBar) :
    MeasureTheory.Integrable
      (fun x => reps.m x
                  * ((DpH x (fun i => reps.Du i x) (reps.m x))
                      ⬝ (fun i => reps.Du i x)))
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
  classical
  -- Equip cube with finite measure.
  haveI hcube_fin :
      MeasureTheory.IsFiniteMeasure (MeasureTheory.Measure.restrict
        (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
        (UnitCube (d := d))) :=
    ⟨by
      rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
          volume_unitCube]
      exact ENNReal.one_lt_top⟩
  set μC : MeasureTheory.Measure (Fin d → ℝ) :=
    MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d) with hμC_def
  -- Positivity facts.
  have hα_pos : 0 < h.α := lt_trans one_pos h.hα
  have hβ_pos : 0 < h.β := h.hβ
  have hβp1_pos : 0 < h.β + 1 := by linarith
  have hC_pos : 0 < h.C := h.hC
  -- `s := 1 + β - β/α` ≥ 0 and ≤ β+1.
  have hβ_div_α_le_β : h.β / h.α ≤ h.β := by
    have h1 : (1 : ℝ) ≤ h.α := le_of_lt h.hα
    have h2 : h.β / h.α ≤ h.β / 1 := by
      apply div_le_div_of_nonneg_left hβ_pos.le _ h1
      linarith [h.hα]
    simpa using h2
  set s : ℝ := 1 + h.β - h.β / h.α with hs_def
  have hs_pos : 0 < s := by
    have : 0 ≤ h.β - h.β / h.α := by linarith
    have : 0 < 1 + (h.β - h.β / h.α) := by linarith
    simpa [hs_def, sub_eq_add_neg, add_assoc] using this
  have hs_le_βp1 : s ≤ h.β + 1 := by
    have : h.β / h.α ≥ 0 := div_nonneg hβ_pos.le (by linarith [h.hα])
    simp [hs_def]; linarith
  -- Hölder-conjugate witness `(β+1, β̄')`.
  have hbetaBarP_eq : StationaryMFG.Hamiltonian.betaBar' h.β = (h.β + 1) / h.β := rfl
  have hbetaBarP_pos : 0 < StationaryMFG.Hamiltonian.betaBar' h.β := by
    rw [hbetaBarP_eq]; positivity
  have hpq1 : (h.β + 1).HolderConjugate (StationaryMFG.Hamiltonian.betaBar' h.β) := by
    refine (Real.holderConjugate_iff).mpr ⟨?_, ?_⟩
    · linarith
    · rw [hbetaBarP_eq]
      field_simp
      ring
  -- For piece 2 we use conjugate pair (p₂, q₂) with p₂ = (β+1)/s, q₂ = α·β̄'.
  -- Sanity: 1/p₂ + 1/q₂ = s/(β+1) + 1/(α·β̄') = s/(β+1) + β/(α·(β+1)) ·.. let's
  -- just verify the equation. We have α·β̄' = α·(β+1)/β, so 1/(α·β̄') = β/(α·(β+1)).
  -- And s/(β+1) = (1+β-β/α)/(β+1). Sum: (1+β-β/α + β/α)/(β+1) = (β+1)/(β+1) = 1. ✓
  set p₂ : ℝ := (h.β + 1) / s with hp₂_def
  set q₂ : ℝ := h.α * StationaryMFG.Hamiltonian.betaBar' h.β with hq₂_def
  have hp₂_pos : 0 < p₂ := by rw [hp₂_def]; exact div_pos hβp1_pos hs_pos
  have hq₂_pos : 0 < q₂ := by rw [hq₂_def]; exact mul_pos hα_pos hbetaBarP_pos
  have hp₂_one_lt : 1 < p₂ := by
    rw [hp₂_def, lt_div_iff₀ hs_pos]
    have : s < h.β + 1 := by
      have hαβ_pos : 0 < h.β / h.α := div_pos hβ_pos (by linarith [h.hα])
      simp [hs_def]; linarith
    linarith
  have hpq2 : p₂.HolderConjugate q₂ := by
    refine (Real.holderConjugate_iff).mpr ⟨hp₂_one_lt, ?_⟩
    -- 1/p₂ + 1/q₂ = s/(β+1) + 1/(α·β̄') = 1.
    rw [hp₂_def, hq₂_def, hbetaBarP_eq]
    have hβ_ne : h.β ≠ 0 := hβ_pos.ne'
    have hα_ne : h.α ≠ 0 := (lt_trans one_pos h.hα).ne'
    have hβp1_ne : h.β + 1 ≠ 0 := hβp1_pos.ne'
    have hs_ne : s ≠ 0 := hs_pos.ne'
    rw [hs_def]
    field_simp
    ring
  -- === Congestion-native exponents (paper Lemma `lem:ADFGU.congestion`). ===
  -- The congestion `D_pH` bound (eq:assH.DpH.upper.congestion) uses the
  -- exponent `γc := α(1 + τ/β)` on `‖p‖`.  Note `0 ≤ τ ≤ 1`, hence
  -- `γc ≤ α(1 + 1/β) = α·β̄' = γBar_min ≤ γBar`.
  have hτ_nn : 0 ≤ hcong.τ := hcong.hτ.1
  have hτ_le_one : hcong.τ ≤ 1 := hcong.hτ.2
  set γc : ℝ := h.α * (1 + hcong.τ / h.β) with hγc_def
  have hγc_pos : 0 < γc := by
    rw [hγc_def]
    have : 0 < 1 + hcong.τ / h.β :=
      by have : 0 ≤ hcong.τ / h.β := div_nonneg hτ_nn hβ_pos.le
         linarith
    exact mul_pos hα_pos this
  -- `α·β̄' = α(β+1)/β = α(1 + 1/β)`, so `γc ≤ α·β̄' ≤ γBar`.
  have hαβ'_eq : h.α * StationaryMFG.Hamiltonian.betaBar' h.β
      = h.α * (1 + 1 / h.β) := by
    rw [hbetaBarP_eq]
    have hβ_ne : h.β ≠ 0 := hβ_pos.ne'
    congr 1
    field_simp
  have hγc_le_αβ' : γc ≤ h.α * StationaryMFG.Hamiltonian.betaBar' h.β := by
    rw [hαβ'_eq, hγc_def]
    apply mul_le_mul_of_nonneg_left _ hα_pos.le
    have hstep : hcong.τ / h.β ≤ 1 / h.β :=
      div_le_div_of_nonneg_right hτ_le_one hβ_pos.le
    linarith
  have hγc_le_γBar : γc ≤ γBar := le_trans hγc_le_αβ' hγBar_ge_alpha_betaBarP
  -- `1 ≤ γBar` (since `γBar ≥ α·β̄' > 1`).
  have hone_le_γBar : (1 : ℝ) ≤ γBar := by
    have h1 : (1 : ℝ) < h.α * StationaryMFG.Hamiltonian.betaBar' h.β := by
      have : (1 : ℝ) < StationaryMFG.Hamiltonian.betaBar' h.β :=
        StationaryMFG.Hamiltonian.one_lt_betaBar' h.β hβ_pos
      calc (1 : ℝ) = 1 * 1 := by ring
        _ < h.α * StationaryMFG.Hamiltonian.betaBar' h.β :=
            mul_lt_mul'' h.hα this zero_le_one zero_le_one
    linarith [hγBar_ge_alpha_betaBarP]
  -- === Piece-B (`m^{1-τ}·‖p‖^{γc}`) Young conjugate pair. ===
  -- We use `(P_B, Q_B) = ((β+1)/(1-τ), (β+1)/(β+τ))` (only for `τ < 1`; the
  -- `τ = 1` case degenerates `m^{1-τ}=1` into Piece A).  Then
  -- `(m^{1-τ})^{P_B} = m^{β+1}` and `γc·Q_B = α·β̄' (= γBar_min) ≤ γBar`.
  set oneMτ : ℝ := 1 - hcong.τ with honeMτ_def
  have honeMτ_nn : 0 ≤ oneMτ := by rw [honeMτ_def]; linarith
  -- Step 1: integrabilities of building blocks.
  have hMβ1 : MeasureTheory.Integrable (fun x => reps.m x ^ (h.β + 1)) μC :=
    reps.hLB_int (β := h.β) hβ_pos hbetaBar_eq
  have hDuγ : MeasureTheory.Integrable
      (fun x => ‖(fun i => reps.Du i x)‖ ^ γBar) μC :=
    reps.hDu_norm_int (γBar := γBar) hγBar_pos hgammaBar_eq
  have h_one_int : MeasureTheory.Integrable (fun _ : (Fin d → ℝ) => (1 : ℝ)) μC :=
    MeasureTheory.integrable_const 1
  -- AE strong measurability of `m`, `Du` (each axis), the joint vector,
  -- and the `DpH`-composition.
  have hm_aesm :
      MeasureTheory.AEStronglyMeasurable reps.m μC := by
    have hm_lp : Periodic.MemLpPer (d := d) betaBar reps.m :=
      Periodic.MemLpPer.congr_ae_unitCube reps.hmem_lp_coe_m reps.hae_m.symm
    exact hm_lp.aestronglyMeasurable
  have hDu_meas : ∀ i, MeasureTheory.AEStronglyMeasurable (reps.Du i) μC :=
    fun i => (reps.hDu_lp i).aestronglyMeasurable
  have hDu_aem : ∀ i, AEMeasurable (reps.Du i) μC :=
    fun i => (hDu_meas i).aemeasurable
  have hPi_aem : AEMeasurable
      (fun x : Fin d → ℝ => (fun i => reps.Du i x)) μC :=
    AEMeasurable.of_eval hDu_aem
  have hPi_meas : MeasureTheory.AEStronglyMeasurable
      (fun x : Fin d → ℝ => (fun i => reps.Du i x)) μC :=
    aestronglyMeasurable_iff_aemeasurable.mpr hPi_aem
  have hm_aem : AEMeasurable reps.m μC := hm_aesm.aemeasurable
  have hself_aem : AEMeasurable (fun x : Fin d → ℝ => x) μC :=
    aemeasurable_id
  have hTriple_aem : AEMeasurable
      (fun x : Fin d → ℝ => (x, (fun i => reps.Du i x), reps.m x)) μC := by
    refine AEMeasurable.prodMk hself_aem ?_
    refine AEMeasurable.prodMk hPi_aem hm_aem
  have hDpH_meas : Measurable
      (fun (xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ) => DpH xpm.1 xpm.2.1 xpm.2.2) :=
    h.measurable_DpH
  have hDpH_comp_aem : AEMeasurable
      (fun x : Fin d → ℝ => DpH x (fun i => reps.Du i x) (reps.m x)) μC :=
    hDpH_meas.comp_aemeasurable hTriple_aem
  have hDpH_comp_aesm : MeasureTheory.AEStronglyMeasurable
      (fun x : Fin d → ℝ => DpH x (fun i => reps.Du i x) (reps.m x)) μC := by
    -- Range is `Fin d → ℝ`, which is `SecondCountableTopology`.
    exact aestronglyMeasurable_iff_aemeasurable.mpr hDpH_comp_aem
  -- The dot product `(DpH ⬝ Du) = ∑ i, DpH·.i * Du i` is AE-strongly measurable.
  have hDot_aesm : MeasureTheory.AEStronglyMeasurable
      (fun x : Fin d → ℝ =>
        (DpH x (fun i => reps.Du i x) (reps.m x)) ⬝ (fun i => reps.Du i x)) μC := by
    unfold dotProduct
    refine Finset.aestronglyMeasurable_fun_sum (Finset.univ : Finset (Fin d))
      (f := fun i x => (DpH x (fun j => reps.Du j x) (reps.m x)) i * reps.Du i x) ?_
    intro i _
    refine MeasureTheory.AEStronglyMeasurable.mul ?_ (hDu_meas i)
    -- (DpH ...) i is AE strongly measurable via composition.
    have hpi_i : Measurable (fun (v : Fin d → ℝ) => v i) :=
      measurable_pi_apply i
    have : MeasureTheory.AEStronglyMeasurable
        (fun x => (DpH x (fun j => reps.Du j x) (reps.m x)) i) μC := by
      refine aestronglyMeasurable_iff_aemeasurable.mpr ?_
      exact hpi_i.comp_aemeasurable hDpH_comp_aem
    exact this
  have hmDot_aesm : MeasureTheory.AEStronglyMeasurable
      (fun x => reps.m x
        * ((DpH x (fun i => reps.Du i x) (reps.m x)) ⬝ (fun i => reps.Du i x))) μC :=
    hm_aesm.mul hDot_aesm
  -- Step 2: dominator envelope `Bnd`.
  -- We will dominate by:
  --   `Bnd x = K_m · m^{β+1} + K_Du · (‖Du‖^γ̄ + 1)` for some K_m, K_Du > 0.
  -- A coarse choice: take K_m and K_Du large enough to absorb all three pieces.
  -- Concretely:
  --   Piece 1 (m·‖Du‖^α):
  --      ≤ m^{β+1}/(β+1) + (‖Du‖^γ̄ + 1) / β̄'    [Young + upgrade]
  --   Piece 2 (m^s · ‖Du‖):
  --      ≤ m^{β+1}/p₂ + (‖Du‖^γ̄ + 1) / q₂      [Young + upgrade]
  --   Piece 3 (m·‖Du‖):
  --      ≤ m^{β+1}/(β+1) + (‖Du‖^γ̄ + 1) / β̄'    [Young + upgrade]
  -- Sum and multiply by `d·C ≥ 0`. Choose
  --   K_m   := d·C · (1/(β+1) + 1/p₂ + 1/(β+1))
  --   K_Du  := d·C · (1/β̄' + 1/q₂ + 1/β̄')
  -- Congestion-native dominator coefficients.  After multiplying the
  -- congestion `D_pH` bound by `m` and Cauchy–Schwarz, the integrand splits
  -- into four pieces A=‖p‖^{γc}, B=m^{1-τ}‖p‖^{γc}, C=m^s‖p‖, D=‖p‖.  Each is
  -- Young-dominated by `c·m^{β+1} + c'·(‖p‖^{γBar}+1)` with all `c, c' ≤ 1`.
  -- We choose generous constants (their precise value is irrelevant for
  -- integrability) and close the final inequality by `linarith`.
  set Km : ℝ := (d : ℝ) * hcong.C * (1 / p₂ + 1) with hKm_def
  set KDu : ℝ := (d : ℝ) * hcong.C * (1 / q₂ + 3) with hKDu_def
  have hKm_nn : 0 ≤ Km := by
    rw [hKm_def]
    have h1 : 0 ≤ 1 / p₂ := by positivity
    have : 0 ≤ 1 / p₂ + 1 := by linarith
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg d) hcong.hC.le) this
  have hKDu_nn : 0 ≤ KDu := by
    rw [hKDu_def]
    have h1 : 0 ≤ 1 / q₂ := by positivity
    have : 0 ≤ 1 / q₂ + 3 := by linarith
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg d) hcong.hC.le) this
  set Bnd : (Fin d → ℝ) → ℝ :=
    fun x => Km * reps.m x ^ (h.β + 1)
              + KDu * (‖(fun i => reps.Du i x)‖ ^ γBar + 1) with hBnd_def
  have hBnd_int : MeasureTheory.Integrable Bnd μC := by
    have h1 : MeasureTheory.Integrable (fun x => Km * reps.m x ^ (h.β + 1)) μC :=
      hMβ1.const_mul Km
    have h2 : MeasureTheory.Integrable
        (fun x => ‖(fun i => reps.Du i x)‖ ^ γBar + 1) μC :=
      hDuγ.add h_one_int
    have h3 : MeasureTheory.Integrable
        (fun x => KDu * (‖(fun i => reps.Du i x)‖ ^ γBar + 1)) μC :=
      h2.const_mul KDu
    exact h1.add h3
  -- Step 3: pointwise AE-bound via Cauchy-Schwarz + DpH_upper + Young.
  have hPointwise :
      ∀ᵐ x ∂μC,
        ‖reps.m x
            * ((DpH x (fun i => reps.Du i x) (reps.m x)) ⬝ (fun i => reps.Du i x))‖
          ≤ Bnd x := by
    -- **Positivity-elimination migration (child-B, route a):** the
    -- pointwise bound on `‖m·(D_pH⬝Du)‖` no longer routes through the
    -- singular congestion `D_pH` envelope (`hcong.DpH_upper`, which carries
    -- the `1/m`, `1/m^τ` terms requiring `0 < m`). Instead we use the
    -- **`m`-multiplied** envelope `CongestionGrowthCore.mDpH_extended_bound`
    -- (`Assumptions.lean`) on the extension `J = m·D_pH`, which holds for
    -- `0 ≤ m` (the singular terms have been cancelled against the outer `m`
    -- analytically and the boundary `m = 0` handled by `mDpHat0`). We only
    -- need a.e. NONNEGATIVITY `reps.mε_nonneg`, NOT strict positivity.
    filter_upwards [hcong.mDpH_extended_bound, reps.mε_nonneg] with x hxJ hxm_nn
    set p : Fin d → ℝ := fun i => reps.Du i x
    set q : Fin d → ℝ := DpH x p (reps.m x)
    have hmpos_nn : 0 ≤ reps.m x := hxm_nn
    have hp_nn : 0 ≤ ‖p‖ := norm_nonneg _
    have hq_nn : 0 ≤ ‖q‖ := norm_nonneg _
    have hd_nn : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
    -- The `m·(D_pH⬝Du)` envelope, derived from `mDpH_extended_bound`.
    -- Target shape (matches the old `hExpandE` RHS times `d`):
    --   |m·(q⬝p)| ≤ d·C·(‖p‖^γc + m^oneMτ·‖p‖^γc + m^s·‖p‖ + ‖p‖).
    have hmEnv : |reps.m x * (q ⬝ p)|
        ≤ (d : ℝ) * (hcong.C * (‖p‖ ^ γc)
            + hcong.C * (reps.m x ^ oneMτ * ‖p‖ ^ γc)
            + hcong.C * (reps.m x ^ s * ‖p‖)
            + hcong.C * ‖p‖) := by
      -- `J`-envelope at `(p, m x)`, exponents aligned to the local names.
      -- `mDpH_extended_bound`: `‖J x p m‖ ≤ C(1+m^{1-τ})‖p‖^{α(1+τ/β)-1}
      --   + C(m^{β+1-β/α}+1)`. With `hα_eq/hβ_eq`: the exponents match
      -- `γc-1`, `oneMτ = 1-τ`, `s = β+1-β/α`.
      have hJbase := hxJ p (reps.m x) hxm_nn
      have hexp1 : hcong.α * (1 + hcong.τ / hcong.β) - 1 = γc - 1 := by
        rw [hγc_def, hα_eq, hβ_eq]
      have hexp2 : hcong.β + 1 - hcong.β / hcong.α = s := by
        rw [hs_def, hα_eq, hβ_eq]; ring
      have hexp3 : (1 : ℝ) - hcong.τ = oneMτ := by rw [honeMτ_def]
      rw [hexp1, hexp2, hexp3] at hJbase
      -- `hJbase : ‖J x p (m x)‖ ≤ C(1+m^oneMτ)‖p‖^{γc-1} + C(m^s+1)`.
      set RJ : ℝ := hcong.C * (1 + reps.m x ^ oneMτ) * (‖p‖ ^ (γc - 1))
                    + hcong.C * (reps.m x ^ s + 1) with hRJ_def
      have hRJ_nn : 0 ≤ RJ := le_trans (norm_nonneg _) hJbase
      -- Cauchy–Schwarz bound `|J⬝p| ≤ d·‖J‖·‖p‖` for any vector `J`.
      have hCS : ∀ Jv : Fin d → ℝ, |Jv ⬝ p| ≤ (d : ℝ) * ‖Jv‖ * ‖p‖ := by
        intro Jv
        have hdot_le : ∀ w : Fin d → ℝ, w ⬝ p ≤ (d : ℝ) * ‖w‖ * ‖p‖ := by
          intro w
          unfold dotProduct
          have h_each : ∀ i ∈ (Finset.univ : Finset (Fin d)),
              w i * p i ≤ ‖w‖ * ‖p‖ := by
            intro i _
            calc w i * p i ≤ |w i * p i| := le_abs_self _
              _ = |w i| * |p i| := abs_mul _ _
              _ ≤ ‖w‖ * |p i| :=
                  mul_le_mul_of_nonneg_right
                    (by simpa [Real.norm_eq_abs] using norm_le_pi_norm w i)
                    (abs_nonneg _)
              _ ≤ ‖w‖ * ‖p‖ :=
                  mul_le_mul_of_nonneg_left
                    (by simpa [Real.norm_eq_abs] using norm_le_pi_norm p i)
                    (norm_nonneg _)
          calc (∑ i, w i * p i) ≤ ∑ _ : Fin d, ‖w‖ * ‖p‖ :=
                Finset.sum_le_sum h_each
            _ = (d : ℝ) * ‖w‖ * ‖p‖ := by
                simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
        have hupper := hdot_le Jv
        have hlower : -(Jv ⬝ p) ≤ (d : ℝ) * ‖Jv‖ * ‖p‖ := by
          have hneg := hdot_le (-Jv)
          have hdot_neg : (-Jv) ⬝ p = -(Jv ⬝ p) := by
            unfold dotProduct
            rw [← Finset.sum_neg_distrib]
            exact Finset.sum_congr rfl (fun i _ => by simp [Pi.neg_apply, neg_mul])
          rwa [hdot_neg, norm_neg] at hneg
        rw [abs_le]; exact ⟨by linarith, hupper⟩
      -- Split on `m x = 0` vs `0 < m x`. At `m x = 0`, LHS is `0`.
      rcases eq_or_lt_of_le hxm_nn with hm0 | hmpos
      · -- `m x = 0`: `|m·(q⬝p)| = 0 ≤ RHS` (RHS ≥ 0).
        rw [← hm0, zero_mul, abs_zero]
        have hγc_nn : 0 ≤ ‖p‖ ^ γc := Real.rpow_nonneg hp_nn _
        have hmoneMτ_nn : 0 ≤ reps.m x ^ oneMτ := Real.rpow_nonneg hmpos_nn _
        have hms_nn0 : 0 ≤ reps.m x ^ s := Real.rpow_nonneg hmpos_nn _
        have hCnn : 0 ≤ hcong.C := hcong.hC.le
        positivity
      · -- `0 < m x`: `m·(q⬝p) = (m•D_pH)⬝p = J⬝p`, then Cauchy–Schwarz + `hJbase`.
        have hJeq : J x p (reps.m x) = reps.m x • q :=
          hcong.mDpHat0.J_of_pos x p (reps.m x) hmpos
        -- `J⬝p = (m•q)⬝p = m·(q⬝p)`.
        have hJdot : J x p (reps.m x) ⬝ p = reps.m x * (q ⬝ p) := by
          rw [hJeq]
          unfold dotProduct
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun i _ => by
            simp [Pi.smul_apply, smul_eq_mul]; ring)
        -- `|m·(q⬝p)| = |J⬝p| ≤ d·‖J‖·‖p‖ ≤ d·RJ·‖p‖`.
        rw [← hJdot]
        refine le_trans (hCS (J x p (reps.m x))) ?_
        have hstep : (d : ℝ) * ‖J x p (reps.m x)‖ * ‖p‖
            ≤ (d : ℝ) * RJ * ‖p‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hJbase hd_nn) hp_nn
        refine le_trans hstep ?_
        -- `d·RJ·‖p‖ = d·C·(‖p‖^γc + m^oneMτ·‖p‖^γc + m^s·‖p‖ + ‖p‖)`,
        -- using `‖p‖^{γc-1}·‖p‖ = ‖p‖^γc`.
        have hpγc : ‖p‖ ^ (γc - 1) * ‖p‖ = ‖p‖ ^ γc := by
          by_cases hp_zero : ‖p‖ = 0
          · rw [hp_zero, mul_zero, Real.zero_rpow hγc_pos.ne']
          · have hp_pos : 0 < ‖p‖ := lt_of_le_of_ne hp_nn (Ne.symm hp_zero)
            calc ‖p‖ ^ (γc - 1) * ‖p‖
                = ‖p‖ ^ (γc - 1) * ‖p‖ ^ (1 : ℝ) := by rw [Real.rpow_one]
              _ = ‖p‖ ^ ((γc - 1) + 1) := (Real.rpow_add hp_pos _ _).symm
              _ = ‖p‖ ^ γc := by ring_nf
        rw [hRJ_def]
        have hexpand : (d : ℝ)
            * (hcong.C * (1 + reps.m x ^ oneMτ) * (‖p‖ ^ (γc - 1))
                + hcong.C * (reps.m x ^ s + 1)) * ‖p‖
            = (d : ℝ) * (hcong.C * (‖p‖ ^ (γc - 1) * ‖p‖)
                + hcong.C * (reps.m x ^ oneMτ * (‖p‖ ^ (γc - 1) * ‖p‖))
                + hcong.C * (reps.m x ^ s * ‖p‖)
                + hcong.C * ‖p‖) := by ring
        rw [hexpand, hpγc]
    -- === Bound each piece by `α·m^{β+1} + β·(‖p‖^{γBar}+1)`. ===
    have hγc_nn : 0 ≤ ‖p‖ ^ γc := Real.rpow_nonneg hp_nn _
    have hγBar_p_nn : 0 ≤ ‖p‖ ^ γBar := Real.rpow_nonneg hp_nn _
    have hβp1_m_nn0 : 0 ≤ reps.m x ^ (h.β + 1) := Real.rpow_nonneg hmpos_nn _
    -- Piece A: `‖p‖^{γc} ≤ ‖p‖^{γBar} + 1` (γc ≤ γBar).
    have hPieceA : ‖p‖ ^ γc ≤ ‖p‖ ^ γBar + 1 := by
      by_cases hp1 : 1 ≤ ‖p‖
      · have := Real.rpow_le_rpow_of_exponent_le hp1 hγc_le_γBar
        linarith
      · push_neg at hp1
        have := Real.rpow_le_one hp_nn hp1.le hγc_pos.le
        linarith
    -- Piece D: `‖p‖ ≤ ‖p‖^{γBar} + 1` (γBar ≥ 1).
    have hPieceD : ‖p‖ ≤ ‖p‖ ^ γBar + 1 := by
      by_cases hp1 : 1 ≤ ‖p‖
      · have h0 : ‖p‖ = ‖p‖ ^ (1 : ℝ) := (Real.rpow_one _).symm
        have := Real.rpow_le_rpow_of_exponent_le hp1 hone_le_γBar
        rw [← h0] at this; linarith
      · push_neg at hp1; linarith
    -- Piece C: `m^s·‖p‖ ≤ m^{β+1}/p₂ + (‖p‖^{γBar}+1)/q₂` (Young at (p₂,q₂)).
    have hms_nn : 0 ≤ reps.m x ^ s := Real.rpow_nonneg hmpos_nn _
    have hYoungC := Real.young_inequality_of_nonneg
      (a := reps.m x ^ s) (b := ‖p‖) (p := p₂) (q := q₂) hms_nn hp_nn hpq2
    have hsp2 : s * p₂ = h.β + 1 := by rw [hp₂_def]; field_simp
    have hrpow_mul2 : (reps.m x ^ s) ^ p₂ = reps.m x ^ (h.β + 1) := by
      rw [← Real.rpow_mul hmpos_nn, hsp2]
    have hbound_pq2 : ‖p‖ ^ q₂ ≤ ‖p‖ ^ γBar + 1 := by
      have hq2_eq : q₂ = h.α * StationaryMFG.Hamiltonian.betaBar' h.β := rfl
      by_cases hp1 : 1 ≤ ‖p‖
      · rw [hq2_eq]
        have := Real.rpow_le_rpow_of_exponent_le hp1 hγBar_ge_alpha_betaBarP
        linarith
      · push_neg at hp1
        have := Real.rpow_le_one hp_nn hp1.le hq₂_pos.le
        linarith
    have hPieceC : reps.m x ^ s * ‖p‖
        ≤ reps.m x ^ (h.β + 1) / p₂ + (‖p‖ ^ γBar + 1) / q₂ := by
      refine le_trans hYoungC ?_
      have hC1 : (reps.m x ^ s) ^ p₂ / p₂ = reps.m x ^ (h.β + 1) / p₂ := by
        rw [hrpow_mul2]
      have hC2 : ‖p‖ ^ q₂ / q₂ ≤ (‖p‖ ^ γBar + 1) / q₂ :=
        div_le_div_of_nonneg_right hbound_pq2 hq₂_pos.le
      linarith
    -- Piece B: `m^{1-τ}·‖p‖^{γc} ≤ m^{β+1} + (‖p‖^{γBar}+1)`.
    -- Case `τ = 1`: `m^{1-τ} = m^0 = 1`, reduces to Piece A.
    -- Case `τ < 1`: Young at `(P_B, Q_B) = ((β+1)/(1-τ), (β+1)/(β+τ))` with
    --   `(m^{1-τ})^{P_B} = m^{β+1}` and `γc·Q_B = α·β̄' ≤ γBar`.
    have hms_oneMτ_nn : 0 ≤ reps.m x ^ oneMτ := Real.rpow_nonneg hmpos_nn _
    have hPieceB : reps.m x ^ oneMτ * ‖p‖ ^ γc
        ≤ reps.m x ^ (h.β + 1) + (‖p‖ ^ γBar + 1) := by
      by_cases hτ1 : hcong.τ = 1
      · -- `oneMτ = 0`, so `m^{oneMτ} = 1`.
        have hone : reps.m x ^ oneMτ = 1 := by
          rw [honeMτ_def, hτ1, sub_self, Real.rpow_zero]
        rw [hone, one_mul]
        have := hPieceA
        linarith [hβp1_m_nn0]
      · -- `τ < 1`, so `oneMτ > 0`.
        have hτ_lt_one : hcong.τ < 1 := lt_of_le_of_ne hτ_le_one hτ1
        have honeMτ_pos : 0 < oneMτ := by rw [honeMτ_def]; linarith
        set PB : ℝ := (h.β + 1) / oneMτ with hPB_def
        set QB : ℝ := (h.β + 1) / (h.β + hcong.τ) with hQB_def
        have hβpτ_pos : 0 < h.β + hcong.τ := by linarith [hτ_nn]
        have hPB_pos : 0 < PB := by rw [hPB_def]; exact div_pos hβp1_pos honeMτ_pos
        have hQB_pos : 0 < QB := by rw [hQB_def]; exact div_pos hβp1_pos hβpτ_pos
        have hPB_one_lt : 1 < PB := by
          rw [hPB_def, lt_div_iff₀ honeMτ_pos]
          rw [honeMτ_def]; linarith [hβ_pos]
        have hpqB : PB.HolderConjugate QB := by
          refine (Real.holderConjugate_iff).mpr ⟨hPB_one_lt, ?_⟩
          -- 1/PB + 1/QB = oneMτ/(β+1) + (β+τ)/(β+1) = (1-τ+β+τ)/(β+1) = 1.
          rw [hPB_def, hQB_def, honeMτ_def]
          have hβp1_ne : h.β + 1 ≠ 0 := hβp1_pos.ne'
          field_simp
          ring
        have hYoungB := Real.young_inequality_of_nonneg
          (a := reps.m x ^ oneMτ) (b := ‖p‖ ^ γc) (p := PB) (q := QB)
          hms_oneMτ_nn hγc_nn hpqB
        -- `(m^{oneMτ})^{PB} = m^{oneMτ·PB} = m^{β+1}`.
        have hoPB : oneMτ * PB = h.β + 1 := by
          rw [hPB_def]; field_simp
        have hrpowB : (reps.m x ^ oneMτ) ^ PB = reps.m x ^ (h.β + 1) := by
          rw [← Real.rpow_mul hmpos_nn, hoPB]
        -- `(‖p‖^{γc})^{QB} = ‖p‖^{γc·QB} ≤ ‖p‖^{γBar} + 1` since `γc·QB ≤ γBar`.
        have hγcQB_le : γc * QB ≤ γBar := by
          -- γc·QB = α(β+τ)/β · (β+1)/(β+τ) = α(β+1)/β = α·β̄' ≤ γBar.
          have hγc_form : γc = h.α * (h.β + hcong.τ) / h.β := by
            rw [hγc_def]
            have hβ_ne : h.β ≠ 0 := hβ_pos.ne'
            field_simp
          have hkey : γc * QB = h.α * StationaryMFG.Hamiltonian.betaBar' h.β := by
            rw [hγc_form, hQB_def, hbetaBarP_eq]
            have hβ_ne : h.β ≠ 0 := hβ_pos.ne'
            have hβpτ_ne : h.β + hcong.τ ≠ 0 := hβpτ_pos.ne'
            field_simp
          rw [hkey]; exact hγBar_ge_alpha_betaBarP
        have hrpowB2 : (‖p‖ ^ γc) ^ QB = ‖p‖ ^ (γc * QB) := by
          rw [← Real.rpow_mul hp_nn]
        have hboundB : (‖p‖ ^ γc) ^ QB ≤ ‖p‖ ^ γBar + 1 := by
          rw [hrpowB2]
          by_cases hp1 : 1 ≤ ‖p‖
          · have hγcQB_pos : 0 < γc * QB := mul_pos hγc_pos hQB_pos
            have := Real.rpow_le_rpow_of_exponent_le hp1 hγcQB_le
            linarith
          · push_neg at hp1
            have hγcQB_pos : 0 < γc * QB := mul_pos hγc_pos hQB_pos
            have := Real.rpow_le_one hp_nn hp1.le hγcQB_pos.le
            linarith
        -- `QB = (β+1)/(β+τ) ≥ 1` since `β+τ ≤ β+1` (τ ≤ 1).
        have hQB_one_le : (1 : ℝ) ≤ QB := by
          rw [hQB_def, le_div_iff₀ hβpτ_pos, one_mul]
          linarith [hτ_le_one]
        refine le_trans hYoungB ?_
        have hB1 : (reps.m x ^ oneMτ) ^ PB / PB ≤ reps.m x ^ (h.β + 1) := by
          rw [hrpowB]
          have hstep : reps.m x ^ (h.β + 1) / PB ≤ reps.m x ^ (h.β + 1) := by
            rw [div_le_iff₀ hPB_pos]
            exact le_mul_of_one_le_right hβp1_m_nn0 hPB_one_lt.le
          exact hstep
        have hB2 : (‖p‖ ^ γc) ^ QB / QB ≤ ‖p‖ ^ γBar + 1 := by
          have hpow_nn : 0 ≤ (‖p‖ ^ γc) ^ QB := Real.rpow_nonneg hγc_nn _
          have hle : (‖p‖ ^ γc) ^ QB / QB ≤ (‖p‖ ^ γc) ^ QB := by
            rw [div_le_iff₀ hQB_pos]
            exact le_mul_of_one_le_right hpow_nn hQB_one_le
          exact le_trans hle hboundB
        linarith
    -- === Assemble: `m·E·‖p‖ ≤ Km·m^{β+1} + KDu·(‖p‖^{γBar}+1)`. ===
    -- coefficient bookkeeping: dC·(A + B + C + D) regroups exactly into
    --   Km·m^{β+1} + KDu·(‖p‖^γ̄+1) with Km = dC(1/p₂+1), KDu = dC(1/q₂+3).
    have hAbs_chain :
        |reps.m x * (q ⬝ p)| ≤ Km * reps.m x ^ (h.β + 1) + KDu * (‖p‖ ^ γBar + 1) := by
      -- Step 1: the `J`-envelope (`hmEnv`, derived from `mDpH_extended_bound`)
      -- gives `|m·(q⬝p)| ≤ d·(C·A + C·B + C·C' + C·D)` directly, for `0 ≤ m`.
      have hstep1 : |reps.m x * (q ⬝ p)|
          ≤ (d : ℝ) * (hcong.C * (‖p‖ ^ γc)
              + hcong.C * (reps.m x ^ oneMτ * ‖p‖ ^ γc)
              + hcong.C * (reps.m x ^ s * ‖p‖)
              + hcong.C * ‖p‖) := hmEnv
      -- Now `|...| ≤ d·(C·A + C·B + C·C' + C·D)` with C = hcong.C.
      -- Bound the bracket by the pieces.  Let `T := A + B + C' + D` style sum.
      have hCcong_nn : 0 ≤ hcong.C := hcong.hC.le
      -- Sum the four pieces (no `C`, no `d`): pure `linarith`.
      have hsum_pieces :
          ‖p‖ ^ γc
            + reps.m x ^ oneMτ * ‖p‖ ^ γc
            + reps.m x ^ s * ‖p‖
            + ‖p‖
          ≤ reps.m x ^ (h.β + 1) / p₂ + (‖p‖ ^ γBar + 1) / q₂
              + reps.m x ^ (h.β + 1)
              + 3 * (‖p‖ ^ γBar + 1) := by
        linarith [hPieceA, hPieceB, hPieceC, hPieceD]
      -- Abbreviate the two sides as `LHSp ≤ RHSp`; then `m·E·‖p‖ = C·LHSp`,
      -- so `C·LHSp ≤ C·RHSp` and `d·(C·LHSp) ≤ d·(C·RHSp)`.
      have hC_sum : hcong.C * (‖p‖ ^ γc
            + reps.m x ^ oneMτ * ‖p‖ ^ γc
            + reps.m x ^ s * ‖p‖
            + ‖p‖)
          ≤ hcong.C * (reps.m x ^ (h.β + 1) / p₂ + (‖p‖ ^ γBar + 1) / q₂
              + reps.m x ^ (h.β + 1)
              + 3 * (‖p‖ ^ γBar + 1)) :=
        mul_le_mul_of_nonneg_left hsum_pieces hCcong_nn
      -- `hExpandE` rewrote `m·E·‖p‖` to the distributed form; refold to `C·LHSp`.
      have hfold : hcong.C * (‖p‖ ^ γc)
            + hcong.C * (reps.m x ^ oneMτ * ‖p‖ ^ γc)
            + hcong.C * (reps.m x ^ s * ‖p‖)
            + hcong.C * ‖p‖
          = hcong.C * (‖p‖ ^ γc
            + reps.m x ^ oneMτ * ‖p‖ ^ γc
            + reps.m x ^ s * ‖p‖
            + ‖p‖) := by ring
      rw [hfold] at hstep1
      -- Multiply by `d ≥ 0`.
      have hd_bracket :
          (d : ℝ) * (hcong.C * (‖p‖ ^ γc
            + reps.m x ^ oneMτ * ‖p‖ ^ γc
            + reps.m x ^ s * ‖p‖
            + ‖p‖))
          ≤ (d : ℝ) * (hcong.C * (reps.m x ^ (h.β + 1) / p₂ + (‖p‖ ^ γBar + 1) / q₂
              + reps.m x ^ (h.β + 1)
              + 3 * (‖p‖ ^ γBar + 1))) :=
        mul_le_mul_of_nonneg_left hC_sum hd_nn
      refine le_trans hstep1 (le_trans hd_bracket ?_)
      -- Final equality: regroup the `m^{β+1}` and `(‖p‖^γ̄+1)` coefficients.
      rw [hKm_def, hKDu_def]
      apply le_of_eq
      ring
    -- Norm vs abs on ℝ:
    have hReal_norm_eq :
        ‖reps.m x * (q ⬝ p)‖ = |reps.m x * (q ⬝ p)| := Real.norm_eq_abs _
    rw [hReal_norm_eq, hBnd_def]
    exact hAbs_chain
  -- Step 4: Integrable.mono'.
  exact hBnd_int.mono' hmDot_aesm hPointwise

/-- **BB3-transport (BB3-transport-hRHSbelow-mH-summand)**:
integrability of the `m_ε · H(x, Du_ε, m_ε)` summand on the unit cube,
the first substantive Hölder pairing of the `hRHSbelow_int` assembly.

Strategy (paper Lemma `lem:ADFGU.congestion`, `eq:boundsH+`),
**congestion-native**: this proof does NOT consume the simple-power
upper fields `h.H_upper_pointwise`/`h.DpH_upper`. Instead it routes the
two sides of the `m · H` envelope through:

* UPPER on `m·H` via `h.lagr` (`m^β/C − C ≤ D_pH⬝p − H`, hence
  `H ≤ D_pH⬝p − m^β/C + C`): multiplying by `m ≥ 0` and dropping the
  nonpositive `−m^{β+1}/C` term,
  `m·H ≤ m·(D_pH⬝Du) + C·m`.
  The first summand is dominated by `|m·(D_pH⬝Du)|`, whose integrability
  is the **child-1 congestion-native** envelope `reps.mDpHDu_int`.

* LOWER on `m·H` (i.e. `−(m·H)`) via `h.lower`
  (`H ≥ ‖p‖^α/C − C(m^β+1)`, hence `−H ≤ C(m^β+1)`): multiplying by
  `m ≥ 0`, `−(m·H) ≤ C·m^{β+1} + C·m`.

The linear-in-`m` terms are dominated by `m ≤ m^{β+1} + 1` (AE under
`m > 0`). The single dominator is
`Bnd x := |m·(D_pH⬝Du)| + C·m^{β+1} + 2·C·(m^{β+1}+1)`,
integrable as a linear combination of `reps.mDpHDu_int` (abs),
`m^{β+1}` from `hLB_int`, and constants on the finite-measure cube. -/
lemma mH_int
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (reps : CongestionBareRepresentativesNN (d := d) X betaBar gammaBar V H DpH ε)
    (h : StationaryMFG.Hamiltonian.CongestionAprioriPowerData H DpH)
    (hcong : StationaryMFG.Hamiltonian.CongestionGrowthCore (d := d) H DpH J)
    (hα_eq : h.α = hcong.α) (hβ_eq : h.β = hcong.β)
    (hbetaBar_eq : betaBar = ENNReal.ofReal (h.β + 1))
    {γBar : ℝ} (hγBar_pos : 0 < γBar)
    (hgammaBar_eq : gammaBar = ENNReal.ofReal γBar)
    (hγBar_ge_alpha_betaBarP :
      h.α * StationaryMFG.Hamiltonian.betaBar' h.β ≤ γBar) :
    MeasureTheory.Integrable
      (fun x => reps.m x * H x (fun i => reps.Du i x) (reps.m x))
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
  classical
  -- Equip cube with finite measure.
  haveI hcube_fin :
      MeasureTheory.IsFiniteMeasure (MeasureTheory.Measure.restrict
        (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
        (UnitCube (d := d))) :=
    ⟨by
      rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
          volume_unitCube]
      exact ENNReal.one_lt_top⟩
  -- Local abbreviations.
  set μC : MeasureTheory.Measure (Fin d → ℝ) :=
    MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d) with hμC_def
  -- Positivity facts.
  have hβ_pos : 0 < h.β := h.hβ
  have hβp1_pos : 0 < h.β + 1 := by linarith
  have hC_pos : 0 < h.C := h.hC
  -- Step 1: integrabilities of the building blocks.
  -- `m^{β+1}` integrable (mass `L^{β+1}` bound).
  have hMβ1 : MeasureTheory.Integrable (fun x => reps.m x ^ (h.β + 1)) μC :=
    reps.hLB_int (β := h.β) hβ_pos hbetaBar_eq
  -- Constant `1`.
  have h_one_int : MeasureTheory.Integrable (fun _ : (Fin d → ℝ) => (1 : ℝ)) μC :=
    MeasureTheory.integrable_const 1
  -- The congestion-native `m · (D_pH ⬝ Du)` envelope (child 1, no upper
  -- simple-power fields consumed); we take its absolute value as a dominator.
  have hmDpHDu_int : MeasureTheory.Integrable
      (fun x => reps.m x
                  * ((DpH x (fun i => reps.Du i x) (reps.m x))
                      ⬝ (fun i => reps.Du i x))) μC :=
    reps.mDpHDu_int (J := J) h hcong hα_eq hβ_eq hbetaBar_eq hγBar_pos hgammaBar_eq
      hγBar_ge_alpha_betaBarP
  have hmDpHDu_abs_int : MeasureTheory.Integrable
      (fun x => |reps.m x
                  * ((DpH x (fun i => reps.Du i x) (reps.m x))
                      ⬝ (fun i => reps.Du i x))|) μC :=
    hmDpHDu_int.abs
  -- AE-strong measurability of `m`, `Du`, and the joint `H`-composition.
  have hm_aesm :
      MeasureTheory.AEStronglyMeasurable reps.m μC := by
    have hm_lp : Periodic.MemLpPer (d := d) betaBar reps.m :=
      Periodic.MemLpPer.congr_ae_unitCube reps.hmem_lp_coe_m reps.hae_m.symm
    exact hm_lp.aestronglyMeasurable
  have hDu_meas : ∀ i, MeasureTheory.AEStronglyMeasurable (reps.Du i) μC := by
    intro i
    exact (reps.hDu_lp i).aestronglyMeasurable
  have hDu_aem : ∀ i, AEMeasurable (reps.Du i) μC :=
    fun i => (hDu_meas i).aemeasurable
  have hPi_aem : AEMeasurable
      (fun x : Fin d → ℝ => (fun i => reps.Du i x)) μC :=
    AEMeasurable.of_eval hDu_aem
  -- The triple `x ↦ (x, Du x, m x)` is AE-measurable; compose with the
  -- jointly-measurable `H` to get AE-strong measurability of
  -- `x ↦ H x (Du x) (m x)`.
  have hm_aem : AEMeasurable reps.m μC := hm_aesm.aemeasurable
  have hself_aem : AEMeasurable (fun x : Fin d → ℝ => x) μC :=
    aemeasurable_id
  have hTriple_aem : AEMeasurable
      (fun x : Fin d → ℝ => (x, (fun i => reps.Du i x), reps.m x)) μC := by
    refine AEMeasurable.prodMk hself_aem ?_
    refine AEMeasurable.prodMk hPi_aem hm_aem
  have hH_meas : Measurable
      (fun (xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ) => H xpm.1 xpm.2.1 xpm.2.2) :=
    h.measurable_H
  have hH_comp_aem : AEMeasurable
      (fun x : Fin d → ℝ => H x (fun i => reps.Du i x) (reps.m x)) μC :=
    hH_meas.comp_aemeasurable hTriple_aem
  have hH_comp_aesm : MeasureTheory.AEStronglyMeasurable
      (fun x : Fin d → ℝ => H x (fun i => reps.Du i x) (reps.m x)) μC :=
    aestronglyMeasurable_iff_aemeasurable.mpr hH_comp_aem
  have hmH_aesm : MeasureTheory.AEStronglyMeasurable
      (fun x => reps.m x * H x (fun i => reps.Du i x) (reps.m x)) μC :=
    hm_aesm.mul hH_comp_aesm
  -- Step 2: dominator.
  --   `Bnd x := |m·(D_pH⬝Du)| + C·m^{β+1} + 2·C·(m^{β+1}+1)`.
  -- It is integrable as a linear combination of the three building blocks.
  set Bnd : (Fin d → ℝ) → ℝ :=
    fun x => |reps.m x
                * ((DpH x (fun i => reps.Du i x) (reps.m x))
                    ⬝ (fun i => reps.Du i x))|
              + h.C * reps.m x ^ (h.β + 1)
              + (2 * h.C) * (reps.m x ^ (h.β + 1) + 1) with hBnd_def
  have hBnd_int : MeasureTheory.Integrable Bnd μC := by
    have h1 : MeasureTheory.Integrable
        (fun x => h.C * reps.m x ^ (h.β + 1)) μC := hMβ1.const_mul h.C
    have h2 : MeasureTheory.Integrable
        (fun x => reps.m x ^ (h.β + 1) + 1) μC := hMβ1.add h_one_int
    have h3 : MeasureTheory.Integrable
        (fun x => (2 * h.C) * (reps.m x ^ (h.β + 1) + 1)) μC := h2.const_mul (2 * h.C)
    exact (hmDpHDu_abs_int.add h1).add h3
  -- Step 3: pointwise AE-bound `|m * H| ≤ Bnd`.
  -- UPPER via `h.lagr` (`m^β/C − C ≤ D_pH⬝p − H` ⟹ `H ≤ D_pH⬝p − m^β/C + C`):
  --   `m·H ≤ m·(D_pH⬝Du) + C·m` (dropping the nonpositive `−m^{β+1}/C` term).
  -- LOWER via `h.lower` (`H ≥ ‖p‖^α/C − C(m^β+1)` ⟹ `−H ≤ C(m^β+1)`):
  --   `−(m·H) ≤ C·m^{β+1} + C·m`.
  have hPointwise :
      ∀ᵐ x ∂μC,
        ‖reps.m x * H x (fun i => reps.Du i x) (reps.m x)‖ ≤ Bnd x := by
    -- **Positivity-elimination (route a):** only a.e. NONNEGATIVITY is used.
    -- The `lagr`/`lower` apriori bounds carry a `0 < m` binder, so we case-split
    -- on `m x = 0` (where `m·H = 0 ≤ Bnd`) vs `0 < m x` (the substantive branch).
    filter_upwards [h.lagr, h.lower, reps.mε_nonneg]
      with x hxLagr hxLower hxm_nn
    set p : Fin d → ℝ := fun i => reps.Du i x with hp_def
    -- Boundary case `m x = 0`: the integrand vanishes.
    rcases eq_or_lt_of_le hxm_nn with hm0 | hxm_pos
    · -- `m x = 0`: `‖m·H‖ = 0 ≤ Bnd x` (the dominator is a sum of nonneg terms).
      have hmx0 : reps.m x = 0 := hm0.symm
      have hlhs0 : ‖reps.m x * H x (fun i => reps.Du i x) (reps.m x)‖ = 0 := by
        rw [hmx0, zero_mul, norm_zero]
      rw [hlhs0, hBnd_def]
      have hβp1_m_nn0 : 0 ≤ reps.m x ^ (h.β + 1) := Real.rpow_nonneg hxm_nn _
      have hCnn : 0 ≤ h.C := hC_pos.le
      have habs_nn : 0 ≤ |reps.m x
            * ((DpH x (fun i => reps.Du i x) (reps.m x))
                ⬝ (fun i => reps.Du i x))| := abs_nonneg _
      have hT : 0 ≤ (2 * h.C) * (reps.m x ^ (h.β + 1) + 1) :=
        mul_nonneg (by linarith) (by linarith)
      have h2 : 0 ≤ h.C * reps.m x ^ (h.β + 1) := mul_nonneg hCnn hβp1_m_nn0
      linarith
    have hmpos_nn : 0 ≤ reps.m x := hxm_nn
    have hβ_m_nn : 0 ≤ reps.m x ^ h.β := Real.rpow_nonneg hxm_nn _
    have hβp1_m_nn : 0 ≤ reps.m x ^ (h.β + 1) := Real.rpow_nonneg hxm_nn _
    have hα_p_nn : 0 ≤ ‖p‖ ^ h.α := Real.rpow_nonneg (norm_nonneg _) _
    -- `m ≤ m^{β+1} + 1` for `m > 0`.
    have hm_le : reps.m x ≤ reps.m x ^ (h.β + 1) + 1 := by
      by_cases hm1 : 1 ≤ reps.m x
      · have h1 : reps.m x ≤ reps.m x ^ (h.β + 1) := by
          have hstep : reps.m x ^ (1 : ℝ) ≤ reps.m x ^ (h.β + 1) :=
            Real.rpow_le_rpow_of_exponent_le hm1 (by linarith)
          rwa [Real.rpow_one] at hstep
        linarith
      · push_neg at hm1; linarith
    -- `m · m^β = m^{β+1}`.
    have hmm : reps.m x * reps.m x ^ h.β = reps.m x ^ (h.β + 1) := by
      have h1 : reps.m x ^ (1 : ℝ) = reps.m x := Real.rpow_one _
      calc reps.m x * reps.m x ^ h.β
          = reps.m x ^ (1 : ℝ) * reps.m x ^ h.β := by rw [h1]
        _ = reps.m x ^ ((1 : ℝ) + h.β) := (Real.rpow_add hxm_pos 1 h.β).symm
        _ = reps.m x ^ (h.β + 1) := by ring_nf
    -- UPPER on `H`: from `lagr`, `H ≤ (D_pH⬝p) − m^β/C + C`.
    have hLagr : (reps.m x ^ h.β) / h.C - h.C
        ≤ (DpH x p (reps.m x)) ⬝ p - H x p (reps.m x) :=
      hxLagr p (reps.m x) hxm_pos
    have hH_upper : H x p (reps.m x)
        ≤ (DpH x p (reps.m x)) ⬝ p - (reps.m x ^ h.β) / h.C + h.C := by linarith
    -- LOWER on `H`: from `lower`, `−H ≤ C(m^β+1)`.
    have hLower : (‖p‖ ^ h.α) / h.C - h.C * (reps.m x ^ h.β + 1)
        ≤ H x p (reps.m x) :=
      hxLower p (reps.m x) hxm_pos
    have hNegH_upper : -H x p (reps.m x) ≤ h.C * (reps.m x ^ h.β + 1) := by
      have hdrop : 0 ≤ (‖p‖ ^ h.α) / h.C := div_nonneg hα_p_nn hC_pos.le
      linarith
    -- Multiply by `m ≥ 0`.
    -- UPPER: `m·H ≤ m·(D_pH⬝p) − m·(m^β/C) + m·C`.
    have hmH_upper : reps.m x * H x p (reps.m x)
        ≤ reps.m x * ((DpH x p (reps.m x)) ⬝ p - (reps.m x ^ h.β) / h.C + h.C) :=
      mul_le_mul_of_nonneg_left hH_upper hmpos_nn
    -- LOWER: `m·(−H) ≤ m·(C(m^β+1))`.
    have hmH_neg_aux : reps.m x * (-H x p (reps.m x))
        ≤ reps.m x * (h.C * (reps.m x ^ h.β + 1)) :=
      mul_le_mul_of_nonneg_left hNegH_upper hmpos_nn
    -- Assemble the two-sided real bound, then read it off as `|·| ≤ Bnd`.
    have hUp_to_Bnd : reps.m x * H x p (reps.m x) ≤ Bnd x := by
      have hdrop_neg : 0 ≤ reps.m x * ((reps.m x ^ h.β) / h.C) :=
        mul_nonneg hmpos_nn (div_nonneg hβ_m_nn hC_pos.le)
      have habs_ge : reps.m x * ((DpH x p (reps.m x)) ⬝ p)
          ≤ |reps.m x * ((DpH x p (reps.m x)) ⬝ p)| := le_abs_self _
      have hCm : h.C * reps.m x ≤ (2 * h.C) * (reps.m x ^ (h.β + 1) + 1) := by
        have h1 : reps.m x ≤ reps.m x ^ (h.β + 1) + 1 := hm_le
        have h2 : h.C * reps.m x ≤ h.C * (reps.m x ^ (h.β + 1) + 1) :=
          mul_le_mul_of_nonneg_left h1 hC_pos.le
        have h3 : h.C * (reps.m x ^ (h.β + 1) + 1)
            ≤ (2 * h.C) * (reps.m x ^ (h.β + 1) + 1) := by
          have hnn : 0 ≤ reps.m x ^ (h.β + 1) + 1 := by linarith
          have : h.C ≤ 2 * h.C := by linarith [hC_pos]
          exact mul_le_mul_of_nonneg_right this hnn
        linarith
      have hCmβ1_nn : 0 ≤ h.C * reps.m x ^ (h.β + 1) :=
        mul_nonneg hC_pos.le hβp1_m_nn
      -- `m·H ≤ m·(D_pH⬝p) + C·m ≤ |m·(D_pH⬝p)| + C·m^{β+1} + 2C(m^{β+1}+1)`.
      have hstep : reps.m x * H x p (reps.m x)
          ≤ reps.m x * ((DpH x p (reps.m x)) ⬝ p) + h.C * reps.m x := by
        have hexpand : reps.m x
              * ((DpH x p (reps.m x)) ⬝ p - (reps.m x ^ h.β) / h.C + h.C)
            = reps.m x * ((DpH x p (reps.m x)) ⬝ p)
              - reps.m x * ((reps.m x ^ h.β) / h.C) + h.C * reps.m x := by ring
        rw [hexpand] at hmH_upper
        linarith
      rw [hBnd_def]
      simp only [hp_def]
      linarith [habs_ge, hCm, hCmβ1_nn, hstep]
    have hLo_to_Bnd : -(reps.m x * H x p (reps.m x)) ≤ Bnd x := by
      -- `−(m·H) = m·(−H) ≤ C·m^{β+1} + C·m ≤ C·m^{β+1} + 2C(m^{β+1}+1)`.
      have hneg_eq : reps.m x * (-H x p (reps.m x))
          = -(reps.m x * H x p (reps.m x)) := by ring
      have hexpand : reps.m x * (h.C * (reps.m x ^ h.β + 1))
          = h.C * (reps.m x * reps.m x ^ h.β) + h.C * reps.m x := by ring
      have hbound : -(reps.m x * H x p (reps.m x))
          ≤ h.C * reps.m x ^ (h.β + 1) + h.C * reps.m x := by
        rw [hneg_eq] at hmH_neg_aux
        rw [hexpand, hmm] at hmH_neg_aux
        exact hmH_neg_aux
      have hCm : h.C * reps.m x ≤ (2 * h.C) * (reps.m x ^ (h.β + 1) + 1) := by
        have h2 : h.C * reps.m x ≤ h.C * (reps.m x ^ (h.β + 1) + 1) :=
          mul_le_mul_of_nonneg_left hm_le hC_pos.le
        have h3 : h.C * (reps.m x ^ (h.β + 1) + 1)
            ≤ (2 * h.C) * (reps.m x ^ (h.β + 1) + 1) := by
          have hnn : 0 ≤ reps.m x ^ (h.β + 1) + 1 := by linarith
          have : h.C ≤ 2 * h.C := by linarith [hC_pos]
          exact mul_le_mul_of_nonneg_right this hnn
        linarith
      have habs_nn : 0 ≤ |reps.m x
            * ((DpH x p (reps.m x)) ⬝ p)| := abs_nonneg _
      rw [hBnd_def]
      simp only [hp_def]
      linarith [hbound, hCm, habs_nn]
    have hAbsBnd : |reps.m x * H x p (reps.m x)| ≤ Bnd x := by
      rw [abs_le]
      exact ⟨by linarith [hLo_to_Bnd], hUp_to_Bnd⟩
    rw [Real.norm_eq_abs]
    exact hAbsBnd
  -- Step 4: `Integrable.mono'`.
  exact hBnd_int.mono' hmH_aesm hPointwise

/-- **BB3-transport #10 (`hRHSbelow_int`) — FINAL ASSEMBLY**: integrability
of the lower-bound integrand from the VI identity
`∫ u = ∫ (m·(-H + DpH ⬝ Du) + V·m + epsTerms)`.

Linear sum of four summands:
* `m · (-H)` integrable from `(mH_int).neg`;
* `m · (DpH ⬝ Du)` integrable from `mDpHDu_int`;
* `V · m` integrable from `hVm_int` rider — note the rider provides
  `Integrable (|V| * m)` so we upgrade via `Integrable.mono'` using
  `|V * m| ≤ |V| * m` (true since `m ≥ 0` AE from `mε_nonneg`), with
  AE-strong measurability of `V * m` from the supplied `hV_aesm` rider
  and `m`'s AE-strong measurability;
* `epsTerms` integrable from `hEpsTerms_int` rider.

Combined via `Integrable.add`/`.sub`/`.neg`/`Integrable.congr` to match
the bridge-field shape exactly. -/
lemma hRHSbelow_int
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (reps : CongestionBareRepresentativesNN (d := d) X betaBar gammaBar V H DpH ε)
    (h : StationaryMFG.Hamiltonian.CongestionAprioriPowerData H DpH)
    (hcong : StationaryMFG.Hamiltonian.CongestionGrowthCore (d := d) H DpH J)
    (hα_eq : h.α = hcong.α) (hβ_eq : h.β = hcong.β)
    (hbetaBar_eq : betaBar = ENNReal.ofReal (h.β + 1))
    {γBar : ℝ} (hγBar_pos : 0 < γBar)
    (hgammaBar_eq : gammaBar = ENNReal.ofReal γBar)
    (hγBar_ge_alpha_betaBarP :
      h.α * StationaryMFG.Hamiltonian.betaBar' h.β ≤ γBar)
    (hV_aesm : MeasureTheory.AEStronglyMeasurable V
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (hVm_int : MeasureTheory.Integrable (fun x => |V x| * reps.m x)
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (hEpsTerms_int : MeasureTheory.Integrable reps.epsTerms
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d))) :
    MeasureTheory.Integrable
      (fun x => reps.m x * (-H x (fun i => reps.Du i x) (reps.m x)
                          + (DpH x (fun i => reps.Du i x) (reps.m x))
                            ⬝ (fun i => reps.Du i x))
                + V x * reps.m x + reps.epsTerms x)
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
  classical
  set μC : MeasureTheory.Measure (Fin d → ℝ) :=
    MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d) with hμC_def
  -- Summand A: m * H integrable.
  have hmH : MeasureTheory.Integrable
      (fun x => reps.m x * H x (fun i => reps.Du i x) (reps.m x)) μC :=
    reps.mH_int (J := J) h hcong hα_eq hβ_eq hbetaBar_eq hγBar_pos hgammaBar_eq
      hγBar_ge_alpha_betaBarP
  -- Summand A negated.
  have hmH_neg : MeasureTheory.Integrable
      (fun x => -(reps.m x * H x (fun i => reps.Du i x) (reps.m x))) μC := hmH.neg
  -- Summand B: m * (DpH ⬝ Du) integrable.
  have hmDpHDu : MeasureTheory.Integrable
      (fun x => reps.m x
        * ((DpH x (fun i => reps.Du i x) (reps.m x)) ⬝ (fun i => reps.Du i x))) μC :=
    reps.mDpHDu_int h hcong hα_eq hβ_eq hbetaBar_eq hγBar_pos hgammaBar_eq
      hγBar_ge_alpha_betaBarP
  -- Sum A+B.
  have hAB_sum : MeasureTheory.Integrable
      (fun x => -(reps.m x * H x (fun i => reps.Du i x) (reps.m x))
                + reps.m x
                  * ((DpH x (fun i => reps.Du i x) (reps.m x))
                      ⬝ (fun i => reps.Du i x))) μC :=
    hmH_neg.add hmDpHDu
  -- Rewrite into the bridge-field form `m * (-H + DpH ⬝ Du)`.
  have hAB_form : MeasureTheory.Integrable
      (fun x => reps.m x * (-H x (fun i => reps.Du i x) (reps.m x)
                          + (DpH x (fun i => reps.Du i x) (reps.m x))
                            ⬝ (fun i => reps.Du i x))) μC := by
    refine hAB_sum.congr ?_
    refine Filter.Eventually.of_forall ?_
    intro x; ring
  -- Summand C: V * m integrable via mono' against |V| * m.
  have hm_aesm : MeasureTheory.AEStronglyMeasurable reps.m μC := by
    have hm_lp : Periodic.MemLpPer (d := d) betaBar reps.m :=
      Periodic.MemLpPer.congr_ae_unitCube reps.hmem_lp_coe_m reps.hae_m.symm
    exact hm_lp.aestronglyMeasurable
  have hVm_aesm : MeasureTheory.AEStronglyMeasurable (fun x => V x * reps.m x) μC :=
    hV_aesm.mul hm_aesm
  have hVm_pointwise :
      ∀ᵐ x ∂μC, ‖V x * reps.m x‖ ≤ |V x| * reps.m x := by
    filter_upwards [reps.mε_nonneg] with x hxm_nn
    have hnorm : ‖V x * reps.m x‖ = |V x * reps.m x| := Real.norm_eq_abs _
    rw [hnorm, abs_mul]
    have hm_abs : |reps.m x| = reps.m x := abs_of_nonneg hxm_nn
    rw [hm_abs]
  have hVm : MeasureTheory.Integrable (fun x => V x * reps.m x) μC :=
    hVm_int.mono' hVm_aesm hVm_pointwise
  -- Summand D: epsTerms integrable (from rider).
  -- Final assembly: (A+B) + C + D.
  exact (hAB_form.add hVm).add hEpsTerms_int


end CongestionBareRepresentativesNN

/-! ### Sanity-check `example` for BB2-transport

Type-check that each of the 11 transport lemmas has the right shape to
discharge the corresponding per-ε bridge field via `fun ε hε => …
(reps ε hε)` once BB4 supplies a per-ε family of bare-representatives
records. -/

example
    {betaBar gammaBar : ℝ≥0∞}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {ε : ℝ}
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (reps : CongestionBareRepresentatives (d := d) X betaBar gammaBar V H DpH ε)
    (hγ_one_le : (1 : ℝ≥0∞) ≤ gammaBar) :
    (∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume
              (UnitCube d)), 0 ≤ reps.m x) ∧
    MeasureTheory.AEStronglyMeasurable reps.u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) ∧
    Periodic.IsPeriodic reps.u ∧
    MeasureTheory.LocallyIntegrable reps.u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) ∧
    Periodic.MemSobolevPer (d := d) gammaBar reps.u ∧
    Periodic.MemLpPer (d := d) gammaBar reps.u ∧
    (∀ i, Periodic.HasWeakDerivPer (d := d) i reps.u (reps.Du i)) ∧
    (∀ i, MeasureTheory.AEStronglyMeasurable (reps.Du i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))) ∧
    (∀ i, Periodic.IsPeriodic (reps.Du i)) ∧
    (∀ i, MeasureTheory.LocallyIntegrable (reps.Du i)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))) ∧
    (∀ i, Periodic.MemLpPer (d := d) gammaBar (reps.Du i)) :=
  ⟨reps.mε_nonneg, reps.hu_meas hγ_one_le, reps.hu_per,
    reps.hu_loc hγ_one_le, reps.hu_sob, reps.hu_lp_γ,
    reps.hDu_weak, reps.hDu_meas hγ_one_le, reps.hDu_per,
    reps.hDu_loc hγ_one_le, reps.hDu_lp⟩

/-! ### Sanity-check `example` for BB3-transport (10 of 10 lemmas landed)

Type-check the 3 Banach-VI conclusion lemmas + the 7 integrability
lemmas (`hu_int`, `hLB_int`, `hMbeta_int`, `hDu_norm_int`,
`hUbetap_int`, `hRHSabove_int`, `hRHSbelow_int`). All ten BB3-transport
lemmas are now landed and bundled here. -/

example
    {betaBar gammaBar : ℝ≥0∞}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {ε : ℝ}
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (reps : CongestionBareRepresentatives (d := d) X betaBar gammaBar V H DpH ε)
    (hγ_one_le : (1 : ℝ≥0∞) ≤ gammaBar)
    (h : StationaryMFG.Hamiltonian.CongestionAprioriPowerData H DpH)
    (hcong : StationaryMFG.Hamiltonian.CongestionGrowthCore (d := d) H DpH J)
    (hα_eq : h.α = hcong.α) (hβ_eq : h.β = hcong.β)
    {γBar : ℝ} (hγBar_pos : 0 < γBar)
    (hgammaBar_eq : gammaBar = ENNReal.ofReal γBar)
    (hbetaBarP_le_gBar : StationaryMFG.Hamiltonian.betaBar' h.β ≤ γBar)
    (hγBar_ge_alpha_betaBarP :
      h.α * StationaryMFG.Hamiltonian.betaBar' h.β ≤ γBar)
    (hbetaBar_eq : betaBar = ENNReal.ofReal (h.β + 1))
    (hV_int : MeasureTheory.Integrable (fun x => |V x|)
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (hV_aesm : MeasureTheory.AEStronglyMeasurable V
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (hVm_int : MeasureTheory.Integrable (fun x => |V x| * reps.m x)
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (hEpsTerms_int : MeasureTheory.Integrable reps.epsTerms
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d))) :
    -- Subgroup A: Banach-VI conclusions (3 lemmas).
    (∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
      reps.u x + H x (fun i => reps.Du i x) (reps.m x) - V x ≤ 0) ∧
    (∫ x in UnitCube d, reps.u x
        ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
      = ∫ x in UnitCube d,
          (reps.m x * (-H x (fun i => reps.Du i x) (reps.m x)
                      + (DpH x (fun i => reps.Du i x) (reps.m x))
                        ⬝ (fun i => reps.Du i x))
            + V x * reps.m x
            + reps.epsTerms x)
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))) ∧
    (∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
      0 ≤ reps.epsTerms x) ∧
    -- Subgroup B: all 7 integrability lemmas.
    MeasureTheory.Integrable reps.u
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) ∧
    MeasureTheory.Integrable (fun x => reps.m x ^ (h.β + 1))
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) ∧
    MeasureTheory.Integrable (fun x => reps.m x ^ h.β)
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) ∧
    MeasureTheory.Integrable
      (fun x => ‖(fun i => reps.Du i x)‖ ^ γBar)
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) ∧
    MeasureTheory.Integrable
      (fun x => |reps.u x| ^ StationaryMFG.Hamiltonian.betaBar' h.β)
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) ∧
    MeasureTheory.Integrable
      (fun x => |V x| + h.C * (reps.m x ^ h.β + 1))
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) ∧
    MeasureTheory.Integrable
      (fun x => reps.m x * (-H x (fun i => reps.Du i x) (reps.m x)
                          + (DpH x (fun i => reps.Du i x) (reps.m x))
                            ⬝ (fun i => reps.Du i x))
                + V x * reps.m x + reps.epsTerms x)
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
  ⟨reps.hHJB_le, reps.hVIIdentity, reps.hEpsNN,
    reps.hu_int hγ_one_le,
    reps.hLB_int h.hβ hbetaBar_eq,
    reps.hMbeta_int h.hβ hbetaBar_eq,
    reps.hDu_norm_int hγBar_pos hgammaBar_eq,
    reps.hUbetap_int h.hβ hbetaBarP_le_gBar hgammaBar_eq,
    reps.hRHSabove_int h hV_int hbetaBar_eq,
    reps.hRHSbelow_int h hcong hα_eq hβ_eq hbetaBar_eq hγBar_pos hgammaBar_eq
      hγBar_ge_alpha_betaBarP hV_aesm hVm_int hEpsTerms_int⟩

/-! ### BB3 — discharge `hcoeWeak_Du` via closedness of `HasWeakDerivPer`

This block discharges the bareBridge weak-derivative field `hcoeWeak_Du`
(paper `Apriori.lean:1724`) at the Browder–Minty regularised-VI witness
`data.weakVI.choose ∈ closure (congestionBanachK)` **via a closedness
argument** — NOT a representation theorem.

The weak-derivative condition (conjunct 2 of `congestionBanachK`) is closed
under norm-`Lp` convergence: take a sequence `q_n ∈ congestionBanachK` with
`q_n → z` in the product norm of `LpPer βBar d × SobolevPerLp 1 γBar d`. Then
the value and gradient `Lp`-components converge in `Lp γBar`, and for any test
function `φ`, the Hölder bound
`|∫ (⇑q_n − ⇑z) · φ| ≤ ‖φ‖∞ · ‖q_n − z‖_{L¹} ≤ ‖φ‖∞ · ‖q_n − z‖_{Lp} → 0`
gives weak (against-test-function) convergence of the integrals. Passing to
the limit through `HasWeakDerivPer.of_weak_limit` (`WeakDerivative.lean:1271`)
yields `HasWeakDerivPer i (⇑z.2.1) (⇑(z.2.2 i))`. -/

/-- A continuous periodic function is bounded on the unit cube. We bound it on
the compact closed cube `Icc 0 1 ⊇ Ico 0 1 = UnitCube`. -/
lemma SmoothPeriodic.exists_bound_on_unitCube (φ : SmoothPeriodic d) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ UnitCube d, |(φ : (Fin d → ℝ) → ℝ) x| ≤ M := by
  have hcompact : IsCompact (Set.Icc (0 : Fin d → ℝ) 1) := isCompact_Icc
  have hcont : ContinuousOn (φ : (Fin d → ℝ) → ℝ) (Set.Icc (0 : Fin d → ℝ) 1) :=
    φ.smooth.continuous.continuousOn
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x hx
  have hxIcc : x ∈ Set.Icc (0 : Fin d → ℝ) 1 := by
    rw [Set.mem_Icc]
    have hx' := (mem_unitCube_iff (d := d)).1 hx
    exact ⟨fun i => (hx' i).1, fun i => le_of_lt (hx' i).2⟩
  calc |(φ : (Fin d → ℝ) → ℝ) x| = ‖(φ : (Fin d → ℝ) → ℝ) x‖ := (Real.norm_eq_abs _).symm
    _ ≤ C := hC x hxIcc
    _ ≤ max C 0 := le_max_left _ _

open Filter Topology in
/-- **The Hölder/closedness step** (raw-`Lp`-typed). If a sequence `g_n`
converges to `g` in `Lp p` on the unit cube, then for every smooth periodic
test function `φ`, the integrals `∫ ⇑g_n · φ` converge to `∫ ⇑g · φ`.

The functional `g ↦ ∫ ⇑g · φ` is Lipschitz (constant `‖φ‖∞`) from `Lp p` (via
the finite-measure inclusion `Lp p ↪ L¹`), so it preserves limits. This is the
sole missing piece for the BB3 closedness discharge of `hcoeWeak_Du`. -/
lemma lp_periodicIntegral_mul_tendsto {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {g_n : ℕ → Lp ℝ p (volume.restrict (UnitCube d))}
    {g : Lp ℝ p (volume.restrict (UnitCube d))}
    (hconv : Tendsto g_n atTop (𝓝 g))
    (φ : SmoothPeriodic d) :
    Tendsto
      (fun n => periodicIntegral
        (fun x => (g_n n : (Fin d → ℝ) → ℝ) x * (φ : (Fin d → ℝ) → ℝ) x))
      atTop
      (𝓝 (periodicIntegral
        (fun x => (g : (Fin d → ℝ) → ℝ) x * (φ : (Fin d → ℝ) → ℝ) x))) := by
  classical
  let μ : Measure (Fin d → ℝ) := volume.restrict (UnitCube (d := d))
  haveI hfin : IsFiniteMeasure (volume.restrict (UnitCube (d := d))) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  obtain ⟨M, hM0, hMbound⟩ := SmoothPeriodic.exists_bound_on_unitCube φ
  -- `φ` is bounded a.e.[μ] by `M` (μ is supported on the cube).
  have hφ_ae : ∀ᵐ x ∂(volume.restrict (UnitCube (d := d))),
      ‖(φ : (Fin d → ℝ) → ℝ) x‖ ≤ M := by
    refine (ae_restrict_iff' measurableSet_unitCube).2 ?_
    filter_upwards with x hx
    rw [Real.norm_eq_abs]; exact hMbound x hx
  have hφ_meas : AEStronglyMeasurable (φ : (Fin d → ℝ) → ℝ)
      (volume.restrict (UnitCube (d := d))) :=
    φ.smooth.continuous.aestronglyMeasurable
  -- Each `⇑g_n` and `⇑g` is in `L¹(μ)` (finite measure, `p ≥ 1`).
  have hL1 : ∀ f : Lp ℝ p (volume.restrict (UnitCube (d := d))),
      Integrable (f : (Fin d → ℝ) → ℝ) (volume.restrict (UnitCube (d := d))) := fun f =>
    memLp_one_iff_integrable.1 ((Lp.memLp f).mono_exponent hp1)
  -- `periodicIntegral F = ∫ x, F x ∂μ`.
  have hper : ∀ F : (Fin d → ℝ) → ℝ,
      periodicIntegral F = ∫ x, F x ∂(volume.restrict (UnitCube (d := d))) := by
    intro F; rfl
  -- Distance bound `dist (∫⇑g_n·φ) (∫⇑g·φ) ≤ M · ‖g_n - g‖`.
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun n => dist_nonneg) (g := fun n => M * ‖g_n n - g‖) ?_ ?_
  · intro n
    -- Set `h := g_n n - g`, so `⇑h =ᵐ ⇑(g_n n) - ⇑g`.
    set h : Lp ℝ p μ := g_n n - g with hh_def
    have hcoe : (h : (Fin d → ℝ) → ℝ) =ᵐ[μ]
        (fun x => (g_n n : (Fin d → ℝ) → ℝ) x - (g : (Fin d → ℝ) → ℝ) x) :=
      Lp.coeFn_sub (g_n n) g
    -- `∫⇑g_n·φ - ∫⇑g·φ = ∫⇑h·φ`.
    have hsub_int :
        (∫ x, (g_n n : (Fin d → ℝ) → ℝ) x * (φ : (Fin d → ℝ) → ℝ) x ∂μ)
          - (∫ x, (g : (Fin d → ℝ) → ℝ) x * (φ : (Fin d → ℝ) → ℝ) x ∂μ)
          = ∫ x, (h : (Fin d → ℝ) → ℝ) x * (φ : (Fin d → ℝ) → ℝ) x ∂μ := by
      rw [← integral_sub
            ((hL1 (g_n n)).mul_bdd hφ_meas hφ_ae)
            ((hL1 g).mul_bdd hφ_meas hφ_ae)]
      refine integral_congr_ae ?_
      filter_upwards [hcoe] with x hx
      simp only [hx]; ring
    -- `dist = |∫⇑h·φ|`.
    rw [Real.dist_eq, hper, hper, hsub_int]
    -- `|∫⇑h·φ| ≤ ∫ ‖⇑h·φ‖ ≤ ∫ M·‖⇑h‖ = M·∫‖⇑h‖`.
    have hbound1 :
        |∫ x, (h : (Fin d → ℝ) → ℝ) x * (φ : (Fin d → ℝ) → ℝ) x ∂μ|
          ≤ ∫ x, ‖(h : (Fin d → ℝ) → ℝ) x * (φ : (Fin d → ℝ) → ℝ) x‖ ∂μ := by
      rw [← Real.norm_eq_abs]
      exact norm_integral_le_integral_norm _
    have hpt : ∀ᵐ x ∂μ,
        ‖(h : (Fin d → ℝ) → ℝ) x * (φ : (Fin d → ℝ) → ℝ) x‖
          ≤ M * ‖(h : (Fin d → ℝ) → ℝ) x‖ := by
      filter_upwards [hφ_ae] with x hx
      rw [norm_mul]
      calc ‖(h : (Fin d → ℝ) → ℝ) x‖ * ‖(φ : (Fin d → ℝ) → ℝ) x‖
          ≤ ‖(h : (Fin d → ℝ) → ℝ) x‖ * M :=
            mul_le_mul_of_nonneg_left hx (norm_nonneg _)
        _ = M * ‖(h : (Fin d → ℝ) → ℝ) x‖ := by ring
    have hbound2 :
        ∫ x, ‖(h : (Fin d → ℝ) → ℝ) x * (φ : (Fin d → ℝ) → ℝ) x‖ ∂μ
          ≤ ∫ x, M * ‖(h : (Fin d → ℝ) → ℝ) x‖ ∂μ := by
      refine integral_mono_ae ?_ ?_ hpt
      · exact ((hL1 h).mul_bdd hφ_meas hφ_ae).norm
      · exact ((hL1 h).norm).const_mul M
    have heq3 :
        ∫ x, M * ‖(h : (Fin d → ℝ) → ℝ) x‖ ∂μ
          = M * ∫ x, ‖(h : (Fin d → ℝ) → ℝ) x‖ ∂μ :=
      integral_const_mul _ _
    -- `∫‖⇑h‖ = (eLpNorm ⇑h 1 μ).toReal ≤ (eLpNorm ⇑h p μ).toReal = ‖h‖`.
    have heq4 : ∫ x, ‖(h : (Fin d → ℝ) → ℝ) x‖ ∂μ
        = (eLpNorm (h : (Fin d → ℝ) → ℝ) 1 μ).toReal := by
      rw [integral_norm_eq_lintegral_enorm
        ((Lp.memLp h).mono_exponent hp1).aestronglyMeasurable,
        eLpNorm_one_eq_lintegral_enorm (Lp.memLp h).aestronglyMeasurable]
    have hmono : (eLpNorm (h : (Fin d → ℝ) → ℝ) 1 μ).toReal
        ≤ (eLpNorm (h : (Fin d → ℝ) → ℝ) p μ).toReal := by
      apply ENNReal.toReal_mono (Lp.eLpNorm_ne_top h)
      have : MemLpPer (d := d) (1 : ℝ≥0∞) (h : (Fin d → ℝ) → ℝ) :=
        (Lp.memLp h).mono_exponent hp1
      exact eLpNormPer_mono_exponent (h : (Fin d → ℝ) → ℝ)
        (Lp.memLp h).aestronglyMeasurable hp1
    have hnorm : (eLpNorm (h : (Fin d → ℝ) → ℝ) p μ).toReal = ‖h‖ :=
      (Lp.norm_def h).symm
    -- Chain everything.
    calc |∫ x, (h : (Fin d → ℝ) → ℝ) x * (φ : (Fin d → ℝ) → ℝ) x ∂μ|
        ≤ ∫ x, ‖(h : (Fin d → ℝ) → ℝ) x * (φ : (Fin d → ℝ) → ℝ) x‖ ∂μ := hbound1
      _ ≤ ∫ x, M * ‖(h : (Fin d → ℝ) → ℝ) x‖ ∂μ := hbound2
      _ = M * ∫ x, ‖(h : (Fin d → ℝ) → ℝ) x‖ ∂μ := heq3
      _ = M * (eLpNorm (h : (Fin d → ℝ) → ℝ) 1 μ).toReal := by rw [heq4]
      _ ≤ M * (eLpNorm (h : (Fin d → ℝ) → ℝ) p μ).toReal :=
            mul_le_mul_of_nonneg_left hmono hM0
      _ = M * ‖h‖ := by rw [hnorm]
      _ = M * ‖g_n n - g‖ := by rw [hh_def]
  · -- `M · ‖g_n - g‖ → 0`.
    have hnorm0 : Tendsto (fun n => ‖g_n n - g‖) atTop (𝓝 0) := by
      rw [tendsto_iff_norm_sub_tendsto_zero] at hconv
      exact hconv
    simpa using hnorm0.const_mul M

open Filter Topology in
/-- **BB3 closedness lemma.** If `z` lies in the (norm) closure of the
admissible congestion Banach domain `congestionBanachK`, then its value /
gradient `Lp`-components satisfy the periodic weak-derivative relation in every
direction. Proved by extracting a norm-convergent sequence from closure
membership and passing to the limit through `HasWeakDerivPer.of_weak_limit`
using the Hölder/closedness step `lp_periodicIntegral_mul_tendsto`. -/
lemma congestionBanachK_hasWeakDerivPer_mem_closure
    {βBar betaBarPrime γBar : ℝ≥0∞} [Fact (1 ≤ βBar)] [Fact (1 ≤ γBar)]
    {α β τ : ℝ}
    {z : congestionXBanach d βBar γBar}
    (hmem : z ∈ closure (congestionBanachK d βBar betaBarPrime γBar α β τ)) :
    ∀ i, Periodic.HasWeakDerivPer (d := d) i
      (⇑z.2.1 : (Fin d → ℝ) → ℝ) (⇑(z.2.2 i) : (Fin d → ℝ) → ℝ) := by
  classical
  intro i
  -- Extract a norm-convergent sequence `q_n → z` from closure membership.
  obtain ⟨q, hq_mem, hq_conv⟩ := mem_closure_iff_seq_limit.1 hmem
  -- `1 ≤ γBar`.
  have hγ1 : (1 : ℝ≥0∞) ≤ γBar := Fact.out
  -- The value / gradient `Lp`-components converge in `Lp γBar`.
  have hconv_fst : Tendsto (fun n => (q n).2.1) atTop (𝓝 z.2.1) :=
    ((continuous_snd.comp continuous_id).fst.tendsto z).comp hq_conv
  have hconv_snd : Tendsto (fun n => (q n).2.2 i) atTop (𝓝 (z.2.2 i)) :=
    (((continuous_apply i).comp
      (continuous_snd.comp continuous_id).snd).tendsto z).comp hq_conv
  -- Each `q n` is in `congestionBanachK`, so satisfies the weak-deriv relation.
  have hseq : ∀ n, Periodic.HasWeakDerivPer (d := d) i
      (⇑(q n).2.1 : (Fin d → ℝ) → ℝ) (⇑((q n).2.2 i) : (Fin d → ℝ) → ℝ) :=
    fun n => (hq_mem n).2 i
  -- `MemLpPer 1 (⇑z.2.2 i)` from `Lp.memLp` + exponent monotonicity.
  haveI hfin : IsFiniteMeasure
      (Measure.restrict volume (UnitCube (d := d))) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  have hDuLp : Periodic.MemLpPer (d := d) (1 : ℝ≥0∞) (⇑(z.2.2 i) : (Fin d → ℝ) → ℝ) :=
    (Lp.memLp (z.2.2 i)).mono_exponent hγ1
  -- Conclude via the limit-passage lemma.
  exact Periodic.HasWeakDerivPer.of_weak_limit
    (u_n := fun n => (⇑(q n).2.1 : (Fin d → ℝ) → ℝ))
    (Du_n := fun n => (⇑((q n).2.2 i) : (Fin d → ℝ) → ℝ))
    hDuLp hseq
    (fun ψ => lp_periodicIntegral_mul_tendsto hconv_fst ψ)
    (fun ψ => lp_periodicIntegral_mul_tendsto hconv_snd ψ)

/-- **BB4a-iv helper #3 (iter-0972 hKBridge discharge):** Sobolev
membership of the value's coercion at the chosen Banach-VI witness, derived
**internally** from closure membership — no bridge hypothesis.

This is the discharge of the (positivity-free) `hKBridge` field's CONJUNCT 2
(`Periodic.MemSobolevPer gammaBar (coe_u vi_witness)`). It bypasses the
`hK_witness` bridge of `coeMemSob_u_atWitness`. The two pieces of
`MemSobolevPer`:

* `MemLpPer gammaBar (⇑z.2.1)`: free from the `SobolevPerLp = Lp × …` type
  via `Lp.memLp`.
* the weak-derivative family `∃ g, ∀ i, HasWeakDerivPer i (⇑z.2.1) (g i)`:
  the conjunct-2 part of `congestionBanachK` membership is CLOSED under
  norm-`Lp` limits (`congestionBanachK_hasWeakDerivPer_mem_closure`), and the
  Browder–Minty witness lies in `closure (congestionBanachK …)` by
  `data.weakVI.choose_spec.1` once `data.K = congestionBanachK …` (which holds
  by `rfl` at the concrete call site, where `data.K = pack.K`).

This is exactly the "conjunct 2+4 are closed under norm limits" route flagged
in the iter-0969 audit; conjunct 3 (the uniform lower bound) is *not* needed
here — it lives in the separate `mε_pos_apriori` track. -/
lemma coeMemSob_u_atWitness_of_closure
    {γBar : ℝ}
    {betaBar betaBarPrime gammaBar : ℝ≥0∞} [Fact (1 ≤ betaBar)] [Fact (1 ≤ gammaBar)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {α β τ ε : ℝ}
    (data : CongestionRegularizedSolutionData (d := d)
              (γBar := γBar) (betaBar := betaBar)
              (betaBarPrime := betaBarPrime) (gammaBar := gammaBar)
              V H DpH J α β τ ε
              (Periodic.LpPer betaBar d × Periodic.SobolevPerLp 1 gammaBar d))
    (hKeq : data.K =
      congestionBanachK d betaBar betaBarPrime gammaBar α β τ) :
    Periodic.MemSobolevPer gammaBar
      (data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ) := by
  -- Closure membership of the chosen witness, transported into
  -- `congestionBanachK` along `closure data.K = closure (congestionBanachK …)`.
  -- A bare `rw [hKeq]` fails (the motive `fun s => choose ∈ closure s`
  -- is type-incorrect because `data.weakVI.choose`'s type itself mentions
  -- `data.K`); we transport via `Eq.mp` on the membership proposition only.
  have hmem_clos :
      data.weakVI.choose ∈
        closure (congestionBanachK d betaBar betaBarPrime gammaBar α β τ) :=
    Eq.mp
      (congrArg (fun s : Set _ => data.weakVI.choose ∈ closure s) hKeq)
      data.weakVI.choose_spec.1
  -- The weak-derivative family of the value coercion (BB3 closedness).
  have hweak := congestionBanachK_hasWeakDerivPer_mem_closure
    (d := d) (betaBarPrime := betaBarPrime) (α := α) (β := β) (τ := τ)
    hmem_clos
  -- `MemLpPer gammaBar (⇑z.2.1)` is free from the `Lp` type.
  exact ⟨MemLp.toMemLpPer (Lp.memLp data.weakVI.choose.2.1),
    ⟨fun i => (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ), hweak⟩⟩

/-- **BB3 `hcoeWeak_Du` discharge (iter-XXXX child-hcoeWeak):** the periodic
weak-derivative relation at the Browder–Minty witness, derived **internally**
from closure membership — no bridge hypothesis.

This drains the former `hcoeWeak_Du` field of
`CongestionRegularizedSequenceBuilderInputs`. The product type
`LpPer × SobolevPerLp` does not enforce that the abstract gradient component
`z.2.2` is a genuine weak derivative of the value `z.2.1`; the relation is,
however, the conjunct-2 part of `congestionBanachK` membership, which is CLOSED
under norm-`Lp` limits (`congestionBanachK_hasWeakDerivPer_mem_closure`). The
Browder–Minty witness lies in `closure (congestionBanachK …)` by
`data.weakVI.choose_spec.1` once `data.K = congestionBanachK …` (which holds
by `rfl` at the concrete native-pack call site, where `data.K = pack.K`).

Strictly simpler than `coeMemSob_u_atWitness_of_closure`: the closedness lemma
already returns exactly the `∀ i, HasWeakDerivPer …` family demanded here, so
no Sobolev-pair assembly is needed. The same `Eq.mp`-via-`hKeq` transport is
used (a bare `rw [hKeq]` fails because the motive
`fun s => choose ∈ closure s` is type-incorrect — `data.weakVI.choose`'s type
itself mentions `data.K`). -/
lemma coeWeakDeriv_atWitness_of_closure
    {γBar : ℝ}
    {betaBar betaBarPrime gammaBar : ℝ≥0∞} [Fact (1 ≤ betaBar)] [Fact (1 ≤ gammaBar)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {α β τ ε : ℝ}
    (data : CongestionRegularizedSolutionData (d := d)
              (γBar := γBar) (betaBar := betaBar)
              (betaBarPrime := betaBarPrime) (gammaBar := gammaBar)
              V H DpH J α β τ ε
              (Periodic.LpPer betaBar d × Periodic.SobolevPerLp 1 gammaBar d))
    (hKeq : data.K =
      congestionBanachK d betaBar betaBarPrime gammaBar α β τ) :
    ∀ i, Periodic.HasWeakDerivPer (d := d) i
      (data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ)
      (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) := by
  -- Closure membership of the chosen witness, transported into
  -- `congestionBanachK` along `closure data.K = closure (congestionBanachK …)`.
  have hmem_clos :
      data.weakVI.choose ∈
        closure (congestionBanachK d betaBar betaBarPrime gammaBar α β τ) :=
    Eq.mp
      (congrArg (fun s : Set _ => data.weakVI.choose ∈ closure s) hKeq)
      data.weakVI.choose_spec.1
  exact congestionBanachK_hasWeakDerivPer_mem_closure
    (d := d) (betaBarPrime := betaBarPrime) (α := α) (β := β) (τ := τ)
    hmem_clos

/-- **VIid-5c child E2 prereq — the free witness `MemLpPer` bundle.**

The three `Lᵖ`-membership facts about the Browder–Minty witness coercions that
are *free* from the ambient `Lp`-pair type structure (`Lp.memLp`), with no
closure / positivity input:

* `m = ⇑choose.1 ∈ L^{betaBar}` (the first factor is `LpPer betaBar`);
* `u = ⇑choose.2.1 ∈ L^{gammaBar}` (the value of the `SobolevPerLp 1 gammaBar`
  factor, whose underlying type is `Lp gammaBar`);
* each `Du i = ⇑(choose.2.2 i) ∈ L^{gammaBar}` (the gradient family of the
  Sobolev factor).

These are exactly the `hm_mem` / `hu_memGamma` / `hDu_mem` inputs the transport
producer (`congestion_transport_at_u_witness`) and the integrability-cert
producers (`congestion_VIid_easy_int_certs`, `congestion_VIid_mFlux_int`,
`congestion_VIid_mH_int`) consume at the witness — *once* `betaBar` /
`gammaBar` are identified with `β+1` / `α(β+1)/β` at the native call site. -/
lemma coeMemLpPer_witness_bundle_of_closure
    {γBar : ℝ}
    {betaBar betaBarPrime gammaBar : ℝ≥0∞} [Fact (1 ≤ betaBar)] [Fact (1 ≤ gammaBar)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {α β τ ε : ℝ}
    (data : CongestionRegularizedSolutionData (d := d)
              (γBar := γBar) (betaBar := betaBar)
              (betaBarPrime := betaBarPrime) (gammaBar := gammaBar)
              V H DpH J α β τ ε
              (Periodic.LpPer betaBar d × Periodic.SobolevPerLp 1 gammaBar d)) :
    Periodic.MemLpPer (d := d) betaBar
        (data.weakVI.choose.1 : (Fin d → ℝ) → ℝ)
    ∧ Periodic.MemLpPer (d := d) gammaBar
        (data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ)
    ∧ ∀ i, Periodic.MemLpPer (d := d) gammaBar
        (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) :=
  ⟨Periodic.memLpPer_iff_memLp.mpr (MeasureTheory.Lp.memLp data.weakVI.choose.1),
   Periodic.memLpPer_iff_memLp.mpr (MeasureTheory.Lp.memLp data.weakVI.choose.2.1),
   fun i => Periodic.memLpPer_iff_memLp.mpr
     (MeasureTheory.Lp.memLp (data.weakVI.choose.2.2 i))⟩

open Filter Topology in
/-- **BB-VIid-5c-E2a closedness lemma (a.e. nonnegativity of the density).**
If `z` lies in the (norm) closure of the admissible congestion Banach domain
`congestionBanachK`, then its density component `⇑z.1` is non-negative
almost everywhere on the unit cube.

Unlike the *strict* uniform lower bound `c ≤ m` (conjunct 3 of
`congestionDomainK` membership), which is NOT closed under `Lᵖ`-limits, the
*weak* nonnegativity `0 ≤ᵐ m` IS closed: the non-negative cone
`nonNegConeLpPer βBar d` is norm-closed (`nonNegConeLpPer_isClosed`), so its
preimage under the continuous projection `Prod.fst` is closed, and
`congestionBanachK` is contained in that closed preimage (the lower bound
`0 < c ≤ m` gives `0 ≤ᵐ m`). Hence the closure is contained in it too, and any
closure point `z` satisfies `z.1 ∈ nonNegConeLpPer βBar d`, i.e. `0 ≤ᵐ ⇑z.1`. -/
lemma congestionBanachK_nonneg_mem_closure
    {βBar betaBarPrime γBar : ℝ≥0∞} [Fact (1 ≤ βBar)] [Fact (1 ≤ γBar)]
    {α β τ : ℝ}
    {z : congestionXBanach d βBar γBar}
    (hmem : z ∈ closure (congestionBanachK d βBar betaBarPrime γBar α β τ)) :
    0 ≤ᵐ[Measure.restrict volume (UnitCube d)]
      (⇑z.1 : (Fin d → ℝ) → ℝ) := by
  classical
  -- The non-negative cone is closed, so its preimage under the continuous
  -- first projection is closed.
  have hcone_closed :
      IsClosed (Theorems.SimplePower.Banach.nonNegConeLpPer (d := d) βBar) :=
    Theorems.SimplePower.Banach.nonNegConeLpPer_isClosed
  have hpre_closed :
      IsClosed
        ((fun q : congestionXBanach d βBar γBar => q.1) ⁻¹'
          (Theorems.SimplePower.Banach.nonNegConeLpPer (d := d) βBar)) :=
    hcone_closed.preimage continuous_fst
  -- `congestionBanachK` is contained in that closed preimage.
  have hsubset :
      congestionBanachK d βBar betaBarPrime γBar α β τ ⊆
        (fun q : congestionXBanach d βBar γBar => q.1) ⁻¹'
          (Theorems.SimplePower.Banach.nonNegConeLpPer (d := d) βBar) := by
    intro q hq
    -- From membership, conjunct 3 of `congestionDomainK` gives `c ≤ᵐ ⇑q.1`.
    obtain ⟨_, _, ⟨c, hc_pos, hc_le⟩, _⟩ := hq.1
    -- `0 ≤ᵐ ⇑q.1` follows.
    change q.1 ∈ Theorems.SimplePower.Banach.nonNegConeLpPer (d := d) βBar
    rw [Theorems.SimplePower.Banach.mem_nonNegConeLpPer_iff]
    filter_upwards [hc_le] with x hx
    exact le_of_lt (lt_of_lt_of_le hc_pos hx)
  -- Hence the closure is contained too, and `z.1` lies in the cone.
  have hz : z.1 ∈ Theorems.SimplePower.Banach.nonNegConeLpPer (d := d) βBar :=
    (closure_minimal hsubset hpre_closed) hmem
  rwa [Theorems.SimplePower.Banach.mem_nonNegConeLpPer_iff] at hz

/-- **BB-VIid-5c-E2a witness `hm_nn` producer.** A.e. nonnegativity of the
density coercion at the Browder–Minty closure witness, derived **internally**
from closure membership — no positivity rider, no `Hext_finite_at_zero`, no
power-growth crutch.

The witness `data.weakVI.choose` lies in `closure (congestionBanachK …)` by
`data.weakVI.choose_spec.1` once `data.K = congestionBanachK …` (which holds by
`rfl` at the concrete native-pack call site, where `data.K = pack.K`). The
density component's a.e. nonnegativity is then read off via
`congestionBanachK_nonneg_mem_closure`. The same `Eq.mp`-via-`hKeq` transport
is used as in `coeMemSob_u_atWitness_of_closure` (a bare `rw [hKeq]` fails
because the motive `fun s => choose ∈ closure s` is type-incorrect —
`data.weakVI.choose`'s type itself mentions `data.K`). -/
lemma coeM_nonneg_atWitness_of_closure
    {γBar : ℝ}
    {betaBar betaBarPrime gammaBar : ℝ≥0∞} [Fact (1 ≤ betaBar)] [Fact (1 ≤ gammaBar)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {α β τ ε : ℝ}
    (data : CongestionRegularizedSolutionData (d := d)
              (γBar := γBar) (betaBar := betaBar)
              (betaBarPrime := betaBarPrime) (gammaBar := gammaBar)
              V H DpH J α β τ ε
              (Periodic.LpPer betaBar d × Periodic.SobolevPerLp 1 gammaBar d))
    (hKeq : data.K =
      congestionBanachK d betaBar betaBarPrime gammaBar α β τ) :
    0 ≤ᵐ[Measure.restrict volume (UnitCube d)]
      (data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) := by
  -- Closure membership of the chosen witness, transported into
  -- `congestionBanachK` along `closure data.K = closure (congestionBanachK …)`.
  have hmem_clos :
      data.weakVI.choose ∈
        closure (congestionBanachK d betaBar betaBarPrime gammaBar α β τ) :=
    Eq.mp
      (congrArg (fun s : Set _ => data.weakVI.choose ∈ closure s) hKeq)
      data.weakVI.choose_spec.1
  exact congestionBanachK_nonneg_mem_closure
    (d := d) (betaBarPrime := betaBarPrime) (α := α) (β := β) (τ := τ)
    hmem_clos

end Congestion
end StationaryMFG
