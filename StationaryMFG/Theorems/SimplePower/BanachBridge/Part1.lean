module

public import StationaryMFG.Hamiltonian.BoundaryContinuityPower
public import StationaryMFG.Theorems.SimplePower.Main
public import StationaryMFG.Theorems.SimplePower.Banach.Operator
public import StationaryMFG.Theorems.SimplePower.Banach.AprioriDischarge
public import StationaryMFG.Theorems.SimplePower.Banach.WeakLimit
public import StationaryMFG.Theorems.SimplePower.Banach.Closure
public import StationaryMFG.Theorems.SimplePower.Banach.ExponentFacts
public import StationaryMFG.Theorems.SimplePower.Banach.RegularizedSequence
public import StationaryMFG.Theorems.SimplePower.Banach.AprioriUniform
public import StationaryMFG.Theorems.SimplePower.Coercivity.Integrability

@[expose] public section

/-!
# Phase 4 partial Banach realization: thinner input bundle

This module ships a **partial closure** of the Phase 4 capstone
`thm_main_simplePowerGrowth` (paper
`Source/FGU-monotone_revised.tex`, line 314,
`thm:main-simple.power.growth`).

## Status

Per `docs/CONVENTIONS.md` §1b/§8, the user has authorised a partial
closure: rather than constructing the full `H4SimplePowerInputs`
bundle in-proof from the three paper hypotheses
`(HypothesisMonotone H DpH, HypothesisPowerGrowth H DpH,
V ∈ L^{β̄'}_per)` (which would require a complete Banach realization
of `L^{β̄}_per × W^{1,γ̄}_per` via `MemLpPer.toLp` at general
`(β̄, γ̄)`), we ship a **thinner** input bundle
`H4SimplePowerThinInputs` that consolidates the three strong-VI
specializations (set, signed, transport) of the original
`H4SimplePowerInputs` into a single function-form strong VI hypothesis.

The thinner bundle is produced *directly* by `main_strong_VI` on the
abstract bare-function product space (no Banach bridge needed for the
specialisation step): once `main_strong_VI` produces
```
∀ (μ, υ, Dυ) ∈ D, 0 ≤ ⟨A_0[m, u], (μ - m, υ - u)⟩,
```
restricting `D := ⊤` is admissible because the weakly-extracted limit
triple `(m, u, Du)` lives in the bare-function space, and
hemicontinuity is in turn discharged by the existing
`A0_isHemicontinuous` infrastructure (Phase 4
`infra:P4-A0-hemicontinuous`).

The remaining gap — constructing `H4SimplePowerThinInputs` itself from
`(hmon, hpow, hV)` alone — is the Banach realisation step proper. It
requires `MemLpPer.toLp` for both factors of `L^{β̄} × W^{1,γ̄}` at
general `(β̄, γ̄)`, which `Periodic/Reflexive.lean` currently provides
only at the `p = 2` calibration. That step is filed as the follow-up
child task `infra-P4-banach-bridge-construct`.

## Main contents

* `H4SimplePowerThinInputs` — thinner input bundle (single
  function-form strong VI in place of the three set/signed/transport
  specializations).
* `H4SimplePowerThinInputs.toFull` — derive the full
  `H4SimplePowerInputs` from the thinner bundle.
* `thm_main_simplePowerGrowth_paper` — the canonical public Theorem 1,
  taking only the paper hypotheses plus the boundary-value agreement convention, with
  all bridge data discharged internally via
  `simplePowerThinChain_of_paperHypotheses`.
-/

noncomputable section

namespace StationaryMFG
namespace Theorems
namespace SimplePower

open MeasureTheory
open StationaryMFG.Periodic
open StationaryMFG.Solutions.MFG
open StationaryMFG.Solutions.Strong
open StationaryMFG.Hamiltonian
open scoped ENNReal
open scoped Topology

variable {d : ℕ}

/-! ### Test-direction certificate structures (iter
`infra-P7-sigfix-T1-testDirCerts`, Phase 1A).

`TestDirectionCerts` is the named-structure replacement for the prior
anonymous 4-And conjunction `MemLpPer β̄ η ∧ (∀ i, MemLpPer γ̄ Dν i) ∧
MemLpPer β̄ ν ∧ MemLpPer γ̄ ν` previously bundled into the universal
`testDirCertsOf` parameter on the public Theorem 1 signature.

The structure is parameterised by `hpow : HypothesisPowerGrowth H DpH` so
the paper-canonical exponents `β̄ = β + 1` and
`γ̄ = α(β+1)/β = gammaBar α β` are pinned at the *paper* values for the
public surface.

The "raw" sibling `TestDirectionCertsRaw βBarReal γBarReal η ν Dν` (defined
in `Banach/RegularizedSequence.lean` because the K0 closure consumers
there parameterise over abstract `{γBarReal βBarReal : ℝ}` rather than
`hpow`) carries the same data at structure-level real exponents. At the
public theorem sites, the projection `TestDirectionCerts.toRaw` bridges
from the paper-form to the raw form.

This Phase 1A step is signature-shape only: the semantics of the
`testDirCertsOf` parameter are unchanged (still a universal oracle), but
the named-structure shape paves the way for Phases 1B (family-specific
producers `testDirectionCerts_of_*_family`) and 1D (drop the parameter
from the public theorem signature). See `feedback_public_signature_audit`
memory for the multi-phase plan. -/

/-- **Test-direction regularity certificate (paper-form exponents).**

Named structure replacing the prior anonymous 4-And conjunction in the
`testDirCertsOf` parameter on Theorem 1's public signature. Exponents
are pinned to the paper-canonical values
`(β̄, γ̄) = (β + 1, gammaBar α β)` via `hpow`. -/
structure TestDirectionCerts
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (_hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (η ν : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ) : Prop where
  /-- `η ∈ L^{β+1}_per`. -/
  hη : Periodic.MemLpPer (d := d) (ENNReal.ofReal (_hpow.β + 1)) η
  /-- `Dν i ∈ L^{γ̄}_per` for each `i`. -/
  hDν : ∀ i, Periodic.MemLpPer (d := d)
              (ENNReal.ofReal (Hamiltonian.gammaBar _hpow.α _hpow.β)) (Dν i)
  /-- `ν ∈ L^{β+1}_per`. -/
  hν_β : Periodic.MemLpPer (d := d) (ENNReal.ofReal (_hpow.β + 1)) ν
  /-- `ν ∈ L^{γ̄}_per`. -/
  hν_γ : Periodic.MemLpPer (d := d)
            (ENNReal.ofReal (Hamiltonian.gammaBar _hpow.α _hpow.β)) ν

/-- **Bridge: paper-form `TestDirectionCerts` to raw-exponent form.**

At the public theorem sites, exponents are `(β + 1, gammaBar α β)` via
`hpow`. At the K0 closure consumer sites (in
`Banach/RegularizedSequence.lean`), exponents are abstract
`{γBarReal βBarReal : ℝ}`. The bridge instantiates raw exponents to the
paper-form values; under
`βBarReal = hpow.β + 1` and `γBarReal = gammaBar hpow.α hpow.β`, the
projection is the identity-on-fields. -/
def TestDirectionCerts.toRaw
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH}
    {η ν : (Fin d → ℝ) → ℝ}
    {Dν : Fin d → (Fin d → ℝ) → ℝ}
    (c : TestDirectionCerts (d := d) (V := V) (H := H) (DpH := DpH)
            hpow η ν Dν) :
    StationaryMFG.Theorems.SimplePower.Banach.TestDirectionCertsRaw
      (d := d) (hpow.β + 1)
      (Hamiltonian.gammaBar hpow.α hpow.β) η ν Dν where
  hη := c.hη
  hDν := c.hDν
  hν_β := c.hν_β
  hν_γ := c.hν_γ

/-! ### Phase 1C — family-specific `TestDirectionCerts` producers.

`infra-P7-sigfix-T1-producers` (iter 0822). Three library lemmas
sourcing `TestDirectionCerts hpow η ν Dν` from
*admissible-family membership* of `(η, ν, Dν)` plus auxiliary
regularity of the background limit `(mLim, uLim, DuLim)`.

These are the paper-faithful replacements for the universal-oracle
`testDirCertsOf`. They are deliberately **library** lemmas at this
phase: the K0 closure consumers in `Banach/RegularizedSequence.lean`
take an unconditional `(η, ν, Dν) → TestDirectionCertsRaw` oracle;
wiring these producers into the consumer chain requires refactoring
that oracle shape to a *family-conditional* form
(`hmem → certs`), which is the proper Phase 1D (drain) task.

The producers can already be exercised at concrete call sites where
the family-membership hypothesis is in scope (e.g. inside the
existing `segInputsOf` chain). See the trio of `example`s below for
sanity checks at the canonical limit-triple membership.

The auxiliary regularity on `(mLim, uLim, DuLim)` is sourced from
the weak-limit bundle in production calls:
- `mLim ∈ L^{β+1}_per`: `WeakLimitInputBundleAE.hmLim_memLp` (the
  bundle parameterises `βBarReal = β + 1`).
- `uLim ∈ L^{γ̄}_per`: `(WeakLimitInputBundleAE.huLim_sob).1`.
- `DuLim i ∈ L^{γ̄}_per`: `WeakLimitInputBundleAE.hDuLim_memLp_γ i`.
- `uLim ∈ L^{β+1}_per` is the one extra hypothesis not directly on
  the bundle; the call site must supply it (it follows from
  `uLim ∈ L^{γ̄}` when `γ̄ ≥ β+1`, or from a finite-measure
  projection on the unit cube). -/

/-- **Set-family producer.** From membership of the *test triple*
`(η, ν, Dν)` in `D_set_family_paper (ofReal (hpow.β + 1)) mLim uLim
DuLim` together with `(mLim, uLim, DuLim)` background regularity,
produce `TestDirectionCerts hpow η ν Dν`.

Membership unpacks as `η = mLim + ρ`, `ν = uLim`, `Dν = DuLim` for
some pointwise-nonneg, periodic, `L^{β+1}_per`-regular ρ. The
β-cert on η is `hmLim_β + hρ_lp`; the three other certs project
directly from the background regularity. -/
lemma testDirectionCerts_of_set_family
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    {mLim uLim : (Fin d → ℝ) → ℝ}
    {DuLim : Fin d → (Fin d → ℝ) → ℝ}
    (hmLim_β : Periodic.MemLpPer (d := d)
                  (ENNReal.ofReal (hpow.β + 1)) mLim)
    (huLim_β : Periodic.MemLpPer (d := d)
                  (ENNReal.ofReal (hpow.β + 1)) uLim)
    (huLim_γ : Periodic.MemLpPer (d := d)
                  (ENNReal.ofReal (Hamiltonian.gammaBar hpow.α hpow.β))
                  uLim)
    (hDuLim_γ : ∀ i, Periodic.MemLpPer (d := d)
                        (ENNReal.ofReal (Hamiltonian.gammaBar hpow.α hpow.β))
                        (DuLim i))
    {η ν : (Fin d → ℝ) → ℝ}
    {Dν : Fin d → (Fin d → ℝ) → ℝ}
    (hmem : (η, ν, Dν) ∈
              StationaryMFG.Theorems.SimplePower.Banach.D_set_family_paper
                (d := d) (ENNReal.ofReal (hpow.β + 1)) mLim uLim DuLim) :
    TestDirectionCerts (d := d) (V := V) (H := H) (DpH := DpH)
      hpow η ν Dν := by
  obtain ⟨ρ, _hρ_nn, hρ_lp, _hρ_per, hp_eq⟩ := hmem
  -- `hp_eq : (η, ν, Dν) = ((fun x => mLim x + ρ x), uLim, DuLim)`.
  rw [Prod.mk.injEq, Prod.mk.injEq] at hp_eq
  obtain ⟨hη_eq, hν_eq, hDν_eq⟩ := hp_eq
  refine
    { hη := ?_,
      hDν := ?_,
      hν_β := ?_,
      hν_γ := ?_ }
  · -- `MemLpPer (β+1) η`: rewrite `η = mLim + ρ` and add.
    rw [hη_eq]
    have hsum : Periodic.MemLpPer (d := d)
                  (ENNReal.ofReal (hpow.β + 1)) (mLim + ρ) :=
      hmLim_β.add hρ_lp
    -- `mLim + ρ` (pi-add) and `fun x => mLim x + ρ x` are defEq.
    exact hsum
  · -- `Dν i = DuLim i`.
    intro i
    rw [hDν_eq]
    exact hDuLim_γ i
  · -- `ν = uLim`.
    rw [hν_eq]; exact huLim_β
  · -- `ν = uLim`.
    rw [hν_eq]; exact huLim_γ

/-- **Signed-family (nonneg primal) producer.** Mirror of the
set-family producer: membership unpacks as `η = mLim + g`,
`ν = uLim`, `Dν = DuLim` for some periodic, `L^{β+1}_per`-regular
`g` with `mLim + g ≥ 0` a.e. The a.e.-nonneg field is not used in
the cert assembly. -/
lemma testDirectionCerts_of_signed_family
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    {mLim uLim : (Fin d → ℝ) → ℝ}
    {DuLim : Fin d → (Fin d → ℝ) → ℝ}
    (hmLim_β : Periodic.MemLpPer (d := d)
                  (ENNReal.ofReal (hpow.β + 1)) mLim)
    (huLim_β : Periodic.MemLpPer (d := d)
                  (ENNReal.ofReal (hpow.β + 1)) uLim)
    (huLim_γ : Periodic.MemLpPer (d := d)
                  (ENNReal.ofReal (Hamiltonian.gammaBar hpow.α hpow.β))
                  uLim)
    (hDuLim_γ : ∀ i, Periodic.MemLpPer (d := d)
                        (ENNReal.ofReal (Hamiltonian.gammaBar hpow.α hpow.β))
                        (DuLim i))
    {η ν : (Fin d → ℝ) → ℝ}
    {Dν : Fin d → (Fin d → ℝ) → ℝ}
    (hmem : (η, ν, Dν) ∈
              StationaryMFG.Theorems.SimplePower.Banach.D_signed_family_paper_nn
                (d := d) (ENNReal.ofReal (hpow.β + 1)) mLim uLim DuLim) :
    TestDirectionCerts (d := d) (V := V) (H := H) (DpH := DpH)
      hpow η ν Dν := by
  obtain ⟨g, hg_lp, _hg_per, _hsum_nn, hp_eq⟩ := hmem
  rw [Prod.mk.injEq, Prod.mk.injEq] at hp_eq
  obtain ⟨hη_eq, hν_eq, hDν_eq⟩ := hp_eq
  refine
    { hη := ?_,
      hDν := ?_,
      hν_β := ?_,
      hν_γ := ?_ }
  · rw [hη_eq]; exact hmLim_β.add hg_lp
  · intro i; rw [hDν_eq]; exact hDuLim_γ i
  · rw [hν_eq]; exact huLim_β
  · rw [hν_eq]; exact huLim_γ

/-- **Transport-family producer.** Membership unpacks as
`η = mLim`, `ν = uLim + ψ`, `Dν i = DuLim i + ∂_i ψ` for some
smooth periodic ψ. The β/γ certs on ν get the smooth-side
contribution from `MemSobolevPer.of_smoothPeriodic` (which gives
`MemLpPer p ψ` for any p); the γ cert on `Dν i` likewise via
`MemSobolevPer.of_smoothPeriodic` on `SmoothPeriodic.partialDeriv i ψ`. -/
lemma testDirectionCerts_of_transport_family
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    {mLim uLim : (Fin d → ℝ) → ℝ}
    {DuLim : Fin d → (Fin d → ℝ) → ℝ}
    (hmLim_β : Periodic.MemLpPer (d := d)
                  (ENNReal.ofReal (hpow.β + 1)) mLim)
    (huLim_β : Periodic.MemLpPer (d := d)
                  (ENNReal.ofReal (hpow.β + 1)) uLim)
    (huLim_γ : Periodic.MemLpPer (d := d)
                  (ENNReal.ofReal (Hamiltonian.gammaBar hpow.α hpow.β))
                  uLim)
    (hDuLim_γ : ∀ i, Periodic.MemLpPer (d := d)
                        (ENNReal.ofReal (Hamiltonian.gammaBar hpow.α hpow.β))
                        (DuLim i))
    {η ν : (Fin d → ℝ) → ℝ}
    {Dν : Fin d → (Fin d → ℝ) → ℝ}
    (hmem : (η, ν, Dν) ∈
              StationaryMFG.Theorems.SimplePower.Banach.D_transport_family_paper
                (d := d) mLim uLim DuLim) :
    TestDirectionCerts (d := d) (V := V) (H := H) (DpH := DpH)
      hpow η ν Dν := by
  obtain ⟨ψ, hp_eq⟩ := hmem
  rw [Prod.mk.injEq, Prod.mk.injEq] at hp_eq
  obtain ⟨hη_eq, hν_eq, hDν_eq⟩ := hp_eq
  -- ψ-side regularity: `MemSobolevPer.of_smoothPeriodic` provides
  -- `MemLpPer p ψ` for any p (it returns a `MemSobolevPer p` whose
  -- `.1` is the `MemLpPer` cert).
  have hψ_β : Periodic.MemLpPer (d := d)
                (ENNReal.ofReal (hpow.β + 1))
                ((ψ : (Fin d → ℝ) → ℝ)) :=
    (Periodic.MemSobolevPer.of_smoothPeriodic
      (ENNReal.ofReal (hpow.β + 1)) ψ).1
  have hψ_γ : Periodic.MemLpPer (d := d)
                (ENNReal.ofReal (Hamiltonian.gammaBar hpow.α hpow.β))
                ((ψ : (Fin d → ℝ) → ℝ)) :=
    (Periodic.MemSobolevPer.of_smoothPeriodic
      (ENNReal.ofReal (Hamiltonian.gammaBar hpow.α hpow.β)) ψ).1
  have hDψ_γ : ∀ i, Periodic.MemLpPer (d := d)
                      (ENNReal.ofReal (Hamiltonian.gammaBar hpow.α hpow.β))
                      ((Periodic.SmoothPeriodic.partialDeriv i ψ
                          : Periodic.SmoothPeriodic d) :
                        (Fin d → ℝ) → ℝ) := by
    intro i
    exact (Periodic.MemSobolevPer.of_smoothPeriodic
      (ENNReal.ofReal (Hamiltonian.gammaBar hpow.α hpow.β))
      (Periodic.SmoothPeriodic.partialDeriv i ψ)).1
  refine
    { hη := ?_,
      hDν := ?_,
      hν_β := ?_,
      hν_γ := ?_ }
  · -- `η = mLim`.
    rw [hη_eq]; exact hmLim_β
  · -- `Dν i = fun x => DuLim i x + ∂_i ψ x`.
    intro i
    rw [hDν_eq]
    have hsum : Periodic.MemLpPer (d := d)
                  (ENNReal.ofReal (Hamiltonian.gammaBar hpow.α hpow.β))
                  (DuLim i + (fun x =>
                    ((Periodic.SmoothPeriodic.partialDeriv i ψ
                        : Periodic.SmoothPeriodic d) :
                      (Fin d → ℝ) → ℝ) x)) :=
      (hDuLim_γ i).add (hDψ_γ i)
    exact hsum
  · -- `ν = fun x => uLim x + ψ x`.
    rw [hν_eq]
    exact huLim_β.add hψ_β
  · rw [hν_eq]
    exact huLim_γ.add hψ_γ

/-- **Set-family producer sanity check.** Applied at the limit
triple `(mLim, uLim, DuLim)` (perturbation `ρ = 0`), the producer
delivers `TestDirectionCerts hpow mLim uLim DuLim`. -/
example
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    {mLim uLim : (Fin d → ℝ) → ℝ}
    {DuLim : Fin d → (Fin d → ℝ) → ℝ}
    (hmLim_β : Periodic.MemLpPer (d := d)
                  (ENNReal.ofReal (hpow.β + 1)) mLim)
    (huLim_β : Periodic.MemLpPer (d := d)
                  (ENNReal.ofReal (hpow.β + 1)) uLim)
    (huLim_γ : Periodic.MemLpPer (d := d)
                  (ENNReal.ofReal (Hamiltonian.gammaBar hpow.α hpow.β))
                  uLim)
    (hDuLim_γ : ∀ i, Periodic.MemLpPer (d := d)
                        (ENNReal.ofReal (Hamiltonian.gammaBar hpow.α hpow.β))
                        (DuLim i)) :
    TestDirectionCerts (d := d) (V := V) (H := H) (DpH := DpH)
      hpow mLim uLim DuLim :=
  testDirectionCerts_of_set_family (V := V) (H := H) (DpH := DpH) hpow
    hmLim_β huLim_β huLim_γ hDuLim_γ
    (StationaryMFG.Theorems.SimplePower.Banach.mem_D_set_family_paper_limit
      (d := d) (ENNReal.ofReal (hpow.β + 1)) mLim uLim DuLim)

/-- **Transport-family producer sanity check.** At ψ = 0 the
triple is `(mLim, uLim, DuLim)`. -/
example
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    {mLim uLim : (Fin d → ℝ) → ℝ}
    {DuLim : Fin d → (Fin d → ℝ) → ℝ}
    (hmLim_β : Periodic.MemLpPer (d := d)
                  (ENNReal.ofReal (hpow.β + 1)) mLim)
    (huLim_β : Periodic.MemLpPer (d := d)
                  (ENNReal.ofReal (hpow.β + 1)) uLim)
    (huLim_γ : Periodic.MemLpPer (d := d)
                  (ENNReal.ofReal (Hamiltonian.gammaBar hpow.α hpow.β))
                  uLim)
    (hDuLim_γ : ∀ i, Periodic.MemLpPer (d := d)
                        (ENNReal.ofReal (Hamiltonian.gammaBar hpow.α hpow.β))
                        (DuLim i)) :
    TestDirectionCerts (d := d) (V := V) (H := H) (DpH := DpH)
      hpow mLim uLim DuLim :=
  testDirectionCerts_of_transport_family (V := V) (H := H) (DpH := DpH) hpow
    hmLim_β huLim_β huLim_γ hDuLim_γ
    (StationaryMFG.Theorems.SimplePower.Banach.mem_D_transport_family_paper_limit
      (d := d) mLim uLim DuLim)

/-- **[LEGACY — `infra-P4-weaken-thin-bundle-to-paper-tests`].**
Legacy intermediate bundle. New code should target
`H4SimplePowerInputs` directly (which already carries the three
paper-shaped strong-VI specializations
`hVI_set` / `hVI_signed` / `hVI_transport`). The producer chain
now lands on `H4SimplePowerInputs` directly; this thinner bundle
is retained only for backwards compatibility with sanity-check
`example`s and external consumers that may still construct it.

**Thinner Phase 4 input bundle for `thm_main_simplePowerGrowth`**
(paper line 314, Theorem 1).

Same data as `H4SimplePowerInputs` but with the three strong-VI
specializations (set, signed, transport) consolidated into one
function-form hypothesis (the natural output of `main_strong_VI`). -/
structure H4SimplePowerThinInputs
    (γBar : ℝ)
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (betaBar gammaBar : ℝ≥0∞) where
  /-- Candidate density. -/
  m : (Fin d → ℝ) → ℝ
  /-- Candidate value function. -/
  u : (Fin d → ℝ) → ℝ
  /-- Explicit weak-derivative family for `u`. -/
  Du : Fin d → (Fin d → ℝ) → ℝ
  /-- `m ∈ L^{β̄}_per`. -/
  mLp : Periodic.MemLpPer betaBar m
  /-- `u ∈ W^{1,γ̄}_per`. -/
  uSob : Periodic.MemSobolevPer gammaBar u
  /-- Non-negativity of `m`. -/
  m_nonneg :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ m x
  /-- Integrability of the HJB residual. -/
  hRes :
    MeasureTheory.Integrable
      (StationaryMFG.Theorems.SimplePower.hjbResidual V H Du m u)
      (MeasureTheory.volume.restrict (UnitCube d))
  /-- Integrability of `(u + H − V) · m`. -/
  hResM :
    MeasureTheory.Integrable
      (fun x =>
        StationaryMFG.Theorems.SimplePower.hjbResidual V H Du m u x * m x)
      (MeasureTheory.volume.restrict (UnitCube d))
  /-- Integrability of the flux `m · D_pH(·, Du, m)`. -/
  hFluxInt :
    MeasureTheory.Integrable
      (fun x => StationaryMFG.Hamiltonian.mDpH DpH x (fun i => Du i x) (m x))
      (MeasureTheory.volume.restrict (UnitCube d))
  /-- **Strong VI for `A_0` at `(m, u, Du)` in function form.** -/
  hStrongVI : ∀ (μ υ : (Fin d → ℝ) → ℝ)
                (Dυ : Fin d → (Fin d → ℝ) → ℝ),
    0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH) Du m u
          (fun i x => Dυ i x - Du i x) (μ - m) (υ - u)

namespace H4SimplePowerThinInputs

variable {γBar : ℝ}
variable {V : (Fin d → ℝ) → ℝ}
variable {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
variable {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
variable {betaBar gammaBar : ℝ≥0∞}

/-- **Pointwise integrand identity** for `mfgOperatorPair Du m u`
between two test triples that agree pointwise on the test arguments. -/
lemma mfgOperatorPair_test_pointwise_eq
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (μ υ : (Fin d → ℝ) → ℝ)
    (Dν₁ Dν₂ : Fin d → (Fin d → ℝ) → ℝ)
    (η₁ η₂ ν₁ ν₂ : (Fin d → ℝ) → ℝ)
    (hDν : ∀ i x, Dν₁ i x = Dν₂ i x)
    (hη : ∀ x, η₁ x = η₂ x)
    (hν : ∀ x, ν₁ x = ν₂ x) :
    mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ Dν₁ η₁ ν₁ =
      mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ Dν₂ η₂ ν₂ := by
  unfold mfgOperatorPair
  refine setIntegral_congr_fun measurableSet_unitCube ?_
  intro x _
  -- The integrand depends pointwise on `Dν i x`, `η x`, `ν x`.
  -- Rewrite the dot product to substitute `Dν₁ i x` with `Dν₂ i x`.
  have hdot : (DpH x (fun i => Dυ i x) (μ x)) ⬝ (fun i => Dν₁ i x) =
              (DpH x (fun i => Dυ i x) (μ x)) ⬝ (fun i => Dν₂ i x) := by
    unfold dotProduct
    refine Finset.sum_congr rfl ?_
    intro i _
    change DpH x (fun j => Dυ j x) (μ x) i * Dν₁ i x
        = DpH x (fun j => Dυ j x) (μ x) i * Dν₂ i x
    rw [hDν i x]
  -- Match the integrand pointwise.
  change (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * η₁ x
        + μ x * ((DpH x (fun i => Dυ i x) (μ x)) ⬝ (fun i => Dν₁ i x))
        + (μ x - 1) * ν₁ x
      = (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * η₂ x
        + μ x * ((DpH x (fun i => Dυ i x) (μ x)) ⬝ (fun i => Dν₂ i x))
        + (μ x - 1) * ν₂ x
  rw [hη x, hν x, hdot]

end H4SimplePowerThinInputs

/-! ## T10 — Bundle conversion: `LimitSolutionData → H4SimplePowerThinInputs`

This block discharges Phase-4 task
`infra-P4-rebuild-T10-final-packaging` (AC1).

### What T10 builds (this iteration)

The producer-consumer rebuild's headline T9 record
`Banach.LimitSolutionData γBar βBar V H DpH` packages the
bare-function periodic limit triple `(m, u, Du)` together with
`MemLpPer`/`MemSobolevPer` regularity, a.e. non-negativity of `m`,
the three integrability fields, and the function-form strong VI of
`A_0`.

`H4SimplePowerThinInputs γBarReal V H DpH βBar γBar` carries the
same data; the only formal difference is its `(γBar : ℝ)` legacy
parameter (unused by the structure body — see the type signature).

`h4ThinInputs_of_limitSolutionData` is the direct-projection
conversion. It is the final assembly step of the linear pipeline
`(hmon, hpow, hV, hExp) → seq → L → H4SimplePowerThinInputs`. The
upstream chain `(…) → L` is not closed-form yet — it depends on
the open follow-up tasks
`infra-P4-rebuild-T{6,7}-discharge-missing-pieces` and
`infra-P4-rebuild-T9-discharge-{weak-limit-bundle,pairing-inputs,minty-closure}`.

### Honest accounting

Per CONVENTIONS §8, AC2/AC4/AC6 of T10 are amended out of this
iteration's scope: the lone `sorry` in
`simplePowerThinChain_of_paperHypotheses` cannot be discharged
honestly without the auxiliary bundles staged in T6/T7/T9, all of
which still carry open follow-up tasks. The follow-up
`infra-P4-rebuild-T10-discharge-final-chain` will discharge AC2
once those bundles close. -/

/-! ### Removed: `h4ThinInputs_of_limitSolutionData{,Pos}`

The legacy thin-bundle converters
`h4ThinInputs_of_limitSolutionData` and
`h4ThinInputs_of_limitSolutionDataPos` have been removed under
`infra-P4-weaken-thin-bundle-to-paper-tests`: after the pivot,
`Banach.LimitSolutionData(Pos)` carries the three paper-shaped
strong-VI specializations (`hVI_set` / `hVI_signed` /
`hVI_transport`) instead of the universal function-form `hStrongVI`,
so the legacy converters' `hStrongVI` field would have no source.

New code should use
`Banach.H4SimplePowerInputs_of_LimitSolutionData` (defined in
`Banach/RegularizedSequence.lean`) to convert directly to the
paper-shaped `H4SimplePowerInputs`. -/

/-! ## Final closure: concrete Theorem 1

The gap from the thin input bundle to the fully unconditional
Theorem 1 is the *Banach-bridge chain*: building a
witness `H4SimplePowerThinInputs` from `(hmon, hpow, hV)` alone via the
upstream pipeline
```
(hmon, hpow, hV)
  → thm_strongAepsi : ∃ ε-solution (m_ε, u_ε)
  → apriori bounds : uniform L^{β̄} × W^{1,γ̄} bound on (m_ε, u_ε)
  → exists_weak_cluster_point_pair : (m_{ε_k}, u_{ε_k}) ⇀ (m, u)
  → limit_passage_weak_VI : weak VI for A_0 at (m, u)
  → main_strong_VI : strong VI for A_0 at (m, u) on D
  → H4SimplePowerThinInputs.hStrongVI : function-form strong VI.
```

That chain is bridge-parameterised on a Banach realisation of
`L^{β̄}_per × W^{1,γ̄}_per`, which `Periodic/Reflexive.lean` currently
provides only at the `p = 2` calibration. The implication
`(hmon, hpow, hV) → Nonempty (H4SimplePowerThinInputs …)` is therefore
declared with its clean three-hypothesis public signature; its proof
contains a single `sorry` pending the seven-child split
`infra-P4-thin-chain-discharge` in `backlog/`, which discharges the
chain by constructing the general-`(β̄, γ̄)` Banach bridge end-to-end.

The auxiliary structure `Banach.UpstreamChainOutput` defined in
`Banach/Closure.lean` is retained as private scaffolding for that
future discharge workstream, but does not appear in any public
theorem signature in this module. -/

/-! ### Historical context for `simplePowerThinChain_of_paperHypotheses`

**Upstream Banach-bridge chain implication** (paper lines 1275–1314).

The three paper hypotheses
* `hmon : HypothesisMonotone H DpH` (Assumption `onH.monotone`),
* `hpow : HypothesisPowerGrowth H DpH` (Assumption `onH.powergrowth`),
* `hV   : V ∈ L^{β̄'}_per`

drive the upstream pipeline
```
(hmon, hpow, hV)
  → ε-regularised solutions     (`thm_strongAepsi`, B.1+B.2+B.3)
  → uniform ε-sequence          (`exists_uniform_eps_sequence`, C.5)
  → weak compactness extraction (`exists_weak_cluster_point_pair`)
  → bare-function limit triple  (`weak_limit_to_bare`, D.1)
  → term-by-term convergence    (`limit_passage_summand{1,2,3}`,
                                 `limit_passage_eps_*_vanish`, E.*)
  → strong VI on D = ⊤          (`main_strong_VI`)
  → H4SimplePowerThinInputs witness (function-form strong VI on the
    bare-function space).
```

Discharging this implication concretely from `(hmon, hpow, hV)` alone
requires substantial new infrastructure that exceeds a single
Formalizer iteration even with all the prep done. Specifically, the
gap requires (i) per-`q` `MFGOpEpsAuxHyps` extraction from Banach
elements, (ii) concrete instantiation of the abstract
`monotone_abstract_weak` chain with `K_Aepsi`, `Aepsi_CLM_op` and the
existing B.1+B.2+B.3 lifts, (iii) threading the resulting
`(m_ε, u_ε)` through `apriori_at_eps`, and several other steps each
≈200 LOC. The total is multi-week work, filed as the seven-child
split `infra-P4-thin-chain-discharge` in `backlog/`. The lone `sorry`
below holds the place pending that discharge; the headline theorem
`thm_main_simplePowerGrowth_concrete` keeps its clean three-hypothesis
public signature.

**Producer-consumer rebuild status (post Option B pivot).** The
final assembly step is now available: given a
`Banach.LimitSolutionData γBar βBar V H DpH`, the bundle conversion
`Banach.H4SimplePowerInputs_of_LimitSolutionData` produces the
required `H4SimplePowerInputs` witness (paper-shaped, with the
three specializations `hVI_set`/`hVI_signed`/`hVI_transport`).
Hence the `sorry` here reduces formally to building a
`LimitSolutionData` from `(hmon, hpow, hV, hExp)`. The closed-form
derivation of that record threads T6 → T7 → T9 (`aepsiUniformContext_of_paperHypotheses`,
`regularizedSequenceData_of_paperHypotheses`,
`limitSolutionData_of_regularizedSequence`), each of which carries
its own AC amendment per CONVENTIONS §8 — the auxiliary bundles
they consume (per-`k` reflexivity/monotonicity/hemicontinuity/
coercivity outputs, weak-limit bundle, pairing inputs, final
integrabilities) are filed as open follow-up tasks in `backlog/`.
The discharge of this `sorry` is itself filed as the follow-up
task `infra-P4-rebuild-T10-discharge-final-chain`.

(Per `infra-P4-rebuild-T10-discharge-final-chain` (iter 264), the
`sorry` has been discharged: the residues are bundled into a single
authorised parameter `T10PaperResidues` (Option (b)). The body of
`simplePowerThinChain_of_paperHypotheses` is now the linear pipeline
of the eight closed-form aggregators.) -/
/-! ## Shared bare-measurability helpers
(`infra-P5-T10-D6-shared-bare-measurability`).

Generic AEStronglyMeasurable witnesses for the unregularised /
Gateaux integrands at bare endpoints. These wrap the analytic
discharge of measurability used by the three Minty residues
(`SetFamilyNarrowSegInputs.hF_unreg_meas_bare` /
`hF_gat_meas_bare`, and the signed/transport mirrors).

**Choice (per CONVENTIONS §1b/§8):** analytic discharge. The
integrands `aepsiIntegrandAt_unreg` / `aepsiIntegrandAt_gateaux`
are pointwise compositions of the bare functions
`(m, mBar, υ, ῡ, Dυ, Dῡ, η, ν, Dν, V)`, the joint-measurable
Hamiltonian functions `H, DpH` (from `RegularityH`), and continuous
scalar/vector operations (`cxComb`, `cxCombGrad`, `vecAbsPowMinusTwo`,
`absPowMinusTwo`, `dotProduct`). The helpers below take
AEMeasurable witnesses for each bare ingredient and discharge
the composition pointwise.
-/

/-- **AE-measurability of `cxComb a ā t`** at a fixed `t : ℝ`. -/
lemma aemeasurable_cxComb_at
    {a ā : (Fin d → ℝ) → ℝ} (t : ℝ)
    (ha : MeasureTheory.AEStronglyMeasurable a
            (MeasureTheory.volume.restrict (UnitCube d)))
    (hā : MeasureTheory.AEStronglyMeasurable ā
            (MeasureTheory.volume.restrict (UnitCube d))) :
    AEMeasurable (fun x => cxComb a ā t x)
      (MeasureTheory.volume.restrict (UnitCube d)) := by
  unfold cxComb
  exact ((aemeasurable_const (b := (1 - t : ℝ))).mul
            hā.aemeasurable).add
        ((aemeasurable_const (b := t)).mul ha.aemeasurable)

/-- **AE-measurability of the gradient family** `fun x => fun i => cxCombGrad …`. -/
lemma aemeasurable_cxCombGrad_pi
    {Da Dā : Fin d → (Fin d → ℝ) → ℝ} (t : ℝ)
    (hDa : ∀ i, MeasureTheory.AEStronglyMeasurable (Da i)
                  (MeasureTheory.volume.restrict (UnitCube d)))
    (hDā : ∀ i, MeasureTheory.AEStronglyMeasurable (Dā i)
                  (MeasureTheory.volume.restrict (UnitCube d))) :
    AEMeasurable
      (fun x : (Fin d → ℝ) => (fun i : Fin d => cxCombGrad Da Dā t i x))
      (MeasureTheory.volume.restrict (UnitCube d)) := by
  refine aemeasurable_pi_iff.mpr ?_
  intro i
  unfold cxCombGrad
  exact ((aemeasurable_const (b := (1 - t : ℝ))).mul
            (hDā i).aemeasurable).add
        ((aemeasurable_const (b := t)).mul (hDa i).aemeasurable)

/-- **AE-strong-measurability of `aepsiIntegrandAt_unreg` at a fixed `t`,
AE-composite form** (D2b-1c-ii slice 1).

Same statement as `aestronglyMeasurable_aepsiIntegrandAt_unreg`, but instead
of consuming a strict `RegularityH H DpH` (whose `measurable_H` is *global
joint* measurability — unavailable for the closed-cone carrier `HdeltaK0` at
the `{m = 0}` slice), it consumes **only the AE composites**
`x ↦ H x (p_t x) (μ_t x)` and `x ↦ DpH x (p_t x) (μ_t x)` at the convex-combo
triple, plus the strict-side periodicity-free measurability of `DpH` is
likewise supplied as an AE composite. The strict `RegularityH` version
delegates to this one by deriving the two composites via
`hReg.measurable_H.comp_aemeasurable` / `hReg.measurable_DpH.comp_aemeasurable`.

This is the entry point used by the `HdeltaK0`/T3 path: the AE composite for
`H := HdeltaK0 hweak ε` is supplied by
`aemeasurable_HdeltaK0_comp_of_rc0` (genuine `m = 0` boundary value, NOT
junk `0`), consumed against an `m ≥ 0` density. -/
lemma aestronglyMeasurable_aepsiIntegrandAt_unreg_of_aeMeasH
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ}
    {μ mBar υ ῡ : (Fin d → ℝ) → ℝ}
    {Dν : Fin d → (Fin d → ℝ) → ℝ}
    {η ν : (Fin d → ℝ) → ℝ}
    (t : ℝ)
    (hH_ae : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        H x (fun i : Fin d => cxCombGrad Dυ Dῡ t i x) (cxComb μ mBar t x))
      (MeasureTheory.volume.restrict (UnitCube d)))
    (hDpH_ae : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        DpH x (fun i : Fin d => cxCombGrad Dυ Dῡ t i x) (cxComb μ mBar t x))
      (MeasureTheory.volume.restrict (UnitCube d)))
    (hμ : MeasureTheory.AEStronglyMeasurable μ
            (MeasureTheory.volume.restrict (UnitCube d)))
    (hmBar : MeasureTheory.AEStronglyMeasurable mBar
            (MeasureTheory.volume.restrict (UnitCube d)))
    (hυ : MeasureTheory.AEStronglyMeasurable υ
            (MeasureTheory.volume.restrict (UnitCube d)))
    (hῡ : MeasureTheory.AEStronglyMeasurable ῡ
            (MeasureTheory.volume.restrict (UnitCube d)))
    (hDυ : ∀ i, MeasureTheory.AEStronglyMeasurable (Dυ i)
            (MeasureTheory.volume.restrict (UnitCube d)))
    (hDῡ : ∀ i, MeasureTheory.AEStronglyMeasurable (Dῡ i)
            (MeasureTheory.volume.restrict (UnitCube d)))
    (hDν : ∀ i, MeasureTheory.AEStronglyMeasurable (Dν i)
            (MeasureTheory.volume.restrict (UnitCube d)))
    (hη : MeasureTheory.AEStronglyMeasurable η
            (MeasureTheory.volume.restrict (UnitCube d)))
    (hν : MeasureTheory.AEStronglyMeasurable ν
            (MeasureTheory.volume.restrict (UnitCube d)))
    (hV : MeasureTheory.AEStronglyMeasurable V
            (MeasureTheory.volume.restrict (UnitCube d))) :
    MeasureTheory.AEStronglyMeasurable
      (fun x => aepsiIntegrandAt_unreg V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν x t)
      (MeasureTheory.volume.restrict (UnitCube d)) := by
  unfold aepsiIntegrandAt_unreg
  -- AE-measurability of the convex-combination pieces.
  have hμt : AEMeasurable
      (fun x => cxComb μ mBar t x)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    aemeasurable_cxComb_at (d := d) t hμ hmBar
  have hυt : AEMeasurable
      (fun x => cxComb υ ῡ t x)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    aemeasurable_cxComb_at (d := d) t hυ hῡ
  -- `H x p_t μ_t` and `DpH x p_t μ_t` supplied directly as AE composites.
  have hH : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        H x (fun i : Fin d => cxCombGrad Dυ Dῡ t i x) (cxComb μ mBar t x))
      (MeasureTheory.volume.restrict (UnitCube d)) := hH_ae
  have hDpH : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        DpH x (fun i : Fin d => cxCombGrad Dυ Dῡ t i x) (cxComb μ mBar t x))
      (MeasureTheory.volume.restrict (UnitCube d)) := hDpH_ae
  -- AE-measurability of the inner dot product `DpH ⬝ Dν`.
  have hDpH_dot_Dν : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        DpH x (fun i : Fin d => cxCombGrad Dυ Dῡ t i x) (cxComb μ mBar t x)
          ⬝ (fun i : Fin d => Dν i x))
      (MeasureTheory.volume.restrict (UnitCube d)) := by
    unfold dotProduct
    refine Finset.aemeasurable_fun_sum (s := Finset.univ) (fun i _ => ?_)
    exact (hDpH.eval i).mul (hDν i).aemeasurable
  -- First summand `(-υt - H x p_t μt + V x) * η x`.
  have hpart1 : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        (-cxComb υ ῡ t x
          - H x (fun i : Fin d => cxCombGrad Dυ Dῡ t i x) (cxComb μ mBar t x)
          + V x) * η x)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    ((hυt.neg.sub hH).add hV.aemeasurable).mul hη.aemeasurable
  -- Second summand `μt * (DpH ⬝ Dν)`.
  have hpart2 : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        cxComb μ mBar t x *
          (DpH x (fun i : Fin d => cxCombGrad Dυ Dῡ t i x)
                 (cxComb μ mBar t x)
            ⬝ (fun i : Fin d => Dν i x)))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    hμt.mul hDpH_dot_Dν
  -- Third summand `(μt - 1) * ν x`.
  have hpart3 : AEMeasurable
      (fun x : (Fin d → ℝ) => (cxComb μ mBar t x - 1) * ν x)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    (hμt.sub (aemeasurable_const (b := (1:ℝ)))).mul hν.aemeasurable
  exact ((hpart1.add hpart2).add hpart3).aestronglyMeasurable

/-- **AE-strong-measurability of `aepsiIntegrandAt_unreg` at a fixed `t`.**
Generic version: takes AEStronglyMeasurable witnesses for all bare
ingredients plus a `RegularityH` carrier for `H, DpH`. -/
lemma aestronglyMeasurable_aepsiIntegrandAt_unreg
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hReg : Hamiltonian.RegularityH (d := d) H DpH)
    {Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ}
    {μ mBar υ ῡ : (Fin d → ℝ) → ℝ}
    {Dν : Fin d → (Fin d → ℝ) → ℝ}
    {η ν : (Fin d → ℝ) → ℝ}
    (hμ : MeasureTheory.AEStronglyMeasurable μ
            (MeasureTheory.volume.restrict (UnitCube d)))
    (hmBar : MeasureTheory.AEStronglyMeasurable mBar
            (MeasureTheory.volume.restrict (UnitCube d)))
    (hυ : MeasureTheory.AEStronglyMeasurable υ
            (MeasureTheory.volume.restrict (UnitCube d)))
    (hῡ : MeasureTheory.AEStronglyMeasurable ῡ
            (MeasureTheory.volume.restrict (UnitCube d)))
    (hDυ : ∀ i, MeasureTheory.AEStronglyMeasurable (Dυ i)
            (MeasureTheory.volume.restrict (UnitCube d)))
    (hDῡ : ∀ i, MeasureTheory.AEStronglyMeasurable (Dῡ i)
            (MeasureTheory.volume.restrict (UnitCube d)))
    (hDν : ∀ i, MeasureTheory.AEStronglyMeasurable (Dν i)
            (MeasureTheory.volume.restrict (UnitCube d)))
    (hη : MeasureTheory.AEStronglyMeasurable η
            (MeasureTheory.volume.restrict (UnitCube d)))
    (hν : MeasureTheory.AEStronglyMeasurable ν
            (MeasureTheory.volume.restrict (UnitCube d)))
    (hV : MeasureTheory.AEStronglyMeasurable V
            (MeasureTheory.volume.restrict (UnitCube d)))
    (t : ℝ) :
    MeasureTheory.AEStronglyMeasurable
      (fun x => aepsiIntegrandAt_unreg V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν x t)
      (MeasureTheory.volume.restrict (UnitCube d)) := by
  -- Derive the two AE composites from the strict `RegularityH` joint
  -- measurability, then delegate to the AE-composite variant.
  have hμt : AEMeasurable
      (fun x => cxComb μ mBar t x)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    aemeasurable_cxComb_at (d := d) t hμ hmBar
  have hpt : AEMeasurable
      (fun x : (Fin d → ℝ) => (fun i : Fin d => cxCombGrad Dυ Dῡ t i x))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    aemeasurable_cxCombGrad_pi (d := d) t hDυ hDῡ
  have htriple : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        (x, (fun i : Fin d => cxCombGrad Dυ Dῡ t i x), cxComb μ mBar t x))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    measurable_id.aemeasurable.prodMk (hpt.prodMk hμt)
  have hH_ae : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        H x (fun i : Fin d => cxCombGrad Dυ Dῡ t i x) (cxComb μ mBar t x))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    hReg.measurable_H.comp_aemeasurable htriple
  have hDpH_ae : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        DpH x (fun i : Fin d => cxCombGrad Dυ Dῡ t i x) (cxComb μ mBar t x))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    hReg.measurable_DpH.comp_aemeasurable htriple
  exact aestronglyMeasurable_aepsiIntegrandAt_unreg_of_aeMeasH (d := d)
    t hH_ae hDpH_ae hμ hmBar hυ hῡ hDυ hDῡ hDν hη hν hV

/-- **AE-strong-measurability of `aepsiIntegrandAt_gateaux` at a fixed `t`.**
Generic version: takes AEStronglyMeasurable witnesses for the
Gateaux block ingredients. -/
lemma aestronglyMeasurable_aepsiIntegrandAt_gateaux
    (γBar : ℝ)
    {Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ}
    {υ ῡ : (Fin d → ℝ) → ℝ}
    {Dν : Fin d → (Fin d → ℝ) → ℝ}
    {ν : (Fin d → ℝ) → ℝ}
    (hυ : MeasureTheory.AEStronglyMeasurable υ
            (MeasureTheory.volume.restrict (UnitCube d)))
    (hῡ : MeasureTheory.AEStronglyMeasurable ῡ
            (MeasureTheory.volume.restrict (UnitCube d)))
    (hDυ : ∀ i, MeasureTheory.AEStronglyMeasurable (Dυ i)
            (MeasureTheory.volume.restrict (UnitCube d)))
    (hDῡ : ∀ i, MeasureTheory.AEStronglyMeasurable (Dῡ i)
            (MeasureTheory.volume.restrict (UnitCube d)))
    (hDν : ∀ i, MeasureTheory.AEStronglyMeasurable (Dν i)
            (MeasureTheory.volume.restrict (UnitCube d)))
    (hν : MeasureTheory.AEStronglyMeasurable ν
            (MeasureTheory.volume.restrict (UnitCube d)))
    (t : ℝ) :
    MeasureTheory.AEStronglyMeasurable
      (fun x => aepsiIntegrandAt_gateaux γBar Dυ Dῡ υ ῡ Dν ν x t)
      (MeasureTheory.volume.restrict (UnitCube d)) := by
  unfold aepsiIntegrandAt_gateaux
  -- AE-measurability of `υ_t` and `Dυ_t` at fixed `t`.
  have hυt : AEMeasurable
      (fun x => cxComb υ ῡ t x)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    aemeasurable_cxComb_at (d := d) t hυ hῡ
  have hpt : AEMeasurable
      (fun x : (Fin d → ℝ) => (fun i : Fin d => cxCombGrad Dυ Dῡ t i x))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    aemeasurable_cxCombGrad_pi (d := d) t hDυ hDῡ
  -- `vecAbsPowMinusTwo γBar (Dυ_t x) = ((Dυ_t x) ⬝ (Dυ_t x)) ^ ((γBar-2)/2)`.
  -- We use the ENNReal-rpow tunnel for measurability (avoiding the
  -- `0 ^ q` discontinuity when `q < 0`):
  -- `s ^ q = ((ENNReal.ofReal s) ^ q).toReal` for `s ≥ 0`.
  have hpt_dot_pt : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        (fun i : Fin d => cxCombGrad Dυ Dῡ t i x)
          ⬝ (fun i : Fin d => cxCombGrad Dυ Dῡ t i x))
      (MeasureTheory.volume.restrict (UnitCube d)) := by
    unfold dotProduct
    refine Finset.aemeasurable_fun_sum (s := Finset.univ) (fun i _ => ?_)
    exact (hpt.eval i).mul (hpt.eval i)
  -- ENNReal-rpow tunnel for nonneg base.
  have hpt_dot_pt_nn : ∀ x,
      0 ≤ (fun i : Fin d => cxCombGrad Dυ Dῡ t i x)
              ⬝ (fun i : Fin d => cxCombGrad Dυ Dῡ t i x) := by
    intro x
    unfold dotProduct
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have hvec : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        vecAbsPowMinusTwo γBar (fun i : Fin d => cxCombGrad Dυ Dῡ t i x))
      (MeasureTheory.volume.restrict (UnitCube d)) := by
    -- Rewrite `s ^ q = ((ENNReal.ofReal s) ^ q).toReal` for `s ≥ 0`.
    have h_ennreal_meas : Measurable
        (fun s : ℝ => ((ENNReal.ofReal s) ^ ((γBar - 2) / 2)).toReal) := by
      refine ENNReal.measurable_toReal.comp ?_
      exact (ENNReal.continuous_rpow_const).measurable.comp
              ENNReal.measurable_ofReal
    have h_ae_eq :
        (fun x : (Fin d → ℝ) =>
          vecAbsPowMinusTwo γBar (fun i : Fin d => cxCombGrad Dυ Dῡ t i x))
        =ᶠ[MeasureTheory.ae (MeasureTheory.volume.restrict (UnitCube d))]
        (fun x : (Fin d → ℝ) =>
          ((ENNReal.ofReal
              ((fun i : Fin d => cxCombGrad Dυ Dῡ t i x)
                ⬝ (fun i : Fin d => cxCombGrad Dυ Dῡ t i x)))
            ^ ((γBar - 2) / 2)).toReal) := by
      refine Filter.Eventually.of_forall (fun x => ?_)
      show vecAbsPowMinusTwo γBar (fun i : Fin d => cxCombGrad Dυ Dῡ t i x)
            = ((ENNReal.ofReal
                ((fun i : Fin d => cxCombGrad Dυ Dῡ t i x)
                  ⬝ (fun i : Fin d => cxCombGrad Dυ Dῡ t i x)))
              ^ ((γBar - 2) / 2)).toReal
      unfold vecAbsPowMinusTwo
      rw [← ENNReal.toReal_rpow]
      rw [ENNReal.toReal_ofReal (hpt_dot_pt_nn x)]
    refine AEMeasurable.congr ?_ h_ae_eq.symm
    exact h_ennreal_meas.comp_aemeasurable hpt_dot_pt
  -- `Dυ_t ⬝ Dν`.
  have hpt_dot_Dν : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        (fun i : Fin d => cxCombGrad Dυ Dῡ t i x)
          ⬝ (fun i : Fin d => Dν i x))
      (MeasureTheory.volume.restrict (UnitCube d)) := by
    unfold dotProduct
    refine Finset.aemeasurable_fun_sum (s := Finset.univ) (fun i _ => ?_)
    exact (hpt.eval i).mul (hDν i).aemeasurable
  -- `absPowMinusTwo γBar (υ_t x) = |υ_t x| ^ (γBar - 2)`.
  -- Same ENNReal tunnel.
  have habsυt_nn : ∀ x, (0 : ℝ) ≤ |cxComb υ ῡ t x| := fun x => abs_nonneg _
  have habsυt : AEMeasurable (fun x => |cxComb υ ῡ t x|)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    continuous_abs.measurable.comp_aemeasurable hυt
  have habsυ : AEMeasurable
      (fun x : (Fin d → ℝ) => absPowMinusTwo γBar (cxComb υ ῡ t x))
      (MeasureTheory.volume.restrict (UnitCube d)) := by
    have h_ennreal_meas : Measurable
        (fun s : ℝ => ((ENNReal.ofReal s) ^ (γBar - 2)).toReal) := by
      refine ENNReal.measurable_toReal.comp ?_
      exact (ENNReal.continuous_rpow_const).measurable.comp
              ENNReal.measurable_ofReal
    have h_ae_eq :
        (fun x : (Fin d → ℝ) => absPowMinusTwo γBar (cxComb υ ῡ t x))
        =ᶠ[MeasureTheory.ae (MeasureTheory.volume.restrict (UnitCube d))]
        (fun x : (Fin d → ℝ) =>
          ((ENNReal.ofReal |cxComb υ ῡ t x|) ^ (γBar - 2)).toReal) := by
      refine Filter.Eventually.of_forall (fun x => ?_)
      show absPowMinusTwo γBar (cxComb υ ῡ t x)
            = ((ENNReal.ofReal |cxComb υ ῡ t x|) ^ (γBar - 2)).toReal
      unfold absPowMinusTwo
      rw [← ENNReal.toReal_rpow]
      rw [ENNReal.toReal_ofReal (habsυt_nn x)]
    refine AEMeasurable.congr ?_ h_ae_eq.symm
    exact h_ennreal_meas.comp_aemeasurable habsυt
  -- Sum of the two products.
  have hpart1 : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        vecAbsPowMinusTwo γBar (fun i : Fin d => cxCombGrad Dυ Dῡ t i x)
          * ((fun i : Fin d => cxCombGrad Dυ Dῡ t i x)
                ⬝ (fun i : Fin d => Dν i x)))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    hvec.mul hpt_dot_Dν
  have hpart2 : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        absPowMinusTwo γBar (cxComb υ ῡ t x)
          * (cxComb υ ῡ t x * ν x))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    habsυ.mul (hυt.mul hν.aemeasurable)
  exact (hpart1.add hpart2).aestronglyMeasurable

/-- **`hF_unreg_meas_bare` discharge for `SetFamilyNarrowSegInputs`.**
Produces the Caratheodory measurability witness for the unregularised
integrand at the bare endpoints `(mLim + ρ₁, mLim + ρ₂, uLim, uLim,
DuLim, DuLim)`, given AEStronglyMeasurable witnesses for the bare
ingredients `(mLim, uLim, DuLim, ρ₁, ρ₂, V, η, ν, Dν)` and the
Hamiltonian regularity bundle. -/
lemma hF_unreg_meas_bare_set_paper
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hReg : Hamiltonian.RegularityH (d := d) H DpH)
    {mLim uLim : (Fin d → ℝ) → ℝ}
    {DuLim : Fin d → (Fin d → ℝ) → ℝ}
    {ρ₁ ρ₂ : (Fin d → ℝ) → ℝ}
    {η ν : (Fin d → ℝ) → ℝ}
    {Dν : Fin d → (Fin d → ℝ) → ℝ}
    (hmLim : MeasureTheory.AEStronglyMeasurable mLim
              (MeasureTheory.volume.restrict (UnitCube d)))
    (huLim : MeasureTheory.AEStronglyMeasurable uLim
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hDuLim : ∀ i, MeasureTheory.AEStronglyMeasurable (DuLim i)
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hρ₁ : MeasureTheory.AEStronglyMeasurable ρ₁
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hρ₂ : MeasureTheory.AEStronglyMeasurable ρ₂
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hV : MeasureTheory.AEStronglyMeasurable V
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hη : MeasureTheory.AEStronglyMeasurable η
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hν : MeasureTheory.AEStronglyMeasurable ν
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hDν : ∀ i, MeasureTheory.AEStronglyMeasurable (Dν i)
              (MeasureTheory.volume.restrict (UnitCube d))) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x =>
          aepsiIntegrandAt_unreg V H DpH DuLim DuLim
            (mLim + ρ₁) (mLim + ρ₂) uLim uLim Dν η ν x t)
        (MeasureTheory.volume.restrict (UnitCube d)) := by
  intro t _
  exact aestronglyMeasurable_aepsiIntegrandAt_unreg (d := d) hReg
    (hmLim.add hρ₁) (hmLim.add hρ₂) huLim huLim hDuLim hDuLim hDν hη hν hV t

/-- **`hF_gat_meas_bare` discharge for the set/signed family.**
Produces the Caratheodory measurability witness for the Gateaux
integrand at the bare endpoints `(uLim, uLim, DuLim, DuLim)`. -/
lemma hF_gat_meas_bare_paper
    (γBar : ℝ)
    {uLim : (Fin d → ℝ) → ℝ}
    {DuLim : Fin d → (Fin d → ℝ) → ℝ}
    {ν : (Fin d → ℝ) → ℝ}
    {Dν : Fin d → (Fin d → ℝ) → ℝ}
    (huLim : MeasureTheory.AEStronglyMeasurable uLim
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hDuLim : ∀ i, MeasureTheory.AEStronglyMeasurable (DuLim i)
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hν : MeasureTheory.AEStronglyMeasurable ν
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hDν : ∀ i, MeasureTheory.AEStronglyMeasurable (Dν i)
              (MeasureTheory.volume.restrict (UnitCube d))) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x =>
          aepsiIntegrandAt_gateaux γBar DuLim DuLim uLim uLim Dν ν x t)
        (MeasureTheory.volume.restrict (UnitCube d)) := by
  intro t _
  exact aestronglyMeasurable_aepsiIntegrandAt_gateaux (d := d) γBar
    huLim huLim hDuLim hDuLim hDν hν t

/-! ### v8 K0 step 3 — paper-derived Carathéodory measurability producers
    (`infra-P5-T10-v8-K0-set-measurability-producer`)

The two paper-derivable Carathéodory measurability producers below feed the
K0 set-family segment-data composer
(`infra-P5-T10-v8-K0-set-segInputsK0-closed-producer`, step 4 of the v8 K0
set-drain plan, 2026-05-21).

Strategy: the K0 integrand `aepsiIntegrandAt_unreg_K0` is *pointwise* equal
to the strict-cone `aepsiIntegrandAt_unreg` by the unconditional algebraic
identity `aepsiIntegrandAt_unreg_K0_eq_unreg` (Hemicontinuity.lean ~1422).
So measurability of the K0 form follows from measurability of the
strict-cone form via congruence. The strict-cone measurability is the
existing generic lemma `aestronglyMeasurable_aepsiIntegrandAt_unreg` which
takes `RegularityH H DpH` — inherited from `HypothesisPowerGrowth` since
`HypothesisPowerGrowth extends RegularityH`.

The Gateaux integrand `aepsiIntegrandAt_gateaux` is K0-agnostic: it only
references the test direction `Dν` and the segment data `υ, ῡ, Dυ, Dῡ`.
Its K0-shaped producer is therefore an alias for the existing
`hF_gat_meas_bare_paper`. -/

/-- **AE-strong-measurability of `aepsiIntegrandAt_unreg_K0` at a fixed `t`.**

Generic K0 sibling of `aestronglyMeasurable_aepsiIntegrandAt_unreg`. The
proof routes through the unconditional pointwise agreement
`aepsiIntegrandAt_unreg_K0_eq_unreg` (Hemicontinuity.lean ~1422) and the
existing strict-cone measurability lemma. -/
lemma aestronglyMeasurable_aepsiIntegrandAt_unreg_K0
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hReg : Hamiltonian.RegularityH (d := d) H DpH)
    {Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ}
    {μ mBar υ ῡ : (Fin d → ℝ) → ℝ}
    {Dν : Fin d → (Fin d → ℝ) → ℝ}
    {η ν : (Fin d → ℝ) → ℝ}
    (hμ : MeasureTheory.AEStronglyMeasurable μ
            (MeasureTheory.volume.restrict (UnitCube d)))
    (hmBar : MeasureTheory.AEStronglyMeasurable mBar
            (MeasureTheory.volume.restrict (UnitCube d)))
    (hυ : MeasureTheory.AEStronglyMeasurable υ
            (MeasureTheory.volume.restrict (UnitCube d)))
    (hῡ : MeasureTheory.AEStronglyMeasurable ῡ
            (MeasureTheory.volume.restrict (UnitCube d)))
    (hDυ : ∀ i, MeasureTheory.AEStronglyMeasurable (Dυ i)
            (MeasureTheory.volume.restrict (UnitCube d)))
    (hDῡ : ∀ i, MeasureTheory.AEStronglyMeasurable (Dῡ i)
            (MeasureTheory.volume.restrict (UnitCube d)))
    (hDν : ∀ i, MeasureTheory.AEStronglyMeasurable (Dν i)
            (MeasureTheory.volume.restrict (UnitCube d)))
    (hη : MeasureTheory.AEStronglyMeasurable η
            (MeasureTheory.volume.restrict (UnitCube d)))
    (hν : MeasureTheory.AEStronglyMeasurable ν
            (MeasureTheory.volume.restrict (UnitCube d)))
    (hV : MeasureTheory.AEStronglyMeasurable V
            (MeasureTheory.volume.restrict (UnitCube d)))
    (t : ℝ) :
    MeasureTheory.AEStronglyMeasurable
      (fun x => aepsiIntegrandAt_unreg_K0 V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν x t)
      (MeasureTheory.volume.restrict (UnitCube d)) := by
  -- Pointwise agreement of K0 and strict-cone integrands.
  have hfun_eq :
      (fun x => aepsiIntegrandAt_unreg_K0 V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν x t)
        = (fun x =>
            aepsiIntegrandAt_unreg V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν x t) := by
    funext x
    exact aepsiIntegrandAt_unreg_K0_eq_unreg
      V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν x t
  rw [hfun_eq]
  exact aestronglyMeasurable_aepsiIntegrandAt_unreg (d := d) hReg
    hμ hmBar hυ hῡ hDυ hDῡ hDν hη hν hV t

/-- **K0 paper-derived `hF_unreg_meas_bare` producer for
`SetFamilyNarrowSegInputsK0`.**

Step 3/5 of the v8 K0 set-drain refined plan (2026-05-21). Produces the
Carathéodory measurability witness for the **K0** unregularised integrand
`aepsiIntegrandAt_unreg_K0` at the bare endpoints
`(mLim + ρ₁, mLim + ρ₂, uLim, uLim, DuLim, DuLim)`, given paper hypotheses
`(hpow, hHextCont)` and AE-strong-measurability witnesses for the bare
ingredients.

Note: `hHextCont` is accepted in the signature for paper-faithfulness
(the closed-cone joint-continuity rider that downstream consumers thread
together with this measurability witness), but it is not used in the
measurability proof itself: the pointwise agreement
`aepsiIntegrandAt_unreg_K0_eq_unreg` reduces K0 measurability to
strict-cone measurability, which uses only `RegularityH` (inherited
from `hpow.toRegularityH`).

This is the paper-derivable replacement for the caller-supplied
`hF_unreg_meas_bare` field of `SetFamilyNarrowSegInputsK0`. -/
lemma aepsiIntegrand_unreg_K0_meas_of_paperHypotheses
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (_hHextCont : Hamiltonian.HypothesisHextJointCont (d := d) H)
    {mLim uLim : (Fin d → ℝ) → ℝ}
    {DuLim : Fin d → (Fin d → ℝ) → ℝ}
    {ρ₁ ρ₂ : (Fin d → ℝ) → ℝ}
    {η ν : (Fin d → ℝ) → ℝ}
    {Dν : Fin d → (Fin d → ℝ) → ℝ}
    (hmLim : MeasureTheory.AEStronglyMeasurable mLim
              (MeasureTheory.volume.restrict (UnitCube d)))
    (huLim : MeasureTheory.AEStronglyMeasurable uLim
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hDuLim : ∀ i, MeasureTheory.AEStronglyMeasurable (DuLim i)
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hρ₁ : MeasureTheory.AEStronglyMeasurable ρ₁
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hρ₂ : MeasureTheory.AEStronglyMeasurable ρ₂
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hV : MeasureTheory.AEStronglyMeasurable V
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hη : MeasureTheory.AEStronglyMeasurable η
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hν : MeasureTheory.AEStronglyMeasurable ν
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hDν : ∀ i, MeasureTheory.AEStronglyMeasurable (Dν i)
              (MeasureTheory.volume.restrict (UnitCube d))) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x =>
          aepsiIntegrandAt_unreg_K0 V H DpH DuLim DuLim
            (mLim + ρ₁) (mLim + ρ₂) uLim uLim Dν η ν x t)
        (MeasureTheory.volume.restrict (UnitCube d)) := by
  intro t _
  -- `HypothesisPowerGrowth` extends `RegularityH`; extract the regularity bundle.
  have hReg : Hamiltonian.RegularityH (d := d) H DpH := hpow.toRegularityH
  exact aestronglyMeasurable_aepsiIntegrandAt_unreg_K0 (d := d) hReg
    (hmLim.add hρ₁) (hmLim.add hρ₂) huLim huLim hDuLim hDuLim hDν hη hν hV t

/-- **K0 paper-derived `hF_gat_meas_bare` producer for
`SetFamilyNarrowSegInputsK0`.**

Step 3/5 of the v8 K0 set-drain refined plan (2026-05-21). The Gateaux
integrand `aepsiIntegrandAt_gateaux` is K0-agnostic (it only references
the test direction `Dν` and the displacement `Du − Du'`), so this is a
direct alias of `hF_gat_meas_bare_paper` exposed under the
"paperHypotheses" name for symmetry with the unreg producer. -/
lemma aepsiIntegrand_gateaux_meas_of_paperHypotheses
    (γBar : ℝ)
    {uLim : (Fin d → ℝ) → ℝ}
    {DuLim : Fin d → (Fin d → ℝ) → ℝ}
    {ν : (Fin d → ℝ) → ℝ}
    {Dν : Fin d → (Fin d → ℝ) → ℝ}
    (huLim : MeasureTheory.AEStronglyMeasurable uLim
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hDuLim : ∀ i, MeasureTheory.AEStronglyMeasurable (DuLim i)
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hν : MeasureTheory.AEStronglyMeasurable ν
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hDν : ∀ i, MeasureTheory.AEStronglyMeasurable (Dν i)
              (MeasureTheory.volume.restrict (UnitCube d))) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x =>
          aepsiIntegrandAt_gateaux γBar DuLim DuLim uLim uLim Dν ν x t)
        (MeasureTheory.volume.restrict (UnitCube d)) :=
  hF_gat_meas_bare_paper (d := d) γBar huLim hDuLim hν hDν

/-- Unit-test for `aepsiIntegrand_unreg_K0_meas_of_paperHypotheses` on the
simple-model Hamiltonian `H(x,p,m) = ‖p‖^2 − m`, with all segment data
identically zero. This exercises that the signature shape correctly aligns
with the available paper-hypothesis witnesses. -/
example (d : ℕ) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x : Fin d → ℝ =>
          aepsiIntegrandAt_unreg_K0 (d := d)
            (fun _ => (0 : ℝ))
            (fun _ p m => (‖p‖ : ℝ) ^ (2 : ℝ) - m ^ (1 : ℝ))
            (fun _ p _ => ((2 : ℝ) • p : Fin d → ℝ))
            (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ))
            ((fun _ => (0 : ℝ)) + (fun _ => (0 : ℝ)))
            ((fun _ => (0 : ℝ)) + (fun _ => (0 : ℝ)))
            (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ))
            (fun _ _ => (0 : ℝ))
            (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) x t)
        (MeasureTheory.volume.restrict (UnitCube d)) := by
  -- `HypothesisHextJointCont` for the simple model: jointly continuous
  -- on the whole space, hence on the closed cone.
  have hHextCont :
      Hamiltonian.HypothesisHextJointCont (d := d)
        (fun _ p m => (‖p‖ : ℝ) ^ (2 : ℝ) - m ^ (1 : ℝ)) := by
    refine Filter.Eventually.of_forall ?_
    intro _
    refine ContinuousOn.sub ?_ ?_
    · refine Continuous.continuousOn ?_
      exact (continuous_norm.comp continuous_fst).rpow_const
        (fun _ => Or.inr (by norm_num))
    · refine Continuous.continuousOn ?_
      exact continuous_snd.rpow_const (fun _ => Or.inr (by norm_num))
  exact aepsiIntegrand_unreg_K0_meas_of_paperHypotheses (d := d)
    (V := fun _ => 0)
    (H := fun _ p m => (‖p‖ : ℝ) ^ (2 : ℝ) - m ^ (1 : ℝ))
    (DpH := fun _ p _ => ((2 : ℝ) • p : Fin d → ℝ))
    (mLim := fun _ => 0) (uLim := fun _ => 0)
    (DuLim := fun _ _ => 0)
    (ρ₁ := fun _ => 0) (ρ₂ := fun _ => 0)
    (η := fun _ => 0) (ν := fun _ => 0)
    (Dν := fun _ _ => 0)
    (Hamiltonian.simpleHypothesisPowerGrowth d) hHextCont
    aestronglyMeasurable_const aestronglyMeasurable_const
    (fun _ => aestronglyMeasurable_const)
    aestronglyMeasurable_const aestronglyMeasurable_const
    aestronglyMeasurable_const aestronglyMeasurable_const
    aestronglyMeasurable_const
    (fun _ => aestronglyMeasurable_const)

/-- Unit-test for `aepsiIntegrand_gateaux_meas_of_paperHypotheses` at
trivially-zero data. -/
example (d : ℕ) (γBar : ℝ) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x : Fin d → ℝ =>
          aepsiIntegrandAt_gateaux γBar
            (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ))
            (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ))
            (fun _ _ => (0 : ℝ))
            (fun _ => (0 : ℝ)) x t)
        (MeasureTheory.volume.restrict (UnitCube d)) :=
  aepsiIntegrand_gateaux_meas_of_paperHypotheses (d := d) γBar
    aestronglyMeasurable_const (fun _ => aestronglyMeasurable_const)
    aestronglyMeasurable_const (fun _ => aestronglyMeasurable_const)

/-! ### Signed-family mirror of the iter-0768 K0 measurability producers

Iter `infra-P5-T10-v8-K0-signed-measurability-producer` (signed mirror
of iter-0768). The iter-0768 producers
`aepsiIntegrand_unreg_K0_meas_of_paperHypotheses` and
`aepsiIntegrand_gateaux_meas_of_paperHypotheses` already take the
endpoint shifts `(ρ₁, ρ₂)` as bare functions with only
AEStronglyMeasurable hypotheses — they impose no nonneg requirement.
Thus they apply directly to the signed family by substituting
`(g₁, g₂)` for `(ρ₁, ρ₂)`. We expose them under the signed-named
identifiers to discharge `SignedFamilyNarrowSegInputsK0.hF_unreg_meas_bare`
and `SignedFamilyNarrowSegInputsK0.hF_gat_meas_bare` cleanly. -/

/-- **Signed-family K0 paper-derived `hF_unreg_meas_bare` producer.**

Signed-family alias of `aepsiIntegrand_unreg_K0_meas_of_paperHypotheses`.
The set-family producer's shift arguments `(ρ₁, ρ₂)` are bare functions
with no nonneg hypotheses, so the same producer discharges the signed
endpoints `(mLim + g₁, mLim + g₂)` of
`SignedFamilyNarrowSegInputsK0.hF_unreg_meas_bare`. -/
lemma aepsiIntegrand_unreg_K0_meas_of_paperHypotheses_signed
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (hHextCont : Hamiltonian.HypothesisHextJointCont (d := d) H)
    {mLim uLim : (Fin d → ℝ) → ℝ}
    {DuLim : Fin d → (Fin d → ℝ) → ℝ}
    {g₁ g₂ : (Fin d → ℝ) → ℝ}
    {η ν : (Fin d → ℝ) → ℝ}
    {Dν : Fin d → (Fin d → ℝ) → ℝ}
    (hmLim : MeasureTheory.AEStronglyMeasurable mLim
              (MeasureTheory.volume.restrict (UnitCube d)))
    (huLim : MeasureTheory.AEStronglyMeasurable uLim
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hDuLim : ∀ i, MeasureTheory.AEStronglyMeasurable (DuLim i)
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hg₁ : MeasureTheory.AEStronglyMeasurable g₁
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hg₂ : MeasureTheory.AEStronglyMeasurable g₂
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hV : MeasureTheory.AEStronglyMeasurable V
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hη : MeasureTheory.AEStronglyMeasurable η
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hν : MeasureTheory.AEStronglyMeasurable ν
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hDν : ∀ i, MeasureTheory.AEStronglyMeasurable (Dν i)
              (MeasureTheory.volume.restrict (UnitCube d))) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x =>
          aepsiIntegrandAt_unreg_K0 V H DpH DuLim DuLim
            (mLim + g₁) (mLim + g₂) uLim uLim Dν η ν x t)
        (MeasureTheory.volume.restrict (UnitCube d)) :=
  aepsiIntegrand_unreg_K0_meas_of_paperHypotheses (d := d)
    (V := V) (H := H) (DpH := DpH)
    (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
    (ρ₁ := g₁) (ρ₂ := g₂) (η := η) (ν := ν) (Dν := Dν)
    hpow hHextCont hmLim huLim hDuLim hg₁ hg₂ hV hη hν hDν

/-- **Signed-family K0 paper-derived `hF_gat_meas_bare` producer.**

Signed-family alias of `aepsiIntegrand_gateaux_meas_of_paperHypotheses`.
The Gateaux integrand `aepsiIntegrandAt_gateaux` is both K0-agnostic
and family-agnostic (no dependence on the density endpoints at all),
so this is a direct alias for symmetry with the unreg producer. -/
lemma aepsiIntegrand_gateaux_meas_of_paperHypotheses_signed
    (γBar : ℝ)
    {uLim : (Fin d → ℝ) → ℝ}
    {DuLim : Fin d → (Fin d → ℝ) → ℝ}
    {ν : (Fin d → ℝ) → ℝ}
    {Dν : Fin d → (Fin d → ℝ) → ℝ}
    (huLim : MeasureTheory.AEStronglyMeasurable uLim
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hDuLim : ∀ i, MeasureTheory.AEStronglyMeasurable (DuLim i)
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hν : MeasureTheory.AEStronglyMeasurable ν
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hDν : ∀ i, MeasureTheory.AEStronglyMeasurable (Dν i)
              (MeasureTheory.volume.restrict (UnitCube d))) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x =>
          aepsiIntegrandAt_gateaux γBar DuLim DuLim uLim uLim Dν ν x t)
        (MeasureTheory.volume.restrict (UnitCube d)) :=
  aepsiIntegrand_gateaux_meas_of_paperHypotheses (d := d) γBar
    huLim hDuLim hν hDν

/-- Unit-test for the signed mirror
`aepsiIntegrand_unreg_K0_meas_of_paperHypotheses_signed` on the
simple-model Hamiltonian with zero signed perturbations. -/
example (d : ℕ) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x : Fin d → ℝ =>
          aepsiIntegrandAt_unreg_K0 (d := d)
            (fun _ => (0 : ℝ))
            (fun _ p m => (‖p‖ : ℝ) ^ (2 : ℝ) - m ^ (1 : ℝ))
            (fun _ p _ => ((2 : ℝ) • p : Fin d → ℝ))
            (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ))
            ((fun _ => (0 : ℝ)) + (fun _ => (0 : ℝ)))
            ((fun _ => (0 : ℝ)) + (fun _ => (0 : ℝ)))
            (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ))
            (fun _ _ => (0 : ℝ))
            (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) x t)
        (MeasureTheory.volume.restrict (UnitCube d)) := by
  have hHextCont :
      Hamiltonian.HypothesisHextJointCont (d := d)
        (fun _ p m => (‖p‖ : ℝ) ^ (2 : ℝ) - m ^ (1 : ℝ)) := by
    refine Filter.Eventually.of_forall ?_
    intro _
    refine ContinuousOn.sub ?_ ?_
    · refine Continuous.continuousOn ?_
      exact (continuous_norm.comp continuous_fst).rpow_const
        (fun _ => Or.inr (by norm_num))
    · refine Continuous.continuousOn ?_
      exact continuous_snd.rpow_const (fun _ => Or.inr (by norm_num))
  exact aepsiIntegrand_unreg_K0_meas_of_paperHypotheses_signed (d := d)
    (V := fun _ => 0)
    (H := fun _ p m => (‖p‖ : ℝ) ^ (2 : ℝ) - m ^ (1 : ℝ))
    (DpH := fun _ p _ => ((2 : ℝ) • p : Fin d → ℝ))
    (mLim := fun _ => 0) (uLim := fun _ => 0)
    (DuLim := fun _ _ => 0)
    (g₁ := fun _ => 0) (g₂ := fun _ => 0)
    (η := fun _ => 0) (ν := fun _ => 0)
    (Dν := fun _ _ => 0)
    (Hamiltonian.simpleHypothesisPowerGrowth d) hHextCont
    aestronglyMeasurable_const aestronglyMeasurable_const
    (fun _ => aestronglyMeasurable_const)
    aestronglyMeasurable_const aestronglyMeasurable_const
    aestronglyMeasurable_const aestronglyMeasurable_const
    aestronglyMeasurable_const
    (fun _ => aestronglyMeasurable_const)

/-- Unit-test for the signed mirror
`aepsiIntegrand_gateaux_meas_of_paperHypotheses_signed` at trivially
zero data. -/
example (d : ℕ) (γBar : ℝ) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x : Fin d → ℝ =>
          aepsiIntegrandAt_gateaux γBar
            (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ))
            (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ))
            (fun _ _ => (0 : ℝ))
            (fun _ => (0 : ℝ)) x t)
        (MeasureTheory.volume.restrict (UnitCube d)) :=
  aepsiIntegrand_gateaux_meas_of_paperHypotheses_signed (d := d) γBar
    aestronglyMeasurable_const (fun _ => aestronglyMeasurable_const)
    aestronglyMeasurable_const (fun _ => aestronglyMeasurable_const)

/-- **`hF_unreg_meas_bare` discharge for `TransportFamilyNarrowSegInputs`.**
Produces the Caratheodory measurability witness for the unregularised
integrand at the bare *transport-perturbed* endpoints
`(mLim, mLim, uLim + ψ₁, uLim + ψ₂, DuLim + ∂ψ₁, DuLim + ∂ψ₂)`. -/
lemma hF_unreg_meas_bare_transport_paper
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hReg : Hamiltonian.RegularityH (d := d) H DpH)
    {mLim uLim : (Fin d → ℝ) → ℝ}
    {DuLim : Fin d → (Fin d → ℝ) → ℝ}
    {η ν : (Fin d → ℝ) → ℝ}
    {Dν : Fin d → (Fin d → ℝ) → ℝ}
    (hmLim : MeasureTheory.AEStronglyMeasurable mLim
              (MeasureTheory.volume.restrict (UnitCube d)))
    (huLim : MeasureTheory.AEStronglyMeasurable uLim
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hDuLim : ∀ i, MeasureTheory.AEStronglyMeasurable (DuLim i)
              (MeasureTheory.volume.restrict (UnitCube d)))
    (ψ₁ ψ₂ : Periodic.SmoothPeriodic d)
    (hV : MeasureTheory.AEStronglyMeasurable V
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hη : MeasureTheory.AEStronglyMeasurable η
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hν : MeasureTheory.AEStronglyMeasurable ν
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hDν : ∀ i, MeasureTheory.AEStronglyMeasurable (Dν i)
              (MeasureTheory.volume.restrict (UnitCube d))) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x =>
          aepsiIntegrandAt_unreg V H DpH
            (fun i => DuLim i + (Periodic.SmoothPeriodic.partialDeriv
                                    i ψ₁ : (Fin d → ℝ) → ℝ))
            (fun i => DuLim i + (Periodic.SmoothPeriodic.partialDeriv
                                    i ψ₂ : (Fin d → ℝ) → ℝ))
            mLim mLim
            (uLim + (ψ₁ : (Fin d → ℝ) → ℝ))
            (uLim + (ψ₂ : (Fin d → ℝ) → ℝ))
            Dν η ν x t)
        (MeasureTheory.volume.restrict (UnitCube d)) := by
  intro t _
  -- `ψᵢ` is smooth hence continuous hence AEStronglyMeasurable.
  have hψ₁ : MeasureTheory.AEStronglyMeasurable
      ((ψ₁ : (Fin d → ℝ) → ℝ))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    ψ₁.smooth.continuous.aestronglyMeasurable
  have hψ₂ : MeasureTheory.AEStronglyMeasurable
      ((ψ₂ : (Fin d → ℝ) → ℝ))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    ψ₂.smooth.continuous.aestronglyMeasurable
  -- `partialDeriv i ψ` is continuous (smooth periodic).
  have hDψ₁ : ∀ i, MeasureTheory.AEStronglyMeasurable
      ((Periodic.SmoothPeriodic.partialDeriv i ψ₁ : (Fin d → ℝ) → ℝ))
      (MeasureTheory.volume.restrict (UnitCube d)) := fun i =>
    (Periodic.SmoothPeriodic.partialDeriv i ψ₁).smooth.continuous.aestronglyMeasurable
  have hDψ₂ : ∀ i, MeasureTheory.AEStronglyMeasurable
      ((Periodic.SmoothPeriodic.partialDeriv i ψ₂ : (Fin d → ℝ) → ℝ))
      (MeasureTheory.volume.restrict (UnitCube d)) := fun i =>
    (Periodic.SmoothPeriodic.partialDeriv i ψ₂).smooth.continuous.aestronglyMeasurable
  exact aestronglyMeasurable_aepsiIntegrandAt_unreg (d := d) hReg
    hmLim hmLim (huLim.add hψ₁) (huLim.add hψ₂)
    (fun i => (hDuLim i).add (hDψ₁ i))
    (fun i => (hDuLim i).add (hDψ₂ i))
    hDν hη hν hV t

/-- **`hF_gat_meas_bare` discharge for `TransportFamilyNarrowSegInputs`.** -/
lemma hF_gat_meas_bare_transport_paper
    (γBar : ℝ)
    {uLim : (Fin d → ℝ) → ℝ}
    {DuLim : Fin d → (Fin d → ℝ) → ℝ}
    {ν : (Fin d → ℝ) → ℝ}
    {Dν : Fin d → (Fin d → ℝ) → ℝ}
    (huLim : MeasureTheory.AEStronglyMeasurable uLim
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hDuLim : ∀ i, MeasureTheory.AEStronglyMeasurable (DuLim i)
              (MeasureTheory.volume.restrict (UnitCube d)))
    (ψ₁ ψ₂ : Periodic.SmoothPeriodic d)
    (hν : MeasureTheory.AEStronglyMeasurable ν
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hDν : ∀ i, MeasureTheory.AEStronglyMeasurable (Dν i)
              (MeasureTheory.volume.restrict (UnitCube d))) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x =>
          aepsiIntegrandAt_gateaux γBar
            (fun i => DuLim i + (Periodic.SmoothPeriodic.partialDeriv
                                    i ψ₁ : (Fin d → ℝ) → ℝ))
            (fun i => DuLim i + (Periodic.SmoothPeriodic.partialDeriv
                                    i ψ₂ : (Fin d → ℝ) → ℝ))
            (uLim + (ψ₁ : (Fin d → ℝ) → ℝ))
            (uLim + (ψ₂ : (Fin d → ℝ) → ℝ))
            Dν ν x t)
        (MeasureTheory.volume.restrict (UnitCube d)) := by
  intro t _
  have hψ₁ : MeasureTheory.AEStronglyMeasurable
      ((ψ₁ : (Fin d → ℝ) → ℝ))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    ψ₁.smooth.continuous.aestronglyMeasurable
  have hψ₂ : MeasureTheory.AEStronglyMeasurable
      ((ψ₂ : (Fin d → ℝ) → ℝ))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    ψ₂.smooth.continuous.aestronglyMeasurable
  have hDψ₁ : ∀ i, MeasureTheory.AEStronglyMeasurable
      ((Periodic.SmoothPeriodic.partialDeriv i ψ₁ : (Fin d → ℝ) → ℝ))
      (MeasureTheory.volume.restrict (UnitCube d)) := fun i =>
    (Periodic.SmoothPeriodic.partialDeriv i ψ₁).smooth.continuous.aestronglyMeasurable
  have hDψ₂ : ∀ i, MeasureTheory.AEStronglyMeasurable
      ((Periodic.SmoothPeriodic.partialDeriv i ψ₂ : (Fin d → ℝ) → ℝ))
      (MeasureTheory.volume.restrict (UnitCube d)) := fun i =>
    (Periodic.SmoothPeriodic.partialDeriv i ψ₂).smooth.continuous.aestronglyMeasurable
  exact aestronglyMeasurable_aepsiIntegrandAt_gateaux (d := d) γBar
    (huLim.add hψ₁) (huLim.add hψ₂)
    (fun i => (hDuLim i).add (hDψ₁ i))
    (fun i => (hDuLim i).add (hDψ₂ i))
    hDν hν t

/-! ### Transport-family mirror of the iter-0768 K0 measurability producers

Iter `infra-P5-T10-v8-K0-transport-measurability-producer` (transport
mirror of iter-0768 / iter-0774). At the transport endpoints
`(mLim, mLim, uLim + ψ₁, uLim + ψ₂, DuLim + ∂ψ₁, DuLim + ∂ψ₂)` the unreg
K0 integrand is again measurable by routing through the K0-=-strict-cone
pointwise identity `aepsiIntegrandAt_unreg_K0_eq_unreg` followed by the
generic strict-cone measurability lemma — but the generic K0 lemma
`aestronglyMeasurable_aepsiIntegrandAt_unreg_K0` (BanachBridge.lean ~916)
already encapsulates this routing and is polymorphic in **all** density,
potential and gradient endpoints. Hence the transport-K0 unreg producer
is a thin wrapper that supplies smooth-periodic AE-measurability of `ψᵢ`
and `∂ψᵢ`, exactly like the strict-cone discharge
`hF_unreg_meas_bare_transport_paper`. The Gateaux integrand is
K0-agnostic so the transport-K0 gateaux producer is the same as the
strict-cone `hF_gat_meas_bare_transport_paper` exposed under the
"paperHypotheses"-suffixed name for symmetry with the set/signed mirrors. -/

/-- **Transport-family K0 paper-derived `hF_unreg_meas_bare` producer.**

K0 sibling of `hF_unreg_meas_bare_transport_paper` (strict-cone). Produces
the Carathéodory measurability witness for the **K0** unregularised
integrand at the bare transport-perturbed endpoints
`(mLim, mLim, uLim + ψ₁, uLim + ψ₂, DuLim + ∂ψ₁, DuLim + ∂ψ₂)`.

Note: `hHextCont` is accepted in the signature for paper-faithfulness
(the closed-cone joint-continuity rider that downstream consumers thread
together with this measurability witness), but it is not used in the
measurability proof itself: the K0 generic lemma
`aestronglyMeasurable_aepsiIntegrandAt_unreg_K0` already routes through
the unconditional pointwise identity `aepsiIntegrandAt_unreg_K0_eq_unreg`,
which only requires `RegularityH` (inherited from `hpow.toRegularityH`).

This is the paper-derivable replacement for the caller-supplied
`hF_unreg_meas_bare` field of `TransportFamilyNarrowSegInputsK0`. -/
lemma aepsiIntegrand_unreg_K0_meas_of_paperHypotheses_transport
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (_hHextCont : Hamiltonian.HypothesisHextJointCont (d := d) H)
    {mLim uLim : (Fin d → ℝ) → ℝ}
    {DuLim : Fin d → (Fin d → ℝ) → ℝ}
    {η ν : (Fin d → ℝ) → ℝ}
    {Dν : Fin d → (Fin d → ℝ) → ℝ}
    (hmLim : MeasureTheory.AEStronglyMeasurable mLim
              (MeasureTheory.volume.restrict (UnitCube d)))
    (huLim : MeasureTheory.AEStronglyMeasurable uLim
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hDuLim : ∀ i, MeasureTheory.AEStronglyMeasurable (DuLim i)
              (MeasureTheory.volume.restrict (UnitCube d)))
    (ψ₁ ψ₂ : Periodic.SmoothPeriodic d)
    (hV : MeasureTheory.AEStronglyMeasurable V
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hη : MeasureTheory.AEStronglyMeasurable η
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hν : MeasureTheory.AEStronglyMeasurable ν
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hDν : ∀ i, MeasureTheory.AEStronglyMeasurable (Dν i)
              (MeasureTheory.volume.restrict (UnitCube d))) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x =>
          aepsiIntegrandAt_unreg_K0 V H DpH
            (fun i => DuLim i + (Periodic.SmoothPeriodic.partialDeriv
                                    i ψ₁ : (Fin d → ℝ) → ℝ))
            (fun i => DuLim i + (Periodic.SmoothPeriodic.partialDeriv
                                    i ψ₂ : (Fin d → ℝ) → ℝ))
            mLim mLim
            (uLim + (ψ₁ : (Fin d → ℝ) → ℝ))
            (uLim + (ψ₂ : (Fin d → ℝ) → ℝ))
            Dν η ν x t)
        (MeasureTheory.volume.restrict (UnitCube d)) := by
  intro t _
  -- `HypothesisPowerGrowth` extends `RegularityH`.
  have hReg : Hamiltonian.RegularityH (d := d) H DpH := hpow.toRegularityH
  -- `ψᵢ` is smooth hence continuous hence AEStronglyMeasurable.
  have hψ₁ : MeasureTheory.AEStronglyMeasurable
      ((ψ₁ : (Fin d → ℝ) → ℝ))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    ψ₁.smooth.continuous.aestronglyMeasurable
  have hψ₂ : MeasureTheory.AEStronglyMeasurable
      ((ψ₂ : (Fin d → ℝ) → ℝ))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    ψ₂.smooth.continuous.aestronglyMeasurable
  -- `partialDeriv i ψ` is continuous (smooth periodic).
  have hDψ₁ : ∀ i, MeasureTheory.AEStronglyMeasurable
      ((Periodic.SmoothPeriodic.partialDeriv i ψ₁ : (Fin d → ℝ) → ℝ))
      (MeasureTheory.volume.restrict (UnitCube d)) := fun i =>
    (Periodic.SmoothPeriodic.partialDeriv i ψ₁).smooth.continuous.aestronglyMeasurable
  have hDψ₂ : ∀ i, MeasureTheory.AEStronglyMeasurable
      ((Periodic.SmoothPeriodic.partialDeriv i ψ₂ : (Fin d → ℝ) → ℝ))
      (MeasureTheory.volume.restrict (UnitCube d)) := fun i =>
    (Periodic.SmoothPeriodic.partialDeriv i ψ₂).smooth.continuous.aestronglyMeasurable
  exact aestronglyMeasurable_aepsiIntegrandAt_unreg_K0 (d := d) hReg
    hmLim hmLim (huLim.add hψ₁) (huLim.add hψ₂)
    (fun i => (hDuLim i).add (hDψ₁ i))
    (fun i => (hDuLim i).add (hDψ₂ i))
    hDν hη hν hV t

/-- **Transport-family K0 paper-derived `hF_gat_meas_bare` producer.**

K0 sibling of `hF_gat_meas_bare_transport_paper`. The Gateaux integrand
`aepsiIntegrandAt_gateaux` is K0-agnostic (it only references the test
direction `Dν` and the displacement `Du − Du'`), so this is a direct
alias of `hF_gat_meas_bare_transport_paper` exposed under the
"paperHypotheses" name for symmetry with the unreg producer. -/
lemma aepsiIntegrand_gateaux_meas_of_paperHypotheses_transport
    (γBar : ℝ)
    {uLim : (Fin d → ℝ) → ℝ}
    {DuLim : Fin d → (Fin d → ℝ) → ℝ}
    {ν : (Fin d → ℝ) → ℝ}
    {Dν : Fin d → (Fin d → ℝ) → ℝ}
    (huLim : MeasureTheory.AEStronglyMeasurable uLim
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hDuLim : ∀ i, MeasureTheory.AEStronglyMeasurable (DuLim i)
              (MeasureTheory.volume.restrict (UnitCube d)))
    (ψ₁ ψ₂ : Periodic.SmoothPeriodic d)
    (hν : MeasureTheory.AEStronglyMeasurable ν
              (MeasureTheory.volume.restrict (UnitCube d)))
    (hDν : ∀ i, MeasureTheory.AEStronglyMeasurable (Dν i)
              (MeasureTheory.volume.restrict (UnitCube d))) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x =>
          aepsiIntegrandAt_gateaux γBar
            (fun i => DuLim i + (Periodic.SmoothPeriodic.partialDeriv
                                    i ψ₁ : (Fin d → ℝ) → ℝ))
            (fun i => DuLim i + (Periodic.SmoothPeriodic.partialDeriv
                                    i ψ₂ : (Fin d → ℝ) → ℝ))
            (uLim + (ψ₁ : (Fin d → ℝ) → ℝ))
            (uLim + (ψ₂ : (Fin d → ℝ) → ℝ))
            Dν ν x t)
        (MeasureTheory.volume.restrict (UnitCube d)) :=
  hF_gat_meas_bare_transport_paper (d := d) γBar huLim hDuLim ψ₁ ψ₂ hν hDν

/-- Unit-test for the transport mirror
`aepsiIntegrand_unreg_K0_meas_of_paperHypotheses_transport` on the
simple-model Hamiltonian with zero transport perturbations. -/
example (d : ℕ) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x : Fin d → ℝ =>
          aepsiIntegrandAt_unreg_K0 (d := d)
            (fun _ => (0 : ℝ))
            (fun _ p m => (‖p‖ : ℝ) ^ (2 : ℝ) - m ^ (1 : ℝ))
            (fun _ p _ => ((2 : ℝ) • p : Fin d → ℝ))
            (fun i =>
              (fun _ => (0 : ℝ))
                + (Periodic.SmoothPeriodic.partialDeriv i
                    (Periodic.SmoothPeriodic.const (d := d) 0)
                  : (Fin d → ℝ) → ℝ))
            (fun i =>
              (fun _ => (0 : ℝ))
                + (Periodic.SmoothPeriodic.partialDeriv i
                    (Periodic.SmoothPeriodic.const (d := d) 0)
                  : (Fin d → ℝ) → ℝ))
            (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ))
            ((fun _ => (0 : ℝ))
              + ((Periodic.SmoothPeriodic.const (d := d) 0
                  : Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ))
            ((fun _ => (0 : ℝ))
              + ((Periodic.SmoothPeriodic.const (d := d) 0
                  : Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ))
            (fun _ _ => (0 : ℝ))
            (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) x t)
        (MeasureTheory.volume.restrict (UnitCube d)) := by
  have hHextCont :
      Hamiltonian.HypothesisHextJointCont (d := d)
        (fun _ p m => (‖p‖ : ℝ) ^ (2 : ℝ) - m ^ (1 : ℝ)) := by
    refine Filter.Eventually.of_forall ?_
    intro _
    refine ContinuousOn.sub ?_ ?_
    · refine Continuous.continuousOn ?_
      exact (continuous_norm.comp continuous_fst).rpow_const
        (fun _ => Or.inr (by norm_num))
    · refine Continuous.continuousOn ?_
      exact continuous_snd.rpow_const (fun _ => Or.inr (by norm_num))
  exact aepsiIntegrand_unreg_K0_meas_of_paperHypotheses_transport (d := d)
    (V := fun _ => 0)
    (H := fun _ p m => (‖p‖ : ℝ) ^ (2 : ℝ) - m ^ (1 : ℝ))
    (DpH := fun _ p _ => ((2 : ℝ) • p : Fin d → ℝ))
    (mLim := fun _ => 0) (uLim := fun _ => 0)
    (DuLim := fun _ _ => 0)
    (η := fun _ => 0) (ν := fun _ => 0)
    (Dν := fun _ _ => 0)
    (Hamiltonian.simpleHypothesisPowerGrowth d) hHextCont
    aestronglyMeasurable_const aestronglyMeasurable_const
    (fun _ => aestronglyMeasurable_const)
    (Periodic.SmoothPeriodic.const (d := d) 0)
    (Periodic.SmoothPeriodic.const (d := d) 0)
    aestronglyMeasurable_const aestronglyMeasurable_const
    aestronglyMeasurable_const
    (fun _ => aestronglyMeasurable_const)

/-- Unit-test for the transport mirror
`aepsiIntegrand_gateaux_meas_of_paperHypotheses_transport` at trivially
zero data. -/
example (d : ℕ) (γBar : ℝ) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x : Fin d → ℝ =>
          aepsiIntegrandAt_gateaux γBar
            (fun i =>
              (fun _ => (0 : ℝ))
                + (Periodic.SmoothPeriodic.partialDeriv i
                    (Periodic.SmoothPeriodic.const (d := d) 0)
                  : (Fin d → ℝ) → ℝ))
            (fun i =>
              (fun _ => (0 : ℝ))
                + (Periodic.SmoothPeriodic.partialDeriv i
                    (Periodic.SmoothPeriodic.const (d := d) 0)
                  : (Fin d → ℝ) → ℝ))
            ((fun _ => (0 : ℝ))
              + ((Periodic.SmoothPeriodic.const (d := d) 0
                  : Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ))
            ((fun _ => (0 : ℝ))
              + ((Periodic.SmoothPeriodic.const (d := d) 0
                  : Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ))
            (fun _ _ => (0 : ℝ))
            (fun _ => (0 : ℝ)) x t)
        (MeasureTheory.volume.restrict (UnitCube d)) :=
  aepsiIntegrand_gateaux_meas_of_paperHypotheses_transport (d := d) γBar
    aestronglyMeasurable_const (fun _ => aestronglyMeasurable_const)
    (Periodic.SmoothPeriodic.const (d := d) 0)
    (Periodic.SmoothPeriodic.const (d := d) 0)
    aestronglyMeasurable_const (fun _ => aestronglyMeasurable_const)

/-! ## Narrow set/signed/transport segment-data ladder — REMOVED

The non-K0-narrow, K0-non-min, and shifted segment-data Seg-Inputs /
Minty-residue ladders (`SetFamilyNarrowSegInputs`, the `K0` siblings,
the `{Signed,Transport}FamilyNarrow…` mirrors, the `…ShiftedSegInputs`
records, and their `mintyData…_of_paperHypotheses` producers) were dead
scaffolding and have been deleted. The live Theorem 1 path uses the
`…K0Min` ladder → `T10PaperResidues.of_paperHypotheses` →
`simplePowerThinChain_of_paperHypotheses`. -/

/-! ## v8 K0 set-family **unshifted** dominator bundle and producer
(iter `infra-P5-T10-v8-K0-set-dominators-producer`, step 2 of 5)

Headline closed paper-faithful packaging of the nine `MemLpPer`-of-power
dominator certificates at the **unshifted** set-family admissible
endpoints `(mLim + ρ₁, mLim + ρ₂)`. These are the exact nine dominator
arguments consumed by the K0 composer
`hemicontSegmentData_set_narrow_K0_of_paperHypotheses`
(BanachBridge.lean ~6040-6064).

**Why unshifted, not shifted?** The K0 path bypasses the v7 shifted
infrastructure entirely. Strict positivity along the segment is
discharged via `K0_Aepsi_segment_pos_nn`, not via a `c > 0` shift, so the
nine dominators live at the unshifted endpoints.

**Iter 0767 review fix (paper-faithful derivation).** The earlier
revision of the producer was a packaging shell: it took the nine
`MemLpPer`-of-power certificates as explicit inputs and forwarded them
through identity wrappers. The reviewer correctly rejected this as the
iter-0764 anti-pattern. The current revision **derives** each of the
nine certificates from the paper-level hypotheses
`(hpow, hmLim_memLp, huLim_sob, hDuLim_memLp_γ, hρ₁_lp, hρ₂_lp)` plus
four exponent identities. The derivation mirrors the inline assembly
of `paperSection8_segmentResiduesMin_of_paperHypotheses`
(`StationaryMFG/Theorems/SimplePower/Banach/AssemblyContext.lean:9343`,
iter 0606/0609), adapted to the set-family endpoints
`(mLim + ρ₁, mLim + ρ₂)`: the summed-abs density function is
`μSum := fun x => |(mLim+ρ₂) x| + |(mLim+ρ₁) x|`, built via
`MemLpPer.add` + `Real.norm_eq_abs` from `hmLim_memLp + hρ_i_lp`.
The Gateaux blocks use `γBarReal` directly; the bundle's `γBar`
parameter is tied to `γBarReal` via the consumer's `hγBar_eq`.

Per `infra-P5-T10-v8-K0-set-dominators-producer` (iter 0767 review). -/

/-- **Local helper:** `|f| + |g| ∈ MemLpPer p` when `f, g ∈ MemLpPer p`.
Adapted from `memLpPer_abs_add_abs` in
`Banach/AssemblyContext.lean:9219` (iter 0606, private there). -/
lemma palomar_BanachBridge_K0setDom_memLpPer_abs_add_abs
    {d : ℕ} {p : ℝ≥0∞} {f g : (Fin d → ℝ) → ℝ}
    (hf : Periodic.MemLpPer (d := d) p f)
    (hg : Periodic.MemLpPer (d := d) p g) :
    Periodic.MemLpPer (d := d) p (fun x => |f x| + |g x|) := by
  have hfabs : Periodic.MemLpPer (d := d) p (fun x => |f x|) := by
    have := hf.toMemLp.norm
    have heq : (fun x => ‖f x‖) = fun x => |f x| := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at this
    exact MemLp.toMemLpPer this
  have hgabs : Periodic.MemLpPer (d := d) p (fun x => |g x|) := by
    have := hg.toMemLp.norm
    have heq : (fun x => ‖g x‖) = fun x => |g x| := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at this
    exact MemLp.toMemLpPer this
  have hsum := hfabs.add hgabs
  have heq :
      ((fun x => |f x|) + (fun x => |g x|))
      = (fun x => |f x| + |g x|) := by
    funext x; simp [Pi.add_apply]
  rw [heq] at hsum
  exact hsum

/-- **Local helper:** vector-valued promotion of a family of
`MemLpPer` functions. Adapted from `memLpPer_pi_of_coord_local`
in `Banach/AssemblyContext.lean:9248` (iter 0606, private there). -/
lemma palomar_BanachBridge_K0setDom_memLpPer_pi_of_coord
    {d : ℕ} {p : ℝ≥0∞} (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (hDυ : ∀ i, Periodic.MemLpPer (d := d) p (Dυ i)) :
    Periodic.MemLpPer (d := d) p
      (fun x : (Fin d → ℝ) => fun i : Fin d => Dυ i x) := by
  haveI : MeasureTheory.IsFiniteMeasure
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube (d := d))) :=
    ⟨by
      rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ]
      simp⟩
  set Dom : (Fin d → ℝ) → ℝ := fun x => ∑ i : Fin d, |Dυ i x| with hDom_def
  have habs_memLp : ∀ i, Periodic.MemLpPer (d := d) p (fun x => |Dυ i x|) := by
    intro i
    have h := (hDυ i).toMemLp.norm
    have heq : (fun x => ‖Dυ i x‖) = fun x => |Dυ i x| := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at h
    exact MemLp.toMemLpPer h
  have hDom_memLp : Periodic.MemLpPer (d := d) p Dom := by
    have hsum :
        MeasureTheory.MemLp
          (fun x => ∑ i : Fin d, (fun x => |Dυ i x|) x) p
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
      MeasureTheory.memLp_finset_sum (Finset.univ : Finset (Fin d))
        (fun i _ => (habs_memLp i).toMemLp)
    exact MemLp.toMemLpPer hsum
  have hbound :
      ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
        ‖(fun i : Fin d => Dυ i x)‖ ≤ (1 : ℝ) * ‖Dom x‖ := by
    refine Filter.Eventually.of_forall ?_
    intro x
    have hsum_nn : 0 ≤ ∑ i, |Dυ i x| :=
      Finset.sum_nonneg (fun i _ => abs_nonneg _)
    have hpi : ‖(fun i : Fin d => Dυ i x)‖ ≤ ∑ i, |Dυ i x| := by
      rw [pi_norm_le_iff_of_nonneg hsum_nn]
      intro i
      have h1 : ‖Dυ i x‖ = |Dυ i x| := Real.norm_eq_abs _
      rw [h1]
      exact Finset.single_le_sum (f := fun j => |Dυ j x|)
        (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    rw [Real.norm_eq_abs, abs_of_nonneg hsum_nn, one_mul]
    exact hpi
  have hmeas :
      MeasureTheory.AEStronglyMeasurable
        (fun x : (Fin d → ℝ) => fun i : Fin d => Dυ i x)
        (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
    have hAEm : AEMeasurable
        (fun x : (Fin d → ℝ) => fun i : Fin d => Dυ i x)
        (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
      aemeasurable_pi_iff.mpr fun i => (hDυ i).aestronglyMeasurable.aemeasurable
    exact hAEm.aestronglyMeasurable
  exact MemLp.toMemLpPer
    (MeasureTheory.MemLp.of_le_mul hDom_memLp.toMemLp hmeas hbound)

/-- **Local helper:** Hölder triple `(β+1, γ̄/(α-1), γ̄')` for
`α > 1, β > 0`. Adapted from
`holderTriple_betaBar_gammaBarOverAlphaMinus1_gammaBar_local` in
`Banach/AssemblyContext.lean:9305` (iter 0606, private there). -/
theorem palomar_BanachBridge_K0setDom_holderTriple
    {α β : ℝ} (hα : 1 < α) (hβ : 0 < β) :
    Real.HolderTriple (β + 1)
      (α * (β + 1) / β / (α - 1))
      (α * (β + 1) / β / (α * (β + 1) / β - 1)) := by
  have hαpos : 0 < α := lt_trans one_pos hα
  have hαm1_pos : 0 < α - 1 := by linarith
  have hbb_pos : 0 < β + 1 := by linarith
  have hγb_pos : 0 < α * (β + 1) / β := by positivity
  have hγb_gt_one : 1 < α * (β + 1) / β := by
    rw [lt_div_iff₀ hβ]; nlinarith
  have hγbm1_pos : 0 < α * (β + 1) / β - 1 := by linarith
  have hγb_quot_pos : 0 < α * (β + 1) / β / (α - 1) :=
    div_pos hγb_pos hαm1_pos
  refine ⟨?_, hbb_pos, hγb_quot_pos⟩
  have hβne : β ≠ 0 := hβ.ne'
  have hbb_ne : β + 1 ≠ 0 := hbb_pos.ne'
  have hαne : α ≠ 0 := hαpos.ne'
  have hαm1_ne : α - 1 ≠ 0 := hαm1_pos.ne'
  have hγb_ne : α * (β + 1) / β ≠ 0 := hγb_pos.ne'
  have hγbm1_ne : α * (β + 1) / β - 1 ≠ 0 := hγbm1_pos.ne'
  field_simp
  ring

/-! ### K0 minimal-shape set-family dominators (no `bΔm1`, no `hβ_ge_one`)

`infra-P6-K0-min-dominators-set` (audit 2026-05-21) — sibling of the iter-0767
`SetFamilyNarrowDominatorsK0` / `setFamilyNarrowDominatorsK0_of_paperHypotheses`
pair, dropping the `bΔm1 : MemLpPer βBar' (μSum + 1)` field that forced the
non-paper-faithful side condition `1 ≤ hpow.β`. The remaining eight fields
package the dominator certificates the K0 minimal-shape composer actually
consumes; the producer derives all eight inline from paper hypotheses (no
packaging-shell anti-pattern) and its signature does not include
`hβ_ge_one`. -/

/-- **`SetFamilyNarrowDominatorsK0Min` bundle.**

Minimal-shape sibling of `SetFamilyNarrowDominatorsK0`: same eight dominator
certificates `(bΔυ, bΔp_pow, bΔm_pow, bΔm_grad, bΔm_endpoint, bΔm, bG_grad,
bG_val)`, dropping the over-specified `bΔm1 : MemLpPer βBar' (μSum + 1)`
field. The dropped field was the only field of the iter-0767 bundle that
forced the non-paper-faithful side condition `1 ≤ hpow.β` on the producer. -/
structure SetFamilyNarrowDominatorsK0Min
    {d : ℕ} {βBarReal' γBarReal' γBar : ℝ}
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    (ρ₁ ρ₂ : (Fin d → ℝ) → ℝ)
    (α β : ℝ) : Type where
  /-- Dominator cert: `|uLim| + |uLim| ∈ Lᵝ'`. -/
  bΔυ : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal')
            (fun x => |uLim x| + |uLim x|)
  /-- Dominator cert for the gradient `α`-power. -/
  bΔp_pow : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal')
            (fun x =>
              ‖fun i => |DuLim i x| + |DuLim i x|‖ ^ α + 1)
  /-- Dominator cert for the density `β`-power. -/
  bΔm_pow : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal')
            (fun x =>
              (|(mLim + ρ₂) x| + |(mLim + ρ₁) x|) ^ β + 1)
  /-- Dominator cert for the gradient cross-term. -/
  bΔm_grad : Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
            (fun x => (|(mLim + ρ₂) x| + |(mLim + ρ₁) x|)
                * ‖fun i => |DuLim i x| + |DuLim i x|‖ ^ (α - 1))
  /-- Dominator cert for the endpoint exponent `1 + β - β/α`. -/
  bΔm_endpoint : Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
            (fun x =>
              (|(mLim + ρ₂) x| + |(mLim + ρ₁) x|) ^
                (1 + β - β / α))
  /-- Dominator cert for the bare density. -/
  bΔm : Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
            (fun x => |(mLim + ρ₂) x| + |(mLim + ρ₁) x|)
  /-- Dominator cert for the Gateaux gradient block. -/
  bG_grad : Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
            (fun x =>
              (∑ i, (|DuLim i x| + |DuLim i x|) ^ (2 : ℕ))
                  ^ ((γBar - 1) / 2))
  /-- Dominator cert for the Gateaux value block. -/
  bG_val : Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
            (fun x => (|uLim x| + |uLim x|) ^ (γBar - 1))

/-- **Closed paper-faithful producer for the `SetFamilyNarrowDominatorsK0Min`
bundle** (`infra-P6-K0-min-dominators-set`, audit 2026-05-21).

First sibling in the `hβ_ge_one`-removal refactor: identical to
`setFamilyNarrowDominatorsK0_of_paperHypotheses` (iter 0767) except that

* the over-specified `bΔm1 : MemLpPer βBar' (μSum + 1)` slot is dropped, and
* with it, the non-paper-faithful side condition `1 ≤ hpow.β` disappears
  from the signature.

The remaining eight dominator certificates are derived inline from the paper
hypotheses by the same routes (`MemLp.norm_rpow_div`, Hölder triple, sum
closure, `mono_exponent_finite`). The producer does not accept any of the
eight as inputs — anti-pattern-free per the iter-0767 reviewer directive. -/
noncomputable def setFamilyNarrowDominatorsK0Min_of_paperHypotheses
    {d : ℕ} {γBarReal βBarReal βBarReal' γBarReal' γBar : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (_hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (_hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    (_hβconj : βBarReal'.HolderConjugate βBarReal)
    (_hγconj : γBarReal'.HolderConjugate γBarReal)
    (hβBar_eq : βBarReal = hpow.β + 1)
    (hγBar_eq : γBarReal = hpow.α * (hpow.β + 1) / hpow.β)
    (hβBar'_eq : βBarReal' = (hpow.β + 1) / hpow.β)
    (hγBar'_eq : γBarReal' = γBarReal / (γBarReal - 1))
    (hγBar_id : γBar = γBarReal)
    {mLim uLim : (Fin d → ℝ) → ℝ}
    {DuLim : Fin d → (Fin d → ℝ) → ℝ}
    (hmLim_memLp : Periodic.MemLpPer (d := d)
                      (ENNReal.ofReal βBarReal) mLim)
    (huLim_sob : Periodic.MemSobolevPer (d := d)
                      (ENNReal.ofReal γBarReal) uLim)
    (hDuLim_memLp_γ : ∀ i, Periodic.MemLpPer (d := d)
                              (ENNReal.ofReal γBarReal) (DuLim i))
    {ρ₁ ρ₂ : (Fin d → ℝ) → ℝ}
    (hρ₁_lp : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) ρ₁)
    (hρ₂_lp : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) ρ₂)
    (_hρ₁_nn : ∀ x, 0 ≤ ρ₁ x)
    (_hρ₂_nn : ∀ x, 0 ≤ ρ₂ x) :
    SetFamilyNarrowDominatorsK0Min
      (βBarReal' := βBarReal') (γBarReal' := γBarReal') (γBar := γBar)
      mLim uLim DuLim ρ₁ ρ₂ hpow.α hpow.β := by
  -- Standing positivity facts (paper exponents).
  have hα_pos : 0 < hpow.α := lt_trans Real.zero_lt_one hpow.hα
  have hβ_pos : 0 < hpow.β := hpow.hβ
  have hβ1_pos : 0 < hpow.β + 1 := by linarith
  have hαm1_pos : 0 < hpow.α - 1 := by linarith [hpow.hα]
  have hβBarReal_pos : 0 < βBarReal := by rw [hβBar_eq]; exact hβ1_pos
  have hγBarReal_pos : 0 < γBarReal := by
    rw [hγBar_eq]
    exact div_pos (mul_pos hα_pos hβ1_pos) hβ_pos
  have hγBar_one_lt_real : 1 < γBarReal := by
    rw [hγBar_eq]; rw [lt_div_iff₀ hβ_pos, one_mul]
    have : (hpow.β + 1) < hpow.α * (hpow.β + 1) := by
      have : (1 : ℝ) * (hpow.β + 1) < hpow.α * (hpow.β + 1) :=
        mul_lt_mul_of_pos_right hpow.hα hβ1_pos
      simpa using this
    linarith
  have hβBarReal'_pos : 0 < βBarReal' := by
    rw [hβBar'_eq]; exact div_pos hβ1_pos hβ_pos
  have hγBarReal'_pos : 0 < γBarReal' := by
    rw [hγBar'_eq]; exact div_pos hγBarReal_pos (by linarith)
  -- Finite-measure instance on the unit cube.
  haveI : MeasureTheory.IsFiniteMeasure
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube (d := d))) :=
    ⟨by
      rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ]
      simp⟩
  -- Notation for the ENNReal exponents.
  set βBarE : ℝ≥0∞ := ENNReal.ofReal βBarReal with hβBarE_def
  set γBarE : ℝ≥0∞ := ENNReal.ofReal γBarReal with hγBarE_def
  set βBar'E : ℝ≥0∞ := ENNReal.ofReal βBarReal' with hβBar'E_def
  set γBar'E : ℝ≥0∞ := ENNReal.ofReal γBarReal' with hγBar'E_def
  -- `MemLpPer` certificates for `(mLim + ρ_i)` at `βBarE`.
  have hmρ₁_β : Periodic.MemLpPer (d := d) βBarE (mLim + ρ₁) :=
    hmLim_memLp.add hρ₁_lp
  have hmρ₂_β : Periodic.MemLpPer (d := d) βBarE (mLim + ρ₂) :=
    hmLim_memLp.add hρ₂_lp
  -- `MemLpPer` cert for `uLim` at `γBarE` (project from Sobolev).
  have huLim_γ : Periodic.MemLpPer (d := d) γBarE uLim := huLim_sob.1
  -- Auxiliary summed-abs functions.
  set μSum : (Fin d → ℝ) → ℝ :=
    fun x => |(mLim + ρ₂) x| + |(mLim + ρ₁) x| with hμSum_def
  set υSum : (Fin d → ℝ) → ℝ :=
    fun x => |uLim x| + |uLim x| with hυSum_def
  set DυSum : Fin d → (Fin d → ℝ) → ℝ :=
    fun i x => |DuLim i x| + |DuLim i x| with hDυSum_def
  have hμSum_β : Periodic.MemLpPer (d := d) βBarE μSum :=
    palomar_BanachBridge_K0setDom_memLpPer_abs_add_abs hmρ₂_β hmρ₁_β
  have hυSum_γ : Periodic.MemLpPer (d := d) γBarE υSum :=
    palomar_BanachBridge_K0setDom_memLpPer_abs_add_abs huLim_γ huLim_γ
  have hDυSum_γ : ∀ i, Periodic.MemLpPer (d := d) γBarE (DυSum i) :=
    fun i => palomar_BanachBridge_K0setDom_memLpPer_abs_add_abs (hDuLim_memLp_γ i) (hDuLim_memLp_γ i)
  have hμSum_paperβ :
      Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1)) μSum := by
    rw [← hβBar_eq]; exact hμSum_β
  have hone_β' : Periodic.MemLpPer (d := d) βBar'E (fun _ : (Fin d → ℝ) => (1 : ℝ)) :=
    MemLp.toMemLpPer (MeasureTheory.memLp_const (1 : ℝ))
  -- Paper-faithful standing fact: `βBarReal' ≤ γBarReal`.
  have hβ'_le_γ_real : βBarReal' ≤ γBarReal := by
    rw [hβBar'_eq, hγBar_eq]
    have h := Hamiltonian.betaBar'_le_gammaBar (hpow.hα.le) hβ_pos
    simp only [Hamiltonian.betaBar', Hamiltonian.gammaBar] at h
    exact h
  have hβ'_le_γ : βBar'E ≤ γBarE := by
    rw [hβBar'E_def, hγBarE_def]
    exact ENNReal.ofReal_le_ofReal hβ'_le_γ_real
  have hγTop : γBarE ≠ ⊤ := by rw [hγBarE_def]; exact ENNReal.ofReal_ne_top
  -- Paper-faithful standing fact: `γBarReal' ≤ βBarReal`.
  have hγ'_le_β_real : γBarReal' ≤ βBarReal := by
    rw [hγBar'_eq, hγBar_eq, hβBar_eq]
    have h := Hamiltonian.gammaBar'_le_betaBar hpow.hα hβ_pos
    exact h
  have hγ'_le_β : γBar'E ≤ βBarE := by
    rw [hγBar'E_def, hβBarE_def]
    exact ENNReal.ofReal_le_ofReal hγ'_le_β_real
  have hβTop : βBarE ≠ ⊤ := by rw [hβBarE_def]; exact ENNReal.ofReal_ne_top
  have hγ'_paper_eq : γBarReal' =
      hpow.α * (hpow.β + 1) / hpow.β /
        (hpow.α * (hpow.β + 1) / hpow.β - 1) := by
    rw [hγBar'_eq, hγBar_eq]
  -- Field (1) `bΔυ`.
  have bΔυ_cert :
      Periodic.MemLpPer (d := d) βBar'E
        (fun x => |uLim x| + |uLim x|) := by
    have hυSum_β' : Periodic.MemLpPer (d := d) βBar'E υSum :=
      Periodic.MemLpPer.mono_exponent_finite hβ'_le_γ hγTop hυSum_γ
    convert hυSum_β' using 1
  -- Field (2) `bΔp_pow`.
  have bΔp_pow_cert :
      Periodic.MemLpPer (d := d) βBar'E
        (fun x => ‖fun i => |DuLim i x| + |DuLim i x|‖ ^ hpow.α + 1) := by
    have hDυSum_vec :
        Periodic.MemLpPer (d := d) γBarE
          (fun x : (Fin d → ℝ) => fun j : Fin d => DυSum j x) :=
      palomar_BanachBridge_K0setDom_memLpPer_pi_of_coord (p := γBarE) DυSum hDυSum_γ
    set qE : ℝ≥0∞ := ENNReal.ofReal hpow.α with hqE_def
    have hqE_toReal : qE.toReal = hpow.α := by
      rw [hqE_def]; exact ENNReal.toReal_ofReal hα_pos.le
    have hT_a :
        MeasureTheory.MemLp (fun x : (Fin d → ℝ) =>
                ‖(fun j : Fin d => DυSum j x)‖ ^ qE.toReal)
              (γBarE / qE)
              (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
      MeasureTheory.MemLp.norm_rpow_div hDυSum_vec.toMemLp qE
    have hdiv : γBarE / qE = βBar'E := by
      rw [hγBarE_def, hqE_def, hβBar'E_def, hγBar_eq, hβBar'_eq,
          ← ENNReal.ofReal_div_of_pos hα_pos]
      congr 1
      field_simp
    have heq :
        (fun x : (Fin d → ℝ) =>
          ‖(fun j : Fin d => DυSum j x)‖ ^ qE.toReal)
        = (fun x : (Fin d → ℝ) =>
          ‖(fun j : Fin d => DυSum j x)‖ ^ hpow.α) := by
      funext x; rw [hqE_toReal]
    rw [heq] at hT_a
    have hT_b :
        Periodic.MemLpPer (d := d) βBar'E
          (fun x : (Fin d → ℝ) =>
            ‖fun j => |DuLim j x| + |DuLim j x|‖ ^ hpow.α) := by
      have := MemLp.toMemLpPer hT_a
      rw [hdiv] at this
      exact this
    have hsum := hT_b.add hone_β'
    have heqf :
        ((fun x : (Fin d → ℝ) =>
          ‖fun j => |DuLim j x| + |DuLim j x|‖ ^ hpow.α)
          + (fun _ : (Fin d → ℝ) => (1 : ℝ)))
        = (fun x : (Fin d → ℝ) =>
          ‖fun j => |DuLim j x| + |DuLim j x|‖ ^ hpow.α + 1) := by
      funext x; simp [Pi.add_apply]
    rw [heqf] at hsum
    exact hsum
  -- Field (3) `bΔm_pow`.
  have bΔm_pow_cert :
      Periodic.MemLpPer (d := d) βBar'E
        (fun x =>
          (|(mLim + ρ₂) x| + |(mLim + ρ₁) x|) ^ hpow.β + 1) := by
    set qE : ℝ≥0∞ := ENNReal.ofReal hpow.β with hqE_def
    have hqE_toReal : qE.toReal = hpow.β := by
      rw [hqE_def]; exact ENNReal.toReal_ofReal hβ_pos.le
    have hT_a :
        MeasureTheory.MemLp (fun x : (Fin d → ℝ) => |μSum x| ^ qE.toReal)
              (βBarE / qE)
              (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
      have h1 := MeasureTheory.MemLp.norm_rpow_div hμSum_β.toMemLp qE
      have heq :
          (fun x : (Fin d → ℝ) => ‖μSum x‖ ^ qE.toReal)
          = fun x : (Fin d → ℝ) => |μSum x| ^ qE.toReal := by
        funext x; rw [Real.norm_eq_abs]
      rw [heq] at h1
      exact h1
    have hdiv : βBarE / qE = βBar'E := by
      rw [hβBarE_def, hqE_def, hβBar'E_def, hβBar_eq, hβBar'_eq,
        ← ENNReal.ofReal_div_of_pos hβ_pos]
    have heq :
        (fun x : (Fin d → ℝ) => |μSum x| ^ qE.toReal)
        = (fun x : (Fin d → ℝ) => |μSum x| ^ hpow.β) := by
      funext x; rw [hqE_toReal]
    rw [heq] at hT_a
    have hT_b : Periodic.MemLpPer (d := d) βBar'E
        (fun x : (Fin d → ℝ) => |μSum x| ^ hpow.β) := by
      have := MemLp.toMemLpPer hT_a
      rw [hdiv] at this
      exact this
    have hμSum_nn : ∀ x, 0 ≤ μSum x := fun x => by
      rw [hμSum_def]; exact add_nonneg (abs_nonneg _) (abs_nonneg _)
    have hT_c : Periodic.MemLpPer (d := d) βBar'E
        (fun x : (Fin d → ℝ) => μSum x ^ hpow.β) := by
      have heq : (fun x : (Fin d → ℝ) => μSum x ^ hpow.β)
                = (fun x : (Fin d → ℝ) => |μSum x| ^ hpow.β) := by
        funext x; rw [abs_of_nonneg (hμSum_nn x)]
      rw [heq]; exact hT_b
    have hsum := hT_c.add hone_β'
    have heqf :
        ((fun x : (Fin d → ℝ) => μSum x ^ hpow.β)
          + (fun _ : (Fin d → ℝ) => (1 : ℝ)))
        = (fun x : (Fin d → ℝ) =>
            (|(mLim + ρ₂) x| + |(mLim + ρ₁) x|) ^ hpow.β + 1) := by
      funext x; simp [Pi.add_apply, hμSum_def]
    rw [heqf] at hsum
    exact hsum
  -- Field (4) `bΔm_grad`.
  have bΔm_grad_cert :
      Periodic.MemLpPer (d := d) γBar'E
        (fun x => (|(mLim + ρ₂) x| + |(mLim + ρ₁) x|)
            * ‖fun i => |DuLim i x| + |DuLim i x|‖ ^ (hpow.α - 1)) := by
    have hDυSum_vec :
        Periodic.MemLpPer (d := d) γBarE
          (fun x : (Fin d → ℝ) => fun j : Fin d => DυSum j x) :=
      palomar_BanachBridge_K0setDom_memLpPer_pi_of_coord (p := γBarE) DυSum hDυSum_γ
    set qE : ℝ≥0∞ := ENNReal.ofReal (hpow.α - 1) with hqE_def
    have hqE_toReal : qE.toReal = hpow.α - 1 := by
      rw [hqE_def]; exact ENNReal.toReal_ofReal hαm1_pos.le
    have hT1a :
        MeasureTheory.MemLp (fun x : (Fin d → ℝ) =>
                ‖(fun j : Fin d => DυSum j x)‖ ^ qE.toReal)
              (γBarE / qE)
              (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
      MeasureTheory.MemLp.norm_rpow_div hDυSum_vec.toMemLp qE
    have hdiv :
        γBarE / qE =
          ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β / (hpow.α - 1)) := by
      rw [hγBarE_def, hqE_def, hγBar_eq, ← ENNReal.ofReal_div_of_pos hαm1_pos]
    have heq :
        (fun x : (Fin d → ℝ) =>
          ‖(fun j : Fin d => DυSum j x)‖ ^ qE.toReal)
        = (fun x : (Fin d → ℝ) =>
          ‖fun j : Fin d => |DuLim j x| + |DuLim j x|‖ ^ (hpow.α - 1)) := by
      funext x; rw [hqE_toReal]
    rw [heq] at hT1a
    have hT1b :
        Periodic.MemLpPer (d := d)
          (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β / (hpow.α - 1)))
          (fun x : (Fin d → ℝ) =>
            ‖fun j : Fin d => |DuLim j x| + |DuLim j x|‖ ^ (hpow.α - 1)) := by
      have := MemLp.toMemLpPer hT1a
      rw [hdiv] at this
      exact this
    have hHT_real :
        Real.HolderTriple (hpow.β + 1)
          (hpow.α * (hpow.β + 1) / hpow.β / (hpow.α - 1))
          (hpow.α * (hpow.β + 1) / hpow.β /
              (hpow.α * (hpow.β + 1) / hpow.β - 1)) :=
      palomar_BanachBridge_K0setDom_holderTriple hpow.hα hpow.hβ
    haveI hHT_enn :
        ENNReal.HolderTriple (ENNReal.ofReal (hpow.β + 1))
          (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β / (hpow.α - 1)))
          (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β /
              (hpow.α * (hpow.β + 1) / hpow.β - 1))) :=
      hHT_real.ennrealOfReal
    have hT1c :
        MeasureTheory.MemLp
          (fun x : (Fin d → ℝ) =>
            μSum x * ‖fun j => |DuLim j x| + |DuLim j x|‖ ^ (hpow.α - 1))
          (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β /
              (hpow.α * (hpow.β + 1) / hpow.β - 1)))
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
      (hμSum_paperβ.toMemLp.fun_mul hT1b.toMemLp : _)
    have hres :
        Periodic.MemLpPer (d := d)
          (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β /
              (hpow.α * (hpow.β + 1) / hpow.β - 1)))
          (fun x : (Fin d → ℝ) =>
            (|(mLim + ρ₂) x| + |(mLim + ρ₁) x|) *
              ‖fun j => |DuLim j x| + |DuLim j x|‖ ^ (hpow.α - 1)) := by
      have := MemLp.toMemLpPer hT1c
      convert this using 1
    have hexp_eq : γBar'E =
        ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β /
            (hpow.α * (hpow.β + 1) / hpow.β - 1)) := by
      rw [hγBar'E_def, hγ'_paper_eq]
    rw [hexp_eq]; exact hres
  -- Field (5) `bΔm_endpoint`.
  have bΔm_endpoint_cert :
      Periodic.MemLpPer (d := d) γBar'E
        (fun x =>
          (|(mLim + ρ₂) x| + |(mLim + ρ₁) x|) ^
            (1 + hpow.β - hpow.β / hpow.α)) := by
    have hβα_pos : 0 < hpow.β / hpow.α := div_pos hβ_pos hα_pos
    have hβα_lt : hpow.β / hpow.α < hpow.β + 1 := by
      have h1 : hpow.β / hpow.α ≤ hpow.β := by
        rw [div_le_iff₀ hα_pos]
        nlinarith [hpow.hα, hβ_pos]
      linarith
    have hexp_pos : 0 < hpow.β + 1 - hpow.β / hpow.α := by linarith
    set qE : ℝ≥0∞ := ENNReal.ofReal (hpow.β + 1 - hpow.β / hpow.α) with hqE_def
    have hqE_toReal : qE.toReal = hpow.β + 1 - hpow.β / hpow.α := by
      rw [hqE_def]; exact ENNReal.toReal_ofReal hexp_pos.le
    have hT2a :
        MeasureTheory.MemLp (fun x : (Fin d → ℝ) => |μSum x| ^ qE.toReal)
              ((ENNReal.ofReal (hpow.β + 1)) / qE)
              (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
      have h1 := MeasureTheory.MemLp.norm_rpow_div hμSum_paperβ.toMemLp qE
      have heq :
          (fun x : (Fin d → ℝ) => ‖μSum x‖ ^ qE.toReal)
          = fun x : (Fin d → ℝ) => |μSum x| ^ qE.toReal := by
        funext x; rw [Real.norm_eq_abs]
      rw [heq] at h1
      exact h1
    have hβne : hpow.β ≠ 0 := hβ_pos.ne'
    have hαne : hpow.α ≠ 0 := hα_pos.ne'
    have hbb_ne : hpow.β + 1 ≠ 0 := hβ1_pos.ne'
    have hβbβα_ne : hpow.β + 1 - hpow.β / hpow.α ≠ 0 := hexp_pos.ne'
    have hgb_gt_one : 1 < hpow.α * (hpow.β + 1) / hpow.β := by
      rw [lt_div_iff₀ hβ_pos]; nlinarith [hpow.hα, hβ_pos]
    have hγb_ne : hpow.α * (hpow.β + 1) / hpow.β ≠ 0 := by
      have : 0 < hpow.α * (hpow.β + 1) / hpow.β :=
        div_pos (mul_pos hα_pos hβ1_pos) hβ_pos
      exact this.ne'
    have hγbm1_ne : hpow.α * (hpow.β + 1) / hpow.β - 1 ≠ 0 := by linarith
    have hdiv_eq :
        (ENNReal.ofReal (hpow.β + 1)) / qE = γBar'E := by
      rw [hqE_def, hγBar'E_def, hγBar'_eq, hγBar_eq,
        ← ENNReal.ofReal_div_of_pos hexp_pos]
      congr 1
      field_simp
    have heq :
        (fun x : (Fin d → ℝ) => |μSum x| ^ qE.toReal)
        = (fun x : (Fin d → ℝ) => |μSum x| ^ (hpow.β + 1 - hpow.β / hpow.α)) := by
      funext x; rw [hqE_toReal]
    rw [heq] at hT2a
    have hT2b :
        Periodic.MemLpPer (d := d) γBar'E
          (fun x : (Fin d → ℝ) => |μSum x| ^ (hpow.β + 1 - hpow.β / hpow.α)) := by
      have := MemLp.toMemLpPer hT2a
      rw [hdiv_eq] at this
      exact this
    have hsh : (1 : ℝ) + hpow.β - hpow.β / hpow.α
                  = hpow.β + 1 - hpow.β / hpow.α := by ring
    have hbound :
        ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
          ‖μSum x ^ (1 + hpow.β - hpow.β / hpow.α)‖ ≤
            (1 : ℝ) * ‖|μSum x| ^ (hpow.β + 1 - hpow.β / hpow.α)‖ := by
      refine Filter.Eventually.of_forall ?_
      intro x
      rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul, hsh]
      have habs := Real.abs_rpow_le_abs_rpow (μSum x) (hpow.β + 1 - hpow.β / hpow.α)
      have hrhs_nn : 0 ≤ |μSum x| ^ (hpow.β + 1 - hpow.β / hpow.α) :=
        Real.rpow_nonneg (abs_nonneg _) _
      rw [abs_of_nonneg hrhs_nn]
      exact habs
    have hmeas :
        MeasureTheory.AEStronglyMeasurable
          (fun x : (Fin d → ℝ) => μSum x ^ (1 + hpow.β - hpow.β / hpow.α))
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
      have h_exp_nn : (0 : ℝ) ≤ 1 + hpow.β - hpow.β / hpow.α := by linarith [hexp_pos]
      have hcont : Continuous (fun y : ℝ => y ^ (1 + hpow.β - hpow.β / hpow.α)) :=
        Real.continuous_rpow_const h_exp_nn
      exact hcont.comp_aestronglyMeasurable hμSum_β.aestronglyMeasurable
    have hT2c :
        Periodic.MemLpPer (d := d) γBar'E
          (fun x : (Fin d → ℝ) => μSum x ^ (1 + hpow.β - hpow.β / hpow.α)) :=
      MemLp.toMemLpPer
        (MeasureTheory.MemLp.of_le_mul hT2b.toMemLp hmeas hbound)
    convert hT2c using 1
  -- Field (6) `bΔm`.
  have bΔm_cert :
      Periodic.MemLpPer (d := d) γBar'E
        (fun x => |(mLim + ρ₂) x| + |(mLim + ρ₁) x|) := by
    have hT10 : Periodic.MemLpPer (d := d) γBar'E μSum :=
      Periodic.MemLpPer.mono_exponent_finite hγ'_le_β hβTop hμSum_β
    convert hT10 using 1
  -- Field (7) `bG_grad`.
  have bG_grad_cert :
      Periodic.MemLpPer (d := d) γBar'E
        (fun x =>
          (∑ i, (|DuLim i x| + |DuLim i x|) ^ (2 : ℕ))
              ^ ((γBar - 1) / 2)) := by
    set q2E : ℝ≥0∞ := (2 : ℝ≥0∞) with hq2E_def
    have hq2E_top : q2E ≠ ⊤ := by rw [hq2E_def]; decide
    have hq2E_toReal : q2E.toReal = 2 := by rw [hq2E_def]; rfl
    have hSq_each : ∀ i,
        MeasureTheory.MemLp
          (fun x : (Fin d → ℝ) => ‖DυSum i x‖ ^ q2E.toReal)
          (γBarE / q2E)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
      fun i => MeasureTheory.MemLp.norm_rpow_div (hDυSum_γ i).toMemLp q2E
    have hSq_each' : ∀ i,
        Periodic.MemLpPer (d := d) (γBarE / q2E)
          (fun x : (Fin d → ℝ) => (DυSum i x) ^ (2 : ℕ)) := by
      intro i
      have h := hSq_each i
      have heq :
          (fun x : (Fin d → ℝ) => ‖DυSum i x‖ ^ q2E.toReal)
          = (fun x : (Fin d → ℝ) => (DυSum i x) ^ (2 : ℕ)) := by
        funext x
        rw [hq2E_toReal, Real.norm_eq_abs]
        rw [show ((2 : ℝ) = ((2 : ℕ) : ℝ)) from by norm_num,
            Real.rpow_natCast, sq_abs]
      rw [heq] at h
      exact MemLp.toMemLpPer h
    have hSumSq :
        Periodic.MemLpPer (d := d) (γBarE / q2E)
          (fun x : (Fin d → ℝ) => ∑ i, (DυSum i x) ^ (2 : ℕ)) := by
      have hsum : MeasureTheory.MemLp
          (fun x : (Fin d → ℝ) => ∑ i : Fin d, (fun x => (DυSum i x) ^ (2 : ℕ)) x)
          (γBarE / q2E)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
        refine MeasureTheory.memLp_finset_sum (Finset.univ : Finset (Fin d)) ?_
        intro i _; exact (hSq_each' i).toMemLp
      exact MemLp.toMemLpPer hsum
    have hγm1_pos : 0 < γBarReal - 1 := by linarith
    have hexp12_pos : 0 < (γBarReal - 1) / 2 := by linarith
    set qE : ℝ≥0∞ := ENNReal.ofReal ((γBarReal - 1) / 2) with hqE_def
    have hqE_toReal : qE.toReal = (γBarReal - 1) / 2 := by
      rw [hqE_def]; exact ENNReal.toReal_ofReal hexp12_pos.le
    have hRpow : MeasureTheory.MemLp
        (fun x : (Fin d → ℝ) =>
          ‖∑ i, (DυSum i x) ^ (2 : ℕ)‖ ^ qE.toReal)
        ((γBarE / q2E) / qE)
        (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
      MeasureTheory.MemLp.norm_rpow_div hSumSq.toMemLp qE
    have hdiv_eq : (γBarE / q2E) / qE = γBar'E := by
      rw [hq2E_def, hqE_def, hγBarE_def, hγBar'E_def, hγBar'_eq,
          ← ENNReal.ofReal_ofNat (n := 2),
          ← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
          ← ENNReal.ofReal_div_of_pos hexp12_pos]
      congr 1
      have hγne : γBarReal ≠ 0 := hγBarReal_pos.ne'
      have hγm1ne : γBarReal - 1 ≠ 0 := hγm1_pos.ne'
      field_simp
    have hSumSq_nn : ∀ x, 0 ≤ ∑ i, (DυSum i x) ^ (2 : ℕ) :=
      fun x => Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have heqfn :
        (fun x : (Fin d → ℝ) =>
          ‖∑ i, (DυSum i x) ^ (2 : ℕ)‖ ^ qE.toReal)
        = (fun x : (Fin d → ℝ) =>
            (∑ i, (DυSum i x) ^ (2 : ℕ)) ^ ((γBarReal - 1) / 2)) := by
      funext x
      rw [hqE_toReal, Real.norm_eq_abs, abs_of_nonneg (hSumSq_nn x)]
    rw [heqfn] at hRpow
    have hres :
        Periodic.MemLpPer (d := d) γBar'E
          (fun x : (Fin d → ℝ) =>
            (∑ i, (DυSum i x) ^ (2 : ℕ)) ^ ((γBarReal - 1) / 2)) := by
      have := MemLp.toMemLpPer hRpow
      rw [hdiv_eq] at this
      exact this
    rw [hγBar_id]
    convert hres using 1
  -- Field (8) `bG_val`.
  have bG_val_cert :
      Periodic.MemLpPer (d := d) γBar'E
        (fun x => (|uLim x| + |uLim x|) ^ (γBar - 1)) := by
    have hγm1_pos : 0 < γBarReal - 1 := by linarith
    set qE : ℝ≥0∞ := ENNReal.ofReal (γBarReal - 1) with hqE_def
    have hqE_toReal : qE.toReal = γBarReal - 1 := by
      rw [hqE_def]; exact ENNReal.toReal_ofReal hγm1_pos.le
    have hRpow : MeasureTheory.MemLp
        (fun x : (Fin d → ℝ) => ‖υSum x‖ ^ qE.toReal)
        (γBarE / qE)
        (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
      MeasureTheory.MemLp.norm_rpow_div hυSum_γ.toMemLp qE
    have hdiv : γBarE / qE = γBar'E := by
      rw [hqE_def, hγBarE_def, hγBar'E_def, hγBar'_eq,
        ← ENNReal.ofReal_div_of_pos hγm1_pos]
    have hυSum_nn : ∀ x, 0 ≤ υSum x := fun x => by
      rw [hυSum_def]; exact add_nonneg (abs_nonneg _) (abs_nonneg _)
    have heq :
        (fun x : (Fin d → ℝ) => ‖υSum x‖ ^ qE.toReal)
        = (fun x : (Fin d → ℝ) => υSum x ^ (γBarReal - 1)) := by
      funext x
      rw [hqE_toReal, Real.norm_eq_abs, abs_of_nonneg (hυSum_nn x)]
    rw [heq] at hRpow
    have hres : Periodic.MemLpPer (d := d) γBar'E
        (fun x : (Fin d → ℝ) => υSum x ^ (γBarReal - 1)) := by
      have := MemLp.toMemLpPer hRpow
      rw [hdiv] at this
      exact this
    rw [hγBar_id]
    convert hres using 1
  -- Bundle the eight derived certs.
  exact
    { bΔυ := bΔυ_cert
      bΔp_pow := bΔp_pow_cert
      bΔm_pow := bΔm_pow_cert
      bΔm_grad := bΔm_grad_cert
      bΔm_endpoint := bΔm_endpoint_cert
      bΔm := bΔm_cert
      bG_grad := bG_grad_cert
      bG_val := bG_val_cert }

/-- **Sanity-check `example` for the minimal-shape K0 set producer.** At
`ρ₁ = ρ₂ = 0` and at the paper exponent identities, the producer derives all
eight `MemLpPer`-of-power dominator certificates at the shapes consumed by
the K0 minimal-shape composer. Crucially, the caller does **not** supply
`hβ_ge_one`. -/
example
    {d : ℕ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    [Fact (1 ≤ ENNReal.ofReal (hpow.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))]
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    (hβconj :
      Real.HolderConjugate ((hpow.β + 1) / hpow.β) (hpow.β + 1))
    (hγconj :
      Real.HolderConjugate
        (hpow.α * (hpow.β + 1) / hpow.β /
          (hpow.α * (hpow.β + 1) / hpow.β - 1))
        (hpow.α * (hpow.β + 1) / hpow.β))
    {mLim uLim : (Fin d → ℝ) → ℝ}
    {DuLim : Fin d → (Fin d → ℝ) → ℝ}
    (hmLim_memLp : Periodic.MemLpPer (d := d)
                      (ENNReal.ofReal (hpow.β + 1)) mLim)
    (huLim_sob : Periodic.MemSobolevPer (d := d)
                      (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))
                      uLim)
    (hDuLim_memLp_γ : ∀ i, Periodic.MemLpPer (d := d)
                              (ENNReal.ofReal
                                (hpow.α * (hpow.β + 1) / hpow.β))
                              (DuLim i)) :
    SetFamilyNarrowDominatorsK0Min
      (βBarReal' := (hpow.β + 1) / hpow.β)
      (γBarReal' := (hpow.α * (hpow.β + 1) / hpow.β) /
                     (hpow.α * (hpow.β + 1) / hpow.β - 1))
      (γBar := hpow.α * (hpow.β + 1) / hpow.β)
      mLim uLim DuLim
      (fun _ : Fin d → ℝ => (0 : ℝ)) (fun _ : Fin d → ℝ => (0 : ℝ))
      hpow.α hpow.β :=
  setFamilyNarrowDominatorsK0Min_of_paperHypotheses
    (d := d)
    (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
    (βBarReal := hpow.β + 1)
    (βBarReal' := (hpow.β + 1) / hpow.β)
    (γBarReal' := (hpow.α * (hpow.β + 1) / hpow.β) /
                   (hpow.α * (hpow.β + 1) / hpow.β - 1))
    (γBar := hpow.α * (hpow.β + 1) / hpow.β)
    (H := H) (DpH := DpH)
    hpow hHat0 hAgree hβconj hγconj
    rfl rfl rfl rfl rfl
    hmLim_memLp huLim_sob hDuLim_memLp_γ
    (Periodic.MemLpPer.const (d := d) (0 : ℝ))
    (Periodic.MemLpPer.const (d := d) (0 : ℝ))
    (fun _ => le_refl 0) (fun _ => le_refl 0)

/-! ### Signed mirror of iter-0767 K0 set dominators producer

`infra-P5-T10-v8-K0-signed-dominators-producer` — signed mirror of the
iter-0767 set-family K0 dominators producer. Same nine `MemLpPer`-of-power
dominator certificates, packaged at the **unshifted signed** endpoints
`(mLim + g₁, mLim + g₂)`, derived inline from paper hypotheses (no
packaging-shell anti-pattern; the iter-0767 anti-pattern-free template).

**Signed vs. set input shape.** The set family receives `(ρ_i)` perturbations
with `MemLpPer βBar ρ_i` and pointwise nonneg `0 ≤ ρ_i`, then builds
`MemLpPer βBar (mLim + ρ_i) = hmLim_memLp.add hρ_i_lp`. The signed family
allows negative perturbations, so the joint primal a.e.-nonnegativity
`0 ≤ᵐ (mLim + g_i)` is the caller-supplied side condition (not a pointwise
fact about `g_i`), and `MemLpPer βBar (mLim + g_i)` is supplied directly
on the sum (the joint regularity from the weak-limit bundle, surfaced via
`D_signed_family_paper_nn` membership in downstream callers).

After binding the joint `hmg_i_β : MemLpPer βBar (mLim + g_i)`, the body is
verbatim the iter-0767 derivation: build `μSum`/`υSum`/`DυSum`, the nine
`MemLpPer` certificates via `MemLpPer.abs/.add/.rpow/.mul/.of_le_mul`,
Hölder triple, sum-closure. -/

/-! ### K0 minimal-shape signed-family dominators (no `bΔm1`, no `hβ_ge_one`)

`infra-P6-K0-min-dominators-signed` (audit 2026-05-22) — signed mirror of the
iter-0786 `SetFamilyNarrowDominatorsK0Min` /
`setFamilyNarrowDominatorsK0Min_of_paperHypotheses` pair, dropping the
`bΔm1 : MemLpPer βBar' (μSum + 1)` field (and with it the non-paper-faithful
side condition `1 ≤ hpow.β` from the signature). The remaining eight fields
package the dominator certificates the K0 minimal-shape signed composer
actually consumes; the producer derives all eight inline from paper
hypotheses (no packaging-shell anti-pattern). -/

/-- **`SignedFamilyNarrowDominatorsK0Min` bundle.**

Minimal-shape sibling of `SignedFamilyNarrowDominatorsK0`: same eight
dominator certificates `(bΔυ, bΔp_pow, bΔm_pow, bΔm_grad, bΔm_endpoint, bΔm,
bG_grad, bG_val)`, dropping the over-specified
`bΔm1 : MemLpPer βBar' (μSum + 1)` field. The dropped field was the only
field of the iter-0773 signed bundle that forced the non-paper-faithful
side condition `1 ≤ hpow.β` on the producer. -/
structure SignedFamilyNarrowDominatorsK0Min
    {d : ℕ} {βBarReal' γBarReal' γBar : ℝ}
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    (g₁ g₂ : (Fin d → ℝ) → ℝ)
    (α β : ℝ) : Type where
  /-- Dominator cert: `|uLim| + |uLim| ∈ Lᵝ'`. -/
  bΔυ : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal')
            (fun x => |uLim x| + |uLim x|)
  /-- Dominator cert for the gradient `α`-power. -/
  bΔp_pow : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal')
            (fun x =>
              ‖fun i => |DuLim i x| + |DuLim i x|‖ ^ α + 1)
  /-- Dominator cert for the density `β`-power. -/
  bΔm_pow : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal')
            (fun x =>
              (|(mLim + g₂) x| + |(mLim + g₁) x|) ^ β + 1)
  /-- Dominator cert for the gradient cross-term. -/
  bΔm_grad : Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
            (fun x => (|(mLim + g₂) x| + |(mLim + g₁) x|)
                * ‖fun i => |DuLim i x| + |DuLim i x|‖ ^ (α - 1))
  /-- Dominator cert for the endpoint exponent `1 + β - β/α`. -/
  bΔm_endpoint : Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
            (fun x =>
              (|(mLim + g₂) x| + |(mLim + g₁) x|) ^
                (1 + β - β / α))
  /-- Dominator cert for the bare density. -/
  bΔm : Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
            (fun x => |(mLim + g₂) x| + |(mLim + g₁) x|)
  /-- Dominator cert for the Gateaux gradient block. -/
  bG_grad : Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
            (fun x =>
              (∑ i, (|DuLim i x| + |DuLim i x|) ^ (2 : ℕ))
                  ^ ((γBar - 1) / 2))
  /-- Dominator cert for the Gateaux value block. -/
  bG_val : Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
            (fun x => (|uLim x| + |uLim x|) ^ (γBar - 1))

/-- **Closed paper-faithful producer for the `SignedFamilyNarrowDominatorsK0Min`
bundle** (`infra-P6-K0-min-dominators-signed`, audit 2026-05-22).

Signed sibling of `setFamilyNarrowDominatorsK0Min_of_paperHypotheses` and
minimal-shape sibling of `signedFamilyNarrowDominatorsK0_of_paperHypotheses`:
identical to the latter except that

* the over-specified `bΔm1 : MemLpPer βBar' (μSum + 1)` slot is dropped, and
* with it, the non-paper-faithful side condition `1 ≤ hpow.β` disappears
  from the signature.

The remaining eight dominator certificates are derived inline from the paper
hypotheses by the same routes (`MemLp.norm_rpow_div`, Hölder triple, sum
closure, `mono_exponent_finite`). The producer does not accept any of the
eight as inputs — anti-pattern-free per the iter-0767 reviewer directive. -/
noncomputable def signedFamilyNarrowDominatorsK0Min_of_paperHypotheses
    {d : ℕ} {γBarReal βBarReal βBarReal' γBarReal' γBar : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (_hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (_hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    (_hβconj : βBarReal'.HolderConjugate βBarReal)
    (_hγconj : γBarReal'.HolderConjugate γBarReal)
    (hβBar_eq : βBarReal = hpow.β + 1)
    (hγBar_eq : γBarReal = hpow.α * (hpow.β + 1) / hpow.β)
    (hβBar'_eq : βBarReal' = (hpow.β + 1) / hpow.β)
    (hγBar'_eq : γBarReal' = γBarReal / (γBarReal - 1))
    (hγBar_id : γBar = γBarReal)
    {mLim uLim : (Fin d → ℝ) → ℝ}
    {DuLim : Fin d → (Fin d → ℝ) → ℝ}
    (hmLim_memLp : Periodic.MemLpPer (d := d)
                      (ENNReal.ofReal βBarReal) mLim)
    (huLim_sob : Periodic.MemSobolevPer (d := d)
                      (ENNReal.ofReal γBarReal) uLim)
    (hDuLim_memLp_γ : ∀ i, Periodic.MemLpPer (d := d)
                              (ENNReal.ofReal γBarReal) (DuLim i))
    {g₁ g₂ : (Fin d → ℝ) → ℝ}
    -- Joint primal Lᵝ certificates `(mLim + g_i) ∈ Lᵝ` (signed mirror;
    -- caller supplies the sum directly, since `g_i` need not be nonneg).
    (hmg₁_β : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal)
                (mLim + g₁))
    (hmg₂_β : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal)
                (mLim + g₂))
    -- Joint primal a.e.-nonneg `0 ≤ᵐ (mLim + g_i)` (signed mirror;
    -- plumbed for downstream consumers, unused in this producer body).
    (_hjoint₁_nn : ∀ᵐ x ∂(MeasureTheory.Measure.restrict
                            MeasureTheory.volume (UnitCube (d := d))),
        0 ≤ (mLim + g₁) x)
    (_hjoint₂_nn : ∀ᵐ x ∂(MeasureTheory.Measure.restrict
                            MeasureTheory.volume (UnitCube (d := d))),
        0 ≤ (mLim + g₂) x) :
    SignedFamilyNarrowDominatorsK0Min
      (βBarReal' := βBarReal') (γBarReal' := γBarReal') (γBar := γBar)
      mLim uLim DuLim g₁ g₂ hpow.α hpow.β := by
  -- Standing positivity facts (paper exponents).
  have hα_pos : 0 < hpow.α := lt_trans Real.zero_lt_one hpow.hα
  have hβ_pos : 0 < hpow.β := hpow.hβ
  have hβ1_pos : 0 < hpow.β + 1 := by linarith
  have hαm1_pos : 0 < hpow.α - 1 := by linarith [hpow.hα]
  have hβBarReal_pos : 0 < βBarReal := by rw [hβBar_eq]; exact hβ1_pos
  have hγBarReal_pos : 0 < γBarReal := by
    rw [hγBar_eq]
    exact div_pos (mul_pos hα_pos hβ1_pos) hβ_pos
  have hγBar_one_lt_real : 1 < γBarReal := by
    rw [hγBar_eq]; rw [lt_div_iff₀ hβ_pos, one_mul]
    have : (hpow.β + 1) < hpow.α * (hpow.β + 1) := by
      have : (1 : ℝ) * (hpow.β + 1) < hpow.α * (hpow.β + 1) :=
        mul_lt_mul_of_pos_right hpow.hα hβ1_pos
      simpa using this
    linarith
  have hβBarReal'_pos : 0 < βBarReal' := by
    rw [hβBar'_eq]; exact div_pos hβ1_pos hβ_pos
  have hγBarReal'_pos : 0 < γBarReal' := by
    rw [hγBar'_eq]; exact div_pos hγBarReal_pos (by linarith)
  -- Finite-measure instance on the unit cube.
  haveI : MeasureTheory.IsFiniteMeasure
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube (d := d))) :=
    ⟨by
      rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ]
      simp⟩
  -- Notation for the ENNReal exponents.
  set βBarE : ℝ≥0∞ := ENNReal.ofReal βBarReal with hβBarE_def
  set γBarE : ℝ≥0∞ := ENNReal.ofReal γBarReal with hγBarE_def
  set βBar'E : ℝ≥0∞ := ENNReal.ofReal βBarReal' with hβBar'E_def
  set γBar'E : ℝ≥0∞ := ENNReal.ofReal γBarReal' with hγBar'E_def
  -- `MemLpPer` certificates for `(mLim + g_i)` at `βBarE` (signed shape:
  -- caller-supplied directly).
  have hmg₁_β' : Periodic.MemLpPer (d := d) βBarE (mLim + g₁) := hmg₁_β
  have hmg₂_β' : Periodic.MemLpPer (d := d) βBarE (mLim + g₂) := hmg₂_β
  -- `MemLpPer` cert for `uLim` at `γBarE` (project from Sobolev).
  have huLim_γ : Periodic.MemLpPer (d := d) γBarE uLim := huLim_sob.1
  -- Auxiliary summed-abs functions.
  set μSum : (Fin d → ℝ) → ℝ :=
    fun x => |(mLim + g₂) x| + |(mLim + g₁) x| with hμSum_def
  set υSum : (Fin d → ℝ) → ℝ :=
    fun x => |uLim x| + |uLim x| with hυSum_def
  set DυSum : Fin d → (Fin d → ℝ) → ℝ :=
    fun i x => |DuLim i x| + |DuLim i x| with hDυSum_def
  have hμSum_β : Periodic.MemLpPer (d := d) βBarE μSum :=
    palomar_BanachBridge_K0setDom_memLpPer_abs_add_abs hmg₂_β' hmg₁_β'
  have hυSum_γ : Periodic.MemLpPer (d := d) γBarE υSum :=
    palomar_BanachBridge_K0setDom_memLpPer_abs_add_abs huLim_γ huLim_γ
  have hDυSum_γ : ∀ i, Periodic.MemLpPer (d := d) γBarE (DυSum i) :=
    fun i => palomar_BanachBridge_K0setDom_memLpPer_abs_add_abs (hDuLim_memLp_γ i) (hDuLim_memLp_γ i)
  have hμSum_paperβ :
      Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1)) μSum := by
    rw [← hβBar_eq]; exact hμSum_β
  have hone_β' : Periodic.MemLpPer (d := d) βBar'E (fun _ : (Fin d → ℝ) => (1 : ℝ)) :=
    MemLp.toMemLpPer (MeasureTheory.memLp_const (1 : ℝ))
  -- Paper-faithful standing fact: `βBarReal' ≤ γBarReal`.
  have hβ'_le_γ_real : βBarReal' ≤ γBarReal := by
    rw [hβBar'_eq, hγBar_eq]
    have h := Hamiltonian.betaBar'_le_gammaBar (hpow.hα.le) hβ_pos
    simp only [Hamiltonian.betaBar', Hamiltonian.gammaBar] at h
    exact h
  have hβ'_le_γ : βBar'E ≤ γBarE := by
    rw [hβBar'E_def, hγBarE_def]
    exact ENNReal.ofReal_le_ofReal hβ'_le_γ_real
  have hγTop : γBarE ≠ ⊤ := by rw [hγBarE_def]; exact ENNReal.ofReal_ne_top
  -- Paper-faithful standing fact: `γBarReal' ≤ βBarReal`.
  have hγ'_le_β_real : γBarReal' ≤ βBarReal := by
    rw [hγBar'_eq, hγBar_eq, hβBar_eq]
    have h := Hamiltonian.gammaBar'_le_betaBar hpow.hα hβ_pos
    exact h
  have hγ'_le_β : γBar'E ≤ βBarE := by
    rw [hγBar'E_def, hβBarE_def]
    exact ENNReal.ofReal_le_ofReal hγ'_le_β_real
  have hβTop : βBarE ≠ ⊤ := by rw [hβBarE_def]; exact ENNReal.ofReal_ne_top
  have hγ'_paper_eq : γBarReal' =
      hpow.α * (hpow.β + 1) / hpow.β /
        (hpow.α * (hpow.β + 1) / hpow.β - 1) := by
    rw [hγBar'_eq, hγBar_eq]
  -- Field (1) `bΔυ`.
  have bΔυ_cert :
      Periodic.MemLpPer (d := d) βBar'E
        (fun x => |uLim x| + |uLim x|) := by
    have hυSum_β' : Periodic.MemLpPer (d := d) βBar'E υSum :=
      Periodic.MemLpPer.mono_exponent_finite hβ'_le_γ hγTop hυSum_γ
    convert hυSum_β' using 1
  -- Field (2) `bΔp_pow`.
  have bΔp_pow_cert :
      Periodic.MemLpPer (d := d) βBar'E
        (fun x => ‖fun i => |DuLim i x| + |DuLim i x|‖ ^ hpow.α + 1) := by
    have hDυSum_vec :
        Periodic.MemLpPer (d := d) γBarE
          (fun x : (Fin d → ℝ) => fun j : Fin d => DυSum j x) :=
      palomar_BanachBridge_K0setDom_memLpPer_pi_of_coord (p := γBarE) DυSum hDυSum_γ
    set qE : ℝ≥0∞ := ENNReal.ofReal hpow.α with hqE_def
    have hqE_toReal : qE.toReal = hpow.α := by
      rw [hqE_def]; exact ENNReal.toReal_ofReal hα_pos.le
    have hT_a :
        MeasureTheory.MemLp (fun x : (Fin d → ℝ) =>
                ‖(fun j : Fin d => DυSum j x)‖ ^ qE.toReal)
              (γBarE / qE)
              (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
      MeasureTheory.MemLp.norm_rpow_div hDυSum_vec.toMemLp qE
    have hdiv : γBarE / qE = βBar'E := by
      rw [hγBarE_def, hqE_def, hβBar'E_def, hγBar_eq, hβBar'_eq,
          ← ENNReal.ofReal_div_of_pos hα_pos]
      congr 1
      field_simp
    have heq :
        (fun x : (Fin d → ℝ) =>
          ‖(fun j : Fin d => DυSum j x)‖ ^ qE.toReal)
        = (fun x : (Fin d → ℝ) =>
          ‖(fun j : Fin d => DυSum j x)‖ ^ hpow.α) := by
      funext x; rw [hqE_toReal]
    rw [heq] at hT_a
    have hT_b :
        Periodic.MemLpPer (d := d) βBar'E
          (fun x : (Fin d → ℝ) =>
            ‖fun j => |DuLim j x| + |DuLim j x|‖ ^ hpow.α) := by
      have := MemLp.toMemLpPer hT_a
      rw [hdiv] at this
      exact this
    have hsum := hT_b.add hone_β'
    have heqf :
        ((fun x : (Fin d → ℝ) =>
          ‖fun j => |DuLim j x| + |DuLim j x|‖ ^ hpow.α)
          + (fun _ : (Fin d → ℝ) => (1 : ℝ)))
        = (fun x : (Fin d → ℝ) =>
          ‖fun j => |DuLim j x| + |DuLim j x|‖ ^ hpow.α + 1) := by
      funext x; simp [Pi.add_apply]
    rw [heqf] at hsum
    exact hsum
  -- Field (3) `bΔm_pow`.
  have bΔm_pow_cert :
      Periodic.MemLpPer (d := d) βBar'E
        (fun x =>
          (|(mLim + g₂) x| + |(mLim + g₁) x|) ^ hpow.β + 1) := by
    set qE : ℝ≥0∞ := ENNReal.ofReal hpow.β with hqE_def
    have hqE_toReal : qE.toReal = hpow.β := by
      rw [hqE_def]; exact ENNReal.toReal_ofReal hβ_pos.le
    have hT_a :
        MeasureTheory.MemLp (fun x : (Fin d → ℝ) => |μSum x| ^ qE.toReal)
              (βBarE / qE)
              (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
      have h1 := MeasureTheory.MemLp.norm_rpow_div hμSum_β.toMemLp qE
      have heq :
          (fun x : (Fin d → ℝ) => ‖μSum x‖ ^ qE.toReal)
          = fun x : (Fin d → ℝ) => |μSum x| ^ qE.toReal := by
        funext x; rw [Real.norm_eq_abs]
      rw [heq] at h1
      exact h1
    have hdiv : βBarE / qE = βBar'E := by
      rw [hβBarE_def, hqE_def, hβBar'E_def, hβBar_eq, hβBar'_eq,
        ← ENNReal.ofReal_div_of_pos hβ_pos]
    have heq :
        (fun x : (Fin d → ℝ) => |μSum x| ^ qE.toReal)
        = (fun x : (Fin d → ℝ) => |μSum x| ^ hpow.β) := by
      funext x; rw [hqE_toReal]
    rw [heq] at hT_a
    have hT_b : Periodic.MemLpPer (d := d) βBar'E
        (fun x : (Fin d → ℝ) => |μSum x| ^ hpow.β) := by
      have := MemLp.toMemLpPer hT_a
      rw [hdiv] at this
      exact this
    have hμSum_nn : ∀ x, 0 ≤ μSum x := fun x => by
      rw [hμSum_def]; exact add_nonneg (abs_nonneg _) (abs_nonneg _)
    have hT_c : Periodic.MemLpPer (d := d) βBar'E
        (fun x : (Fin d → ℝ) => μSum x ^ hpow.β) := by
      have heq : (fun x : (Fin d → ℝ) => μSum x ^ hpow.β)
                = (fun x : (Fin d → ℝ) => |μSum x| ^ hpow.β) := by
        funext x; rw [abs_of_nonneg (hμSum_nn x)]
      rw [heq]; exact hT_b
    have hsum := hT_c.add hone_β'
    have heqf :
        ((fun x : (Fin d → ℝ) => μSum x ^ hpow.β)
          + (fun _ : (Fin d → ℝ) => (1 : ℝ)))
        = (fun x : (Fin d → ℝ) =>
            (|(mLim + g₂) x| + |(mLim + g₁) x|) ^ hpow.β + 1) := by
      funext x; simp [Pi.add_apply, hμSum_def]
    rw [heqf] at hsum
    exact hsum
  -- Field (4) `bΔm_grad`.
  have bΔm_grad_cert :
      Periodic.MemLpPer (d := d) γBar'E
        (fun x => (|(mLim + g₂) x| + |(mLim + g₁) x|)
            * ‖fun i => |DuLim i x| + |DuLim i x|‖ ^ (hpow.α - 1)) := by
    have hDυSum_vec :
        Periodic.MemLpPer (d := d) γBarE
          (fun x : (Fin d → ℝ) => fun j : Fin d => DυSum j x) :=
      palomar_BanachBridge_K0setDom_memLpPer_pi_of_coord (p := γBarE) DυSum hDυSum_γ
    set qE : ℝ≥0∞ := ENNReal.ofReal (hpow.α - 1) with hqE_def
    have hqE_toReal : qE.toReal = hpow.α - 1 := by
      rw [hqE_def]; exact ENNReal.toReal_ofReal hαm1_pos.le
    have hT1a :
        MeasureTheory.MemLp (fun x : (Fin d → ℝ) =>
                ‖(fun j : Fin d => DυSum j x)‖ ^ qE.toReal)
              (γBarE / qE)
              (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
      MeasureTheory.MemLp.norm_rpow_div hDυSum_vec.toMemLp qE
    have hdiv :
        γBarE / qE =
          ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β / (hpow.α - 1)) := by
      rw [hγBarE_def, hqE_def, hγBar_eq, ← ENNReal.ofReal_div_of_pos hαm1_pos]
    have heq :
        (fun x : (Fin d → ℝ) =>
          ‖(fun j : Fin d => DυSum j x)‖ ^ qE.toReal)
        = (fun x : (Fin d → ℝ) =>
          ‖fun j : Fin d => |DuLim j x| + |DuLim j x|‖ ^ (hpow.α - 1)) := by
      funext x; rw [hqE_toReal]
    rw [heq] at hT1a
    have hT1b :
        Periodic.MemLpPer (d := d)
          (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β / (hpow.α - 1)))
          (fun x : (Fin d → ℝ) =>
            ‖fun j : Fin d => |DuLim j x| + |DuLim j x|‖ ^ (hpow.α - 1)) := by
      have := MemLp.toMemLpPer hT1a
      rw [hdiv] at this
      exact this
    have hHT_real :
        Real.HolderTriple (hpow.β + 1)
          (hpow.α * (hpow.β + 1) / hpow.β / (hpow.α - 1))
          (hpow.α * (hpow.β + 1) / hpow.β /
              (hpow.α * (hpow.β + 1) / hpow.β - 1)) :=
      palomar_BanachBridge_K0setDom_holderTriple hpow.hα hpow.hβ
    haveI hHT_enn :
        ENNReal.HolderTriple (ENNReal.ofReal (hpow.β + 1))
          (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β / (hpow.α - 1)))
          (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β /
              (hpow.α * (hpow.β + 1) / hpow.β - 1))) :=
      hHT_real.ennrealOfReal
    have hT1c :
        MeasureTheory.MemLp
          (fun x : (Fin d → ℝ) =>
            μSum x * ‖fun j => |DuLim j x| + |DuLim j x|‖ ^ (hpow.α - 1))
          (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β /
              (hpow.α * (hpow.β + 1) / hpow.β - 1)))
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
      (hμSum_paperβ.toMemLp.fun_mul hT1b.toMemLp : _)
    have hres :
        Periodic.MemLpPer (d := d)
          (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β /
              (hpow.α * (hpow.β + 1) / hpow.β - 1)))
          (fun x : (Fin d → ℝ) =>
            (|(mLim + g₂) x| + |(mLim + g₁) x|) *
              ‖fun j => |DuLim j x| + |DuLim j x|‖ ^ (hpow.α - 1)) := by
      have := MemLp.toMemLpPer hT1c
      convert this using 1
    have hexp_eq : γBar'E =
        ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β /
            (hpow.α * (hpow.β + 1) / hpow.β - 1)) := by
      rw [hγBar'E_def, hγ'_paper_eq]
    rw [hexp_eq]; exact hres
  -- Field (5) `bΔm_endpoint`.
  have bΔm_endpoint_cert :
      Periodic.MemLpPer (d := d) γBar'E
        (fun x =>
          (|(mLim + g₂) x| + |(mLim + g₁) x|) ^
            (1 + hpow.β - hpow.β / hpow.α)) := by
    have hβα_pos : 0 < hpow.β / hpow.α := div_pos hβ_pos hα_pos
    have hβα_lt : hpow.β / hpow.α < hpow.β + 1 := by
      have h1 : hpow.β / hpow.α ≤ hpow.β := by
        rw [div_le_iff₀ hα_pos]
        nlinarith [hpow.hα, hβ_pos]
      linarith
    have hexp_pos : 0 < hpow.β + 1 - hpow.β / hpow.α := by linarith
    set qE : ℝ≥0∞ := ENNReal.ofReal (hpow.β + 1 - hpow.β / hpow.α) with hqE_def
    have hqE_toReal : qE.toReal = hpow.β + 1 - hpow.β / hpow.α := by
      rw [hqE_def]; exact ENNReal.toReal_ofReal hexp_pos.le
    have hT2a :
        MeasureTheory.MemLp (fun x : (Fin d → ℝ) => |μSum x| ^ qE.toReal)
              ((ENNReal.ofReal (hpow.β + 1)) / qE)
              (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
      have h1 := MeasureTheory.MemLp.norm_rpow_div hμSum_paperβ.toMemLp qE
      have heq :
          (fun x : (Fin d → ℝ) => ‖μSum x‖ ^ qE.toReal)
          = fun x : (Fin d → ℝ) => |μSum x| ^ qE.toReal := by
        funext x; rw [Real.norm_eq_abs]
      rw [heq] at h1
      exact h1
    have hβne : hpow.β ≠ 0 := hβ_pos.ne'
    have hαne : hpow.α ≠ 0 := hα_pos.ne'
    have hbb_ne : hpow.β + 1 ≠ 0 := hβ1_pos.ne'
    have hβbβα_ne : hpow.β + 1 - hpow.β / hpow.α ≠ 0 := hexp_pos.ne'
    have hgb_gt_one : 1 < hpow.α * (hpow.β + 1) / hpow.β := by
      rw [lt_div_iff₀ hβ_pos]; nlinarith [hpow.hα, hβ_pos]
    have hγb_ne : hpow.α * (hpow.β + 1) / hpow.β ≠ 0 := by
      have : 0 < hpow.α * (hpow.β + 1) / hpow.β :=
        div_pos (mul_pos hα_pos hβ1_pos) hβ_pos
      exact this.ne'
    have hγbm1_ne : hpow.α * (hpow.β + 1) / hpow.β - 1 ≠ 0 := by linarith
    have hdiv_eq :
        (ENNReal.ofReal (hpow.β + 1)) / qE = γBar'E := by
      rw [hqE_def, hγBar'E_def, hγBar'_eq, hγBar_eq,
        ← ENNReal.ofReal_div_of_pos hexp_pos]
      congr 1
      field_simp
    have heq :
        (fun x : (Fin d → ℝ) => |μSum x| ^ qE.toReal)
        = (fun x : (Fin d → ℝ) => |μSum x| ^ (hpow.β + 1 - hpow.β / hpow.α)) := by
      funext x; rw [hqE_toReal]
    rw [heq] at hT2a
    have hT2b :
        Periodic.MemLpPer (d := d) γBar'E
          (fun x : (Fin d → ℝ) => |μSum x| ^ (hpow.β + 1 - hpow.β / hpow.α)) := by
      have := MemLp.toMemLpPer hT2a
      rw [hdiv_eq] at this
      exact this
    have hsh : (1 : ℝ) + hpow.β - hpow.β / hpow.α
                  = hpow.β + 1 - hpow.β / hpow.α := by ring
    have hbound :
        ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
          ‖μSum x ^ (1 + hpow.β - hpow.β / hpow.α)‖ ≤
            (1 : ℝ) * ‖|μSum x| ^ (hpow.β + 1 - hpow.β / hpow.α)‖ := by
      refine Filter.Eventually.of_forall ?_
      intro x
      rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul, hsh]
      have habs := Real.abs_rpow_le_abs_rpow (μSum x) (hpow.β + 1 - hpow.β / hpow.α)
      have hrhs_nn : 0 ≤ |μSum x| ^ (hpow.β + 1 - hpow.β / hpow.α) :=
        Real.rpow_nonneg (abs_nonneg _) _
      rw [abs_of_nonneg hrhs_nn]
      exact habs
    have hmeas :
        MeasureTheory.AEStronglyMeasurable
          (fun x : (Fin d → ℝ) => μSum x ^ (1 + hpow.β - hpow.β / hpow.α))
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
      have h_exp_nn : (0 : ℝ) ≤ 1 + hpow.β - hpow.β / hpow.α := by linarith [hexp_pos]
      have hcont : Continuous (fun y : ℝ => y ^ (1 + hpow.β - hpow.β / hpow.α)) :=
        Real.continuous_rpow_const h_exp_nn
      exact hcont.comp_aestronglyMeasurable hμSum_β.aestronglyMeasurable
    have hT2c :
        Periodic.MemLpPer (d := d) γBar'E
          (fun x : (Fin d → ℝ) => μSum x ^ (1 + hpow.β - hpow.β / hpow.α)) :=
      MemLp.toMemLpPer
        (MeasureTheory.MemLp.of_le_mul hT2b.toMemLp hmeas hbound)
    convert hT2c using 1
  -- Field (6) `bΔm`.
  have bΔm_cert :
      Periodic.MemLpPer (d := d) γBar'E
        (fun x => |(mLim + g₂) x| + |(mLim + g₁) x|) := by
    have hT10 : Periodic.MemLpPer (d := d) γBar'E μSum :=
      Periodic.MemLpPer.mono_exponent_finite hγ'_le_β hβTop hμSum_β
    convert hT10 using 1
  -- Field (7) `bG_grad`.
  have bG_grad_cert :
      Periodic.MemLpPer (d := d) γBar'E
        (fun x =>
          (∑ i, (|DuLim i x| + |DuLim i x|) ^ (2 : ℕ))
              ^ ((γBar - 1) / 2)) := by
    set q2E : ℝ≥0∞ := (2 : ℝ≥0∞) with hq2E_def
    have hq2E_top : q2E ≠ ⊤ := by rw [hq2E_def]; decide
    have hq2E_toReal : q2E.toReal = 2 := by rw [hq2E_def]; rfl
    have hSq_each : ∀ i,
        MeasureTheory.MemLp
          (fun x : (Fin d → ℝ) => ‖DυSum i x‖ ^ q2E.toReal)
          (γBarE / q2E)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
      fun i => MeasureTheory.MemLp.norm_rpow_div (hDυSum_γ i).toMemLp q2E
    have hSq_each' : ∀ i,
        Periodic.MemLpPer (d := d) (γBarE / q2E)
          (fun x : (Fin d → ℝ) => (DυSum i x) ^ (2 : ℕ)) := by
      intro i
      have h := hSq_each i
      have heq :
          (fun x : (Fin d → ℝ) => ‖DυSum i x‖ ^ q2E.toReal)
          = (fun x : (Fin d → ℝ) => (DυSum i x) ^ (2 : ℕ)) := by
        funext x
        rw [hq2E_toReal, Real.norm_eq_abs]
        rw [show ((2 : ℝ) = ((2 : ℕ) : ℝ)) from by norm_num,
            Real.rpow_natCast, sq_abs]
      rw [heq] at h
      exact MemLp.toMemLpPer h
    have hSumSq :
        Periodic.MemLpPer (d := d) (γBarE / q2E)
          (fun x : (Fin d → ℝ) => ∑ i, (DυSum i x) ^ (2 : ℕ)) := by
      have hsum : MeasureTheory.MemLp
          (fun x : (Fin d → ℝ) => ∑ i : Fin d, (fun x => (DυSum i x) ^ (2 : ℕ)) x)
          (γBarE / q2E)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
        refine MeasureTheory.memLp_finset_sum (Finset.univ : Finset (Fin d)) ?_
        intro i _; exact (hSq_each' i).toMemLp
      exact MemLp.toMemLpPer hsum
    have hγm1_pos : 0 < γBarReal - 1 := by linarith
    have hexp12_pos : 0 < (γBarReal - 1) / 2 := by linarith
    set qE : ℝ≥0∞ := ENNReal.ofReal ((γBarReal - 1) / 2) with hqE_def
    have hqE_toReal : qE.toReal = (γBarReal - 1) / 2 := by
      rw [hqE_def]; exact ENNReal.toReal_ofReal hexp12_pos.le
    have hRpow : MeasureTheory.MemLp
        (fun x : (Fin d → ℝ) =>
          ‖∑ i, (DυSum i x) ^ (2 : ℕ)‖ ^ qE.toReal)
        ((γBarE / q2E) / qE)
        (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
      MeasureTheory.MemLp.norm_rpow_div hSumSq.toMemLp qE
    have hdiv_eq : (γBarE / q2E) / qE = γBar'E := by
      rw [hq2E_def, hqE_def, hγBarE_def, hγBar'E_def, hγBar'_eq,
          ← ENNReal.ofReal_ofNat (n := 2),
          ← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
          ← ENNReal.ofReal_div_of_pos hexp12_pos]
      congr 1
      have hγne : γBarReal ≠ 0 := hγBarReal_pos.ne'
      have hγm1ne : γBarReal - 1 ≠ 0 := hγm1_pos.ne'
      field_simp
    have hSumSq_nn : ∀ x, 0 ≤ ∑ i, (DυSum i x) ^ (2 : ℕ) :=
      fun x => Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have heqfn :
        (fun x : (Fin d → ℝ) =>
          ‖∑ i, (DυSum i x) ^ (2 : ℕ)‖ ^ qE.toReal)
        = (fun x : (Fin d → ℝ) =>
            (∑ i, (DυSum i x) ^ (2 : ℕ)) ^ ((γBarReal - 1) / 2)) := by
      funext x
      rw [hqE_toReal, Real.norm_eq_abs, abs_of_nonneg (hSumSq_nn x)]
    rw [heqfn] at hRpow
    have hres :
        Periodic.MemLpPer (d := d) γBar'E
          (fun x : (Fin d → ℝ) =>
            (∑ i, (DυSum i x) ^ (2 : ℕ)) ^ ((γBarReal - 1) / 2)) := by
      have := MemLp.toMemLpPer hRpow
      rw [hdiv_eq] at this
      exact this
    rw [hγBar_id]
    convert hres using 1
  -- Field (8) `bG_val`.
  have bG_val_cert :
      Periodic.MemLpPer (d := d) γBar'E
        (fun x => (|uLim x| + |uLim x|) ^ (γBar - 1)) := by
    have hγm1_pos : 0 < γBarReal - 1 := by linarith
    set qE : ℝ≥0∞ := ENNReal.ofReal (γBarReal - 1) with hqE_def
    have hqE_toReal : qE.toReal = γBarReal - 1 := by
      rw [hqE_def]; exact ENNReal.toReal_ofReal hγm1_pos.le
    have hRpow : MeasureTheory.MemLp
        (fun x : (Fin d → ℝ) => ‖υSum x‖ ^ qE.toReal)
        (γBarE / qE)
        (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
      MeasureTheory.MemLp.norm_rpow_div hυSum_γ.toMemLp qE
    have hdiv : γBarE / qE = γBar'E := by
      rw [hqE_def, hγBarE_def, hγBar'E_def, hγBar'_eq,
        ← ENNReal.ofReal_div_of_pos hγm1_pos]
    have hυSum_nn : ∀ x, 0 ≤ υSum x := fun x => by
      rw [hυSum_def]; exact add_nonneg (abs_nonneg _) (abs_nonneg _)
    have heq :
        (fun x : (Fin d → ℝ) => ‖υSum x‖ ^ qE.toReal)
        = (fun x : (Fin d → ℝ) => υSum x ^ (γBarReal - 1)) := by
      funext x
      rw [hqE_toReal, Real.norm_eq_abs, abs_of_nonneg (hυSum_nn x)]
    rw [heq] at hRpow
    have hres : Periodic.MemLpPer (d := d) γBar'E
        (fun x : (Fin d → ℝ) => υSum x ^ (γBarReal - 1)) := by
      have := MemLp.toMemLpPer hRpow
      rw [hdiv] at this
      exact this
    rw [hγBar_id]
    convert hres using 1
  -- Bundle the eight derived certs.
  exact
    { bΔυ := bΔυ_cert
      bΔp_pow := bΔp_pow_cert
      bΔm_pow := bΔm_pow_cert
      bΔm_grad := bΔm_grad_cert
      bΔm_endpoint := bΔm_endpoint_cert
      bΔm := bΔm_cert
      bG_grad := bG_grad_cert
      bG_val := bG_val_cert }

/-- **Sanity-check `example` for the minimal-shape K0 signed producer.** At
`g₁ = g₂ = 0` and at the paper exponent identities, the producer derives all
eight `MemLpPer`-of-power dominator certificates at the shapes consumed by
the K0 minimal-shape signed composer. Crucially, the caller does **not**
supply `hβ_ge_one`. -/
example
    {d : ℕ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    [Fact (1 ≤ ENNReal.ofReal (hpow.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))]
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    (hβconj :
      Real.HolderConjugate ((hpow.β + 1) / hpow.β) (hpow.β + 1))
    (hγconj :
      Real.HolderConjugate
        (hpow.α * (hpow.β + 1) / hpow.β /
          (hpow.α * (hpow.β + 1) / hpow.β - 1))
        (hpow.α * (hpow.β + 1) / hpow.β))
    {mLim uLim : (Fin d → ℝ) → ℝ}
    {DuLim : Fin d → (Fin d → ℝ) → ℝ}
    (hmLim_memLp : Periodic.MemLpPer (d := d)
                      (ENNReal.ofReal (hpow.β + 1)) mLim)
    (huLim_sob : Periodic.MemSobolevPer (d := d)
                      (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))
                      uLim)
    (hDuLim_memLp_γ : ∀ i, Periodic.MemLpPer (d := d)
                              (ENNReal.ofReal
                                (hpow.α * (hpow.β + 1) / hpow.β))
                              (DuLim i))
    (aeNN : ∀ᵐ x ∂(MeasureTheory.Measure.restrict
                      MeasureTheory.volume (UnitCube (d := d))),
        0 ≤ mLim x) :
    SignedFamilyNarrowDominatorsK0Min
      (βBarReal' := (hpow.β + 1) / hpow.β)
      (γBarReal' := (hpow.α * (hpow.β + 1) / hpow.β) /
                     (hpow.α * (hpow.β + 1) / hpow.β - 1))
      (γBar := hpow.α * (hpow.β + 1) / hpow.β)
      mLim uLim DuLim
      (fun _ : Fin d → ℝ => (0 : ℝ)) (fun _ : Fin d → ℝ => (0 : ℝ))
      hpow.α hpow.β := by
  -- `mLim + 0 = mLim` as a function.
  have hmg_β :
      Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1))
        (mLim + fun _ : Fin d → ℝ => (0 : ℝ)) := by
    have heq : (mLim + fun _ : Fin d → ℝ => (0 : ℝ)) = mLim := by
      funext x; simp [Pi.add_apply]
    rw [heq]; exact hmLim_memLp
  have hmg_nn :
      ∀ᵐ x ∂(MeasureTheory.Measure.restrict
                MeasureTheory.volume (UnitCube (d := d))),
        0 ≤ (mLim + fun _ : Fin d → ℝ => (0 : ℝ)) x := by
    refine aeNN.mono ?_
    intro x hx
    simpa [Pi.add_apply] using hx
  exact
    signedFamilyNarrowDominatorsK0Min_of_paperHypotheses
      (d := d)
      (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
      (βBarReal := hpow.β + 1)
      (βBarReal' := (hpow.β + 1) / hpow.β)
      (γBarReal' := (hpow.α * (hpow.β + 1) / hpow.β) /
                     (hpow.α * (hpow.β + 1) / hpow.β - 1))
      (γBar := hpow.α * (hpow.β + 1) / hpow.β)
      (H := H) (DpH := DpH)
      hpow hHat0 hAgree hβconj hγconj
      rfl rfl rfl rfl rfl
      hmLim_memLp huLim_sob hDuLim_memLp_γ
      hmg_β hmg_β hmg_nn hmg_nn

/-! ### Transport mirror of iter-0767 K0 set dominators producer

`infra-P5-T10-v8-K0-transport-dominators-producer` — transport mirror of the
iter-0767 set-family / iter-0773 signed-family K0 dominators producer. Same
nine `MemLpPer`-of-power dominator certificates, packaged at the
**unshifted transport** endpoints: both density-sides collapse to `mLim`,
and the `u`/`Du`-sides carry the smooth test directions
`(uLim + ψ_i, DuLim_i + ∂_i ψ_i)`. Derived inline from paper hypotheses
(no packaging-shell anti-pattern; the iter-0767 anti-pattern-free template).

**Transport vs. set/signed input shape.** The transport family leaves the
primal density fixed at `mLim`, so the perturbation channel goes through
the `u`/`Du`-sides instead: smooth periodic test directions `ψ₁ ψ₂` enter
via `(uLim + ψ_i)` and `(DuLim_i + ∂_i ψ_i)`. Both sums sit in
`MemLpPer γBarE` via `Periodic.MemSobolevPer.of_smoothPeriodic`. The
density-side `μSum` collapses to `|mLim| + |mLim|` (no perturbation), so
all nine derivations reuse the iter-0767 toolkit verbatim. -/

/-- **`TransportFamilyNarrowDominatorsK0Min` bundle.**

Minimal-shape sibling of `TransportFamilyNarrowDominatorsK0`: same eight
dominator certificates `(bΔυ, bΔp_pow, bΔm_pow, bΔm_grad, bΔm_endpoint, bΔm,
bG_grad, bG_val)`, dropping the over-specified
`bΔm1 : MemLpPer βBar' (μSum + 1)` field. The dropped field was the only
field of the iter-0779 transport bundle that forced the non-paper-faithful
side condition `1 ≤ hpow.β` on the producer. Density-side endpoints stay
collapsed to `mLim` (transport convention); `u`/`Du`-sides carry smooth
perturbations `ψ₁ ψ₂`. -/
structure TransportFamilyNarrowDominatorsK0Min
    {d : ℕ} {βBarReal' γBarReal' γBar : ℝ}
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    (ψ₁ ψ₂ : Periodic.SmoothPeriodic d)
    (α β : ℝ) : Type where
  /-- Dominator cert: `|uLim + ψ₂| + |uLim + ψ₁| ∈ Lᵝ'`. -/
  bΔυ : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal')
            (fun x => |(uLim + (ψ₂ : (Fin d → ℝ) → ℝ)) x|
                        + |(uLim + (ψ₁ : (Fin d → ℝ) → ℝ)) x|)
  /-- Dominator cert for the gradient `α`-power. -/
  bΔp_pow : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal')
            (fun x =>
              ‖fun i =>
                  |(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₂
                                : (Fin d → ℝ) → ℝ)) x|
                + |(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₁
                                : (Fin d → ℝ) → ℝ)) x|‖ ^ α + 1)
  /-- Dominator cert for the density `β`-power (transport: collapsed to `mLim`). -/
  bΔm_pow : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal')
            (fun x => (|mLim x| + |mLim x|) ^ β + 1)
  /-- Dominator cert for the gradient cross-term. -/
  bΔm_grad : Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
            (fun x => (|mLim x| + |mLim x|)
                * ‖fun i =>
                    |(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₂
                                  : (Fin d → ℝ) → ℝ)) x|
                  + |(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₁
                                  : (Fin d → ℝ) → ℝ)) x|‖ ^ (α - 1))
  /-- Dominator cert for the endpoint exponent `1 + β - β/α`. -/
  bΔm_endpoint : Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
            (fun x => (|mLim x| + |mLim x|) ^ (1 + β - β / α))
  /-- Dominator cert for the bare density. -/
  bΔm : Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
            (fun x => |mLim x| + |mLim x|)
  /-- Dominator cert for the Gateaux gradient block. -/
  bG_grad : Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
            (fun x =>
              (∑ i,
                  (|(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₂
                                  : (Fin d → ℝ) → ℝ)) x|
                    + |(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₁
                                  : (Fin d → ℝ) → ℝ)) x|) ^ (2 : ℕ))
                  ^ ((γBar - 1) / 2))
  /-- Dominator cert for the Gateaux value block. -/
  bG_val : Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
            (fun x => (|(uLim + (ψ₂ : (Fin d → ℝ) → ℝ)) x|
                        + |(uLim + (ψ₁ : (Fin d → ℝ) → ℝ)) x|)
                        ^ (γBar - 1))

/-- **Closed paper-faithful producer for the `TransportFamilyNarrowDominatorsK0Min`
bundle** (`infra-P6-K0-min-dominators-transport`, audit 2026-05-22).

Transport sibling of `setFamilyNarrowDominatorsK0Min_of_paperHypotheses` /
`signedFamilyNarrowDominatorsK0Min_of_paperHypotheses` and minimal-shape
sibling of `transportFamilyNarrowDominatorsK0_of_paperHypotheses`
(iter-0779): identical to the latter except that

* the over-specified `bΔm1 : MemLpPer βBar' (μSum + 1)` slot is dropped, and
* with it, the non-paper-faithful side condition `1 ≤ hpow.β` disappears
  from the signature.

The remaining eight dominator certificates are derived inline from the
paper hypotheses (`hpow`, `hmLim_memLp`, `huLim_sob`, `hDuLim_memLp_γ`)
by the same routes (`MemLp.norm_rpow_div`, Hölder triple, sum closure,
`mono_exponent_finite`). The producer does not accept any of the eight
as inputs — anti-pattern-free per the iter-0767 reviewer directive.
Transport input shape: smooth test directions `ψ₁ ψ₂ : SmoothPeriodic d`
enter through the `u`/`Du`-sides, density-side collapses (both endpoints
equal `mLim`). -/
noncomputable def transportFamilyNarrowDominatorsK0Min_of_paperHypotheses
    {d : ℕ} {γBarReal βBarReal βBarReal' γBarReal' γBar : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (_hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (_hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    (_hβconj : βBarReal'.HolderConjugate βBarReal)
    (_hγconj : γBarReal'.HolderConjugate γBarReal)
    (hβBar_eq : βBarReal = hpow.β + 1)
    (hγBar_eq : γBarReal = hpow.α * (hpow.β + 1) / hpow.β)
    (hβBar'_eq : βBarReal' = (hpow.β + 1) / hpow.β)
    (hγBar'_eq : γBarReal' = γBarReal / (γBarReal - 1))
    (hγBar_id : γBar = γBarReal)
    {mLim uLim : (Fin d → ℝ) → ℝ}
    {DuLim : Fin d → (Fin d → ℝ) → ℝ}
    (hmLim_memLp : Periodic.MemLpPer (d := d)
                      (ENNReal.ofReal βBarReal) mLim)
    (huLim_sob : Periodic.MemSobolevPer (d := d)
                      (ENNReal.ofReal γBarReal) uLim)
    (hDuLim_memLp_γ : ∀ i, Periodic.MemLpPer (d := d)
                              (ENNReal.ofReal γBarReal) (DuLim i))
    (ψ₁ ψ₂ : Periodic.SmoothPeriodic d) :
    TransportFamilyNarrowDominatorsK0Min
      (βBarReal' := βBarReal') (γBarReal' := γBarReal') (γBar := γBar)
      mLim uLim DuLim ψ₁ ψ₂ hpow.α hpow.β := by
  -- Standing positivity facts (paper exponents).
  have hα_pos : 0 < hpow.α := lt_trans Real.zero_lt_one hpow.hα
  have hβ_pos : 0 < hpow.β := hpow.hβ
  have hβ1_pos : 0 < hpow.β + 1 := by linarith
  have hαm1_pos : 0 < hpow.α - 1 := by linarith [hpow.hα]
  have hβBarReal_pos : 0 < βBarReal := by rw [hβBar_eq]; exact hβ1_pos
  have hγBarReal_pos : 0 < γBarReal := by
    rw [hγBar_eq]
    exact div_pos (mul_pos hα_pos hβ1_pos) hβ_pos
  have hγBar_one_lt_real : 1 < γBarReal := by
    rw [hγBar_eq]; rw [lt_div_iff₀ hβ_pos, one_mul]
    have : (hpow.β + 1) < hpow.α * (hpow.β + 1) := by
      have : (1 : ℝ) * (hpow.β + 1) < hpow.α * (hpow.β + 1) :=
        mul_lt_mul_of_pos_right hpow.hα hβ1_pos
      simpa using this
    linarith
  have hβBarReal'_pos : 0 < βBarReal' := by
    rw [hβBar'_eq]; exact div_pos hβ1_pos hβ_pos
  have hγBarReal'_pos : 0 < γBarReal' := by
    rw [hγBar'_eq]; exact div_pos hγBarReal_pos (by linarith)
  -- Finite-measure instance on the unit cube.
  haveI : MeasureTheory.IsFiniteMeasure
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube (d := d))) :=
    ⟨by
      rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ]
      simp⟩
  -- Notation for the ENNReal exponents.
  set βBarE : ℝ≥0∞ := ENNReal.ofReal βBarReal with hβBarE_def
  set γBarE : ℝ≥0∞ := ENNReal.ofReal γBarReal with hγBarE_def
  set βBar'E : ℝ≥0∞ := ENNReal.ofReal βBarReal' with hβBar'E_def
  set γBar'E : ℝ≥0∞ := ENNReal.ofReal γBarReal' with hγBar'E_def
  -- `MemLpPer` cert for `uLim` at `γBarE` (project from Sobolev).
  have huLim_γ : Periodic.MemLpPer (d := d) γBarE uLim := huLim_sob.1
  -- Project the smooth test directions to `MemLpPer γBarE`.
  have hψ₁_γ : Periodic.MemLpPer (d := d) γBarE
                  ((ψ₁ : (Fin d → ℝ) → ℝ)) :=
    (Periodic.MemSobolevPer.of_smoothPeriodic γBarE ψ₁).1
  have hψ₂_γ : Periodic.MemLpPer (d := d) γBarE
                  ((ψ₂ : (Fin d → ℝ) → ℝ)) :=
    (Periodic.MemSobolevPer.of_smoothPeriodic γBarE ψ₂).1
  -- Build the `u`-side endpoints `(uLim + ψ_i) ∈ MemLpPer γBarE`.
  have huψ₁_γ : Periodic.MemLpPer (d := d) γBarE
                  (uLim + (ψ₁ : (Fin d → ℝ) → ℝ)) :=
    huLim_γ.add hψ₁_γ
  have huψ₂_γ : Periodic.MemLpPer (d := d) γBarE
                  (uLim + (ψ₂ : (Fin d → ℝ) → ℝ)) :=
    huLim_γ.add hψ₂_γ
  -- Project the partial derivatives `∂_i ψ_j` to `MemLpPer γBarE`.
  have hDψ₁_γ : ∀ i, Periodic.MemLpPer (d := d) γBarE
                        ((Periodic.SmoothPeriodic.partialDeriv i ψ₁
                            : (Fin d → ℝ) → ℝ)) :=
    fun i => (Periodic.MemSobolevPer.of_smoothPeriodic γBarE
                  (Periodic.SmoothPeriodic.partialDeriv i ψ₁)).1
  have hDψ₂_γ : ∀ i, Periodic.MemLpPer (d := d) γBarE
                        ((Periodic.SmoothPeriodic.partialDeriv i ψ₂
                            : (Fin d → ℝ) → ℝ)) :=
    fun i => (Periodic.MemSobolevPer.of_smoothPeriodic γBarE
                  (Periodic.SmoothPeriodic.partialDeriv i ψ₂)).1
  -- Build the `Du`-side endpoints `(DuLim i + ∂_i ψ_j) ∈ MemLpPer γBarE`.
  have hDuψ₁_γ : ∀ i, Periodic.MemLpPer (d := d) γBarE
                        (DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₁
                                      : (Fin d → ℝ) → ℝ)) :=
    fun i => (hDuLim_memLp_γ i).add (hDψ₁_γ i)
  have hDuψ₂_γ : ∀ i, Periodic.MemLpPer (d := d) γBarE
                        (DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₂
                                      : (Fin d → ℝ) → ℝ)) :=
    fun i => (hDuLim_memLp_γ i).add (hDψ₂_γ i)
  -- Auxiliary summed-abs functions. Transport collapse: `μSum = |mLim|+|mLim|`.
  set μSum : (Fin d → ℝ) → ℝ :=
    fun x => |mLim x| + |mLim x| with hμSum_def
  set υSum : (Fin d → ℝ) → ℝ :=
    fun x => |(uLim + (ψ₂ : (Fin d → ℝ) → ℝ)) x|
              + |(uLim + (ψ₁ : (Fin d → ℝ) → ℝ)) x| with hυSum_def
  set DυSum : Fin d → (Fin d → ℝ) → ℝ :=
    fun i x => |(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₂
                              : (Fin d → ℝ) → ℝ)) x|
              + |(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₁
                              : (Fin d → ℝ) → ℝ)) x| with hDυSum_def
  -- `μSum ∈ MemLpPer βBarE` (transport: both `m`-endpoints are `mLim`).
  have hμSum_β : Periodic.MemLpPer (d := d) βBarE μSum :=
    palomar_BanachBridge_K0setDom_memLpPer_abs_add_abs hmLim_memLp hmLim_memLp
  -- `υSum ∈ MemLpPer γBarE`.
  have hυSum_γ : Periodic.MemLpPer (d := d) γBarE υSum :=
    palomar_BanachBridge_K0setDom_memLpPer_abs_add_abs huψ₂_γ huψ₁_γ
  -- `DυSum i ∈ MemLpPer γBarE` for each `i`.
  have hDυSum_γ : ∀ i, Periodic.MemLpPer (d := d) γBarE (DυSum i) :=
    fun i => palomar_BanachBridge_K0setDom_memLpPer_abs_add_abs (hDuψ₂_γ i) (hDuψ₁_γ i)
  -- Restate `μSum` at the paper exponent `β + 1`.
  have hμSum_paperβ :
      Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1)) μSum := by
    rw [← hβBar_eq]; exact hμSum_β
  -- Constants 1 helper at `βBar'E`.
  have hone_β' : Periodic.MemLpPer (d := d) βBar'E (fun _ : (Fin d → ℝ) => (1 : ℝ)) :=
    MemLp.toMemLpPer (MeasureTheory.memLp_const (1 : ℝ))
  -- Paper-faithful standing fact: `βBarReal' ≤ γBarReal`.
  have hβ'_le_γ_real : βBarReal' ≤ γBarReal := by
    rw [hβBar'_eq, hγBar_eq]
    have h := Hamiltonian.betaBar'_le_gammaBar (hpow.hα.le) hβ_pos
    simp only [Hamiltonian.betaBar', Hamiltonian.gammaBar] at h
    exact h
  have hβ'_le_γ : βBar'E ≤ γBarE := by
    rw [hβBar'E_def, hγBarE_def]
    exact ENNReal.ofReal_le_ofReal hβ'_le_γ_real
  have hγTop : γBarE ≠ ⊤ := by rw [hγBarE_def]; exact ENNReal.ofReal_ne_top
  -- Paper-faithful standing fact: `γBarReal' ≤ βBarReal`.
  have hγ'_le_β_real : γBarReal' ≤ βBarReal := by
    rw [hγBar'_eq, hγBar_eq, hβBar_eq]
    have h := Hamiltonian.gammaBar'_le_betaBar hpow.hα hβ_pos
    exact h
  have hγ'_le_β : γBar'E ≤ βBarE := by
    rw [hγBar'E_def, hβBarE_def]
    exact ENNReal.ofReal_le_ofReal hγ'_le_β_real
  have hβTop : βBarE ≠ ⊤ := by rw [hβBarE_def]; exact ENNReal.ofReal_ne_top
  -- Derived paper-exponent identity for γBar'.
  have hγ'_paper_eq : γBarReal' =
      hpow.α * (hpow.β + 1) / hpow.β /
        (hpow.α * (hpow.β + 1) / hpow.β - 1) := by
    rw [hγBar'_eq, hγBar_eq]
  -- Field (1) `bΔυ`: `υSum ∈ Lᵝ'` via mono_exponent.
  have bΔυ_cert :
      Periodic.MemLpPer (d := d) βBar'E
        (fun x => |(uLim + (ψ₂ : (Fin d → ℝ) → ℝ)) x|
                    + |(uLim + (ψ₁ : (Fin d → ℝ) → ℝ)) x|) := by
    have hυSum_β' : Periodic.MemLpPer (d := d) βBar'E υSum :=
      Periodic.MemLpPer.mono_exponent_finite hβ'_le_γ hγTop hυSum_γ
    convert hυSum_β' using 1
  -- Field (2) `bΔp_pow`.
  have bΔp_pow_cert :
      Periodic.MemLpPer (d := d) βBar'E
        (fun x =>
          ‖fun i =>
              |(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₂
                            : (Fin d → ℝ) → ℝ)) x|
            + |(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₁
                            : (Fin d → ℝ) → ℝ)) x|‖ ^ hpow.α + 1) := by
    have hDυSum_vec :
        Periodic.MemLpPer (d := d) γBarE
          (fun x : (Fin d → ℝ) => fun j : Fin d => DυSum j x) :=
      palomar_BanachBridge_K0setDom_memLpPer_pi_of_coord (p := γBarE) DυSum hDυSum_γ
    set qE : ℝ≥0∞ := ENNReal.ofReal hpow.α with hqE_def
    have hqE_toReal : qE.toReal = hpow.α := by
      rw [hqE_def]; exact ENNReal.toReal_ofReal hα_pos.le
    have hT_a :
        MeasureTheory.MemLp (fun x : (Fin d → ℝ) =>
                ‖(fun j : Fin d => DυSum j x)‖ ^ qE.toReal)
              (γBarE / qE)
              (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
      MeasureTheory.MemLp.norm_rpow_div hDυSum_vec.toMemLp qE
    have hdiv : γBarE / qE = βBar'E := by
      rw [hγBarE_def, hqE_def, hβBar'E_def, hγBar_eq, hβBar'_eq,
          ← ENNReal.ofReal_div_of_pos hα_pos]
      congr 1
      field_simp
    have heq :
        (fun x : (Fin d → ℝ) =>
          ‖(fun j : Fin d => DυSum j x)‖ ^ qE.toReal)
        = (fun x : (Fin d → ℝ) =>
          ‖(fun j : Fin d => DυSum j x)‖ ^ hpow.α) := by
      funext x; rw [hqE_toReal]
    rw [heq] at hT_a
    have hT_b :
        Periodic.MemLpPer (d := d) βBar'E
          (fun x : (Fin d → ℝ) =>
            ‖fun j => |(DuLim j + (Periodic.SmoothPeriodic.partialDeriv j ψ₂
                                    : (Fin d → ℝ) → ℝ)) x|
                    + |(DuLim j + (Periodic.SmoothPeriodic.partialDeriv j ψ₁
                                    : (Fin d → ℝ) → ℝ)) x|‖ ^ hpow.α) := by
      have := MemLp.toMemLpPer hT_a
      rw [hdiv] at this
      exact this
    have hsum := hT_b.add hone_β'
    have heqf :
        ((fun x : (Fin d → ℝ) =>
          ‖fun j => |(DuLim j + (Periodic.SmoothPeriodic.partialDeriv j ψ₂
                                  : (Fin d → ℝ) → ℝ)) x|
                  + |(DuLim j + (Periodic.SmoothPeriodic.partialDeriv j ψ₁
                                  : (Fin d → ℝ) → ℝ)) x|‖ ^ hpow.α)
          + (fun _ : (Fin d → ℝ) => (1 : ℝ)))
        = (fun x : (Fin d → ℝ) =>
          ‖fun j => |(DuLim j + (Periodic.SmoothPeriodic.partialDeriv j ψ₂
                                  : (Fin d → ℝ) → ℝ)) x|
                  + |(DuLim j + (Periodic.SmoothPeriodic.partialDeriv j ψ₁
                                  : (Fin d → ℝ) → ℝ)) x|‖ ^ hpow.α + 1) := by
      funext x; simp [Pi.add_apply]
    rw [heqf] at hsum
    exact hsum
  -- Field (3) `bΔm_pow` (transport: μSum collapses to `|mLim| + |mLim|`).
  have bΔm_pow_cert :
      Periodic.MemLpPer (d := d) βBar'E
        (fun x => (|mLim x| + |mLim x|) ^ hpow.β + 1) := by
    set qE : ℝ≥0∞ := ENNReal.ofReal hpow.β with hqE_def
    have hqE_toReal : qE.toReal = hpow.β := by
      rw [hqE_def]; exact ENNReal.toReal_ofReal hβ_pos.le
    have hT_a :
        MeasureTheory.MemLp (fun x : (Fin d → ℝ) => |μSum x| ^ qE.toReal)
              (βBarE / qE)
              (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
      have h1 := MeasureTheory.MemLp.norm_rpow_div hμSum_β.toMemLp qE
      have heq :
          (fun x : (Fin d → ℝ) => ‖μSum x‖ ^ qE.toReal)
          = fun x : (Fin d → ℝ) => |μSum x| ^ qE.toReal := by
        funext x; rw [Real.norm_eq_abs]
      rw [heq] at h1
      exact h1
    have hdiv : βBarE / qE = βBar'E := by
      rw [hβBarE_def, hqE_def, hβBar'E_def, hβBar_eq, hβBar'_eq,
        ← ENNReal.ofReal_div_of_pos hβ_pos]
    have heq :
        (fun x : (Fin d → ℝ) => |μSum x| ^ qE.toReal)
        = (fun x : (Fin d → ℝ) => |μSum x| ^ hpow.β) := by
      funext x; rw [hqE_toReal]
    rw [heq] at hT_a
    have hT_b : Periodic.MemLpPer (d := d) βBar'E
        (fun x : (Fin d → ℝ) => |μSum x| ^ hpow.β) := by
      have := MemLp.toMemLpPer hT_a
      rw [hdiv] at this
      exact this
    have hμSum_nn : ∀ x, 0 ≤ μSum x := fun x => by
      rw [hμSum_def]; exact add_nonneg (abs_nonneg _) (abs_nonneg _)
    have hT_c : Periodic.MemLpPer (d := d) βBar'E
        (fun x : (Fin d → ℝ) => μSum x ^ hpow.β) := by
      have heq : (fun x : (Fin d → ℝ) => μSum x ^ hpow.β)
                = (fun x : (Fin d → ℝ) => |μSum x| ^ hpow.β) := by
        funext x; rw [abs_of_nonneg (hμSum_nn x)]
      rw [heq]; exact hT_b
    have hsum := hT_c.add hone_β'
    have heqf :
        ((fun x : (Fin d → ℝ) => μSum x ^ hpow.β)
          + (fun _ : (Fin d → ℝ) => (1 : ℝ)))
        = (fun x : (Fin d → ℝ) =>
            (|mLim x| + |mLim x|) ^ hpow.β + 1) := by
      funext x; simp [Pi.add_apply, hμSum_def]
    rw [heqf] at hsum
    exact hsum
  -- Field (4) `bΔm_grad`.
  have bΔm_grad_cert :
      Periodic.MemLpPer (d := d) γBar'E
        (fun x => (|mLim x| + |mLim x|)
            * ‖fun i =>
                |(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₂
                              : (Fin d → ℝ) → ℝ)) x|
              + |(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₁
                              : (Fin d → ℝ) → ℝ)) x|‖ ^ (hpow.α - 1)) := by
    have hDυSum_vec :
        Periodic.MemLpPer (d := d) γBarE
          (fun x : (Fin d → ℝ) => fun j : Fin d => DυSum j x) :=
      palomar_BanachBridge_K0setDom_memLpPer_pi_of_coord (p := γBarE) DυSum hDυSum_γ
    set qE : ℝ≥0∞ := ENNReal.ofReal (hpow.α - 1) with hqE_def
    have hqE_toReal : qE.toReal = hpow.α - 1 := by
      rw [hqE_def]; exact ENNReal.toReal_ofReal hαm1_pos.le
    have hT1a :
        MeasureTheory.MemLp (fun x : (Fin d → ℝ) =>
                ‖(fun j : Fin d => DυSum j x)‖ ^ qE.toReal)
              (γBarE / qE)
              (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
      MeasureTheory.MemLp.norm_rpow_div hDυSum_vec.toMemLp qE
    have hdiv :
        γBarE / qE =
          ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β / (hpow.α - 1)) := by
      rw [hγBarE_def, hqE_def, hγBar_eq, ← ENNReal.ofReal_div_of_pos hαm1_pos]
    have heq :
        (fun x : (Fin d → ℝ) =>
          ‖(fun j : Fin d => DυSum j x)‖ ^ qE.toReal)
        = (fun x : (Fin d → ℝ) =>
          ‖fun j : Fin d =>
              |(DuLim j + (Periodic.SmoothPeriodic.partialDeriv j ψ₂
                            : (Fin d → ℝ) → ℝ)) x|
            + |(DuLim j + (Periodic.SmoothPeriodic.partialDeriv j ψ₁
                            : (Fin d → ℝ) → ℝ)) x|‖ ^ (hpow.α - 1)) := by
      funext x; rw [hqE_toReal]
    rw [heq] at hT1a
    have hT1b :
        Periodic.MemLpPer (d := d)
          (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β / (hpow.α - 1)))
          (fun x : (Fin d → ℝ) =>
            ‖fun j : Fin d =>
                |(DuLim j + (Periodic.SmoothPeriodic.partialDeriv j ψ₂
                              : (Fin d → ℝ) → ℝ)) x|
              + |(DuLim j + (Periodic.SmoothPeriodic.partialDeriv j ψ₁
                              : (Fin d → ℝ) → ℝ)) x|‖ ^ (hpow.α - 1)) := by
      have := MemLp.toMemLpPer hT1a
      rw [hdiv] at this
      exact this
    have hHT_real :
        Real.HolderTriple (hpow.β + 1)
          (hpow.α * (hpow.β + 1) / hpow.β / (hpow.α - 1))
          (hpow.α * (hpow.β + 1) / hpow.β /
              (hpow.α * (hpow.β + 1) / hpow.β - 1)) :=
      palomar_BanachBridge_K0setDom_holderTriple hpow.hα hpow.hβ
    haveI hHT_enn :
        ENNReal.HolderTriple (ENNReal.ofReal (hpow.β + 1))
          (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β / (hpow.α - 1)))
          (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β /
              (hpow.α * (hpow.β + 1) / hpow.β - 1))) :=
      hHT_real.ennrealOfReal
    have hT1c :
        MeasureTheory.MemLp
          (fun x : (Fin d → ℝ) =>
            μSum x * ‖fun j =>
                |(DuLim j + (Periodic.SmoothPeriodic.partialDeriv j ψ₂
                              : (Fin d → ℝ) → ℝ)) x|
              + |(DuLim j + (Periodic.SmoothPeriodic.partialDeriv j ψ₁
                              : (Fin d → ℝ) → ℝ)) x|‖ ^ (hpow.α - 1))
          (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β /
              (hpow.α * (hpow.β + 1) / hpow.β - 1)))
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
      (hμSum_paperβ.toMemLp.fun_mul hT1b.toMemLp : _)
    have hres :
        Periodic.MemLpPer (d := d)
          (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β /
              (hpow.α * (hpow.β + 1) / hpow.β - 1)))
          (fun x : (Fin d → ℝ) =>
            (|mLim x| + |mLim x|) *
              ‖fun j =>
                  |(DuLim j + (Periodic.SmoothPeriodic.partialDeriv j ψ₂
                                : (Fin d → ℝ) → ℝ)) x|
                + |(DuLim j + (Periodic.SmoothPeriodic.partialDeriv j ψ₁
                                : (Fin d → ℝ) → ℝ)) x|‖ ^ (hpow.α - 1)) := by
      have := MemLp.toMemLpPer hT1c
      convert this using 1
    have hexp_eq : γBar'E =
        ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β /
            (hpow.α * (hpow.β + 1) / hpow.β - 1)) := by
      rw [hγBar'E_def, hγ'_paper_eq]
    rw [hexp_eq]; exact hres
  -- Field (5) `bΔm_endpoint`.
  have bΔm_endpoint_cert :
      Periodic.MemLpPer (d := d) γBar'E
        (fun x => (|mLim x| + |mLim x|) ^
            (1 + hpow.β - hpow.β / hpow.α)) := by
    have hβα_pos : 0 < hpow.β / hpow.α := div_pos hβ_pos hα_pos
    have hβα_lt : hpow.β / hpow.α < hpow.β + 1 := by
      have h1 : hpow.β / hpow.α ≤ hpow.β := by
        rw [div_le_iff₀ hα_pos]
        nlinarith [hpow.hα, hβ_pos]
      linarith
    have hexp_pos : 0 < hpow.β + 1 - hpow.β / hpow.α := by linarith
    set qE : ℝ≥0∞ := ENNReal.ofReal (hpow.β + 1 - hpow.β / hpow.α) with hqE_def
    have hqE_toReal : qE.toReal = hpow.β + 1 - hpow.β / hpow.α := by
      rw [hqE_def]; exact ENNReal.toReal_ofReal hexp_pos.le
    have hT2a :
        MeasureTheory.MemLp (fun x : (Fin d → ℝ) => |μSum x| ^ qE.toReal)
              ((ENNReal.ofReal (hpow.β + 1)) / qE)
              (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
      have h1 := MeasureTheory.MemLp.norm_rpow_div hμSum_paperβ.toMemLp qE
      have heq :
          (fun x : (Fin d → ℝ) => ‖μSum x‖ ^ qE.toReal)
          = fun x : (Fin d → ℝ) => |μSum x| ^ qE.toReal := by
        funext x; rw [Real.norm_eq_abs]
      rw [heq] at h1
      exact h1
    have hβne : hpow.β ≠ 0 := hβ_pos.ne'
    have hαne : hpow.α ≠ 0 := hα_pos.ne'
    have hbb_ne : hpow.β + 1 ≠ 0 := hβ1_pos.ne'
    have hβbβα_ne : hpow.β + 1 - hpow.β / hpow.α ≠ 0 := hexp_pos.ne'
    have hgb_gt_one : 1 < hpow.α * (hpow.β + 1) / hpow.β := by
      rw [lt_div_iff₀ hβ_pos]; nlinarith [hpow.hα, hβ_pos]
    have hγb_ne : hpow.α * (hpow.β + 1) / hpow.β ≠ 0 := by
      have : 0 < hpow.α * (hpow.β + 1) / hpow.β :=
        div_pos (mul_pos hα_pos hβ1_pos) hβ_pos
      exact this.ne'
    have hγbm1_ne : hpow.α * (hpow.β + 1) / hpow.β - 1 ≠ 0 := by linarith
    have hdiv_eq :
        (ENNReal.ofReal (hpow.β + 1)) / qE = γBar'E := by
      rw [hqE_def, hγBar'E_def, hγBar'_eq, hγBar_eq,
        ← ENNReal.ofReal_div_of_pos hexp_pos]
      congr 1
      field_simp
    have heq :
        (fun x : (Fin d → ℝ) => |μSum x| ^ qE.toReal)
        = (fun x : (Fin d → ℝ) => |μSum x| ^ (hpow.β + 1 - hpow.β / hpow.α)) := by
      funext x; rw [hqE_toReal]
    rw [heq] at hT2a
    have hT2b :
        Periodic.MemLpPer (d := d) γBar'E
          (fun x : (Fin d → ℝ) => |μSum x| ^ (hpow.β + 1 - hpow.β / hpow.α)) := by
      have := MemLp.toMemLpPer hT2a
      rw [hdiv_eq] at this
      exact this
    have hsh : (1 : ℝ) + hpow.β - hpow.β / hpow.α
                  = hpow.β + 1 - hpow.β / hpow.α := by ring
    have hbound :
        ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
          ‖μSum x ^ (1 + hpow.β - hpow.β / hpow.α)‖ ≤
            (1 : ℝ) * ‖|μSum x| ^ (hpow.β + 1 - hpow.β / hpow.α)‖ := by
      refine Filter.Eventually.of_forall ?_
      intro x
      rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul, hsh]
      have habs := Real.abs_rpow_le_abs_rpow (μSum x) (hpow.β + 1 - hpow.β / hpow.α)
      have hrhs_nn : 0 ≤ |μSum x| ^ (hpow.β + 1 - hpow.β / hpow.α) :=
        Real.rpow_nonneg (abs_nonneg _) _
      rw [abs_of_nonneg hrhs_nn]
      exact habs
    have hmeas :
        MeasureTheory.AEStronglyMeasurable
          (fun x : (Fin d → ℝ) => μSum x ^ (1 + hpow.β - hpow.β / hpow.α))
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
      have h_exp_nn : (0 : ℝ) ≤ 1 + hpow.β - hpow.β / hpow.α := by linarith [hexp_pos]
      have hcont : Continuous (fun y : ℝ => y ^ (1 + hpow.β - hpow.β / hpow.α)) :=
        Real.continuous_rpow_const h_exp_nn
      exact hcont.comp_aestronglyMeasurable hμSum_β.aestronglyMeasurable
    have hT2c :
        Periodic.MemLpPer (d := d) γBar'E
          (fun x : (Fin d → ℝ) => μSum x ^ (1 + hpow.β - hpow.β / hpow.α)) :=
      MemLp.toMemLpPer
        (MeasureTheory.MemLp.of_le_mul hT2b.toMemLp hmeas hbound)
    convert hT2c using 1
  -- Field (6) `bΔm`: `μSum ∈ Lᵞ'`.
  have bΔm_cert :
      Periodic.MemLpPer (d := d) γBar'E
        (fun x => |mLim x| + |mLim x|) := by
    have hT10 : Periodic.MemLpPer (d := d) γBar'E μSum :=
      Periodic.MemLpPer.mono_exponent_finite hγ'_le_β hβTop hμSum_β
    convert hT10 using 1
  -- Field (7) `bG_grad`.
  have bG_grad_cert :
      Periodic.MemLpPer (d := d) γBar'E
        (fun x =>
          (∑ i,
              (|(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₂
                              : (Fin d → ℝ) → ℝ)) x|
                + |(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₁
                              : (Fin d → ℝ) → ℝ)) x|) ^ (2 : ℕ))
              ^ ((γBar - 1) / 2)) := by
    set q2E : ℝ≥0∞ := (2 : ℝ≥0∞) with hq2E_def
    have hq2E_top : q2E ≠ ⊤ := by rw [hq2E_def]; decide
    have hq2E_toReal : q2E.toReal = 2 := by rw [hq2E_def]; rfl
    have hSq_each : ∀ i,
        MeasureTheory.MemLp
          (fun x : (Fin d → ℝ) => ‖DυSum i x‖ ^ q2E.toReal)
          (γBarE / q2E)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
      fun i => MeasureTheory.MemLp.norm_rpow_div (hDυSum_γ i).toMemLp q2E
    have hSq_each' : ∀ i,
        Periodic.MemLpPer (d := d) (γBarE / q2E)
          (fun x : (Fin d → ℝ) => (DυSum i x) ^ (2 : ℕ)) := by
      intro i
      have h := hSq_each i
      have heq :
          (fun x : (Fin d → ℝ) => ‖DυSum i x‖ ^ q2E.toReal)
          = (fun x : (Fin d → ℝ) => (DυSum i x) ^ (2 : ℕ)) := by
        funext x
        rw [hq2E_toReal, Real.norm_eq_abs]
        rw [show ((2 : ℝ) = ((2 : ℕ) : ℝ)) from by norm_num,
            Real.rpow_natCast, sq_abs]
      rw [heq] at h
      exact MemLp.toMemLpPer h
    have hSumSq :
        Periodic.MemLpPer (d := d) (γBarE / q2E)
          (fun x : (Fin d → ℝ) => ∑ i, (DυSum i x) ^ (2 : ℕ)) := by
      have hsum : MeasureTheory.MemLp
          (fun x : (Fin d → ℝ) => ∑ i : Fin d, (fun x => (DυSum i x) ^ (2 : ℕ)) x)
          (γBarE / q2E)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
        refine MeasureTheory.memLp_finset_sum (Finset.univ : Finset (Fin d)) ?_
        intro i _; exact (hSq_each' i).toMemLp
      exact MemLp.toMemLpPer hsum
    have hγm1_pos : 0 < γBarReal - 1 := by linarith
    have hexp12_pos : 0 < (γBarReal - 1) / 2 := by linarith
    set qE : ℝ≥0∞ := ENNReal.ofReal ((γBarReal - 1) / 2) with hqE_def
    have hqE_toReal : qE.toReal = (γBarReal - 1) / 2 := by
      rw [hqE_def]; exact ENNReal.toReal_ofReal hexp12_pos.le
    have hRpow : MeasureTheory.MemLp
        (fun x : (Fin d → ℝ) =>
          ‖∑ i, (DυSum i x) ^ (2 : ℕ)‖ ^ qE.toReal)
        ((γBarE / q2E) / qE)
        (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
      MeasureTheory.MemLp.norm_rpow_div hSumSq.toMemLp qE
    have hdiv_eq : (γBarE / q2E) / qE = γBar'E := by
      rw [hq2E_def, hqE_def, hγBarE_def, hγBar'E_def, hγBar'_eq,
          ← ENNReal.ofReal_ofNat (n := 2),
          ← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
          ← ENNReal.ofReal_div_of_pos hexp12_pos]
      congr 1
      have hγne : γBarReal ≠ 0 := hγBarReal_pos.ne'
      have hγm1ne : γBarReal - 1 ≠ 0 := hγm1_pos.ne'
      field_simp
    have hSumSq_nn : ∀ x, 0 ≤ ∑ i, (DυSum i x) ^ (2 : ℕ) :=
      fun x => Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have heqfn :
        (fun x : (Fin d → ℝ) =>
          ‖∑ i, (DυSum i x) ^ (2 : ℕ)‖ ^ qE.toReal)
        = (fun x : (Fin d → ℝ) =>
            (∑ i, (DυSum i x) ^ (2 : ℕ)) ^ ((γBarReal - 1) / 2)) := by
      funext x
      rw [hqE_toReal, Real.norm_eq_abs, abs_of_nonneg (hSumSq_nn x)]
    rw [heqfn] at hRpow
    have hres :
        Periodic.MemLpPer (d := d) γBar'E
          (fun x : (Fin d → ℝ) =>
            (∑ i, (DυSum i x) ^ (2 : ℕ)) ^ ((γBarReal - 1) / 2)) := by
      have := MemLp.toMemLpPer hRpow
      rw [hdiv_eq] at this
      exact this
    rw [hγBar_id]
    convert hres using 1
  -- Field (8) `bG_val`.
  have bG_val_cert :
      Periodic.MemLpPer (d := d) γBar'E
        (fun x => (|(uLim + (ψ₂ : (Fin d → ℝ) → ℝ)) x|
                    + |(uLim + (ψ₁ : (Fin d → ℝ) → ℝ)) x|)
                    ^ (γBar - 1)) := by
    have hγm1_pos : 0 < γBarReal - 1 := by linarith
    set qE : ℝ≥0∞ := ENNReal.ofReal (γBarReal - 1) with hqE_def
    have hqE_toReal : qE.toReal = γBarReal - 1 := by
      rw [hqE_def]; exact ENNReal.toReal_ofReal hγm1_pos.le
    have hRpow : MeasureTheory.MemLp
        (fun x : (Fin d → ℝ) => ‖υSum x‖ ^ qE.toReal)
        (γBarE / qE)
        (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
      MeasureTheory.MemLp.norm_rpow_div hυSum_γ.toMemLp qE
    have hdiv : γBarE / qE = γBar'E := by
      rw [hqE_def, hγBarE_def, hγBar'E_def, hγBar'_eq,
        ← ENNReal.ofReal_div_of_pos hγm1_pos]
    have hυSum_nn : ∀ x, 0 ≤ υSum x := fun x => by
      rw [hυSum_def]; exact add_nonneg (abs_nonneg _) (abs_nonneg _)
    have heq :
        (fun x : (Fin d → ℝ) => ‖υSum x‖ ^ qE.toReal)
        = (fun x : (Fin d → ℝ) => υSum x ^ (γBarReal - 1)) := by
      funext x
      rw [hqE_toReal, Real.norm_eq_abs, abs_of_nonneg (hυSum_nn x)]
    rw [heq] at hRpow
    have hres : Periodic.MemLpPer (d := d) γBar'E
        (fun x : (Fin d → ℝ) => υSum x ^ (γBarReal - 1)) := by
      have := MemLp.toMemLpPer hRpow
      rw [hdiv] at this
      exact this
    rw [hγBar_id]
    convert hres using 1
  -- Bundle the eight derived certs.
  exact
    { bΔυ := bΔυ_cert
      bΔp_pow := bΔp_pow_cert
      bΔm_pow := bΔm_pow_cert
      bΔm_grad := bΔm_grad_cert
      bΔm_endpoint := bΔm_endpoint_cert
      bΔm := bΔm_cert
      bG_grad := bG_grad_cert
      bG_val := bG_val_cert }

/-! ## Abstract DCT-Tendsto producer for set-family scalar Minty residues
(iter 0723, B′ path — Child 1 of 3 of the iter-0722 final-drain split)

Per the iter-0722 final-drain split (user directive 2026-05-21), this
section lands the **abstract scalar DCT-Tendsto producer** that the
record-assembly child (Child 2) was to compose with the iter-0721
shifted-route limit-passage helper (since deleted with the abandoned
K0-non-min shifted ladder) to drain the `setSegInputsAuth` field.

**Architecture (B′ discipline).** The producer is parameterised by:
- a sequence of integrands `Fn : ℕ → (Fin d → ℝ) → ℝ` indexed by the
  shift `cseq n := 1/(n+1)`;
- an a.e. pointwise limit integrand `Finf`;
- a uniform `L¹` dominator `G` controlling `|Fn n|` for all `n`;
- AE-strong-measurability of `Fn n` and `Finf`.

It produces the `Tendsto` of the integrals of `Fn n` over the unit cube
to the integral of `Finf`, via the project-standard pattern
`MeasureTheory.tendsto_integral_filter_of_dominated_convergence`.

**Paper anchor.** `lem:hemicont` (paper line 990). At the scalar
Minty-residue level, the segment integrand at shifted endpoints
`(mLim + ρ_i + c)` depends continuously on `c`, with a uniform
power-growth-based dominator (iter-0606/0609 paperSection8 segment
residues + `MemLpPer.add_const`). The abstract producer below isolates
the DCT-Tendsto step in a packaged form suitable for the record
assembly child.

**B′ discipline.** No new authorisation parameter; the
`setSegInputsAuth` field on `T10PaperResidues.of_paperHypotheses` is
untouched at this step (auth count stays at 3; it will be drained by
Child 3 after Child 2 lands the unshifted record assembly). -/

/-- **Abstract scalar DCT-Tendsto producer (iter 0723, B′ path, set-family).**
Given a sequence of integrands `Fn : ℕ → (Fin d → ℝ) → ℝ`, a pointwise
limit integrand `Finf`, AE-strong-measurability of all of them, an
`L¹` dominator `G` controlling `|Fn n x|` uniformly in `n`, and a.e.
pointwise convergence `Fn n x → Finf x`, conclude
`Tendsto (∫ Fn n) atTop (𝓝 (∫ Finf))` over the unit cube.

Body: direct application of
`MeasureTheory.tendsto_integral_filter_of_dominated_convergence` at
`Filter.atTop`. This is the scalar packaging used by the set-family
final-drain Child 2 (`set-final-shifted-to-unshifted-assembly`): the
`Fn` is the per-`c_n` shifted Minty-residue integrand and `Finf` is the
unshifted version. The uniform dominator `G` is constructed from the
iter-0720 set-family shifted dominator certificates via the cofinite
filter (`Filter.eventually_of_forall`). -/
theorem set_minty_residue_integral_tendsto_of_dominated
    {d : ℕ}
    {Fn : ℕ → (Fin d → ℝ) → ℝ} {Finf : (Fin d → ℝ) → ℝ}
    {G : (Fin d → ℝ) → ℝ}
    (hFn_meas : ∀ n,
      MeasureTheory.AEStronglyMeasurable (Fn n)
        (MeasureTheory.volume.restrict (UnitCube d)))
    (hG_int : MeasureTheory.Integrable G
                (MeasureTheory.volume.restrict (UnitCube d)))
    (hFn_bd : ∀ n,
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), ‖Fn n x‖ ≤ G x)
    (hFn_lim :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        Filter.Tendsto (fun n => Fn n x) Filter.atTop (nhds (Finf x))) :
    Filter.Tendsto
      (fun n => ∫ x in UnitCube d, Fn n x
                  ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
      Filter.atTop
      (nhds (∫ x in UnitCube d, Finf x
              ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))) :=
  MeasureTheory.tendsto_integral_of_dominated_convergence
    G hFn_meas hG_int hFn_bd hFn_lim

/-- **Canonical shift sequence for the set-family final-drain (iter 0723).**
`setFinalDrainCseq n := 1 / ((n : ℝ) + 1)`. Mirrors the project-standard
`paperEpsSeq` (BanachBridge.lean:7429). Strictly positive, tending to
`0` at infinity. This is the canonical shift sequence the record-assembly
Child 2 was to instantiate the (since-deleted) shifted-route
limit-passage helper at. -/
noncomputable def setFinalDrainCseq : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)

/-- Strict positivity of the canonical shift sequence. -/
lemma setFinalDrainCseq_pos : ∀ n, 0 < setFinalDrainCseq n := by
  intro n
  unfold setFinalDrainCseq
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  exact div_pos one_pos hn

/-- Convergence: `setFinalDrainCseq → 0` at infinity. -/
lemma setFinalDrainCseq_tendsto :
    Filter.Tendsto setFinalDrainCseq Filter.atTop (nhds 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- Strengthened convergence into the right-neighborhood `𝓝[>] 0`, the
filter form expected by the (since-deleted) shifted-route helper. -/
lemma setFinalDrainCseq_tendsto_nhdsWithin_Ioi :
    Filter.Tendsto setFinalDrainCseq Filter.atTop
      (nhdsWithin 0 (Set.Ioi 0)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨setFinalDrainCseq_tendsto, ?_⟩
  exact Filter.Eventually.of_forall (fun n => setFinalDrainCseq_pos n)

/-- **Sanity-check `example`** for the iter-0723 abstract scalar
DCT-Tendsto producer at symbolic inputs, the producer applies
DCT and yields the desired `Tendsto`. -/
example
    {d : ℕ}
    {Fn : ℕ → (Fin d → ℝ) → ℝ} {Finf : (Fin d → ℝ) → ℝ}
    {G : (Fin d → ℝ) → ℝ}
    (hFn_meas : ∀ n,
      MeasureTheory.AEStronglyMeasurable (Fn n)
        (MeasureTheory.volume.restrict (UnitCube d)))
    (hG_int : MeasureTheory.Integrable G
                (MeasureTheory.volume.restrict (UnitCube d)))
    (hFn_bd : ∀ n,
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), ‖Fn n x‖ ≤ G x)
    (hFn_lim :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        Filter.Tendsto (fun n => Fn n x) Filter.atTop (nhds (Finf x))) :
    Filter.Tendsto
      (fun n => ∫ x in UnitCube d, Fn n x
                  ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
      Filter.atTop
      (nhds (∫ x in UnitCube d, Finf x
              ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))) :=
  set_minty_residue_integral_tendsto_of_dominated
    hFn_meas hG_int hFn_bd hFn_lim

/-! ### K0 minimal-shape SegInputs record + closed producer (no `hβ_ge_one`)

Iter `infra-P6-K0-min-closed-segInputsK0-set` (2026-05-22). Sibling of
iter-0769's `setFamilyNarrowSegInputsK0_closed_of_paperHypotheses`
mirrored down the `hβ_ge_one`-removal chain begun by iter 0786
(`SetFamilyNarrowDominatorsK0Min`) and iter 0789
(`hemicontSegmentData_set_narrow_K0_min_of_paperHypotheses`).

The legacy `SetFamilyNarrowSegInputsK0` carries an over-specified
`bΔm1 : MemLpPer βBar' (μSum + 1)` field that uniquely forces the
non-paper-faithful side condition `1 ≤ hpow.β` on the closed dominators
producer. The minimal sibling `SetFamilyNarrowSegInputsK0Min` drops this
field; its closed producer
`setFamilyNarrowSegInputsK0_closed_min_of_paperHypotheses` then composes
the iter-0786 minimal dominators producer (no `hβ_ge_one`) with the
unchanged paper-Section-8 K0 aux-hyps producer and the iter-0768
measurability lemmas.

The field set of `SetFamilyNarrowSegInputsK0Min` matches the input
surface of the iter-0789 minimal composer
`hemicontSegmentData_set_narrow_K0_min_of_paperHypotheses` exactly. -/

/-- **K0 minimal-shape sibling of `SetFamilyNarrowSegInputsK0`.**

Eight dominator certificates (drops the `bΔm1` over-specification),
two `MFGOpEpsAuxHyps` certificates at the two lifted Banach pairs, and
two Carathéodory measurabilities at the bare endpoints. Field set
matches the input surface of iter-0789's minimal composer. -/
structure SetFamilyNarrowSegInputsK0Min
    {d : ℕ} {γBarReal βBarReal βBarReal' γBarReal' γBar : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    (hmLim_memLp : Periodic.MemLpPer (d := d)
                      (ENNReal.ofReal βBarReal) mLim)
    (huLim_sob : Periodic.MemSobolevPer (d := d)
                      (ENNReal.ofReal γBarReal) uLim)
    (hDuLim_memLp_γ : ∀ i, Periodic.MemLpPer (d := d)
                              (ENNReal.ofReal γBarReal) (DuLim i))
    (ρ₁ ρ₂ : (Fin d → ℝ) → ℝ)
    (hρ₁_lp : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) ρ₁)
    (hρ₂_lp : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) ρ₂)
    (η ν : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    : Type where
  /-- Primal `MFGOpEpsAuxHyps` certificate at the first lifted Banach pair. -/
  aux₁ : StationaryMFG.Theorems.SimplePower.Banach.MFGOpEpsAuxHyps
            (d := d) γBarReal βBarReal βBarReal' γBarReal' V H DpH
            (StationaryMFG.Theorems.SimplePower.Banach.DuOf
              (StationaryMFG.Theorems.SimplePower.Banach.bareToBanachPair_set_paper
                (d := d) (βBarReal := βBarReal) (γBarReal := γBarReal)
                (DuLim := DuLim)
                hmLim_memLp huLim_sob hDuLim_memLp_γ hρ₁_lp))
            (StationaryMFG.Theorems.SimplePower.Banach.mOf
              (StationaryMFG.Theorems.SimplePower.Banach.bareToBanachPair_set_paper
                (d := d) (βBarReal := βBarReal) (γBarReal := γBarReal)
                (DuLim := DuLim)
                hmLim_memLp huLim_sob hDuLim_memLp_γ hρ₁_lp))
            (StationaryMFG.Theorems.SimplePower.Banach.uOf
              (StationaryMFG.Theorems.SimplePower.Banach.bareToBanachPair_set_paper
                (d := d) (βBarReal := βBarReal) (γBarReal := γBarReal)
                (DuLim := DuLim)
                hmLim_memLp huLim_sob hDuLim_memLp_γ hρ₁_lp))
  /-- Primal `MFGOpEpsAuxHyps` at the second lifted Banach pair. -/
  aux₂ : StationaryMFG.Theorems.SimplePower.Banach.MFGOpEpsAuxHyps
            (d := d) γBarReal βBarReal βBarReal' γBarReal' V H DpH
            (StationaryMFG.Theorems.SimplePower.Banach.DuOf
              (StationaryMFG.Theorems.SimplePower.Banach.bareToBanachPair_set_paper
                (d := d) (βBarReal := βBarReal) (γBarReal := γBarReal)
                (DuLim := DuLim)
                hmLim_memLp huLim_sob hDuLim_memLp_γ hρ₂_lp))
            (StationaryMFG.Theorems.SimplePower.Banach.mOf
              (StationaryMFG.Theorems.SimplePower.Banach.bareToBanachPair_set_paper
                (d := d) (βBarReal := βBarReal) (γBarReal := γBarReal)
                (DuLim := DuLim)
                hmLim_memLp huLim_sob hDuLim_memLp_γ hρ₂_lp))
            (StationaryMFG.Theorems.SimplePower.Banach.uOf
              (StationaryMFG.Theorems.SimplePower.Banach.bareToBanachPair_set_paper
                (d := d) (βBarReal := βBarReal) (γBarReal := γBarReal)
                (DuLim := DuLim)
                hmLim_memLp huLim_sob hDuLim_memLp_γ hρ₂_lp))
  /-- Dominator cert: `|uLim| + |uLim| ∈ Lᵝ'`. -/
  bΔυ : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal')
            (fun x => |uLim x| + |uLim x|)
  /-- Dominator cert for the gradient `α`-power. -/
  bΔp_pow : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal')
            (fun x =>
              ‖fun i => |DuLim i x| + |DuLim i x|‖ ^ hpow.α + 1)
  /-- Dominator cert for the density `β`-power. -/
  bΔm_pow : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal')
            (fun x =>
              (|(mLim + ρ₂) x| + |(mLim + ρ₁) x|) ^ hpow.β + 1)
  /-- Dominator cert for the gradient cross-term. -/
  bΔm_grad : Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
            (fun x => (|(mLim + ρ₂) x| + |(mLim + ρ₁) x|)
                * ‖fun i => |DuLim i x| + |DuLim i x|‖ ^ (hpow.α - 1))
  /-- Dominator cert for the endpoint exponent. -/
  bΔm_endpoint : Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
            (fun x =>
              (|(mLim + ρ₂) x| + |(mLim + ρ₁) x|) ^
                (1 + hpow.β - hpow.β / hpow.α))
  /-- Dominator cert for the bare density. -/
  bΔm : Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
            (fun x => |(mLim + ρ₂) x| + |(mLim + ρ₁) x|)
  -- NB: NO `bΔm1` field — its removal is the entire point of this
  -- minimal-shape sibling; this is what removes the `hβ_ge_one` side
  -- condition from the closed dominators producer.
  /-- Dominator cert for the Gateaux gradient block. -/
  bG_grad : Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
            (fun x =>
              (∑ i, (|DuLim i x| + |DuLim i x|) ^ (2 : ℕ))
                  ^ ((γBar - 1) / 2))
  /-- Dominator cert for the Gateaux value block. -/
  bG_val : Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
            (fun x => (|uLim x| + |uLim x|) ^ (γBar - 1))
  /-- Caratheodory measurability of the **K0** unregularised integrand
  at the bare endpoints. -/
  hF_unreg_meas_bare :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x =>
          StationaryMFG.Theorems.SimplePower.aepsiIntegrandAt_unreg_K0
            V H DpH DuLim DuLim (mLim + ρ₁) (mLim + ρ₂)
            uLim uLim Dν η ν x t)
        (MeasureTheory.volume.restrict (UnitCube d))
  /-- Caratheodory measurability of the Gateaux integrand
  at the bare endpoints. -/
  hF_gat_meas_bare :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x =>
          StationaryMFG.Theorems.SimplePower.aepsiIntegrandAt_gateaux
            γBar DuLim DuLim uLim uLim Dν ν x t)
        (MeasureTheory.volume.restrict (UnitCube d))

/-- **Closed paper-faithful producer for the K0 minimal-shape set-family
per-pair record** (`infra-P6-K0-min-closed-segInputsK0-set`, 2026-05-22).

Sibling of `setFamilyNarrowSegInputsK0_closed_of_paperHypotheses` (iter
0769). Identical pipeline except:
- swaps the iter-0767 closed dominators producer for the iter-0786
  minimal sibling `setFamilyNarrowDominatorsK0Min_of_paperHypotheses`
  (no `bΔm1`, no `hβ_ge_one`);
- outputs `SetFamilyNarrowSegInputsK0Min` instead of
  `SetFamilyNarrowSegInputsK0`.

Signature drops `hβ_ge_one` — this producer is the entire purpose of the
minimal-shape refactor. The two `MFGOpEpsAuxHyps` certificates come from
the unchanged paper-Section-8 K0 aux-hyps producer
`paperSection8_auxHypsK0_of_paperHypotheses` at the lifted Banach pairs
(K0 membership via `bareToBanachPair_set_paper_mem_K0Aepsi`); the two
Carathéodory measurabilities come from
`aepsiIntegrand_unreg_K0_meas_of_paperHypotheses` and
`aepsiIntegrand_gateaux_meas_of_paperHypotheses`. -/
noncomputable def setFamilyNarrowSegInputsK0_closed_min_of_paperHypotheses
    {d : ℕ} {γBarReal βBarReal βBarReal' γBarReal' γBar : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    -- Paper-side Hamiltonian hypotheses.
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hHextCont : Hamiltonian.HypothesisHextJointCont (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    (hV : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (hExp :
      StationaryMFG.Theorems.SimplePower.SimplePowerExponentFacts
        γBarReal (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
        (ENNReal.ofReal βBarReal'))
    -- Paper-exponent identification residues.
    (hβBar_eq : βBarReal = hpow.β + 1)
    (hγBar_eq : γBarReal = hpow.α * (hpow.β + 1) / hpow.β)
    (hβBar'_eq : βBarReal' = (hpow.β + 1) / hpow.β)
    (hγBar'_eq : γBarReal' = γBarReal / (γBarReal - 1))
    -- Hölder-pair residues.
    (hβ : βBarReal.HolderConjugate βBarReal')
    (hγ : γBarReal.HolderConjugate γBarReal')
    (hβTop : ENNReal.ofReal γBarReal ≠ ⊤)
    (hγ'_le_β : ENNReal.ofReal γBarReal' ≤ ENNReal.ofReal βBarReal)
    -- Gateaux-parameter identification residue.
    (hγBar_id : γBar = γBarReal)
    -- Weak-limit triple.
    {mLim uLim : (Fin d → ℝ) → ℝ}
    {DuLim : Fin d → (Fin d → ℝ) → ℝ}
    (hmLim_memLp : Periodic.MemLpPer (d := d)
                      (ENNReal.ofReal βBarReal) mLim)
    (huLim_sob : Periodic.MemSobolevPer (d := d)
                      (ENNReal.ofReal γBarReal) uLim)
    (hDuLim_memLp_γ : ∀ i, Periodic.MemLpPer (d := d)
                              (ENNReal.ofReal γBarReal) (DuLim i))
    (hmLim_nn : 0 ≤ᵐ[MeasureTheory.Measure.restrict
                      MeasureTheory.volume (UnitCube d)] mLim)
    -- Universal-`q` measurability witnesses for the aux-hyps producer.
    (hF_HJB_meas :
      ∀ q : StationaryMFG.Theorems.SimplePower.Banach.XBanach
              d βBarReal γBarReal,
        MeasureTheory.AEStronglyMeasurable
          (fun x =>
            -(StationaryMFG.Theorems.SimplePower.Banach.uOf q x)
              - H x (fun i =>
                  StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
                  (StationaryMFG.Theorems.SimplePower.Banach.mOf q x) + V x)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (hF_flux_meas :
      ∀ q : StationaryMFG.Theorems.SimplePower.Banach.XBanach
              d βBarReal γBarReal, ∀ i,
        MeasureTheory.AEStronglyMeasurable
          (fun x =>
            StationaryMFG.Theorems.SimplePower.Banach.mOf q x
              * DpH x (fun j =>
                  StationaryMFG.Theorems.SimplePower.Banach.DuOf q j x)
                  (StationaryMFG.Theorems.SimplePower.Banach.mOf q x) i)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    -- Family-member selectors and certificates.
    {ρ₁ ρ₂ : (Fin d → ℝ) → ℝ}
    (hρ₁_lp : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) ρ₁)
    (hρ₂_lp : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) ρ₂)
    (hρ₁_nn : ∀ x, 0 ≤ ρ₁ x)
    (hρ₂_nn : ∀ x, 0 ≤ ρ₂ x)
    -- Per-test-pair local args (paper-faithful per-test-pair, NOT auths).
    (η ν : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (hη : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) η)
    (hDν : ∀ i, Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dν i))
    (hν_β : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) ν)
    (hν_γ : Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal) ν) :
    SetFamilyNarrowSegInputsK0Min (d := d)
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal') (γBar := γBar)
      V H DpH hpow
      mLim uLim DuLim hmLim_memLp huLim_sob hDuLim_memLp_γ
      ρ₁ ρ₂ hρ₁_lp hρ₂_lp η ν Dν := by
  -- (1) Derive the eight (minimal) dominator certificates from paper
  -- hypotheses via the iter-0786 minimal closed dominators producer.
  -- No `hβ_ge_one` needed here — that side condition is gone exactly
  -- because the `bΔm1` slot is dropped.
  have hDom :=
    setFamilyNarrowDominatorsK0Min_of_paperHypotheses
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal') (γBar := γBar)
      (H := H) (DpH := DpH)
      hpow hHat0 hAgree hβ.symm hγ.symm
      hβBar_eq hγBar_eq hβBar'_eq hγBar'_eq hγBar_id
      hmLim_memLp huLim_sob hDuLim_memLp_γ
      hρ₁_lp hρ₂_lp hρ₁_nn hρ₂_nn
  -- (2) Derive AE-strong-measurability inputs and plug them into the
  -- iter-0768 measurability producers (identical to iter-0769).
  have hmLim_meas := hmLim_memLp.aestronglyMeasurable
  have huLim_meas := huLim_sob.1.aestronglyMeasurable
  have hDuLim_meas : ∀ i, MeasureTheory.AEStronglyMeasurable (DuLim i)
        (MeasureTheory.volume.restrict (UnitCube d)) :=
    fun i => (hDuLim_memLp_γ i).aestronglyMeasurable
  have hρ₁_meas := hρ₁_lp.aestronglyMeasurable
  have hρ₂_meas := hρ₂_lp.aestronglyMeasurable
  have hV_meas := hV.aestronglyMeasurable
  have hη_meas := hη.aestronglyMeasurable
  have hν_meas := hν_β.aestronglyMeasurable
  have hDν_meas : ∀ i, MeasureTheory.AEStronglyMeasurable (Dν i)
        (MeasureTheory.volume.restrict (UnitCube d)) :=
    fun i => (hDν i).aestronglyMeasurable
  have hF_unreg_meas_bare :=
    aepsiIntegrand_unreg_K0_meas_of_paperHypotheses (d := d)
      (V := V) (H := H) (DpH := DpH)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      (ρ₁ := ρ₁) (ρ₂ := ρ₂) (η := η) (ν := ν) (Dν := Dν)
      hpow hHextCont
      hmLim_meas huLim_meas hDuLim_meas hρ₁_meas hρ₂_meas
      hV_meas hη_meas hν_meas hDν_meas
  have hF_gat_meas_bare :=
    aepsiIntegrand_gateaux_meas_of_paperHypotheses (d := d) γBar
      (uLim := uLim) (DuLim := DuLim) (ν := ν) (Dν := Dν)
      huLim_meas hDuLim_meas hν_meas hDν_meas
  -- (3) K0-membership of the two lifted set-family Banach pairs
  -- (identical to iter-0769).
  have hq₁_K0 :
      StationaryMFG.Theorems.SimplePower.Banach.bareToBanachPair_set_paper
          (d := d) (βBarReal := βBarReal) (γBarReal := γBarReal)
          (DuLim := DuLim)
          hmLim_memLp huLim_sob hDuLim_memLp_γ hρ₁_lp
        ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi
            d βBarReal γBarReal :=
    StationaryMFG.Theorems.SimplePower.Banach.bareToBanachPair_set_paper_mem_K0Aepsi
      (d := d) (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hmLim_nn hρ₁_nn hρ₁_lp
  have hq₂_K0 :
      StationaryMFG.Theorems.SimplePower.Banach.bareToBanachPair_set_paper
          (d := d) (βBarReal := βBarReal) (γBarReal := γBarReal)
          (DuLim := DuLim)
          hmLim_memLp huLim_sob hDuLim_memLp_γ hρ₂_lp
        ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi
            d βBarReal γBarReal :=
    StationaryMFG.Theorems.SimplePower.Banach.bareToBanachPair_set_paper_mem_K0Aepsi
      (d := d) (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hmLim_nn hρ₂_nn hρ₂_lp
  -- (4) Specialise the universal-`q` K0 aux-hyps producer at each lifted pair.
  have aux₁ :=
    StationaryMFG.Theorems.SimplePower.Banach.paperSection8_auxHypsK0_of_paperHypotheses
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      (V := V) (H := H) (DpH := DpH)
      hmon hpow hHat0 hAgree hV hExp
      hβBar_eq hγBar_eq hβBar'_eq hγBar'_eq
      hβ hγ hβTop hγ'_le_β hF_HJB_meas hF_flux_meas
      _ hq₁_K0
  have aux₂ :=
    StationaryMFG.Theorems.SimplePower.Banach.paperSection8_auxHypsK0_of_paperHypotheses
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      (V := V) (H := H) (DpH := DpH)
      hmon hpow hHat0 hAgree hV hExp
      hβBar_eq hγBar_eq hβBar'_eq hγBar'_eq
      hβ hγ hβTop hγ'_le_β hF_HJB_meas hF_flux_meas
      _ hq₂_K0
  -- (5) Assemble the minimal record. Eight dominator fields come from
  -- `hDom` (iter-0786 minimal closed producer); the two measurabilities
  -- from the iter-0768 producers. No `bΔm1` field.
  exact
    { aux₁ := aux₁
      aux₂ := aux₂
      bΔυ := hDom.bΔυ
      bΔp_pow := hDom.bΔp_pow
      bΔm_pow := hDom.bΔm_pow
      bΔm_grad := hDom.bΔm_grad
      bΔm_endpoint := hDom.bΔm_endpoint
      bΔm := hDom.bΔm
      bG_grad := hDom.bG_grad
      bG_val := hDom.bG_val
      hF_unreg_meas_bare := hF_unreg_meas_bare
      hF_gat_meas_bare := hF_gat_meas_bare }

/-! ### K0 minimal-shape signed-family per-pair seg-inputs record and closed
producer (`infra-P6-K0-min-closed-segInputsK0-signed`, audit 2026-05-22).

Signed mirror of `SetFamilyNarrowSegInputsK0Min` /
`setFamilyNarrowSegInputsK0_closed_min_of_paperHypotheses` (iter-0792, above)
using the iter-0790 minimal-shape signed K0 composer
`hemicontSegmentData_signed_narrow_K0_min_of_paperHypotheses` as the
downstream consumer. Differences from the iter-0775 closed signed producer:

- drops the over-specified `bΔm1` dominator field;
- with it, drops the non-paper-faithful side condition `1 ≤ hpow.β` from
  the signature;
- swaps the iter-0773 closed signed dominators producer for the iter-0787
  minimal sibling `signedFamilyNarrowDominatorsK0Min_of_paperHypotheses`;
- outputs `SignedFamilyNarrowSegInputsK0Min` in place of
  `SignedFamilyNarrowSegInputsK0`. -/

/-- **K0 minimal-shape sibling of `SignedFamilyNarrowSegInputsK0`.**

Per-test-pair segment-data inputs for the K0 minimal-shape signed-family
composer `hemicontSegmentData_signed_narrow_K0_min_of_paperHypotheses`.
Eight dominator certificates (drops the `bΔm1` over-specification), two
`MFGOpEpsAuxHyps` certificates at the two lifted signed Banach pairs, and
two Carathéodory measurabilities at the bare signed endpoints
`(mLim + g_i)`. Signed mirror of `SetFamilyNarrowSegInputsK0Min`. -/
structure SignedFamilyNarrowSegInputsK0Min
    {d : ℕ} {γBarReal βBarReal βBarReal' γBarReal' γBar : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    (hmLim_memLp : Periodic.MemLpPer (d := d)
                      (ENNReal.ofReal βBarReal) mLim)
    (huLim_sob : Periodic.MemSobolevPer (d := d)
                      (ENNReal.ofReal γBarReal) uLim)
    (hDuLim_memLp_γ : ∀ i, Periodic.MemLpPer (d := d)
                              (ENNReal.ofReal γBarReal) (DuLim i))
    (g₁ g₂ : (Fin d → ℝ) → ℝ)
    (hg₁_lp : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) g₁)
    (hg₂_lp : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) g₂)
    (η ν : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    : Type where
  /-- Primal `MFGOpEpsAuxHyps` certificate at the first lifted Banach pair. -/
  aux₁ : StationaryMFG.Theorems.SimplePower.Banach.MFGOpEpsAuxHyps
            (d := d) γBarReal βBarReal βBarReal' γBarReal' V H DpH
            (StationaryMFG.Theorems.SimplePower.Banach.DuOf
              (StationaryMFG.Theorems.SimplePower.Banach.bareToBanachPair_set_paper
                (d := d) (βBarReal := βBarReal) (γBarReal := γBarReal)
                (DuLim := DuLim)
                hmLim_memLp huLim_sob hDuLim_memLp_γ hg₁_lp))
            (StationaryMFG.Theorems.SimplePower.Banach.mOf
              (StationaryMFG.Theorems.SimplePower.Banach.bareToBanachPair_set_paper
                (d := d) (βBarReal := βBarReal) (γBarReal := γBarReal)
                (DuLim := DuLim)
                hmLim_memLp huLim_sob hDuLim_memLp_γ hg₁_lp))
            (StationaryMFG.Theorems.SimplePower.Banach.uOf
              (StationaryMFG.Theorems.SimplePower.Banach.bareToBanachPair_set_paper
                (d := d) (βBarReal := βBarReal) (γBarReal := γBarReal)
                (DuLim := DuLim)
                hmLim_memLp huLim_sob hDuLim_memLp_γ hg₁_lp))
  /-- Primal `MFGOpEpsAuxHyps` at the second lifted Banach pair. -/
  aux₂ : StationaryMFG.Theorems.SimplePower.Banach.MFGOpEpsAuxHyps
            (d := d) γBarReal βBarReal βBarReal' γBarReal' V H DpH
            (StationaryMFG.Theorems.SimplePower.Banach.DuOf
              (StationaryMFG.Theorems.SimplePower.Banach.bareToBanachPair_set_paper
                (d := d) (βBarReal := βBarReal) (γBarReal := γBarReal)
                (DuLim := DuLim)
                hmLim_memLp huLim_sob hDuLim_memLp_γ hg₂_lp))
            (StationaryMFG.Theorems.SimplePower.Banach.mOf
              (StationaryMFG.Theorems.SimplePower.Banach.bareToBanachPair_set_paper
                (d := d) (βBarReal := βBarReal) (γBarReal := γBarReal)
                (DuLim := DuLim)
                hmLim_memLp huLim_sob hDuLim_memLp_γ hg₂_lp))
            (StationaryMFG.Theorems.SimplePower.Banach.uOf
              (StationaryMFG.Theorems.SimplePower.Banach.bareToBanachPair_set_paper
                (d := d) (βBarReal := βBarReal) (γBarReal := γBarReal)
                (DuLim := DuLim)
                hmLim_memLp huLim_sob hDuLim_memLp_γ hg₂_lp))
  /-- Dominator cert: `|uLim| + |uLim| ∈ Lᵝ'`. -/
  bΔυ : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal')
            (fun x => |uLim x| + |uLim x|)
  /-- Dominator cert for the gradient `α`-power. -/
  bΔp_pow : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal')
            (fun x =>
              ‖fun i => |DuLim i x| + |DuLim i x|‖ ^ hpow.α + 1)
  /-- Dominator cert for the density `β`-power. -/
  bΔm_pow : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal')
            (fun x =>
              (|(mLim + g₂) x| + |(mLim + g₁) x|) ^ hpow.β + 1)
  /-- Dominator cert for the gradient cross-term. -/
  bΔm_grad : Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
            (fun x => (|(mLim + g₂) x| + |(mLim + g₁) x|)
                * ‖fun i => |DuLim i x| + |DuLim i x|‖ ^ (hpow.α - 1))
  /-- Dominator cert for the endpoint exponent. -/
  bΔm_endpoint : Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
            (fun x =>
              (|(mLim + g₂) x| + |(mLim + g₁) x|) ^
                (1 + hpow.β - hpow.β / hpow.α))
  /-- Dominator cert for the bare density. -/
  bΔm : Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
            (fun x => |(mLim + g₂) x| + |(mLim + g₁) x|)
  -- NB: NO `bΔm1` field — its removal is the entire point of this
  -- minimal-shape sibling; this is what removes the `hβ_ge_one` side
  -- condition from the closed dominators producer.
  /-- Dominator cert for the Gateaux gradient block. -/
  bG_grad : Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
            (fun x =>
              (∑ i, (|DuLim i x| + |DuLim i x|) ^ (2 : ℕ))
                  ^ ((γBar - 1) / 2))
  /-- Dominator cert for the Gateaux value block. -/
  bG_val : Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
            (fun x => (|uLim x| + |uLim x|) ^ (γBar - 1))
  /-- Caratheodory measurability of the **K0** unregularised integrand
  at the bare signed endpoints. -/
  hF_unreg_meas_bare :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x =>
          StationaryMFG.Theorems.SimplePower.aepsiIntegrandAt_unreg_K0
            V H DpH DuLim DuLim (mLim + g₁) (mLim + g₂)
            uLim uLim Dν η ν x t)
        (MeasureTheory.volume.restrict (UnitCube d))
  /-- Caratheodory measurability of the Gateaux integrand
  at the bare endpoints. -/
  hF_gat_meas_bare :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x =>
          StationaryMFG.Theorems.SimplePower.aepsiIntegrandAt_gateaux
            γBar DuLim DuLim uLim uLim Dν ν x t)
        (MeasureTheory.volume.restrict (UnitCube d))

/-- **Closed paper-faithful producer for the K0 minimal-shape signed-family
per-pair record** (`infra-P6-K0-min-closed-segInputsK0-signed`,
2026-05-22).

Signed sibling of `setFamilyNarrowSegInputsK0_closed_min_of_paperHypotheses`
(iter-0792) and minimal-shape sibling of
`signedFamilyNarrowSegInputsK0_closed_of_paperHypotheses` (iter-0775).
Identical pipeline to the latter except:
- swaps the iter-0773 closed dominators producer for the iter-0787 minimal
  sibling `signedFamilyNarrowDominatorsK0Min_of_paperHypotheses` (no
  `bΔm1`, no `hβ_ge_one`);
- outputs `SignedFamilyNarrowSegInputsK0Min` instead of
  `SignedFamilyNarrowSegInputsK0`.

Signature drops `hβ_ge_one` — this producer is the entire purpose of the
minimal-shape signed refactor. The two `MFGOpEpsAuxHyps` certificates come
from the unchanged paper-Section-8 K0 aux-hyps producer
`paperSection8_auxHypsK0_of_paperHypotheses` at the lifted Banach pairs
(K0 membership via `bareToBanachPair_set_paper_mem_K0Aepsi_jointNN`); the
two Carathéodory measurabilities come from the iter-0774 signed
measurability aliases. -/
noncomputable def signedFamilyNarrowSegInputsK0_closed_min_of_paperHypotheses
    {d : ℕ} {γBarReal βBarReal βBarReal' γBarReal' γBar : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    -- Paper-side Hamiltonian hypotheses.
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hHextCont : Hamiltonian.HypothesisHextJointCont (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    (hV : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (hExp :
      StationaryMFG.Theorems.SimplePower.SimplePowerExponentFacts
        γBarReal (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
        (ENNReal.ofReal βBarReal'))
    -- Paper-exponent identification residues.
    (hβBar_eq : βBarReal = hpow.β + 1)
    (hγBar_eq : γBarReal = hpow.α * (hpow.β + 1) / hpow.β)
    (hβBar'_eq : βBarReal' = (hpow.β + 1) / hpow.β)
    (hγBar'_eq : γBarReal' = γBarReal / (γBarReal - 1))
    -- Hölder-pair residues.
    (hβ : βBarReal.HolderConjugate βBarReal')
    (hγ : γBarReal.HolderConjugate γBarReal')
    (hβTop : ENNReal.ofReal γBarReal ≠ ⊤)
    (hγ'_le_β : ENNReal.ofReal γBarReal' ≤ ENNReal.ofReal βBarReal)
    -- Gateaux-parameter identification residue.
    (hγBar_id : γBar = γBarReal)
    -- Weak-limit triple.
    {mLim uLim : (Fin d → ℝ) → ℝ}
    {DuLim : Fin d → (Fin d → ℝ) → ℝ}
    (hmLim_memLp : Periodic.MemLpPer (d := d)
                      (ENNReal.ofReal βBarReal) mLim)
    (huLim_sob : Periodic.MemSobolevPer (d := d)
                      (ENNReal.ofReal γBarReal) uLim)
    (hDuLim_memLp_γ : ∀ i, Periodic.MemLpPer (d := d)
                              (ENNReal.ofReal γBarReal) (DuLim i))
    -- Universal-`q` measurability witnesses for the aux-hyps producer.
    (hF_HJB_meas :
      ∀ q : StationaryMFG.Theorems.SimplePower.Banach.XBanach
              d βBarReal γBarReal,
        MeasureTheory.AEStronglyMeasurable
          (fun x =>
            -(StationaryMFG.Theorems.SimplePower.Banach.uOf q x)
              - H x (fun i =>
                  StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
                  (StationaryMFG.Theorems.SimplePower.Banach.mOf q x) + V x)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (hF_flux_meas :
      ∀ q : StationaryMFG.Theorems.SimplePower.Banach.XBanach
              d βBarReal γBarReal, ∀ i,
        MeasureTheory.AEStronglyMeasurable
          (fun x =>
            StationaryMFG.Theorems.SimplePower.Banach.mOf q x
              * DpH x (fun j =>
                  StationaryMFG.Theorems.SimplePower.Banach.DuOf q j x)
                  (StationaryMFG.Theorems.SimplePower.Banach.mOf q x) i)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    -- Signed family-member selectors and certificates.
    {g₁ g₂ : (Fin d → ℝ) → ℝ}
    (hg₁_lp : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) g₁)
    (hg₂_lp : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) g₂)
    -- Joint primal `Lᵝ`/nonneg certs (signed shape).
    (hmg₁_β : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal)
                (mLim + g₁))
    (hmg₂_β : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal)
                (mLim + g₂))
    (hjoint₁_nn : ∀ᵐ x ∂(MeasureTheory.Measure.restrict
                            MeasureTheory.volume (UnitCube (d := d))),
        0 ≤ (mLim + g₁) x)
    (hjoint₂_nn : ∀ᵐ x ∂(MeasureTheory.Measure.restrict
                            MeasureTheory.volume (UnitCube (d := d))),
        0 ≤ (mLim + g₂) x)
    -- Per-test-pair local args (paper-faithful per-test-pair, NOT auths).
    (η ν : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (hη : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) η)
    (hDν : ∀ i, Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dν i))
    (hν_β : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) ν)
    (_hν_γ : Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal) ν) :
    SignedFamilyNarrowSegInputsK0Min (d := d)
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal') (γBar := γBar)
      V H DpH hpow
      mLim uLim DuLim hmLim_memLp huLim_sob hDuLim_memLp_γ
      g₁ g₂ hg₁_lp hg₂_lp η ν Dν := by
  -- (1) Derive the eight (minimal) dominator certificates from paper
  -- hypotheses via the iter-0787 minimal closed signed dominators producer.
  -- No `hβ_ge_one` needed here — that side condition is gone exactly
  -- because the `bΔm1` slot is dropped.
  have hDom :=
    signedFamilyNarrowDominatorsK0Min_of_paperHypotheses
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal') (γBar := γBar)
      (H := H) (DpH := DpH)
      hpow hHat0 hAgree hβ.symm hγ.symm
      hβBar_eq hγBar_eq hβBar'_eq hγBar'_eq hγBar_id
      hmLim_memLp huLim_sob hDuLim_memLp_γ
      hmg₁_β hmg₂_β hjoint₁_nn hjoint₂_nn
  -- (2) Derive AE-strong-measurability of `mLim, uLim, DuLim, V, g_i,
  -- η, ν, Dν` from their `MemLpPer` certificates, then plug into the
  -- iter-0774 signed measurability producers.
  have hmLim_meas := hmLim_memLp.aestronglyMeasurable
  have huLim_meas := huLim_sob.1.aestronglyMeasurable
  have hDuLim_meas : ∀ i, MeasureTheory.AEStronglyMeasurable (DuLim i)
        (MeasureTheory.volume.restrict (UnitCube d)) :=
    fun i => (hDuLim_memLp_γ i).aestronglyMeasurable
  have hg₁_meas := hg₁_lp.aestronglyMeasurable
  have hg₂_meas := hg₂_lp.aestronglyMeasurable
  have hV_meas := hV.aestronglyMeasurable
  have hη_meas := hη.aestronglyMeasurable
  have hν_meas := hν_β.aestronglyMeasurable
  have hDν_meas : ∀ i, MeasureTheory.AEStronglyMeasurable (Dν i)
        (MeasureTheory.volume.restrict (UnitCube d)) :=
    fun i => (hDν i).aestronglyMeasurable
  have hF_unreg_meas_bare :=
    aepsiIntegrand_unreg_K0_meas_of_paperHypotheses_signed (d := d)
      (V := V) (H := H) (DpH := DpH)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      (g₁ := g₁) (g₂ := g₂) (η := η) (ν := ν) (Dν := Dν)
      hpow hHextCont
      hmLim_meas huLim_meas hDuLim_meas hg₁_meas hg₂_meas
      hV_meas hη_meas hν_meas hDν_meas
  have hF_gat_meas_bare :=
    aepsiIntegrand_gateaux_meas_of_paperHypotheses_signed (d := d) γBar
      (uLim := uLim) (DuLim := DuLim) (ν := ν) (Dν := Dν)
      huLim_meas hDuLim_meas hν_meas hDν_meas
  -- (3) K0-membership of the two lifted signed-family Banach pairs.
  -- The signed `jointNN` lemma expects the joint nonneg in the
  -- `fun x => mLim x + g x` form; convert from the `(mLim + g_i) x` form
  -- supplied by the caller.
  have hjoint₁_nn' :
      0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
              (UnitCube d)] (fun x => mLim x + g₁ x) := by
    refine hjoint₁_nn.mono ?_
    intro x hx
    simpa [Pi.add_apply] using hx
  have hjoint₂_nn' :
      0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
              (UnitCube d)] (fun x => mLim x + g₂ x) := by
    refine hjoint₂_nn.mono ?_
    intro x hx
    simpa [Pi.add_apply] using hx
  have hq₁_K0 :
      StationaryMFG.Theorems.SimplePower.Banach.bareToBanachPair_set_paper
          (d := d) (βBarReal := βBarReal) (γBarReal := γBarReal)
          (DuLim := DuLim)
          hmLim_memLp huLim_sob hDuLim_memLp_γ hg₁_lp
        ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi
            d βBarReal γBarReal :=
    StationaryMFG.Theorems.SimplePower.Banach.bareToBanachPair_set_paper_mem_K0Aepsi_jointNN
      (d := d) (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hg₁_lp hjoint₁_nn'
  have hq₂_K0 :
      StationaryMFG.Theorems.SimplePower.Banach.bareToBanachPair_set_paper
          (d := d) (βBarReal := βBarReal) (γBarReal := γBarReal)
          (DuLim := DuLim)
          hmLim_memLp huLim_sob hDuLim_memLp_γ hg₂_lp
        ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi
            d βBarReal γBarReal :=
    StationaryMFG.Theorems.SimplePower.Banach.bareToBanachPair_set_paper_mem_K0Aepsi_jointNN
      (d := d) (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hg₂_lp hjoint₂_nn'
  -- (4) Specialise the universal-`q` K0 aux-hyps producer at each lifted pair.
  have aux₁ :=
    StationaryMFG.Theorems.SimplePower.Banach.paperSection8_auxHypsK0_of_paperHypotheses
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      (V := V) (H := H) (DpH := DpH)
      hmon hpow hHat0 hAgree hV hExp
      hβBar_eq hγBar_eq hβBar'_eq hγBar'_eq
      hβ hγ hβTop hγ'_le_β hF_HJB_meas hF_flux_meas
      _ hq₁_K0
  have aux₂ :=
    StationaryMFG.Theorems.SimplePower.Banach.paperSection8_auxHypsK0_of_paperHypotheses
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      (V := V) (H := H) (DpH := DpH)
      hmon hpow hHat0 hAgree hV hExp
      hβBar_eq hγBar_eq hβBar'_eq hγBar'_eq
      hβ hγ hβTop hγ'_le_β hF_HJB_meas hF_flux_meas
      _ hq₂_K0
  -- (5) Assemble the minimal record. Eight dominator fields come from
  -- `hDom` (iter-0787 minimal closed signed producer); the two
  -- measurabilities from the iter-0774 signed aliases. No `bΔm1` field.
  exact
    { aux₁ := aux₁
      aux₂ := aux₂
      bΔυ := hDom.bΔυ
      bΔp_pow := hDom.bΔp_pow
      bΔm_pow := hDom.bΔm_pow
      bΔm_grad := hDom.bΔm_grad
      bΔm_endpoint := hDom.bΔm_endpoint
      bΔm := hDom.bΔm
      bG_grad := hDom.bG_grad
      bG_val := hDom.bG_val
      hF_unreg_meas_bare := hF_unreg_meas_bare
      hF_gat_meas_bare := hF_gat_meas_bare }

/-! ### K0 minimal-shape transport-family per-pair seg-inputs record and
closed producer (`infra-P6-K0-min-closed-segInputsK0-transport`,
audit 2026-05-22).

Transport mirror of `SetFamilyNarrowSegInputsK0Min` /
`setFamilyNarrowSegInputsK0_closed_min_of_paperHypotheses` (iter-0792) and
`SignedFamilyNarrowSegInputsK0Min` /
`signedFamilyNarrowSegInputsK0_closed_min_of_paperHypotheses` (iter-0793,
just above) using the iter-0791 minimal-shape K0 transport composer
`hemicontSegmentData_transport_narrow_K0_min_of_paperHypotheses` as the
downstream consumer. Differences from the iter-0781 closed transport
producer:

- drops the over-specified `bΔm1` dominator field;
- with it, drops the non-paper-faithful side condition `1 ≤ hpow.β` from
  the signature;
- swaps the iter-0779 closed transport dominators producer for the
  iter-0788 minimal sibling
  `transportFamilyNarrowDominatorsK0Min_of_paperHypotheses`;
- outputs `TransportFamilyNarrowSegInputsK0Min` in place of
  `TransportFamilyNarrowSegInputsK0`. -/

/-- **K0 minimal-shape sibling of `TransportFamilyNarrowSegInputsK0`.**

Per-test-pair segment-data inputs for the K0 minimal-shape transport-family
composer `hemicontSegmentData_transport_narrow_K0_min_of_paperHypotheses`.
Eight dominator certificates (drops the `bΔm1` over-specification), two
`MFGOpEpsAuxHyps` certificates at the two lifted transport-perturbed Banach
pairs, and two Carathéodory measurabilities at the bare
transport-perturbed endpoints `(mLim, uLim + ψᵢ, DuLim + ∂ψᵢ)`. Transport
mirror of `SetFamilyNarrowSegInputsK0Min` / `SignedFamilyNarrowSegInputsK0Min`. -/
structure TransportFamilyNarrowSegInputsK0Min
    {d : ℕ} {γBarReal βBarReal βBarReal' γBarReal' γBar : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    (hmLim_memLp : Periodic.MemLpPer (d := d)
                      (ENNReal.ofReal βBarReal) mLim)
    (huLim_sob : Periodic.MemSobolevPer (d := d)
                      (ENNReal.ofReal γBarReal) uLim)
    (hDuLim_memLp_γ : ∀ i, Periodic.MemLpPer (d := d)
                              (ENNReal.ofReal γBarReal) (DuLim i))
    (ψ₁ ψ₂ : Periodic.SmoothPeriodic d)
    (η ν : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    : Type where
  /-- Primal `MFGOpEpsAuxHyps` certificate at the first lifted Banach pair. -/
  aux₁ : StationaryMFG.Theorems.SimplePower.Banach.MFGOpEpsAuxHyps
            (d := d) γBarReal βBarReal βBarReal' γBarReal' V H DpH
            (StationaryMFG.Theorems.SimplePower.Banach.DuOf
              (StationaryMFG.Theorems.SimplePower.Banach.bareToBanachPair_transport_paper
                (d := d) (βBarReal := βBarReal) (γBarReal := γBarReal)
                (DuLim := DuLim)
                hmLim_memLp huLim_sob hDuLim_memLp_γ ψ₁))
            (StationaryMFG.Theorems.SimplePower.Banach.mOf
              (StationaryMFG.Theorems.SimplePower.Banach.bareToBanachPair_transport_paper
                (d := d) (βBarReal := βBarReal) (γBarReal := γBarReal)
                (DuLim := DuLim)
                hmLim_memLp huLim_sob hDuLim_memLp_γ ψ₁))
            (StationaryMFG.Theorems.SimplePower.Banach.uOf
              (StationaryMFG.Theorems.SimplePower.Banach.bareToBanachPair_transport_paper
                (d := d) (βBarReal := βBarReal) (γBarReal := γBarReal)
                (DuLim := DuLim)
                hmLim_memLp huLim_sob hDuLim_memLp_γ ψ₁))
  /-- Primal `MFGOpEpsAuxHyps` at the second lifted Banach pair. -/
  aux₂ : StationaryMFG.Theorems.SimplePower.Banach.MFGOpEpsAuxHyps
            (d := d) γBarReal βBarReal βBarReal' γBarReal' V H DpH
            (StationaryMFG.Theorems.SimplePower.Banach.DuOf
              (StationaryMFG.Theorems.SimplePower.Banach.bareToBanachPair_transport_paper
                (d := d) (βBarReal := βBarReal) (γBarReal := γBarReal)
                (DuLim := DuLim)
                hmLim_memLp huLim_sob hDuLim_memLp_γ ψ₂))
            (StationaryMFG.Theorems.SimplePower.Banach.mOf
              (StationaryMFG.Theorems.SimplePower.Banach.bareToBanachPair_transport_paper
                (d := d) (βBarReal := βBarReal) (γBarReal := γBarReal)
                (DuLim := DuLim)
                hmLim_memLp huLim_sob hDuLim_memLp_γ ψ₂))
            (StationaryMFG.Theorems.SimplePower.Banach.uOf
              (StationaryMFG.Theorems.SimplePower.Banach.bareToBanachPair_transport_paper
                (d := d) (βBarReal := βBarReal) (γBarReal := γBarReal)
                (DuLim := DuLim)
                hmLim_memLp huLim_sob hDuLim_memLp_γ ψ₂))
  /-- Dominator cert: `|uLim + ψ₂| + |uLim + ψ₁| ∈ Lᵝ'`. -/
  bΔυ : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal')
            (fun x => |(uLim + (ψ₂ : (Fin d → ℝ) → ℝ)) x|
                        + |(uLim + (ψ₁ : (Fin d → ℝ) → ℝ)) x|)
  /-- Dominator cert for the gradient `α`-power. -/
  bΔp_pow : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal')
            (fun x =>
              ‖fun i =>
                  |(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₂
                                : (Fin d → ℝ) → ℝ)) x|
                + |(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₁
                                : (Fin d → ℝ) → ℝ)) x|‖ ^ hpow.α + 1)
  /-- Dominator cert for the density `β`-power (transport: primal at `mLim`). -/
  bΔm_pow : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal')
            (fun x => (|mLim x| + |mLim x|) ^ hpow.β + 1)
  /-- Dominator cert for the gradient cross-term. -/
  bΔm_grad : Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
            (fun x => (|mLim x| + |mLim x|)
                * ‖fun i =>
                    |(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₂
                                  : (Fin d → ℝ) → ℝ)) x|
                  + |(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₁
                                  : (Fin d → ℝ) → ℝ)) x|‖ ^ (hpow.α - 1))
  /-- Dominator cert for the endpoint exponent. -/
  bΔm_endpoint : Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
            (fun x => (|mLim x| + |mLim x|) ^ (1 + hpow.β - hpow.β / hpow.α))
  /-- Dominator cert for the bare density. -/
  bΔm : Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
            (fun x => |mLim x| + |mLim x|)
  -- NB: NO `bΔm1` field — its removal is the entire point of this
  -- minimal-shape transport sibling; it is what removes the
  -- `hβ_ge_one` side condition from the closed dominators producer.
  /-- Dominator cert for the Gateaux gradient block. -/
  bG_grad : Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
            (fun x =>
              (∑ i,
                  (|(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₂
                                  : (Fin d → ℝ) → ℝ)) x|
                    + |(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₁
                                  : (Fin d → ℝ) → ℝ)) x|) ^ (2 : ℕ))
                  ^ ((γBar - 1) / 2))
  /-- Dominator cert for the Gateaux value block. -/
  bG_val : Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
            (fun x => (|(uLim + (ψ₂ : (Fin d → ℝ) → ℝ)) x|
                        + |(uLim + (ψ₁ : (Fin d → ℝ) → ℝ)) x|)
                        ^ (γBar - 1))
  /-- Caratheodory measurability of the **K0** unregularised integrand
  at the bare transport-perturbed endpoints. -/
  hF_unreg_meas_bare :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x =>
          StationaryMFG.Theorems.SimplePower.aepsiIntegrandAt_unreg_K0
            V H DpH
            (fun i => DuLim i + (Periodic.SmoothPeriodic.partialDeriv
                                    i ψ₁ : (Fin d → ℝ) → ℝ))
            (fun i => DuLim i + (Periodic.SmoothPeriodic.partialDeriv
                                    i ψ₂ : (Fin d → ℝ) → ℝ))
            mLim mLim
            (uLim + (ψ₁ : (Fin d → ℝ) → ℝ))
            (uLim + (ψ₂ : (Fin d → ℝ) → ℝ))
            Dν η ν x t)
        (MeasureTheory.volume.restrict (UnitCube d))
  /-- Caratheodory measurability of the Gateaux integrand at the bare
  transport-perturbed endpoints. -/
  hF_gat_meas_bare :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x =>
          StationaryMFG.Theorems.SimplePower.aepsiIntegrandAt_gateaux
            γBar
            (fun i => DuLim i + (Periodic.SmoothPeriodic.partialDeriv
                                    i ψ₁ : (Fin d → ℝ) → ℝ))
            (fun i => DuLim i + (Periodic.SmoothPeriodic.partialDeriv
                                    i ψ₂ : (Fin d → ℝ) → ℝ))
            (uLim + (ψ₁ : (Fin d → ℝ) → ℝ))
            (uLim + (ψ₂ : (Fin d → ℝ) → ℝ))
            Dν ν x t)
        (MeasureTheory.volume.restrict (UnitCube d))

/-- **Closed paper-faithful producer for the K0 minimal-shape transport-family
per-pair record** (`infra-P6-K0-min-closed-segInputsK0-transport`,
2026-05-22).

Transport sibling of `setFamilyNarrowSegInputsK0_closed_min_of_paperHypotheses`
(iter-0792) and `signedFamilyNarrowSegInputsK0_closed_min_of_paperHypotheses`
(iter-0793, just above), minimal-shape sibling of
`transportFamilyNarrowSegInputsK0_closed_of_paperHypotheses` (iter-0781).
Identical pipeline to the latter except:
- swaps the iter-0779 closed transport dominators producer for the
  iter-0788 minimal sibling
  `transportFamilyNarrowDominatorsK0Min_of_paperHypotheses` (no `bΔm1`,
  no `hβ_ge_one`);
- outputs `TransportFamilyNarrowSegInputsK0Min` instead of
  `TransportFamilyNarrowSegInputsK0`.

Signature drops `hβ_ge_one` — this producer is the entire purpose of the
minimal-shape transport refactor. The two `MFGOpEpsAuxHyps` certificates
come from the unchanged paper-Section-8 K0 aux-hyps producer
`paperSection8_auxHypsK0_of_paperHypotheses` at the lifted Banach pairs
(K0 membership via `bareToBanachPair_transport_paper_mem_K0Aepsi`); the
two Carathéodory measurabilities come from the iter-0780 transport
measurability aliases. -/
noncomputable def transportFamilyNarrowSegInputsK0_closed_min_of_paperHypotheses
    {d : ℕ} {γBarReal βBarReal βBarReal' γBarReal' γBar : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    -- Paper-side Hamiltonian hypotheses.
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hHextCont : Hamiltonian.HypothesisHextJointCont (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    (hV : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (hExp :
      StationaryMFG.Theorems.SimplePower.SimplePowerExponentFacts
        γBarReal (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
        (ENNReal.ofReal βBarReal'))
    -- Paper-exponent identification residues.
    (hβBar_eq : βBarReal = hpow.β + 1)
    (hγBar_eq : γBarReal = hpow.α * (hpow.β + 1) / hpow.β)
    (hβBar'_eq : βBarReal' = (hpow.β + 1) / hpow.β)
    (hγBar'_eq : γBarReal' = γBarReal / (γBarReal - 1))
    -- Hölder-pair residues.
    (hβ : βBarReal.HolderConjugate βBarReal')
    (hγ : γBarReal.HolderConjugate γBarReal')
    (hβTop : ENNReal.ofReal γBarReal ≠ ⊤)
    (hγ'_le_β : ENNReal.ofReal γBarReal' ≤ ENNReal.ofReal βBarReal)
    -- Gateaux-parameter identification residue.
    (hγBar_id : γBar = γBarReal)
    -- Weak-limit triple.
    {mLim uLim : (Fin d → ℝ) → ℝ}
    {DuLim : Fin d → (Fin d → ℝ) → ℝ}
    (hmLim_memLp : Periodic.MemLpPer (d := d)
                      (ENNReal.ofReal βBarReal) mLim)
    (huLim_sob : Periodic.MemSobolevPer (d := d)
                      (ENNReal.ofReal γBarReal) uLim)
    (hDuLim_memLp_γ : ∀ i, Periodic.MemLpPer (d := d)
                              (ENNReal.ofReal γBarReal) (DuLim i))
    (hmLim_nn : 0 ≤ᵐ[MeasureTheory.Measure.restrict
                      MeasureTheory.volume (UnitCube d)] mLim)
    -- Universal-`q` measurability witnesses for the aux-hyps producer.
    (hF_HJB_meas :
      ∀ q : StationaryMFG.Theorems.SimplePower.Banach.XBanach
              d βBarReal γBarReal,
        MeasureTheory.AEStronglyMeasurable
          (fun x =>
            -(StationaryMFG.Theorems.SimplePower.Banach.uOf q x)
              - H x (fun i =>
                  StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
                  (StationaryMFG.Theorems.SimplePower.Banach.mOf q x) + V x)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (hF_flux_meas :
      ∀ q : StationaryMFG.Theorems.SimplePower.Banach.XBanach
              d βBarReal γBarReal, ∀ i,
        MeasureTheory.AEStronglyMeasurable
          (fun x =>
            StationaryMFG.Theorems.SimplePower.Banach.mOf q x
              * DpH x (fun j =>
                  StationaryMFG.Theorems.SimplePower.Banach.DuOf q j x)
                  (StationaryMFG.Theorems.SimplePower.Banach.mOf q x) i)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    -- Transport test-direction selectors (smooth periodic perturbations).
    (ψ₁ ψ₂ : Periodic.SmoothPeriodic d)
    -- Per-test-pair local args (paper-faithful per-test-pair, NOT auths).
    (η ν : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (hη : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) η)
    (hDν : ∀ i, Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dν i))
    (hν_β : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) ν)
    (_hν_γ : Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal) ν) :
    TransportFamilyNarrowSegInputsK0Min (d := d)
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal') (γBar := γBar)
      V H DpH hpow
      mLim uLim DuLim hmLim_memLp huLim_sob hDuLim_memLp_γ
      ψ₁ ψ₂ η ν Dν := by
  -- (1) Derive the eight (minimal) dominator certificates from paper
  -- hypotheses via the iter-0788 minimal closed transport dominators
  -- producer. No `hβ_ge_one` needed here — that side condition is gone
  -- exactly because the `bΔm1` slot is dropped.
  have hDom :=
    transportFamilyNarrowDominatorsK0Min_of_paperHypotheses
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal') (γBar := γBar)
      (H := H) (DpH := DpH)
      hpow hHat0 hAgree hβ.symm hγ.symm
      hβBar_eq hγBar_eq hβBar'_eq hγBar'_eq hγBar_id
      hmLim_memLp huLim_sob hDuLim_memLp_γ
      ψ₁ ψ₂
  -- (2) Derive AE-strong-measurability from the `MemLpPer` certificates,
  -- then plug into the iter-0780 transport measurability aliases.
  have hmLim_meas := hmLim_memLp.aestronglyMeasurable
  have huLim_meas := huLim_sob.1.aestronglyMeasurable
  have hDuLim_meas : ∀ i, MeasureTheory.AEStronglyMeasurable (DuLim i)
        (MeasureTheory.volume.restrict (UnitCube d)) :=
    fun i => (hDuLim_memLp_γ i).aestronglyMeasurable
  have hV_meas := hV.aestronglyMeasurable
  have hη_meas := hη.aestronglyMeasurable
  have hν_meas := hν_β.aestronglyMeasurable
  have hDν_meas : ∀ i, MeasureTheory.AEStronglyMeasurable (Dν i)
        (MeasureTheory.volume.restrict (UnitCube d)) :=
    fun i => (hDν i).aestronglyMeasurable
  have hF_unreg_meas_bare :=
    aepsiIntegrand_unreg_K0_meas_of_paperHypotheses_transport (d := d)
      (V := V) (H := H) (DpH := DpH)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      (η := η) (ν := ν) (Dν := Dν)
      hpow hHextCont
      hmLim_meas huLim_meas hDuLim_meas
      ψ₁ ψ₂
      hV_meas hη_meas hν_meas hDν_meas
  have hF_gat_meas_bare :=
    aepsiIntegrand_gateaux_meas_of_paperHypotheses_transport (d := d) γBar
      (uLim := uLim) (DuLim := DuLim) (ν := ν) (Dν := Dν)
      huLim_meas hDuLim_meas ψ₁ ψ₂ hν_meas hDν_meas
  -- (3) K0-membership of the two lifted transport-family Banach pairs.
  have hq₁_K0 :
      StationaryMFG.Theorems.SimplePower.Banach.bareToBanachPair_transport_paper
          (d := d) (βBarReal := βBarReal) (γBarReal := γBarReal)
          (DuLim := DuLim)
          hmLim_memLp huLim_sob hDuLim_memLp_γ ψ₁
        ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi
            d βBarReal γBarReal :=
    StationaryMFG.Theorems.SimplePower.Banach.bareToBanachPair_transport_paper_mem_K0Aepsi
      (d := d) (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hmLim_nn ψ₁
  have hq₂_K0 :
      StationaryMFG.Theorems.SimplePower.Banach.bareToBanachPair_transport_paper
          (d := d) (βBarReal := βBarReal) (γBarReal := γBarReal)
          (DuLim := DuLim)
          hmLim_memLp huLim_sob hDuLim_memLp_γ ψ₂
        ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi
            d βBarReal γBarReal :=
    StationaryMFG.Theorems.SimplePower.Banach.bareToBanachPair_transport_paper_mem_K0Aepsi
      (d := d) (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hmLim_nn ψ₂
  -- (4) Specialise the universal-`q` K0 aux-hyps producer at each lifted pair.
  have aux₁ :=
    StationaryMFG.Theorems.SimplePower.Banach.paperSection8_auxHypsK0_of_paperHypotheses
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      (V := V) (H := H) (DpH := DpH)
      hmon hpow hHat0 hAgree hV hExp
      hβBar_eq hγBar_eq hβBar'_eq hγBar'_eq
      hβ hγ hβTop hγ'_le_β hF_HJB_meas hF_flux_meas
      _ hq₁_K0
  have aux₂ :=
    StationaryMFG.Theorems.SimplePower.Banach.paperSection8_auxHypsK0_of_paperHypotheses
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      (V := V) (H := H) (DpH := DpH)
      hmon hpow hHat0 hAgree hV hExp
      hβBar_eq hγBar_eq hβBar'_eq hγBar'_eq
      hβ hγ hβTop hγ'_le_β hF_HJB_meas hF_flux_meas
      _ hq₂_K0
  -- (5) Assemble the minimal record. Eight dominator fields come from
  -- `hDom` (iter-0788 minimal closed transport producer); the two
  -- measurabilities from the iter-0780 transport aliases. No `bΔm1` field.
  exact
    { aux₁ := aux₁
      aux₂ := aux₂
      bΔυ := hDom.bΔυ
      bΔp_pow := hDom.bΔp_pow
      bΔm_pow := hDom.bΔm_pow
      bΔm_grad := hDom.bΔm_grad
      bΔm_endpoint := hDom.bΔm_endpoint
      bΔm := hDom.bΔm
      bG_grad := hDom.bG_grad
      bG_val := hDom.bG_val
      hF_unreg_meas_bare := hF_unreg_meas_bare
      hF_gat_meas_bare := hF_gat_meas_bare }

/-! ### K0 minimal-shape residue types
(`infra-P6-K0-min-residue-types`, 2026-05-22)

K0 minimal-shape siblings of the three `*FamilyNarrowMintyResidueK0`
structures (lines 2157 / 2741 / 3384). Each is a field-by-field copy of
its non-Min K0 sibling with the `segInputsOf` field's return type swapped
from `*FamilyNarrowSegInputsK0` to `*FamilyNarrowSegInputsK0Min`. The
structural purpose is to feed the iter-0786 / 0787 / 0788 minimal-shape
K0 dominators producers (no `bΔm1`, no `hβ_ge_one`) into the consumer's
K0 producer chain.

No producer at this stage; producers are filled later by the consumer
in `T10PaperResidues.of_paperHypotheses` (first child of iter-0795 split). -/

/-- **K0 minimal-shape sibling of `SetFamilyNarrowMintyResidueK0`.**

Field-by-field copy of `SetFamilyNarrowMintyResidueK0` with the
`segInputsOf` return type swapped from `SetFamilyNarrowSegInputsK0` to
`SetFamilyNarrowSegInputsK0Min`. The other scalar fields (`hHat0`,
`hAgree`, `hβconj`, `hγconj`, `hγ_one_lt`, `hγBar_eq`, `hV_conj`,
`ρ₁_nn`) are unchanged. -/
structure SetFamilyNarrowMintyResidueK0Min
    {d : ℕ} {γBarReal βBarReal βBarReal' γBarReal' γBar : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (wkBundle : StationaryMFG.Theorems.SimplePower.Banach.WeakLimitInputBundleAE
                  (d := d) γBarReal βBarReal) where
  /-- Paper-Hamiltonian residue: `H` is finite at zero density. -/
  hHat0 : Hamiltonian.HypothesisHat0 (d := d) H
  /-- Paper-Hamiltonian residue: `H` agrees with `Hext` at zero density. -/
  hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H
  /-- Hölder-conjugacy of the `β`-exponent pair. -/
  hβconj : βBarReal'.HolderConjugate βBarReal
  /-- Hölder-conjugacy of the `γ`-exponent pair. -/
  hγconj : γBarReal'.HolderConjugate γBarReal
  /-- Strict lower bound `1 < γBar`. -/
  hγ_one_lt : 1 < γBar
  /-- Identification of the chosen Gateaux exponent with `γBarReal`. -/
  hγBar_eq : γBar = γBarReal
  /-- `V`-regularity at the conjugate exponent. -/
  hV_conj : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal') V
  /-- Per-test-pair K0 **minimal-shape** segment-data record. Mirror of
  `SetFamilyNarrowMintyResidueK0.segInputsOf` with the return type swapped
  to `SetFamilyNarrowSegInputsK0Min`. -/
  segInputsOf :
    ∀ ⦃μBar ῡ : (Fin d → ℝ) → ℝ⦄ ⦃Dῡ : Fin d → (Fin d → ℝ) → ℝ⦄
      (hBar : (μBar, ῡ, Dῡ) ∈
        StationaryMFG.Theorems.SimplePower.Banach.D_set_family_paper
          (d := d) (ENNReal.ofReal βBarReal)
          wkBundle.mLim wkBundle.uLim wkBundle.DuLim),
    ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄ ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄
      (hμ : (μ, υ, Dυ) ∈
        StationaryMFG.Theorems.SimplePower.Banach.D_set_family_paper
          (d := d) (ENNReal.ofReal βBarReal)
          wkBundle.mLim wkBundle.uLim wkBundle.DuLim),
    ∀ (η ν : (Fin d → ℝ) → ℝ) (Dν : Fin d → (Fin d → ℝ) → ℝ)
      (_hη : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) η)
      (_hDν : ∀ i, Periodic.MemLpPer (d := d)
                      (ENNReal.ofReal γBarReal) (Dν i))
      (_hν_β : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) ν)
      (_hν_γ : Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal) ν),
      SetFamilyNarrowSegInputsK0Min (d := d)
        (γBarReal := γBarReal) (βBarReal := βBarReal)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal') (γBar := γBar)
        V H DpH hpow
        wkBundle.mLim wkBundle.uLim wkBundle.DuLim
        wkBundle.hmLim_memLp wkBundle.huLim_sob
        (fun i => wkBundle.hDuLim_memLp_γ i)
        (Classical.choose hμ) (Classical.choose hBar)
        (Classical.choose_spec hμ).2.1
        (Classical.choose_spec hBar).2.1
        η ν Dν
  /-- The first perturbation is pointwise nonneg
  (extracted from membership; surfaced for the K0 producer). -/
  ρ₁_nn :
    ∀ ⦃μBar ῡ : (Fin d → ℝ) → ℝ⦄ ⦃Dῡ : Fin d → (Fin d → ℝ) → ℝ⦄
      (hBar : (μBar, ῡ, Dῡ) ∈
        StationaryMFG.Theorems.SimplePower.Banach.D_set_family_paper
          (d := d) (ENNReal.ofReal βBarReal)
          wkBundle.mLim wkBundle.uLim wkBundle.DuLim),
    ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄ ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄
      (hμ : (μ, υ, Dυ) ∈
        StationaryMFG.Theorems.SimplePower.Banach.D_set_family_paper
          (d := d) (ENNReal.ofReal βBarReal)
          wkBundle.mLim wkBundle.uLim wkBundle.DuLim),
    ∀ x, 0 ≤ Classical.choose hμ x

/-- **K0 minimal-shape sibling of `SignedFamilyNarrowMintyResidueK0`.**

Field-by-field copy of `SignedFamilyNarrowMintyResidueK0` with the
`segInputsOf` return type swapped from `SignedFamilyNarrowSegInputsK0` to
`SignedFamilyNarrowSegInputsK0Min`. The other scalar fields (`hHat0`,
`hAgree`, `hβconj`, `hγconj`, `hγ_one_lt`, `hγBar_eq`, `hV_conj`) are
unchanged. -/
structure SignedFamilyNarrowMintyResidueK0Min
    {d : ℕ} {γBarReal βBarReal βBarReal' γBarReal' γBar : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (wkBundle : StationaryMFG.Theorems.SimplePower.Banach.WeakLimitInputBundleAE
                  (d := d) γBarReal βBarReal) where
  /-- Paper-Hamiltonian residue: `H` is finite at zero density. -/
  hHat0 : Hamiltonian.HypothesisHat0 (d := d) H
  /-- Paper-Hamiltonian residue: `H` agrees with `Hext` at zero density. -/
  hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H
  /-- Hölder-conjugacy of the `β`-exponent pair. -/
  hβconj : βBarReal'.HolderConjugate βBarReal
  /-- Hölder-conjugacy of the `γ`-exponent pair. -/
  hγconj : γBarReal'.HolderConjugate γBarReal
  /-- Strict lower bound `1 < γBar`. -/
  hγ_one_lt : 1 < γBar
  /-- Identification of the chosen Gateaux exponent with `γBarReal`. -/
  hγBar_eq : γBar = γBarReal
  /-- `V`-regularity at the conjugate exponent. -/
  hV_conj : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal') V
  /-- Per-test-pair K0 **minimal-shape** signed segment-data record.
  Mirror of `SignedFamilyNarrowMintyResidueK0.segInputsOf` with the return
  type swapped to `SignedFamilyNarrowSegInputsK0Min`. -/
  segInputsOf :
    ∀ ⦃μBar ῡ : (Fin d → ℝ) → ℝ⦄ ⦃Dῡ : Fin d → (Fin d → ℝ) → ℝ⦄
      (hBar : (μBar, ῡ, Dῡ) ∈
        StationaryMFG.Theorems.SimplePower.Banach.D_signed_family_paper_nn
          (d := d) (ENNReal.ofReal βBarReal)
          wkBundle.mLim wkBundle.uLim wkBundle.DuLim),
    ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄ ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄
      (hμ : (μ, υ, Dυ) ∈
        StationaryMFG.Theorems.SimplePower.Banach.D_signed_family_paper_nn
          (d := d) (ENNReal.ofReal βBarReal)
          wkBundle.mLim wkBundle.uLim wkBundle.DuLim),
    ∀ (η ν : (Fin d → ℝ) → ℝ) (Dν : Fin d → (Fin d → ℝ) → ℝ)
      (_hη : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) η)
      (_hDν : ∀ i, Periodic.MemLpPer (d := d)
                      (ENNReal.ofReal γBarReal) (Dν i))
      (_hν_β : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) ν)
      (_hν_γ : Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal) ν),
      SignedFamilyNarrowSegInputsK0Min (d := d)
        (γBarReal := γBarReal) (βBarReal := βBarReal)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal') (γBar := γBar)
        V H DpH hpow
        wkBundle.mLim wkBundle.uLim wkBundle.DuLim
        wkBundle.hmLim_memLp wkBundle.huLim_sob
        (fun i => wkBundle.hDuLim_memLp_γ i)
        (Classical.choose hμ) (Classical.choose hBar)
        (Classical.choose_spec hμ).1
        (Classical.choose_spec hBar).1
        η ν Dν

/-- **K0 minimal-shape sibling of `TransportFamilyNarrowMintyResidueK0`.**

Field-by-field copy of `TransportFamilyNarrowMintyResidueK0` with the
`segInputsOf` return type swapped from `TransportFamilyNarrowSegInputsK0`
to `TransportFamilyNarrowSegInputsK0Min`. The other scalar fields
(`hHat0`, `hAgree`, `hβconj`, `hγconj`, `hγ_one_lt`, `hγBar_eq`,
`hV_conj`, `hmLim_nn`) are unchanged. -/
structure TransportFamilyNarrowMintyResidueK0Min
    {d : ℕ} {γBarReal βBarReal βBarReal' γBarReal' γBar : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (wkBundle : StationaryMFG.Theorems.SimplePower.Banach.WeakLimitInputBundleAE
                  (d := d) γBarReal βBarReal) where
  /-- Paper-Hamiltonian residue: `H` is finite at zero density. -/
  hHat0 : Hamiltonian.HypothesisHat0 (d := d) H
  /-- Paper-Hamiltonian residue: `H` agrees with `Hext` at zero density. -/
  hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H
  /-- Hölder-conjugacy of the `β`-exponent pair. -/
  hβconj : βBarReal'.HolderConjugate βBarReal
  /-- Hölder-conjugacy of the `γ`-exponent pair. -/
  hγconj : γBarReal'.HolderConjugate γBarReal
  /-- Strict lower bound `1 < γBar`. -/
  hγ_one_lt : 1 < γBar
  /-- Identification of the chosen Gateaux exponent with `γBarReal`. -/
  hγBar_eq : γBar = γBarReal
  /-- `V`-regularity at the conjugate exponent. -/
  hV_conj : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal') V
  /-- A.e.-nonneg of the primal `wkBundle.mLim`. The transport lift's
  K0-membership discharge consumes this single certificate (no per-pair
  primal-side nonneg, since the primal stays fixed at `mLim`). -/
  hmLim_nn : 0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                    (UnitCube d)] wkBundle.mLim
  /-- Per-test-pair K0 **minimal-shape** transport segment-data record.
  Mirror of `TransportFamilyNarrowMintyResidueK0.segInputsOf` with the
  return type swapped to `TransportFamilyNarrowSegInputsK0Min`. -/
  segInputsOf :
    ∀ ⦃μBar ῡ : (Fin d → ℝ) → ℝ⦄ ⦃Dῡ : Fin d → (Fin d → ℝ) → ℝ⦄
      (hBar : (μBar, ῡ, Dῡ) ∈
        StationaryMFG.Theorems.SimplePower.Banach.D_transport_family_paper
          (d := d) wkBundle.mLim wkBundle.uLim wkBundle.DuLim),
    ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄ ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄
      (hμ : (μ, υ, Dυ) ∈
        StationaryMFG.Theorems.SimplePower.Banach.D_transport_family_paper
          (d := d) wkBundle.mLim wkBundle.uLim wkBundle.DuLim),
    ∀ (η ν : (Fin d → ℝ) → ℝ) (Dν : Fin d → (Fin d → ℝ) → ℝ)
      (_hη : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) η)
      (_hDν : ∀ i, Periodic.MemLpPer (d := d)
                      (ENNReal.ofReal γBarReal) (Dν i))
      (_hν_β : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) ν)
      (_hν_γ : Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal) ν),
      TransportFamilyNarrowSegInputsK0Min (d := d)
        (γBarReal := γBarReal) (βBarReal := βBarReal)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal') (γBar := γBar)
        V H DpH hpow
        wkBundle.mLim wkBundle.uLim wkBundle.DuLim
        wkBundle.hmLim_memLp wkBundle.huLim_sob
        (fun i => wkBundle.hDuLim_memLp_γ i)
        (Classical.choose hμ) (Classical.choose hBar)
        η ν Dν
/-- **Aggregated paper-residue bundle for Theorem 1's Banach-bridge chain.**

Per CONVENTIONS §1b/§8 (Option (b) bundling), the closed-form
producer chain of `simplePowerThinChain_of_paperHypotheses`
threads the four primary paper hypotheses
`(hmon, hpow, hV, hExp)` through eight closed-form aggregators
(`aepsiUniformContextK_of_paperHypotheses_closed`,
`regularizedSequenceData_of_paperHypotheses`,
`weakLimitInputBundle_of_paperHypotheses`,
`mintyClosureSelector_of_paperHypotheses`,
`mintyClosure_of_paperHypotheses`,
`limitPairingSelector_of_paperHypotheses`,
`limitPairingInputs_of_regularizedSequence`,
`finalIntegrabilityBundle_of_paperHypotheses`,
`limitSolutionData_of_regularizedSequence`,
`H4SimplePowerInputs_of_LimitSolutionData`).

Each closed-form aggregator absorbs the closed-form-derivable content
from `(hmon, hpow, hV, hExp)`, but each one also requires a residual
bundle of paper-§8 analytic / Path-A selector inputs (filed as
follow-up tasks in `backlog/`). Here we aggregate those residues —
which are pinned to the same `(βBarReal, γBarReal, βBarReal', γBarReal')`
exponent quadruple as the four paper hypotheses — into a single
authorised parameter, keeping Theorem 1's public contract clean. -/
structure T10PaperResidues
    {d : ℕ}
    (γBarReal βBarReal βBarReal' γBarReal' : ℝ)
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH) where
  -- **Phase 2b T10 shrink.** The ε-uniform apriori bound's residue
  -- scaffold is now the per-`k` C-class bundle + 4 authorised B-class
  -- inputs (iter `infra-P5-T10-v7-HMinty-3-rewire-and-drain`: 5 → 4
  -- after draining the Minty / hemicontinuity-upgrade limit
  -- authorisation `h_minty_limit_auth` via the 4-step HMinty plan
  -- (HMinty-0 audit, HMinty-1 subseq+WeakLimitSubsequenceData,
  -- HMinty-2 ExtractedWeakPairingData producer, HMinty-3 rewire and
  -- drain — this iteration); prior iter
  -- `infra-P5-T10-v7-HMpos-4-bridge-and-drain`: 6 → 5 after draining
  -- the strict-positivity authorisation `paperHMposAuth` via the
  -- 5-step HMpos plan; prior iter
  -- `infra-P5-T10-v7-phase4-hmu-posAuth-drain`: 9 → 6 after draining
  -- `hμ_posAuth_{set,signed,transport}` via the strict→nonneg
  -- consumer migration; prior iter
  -- `infra-P5-T10-v7-phase2c-delta-paperCBundleFor-of-paperHypotheses`
  -- went 10 → 9 by draining `paperCBundleFor`). The full
  -- `AprioriUniformResidueInputs`
  -- is assembled in-body
  -- of `simplePowerThinChain_of_paperHypotheses` via the iter-400
  -- closed-paper producer
  -- `aprioriUniformResidueInputs_of_paperHypotheses_closedPaper`.
  --
  -- Per `infra-P5-theorem1-phase-2b-T10-aprioriResidue-shrink`, this
  -- splits the residue into:
  -- * `epsSeq`/`epsSeq_pos`/`epsSeq_tendsto` — regularisation sequence;
  -- * `sol` — per-`k` `RegularizedBareSolution` at paper-form exponents
  --   `(gammaBar hpow.α hpow.β, hpow.β + 1, βBarReal', γBarReal')`;
  -- * `cBundles` — per-`k` C-class bundle;
  -- * 4 per-`k` B-class authorised inputs feeding
  --   `AprioriUniformPerSolHypotheses.fromCAndAuthorised`.
  /-- Regularisation parameters. -/
  epsSeq : ℕ → ℝ
  /-- Strict positivity of each `epsSeq k`. -/
  epsSeq_pos : ∀ k, 0 < epsSeq k
  /-- Convergence of `epsSeq → 0`. -/
  epsSeq_tendsto : Filter.Tendsto epsSeq Filter.atTop (nhds 0)
  -- **Phase 1 sub-task 1b (v7 plan)** — the V-bound triple
  -- `(Vbound, Vint_bound, Vβp_bound)` and the associated non-negativity
  -- predicates `(hVint_nn, hVβp_nn)` have been **dropped** from
  -- `T10PaperResidues`. They were originally introduced in iteration 0397
  -- as an interim measure when the closed-form Du integral chain was
  -- not yet available. After D4.0d (integral Du chain) and D4.1a-deep
  -- (producer body migration), the V-bound parameters in the `cBundles`
  -- field type are pinned to `(0, 0, 0)` (matching the existing
  -- `paperCBundleFor` discharge), and the unique consumer
  -- (`simplePowerThinChain_of_paperHypotheses` building `aprioriResidue`)
  -- passes literal `(0, 0, 0, le_refl 0, le_refl 0)` directly to the
  -- pointwise `_setInputs` residue producer. The follow-up `1b-deep`
  -- will migrate the consumer routing to the integral chain
  -- (`aprioriUniformResidueInputs_of_paperHypotheses_int`).
  /-- **Per-`k` paper-enriched regularised solution data** at paper-form
  exponents. Bundles the bare solution together with the three paper-side
  identities/inequalities (HJ0 orthogonality, paper-line-1212 transport
  identity, Legendre lower bound). The legacy raw fields `sol`,
  `hIdentityRaw`, `hLagrRaw` are now derived projections of this single
  bundle (`paperSol k).sol`, `(paperSol k).hTransport_identity`,
  `(paperSol k).h_lagr` respectively).

  Per `infra-P5-T10-rewire-paperSol-bundle`. -/
  paperSol : ∀ k : ℕ,
    StationaryMFG.Theorems.SimplePower.Banach.RegularizedPaperSolutionData
      (d := d) (epsSeq k) V H DpH
      (StationaryMFG.Hamiltonian.gammaBar hpow.α hpow.β)
      (hpow.β + 1) βBarReal' γBarReal' hpow
  /-- Per-`k` C-class bundle. **Phase 1 sub-task 1c-a (v7 plan,
  D4.1c-a):** retyped from the pointwise `AprioriUniformPerSolHypothesesC`
  to the integral V-data sibling `AprioriUniformPerSolHypothesesC_int`
  (`AprioriUniform.lean:2665`). **iter
  `infra-P5-T10-v7-drain-paperHVbndAuth`**: the transitional
  `Vbound : ℝ` parameter and the impossible `hVbnd : ∀ᵐ x, |V x| ≤ 0`
  field have been dropped from the structure entirely, since the
  canonical `_paperHypotheses_int` consumer's body has zero `hVbnd`
  references. The bundle now carries only paper-faithful content. -/
  cBundles : ∀ k : ℕ,
    StationaryMFG.Theorems.SimplePower.Banach.AprioriUniformPerSolHypothesesC_int
      (d := d) hpow (paperSol k).sol
  -- **iter 419 / drop-`hRes_Lp` shrink**
  -- (`infra-P5-theorem1-T10-drop-hRes_Lp`): the per-`k` HJB-residual
  -- `MemLpPer β̄'` field is now derived in-body of
  -- `simplePowerThinChain_of_paperHypotheses` from
  -- `(hpow, hHat0, hFin, hAgree, hV_paper, sol, hmNonneg, hmLp, huLp,
  --  hDuLp)` plus per-`k` measurabilities `(hu_measRaw, hDu_measRaw,
  --  hm_measRaw, hV_meas)` via `Hamiltonian.g_memLp_betaBar'_nonneg`.
  -- This mirrors `Banach.WeakLimitInputBundle.hRes_Lp` (the weak-limit
  -- variant) but per-`k` for the regularised sequence.
  -- **iter 417 / drop-`hStrongVI_set` shrink**
  -- (`infra-P5-theorem1-T10-drop-hStrongVI_set`): the universal
  -- `hStrongVI_set` field has been replaced by per-(k, S) dominator
  -- data (`setDominator`, `setDominator_memLp`, `setDominator_bd`)
  -- + two authorised measurabilities (`hm_measRaw`, `hV_meas`). The
  -- chain builds per-`k` `SetAdditiveContinuityInputs` in-body via
  -- `SetAdditiveContinuityInputs.of_paperHypotheses`, then routes the
  -- residue producer through the iter-414
  -- `aprioriUniformResidueInputs_of_paperHypotheses_closedPaper_setInputs`
  -- variant.
  -- **iter `infra-P5-T10-drop-hm_measRaw-hV_meas-final`** (split-child of
  -- `infra-P5-T10-drop-measurabilities-final`): the B-class authorised
  -- fields `hm_measRaw : ∀ k, Measurable (paperSol k).sol.m` and
  -- `hV_meas : Measurable V` have been removed. Their consumers in
  -- `simplePowerThinChain_of_paperHypotheses` are now discharged inline
  -- from `(sol k).hmLp.aestronglyMeasurable.aemeasurable` and
  -- `hV.aestronglyMeasurable.aemeasurable` (the `MemLpPer` `V`-witness
  -- threaded through the chain), routed via `Measurable.comp_aemeasurable`
  -- for the `H ∘ (id, Du, m)` and `DpH ∘ (id, Du, m)` compositions.
  -- The remaining two B-class measurability fields `hu_measRaw` and
  -- `hDu_measRaw` are deferred to
  -- `infra-P5-T10-drop-hu_measRaw-hDu_measRaw-final` (gated on the two
  -- consumer-relax children
  -- `infra-P5-T10-relax-poincare-wirtinger-measurabilities`,
  -- `infra-P5-T10-relax-aggregate-producer-measurabilities`).
  -- **iter `infra-P5-T10-drop-setDominator-from-residues`**: the three
  -- per-`(k, S)` dominator fields `setDominator`, `setDominator_memLp`,
  -- `setDominator_bd` have been removed. The HJB-residual dominator
  -- (a single `(Fin d → ℝ) → ℝ` envelope, independent of `S` and `n`)
  -- is now constructed in-body of `simplePowerThinChain_of_paperHypotheses`
  -- via `setDominator_of_paperHypotheses` from
  -- `(hpow, hHat0, hFin, hAgree, sol k, hV_paper)`. The chain consumer
  -- reads the bundle through the closed-form
  -- `SetAdditiveContinuityInputs.of_paperHypotheses_closed`, which
  -- threads the producer internally; the dominator triple is no longer
  -- exposed on the residue surface.
  /-- B-class authorised: alignment between the opaque C-class
  `epsTerms` field and the paper-form regulariser shape
  `ε·|Du|^(γ̄/2) + ε·u^γ̄`. Required to bridge the C-class
  `hIdentityRaw` consumer shape with the paper-form
  `(paperSol k).hTransport_identity`.

  Phase-0 note (per
  `infra-P5-T10-D4-4-PaperCBundleForK-fix-scaffolding`): the
  paper-canonical formula is `ε|u_ε|^γ̄`
  (`Source/FGU-monotone_revised.tex` lines 1212-1214); the
  absolute-value migration is deferred because the consumer
  `hIdentityRaw_of_regularizedPaperSolutionData` aligns to the
  fixed shape carried by
  `RegularizedPaperSolutionData.hTransport_identity`
  (`AssemblyContext.lean`), and migrating that record and its
  producer chain is the scope of the follow-up
  `infra-P5-T10-D4-4-paperEpsTerms-abs-u-migration`. -/
  epsTerms_align : ∀ k : ℕ, ∀ x,
    (cBundles k).epsTerms x =
      epsSeq k *
          ((fun i => (paperSol k).sol.Du i x)
            ⬝ (fun i => (paperSol k).sol.Du i x))
          ^ (StationaryMFG.Hamiltonian.gammaBar hpow.α hpow.β / 2)
      + epsSeq k * |(paperSol k).sol.u x|
          ^ StationaryMFG.Hamiltonian.gammaBar hpow.α hpow.β
  -- **iter `infra-P5-T10-drop-hIdentityRaw-final`**: the `hIdentityRaw`
  -- field has been removed. Its content is now sourced via the bridge
  -- lemma `hIdentityRaw_of_regularizedPaperSolutionData` (consuming
  -- `paperSol k`, `cBundles k`, and `epsTerms_align k`) at the consumer
  -- site in `simplePowerThinChain_of_paperHypotheses`.
  -- **iter post-420 / drop-`hRHSaboveRaw` shrink**
  -- (`infra-P5-theorem1-T10-drop-hRHSaboveRaw`): the per-`k`
  -- integrability of `|V| + C·(m^β + 1)` is now derived in-body of
  -- `simplePowerThinChain_of_paperHypotheses` from `hV : MemLpPer
  -- (ENNReal.ofReal βBarReal') V` (descended to `L¹` via
  -- `MemLp.integrable`, then `Integrable.abs`), `hMbeta_int_k k` (the
  -- existing `m^β` integrability), and `MeasureTheory.integrable_const`
  -- on the finite-measure unit cube, combined with `Integrable.add` and
  -- `Integrable.const_mul`.
  -- **iter post-419 / drop-`hMbetaRaw` shrink**
  -- (`infra-P5-theorem1-T10-drop-integrability-triple`): the per-`k`
  -- integrability of `m^β` is now derived in-body of
  -- `simplePowerThinChain_of_paperHypotheses` from
  -- `(sol k).hmLp : MemLpPer (β+1) m` via
  -- `Periodic.MemLpPer.mono_exponent_finite` (descend to L^β on the
  -- finite-measure cube) followed by `MemLp.integrable_norm_rpow`,
  -- realigning `‖m‖^β = m^β` a.e. via `(sol k).hmNonneg`.
  -- **iter post-425 / drop-`hRHSbelowRaw` shrink**
  -- (`infra-P5-theorem1-T10-drop-hRHSbelowRaw-final`): the per-`k`
  -- integrability of the paper RHS lower bound is now derived
  -- in-body of `simplePowerThinChain_of_paperHypotheses` by combining
  -- the four ingredients `hMresidual_int_k`, `hMu_int_k`,
  -- `hMDpHDu_int_k`, and `(cBundles k).hEpsInt` with the algebraic
  -- identity `m·(-H + DpH·Du) + V·m + epsTerms = m·hjbResidual + m·u
  -- + m·(DpH·Du) + epsTerms` (the `-m·V` and `+V·m` cancel pointwise),
  -- using `Integrable.add` and `Integrable.congr` against `hjbResidual`'s
  -- definition.
  -- **iter `infra-P5-T10-drop-hu_measRaw-hDu_measRaw-final`**: the
  -- raw measurability fields `hu_measRaw` and `hDu_measRaw` have been
  -- removed. Their content is now derived inline from the per-`k`
  -- `MemLpPer` witnesses `(paperSol k).sol.huLp` and
  -- `(paperSol k).sol.hDuLp i` (each yielding
  -- `AEStronglyMeasurable … (volume.restrict (UnitCube d))`), upgraded
  -- to `AEStronglyMeasurable … volume` via
  -- `MemLpPer.locallyIntegrable_of_periodic.aestronglyMeasurable`
  -- using the periodicity certificates `(cBundles k).hu_per` and
  -- `(cBundles k).hDu_per`. The downstream consumer chain
  -- (`apriori_*` producers, `closedPaper_setInputs`, the
  -- `AprioriUniformPerSolHypotheses.{hu_meas,hDu_meas}` struct fields,
  -- and the `AprioriDischargeInputs` / `AprioriInputAuxHyps` analogues)
  -- has been relaxed to `AEStronglyMeasurable … volume` in lockstep.
  -- **iter post-419 / drop-`hDu_norm_intRaw` shrink**
  -- (`infra-P5-theorem1-T10-drop-integrability-triple`): the per-`k`
  -- integrability of `‖Du‖^γ̄` is now derived in-body of
  -- `simplePowerThinChain_of_paperHypotheses` from per-coordinate
  -- `(sol k).hDuLp i : MemLpPer (ENNReal.ofReal γ̄) (Du i)` via
  -- `MemLp.integrable_norm_rpow`, dominated by the finite sum
  -- `∑ i, ‖Du i x‖^γ̄` (sup-norm bound `‖v‖ ≤ max_i |v_i|` on
  -- `Fin d → ℝ`), and the resulting integrability of the sum.
  -- **iter `infra-P5-T10-rewire-paperSol-bundle`**: the legacy raw
  -- field `hLagrRaw` has been removed; its content is now sourced via
  -- the projection `(paperSol k).h_lagr`. The `hIdentityRaw` field is
  -- *retained* for now: its consumer at
  -- `aprioriUniformResidueInputs_of_paperHypotheses_closedPaper_setInputs`
  -- expects the C-class shape `… + (cBundles k).epsTerms x`, which is
  -- not definitionally equal to the paper-form
  -- `… + ε·|Du|^(γ̄/2) + ε·u^γ̄` stored in `(paperSol k).hTransport_identity`.
  -- A follow-up will add an `epsTerms_align` residue and derive
  -- `hIdentityRaw` via `hIdentityRaw_of_regularizedPaperSolutionData`.
  -- **iter `infra-P5-T10-drop-weakSelector`**: the legacy
  -- `weakSelector : WeakLimitExtractionAE …` field has been removed.
  -- Its sole consumer was `simplePowerThinChain_of_paperHypotheses`,
  -- which now constructs the `WeakLimitExtractionAE` value inline
  -- via `weakLimitExtractionAE_of_uniform_apriori (… seq)`. No code
  -- path read `residues.weakSelector` at term level (the only hit
  -- across `StationaryMFG/` was a docstring in `RegularizedSequence.lean`),
  -- so the field is dropped from the public residue surface.
  -- **iter `infra-P5-mintyData-discharge-set-family-wire-final`**: the
  -- legacy wide-domain `mintyDataSetOf` field has been replaced by the
  -- narrow-domain `mintyResSetOf` field below, carrying a
  -- `SetFamilyNarrowMintyResidue` (Child 1, defined just above this
  -- structure). The chain consumer
  -- `mintyClosure_familyNative_set_of_paperHypotheses_narrow` reads
  -- the narrow paper-form domain `D_set_family_paper βBar mLim uLim DuLim`
  -- directly, so the wide-domain build + narrowing step
  -- `mintyClosureOn_set_paper_of_wider` is dropped from the chain.
  /-- **Phase 5 residue (set family, narrow paper-form).** Per-family
  narrow hemicontinuity segment-data residue on
  `D_set_family_paper βBar wkBundle.{mLim,uLim,DuLim}`. Parameterised
  on `wkBundle` (mirroring the `h_weak_*Of` / `pairingResidueOf` field
  convention). The Gateaux exponent is pinned to `γBarReal` (the value
  consumed by `mintyClosure_familyNative_set_of_paperHypotheses_narrow`).

  Together with `mintyDataSetNarrowK0_of_paperHypotheses` (defined
  further below in this file) this produces the per-pair
  `HemicontSegmentDataK0` aggregator that the Theorem-1 chain feeds
  into the narrow K0 `MintyClosureOn` builder
  `mintyClosure_familyNative_set_of_paperHypotheses_narrowK0`.

  **iter `infra-P5-T10-v8-K0-set-mintyResSetOf-retype`**: the field
  type has been swapped from the strict-K `SetFamilyNarrowMintyResidue`
  to the closed-cone sibling `SetFamilyNarrowMintyResidueK0`. The
  structural difference is that the K0 residue's `segInputsOf`
  returns `SetFamilyNarrowSegInputsK0` (dropping `hPosSeg`, swapping
  to the K0 unreg measurability shape). Step 10a.1 of the v8 K0
  set-auth-drain. -/
  mintyResSetOf :
    ∀ (wkBundle : StationaryMFG.Theorems.SimplePower.Banach.WeakLimitInputBundleAE
                    (d := d) γBarReal βBarReal),
      SetFamilyNarrowMintyResidueK0Min (d := d)
        (γBarReal := γBarReal) (βBarReal := βBarReal)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        (γBar := γBarReal) V H DpH hpow wkBundle
  /-- **Phase 5 residue (signed family, narrow paper-form, nonneg primal).**
  Per-family narrow hemicontinuity segment-data residue on
  `D_signed_family_paper_nn βBar wkBundle.{mLim,uLim,DuLim}`. The Gateaux
  exponent is pinned to `γBarReal` (the value consumed by
  `mintyClosure_familyNative_signed_of_paperHypotheses_narrowK0`).

  Together with `mintyDataSignedNarrowK0_of_paperHypotheses` (defined
  further below) this produces the per-pair `HemicontSegmentDataK0`
  aggregator that the Theorem-1 chain feeds into the narrow K0 signed
  `MintyClosureOn` builder
  `mintyClosure_familyNative_signed_of_paperHypotheses_narrowK0`.

  Per `infra-P5-mintyData-discharge-signed-family`, this replaces the
  legacy wide-domain `mintyDataSignedOf` field; the wide build +
  narrowing chain (`mintyClosureOn_signed_nn_of_wider` then
  `mintyClosureOn_signed_paper_nn_of_wider`) is dropped from
  `simplePowerThinChain_of_paperHypotheses`.

  **iter `infra-P5-T10-v8-K0-signed-mintyResSignedOf-retype`**: the field
  type has been swapped from the strict-K `SignedFamilyNarrowMintyResidue`
  to the closed-cone sibling `SignedFamilyNarrowMintyResidueK0` (signed
  mirror of iter-0762's set retype). The structural difference is that
  the K0 residue's `segInputsOf` returns `SignedFamilyNarrowSegInputsK0`
  (dropping `hPosSeg`, swapping to the K0 unreg measurability shape). -/
  mintyResSignedOf :
    ∀ (wkBundle : StationaryMFG.Theorems.SimplePower.Banach.WeakLimitInputBundleAE
                    (d := d) γBarReal βBarReal),
      SignedFamilyNarrowMintyResidueK0Min (d := d)
        (γBarReal := γBarReal) (βBarReal := βBarReal)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        (γBar := γBarReal) V H DpH hpow wkBundle
  /-- **Phase 5 residue (transport family, narrow paper-form).**
  Per-family narrow hemicontinuity segment-data residue on
  `D_transport_family_paper wkBundle.{mLim,uLim,DuLim}`. The Gateaux
  exponent is pinned to `γBarReal` (the value consumed by
  `mintyClosure_familyNative_transport_of_paperHypotheses_narrow`).

  Together with `mintyDataTransport_of_paperHypotheses` (defined above)
  this produces the per-pair `HemicontSegmentData` aggregator that the
  Theorem-1 chain feeds into the narrow transport `MintyClosureOn`
  builder.

  Per `infra-P5-mintyData-transport-rewire-T10`, this replaces the
  legacy wide-domain `mintyDataTransportOf` field; the wide build
  `mintyClosure_familyNative_transport_of_paperHypotheses` plus the
  narrowing step `mintyClosureOn_transport_paper_of_wider` are dropped
  from `simplePowerThinChain_of_paperHypotheses`.

  **iter `infra-P5-T10-v8-K0-transport-mintyResTransportOf-retype`**
  (transport mirror of iter-0762's set retype and iter-0771's signed
  retype): the field type has been swapped from the strict-K
  `TransportFamilyNarrowMintyResidue` to the closed-cone sibling
  `TransportFamilyNarrowMintyResidueK0`. The structural difference is
  that the K0 residue's `segInputsOf` returns
  `TransportFamilyNarrowSegInputsK0` (dropping `hPosSeg`, swapping to the
  K0 unreg measurability shape, and relocating the four test-direction
  certs into the function signature). -/
  mintyResTransportOf :
    ∀ (wkBundle : StationaryMFG.Theorems.SimplePower.Banach.WeakLimitInputBundleAE
                    (d := d) γBarReal βBarReal),
      TransportFamilyNarrowMintyResidueK0Min (d := d)
        (γBarReal := γBarReal) (βBarReal := βBarReal)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        (γBar := γBarReal) V H DpH hpow wkBundle
  -- Historical: the universal `regBundle` field has been removed
  -- (Phase 6d-ii-d-3); the three per-family per-test-triple regularity
  -- records are now built inline in `simplePowerThinChain_of_paperHypotheses`
  -- from `wkBundle.perTestTripleBase` plus the per-family
  -- `PerTestTripleRegularity._perturbation` constructors.
  -- **`infra-P5-T10-drop-pairingResidueOf-final-hmu-pos`** (Option A).
  -- The wrapping `pairingResidueOf` field has been dropped: its only
  -- non-vacuous content (the single-field
  -- `LimitPairingSelectorPaperResidue.hμ_pos`) is now exposed as the
  -- slim flat field `hμ_posOf` below. Consumers in
  -- `simplePowerThinChain_of_paperHypotheses` build the
  -- `LimitPairingSelectorPaperResidue` value inline as
  -- `{ hμ_pos := residues.hμ_posOf seq wkBundle }`.
  --
  -- **`infra-P5-T10-D5-hmu-pos-shape-audit`** (Outcome A): the single
  -- arbitrary-`μ` field `hμ_posOf` has been split into three
  -- family-scoped flat fields, one per paper-form family domain
  -- (`D_set_family_paper`, `D_signed_family_paper_nn`,
  -- `D_transport_family_paper`). Each field consumes a
  -- family-membership hypothesis `(μ, υ, Dυ) ∈ D_*_family_paper …`,
  -- matching the paper's `essinf μ > 0` framing for admissible test
  -- triples (`Source/FGU-monotone_revised.tex` lines 303 / 1330).
  /-- **Set-family-scoped a.e. non-negativity** (iter
  `infra-P5-T10-v7-phase4-hmu-posAuth-drain`). For test triples in
  the narrow paper-form set domain, a.e. non-negativity of the
  density `μ`. Paper-faithful (the set family triple is
  `(mLim + ρ, _, _)` with `ρ ≥ 0` and `0 ≤ mLim`, so `0 ≤ mLim + ρ`).
  Strict positivity was unprovable since the unperturbed limit
  triple has `ρ = 0` and the paper only gives `mLim ≥ 0`. -/
  hμ_posOf_set :
    ∀ (_seq : StationaryMFG.Theorems.SimplePower.Banach.RegularizedSequenceData
              (d := d) γBarReal βBarReal βBarReal' γBarReal' V H DpH)
      (wkBundle : StationaryMFG.Theorems.SimplePower.Banach.WeakLimitInputBundleAE
                    (d := d) γBarReal βBarReal)
      ⦃μ υ : (Fin d → ℝ) → ℝ⦄
      ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
      (μ, υ, Dυ) ∈ StationaryMFG.Theorems.SimplePower.Banach.D_set_family_paper
                      (d := d) (ENNReal.ofReal βBarReal)
                      wkBundle.mLim wkBundle.uLim wkBundle.DuLim →
      0 ≤ᵐ[MeasureTheory.volume.restrict (Periodic.UnitCube d)] μ
  /-- **Signed-family-scoped a.e. non-negativity** (iter
  `infra-P5-T10-v7-phase4-hmu-posAuth-drain`). The signed-family
  membership already provides `0 ≤ᵐ (mLim + g)` by definition. -/
  hμ_posOf_signed :
    ∀ (_seq : StationaryMFG.Theorems.SimplePower.Banach.RegularizedSequenceData
              (d := d) γBarReal βBarReal βBarReal' γBarReal' V H DpH)
      (wkBundle : StationaryMFG.Theorems.SimplePower.Banach.WeakLimitInputBundleAE
                    (d := d) γBarReal βBarReal)
      ⦃μ υ : (Fin d → ℝ) → ℝ⦄
      ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
      (μ, υ, Dυ) ∈ StationaryMFG.Theorems.SimplePower.Banach.D_signed_family_paper_nn
                      (d := d) (ENNReal.ofReal βBarReal)
                      wkBundle.mLim wkBundle.uLim wkBundle.DuLim →
      0 ≤ᵐ[MeasureTheory.volume.restrict (Periodic.UnitCube d)] μ
  /-- **Transport-family-scoped a.e. non-negativity** (iter
  `infra-P5-T10-v7-phase4-hmu-posAuth-drain`). The transport-family
  triple has `μ = mLim` always (transport perturbs only `(u, Du)`),
  so `0 ≤ᵐ μ ↔ 0 ≤ᵐ mLim` = `wkBundle.hmRep_nonneg`. -/
  hμ_posOf_transport :
    ∀ (_seq : StationaryMFG.Theorems.SimplePower.Banach.RegularizedSequenceData
              (d := d) γBarReal βBarReal βBarReal' γBarReal' V H DpH)
      (wkBundle : StationaryMFG.Theorems.SimplePower.Banach.WeakLimitInputBundleAE
                    (d := d) γBarReal βBarReal)
      ⦃μ υ : (Fin d → ℝ) → ℝ⦄
      ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
      (μ, υ, Dυ) ∈ StationaryMFG.Theorems.SimplePower.Banach.D_transport_family_paper
                      (d := d)
                      wkBundle.mLim wkBundle.uLim wkBundle.DuLim →
      0 ≤ᵐ[MeasureTheory.volume.restrict (Periodic.UnitCube d)] μ
  -- Historical: the legacy `hVI_eps_universalOf` field has been removed
  -- (Phase 5b); the pairing producers consume the leaner
  -- `LimitPassageInputData_noVI` shape. The universal weak-pairing
  -- certificates `h_weak_{m,u,Du}Of` were lifted from
  -- `LimitPairingSelectorPaperResidue` to top-level fields of this
  -- bundle (Phase H2) so the Theorem 1 chain consumes them directly.
  --
  -- **Phase 1 of expert post-iter-412 plan**
  -- (`infra-P5-theorem1-remove-pairingResidue-hpq-dependency`). The
  -- Hölder-conjugacy proof in the `WeakConvPairing_universal` type
  -- now comes from the canonical paper helpers
  -- `hpqBeta_paper hpow` / `hpqGamma_paper hpow`.
  --
  -- **Phase D1 (`infra-P5-T10-D1-discharge-h-weak-fields`)** — the
  -- field `h_subseq_uniqueness` was the single B-class authorised
  -- cluster-point-uniqueness premise (bundled across the three
  -- components), from which the three `h_weak_{m,u,Du}Of` certificates
  -- were derived inline at producer sites via
  -- `WeakConvPairing_universal.of_subseq_tendsto`.
  --
  -- **HMinty-3 (`infra-P5-T10-v7-HMinty-3-rewire-and-drain`)** — the
  -- `h_subseq_uniqueness` field and the three `h_weak_{m,u,Du}Of`
  -- fields have been **dropped** from this structure. They are no
  -- longer needed: the chain consumer
  -- `simplePowerThinChain_of_paperHypotheses` now sources the three
  -- universal weak-pairing certificates from the in-tree HMinty-2
  -- producer `extractedWeakPairingData_of_regularizedSequence`,
  -- bypassing the legacy `T10PaperResidues.h_weak_{m,u,Du}Of`
  -- indirection. The Route-1 bridge
  -- `weakConvPairing_universal_of_toWeakSpace_conv` discharges the
  -- pairings from `WeakLimitSubsequenceData.hWeakSpace_tendsto`, so
  -- the corresponding `h_minty_limit_auth` B-class parameter on
  -- `T10PaperResidues.of_paperHypotheses` has been drained.
  -- Historical: the legacy `finIntResidue` field has been removed
  -- (Phases H5b/H5c/H5d). The HJB-residual `MemLpPer βBar'` claim is
  -- now derived in-body of `simplePowerThinChain_of_paperHypotheses` via
  -- `Banach.WeakLimitInputBundle.hRes_Lp` (reducing to
  -- `Hamiltonian.g_memLp_betaBar'_nonneg` and `Hamiltonian.H_rc0_of_hHat0`).

/-- **Compatibility projection** for the legacy `sol` field of
`T10PaperResidues`. After `infra-P5-T10-rewire-paperSol-bundle`, the
per-`k` regularised bare solution is no longer a top-level field; it is
sourced as the `.sol` projection of the bundled `paperSol k`. This
helper restores `residues.sol k` as the dot-notation form expected by
the >100 in-body references in
`simplePowerThinChain_of_paperHypotheses`. -/
def T10PaperResidues.sol
    {d : ℕ}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {hpow : Hamiltonian.HypothesisPowerGrowth H DpH}
    (residues : T10PaperResidues
                  (d := d) γBarReal βBarReal βBarReal' γBarReal' V H DpH hpow)
    (k : ℕ) :
    StationaryMFG.Theorems.SimplePower.Banach.RegularizedBareSolution
      d (residues.epsSeq k) V H DpH
      (StationaryMFG.Hamiltonian.gammaBar hpow.α hpow.β)
      (hpow.β + 1) βBarReal' γBarReal' :=
  (residues.paperSol k).sol

/-- **Sanity-check `example`** for the K0 retype iter
`infra-P5-T10-v8-K0-set-mintyResSetOf-retype`. The `mintyResSetOf` field
now returns the K0 residue `SetFamilyNarrowMintyResidueK0` instead of
the strict-K `SetFamilyNarrowMintyResidue`. -/
example
    {d : ℕ}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {hpow : Hamiltonian.HypothesisPowerGrowth H DpH}
    (residues : T10PaperResidues
                  (d := d) γBarReal βBarReal βBarReal' γBarReal' V H DpH hpow)
    (wkBundle : StationaryMFG.Theorems.SimplePower.Banach.WeakLimitInputBundleAE
                  (d := d) γBarReal βBarReal) :
    SetFamilyNarrowMintyResidueK0Min (d := d)
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      (γBar := γBarReal) V H DpH hpow wkBundle :=
  residues.mintyResSetOf wkBundle

/-- **Sanity-check `example`** for the K0 retype iter
`infra-P5-T10-v8-K0-transport-mintyResTransportOf-retype`. The
`mintyResTransportOf` field now returns the K0 residue
`TransportFamilyNarrowMintyResidueK0` instead of the strict-K
`TransportFamilyNarrowMintyResidue`. -/
example
    {d : ℕ}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {hpow : Hamiltonian.HypothesisPowerGrowth H DpH}
    (residues : T10PaperResidues
                  (d := d) γBarReal βBarReal βBarReal' γBarReal' V H DpH hpow)
    (wkBundle : StationaryMFG.Theorems.SimplePower.Banach.WeakLimitInputBundleAE
                  (d := d) γBarReal βBarReal) :
    TransportFamilyNarrowMintyResidueK0Min (d := d)
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      (γBar := γBarReal) V H DpH hpow wkBundle :=
  residues.mintyResTransportOf wkBundle

/-! ### K0-minimal set-family composer (sibling of iter-0758)

`hemicontSegmentData_set_narrow_K0_min_of_paperHypotheses` is the
minimal-shape sibling of `hemicontSegmentData_set_narrow_K0_of_paperHypotheses`
(iter 0758). It takes the eight bare-function `MemLpPer p`-of-power
certificates of `SetFamilyNarrowDominatorsK0Min` (iter 0786) — the
over-specified `bΔm1` cert is dropped — and discharges the Term-5
integrability `((|m̄|+|μ|)+1)·|ν|` via the iter-0785 helper
`integrable_deltaM_add_one_mul_abs_nu_from_gamma` (i.e. the route
`g_unreg_natural_integrableOn_min` used at the Banach pair).

The iter-0758 composer is preserved unchanged (sibling pattern, per
`docs/CONVENTIONS.md` §8); this composer is the consumer for the
minimal `SetFamilyNarrowDominatorsK0Min` bundle and unblocks the
`hβ_ge_one`-free SegInputs chain. -/

noncomputable def hemicontSegmentData_set_narrow_K0_min_of_paperHypotheses
    {d : ℕ} {γBarReal βBarReal βBarReal' γBarReal' γBar : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    (hβconj : βBarReal'.HolderConjugate βBarReal)
    (hγconj : γBarReal'.HolderConjugate γBarReal)
    {mLim uLim : (Fin d → ℝ) → ℝ}
    {DuLim : Fin d → (Fin d → ℝ) → ℝ}
    (hmLim_memLp : Periodic.MemLpPer (d := d)
                      (ENNReal.ofReal βBarReal) mLim)
    (huLim_sob : Periodic.MemSobolevPer (d := d)
                      (ENNReal.ofReal γBarReal) uLim)
    (hDuLim_memLp_γ : ∀ i, Periodic.MemLpPer (d := d)
                              (ENNReal.ofReal γBarReal) (DuLim i))
    (hmLim_nn : 0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                      (UnitCube d)] mLim)
    {ρ₁ ρ₂ : (Fin d → ℝ) → ℝ}
    (hρ₁_nn : ∀ x, 0 ≤ ρ₁ x)
    (hρ₂_nn : ∀ x, 0 ≤ ρ₂ x)
    (hρ₁_lp : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) ρ₁)
    (hρ₂_lp : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) ρ₂)
    -- Eight bare-function `MemLpPer p`-of-power certificates (NO `bΔm1`).
    (bΔυ : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x => |uLim x| + |uLim x|))
    (bΔp_pow : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x =>
                ‖fun i => |DuLim i x| + |DuLim i x|‖ ^ hpow.α + 1))
    (bΔm_pow : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x =>
                (|(mLim + ρ₂) x| + |(mLim + ρ₁) x|) ^ hpow.β + 1))
    (bΔm_grad : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => (|(mLim + ρ₂) x| + |(mLim + ρ₁) x|)
                  * ‖fun i => |DuLim i x| + |DuLim i x|‖ ^ (hpow.α - 1)))
    (bΔm_endpoint : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x =>
                (|(mLim + ρ₂) x| + |(mLim + ρ₁) x|) ^
                  (1 + hpow.β - hpow.β / hpow.α)))
    (bΔm : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => |(mLim + ρ₂) x| + |(mLim + ρ₁) x|))
    (bG_grad : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x =>
                (∑ i, (|DuLim i x| + |DuLim i x|) ^ (2 : ℕ))
                    ^ ((γBar - 1) / 2)))
    (bG_val : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => (|uLim x| + |uLim x|) ^ (γBar - 1)))
    (hγ_one_lt : 1 < γBar)
    (Dν : Fin d → (Fin d → ℝ) → ℝ) (η ν : (Fin d → ℝ) → ℝ)
    (hη : MemLpPer (d := d) (ENNReal.ofReal βBarReal) η)
    (hDν : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dν i))
    (hν_γ : MemLpPer (d := d) (ENNReal.ofReal γBarReal) ν)
    (hγBar_eq : γBar = γBarReal)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    -- Bare-function measurability of the K0 unreg integrand and the
    -- Gateaux integrand at the unshifted set endpoints.
    (hF_unreg_meas_bare : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x => aepsiIntegrandAt_unreg_K0 V H DpH
                    DuLim DuLim (mLim + ρ₁) (mLim + ρ₂)
                    uLim uLim Dν η ν x t)
        (MeasureTheory.volume.restrict (UnitCube d)))
    (hF_gat_meas_bare : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x => aepsiIntegrandAt_gateaux γBar
                    DuLim DuLim uLim uLim Dν ν x t)
        (MeasureTheory.volume.restrict (UnitCube d))) :
    HemicontSegmentDataK0 V H DpH γBar
      DuLim DuLim (mLim + ρ₁) (mLim + ρ₂)
      uLim uLim Dν η ν := by
  -- Build the two Banach pairs (same as iter-0758).
  set q₁ := Banach.bareToBanachPair_set_paper (d := d)
              (βBarReal := βBarReal) (γBarReal := γBarReal)
              (DuLim := DuLim)
              hmLim_memLp huLim_sob hDuLim_memLp_γ hρ₁_lp with hq₁_def
  set q₂ := Banach.bareToBanachPair_set_paper (d := d)
              (βBarReal := βBarReal) (γBarReal := γBarReal)
              (DuLim := DuLim)
              hmLim_memLp huLim_sob hDuLim_memLp_γ hρ₂_lp with hq₂_def
  -- K0 memberships.
  have hq₁_K0 : q₁ ∈ Banach.K0_Aepsi d βBarReal γBarReal :=
    Banach.bareToBanachPair_set_paper_mem_K0Aepsi (uLim := uLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hmLim_nn hρ₁_nn hρ₁_lp
  have hq₂_K0 : q₂ ∈ Banach.K0_Aepsi d βBarReal γBarReal :=
    Banach.bareToBanachPair_set_paper_mem_K0Aepsi (uLim := uLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hmLim_nn hρ₂_nn hρ₂_lp
  -- Four a.e.-coercion identities.
  have hm₁ :
      Banach.mOf q₁ =ᵐ[MeasureTheory.Measure.restrict
                  MeasureTheory.volume (UnitCube d)] (mLim + ρ₁) :=
    Banach.bareToBanachPair_set_paper_mOf_ae_eq (d := d)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hρ₁_lp
  have hm₂ :
      Banach.mOf q₂ =ᵐ[MeasureTheory.Measure.restrict
                  MeasureTheory.volume (UnitCube d)] (mLim + ρ₂) :=
    Banach.bareToBanachPair_set_paper_mOf_ae_eq (d := d)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hρ₂_lp
  have hu₁ :
      Banach.uOf q₁ =ᵐ[MeasureTheory.Measure.restrict
                  MeasureTheory.volume (UnitCube d)] uLim :=
    Banach.bareToBanachPair_set_paper_uOf_ae_eq (d := d)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hρ₁_lp
  have hu₂ :
      Banach.uOf q₂ =ᵐ[MeasureTheory.Measure.restrict
                  MeasureTheory.volume (UnitCube d)] uLim :=
    Banach.bareToBanachPair_set_paper_uOf_ae_eq (d := d)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hρ₂_lp
  have hDu₁ : ∀ i,
      Banach.DuOf q₁ i =ᵐ[MeasureTheory.Measure.restrict
                      MeasureTheory.volume (UnitCube d)] DuLim i := fun i =>
    Banach.bareToBanachPair_set_paper_DuOf_ae_eq (d := d)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hρ₁_lp i
  have hDu₂ : ∀ i,
      Banach.DuOf q₂ i =ᵐ[MeasureTheory.Measure.restrict
                      MeasureTheory.volume (UnitCube d)] DuLim i := fun i =>
    Banach.bareToBanachPair_set_paper_DuOf_ae_eq (d := d)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hρ₂_lp i
  -- Inline transport of the eight bare certs to the Banach pair endpoints.
  -- (Mirror of the eight `MemLp.ae_eq` blocks inside
  -- `Banach.segMemLpBundle_of_setPaper`, but without the `bΔm1` field.)
  -- Joint pointwise version of `(hDu₁, hDu₂)`.
  have hDuAll :
      ∀ᵐ x ∂(MeasureTheory.Measure.restrict
              MeasureTheory.volume (UnitCube d)),
        ∀ i, Banach.DuOf q₁ i x = DuLim i x ∧
             Banach.DuOf q₂ i x = DuLim i x := by
    rw [MeasureTheory.ae_all_iff]
    intro i
    filter_upwards [hDu₁ i, hDu₂ i] with x ha hb
    exact ⟨ha, hb⟩
  -- (1) `bhΔυ`.
  have bhΔυ :
      MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x => |Banach.uOf q₂ x| + |Banach.uOf q₁ x|) := by
    have heq :
        (fun x => |uLim x| + |uLim x|)
          =ᵐ[MeasureTheory.Measure.restrict
                MeasureTheory.volume (UnitCube d)]
            (fun x => |Banach.uOf q₂ x| + |Banach.uOf q₁ x|) := by
      filter_upwards [hu₁, hu₂] with x hx₁ hx₂
      simp [hx₁, hx₂]
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq heq bΔυ.toMemLp)
  -- (2) `bhΔp_pow`.
  have bhΔp_pow :
      MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x =>
          ‖fun i => |Banach.DuOf q₂ i x| + |Banach.DuOf q₁ i x|‖ ^ hpow.α
            + 1) := by
    have heq :
        (fun x => ‖fun i => |DuLim i x| + |DuLim i x|‖ ^ hpow.α + 1)
          =ᵐ[MeasureTheory.Measure.restrict
                MeasureTheory.volume (UnitCube d)]
            (fun x =>
              ‖fun i => |Banach.DuOf q₂ i x| + |Banach.DuOf q₁ i x|‖
                ^ hpow.α + 1) := by
      filter_upwards [hDuAll] with x hx
      have hfun :
          (fun i => |DuLim i x| + |DuLim i x|)
            = (fun i => |Banach.DuOf q₂ i x| + |Banach.DuOf q₁ i x|) := by
        funext i
        rcases hx i with ⟨h₁, h₂⟩
        simp [h₁, h₂]
      rw [hfun]
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq heq bΔp_pow.toMemLp)
  -- (3) `bhΔm_pow`.
  have bhΔm_pow :
      MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x => (|Banach.mOf q₂ x| + |Banach.mOf q₁ x|) ^ hpow.β + 1) := by
    have heq :
        (fun x => (|(mLim + ρ₂) x| + |(mLim + ρ₁) x|) ^ hpow.β + 1)
          =ᵐ[MeasureTheory.Measure.restrict
                MeasureTheory.volume (UnitCube d)]
            (fun x =>
              (|Banach.mOf q₂ x| + |Banach.mOf q₁ x|) ^ hpow.β + 1) := by
      filter_upwards [hm₁, hm₂] with x hx₁ hx₂
      simp [hx₁, hx₂]
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq heq bΔm_pow.toMemLp)
  -- (4) `bhΔm_grad`.
  have bhΔm_grad :
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => (|Banach.mOf q₂ x| + |Banach.mOf q₁ x|)
            * ‖fun i => |Banach.DuOf q₂ i x| + |Banach.DuOf q₁ i x|‖
              ^ (hpow.α - 1)) := by
    have heq :
        (fun x => (|(mLim + ρ₂) x| + |(mLim + ρ₁) x|)
            * ‖fun i => |DuLim i x| + |DuLim i x|‖ ^ (hpow.α - 1))
          =ᵐ[MeasureTheory.Measure.restrict
                MeasureTheory.volume (UnitCube d)]
            (fun x => (|Banach.mOf q₂ x| + |Banach.mOf q₁ x|)
              * ‖fun i =>
                  |Banach.DuOf q₂ i x| + |Banach.DuOf q₁ i x|‖
                  ^ (hpow.α - 1)) := by
      filter_upwards [hm₁, hm₂, hDuAll] with x hx₁ hx₂ hxDu
      have hfun :
          (fun i => |DuLim i x| + |DuLim i x|)
            = (fun i => |Banach.DuOf q₂ i x| + |Banach.DuOf q₁ i x|) := by
        funext i
        rcases hxDu i with ⟨h₁, h₂⟩
        simp [h₁, h₂]
      simp [hx₁, hx₂, hfun]
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq heq bΔm_grad.toMemLp)
  -- (5) `bhΔm_endpoint`.
  have bhΔm_endpoint :
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => (|Banach.mOf q₂ x| + |Banach.mOf q₁ x|)
            ^ (1 + hpow.β - hpow.β / hpow.α)) := by
    have heq :
        (fun x => (|(mLim + ρ₂) x| + |(mLim + ρ₁) x|)
            ^ (1 + hpow.β - hpow.β / hpow.α))
          =ᵐ[MeasureTheory.Measure.restrict
                MeasureTheory.volume (UnitCube d)]
            (fun x => (|Banach.mOf q₂ x| + |Banach.mOf q₁ x|)
              ^ (1 + hpow.β - hpow.β / hpow.α)) := by
      filter_upwards [hm₁, hm₂] with x hx₁ hx₂
      simp [hx₁, hx₂]
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq heq bΔm_endpoint.toMemLp)
  -- (6) `bhΔm`.
  have bhΔm :
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => |Banach.mOf q₂ x| + |Banach.mOf q₁ x|) := by
    have heq :
        (fun x => |(mLim + ρ₂) x| + |(mLim + ρ₁) x|)
          =ᵐ[MeasureTheory.Measure.restrict
                MeasureTheory.volume (UnitCube d)]
            (fun x => |Banach.mOf q₂ x| + |Banach.mOf q₁ x|) := by
      filter_upwards [hm₁, hm₂] with x hx₁ hx₂
      simp [hx₁, hx₂]
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq heq bΔm.toMemLp)
  -- (7) `bhG_grad`.
  have bhG_grad :
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x =>
          (∑ i, (|Banach.DuOf q₂ i x| + |Banach.DuOf q₁ i x|) ^ (2 : ℕ))
            ^ ((γBar - 1) / 2)) := by
    have heq :
        (fun x =>
            (∑ i, (|DuLim i x| + |DuLim i x|) ^ (2 : ℕ))
              ^ ((γBar - 1) / 2))
          =ᵐ[MeasureTheory.Measure.restrict
                MeasureTheory.volume (UnitCube d)]
            (fun x =>
              (∑ i,
                (|Banach.DuOf q₂ i x| + |Banach.DuOf q₁ i x|) ^ (2 : ℕ))
                ^ ((γBar - 1) / 2)) := by
      filter_upwards [hDuAll] with x hx
      have hsum :
          (∑ i, (|DuLim i x| + |DuLim i x|) ^ (2 : ℕ))
            = ∑ i,
              (|Banach.DuOf q₂ i x| + |Banach.DuOf q₁ i x|) ^ (2 : ℕ) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        rcases hx i with ⟨h₁, h₂⟩
        simp [h₁, h₂]
      rw [hsum]
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq heq bG_grad.toMemLp)
  -- (8) `bhG_val`.
  have bhG_val :
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => (|Banach.uOf q₂ x| + |Banach.uOf q₁ x|) ^ (γBar - 1)) := by
    have heq :
        (fun x => (|uLim x| + |uLim x|) ^ (γBar - 1))
          =ᵐ[MeasureTheory.Measure.restrict
                MeasureTheory.volume (UnitCube d)]
            (fun x =>
              (|Banach.uOf q₂ x| + |Banach.uOf q₁ x|) ^ (γBar - 1)) := by
      filter_upwards [hu₁, hu₂] with x hx₁ hx₂
      simp [hx₁, hx₂]
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq heq bG_val.toMemLp)
  -- K0 dominators (Child C).
  have hHabs_K0 :
      IsHK0AbsDominator (d := d) hpow (Banach.mOf q₁) (Banach.mOf q₂)
                          (Banach.DuOf q₁) (Banach.DuOf q₂) hpow.C :=
    Banach.isHK0AbsDominator_of_paperHypotheses hpow hHat0 hAgree
      (Banach.mOf q₁) (Banach.mOf q₂) (Banach.DuOf q₁) (Banach.DuOf q₂)
  have hmDpH_K0 :
      IsmDpHK0Dominator (d := d) hpow (Banach.mOf q₁) (Banach.mOf q₂)
                          (Banach.DuOf q₁) (Banach.DuOf q₂) :=
    Banach.isMDpHK0Dominator_of_paperHypotheses hpow hHat0 hAgree
      (Banach.mOf q₁) (Banach.mOf q₂) (Banach.DuOf q₁) (Banach.DuOf q₂)
  -- K0 segment nonnegativity at the Banach pair.
  have hNonneg_q :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          0 ≤ cxComb (Banach.mOf q₁) (Banach.mOf q₂) t x :=
    Banach.K0_Aepsi_segment_pos_nn hq₁_K0 hq₂_K0
  -- Transport `hF_unreg_meas_bare` and `hF_gat_meas_bare` to the Banach pair.
  have hF_unreg_K0_eq :=
    aepsiIntegrandAt_unreg_K0_congr_ae V H DpH Dν η ν
      hm₁ hm₂ hu₁ hu₂ hDu₁ hDu₂
  have hF_gat_eq :=
    aepsiIntegrandAt_gateaux_congr_ae γBar Dν ν
      hu₁ hu₂ hDu₁ hDu₂
  have hF_unreg_meas_q :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        MeasureTheory.AEStronglyMeasurable
          (fun x => aepsiIntegrandAt_unreg_K0 V H DpH
                      (Banach.DuOf q₁) (Banach.DuOf q₂)
                      (Banach.mOf q₁) (Banach.mOf q₂)
                      (Banach.uOf q₁) (Banach.uOf q₂) Dν η ν x t)
          (MeasureTheory.volume.restrict (UnitCube d)) := by
    intro t ht
    have hmeas := hF_unreg_meas_bare t ht
    refine hmeas.congr ?_
    filter_upwards [hF_unreg_K0_eq] with x hx
    exact (hx t).symm
  have hF_gat_meas_q :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        MeasureTheory.AEStronglyMeasurable
          (fun x => aepsiIntegrandAt_gateaux γBar
                      (Banach.DuOf q₁) (Banach.DuOf q₂)
                      (Banach.uOf q₁) (Banach.uOf q₂) Dν ν x t)
          (MeasureTheory.volume.restrict (UnitCube d)) := by
    intro t ht
    have hmeas := hF_gat_meas_bare t ht
    refine hmeas.congr ?_
    filter_upwards [hF_gat_eq] with x hx
    exact (hx t).symm
  -- Pointwise K0 bound on `aepsiIntegrandAt_unreg`.
  have hbound_unreg :=
    aepsiIntegrandAt_unreg_pointwise_bound_K0 V hpow hpow.hC
      (Banach.mOf q₁) (Banach.mOf q₂) (Banach.uOf q₁) (Banach.uOf q₂)
      (Banach.DuOf q₁) (Banach.DuOf q₂)
      Dν η ν hHabs_K0 hmDpH_K0
  -- Derive `1 ≤ ENNReal.ofReal γBarReal` from the `Fact` instance.
  have hγ_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal γBarReal :=
    (Fact.out : (1 : ℝ≥0∞) ≤ ENNReal.ofReal γBarReal)
  -- Assemble the K0 bundle at the Banach coercions.
  have dataQ :
      HemicontSegmentDataK0 V H DpH γBar
        (Banach.DuOf q₁) (Banach.DuOf q₂)
        (Banach.mOf q₁) (Banach.mOf q₂)
        (Banach.uOf q₁) (Banach.uOf q₂) Dν η ν :=
    { hNonneg := hNonneg_q
      g_unreg := Banach.g_unreg_natural hpow.α hpow.β hpow.C hpow.C V
                    (Banach.DuOf q₁) (Banach.DuOf q₂)
                    (Banach.mOf q₁) (Banach.mOf q₂)
                    (Banach.uOf q₁) (Banach.uOf q₂) Dν η ν
      g_gat := Banach.g_gat_natural γBar
                    (Banach.DuOf q₁) (Banach.DuOf q₂)
                    (Banach.uOf q₁) (Banach.uOf q₂) Dν ν
      hg_unreg_int :=
        -- Paper-faithful Term-5 split via `g_unreg_natural_integrableOn_min`:
        -- `((|m̄|+|μ|)+1)*|ν| = (|m̄|+|μ|)*|ν| + |ν|`, with the second piece
        -- discharged from `|ν| ∈ L^γ̄` and `1 ≤ γ̄`. This is exactly the
        -- iter-0785 `integrable_deltaM_add_one_mul_abs_nu_from_gamma` route.
        Banach.g_unreg_natural_integrableOn_min (α := hpow.α) (β := hpow.β)
          (C := hpow.C) (C' := hpow.C) (V := V)
          (Dυ := Banach.DuOf q₁) (Dῡ := Banach.DuOf q₂)
          (μ := Banach.mOf q₁) (mBar := Banach.mOf q₂)
          (υ := Banach.uOf q₁) (ῡ := Banach.uOf q₂)
          (Dν := Dν) (η := η) (ν := ν)
          hβconj hγconj hγ_one_le hη hDν hν_γ hV bhΔυ
          bhΔp_pow bhΔm_pow bhΔm_grad bhΔm_endpoint bhΔm
      hg_gat_int := by
        have :=
          Banach.g_gat_natural_integrableOn (γBar := γBarReal)
            (Dυ := Banach.DuOf q₁) (Dῡ := Banach.DuOf q₂)
            (υ := Banach.uOf q₁) (ῡ := Banach.uOf q₂)
            (Dν := Dν) (ν := ν) hγconj hDν hν_γ
            (hγBar_eq ▸ bhG_grad) (hγBar_eq ▸ bhG_val)
        simpa [hγBar_eq] using this
      hF_unreg_meas := hF_unreg_meas_q
      hF_unreg_bound := by
        intro t ht
        filter_upwards [hbound_unreg, hNonneg_q] with x hxBd hxNN
        have hbd := hxBd t ht (hxNN t ht)
        have hagree := aepsiIntegrandAt_unreg_K0_eq_unreg
          V H DpH (Banach.DuOf q₁) (Banach.DuOf q₂)
          (Banach.mOf q₁) (Banach.mOf q₂)
          (Banach.uOf q₁) (Banach.uOf q₂)
          Dν η ν x t
        rw [hagree]
        exact hbd
      hF_gat_meas := hF_gat_meas_q
      hF_gat_bound := by
        intro t ht
        have hgat :=
          aepsiIntegrandAt_gateaux_pointwise_bound_product (d := d)
            (γBar := γBar) hγ_one_lt
            (Banach.DuOf q₁) (Banach.DuOf q₂)
            (Banach.uOf q₁) (Banach.uOf q₂) Dν ν
        refine MeasureTheory.ae_of_all _ ?_
        intro x
        exact hgat x t ht }
  -- Transport from `(mOf q_i, …)` to `(mLim + ρ_i, uLim, DuLim)`.
  exact HemicontSegmentDataK0.ae_eq V H DpH γBar Dν η ν
    hm₁ hm₂ hu₁ hu₂ hDu₁ hDu₂ dataQ

/-! ## v8 K0 — signed-family K0 minimal-shape composer
(`infra-P6-K0-min-composer-signed`, audit 2026-05-22).

Signed mirror of the iter-0789 minimal-shape set composer
`hemicontSegmentData_set_narrow_K0_min_of_paperHypotheses`, and
minimal-shape sibling of the iter-0759 signed composer
`hemicontSegmentData_signed_narrow_K0_of_paperHypotheses`: same
preconditions and same return as iter 0759, except

* the over-specified `bΔm1` `MemLpPer βBarReal'` dominator is dropped
  (eight dominator inputs instead of nine), and
* the Term-5 integrability for the unreg piece is discharged via the
  iter-0785 helper `g_unreg_natural_integrableOn_min` (route
  `((|m̄|+|μ|)+1)·|ν| = (|m̄|+|μ|)·|ν| + |ν|`, using `1 ≤ γ̄` and
  `|ν| ∈ L^γ̄` on the unit cube).

Signature does **not** require `hβ_ge_one`: the dropped `bΔm1` cert
was the only field of the iter-0773 signed bundle that forced the
non-paper-faithful side condition. -/

noncomputable def hemicontSegmentData_signed_narrow_K0_min_of_paperHypotheses
    {d : ℕ} {γBarReal βBarReal βBarReal' γBarReal' γBar : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    (hβconj : βBarReal'.HolderConjugate βBarReal)
    (hγconj : γBarReal'.HolderConjugate γBarReal)
    {mLim uLim : (Fin d → ℝ) → ℝ}
    {DuLim : Fin d → (Fin d → ℝ) → ℝ}
    (hmLim_memLp : Periodic.MemLpPer (d := d)
                      (ENNReal.ofReal βBarReal) mLim)
    (huLim_sob : Periodic.MemSobolevPer (d := d)
                      (ENNReal.ofReal γBarReal) uLim)
    (hDuLim_memLp_γ : ∀ i, Periodic.MemLpPer (d := d)
                              (ENNReal.ofReal γBarReal) (DuLim i))
    -- Signed-family perturbations: only `MemLpPer` regularity is
    -- required; sign is unrestricted.
    {g₁ g₂ : (Fin d → ℝ) → ℝ}
    (hg₁_lp : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) g₁)
    (hg₂_lp : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) g₂)
    -- Joint primal a.e.-nonnegativity at each endpoint (signed family).
    (hjoint₁_nn :
      0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
              (UnitCube d)] (fun x => mLim x + g₁ x))
    (hjoint₂_nn :
      0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
              (UnitCube d)] (fun x => mLim x + g₂ x))
    -- Eight bare-function `MemLpPer p`-of-power certificates (NO `bΔm1`).
    (bΔυ : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x => |uLim x| + |uLim x|))
    (bΔp_pow : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x =>
                ‖fun i => |DuLim i x| + |DuLim i x|‖ ^ hpow.α + 1))
    (bΔm_pow : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x =>
                (|(mLim + g₂) x| + |(mLim + g₁) x|) ^ hpow.β + 1))
    (bΔm_grad : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => (|(mLim + g₂) x| + |(mLim + g₁) x|)
                  * ‖fun i => |DuLim i x| + |DuLim i x|‖ ^ (hpow.α - 1)))
    (bΔm_endpoint : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x =>
                (|(mLim + g₂) x| + |(mLim + g₁) x|) ^
                  (1 + hpow.β - hpow.β / hpow.α)))
    (bΔm : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => |(mLim + g₂) x| + |(mLim + g₁) x|))
    (bG_grad : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x =>
                (∑ i, (|DuLim i x| + |DuLim i x|) ^ (2 : ℕ))
                    ^ ((γBar - 1) / 2)))
    (bG_val : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => (|uLim x| + |uLim x|) ^ (γBar - 1)))
    (hγ_one_lt : 1 < γBar)
    (Dν : Fin d → (Fin d → ℝ) → ℝ) (η ν : (Fin d → ℝ) → ℝ)
    (hη : MemLpPer (d := d) (ENNReal.ofReal βBarReal) η)
    (hDν : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dν i))
    (hν_γ : MemLpPer (d := d) (ENNReal.ofReal γBarReal) ν)
    (hγBar_eq : γBar = γBarReal)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    -- Bare-function measurability of the K0 unreg integrand and the
    -- Gateaux integrand at the unshifted signed endpoints.
    (hF_unreg_meas_bare : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x => aepsiIntegrandAt_unreg_K0 V H DpH
                    DuLim DuLim (mLim + g₁) (mLim + g₂)
                    uLim uLim Dν η ν x t)
        (MeasureTheory.volume.restrict (UnitCube d)))
    (hF_gat_meas_bare : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x => aepsiIntegrandAt_gateaux γBar
                    DuLim DuLim uLim uLim Dν ν x t)
        (MeasureTheory.volume.restrict (UnitCube d))) :
    HemicontSegmentDataK0 V H DpH γBar
      DuLim DuLim (mLim + g₁) (mLim + g₂)
      uLim uLim Dν η ν := by
  -- Build the two Banach pairs (same Child A as in iter-0759).
  set q₁ := Banach.bareToBanachPair_set_paper (d := d)
              (βBarReal := βBarReal) (γBarReal := γBarReal)
              (DuLim := DuLim)
              hmLim_memLp huLim_sob hDuLim_memLp_γ hg₁_lp with hq₁_def
  set q₂ := Banach.bareToBanachPair_set_paper (d := d)
              (βBarReal := βBarReal) (γBarReal := γBarReal)
              (DuLim := DuLim)
              hmLim_memLp huLim_sob hDuLim_memLp_γ hg₂_lp with hq₂_def
  -- K0 memberships via the joint-NN signed-family producer.
  have hq₁_K0 : q₁ ∈ Banach.K0_Aepsi d βBarReal γBarReal :=
    Banach.bareToBanachPair_set_paper_mem_K0Aepsi_jointNN (uLim := uLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hg₁_lp hjoint₁_nn
  have hq₂_K0 : q₂ ∈ Banach.K0_Aepsi d βBarReal γBarReal :=
    Banach.bareToBanachPair_set_paper_mem_K0Aepsi_jointNN (uLim := uLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hg₂_lp hjoint₂_nn
  -- Four a.e.-coercion identities.
  have hm₁ :
      Banach.mOf q₁ =ᵐ[MeasureTheory.Measure.restrict
                  MeasureTheory.volume (UnitCube d)] (mLim + g₁) :=
    Banach.bareToBanachPair_set_paper_mOf_ae_eq (d := d)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hg₁_lp
  have hm₂ :
      Banach.mOf q₂ =ᵐ[MeasureTheory.Measure.restrict
                  MeasureTheory.volume (UnitCube d)] (mLim + g₂) :=
    Banach.bareToBanachPair_set_paper_mOf_ae_eq (d := d)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hg₂_lp
  have hu₁ :
      Banach.uOf q₁ =ᵐ[MeasureTheory.Measure.restrict
                  MeasureTheory.volume (UnitCube d)] uLim :=
    Banach.bareToBanachPair_set_paper_uOf_ae_eq (d := d)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hg₁_lp
  have hu₂ :
      Banach.uOf q₂ =ᵐ[MeasureTheory.Measure.restrict
                  MeasureTheory.volume (UnitCube d)] uLim :=
    Banach.bareToBanachPair_set_paper_uOf_ae_eq (d := d)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hg₂_lp
  have hDu₁ : ∀ i,
      Banach.DuOf q₁ i =ᵐ[MeasureTheory.Measure.restrict
                      MeasureTheory.volume (UnitCube d)] DuLim i := fun i =>
    Banach.bareToBanachPair_set_paper_DuOf_ae_eq (d := d)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hg₁_lp i
  have hDu₂ : ∀ i,
      Banach.DuOf q₂ i =ᵐ[MeasureTheory.Measure.restrict
                      MeasureTheory.volume (UnitCube d)] DuLim i := fun i =>
    Banach.bareToBanachPair_set_paper_DuOf_ae_eq (d := d)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hg₂_lp i
  -- Inline transport of the eight bare certs to the Banach pair endpoints.
  -- Mirror of the iter-0789 set-min composer (without the `bΔm1` field).
  -- Joint pointwise version of `(hDu₁, hDu₂)`.
  have hDuAll :
      ∀ᵐ x ∂(MeasureTheory.Measure.restrict
              MeasureTheory.volume (UnitCube d)),
        ∀ i, Banach.DuOf q₁ i x = DuLim i x ∧
             Banach.DuOf q₂ i x = DuLim i x := by
    rw [MeasureTheory.ae_all_iff]
    intro i
    filter_upwards [hDu₁ i, hDu₂ i] with x ha hb
    exact ⟨ha, hb⟩
  -- (1) `bhΔυ`.
  have bhΔυ :
      MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x => |Banach.uOf q₂ x| + |Banach.uOf q₁ x|) := by
    have heq :
        (fun x => |uLim x| + |uLim x|)
          =ᵐ[MeasureTheory.Measure.restrict
                MeasureTheory.volume (UnitCube d)]
            (fun x => |Banach.uOf q₂ x| + |Banach.uOf q₁ x|) := by
      filter_upwards [hu₁, hu₂] with x hx₁ hx₂
      simp [hx₁, hx₂]
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq heq bΔυ.toMemLp)
  -- (2) `bhΔp_pow`.
  have bhΔp_pow :
      MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x =>
          ‖fun i => |Banach.DuOf q₂ i x| + |Banach.DuOf q₁ i x|‖ ^ hpow.α
            + 1) := by
    have heq :
        (fun x => ‖fun i => |DuLim i x| + |DuLim i x|‖ ^ hpow.α + 1)
          =ᵐ[MeasureTheory.Measure.restrict
                MeasureTheory.volume (UnitCube d)]
            (fun x =>
              ‖fun i => |Banach.DuOf q₂ i x| + |Banach.DuOf q₁ i x|‖
                ^ hpow.α + 1) := by
      filter_upwards [hDuAll] with x hx
      have hfun :
          (fun i => |DuLim i x| + |DuLim i x|)
            = (fun i => |Banach.DuOf q₂ i x| + |Banach.DuOf q₁ i x|) := by
        funext i
        rcases hx i with ⟨h₁, h₂⟩
        simp [h₁, h₂]
      rw [hfun]
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq heq bΔp_pow.toMemLp)
  -- (3) `bhΔm_pow`.
  have bhΔm_pow :
      MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x => (|Banach.mOf q₂ x| + |Banach.mOf q₁ x|) ^ hpow.β + 1) := by
    have heq :
        (fun x => (|(mLim + g₂) x| + |(mLim + g₁) x|) ^ hpow.β + 1)
          =ᵐ[MeasureTheory.Measure.restrict
                MeasureTheory.volume (UnitCube d)]
            (fun x =>
              (|Banach.mOf q₂ x| + |Banach.mOf q₁ x|) ^ hpow.β + 1) := by
      filter_upwards [hm₁, hm₂] with x hx₁ hx₂
      simp [hx₁, hx₂]
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq heq bΔm_pow.toMemLp)
  -- (4) `bhΔm_grad`.
  have bhΔm_grad :
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => (|Banach.mOf q₂ x| + |Banach.mOf q₁ x|)
            * ‖fun i => |Banach.DuOf q₂ i x| + |Banach.DuOf q₁ i x|‖
              ^ (hpow.α - 1)) := by
    have heq :
        (fun x => (|(mLim + g₂) x| + |(mLim + g₁) x|)
            * ‖fun i => |DuLim i x| + |DuLim i x|‖ ^ (hpow.α - 1))
          =ᵐ[MeasureTheory.Measure.restrict
                MeasureTheory.volume (UnitCube d)]
            (fun x => (|Banach.mOf q₂ x| + |Banach.mOf q₁ x|)
              * ‖fun i =>
                  |Banach.DuOf q₂ i x| + |Banach.DuOf q₁ i x|‖
                  ^ (hpow.α - 1)) := by
      filter_upwards [hm₁, hm₂, hDuAll] with x hx₁ hx₂ hxDu
      have hfun :
          (fun i => |DuLim i x| + |DuLim i x|)
            = (fun i => |Banach.DuOf q₂ i x| + |Banach.DuOf q₁ i x|) := by
        funext i
        rcases hxDu i with ⟨h₁, h₂⟩
        simp [h₁, h₂]
      simp [hx₁, hx₂, hfun]
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq heq bΔm_grad.toMemLp)
  -- (5) `bhΔm_endpoint`.
  have bhΔm_endpoint :
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => (|Banach.mOf q₂ x| + |Banach.mOf q₁ x|)
            ^ (1 + hpow.β - hpow.β / hpow.α)) := by
    have heq :
        (fun x => (|(mLim + g₂) x| + |(mLim + g₁) x|)
            ^ (1 + hpow.β - hpow.β / hpow.α))
          =ᵐ[MeasureTheory.Measure.restrict
                MeasureTheory.volume (UnitCube d)]
            (fun x => (|Banach.mOf q₂ x| + |Banach.mOf q₁ x|)
              ^ (1 + hpow.β - hpow.β / hpow.α)) := by
      filter_upwards [hm₁, hm₂] with x hx₁ hx₂
      simp [hx₁, hx₂]
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq heq bΔm_endpoint.toMemLp)
  -- (6) `bhΔm`.
  have bhΔm :
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => |Banach.mOf q₂ x| + |Banach.mOf q₁ x|) := by
    have heq :
        (fun x => |(mLim + g₂) x| + |(mLim + g₁) x|)
          =ᵐ[MeasureTheory.Measure.restrict
                MeasureTheory.volume (UnitCube d)]
            (fun x => |Banach.mOf q₂ x| + |Banach.mOf q₁ x|) := by
      filter_upwards [hm₁, hm₂] with x hx₁ hx₂
      simp [hx₁, hx₂]
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq heq bΔm.toMemLp)
  -- (7) `bhG_grad`.
  have bhG_grad :
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x =>
          (∑ i, (|Banach.DuOf q₂ i x| + |Banach.DuOf q₁ i x|) ^ (2 : ℕ))
            ^ ((γBar - 1) / 2)) := by
    have heq :
        (fun x =>
            (∑ i, (|DuLim i x| + |DuLim i x|) ^ (2 : ℕ))
              ^ ((γBar - 1) / 2))
          =ᵐ[MeasureTheory.Measure.restrict
                MeasureTheory.volume (UnitCube d)]
            (fun x =>
              (∑ i,
                (|Banach.DuOf q₂ i x| + |Banach.DuOf q₁ i x|) ^ (2 : ℕ))
                ^ ((γBar - 1) / 2)) := by
      filter_upwards [hDuAll] with x hx
      have hsum :
          (∑ i, (|DuLim i x| + |DuLim i x|) ^ (2 : ℕ))
            = ∑ i,
              (|Banach.DuOf q₂ i x| + |Banach.DuOf q₁ i x|) ^ (2 : ℕ) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        rcases hx i with ⟨h₁, h₂⟩
        simp [h₁, h₂]
      rw [hsum]
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq heq bG_grad.toMemLp)
  -- (8) `bhG_val`.
  have bhG_val :
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => (|Banach.uOf q₂ x| + |Banach.uOf q₁ x|) ^ (γBar - 1)) := by
    have heq :
        (fun x => (|uLim x| + |uLim x|) ^ (γBar - 1))
          =ᵐ[MeasureTheory.Measure.restrict
                MeasureTheory.volume (UnitCube d)]
            (fun x =>
              (|Banach.uOf q₂ x| + |Banach.uOf q₁ x|) ^ (γBar - 1)) := by
      filter_upwards [hu₁, hu₂] with x hx₁ hx₂
      simp [hx₁, hx₂]
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq heq bG_val.toMemLp)
  -- Child C: K0 dominators.
  have hHabs_K0 :
      IsHK0AbsDominator (d := d) hpow (Banach.mOf q₁) (Banach.mOf q₂)
                          (Banach.DuOf q₁) (Banach.DuOf q₂) hpow.C :=
    Banach.isHK0AbsDominator_of_paperHypotheses hpow hHat0 hAgree
      (Banach.mOf q₁) (Banach.mOf q₂) (Banach.DuOf q₁) (Banach.DuOf q₂)
  have hmDpH_K0 :
      IsmDpHK0Dominator (d := d) hpow (Banach.mOf q₁) (Banach.mOf q₂)
                          (Banach.DuOf q₁) (Banach.DuOf q₂) :=
    Banach.isMDpHK0Dominator_of_paperHypotheses hpow hHat0 hAgree
      (Banach.mOf q₁) (Banach.mOf q₂) (Banach.DuOf q₁) (Banach.DuOf q₂)
  -- K0 segment nonnegativity at the Banach pair (signed family).
  have hNonneg_q :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          0 ≤ cxComb (Banach.mOf q₁) (Banach.mOf q₂) t x :=
    Banach.K0_Aepsi_segment_pos_nn hq₁_K0 hq₂_K0
  -- Transport `hF_unreg_meas_bare` and `hF_gat_meas_bare` to the Banach pair.
  have hF_unreg_K0_eq :=
    aepsiIntegrandAt_unreg_K0_congr_ae V H DpH Dν η ν
      hm₁ hm₂ hu₁ hu₂ hDu₁ hDu₂
  have hF_gat_eq :=
    aepsiIntegrandAt_gateaux_congr_ae γBar Dν ν
      hu₁ hu₂ hDu₁ hDu₂
  have hF_unreg_meas_q :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        MeasureTheory.AEStronglyMeasurable
          (fun x => aepsiIntegrandAt_unreg_K0 V H DpH
                      (Banach.DuOf q₁) (Banach.DuOf q₂)
                      (Banach.mOf q₁) (Banach.mOf q₂)
                      (Banach.uOf q₁) (Banach.uOf q₂) Dν η ν x t)
          (MeasureTheory.volume.restrict (UnitCube d)) := by
    intro t ht
    have hmeas := hF_unreg_meas_bare t ht
    refine hmeas.congr ?_
    filter_upwards [hF_unreg_K0_eq] with x hx
    exact (hx t).symm
  have hF_gat_meas_q :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        MeasureTheory.AEStronglyMeasurable
          (fun x => aepsiIntegrandAt_gateaux γBar
                      (Banach.DuOf q₁) (Banach.DuOf q₂)
                      (Banach.uOf q₁) (Banach.uOf q₂) Dν ν x t)
          (MeasureTheory.volume.restrict (UnitCube d)) := by
    intro t ht
    have hmeas := hF_gat_meas_bare t ht
    refine hmeas.congr ?_
    filter_upwards [hF_gat_eq] with x hx
    exact (hx t).symm
  -- Pointwise K0 bound on `aepsiIntegrandAt_unreg`.
  have hbound_unreg :=
    aepsiIntegrandAt_unreg_pointwise_bound_K0 V hpow hpow.hC
      (Banach.mOf q₁) (Banach.mOf q₂) (Banach.uOf q₁) (Banach.uOf q₂)
      (Banach.DuOf q₁) (Banach.DuOf q₂)
      Dν η ν hHabs_K0 hmDpH_K0
  -- Derive `1 ≤ ENNReal.ofReal γBarReal` from the `Fact` instance.
  have hγ_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal γBarReal :=
    (Fact.out : (1 : ℝ≥0∞) ≤ ENNReal.ofReal γBarReal)
  -- Assemble the K0 bundle at the Banach coercions.
  have dataQ :
      HemicontSegmentDataK0 V H DpH γBar
        (Banach.DuOf q₁) (Banach.DuOf q₂)
        (Banach.mOf q₁) (Banach.mOf q₂)
        (Banach.uOf q₁) (Banach.uOf q₂) Dν η ν :=
    { hNonneg := hNonneg_q
      g_unreg := Banach.g_unreg_natural hpow.α hpow.β hpow.C hpow.C V
                    (Banach.DuOf q₁) (Banach.DuOf q₂)
                    (Banach.mOf q₁) (Banach.mOf q₂)
                    (Banach.uOf q₁) (Banach.uOf q₂) Dν η ν
      g_gat := Banach.g_gat_natural γBar
                    (Banach.DuOf q₁) (Banach.DuOf q₂)
                    (Banach.uOf q₁) (Banach.uOf q₂) Dν ν
      hg_unreg_int :=
        -- Paper-faithful Term-5 split via `g_unreg_natural_integrableOn_min`:
        -- `((|m̄|+|μ|)+1)*|ν| = (|m̄|+|μ|)*|ν| + |ν|`, with the second piece
        -- discharged from `|ν| ∈ L^γ̄` and `1 ≤ γ̄` (iter-0785 helper route).
        Banach.g_unreg_natural_integrableOn_min (α := hpow.α) (β := hpow.β)
          (C := hpow.C) (C' := hpow.C) (V := V)
          (Dυ := Banach.DuOf q₁) (Dῡ := Banach.DuOf q₂)
          (μ := Banach.mOf q₁) (mBar := Banach.mOf q₂)
          (υ := Banach.uOf q₁) (ῡ := Banach.uOf q₂)
          (Dν := Dν) (η := η) (ν := ν)
          hβconj hγconj hγ_one_le hη hDν hν_γ hV bhΔυ
          bhΔp_pow bhΔm_pow bhΔm_grad bhΔm_endpoint bhΔm
      hg_gat_int := by
        have :=
          Banach.g_gat_natural_integrableOn (γBar := γBarReal)
            (Dυ := Banach.DuOf q₁) (Dῡ := Banach.DuOf q₂)
            (υ := Banach.uOf q₁) (ῡ := Banach.uOf q₂)
            (Dν := Dν) (ν := ν) hγconj hDν hν_γ
            (hγBar_eq ▸ bhG_grad) (hγBar_eq ▸ bhG_val)
        simpa [hγBar_eq] using this
      hF_unreg_meas := hF_unreg_meas_q
      hF_unreg_bound := by
        intro t ht
        filter_upwards [hbound_unreg, hNonneg_q] with x hxBd hxNN
        have hbd := hxBd t ht (hxNN t ht)
        have hagree := aepsiIntegrandAt_unreg_K0_eq_unreg
          V H DpH (Banach.DuOf q₁) (Banach.DuOf q₂)
          (Banach.mOf q₁) (Banach.mOf q₂)
          (Banach.uOf q₁) (Banach.uOf q₂)
          Dν η ν x t
        rw [hagree]
        exact hbd
      hF_gat_meas := hF_gat_meas_q
      hF_gat_bound := by
        intro t ht
        have hgat :=
          aepsiIntegrandAt_gateaux_pointwise_bound_product (d := d)
            (γBar := γBar) hγ_one_lt
            (Banach.DuOf q₁) (Banach.DuOf q₂)
            (Banach.uOf q₁) (Banach.uOf q₂) Dν ν
        refine MeasureTheory.ae_of_all _ ?_
        intro x
        exact hgat x t ht }
  -- Transport from `(mOf q_i, …)` to `(mLim + g_i, uLim, DuLim)`.
  exact HemicontSegmentDataK0.ae_eq V H DpH γBar Dν η ν
    hm₁ hm₂ hu₁ hu₂ hDu₁ hDu₂ dataQ

/-! ## v8 K0 — transport-family K0 minimal-shape composer
(`infra-P6-K0-min-composer-transport`, audit 2026-05-22).

Transport mirror of the iter-0789 set-min composer
`hemicontSegmentData_set_narrow_K0_min_of_paperHypotheses` (and of the
iter-0790 signed-min composer
`hemicontSegmentData_signed_narrow_K0_min_of_paperHypotheses`).
Minimal-shape sibling of the iter-0760 transport composer
`hemicontSegmentData_transport_narrow_K0_of_paperHypotheses`: same
preconditions and same return, except

* the over-specified `bΔm1` `MemLpPer βBarReal'` dominator is dropped
  (eight dominator inputs instead of nine), in line with the iter-0788
  `TransportFamilyNarrowDominatorsK0Min` bundle;
* the `hν_β` test-direction regularity is dropped (the legacy Term-5
  pair consumed it; the new helper does not);
* the Term-5 integrability for the unreg piece is discharged via the
  iter-0785 helper `g_unreg_natural_integrableOn_min` (route
  `((|m̄|+|μ|)+1)·|ν| = (|m̄|+|μ|)·|ν| + |ν|`, using `1 ≤ γ̄` and
  `|ν| ∈ L^γ̄` on the unit cube);
* the inline eight Banach-side `MemLp.ae_eq` blocks replace the call to
  `Banach.segMemLpBundle_of_transportPaper` (which would still demand
  `bΔm1`).

Transport collapse: the density-side endpoints stay at `mLim`, so all
eight inline transports use just `hm₁, hm₂` (both saying
`mOf q_i =ᵐ mLim`); the `u`/`Du`-sides carry `ψ_i` / `∂_i ψ_j`. Signature
does **not** require `hβ_ge_one`: the dropped `bΔm1` cert was the only
field that forced the non-paper-faithful side condition. -/

noncomputable def hemicontSegmentData_transport_narrow_K0_min_of_paperHypotheses
    {d : ℕ} {γBarReal βBarReal βBarReal' γBarReal' γBar : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    (hβconj : βBarReal'.HolderConjugate βBarReal)
    (hγconj : γBarReal'.HolderConjugate γBarReal)
    {mLim uLim : (Fin d → ℝ) → ℝ}
    {DuLim : Fin d → (Fin d → ℝ) → ℝ}
    (hmLim_memLp : Periodic.MemLpPer (d := d)
                      (ENNReal.ofReal βBarReal) mLim)
    (huLim_sob : Periodic.MemSobolevPer (d := d)
                      (ENNReal.ofReal γBarReal) uLim)
    (hDuLim_memLp_γ : ∀ i, Periodic.MemLpPer (d := d)
                              (ENNReal.ofReal γBarReal) (DuLim i))
    -- Pointwise a.e.-nonneg of the primal `mLim` (transport leaves `m`
    -- fixed, so this is the only nonneg input we need).
    (hmLim_nn : 0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                      (UnitCube d)] mLim)
    -- Transport-family perturbations: smooth periodic test directions.
    (ψ₁ ψ₂ : Periodic.SmoothPeriodic d)
    -- Eight bare-function `MemLpPer p`-of-power certificates (NO `bΔm1`).
    (bΔυ : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x => |(uLim + (ψ₂ : (Fin d → ℝ) → ℝ)) x|
                          + |(uLim + (ψ₁ : (Fin d → ℝ) → ℝ)) x|))
    (bΔp_pow : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x =>
                ‖fun i =>
                    |(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₂
                                  : (Fin d → ℝ) → ℝ)) x|
                  + |(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₁
                                  : (Fin d → ℝ) → ℝ)) x|‖ ^ hpow.α + 1))
    (bΔm_pow : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x => (|mLim x| + |mLim x|) ^ hpow.β + 1))
    (bΔm_grad : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => (|mLim x| + |mLim x|)
                  * ‖fun i =>
                      |(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₂
                                    : (Fin d → ℝ) → ℝ)) x|
                    + |(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₁
                                    : (Fin d → ℝ) → ℝ)) x|‖ ^ (hpow.α - 1)))
    (bΔm_endpoint : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => (|mLim x| + |mLim x|) ^ (1 + hpow.β - hpow.β / hpow.α)))
    (bΔm : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => |mLim x| + |mLim x|))
    (bG_grad : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x =>
                (∑ i,
                    (|(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₂
                                    : (Fin d → ℝ) → ℝ)) x|
                      + |(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₁
                                    : (Fin d → ℝ) → ℝ)) x|) ^ (2 : ℕ))
                    ^ ((γBar - 1) / 2)))
    (bG_val : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => (|(uLim + (ψ₂ : (Fin d → ℝ) → ℝ)) x|
                          + |(uLim + (ψ₁ : (Fin d → ℝ) → ℝ)) x|)
                          ^ (γBar - 1)))
    (hγ_one_lt : 1 < γBar)
    (Dν : Fin d → (Fin d → ℝ) → ℝ) (η ν : (Fin d → ℝ) → ℝ)
    (hη : MemLpPer (d := d) (ENNReal.ofReal βBarReal) η)
    (hDν : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dν i))
    (hν_γ : MemLpPer (d := d) (ENNReal.ofReal γBarReal) ν)
    (hγBar_eq : γBar = γBarReal)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    -- Bare-function measurability of the K0 unreg integrand and the
    -- Gateaux integrand at the unshifted transport endpoints.
    (hF_unreg_meas_bare : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x => aepsiIntegrandAt_unreg_K0 V H DpH
                    (fun i => DuLim i + (Periodic.SmoothPeriodic.partialDeriv
                                            i ψ₁ : (Fin d → ℝ) → ℝ))
                    (fun i => DuLim i + (Periodic.SmoothPeriodic.partialDeriv
                                            i ψ₂ : (Fin d → ℝ) → ℝ))
                    mLim mLim
                    (uLim + (ψ₁ : (Fin d → ℝ) → ℝ))
                    (uLim + (ψ₂ : (Fin d → ℝ) → ℝ))
                    Dν η ν x t)
        (MeasureTheory.volume.restrict (UnitCube d)))
    (hF_gat_meas_bare : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x => aepsiIntegrandAt_gateaux γBar
                    (fun i => DuLim i + (Periodic.SmoothPeriodic.partialDeriv
                                            i ψ₁ : (Fin d → ℝ) → ℝ))
                    (fun i => DuLim i + (Periodic.SmoothPeriodic.partialDeriv
                                            i ψ₂ : (Fin d → ℝ) → ℝ))
                    (uLim + (ψ₁ : (Fin d → ℝ) → ℝ))
                    (uLim + (ψ₂ : (Fin d → ℝ) → ℝ))
                    Dν ν x t)
        (MeasureTheory.volume.restrict (UnitCube d))) :
    HemicontSegmentDataK0 V H DpH γBar
      (fun i => DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₁
                            : (Fin d → ℝ) → ℝ))
      (fun i => DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₂
                            : (Fin d → ℝ) → ℝ))
      mLim mLim
      (uLim + (ψ₁ : (Fin d → ℝ) → ℝ))
      (uLim + (ψ₂ : (Fin d → ℝ) → ℝ))
      Dν η ν := by
  -- Build the two Banach pairs via Child A (transport).
  set q₁ := Banach.bareToBanachPair_transport_paper (d := d)
              (βBarReal := βBarReal) (γBarReal := γBarReal)
              (DuLim := DuLim)
              hmLim_memLp huLim_sob hDuLim_memLp_γ ψ₁ with hq₁_def
  set q₂ := Banach.bareToBanachPair_transport_paper (d := d)
              (βBarReal := βBarReal) (γBarReal := γBarReal)
              (DuLim := DuLim)
              hmLim_memLp huLim_sob hDuLim_memLp_γ ψ₂ with hq₂_def
  -- K0 memberships: transport leaves `m` fixed at `mLim`, so `hmLim_nn`
  -- alone suffices via the transport-narrow K0 producer.
  have hq₁_K0 : q₁ ∈ Banach.K0_Aepsi d βBarReal γBarReal :=
    Banach.bareToBanachPair_transport_paper_mem_K0Aepsi (uLim := uLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hmLim_nn ψ₁
  have hq₂_K0 : q₂ ∈ Banach.K0_Aepsi d βBarReal γBarReal :=
    Banach.bareToBanachPair_transport_paper_mem_K0Aepsi (uLim := uLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hmLim_nn ψ₂
  -- Six a.e.-coercion identities from Child A (transport).
  have hm₁ :
      Banach.mOf q₁ =ᵐ[MeasureTheory.Measure.restrict
                  MeasureTheory.volume (UnitCube d)] mLim :=
    Banach.bareToBanachPair_transport_paper_mOf_ae_eq (d := d)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ ψ₁
  have hm₂ :
      Banach.mOf q₂ =ᵐ[MeasureTheory.Measure.restrict
                  MeasureTheory.volume (UnitCube d)] mLim :=
    Banach.bareToBanachPair_transport_paper_mOf_ae_eq (d := d)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ ψ₂
  have hu₁ :
      Banach.uOf q₁ =ᵐ[MeasureTheory.Measure.restrict
                  MeasureTheory.volume (UnitCube d)]
          (uLim + (ψ₁ : (Fin d → ℝ) → ℝ)) :=
    Banach.bareToBanachPair_transport_paper_uOf_ae_eq (d := d)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ ψ₁
  have hu₂ :
      Banach.uOf q₂ =ᵐ[MeasureTheory.Measure.restrict
                  MeasureTheory.volume (UnitCube d)]
          (uLim + (ψ₂ : (Fin d → ℝ) → ℝ)) :=
    Banach.bareToBanachPair_transport_paper_uOf_ae_eq (d := d)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ ψ₂
  have hDu₁ : ∀ i,
      Banach.DuOf q₁ i =ᵐ[MeasureTheory.Measure.restrict
                      MeasureTheory.volume (UnitCube d)]
          (DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₁
                        : (Fin d → ℝ) → ℝ)) := fun i =>
    Banach.bareToBanachPair_transport_paper_DuOf_ae_eq (d := d)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ ψ₁ i
  have hDu₂ : ∀ i,
      Banach.DuOf q₂ i =ᵐ[MeasureTheory.Measure.restrict
                      MeasureTheory.volume (UnitCube d)]
          (DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₂
                        : (Fin d → ℝ) → ℝ)) := fun i =>
    Banach.bareToBanachPair_transport_paper_DuOf_ae_eq (d := d)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ ψ₂ i
  -- Inline transport of the eight bare certs to the Banach pair endpoints.
  -- Mirror of the iter-0789 set-min composer, adapted to the transport
  -- shape (both Banach `m`-projections coerce to `mLim`; `u`/`Du`-sides
  -- carry `ψ_i` / `∂_i ψ_j`).
  -- Joint pointwise version of `(hDu₁, hDu₂)`.
  have hDuAll :
      ∀ᵐ x ∂(MeasureTheory.Measure.restrict
              MeasureTheory.volume (UnitCube d)),
        ∀ i,
          Banach.DuOf q₁ i x
            = (DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₁
                            : (Fin d → ℝ) → ℝ)) x ∧
          Banach.DuOf q₂ i x
            = (DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₂
                            : (Fin d → ℝ) → ℝ)) x := by
    rw [MeasureTheory.ae_all_iff]
    intro i
    filter_upwards [hDu₁ i, hDu₂ i] with x ha hb
    exact ⟨ha, hb⟩
  -- (1) `bhΔυ`.
  have bhΔυ :
      MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x => |Banach.uOf q₂ x| + |Banach.uOf q₁ x|) := by
    have heq :
        (fun x => |(uLim + (ψ₂ : (Fin d → ℝ) → ℝ)) x|
                    + |(uLim + (ψ₁ : (Fin d → ℝ) → ℝ)) x|)
          =ᵐ[MeasureTheory.Measure.restrict
                MeasureTheory.volume (UnitCube d)]
            (fun x => |Banach.uOf q₂ x| + |Banach.uOf q₁ x|) := by
      filter_upwards [hu₁, hu₂] with x hx₁ hx₂
      simp [hx₁, hx₂]
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq heq bΔυ.toMemLp)
  -- (2) `bhΔp_pow`.
  have bhΔp_pow :
      MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x =>
          ‖fun i => |Banach.DuOf q₂ i x| + |Banach.DuOf q₁ i x|‖ ^ hpow.α
            + 1) := by
    have heq :
        (fun x =>
            ‖fun i =>
                |(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₂
                              : (Fin d → ℝ) → ℝ)) x|
              + |(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₁
                              : (Fin d → ℝ) → ℝ)) x|‖ ^ hpow.α + 1)
          =ᵐ[MeasureTheory.Measure.restrict
                MeasureTheory.volume (UnitCube d)]
            (fun x =>
              ‖fun i => |Banach.DuOf q₂ i x| + |Banach.DuOf q₁ i x|‖
                ^ hpow.α + 1) := by
      filter_upwards [hDuAll] with x hx
      have hfun :
          (fun i =>
              |(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₂
                            : (Fin d → ℝ) → ℝ)) x|
            + |(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₁
                            : (Fin d → ℝ) → ℝ)) x|)
            = (fun i => |Banach.DuOf q₂ i x| + |Banach.DuOf q₁ i x|) := by
        funext i
        rcases hx i with ⟨h₁, h₂⟩
        simp [h₁, h₂]
      rw [hfun]
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq heq bΔp_pow.toMemLp)
  -- (3) `bhΔm_pow`. (Transport: both `m`-sides coerce to `mLim`.)
  have bhΔm_pow :
      MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x => (|Banach.mOf q₂ x| + |Banach.mOf q₁ x|) ^ hpow.β + 1) := by
    have heq :
        (fun x => (|mLim x| + |mLim x|) ^ hpow.β + 1)
          =ᵐ[MeasureTheory.Measure.restrict
                MeasureTheory.volume (UnitCube d)]
            (fun x =>
              (|Banach.mOf q₂ x| + |Banach.mOf q₁ x|) ^ hpow.β + 1) := by
      filter_upwards [hm₁, hm₂] with x hx₁ hx₂
      simp [hx₁, hx₂]
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq heq bΔm_pow.toMemLp)
  -- (4) `bhΔm_grad`.
  have bhΔm_grad :
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => (|Banach.mOf q₂ x| + |Banach.mOf q₁ x|)
            * ‖fun i => |Banach.DuOf q₂ i x| + |Banach.DuOf q₁ i x|‖
              ^ (hpow.α - 1)) := by
    have heq :
        (fun x => (|mLim x| + |mLim x|)
            * ‖fun i =>
                |(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₂
                              : (Fin d → ℝ) → ℝ)) x|
              + |(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₁
                              : (Fin d → ℝ) → ℝ)) x|‖ ^ (hpow.α - 1))
          =ᵐ[MeasureTheory.Measure.restrict
                MeasureTheory.volume (UnitCube d)]
            (fun x => (|Banach.mOf q₂ x| + |Banach.mOf q₁ x|)
              * ‖fun i =>
                  |Banach.DuOf q₂ i x| + |Banach.DuOf q₁ i x|‖
                  ^ (hpow.α - 1)) := by
      filter_upwards [hm₁, hm₂, hDuAll] with x hx₁ hx₂ hxDu
      have hfun :
          (fun i =>
              |(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₂
                            : (Fin d → ℝ) → ℝ)) x|
            + |(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₁
                            : (Fin d → ℝ) → ℝ)) x|)
            = (fun i => |Banach.DuOf q₂ i x| + |Banach.DuOf q₁ i x|) := by
        funext i
        rcases hxDu i with ⟨h₁, h₂⟩
        simp [h₁, h₂]
      rw [hfun, hx₁, hx₂]
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq heq bΔm_grad.toMemLp)
  -- (5) `bhΔm_endpoint`.
  have bhΔm_endpoint :
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => (|Banach.mOf q₂ x| + |Banach.mOf q₁ x|)
            ^ (1 + hpow.β - hpow.β / hpow.α)) := by
    have heq :
        (fun x => (|mLim x| + |mLim x|)
            ^ (1 + hpow.β - hpow.β / hpow.α))
          =ᵐ[MeasureTheory.Measure.restrict
                MeasureTheory.volume (UnitCube d)]
            (fun x => (|Banach.mOf q₂ x| + |Banach.mOf q₁ x|)
              ^ (1 + hpow.β - hpow.β / hpow.α)) := by
      filter_upwards [hm₁, hm₂] with x hx₁ hx₂
      simp [hx₁, hx₂]
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq heq bΔm_endpoint.toMemLp)
  -- (6) `bhΔm`.
  have bhΔm :
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => |Banach.mOf q₂ x| + |Banach.mOf q₁ x|) := by
    have heq :
        (fun x => |mLim x| + |mLim x|)
          =ᵐ[MeasureTheory.Measure.restrict
                MeasureTheory.volume (UnitCube d)]
            (fun x => |Banach.mOf q₂ x| + |Banach.mOf q₁ x|) := by
      filter_upwards [hm₁, hm₂] with x hx₁ hx₂
      simp [hx₁, hx₂]
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq heq bΔm.toMemLp)
  -- (7) `bhG_grad`.
  have bhG_grad :
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x =>
          (∑ i, (|Banach.DuOf q₂ i x| + |Banach.DuOf q₁ i x|) ^ (2 : ℕ))
            ^ ((γBar - 1) / 2)) := by
    have heq :
        (fun x =>
            (∑ i,
                (|(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₂
                                : (Fin d → ℝ) → ℝ)) x|
                  + |(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₁
                                : (Fin d → ℝ) → ℝ)) x|) ^ (2 : ℕ))
              ^ ((γBar - 1) / 2))
          =ᵐ[MeasureTheory.Measure.restrict
                MeasureTheory.volume (UnitCube d)]
            (fun x =>
              (∑ i,
                (|Banach.DuOf q₂ i x| + |Banach.DuOf q₁ i x|) ^ (2 : ℕ))
                ^ ((γBar - 1) / 2)) := by
      filter_upwards [hDuAll] with x hx
      have hsum :
          (∑ i,
              (|(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₂
                              : (Fin d → ℝ) → ℝ)) x|
                + |(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₁
                              : (Fin d → ℝ) → ℝ)) x|) ^ (2 : ℕ))
            = ∑ i,
              (|Banach.DuOf q₂ i x| + |Banach.DuOf q₁ i x|) ^ (2 : ℕ) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        rcases hx i with ⟨h₁, h₂⟩
        simp [h₁, h₂]
      rw [hsum]
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq heq bG_grad.toMemLp)
  -- (8) `bhG_val`.
  have bhG_val :
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => (|Banach.uOf q₂ x| + |Banach.uOf q₁ x|) ^ (γBar - 1)) := by
    have heq :
        (fun x => (|(uLim + (ψ₂ : (Fin d → ℝ) → ℝ)) x|
                    + |(uLim + (ψ₁ : (Fin d → ℝ) → ℝ)) x|) ^ (γBar - 1))
          =ᵐ[MeasureTheory.Measure.restrict
                MeasureTheory.volume (UnitCube d)]
            (fun x =>
              (|Banach.uOf q₂ x| + |Banach.uOf q₁ x|) ^ (γBar - 1)) := by
      filter_upwards [hu₁, hu₂] with x hx₁ hx₂
      simp [hx₁, hx₂]
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq heq bG_val.toMemLp)
  -- Child C: K0 dominators.
  have hHabs_K0 :
      IsHK0AbsDominator (d := d) hpow (Banach.mOf q₁) (Banach.mOf q₂)
                          (Banach.DuOf q₁) (Banach.DuOf q₂) hpow.C :=
    Banach.isHK0AbsDominator_of_paperHypotheses hpow hHat0 hAgree
      (Banach.mOf q₁) (Banach.mOf q₂) (Banach.DuOf q₁) (Banach.DuOf q₂)
  have hmDpH_K0 :
      IsmDpHK0Dominator (d := d) hpow (Banach.mOf q₁) (Banach.mOf q₂)
                          (Banach.DuOf q₁) (Banach.DuOf q₂) :=
    Banach.isMDpHK0Dominator_of_paperHypotheses hpow hHat0 hAgree
      (Banach.mOf q₁) (Banach.mOf q₂) (Banach.DuOf q₁) (Banach.DuOf q₂)
  -- K0 segment nonnegativity at the Banach pair (transport family).
  have hNonneg_q :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          0 ≤ cxComb (Banach.mOf q₁) (Banach.mOf q₂) t x :=
    Banach.K0_Aepsi_segment_pos_nn hq₁_K0 hq₂_K0
  -- Transport `hF_unreg_meas_bare` and `hF_gat_meas_bare` to the Banach pair.
  have hF_unreg_K0_eq :=
    aepsiIntegrandAt_unreg_K0_congr_ae V H DpH Dν η ν
      hm₁ hm₂ hu₁ hu₂ hDu₁ hDu₂
  have hF_gat_eq :=
    aepsiIntegrandAt_gateaux_congr_ae γBar Dν ν
      hu₁ hu₂ hDu₁ hDu₂
  have hF_unreg_meas_q :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        MeasureTheory.AEStronglyMeasurable
          (fun x => aepsiIntegrandAt_unreg_K0 V H DpH
                      (Banach.DuOf q₁) (Banach.DuOf q₂)
                      (Banach.mOf q₁) (Banach.mOf q₂)
                      (Banach.uOf q₁) (Banach.uOf q₂) Dν η ν x t)
          (MeasureTheory.volume.restrict (UnitCube d)) := by
    intro t ht
    have hmeas := hF_unreg_meas_bare t ht
    refine hmeas.congr ?_
    filter_upwards [hF_unreg_K0_eq] with x hx
    exact (hx t).symm
  have hF_gat_meas_q :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        MeasureTheory.AEStronglyMeasurable
          (fun x => aepsiIntegrandAt_gateaux γBar
                      (Banach.DuOf q₁) (Banach.DuOf q₂)
                      (Banach.uOf q₁) (Banach.uOf q₂) Dν ν x t)
          (MeasureTheory.volume.restrict (UnitCube d)) := by
    intro t ht
    have hmeas := hF_gat_meas_bare t ht
    refine hmeas.congr ?_
    filter_upwards [hF_gat_eq] with x hx
    exact (hx t).symm
  -- Pointwise K0 bound on `aepsiIntegrandAt_unreg`.
  have hbound_unreg :=
    aepsiIntegrandAt_unreg_pointwise_bound_K0 V hpow hpow.hC
      (Banach.mOf q₁) (Banach.mOf q₂) (Banach.uOf q₁) (Banach.uOf q₂)
      (Banach.DuOf q₁) (Banach.DuOf q₂)
      Dν η ν hHabs_K0 hmDpH_K0
  -- Derive `1 ≤ ENNReal.ofReal γBarReal` from the `Fact` instance.
  have hγ_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal γBarReal :=
    (Fact.out : (1 : ℝ≥0∞) ≤ ENNReal.ofReal γBarReal)
  -- Assemble the K0 bundle at the Banach coercions.
  have dataQ :
      HemicontSegmentDataK0 V H DpH γBar
        (Banach.DuOf q₁) (Banach.DuOf q₂)
        (Banach.mOf q₁) (Banach.mOf q₂)
        (Banach.uOf q₁) (Banach.uOf q₂) Dν η ν :=
    { hNonneg := hNonneg_q
      g_unreg := Banach.g_unreg_natural hpow.α hpow.β hpow.C hpow.C V
                    (Banach.DuOf q₁) (Banach.DuOf q₂)
                    (Banach.mOf q₁) (Banach.mOf q₂)
                    (Banach.uOf q₁) (Banach.uOf q₂) Dν η ν
      g_gat := Banach.g_gat_natural γBar
                    (Banach.DuOf q₁) (Banach.DuOf q₂)
                    (Banach.uOf q₁) (Banach.uOf q₂) Dν ν
      hg_unreg_int :=
        -- Paper-faithful Term-5 split via `g_unreg_natural_integrableOn_min`
        -- (iter-0785 helper). Drops both the `bΔm1` cert and the `hν_β`
        -- regularity, and removes the `hβ_ge_one` side condition.
        Banach.g_unreg_natural_integrableOn_min (α := hpow.α) (β := hpow.β)
          (C := hpow.C) (C' := hpow.C) (V := V)
          (Dυ := Banach.DuOf q₁) (Dῡ := Banach.DuOf q₂)
          (μ := Banach.mOf q₁) (mBar := Banach.mOf q₂)
          (υ := Banach.uOf q₁) (ῡ := Banach.uOf q₂)
          (Dν := Dν) (η := η) (ν := ν)
          hβconj hγconj hγ_one_le hη hDν hν_γ hV bhΔυ
          bhΔp_pow bhΔm_pow bhΔm_grad bhΔm_endpoint bhΔm
      hg_gat_int := by
        have :=
          Banach.g_gat_natural_integrableOn (γBar := γBarReal)
            (Dυ := Banach.DuOf q₁) (Dῡ := Banach.DuOf q₂)
            (υ := Banach.uOf q₁) (ῡ := Banach.uOf q₂)
            (Dν := Dν) (ν := ν) hγconj hDν hν_γ
            (hγBar_eq ▸ bhG_grad) (hγBar_eq ▸ bhG_val)
        simpa [hγBar_eq] using this
      hF_unreg_meas := hF_unreg_meas_q
      hF_unreg_bound := by
        intro t ht
        filter_upwards [hbound_unreg, hNonneg_q] with x hxBd hxNN
        have hbd := hxBd t ht (hxNN t ht)
        have hagree := aepsiIntegrandAt_unreg_K0_eq_unreg
          V H DpH (Banach.DuOf q₁) (Banach.DuOf q₂)
          (Banach.mOf q₁) (Banach.mOf q₂)
          (Banach.uOf q₁) (Banach.uOf q₂)
          Dν η ν x t
        rw [hagree]
        exact hbd
      hF_gat_meas := hF_gat_meas_q
      hF_gat_bound := by
        intro t ht
        have hgat :=
          aepsiIntegrandAt_gateaux_pointwise_bound_product (d := d)
            (γBar := γBar) hγ_one_lt
            (Banach.DuOf q₁) (Banach.DuOf q₂)
            (Banach.uOf q₁) (Banach.uOf q₂) Dν ν
        refine MeasureTheory.ae_of_all _ ?_
        intro x
        exact hgat x t ht }
  -- Transport from `(mOf qᵢ, …)` to `(mLim, uLim+ψᵢ, DuLim+∂ᵢψ)`.
  exact HemicontSegmentDataK0.ae_eq V H DpH γBar Dν η ν
    hm₁ hm₂ hu₁ hu₂ hDu₁ hDu₂ dataQ

/-- **Sanity-check `example`** for the K0 transport-narrow minimal-shape
composer. Mirror of the iter-0760 sanity-check, with `bΔm1` and `hν_β`
dropped from the input list. -/
example
    {d : ℕ} {γBarReal βBarReal βBarReal' γBarReal' γBar : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    (hβconj : βBarReal'.HolderConjugate βBarReal)
    (hγconj : γBarReal'.HolderConjugate γBarReal)
    {mLim uLim : (Fin d → ℝ) → ℝ}
    {DuLim : Fin d → (Fin d → ℝ) → ℝ}
    (hmLim_memLp : Periodic.MemLpPer (d := d)
                      (ENNReal.ofReal βBarReal) mLim)
    (huLim_sob : Periodic.MemSobolevPer (d := d)
                      (ENNReal.ofReal γBarReal) uLim)
    (hDuLim_memLp_γ : ∀ i, Periodic.MemLpPer (d := d)
                              (ENNReal.ofReal γBarReal) (DuLim i))
    (hmLim_nn : 0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                      (UnitCube d)] mLim)
    (ψ₁ ψ₂ : Periodic.SmoothPeriodic d)
    (dom : TransportFamilyNarrowDominatorsK0Min
              (βBarReal' := βBarReal') (γBarReal' := γBarReal') (γBar := γBar)
              mLim uLim DuLim ψ₁ ψ₂ hpow.α hpow.β)
    (hγ_one_lt : 1 < γBar)
    (Dν : Fin d → (Fin d → ℝ) → ℝ) (η ν : (Fin d → ℝ) → ℝ)
    (hη : MemLpPer (d := d) (ENNReal.ofReal βBarReal) η)
    (hDν : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dν i))
    (hν_γ : MemLpPer (d := d) (ENNReal.ofReal γBarReal) ν)
    (hγBar_eq : γBar = γBarReal)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (hF_unreg_meas_bare : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x => aepsiIntegrandAt_unreg_K0 V H DpH
                    (fun i => DuLim i + (Periodic.SmoothPeriodic.partialDeriv
                                            i ψ₁ : (Fin d → ℝ) → ℝ))
                    (fun i => DuLim i + (Periodic.SmoothPeriodic.partialDeriv
                                            i ψ₂ : (Fin d → ℝ) → ℝ))
                    mLim mLim
                    (uLim + (ψ₁ : (Fin d → ℝ) → ℝ))
                    (uLim + (ψ₂ : (Fin d → ℝ) → ℝ))
                    Dν η ν x t)
        (MeasureTheory.volume.restrict (UnitCube d)))
    (hF_gat_meas_bare : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x => aepsiIntegrandAt_gateaux γBar
                    (fun i => DuLim i + (Periodic.SmoothPeriodic.partialDeriv
                                            i ψ₁ : (Fin d → ℝ) → ℝ))
                    (fun i => DuLim i + (Periodic.SmoothPeriodic.partialDeriv
                                            i ψ₂ : (Fin d → ℝ) → ℝ))
                    (uLim + (ψ₁ : (Fin d → ℝ) → ℝ))
                    (uLim + (ψ₂ : (Fin d → ℝ) → ℝ))
                    Dν ν x t)
        (MeasureTheory.volume.restrict (UnitCube d))) :
    HemicontSegmentDataK0 V H DpH γBar
      (fun i => DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₁
                            : (Fin d → ℝ) → ℝ))
      (fun i => DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₂
                            : (Fin d → ℝ) → ℝ))
      mLim mLim
      (uLim + (ψ₁ : (Fin d → ℝ) → ℝ))
      (uLim + (ψ₂ : (Fin d → ℝ) → ℝ))
      Dν η ν :=
  hemicontSegmentData_transport_narrow_K0_min_of_paperHypotheses
    (γBarReal := γBarReal) (βBarReal := βBarReal)
    (βBarReal' := βBarReal') (γBarReal' := γBarReal') (γBar := γBar)
    (V := V) (H := H) (DpH := DpH)
    hpow hHat0 hAgree hβconj hγconj
    hmLim_memLp huLim_sob hDuLim_memLp_γ hmLim_nn
    ψ₁ ψ₂
    dom.bΔυ dom.bΔp_pow dom.bΔm_pow dom.bΔm_grad
    dom.bΔm_endpoint dom.bΔm dom.bG_grad dom.bG_val
    hγ_one_lt Dν η ν hη hDν hν_γ hγBar_eq hV
    hF_unreg_meas_bare hF_gat_meas_bare

/-! ### K0-min producer: `mintyDataSetNarrowK0Min_of_paperHypotheses`
(`infra-P6-K0-min-mintyData-consumers`, audit 2026-05-22).

K0 minimal-shape sibling of `mintyDataSetNarrowK0_of_paperHypotheses`
(set K0 consumer, line 14342). Per-pair narrow segment-data aggregator
on the set family in the K0 minimal form: consumes a
`SetFamilyNarrowMintyResidueK0Min` (iter 0796, no `bΔm1` field) and
calls the iter-0789 minimal composer
`hemicontSegmentData_set_narrow_K0_min_of_paperHypotheses` (eight
dominators, no `hβ_ge_one`). Body byte-equal to the K0 sibling except
for the residue type, the composer call, and the removal of the
`segIn.bΔm1` projection (the min composer takes eight dominators). -/
def mintyDataSetNarrowK0Min_of_paperHypotheses
    {d : ℕ} {γBarReal βBarReal βBarReal' γBarReal' γBar : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (wkBundle : StationaryMFG.Theorems.SimplePower.Banach.WeakLimitInputBundleAE
                  (d := d) γBarReal βBarReal)
    (residue : SetFamilyNarrowMintyResidueK0Min (d := d)
                  (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  (γBar := γBar) V H DpH hpow wkBundle) :
    ∀ ⦃μBar ῡ : (Fin d → ℝ) → ℝ⦄ ⦃Dῡ : Fin d → (Fin d → ℝ) → ℝ⦄,
      (μBar, ῡ, Dῡ) ∈
        StationaryMFG.Theorems.SimplePower.Banach.D_set_family_paper
          (d := d) (ENNReal.ofReal βBarReal)
          wkBundle.mLim wkBundle.uLim wkBundle.DuLim →
    ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄ ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
      (μ, υ, Dυ) ∈
        StationaryMFG.Theorems.SimplePower.Banach.D_set_family_paper
          (d := d) (ENNReal.ofReal βBarReal)
          wkBundle.mLim wkBundle.uLim wkBundle.DuLim →
    ∀ (η ν : (Fin d → ℝ) → ℝ) (Dν : Fin d → (Fin d → ℝ) → ℝ),
    Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) η →
    (∀ i, Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dν i)) →
    Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) ν →
    Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal) ν →
      StationaryMFG.Theorems.SimplePower.HemicontSegmentDataK0
        (d := d) V H DpH γBar Dυ Dῡ μ μBar υ ῡ Dν η ν := by
  intro μBar ῡ Dῡ hBar μ υ Dυ hμ η ν Dν hη hDν hν_β hν_γ
  set ρ₁ := Classical.choose hμ with hρ₁_def
  set ρ₂ := Classical.choose hBar with hρ₂_def
  have hρ₁_spec := Classical.choose_spec hμ
  have hρ₂_spec := Classical.choose_spec hBar
  obtain ⟨hρ₁_nn0, hρ₁_lp, hρ₁_per, hμ_eq⟩ := hρ₁_spec
  obtain ⟨hρ₂_nn0, hρ₂_lp, hρ₂_per, hBar_eq⟩ := hρ₂_spec
  rw [Prod.mk.injEq, Prod.mk.injEq] at hμ_eq hBar_eq
  obtain ⟨hμ_eq_m, hμ_eq_u, hμ_eq_Du⟩ := hμ_eq
  obtain ⟨hBar_eq_m, hBar_eq_u, hBar_eq_Du⟩ := hBar_eq
  -- Per-pair K0-min residue inputs (8 dominator fields; no `bΔm1`).
  have segIn := residue.segInputsOf hBar hμ η ν Dν hη hDν hν_β hν_γ
  -- Pointwise nonneg of `ρ₁` (from residue) and `ρ₂` (from membership).
  have hρ₁_nn : ∀ x, 0 ≤ ρ₁ x := residue.ρ₁_nn hBar hμ
  have hρ₂_nn : ∀ x, 0 ≤ ρ₂ x := hρ₂_nn0
  -- Build the K0 bundle at the bare endpoints `(mLim + ρ_i, …)` via the
  -- iter-0789 minimal-shape composer (8 dominators, no `bΔm1`).
  have dataBare :
      StationaryMFG.Theorems.SimplePower.HemicontSegmentDataK0
        (d := d) V H DpH γBar wkBundle.DuLim wkBundle.DuLim
        (wkBundle.mLim + ρ₁) (wkBundle.mLim + ρ₂)
        wkBundle.uLim wkBundle.uLim Dν η ν :=
    hemicontSegmentData_set_narrow_K0_min_of_paperHypotheses
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal') (γBar := γBar)
      (V := V) (H := H) (DpH := DpH)
      hpow residue.hHat0 residue.hAgree residue.hβconj residue.hγconj
      wkBundle.hmLim_memLp wkBundle.huLim_sob
      (fun i => wkBundle.hDuLim_memLp_γ i)
      wkBundle.hmRep_nonneg
      hρ₁_nn hρ₂_nn hρ₁_lp hρ₂_lp
      segIn.bΔυ segIn.bΔp_pow segIn.bΔm_pow segIn.bΔm_grad
      segIn.bΔm_endpoint segIn.bΔm segIn.bG_grad segIn.bG_val
      residue.hγ_one_lt Dν η ν
      hη hDν hν_γ residue.hγBar_eq
      residue.hV_conj
      segIn.hF_unreg_meas_bare segIn.hF_gat_meas_bare
  have hμ_aem : μ =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
                    (wkBundle.mLim + ρ₁) := by
    refine MeasureTheory.ae_of_all _ (fun x => ?_)
    have : μ x = wkBundle.mLim x + ρ₁ x := by
      have := congrArg (fun f => f x) hμ_eq_m
      simpa using this
    simpa [Pi.add_apply] using this
  have hBar_aem : μBar =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
                    (wkBundle.mLim + ρ₂) := by
    refine MeasureTheory.ae_of_all _ (fun x => ?_)
    have : μBar x = wkBundle.mLim x + ρ₂ x := by
      have := congrArg (fun f => f x) hBar_eq_m
      simpa using this
    simpa [Pi.add_apply] using this
  have hυ_aem : υ =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
                  wkBundle.uLim := by
    refine MeasureTheory.ae_of_all _ (fun x => ?_)
    have := congrArg (fun f => f x) hμ_eq_u
    simpa using this
  have hῡ_aem : ῡ =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
                  wkBundle.uLim := by
    refine MeasureTheory.ae_of_all _ (fun x => ?_)
    have := congrArg (fun f => f x) hBar_eq_u
    simpa using this
  have hDυ_aem : ∀ i, Dυ i =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
                        wkBundle.DuLim i := by
    intro i
    refine MeasureTheory.ae_of_all _ (fun x => ?_)
    have := congrArg (fun f : Fin d → (Fin d → ℝ) → ℝ => f i x) hμ_eq_Du
    simpa using this
  have hDῡ_aem : ∀ i, Dῡ i =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
                        wkBundle.DuLim i := by
    intro i
    refine MeasureTheory.ae_of_all _ (fun x => ?_)
    have := congrArg (fun f : Fin d → (Fin d → ℝ) → ℝ => f i x) hBar_eq_Du
    simpa using this
  exact StationaryMFG.Theorems.SimplePower.HemicontSegmentDataK0.ae_eq
    V H DpH γBar Dν η ν
    hμ_aem.symm hBar_aem.symm hυ_aem.symm hῡ_aem.symm
    (fun i => (hDυ_aem i).symm) (fun i => (hDῡ_aem i).symm) dataBare

/-! ### K0-min producer: `mintyDataSignedNarrowK0Min_of_paperHypotheses`
(`infra-P6-K0-min-mintyData-consumers`, audit 2026-05-22).

Signed mirror of `mintyDataSetNarrowK0Min_of_paperHypotheses` and K0
minimal-shape sibling of `mintyDataSignedNarrowK0_of_paperHypotheses`
(signed K0 consumer, line 15316). Per-pair narrow segment-data
aggregator on the signed family in the K0 minimal form: consumes a
`SignedFamilyNarrowMintyResidueK0Min` and calls the iter-0790 minimal
composer `hemicontSegmentData_signed_narrow_K0_min_of_paperHypotheses`
(8 dominators, no `bΔm1`, no `hβ_ge_one`). Body byte-equal to the K0
sibling except for the residue type, the composer call, and the
removal of the `segIn.bΔm1` projection. -/
def mintyDataSignedNarrowK0Min_of_paperHypotheses
    {d : ℕ} {γBarReal βBarReal βBarReal' γBarReal' γBar : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (wkBundle : StationaryMFG.Theorems.SimplePower.Banach.WeakLimitInputBundleAE
                  (d := d) γBarReal βBarReal)
    (residue : SignedFamilyNarrowMintyResidueK0Min (d := d)
                  (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  (γBar := γBar) V H DpH hpow wkBundle) :
    ∀ ⦃μBar ῡ : (Fin d → ℝ) → ℝ⦄ ⦃Dῡ : Fin d → (Fin d → ℝ) → ℝ⦄,
      (μBar, ῡ, Dῡ) ∈
        StationaryMFG.Theorems.SimplePower.Banach.D_signed_family_paper_nn
          (d := d) (ENNReal.ofReal βBarReal)
          wkBundle.mLim wkBundle.uLim wkBundle.DuLim →
    ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄ ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
      (μ, υ, Dυ) ∈
        StationaryMFG.Theorems.SimplePower.Banach.D_signed_family_paper_nn
          (d := d) (ENNReal.ofReal βBarReal)
          wkBundle.mLim wkBundle.uLim wkBundle.DuLim →
    ∀ (η ν : (Fin d → ℝ) → ℝ) (Dν : Fin d → (Fin d → ℝ) → ℝ),
    Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) η →
    (∀ i, Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dν i)) →
    Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) ν →
    Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal) ν →
      StationaryMFG.Theorems.SimplePower.HemicontSegmentDataK0
        (d := d) V H DpH γBar Dυ Dῡ μ μBar υ ῡ Dν η ν := by
  intro μBar ῡ Dῡ hBar μ υ Dυ hμ η ν Dν hη hDν hν_β hν_γ
  set g₁ := Classical.choose hμ with hg₁_def
  set g₂ := Classical.choose hBar with hg₂_def
  have hg₁_spec := Classical.choose_spec hμ
  have hg₂_spec := Classical.choose_spec hBar
  obtain ⟨hg₁_lp, hg₁_per, hμ_jointNN, hμ_eq⟩ := hg₁_spec
  obtain ⟨hg₂_lp, hg₂_per, hBar_jointNN, hBar_eq⟩ := hg₂_spec
  rw [Prod.mk.injEq, Prod.mk.injEq] at hμ_eq hBar_eq
  obtain ⟨hμ_eq_m, hμ_eq_u, hμ_eq_Du⟩ := hμ_eq
  obtain ⟨hBar_eq_m, hBar_eq_u, hBar_eq_Du⟩ := hBar_eq
  have segIn := residue.segInputsOf hBar hμ η ν Dν hη hDν hν_β hν_γ
  have hjoint₁_nn :
      0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
              (UnitCube d)] (fun x => wkBundle.mLim x + g₁ x) := hμ_jointNN
  have hjoint₂_nn :
      0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
              (UnitCube d)] (fun x => wkBundle.mLim x + g₂ x) := hBar_jointNN
  have dataBare :
      StationaryMFG.Theorems.SimplePower.HemicontSegmentDataK0
        (d := d) V H DpH γBar wkBundle.DuLim wkBundle.DuLim
        (wkBundle.mLim + g₁) (wkBundle.mLim + g₂)
        wkBundle.uLim wkBundle.uLim Dν η ν :=
    hemicontSegmentData_signed_narrow_K0_min_of_paperHypotheses
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal') (γBar := γBar)
      (V := V) (H := H) (DpH := DpH)
      hpow residue.hHat0 residue.hAgree residue.hβconj residue.hγconj
      wkBundle.hmLim_memLp wkBundle.huLim_sob
      (fun i => wkBundle.hDuLim_memLp_γ i)
      hg₁_lp hg₂_lp hjoint₁_nn hjoint₂_nn
      segIn.bΔυ segIn.bΔp_pow segIn.bΔm_pow segIn.bΔm_grad
      segIn.bΔm_endpoint segIn.bΔm segIn.bG_grad segIn.bG_val
      residue.hγ_one_lt Dν η ν
      hη hDν hν_γ residue.hγBar_eq
      residue.hV_conj
      segIn.hF_unreg_meas_bare segIn.hF_gat_meas_bare
  have hμ_aem : μ =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
                    (wkBundle.mLim + g₁) := by
    refine MeasureTheory.ae_of_all _ (fun x => ?_)
    have : μ x = wkBundle.mLim x + g₁ x := by
      have := congrArg (fun f => f x) hμ_eq_m
      simpa using this
    simpa [Pi.add_apply] using this
  have hBar_aem : μBar =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
                    (wkBundle.mLim + g₂) := by
    refine MeasureTheory.ae_of_all _ (fun x => ?_)
    have : μBar x = wkBundle.mLim x + g₂ x := by
      have := congrArg (fun f => f x) hBar_eq_m
      simpa using this
    simpa [Pi.add_apply] using this
  have hυ_aem : υ =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
                  wkBundle.uLim := by
    refine MeasureTheory.ae_of_all _ (fun x => ?_)
    have := congrArg (fun f => f x) hμ_eq_u
    simpa using this
  have hῡ_aem : ῡ =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
                  wkBundle.uLim := by
    refine MeasureTheory.ae_of_all _ (fun x => ?_)
    have := congrArg (fun f => f x) hBar_eq_u
    simpa using this
  have hDυ_aem : ∀ i, Dυ i =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
                        wkBundle.DuLim i := by
    intro i
    refine MeasureTheory.ae_of_all _ (fun x => ?_)
    have := congrArg (fun f : Fin d → (Fin d → ℝ) → ℝ => f i x) hμ_eq_Du
    simpa using this
  have hDῡ_aem : ∀ i, Dῡ i =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
                        wkBundle.DuLim i := by
    intro i
    refine MeasureTheory.ae_of_all _ (fun x => ?_)
    have := congrArg (fun f : Fin d → (Fin d → ℝ) → ℝ => f i x) hBar_eq_Du
    simpa using this
  exact StationaryMFG.Theorems.SimplePower.HemicontSegmentDataK0.ae_eq
    V H DpH γBar Dν η ν
    hμ_aem.symm hBar_aem.symm hυ_aem.symm hῡ_aem.symm
    (fun i => (hDυ_aem i).symm) (fun i => (hDῡ_aem i).symm) dataBare

/-! ### K0-min producer: `mintyDataTransportNarrowK0Min_of_paperHypotheses`
(`infra-P6-K0-min-mintyData-consumers`, audit 2026-05-22).

Transport mirror of `mintyDataSetNarrowK0Min_of_paperHypotheses` /
`mintyDataSignedNarrowK0Min_of_paperHypotheses`, and K0 minimal-shape
sibling of `mintyDataTransportNarrowK0_of_paperHypotheses` (transport
K0 consumer, line 16486). Per-pair narrow segment-data aggregator on
the transport family in the K0 minimal form: consumes a
`TransportFamilyNarrowMintyResidueK0Min` and calls the iter-0791
minimal composer
`hemicontSegmentData_transport_narrow_K0_min_of_paperHypotheses` (8
dominators, no `bΔm1`, no `hβ_ge_one`). Body byte-equal to the K0
sibling except for the residue type, the composer call, and the
removal of the `segIn.bΔm1` projection. -/
def mintyDataTransportNarrowK0Min_of_paperHypotheses
    {d : ℕ} {γBarReal βBarReal βBarReal' γBarReal' γBar : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (wkBundle : StationaryMFG.Theorems.SimplePower.Banach.WeakLimitInputBundleAE
                  (d := d) γBarReal βBarReal)
    (residue : TransportFamilyNarrowMintyResidueK0Min (d := d)
                  (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  (γBar := γBar) V H DpH hpow wkBundle) :
    ∀ ⦃μBar ῡ : (Fin d → ℝ) → ℝ⦄ ⦃Dῡ : Fin d → (Fin d → ℝ) → ℝ⦄,
      (μBar, ῡ, Dῡ) ∈
        StationaryMFG.Theorems.SimplePower.Banach.D_transport_family_paper
          (d := d) wkBundle.mLim wkBundle.uLim wkBundle.DuLim →
    ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄ ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
      (μ, υ, Dυ) ∈
        StationaryMFG.Theorems.SimplePower.Banach.D_transport_family_paper
          (d := d) wkBundle.mLim wkBundle.uLim wkBundle.DuLim →
    ∀ (η ν : (Fin d → ℝ) → ℝ) (Dν : Fin d → (Fin d → ℝ) → ℝ),
    Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) η →
    (∀ i, Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dν i)) →
    Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) ν →
    Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal) ν →
      StationaryMFG.Theorems.SimplePower.HemicontSegmentDataK0
        (d := d) V H DpH γBar Dυ Dῡ μ μBar υ ῡ Dν η ν := by
  intro μBar ῡ Dῡ hBar μ υ Dυ hμ η ν Dν hη hDν hν_β hν_γ
  have hμ_eq := Classical.choose_spec hμ
  have hBar_eq := Classical.choose_spec hBar
  set ψ₁ := Classical.choose hμ with hψ₁_def
  set ψ₂ := Classical.choose hBar with hψ₂_def
  rw [Prod.mk.injEq, Prod.mk.injEq] at hμ_eq hBar_eq
  obtain ⟨hμ_eq_m, hμ_eq_u, hμ_eq_Du⟩ := hμ_eq
  obtain ⟨hBar_eq_m, hBar_eq_u, hBar_eq_Du⟩ := hBar_eq
  have segIn := residue.segInputsOf hBar hμ η ν Dν hη hDν hν_β hν_γ
  have dataBare :
      StationaryMFG.Theorems.SimplePower.HemicontSegmentDataK0
        (d := d) V H DpH γBar
        (fun i => wkBundle.DuLim i +
            (Periodic.SmoothPeriodic.partialDeriv i ψ₁
              : (Fin d → ℝ) → ℝ))
        (fun i => wkBundle.DuLim i +
            (Periodic.SmoothPeriodic.partialDeriv i ψ₂
              : (Fin d → ℝ) → ℝ))
        wkBundle.mLim wkBundle.mLim
        (wkBundle.uLim + (ψ₁ : (Fin d → ℝ) → ℝ))
        (wkBundle.uLim + (ψ₂ : (Fin d → ℝ) → ℝ))
        Dν η ν :=
    hemicontSegmentData_transport_narrow_K0_min_of_paperHypotheses
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal') (γBar := γBar)
      (V := V) (H := H) (DpH := DpH)
      hpow residue.hHat0 residue.hAgree residue.hβconj residue.hγconj
      wkBundle.hmLim_memLp wkBundle.huLim_sob
      (fun i => wkBundle.hDuLim_memLp_γ i)
      residue.hmLim_nn
      ψ₁ ψ₂
      segIn.bΔυ segIn.bΔp_pow segIn.bΔm_pow segIn.bΔm_grad
      segIn.bΔm_endpoint segIn.bΔm segIn.bG_grad segIn.bG_val
      residue.hγ_one_lt Dν η ν
      hη hDν hν_γ residue.hγBar_eq
      residue.hV_conj
      segIn.hF_unreg_meas_bare segIn.hF_gat_meas_bare
  have hμ_aem : μ =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
                    wkBundle.mLim := by
    refine MeasureTheory.ae_of_all _ (fun x => ?_)
    have := congrArg (fun f => f x) hμ_eq_m
    simpa using this
  have hBar_aem : μBar =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
                    wkBundle.mLim := by
    refine MeasureTheory.ae_of_all _ (fun x => ?_)
    have := congrArg (fun f => f x) hBar_eq_m
    simpa using this
  have hυ_aem : υ =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
                  (wkBundle.uLim + (ψ₁ : (Fin d → ℝ) → ℝ)) := by
    refine MeasureTheory.ae_of_all _ (fun x => ?_)
    have : υ x = wkBundle.uLim x + (ψ₁ : (Fin d → ℝ) → ℝ) x := by
      have := congrArg (fun f => f x) hμ_eq_u
      simpa using this
    simpa [Pi.add_apply] using this
  have hῡ_aem : ῡ =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
                  (wkBundle.uLim + (ψ₂ : (Fin d → ℝ) → ℝ)) := by
    refine MeasureTheory.ae_of_all _ (fun x => ?_)
    have : ῡ x = wkBundle.uLim x + (ψ₂ : (Fin d → ℝ) → ℝ) x := by
      have := congrArg (fun f => f x) hBar_eq_u
      simpa using this
    simpa [Pi.add_apply] using this
  have hDυ_aem : ∀ i, Dυ i =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
                        (wkBundle.DuLim i +
                          (Periodic.SmoothPeriodic.partialDeriv i ψ₁
                            : (Fin d → ℝ) → ℝ)) := by
    intro i
    refine MeasureTheory.ae_of_all _ (fun x => ?_)
    have : Dυ i x = wkBundle.DuLim i x +
                      (Periodic.SmoothPeriodic.partialDeriv i ψ₁
                        : (Fin d → ℝ) → ℝ) x := by
      have := congrArg (fun f : Fin d → (Fin d → ℝ) → ℝ => f i x) hμ_eq_Du
      simpa using this
    simpa [Pi.add_apply] using this
  have hDῡ_aem : ∀ i, Dῡ i =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
                        (wkBundle.DuLim i +
                          (Periodic.SmoothPeriodic.partialDeriv i ψ₂
                            : (Fin d → ℝ) → ℝ)) := by
    intro i
    refine MeasureTheory.ae_of_all _ (fun x => ?_)
    have : Dῡ i x = wkBundle.DuLim i x +
                      (Periodic.SmoothPeriodic.partialDeriv i ψ₂
                        : (Fin d → ℝ) → ℝ) x := by
      have := congrArg (fun f : Fin d → (Fin d → ℝ) → ℝ => f i x) hBar_eq_Du
      simpa using this
    simpa [Pi.add_apply] using this
  exact StationaryMFG.Theorems.SimplePower.HemicontSegmentDataK0.ae_eq
    V H DpH γBar Dν η ν
    hμ_aem.symm hBar_aem.symm hυ_aem.symm hῡ_aem.symm
    (fun i => (hDυ_aem i).symm) (fun i => (hDῡ_aem i).symm) dataBare

end SimplePower
end Theorems
end StationaryMFG
end
