module

public import StationaryMFG.Theorems.SimplePower.Main
public import StationaryMFG.Theorems.SimplePower.Banach.AbstractLifts
public import StationaryMFG.Theorems.SimplePower.Banach.UniformSequence
public import StationaryMFG.Theorems.SimplePower.Banach.WeakLimit
public import StationaryMFG.Theorems.SimplePower.Banach.WeakPairing
public import StationaryMFG.Theorems.SimplePower.Banach.LimitPassage
public import StationaryMFG.Theorems.SimplePower.Banach.AprioriDischarge
public import StationaryMFG.Monotone.AbstractWeak
public import StationaryMFG.Monotone.HemicontUpgrade
public import StationaryMFG.Hamiltonian.Assumptions

@[expose] public section

/-!
# Phase 4 closure: assembly helpers for `simplePowerThinChain_of_paperHypotheses`

This module collects the *assembly* helpers used by
`simplePowerThinChain_of_paperHypotheses` to wire together the upstream
Banach-bridge chain
```
(hmon, hpow, hV)
  → ε-regularised solutions   (`thm_strongAepsi`, B.1+B.2+B.3)
  → uniform ε-sequence         (`exists_uniform_eps_sequence`, C.5)
  → weak cluster point         (`exists_weak_cluster_point_pair`)
  → bare-function limit triple (`weak_limit_to_bare`, D.1)
  → weak VI for A_0            (`limit_passage_summand{1,2,3}` etc., E.*)
  → strong VI on D = ⊤         (`main_strong_VI`)
  → H4SimplePowerThinInputs witness.
```

Per `docs/CONVENTIONS.md` §1b/§8 (statement-then-proof; auxiliary
hypotheses authorised where genuinely needed), the closure is
parameterised on a single auxiliary hypothesis bundle
`UpstreamChainOutput` carrying the candidate triple `(m, u, Du)`,
the L^{β̄}/W^{1,γ̄} regularity, the non-negativity certificate,
the integrability of the three flux/residual integrands,
and the function-form strong VI for `A_0` at `(m, u, Du)`. This bundle
is exactly the data the upstream chain produces and that the thinner
input `H4SimplePowerThinInputs` consumes; the assembly is then a direct
re-packaging.

Concretising the upstream chain (i.e. discharging
`UpstreamChainOutput` from `(hmon, hpow, hV)` alone via a complete
Banach realisation of `L^{β̄}_per × W^{1,γ̄}_per` at general
`(β̄, γ̄)`) is the substantial workstream filed as the seven-child
split in `infra-P4-thin-chain-discharge`.

## Main contents

* `UpstreamChainOutput` — the auxiliary hypothesis bundle carrying the
  upstream chain's outputs.
* `H4SimplePowerThinInputs.ofUpstreamChainOutput` — assemble the
  thin-input bundle from an `UpstreamChainOutput`.
* `auxHypsOfBanachPair` — F.1 of the seven-child final-closure split:
  package per-base-point primal-side `MemLpPer` certificates plus the
  Hölder-conjugacy / finiteness data into an `MFGOpEpsAuxHyps` bundle
  for the bare-function triple `(⇑q.1, ⇑q.2.1, fun i x => ⇑(q.2.2 i) x)`
  associated to a Banach pair `q : LpPer βBar × SobolevPerLp 1 γBar`.
-/

noncomputable section

namespace StationaryMFG
namespace Theorems
namespace SimplePower
namespace Banach

open MeasureTheory NormedSpace
open Bornology Filter Topology
open StationaryMFG.Periodic
open StationaryMFG.Hamiltonian
open StationaryMFG.Monotone
open StationaryMFG.Solutions.MFG
open scoped ENNReal Topology

variable {d : ℕ}

/-! ## F.1 — Per-`q` `MFGOpEpsAuxHyps` extraction

For an arbitrary Banach point `q : LpPer (ENNReal.ofReal βBarReal) d ×
SobolevPerLp 1 (ENNReal.ofReal γBarReal) d`, we assemble an
`MFGOpEpsAuxHyps` bundle whose underlying primal triple is
`(m, u, Du) := (⇑q.1, ⇑q.2.1, fun i x => ⇑(q.2.2 i) x)`.

The five primal-side `MemLpPer` certificates required by the bundle
(`hF_HJB`, `hF_flux`, `hF_mass`, `hG_grad`, `hG_val`) reference the
*private* primal-side definitions of `Banach/Operator.lean`:

* `F_HJB V H Du m u := fun x => -(u x) - H x (fun i => Du i x) (m x) + V x`,
* `F_flux DpH Du m i := fun x => m x * DpH x (fun j => Du j x) (m x) i`,
* `F_mass m := fun x => m x - 1`,
* `G_grad γBarReal Du i := fun x => vecAbsPowMinusTwo γBarReal (fun j => Du j x) * Du i x`,
* `G_val γBarReal u := fun x => absPowMinusTwo γBarReal (u x) * u x`.

Since these are `private def`s, file-private to `Operator.lean`, we
cannot name them here, but the structure-field types are stated in
their unfolded form in the hypotheses below. By definitional unfolding
of the private `def`s, `MemLpPer p' (F_HJB V H Du m u)` is identical to
`MemLpPer p' (fun x => -(u x) - H x (fun i => Du i x) (m x) + V x)`,
and Lean's anonymous-constructor elaboration accepts the unfolded form.

This is the *bundling* step: discharging the five `MemLpPer`
hypotheses from concrete structural assumptions on `(V, H, DpH)` and
`q` (paper power-growth, etc.) is the workstream of subsequent F.*
children of the seven-child split. -/

variable {V : (Fin d → ℝ) → ℝ}
variable {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
variable {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}

/-- **F.1 — Per-`q` `MFGOpEpsAuxHyps` extraction.**

Given a Banach point
`q : LpPer (ENNReal.ofReal βBarReal) d × SobolevPerLp 1 (ENNReal.ofReal γBarReal) d`,
the Hölder-conjugacy data `(hβ, hγ, hβγ, hβTop)`, and five primal-side
`MemLpPer` certificates of the unfolded `F_HJB`, `F_flux i`, `F_mass`,
`G_grad i`, `G_val` integrands at `(m, u, Du) := (⇑q.1, ⇑q.2.1,
fun i x => ⇑(q.2.2 i) x)`, return the `MFGOpEpsAuxHyps` bundle
`mfgOperatorEps_CLM` consumes.

The five `MemLpPer` hypotheses are stated in **unfolded** pointwise
form for callability from outside `Banach/Operator.lean` (where
`F_HJB`/`F_flux`/`F_mass`/`G_grad`/`G_val` are file-private). By
definitional unfolding of those private `def`s, the unfolded forms are
type-equal to the structure-field types and are accepted by the
anonymous constructor. -/
def auxHypsOfBanachPair
    (γBarReal βBarReal βBarReal' γBarReal' : ℝ)
    (q : Periodic.LpPer (ENNReal.ofReal βBarReal) d
          × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d)
    (hβ : βBarReal.HolderConjugate βBarReal')
    (hγ : γBarReal.HolderConjugate γBarReal')
    (hβTop : ENNReal.ofReal γBarReal ≠ ⊤)
    (hF_HJB :
      Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x => -((⇑q.2.1 : (Fin d → ℝ) → ℝ) x)
                    - H x (fun i => (⇑(q.2.2 i) : (Fin d → ℝ) → ℝ) x)
                          ((⇑q.1 : (Fin d → ℝ) → ℝ) x)
                    + V x))
    (hF_flux : ∀ i,
      Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => (⇑q.1 : (Fin d → ℝ) → ℝ) x
                    * DpH x (fun j => (⇑(q.2.2 j) : (Fin d → ℝ) → ℝ) x)
                          ((⇑q.1 : (Fin d → ℝ) → ℝ) x) i))
    -- Phase 0 routing fix: `F_mass` lives in `L^γ̄'`.
    (hF_mass :
      Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => (⇑q.1 : (Fin d → ℝ) → ℝ) x - 1))
    (hG_grad : ∀ i,
      Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => vecAbsPowMinusTwo γBarReal
                    (fun j => (⇑(q.2.2 j) : (Fin d → ℝ) → ℝ) x)
                    * (⇑(q.2.2 i) : (Fin d → ℝ) → ℝ) x))
    (hG_val :
      Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => absPowMinusTwo γBarReal ((⇑q.2.1 : (Fin d → ℝ) → ℝ) x)
                    * (⇑q.2.1 : (Fin d → ℝ) → ℝ) x)) :
    MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
        V H DpH
        (fun i x => (⇑(q.2.2 i) : (Fin d → ℝ) → ℝ) x)
        (⇑q.1 : (Fin d → ℝ) → ℝ)
        (⇑q.2.1 : (Fin d → ℝ) → ℝ) where
  hβ := hβ
  hγ := hγ
  hβTop := hβTop
  hF_HJB := hF_HJB
  hF_flux := hF_flux
  hF_mass := hF_mass
  hG_grad := hG_grad
  hG_val := hG_val

/-- Helper projection: re-export the `F_HJB`-membership field of the
bundle produced by `auxHypsOfBanachPair` in unfolded form. -/
lemma auxHyps_F_HJB_memLp
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    {q : Periodic.LpPer (ENNReal.ofReal βBarReal) d
          × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d}
    {hβ : βBarReal.HolderConjugate βBarReal'}
    {hγ : γBarReal.HolderConjugate γBarReal'}
    {hβTop : ENNReal.ofReal γBarReal ≠ ⊤}
    {hF_HJB :
      Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x => -((⇑q.2.1 : (Fin d → ℝ) → ℝ) x)
                    - H x (fun i => (⇑(q.2.2 i) : (Fin d → ℝ) → ℝ) x)
                          ((⇑q.1 : (Fin d → ℝ) → ℝ) x)
                    + V x)}
    {hF_flux : ∀ i,
      Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => (⇑q.1 : (Fin d → ℝ) → ℝ) x
                    * DpH x (fun j => (⇑(q.2.2 j) : (Fin d → ℝ) → ℝ) x)
                          ((⇑q.1 : (Fin d → ℝ) → ℝ) x) i)}
    {hF_mass :
      Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => (⇑q.1 : (Fin d → ℝ) → ℝ) x - 1)}
    {hG_grad : ∀ i,
      Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => vecAbsPowMinusTwo γBarReal
                    (fun j => (⇑(q.2.2 j) : (Fin d → ℝ) → ℝ) x)
                    * (⇑(q.2.2 i) : (Fin d → ℝ) → ℝ) x)}
    {hG_val :
      Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => absPowMinusTwo γBarReal ((⇑q.2.1 : (Fin d → ℝ) → ℝ) x)
                    * (⇑q.2.1 : (Fin d → ℝ) → ℝ) x)} :
    Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal')
      (fun x => -((⇑q.2.1 : (Fin d → ℝ) → ℝ) x)
                  - H x (fun i => (⇑(q.2.2 i) : (Fin d → ℝ) → ℝ) x)
                        ((⇑q.1 : (Fin d → ℝ) → ℝ) x)
                  + V x) :=
  (auxHypsOfBanachPair (V := V) (H := H) (DpH := DpH)
    γBarReal βBarReal βBarReal' γBarReal' q
    hβ hγ hβTop hF_HJB hF_flux hF_mass hG_grad hG_val).hF_HJB

/-- Helper projection: re-export the `F_flux i`-membership field of the
bundle produced by `auxHypsOfBanachPair` in unfolded form. -/
lemma auxHyps_F_flux_memLp
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    {q : Periodic.LpPer (ENNReal.ofReal βBarReal) d
          × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d}
    {hβ : βBarReal.HolderConjugate βBarReal'}
    {hγ : γBarReal.HolderConjugate γBarReal'}
    {hβTop : ENNReal.ofReal γBarReal ≠ ⊤}
    {hF_HJB :
      Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x => -((⇑q.2.1 : (Fin d → ℝ) → ℝ) x)
                    - H x (fun i => (⇑(q.2.2 i) : (Fin d → ℝ) → ℝ) x)
                          ((⇑q.1 : (Fin d → ℝ) → ℝ) x)
                    + V x)}
    {hF_flux : ∀ i,
      Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => (⇑q.1 : (Fin d → ℝ) → ℝ) x
                    * DpH x (fun j => (⇑(q.2.2 j) : (Fin d → ℝ) → ℝ) x)
                          ((⇑q.1 : (Fin d → ℝ) → ℝ) x) i)}
    {hF_mass :
      Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => (⇑q.1 : (Fin d → ℝ) → ℝ) x - 1)}
    {hG_grad : ∀ i,
      Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => vecAbsPowMinusTwo γBarReal
                    (fun j => (⇑(q.2.2 j) : (Fin d → ℝ) → ℝ) x)
                    * (⇑(q.2.2 i) : (Fin d → ℝ) → ℝ) x)}
    {hG_val :
      Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => absPowMinusTwo γBarReal ((⇑q.2.1 : (Fin d → ℝ) → ℝ) x)
                    * (⇑q.2.1 : (Fin d → ℝ) → ℝ) x)}
    (i : Fin d) :
    Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
      (fun x => (⇑q.1 : (Fin d → ℝ) → ℝ) x
                  * DpH x (fun j => (⇑(q.2.2 j) : (Fin d → ℝ) → ℝ) x)
                        ((⇑q.1 : (Fin d → ℝ) → ℝ) x) i) :=
  (auxHypsOfBanachPair (V := V) (H := H) (DpH := DpH)
    γBarReal βBarReal βBarReal' γBarReal' q
    hβ hγ hβTop hF_HJB hF_flux hF_mass hG_grad hG_val).hF_flux i

/-! ### Sanity-check unit test for F.1

Exercise `auxHypsOfBanachPair` on the trivial Hamiltonian
(`H ≡ 0`, `D_pH ≡ 0`). On the trivial Hamiltonian:

* `F_HJB` reduces to `fun x => -u x + V x`,
* `F_flux i` reduces to `fun x => 0` (constantly zero),
* `F_mass`, `G_grad`, `G_val` are unchanged (they do not see `H`/`DpH`).

We just check that the construction type-checks: the bundle is
producible whenever the five `MemLpPer` certificates are supplied. -/

example
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (V : (Fin d → ℝ) → ℝ)
    (q : Periodic.LpPer (ENNReal.ofReal βBarReal) d
          × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d)
    (hβ : βBarReal.HolderConjugate βBarReal')
    (hγ : γBarReal.HolderConjugate γBarReal')
    (hβTop : ENNReal.ofReal γBarReal ≠ ⊤)
    (hF_HJB :
      Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x => -((⇑q.2.1 : (Fin d → ℝ) → ℝ) x)
                    - (0 : ℝ) + V x))
    (hF_flux : ∀ i,
      Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => (⇑q.1 : (Fin d → ℝ) → ℝ) x
                    * ((0 : Fin d → ℝ) i)))
    (hF_mass :
      Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => (⇑q.1 : (Fin d → ℝ) → ℝ) x - 1))
    (hG_grad : ∀ i,
      Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => vecAbsPowMinusTwo γBarReal
                    (fun j => (⇑(q.2.2 j) : (Fin d → ℝ) → ℝ) x)
                    * (⇑(q.2.2 i) : (Fin d → ℝ) → ℝ) x))
    (hG_val :
      Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x => absPowMinusTwo γBarReal ((⇑q.2.1 : (Fin d → ℝ) → ℝ) x)
                    * (⇑q.2.1 : (Fin d → ℝ) → ℝ) x)) :
    MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
        V (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : Fin d → ℝ))
        (fun i x => (⇑(q.2.2 i) : (Fin d → ℝ) → ℝ) x)
        (⇑q.1 : (Fin d → ℝ) → ℝ)
        (⇑q.2.1 : (Fin d → ℝ) → ℝ) :=
  auxHypsOfBanachPair (V := V) (H := fun _ _ _ => (0 : ℝ))
    (DpH := fun _ _ _ => (0 : Fin d → ℝ))
    γBarReal βBarReal βBarReal' γBarReal' q
    hβ hγ hβTop hF_HJB hF_flux hF_mass hG_grad hG_val

/-! ## F.2 — Concrete Banach-VI invocation per `ε`

For each `ε > 0`, invoke the Phase-3 abstract Browder–Minty theorem
`monotone_abstract_weak` on the concrete `(K_Aepsi, Aepsi_CLM_op …)`
pair to produce a weak-VI witness `q ∈ closure K_Aepsi`, then upgrade
to the strong-VI form `0 ≤ A q (q' - q)` via the abstract Minty trick
`hemicont_upgrade`.

The headline result is `existsStrongVI_at_eps`. The hypotheses are
the three operator-theoretic predicates produced by the B.* wraps
(monotonicity, hemicontinuity, coercivity), plus the Banach-space
data (reflexivity and `FiniteConvexHullWeakVI`) needed by
`monotone_abstract_weak`.

The strong-VI form delivered here is on `closure K_Aepsi` (which is
what the abstract Minty trick supports without an additional closure
argument): the Browder–Minty theorem produces a weak limit in
`closure K_Aepsi`, and `hemicont_upgrade` requires a `K`-membership
hypothesis. We therefore expose two complementary forms: the raw
weak VI (`q ∈ closure K_Aepsi`, weak form `0 ≤ A v (v - q)`) and the
strong upgrade applied conditionally on `q ∈ K_Aepsi` (the typical
case once an extra closedness lemma is supplied at the F.* downstream
layer).
-/

variable {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
variable [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)]

/-- Local abbreviation for the Banach domain of `mfgOperatorEps_CLM`,
mirroring the private one in `Banach/AbstractLifts.lean`. -/
abbrev palomar_Closure_XBanachClosure (d : ℕ) (βBarReal γBarReal : ℝ) : Type :=
  Periodic.LpPer (ENNReal.ofReal βBarReal) d
    × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d

-- `K_Aepsi_convex` was originally defined locally in this module but
-- is now exposed canonically from `Banach/AbstractLifts.lean` (per the
-- two-domain redesign, child A); see the public lemma there.

/-- **F.2 — Concrete Banach weak-VI invocation per `ε`.**

For each `ε`, package the abstract Browder–Minty conclusion
`monotone_abstract_weak` on the `(K_Aepsi, Aepsi_CLM_op …)` pair as a
named lemma. The hypotheses are the three operator-theoretic
predicates produced by the B.* wraps:

* `hMono : IsMonotone K_Aepsi (Aepsi_CLM_op …)` (from `B.1b`,
  `isMonotone_Aepsi_CLM`),
* `hHC   : IsHemicontinuous K_Aepsi (Aepsi_CLM_op …)` (from `B.2`,
  `isHemicontinuous_Aepsi_CLM`),
* `hCoerc : IsCoerciveAt K_Aepsi (Aepsi_CLM_op …) v0` (from `B.3`,
  `isCoerciveAt_Aepsi_CLM`),

together with the Banach-space data needed by
`monotone_abstract_weak`:

* `[FiniteConvexHullWeakVI XBanach]` (the doubleton-finite-VI
  typeclass; satisfied for any reflexive Banach space — see
  `Monotone/FiniteConvexHullWeakVI.lean`),
* `IsReflexiveNormedSpace XBanach` (project-local reflexivity
  predicate from `Periodic/Reflexive.lean`).

The conclusion is the *weak* VI on `closure K_Aepsi`:
`∃ q ∈ closure K_Aepsi, ∀ q' ∈ K_Aepsi, 0 ≤ A q' (q' - q)`. -/
theorem existsWeakVI_at_eps_aepsi
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (auxHyps : ∀ (Du : Fin d → (Fin d → ℝ) → ℝ) (m u : (Fin d → ℝ) → ℝ),
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V H DpH Du m u)
    (ε : ℝ)
    [FiniteConvexHullWeakVI (palomar_Closure_XBanachClosure d βBarReal γBarReal)]
    (hX : Periodic.IsReflexiveNormedSpace (palomar_Closure_XBanachClosure d βBarReal γBarReal))
    {v0 : palomar_Closure_XBanachClosure d βBarReal γBarReal}
    (hMono : IsMonotone (X := palomar_Closure_XBanachClosure d βBarReal γBarReal)
              (K_Aepsi d βBarReal γBarReal)
              (Aepsi_CLM_op (γBarReal := γBarReal) (βBarReal := βBarReal)
                (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                V H DpH auxHyps ε))
    (hCoerc : IsCoerciveAt (X := palomar_Closure_XBanachClosure d βBarReal γBarReal)
              (K_Aepsi d βBarReal γBarReal)
              (Aepsi_CLM_op (γBarReal := γBarReal) (βBarReal := βBarReal)
                (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                V H DpH auxHyps ε)
              v0) :
    ∃ q ∈ closure (K_Aepsi d βBarReal γBarReal),
      ∀ q' ∈ K_Aepsi d βBarReal γBarReal,
        0 ≤ Aepsi_CLM_op (γBarReal := γBarReal) (βBarReal := βBarReal)
              (βBarReal' := βBarReal') (γBarReal' := γBarReal')
              V H DpH auxHyps ε q' (q' - q) :=
  StationaryMFG.Monotone.monotone_abstract_weak
    (X := palomar_Closure_XBanachClosure d βBarReal γBarReal) hX
    (K := K_Aepsi d βBarReal γBarReal)
    (K_Aepsi_convex d βBarReal γBarReal)
    (A := Aepsi_CLM_op (γBarReal := γBarReal) (βBarReal := βBarReal)
            (βBarReal' := βBarReal') (γBarReal' := γBarReal')
            V H DpH auxHyps ε)
    hMono (v₀ := v0) hCoerc

/-- **F.2 — Concrete Banach strong-VI invocation per `ε`** (conditional
on the weak limit landing inside `K_Aepsi`, not just `closure K_Aepsi`).

Combining `existsWeakVI_at_eps_aepsi` with the abstract Minty trick
`hemicont_upgrade`, on the *hypothesis* that the weak-VI witness
produced by `monotone_abstract_weak` is in `K_Aepsi` (rather than
merely in `closure K_Aepsi`), we obtain the strong-VI form
`∃ q ∈ K_Aepsi, ∀ q' ∈ K_Aepsi, 0 ≤ A q (q' - q)`.

The `K_Aepsi` membership of the weak-limit witness is a downstream
closedness fact (e.g. via Mazur on the strict-positivity cone, or via
the apriori discharge); we expose it as a hypothesis here. -/
theorem existsStrongVI_at_eps
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (auxHyps : ∀ (Du : Fin d → (Fin d → ℝ) → ℝ) (m u : (Fin d → ℝ) → ℝ),
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V H DpH Du m u)
    (ε : ℝ)
    [FiniteConvexHullWeakVI (palomar_Closure_XBanachClosure d βBarReal γBarReal)]
    (hX : Periodic.IsReflexiveNormedSpace (palomar_Closure_XBanachClosure d βBarReal γBarReal))
    {v0 : palomar_Closure_XBanachClosure d βBarReal γBarReal}
    (hMono : IsMonotone (X := palomar_Closure_XBanachClosure d βBarReal γBarReal)
              (K_Aepsi d βBarReal γBarReal)
              (Aepsi_CLM_op (γBarReal := γBarReal) (βBarReal := βBarReal)
                (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                V H DpH auxHyps ε))
    (hHC : IsHemicontinuous (X := palomar_Closure_XBanachClosure d βBarReal γBarReal)
              (K_Aepsi d βBarReal γBarReal)
              (Aepsi_CLM_op (γBarReal := γBarReal) (βBarReal := βBarReal)
                (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                V H DpH auxHyps ε))
    (hCoerc : IsCoerciveAt (X := palomar_Closure_XBanachClosure d βBarReal γBarReal)
              (K_Aepsi d βBarReal γBarReal)
              (Aepsi_CLM_op (γBarReal := γBarReal) (βBarReal := βBarReal)
                (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                V H DpH auxHyps ε)
              v0)
    (hClosure : ∀ q ∈ closure (K_Aepsi d βBarReal γBarReal),
                  q ∈ K_Aepsi d βBarReal γBarReal) :
    ∃ q ∈ K_Aepsi d βBarReal γBarReal,
      ∀ q' ∈ K_Aepsi d βBarReal γBarReal,
        0 ≤ Aepsi_CLM_op (γBarReal := γBarReal) (βBarReal := βBarReal)
              (βBarReal' := βBarReal') (γBarReal' := γBarReal')
              V H DpH auxHyps ε q (q' - q) := by
  obtain ⟨q, hq_clos, hq_weak⟩ :=
    existsWeakVI_at_eps_aepsi (V := V) (H := H) (DpH := DpH) auxHyps ε hX
      (v0 := v0) hMono hCoerc
  have hq_K : q ∈ K_Aepsi d βBarReal γBarReal := hClosure q hq_clos
  refine ⟨q, hq_K, ?_⟩
  -- Apply the abstract `hemicont_upgrade`: weak VI ⇒ strong VI on `K`.
  exact StationaryMFG.Monotone.hemicont_upgrade
    (X := palomar_Closure_XBanachClosure d βBarReal γBarReal)
    (K := K_Aepsi d βBarReal γBarReal)
    (K_Aepsi_convex d βBarReal γBarReal)
    (A := Aepsi_CLM_op (γBarReal := γBarReal) (βBarReal := βBarReal)
            (βBarReal' := βBarReal') (γBarReal' := γBarReal')
            V H DpH auxHyps ε)
    hHC hq_K (by intro v hv; exact hq_weak v hv)

/-! ### Sanity-check unit `example` for F.2

Trivial Hamiltonian (`H ≡ 0`, `D_pH ≡ 0`, `V ≡ 0`) sanity check: the
unit-test `example` confirms the headline `existsStrongVI_at_eps`
type-checks under canonical aux hyps. The proof itself is delegated
to the named theorem. -/

example
    [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    [FiniteConvexHullWeakVI (palomar_Closure_XBanachClosure d βBarReal γBarReal)]
    (auxHyps : ∀ (Du : Fin d → (Fin d → ℝ) → ℝ) (m u : (Fin d → ℝ) → ℝ),
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    (fun _ => (0 : ℝ))
                    (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : Fin d → ℝ))
                    Du m u)
    (ε : ℝ)
    (hX : Periodic.IsReflexiveNormedSpace (palomar_Closure_XBanachClosure d βBarReal γBarReal))
    {v0 : palomar_Closure_XBanachClosure d βBarReal γBarReal}
    (hMono : IsMonotone (X := palomar_Closure_XBanachClosure d βBarReal γBarReal)
              (K_Aepsi d βBarReal γBarReal)
              (Aepsi_CLM_op (γBarReal := γBarReal) (βBarReal := βBarReal)
                (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                (fun _ => (0 : ℝ))
                (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : Fin d → ℝ))
                auxHyps ε))
    (hHC : IsHemicontinuous (X := palomar_Closure_XBanachClosure d βBarReal γBarReal)
              (K_Aepsi d βBarReal γBarReal)
              (Aepsi_CLM_op (γBarReal := γBarReal) (βBarReal := βBarReal)
                (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                (fun _ => (0 : ℝ))
                (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : Fin d → ℝ))
                auxHyps ε))
    (hCoerc : IsCoerciveAt (X := palomar_Closure_XBanachClosure d βBarReal γBarReal)
              (K_Aepsi d βBarReal γBarReal)
              (Aepsi_CLM_op (γBarReal := γBarReal) (βBarReal := βBarReal)
                (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                (fun _ => (0 : ℝ))
                (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : Fin d → ℝ))
                auxHyps ε)
              v0)
    (hClosure : ∀ q ∈ closure (K_Aepsi d βBarReal γBarReal),
                  q ∈ K_Aepsi d βBarReal γBarReal) :
    ∃ q ∈ K_Aepsi d βBarReal γBarReal,
      ∀ q' ∈ K_Aepsi d βBarReal γBarReal,
        0 ≤ Aepsi_CLM_op (γBarReal := γBarReal) (βBarReal := βBarReal)
              (βBarReal' := βBarReal') (γBarReal' := γBarReal')
              (fun _ => (0 : ℝ))
              (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : Fin d → ℝ))
              auxHyps ε q (q' - q) :=
  existsStrongVI_at_eps (V := fun _ => (0 : ℝ))
    (H := fun _ _ _ => (0 : ℝ)) (DpH := fun _ _ _ => (0 : Fin d → ℝ))
    auxHyps ε hX (v0 := v0) hMono hHC hCoerc hClosure

/-! ## F.3 — `AprioriDischargeInputs` from F.2's strong-VI output

Given the strong-VI witness produced by F.2 (a `q ∈ K_Aepsi` with the
strong VI on the Banach pair) and the standing hypotheses
`(hmon, hpow, hV)`, build the `AprioriDischargeInputs` bundle consumed
by C.4's `apriori_at_eps`.

The ~30 fields of `AprioriDischargeInputs` split as follows:

* the bare-function triple `(m_ε, u_ε, Du_ε)` is extracted from the
  `BanachOutputData` (C.2 input);
* `Vint_bound` is supplied by C.3 (`Vint_bound`,
  `V_norm_le_Vint_bound`);
* the three integrability fields `hu_int`, `hRHSabove_int`, ... are
  collected as additional auxiliary inputs alongside the C.1
  `MemLpPer` certificates;
* the HJB inequality `hHJB` is produced by `lem_strong_is_strong_HJB_ineq`
  applied to (i) the C.1 residual integrability and (ii) the
  set-form strong-VI specialisation supplied as an aux input;
* the Lagrangian lower bound `h_lagr` is supplied as an aux input
  (the paper's `eq:lagrangian.lb` is a Legendre/convexity consequence
  of `hpow`'s `lower` bound, not a one-line rearrangement);
* the remaining structural fields (measurability, periodicity, local
  integrability, ε-residual non-negativity, transport identity, etc.)
  are aux inputs as authorised by CONVENTIONS §1b.

The resulting bundle is fed into C.4's `apriori_at_eps` to obtain the
ε-uniform a priori bound. -/

/-- **F.3 — Auxiliary input bundle for `aprioriInputsAtEps`.**

Records the user-side hypotheses required to assemble an
`AprioriDischargeInputs` bundle from F.2's strong-VI output, beyond
what the C.1/C.2/C.3 discharges and the strong-is-strong lemmas can
extract directly. Per CONVENTIONS §1b, these auxiliary hypotheses are
authorised: they correspond to paper-level structural facts (the
specific algebraic form of the Lagrangian lower bound, ε-residual
non-negativity, structural integrability/measurability, etc.) whose
extraction from the abstract strong VI is a separate workstream.

Fields are grouped into:

* C.1-flavoured `MemLpPer` certificates (`hRes_Lp`, `hm_Lp`,
  `hFlux_Lp`) — these enable the three integrability discharges of
  Block C.1;
* user-side bounds and integrability of structural integrands
  (`hVbnd`, `hMpos`, `hEpsNN`, `h_identity`, the eight `Integrable`
  fields, the `Vβp_bound` and `hVβp` data);
* user-side regularity certificates on `(u_ε, Du_ε)`
  (`hu_meas`, `hu_per`, `hu_loc`, `hDu_meas`, `hDu_per`, `hDu_loc`,
  `hDu_lp`, `hu_lp_γ`);
* user-side Lagrangian bound (`h_lagr`);
* user-side strong-VI specialisations from F.2's output
  (`hStrongVI_set`, `hStrongVI_signed`, `hStrongVI_transport`).
-/
structure AprioriInputAuxHyps
    [AxisMixMeasureHypothesis]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (ε : ℝ) where
  /-- The ε-residual integrand (paper proof of
  `thm:apriori-simple.power.growth`, `eq:apriori-eps.terms`). -/
  epsTerms : (Fin d → ℝ) → ℝ
  /-- Pointwise bound on `|V|`. -/
  Vbound : ℝ
  /-- `L^{β̄'}`-power bound on `|V|^{β̄'}`. -/
  Vβp_bound : ℝ
  /-- C.1 `MemLpPer β̄'`-certificate for the HJB residual. -/
  hRes_Lp :
    Periodic.MemLpPer (ENNReal.ofReal (betaBar' h.β))
      (StationaryMFG.Theorems.SimplePower.hjbResidual V H Du m u)
  /-- C.1 `MemLpPer β̄`-certificate for `m`. -/
  hm_Lp : Periodic.MemLpPer (ENNReal.ofReal (betaBar h.β)) m
  /-- C.1 `MemLpPer γ̄'`-certificate for the flux (paper `eq:boundsmDpH`). -/
  hFlux_Lp :
    Periodic.MemLpPer (ENNReal.ofReal (gammaBar' h.α h.β))
      (fun x => StationaryMFG.Hamiltonian.mDpH DpH x (fun i => Du i x) (m x))
  /-- `1 < β̄` (paper convention). -/
  hβBar_one_lt : 1 < betaBar h.β
  /-- `(β̄', β̄)` are real Hölder conjugates. -/
  hHolder : (betaBar' h.β).HolderConjugate (betaBar h.β)
  /-- `1 ≤ γ̄'`. -/
  hγBar'_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (gammaBar' h.α h.β)
  /-- Lagrangian lower bound (paper `eq:lagrangian.lb`). -/
  h_lagr :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      ∀ p mx, 0 < mx →
        (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx
  /-- Strict positivity of `m` a.e. (paper `eq:hpos`). -/
  hMpos : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 < m x
  /-- `|V x| ≤ Vbound` a.e. -/
  hVbnd : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), |V x| ≤ Vbound
  /-- Non-negativity of `epsTerms` a.e. -/
  hEpsNN : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ epsTerms x
  /-- Apriori identity (transport-test integrated form). -/
  h_identity :
    ∫ x in UnitCube d, u x ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) =
      ∫ x in UnitCube d,
        (m x * (-H x (fun i => Du i x) (m x)
                  + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
          + V x * m x
          + epsTerms x)
        ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
  /-- `u ∈ L¹` on the cube. -/
  hu_int : MeasureTheory.Integrable u
            (MeasureTheory.volume.restrict (UnitCube d))
  /-- The HJB upper bound's RHS is `L¹`. -/
  hRHSabove_int : MeasureTheory.Integrable
            (fun x => |V x| + h.C * (m x ^ h.β + 1))
            (MeasureTheory.volume.restrict (UnitCube d))
  /-- `m^{β+1} ∈ L¹`. -/
  hLB_int : MeasureTheory.Integrable
              (fun x => m x ^ (h.β + 1))
              (MeasureTheory.volume.restrict (UnitCube d))
  /-- `m^{β} ∈ L¹`. -/
  hMbeta_int : MeasureTheory.Integrable
              (fun x => m x ^ h.β)
              (MeasureTheory.volume.restrict (UnitCube d))
  /-- The integrand of `h_identity`'s RHS is `L¹`. -/
  hRHSbelow_int : MeasureTheory.Integrable
              (fun x =>
                m x * (-H x (fun i => Du i x) (m x)
                          + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                  + V x * m x
                  + epsTerms x)
              (MeasureTheory.volume.restrict (UnitCube d))
  /-- `u` is AE strongly measurable (relaxed from strict `Measurable`
  per `infra-P5-T10-drop-hu_measRaw-hDu_measRaw-final`). -/
  hu_meas : MeasureTheory.AEStronglyMeasurable u
              (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
  /-- `u` is periodic. -/
  hu_per : StationaryMFG.Periodic.IsPeriodic u
  /-- `u` is locally integrable. -/
  hu_loc : MeasureTheory.LocallyIntegrable u
    (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
  /-- Each `Du i` is a weak partial derivative of `u`. -/
  hDu_weak : ∀ i, Periodic.HasWeakDerivPer i u (Du i)
  /-- Each `Du i` is AE strongly measurable. -/
  hDu_meas : ∀ i, MeasureTheory.AEStronglyMeasurable (Du i)
                    (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
  /-- Each `Du i` is periodic. -/
  hDu_per : ∀ i, StationaryMFG.Periodic.IsPeriodic (Du i)
  /-- Each `Du i` is locally integrable. -/
  hDu_loc : ∀ i, MeasureTheory.LocallyIntegrable (Du i)
    (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
  /-- Each `Du i ∈ L^{γ̄}`. -/
  hDu_lp : ∀ i, Periodic.MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) (Du i)
  /-- `‖Du‖^{γ̄}` is `L¹`. -/
  hDu_norm_int : MeasureTheory.Integrable
      (fun x => ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β)
      (MeasureTheory.volume.restrict (UnitCube d))
  /-- `|u|^{β̄'}` is `L¹`. -/
  hUbetap_int : MeasureTheory.Integrable
      (fun x => |u x| ^ betaBar' h.β)
      (MeasureTheory.volume.restrict (UnitCube d))
  /-- `|V|^{β̄'}` is `L¹`. -/
  hVbetap_int : MeasureTheory.Integrable
      (fun x => |V x| ^ betaBar' h.β)
      (MeasureTheory.volume.restrict (UnitCube d))
  /-- `∫|V|^{β̄'} ≤ Vβp_bound`. -/
  hVβp :
    ∫ x in UnitCube d, |V x| ^ betaBar' h.β
        ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) ≤ Vβp_bound
  /-- `u ∈ L^{γ̄}`. -/
  hu_lp_γ : Periodic.MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) u
  /-- C.3 input: `MemLpPer β̄' V` (the paper's `hV` hypothesis). -/
  hV_Lp : Periodic.MemLpPer (ENNReal.ofReal (betaBar' h.β)) V
  /-- F.2-derived strong-VI `set`-form specialisation at `(Du, m, u)`. -/
  hStrongVI_set :
    StationaryMFG.Theorems.SimplePower.StrongVI_setForm
      V H DpH (gammaBar h.α h.β) ε Du m u
  /-- F.2-derived strong-VI `signed`-form specialisation at `(Du, m, u)`. -/
  hStrongVI_signed :
    StationaryMFG.Theorems.SimplePower.StrongVI_setForm_signed
      V H DpH (gammaBar h.α h.β) ε Du m u
  /-- F.2-derived strong-VI `transport`-form specialisation at `(Du, m, u)`. -/
  hStrongVI_transport :
    StationaryMFG.Theorems.SimplePower.StrongVI_transportForm
      V H DpH (gammaBar h.α h.β) ε Du m u

/-- **F.3 — Build `AprioriDischargeInputs` from F.2's strong-VI output.**

Given:
* the standing power-growth hypothesis `h : HypothesisPowerGrowth H DpH`
  (Assumption `onH.powergrowth`);
* a potential `V : (Fin d → ℝ) → ℝ`;
* a Banach-output bundle `B : BanachOutputData (ENNReal.ofReal (betaBar h.β))
    (ENNReal.ofReal (gammaBar h.α h.β)) d` (C.2 output) carrying the
  bare-function triple `(m_ε, u_ε, Du_ε)`;
* an auxiliary input bundle `aux : AprioriInputAuxHyps h V B.Du B.m B.u ε`
  (described above);
* an `ε > 0`,

assemble an `AprioriDischargeInputs h V ε hε` bundle consumed by
`apriori_at_eps`.

Each ~30 field of the output bundle is dispatched as follows:

* `(m, u, Du)` — `B.{m, u, Du}`;
* `epsTerms, Vbound, Vβp_bound` — `aux.{epsTerms, Vbound, Vβp_bound}`;
* `Vint_bound` — `Vint_bound (ENNReal.ofReal (betaBar' h.β)) V` (C.3);
* `hHJB` — `lem_strong_is_strong_HJB_ineq` applied to C.1's residual
  integrability and `aux.hStrongVI_set`;
* `h_lagr` — `aux.h_lagr`;
* `hMpos, hVbnd, hEpsNN, h_identity` — direct from `aux`;
* `hu_int, hRHSabove_int, ..., hRHSbelow_int` — from `aux`;
* `hVint` — `V_norm_le_Vint_bound` from C.3;
* `hγ_one_le, hγ_top` — from `h.hα, h.hβ`;
* `hu_{meas, per, loc, sob}` — from `aux` and `B.u_eps_sobolev`;
* `hDu_weak` — `B.hWeak`;
* `hDu_{meas, per, loc, lp, norm_int}` — from `aux`;
* `hUbetap_int, hVbetap_int, hVβp, hu_lp_γ` — from `aux`. -/
noncomputable def aprioriInputsAtEps
    [AxisMixMeasureHypothesis]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (ε : ℝ) (hε : 0 < ε)
    (B : BanachOutputData (d := d)
            (ENNReal.ofReal (betaBar h.β))
            (ENNReal.ofReal (gammaBar h.α h.β)))
    (aux : AprioriInputAuxHyps (d := d) h V B.Du B.m B.u ε) :
    AprioriDischargeInputs (d := d) h V ε hε where
  u := B.u
  m := B.m
  Du := B.Du
  epsTerms := aux.epsTerms
  Vbound := aux.Vbound
  Vint_bound :=
    StationaryMFG.Theorems.SimplePower.Banach.Vint_bound
      (d := d) (ENNReal.ofReal (betaBar' h.β)) V
  Vβp_bound := aux.Vβp_bound
  hHJB := by
    -- HJB inequality from `lem_strong_is_strong_HJB_ineq` applied to
    -- the C.1 residual integrability and `aux.hStrongVI_set`.
    have hβBar'_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (betaBar' h.β) := by
      have hβ'_one_le : (1 : ℝ) ≤ betaBar' h.β :=
        (one_lt_betaBar' h.β h.hβ).le
      have h1 : ENNReal.ofReal 1 ≤ ENNReal.ofReal (betaBar' h.β) :=
        ENNReal.ofReal_le_ofReal hβ'_one_le
      simpa using h1
    have hRes_int :
        MeasureTheory.Integrable
          (StationaryMFG.Theorems.SimplePower.hjbResidual V H B.Du B.m B.u)
          (MeasureTheory.volume.restrict (UnitCube d)) :=
      aprioriDischarge_residual_integrable
        (βBar' := ENNReal.ofReal (betaBar' h.β))
        hβBar'_one_le aux.hRes_Lp
    exact StationaryMFG.Theorems.SimplePower.lem_strong_is_strong_HJB_ineq
      V H DpH (gammaBar h.α h.β) ε B.Du B.m B.u
      hRes_int aux.hStrongVI_set
  h_lagr := aux.h_lagr
  hMpos := aux.hMpos
  hVbnd := aux.hVbnd
  hEpsNN := aux.hEpsNN
  h_identity := aux.h_identity
  hu_int := aux.hu_int
  hRHSabove_int := aux.hRHSabove_int
  hLB_int := aux.hLB_int
  hMbeta_int := aux.hMbeta_int
  hRHSbelow_int := aux.hRHSbelow_int
  hVint := by
    -- `∫ |V| ≤ Vint_bound β̄' V`, from C.3's `V_norm_le_Vint_bound`,
    -- using `aux.hV_Lp` as the `MemLpPer β̄' V` certificate.
    have hβBar'_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (betaBar' h.β) := by
      have hβ'_one_le : (1 : ℝ) ≤ betaBar' h.β :=
        (one_lt_betaBar' h.β h.hβ).le
      have h1 : ENNReal.ofReal 1 ≤ ENNReal.ofReal (betaBar' h.β) :=
        ENNReal.ofReal_le_ofReal hβ'_one_le
      simpa using h1
    exact V_norm_le_Vint_bound (d := d) hβBar'_one_le aux.hV_Lp
  hγ_one_le := by
    -- `1 ≤ γ̄` from `h.hα, h.hβ`.
    have hγ_one_lt : 1 < gammaBar h.α h.β :=
      one_lt_gammaBar h.α h.β h.hα h.hβ
    have h1 : ENNReal.ofReal 1 ≤ ENNReal.ofReal (gammaBar h.α h.β) :=
      ENNReal.ofReal_le_ofReal hγ_one_lt.le
    simpa using h1
  hγ_top := ENNReal.ofReal_ne_top
  hu_meas := aux.hu_meas
  hu_per := aux.hu_per
  hu_loc := aux.hu_loc
  hu_sob := B.u_eps_sobolev
  hDu_weak := B.hWeak
  hDu_meas := aux.hDu_meas
  hDu_per := aux.hDu_per
  hDu_loc := aux.hDu_loc
  hDu_lp := aux.hDu_lp
  hDu_norm_int := aux.hDu_norm_int
  hUbetap_int := aux.hUbetap_int
  hVbetap_int := aux.hVbetap_int
  hVβp := aux.hVβp
  hu_lp_γ := aux.hu_lp_γ

/-! ### Sanity-check unit `example` for F.3

Pin the type-shape of `aprioriInputsAtEps`: feeding it a
`BanachOutputData` (C.2) and an `AprioriInputAuxHyps` (the auxiliary
input bundle authorised by CONVENTIONS §1b) produces an
`AprioriDischargeInputs` consumable by `apriori_at_eps`. This unit
test does not aim to construct concrete witnesses — it merely verifies
that the assembly type-checks. -/

example
    [AxisMixMeasureHypothesis]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (ε : ℝ) (hε : 0 < ε)
    (B : BanachOutputData (d := d)
            (ENNReal.ofReal (betaBar h.β))
            (ENNReal.ofReal (gammaBar h.α h.β)))
    (aux : AprioriInputAuxHyps (d := d) h V B.Du B.m B.u ε) :
    AprioriDischargeInputs (d := d) h V ε hε :=
  aprioriInputsAtEps (h := h) V ε hε B aux

/-- **F.3 — Composed apriori bound at fixed `ε` from F.2's strong-VI
output.** Composing `aprioriInputsAtEps` with C.4's `apriori_at_eps`:
given the standing power-growth hypothesis, the C.2 Banach output
data, and the auxiliary inputs, conclude the existential ε-uniform
apriori bound on the assembled `AprioriDischargeInputs`'s
`(m, u, Du)` triple, which by construction projects to
`(B.m, B.u, B.Du)`. -/
theorem aprioriBound_at_eps
    [AxisMixMeasureHypothesis]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (ε : ℝ) (hε : 0 < ε)
    (B : BanachOutputData (d := d)
            (ENNReal.ofReal (betaBar h.β))
            (ENNReal.ofReal (gammaBar h.α h.β)))
    (aux : AprioriInputAuxHyps (d := d) h V B.Du B.m B.u ε) :
    let T := aprioriInputsAtEps (h := h) V ε hε B aux
    ∃ C : ℝ, 0 ≤ C ∧
      (∫ x in UnitCube d, T.m x ^ betaBar h.β
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
        + Periodic.lpNormPer
              (ENNReal.ofReal (gammaBar h.α h.β)) T.u
            ^ gammaBar h.α h.β
        + (∫ x in UnitCube d, ‖(fun i => T.Du i x)‖ ^ gammaBar h.α h.β
            ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
          ≤ C :=
  apriori_at_eps (h := h) (V := V) (ε := ε) (hε := hε)
    (aprioriInputsAtEps (h := h) V ε hε B aux)

/-! ## F.3-int — D4.0b4 sibling builders for the integral V-data shape

Mirroring F.3, this block ships sibling builders that consume an
`AprioriVData (betaBar' h.β) V` slot in place of the four V-bound
fields `Vint_bound`, `Vβp_bound`, `hVint`, `hVβp` of the pointwise
variant. The pointwise variant's sibling fields `Vbound`/`hVbnd`
remain present transitionally (the Du closed-form bound has not yet
been migrated to integral V-data; deferred to a `D4.0b5`-shaped
follow-up).

The concrete deliverables:

* `AprioriInputAuxHyps_int` — sibling auxiliary input bundle, identical
  to `AprioriInputAuxHyps` except the four V-bound fields are replaced
  by `vData : AprioriVData (betaBar' h.β) V`.
* `aprioriInputsAtEps_int` — builder for `AprioriDischargeInputs_int`.
* `aprioriBound_at_eps_int` — composed apriori bound at fixed `ε`,
  same existential conclusion as `aprioriBound_at_eps`. -/

/-- **D4.0b4 — Integral V-data sibling of `AprioriInputAuxHyps`.**

Replaces the four V-bound fields `Vint_bound, Vβp_bound, hVint, hVβp`
of the pointwise variant with a single
`AprioriVData (betaBar' h.β) V` slot (`vData`). All other fields are
identical to `AprioriInputAuxHyps`.

The pointwise residue fields `Vbound`/`hVbnd` are kept transitionally
(see the docstring of `AprioriDischargeInputs_int` in
`AprioriDischarge.lean`). -/
structure AprioriInputAuxHyps_int
    [AxisMixMeasureHypothesis]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ)
    (ε : ℝ) where
  /-- The ε-residual integrand. -/
  epsTerms : (Fin d → ℝ) → ℝ
  /-- **Transitional** pointwise bound on `|V|`. -/
  Vbound : ℝ
  /-- **Integral V-data record** (paper-form `L^{β̄'}` bounds on `V`).
  Replaces the pointwise variant's four fields `Vint_bound`,
  `Vβp_bound`, `hVint`, `hVβp`. -/
  vData : AprioriVData (d := d) (betaBar' h.β) V
  /-- C.1 `MemLpPer β̄'`-certificate for the HJB residual. -/
  hRes_Lp :
    Periodic.MemLpPer (ENNReal.ofReal (betaBar' h.β))
      (StationaryMFG.Theorems.SimplePower.hjbResidual V H Du m u)
  /-- C.1 `MemLpPer β̄`-certificate for `m`. -/
  hm_Lp : Periodic.MemLpPer (ENNReal.ofReal (betaBar h.β)) m
  /-- C.1 `MemLpPer γ̄'`-certificate for the flux. -/
  hFlux_Lp :
    Periodic.MemLpPer (ENNReal.ofReal (gammaBar' h.α h.β))
      (fun x => StationaryMFG.Hamiltonian.mDpH DpH x (fun i => Du i x) (m x))
  /-- `1 < β̄`. -/
  hβBar_one_lt : 1 < betaBar h.β
  /-- `(β̄', β̄)` are real Hölder conjugates. -/
  hHolder : (betaBar' h.β).HolderConjugate (betaBar h.β)
  /-- `1 ≤ γ̄'`. -/
  hγBar'_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (gammaBar' h.α h.β)
  /-- Lagrangian lower bound. -/
  h_lagr :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      ∀ p mx, 0 < mx →
        (mx ^ h.β) / h.C - h.C ≤ (DpH x p mx) ⬝ p - H x p mx
  /-- Strict positivity of `m` a.e. -/
  hMpos : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 < m x
  /-- **Transitional** `|V x| ≤ Vbound` a.e. -/
  hVbnd : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), |V x| ≤ Vbound
  /-- Non-negativity of `epsTerms` a.e. -/
  hEpsNN : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ epsTerms x
  /-- Apriori identity. -/
  h_identity :
    ∫ x in UnitCube d, u x ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) =
      ∫ x in UnitCube d,
        (m x * (-H x (fun i => Du i x) (m x)
                  + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
          + V x * m x
          + epsTerms x)
        ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
  /-- `u ∈ L¹` on the cube. -/
  hu_int : MeasureTheory.Integrable u
            (MeasureTheory.volume.restrict (UnitCube d))
  /-- The HJB upper bound's RHS is `L¹`. -/
  hRHSabove_int : MeasureTheory.Integrable
            (fun x => |V x| + h.C * (m x ^ h.β + 1))
            (MeasureTheory.volume.restrict (UnitCube d))
  /-- `m^{β+1} ∈ L¹`. -/
  hLB_int : MeasureTheory.Integrable
              (fun x => m x ^ (h.β + 1))
              (MeasureTheory.volume.restrict (UnitCube d))
  /-- `m^{β} ∈ L¹`. -/
  hMbeta_int : MeasureTheory.Integrable
              (fun x => m x ^ h.β)
              (MeasureTheory.volume.restrict (UnitCube d))
  /-- The integrand of `h_identity`'s RHS is `L¹`. -/
  hRHSbelow_int : MeasureTheory.Integrable
              (fun x =>
                m x * (-H x (fun i => Du i x) (m x)
                          + (DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
                  + V x * m x
                  + epsTerms x)
              (MeasureTheory.volume.restrict (UnitCube d))
  /-- `u` is AE strongly measurable. -/
  hu_meas : MeasureTheory.AEStronglyMeasurable u
              (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
  /-- `u` is periodic. -/
  hu_per : StationaryMFG.Periodic.IsPeriodic u
  /-- `u` is locally integrable. -/
  hu_loc : MeasureTheory.LocallyIntegrable u
    (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
  /-- Each `Du i` is a weak partial derivative of `u`. -/
  hDu_weak : ∀ i, Periodic.HasWeakDerivPer i u (Du i)
  /-- Each `Du i` is AE strongly measurable. -/
  hDu_meas : ∀ i, MeasureTheory.AEStronglyMeasurable (Du i)
                    (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
  /-- Each `Du i` is periodic. -/
  hDu_per : ∀ i, StationaryMFG.Periodic.IsPeriodic (Du i)
  /-- Each `Du i` is locally integrable. -/
  hDu_loc : ∀ i, MeasureTheory.LocallyIntegrable (Du i)
    (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
  /-- Each `Du i ∈ L^{γ̄}`. -/
  hDu_lp : ∀ i, Periodic.MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) (Du i)
  /-- `‖Du‖^{γ̄}` is `L¹`. -/
  hDu_norm_int : MeasureTheory.Integrable
      (fun x => ‖(fun i => Du i x)‖ ^ gammaBar h.α h.β)
      (MeasureTheory.volume.restrict (UnitCube d))
  /-- `|u|^{β̄'}` is `L¹`. -/
  hUbetap_int : MeasureTheory.Integrable
      (fun x => |u x| ^ betaBar' h.β)
      (MeasureTheory.volume.restrict (UnitCube d))
  /-- `|V|^{β̄'}` is `L¹`. -/
  hVbetap_int : MeasureTheory.Integrable
      (fun x => |V x| ^ betaBar' h.β)
      (MeasureTheory.volume.restrict (UnitCube d))
  /-- `u ∈ L^{γ̄}`. -/
  hu_lp_γ : Periodic.MemLpPer (ENNReal.ofReal (gammaBar h.α h.β)) u
  /-- C.3 input: `MemLpPer β̄' V` (the paper's `hV` hypothesis). -/
  hV_Lp : Periodic.MemLpPer (ENNReal.ofReal (betaBar' h.β)) V
  /-- F.2-derived strong-VI `set`-form specialisation at `(Du, m, u)`. -/
  hStrongVI_set :
    StationaryMFG.Theorems.SimplePower.StrongVI_setForm
      V H DpH (gammaBar h.α h.β) ε Du m u
  /-- F.2-derived strong-VI `signed`-form specialisation at `(Du, m, u)`. -/
  hStrongVI_signed :
    StationaryMFG.Theorems.SimplePower.StrongVI_setForm_signed
      V H DpH (gammaBar h.α h.β) ε Du m u
  /-- F.2-derived strong-VI `transport`-form specialisation at `(Du, m, u)`. -/
  hStrongVI_transport :
    StationaryMFG.Theorems.SimplePower.StrongVI_transportForm
      V H DpH (gammaBar h.α h.β) ε Du m u

/-- **D4.0b4 — Build `AprioriDischargeInputs_int` from F.2's strong-VI
output.** Sibling of `aprioriInputsAtEps`, consuming
`AprioriInputAuxHyps_int` (which carries an `AprioriVData` slot in
place of the four V-bound fields). -/
noncomputable def aprioriInputsAtEps_int
    [AxisMixMeasureHypothesis]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (ε : ℝ) (hε : 0 < ε)
    (B : BanachOutputData (d := d)
            (ENNReal.ofReal (betaBar h.β))
            (ENNReal.ofReal (gammaBar h.α h.β)))
    (aux : AprioriInputAuxHyps_int (d := d) h V B.Du B.m B.u ε) :
    AprioriDischargeInputs_int (d := d) h V ε hε where
  u := B.u
  m := B.m
  Du := B.Du
  epsTerms := aux.epsTerms
  Vbound := aux.Vbound
  vData := aux.vData
  hHJB := by
    have hβBar'_one_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (betaBar' h.β) := by
      have hβ'_one_le : (1 : ℝ) ≤ betaBar' h.β :=
        (one_lt_betaBar' h.β h.hβ).le
      have h1 : ENNReal.ofReal 1 ≤ ENNReal.ofReal (betaBar' h.β) :=
        ENNReal.ofReal_le_ofReal hβ'_one_le
      simpa using h1
    have hRes_int :
        MeasureTheory.Integrable
          (StationaryMFG.Theorems.SimplePower.hjbResidual V H B.Du B.m B.u)
          (MeasureTheory.volume.restrict (UnitCube d)) :=
      aprioriDischarge_residual_integrable
        (βBar' := ENNReal.ofReal (betaBar' h.β))
        hβBar'_one_le aux.hRes_Lp
    exact StationaryMFG.Theorems.SimplePower.lem_strong_is_strong_HJB_ineq
      V H DpH (gammaBar h.α h.β) ε B.Du B.m B.u
      hRes_int aux.hStrongVI_set
  h_lagr := aux.h_lagr
  hMpos := aux.hMpos
  hVbnd := aux.hVbnd
  hEpsNN := aux.hEpsNN
  h_identity := aux.h_identity
  hu_int := aux.hu_int
  hRHSabove_int := aux.hRHSabove_int
  hLB_int := aux.hLB_int
  hMbeta_int := aux.hMbeta_int
  hRHSbelow_int := aux.hRHSbelow_int
  hγ_one_le := by
    have hγ_one_lt : 1 < gammaBar h.α h.β :=
      one_lt_gammaBar h.α h.β h.hα h.hβ
    have h1 : ENNReal.ofReal 1 ≤ ENNReal.ofReal (gammaBar h.α h.β) :=
      ENNReal.ofReal_le_ofReal hγ_one_lt.le
    simpa using h1
  hγ_top := ENNReal.ofReal_ne_top
  hu_meas := aux.hu_meas
  hu_per := aux.hu_per
  hu_loc := aux.hu_loc
  hu_sob := B.u_eps_sobolev
  hDu_weak := B.hWeak
  hDu_meas := aux.hDu_meas
  hDu_per := aux.hDu_per
  hDu_loc := aux.hDu_loc
  hDu_lp := aux.hDu_lp
  hDu_norm_int := aux.hDu_norm_int
  hUbetap_int := aux.hUbetap_int
  hVbetap_int := aux.hVbetap_int
  hu_lp_γ := aux.hu_lp_γ

/-! ### Sanity-check unit `example`s pinning the type-shape of the
D4.0b4 sibling. -/

example
    [AxisMixMeasureHypothesis]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (ε : ℝ) (hε : 0 < ε)
    (B : BanachOutputData (d := d)
            (ENNReal.ofReal (betaBar h.β))
            (ENNReal.ofReal (gammaBar h.α h.β)))
    (aux : AprioriInputAuxHyps_int (d := d) h V B.Du B.m B.u ε) :
    AprioriDischargeInputs_int (d := d) h V ε hε :=
  aprioriInputsAtEps_int (h := h) V ε hε B aux

/-- **D4.0b4 — Composed apriori bound at fixed `ε` from F.2's strong-VI
output (integral V-data sibling).** Sibling of `aprioriBound_at_eps`,
composing `aprioriInputsAtEps_int` with `apriori_at_eps_int`. -/
theorem aprioriBound_at_eps_int
    [AxisMixMeasureHypothesis]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisPowerGrowth H DpH)
    (V : (Fin d → ℝ) → ℝ)
    (ε : ℝ) (hε : 0 < ε)
    (B : BanachOutputData (d := d)
            (ENNReal.ofReal (betaBar h.β))
            (ENNReal.ofReal (gammaBar h.α h.β)))
    (aux : AprioriInputAuxHyps_int (d := d) h V B.Du B.m B.u ε) :
    let T := aprioriInputsAtEps_int (h := h) V ε hε B aux
    ∃ C : ℝ, 0 ≤ C ∧
      (∫ x in UnitCube d, T.m x ^ betaBar h.β
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
        + Periodic.lpNormPer
              (ENNReal.ofReal (gammaBar h.α h.β)) T.u
            ^ gammaBar h.α h.β
        + (∫ x in UnitCube d, ‖(fun i => T.Du i x)‖ ^ gammaBar h.α h.β
            ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)))
          ≤ C :=
  apriori_at_eps_int (h := h) (V := V) (ε := ε) (hε := hε)
    (aprioriInputsAtEps_int (h := h) V ε hε B aux)

/-! ## F.4 — Build the ε-uniform sequence concretely

Apply C.5's `exists_uniform_eps_sequence` to F.2 + F.3 to produce a
concrete sequence `(ε_k, q_k) : ℕ → ℝ × X` with:
* `ε_k → 0`,
* each `q_k ∈ K_Aepsi`,
* each `q_k` solving the strong VI at `ε_k` (i.e. the F.2 strong-VI
  conclusion at parameter `ε_k`),
* uniform Banach-pair-norm bound `‖q_k‖ ≤ C`.

The "uniform bound" `C` is the ε-independent apriori constant from
F.3 / C.4 (`aprioriBound_at_eps`). The wiring takes a per-`k` family
of step bundles, each carrying the F.2 strong-VI witness plus its
`K_Aepsi`-membership/`hNorm` certificates, and threads them through
the canonical sequence `epsSeq k := 1 / (k + 1)` from C.5. -/

/-- **Per-`k` step input** for the ε-uniform sequence construction.

Records:
* `q` — the strong-VI witness in the Banach-pair domain at `ε := epsSeq k`,
  produced by F.2 (`existsStrongVI_at_eps`).
* `hK` — the `K_Aepsi`-membership certificate for `q` (the strict-positivity
  cone, paper `eq:hpos`).
* `hVI` — the strong-VI inequality at `ε := epsSeq k`:
  `∀ q' ∈ K_Aepsi …, 0 ≤ Aepsi_CLM_op … (epsSeq k) q (q' - q)`.
* `hNorm` — uniform bound `‖q‖ ≤ C` on the Banach-pair norm
  (the ε-independent constant from F.3 / C.4). -/
structure EpsSequenceStep
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (γBarReal βBarReal βBarReal' γBarReal' : ℝ)
    [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (auxHyps : ∀ (Du : Fin d → (Fin d → ℝ) → ℝ) (m u : (Fin d → ℝ) → ℝ),
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V H DpH Du m u)
    (C : ℝ) (k : ℕ) where
  /-- Strong-VI witness at `ε := epsSeq k`. -/
  q : palomar_Closure_XBanachClosure d βBarReal γBarReal
  /-- Strict-positivity cone membership. -/
  hK : q ∈ K_Aepsi d βBarReal γBarReal
  /-- Strong-VI inequality at `ε := epsSeq k`. -/
  hVI : ∀ q' ∈ K_Aepsi d βBarReal γBarReal,
          0 ≤ Aepsi_CLM_op (γBarReal := γBarReal) (βBarReal := βBarReal)
                (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                V H DpH auxHyps (epsSeq k) q (q' - q)
  /-- Uniform Banach-pair-norm bound. -/
  hNorm : ‖q‖ ≤ C

/-- **F.4 — Build the ε-uniform sequence concretely.**

Given a per-`k` family of step bundles `EpsSequenceStep …` (each
packaging F.2's strong-VI witness at `ε := epsSeq k` plus its
`K_Aepsi`-membership and uniform Banach-pair-norm bound), produce the
joint existential conclusion:
* `ε : ℕ → ℝ` — the canonical sequence `epsSeq` (= `k ↦ 1 / (k + 1)`),
* `q : ℕ → X` — the per-`k` strong-VI witnesses,
* `ε → 0`,
* `∀ k, q k ∈ K_Aepsi`,
* `∀ k, strong-VI at (ε k, q k)` (the F.2 strong-VI conclusion),
* `∀ k, ‖q k‖ ≤ C`.

This is the F.4 deliverable wiring F.2's per-`ε` strong-VI output and
F.3's ε-independent norm bound into C.5's `exists_uniform_eps_sequence`
plumbing. -/
theorem uniformEpsSequence
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (auxHyps : ∀ (Du : Fin d → (Fin d → ℝ) → ℝ) (m u : (Fin d → ℝ) → ℝ),
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V H DpH Du m u)
    {C : ℝ}
    (steps : ∀ k : ℕ, EpsSequenceStep (d := d) V H DpH
                          γBarReal βBarReal βBarReal' γBarReal'
                          auxHyps C k) :
    ∃ (ε : ℕ → ℝ) (q : ℕ → palomar_Closure_XBanachClosure d βBarReal γBarReal),
      Filter.Tendsto ε Filter.atTop (nhds 0)
        ∧ (∀ k, q k ∈ K_Aepsi d βBarReal γBarReal)
        ∧ (∀ k, ∀ q' ∈ K_Aepsi d βBarReal γBarReal,
              0 ≤ Aepsi_CLM_op (γBarReal := γBarReal) (βBarReal := βBarReal)
                    (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                    V H DpH auxHyps (ε k) (q k) (q' - q k))
        ∧ (∀ k, ‖q k‖ ≤ C) := by
  refine ⟨epsSeq, fun k => (steps k).q, ?_, ?_, ?_, ?_⟩
  · exact epsSeq_tendsto_zero
  · intro k; exact (steps k).hK
  · intro k q' hq'; exact (steps k).hVI q' hq'
  · intro k; exact (steps k).hNorm

/-! ### Sanity-check unit `example` for F.4

Pin the type-shape of `uniformEpsSequence`: feeding it a per-`k` step
family produces the joint existential conclusion. We exercise the wiring
on a structurally trivial step: any per-`k` family of `EpsSequenceStep`
bundles type-checks, and the headline `uniformEpsSequence` discharges
the existential. -/

example
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (auxHyps : ∀ (Du : Fin d → (Fin d → ℝ) → ℝ) (m u : (Fin d → ℝ) → ℝ),
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V H DpH Du m u)
    {C : ℝ}
    (steps : ∀ k : ℕ, EpsSequenceStep (d := d) V H DpH
                          γBarReal βBarReal βBarReal' γBarReal'
                          auxHyps C k) :
    ∃ (ε : ℕ → ℝ) (q : ℕ → palomar_Closure_XBanachClosure d βBarReal γBarReal),
      Filter.Tendsto ε Filter.atTop (nhds 0)
        ∧ (∀ k, q k ∈ K_Aepsi d βBarReal γBarReal)
        ∧ (∀ k, ∀ q' ∈ K_Aepsi d βBarReal γBarReal,
              0 ≤ Aepsi_CLM_op (γBarReal := γBarReal) (βBarReal := βBarReal)
                    (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                    V H DpH auxHyps (ε k) (q k) (q' - q k))
        ∧ (∀ k, ‖q k‖ ≤ C) :=
  uniformEpsSequence (V := V) (H := H) (DpH := DpH) auxHyps steps

/-! ## F.5 — Extract bare-function weak limit

Apply `exists_weak_cluster_point` (Phase-4 weak compactness, abstract
form) to F.4's bounded sequence to obtain a weak cluster point
`z ∈ WeakSpace ℝ (LpPer β̄ × SobolevPerLp 1 γ̄)`. Convert back to a
concrete pair `w := (toWeakSpace ℝ _).symm z`, build a `WeakLimitData`
bundle (D.1) using the supplied auxiliary certificates `hWeak`, `hPerM`,
`hPerU`, and apply `weak_limit_to_bare` plus `m_nonneg_weak_limit`
(D.1 + D.2) to deliver the bare-function triple `(m, u, Du)` with:

* `MemLpPer β̄ m`, `MemSobolevPer γ̄ u`,
* `IsPeriodic m`, `IsPeriodic u`,
* `HasWeakDerivPer i u (Du i)`,
* `0 ≤ m` a.e. (Mazur on the non-negative cone in `LpPer`).

Because the public abstract `exists_weak_cluster_point` lives at
`StationaryMFG.Theorems.SimplePower` (parent namespace), and the
pair-shaped version `exists_weak_cluster_point_pair` references a
file-private helper `weakProdFst` of `Compactness.lean` (not visible
here), we use the abstract form directly on the product
`X := LpPer β̄ d × SobolevPerLp 1 γ̄ d`, with the cone constraint encoded
at the product level via `nonNegConeProd`.
-/

/-- **The non-negative cone in `LpPer βBar d × SobolevPerLp 1 γBar d`.**

`nonNegConeProd βBar γBar d := {w | 0 ≤ ⇑w.1 a.e.}` is the set of
Banach pairs whose first-component representative is non-negative
almost everywhere on the unit cube. -/
def nonNegConeProd (βBar γBar : ℝ≥0∞) (d : ℕ) :
    Set (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d) :=
  {w | 0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        (⇑w.1 : (Fin d → ℝ) → ℝ)}

/-- The first-coordinate projection
`WeakSpace ℝ (LpPer βBar d × SobolevPerLp 1 γBar d)
    → WeakSpace ℝ (LpPer βBar d)`, defined as
`WeakSpace.map (ContinuousLinearMap.fst ℝ _ _)`.

A public re-derivation of the file-private `weakProdFst` of
`Theorems/SimplePower/Compactness.lean`, exposed here for use in the
F.5 weak-limit extraction. -/
def weakProdFstLpSob (βBar γBar : ℝ≥0∞) [Fact (1 ≤ βBar)] [Fact (1 ≤ γBar)]
    (d : ℕ) :
    WeakSpace ℝ (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)
      → WeakSpace ℝ (Periodic.LpPer βBar d) :=
  WeakSpace.map
    (ContinuousLinearMap.fst ℝ
      (Periodic.LpPer βBar d) (Periodic.SobolevPerLp 1 γBar d))

lemma continuous_weakProdFstLpSob (βBar γBar : ℝ≥0∞)
    [Fact (1 ≤ βBar)] [Fact (1 ≤ γBar)] (d : ℕ) :
    Continuous (weakProdFstLpSob βBar γBar d) :=
  (WeakSpace.map
    (ContinuousLinearMap.fst ℝ
      (Periodic.LpPer βBar d) (Periodic.SobolevPerLp 1 γBar d))).continuous

/-- **The image of `nonNegConeProd` under `toWeakSpace` is sequentially
closed in `WeakSpace ℝ (LpPer × SobolevPerLp 1)`.**

Strategy: characterise membership in the image as the preimage of the
weakly-sequentially-closed `(toWeakSpace …) '' nonNegConeLpPer βBar d`
under the continuous projection `weakProdFstLpSob`. Concretely, an
element `z ∈ WeakSpace ℝ (Y × Z)` is in the image of `nonNegConeProd`
iff its first-coordinate projection `weakProdFstLpSob z` is in the
image of `nonNegConeLpPer`. -/
theorem nonNegConeProd_isSeqClosedW
    (βBar γBar : ℝ≥0∞) [Fact (1 ≤ βBar)] [Fact (1 ≤ γBar)] (d : ℕ) :
    IsSeqClosed
      ((toWeakSpace ℝ
          (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)) ''
        (nonNegConeProd βBar γBar d)) := by
  -- We characterise the image as the preimage of the corresponding
  -- weakly-sequentially-closed image of `nonNegConeLpPer` under the
  -- first-coordinate projection.
  intro w wlim hmem hconv
  -- Project to the first factor in `WeakSpace ℝ (LpPer βBar d)`.
  have hcont : Continuous (weakProdFstLpSob βBar γBar d) :=
    continuous_weakProdFstLpSob βBar γBar d
  have hconv₁ :
      Filter.Tendsto (fun k => weakProdFstLpSob βBar γBar d (w k))
        Filter.atTop (𝓝 (weakProdFstLpSob βBar γBar d wlim)) :=
    hcont.tendsto wlim |>.comp hconv
  -- The first-component image lies in the seq-closed cone of `LpPer βBar d`.
  have hmem₁ : ∀ k, weakProdFstLpSob βBar γBar d (w k) ∈
      (toWeakSpace ℝ (Periodic.LpPer βBar d)) '' nonNegConeLpPer βBar d := by
    intro k
    rcases hmem k with ⟨v, hv_mem, hv_eq⟩
    refine ⟨v.1, hv_mem, ?_⟩
    -- Compute `weakProdFstLpSob (toWeakSpace … v) = toWeakSpace … v.1`.
    have h_proj :
        weakProdFstLpSob βBar γBar d
            ((toWeakSpace ℝ
              (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)) v)
          = (toWeakSpace ℝ (Periodic.LpPer βBar d)) v.1 := by
      rfl
    rw [← hv_eq, h_proj]
  have hSeq₁ :
      IsSeqClosed
        ((toWeakSpace ℝ (Periodic.LpPer βBar d)) '' nonNegConeLpPer βBar d) :=
    nonNegConeLpPer_isSeqClosedW (d := d)
  have hwlim_proj :
      weakProdFstLpSob βBar γBar d wlim ∈
        (toWeakSpace ℝ (Periodic.LpPer βBar d)) '' nonNegConeLpPer βBar d :=
    hSeq₁ hmem₁ hconv₁
  -- Lift back: `wlim` itself is in the product image.
  -- Take the concrete preimage `w_concrete := (toWeakSpace ℝ _).symm wlim`.
  set w_concrete :
      Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d :=
    (toWeakSpace ℝ
      (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)).symm wlim
    with hw_concrete_def
  refine ⟨w_concrete, ?_, ?_⟩
  · -- `w_concrete.1 = (toWeakSpace ℝ (LpPer βBar d)).symm (weakProdFstLpSob wlim)`,
    -- which by construction has a non-negative representative.
    rcases hwlim_proj with ⟨v₁, hv₁_mem, hv₁_eq⟩
    -- `weakProdFstLpSob wlim = toWeakSpace ℝ _ v₁`, hence (by injectivity of
    -- `toWeakSpace ℝ _`) `(toWeakSpace ℝ _).symm (weakProdFstLpSob wlim) = v₁`.
    have h_eq_proj :
        weakProdFstLpSob βBar γBar d
            ((toWeakSpace ℝ
              (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d))
                w_concrete)
          = (toWeakSpace ℝ (Periodic.LpPer βBar d)) w_concrete.1 := by
      rfl
    have h_w_eq :
        (toWeakSpace ℝ
          (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d))
          w_concrete = wlim := by
      simp [hw_concrete_def]
    rw [h_w_eq] at h_eq_proj
    -- So `weakProdFstLpSob wlim = (toWeakSpace ℝ _) w_concrete.1` and
    -- `(toWeakSpace ℝ _) v₁ = weakProdFstLpSob wlim`.
    rw [← hv₁_eq] at h_eq_proj
    have h_v₁_eq : v₁ = w_concrete.1 :=
      (toWeakSpace ℝ (Periodic.LpPer βBar d)).injective h_eq_proj
    -- Conclude `w_concrete.1 ∈ nonNegConeLpPer βBar d`.
    change 0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
            (⇑w_concrete.1 : (Fin d → ℝ) → ℝ)
    rw [← h_v₁_eq]
    exact hv₁_mem
  · simp [hw_concrete_def]

/-- **Per-extraction input bundle for `extractWeakLimit` (F.5).**

Path-B refactor (`infra-P4-rebuild-T8-discharge-aux-weakLimit-selector`):
the cluster-point-dependent `auxOfWeakLimit` field of the previous
shape has been replaced by **sequence-side bare data** plus a chosen
periodic limit and test-function `Tendsto` hypotheses, so the
weak-derivative limit-passage is now genuinely discharged closed-form
inside `extractWeakLimit` via `Periodic.HasWeakDerivPer.of_weak_limit`.

The residual cluster-point-dependent witness `auxAeOfClusterPoint`
records only **a.e.-equality** between the chosen periodic limit and
the cluster point's `Lp.coeFn` representative — the genuine
periodic-representative-selector obstruction (Path A) — and is
strictly narrower than the previous `auxOfWeakLimit` (which demanded
pointwise periodicity *and* a weak-derivative relation between
unspecified Lp coercions).

Fields:

* `v_n`, `hBound`, `hMpos`, `hRefl`, `hSep` — unchanged sequence-side
  Banach-pair data plus reflexivity / separability infrastructure.
* `mLim`, `uLim`, `DuLim` — chosen bare-function periodic limit
  (sequence-independent witnesses, supplied by the caller).
* `hMlimPer`, `hUlimPer` — `IsPeriodic mLim`, `IsPeriodic uLim`.
* `hDuLim_memLp` — `MemLpPer 1 (DuLim i)` (required by
  `HasWeakDerivPer.of_weak_limit`).
* `seqRepU n`, `seqRepDu n i` — sequence-side periodic representatives
  a.e.-equal to the Lp coercions of `(v_n n).2.1, (v_n n).2.2 i`.
* `hSeqRepWeak n i` — per-`n` bare-function weak-derivative relation
  between `seqRepU n` and `seqRepDu n i`.
* `hConvU`, `hConvDu` — test-function `Tendsto` hypotheses for the
  chosen subsequence (we range over an arbitrary `φ : ℕ → ℕ` because
  the cluster-point extraction inside `extractWeakLimit` chooses
  `φ` via Banach–Alaoglu; `extractWeakLimit` will instantiate at the
  produced `φ`).
* `auxAeOfClusterPoint w` — a.e.-equality between `(mLim, uLim, DuLim)`
  and the Lp coercions of an arbitrary candidate cluster point `w`,
  carrying the residual Path-A obstruction. -/
structure WeakLimitInputData
    (βBar γBar : ℝ≥0∞) [Fact (1 ≤ βBar)] [Fact (1 ≤ γBar)] (d : ℕ) where
  /-- The bounded sequence of Banach-pair elements. -/
  v_n : ℕ → Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d
  /-- Norm-bound on the sequence. -/
  hBound : Bornology.IsBounded (Set.range v_n)
  /-- Per-`n` non-negativity of the first-component representative. -/
  hMpos : ∀ n,
    0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
      (⇑(v_n n).1 : (Fin d → ℝ) → ℝ)
  /-- Reflexivity of the Banach pair. -/
  hRefl : Periodic.IsReflexiveNormedSpace
    (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)
  /-- Separability of the strong dual (needed by
  `weakSeqCompact_of_bounded_reflexive`). -/
  hSep : TopologicalSpace.SeparableSpace
    (StrongDual ℝ
      (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d))
  /-- Chosen periodic bare-function limit for the `m`-component. -/
  mLim : (Fin d → ℝ) → ℝ
  /-- Chosen periodic bare-function limit for the `u`-component. -/
  uLim : (Fin d → ℝ) → ℝ
  /-- Chosen periodic bare-function limit for the gradient family. -/
  DuLim : Fin d → (Fin d → ℝ) → ℝ
  /-- Pointwise periodicity of the chosen `m`-limit. -/
  hMlimPer : Periodic.IsPeriodic mLim
  /-- Pointwise periodicity of the chosen `u`-limit. -/
  hUlimPer : Periodic.IsPeriodic uLim
  /-- `L¹_per`-membership of every gradient-limit component, required by
  `HasWeakDerivPer.of_weak_limit`. -/
  hDuLim_memLp : ∀ i, Periodic.MemLpPer (d := d) 1 (DuLim i)
  /-- Sequence-side periodic representative of the `u`-component. -/
  seqRepU : ℕ → (Fin d → ℝ) → ℝ
  /-- Sequence-side periodic representative of the gradient family. -/
  seqRepDu : ℕ → Fin d → (Fin d → ℝ) → ℝ
  /-- Per-`n`, per-`i` bare-function weak-derivative relation between
  `seqRepU n` and `seqRepDu n i`. -/
  hSeqRepWeak : ∀ n i,
    Periodic.HasWeakDerivPer (d := d) i (seqRepU n) (seqRepDu n i)
  /-- For every test function and every strictly-monotone subsequence
  index `φ : ℕ → ℕ`, the integrals of `seqRepU (φ k) · ψ` converge to
  the integral of `uLim · ψ`. (`extractWeakLimit` produces a specific
  `φ` via Banach–Alaoglu; the universal-`φ` quantification keeps this
  field independent of the internal choice.) -/
  hConvU : ∀ (φ : ℕ → ℕ), StrictMono φ →
    ∀ ψ : Periodic.SmoothPeriodic d,
      Filter.Tendsto
        (fun k => StationaryMFG.Periodic.periodicIntegral
                    (fun x =>
                      seqRepU (φ k) x *
                        (ψ : (Fin d → ℝ) → ℝ) x))
        Filter.atTop
        (𝓝 (StationaryMFG.Periodic.periodicIntegral
              (fun x => uLim x * (ψ : (Fin d → ℝ) → ℝ) x)))
  /-- Per-coordinate test-function convergence between the gradient
  sequence and the chosen gradient limit. -/
  hConvDu : ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ i,
    ∀ ψ : Periodic.SmoothPeriodic d,
      Filter.Tendsto
        (fun k => StationaryMFG.Periodic.periodicIntegral
                    (fun x =>
                      seqRepDu (φ k) i x *
                        (ψ : (Fin d → ℝ) → ℝ) x))
        Filter.atTop
        (𝓝 (StationaryMFG.Periodic.periodicIntegral
              (fun x => DuLim i x * (ψ : (Fin d → ℝ) → ℝ) x)))
  /-- Residual Path-A obstruction: a.e.-equalities between the chosen
  bare-function limit `(mLim, uLim, DuLim)` and the Lp coercions of any
  candidate cluster point `w`. The cluster-point-dependence is
  irreducible without a periodic-representative selector for `Lp.coeFn`
  (see the parent task `infra-P4-rebuild-T8-discharge-aux-weakLimit`'s
  reconnaissance). -/
  auxAeOfClusterPoint : ∀
    (w : Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d),
      mLim
        =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
          (⇑w.1 : (Fin d → ℝ) → ℝ)
      ∧ uLim
          =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                (UnitCube d)]
          (⇑w.2.1 : (Fin d → ℝ) → ℝ)
      ∧ ∀ i, DuLim i
          =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                (UnitCube d)]
          (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ)

/-- **F.5 — Extract bare-function weak limit.**

Given a `WeakLimitInputData` bundle (the F.4 bounded sequence plus the
cluster-point-dependent auxiliary certificates), extract:

* a strictly increasing index function `φ : ℕ → ℕ`,
* a weak-limit Banach pair `w : LpPer βBar d × SobolevPerLp 1 γBar d`
  whose first component has a non-negative representative a.e.,
* the bare-function projections `(m, u, Du)` of `w`,
* the four classes of facts D.1 produces:
  `MemLpPer βBar m`, `MemSobolevPer γBar u`, `IsPeriodic m`,
  `IsPeriodic u`, `AEStronglyMeasurable m`, `AEStronglyMeasurable u`,
  `HasWeakDerivPer i u (Du i)`,
* the D.2 fact: `0 ≤ m` a.e.,
* the abstract weak-convergence statement:
  `Tendsto (fun k => toWeakSpace ℝ _ (v_n (φ k))) atTop (𝓝 (toWeakSpace ℝ _ w))`. -/
theorem extractWeakLimit
    {βBar γBar : ℝ≥0∞} [Fact (1 ≤ βBar)] [Fact (1 ≤ γBar)]
    (T : WeakLimitInputData (d := d) βBar γBar) :
    ∃ (φ : ℕ → ℕ)
      (w : Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)
      (m u : (Fin d → ℝ) → ℝ) (Du : Fin d → (Fin d → ℝ) → ℝ),
      StrictMono φ
        ∧ m =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                  (UnitCube d)] (⇑w.1 : (Fin d → ℝ) → ℝ)
        ∧ u =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                  (UnitCube d)] (⇑w.2.1 : (Fin d → ℝ) → ℝ)
        ∧ (∀ i, Du i
              =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                    (UnitCube d)] (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ))
        ∧ Periodic.MemLpPer βBar m
        ∧ Periodic.MemSobolevPer γBar u
        ∧ Periodic.IsPeriodic m
        ∧ Periodic.IsPeriodic u
        ∧ MeasureTheory.AEStronglyMeasurable m
            (MeasureTheory.Measure.restrict
              MeasureTheory.volume (UnitCube d))
        ∧ MeasureTheory.AEStronglyMeasurable u
            (MeasureTheory.Measure.restrict
              MeasureTheory.volume (UnitCube d))
        ∧ (∀ i, Periodic.HasWeakDerivPer i u (Du i))
        ∧ 0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                  (UnitCube d)] m
        ∧ Filter.Tendsto
            (fun k => (toWeakSpace ℝ
              (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d))
                (T.v_n (φ k)))
            Filter.atTop
            (𝓝 ((toWeakSpace ℝ
              (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)) w)) := by
  -- 1. Apply abstract weak-cluster-point extraction on the product.
  haveI : TopologicalSpace.SeparableSpace
            (StrongDual ℝ
              (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)) :=
    T.hSep
  -- The cone-membership constraint at the product level.
  set S :
      Set (WeakSpace ℝ
        (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)) :=
    (toWeakSpace ℝ
        (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)) ''
      (nonNegConeProd βBar γBar d) with hS_def
  have hS_closed : IsSeqClosed S := nonNegConeProd_isSeqClosedW βBar γBar d
  have hmem : ∀ n, (toWeakSpace ℝ _) (T.v_n n) ∈ S := by
    intro n
    refine ⟨T.v_n n, ?_, rfl⟩
    change 0 ≤ᵐ[MeasureTheory.Measure.restrict
              MeasureTheory.volume (UnitCube d)]
            (⇑(T.v_n n).1 : (Fin d → ℝ) → ℝ)
    exact T.hMpos n
  obtain ⟨φ, z, hmono, hzS, hzlim⟩ :=
    StationaryMFG.Theorems.SimplePower.exists_weak_cluster_point
      T.hRefl T.v_n T.hBound hS_closed hmem
  -- 2. Convert the cluster point to a concrete pair.
  set w : Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d :=
    (toWeakSpace ℝ
      (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)).symm z
    with hw_def
  have hw_eq :
      (toWeakSpace ℝ
        (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)) w = z := by
    simp [hw_def]
  -- 3. The first component has a non-negative representative.
  rcases hzS with ⟨w', hw'_mem, hw'_eq⟩
  have hw_eq_w' : w = w' := by
    have : (toWeakSpace ℝ
      (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)) w
        = (toWeakSpace ℝ
            (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)) w' := by
      rw [hw_eq, hw'_eq]
    exact (toWeakSpace ℝ
      (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)).injective this
  have hm_nonneg_w :
      0 ≤ᵐ[MeasureTheory.Measure.restrict
              MeasureTheory.volume (UnitCube d)]
        (⇑w.1 : (Fin d → ℝ) → ℝ) := by
    rw [hw_eq_w']
    exact hw'_mem
  -- 4. Path-B refactor: instead of consuming a cluster-point-dependent
  -- `auxOfWeakLimit` triple, derive the limit-side weak-derivative
  -- relation via `Periodic.HasWeakDerivPer.of_weak_limit` from the
  -- sequence-side bare data and the test-function `Tendsto` hypotheses
  -- in `T`. Periodicity of `mLim`, `uLim` is read off `T.hMlimPer`,
  -- `T.hUlimPer` directly. The a.e.-equalities to the cluster-point's
  -- `Lp.coeFn` representative are read off `T.auxAeOfClusterPoint w`
  -- (the residual selector-only obstruction).
  obtain ⟨hAeM, hAeU, hAeDu⟩ := T.auxAeOfClusterPoint w
  -- Derive the limit-side weak-derivative relation per coordinate.
  have hWeakLim :
      ∀ i, Periodic.HasWeakDerivPer (d := d) i T.uLim (T.DuLim i) := by
    intro i
    refine Periodic.HasWeakDerivPer.of_weak_limit
      (i := i) (u_n := fun n => T.seqRepU (φ n))
      (Du_n := fun n => T.seqRepDu (φ n) i)
      (u := T.uLim) (Du := T.DuLim i)
      (T.hDuLim_memLp i) (fun n => T.hSeqRepWeak (φ n) i)
      (T.hConvU φ hmono) ?_
    -- Per-coordinate gradient test-function convergence.
    intro ψ
    exact T.hConvDu φ hmono i ψ
  -- `MemLpPer βBar` of the chosen `m`-limit, by congruence with `⇑w.1`.
  have hMemLp_w1 : Periodic.MemLpPer βBar (⇑w.1 : (Fin d → ℝ) → ℝ) :=
    memLpPer_of_lpPer (d := d) w.1
  have hMlim_memLp : Periodic.MemLpPer βBar T.mLim :=
    Periodic.MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq (μ := MeasureTheory.Measure.restrict
      MeasureTheory.volume (UnitCube d)) hAeM.symm hMemLp_w1.toMemLp)
  -- `MemSobolevPer γBar` of the chosen `u`-limit, built directly from
  -- `MemLpPer γBar T.uLim` (by congruence with `⇑w.2.1`) and the
  -- per-coordinate weak-derivative relation `hWeakLim`.
  have hMemLp_w21 : Periodic.MemLpPer γBar (⇑w.2.1 : (Fin d → ℝ) → ℝ) :=
    memLpPer_of_lpPer (d := d) w.2.1
  have hUlim_memLp : Periodic.MemLpPer γBar T.uLim :=
    Periodic.MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq (μ := MeasureTheory.Measure.restrict
      MeasureTheory.volume (UnitCube d)) hAeU.symm hMemLp_w21.toMemLp)
  have hUlim_sob : Periodic.MemSobolevPer γBar T.uLim :=
    ⟨hUlim_memLp, ⟨T.DuLim, hWeakLim⟩⟩
  -- Non-negativity of `mLim` a.e., from `mLim =ᵐ ⇑w.1` and `0 ≤ᵐ ⇑w.1`.
  have hMlim_nonneg :
      0 ≤ᵐ[MeasureTheory.Measure.restrict
              MeasureTheory.volume (UnitCube d)] T.mLim := by
    filter_upwards [hAeM, hm_nonneg_w] with x hx hxnn
    rw [hx]; exact hxnn
  -- 5. Assemble the existential conclusion.
  refine ⟨φ, w, T.mLim, T.uLim, T.DuLim, hmono, hAeM, hAeU, hAeDu,
          hMlim_memLp, hUlim_sob, T.hMlimPer, T.hUlimPer, ?_, ?_,
          hWeakLim, hMlim_nonneg, ?_⟩
  · exact hMlim_memLp.aestronglyMeasurable
  · exact hUlim_memLp.aestronglyMeasurable
  · -- Convergence statement: rewrite via `hw_eq`.
    rw [hw_eq]
    exact hzlim

/-! ### Sanity-check unit `example` for F.5

Exercise `extractWeakLimit` on a structurally trivial bundle: any
`WeakLimitInputData` produces the F.5 existential conclusion. We do
not aim to construct concrete witnesses for the bundle here — that is
the upstream chain's job — only to verify that the assembly
type-checks. -/

example
    {βBar γBar : ℝ≥0∞} [Fact (1 ≤ βBar)] [Fact (1 ≤ γBar)]
    (T : WeakLimitInputData (d := d) βBar γBar) :
    ∃ (φ : ℕ → ℕ)
      (w : Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)
      (m u : (Fin d → ℝ) → ℝ) (Du : Fin d → (Fin d → ℝ) → ℝ),
      StrictMono φ
        ∧ m =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                  (UnitCube d)] (⇑w.1 : (Fin d → ℝ) → ℝ)
        ∧ u =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                  (UnitCube d)] (⇑w.2.1 : (Fin d → ℝ) → ℝ)
        ∧ (∀ i, Du i
              =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                    (UnitCube d)] (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ))
        ∧ Periodic.MemLpPer βBar m
        ∧ Periodic.MemSobolevPer γBar u
        ∧ Periodic.IsPeriodic m
        ∧ Periodic.IsPeriodic u
        ∧ MeasureTheory.AEStronglyMeasurable m
            (MeasureTheory.Measure.restrict
              MeasureTheory.volume (UnitCube d))
        ∧ MeasureTheory.AEStronglyMeasurable u
            (MeasureTheory.Measure.restrict
              MeasureTheory.volume (UnitCube d))
        ∧ (∀ i, Periodic.HasWeakDerivPer i u (Du i))
        ∧ 0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                  (UnitCube d)] m
        ∧ Filter.Tendsto
            (fun k => (toWeakSpace ℝ
              (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d))
                (T.v_n (φ k)))
            Filter.atTop
            (𝓝 ((toWeakSpace ℝ
              (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)) w)) :=
  extractWeakLimit T

/-! ### Path-A noAux variant of `extractWeakLimit`

The original `WeakLimitInputData` carries a residual cluster-point-
dependent witness `auxAeOfClusterPoint` capturing a.e.-equality
between caller-supplied limits `(mLim, uLim, DuLim)` and an
*arbitrary* candidate `w`. The universal-`w` quantification is
incompatible with constructing the limits from a *specific* `w`,
which is exactly what the `bareCoeFnOfLpPer` primitive (landed in
`StationaryMFG/Periodic/Lp.lean`, iter 0490) lets us do.

`WeakLimitInputData_noAux` drops the caller-supplied limits and the
residual auxiliary witness; the proof of `extractWeakLimit_noAux`
constructs `(mLim, uLim, DuLim)` *internally* from the chosen
cluster point `w` via `bareCoeFnOfLpPer`. The test-function
`Tendsto` hypotheses are reformulated to depend on `w` (chosen-`w`
granularity); the noAux bundle's `hConvU` / `hConvDu` fields range
over `(φ, w)` pairs satisfying the abstract weak-limit relation. -/

/-- **Per-extraction input bundle for `extractWeakLimit_noAux`.**

A "no-aux" variant of `WeakLimitInputData` that constructs the
periodic bare-function limit *internally* from the chosen cluster
point via `bareCoeFnOfLpPer`, so the residual `auxAeOfClusterPoint`
universal-quantifier obstruction is removed.

Compared to `WeakLimitInputData`:

* removes `mLim`, `uLim`, `DuLim`, `hMlimPer`, `hUlimPer`,
  `hDuLim_memLp`, `auxAeOfClusterPoint`;
* adds `hSeqRepU_aeEq`, `hSeqRepDu_aeEq` (a.e.-equality between the
  sequence-side periodic representatives and the bare-function
  coercions of the Banach pair components);
* reformulates `hConvU` / `hConvDu` to depend on the chosen cluster
  point `w` (the integrals on the right-hand side use `⇑w.2.1` and
  `⇑w.2.2 i` directly).

The cluster-point-dependent test-function-convergence statements are
*not* a mere re-encoding of the original `hConvU` / `hConvDu`: the
caller is expected to discharge them only at the genuine
weak-limit cluster point produced by Banach–Alaoglu, by integrating
duality with smooth periodic test functions against the Lp coercion. -/
structure WeakLimitInputData_noAux
    (βBar γBar : ℝ≥0∞) [Fact (1 ≤ βBar)] [Fact (1 ≤ γBar)] (d : ℕ) where
  /-- The bounded sequence of Banach-pair elements. -/
  v_n : ℕ → Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d
  /-- Norm-bound on the sequence. -/
  hBound : Bornology.IsBounded (Set.range v_n)
  /-- Per-`n` non-negativity of the first-component representative. -/
  hMpos : ∀ n,
    0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
      (⇑(v_n n).1 : (Fin d → ℝ) → ℝ)
  /-- Reflexivity of the Banach pair. -/
  hRefl : Periodic.IsReflexiveNormedSpace
    (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)
  /-- Separability of the strong dual (needed by
  `weakSeqCompact_of_bounded_reflexive`). -/
  hSep : TopologicalSpace.SeparableSpace
    (StrongDual ℝ
      (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d))
  /-- Sequence-side periodic representative of the `u`-component. -/
  seqRepU : ℕ → (Fin d → ℝ) → ℝ
  /-- Sequence-side periodic representative of the gradient family. -/
  seqRepDu : ℕ → Fin d → (Fin d → ℝ) → ℝ
  /-- A.e.-equality between the sequence-side `u`-representative and
  the Lp coercion of `(v_n n).2.1`. -/
  hSeqRepU_aeEq : ∀ n,
    seqRepU n
      =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        (⇑(v_n n).2.1 : (Fin d → ℝ) → ℝ)
  /-- Per-coordinate a.e.-equality between the sequence-side gradient
  representative and the Lp coercion of `(v_n n).2.2 i`. -/
  hSeqRepDu_aeEq : ∀ n i,
    seqRepDu n i
      =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        (⇑((v_n n).2.2 i) : (Fin d → ℝ) → ℝ)
  /-- Per-`n`, per-`i` bare-function weak-derivative relation between
  `seqRepU n` and `seqRepDu n i`. -/
  hSeqRepWeak : ∀ n i,
    Periodic.HasWeakDerivPer (d := d) i (seqRepU n) (seqRepDu n i)
  /-- Cluster-point-dependent test-function convergence for the
  `u`-component. For every strict-mono `φ : ℕ → ℕ` and every cluster
  point `w` such that `(toWeakSpace ℝ _) ∘ v_n ∘ φ` tends to
  `(toWeakSpace ℝ _) w`, the integral of `seqRepU (φ k) · ψ` tends to
  the integral of `⇑w.2.1 · ψ`. -/
  hConvU : ∀ (φ : ℕ → ℕ), StrictMono φ →
    ∀ (w : Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d),
    Filter.Tendsto
        (fun k => (toWeakSpace ℝ
          (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d))
            (v_n (φ k)))
        Filter.atTop
        (𝓝 ((toWeakSpace ℝ
          (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)) w)) →
    ∀ ψ : Periodic.SmoothPeriodic d,
      Filter.Tendsto
        (fun k => StationaryMFG.Periodic.periodicIntegral
                    (fun x =>
                      seqRepU (φ k) x *
                        (ψ : (Fin d → ℝ) → ℝ) x))
        Filter.atTop
        (𝓝 (StationaryMFG.Periodic.periodicIntegral
              (fun x =>
                (⇑w.2.1 : (Fin d → ℝ) → ℝ) x *
                  (ψ : (Fin d → ℝ) → ℝ) x)))
  /-- Cluster-point-dependent test-function convergence for the
  gradient component (per coordinate). -/
  hConvDu : ∀ (φ : ℕ → ℕ), StrictMono φ →
    ∀ (w : Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d),
    Filter.Tendsto
        (fun k => (toWeakSpace ℝ
          (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d))
            (v_n (φ k)))
        Filter.atTop
        (𝓝 ((toWeakSpace ℝ
          (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)) w)) →
    ∀ i,
    ∀ ψ : Periodic.SmoothPeriodic d,
      Filter.Tendsto
        (fun k => StationaryMFG.Periodic.periodicIntegral
                    (fun x =>
                      seqRepDu (φ k) i x *
                        (ψ : (Fin d → ℝ) → ℝ) x))
        Filter.atTop
        (𝓝 (StationaryMFG.Periodic.periodicIntegral
              (fun x =>
                (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ) x *
                  (ψ : (Fin d → ℝ) → ℝ) x)))

/-- **F.5 (noAux) — Extract bare-function weak limit.**

Same 14-tuple existential conclusion as `extractWeakLimit`, but
consuming a `WeakLimitInputData_noAux` bundle: the bare-function
periodic limit `(mLim, uLim, DuLim)` is constructed *internally* from
the chosen cluster point `w` via the
`bareCoeFnOfLpPer` primitive, dispensing with the residual
universal-`w` `auxAeOfClusterPoint` field of the original bundle. -/
theorem extractWeakLimit_noAux
    {βBar γBar : ℝ≥0∞} [Fact (1 ≤ βBar)] [Fact (1 ≤ γBar)]
    (T : WeakLimitInputData_noAux (d := d) βBar γBar) :
    ∃ (φ : ℕ → ℕ)
      (w : Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)
      (m u : (Fin d → ℝ) → ℝ) (Du : Fin d → (Fin d → ℝ) → ℝ),
      StrictMono φ
        ∧ m =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                  (UnitCube d)] (⇑w.1 : (Fin d → ℝ) → ℝ)
        ∧ u =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                  (UnitCube d)] (⇑w.2.1 : (Fin d → ℝ) → ℝ)
        ∧ (∀ i, Du i
              =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                    (UnitCube d)] (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ))
        ∧ Periodic.MemLpPer βBar m
        ∧ Periodic.MemSobolevPer γBar u
        ∧ Periodic.IsPeriodic m
        ∧ Periodic.IsPeriodic u
        ∧ MeasureTheory.AEStronglyMeasurable m
            (MeasureTheory.Measure.restrict
              MeasureTheory.volume (UnitCube d))
        ∧ MeasureTheory.AEStronglyMeasurable u
            (MeasureTheory.Measure.restrict
              MeasureTheory.volume (UnitCube d))
        ∧ (∀ i, Periodic.HasWeakDerivPer i u (Du i))
        ∧ 0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                  (UnitCube d)] m
        ∧ Filter.Tendsto
            (fun k => (toWeakSpace ℝ
              (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d))
                (T.v_n (φ k)))
            Filter.atTop
            (𝓝 ((toWeakSpace ℝ
              (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)) w)) := by
  -- 1. Apply abstract weak-cluster-point extraction on the product.
  haveI : TopologicalSpace.SeparableSpace
            (StrongDual ℝ
              (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)) :=
    T.hSep
  set S :
      Set (WeakSpace ℝ
        (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)) :=
    (toWeakSpace ℝ
        (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)) ''
      (nonNegConeProd βBar γBar d) with hS_def
  have hS_closed : IsSeqClosed S := nonNegConeProd_isSeqClosedW βBar γBar d
  have hmem : ∀ n, (toWeakSpace ℝ _) (T.v_n n) ∈ S := by
    intro n
    refine ⟨T.v_n n, ?_, rfl⟩
    change 0 ≤ᵐ[MeasureTheory.Measure.restrict
              MeasureTheory.volume (UnitCube d)]
            (⇑(T.v_n n).1 : (Fin d → ℝ) → ℝ)
    exact T.hMpos n
  obtain ⟨φ, z, hmono, hzS, hzlim⟩ :=
    StationaryMFG.Theorems.SimplePower.exists_weak_cluster_point
      T.hRefl T.v_n T.hBound hS_closed hmem
  -- 2. Convert the cluster point to a concrete pair.
  set w : Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d :=
    (toWeakSpace ℝ
      (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)).symm z
    with hw_def
  have hw_eq :
      (toWeakSpace ℝ
        (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)) w = z := by
    simp [hw_def]
  -- 3. Sign of the first component at the cluster point.
  rcases hzS with ⟨w', hw'_mem, hw'_eq⟩
  have hw_eq_w' : w = w' := by
    have : (toWeakSpace ℝ
      (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)) w
        = (toWeakSpace ℝ
            (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)) w' := by
      rw [hw_eq, hw'_eq]
    exact (toWeakSpace ℝ
      (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)).injective this
  have hm_nonneg_w :
      0 ≤ᵐ[MeasureTheory.Measure.restrict
              MeasureTheory.volume (UnitCube d)]
        (⇑w.1 : (Fin d → ℝ) → ℝ) := by
    rw [hw_eq_w']
    exact hw'_mem
  -- 4. The sequence indexed by `φ` tends to `(toWeakSpace …) w` —
  -- needed both to feed `T.hConvU`/`T.hConvDu` and as the final
  -- conclusion.
  have hφlim :
      Filter.Tendsto
        (fun k => (toWeakSpace ℝ
          (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d))
            (T.v_n (φ k)))
        Filter.atTop
        (𝓝 ((toWeakSpace ℝ
          (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)) w)) := by
    rw [hw_eq]
    exact hzlim
  -- 5. Construct the periodic bare-function limit from `w` via
  -- `bareCoeFnOfLpPer`. `mLim`, `uLim`, `DuLim` are pointwise periodic
  -- and a.e. equal to the Lp coercions on `UnitCube d`.
  set mRep : AEPeriodicRep (⇑w.1 : (Fin d → ℝ) → ℝ) :=
    bareCoeFnOfLpPer (d := d) w.1 with hmRep_def
  set uRep : AEPeriodicRep (⇑w.2.1 : (Fin d → ℝ) → ℝ) :=
    bareCoeFnOfLpPer (d := d) w.2.1 with huRep_def
  let DuRep : ∀ i : Fin d,
      AEPeriodicRep (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ) :=
    fun i => bareCoeFnOfLpPer (d := d) (w.2.2 i)
  set mLim : (Fin d → ℝ) → ℝ := mRep.rep with hmLim_def
  set uLim : (Fin d → ℝ) → ℝ := uRep.rep with huLim_def
  let DuLim : Fin d → (Fin d → ℝ) → ℝ := fun i => (DuRep i).rep
  have hMlimPer : Periodic.IsPeriodic mLim := mRep.periodic
  have hUlimPer : Periodic.IsPeriodic uLim := uRep.periodic
  have hDuLimPer : ∀ i, Periodic.IsPeriodic (DuLim i) :=
    fun i => (DuRep i).periodic
  have hAeM : mLim
      =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        (⇑w.1 : (Fin d → ℝ) → ℝ) := mRep.ae_eq
  have hAeU : uLim
      =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        (⇑w.2.1 : (Fin d → ℝ) → ℝ) := uRep.ae_eq
  have hAeDu : ∀ i, DuLim i
      =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ) := fun i => (DuRep i).ae_eq
  -- 6. `MemLpPer` properties of the constructed limits, from
  -- `MemLpPer βBar ⇑w.1` etc. via `MemLp.ae_eq`.
  have hMemLp_w1 : Periodic.MemLpPer βBar (⇑w.1 : (Fin d → ℝ) → ℝ) :=
    memLpPer_of_lpPer (d := d) w.1
  have hMlim_memLp : Periodic.MemLpPer βBar mLim :=
    Periodic.MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq (μ := MeasureTheory.Measure.restrict
      MeasureTheory.volume (UnitCube d)) hAeM.symm hMemLp_w1.toMemLp)
  have hMemLp_w21 : Periodic.MemLpPer γBar (⇑w.2.1 : (Fin d → ℝ) → ℝ) :=
    memLpPer_of_lpPer (d := d) w.2.1
  have hUlim_memLp : Periodic.MemLpPer γBar uLim :=
    Periodic.MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq (μ := MeasureTheory.Measure.restrict
      MeasureTheory.volume (UnitCube d)) hAeU.symm hMemLp_w21.toMemLp)
  -- For the gradient: `MemLpPer 1 (DuLim i)`. We get it from
  -- `MemLpPer γBar ⇑(w.2.2 i)`, transfer along a.e.-equality to
  -- `MemLpPer γBar (DuLim i)`, and drop to `p = 1` via finite measure.
  have hDuLim_memLp : ∀ i, Periodic.MemLpPer 1 (DuLim i) := by
    intro i
    -- `MemLpPer γBar ⇑(w.2.2 i)` (from `memLpPer_of_lpPer`), then
    -- transfer to `DuLim i` via a.e.-equality, then drop to `p = 1`.
    have h1 : Periodic.MemLpPer γBar (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ) :=
      memLpPer_of_lpPer (d := d) (w.2.2 i)
    have h2 : Periodic.MemLpPer γBar (DuLim i) :=
      Periodic.MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq (μ := MeasureTheory.Measure.restrict
        MeasureTheory.volume (UnitCube d)) (hAeDu i).symm h1.toMemLp)
    -- Drop `γBar ≥ 1` to `p = 1`.
    haveI : MeasureTheory.IsFiniteMeasure
        (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
      ⟨by
        rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ]
        simp⟩
    exact Periodic.MemLp.toMemLpPer
      (MeasureTheory.MemLp.mono_exponent (Periodic.MemLpPer.toMemLp h2)
        (Fact.out : (1 : ℝ≥0∞) ≤ γBar))
  -- 7. Test-function convergence at the chosen `w` (cluster-point-
  -- dependent fields of the noAux bundle).
  have hConvU_w :
      ∀ ψ : Periodic.SmoothPeriodic d,
        Filter.Tendsto
          (fun k => StationaryMFG.Periodic.periodicIntegral
                      (fun x =>
                        T.seqRepU (φ k) x *
                          (ψ : (Fin d → ℝ) → ℝ) x))
          Filter.atTop
          (𝓝 (StationaryMFG.Periodic.periodicIntegral
                (fun x =>
                  (⇑w.2.1 : (Fin d → ℝ) → ℝ) x *
                    (ψ : (Fin d → ℝ) → ℝ) x))) :=
    fun ψ => T.hConvU φ hmono w hφlim ψ
  have hConvDu_w :
      ∀ i, ∀ ψ : Periodic.SmoothPeriodic d,
        Filter.Tendsto
          (fun k => StationaryMFG.Periodic.periodicIntegral
                      (fun x =>
                        T.seqRepDu (φ k) i x *
                          (ψ : (Fin d → ℝ) → ℝ) x))
          Filter.atTop
          (𝓝 (StationaryMFG.Periodic.periodicIntegral
                (fun x =>
                  (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ) x *
                    (ψ : (Fin d → ℝ) → ℝ) x))) :=
    fun i ψ => T.hConvDu φ hmono w hφlim i ψ
  -- 8. Tendsto-transfer along a.e.-equality on the unit cube. The
  -- targets of `hConvU_w` / `hConvDu_w` use `⇑w.2.1` / `⇑(w.2.2 i)` on
  -- the right-hand side; rewrite them to `uLim` / `DuLim i` using
  -- `integral_congr_ae` + `hAeU.symm` / `(hAeDu i).symm`.
  -- Per-`ψ` integral-rewrite lemma: `∫ uLim · ψ = ∫ ⇑w.2.1 · ψ`.
  have hIntU :
      ∀ ψ : Periodic.SmoothPeriodic d,
        StationaryMFG.Periodic.periodicIntegral
            (fun x => uLim x * (ψ : (Fin d → ℝ) → ℝ) x) =
          StationaryMFG.Periodic.periodicIntegral
            (fun x =>
              (⇑w.2.1 : (Fin d → ℝ) → ℝ) x *
                (ψ : (Fin d → ℝ) → ℝ) x) := by
    intro ψ
    unfold StationaryMFG.Periodic.periodicIntegral
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hAeU] with x hx
    rw [hx]
  have hIntDu :
      ∀ i, ∀ ψ : Periodic.SmoothPeriodic d,
        StationaryMFG.Periodic.periodicIntegral
            (fun x => DuLim i x * (ψ : (Fin d → ℝ) → ℝ) x) =
          StationaryMFG.Periodic.periodicIntegral
            (fun x =>
              (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ) x *
                (ψ : (Fin d → ℝ) → ℝ) x) := by
    intro i ψ
    unfold StationaryMFG.Periodic.periodicIntegral
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hAeDu i] with x hx
    rw [hx]
  -- Tendsto with the rewritten targets — now matching `seqRepU` /
  -- `seqRepDu` (sequence-side periodic representatives) against
  -- `uLim` / `DuLim i` directly.
  have hConvU_seq :
      ∀ ψ : Periodic.SmoothPeriodic d,
        Filter.Tendsto
          (fun k => StationaryMFG.Periodic.periodicIntegral
                      (fun x =>
                        T.seqRepU (φ k) x *
                          (ψ : (Fin d → ℝ) → ℝ) x))
          Filter.atTop
          (𝓝 (StationaryMFG.Periodic.periodicIntegral
                (fun x => uLim x * (ψ : (Fin d → ℝ) → ℝ) x))) := by
    intro ψ
    rw [hIntU ψ]
    exact hConvU_w ψ
  have hConvDu_seq :
      ∀ i, ∀ ψ : Periodic.SmoothPeriodic d,
        Filter.Tendsto
          (fun k => StationaryMFG.Periodic.periodicIntegral
                      (fun x =>
                        T.seqRepDu (φ k) i x *
                          (ψ : (Fin d → ℝ) → ℝ) x))
          Filter.atTop
          (𝓝 (StationaryMFG.Periodic.periodicIntegral
                (fun x => DuLim i x * (ψ : (Fin d → ℝ) → ℝ) x))) := by
    intro i ψ
    rw [hIntDu i ψ]
    exact hConvDu_w i ψ
  -- 9. Limit-side weak-derivative relation per coordinate.
  have hWeakLim :
      ∀ i, Periodic.HasWeakDerivPer (d := d) i uLim (DuLim i) := by
    intro i
    refine Periodic.HasWeakDerivPer.of_weak_limit
      (i := i) (u_n := fun n => T.seqRepU (φ n))
      (Du_n := fun n => T.seqRepDu (φ n) i)
      (u := uLim) (Du := DuLim i)
      (hDuLim_memLp i) (fun n => T.hSeqRepWeak (φ n) i)
      (hConvU_seq) ?_
    intro ψ
    exact hConvDu_seq i ψ
  have hUlim_sob : Periodic.MemSobolevPer γBar uLim :=
    ⟨hUlim_memLp, ⟨DuLim, hWeakLim⟩⟩
  -- Non-negativity of `mLim` a.e. from `mLim =ᵐ ⇑w.1` and `0 ≤ᵐ ⇑w.1`.
  have hMlim_nonneg :
      0 ≤ᵐ[MeasureTheory.Measure.restrict
              MeasureTheory.volume (UnitCube d)] mLim := by
    filter_upwards [hAeM, hm_nonneg_w] with x hx hxnn
    rw [hx]; exact hxnn
  -- 10. Assemble the existential conclusion.
  refine ⟨φ, w, mLim, uLim, DuLim, hmono, hAeM, hAeU, hAeDu,
          hMlim_memLp, hUlim_sob, hMlimPer, hUlimPer, ?_, ?_,
          hWeakLim, hMlim_nonneg, hφlim⟩
  · exact hMlim_memLp.aestronglyMeasurable
  · exact hUlim_memLp.aestronglyMeasurable

/-! ### Sanity-check unit `example` for F.5 (noAux) -/

example
    {βBar γBar : ℝ≥0∞} [Fact (1 ≤ βBar)] [Fact (1 ≤ γBar)]
    (T : WeakLimitInputData_noAux (d := d) βBar γBar) :
    ∃ (φ : ℕ → ℕ)
      (w : Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)
      (m u : (Fin d → ℝ) → ℝ) (Du : Fin d → (Fin d → ℝ) → ℝ),
      StrictMono φ
        ∧ m =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                  (UnitCube d)] (⇑w.1 : (Fin d → ℝ) → ℝ)
        ∧ u =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                  (UnitCube d)] (⇑w.2.1 : (Fin d → ℝ) → ℝ)
        ∧ (∀ i, Du i
              =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                    (UnitCube d)] (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ))
        ∧ Periodic.MemLpPer βBar m
        ∧ Periodic.MemSobolevPer γBar u
        ∧ Periodic.IsPeriodic m
        ∧ Periodic.IsPeriodic u
        ∧ MeasureTheory.AEStronglyMeasurable m
            (MeasureTheory.Measure.restrict
              MeasureTheory.volume (UnitCube d))
        ∧ MeasureTheory.AEStronglyMeasurable u
            (MeasureTheory.Measure.restrict
              MeasureTheory.volume (UnitCube d))
        ∧ (∀ i, Periodic.HasWeakDerivPer i u (Du i))
        ∧ 0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                  (UnitCube d)] m
        ∧ Filter.Tendsto
            (fun k => (toWeakSpace ℝ
              (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d))
                (T.v_n (φ k)))
            Filter.atTop
            (𝓝 ((toWeakSpace ℝ
              (Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)) w)) :=
  extractWeakLimit_noAux T

/-! ## F.6 — Limit passage to function-form weak VI

Apply E.1 + E.2 + E.3 + E.4 plus the abstract real-numerical kernel
`limit_passage_real` (in `SimplePower/Main.lean`, repackaged as
`limit_passage_weak_VI_of_eps`) to pass the regularised operator
pairing
```
0 ≤ mfgOperatorEpsPair γ̄ (ε k) Dυ μ υ (Dυ - Du_n k) (μ - m_n k) (υ - u_n k)
```
applied at the F.5 sequence to the limit, producing the **weak VI**
at the limit triple `(m, u, Du)`:
```
0 ≤ mfgOperatorPair Dυ μ υ (Dυ - Du) (μ - m) (υ - u).
```

The substantive content is the **assembly**: split the unregularised
pairing pointwise into three summands, apply E.1 (resp. E.2 per
coordinate, E.3) to each, sum the convergence statements, and feed
the resulting `Tendsto` into the abstract real-numerical kernel via
`limit_passage_weak_VI_of_eps`.

Per CONVENTIONS §1b/§8 we package the per-summand `WeakConvPairing`
certificates and the multiplier `MemLpPer` certificates as authorised
auxiliary hypotheses in the input bundle: deriving them from the F.5
product weak convergence requires component projections through the
CLM `ContinuousLinearMap.fst`/`.snd` — a routine but bulky transfer
that we punt to the upstream consumer chain. -/


open scoped Hamiltonian

/-- **Per-test input bundle for the limit-passage assembly (F.6).**

Carries the F.4-shaped sequential strong-VI data and the F.5-shaped
weak-limit data, plus the per-summand `WeakConvPairing` certificates
and multiplier `MemLpPer` certificates required by E.1/E.2/E.3, plus
the regularization-vanishing data required by E.4.

Fields:
* `ε`, `m_n`, `u_n`, `Du_n`, `m`, `u`, `Du` — the regularization
  sequence and the F.5 weak-limit triple (sequence + limit).
* `hε_nonneg`, `hε_to0` — `0 ≤ ε k`, `ε k → 0`.
* `hm_n_memLp`, `hm_memLp` — `m_n k`, `m` ∈ `L^{β̄}_per`.
* `hu_n_memLp`, `hu_memLp`, `hυ_memLp` — `u_n k`, `u`, `υ` ∈ `L^{γ̄}_per`.
* `hDu_n_memLp i`, `hDu_memLp i`, `hDυ_memLp i` — `Du_n k i`, `Du i`,
  `Dυ i` ∈ `L^{γ̄}_per`.
* `hμ_memLp` — `μ ∈ L^{β̄}_per`.
* `hg_memLp` — multiplier `g(x) := -υ(x) - H(x, Dυ, μ) + V(x)` ∈
  `L^{β̄'}_per`.
* `hflux_memLp i` — flux `flux_i(x) := μ(x) · D_pH(x, Dυ, μ) i` ∈
  `L^{γ̄'}_per` (per-coordinate).
* `hμMinusOne_memLp` — `(μ - 1) ∈ L^{γ̄'}_per` (re-branded from
  `L^{β̄}` via finite-measure inclusion at the consumer site).
* `h_weak_m`, `h_weak_u`, `h_weak_Du i` — per-summand weak-pairing
  certificates from the F.5 product weak convergence, supplied as
  authorised auxiliary hypotheses.
* `hVI_eps` — the regularised strong-VI inequality at each `k`.
* `hreg_bdd` — uniform Gateaux-residual bound. -/
structure LimitPassageInputData
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (βBar βBar' γBar γBar' : ℝ)
    (μ υ : (Fin d → ℝ) → ℝ)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ) where
  /-- Hölder-conjugate pair `(β̄, β̄')`, `1/β̄ + 1/β̄' = 1`. -/
  hpqβ : βBar.HolderConjugate βBar'
  /-- Hölder-conjugate pair `(γ̄, γ̄')`, `1/γ̄ + 1/γ̄' = 1`. -/
  hpqγ : γBar.HolderConjugate γBar'
  /-- Regularization sequence `ε : ℕ → ℝ`. -/
  ε : ℕ → ℝ
  /-- Per-`k` density `m_n`. -/
  m_n : ℕ → (Fin d → ℝ) → ℝ
  /-- Per-`k` value function `u_n`. -/
  u_n : ℕ → (Fin d → ℝ) → ℝ
  /-- Per-`k` weak-derivative family `Du_n`. -/
  Du_n : ℕ → Fin d → (Fin d → ℝ) → ℝ
  /-- Limit density `m`. -/
  m : (Fin d → ℝ) → ℝ
  /-- Limit value function `u`. -/
  u : (Fin d → ℝ) → ℝ
  /-- Limit weak-derivative family `Du`. -/
  Du : Fin d → (Fin d → ℝ) → ℝ
  /-- `0 ≤ ε k`. -/
  hε_nonneg : ∀ k, 0 ≤ ε k
  /-- `ε k → 0`. -/
  hε_to0 : Filter.Tendsto ε Filter.atTop (𝓝 0)
  /-- `m_n k ∈ L^{β̄}_per` for every `k`. -/
  hm_n_memLp : ∀ k, Periodic.MemLpPer (ENNReal.ofReal βBar) (m_n k)
  /-- `m ∈ L^{β̄}_per`. -/
  hm_memLp : Periodic.MemLpPer (ENNReal.ofReal βBar) m
  /-- `u_n k ∈ L^{γ̄}_per` for every `k`. -/
  hu_n_memLp : ∀ k, Periodic.MemLpPer (ENNReal.ofReal γBar) (u_n k)
  /-- `u ∈ L^{γ̄}_per`. -/
  hu_memLp : Periodic.MemLpPer (ENNReal.ofReal γBar) u
  /-- `υ ∈ L^{γ̄}_per`. -/
  hυ_memLp : Periodic.MemLpPer (ENNReal.ofReal γBar) υ
  /-- `Du_n k i ∈ L^{γ̄}_per` for every `k`, `i`. -/
  hDu_n_memLp : ∀ k i, Periodic.MemLpPer (ENNReal.ofReal γBar) (Du_n k i)
  /-- `Du i ∈ L^{γ̄}_per` for every `i`. -/
  hDu_memLp : ∀ i, Periodic.MemLpPer (ENNReal.ofReal γBar) (Du i)
  /-- `Dυ i ∈ L^{γ̄}_per` for every `i`. -/
  hDυ_memLp : ∀ i, Periodic.MemLpPer (ENNReal.ofReal γBar) (Dυ i)
  /-- `μ ∈ L^{β̄}_per`. -/
  hμ_memLp : Periodic.MemLpPer (ENNReal.ofReal βBar) μ
  /-- Multiplier `g(x) := -υ(x) - H(x, Dυ, μ) + V(x)` is in
  `L^{β̄'}_per`. -/
  hg_memLp : Periodic.MemLpPer (ENNReal.ofReal βBar')
              (fun x => -(υ x) - H x (fun i => Dυ i x) (μ x) + V x)
  /-- Per-coordinate flux `flux_i(x) := μ(x) · D_pH(x, Dυ, μ) i` is in
  `L^{γ̄'}_per`. -/
  hflux_memLp : ∀ i, Periodic.MemLpPer (ENNReal.ofReal γBar')
                      (fun x => μ x * DpH x (fun j => Dυ j x) (μ x) i)
  /-- Mass-defect multiplier `(μ - 1) ∈ L^{γ̄'}_per` (re-branded from
  `L^{β̄}` via the finite-measure inclusion at the consumer site). -/
  hμMinusOne_memLp : Periodic.MemLpPer (ENNReal.ofReal γBar')
                      (fun x => μ x - 1)
  /-- Weak-pairing certificate: `m_n ⇀ m` against `L^{β̄'}_per` tests. -/
  h_weak_m : WeakConvPairing_universal (d := d) hpqβ m_n m
  /-- Weak-pairing certificate: `u_n ⇀ u` against `L^{γ̄'}_per` tests. -/
  h_weak_u : WeakConvPairing_universal (d := d) hpqγ u_n u
  /-- Weak-pairing certificate per coordinate: `Du_n · i ⇀ Du i`
  against `L^{γ̄'}_per` tests. -/
  h_weak_Du : ∀ i,
    WeakConvPairing_universal (d := d) hpqγ (fun k => Du_n k i) (Du i)
  /-- Per-`k` regularised strong-VI inequality (input from F.4 chained
  through `paper:thm:strongAepsi`). -/
  hVI_eps : ∀ k,
    0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBar (ε k) Dυ μ υ
          (fun i x => Dυ i x - Du_n k i x) (μ - m_n k) (υ - u_n k)
  /-- Uniform bound on the Gateaux residual. -/
  M : ℝ
  /-- The Gateaux residual is bounded by `M`. -/
  hreg_bdd : ∀ k,
    |gateauxWpPair γBar Dυ υ
        (fun i x => Dυ i x - Du_n k i x) (υ - u_n k)| ≤ M

namespace LimitPassageInputData

variable
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {βBar βBar' γBar γBar' : ℝ}
    {μ υ : (Fin d → ℝ) → ℝ}
    {Dυ : Fin d → (Fin d → ℝ) → ℝ}

/-- **Convergence of the first summand** (E.1 application).

For the multiplier `g := -υ - H(·, Dυ, μ) + V ∈ L^{β̄'}_per` and the
sequence `m_n ⇀ m` in `L^{β̄}_per`,
```
∫ g(x) · (μ(x) - m_n k x) dx → ∫ g(x) · (μ(x) - m(x)) dx.
```
This is a direct application of `limit_passage_summand1`. -/
theorem tendsto_summand1
    (T : LimitPassageInputData (d := d) V H DpH βBar βBar' γBar γBar' μ υ Dυ) :
    Filter.Tendsto
      (fun k => ∫ x in UnitCube d,
        (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (μ x - T.m_n k x))
      Filter.atTop
      (𝓝 (∫ x in UnitCube d,
        (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (μ x - T.m x))) :=
  limit_passage_summand1 T.hpqβ T.hm_n_memLp T.hm_memLp T.hμ_memLp
    T.hg_memLp T.h_weak_m

/-- **Convergence of the third summand** (E.3 application).

For the multiplier `(μ - 1) ∈ L^{γ̄'}_per` and the sequence
`u_n ⇀ u` in `L^{γ̄}_per`,
```
∫ (μ(x) - 1) · (υ(x) - u_n k x) dx → ∫ (μ(x) - 1) · (υ(x) - u(x)) dx.
```
This is a direct application of `limit_passage_summand3`. -/
theorem tendsto_summand3
    (T : LimitPassageInputData (d := d) V H DpH βBar βBar' γBar γBar' μ υ Dυ) :
    Filter.Tendsto
      (fun k => ∫ x in UnitCube d,
        (μ x - 1) * (υ x - T.u_n k x))
      Filter.atTop
      (𝓝 (∫ x in UnitCube d,
        (μ x - 1) * (υ x - T.u x))) :=
  limit_passage_summand3 T.hpqγ T.hu_n_memLp T.hu_memLp T.hυ_memLp
    T.hμMinusOne_memLp T.h_weak_u

/-- **Convergence of the middle summand, per coordinate** (E.2
application).

For each coordinate `i`, the multiplier
`flux_i := μ · D_pH(·, Dυ, μ) i ∈ L^{γ̄'}_per` and the sequence
`Du_n · i ⇀ Du i` in `L^{γ̄}_per` give
```
∫ flux_i(x) · (Dυ_i(x) - Du_n k i x) dx
   → ∫ flux_i(x) · (Dυ_i(x) - Du i x) dx.
```
Direct application of `limit_passage_summand2`. -/
theorem tendsto_summand2_coord
    (T : LimitPassageInputData (d := d) V H DpH βBar βBar' γBar γBar' μ υ Dυ)
    (i : Fin d) :
    Filter.Tendsto
      (fun k => ∫ x in UnitCube d,
        (μ x * DpH x (fun j => Dυ j x) (μ x) i)
          * (Dυ i x - T.Du_n k i x))
      Filter.atTop
      (𝓝 (∫ x in UnitCube d,
        (μ x * DpH x (fun j => Dυ j x) (μ x) i)
          * (Dυ i x - T.Du i x))) :=
  limit_passage_summand2 T.hpqγ
    (fun k => T.hDu_n_memLp k i) (T.hDu_memLp i) (T.hDυ_memLp i)
    (T.hflux_memLp i) (T.h_weak_Du i)

/-! ### AC5 — Assemble `hpair_conv` from the three summand pairings

Producer that takes a `LimitPassageInputData` bundle and constructs
the assembled `mfgOperatorPair` convergence (the `hpair_conv` shape
required by F.6's `limitPassage_to_weakVI`).

The proof:
1. Rewrites both sides via `mfgOperatorPair_split` (the algebraic
   integral split in `Solutions/MFGOperator.lean`), feeding it the
   three per-summand integrability witnesses derived from the
   `MemLpPer` / Hölder-conjugacy data in the bundle.
2. Pushes the integral over the dot-product `D_pH ⬝ (Dυ - Dν)`
   inside the finite sum via `integral_finset_sum`, so summand 2
   matches the per-coordinate `tendsto_summand2_coord` shape.
3. Combines per-coordinate convergence via `tendsto_finset_sum`,
   then assembles the three summand limits via `Tendsto.add`. -/

/-- Per-summand-1 integrability of `(-υ - H + V) · (μ - m_n k)` at
the per-`k` running difference, derived from the bundle's
`MemLpPer` certificates via the Hölder pair `(βBar', βBar)`. -/
private lemma integrable_summand1_step
    (T : LimitPassageInputData (d := d) V H DpH βBar βBar' γBar γBar' μ υ Dυ)
    (k : ℕ) :
    Integrable
      (fun x => (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x)
                 * (μ x - T.m_n k x))
      (volume.restrict (UnitCube d)) := by
  -- `(μ - m_n k) ∈ L^{βBar}_per` via `MemLp.sub`.
  have hμmn : Periodic.MemLpPer (ENNReal.ofReal βBar) (μ - T.m_n k) :=
    Periodic.MemLp.toMemLpPer (MeasureTheory.MemLp.sub T.hμ_memLp.toMemLp (T.hm_n_memLp k).toMemLp)
  -- Rewrite pointwise `(μ - m_n k) x = μ x - m_n k x`.
  have hμmn' :
      Periodic.MemLpPer (ENNReal.ofReal βBar)
        (fun x => μ x - T.m_n k x) := hμmn
  -- Hölder pair `(βBar', βBar)` integrability.
  have hpq' : βBar'.HolderConjugate βBar := T.hpqβ.symm
  exact Periodic.MemLpPer.integrable_mul hpq' T.hg_memLp hμmn'

/-- Per-summand-1 integrability at the limit, mirror of the step
case. -/
private lemma integrable_summand1_lim
    (T : LimitPassageInputData (d := d) V H DpH βBar βBar' γBar γBar' μ υ Dυ) :
    Integrable
      (fun x => (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x)
                 * (μ x - T.m x))
      (volume.restrict (UnitCube d)) := by
  have hμm : Periodic.MemLpPer (ENNReal.ofReal βBar) (μ - T.m) :=
    Periodic.MemLp.toMemLpPer (MeasureTheory.MemLp.sub T.hμ_memLp.toMemLp T.hm_memLp.toMemLp)
  have hμm' :
      Periodic.MemLpPer (ENNReal.ofReal βBar)
        (fun x => μ x - T.m x) := hμm
  have hpq' : βBar'.HolderConjugate βBar := T.hpqβ.symm
  exact Periodic.MemLpPer.integrable_mul hpq' T.hg_memLp hμm'

/-- Per-coord, per-`k` integrability of
`flux_i · (Dυ_i - Du_n k i)` for summand 2 (per coord). -/
private lemma integrable_summand2_coord_step
    (T : LimitPassageInputData (d := d) V H DpH βBar βBar' γBar γBar' μ υ Dυ)
    (k : ℕ) (i : Fin d) :
    Integrable
      (fun x => (μ x * DpH x (fun j => Dυ j x) (μ x) i)
                  * (Dυ i x - T.Du_n k i x))
      (volume.restrict (UnitCube d)) := by
  have hDνmem : Periodic.MemLpPer (ENNReal.ofReal γBar)
      (Dυ i - T.Du_n k i) :=
    Periodic.MemLp.toMemLpPer (MeasureTheory.MemLp.sub (T.hDυ_memLp i).toMemLp (T.hDu_n_memLp k i).toMemLp)
  have hDνmem' : Periodic.MemLpPer (ENNReal.ofReal γBar)
      (fun x => Dυ i x - T.Du_n k i x) := hDνmem
  have hpq' : γBar'.HolderConjugate γBar := T.hpqγ.symm
  exact Periodic.MemLpPer.integrable_mul hpq' (T.hflux_memLp i) hDνmem'

/-- Per-coord integrability of `flux_i · (Dυ_i - Du i)` at the limit. -/
private lemma integrable_summand2_coord_lim
    (T : LimitPassageInputData (d := d) V H DpH βBar βBar' γBar γBar' μ υ Dυ)
    (i : Fin d) :
    Integrable
      (fun x => (μ x * DpH x (fun j => Dυ j x) (μ x) i)
                  * (Dυ i x - T.Du i x))
      (volume.restrict (UnitCube d)) := by
  have hDνmem : Periodic.MemLpPer (ENNReal.ofReal γBar)
      (Dυ i - T.Du i) :=
    Periodic.MemLp.toMemLpPer (MeasureTheory.MemLp.sub (T.hDυ_memLp i).toMemLp (T.hDu_memLp i).toMemLp)
  have hDνmem' : Periodic.MemLpPer (ENNReal.ofReal γBar)
      (fun x => Dυ i x - T.Du i x) := hDνmem
  have hpq' : γBar'.HolderConjugate γBar := T.hpqγ.symm
  exact Periodic.MemLpPer.integrable_mul hpq' (T.hflux_memLp i) hDνmem'

/-- Per-`k` integrability of the summand-2 lump-sum integrand
`μ · (D_pH ⬝ (Dυ - Du_n k))`. The dot product unfolds to a finite
sum of the per-coord integrands; integrability of a finite sum
follows from per-coord integrability. -/
private lemma integrable_summand2_step
    (T : LimitPassageInputData (d := d) V H DpH βBar βBar' γBar γBar' μ υ Dυ)
    (k : ℕ) :
    Integrable
      (fun x => μ x * (DpH x (fun j => Dυ j x) (μ x)
                         ⬝ (fun i => Dυ i x - T.Du_n k i x)))
      (volume.restrict (UnitCube d)) := by
  -- Pointwise rewrite of the dot product as a finite sum, with
  -- `μ` distributed.
  have hpt :
      (fun x => μ x * (DpH x (fun j => Dυ j x) (μ x)
                         ⬝ (fun i => Dυ i x - T.Du_n k i x)))
        = (fun x => ∑ i : Fin d,
            (μ x * DpH x (fun j => Dυ j x) (μ x) i)
              * (Dυ i x - T.Du_n k i x)) := by
    funext x
    -- `⬝` unfolds to `∑ i, _`.
    unfold dotProduct
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  rw [hpt]
  exact MeasureTheory.integrable_finset_sum _
    (fun i _ => T.integrable_summand2_coord_step k i)

/-- Limit-time integrability of the summand-2 lump-sum integrand. -/
private lemma integrable_summand2_lim
    (T : LimitPassageInputData (d := d) V H DpH βBar βBar' γBar γBar' μ υ Dυ) :
    Integrable
      (fun x => μ x * (DpH x (fun j => Dυ j x) (μ x)
                         ⬝ (fun i => Dυ i x - T.Du i x)))
      (volume.restrict (UnitCube d)) := by
  have hpt :
      (fun x => μ x * (DpH x (fun j => Dυ j x) (μ x)
                         ⬝ (fun i => Dυ i x - T.Du i x)))
        = (fun x => ∑ i : Fin d,
            (μ x * DpH x (fun j => Dυ j x) (μ x) i)
              * (Dυ i x - T.Du i x)) := by
    funext x
    unfold dotProduct
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  rw [hpt]
  exact MeasureTheory.integrable_finset_sum _
    (fun i _ => T.integrable_summand2_coord_lim i)

/-- Per-`k` integrability of the summand-3 integrand `(μ - 1) · (υ - u_n k)`. -/
private lemma integrable_summand3_step
    (T : LimitPassageInputData (d := d) V H DpH βBar βBar' γBar γBar' μ υ Dυ)
    (k : ℕ) :
    Integrable (fun x => (μ x - 1) * (υ x - T.u_n k x))
      (volume.restrict (UnitCube d)) := by
  have hυu : Periodic.MemLpPer (ENNReal.ofReal γBar) (υ - T.u_n k) :=
    Periodic.MemLp.toMemLpPer (MeasureTheory.MemLp.sub T.hυ_memLp.toMemLp (T.hu_n_memLp k).toMemLp)
  have hυu' :
      Periodic.MemLpPer (ENNReal.ofReal γBar)
        (fun x => υ x - T.u_n k x) := hυu
  -- `μ - 1` already in `L^{γBar'}_per` from the bundle.
  have hμ1' :
      Periodic.MemLpPer (ENNReal.ofReal γBar')
        (fun x => μ x - 1) := T.hμMinusOne_memLp
  have hpq : γBar'.HolderConjugate γBar := T.hpqγ.symm
  exact Periodic.MemLpPer.integrable_mul hpq hμ1' hυu'

/-- Limit-time integrability of summand 3. -/
private lemma integrable_summand3_lim
    (T : LimitPassageInputData (d := d) V H DpH βBar βBar' γBar γBar' μ υ Dυ) :
    Integrable (fun x => (μ x - 1) * (υ x - T.u x))
      (volume.restrict (UnitCube d)) := by
  have hυu : Periodic.MemLpPer (ENNReal.ofReal γBar) (υ - T.u) :=
    Periodic.MemLp.toMemLpPer (MeasureTheory.MemLp.sub T.hυ_memLp.toMemLp T.hu_memLp.toMemLp)
  have hυu' :
      Periodic.MemLpPer (ENNReal.ofReal γBar)
        (fun x => υ x - T.u x) := hυu
  have hμ1' :
      Periodic.MemLpPer (ENNReal.ofReal γBar')
        (fun x => μ x - 1) := T.hμMinusOne_memLp
  have hpq : γBar'.HolderConjugate γBar := T.hpqγ.symm
  exact Periodic.MemLpPer.integrable_mul hpq hμ1' hυu'

/-- **Convergence of the middle summand, in lump-sum form** (sum of
`tendsto_summand2_coord` over `Fin d`).

The per-coordinate convergences from `tendsto_summand2_coord` are
summed via `tendsto_finset_sum`, then the result is folded back
into the lump-sum integrand `μ · (D_pH ⬝ (Dυ - Du_n))` via
`integral_finset_sum`. -/
theorem tendsto_summand2_summed
    (T : LimitPassageInputData (d := d) V H DpH βBar βBar' γBar γBar' μ υ Dυ) :
    Filter.Tendsto
      (fun k => ∫ x in UnitCube d,
        μ x * (DpH x (fun j => Dυ j x) (μ x)
                 ⬝ (fun i => Dυ i x - T.Du_n k i x)))
      Filter.atTop
      (𝓝 (∫ x in UnitCube d,
        μ x * (DpH x (fun j => Dυ j x) (μ x)
                 ⬝ (fun i => Dυ i x - T.Du i x)))) := by
  -- Per-coordinate convergence (E.2).
  have hcoord : ∀ i : Fin d,
      Filter.Tendsto
        (fun k => ∫ x in UnitCube d,
          (μ x * DpH x (fun j => Dυ j x) (μ x) i)
            * (Dυ i x - T.Du_n k i x))
        Filter.atTop
        (𝓝 (∫ x in UnitCube d,
          (μ x * DpH x (fun j => Dυ j x) (μ x) i)
            * (Dυ i x - T.Du i x))) := T.tendsto_summand2_coord
  -- Sum over coordinates via `tendsto_finset_sum`.
  have hsum :
      Filter.Tendsto
        (fun k => ∑ i : Fin d, ∫ x in UnitCube d,
          (μ x * DpH x (fun j => Dυ j x) (μ x) i)
            * (Dυ i x - T.Du_n k i x))
        Filter.atTop
        (𝓝 (∑ i : Fin d, ∫ x in UnitCube d,
          (μ x * DpH x (fun j => Dυ j x) (μ x) i)
            * (Dυ i x - T.Du i x))) :=
    tendsto_finset_sum _ (fun i _ => hcoord i)
  -- Identify the per-`k` and limit integrals with the lump-sum form
  -- via `integral_finset_sum`.
  have hpt_n : ∀ k : ℕ, ∀ x : Fin d → ℝ,
      μ x * (DpH x (fun j => Dυ j x) (μ x)
               ⬝ (fun i => Dυ i x - T.Du_n k i x))
        = ∑ i : Fin d, (μ x * DpH x (fun j => Dυ j x) (μ x) i)
                           * (Dυ i x - T.Du_n k i x) := by
    intro k x
    unfold dotProduct
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  have hpt_lim : ∀ x : Fin d → ℝ,
      μ x * (DpH x (fun j => Dυ j x) (μ x)
               ⬝ (fun i => Dυ i x - T.Du i x))
        = ∑ i : Fin d, (μ x * DpH x (fun j => Dυ j x) (μ x) i)
                           * (Dυ i x - T.Du i x) := by
    intro x
    unfold dotProduct
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  -- For each `k`, the per-`k` lump-sum integral equals the sum of
  -- per-coord integrals.
  have hint_n : ∀ k : ℕ,
      ∫ x in UnitCube d,
        μ x * (DpH x (fun j => Dυ j x) (μ x)
                 ⬝ (fun i => Dυ i x - T.Du_n k i x))
        = ∑ i : Fin d, ∫ x in UnitCube d,
            (μ x * DpH x (fun j => Dυ j x) (μ x) i)
              * (Dυ i x - T.Du_n k i x) := by
    intro k
    have h1 :
        (fun x => μ x * (DpH x (fun j => Dυ j x) (μ x)
                           ⬝ (fun i => Dυ i x - T.Du_n k i x)))
          = (fun x => ∑ i : Fin d,
              (μ x * DpH x (fun j => Dυ j x) (μ x) i)
                * (Dυ i x - T.Du_n k i x)) := by
      funext x; exact hpt_n k x
    rw [h1, MeasureTheory.integral_finset_sum]
    intro i _
    exact T.integrable_summand2_coord_step k i
  have hint_lim :
      ∫ x in UnitCube d,
        μ x * (DpH x (fun j => Dυ j x) (μ x)
                 ⬝ (fun i => Dυ i x - T.Du i x))
        = ∑ i : Fin d, ∫ x in UnitCube d,
            (μ x * DpH x (fun j => Dυ j x) (μ x) i)
              * (Dυ i x - T.Du i x) := by
    have h1 :
        (fun x => μ x * (DpH x (fun j => Dυ j x) (μ x)
                           ⬝ (fun i => Dυ i x - T.Du i x)))
          = (fun x => ∑ i : Fin d,
              (μ x * DpH x (fun j => Dυ j x) (μ x) i)
                * (Dυ i x - T.Du i x)) := by
      funext x; exact hpt_lim x
    rw [h1, MeasureTheory.integral_finset_sum]
    intro i _
    exact T.integrable_summand2_coord_lim i
  -- Convert `hsum` (sum-of-integrals shape) to the lump-sum
  -- integral shape via `hint_n` / `hint_lim`.
  have hfun_n :
      (fun k => ∑ i : Fin d, ∫ x in UnitCube d,
          (μ x * DpH x (fun j => Dυ j x) (μ x) i)
            * (Dυ i x - T.Du_n k i x))
        = (fun k => ∫ x in UnitCube d,
            μ x * (DpH x (fun j => Dυ j x) (μ x)
                     ⬝ (fun i => Dυ i x - T.Du_n k i x))) := by
    funext k; exact (hint_n k).symm
  rw [hfun_n] at hsum
  rw [← hint_lim] at hsum
  exact hsum

/-- **AC5 — assembled `mfgOperatorPair` convergence.**

Combines `tendsto_summand1`, `tendsto_summand2_summed` (a sum
over coordinates of `tendsto_summand2_coord`), and
`tendsto_summand3` via `Tendsto.add` and `mfgOperatorPair_split`
to conclude the convergence of the unregularised pairing along
the F.5 sequence:
```
mfgOperatorPair Dυ μ υ (Dυ - Du_n k) (μ - m_n k) (υ - u_n k)
  → mfgOperatorPair Dυ μ υ (Dυ - Du) (μ - m) (υ - u).
```
This is exactly the `hpair_conv` hypothesis required by F.6's
`limitPassage_to_weakVI`. -/
theorem tendsto_mfgOperatorPair_assembled
    (T : LimitPassageInputData (d := d) V H DpH βBar βBar' γBar γBar' μ υ Dυ) :
    Filter.Tendsto (fun k =>
      mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
          (fun i x => Dυ i x - T.Du_n k i x)
          (μ - T.m_n k) (υ - T.u_n k))
      Filter.atTop
      (𝓝 (mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
            (fun i x => Dυ i x - T.Du i x)
            (μ - T.m) (υ - T.u))) := by
  -- Step 1: rewrite `mfgOperatorPair` on both sides into its three
  -- summands via `mfgOperatorPair_split`.
  have hsplit_n : ∀ k : ℕ,
      mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
          (fun i x => Dυ i x - T.Du_n k i x)
          (μ - T.m_n k) (υ - T.u_n k)
        = (∫ x in UnitCube d,
            (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x)
              * ((μ - T.m_n k) x))
          + (∫ x in UnitCube d,
              μ x * (DpH x (fun j => Dυ j x) (μ x)
                       ⬝ (fun i => Dυ i x - T.Du_n k i x)))
          + (∫ x in UnitCube d, (μ x - 1) * ((υ - T.u_n k) x)) := by
    intro k
    -- Apply `mfgOperatorPair_split` with the three integrability
    -- witnesses derived above.
    apply Solutions.MFG.mfgOperatorPair_split
      (V := V) (H := H) (DpH := DpH)
    · -- summand 1 integrability: rewrite `(μ - m_n k) x` as
      -- `μ x - m_n k x` to match the hypothesis form.
      have h := T.integrable_summand1_step k
      simpa using h
    · exact T.integrable_summand2_step k
    · have h := T.integrable_summand3_step k
      simpa using h
  have hsplit_lim :
      mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
          (fun i x => Dυ i x - T.Du i x)
          (μ - T.m) (υ - T.u)
        = (∫ x in UnitCube d,
            (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x)
              * ((μ - T.m) x))
          + (∫ x in UnitCube d,
              μ x * (DpH x (fun j => Dυ j x) (μ x)
                       ⬝ (fun i => Dυ i x - T.Du i x)))
          + (∫ x in UnitCube d, (μ x - 1) * ((υ - T.u) x)) := by
    apply Solutions.MFG.mfgOperatorPair_split
      (V := V) (H := H) (DpH := DpH)
    · have h := T.integrable_summand1_lim
      simpa using h
    · exact T.integrable_summand2_lim
    · have h := T.integrable_summand3_lim
      simpa using h
  -- Step 2: rewrite `(μ - m_n k) x` as `μ x - m_n k x` (likewise
  -- for `υ - u_n k`) in the summand 1 / 3 integrals to match the
  -- `tendsto_summand1` / `tendsto_summand3` shapes.
  have hfun_pt1 : ∀ k : ℕ,
      (fun x => (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x)
                  * ((μ - T.m_n k) x))
        = (fun x => (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x)
                      * (μ x - T.m_n k x)) := by
    intro k; funext x; simp [Pi.sub_apply]
  have hfun_pt1_lim :
      (fun x => (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x)
                  * ((μ - T.m) x))
        = (fun x => (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x)
                      * (μ x - T.m x)) := by
    funext x; simp [Pi.sub_apply]
  have hfun_pt3 : ∀ k : ℕ,
      (fun x => (μ x - 1) * ((υ - T.u_n k) x))
        = (fun x => (μ x - 1) * (υ x - T.u_n k x)) := by
    intro k; funext x; simp [Pi.sub_apply]
  have hfun_pt3_lim :
      (fun x => (μ x - 1) * ((υ - T.u) x))
        = (fun x => (μ x - 1) * (υ x - T.u x)) := by
    funext x; simp [Pi.sub_apply]
  -- Step 3: convert split equalities into integral equalities.
  have hint_eq_n : ∀ k : ℕ,
      ∫ x in UnitCube d,
        (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x)
          * ((μ - T.m_n k) x)
        = ∫ x in UnitCube d,
            (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x)
              * (μ x - T.m_n k x) := by
    intro k; rw [hfun_pt1 k]
  have hint_eq_lim :
      ∫ x in UnitCube d,
        (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x)
          * ((μ - T.m) x)
        = ∫ x in UnitCube d,
            (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x)
              * (μ x - T.m x) := by
    rw [hfun_pt1_lim]
  have hint3_eq_n : ∀ k : ℕ,
      ∫ x in UnitCube d, (μ x - 1) * ((υ - T.u_n k) x)
        = ∫ x in UnitCube d, (μ x - 1) * (υ x - T.u_n k x) := by
    intro k; rw [hfun_pt3 k]
  have hint3_eq_lim :
      ∫ x in UnitCube d, (μ x - 1) * ((υ - T.u) x)
        = ∫ x in UnitCube d, (μ x - 1) * (υ x - T.u x) := by
    rw [hfun_pt3_lim]
  -- Step 4: assemble the three summand `Tendsto` statements.
  have h1 := T.tendsto_summand1
  have h3 := T.tendsto_summand3
  have h2 := T.tendsto_summand2_summed
  -- Combine via `Tendsto.add` (twice).
  have h12 := h1.add h2
  have h123 := h12.add h3
  -- Convert h123 to the `mfgOperatorPair`-shape via the split
  -- equalities and the pointwise rewrites.
  have hfun_target :
      (fun k =>
        mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
            (fun i x => Dυ i x - T.Du_n k i x)
            (μ - T.m_n k) (υ - T.u_n k))
        = (fun k =>
            (∫ x in UnitCube d,
                (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x)
                  * (μ x - T.m_n k x))
              + (∫ x in UnitCube d,
                  μ x * (DpH x (fun j => Dυ j x) (μ x)
                           ⬝ (fun i => Dυ i x - T.Du_n k i x)))
              + (∫ x in UnitCube d, (μ x - 1) * (υ x - T.u_n k x))) := by
    funext k
    rw [hsplit_n k, hint_eq_n k, hint3_eq_n k]
  have htgt_lim :
      mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
          (fun i x => Dυ i x - T.Du i x)
          (μ - T.m) (υ - T.u)
        = (∫ x in UnitCube d,
            (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x)
              * (μ x - T.m x))
          + (∫ x in UnitCube d,
              μ x * (DpH x (fun j => Dυ j x) (μ x)
                       ⬝ (fun i => Dυ i x - T.Du i x)))
          + (∫ x in UnitCube d, (μ x - 1) * (υ x - T.u x)) := by
    rw [hsplit_lim, hint_eq_lim, hint3_eq_lim]
  rw [hfun_target, htgt_lim]
  exact h123

end LimitPassageInputData

/-! ### Lite variant — `LimitPassageInputData_noVI`

The Theorem-1 chain only consumes `LimitPassageInputData` through
`tendsto_mfgOperatorPair_assembled` (the universal `hVI_eps` field is
structurally dead in Theorem 1: the `hpair_conv` selector only invokes
`tendsto_mfgOperatorPair_assembled`, whose proof body never reads
`hVI_eps`; only the bypassed `limitPassage_to_weakVI` path reads it).

Because populating `LimitPassageInputData.hVI_eps` requires a universal
non-negativity statement at every `(μ, υ, Dυ)` — not derivable from
the per-family `RegularizedBareSolution.hVIeps_*` fields — we expose a
leaner shape `LimitPassageInputData_noVI` omitting `hVI_eps`, and a
companion `tendsto_mfgOperatorPair_assembled_noVI`. -/

/-- Lite version of `LimitPassageInputData` omitting the universal
`hVI_eps` field. Carries everything needed for the assembled
`mfgOperatorPair` convergence (E.1 + E.2 + E.3) but *not* for the
F.6 weak VI conclusion (which reads `hVI_eps`). -/
structure LimitPassageInputData_noVI
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (βBar βBar' γBar γBar' : ℝ)
    (μ υ : (Fin d → ℝ) → ℝ)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ) where
  /-- Hölder-conjugate pair `(β̄, β̄')`, `1/β̄ + 1/β̄' = 1`. -/
  hpqβ : βBar.HolderConjugate βBar'
  /-- Hölder-conjugate pair `(γ̄, γ̄')`, `1/γ̄ + 1/γ̄' = 1`. -/
  hpqγ : γBar.HolderConjugate γBar'
  /-- Regularization sequence `ε : ℕ → ℝ`. -/
  ε : ℕ → ℝ
  /-- Per-`k` density `m_n`. -/
  m_n : ℕ → (Fin d → ℝ) → ℝ
  /-- Per-`k` value function `u_n`. -/
  u_n : ℕ → (Fin d → ℝ) → ℝ
  /-- Per-`k` weak-derivative family `Du_n`. -/
  Du_n : ℕ → Fin d → (Fin d → ℝ) → ℝ
  /-- Limit density `m`. -/
  m : (Fin d → ℝ) → ℝ
  /-- Limit value function `u`. -/
  u : (Fin d → ℝ) → ℝ
  /-- Limit weak-derivative family `Du`. -/
  Du : Fin d → (Fin d → ℝ) → ℝ
  /-- `0 ≤ ε k`. -/
  hε_nonneg : ∀ k, 0 ≤ ε k
  /-- `ε k → 0`. -/
  hε_to0 : Filter.Tendsto ε Filter.atTop (𝓝 0)
  /-- `m_n k ∈ L^{β̄}_per` for every `k`. -/
  hm_n_memLp : ∀ k, Periodic.MemLpPer (ENNReal.ofReal βBar) (m_n k)
  /-- `m ∈ L^{β̄}_per`. -/
  hm_memLp : Periodic.MemLpPer (ENNReal.ofReal βBar) m
  /-- `u_n k ∈ L^{γ̄}_per` for every `k`. -/
  hu_n_memLp : ∀ k, Periodic.MemLpPer (ENNReal.ofReal γBar) (u_n k)
  /-- `u ∈ L^{γ̄}_per`. -/
  hu_memLp : Periodic.MemLpPer (ENNReal.ofReal γBar) u
  /-- `υ ∈ L^{γ̄}_per`. -/
  hυ_memLp : Periodic.MemLpPer (ENNReal.ofReal γBar) υ
  /-- `Du_n k i ∈ L^{γ̄}_per` for every `k`, `i`. -/
  hDu_n_memLp : ∀ k i, Periodic.MemLpPer (ENNReal.ofReal γBar) (Du_n k i)
  /-- `Du i ∈ L^{γ̄}_per` for every `i`. -/
  hDu_memLp : ∀ i, Periodic.MemLpPer (ENNReal.ofReal γBar) (Du i)
  /-- `Dυ i ∈ L^{γ̄}_per` for every `i`. -/
  hDυ_memLp : ∀ i, Periodic.MemLpPer (ENNReal.ofReal γBar) (Dυ i)
  /-- `μ ∈ L^{β̄}_per`. -/
  hμ_memLp : Periodic.MemLpPer (ENNReal.ofReal βBar) μ
  /-- Multiplier `g(x) := -υ(x) - H(x, Dυ, μ) + V(x)` is in
  `L^{β̄'}_per`. -/
  hg_memLp : Periodic.MemLpPer (ENNReal.ofReal βBar')
              (fun x => -(υ x) - H x (fun i => Dυ i x) (μ x) + V x)
  /-- Per-coordinate flux `flux_i(x) := μ(x) · D_pH(x, Dυ, μ) i` is in
  `L^{γ̄'}_per`. -/
  hflux_memLp : ∀ i, Periodic.MemLpPer (ENNReal.ofReal γBar')
                      (fun x => μ x * DpH x (fun j => Dυ j x) (μ x) i)
  /-- Mass-defect multiplier `(μ - 1) ∈ L^{γ̄'}_per`. -/
  hμMinusOne_memLp : Periodic.MemLpPer (ENNReal.ofReal γBar')
                      (fun x => μ x - 1)
  /-- Weak-pairing certificate: `m_n ⇀ m` against `L^{β̄'}_per` tests. -/
  h_weak_m : WeakConvPairing_universal (d := d) hpqβ m_n m
  /-- Weak-pairing certificate: `u_n ⇀ u` against `L^{γ̄'}_per` tests. -/
  h_weak_u : WeakConvPairing_universal (d := d) hpqγ u_n u
  /-- Weak-pairing certificate per coordinate: `Du_n · i ⇀ Du i`
  against `L^{γ̄'}_per` tests. -/
  h_weak_Du : ∀ i,
    WeakConvPairing_universal (d := d) hpqγ (fun k => Du_n k i) (Du i)
  /-- Uniform bound on the Gateaux residual. -/
  M : ℝ
  /-- The Gateaux residual is bounded by `M`. -/
  hreg_bdd : ∀ k,
    |gateauxWpPair γBar Dυ υ
        (fun i x => Dυ i x - Du_n k i x) (υ - u_n k)| ≤ M

namespace LimitPassageInputData

/-- Project a `LimitPassageInputData` bundle to its lite variant by
forgetting the `hVI_eps` field. -/
def to_noVI
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {βBar βBar' γBar γBar' : ℝ}
    {μ υ : (Fin d → ℝ) → ℝ}
    {Dυ : Fin d → (Fin d → ℝ) → ℝ}
    (T : LimitPassageInputData (d := d) V H DpH βBar βBar' γBar γBar' μ υ Dυ) :
    LimitPassageInputData_noVI (d := d) V H DpH βBar βBar' γBar γBar' μ υ Dυ where
  hpqβ := T.hpqβ
  hpqγ := T.hpqγ
  ε := T.ε
  m_n := T.m_n
  u_n := T.u_n
  Du_n := T.Du_n
  m := T.m
  u := T.u
  Du := T.Du
  hε_nonneg := T.hε_nonneg
  hε_to0 := T.hε_to0
  hm_n_memLp := T.hm_n_memLp
  hm_memLp := T.hm_memLp
  hu_n_memLp := T.hu_n_memLp
  hu_memLp := T.hu_memLp
  hυ_memLp := T.hυ_memLp
  hDu_n_memLp := T.hDu_n_memLp
  hDu_memLp := T.hDu_memLp
  hDυ_memLp := T.hDυ_memLp
  hμ_memLp := T.hμ_memLp
  hg_memLp := T.hg_memLp
  hflux_memLp := T.hflux_memLp
  hμMinusOne_memLp := T.hμMinusOne_memLp
  h_weak_m := T.h_weak_m
  h_weak_u := T.h_weak_u
  h_weak_Du := T.h_weak_Du
  M := T.M
  hreg_bdd := T.hreg_bdd

end LimitPassageInputData

namespace LimitPassageInputData_noVI

/-- Lift a `LimitPassageInputData_noVI` bundle to a full
`LimitPassageInputData` by supplying the missing `hVI_eps` field. This
is the inverse of `LimitPassageInputData.to_noVI` and is used by the
legacy F.6 producers (`limitSolutionData_of_regularizedSequence` and
its strict-positivity variant) to recover the universal regularised-VI
input from the leaner Theorem-1 plumbing. -/
def of_noVI_withVI
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {βBar βBar' γBar γBar' : ℝ}
    {μ υ : (Fin d → ℝ) → ℝ}
    {Dυ : Fin d → (Fin d → ℝ) → ℝ}
    (T : LimitPassageInputData_noVI
            (d := d) V H DpH βBar βBar' γBar γBar' μ υ Dυ)
    (hVI_eps : ∀ k,
        0 ≤ StationaryMFG.Solutions.MFG.mfgOperatorEpsPair
              (V := V) (H := H) (DpH := DpH)
              γBar (T.ε k) Dυ μ υ
              (fun i x => Dυ i x - T.Du_n k i x)
              (μ - T.m_n k) (υ - T.u_n k)) :
    LimitPassageInputData (d := d) V H DpH βBar βBar' γBar γBar' μ υ Dυ where
  hpqβ := T.hpqβ
  hpqγ := T.hpqγ
  ε := T.ε
  m_n := T.m_n
  u_n := T.u_n
  Du_n := T.Du_n
  m := T.m
  u := T.u
  Du := T.Du
  hε_nonneg := T.hε_nonneg
  hε_to0 := T.hε_to0
  hm_n_memLp := T.hm_n_memLp
  hm_memLp := T.hm_memLp
  hu_n_memLp := T.hu_n_memLp
  hu_memLp := T.hu_memLp
  hυ_memLp := T.hυ_memLp
  hDu_n_memLp := T.hDu_n_memLp
  hDu_memLp := T.hDu_memLp
  hDυ_memLp := T.hDυ_memLp
  hμ_memLp := T.hμ_memLp
  hg_memLp := T.hg_memLp
  hflux_memLp := T.hflux_memLp
  hμMinusOne_memLp := T.hμMinusOne_memLp
  h_weak_m := T.h_weak_m
  h_weak_u := T.h_weak_u
  h_weak_Du := T.h_weak_Du
  hVI_eps := hVI_eps
  M := T.M
  hreg_bdd := T.hreg_bdd

end LimitPassageInputData_noVI

namespace LimitPassageInputData_noVI

variable
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {βBar βBar' γBar γBar' : ℝ}
    {μ υ : (Fin d → ℝ) → ℝ}
    {Dυ : Fin d → (Fin d → ℝ) → ℝ}

/-- Per-summand-1 step integrability (lite version). Mirrors
`LimitPassageInputData.integrable_summand1_step`. -/
private lemma integrable_summand1_step
    (T : LimitPassageInputData_noVI (d := d) V H DpH βBar βBar' γBar γBar' μ υ Dυ)
    (k : ℕ) :
    Integrable
      (fun x => (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x)
                 * (μ x - T.m_n k x))
      (volume.restrict (UnitCube d)) := by
  have hμmn : Periodic.MemLpPer (ENNReal.ofReal βBar) (μ - T.m_n k) :=
    Periodic.MemLp.toMemLpPer (MeasureTheory.MemLp.sub T.hμ_memLp.toMemLp (T.hm_n_memLp k).toMemLp)
  have hμmn' :
      Periodic.MemLpPer (ENNReal.ofReal βBar)
        (fun x => μ x - T.m_n k x) := hμmn
  have hpq' : βBar'.HolderConjugate βBar := T.hpqβ.symm
  exact Periodic.MemLpPer.integrable_mul hpq' T.hg_memLp hμmn'

/-- Per-summand-1 limit integrability (lite version). -/
private lemma integrable_summand1_lim
    (T : LimitPassageInputData_noVI (d := d) V H DpH βBar βBar' γBar γBar' μ υ Dυ) :
    Integrable
      (fun x => (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x)
                 * (μ x - T.m x))
      (volume.restrict (UnitCube d)) := by
  have hμm : Periodic.MemLpPer (ENNReal.ofReal βBar) (μ - T.m) :=
    Periodic.MemLp.toMemLpPer (MeasureTheory.MemLp.sub T.hμ_memLp.toMemLp T.hm_memLp.toMemLp)
  have hμm' :
      Periodic.MemLpPer (ENNReal.ofReal βBar)
        (fun x => μ x - T.m x) := hμm
  have hpq' : βBar'.HolderConjugate βBar := T.hpqβ.symm
  exact Periodic.MemLpPer.integrable_mul hpq' T.hg_memLp hμm'

/-- Per-coord, per-`k` integrability of summand 2 (lite version). -/
private lemma integrable_summand2_coord_step
    (T : LimitPassageInputData_noVI (d := d) V H DpH βBar βBar' γBar γBar' μ υ Dυ)
    (k : ℕ) (i : Fin d) :
    Integrable
      (fun x => (μ x * DpH x (fun j => Dυ j x) (μ x) i)
                  * (Dυ i x - T.Du_n k i x))
      (volume.restrict (UnitCube d)) := by
  have hDνmem : Periodic.MemLpPer (ENNReal.ofReal γBar)
      (Dυ i - T.Du_n k i) :=
    Periodic.MemLp.toMemLpPer (MeasureTheory.MemLp.sub (T.hDυ_memLp i).toMemLp (T.hDu_n_memLp k i).toMemLp)
  have hDνmem' : Periodic.MemLpPer (ENNReal.ofReal γBar)
      (fun x => Dυ i x - T.Du_n k i x) := hDνmem
  have hpq' : γBar'.HolderConjugate γBar := T.hpqγ.symm
  exact Periodic.MemLpPer.integrable_mul hpq' (T.hflux_memLp i) hDνmem'

/-- Per-coord limit integrability of summand 2 (lite version). -/
private lemma integrable_summand2_coord_lim
    (T : LimitPassageInputData_noVI (d := d) V H DpH βBar βBar' γBar γBar' μ υ Dυ)
    (i : Fin d) :
    Integrable
      (fun x => (μ x * DpH x (fun j => Dυ j x) (μ x) i)
                  * (Dυ i x - T.Du i x))
      (volume.restrict (UnitCube d)) := by
  have hDνmem : Periodic.MemLpPer (ENNReal.ofReal γBar)
      (Dυ i - T.Du i) :=
    Periodic.MemLp.toMemLpPer (MeasureTheory.MemLp.sub (T.hDυ_memLp i).toMemLp (T.hDu_memLp i).toMemLp)
  have hDνmem' : Periodic.MemLpPer (ENNReal.ofReal γBar)
      (fun x => Dυ i x - T.Du i x) := hDνmem
  have hpq' : γBar'.HolderConjugate γBar := T.hpqγ.symm
  exact Periodic.MemLpPer.integrable_mul hpq' (T.hflux_memLp i) hDνmem'

/-- Per-`k` integrability of the summand-2 lump-sum integrand (lite). -/
private lemma integrable_summand2_step
    (T : LimitPassageInputData_noVI (d := d) V H DpH βBar βBar' γBar γBar' μ υ Dυ)
    (k : ℕ) :
    Integrable
      (fun x => μ x * (DpH x (fun j => Dυ j x) (μ x)
                         ⬝ (fun i => Dυ i x - T.Du_n k i x)))
      (volume.restrict (UnitCube d)) := by
  have hpt :
      (fun x => μ x * (DpH x (fun j => Dυ j x) (μ x)
                         ⬝ (fun i => Dυ i x - T.Du_n k i x)))
        = (fun x => ∑ i : Fin d,
            (μ x * DpH x (fun j => Dυ j x) (μ x) i)
              * (Dυ i x - T.Du_n k i x)) := by
    funext x
    unfold dotProduct
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  rw [hpt]
  exact MeasureTheory.integrable_finset_sum _
    (fun i _ => T.integrable_summand2_coord_step k i)

/-- Limit-time integrability of the summand-2 lump-sum integrand (lite). -/
private lemma integrable_summand2_lim
    (T : LimitPassageInputData_noVI (d := d) V H DpH βBar βBar' γBar γBar' μ υ Dυ) :
    Integrable
      (fun x => μ x * (DpH x (fun j => Dυ j x) (μ x)
                         ⬝ (fun i => Dυ i x - T.Du i x)))
      (volume.restrict (UnitCube d)) := by
  have hpt :
      (fun x => μ x * (DpH x (fun j => Dυ j x) (μ x)
                         ⬝ (fun i => Dυ i x - T.Du i x)))
        = (fun x => ∑ i : Fin d,
            (μ x * DpH x (fun j => Dυ j x) (μ x) i)
              * (Dυ i x - T.Du i x)) := by
    funext x
    unfold dotProduct
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  rw [hpt]
  exact MeasureTheory.integrable_finset_sum _
    (fun i _ => T.integrable_summand2_coord_lim i)

/-- Per-`k` integrability of summand 3 (lite). -/
private lemma integrable_summand3_step
    (T : LimitPassageInputData_noVI (d := d) V H DpH βBar βBar' γBar γBar' μ υ Dυ)
    (k : ℕ) :
    Integrable (fun x => (μ x - 1) * (υ x - T.u_n k x))
      (volume.restrict (UnitCube d)) := by
  have hυu : Periodic.MemLpPer (ENNReal.ofReal γBar) (υ - T.u_n k) :=
    Periodic.MemLp.toMemLpPer (MeasureTheory.MemLp.sub T.hυ_memLp.toMemLp (T.hu_n_memLp k).toMemLp)
  have hυu' :
      Periodic.MemLpPer (ENNReal.ofReal γBar)
        (fun x => υ x - T.u_n k x) := hυu
  have hμ1' :
      Periodic.MemLpPer (ENNReal.ofReal γBar')
        (fun x => μ x - 1) := T.hμMinusOne_memLp
  have hpq : γBar'.HolderConjugate γBar := T.hpqγ.symm
  exact Periodic.MemLpPer.integrable_mul hpq hμ1' hυu'

/-- Limit-time integrability of summand 3 (lite). -/
private lemma integrable_summand3_lim
    (T : LimitPassageInputData_noVI (d := d) V H DpH βBar βBar' γBar γBar' μ υ Dυ) :
    Integrable (fun x => (μ x - 1) * (υ x - T.u x))
      (volume.restrict (UnitCube d)) := by
  have hυu : Periodic.MemLpPer (ENNReal.ofReal γBar) (υ - T.u) :=
    Periodic.MemLp.toMemLpPer (MeasureTheory.MemLp.sub T.hυ_memLp.toMemLp T.hu_memLp.toMemLp)
  have hυu' :
      Periodic.MemLpPer (ENNReal.ofReal γBar)
        (fun x => υ x - T.u x) := hυu
  have hμ1' :
      Periodic.MemLpPer (ENNReal.ofReal γBar')
        (fun x => μ x - 1) := T.hμMinusOne_memLp
  have hpq : γBar'.HolderConjugate γBar := T.hpqγ.symm
  exact Periodic.MemLpPer.integrable_mul hpq hμ1' hυu'

/-- Convergence of summand 1 (lite). -/
theorem tendsto_summand1
    (T : LimitPassageInputData_noVI (d := d) V H DpH βBar βBar' γBar γBar' μ υ Dυ) :
    Filter.Tendsto
      (fun k => ∫ x in UnitCube d,
        (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (μ x - T.m_n k x))
      Filter.atTop
      (𝓝 (∫ x in UnitCube d,
        (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * (μ x - T.m x))) :=
  limit_passage_summand1 T.hpqβ T.hm_n_memLp T.hm_memLp T.hμ_memLp
    T.hg_memLp T.h_weak_m

/-- Convergence of summand 3 (lite). -/
theorem tendsto_summand3
    (T : LimitPassageInputData_noVI (d := d) V H DpH βBar βBar' γBar γBar' μ υ Dυ) :
    Filter.Tendsto
      (fun k => ∫ x in UnitCube d,
        (μ x - 1) * (υ x - T.u_n k x))
      Filter.atTop
      (𝓝 (∫ x in UnitCube d,
        (μ x - 1) * (υ x - T.u x))) :=
  limit_passage_summand3 T.hpqγ T.hu_n_memLp T.hu_memLp T.hυ_memLp
    T.hμMinusOne_memLp T.h_weak_u

/-- Convergence of summand 2, per coordinate (lite). -/
theorem tendsto_summand2_coord
    (T : LimitPassageInputData_noVI (d := d) V H DpH βBar βBar' γBar γBar' μ υ Dυ)
    (i : Fin d) :
    Filter.Tendsto
      (fun k => ∫ x in UnitCube d,
        (μ x * DpH x (fun j => Dυ j x) (μ x) i)
          * (Dυ i x - T.Du_n k i x))
      Filter.atTop
      (𝓝 (∫ x in UnitCube d,
        (μ x * DpH x (fun j => Dυ j x) (μ x) i)
          * (Dυ i x - T.Du i x))) :=
  limit_passage_summand2 T.hpqγ
    (fun k => T.hDu_n_memLp k i) (T.hDu_memLp i) (T.hDυ_memLp i)
    (T.hflux_memLp i) (T.h_weak_Du i)

/-- Lump-sum convergence of summand 2 (lite). -/
theorem tendsto_summand2_summed
    (T : LimitPassageInputData_noVI (d := d) V H DpH βBar βBar' γBar γBar' μ υ Dυ) :
    Filter.Tendsto
      (fun k => ∫ x in UnitCube d,
        μ x * (DpH x (fun j => Dυ j x) (μ x)
                 ⬝ (fun i => Dυ i x - T.Du_n k i x)))
      Filter.atTop
      (𝓝 (∫ x in UnitCube d,
        μ x * (DpH x (fun j => Dυ j x) (μ x)
                 ⬝ (fun i => Dυ i x - T.Du i x)))) := by
  have hcoord : ∀ i : Fin d,
      Filter.Tendsto
        (fun k => ∫ x in UnitCube d,
          (μ x * DpH x (fun j => Dυ j x) (μ x) i)
            * (Dυ i x - T.Du_n k i x))
        Filter.atTop
        (𝓝 (∫ x in UnitCube d,
          (μ x * DpH x (fun j => Dυ j x) (μ x) i)
            * (Dυ i x - T.Du i x))) := T.tendsto_summand2_coord
  have hsum :
      Filter.Tendsto
        (fun k => ∑ i : Fin d, ∫ x in UnitCube d,
          (μ x * DpH x (fun j => Dυ j x) (μ x) i)
            * (Dυ i x - T.Du_n k i x))
        Filter.atTop
        (𝓝 (∑ i : Fin d, ∫ x in UnitCube d,
          (μ x * DpH x (fun j => Dυ j x) (μ x) i)
            * (Dυ i x - T.Du i x))) :=
    tendsto_finset_sum _ (fun i _ => hcoord i)
  have hpt_n : ∀ k : ℕ, ∀ x : Fin d → ℝ,
      μ x * (DpH x (fun j => Dυ j x) (μ x)
               ⬝ (fun i => Dυ i x - T.Du_n k i x))
        = ∑ i : Fin d, (μ x * DpH x (fun j => Dυ j x) (μ x) i)
                           * (Dυ i x - T.Du_n k i x) := by
    intro k x
    unfold dotProduct
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  have hpt_lim : ∀ x : Fin d → ℝ,
      μ x * (DpH x (fun j => Dυ j x) (μ x)
               ⬝ (fun i => Dυ i x - T.Du i x))
        = ∑ i : Fin d, (μ x * DpH x (fun j => Dυ j x) (μ x) i)
                           * (Dυ i x - T.Du i x) := by
    intro x
    unfold dotProduct
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  have hint_n : ∀ k : ℕ,
      ∫ x in UnitCube d,
        μ x * (DpH x (fun j => Dυ j x) (μ x)
                 ⬝ (fun i => Dυ i x - T.Du_n k i x))
        = ∑ i : Fin d, ∫ x in UnitCube d,
            (μ x * DpH x (fun j => Dυ j x) (μ x) i)
              * (Dυ i x - T.Du_n k i x) := by
    intro k
    have h1 :
        (fun x => μ x * (DpH x (fun j => Dυ j x) (μ x)
                           ⬝ (fun i => Dυ i x - T.Du_n k i x)))
          = (fun x => ∑ i : Fin d,
              (μ x * DpH x (fun j => Dυ j x) (μ x) i)
                * (Dυ i x - T.Du_n k i x)) := by
      funext x; exact hpt_n k x
    rw [h1, MeasureTheory.integral_finset_sum]
    intro i _
    exact T.integrable_summand2_coord_step k i
  have hint_lim :
      ∫ x in UnitCube d,
        μ x * (DpH x (fun j => Dυ j x) (μ x)
                 ⬝ (fun i => Dυ i x - T.Du i x))
        = ∑ i : Fin d, ∫ x in UnitCube d,
            (μ x * DpH x (fun j => Dυ j x) (μ x) i)
              * (Dυ i x - T.Du i x) := by
    have h1 :
        (fun x => μ x * (DpH x (fun j => Dυ j x) (μ x)
                           ⬝ (fun i => Dυ i x - T.Du i x)))
          = (fun x => ∑ i : Fin d,
              (μ x * DpH x (fun j => Dυ j x) (μ x) i)
                * (Dυ i x - T.Du i x)) := by
      funext x; exact hpt_lim x
    rw [h1, MeasureTheory.integral_finset_sum]
    intro i _
    exact T.integrable_summand2_coord_lim i
  have hfun_n :
      (fun k => ∑ i : Fin d, ∫ x in UnitCube d,
          (μ x * DpH x (fun j => Dυ j x) (μ x) i)
            * (Dυ i x - T.Du_n k i x))
        = (fun k => ∫ x in UnitCube d,
            μ x * (DpH x (fun j => Dυ j x) (μ x)
                     ⬝ (fun i => Dυ i x - T.Du_n k i x))) := by
    funext k; exact (hint_n k).symm
  rw [hfun_n] at hsum
  rw [← hint_lim] at hsum
  exact hsum

/-- **AC5 — assembled `mfgOperatorPair` convergence (lite version).**

Same conclusion as `LimitPassageInputData.tendsto_mfgOperatorPair_assembled`,
but consumes the leaner `LimitPassageInputData_noVI` shape (no
`hVI_eps` field). The proof body is identical to the universal
version, since that proof never reads `hVI_eps`. -/
theorem tendsto_mfgOperatorPair_assembled_noVI
    (T : LimitPassageInputData_noVI (d := d) V H DpH βBar βBar' γBar γBar' μ υ Dυ) :
    Filter.Tendsto (fun k =>
      mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
          (fun i x => Dυ i x - T.Du_n k i x)
          (μ - T.m_n k) (υ - T.u_n k))
      Filter.atTop
      (𝓝 (mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
            (fun i x => Dυ i x - T.Du i x)
            (μ - T.m) (υ - T.u))) := by
  have hsplit_n : ∀ k : ℕ,
      mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
          (fun i x => Dυ i x - T.Du_n k i x)
          (μ - T.m_n k) (υ - T.u_n k)
        = (∫ x in UnitCube d,
            (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x)
              * ((μ - T.m_n k) x))
          + (∫ x in UnitCube d,
              μ x * (DpH x (fun j => Dυ j x) (μ x)
                       ⬝ (fun i => Dυ i x - T.Du_n k i x)))
          + (∫ x in UnitCube d, (μ x - 1) * ((υ - T.u_n k) x)) := by
    intro k
    apply Solutions.MFG.mfgOperatorPair_split
      (V := V) (H := H) (DpH := DpH)
    · have h := T.integrable_summand1_step k
      simpa using h
    · exact T.integrable_summand2_step k
    · have h := T.integrable_summand3_step k
      simpa using h
  have hsplit_lim :
      mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
          (fun i x => Dυ i x - T.Du i x)
          (μ - T.m) (υ - T.u)
        = (∫ x in UnitCube d,
            (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x)
              * ((μ - T.m) x))
          + (∫ x in UnitCube d,
              μ x * (DpH x (fun j => Dυ j x) (μ x)
                       ⬝ (fun i => Dυ i x - T.Du i x)))
          + (∫ x in UnitCube d, (μ x - 1) * ((υ - T.u) x)) := by
    apply Solutions.MFG.mfgOperatorPair_split
      (V := V) (H := H) (DpH := DpH)
    · have h := T.integrable_summand1_lim
      simpa using h
    · exact T.integrable_summand2_lim
    · have h := T.integrable_summand3_lim
      simpa using h
  have hfun_pt1 : ∀ k : ℕ,
      (fun x => (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x)
                  * ((μ - T.m_n k) x))
        = (fun x => (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x)
                      * (μ x - T.m_n k x)) := by
    intro k; funext x; simp [Pi.sub_apply]
  have hfun_pt1_lim :
      (fun x => (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x)
                  * ((μ - T.m) x))
        = (fun x => (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x)
                      * (μ x - T.m x)) := by
    funext x; simp [Pi.sub_apply]
  have hfun_pt3 : ∀ k : ℕ,
      (fun x => (μ x - 1) * ((υ - T.u_n k) x))
        = (fun x => (μ x - 1) * (υ x - T.u_n k x)) := by
    intro k; funext x; simp [Pi.sub_apply]
  have hfun_pt3_lim :
      (fun x => (μ x - 1) * ((υ - T.u) x))
        = (fun x => (μ x - 1) * (υ x - T.u x)) := by
    funext x; simp [Pi.sub_apply]
  have hint_eq_n : ∀ k : ℕ,
      ∫ x in UnitCube d,
        (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x)
          * ((μ - T.m_n k) x)
        = ∫ x in UnitCube d,
            (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x)
              * (μ x - T.m_n k x) := by
    intro k; rw [hfun_pt1 k]
  have hint_eq_lim :
      ∫ x in UnitCube d,
        (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x)
          * ((μ - T.m) x)
        = ∫ x in UnitCube d,
            (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x)
              * (μ x - T.m x) := by
    rw [hfun_pt1_lim]
  have hint3_eq_n : ∀ k : ℕ,
      ∫ x in UnitCube d, (μ x - 1) * ((υ - T.u_n k) x)
        = ∫ x in UnitCube d, (μ x - 1) * (υ x - T.u_n k x) := by
    intro k; rw [hfun_pt3 k]
  have hint3_eq_lim :
      ∫ x in UnitCube d, (μ x - 1) * ((υ - T.u) x)
        = ∫ x in UnitCube d, (μ x - 1) * (υ x - T.u x) := by
    rw [hfun_pt3_lim]
  have h1 := T.tendsto_summand1
  have h3 := T.tendsto_summand3
  have h2 := T.tendsto_summand2_summed
  have h12 := h1.add h2
  have h123 := h12.add h3
  have hfun_target :
      (fun k =>
        mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
            (fun i x => Dυ i x - T.Du_n k i x)
            (μ - T.m_n k) (υ - T.u_n k))
        = (fun k =>
            (∫ x in UnitCube d,
                (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x)
                  * (μ x - T.m_n k x))
              + (∫ x in UnitCube d,
                  μ x * (DpH x (fun j => Dυ j x) (μ x)
                           ⬝ (fun i => Dυ i x - T.Du_n k i x)))
              + (∫ x in UnitCube d, (μ x - 1) * (υ x - T.u_n k x))) := by
    funext k
    rw [hsplit_n k, hint_eq_n k, hint3_eq_n k]
  have htgt_lim :
      mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
          (fun i x => Dυ i x - T.Du i x)
          (μ - T.m) (υ - T.u)
        = (∫ x in UnitCube d,
            (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x)
              * (μ x - T.m x))
          + (∫ x in UnitCube d,
              μ x * (DpH x (fun j => Dυ j x) (μ x)
                       ⬝ (fun i => Dυ i x - T.Du i x)))
          + (∫ x in UnitCube d, (μ x - 1) * (υ x - T.u x)) := by
    rw [hsplit_lim, hint_eq_lim, hint3_eq_lim]
  rw [hfun_target, htgt_lim]
  exact h123

end LimitPassageInputData_noVI

/-! ### Sanity checks for the lite variant. -/

/-- Feeding the lite structure produces the assembled-pairing
`Tendsto`. -/
example
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {βBar βBar' γBar γBar' : ℝ}
    {μ υ : (Fin d → ℝ) → ℝ}
    {Dυ : Fin d → (Fin d → ℝ) → ℝ}
    (T : LimitPassageInputData_noVI (d := d) V H DpH βBar βBar' γBar γBar' μ υ Dυ) :
    Filter.Tendsto (fun k =>
      mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
          (fun i x => Dυ i x - T.Du_n k i x)
          (μ - T.m_n k) (υ - T.u_n k))
      Filter.atTop
      (𝓝 (mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
            (fun i x => Dυ i x - T.Du i x)
            (μ - T.m) (υ - T.u))) :=
  T.tendsto_mfgOperatorPair_assembled_noVI

/-- Both assembled-pairing lemmas agree: applying
`tendsto_mfgOperatorPair_assembled_noVI` to `T.to_noVI` yields the same
`Tendsto` as the universal `tendsto_mfgOperatorPair_assembled` on `T`. -/
example
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {βBar βBar' γBar γBar' : ℝ}
    {μ υ : (Fin d → ℝ) → ℝ}
    {Dυ : Fin d → (Fin d → ℝ) → ℝ}
    (T : LimitPassageInputData (d := d) V H DpH βBar βBar' γBar γBar' μ υ Dυ) :
    Filter.Tendsto (fun k =>
      mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
          (fun i x => Dυ i x - T.Du_n k i x)
          (μ - T.m_n k) (υ - T.u_n k))
      Filter.atTop
      (𝓝 (mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
            (fun i x => Dυ i x - T.Du i x)
            (μ - T.m) (υ - T.u))) :=
  T.to_noVI.tendsto_mfgOperatorPair_assembled_noVI

/-! ### Headline theorem — F.6

Combine the three per-summand `Tendsto` statements
(`tendsto_summand1`, `tendsto_summand2_coord` summed over `Fin d`,
`tendsto_summand3`) to obtain the convergence of the unregularised
operator pairing along the F.5 sequence, and feed it into
`limit_passage_weak_VI_of_eps` to discharge the weak VI at the limit.

The unregularised operator integrand splits pointwise as:
```
mfgOperatorPair Dυ μ υ (Dυ - Du_n k) (μ - m_n k) (υ - u_n k)
  = ∫ (-υ - H + V) · (μ - m_n k)             -- summand 1
  + ∫ μ · (D_pH ⬝ (Dυ - Du_n k))             -- summand 2 (sum over coords)
  + ∫ (μ - 1) · (υ - u_n k)                   -- summand 3
```
We make this split explicit via integral-additivity, apply the three
summand limits, and combine. -/

/-- **F.6 — Limit passage to function-form weak VI.**

Given a `LimitPassageInputData` bundle (the F.5 weak-limit data plus
the per-summand `WeakConvPairing` and `MemLpPer` certificates and the
F.4 regularised strong-VI inequality), conclude the **weak VI** at
the limit triple `(m, u, Du)`:
```
0 ≤ mfgOperatorPair Dυ μ υ (Dυ - Du) (μ - m) (υ - u).
```

The proof assembles the convergence of the unregularised pairing
along the F.5 sequence from the three summand `Tendsto` statements
(`tendsto_summand1`, `tendsto_summand2_coord` per coordinate,
`tendsto_summand3`) and feeds the result into
`limit_passage_weak_VI_of_eps`. -/
theorem limitPassage_to_weakVI
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {βBar βBar' γBar γBar' : ℝ}
    {μ υ : (Fin d → ℝ) → ℝ}
    {Dυ : Fin d → (Fin d → ℝ) → ℝ}
    (T : LimitPassageInputData (d := d) V H DpH βBar βBar' γBar γBar' μ υ Dυ)
    (hpair_conv :
      Filter.Tendsto (fun k =>
        mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
            (fun i x => Dυ i x - T.Du_n k i x) (μ - T.m_n k) (υ - T.u_n k))
        Filter.atTop
        (𝓝 (mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
              (fun i x => Dυ i x - T.Du i x) (μ - T.m) (υ - T.u)))) :
    0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
          (fun i x => Dυ i x - T.Du i x) (μ - T.m) (υ - T.u) :=
  limit_passage_weak_VI_of_eps (V := V) (H := H) (DpH := DpH)
    T.hε_nonneg T.hε_to0 T.hVI_eps hpair_conv T.hreg_bdd

/-! ### Sanity-check unit `example` for F.6

Pin the type-shape of `limitPassage_to_weakVI`: feeding it a
`LimitPassageInputData` bundle and the assembled convergence of the
unregularised operator pairing produces the weak VI at the limit. -/

example
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {βBar βBar' γBar γBar' : ℝ}
    {μ υ : (Fin d → ℝ) → ℝ}
    {Dυ : Fin d → (Fin d → ℝ) → ℝ}
    (T : LimitPassageInputData (d := d) V H DpH βBar βBar' γBar γBar' μ υ Dυ)
    (hpair_conv :
      Filter.Tendsto (fun k =>
        mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
            (fun i x => Dυ i x - T.Du_n k i x) (μ - T.m_n k) (υ - T.u_n k))
        Filter.atTop
        (𝓝 (mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
              (fun i x => Dυ i x - T.Du i x) (μ - T.m) (υ - T.u)))) :
    0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
          (fun i x => Dυ i x - T.Du i x) (μ - T.m) (υ - T.u) :=
  limitPassage_to_weakVI T hpair_conv

/-! ### AC5 sanity check: end-to-end pipeline.

`tendsto_mfgOperatorPair_assembled` produces the `hpair_conv` input
required by `limitPassage_to_weakVI`. Composing both gives the
weak VI at the limit triple from the F.5 weak-limit data alone
(no separately-supplied pairing convergence). -/
example
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {βBar βBar' γBar γBar' : ℝ}
    {μ υ : (Fin d → ℝ) → ℝ}
    {Dυ : Fin d → (Fin d → ℝ) → ℝ}
    (T : LimitPassageInputData (d := d) V H DpH βBar βBar' γBar γBar' μ υ Dυ) :
    0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
          (fun i x => Dυ i x - T.Du i x) (μ - T.m) (υ - T.u) :=
  limitPassage_to_weakVI T T.tendsto_mfgOperatorPair_assembled

end Banach
end SimplePower
end Theorems
end StationaryMFG
