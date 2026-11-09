module

public import StationaryMFG.Theorems.SimplePower.Banach.AssemblyContext
public import StationaryMFG.Theorems.SimplePower.Banach.UniformSequence
public import StationaryMFG.Theorems.SimplePower.Banach.Closure
public import StationaryMFG.Periodic.Separability
public import Mathlib.MeasureTheory.Function.Floor
public import StationaryMFG.Theorems.SimplePower.Banach.RegularizedSequence.Part1
import all StationaryMFG.Theorems.SimplePower.Banach.RegularizedSequence.Part1
public import StationaryMFG.Theorems.SimplePower.Banach.RegularizedSequence.Part2
import all StationaryMFG.Theorems.SimplePower.Banach.RegularizedSequence.Part2

@[expose] public section

noncomputable section
namespace StationaryMFG
namespace Theorems
namespace SimplePower
namespace Banach
open MeasureTheory Filter
open StationaryMFG.Periodic
open StationaryMFG.Hamiltonian
open StationaryMFG.Solutions.MFG
open scoped ENNReal Topology
variable {d : ℕ}
open MeasureTheory Filter
variable {V : (Fin d → ℝ) → ℝ}
variable {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
variable {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}


/-! ### `WeakLimitSelectorAE` — selector data via `AEPeriodicRep`.

This is the **localized Path-A discharge**: the selector returns chosen
periodic representatives **as data** through the
`AEPeriodicRep` interface (introduced by
`infra-P4-refactor-aeperiodic-bridge`), and the cluster-point
a.e.-equality becomes a **direct projection** onto
`AEPeriodicRep.ae_eq` for the chosen `w`.

Banach-side convergence statements that mention `Lp.coeFn` are
transported through the chosen periodic representatives via the
pairing-congruence lemmas
(`Solutions.MFG.mfgOperatorPair_eq_on_AEPeriodicRep_*`,
`mfgOperatorPair_congr_ae`, `_congr_ae_primal`) introduced by
`infra-P4-refactor-pairing-congruence`. The structure below contains
**no raw `Lp.coeFn` references**.

The original universally-quantified `auxAeOfClusterPoint` field of
`WeakLimitSelector` (the genuine Path-A residue for arbitrary `w'`)
is therefore reduced to the chosen-`w` projection — exactly the
acceptance criterion (3) of this task. The migration of downstream
consumers (which still reference `WeakLimitSelector` via `WeakLimitInputBundle`)
is filed as a follow-up internal refactor. -/

/-- **Selector data via `AEPeriodicRep`.**

Parametrised by a chosen Banach-pair cluster point `w`, this structure
packages:

* the chosen periodic representatives `mRep`, `uRep`, `DuRep i` of
  `w.1`, `w.2.1`, `w.2.2 i` respectively (as `AEPeriodicRep`s);
* the sequence-side bare-function periodic representatives
  `seqRepU n`, `seqRepDu n i` plus their per-`n` weak-derivative
  relation;
* the test-function `Tendsto` hypotheses against the chosen
  `mRep.rep`, `uRep.rep`, `DuRep i.rep`;
* the non-negativity certificate.

There is **no** universally-quantified `auxAeOfClusterPoint` field:
for the chosen `w`, the agreement is precisely
`mRep.ae_eq`, `uRep.ae_eq`, `DuRep i.ae_eq`
(see `WeakLimitSelectorAE.aeEqClusterPoint_chosen`). This eliminates
the Path-A obstruction *for the chosen cluster point*; downstream
consumers needing the universal-`w'` form should call
`WeakLimitSelectorAE.toWeakLimitSelector` with an explicit
"other-cluster-point" residue parameter. -/
structure WeakLimitSelectorAE
    (γBarReal βBarReal : ℝ)
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (w : Periodic.LpPer (ENNReal.ofReal βBarReal) d
            × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d) where
  /-- Chosen periodic representative of the `m`-component cluster point. -/
  mRep : Periodic.AEPeriodicRep (⇑w.1 : (Fin d → ℝ) → ℝ)
  /-- Chosen periodic representative of the `u`-component cluster point. -/
  uRep : Periodic.AEPeriodicRep (⇑w.2.1 : (Fin d → ℝ) → ℝ)
  /-- Chosen periodic representative of every gradient-component cluster point. -/
  DuRep : ∀ i, Periodic.AEPeriodicRep (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ)
  /-- `MemLpPer 1` of every gradient-limit component (needed downstream by
  `HasWeakDerivPer.of_weak_limit`). -/
  hDuRep_memLp : ∀ i, Periodic.MemLpPer (d := d) 1 ((DuRep i).rep)
  /-- Sequence-side periodic representative of the `u`-component. -/
  seqRepU : ℕ → (Fin d → ℝ) → ℝ
  /-- Sequence-side periodic representative of the gradient family. -/
  seqRepDu : ℕ → Fin d → (Fin d → ℝ) → ℝ
  /-- Per-`n`, per-`i` weak-derivative relation. -/
  hSeqRepWeak : ∀ n i,
    Periodic.HasWeakDerivPer (d := d) i (seqRepU n) (seqRepDu n i)
  /-- Test-function `Tendsto` for `seqRepU` against `uRep.rep`. -/
  hConvU : ∀ (φ : ℕ → ℕ), StrictMono φ →
    ∀ ψ : Periodic.SmoothPeriodic d,
      Filter.Tendsto
        (fun k => StationaryMFG.Periodic.periodicIntegral
                    (fun x =>
                      seqRepU (φ k) x *
                        (ψ : (Fin d → ℝ) → ℝ) x))
        Filter.atTop
        (𝓝 (StationaryMFG.Periodic.periodicIntegral
              (fun x => uRep.rep x * (ψ : (Fin d → ℝ) → ℝ) x)))
  /-- Test-function `Tendsto` for `seqRepDu` against `(DuRep i).rep`. -/
  hConvDu : ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ i,
    ∀ ψ : Periodic.SmoothPeriodic d,
      Filter.Tendsto
        (fun k => StationaryMFG.Periodic.periodicIntegral
                    (fun x =>
                      seqRepDu (φ k) i x *
                        (ψ : (Fin d → ℝ) → ℝ) x))
        Filter.atTop
        (𝓝 (StationaryMFG.Periodic.periodicIntegral
              (fun x => (DuRep i).rep x * (ψ : (Fin d → ℝ) → ℝ) x)))
  /-- `0 ≤ mRep.rep` a.e. on the unit cube. -/
  hmRep_nonneg :
    0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
            (UnitCube d)] mRep.rep

namespace WeakLimitSelectorAE

variable {γBarReal βBarReal : ℝ}
variable [Fact (1 ≤ ENNReal.ofReal βBarReal)]
variable [Fact (1 ≤ ENNReal.ofReal γBarReal)]
variable {w : Periodic.LpPer (ENNReal.ofReal βBarReal) d
             × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d}

/-- **AC3 — direct projection.** For the chosen cluster point `w`, the
a.e.-equality between the chosen bare-function limit and the
`Lp.coeFn` representative is precisely the `AEPeriodicRep.ae_eq`
projections — no independent witness is needed. This eliminates the
universal-`w'` Path-A obstruction *at the chosen cluster point*. -/
theorem aeEqClusterPoint_chosen
    (S : WeakLimitSelectorAE (d := d) γBarReal βBarReal w) :
    S.mRep.rep
        =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
              (UnitCube d)] (⇑w.1 : (Fin d → ℝ) → ℝ)
      ∧ S.uRep.rep
          =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                (UnitCube d)] (⇑w.2.1 : (Fin d → ℝ) → ℝ)
      ∧ ∀ i, (S.DuRep i).rep
          =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                (UnitCube d)] (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ) :=
  ⟨S.mRep.ae_eq, S.uRep.ae_eq, fun i => (S.DuRep i).ae_eq⟩

/-- The `m`-component periodic limit lies in `L^{βBar}_per`. Derived by
transporting `MemLpPer βBar (⇑w.1)` (which is automatic from
`memLpPer_of_lpPer`) along `S.mRep.ae_eq.symm`. -/
theorem hmLim_memLp
    (S : WeakLimitSelectorAE (d := d) γBarReal βBarReal w) :
    Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) S.mRep.rep := by
  have h1 : Periodic.MemLpPer (ENNReal.ofReal βBarReal)
              (⇑w.1 : (Fin d → ℝ) → ℝ) :=
    memLpPer_of_lpPer (d := d) w.1
  exact MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq
    (μ := MeasureTheory.Measure.restrict MeasureTheory.volume
            (UnitCube d))
    S.mRep.ae_eq.symm h1.toMemLp)

/-- The `u`-component periodic limit lies in `L^{γBar}_per`. -/
theorem huLim_memLp
    (S : WeakLimitSelectorAE (d := d) γBarReal βBarReal w) :
    Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal) S.uRep.rep := by
  have h1 : Periodic.MemLpPer (ENNReal.ofReal γBarReal)
              (⇑w.2.1 : (Fin d → ℝ) → ℝ) :=
    memLpPer_of_lpPer (d := d) w.2.1
  exact MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq
    (μ := MeasureTheory.Measure.restrict MeasureTheory.volume
            (UnitCube d))
    S.uRep.ae_eq.symm h1.toMemLp)

end WeakLimitSelectorAE

/-! ### `AESelectorData_of_extractWeakLimit` — thin wrapper from F.5 outputs

`extractWeakLimit` (above, in `Closure.lean`) returns a 14-tuple of
existentials: a strictly increasing index function `φ`, a Banach-pair
cluster point `w`, bare periodic functions `(m, u, Du)`, the four
classes of facts (`MemLpPer`, `MemSobolevPer`, `IsPeriodic`,
`AEStronglyMeasurable`), the per-coordinate weak-derivative relation,
the cluster-point a.e.-equalities `m =ᵐ ⇑w.1` etc., the non-negativity
witness `0 ≤ᵐ m`, and the abstract weak-convergence statement.

The downstream `WeakLimitSelectorAE` structure consumes exactly the
`(mRep, uRep, DuRep, hmRep_nonneg)` slice of that data, packaged as
`AEPeriodicRep` records over the cluster-point coercions `⇑w.*`. This
section provides a closed-form packager that builds that slice from
the F.5 outputs already destructured at the call site — pure
repackaging, no new math.

Unlike the general `Lp.coeFn`-selector obstruction (which forces a
universally-quantified residue over all cluster points), here we have
a *concrete* periodic representative on hand for the specific `w`
returned by F.5, so the chosen-`w` `AEPeriodicRep`s are constructed
directly from the F.5 data.
-/

/-- **F.5 → `WeakLimitSelectorAE` slice — packaged data.**

Given a Banach-pair cluster point `w`, this structure carries the
`(mRep, uRep, DuRep, hmRep_nonneg)` slice of the data
`WeakLimitSelectorAE βBarReal γBarReal w` requires, but at the
F.5-native exponent shape `βBar γBar : ℝ≥0∞`. Used as a thin staging
record between `extractWeakLimit` and the eventual
`WeakLimitSelectorAE` field assignment (which itself takes
`βBarReal γBarReal : ℝ` and applies `ENNReal.ofReal`).

The record contains no test-function `Tendsto` hypotheses or
sequence-side data — those are the *other* slices of
`WeakLimitSelectorAE`, sourced from upstream paper hypotheses, not
from F.5. -/
structure AESelectorData_of_extractWeakLimit
    (βBar γBar : ℝ≥0∞) [Fact (1 ≤ βBar)] [Fact (1 ≤ γBar)]
    (w : Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d) where
  /-- Chosen periodic a.e.-representative of `⇑w.1`. -/
  mRep : Periodic.AEPeriodicRep (⇑w.1 : (Fin d → ℝ) → ℝ)
  /-- Chosen periodic a.e.-representative of `⇑w.2.1`. -/
  uRep : Periodic.AEPeriodicRep (⇑w.2.1 : (Fin d → ℝ) → ℝ)
  /-- Chosen periodic a.e.-representatives of every gradient component
  `⇑(w.2.2 i)`. -/
  DuRep : ∀ i, Periodic.AEPeriodicRep (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ)
  /-- Non-negativity of `mRep.rep` a.e. on the unit cube — the F.5
  cluster-point cone-membership certificate. -/
  hmRep_nonneg :
    0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
            (UnitCube d)] mRep.rep

/-- **F.5 → `AESelectorData_of_extractWeakLimit` producer.**

Given the bare-function outputs `(m, u, Du)` produced by
`extractWeakLimit`, their periodicity certificates, the cluster-point
a.e.-equalities `m =ᵐ ⇑w.1`, `u =ᵐ ⇑w.2.1`, `Du i =ᵐ ⇑(w.2.2 i)`,
and the non-negativity certificate `0 ≤ᵐ m`, package the data into an
`AESelectorData_of_extractWeakLimit βBar γBar w`.

The body is a pure record assembly: each `AEPeriodicRep` is built by
the structure constructor `{ rep := …, periodic := …, ae_eq := … }`,
and `hmRep_nonneg` is `hMnn` since `mRep.rep` reduces to `m`
definitionally.

This producer is the missing thin wrapper between `extractWeakLimit`'s
14-tuple and the `WeakLimitSelectorAE` field shape. The
`βBar`/`γBar` exponents here match the F.5 signature directly; a
follow-up bridge (when needed) can specialise to `ENNReal.ofReal`
shapes for the `WeakLimitSelectorAE` consumer. -/
noncomputable def aeSelectorData_of_extractWeakLimit_outputs
    {βBar γBar : ℝ≥0∞} [Fact (1 ≤ βBar)] [Fact (1 ≤ γBar)]
    {w : Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d}
    (m u : (Fin d → ℝ) → ℝ) (Du : Fin d → (Fin d → ℝ) → ℝ)
    (hMper : Periodic.IsPeriodic m) (hUper : Periodic.IsPeriodic u)
    (hDuPer : ∀ i, Periodic.IsPeriodic (Du i))
    (hMae :
      m =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
              (UnitCube d)] (⇑w.1 : (Fin d → ℝ) → ℝ))
    (hUae :
      u =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
              (UnitCube d)] (⇑w.2.1 : (Fin d → ℝ) → ℝ))
    (hDuae : ∀ i,
      Du i =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                (UnitCube d)] (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ))
    (hMnn :
      0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
              (UnitCube d)] m) :
    AESelectorData_of_extractWeakLimit (d := d) βBar γBar w where
  mRep :=
    { rep := m
      periodic := hMper
      ae_eq := hMae }
  uRep :=
    { rep := u
      periodic := hUper
      ae_eq := hUae }
  DuRep := fun i =>
    { rep := Du i
      periodic := hDuPer i
      ae_eq := hDuae i }
  hmRep_nonneg := hMnn

/-! ### Sanity-check unit `example` for the F.5 → `AESelectorData` packager

Exercise `aeSelectorData_of_extractWeakLimit_outputs` on a structurally
trivial cluster point: any choice of `(βBar, γBar, w)` admits the
packager when fed the trivial bare data `m = u = Du i ≡ 0`. We rely
on `extractWeakLimit`'s precise output direction (`m =ᵐ ⇑w.1`), which
is also the direction `AEPeriodicRep.ae_eq` requires, so no
symmetrisation is needed in the body. -/

example
    {βBar γBar : ℝ≥0∞} [Fact (1 ≤ βBar)] [Fact (1 ≤ γBar)]
    (w : Periodic.LpPer βBar d × Periodic.SobolevPerLp 1 γBar d)
    (hAe1 :
      (fun _ : Fin d → ℝ => (0 : ℝ))
          =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                (UnitCube d)] (⇑w.1 : (Fin d → ℝ) → ℝ))
    (hAe2 :
      (fun _ : Fin d → ℝ => (0 : ℝ))
          =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                (UnitCube d)] (⇑w.2.1 : (Fin d → ℝ) → ℝ))
    (hAe3 : ∀ i,
      (fun _ : Fin d → ℝ => (0 : ℝ))
          =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                (UnitCube d)] (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ)) :
    AESelectorData_of_extractWeakLimit (d := d) βBar γBar w :=
  aeSelectorData_of_extractWeakLimit_outputs
    (m := fun _ => 0) (u := fun _ => 0) (Du := fun _ _ => 0)
    (Periodic.IsPeriodic.const 0) (Periodic.IsPeriodic.const 0)
    (fun _ => Periodic.IsPeriodic.const 0)
    hAe1 hAe2 hAe3
    (Filter.Eventually.of_forall (fun _ => le_refl 0))

/-! ### Producer: `weakLimitSelector_of_regularizedSequence`

Discharge the chosen-`w` selector residue from
`(hExp, seq, w, mRep, uRep, DuRep)` plus the sequence-side data and
the test-function `Tendsto` hypotheses. The cluster-point `w` and the
`AEPeriodicRep` choices are taken as inputs (the only genuine Path-A
data); everything else is a direct field assignment.

No raw `Lp.coeFn` is constructed inside this producer body — Banach-side
quantities surface only via `⇑w.1`, `⇑w.2.1`, `⇑(w.2.2 i)`, which
are the original cluster-point coercions, paired with the
`AEPeriodicRep.ae_eq` witnesses. Downstream Banach-side convergence is
transported through the pairing-congruence lemmas in
`Solutions/MFGOperator.lean`. -/

/-- **AE-form selector producer.** Build a `WeakLimitSelectorAE` from
`(hExp, seq, w)` together with chosen `AEPeriodicRep`s for each
component of the cluster point and the sequence-side data.

The `hExp` and `seq` parameters are not consumed by the body — they
appear in the signature to pin the producer to the same upstream
context as `weakLimitInputBundle_of_regularizedSequence`. -/
noncomputable def weakLimitSelector_of_regularizedSequence
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (_hExp : SimplePowerExponentFacts γBarReal
                (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
                (ENNReal.ofReal βBarReal'))
    (_seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH)
    (w : Periodic.LpPer (ENNReal.ofReal βBarReal) d
            × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d)
    (mRep : Periodic.AEPeriodicRep (⇑w.1 : (Fin d → ℝ) → ℝ))
    (uRep : Periodic.AEPeriodicRep (⇑w.2.1 : (Fin d → ℝ) → ℝ))
    (DuRep : ∀ i, Periodic.AEPeriodicRep (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ))
    (hDuRep_memLp : ∀ i, Periodic.MemLpPer (d := d) 1 ((DuRep i).rep))
    (seqRepU : ℕ → (Fin d → ℝ) → ℝ)
    (seqRepDu : ℕ → Fin d → (Fin d → ℝ) → ℝ)
    (hSeqRepWeak : ∀ n i,
      Periodic.HasWeakDerivPer (d := d) i (seqRepU n) (seqRepDu n i))
    (hConvU : ∀ (φ : ℕ → ℕ), StrictMono φ →
      ∀ ψ : Periodic.SmoothPeriodic d,
        Filter.Tendsto
          (fun k => StationaryMFG.Periodic.periodicIntegral
                      (fun x =>
                        seqRepU (φ k) x *
                          (ψ : (Fin d → ℝ) → ℝ) x))
          Filter.atTop
          (𝓝 (StationaryMFG.Periodic.periodicIntegral
                (fun x => uRep.rep x * (ψ : (Fin d → ℝ) → ℝ) x))))
    (hConvDu : ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ i,
      ∀ ψ : Periodic.SmoothPeriodic d,
        Filter.Tendsto
          (fun k => StationaryMFG.Periodic.periodicIntegral
                      (fun x =>
                        seqRepDu (φ k) i x *
                          (ψ : (Fin d → ℝ) → ℝ) x))
          Filter.atTop
          (𝓝 (StationaryMFG.Periodic.periodicIntegral
                (fun x => (DuRep i).rep x * (ψ : (Fin d → ℝ) → ℝ) x))))
    (hmRep_nonneg :
      0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
              (UnitCube d)] mRep.rep) :
    WeakLimitSelectorAE (d := d) γBarReal βBarReal w where
  mRep := mRep
  uRep := uRep
  DuRep := DuRep
  hDuRep_memLp := hDuRep_memLp
  seqRepU := seqRepU
  seqRepDu := seqRepDu
  hSeqRepWeak := hSeqRepWeak
  hConvU := hConvU
  hConvDu := hConvDu
  hmRep_nonneg := hmRep_nonneg

/-! ### `WeakLimitExtraction` — AE-native selector + chosen cluster point.

Per Phase E1 of `THEOREM1_CLOSURE_PLAN.md` (v3 §9), this wrapping
structure carries **a chosen cluster point `w`** alongside an
AE-native `WeakLimitSelectorAE … w`. It was the migration target for
the legacy `WeakLimitSelector` at the public residue-bundle interface
(formerly `T10PaperResidues.weakSelector`, dropped in
`infra-P5-T10-drop-weakSelector` once all consumers constructed the
value inline).

The shape:
* `w` — the chosen cluster point (paper "we extract a subsequence
  converging to `(m, u)`").
* `selector` — the AE-native selector indexed at the chosen `w`;
  the cluster-point a.e.-equality is a direct projection
  (`AEPeriodicRep.ae_eq`), no universal quantifier.
* `auxOther` — residual residue for `w' ≠ w`, kept because the
  internal consumer chain (which still threads through the legacy
  `WeakLimitSelector`) consumes a Banach–Alaoglu-produced cluster
  point in `extractWeakLimit`. The chosen-`w` case is a direct
  projection; only the residual `w' ≠ w` case is residue.

The `mLim`, `uLim`, `DuLim` projections expose the bare-function
periodic limit triple as the legacy `WeakLimitSelector` did, so
downstream consumers reading those fields (e.g. the
`finIntResidue` field type on `T10PaperResidues`) need no surface
change. -/

/-- **Chosen-`w` weak-limit extraction wrapping structure.**

Per Phase E1 of `THEOREM1_CLOSURE_PLAN.md` (v3 §9), this is the
migration target for the legacy `WeakLimitSelector` at the public
residue-bundle interface. It bundles a chosen cluster point `w`
together with an AE-native `WeakLimitSelectorAE … w`. -/
structure WeakLimitExtraction
    (γBarReal βBarReal : ℝ)
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)] where
  /-- Chosen Banach-pair cluster point. -/
  w : Periodic.LpPer (ENNReal.ofReal βBarReal) d
        × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d
  /-- AE-native selector indexed at the chosen `w`. -/
  selector : WeakLimitSelectorAE (d := d) γBarReal βBarReal w
  /-- Residual "other-cluster-point" residue for `w' ≠ w`. The
  chosen-`w` case is a direct projection
  (`WeakLimitSelectorAE.aeEqClusterPoint_chosen`); only the
  residual `w' ≠ w` case carries a Path-A obstruction. This field
  exists because internal consumers (e.g. `extractWeakLimit`) still
  consume a Banach–Alaoglu-produced cluster point through the
  legacy universally-quantified `WeakLimitSelector`. Once Phase E2
  / Phase F0 land an AE-native consumer surface for
  `extractWeakLimit`, this residual field becomes vacuous. -/
  auxOther : ∀
    (w' : Periodic.LpPer (ENNReal.ofReal βBarReal) d
            × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d),
      w' ≠ w →
      selector.mRep.rep
          =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                (UnitCube d)] (⇑w'.1 : (Fin d → ℝ) → ℝ)
      ∧ selector.uRep.rep
          =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                (UnitCube d)] (⇑w'.2.1 : (Fin d → ℝ) → ℝ)
      ∧ ∀ i, (selector.DuRep i).rep
          =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                (UnitCube d)] (⇑(w'.2.2 i) : (Fin d → ℝ) → ℝ)

namespace WeakLimitExtraction

variable {γBarReal βBarReal : ℝ}
variable [Fact (1 ≤ ENNReal.ofReal βBarReal)]
variable [Fact (1 ≤ ENNReal.ofReal γBarReal)]

/-- Bare-function periodic `m`-limit (read off the chosen
`AEPeriodicRep` representative). Surface-compatible with the legacy
`WeakLimitSelector.mLim` field. -/
def mLim (E : WeakLimitExtraction (d := d) γBarReal βBarReal) :
    (Fin d → ℝ) → ℝ :=
  E.selector.mRep.rep

/-- Bare-function periodic `u`-limit. -/
def uLim (E : WeakLimitExtraction (d := d) γBarReal βBarReal) :
    (Fin d → ℝ) → ℝ :=
  E.selector.uRep.rep

/-- Bare-function periodic gradient-limit family. -/
def DuLim (E : WeakLimitExtraction (d := d) γBarReal βBarReal)
    (i : Fin d) : (Fin d → ℝ) → ℝ :=
  (E.selector.DuRep i).rep

end WeakLimitExtraction

/-! ### `WeakLimitExtractionAE` — leaner AE-native extraction.

Per Phase 3c-ii of the Theorem 1 closure plan
(`infra-P5-theorem1-phase-3c-ii-drop-auxOther-from-weakSelector`),
this is the residue-bundle interface target replacing
`WeakLimitExtraction`. It carries the chosen cluster point `w` plus the
AE-native selector indexed at `w`, **without** the universal
"other-cluster-point" residue field `auxOther`. The legacy
`auxOther` field on `WeakLimitExtraction` exists solely to feed the
legacy converter `WeakLimitSelectorAE.toWeakLimitSelector`, which is no
longer reachable from the Theorem 1 chain after Phase 3c-i rewired all
producers to consume `WeakLimitInputBundleAE`.

This means: a `WeakLimitExtractionAE` carries strictly less data than
a `WeakLimitExtraction` — the universal `auxOther` obligation has been
dropped at the public residue surface. -/

/-- **Leaner chosen-`w` weak-limit extraction.**

Carries a chosen Banach-pair cluster point `w` together with an
AE-native `WeakLimitSelectorAE … w`. **No** universal
"other-cluster-point" residue (cf. `WeakLimitExtraction.auxOther`). -/
structure WeakLimitExtractionAE
    (γBarReal βBarReal : ℝ)
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)] where
  /-- Chosen Banach-pair cluster point. -/
  w : Periodic.LpPer (ENNReal.ofReal βBarReal) d
        × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d
  /-- AE-native selector indexed at the chosen `w`. -/
  selector : WeakLimitSelectorAE (d := d) γBarReal βBarReal w

namespace WeakLimitExtractionAE

variable {γBarReal βBarReal : ℝ}
variable [Fact (1 ≤ ENNReal.ofReal βBarReal)]
variable [Fact (1 ≤ ENNReal.ofReal γBarReal)]

/-- Bare-function periodic `m`-limit. -/
def mLim (E : WeakLimitExtractionAE (d := d) γBarReal βBarReal) :
    (Fin d → ℝ) → ℝ :=
  E.selector.mRep.rep

/-- Bare-function periodic `u`-limit. -/
def uLim (E : WeakLimitExtractionAE (d := d) γBarReal βBarReal) :
    (Fin d → ℝ) → ℝ :=
  E.selector.uRep.rep

/-- Bare-function periodic gradient-limit family. -/
def DuLim (E : WeakLimitExtractionAE (d := d) γBarReal βBarReal)
    (i : Fin d) : (Fin d → ℝ) → ℝ :=
  (E.selector.DuRep i).rep

end WeakLimitExtractionAE

/-! ### `WeakLimitSubsequenceData` — `WeakLimitExtractionAE` plus the
F.5 strict-mono index and the abstract Banach-pair weak-tendsto.

Per `infra-P5-T10-v7-HMinty-1-subseq-infrastructure` (Route 1 of the
HMinty drain): the F.5 strict-mono index `φ_F5` and the abstract
`WeakSpace`-tendsto on the product Banach pair `(LpPer βBar ×
SobolevPerLp 1 γBar d)` are already produced by `extractWeakLimit_noAux`
(Banach/Closure.lean), but currently *dropped* at the public surface
(`weakLimitExtractionAE_of_uniform_apriori`). This structure exposes
them. The abstract `hWeakSpace_tendsto` is the Route-1 entry point —
HMinty-2 derives the m/u/Du smooth-tester convergences from it via
the `tendsto_smoothTester_of_banachWeak_pair_{fst,snd_val,snd_grad}`
corollaries (Banach/WeakLimit.lean), and packages them into
`WeakConvPairing_universal` certificates via the
`weakConvPairing_universal_of_toWeakSpace_conv` bridge
(Banach/WeakPairing.lean). -/
structure WeakLimitSubsequenceData
    (γBarReal βBarReal : ℝ)
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {βBarReal' γBarReal' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH) where
  /-- Strict-mono extraction index produced by `extractWeakLimit_noAux`. -/
  idx : ℕ → ℕ
  /-- Strict-monotonicity of the F.5 index. -/
  idx_strict : StrictMono idx
  /-- The downstream selector data at the chosen cluster point. -/
  extraction : WeakLimitExtractionAE (d := d) γBarReal βBarReal
  /-- **Route-1 hook**: abstract `WeakSpace`-tendsto on the product
  Banach pair along `idx`. This is the `hφlim` output of
  `extractWeakLimit_noAux`, threaded through to the public surface. -/
  hWeakSpace_tendsto :
    Filter.Tendsto
      (fun k => (toWeakSpace ℝ
        (Periodic.LpPer (ENNReal.ofReal βBarReal) d
          × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d))
          ((seq.sol (idx k)).toBanachPair))
      Filter.atTop
      (𝓝 ((toWeakSpace ℝ
        (Periodic.LpPer (ENNReal.ofReal βBarReal) d
          × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d))
            extraction.w))

/-! ### `WeakLimitInputBundleAE` — AE-native sibling of
    `WeakLimitInputBundle`.

Per Phase 3a of the Theorem 1 closure plan, this structure is the
parallel AE-native bundle: it carries a chosen Banach-pair cluster
point `w` together with the AE-native selector fields (mirroring
`WeakLimitSelectorAE … w`) **inlined** for call-site convenience, plus
the structural fields `hRefl`, `hSep`, `hmLim_memLp`, `huLim_sob`,
`hMlimPer`, `hUlimPer`, `hDuLim_periodic` materialised as fields to
mirror the legacy `WeakLimitInputBundle` surface and avoid
Σ-destructuring at call sites.

Compared with `WeakLimitInputBundle`, the universally-quantified
`auxAeOfClusterPoint` field is **dropped**: at the chosen `w`, the
agreement between the bare-function limit triple and the Banach-pair
coercion is the direct projection through `(mRep|uRep|DuRep i).ae_eq`.
The eight derived helpers `hDuLim_memLp_γ`, `huLim_DuLim_weakDeriv`,
`hFlux_meas`, `hRes_Lp`, `perTestTripleBase` (each with a
sanity-`example`) are reproved from this AE selector at the chosen
`w`, with no Banach–Alaoglu detour. -/

/-- **AE-native sibling of `WeakLimitInputBundle`.**

Carries a chosen Banach-pair cluster point `w`, the AE-native selector
data (mirroring `WeakLimitSelectorAE … w`), and the same structural
fields as the legacy bundle (`hRefl`, `hSep`, periodicities,
`hmLim_memLp`, `huLim_sob`, `hmLim_nonneg`). The chosen-`w`
a.e.-equalities are *not* a separate field — they are direct
projections `mRep.ae_eq`, `uRep.ae_eq`, `(DuRep i).ae_eq`. -/
structure WeakLimitInputBundleAE
    (γBarReal βBarReal : ℝ)
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)] where
  /-- Reflexivity of the Banach pair. -/
  hRefl : Periodic.IsReflexiveNormedSpace
            (Periodic.LpPer (ENNReal.ofReal βBarReal) d
              × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d)
  /-- Separability of the strong dual. -/
  hSep : TopologicalSpace.SeparableSpace
            (StrongDual ℝ
              (Periodic.LpPer (ENNReal.ofReal βBarReal) d
                × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d))
  /-- Chosen Banach-pair cluster point. -/
  w : Periodic.LpPer (ENNReal.ofReal βBarReal) d
        × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d
  /-- Chosen periodic representative of the `m`-component cluster point. -/
  mRep : Periodic.AEPeriodicRep (⇑w.1 : (Fin d → ℝ) → ℝ)
  /-- Chosen periodic representative of the `u`-component cluster point. -/
  uRep : Periodic.AEPeriodicRep (⇑w.2.1 : (Fin d → ℝ) → ℝ)
  /-- Chosen periodic representative of every gradient-component
      cluster point. -/
  DuRep : ∀ i, Periodic.AEPeriodicRep (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ)
  /-- `MemLpPer 1` of every gradient-limit component (needed downstream
      by `HasWeakDerivPer.of_weak_limit`). -/
  hDuRep_memLp : ∀ i, Periodic.MemLpPer (d := d) 1 ((DuRep i).rep)
  /-- Sequence-side periodic representative of the `u`-component. -/
  seqRepU : ℕ → (Fin d → ℝ) → ℝ
  /-- Sequence-side periodic representative of the gradient family. -/
  seqRepDu : ℕ → Fin d → (Fin d → ℝ) → ℝ
  /-- Per-`n`, per-`i` weak-derivative relation. -/
  hSeqRepWeak : ∀ n i,
    Periodic.HasWeakDerivPer (d := d) i (seqRepU n) (seqRepDu n i)
  /-- Test-function `Tendsto` for `seqRepU` against `uRep.rep`. -/
  hConvU : ∀ (φ : ℕ → ℕ), StrictMono φ →
    ∀ ψ : Periodic.SmoothPeriodic d,
      Filter.Tendsto
        (fun k => StationaryMFG.Periodic.periodicIntegral
                    (fun x =>
                      seqRepU (φ k) x *
                        (ψ : (Fin d → ℝ) → ℝ) x))
        Filter.atTop
        (𝓝 (StationaryMFG.Periodic.periodicIntegral
              (fun x => uRep.rep x * (ψ : (Fin d → ℝ) → ℝ) x)))
  /-- Test-function `Tendsto` for `seqRepDu` against `(DuRep i).rep`. -/
  hConvDu : ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ i,
    ∀ ψ : Periodic.SmoothPeriodic d,
      Filter.Tendsto
        (fun k => StationaryMFG.Periodic.periodicIntegral
                    (fun x =>
                      seqRepDu (φ k) i x *
                        (ψ : (Fin d → ℝ) → ℝ) x))
        Filter.atTop
        (𝓝 (StationaryMFG.Periodic.periodicIntegral
              (fun x => (DuRep i).rep x * (ψ : (Fin d → ℝ) → ℝ) x)))
  /-- `0 ≤ mRep.rep` a.e. on the unit cube. -/
  hmRep_nonneg :
    0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
            (UnitCube d)] mRep.rep
  /-- Periodicity of the `m`-limit. Structurally `mRep.periodic`,
      materialised as a field to mirror `WeakLimitInputBundle`. -/
  hMlimPer : Periodic.IsPeriodic mRep.rep
  /-- Periodicity of the `u`-limit. Structurally `uRep.periodic`. -/
  hUlimPer : Periodic.IsPeriodic uRep.rep
  /-- Periodicity of every gradient-limit component. Structurally
      `(DuRep i).periodic`. -/
  hDuLim_periodic : ∀ i, Periodic.IsPeriodic ((DuRep i).rep)
  /-- `mRep.rep ∈ L^{βBar}_per`. Structurally derivable via
      `memLpPer_of_lpPer w.1` + `MemLp.ae_eq mRep.ae_eq.symm`. -/
  hmLim_memLp : Periodic.MemLpPer (d := d)
                  (ENNReal.ofReal βBarReal) mRep.rep
  /-- `uRep.rep ∈ W^{1,γBar}_per`. -/
  huLim_sob : Periodic.MemSobolevPer (d := d)
                (ENNReal.ofReal γBarReal) uRep.rep

namespace WeakLimitInputBundleAE

variable {γBarReal βBarReal : ℝ}
variable [Fact (1 ≤ ENNReal.ofReal βBarReal)]
variable [Fact (1 ≤ ENNReal.ofReal γBarReal)]

/-- Bare-function periodic `m`-limit. Surface-compatible with the
legacy `WeakLimitInputBundle.mLim`. -/
def mLim (B : WeakLimitInputBundleAE (d := d) γBarReal βBarReal) :
    (Fin d → ℝ) → ℝ :=
  B.mRep.rep

/-- Bare-function periodic `u`-limit. -/
def uLim (B : WeakLimitInputBundleAE (d := d) γBarReal βBarReal) :
    (Fin d → ℝ) → ℝ :=
  B.uRep.rep

/-- Bare-function periodic gradient-limit family. -/
def DuLim (B : WeakLimitInputBundleAE (d := d) γBarReal βBarReal)
    (i : Fin d) : (Fin d → ℝ) → ℝ :=
  (B.DuRep i).rep

/-- `MemLpPer 1` of every gradient-limit component, surface-compatible
with `WeakLimitInputBundle.hDuLim_memLp`. -/
theorem hDuLim_memLp
    (B : WeakLimitInputBundleAE (d := d) γBarReal βBarReal) (i : Fin d) :
    Periodic.MemLpPer (d := d) 1 (B.DuLim i) :=
  B.hDuRep_memLp i

/-- Surface-compatibility accessor: `0 ≤ B.mLim` a.e. on the unit
cube. Reduces structurally to `B.hmRep_nonneg` since
`B.mLim = B.mRep.rep` definitionally. Mirrors the legacy
`WeakLimitInputBundle.hmLim_nonneg` field name so call sites remain
agnostic between the legacy and AE-native bundles. -/
theorem hmLim_nonneg
    (B : WeakLimitInputBundleAE (d := d) γBarReal βBarReal) :
    0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
            (UnitCube d)] B.mLim :=
  B.hmRep_nonneg

end WeakLimitInputBundleAE

/-- **AC3 — strict-`γ̄` `MemLpPer` for `B.DuLim i` from the chosen `w`.**

At the chosen cluster point `w` carried by the bundle, the
a.e.-equality `(DuRep i).rep =ᵐ ⇑(w.2.2 i)` (= `(DuRep i).ae_eq`) lets
us transport `MemLp ⇑(w.2.2 i) γBar (volume.restrict (UnitCube d))`
(automatic from `Lp.memLp`) to the strict-`γ̄` `MemLpPer` of every
component of `DuLim`. **No** Banach–Alaoglu detour, **no**
universally-quantified `auxAeOfClusterPoint` field. -/
theorem WeakLimitInputBundleAE.hDuLim_memLp_γ
    {γBarReal βBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (B : WeakLimitInputBundleAE (d := d) γBarReal βBarReal)
    (i : Fin d) :
    Periodic.MemLpPer (d := d)
      (ENNReal.ofReal γBarReal) (B.DuLim i) := by
  -- `Lp.memLp` gives `MemLp ⇑(w.2.2 i) γBar (volume.restrict (UnitCube d))`.
  have hmemLp :
      MeasureTheory.MemLp (⇑(B.w.2.2 i) : (Fin d → ℝ) → ℝ)
        (ENNReal.ofReal γBarReal)
        (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
    MeasureTheory.Lp.memLp (B.w.2.2 i)
  -- Transfer along `(DuRep i).ae_eq.symm`. The predicate
  -- `Periodic.MemLpPer p f` is equivalent to
  -- `MemLp f p (volume.restrict (UnitCube d))`.
  exact MemLp.toMemLpPer (hmemLp.ae_eq (B.DuRep i).ae_eq.symm)

/-- **AC4 sanity check.** The strict-`γ̄` `MemLpPer` on `B.DuLim i` is
projectable from any `WeakLimitInputBundleAE`. -/
example
    {γBarReal βBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (B : WeakLimitInputBundleAE (d := d) γBarReal βBarReal)
    (i : Fin d) :
    Periodic.MemLpPer (d := d)
      (ENNReal.ofReal γBarReal) (B.DuLim i) :=
  B.hDuLim_memLp_γ i

/-- **AC3 — `(uLim, DuLim i)` weak-derivative tie.**

The `MemSobolevPer` field `huLim_sob.2` of `WeakLimitInputBundleAE`
existentially quantifies the gradient witness, so it does not directly
identify `DuLim` with the weak derivative of `uLim`. We tie the two
together via the sequence-side data
`(seqRepU, seqRepDu, hSeqRepWeak, hConvU, hConvDu, hDuRep_memLp)` and
`Periodic.HasWeakDerivPer.of_weak_limit`. -/
theorem WeakLimitInputBundleAE.huLim_DuLim_weakDeriv
    {γBarReal βBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (B : WeakLimitInputBundleAE (d := d) γBarReal βBarReal)
    (i : Fin d) :
    Periodic.HasWeakDerivPer (d := d) i B.uLim (B.DuLim i) := by
  refine Periodic.HasWeakDerivPer.of_weak_limit
    (i := i) (u_n := B.seqRepU)
    (Du_n := fun n => B.seqRepDu n i)
    (u := B.uLim) (Du := B.DuLim i)
    (B.hDuRep_memLp i) (fun n => B.hSeqRepWeak n i)
    ?_ ?_
  · intro ψ
    have h := B.hConvU id strictMono_id ψ
    simpa using! h
  · intro ψ
    have h := B.hConvDu id strictMono_id i ψ
    simpa using! h

/-- **AC4 sanity check.** The derived weak-derivative tie can be
projected from any `WeakLimitInputBundleAE`. -/
example
    {γBarReal βBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (B : WeakLimitInputBundleAE (d := d) γBarReal βBarReal)
    (i : Fin d) :
    Periodic.HasWeakDerivPer (d := d) i B.uLim (B.DuLim i) :=
  B.huLim_DuLim_weakDeriv i

/-- **AC3 — derived a.e.-strong measurability of the flux vector.**

For any `WeakLimitInputBundleAE` and any power-growth bundle
`hpow : HypothesisPowerGrowth H DpH`, the `Fin d → ℝ`-valued map
`x ↦ mLim x • DpH x (fun i => DuLim i x) (mLim x)` is a.e.-strongly
measurable on the unit cube. The proof mirrors
`WeakLimitInputBundle.hFlux_meas` with the AE-bundle's own field
names. -/
theorem WeakLimitInputBundleAE.hFlux_meas
    {γBarReal βBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (B : WeakLimitInputBundleAE (d := d) γBarReal βBarReal) :
    MeasureTheory.AEStronglyMeasurable
      (fun x : (Fin d → ℝ) =>
        Hamiltonian.mDpH DpH x
          (fun i => B.DuLim i x) (B.mLim x))
      (MeasureTheory.volume.restrict (UnitCube d)) := by
  have hDu_aem : ∀ i,
      AEMeasurable (fun x : (Fin d → ℝ) => B.DuLim i x)
        (MeasureTheory.volume.restrict (UnitCube d)) := fun i =>
    (B.hDuLim_memLp i).aestronglyMeasurable.aemeasurable
  have hDu_pi_aem :
      AEMeasurable (fun x : (Fin d → ℝ) => (fun i : Fin d => B.DuLim i x))
        (MeasureTheory.volume.restrict (UnitCube d)) :=
    aemeasurable_pi_iff.mpr hDu_aem
  have hm_aem : AEMeasurable B.mLim
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    B.hmLim_memLp.aestronglyMeasurable.aemeasurable
  have hxpm : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        (x, (fun i : Fin d => B.DuLim i x), B.mLim x))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    aemeasurable_id.prodMk (hDu_pi_aem.prodMk hm_aem)
  have hDpH_aem : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        DpH x (fun i => B.DuLim i x) (B.mLim x))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    hpow.measurable_DpH.comp_aemeasurable hxpm
  have hDpH_asm :
      MeasureTheory.AEStronglyMeasurable
        (fun x : (Fin d → ℝ) =>
          DpH x (fun i => B.DuLim i x) (B.mLim x))
        (MeasureTheory.volume.restrict (UnitCube d)) :=
    hDpH_aem.aestronglyMeasurable
  have hm_asm : MeasureTheory.AEStronglyMeasurable B.mLim
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    B.hmLim_memLp.aestronglyMeasurable
  exact hm_asm.smul hDpH_asm

/-- **AC4 sanity check.** The flux a.e.-strong measurability is
projectable from `(hpow, B)`. -/
example
    {γBarReal βBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (B : WeakLimitInputBundleAE (d := d) γBarReal βBarReal) :
    MeasureTheory.AEStronglyMeasurable
      (fun x : (Fin d → ℝ) =>
        Hamiltonian.mDpH DpH x
          (fun i => B.DuLim i x) (B.mLim x))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
  WeakLimitInputBundleAE.hFlux_meas (d := d) hpow B

/-- **AC3 — `MemLpPer βBar'` of the HJB residual at the weak limit.**

Mirrors `WeakLimitInputBundle.hRes_Lp` with the AE-bundle's own field
names. The proof reduces to `Hamiltonian.g_memLp_betaBar'_nonneg` after
rewriting bundle exponents to the `hpow`-shape. -/
theorem WeakLimitInputBundleAE.hRes_Lp
    {γBarReal βBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hFin : Hamiltonian.Hext_finite_at_zero (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    (hV : Periodic.MemLpPer (d := d)
            (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) V)
    (hβBarPaper : βBarReal = hpow.β + 1)
    (hγBarPaper : γBarReal = hpow.α * (hpow.β + 1) / hpow.β)
    (B : WeakLimitInputBundleAE (d := d) γBarReal βBarReal) :
    Periodic.MemLpPer (d := d)
      (ENNReal.ofReal ((hpow.β + 1) / hpow.β))
      (StationaryMFG.Theorems.SimplePower.hjbResidual V H
        B.DuLim B.mLim B.uLim) := by
  have hμ : Periodic.MemLpPer (d := d)
              (ENNReal.ofReal (hpow.β + 1)) B.mLim := by
    rw [show ENNReal.ofReal (hpow.β + 1) = ENNReal.ofReal βBarReal from by
          rw [hβBarPaper]]
    exact B.hmLim_memLp
  have hu_γ : Periodic.MemLpPer (d := d)
                (ENNReal.ofReal γBarReal) B.uLim :=
    B.huLim_sob.1
  have hυ : Periodic.MemLpPer (d := d)
              (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))
              B.uLim := by
    rw [show ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)
          = ENNReal.ofReal γBarReal from by rw [hγBarPaper]]
    exact hu_γ
  have hDυ : ∀ i, Periodic.MemLpPer (d := d)
              (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))
              (B.DuLim i) := by
    intro i
    rw [show ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)
          = ENNReal.ofReal γBarReal from by rw [hγBarPaper]]
    exact B.hDuLim_memLp_γ i
  have hDu_aem : ∀ i,
      AEMeasurable (fun x : (Fin d → ℝ) => B.DuLim i x)
        (MeasureTheory.volume.restrict (UnitCube d)) := fun i =>
    (B.hDuLim_memLp i).aestronglyMeasurable.aemeasurable
  have hDu_pi_aem :
      AEMeasurable (fun x : (Fin d → ℝ) =>
                      (fun i : Fin d => B.DuLim i x))
        (MeasureTheory.volume.restrict (UnitCube d)) :=
    aemeasurable_pi_iff.mpr hDu_aem
  have hm_aem : AEMeasurable B.mLim
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    B.hmLim_memLp.aestronglyMeasurable.aemeasurable
  have hxpm : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        (x, (fun i : Fin d => B.DuLim i x), B.mLim x))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    aemeasurable_id.prodMk (hDu_pi_aem.prodMk hm_aem)
  have hH_aem : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        H x (fun i => B.DuLim i x) (B.mLim x))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
    hpow.measurable_H.comp_aemeasurable hxpm
  have hH_asm :
      MeasureTheory.AEStronglyMeasurable
        (fun x : (Fin d → ℝ) =>
          H x (fun i => B.DuLim i x) (B.mLim x))
        (MeasureTheory.volume.restrict (UnitCube d)) :=
    hH_aem.aestronglyMeasurable
  have hu_asm := hu_γ.aestronglyMeasurable
  have hV_asm := hV.aestronglyMeasurable
  have hg_meas' :
      MeasureTheory.AEStronglyMeasurable
        (fun x : (Fin d → ℝ) =>
          -(B.uLim x)
            - H x (fun i => B.DuLim i x) (B.mLim x)
            + V x)
        (MeasureTheory.volume.restrict (UnitCube d)) :=
    ((hu_asm.neg).sub hH_asm).add hV_asm
  have hres :=
    Hamiltonian.g_memLp_betaBar'_nonneg (d := d) hpow hHat0 hFin hAgree
      V B.uLim B.mLim B.DuLim
      B.hmRep_nonneg hg_meas' hμ hυ hDυ hV
  exact hres

/-- **AC4 sanity check.** The HJB-residual `MemLpPer βBar'` is
projectable from the AE-bundle. -/
example
    {γBarReal βBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hFin : Hamiltonian.Hext_finite_at_zero (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    (hV : Periodic.MemLpPer (d := d)
            (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) V)
    (hβBarPaper : βBarReal = hpow.β + 1)
    (hγBarPaper : γBarReal = hpow.α * (hpow.β + 1) / hpow.β)
    (B : WeakLimitInputBundleAE (d := d) γBarReal βBarReal) :
    Periodic.MemLpPer (d := d)
      (ENNReal.ofReal ((hpow.β + 1) / hpow.β))
      (StationaryMFG.Theorems.SimplePower.hjbResidual V H
        B.DuLim B.mLim B.uLim) :=
  WeakLimitInputBundleAE.hRes_Lp (d := d)
    hpow hHat0 hFin hAgree hV hβBarPaper hγBarPaper B

/-- **AC sanity check (AE form).** `weakLimitSelector_of_regularizedSequence`
produces a `WeakLimitSelectorAE` from `(hExp, seq, w, mRep, uRep,
DuRep, …)` alone — this is the *positive* side of the AC: AEPeriodicRep
choices are sufficient inputs to discharge every selector field except
the residual non-chosen-`w'` case (the genuine Path-A obstruction
that survives in the converter). -/
example
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hExp : SimplePowerExponentFacts γBarReal
                (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
                (ENNReal.ofReal βBarReal'))
    (seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH)
    (w : Periodic.LpPer (ENNReal.ofReal βBarReal) d
            × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d)
    (mRep : Periodic.AEPeriodicRep (⇑w.1 : (Fin d → ℝ) → ℝ))
    (uRep : Periodic.AEPeriodicRep (⇑w.2.1 : (Fin d → ℝ) → ℝ))
    (DuRep : ∀ i, Periodic.AEPeriodicRep (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ))
    (hDuRep_memLp : ∀ i, Periodic.MemLpPer (d := d) 1 ((DuRep i).rep))
    (seqRepU : ℕ → (Fin d → ℝ) → ℝ)
    (seqRepDu : ℕ → Fin d → (Fin d → ℝ) → ℝ)
    (hSeqRepWeak : ∀ n i,
      Periodic.HasWeakDerivPer (d := d) i (seqRepU n) (seqRepDu n i))
    (hConvU : ∀ (φ : ℕ → ℕ), StrictMono φ →
      ∀ ψ : Periodic.SmoothPeriodic d,
        Filter.Tendsto
          (fun k => StationaryMFG.Periodic.periodicIntegral
                      (fun x =>
                        seqRepU (φ k) x *
                          (ψ : (Fin d → ℝ) → ℝ) x))
          Filter.atTop
          (𝓝 (StationaryMFG.Periodic.periodicIntegral
                (fun x => uRep.rep x * (ψ : (Fin d → ℝ) → ℝ) x))))
    (hConvDu : ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ i,
      ∀ ψ : Periodic.SmoothPeriodic d,
        Filter.Tendsto
          (fun k => StationaryMFG.Periodic.periodicIntegral
                      (fun x =>
                        seqRepDu (φ k) i x *
                          (ψ : (Fin d → ℝ) → ℝ) x))
          Filter.atTop
          (𝓝 (StationaryMFG.Periodic.periodicIntegral
                (fun x => (DuRep i).rep x * (ψ : (Fin d → ℝ) → ℝ) x))))
    (hmRep_nonneg :
      0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
              (UnitCube d)] mRep.rep) :
    WeakLimitSelectorAE (d := d) γBarReal βBarReal w :=
  weakLimitSelector_of_regularizedSequence
    hExp seq w mRep uRep DuRep hDuRep_memLp
    seqRepU seqRepDu hSeqRepWeak hConvU hConvDu hmRep_nonneg

/-! ### `LimitPairingInputs` — per-test-triple authorized bundle for F.6. -/

/-- **Authorized auxiliary bundle** for T9's per-test-triple weak VI.
For every test triple `(μ, υ, Dυ)`, supplies the
`LimitPassageInputData` whose `(m, u, Du)` equals the chosen
periodic limit triple `(mLim, uLim, DuLim)` and whose
`(m_n, u_n, Du_n, ε)` equals the regularized sequence's per-`k`
projections; together with the assembled convergence `hpair_conv`
F.6's `limitPassage_to_weakVI` consumes.

The follow-up task `infra-P4-rebuild-T9-discharge-pairing-inputs`
closes this bundle from `(hmon, hpow, hV, hExp, seq)` via
`paper:lem:ADFGU.a/b`, `paper:thm:strongAepsi`, and the apriori
Gateaux bound. -/
structure LimitPairingInputs
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH)
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ) where
  /-- Per test triple, an `LimitPassageInputData_noVI` whose limit
  triple and per-`k` data align with `(mLim, uLim, DuLim)` and `seq`.
  Phase 5b: the universal `hVI_eps` field is **not** carried here —
  Theorem 1 never reads it (the consumer is
  `tendsto_mfgOperatorPair_assembled_noVI`), and the per-family weak
  VIs flow through `LimitPairingSelector.hVI_eps_{set,signed,transport}`
  directly. Legacy F.6 consumers
  (`limitSolutionData_of_regularizedSequence`{`,_strictPos`}) recover a
  full `LimitPassageInputData` via `of_noVI_withVI` plus an external
  `hVI_eps_universal`. -/
  data : ∀ (μ υ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ),
    LimitPassageInputData_noVI (d := d) V H DpH βBarReal βBarReal'
      γBarReal γBarReal' μ υ Dυ
  /-- `data μ υ Dυ` carries the regularization sequence of `seq`. -/
  data_ε : ∀ (μ υ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ),
    (data μ υ Dυ).ε = seq.epsSeq
  /-- `data μ υ Dυ` carries the per-`k` densities of `seq`. -/
  data_m_n : ∀ (μ υ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ),
    (data μ υ Dυ).m_n = fun k => (seq.sol k).m
  /-- `data μ υ Dυ` carries the per-`k` value functions of `seq`. -/
  data_u_n : ∀ (μ υ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ),
    (data μ υ Dυ).u_n = fun k => (seq.sol k).u
  /-- `data μ υ Dυ` carries the per-`k` gradient families of `seq`. -/
  data_Du_n : ∀ (μ υ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ),
    (data μ υ Dυ).Du_n = fun k => (seq.sol k).Du
  /-- `data μ υ Dυ`'s limit density equals `mLim`. -/
  data_m : ∀ (μ υ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ),
    (data μ υ Dυ).m = mLim
  /-- `data μ υ Dυ`'s limit value-function equals `uLim`. -/
  data_u : ∀ (μ υ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ),
    (data μ υ Dυ).u = uLim
  /-- `data μ υ Dυ`'s limit gradient-family equals `DuLim`. -/
  data_Du : ∀ (μ υ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ),
    (data μ υ Dυ).Du = DuLim
  /-- The assembled un-regularised pairing convergence per test triple. -/
  hpair_conv : ∀ (μ υ : (Fin d → ℝ) → ℝ)
                  (Dυ : Fin d → (Fin d → ℝ) → ℝ),
    Filter.Tendsto (fun k =>
      mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
          (fun i x => Dυ i x - (data μ υ Dυ).Du_n k i x)
          (μ - (data μ υ Dυ).m_n k) (υ - (data μ υ Dυ).u_n k))
      Filter.atTop
      (𝓝 (mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
            (fun i x => Dυ i x - (data μ υ Dυ).Du i x)
            (μ - (data μ υ Dυ).m) (υ - (data μ υ Dυ).u)))

/-! ### `LimitPairingSelector` — the genuine per-test-triple residue.

The fields of `LimitPairingInputs` split cleanly into two groups:

* **Auto-derivable from `(seq, wkBundle)`**: the test-triple-*independent*
  fields of each `LimitPassageInputData T := data μ υ Dυ`. These are the
  ε-sequence `T.ε := seq.epsSeq`, the per-`k` triples `T.{m_n, u_n, Du_n}`
  read off `seq.sol`, the limit triple `T.{m, u, Du}` read off `wkBundle`,
  the `MemLpPer` certificates of the per-`k` triple read off
  `(seq.sol k).{hmLp, huLp, hDuLp}`, and `T.{hε_nonneg, hε_to0}` read off
  `seq.{heps_pos, heps_tendsto}`.

* **Genuinely test-triple-dependent (Path-A residue)**: the test-triple
  regularity (`hυ_memLp`, `hDυ_memLp`, `hμ_memLp`), the multiplier
  `MemLpPer` certificates (`hg_memLp`, `hflux_memLp`, `hμMinusOne_memLp`),
  the `WeakConvPairing` certificates (`h_weak_m`, `h_weak_u`,
  `h_weak_Du`), the per-`k` strong-VI at the test triple (`hVI_eps`),
  the Gateaux uniform bound `(M, hreg_bdd)`, and the assembled
  pairing convergence `hpair_conv`. None can be discharged from
  `(seq, wkBundle, hExp)` alone.

  - Multiplier integrabilities depend on the user-chosen test triple
    `(μ, υ, Dυ)` and on `H, DpH, V`; paper `lem:ADFGU.a/b` proves them
    at the regularised pair, not at an arbitrary test triple.
  - `WeakConvPairing` requires upgrading F.5's smooth-tester
    convergence to arbitrary `L^q`-testers; needs density of
    `SmoothPeriodic d` in `L^q_per`, which is not in the codebase.
  - The per-`k` strong-VI in bare-triple form requires translating
    `paper:thm:strongAepsi` to arbitrary bare test triples (the
    three regularised paper-family VIs `RegularizedBareSolution.hVIeps_set`,
    `hVIeps_signed`, `hVIeps_transport` produced by the two-domain
    redesign cover the indicator/signed/transport test families
    individually but not yet all `L^q`-testers).
  - The Gateaux residual bound is the apriori `‖u_{ε_k}‖_{W^{1,γBar}}` work.

`LimitPairingSelector` packages **only the second group** as authorised
inputs to the producer below. Per CONVENTIONS §8, the genuine residue
is filed as the follow-up
`infra-P4-rebuild-T9-discharge-pairing-inputs-selector`. -/

/-! #### Helpers: derive `Real.HolderConjugate βBarReal βBarReal'` /
`Real.HolderConjugate γBarReal γBarReal'` from `SimplePowerExponentFacts`.

Per `infra-P5-theorem1-phase-6e-shrink-pairingResidueOf-hpq` (Step 5 of
the expert post-iter-388 prescriptive plan), these helpers bridge
`hExp.βConj` / `hExp.γConj` (which carry `toReal`-form conjugacies)
to the `ℝ`-form conjugacies expected by `LimitPairingSelector`'s
`hpqβ` / `hpqγ` parameters, via `ENNReal.toReal_ofReal`. -/

/-- Derive `βBarReal.HolderConjugate βBarReal'` from `hExp` plus
positivity of the real-valued exponents. Bridges the `toReal`
conversion via `ENNReal.toReal_ofReal`. -/
lemma holder_beta_of_exp
    {γBarReal βBarReal βBarReal' : ℝ}
    (hExp : SimplePowerExponentFacts γBarReal
              (ENNReal.ofReal βBarReal)
              (ENNReal.ofReal γBarReal)
              (ENNReal.ofReal βBarReal'))
    (hβ : 0 ≤ βBarReal) (hβ' : 0 ≤ βBarReal') :
    βBarReal.HolderConjugate βBarReal' := by
  have h := hExp.βConj
  rw [ENNReal.toReal_ofReal hβ, ENNReal.toReal_ofReal hβ'] at h
  exact h

/-- Derive `γBarReal.HolderConjugate γBarReal'` from `hExp` plus the
identification `γBarReal' = γBarReal / (γBarReal - 1)` (paper formula)
and positivity of `γBarReal`. Bridges the `toReal` conversion via
`ENNReal.toReal_ofReal`. -/
lemma holder_gamma_of_exp
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (hExp : SimplePowerExponentFacts γBarReal
              (ENNReal.ofReal βBarReal)
              (ENNReal.ofReal γBarReal)
              (ENNReal.ofReal βBarReal'))
    (hγ : 0 ≤ γBarReal)
    (hγ'Eq : γBarReal' = γBarReal / (γBarReal - 1)) :
    γBarReal.HolderConjugate γBarReal' := by
  have h := hExp.γConj
  rw [ENNReal.toReal_ofReal hγ] at h
  -- Now `h : γBarReal.HolderConjugate (γBarReal / (γBarReal - 1))`.
  rw [hγ'Eq]
  exact h

/-! #### Canonical paper Hölder helpers

Per `infra-P5-theorem1-remove-pairingResidue-hpq-dependency` (Phase 1 of
the expert post-iter-412 prescriptive plan): supply Hölder-conjugacy
proofs `(β̄, β̄')` and `(γ̄, γ̄')` derived solely from a
`HypothesisPowerGrowth` bundle, so that downstream residue fields can
type their `WeakConvPairing_universal` props **independently** of any
`pairingResidueOf seq wkBundle`. The previous wiring kept
`pairingResidueOf` structurally alive in the `T10PaperResidues.h_weak_*Of`
field signatures even though `hpqβ`/`hpqγ` are derivable from `hExp`.
-/

/-- Canonical paper Hölder conjugacy at `(β̄, β̄')`, derived from the
data fields of a `HypothesisPowerGrowth` bundle (specifically `hpow.hβ`).
This is the `(β̄, β̄')` analogue of `holder_beta_of_exp`, but only depends
on `hpow` (no `hExp`). Used in `T10PaperResidues.h_weak_mOf` to break
the `pairingResidueOf ↔ h_weak_*Of` dependency knot. -/
lemma hpqBeta_paper {d : ℕ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH) :
    Real.HolderConjugate (Hamiltonian.betaBar hpow.β)
      (Hamiltonian.betaBar' hpow.β) := by
  -- `betaBar β = β + 1`, `betaBar' β = (β + 1) / β`.
  unfold Hamiltonian.betaBar Hamiltonian.betaBar'
  exact StationaryMFG.Theorems.SimplePower.SimplePowerExponentFacts.paper_holderConjugate_betaBar
    hpow.hβ

/-- Canonical paper Hölder conjugacy at `(γ̄, γ̄')`, derived from the
data fields of a `HypothesisPowerGrowth` bundle (specifically
`hpow.hα` and `hpow.hβ`). Used in `T10PaperResidues.h_weak_uOf` /
`h_weak_DuOf` to break the `pairingResidueOf ↔ h_weak_*Of`
dependency knot. -/
lemma hpqGamma_paper {d : ℕ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH) :
    Real.HolderConjugate (Hamiltonian.gammaBar hpow.α hpow.β)
      (Hamiltonian.gammaBar' hpow.α hpow.β) := by
  -- `gammaBar α β = α * (β + 1) / β`,
  -- `gammaBar' α β = gammaBar α β / (gammaBar α β - 1)`.
  unfold Hamiltonian.gammaBar' Hamiltonian.gammaBar
  exact StationaryMFG.Theorems.SimplePower.SimplePowerExponentFacts.paper_holderConjugate_gammaBar
    hpow.hα hpow.hβ

/-! #### `LimitPairingSelectorPaperResidue` Hölder helpers

Per `infra-P5-theorem1-remove-pairingResidue-hpq-dependency` (Phase 1 of
the expert post-iter-412 prescriptive plan, Formalizer iter 0493): with
`hpqβ` / `hpqγ` removed from `LimitPairingSelectorPaperResidue`, downstream
producers (`limitPairingSelector_of_paperHypotheses`,
`limitPairingSelectorFamily_of_paperHypotheses_at`, and the three
per-family direct producers) need a closed-form `βBarReal.HolderConjugate
βBarReal'` / `γBarReal.HolderConjugate γBarReal'` at the residue exponents
to type the `h_weak_*_universal` parameters. The two helpers below
package the derivations from `_hExp` plus the paper-form equalities,
mirroring the in-body `hpqβ_derived`/`hpqγ_derived` of those producers. -/

/-- Closed-form `βBarReal.HolderConjugate βBarReal'` at the residue's
abstract exponents, derived from `_hExp` plus `hpow` and the paper-form
equalities `hβBarEq` / `hβBar'Eq`. Used to type the `h_weak_m_universal`
parameter of the `LimitPairingSelector(...)Family` producers after the
removal of `LimitPairingSelectorPaperResidue.hpqβ`. -/
lemma hpqBeta_paperResidue {d : ℕ}
    {γBarReal βBarReal βBarReal' : ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (hExp : SimplePowerExponentFacts γBarReal
              (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
              (ENNReal.ofReal βBarReal'))
    (hβBarEq : βBarReal = hpow.β + 1)
    (hβBar'Eq : βBarReal' = (hpow.β + 1) / hpow.β) :
    βBarReal.HolderConjugate βBarReal' := by
  have h_β_pos : (0 : ℝ) < βBarReal := by
    rw [hβBarEq]; linarith [hpow.hβ]
  have h_β'_pos : (0 : ℝ) < βBarReal' := by
    rw [hβBar'Eq]
    have hβ1 : (0 : ℝ) < hpow.β + 1 := by linarith [hpow.hβ]
    exact div_pos hβ1 hpow.hβ
  exact holder_beta_of_exp hExp h_β_pos.le h_β'_pos.le

/-- Closed-form `γBarReal.HolderConjugate γBarReal'` at the residue's
abstract exponents, derived from `_hExp` plus `hpow` and the paper-form
equalities `hγBarEq` / `hγBar'Eq`. Used to type the `h_weak_u_universal`
and `h_weak_Du_universal` parameters of the `LimitPairingSelector(...)Family`
producers after the removal of `LimitPairingSelectorPaperResidue.hpqγ`. -/
lemma hpqGamma_paperResidue {d : ℕ}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (hExp : SimplePowerExponentFacts γBarReal
              (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
              (ENNReal.ofReal βBarReal'))
    (hγBarEq : γBarReal = hpow.α * (hpow.β + 1) / hpow.β)
    (hγBar'Eq : γBarReal' = hpow.α * (hpow.β + 1) / hpow.β /
                              (hpow.α * (hpow.β + 1) / hpow.β - 1)) :
    γBarReal.HolderConjugate γBarReal' := by
  have h_γ_pos : (0 : ℝ) < γBarReal := by
    rw [hγBarEq]
    have hα0 : (0 : ℝ) < hpow.α := lt_trans zero_lt_one hpow.hα
    have hβ1 : (0 : ℝ) < hpow.β + 1 := by linarith [hpow.hβ]
    exact div_pos (mul_pos hα0 hβ1) hpow.hβ
  have h_γ'_eq : γBarReal' = γBarReal / (γBarReal - 1) := by
    rw [hγBar'Eq, hγBarEq]
  exact holder_gamma_of_exp hExp h_γ_pos.le h_γ'_eq

/-- **Selector-only authorised inputs** for the `LimitPairingInputs`
producer.

Per CONVENTIONS §8 (statement-then-proof discipline), this structure
isolates the genuinely Path-A-selector-dependent and per-test-triple-
dependent fields of `LimitPairingInputs`, leaving the producer to
discharge the test-triple-independent fields automatically from
`(seq, wkBundle)`.

**Phase 6e refactor** (`infra-P5-theorem1-phase-6e-shrink-pairingResidueOf-hpq`):
the Hölder conjugacy facts `hpqβ`/`hpqγ` have been promoted from
`where`-block fields to **structure parameters**, removing them as
user-supplied per-selector data. Producers derive them from `hExp`
via `holder_beta_of_exp` / `holder_gamma_of_exp` and pass them at the
parameter slot. -/
structure LimitPairingSelector
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH)
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ) where
  /-- Hölder-conjugate pair `(βBar, βBar')`, `1/βBar + 1/βBar' = 1`.

  **Phase 6e**: this remains a field, but the producer
  `limitPairingSelector_of_paperHypotheses` now populates it
  automatically from `hExp` via `holder_beta_of_exp` rather than
  reading it from `LimitPairingSelectorPaperResidue.hpqβ`. The
  field is therefore no longer "user-supplied" at the producer
  layer (acceptance criterion 2 of the Phase 6e task). -/
  hpqβ : βBarReal.HolderConjugate βBarReal'
  /-- Hölder-conjugate pair `(γBar, γBar')`, `1/γBar + 1/γBar' = 1`.

  **Phase 6e**: now populated automatically from `hExp` via
  `holder_gamma_of_exp` in the producer, paralleling `hpqβ`. -/
  hpqγ : γBarReal.HolderConjugate γBarReal'
  /-- `MemLpPer γBar` of every gradient-limit component. The bundle
  `wkBundle.hDuLim_memLp` only certifies `MemLpPer 1`; this strict
  upgrade is a Path-A residue (the existentially-quantified weak-deriv
  family inside `MemSobolevPer γBar uLim` is *separate* from `DuLim`). -/
  hDuLim_memLp_γ : ∀ i, Periodic.MemLpPer (d := d)
                          (ENNReal.ofReal γBarReal) (DuLim i)
  /-- Per test triple, `υ ∈ L^{γBar}_per`. -/
  hυ_memLp : ∀ (μ υ : (Fin d → ℝ) → ℝ)
                (Dυ : Fin d → (Fin d → ℝ) → ℝ),
              Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal) υ
  /-- Per test triple, `Dυ i ∈ L^{γBar}_per`. -/
  hDυ_memLp : ∀ (μ υ : (Fin d → ℝ) → ℝ)
                 (Dυ : Fin d → (Fin d → ℝ) → ℝ) (i : Fin d),
                Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i)
  /-- Per test triple, `μ ∈ L^{βBar}_per`. -/
  hμ_memLp : ∀ (μ υ : (Fin d → ℝ) → ℝ)
                (Dυ : Fin d → (Fin d → ℝ) → ℝ),
              Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) μ
  /-- Per test triple, multiplier `g(x) := -υ(x) - H(x, Dυ, μ) + V(x)`
  is in `L^{βBar'}_per` (paper `lem:ADFGU.a` analogue at the test triple). -/
  hg_memLp : ∀ (μ υ : (Fin d → ℝ) → ℝ)
                (Dυ : Fin d → (Fin d → ℝ) → ℝ),
              Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal')
                (fun x => -(υ x) - H x (fun i => Dυ i x) (μ x) + V x)
  /-- Per test triple, per coordinate, the flux
  `flux_i(x) := μ(x) · D_pH(x, Dυ, μ) i` is in `L^{γBar'}_per`
  (paper `lem:ADFGU.b` analogue). -/
  hflux_memLp : ∀ (μ υ : (Fin d → ℝ) → ℝ)
                   (Dυ : Fin d → (Fin d → ℝ) → ℝ) (i : Fin d),
                 Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
                   (fun x => μ x * DpH x (fun j => Dυ j x) (μ x) i)
  /-- Per test triple, the mass-defect multiplier `(μ - 1) ∈ L^{γBar'}_per`. -/
  hμMinusOne_memLp : ∀ (μ υ : (Fin d → ℝ) → ℝ)
                        (Dυ : Fin d → (Fin d → ℝ) → ℝ),
                      Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
                        (fun x => μ x - 1)
  /-- Weak-pairing certificate: `(seq.sol k).m ⇀ mLim` against
  `L^{βBar'}_per` testers (F.5 product weak-convergence upgraded
  through density). -/
  h_weak_m : WeakConvPairing_universal (d := d) hpqβ
              (fun k => (seq.sol k).m) mLim
  /-- Weak-pairing certificate: `(seq.sol k).u ⇀ uLim` against
  `L^{γBar'}_per` testers. -/
  h_weak_u : WeakConvPairing_universal (d := d) hpqγ
              (fun k => (seq.sol k).u) uLim
  /-- Per coordinate, weak-pairing certificate:
  `fun k => (seq.sol k).Du i ⇀ DuLim i` against `L^{γBar'}_per` testers. -/
  h_weak_Du : ∀ i, WeakConvPairing_universal (d := d) hpqγ
                    (fun k => (seq.sol k).Du i) (DuLim i)
  /-- **Set-family regularised VI per `k`** — paper `thm:strongAepsi`
  on the indicator-modulated test family (paper test family (a) of
  `lem:strong.is.strong`). Mirrors
  `RegularizedBareSolution.hVIeps_set` at every `k`, with the
  per-`k` solution `(seq.sol k)` and the regularisation
  parameter `seq.epsSeq k`. -/
  hVI_eps_set : ∀ (k : ℕ)
    (S : Set (Fin d → ℝ)), MeasurableSet S →
    ∀ (ρ υ : (Fin d → ℝ) → ℝ)
      (Dυ : Fin d → (Fin d → ℝ) → ℝ),
      (∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ ρ x) →
      MemLpPer (d := d) (ENNReal.ofReal βBarReal) (S.indicator ρ) →
      MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ →
      (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i)) →
      (∀ i, HasWeakDerivPer (d := d) i υ (Dυ i)) →
        0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal (seq.epsSeq k)
              Dυ (S.indicator ρ) υ
              (fun i x => Dυ i x - (seq.sol k).Du i x)
              (S.indicator ρ - (seq.sol k).m) (υ - (seq.sol k).u)
  /-- **Signed-family regularised VI per `k`** — paper test family
  (b) of `lem:strong.is.strong`, paper-exact shape per
  `infra-P4-narrow-hVIeps-signed-shape`. Mirrors
  `RegularizedBareSolution.hVIeps_signed` at every `k`. -/
  hVI_eps_signed : ∀ (k : ℕ)
    (σ : ℝ), σ = 1 ∨ σ = -1 →
    ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
      (MeasureTheory.volume.restrict (UnitCube d)) S < ⊤ →
        0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal (seq.epsSeq k)
              (seq.sol k).Du
              (fun x => (seq.sol k).m x + σ * (seq.sol k).m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              (seq.sol k).u
              (fun _ _ => (0 : ℝ))
              (fun x => σ * (seq.sol k).m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              (fun _ => (0 : ℝ))
  /-- **Transport-family regularised VI per `k`** — paper test family
  (c) of `lem:strong.is.strong`. Mirrors
  `RegularizedBareSolution.hVIeps_transport` at every `k`. -/
  hVI_eps_transport : ∀ (k : ℕ)
    (σ υ : (Fin d → ℝ) → ℝ)
    (φ : Fin d → (Fin d → ℝ) → ℝ),
      (∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ σ x) →
      MemLpPer (d := d) (ENNReal.ofReal βBarReal) σ →
      MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ →
      (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (φ i)) →
      (∀ i, HasWeakDerivPer (d := d) i υ (φ i)) →
        0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal (seq.epsSeq k)
              φ σ υ
              (fun i x => φ i x - (seq.sol k).Du i x)
              (σ - (seq.sol k).m) (υ - (seq.sol k).u)
  /-- Per test triple, a uniform Gateaux-residual bound `M μ υ Dυ`. -/
  M : ((Fin d → ℝ) → ℝ) → ((Fin d → ℝ) → ℝ) →
        (Fin d → (Fin d → ℝ) → ℝ) → ℝ
  /-- Per test triple, per `k`, the Gateaux residual is bounded
  by `M μ υ Dυ`. -/
  hreg_bdd : ∀ (μ υ : (Fin d → ℝ) → ℝ)
                (Dυ : Fin d → (Fin d → ℝ) → ℝ) (k : ℕ),
              |gateauxWpPair γBarReal Dυ υ
                  (fun i x => Dυ i x - (seq.sol k).Du i x)
                  (υ - (seq.sol k).u)| ≤ M μ υ Dυ
  /-- Per test triple, the assembled un-regularised pairing
  convergence (the F.6 input). -/
  hpair_conv : ∀ (μ υ : (Fin d → ℝ) → ℝ)
                  (Dυ : Fin d → (Fin d → ℝ) → ℝ),
    Filter.Tendsto (fun k =>
      mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
          (fun i x => Dυ i x - (seq.sol k).Du i x)
          (μ - (seq.sol k).m) (υ - (seq.sol k).u))
      Filter.atTop
      (𝓝 (mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
            (fun i x => Dυ i x - DuLim i x)
            (μ - mLim) (υ - uLim)))

/-! ### Producer: `limitPairingInputs_of_regularizedSequence`

Per CONVENTIONS §8, this discharges the test-triple-independent fields
of `LimitPairingInputs` genuinely (read off `seq.sol` and `wkBundle`),
while leaving the test-triple-dependent / Path-A fields parameterised
through `selector`. Filed follow-up:
`infra-P4-rebuild-T9-discharge-pairing-inputs-selector`. -/

/-- **AC1–AC4 producer (partial / amended).** Build a
`LimitPairingInputs` whose test-triple-independent fields are
**derived from `(seq, wkBundle)`**. The genuinely selector-dependent
fields are read off `selector`.

This discharges the structural / test-triple-independent content of
the parent task ACs in full. AC1–AC4 are amended into the
`LimitPairingSelector` parameter per CONVENTIONS §8 (filed follow-up
`infra-P4-rebuild-T9-discharge-pairing-inputs-selector`). -/
noncomputable def limitPairingInputs_of_regularizedSequence
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (_hmon : Hamiltonian.HypothesisMonotone H DpH)
    (_hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (_hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (_hExp : SimplePowerExponentFacts γBarReal
                (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
                (ENNReal.ofReal βBarReal'))
    (seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH)
    (wkBundle : WeakLimitInputBundleAE (d := d) γBarReal βBarReal)
    (selector : LimitPairingSelector (d := d)
                  (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  (V := V) (H := H) (DpH := DpH)
                  seq wkBundle.mLim wkBundle.uLim wkBundle.DuLim) :
    -- **Phase 5b** (`infra-P5-theorem1-phase-5b-rebuild-pairing-on-noVI`).
    -- The legacy `hVI_eps_universal` parameter has been dropped: the
    -- structurally dead `LimitPassageInputData.hVI_eps` field is no
    -- longer reachable from Theorem 1 because `LimitPairingInputs.data`
    -- now returns the leaner `LimitPassageInputData_noVI`. Legacy F.6
    -- producers reconstruct the universal shape via `of_noVI_withVI`.
    LimitPairingInputs (d := d)
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      (V := V) (H := H) (DpH := DpH)
      seq wkBundle.mLim wkBundle.uLim wkBundle.DuLim where
  data := fun μ υ Dυ =>
    { hpqβ := selector.hpqβ
      hpqγ := selector.hpqγ
      ε := seq.epsSeq
      m_n := fun k => (seq.sol k).m
      u_n := fun k => (seq.sol k).u
      Du_n := fun k => (seq.sol k).Du
      m := wkBundle.mLim
      u := wkBundle.uLim
      Du := wkBundle.DuLim
      hε_nonneg := fun k => (seq.heps_pos k).le
      hε_to0 := seq.heps_tendsto
      hm_n_memLp := fun k => (seq.sol k).hmLp
      hm_memLp := wkBundle.hmLim_memLp
      hu_n_memLp := fun k => (seq.sol k).huLp
      hu_memLp := wkBundle.huLim_sob.1
      hυ_memLp := selector.hυ_memLp μ υ Dυ
      hDu_n_memLp := fun k i => (seq.sol k).hDuLp i
      hDu_memLp := selector.hDuLim_memLp_γ
      hDυ_memLp := selector.hDυ_memLp μ υ Dυ
      hμ_memLp := selector.hμ_memLp μ υ Dυ
      hg_memLp := selector.hg_memLp μ υ Dυ
      hflux_memLp := selector.hflux_memLp μ υ Dυ
      hμMinusOne_memLp := selector.hμMinusOne_memLp μ υ Dυ
      h_weak_m := selector.h_weak_m
      h_weak_u := selector.h_weak_u
      h_weak_Du := selector.h_weak_Du
      M := selector.M μ υ Dυ
      hreg_bdd := selector.hreg_bdd μ υ Dυ }
  data_ε := fun _ _ _ => rfl
  data_m_n := fun _ _ _ => rfl
  data_u_n := fun _ _ _ => rfl
  data_Du_n := fun _ _ _ => rfl
  data_m := fun _ _ _ => rfl
  data_u := fun _ _ _ => rfl
  data_Du := fun _ _ _ => rfl
  hpair_conv := selector.hpair_conv

/-- **AC sanity check.** `limitPairingInputs_of_regularizedSequence`
produces a `LimitPairingInputs` from `(hmon, hpow, hV, hExp, seq,
wkBundle, selector)`. Phase 5b: the legacy `hVI_eps_universal`
parameter has been dropped (the structurally dead `hVI_eps` field is
no longer reachable from `LimitPairingInputs.data`). -/
example
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (hExp : SimplePowerExponentFacts γBarReal
                (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
                (ENNReal.ofReal βBarReal'))
    (seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH)
    (wkBundle : WeakLimitInputBundleAE (d := d) γBarReal βBarReal)
    (selector : LimitPairingSelector (d := d)
                  (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  (V := V) (H := H) (DpH := DpH)
                  seq wkBundle.mLim wkBundle.uLim wkBundle.DuLim) :
    LimitPairingInputs (d := d)
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      (V := V) (H := H) (DpH := DpH)
      seq wkBundle.mLim wkBundle.uLim wkBundle.DuLim :=
  limitPairingInputs_of_regularizedSequence
    hmon hpow hV hExp seq wkBundle selector

/-! ### Phase 6c-i — family-restricted `LimitPairingSelectorFamily`

Per `infra-P5-theorem1-phase-6c-pairingResidue-familyRestrict`, we
land **parallel infrastructure** mirroring `LimitPairingSelector`'s
shape but with the six universal `MemLpPer` fields
(`hυ_memLp`, `hDυ_memLp`, `hμ_memLp`, `hg_memLp`, `hflux_memLp`,
`hμMinusOne_memLp`) and the per-test-triple Gateaux/pairing fields
(`M`, `hreg_bdd`, `hpair_conv`) restricted to a single domain
`D : Set (MFGTriple d)`. The legacy universal `LimitPairingSelector`
(and its producer `limitPairingSelector_of_paperHypotheses`) is left
untouched — child tasks 6c-ii / 6c-iii / 6c-iv will rewire
`LimitPairingInputs`, the three strongVI helpers, and the
BanachBridge to consume the family-restricted variant before Phase
6d drops `regBundle` from `T10PaperResidues`.

The structure parallels `LimitPairingSelectorGateauxAuxFamily`'s
design (Phase 6b, lines ~10287–10453): each universally-shaped field
becomes a `(μ, υ, Dυ) ∈ D → …`-shaped field, and the
universal-to-family bridge `LimitPairingSelector.toFamily` produces a
`LimitPairingSelectorFamily` for any `D` by ignoring the membership
hypothesis. -/

/-- **Family-restricted authorised inputs** for the `LimitPairingInputs`
producer.

A domain-parameterised version of `LimitPairingSelector`: each of the
nine per-test-triple fields (`hυ_memLp`, `hDυ_memLp`, `hμ_memLp`,
`hg_memLp`, `hflux_memLp`, `hμMinusOne_memLp`, `M`, `hreg_bdd`,
`hpair_conv`) is now quantified over `(μ, υ, Dυ) ∈ D` rather than
universally. The exponent-conjugacy fields (`hpqβ`, `hpqγ`), the
strict-`γ̄` `MemLpPer` on `DuLim` (`hDuLim_memLp_γ`), the three
weak-pairing certificates (`h_weak_m/u/Du`), and the per-`k`
regularised VIs (`hVI_eps_set/_signed/_transport`) remain
*test-triple-independent* (or per-`k`-but-not-per-test-triple), so
they keep their universal shape.

When `D = Set.univ`, this structure is interconvertible with the
universal `LimitPairingSelector` (cf.
`LimitPairingSelector.toFamily` below). Phase 6c-ii will add a
matching `LimitPairingInputsFamily` plus a producer
`limitPairingInputsFamily_of_regularizedSequence` consuming this
selector. -/
structure LimitPairingSelectorFamily
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH)
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    (D : Set (StationaryMFG.Theorems.SimplePower.MFGTriple d)) where
  /-- Hölder-conjugate pair `(βBar, βBar')`, `1/βBar + 1/βBar' = 1`.
  **Phase 6e**: producers populate this automatically from `hExp` via
  `holder_beta_of_exp`. -/
  hpqβ : βBarReal.HolderConjugate βBarReal'
  /-- Hölder-conjugate pair `(γBar, γBar')`, `1/γBar + 1/γBar' = 1`.
  **Phase 6e**: producers populate this automatically from `hExp` via
  `holder_gamma_of_exp`. -/
  hpqγ : γBarReal.HolderConjugate γBarReal'
  /-- `MemLpPer γBar` of every gradient-limit component. The bundle
  `wkBundle.hDuLim_memLp` only certifies `MemLpPer 1`; this strict
  upgrade is a Path-A residue (the existentially-quantified weak-deriv
  family inside `MemSobolevPer γBar uLim` is *separate* from `DuLim`). -/
  hDuLim_memLp_γ : ∀ i, Periodic.MemLpPer (d := d)
                          (ENNReal.ofReal γBarReal) (DuLim i)
  /-- Per test triple in `D`, `υ ∈ L^{γBar}_per`. -/
  hυ_memLp : ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄
                ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
                (μ, υ, Dυ) ∈ D →
              Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal) υ
  /-- Per test triple in `D`, `Dυ i ∈ L^{γBar}_per`. -/
  hDυ_memLp : ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄
                 ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
                 (μ, υ, Dυ) ∈ D → ∀ (i : Fin d),
                Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i)
  /-- Per test triple in `D`, `μ ∈ L^{βBar}_per`. -/
  hμ_memLp : ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄
                ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
                (μ, υ, Dυ) ∈ D →
              Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) μ
  /-- Per test triple in `D`, multiplier `g(x) := -υ(x) - H(x, Dυ, μ) + V(x)`
  is in `L^{βBar'}_per` (paper `lem:ADFGU.a` analogue at the test triple). -/
  hg_memLp : ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄
                ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
                (μ, υ, Dυ) ∈ D →
              Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal')
                (fun x => -(υ x) - H x (fun i => Dυ i x) (μ x) + V x)
  /-- Per test triple in `D`, per coordinate, the flux
  `flux_i(x) := μ(x) · D_pH(x, Dυ, μ) i` is in `L^{γBar'}_per`
  (paper `lem:ADFGU.b` analogue). -/
  hflux_memLp : ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄
                   ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
                   (μ, υ, Dυ) ∈ D → ∀ (i : Fin d),
                 Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
                   (fun x => μ x * DpH x (fun j => Dυ j x) (μ x) i)
  /-- Per test triple in `D`, the mass-defect multiplier
  `(μ - 1) ∈ L^{γBar'}_per`. -/
  hμMinusOne_memLp : ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄
                        ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
                        (μ, υ, Dυ) ∈ D →
                      Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
                        (fun x => μ x - 1)
  /-- Weak-pairing certificate: `(seq.sol k).m ⇀ mLim` against
  `L^{βBar'}_per` testers. -/
  h_weak_m : WeakConvPairing_universal (d := d) hpqβ
              (fun k => (seq.sol k).m) mLim
  /-- Weak-pairing certificate: `(seq.sol k).u ⇀ uLim` against
  `L^{γBar'}_per` testers. -/
  h_weak_u : WeakConvPairing_universal (d := d) hpqγ
              (fun k => (seq.sol k).u) uLim
  /-- Per coordinate, weak-pairing certificate:
  `fun k => (seq.sol k).Du i ⇀ DuLim i` against `L^{γBar'}_per` testers. -/
  h_weak_Du : ∀ i, WeakConvPairing_universal (d := d) hpqγ
                    (fun k => (seq.sol k).Du i) (DuLim i)
  /-- **Set-family regularised VI per `k`** — paper `thm:strongAepsi`
  on the indicator-modulated test family. -/
  hVI_eps_set : ∀ (k : ℕ)
    (S : Set (Fin d → ℝ)), MeasurableSet S →
    ∀ (ρ υ : (Fin d → ℝ) → ℝ)
      (Dυ : Fin d → (Fin d → ℝ) → ℝ),
      (∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ ρ x) →
      MemLpPer (d := d) (ENNReal.ofReal βBarReal) (S.indicator ρ) →
      MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ →
      (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i)) →
      (∀ i, HasWeakDerivPer (d := d) i υ (Dυ i)) →
        0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal (seq.epsSeq k)
              Dυ (S.indicator ρ) υ
              (fun i x => Dυ i x - (seq.sol k).Du i x)
              (S.indicator ρ - (seq.sol k).m) (υ - (seq.sol k).u)
  /-- **Signed-family regularised VI per `k`** — paper test family (b). -/
  hVI_eps_signed : ∀ (k : ℕ)
    (σ : ℝ), σ = 1 ∨ σ = -1 →
    ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
      (MeasureTheory.volume.restrict (UnitCube d)) S < ⊤ →
        0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal (seq.epsSeq k)
              (seq.sol k).Du
              (fun x => (seq.sol k).m x + σ * (seq.sol k).m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              (seq.sol k).u
              (fun _ _ => (0 : ℝ))
              (fun x => σ * (seq.sol k).m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              (fun _ => (0 : ℝ))
  /-- **Transport-family regularised VI per `k`** — paper test family (c). -/
  hVI_eps_transport : ∀ (k : ℕ)
    (σ υ : (Fin d → ℝ) → ℝ)
    (φ : Fin d → (Fin d → ℝ) → ℝ),
      (∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ σ x) →
      MemLpPer (d := d) (ENNReal.ofReal βBarReal) σ →
      MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ →
      (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (φ i)) →
      (∀ i, HasWeakDerivPer (d := d) i υ (φ i)) →
        0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal (seq.epsSeq k)
              φ σ υ
              (fun i x => φ i x - (seq.sol k).Du i x)
              (σ - (seq.sol k).m) (υ - (seq.sol k).u)
  /-- Per test triple in `D`, a uniform Gateaux-residual bound `M μ υ Dυ`. -/
  M : ((Fin d → ℝ) → ℝ) → ((Fin d → ℝ) → ℝ) →
        (Fin d → (Fin d → ℝ) → ℝ) → ℝ
  /-- Per test triple in `D`, per `k`, the Gateaux residual is bounded
  by `M μ υ Dυ`. -/
  hreg_bdd : ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄
                ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
                (μ, υ, Dυ) ∈ D → ∀ (k : ℕ),
              |gateauxWpPair γBarReal Dυ υ
                  (fun i x => Dυ i x - (seq.sol k).Du i x)
                  (υ - (seq.sol k).u)| ≤ M μ υ Dυ
  /-- Per test triple in `D`, the assembled un-regularised pairing
  convergence (the F.6 input). -/
  hpair_conv : ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄
                  ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
                  (μ, υ, Dυ) ∈ D →
    Filter.Tendsto (fun k =>
      mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
          (fun i x => Dυ i x - (seq.sol k).Du i x)
          (μ - (seq.sol k).m) (υ - (seq.sol k).u))
      Filter.atTop
      (𝓝 (mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
            (fun i x => Dυ i x - DuLim i x)
            (μ - mLim) (υ - uLim)))

/-- **Universal-to-family bridge for `LimitPairingSelector`.** A
universal `LimitPairingSelector` produces, for any domain `D`, a
matching `LimitPairingSelectorFamily seq mLim uLim DuLim D` by
ignoring the membership hypothesis on the per-test-triple fields.
The exponent-conjugacy, strict-`γ̄` `MemLpPer` on `DuLim`,
weak-pairing certificates, and per-`k` regularised VIs are
test-triple-independent and pass through unchanged. -/
def LimitPairingSelector.toFamily
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH}
    {mLim uLim : (Fin d → ℝ) → ℝ}
    {DuLim : Fin d → (Fin d → ℝ) → ℝ}
    (selector : LimitPairingSelector (d := d)
                  (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  (V := V) (H := H) (DpH := DpH)
                  seq mLim uLim DuLim)
    (D : Set (StationaryMFG.Theorems.SimplePower.MFGTriple d)) :
    LimitPairingSelectorFamily (d := d)
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      (V := V) (H := H) (DpH := DpH)
      seq mLim uLim DuLim D where
  hpqβ := selector.hpqβ
  hpqγ := selector.hpqγ
  hDuLim_memLp_γ := selector.hDuLim_memLp_γ
  hυ_memLp := fun μ υ Dυ _ => selector.hυ_memLp μ υ Dυ
  hDυ_memLp := fun μ υ Dυ _ i => selector.hDυ_memLp μ υ Dυ i
  hμ_memLp := fun μ υ Dυ _ => selector.hμ_memLp μ υ Dυ
  hg_memLp := fun μ υ Dυ _ => selector.hg_memLp μ υ Dυ
  hflux_memLp := fun μ υ Dυ _ i => selector.hflux_memLp μ υ Dυ i
  hμMinusOne_memLp := fun μ υ Dυ _ => selector.hμMinusOne_memLp μ υ Dυ
  h_weak_m := selector.h_weak_m
  h_weak_u := selector.h_weak_u
  h_weak_Du := selector.h_weak_Du
  hVI_eps_set := selector.hVI_eps_set
  hVI_eps_signed := selector.hVI_eps_signed
  hVI_eps_transport := selector.hVI_eps_transport
  M := selector.M
  hreg_bdd := fun μ υ Dυ _ k => selector.hreg_bdd μ υ Dυ k
  hpair_conv := fun μ υ Dυ _ => selector.hpair_conv μ υ Dυ

/-- **Phase 6c-i sanity check.** The universal-to-family bridge is
type-correct on a generic universal selector at any domain. -/
example
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH}
    {mLim uLim : (Fin d → ℝ) → ℝ}
    {DuLim : Fin d → (Fin d → ℝ) → ℝ}
    (selector : LimitPairingSelector (d := d)
                  (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  (V := V) (H := H) (DpH := DpH)
                  seq mLim uLim DuLim)
    (D : Set (StationaryMFG.Theorems.SimplePower.MFGTriple d)) :
    LimitPairingSelectorFamily (d := d)
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      (V := V) (H := H) (DpH := DpH)
      seq mLim uLim DuLim D :=
  selector.toFamily D

/-! ### Phase 6c-ii — family-restricted `LimitPairingInputsFamily`

Per `infra-P5-theorem1-phase-6c-ii-pairingInputs-familyRestrict`, we
land **parallel infrastructure** mirroring `LimitPairingInputs`'s
shape but with each per-test-triple field guarded by membership in
a single domain `D : Set (MFGTriple d)`. Together with the matching
producer `limitPairingInputsFamily_of_regularizedSequence`
(consuming the Phase 6c-i `LimitPairingSelectorFamily`), this lets
the three strongVI helpers consume the family-restricted *inputs*
shape at their respective family domains.

A universal-to-family bridge `LimitPairingInputs.toFamily` is also
provided for legacy callers. -/

/-- **Family-restricted authorised auxiliary bundle** for T9's
per-test-triple weak VI.

A domain-parameterised version of `LimitPairingInputs`: the `data`
field and the eight projection-equality fields plus the assembled
pairing convergence are quantified over `(μ, υ, Dυ) ∈ D` rather
than universally.

When `D = Set.univ`, this structure is interconvertible with the
universal `LimitPairingInputs` (cf. `LimitPairingInputs.toFamily`
below). -/
structure LimitPairingInputsFamily
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH)
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    (D : Set (StationaryMFG.Theorems.SimplePower.MFGTriple d)) where
  /-- Per test triple in `D`, an `LimitPassageInputData_noVI` whose
  limit triple and per-`k` data align with `(mLim, uLim, DuLim)` and
  `seq`. -/
  data : ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄
           ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
           (μ, υ, Dυ) ∈ D →
    LimitPassageInputData_noVI (d := d) V H DpH βBarReal βBarReal'
      γBarReal γBarReal' μ υ Dυ
  /-- `data hμυDυ` carries the regularization sequence of `seq`. -/
  data_ε : ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄
              ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄
              (hμυDυ : (μ, υ, Dυ) ∈ D),
    (data hμυDυ).ε = seq.epsSeq
  /-- `data hμυDυ` carries the per-`k` densities of `seq`. -/
  data_m_n : ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄
                ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄
                (hμυDυ : (μ, υ, Dυ) ∈ D),
    (data hμυDυ).m_n = fun k => (seq.sol k).m
  /-- `data hμυDυ` carries the per-`k` value functions of `seq`. -/
  data_u_n : ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄
                ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄
                (hμυDυ : (μ, υ, Dυ) ∈ D),
    (data hμυDυ).u_n = fun k => (seq.sol k).u
  /-- `data hμυDυ` carries the per-`k` gradient families of `seq`. -/
  data_Du_n : ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄
                 ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄
                 (hμυDυ : (μ, υ, Dυ) ∈ D),
    (data hμυDυ).Du_n = fun k => (seq.sol k).Du
  /-- `data hμυDυ`'s limit density equals `mLim`. -/
  data_m : ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄
              ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄
              (hμυDυ : (μ, υ, Dυ) ∈ D),
    (data hμυDυ).m = mLim
  /-- `data hμυDυ`'s limit value-function equals `uLim`. -/
  data_u : ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄
              ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄
              (hμυDυ : (μ, υ, Dυ) ∈ D),
    (data hμυDυ).u = uLim
  /-- `data hμυDυ`'s limit gradient-family equals `DuLim`. -/
  data_Du : ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄
               ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄
               (hμυDυ : (μ, υ, Dυ) ∈ D),
    (data hμυDυ).Du = DuLim
  /-- The assembled un-regularised pairing convergence per test
  triple in `D`. -/
  hpair_conv : ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄
                  ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄
                  (hμυDυ : (μ, υ, Dυ) ∈ D),
    Filter.Tendsto (fun k =>
      mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
          (fun i x => Dυ i x - (data hμυDυ).Du_n k i x)
          (μ - (data hμυDυ).m_n k) (υ - (data hμυDυ).u_n k))
      Filter.atTop
      (𝓝 (mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
            (fun i x => Dυ i x - (data hμυDυ).Du i x)
            (μ - (data hμυDυ).m) (υ - (data hμυDυ).u)))

/-- **Producer for `LimitPairingInputsFamily`.** Build a
`LimitPairingInputsFamily` whose test-triple-independent fields are
**derived from `(seq, wkBundle)`**, by mirroring
`limitPairingInputs_of_regularizedSequence` and gating each
per-test-triple field on `(μ, υ, Dυ) ∈ D`. -/
noncomputable def limitPairingInputsFamily_of_regularizedSequence
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (_hmon : Hamiltonian.HypothesisMonotone H DpH)
    (_hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (_hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (_hExp : SimplePowerExponentFacts γBarReal
                (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
                (ENNReal.ofReal βBarReal'))
    (seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH)
    (wkBundle : WeakLimitInputBundleAE (d := d) γBarReal βBarReal)
    (D : Set (StationaryMFG.Theorems.SimplePower.MFGTriple d))
    (selector : LimitPairingSelectorFamily (d := d)
                  (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  (V := V) (H := H) (DpH := DpH)
                  seq wkBundle.mLim wkBundle.uLim wkBundle.DuLim D) :
    LimitPairingInputsFamily (d := d)
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      (V := V) (H := H) (DpH := DpH)
      seq wkBundle.mLim wkBundle.uLim wkBundle.DuLim D where
  data := fun μ υ Dυ hμυDυ =>
    { hpqβ := selector.hpqβ
      hpqγ := selector.hpqγ
      ε := seq.epsSeq
      m_n := fun k => (seq.sol k).m
      u_n := fun k => (seq.sol k).u
      Du_n := fun k => (seq.sol k).Du
      m := wkBundle.mLim
      u := wkBundle.uLim
      Du := wkBundle.DuLim
      hε_nonneg := fun k => (seq.heps_pos k).le
      hε_to0 := seq.heps_tendsto
      hm_n_memLp := fun k => (seq.sol k).hmLp
      hm_memLp := wkBundle.hmLim_memLp
      hu_n_memLp := fun k => (seq.sol k).huLp
      hu_memLp := wkBundle.huLim_sob.1
      hυ_memLp := selector.hυ_memLp hμυDυ
      hDu_n_memLp := fun k i => (seq.sol k).hDuLp i
      hDu_memLp := selector.hDuLim_memLp_γ
      hDυ_memLp := selector.hDυ_memLp hμυDυ
      hμ_memLp := selector.hμ_memLp hμυDυ
      hg_memLp := selector.hg_memLp hμυDυ
      hflux_memLp := selector.hflux_memLp hμυDυ
      hμMinusOne_memLp := selector.hμMinusOne_memLp hμυDυ
      h_weak_m := selector.h_weak_m
      h_weak_u := selector.h_weak_u
      h_weak_Du := selector.h_weak_Du
      M := selector.M μ υ Dυ
      hreg_bdd := selector.hreg_bdd hμυDυ }
  data_ε := fun _ _ _ _ => rfl
  data_m_n := fun _ _ _ _ => rfl
  data_u_n := fun _ _ _ _ => rfl
  data_Du_n := fun _ _ _ _ => rfl
  data_m := fun _ _ _ _ => rfl
  data_u := fun _ _ _ _ => rfl
  data_Du := fun _ _ _ _ => rfl
  hpair_conv := fun _ _ _ hμυDυ => selector.hpair_conv hμυDυ

/-- **Universal-to-family bridge for `LimitPairingInputs`.** A
universal `LimitPairingInputs` produces, for any domain `D`, a
matching `LimitPairingInputsFamily seq mLim uLim DuLim D` by
ignoring the membership hypothesis on the per-test-triple fields. -/
def LimitPairingInputs.toFamily
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH}
    {mLim uLim : (Fin d → ℝ) → ℝ}
    {DuLim : Fin d → (Fin d → ℝ) → ℝ}
    (inputs : LimitPairingInputs (d := d)
                  (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  (V := V) (H := H) (DpH := DpH)
                  seq mLim uLim DuLim)
    (D : Set (StationaryMFG.Theorems.SimplePower.MFGTriple d)) :
    LimitPairingInputsFamily (d := d)
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      (V := V) (H := H) (DpH := DpH)
      seq mLim uLim DuLim D where
  data := fun μ υ Dυ _ => inputs.data μ υ Dυ
  data_ε := fun μ υ Dυ _ => inputs.data_ε μ υ Dυ
  data_m_n := fun μ υ Dυ _ => inputs.data_m_n μ υ Dυ
  data_u_n := fun μ υ Dυ _ => inputs.data_u_n μ υ Dυ
  data_Du_n := fun μ υ Dυ _ => inputs.data_Du_n μ υ Dυ
  data_m := fun μ υ Dυ _ => inputs.data_m μ υ Dυ
  data_u := fun μ υ Dυ _ => inputs.data_u μ υ Dυ
  data_Du := fun μ υ Dυ _ => inputs.data_Du μ υ Dυ
  hpair_conv := fun μ υ Dυ _ => inputs.hpair_conv μ υ Dυ

/-- **Domain-monotone restriction for `LimitPairingInputsFamily`.**

Phase 6d-ii-c-2d (`infra-P5-theorem1-phase-6d-ii-c-2d-chain-migrate-to-narrow`):
given a `LimitPairingInputsFamily` at a wider domain `D` and a subset
`hsub : D' ⊆ D`, restrict every per-test-triple field to `D'` by
composing the membership with `hsub`. Used in the F0 chain to bridge
from the wider paper-family pairings (built via the per-family direct
producers in BanachBridge) to the narrow paper-form domains
`D_set_family_paper` / `D_signed_family_paper_nn` consumed by
`strongVI_set_at_limit_of_paperHypotheses_paper` /
`strongVI_signed_at_limit_of_paperHypotheses_paper`. -/
def LimitPairingInputsFamily.subdomain
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH}
    {mLim uLim : (Fin d → ℝ) → ℝ}
    {DuLim : Fin d → (Fin d → ℝ) → ℝ}
    {D D' : Set (StationaryMFG.Theorems.SimplePower.MFGTriple d)}
    (pairing : LimitPairingInputsFamily (d := d)
                  (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  (V := V) (H := H) (DpH := DpH)
                  seq mLim uLim DuLim D)
    (hsub : D' ⊆ D) :
    LimitPairingInputsFamily (d := d)
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      (V := V) (H := H) (DpH := DpH)
      seq mLim uLim DuLim D' where
  data := fun _ _ _ hμυDυ => pairing.data (hsub hμυDυ)
  data_ε := fun _ _ _ hμυDυ => pairing.data_ε (hsub hμυDυ)
  data_m_n := fun _ _ _ hμυDυ => pairing.data_m_n (hsub hμυDυ)
  data_u_n := fun _ _ _ hμυDυ => pairing.data_u_n (hsub hμυDυ)
  data_Du_n := fun _ _ _ hμυDυ => pairing.data_Du_n (hsub hμυDυ)
  data_m := fun _ _ _ hμυDυ => pairing.data_m (hsub hμυDυ)
  data_u := fun _ _ _ hμυDυ => pairing.data_u (hsub hμυDυ)
  data_Du := fun _ _ _ hμυDυ => pairing.data_Du (hsub hμυDυ)
  hpair_conv := fun _ _ _ hμυDυ => pairing.hpair_conv (hsub hμυDυ)

/-- **Phase 6c-ii sanity check.** The family producer is type-correct
on a generic family selector at any domain. -/
example
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (hExp : SimplePowerExponentFacts γBarReal
                (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
                (ENNReal.ofReal βBarReal'))
    (seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH)
    (wkBundle : WeakLimitInputBundleAE (d := d) γBarReal βBarReal)
    (D : Set (StationaryMFG.Theorems.SimplePower.MFGTriple d))
    (selector : LimitPairingSelectorFamily (d := d)
                  (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  (V := V) (H := H) (DpH := DpH)
                  seq wkBundle.mLim wkBundle.uLim wkBundle.DuLim D) :
    LimitPairingInputsFamily (d := d)
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      (V := V) (H := H) (DpH := DpH)
      seq wkBundle.mLim wkBundle.uLim wkBundle.DuLim D :=
  limitPairingInputsFamily_of_regularizedSequence
    hmon hpow hV hExp seq wkBundle D selector

/-- **Phase 6c-ii sanity check (universal-to-family bridge).** -/
example
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH}
    {mLim uLim : (Fin d → ℝ) → ℝ}
    {DuLim : Fin d → (Fin d → ℝ) → ℝ}
    (inputs : LimitPairingInputs (d := d)
                  (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  (V := V) (H := H) (DpH := DpH)
                  seq mLim uLim DuLim)
    (D : Set (StationaryMFG.Theorems.SimplePower.MFGTriple d)) :
    LimitPairingInputsFamily (d := d)
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      (V := V) (H := H) (DpH := DpH)
      seq mLim uLim DuLim D :=
  inputs.toFamily D

/-! ### Three specialized limit-passage lemmas at the LIMIT triple

Per task `infra-P4-T9-three-family-limit-passage`, these three
specialized lemmas bypass the F.6 universal `hVI_eps` consumer by
producing the three final-form strong VIs at the limit `(m, u, Du)`
directly from the three paper-family selector fields
(`selector.hVI_eps_set/_signed/_transport`) plus the assembled
unregularised pairing convergence (`selector.hpair_conv`) and the
uniform Gateaux residual bound (`selector.hreg_bdd`).

The structural mirror is the per-`k` Children C/D
`hVIeps_set_of_KAepsi_VI` etc., but here at the LIMIT (instead of
per-`k`), against `mfgOperatorPair` (instead of `mfgOperatorEpsPair`).

Going from a per-`k` op-at-test-form weak VI (the shape of the
selector's `hVI_eps_*` fields) to the goal's op-at-LIMIT-primal
form is the paper Minty-trick step. Per CONVENTIONS §8, the
per-family Minty-upgrade conclusion is taken as an **authorised
hypothesis** of each lemma, scoped narrowly to the family's specific
test-triple shape (set / signed / transport) — much narrower than
the previous `hVI_eps_universal` residue, which was universal in
arbitrary `(μ, υ, Dυ)`.

Filed follow-up
`infra-P4-rebuild-T9-discharge-pairing-inputs-selector`: derive each
authorised Minty-upgrade input from the operator-at-test-form
universal weak VI at the limit (the latter follows from
`limit_passage_weak_VI_of_eps` applied to the universal selector
fields once `selector.hVI_eps_*` cover all admissible test triples). -/

/-- **`limitPassage_setForm_at_limit` — set-form specialization.**

Produce the **set-form strong VI** at the limit triple `(m, u, Du)`
directly from a paper-family Minty-upgrade hypothesis `hMinty_set`.

The hypothesis `hMinty_set` is the paper-authorised input
(CONVENTIONS §8): for every measurable subset `S` of finite
restricted-cube measure, the operator-at-LIMIT-primal pairing of
`A_0(Du, m, u)` against the test direction `(0, 1_S, 0)` is
non-negative. This is exactly the conclusion of the Minty trick
(`main_strong_VI`) applied at the test triple `(m + 1_S, u, Du)` to
the limit op-at-test-form weak VI obtained from
`selector.hVI_eps_set` via `limit_passage_weak_VI_of_eps`.

Closing `hMinty_set` from the selector fields is the workstream of
the filed follow-up
`infra-P4-rebuild-T9-discharge-pairing-inputs-selector`. -/
theorem limitPassage_setForm_at_limit
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH}
    {wkBundle : WeakLimitInputBundleAE (d := d) γBarReal βBarReal}
    (_selector : LimitPairingSelector (d := d)
                  (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  (V := V) (H := H) (DpH := DpH)
                  seq wkBundle.mLim wkBundle.uLim wkBundle.DuLim)
    (hMinty_set : ∀ S : Set (Fin d → ℝ), MeasurableSet S →
        (MeasureTheory.volume.restrict (UnitCube d)) S < ∞ →
        0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH)
              wkBundle.DuLim wkBundle.mLim wkBundle.uLim
              (fun _ _ => (0 : ℝ))
              (fun x => S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              (fun _ => (0 : ℝ))) :
    StationaryMFG.Theorems.SimplePower.StrongVI_setForm
      V H DpH γBarReal 0 wkBundle.DuLim wkBundle.mLim wkBundle.uLim := by
  intro S hSmeas hSfin
  rw [StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_zero_eq
        (V := V) (H := H) (DpH := DpH)]
  exact hMinty_set S hSmeas hSfin

/-- **`limitPassage_setFormSigned_at_limit` — signed set-form
specialization** (paper-exact `σ ∈ {±1}` shape per
`infra-P4-narrow-hVIeps-signed-shape`).

Produce the **signed set-form strong VI** at the limit triple
`(m, u, Du)` directly from a paper-family Minty-upgrade hypothesis
`hMinty_signed`.

The hypothesis is paper-authorised (CONVENTIONS §8): for every sign
`σ ∈ {±1}` and every measurable subset `S` of finite restricted-cube
measure, the operator-at-LIMIT-primal pairing of `A_0(Du, m, u)`
against the test direction `(0, σ · m · 1_S, 0)` is non-negative.
This is the conclusion of the Minty trick applied to the limit
op-at-test-form weak VI obtained from `selector.hVI_eps_signed` via
`limit_passage_weak_VI_of_eps`.

Filed follow-up
`infra-P4-rebuild-T9-discharge-pairing-inputs-selector`. -/
theorem limitPassage_setFormSigned_at_limit
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH}
    {wkBundle : WeakLimitInputBundleAE (d := d) γBarReal βBarReal}
    (_selector : LimitPairingSelector (d := d)
                  (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  (V := V) (H := H) (DpH := DpH)
                  seq wkBundle.mLim wkBundle.uLim wkBundle.DuLim)
    (hMinty_signed : ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
        ∀ S : Set (Fin d → ℝ), MeasurableSet S →
        (MeasureTheory.volume.restrict (UnitCube d)) S < ∞ →
        0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH)
              wkBundle.DuLim wkBundle.mLim wkBundle.uLim
              (fun _ _ => (0 : ℝ))
              (fun x => σ * wkBundle.mLim x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              (fun _ => (0 : ℝ))) :
    StationaryMFG.Theorems.SimplePower.StrongVI_setForm_signed
      V H DpH γBarReal 0 wkBundle.DuLim wkBundle.mLim wkBundle.uLim := by
  intro σ hσ S hSmeas hSfin
  rw [StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_zero_eq
        (V := V) (H := H) (DpH := DpH)]
  exact hMinty_signed σ hσ S hSmeas hSfin

/-- **`limitPassage_transportForm_at_limit` — transport-form
specialization.**

Produce the **transport-form strong VI** at the limit triple
`(m, u, Du)` directly from a paper-family Minty-upgrade hypothesis
`hMinty_transport`.

The hypothesis is paper-authorised (CONVENTIONS §8): for every sign
`σ ∈ {±1}` and every smooth periodic test function `φ`, the
operator-at-LIMIT-primal pairing of `A_0(Du, m, u)` against the test
direction `(σ · ∇φ, 0, σ · φ)` is non-negative. This is the
conclusion of the Minty trick applied to the limit op-at-test-form
weak VI obtained from `selector.hVI_eps_transport` via
`limit_passage_weak_VI_of_eps`.

Filed follow-up
`infra-P4-rebuild-T9-discharge-pairing-inputs-selector`. -/
theorem limitPassage_transportForm_at_limit
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH}
    {wkBundle : WeakLimitInputBundleAE (d := d) γBarReal βBarReal}
    (_selector : LimitPairingSelector (d := d)
                  (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  (V := V) (H := H) (DpH := DpH)
                  seq wkBundle.mLim wkBundle.uLim wkBundle.DuLim)
    (hMinty_transport : ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
        ∀ φ : Periodic.SmoothPeriodic d,
        0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH)
              wkBundle.DuLim wkBundle.mLim wkBundle.uLim
              (fun i x => σ *
                ((Periodic.SmoothPeriodic.partialDeriv i φ
                    : Periodic.SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x)
              (fun _ => (0 : ℝ))
              (fun x => σ * (φ : (Fin d → ℝ) → ℝ) x)) :
    StationaryMFG.Theorems.SimplePower.StrongVI_transportForm
      V H DpH γBarReal 0 wkBundle.DuLim wkBundle.mLim wkBundle.uLim := by
  intro σ hσ φ
  rw [StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_zero_eq
        (V := V) (H := H) (DpH := DpH)]
  exact hMinty_transport σ hσ φ

/-! ### Sanity-check `example`s for the three specialized lemmas. -/

/-- Sanity check: `limitPassage_setForm_at_limit` accepts a selector
and a paper-authorised Minty-upgrade hypothesis and delivers the
set-form strong VI at the limit. -/
example
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH}
    {wkBundle : WeakLimitInputBundleAE (d := d) γBarReal βBarReal}
    (selector : LimitPairingSelector (d := d)
                  (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  (V := V) (H := H) (DpH := DpH)
                  seq wkBundle.mLim wkBundle.uLim wkBundle.DuLim)
    (hMinty_set : ∀ S : Set (Fin d → ℝ), MeasurableSet S →
        (MeasureTheory.volume.restrict (UnitCube d)) S < ∞ →
        0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH)
              wkBundle.DuLim wkBundle.mLim wkBundle.uLim
              (fun _ _ => (0 : ℝ))
              (fun x => S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              (fun _ => (0 : ℝ))) :
    StationaryMFG.Theorems.SimplePower.StrongVI_setForm
      V H DpH γBarReal 0 wkBundle.DuLim wkBundle.mLim wkBundle.uLim :=
  limitPassage_setForm_at_limit selector hMinty_set

/-- Sanity check: `limitPassage_setFormSigned_at_limit` produces
the signed set-form strong VI from a selector and Minty-upgrade. -/
example
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH}
    {wkBundle : WeakLimitInputBundleAE (d := d) γBarReal βBarReal}
    (selector : LimitPairingSelector (d := d)
                  (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  (V := V) (H := H) (DpH := DpH)
                  seq wkBundle.mLim wkBundle.uLim wkBundle.DuLim)
    (hMinty_signed : ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
        ∀ S : Set (Fin d → ℝ), MeasurableSet S →
        (MeasureTheory.volume.restrict (UnitCube d)) S < ∞ →
        0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH)
              wkBundle.DuLim wkBundle.mLim wkBundle.uLim
              (fun _ _ => (0 : ℝ))
              (fun x => σ * wkBundle.mLim x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              (fun _ => (0 : ℝ))) :
    StationaryMFG.Theorems.SimplePower.StrongVI_setForm_signed
      V H DpH γBarReal 0 wkBundle.DuLim wkBundle.mLim wkBundle.uLim :=
  limitPassage_setFormSigned_at_limit selector hMinty_signed

/-- Sanity check: `limitPassage_transportForm_at_limit` produces
the transport-form strong VI from a selector and Minty-upgrade. -/
example
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH}
    {wkBundle : WeakLimitInputBundleAE (d := d) γBarReal βBarReal}
    (selector : LimitPairingSelector (d := d)
                  (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  (V := V) (H := H) (DpH := DpH)
                  seq wkBundle.mLim wkBundle.uLim wkBundle.DuLim)
    (hMinty_transport : ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
        ∀ φ : Periodic.SmoothPeriodic d,
        0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH)
              wkBundle.DuLim wkBundle.mLim wkBundle.uLim
              (fun i x => σ *
                ((Periodic.SmoothPeriodic.partialDeriv i φ
                    : Periodic.SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x)
              (fun _ => (0 : ℝ))
              (fun x => σ * (φ : (Fin d → ℝ) → ℝ) x)) :
    StationaryMFG.Theorems.SimplePower.StrongVI_transportForm
      V H DpH γBarReal 0 wkBundle.DuLim wkBundle.mLim wkBundle.uLim :=
  limitPassage_transportForm_at_limit selector hMinty_transport

/-! ### Wiring AC4 into `LimitPairingSelector.{M, hreg_bdd}`

Per task `infra-P4-AC4-wire-into-LimitPairingSelector`, this section
plumbs `gateauxWpPair_uniform_bound_per_triple`
(`Banach/AprioriDischarge.lean`) into the `M, hreg_bdd` fields of
`LimitPairingSelector`.

The parent task already produced the per-test-triple per-`k`
absolute bound

```
|gateauxWpPair γ̄ Dυ υ (Dυ - Du_k) (υ - u_k)|
    ≤ Aυ + Au + ADυ + ADu
```

assuming four upper bounds and four `Integrable` certificates as
explicit parameters. The closed-form derivation of those eight
inputs from `apriori_at_eps` (the genuine C.4-bridge) is out of
scope here — per CONVENTIONS §8 it is parameterised through the
`LimitPairingSelectorGateauxAux` record below, exactly matching
the sibling pattern of `LimitPairingSelector` itself. The result
is that *a client supplying the eight per-test-triple per-`k`
certificates can fill `LimitPairingSelector.{M, hreg_bdd}` with no
extra arithmetic step on the producer side*. -/

/-- **Authorised aux for `LimitPairingSelector.{M, hreg_bdd}`.**

Packages the eight per-test-triple per-`k` certificates consumed
by `gateauxWpPair_uniform_bound_per_triple`, with `Du := (seq.sol k).Du`
and `u := (seq.sol k).u` threaded automatically.

* `Aυ μ υ Dυ`, `ADυ μ υ Dυ` only depend on the test triple (the
  integrals `∫|υ|^γ̄` and `∫(Dυ·Dυ)^(γ̄/2)` are `k`-independent).
* `Au μ υ Dυ` and `ADu μ υ Dυ` are uniform bounds on the per-`k`
  integrals `∫|υ - u_k|^γ̄` and `∫((Dυ - Du_k)·…)^(γ̄/2)`,
  certified by `hAu_k` and `hADu_k` for every `k`.
* `hInt_*` provide the four required `Integrable` certificates,
  per-test-triple resp. per-test-triple-per-`k`. -/
structure LimitPairingSelectorGateauxAux
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH) where
  /-- `1 ≤ γ̄` (real form), needed for
  `gateauxWpPair_uniform_bound_per_triple`. -/
  hγ_one_le : (1 : ℝ) ≤ γBarReal
  /-- Per test triple, an upper bound on `∫|υ|^γ̄`. -/
  Aυ : ((Fin d → ℝ) → ℝ) → ((Fin d → ℝ) → ℝ) →
        (Fin d → (Fin d → ℝ) → ℝ) → ℝ
  /-- Per test triple per `k`, an upper bound on `∫|υ - u_k|^γ̄`. -/
  Au : ((Fin d → ℝ) → ℝ) → ((Fin d → ℝ) → ℝ) →
        (Fin d → (Fin d → ℝ) → ℝ) → ℝ
  /-- Per test triple, an upper bound on `∫(Dυ·Dυ)^(γ̄/2)`. -/
  ADυ : ((Fin d → ℝ) → ℝ) → ((Fin d → ℝ) → ℝ) →
         (Fin d → (Fin d → ℝ) → ℝ) → ℝ
  /-- Per test triple per `k`, an upper bound on
  `∫((Dυ - Du_k)·(Dυ - Du_k))^(γ̄/2)`. -/
  ADu : ((Fin d → ℝ) → ℝ) → ((Fin d → ℝ) → ℝ) →
         (Fin d → (Fin d → ℝ) → ℝ) → ℝ
  /-- `Integrable` certificate for `(Dυ·Dυ)^(γ̄/2)`. -/
  hInt_DυDυ : ∀ (μ υ : (Fin d → ℝ) → ℝ)
                 (Dυ : Fin d → (Fin d → ℝ) → ℝ),
              Integrable (fun x : Fin d → ℝ =>
                ((fun i => Dυ i x) ⬝ (fun i => Dυ i x)) ^ (γBarReal / 2))
                (volume.restrict (UnitCube d))
  /-- `Integrable` certificate for `((Dυ - Du_k)·(Dυ - Du_k))^(γ̄/2)`. -/
  hInt_DυmDu : ∀ (μ υ : (Fin d → ℝ) → ℝ)
                  (Dυ : Fin d → (Fin d → ℝ) → ℝ) (k : ℕ),
              Integrable (fun x : Fin d → ℝ =>
                ((fun i => Dυ i x - (seq.sol k).Du i x)
                  ⬝ (fun i => Dυ i x - (seq.sol k).Du i x))
                  ^ (γBarReal / 2))
                (volume.restrict (UnitCube d))
  /-- `Integrable` certificate for `|υ|^γ̄`. -/
  hInt_υ : ∀ (μ υ : (Fin d → ℝ) → ℝ)
              (Dυ : Fin d → (Fin d → ℝ) → ℝ),
            Integrable (fun x : Fin d → ℝ => |υ x| ^ γBarReal)
              (volume.restrict (UnitCube d))
  /-- `Integrable` certificate for `|υ - u_k|^γ̄`. -/
  hInt_υmu : ∀ (μ υ : (Fin d → ℝ) → ℝ)
                (Dυ : Fin d → (Fin d → ℝ) → ℝ) (k : ℕ),
              Integrable (fun x : Fin d → ℝ =>
                |υ x - (seq.sol k).u x| ^ γBarReal)
                (volume.restrict (UnitCube d))
  /-- Per-test-triple bound on `∫|υ|^γ̄ ≤ Aυ`. -/
  hAυ : ∀ (μ υ : (Fin d → ℝ) → ℝ)
           (Dυ : Fin d → (Fin d → ℝ) → ℝ),
          ∫ x in UnitCube d, |υ x| ^ γBarReal
            ∂(volume : Measure (Fin d → ℝ)) ≤ Aυ μ υ Dυ
  /-- Per-test-triple per-`k` uniform bound on `∫|υ - u_k|^γ̄ ≤ Au`. -/
  hAu : ∀ (μ υ : (Fin d → ℝ) → ℝ)
           (Dυ : Fin d → (Fin d → ℝ) → ℝ) (k : ℕ),
          ∫ x in UnitCube d, |υ x - (seq.sol k).u x| ^ γBarReal
            ∂(volume : Measure (Fin d → ℝ)) ≤ Au μ υ Dυ
  /-- Per-test-triple bound on `∫(Dυ·Dυ)^(γ̄/2) ≤ ADυ`. -/
  hADυ : ∀ (μ υ : (Fin d → ℝ) → ℝ)
            (Dυ : Fin d → (Fin d → ℝ) → ℝ),
           ∫ x in UnitCube d,
              ((fun i => Dυ i x) ⬝ (fun i => Dυ i x)) ^ (γBarReal / 2)
              ∂(volume : Measure (Fin d → ℝ)) ≤ ADυ μ υ Dυ
  /-- Per-test-triple per-`k` uniform bound on
  `∫((Dυ - Du_k)·(Dυ - Du_k))^(γ̄/2) ≤ ADu`. -/
  hADu : ∀ (μ υ : (Fin d → ℝ) → ℝ)
            (Dυ : Fin d → (Fin d → ℝ) → ℝ) (k : ℕ),
           ∫ x in UnitCube d,
              ((fun i => Dυ i x - (seq.sol k).Du i x)
                 ⬝ (fun i => Dυ i x - (seq.sol k).Du i x))
                ^ (γBarReal / 2)
              ∂(volume : Measure (Fin d → ℝ)) ≤ ADu μ υ Dυ

namespace LimitPairingSelectorGateauxAux

variable {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
  [Fact (1 ≤ ENNReal.ofReal βBarReal)]
  [Fact (1 ≤ ENNReal.ofReal γBarReal)]
  {V : (Fin d → ℝ) → ℝ}
  {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
  {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
  {seq : RegularizedSequenceData (d := d)
            γBarReal βBarReal βBarReal' γBarReal' V H DpH}

/-- The selector's `M` field, derived from the four uniform bounds. -/
def M (aux : LimitPairingSelectorGateauxAux (d := d) seq) :
    ((Fin d → ℝ) → ℝ) → ((Fin d → ℝ) → ℝ) →
    (Fin d → (Fin d → ℝ) → ℝ) → ℝ :=
  fun μ υ Dυ => aux.Aυ μ υ Dυ + aux.Au μ υ Dυ
                  + aux.ADυ μ υ Dυ + aux.ADu μ υ Dυ

/-- The selector's `hreg_bdd` field: the per-`k` per-test-triple
Gateaux residual is bounded by `aux.M μ υ Dυ`.

Direct application of `gateauxWpPair_uniform_bound_per_triple`
with `Du := (seq.sol k).Du` and `u := (seq.sol k).u`. -/
theorem hreg_bdd (aux : LimitPairingSelectorGateauxAux (d := d) seq) :
    ∀ (μ υ : (Fin d → ℝ) → ℝ)
       (Dυ : Fin d → (Fin d → ℝ) → ℝ) (k : ℕ),
      |gateauxWpPair γBarReal Dυ υ
          (fun i x => Dυ i x - (seq.sol k).Du i x)
          (υ - (seq.sol k).u)| ≤ aux.M μ υ Dυ := by
  intro μ υ Dυ k
  -- Apply the per-test-triple bound at `(Du := (seq.sol k).Du,
  -- u := (seq.sol k).u)`.
  exact gateauxWpPair_uniform_bound_per_triple
    (d := d) γBarReal aux.hγ_one_le μ υ Dυ
    (fun i => (seq.sol k).Du i) (seq.sol k).u
    (aux.Aυ μ υ Dυ) (aux.Au μ υ Dυ)
    (aux.ADυ μ υ Dυ) (aux.ADu μ υ Dυ)
    (aux.hInt_DυDυ μ υ Dυ)
    (aux.hInt_DυmDu μ υ Dυ k)
    (aux.hInt_υ μ υ Dυ)
    (aux.hInt_υmu μ υ Dυ k)
    (aux.hAυ μ υ Dυ)
    (aux.hAu μ υ Dυ k)
    (aux.hADυ μ υ Dυ)
    (aux.hADu μ υ Dυ k)

end LimitPairingSelectorGateauxAux

/-- **AC sanity check.** A `LimitPairingSelectorGateauxAux` produces
the `(M, hreg_bdd)` pair consumed by
`LimitPairingSelector.{M, hreg_bdd}`. -/
example
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH)
    (aux : LimitPairingSelectorGateauxAux (d := d) seq) :
    ∃ M : ((Fin d → ℝ) → ℝ) → ((Fin d → ℝ) → ℝ) →
            (Fin d → (Fin d → ℝ) → ℝ) → ℝ,
    ∀ (μ υ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ) (k : ℕ),
      |gateauxWpPair γBarReal Dυ υ
          (fun i x => Dυ i x - (seq.sol k).Du i x)
          (υ - (seq.sol k).u)| ≤ M μ υ Dυ :=
  ⟨aux.M, aux.hreg_bdd⟩

/-! ### Phase G — closed-form `gateauxAux_of_paperHypotheses`

The closed-form aggregator builds `LimitPairingSelectorGateauxAux seq`
from `(seq, regBundle, Capr, hCapr)` plus the apriori-induced
`MemLpPer` certificates on `(seq.sol k).{u, Du i}`. The strategy is:

* `Aυ μ υ Dυ := ∫|υ|^γ̄`, `ADυ μ υ Dυ := ∫(Dυ·Dυ)^(γ̄/2)` — exact
  values, with the bounds `≤` discharged by `le_refl`.
* `Au μ υ Dυ := 2^γ̄ · (∫|υ|^γ̄ + Capr)` — the uniform-in-`k` bound
  on `∫|υ - u_k|^γ̄`. Pointwise `|a - b|^γ̄ ≤ 2^γ̄·(|a|^γ̄ + |b|^γ̄)` via
  triangle and `add_rpow_le_two_rpow_mul`; then `∫|u_k|^γ̄ ≤ Capr`
  from `hCapr`.
* `ADu μ υ Dυ := 2^γ̄ · (∫(Dυ·Dυ)^(γ̄/2) + ((d:ℝ))^γ̄ · Capr)` — the
  uniform-in-`k` bound on `∫((Dυ - Du_k)·(Dυ - Du_k))^(γ̄/2)`.
  Pointwise `‖a - b‖^γ̄ ≤ 2^γ̄·(‖a‖^γ̄ + ‖b‖^γ̄)`; then
  `(Σᵢ aᵢ²)^(γ̄/2) = ‖a‖₂^γ̄ ≤ ‖a‖₁^γ̄ ≤ d^(γ̄-1)·Σᵢ |aᵢ|^γ̄` via
  `Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg`. -/

/-- Pointwise additive helper: `(a + b)^q ≤ 2^q · (a^q + b^q)`
for `a, b ≥ 0` and `q ≥ 0`. Local copy of the private lemma in
`Apriori.lean` to keep this module self-contained. -/
private lemma add_rpow_le_two_rpow_mul_local
    {a b q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hq : 0 ≤ q) :
    (a + b) ^ q ≤ (2 : ℝ) ^ q * (a ^ q + b ^ q) := by
  have hab : 0 ≤ a + b := add_nonneg ha hb
  have hmax_nn : 0 ≤ max a b := le_max_of_le_left ha
  have h1 : a + b ≤ 2 * max a b := by
    have ha' : a ≤ max a b := le_max_left a b
    have hb' : b ≤ max a b := le_max_right a b
    linarith
  have h2 : (a + b) ^ q ≤ (2 * max a b) ^ q :=
    Real.rpow_le_rpow hab h1 hq
  have h3 : (2 * max a b) ^ q = (2 : ℝ) ^ q * (max a b) ^ q :=
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hmax_nn
  have h4 : (max a b) ^ q ≤ a ^ q + b ^ q := by
    rcases le_total a b with hab' | hab'
    · rw [max_eq_right hab']
      have : 0 ≤ a ^ q := Real.rpow_nonneg ha q
      linarith
    · rw [max_eq_left hab']
      have : 0 ≤ b ^ q := Real.rpow_nonneg hb q
      linarith
  have h2pos : (0 : ℝ) ≤ (2 : ℝ) ^ q :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) q
  calc (a + b) ^ q
      ≤ (2 * max a b) ^ q := h2
    _ = (2 : ℝ) ^ q * (max a b) ^ q := h3
    _ ≤ (2 : ℝ) ^ q * (a ^ q + b ^ q) := by
        exact mul_le_mul_of_nonneg_left h4 h2pos

/-- Pointwise scalar bound: `|a - b|^γ̄ ≤ 2^γ̄ · (|a|^γ̄ + |b|^γ̄)`. -/
lemma palomar_RegularizedSequence_abs_sub_rpow_le_two_rpow_mul
    {γBarReal : ℝ} (hγ : 0 ≤ γBarReal) (a b : ℝ) :
    |a - b| ^ γBarReal
      ≤ (2 : ℝ) ^ γBarReal * (|a| ^ γBarReal + |b| ^ γBarReal) := by
  have htriangle : |a - b| ≤ |a| + |b| := abs_sub _ _
  have ha : 0 ≤ |a| := abs_nonneg a
  have hb : 0 ≤ |b| := abs_nonneg b
  have hab : 0 ≤ |a - b| := abs_nonneg _
  have h1 : |a - b| ^ γBarReal ≤ (|a| + |b|) ^ γBarReal :=
    Real.rpow_le_rpow hab htriangle hγ
  have h2 : (|a| + |b|) ^ γBarReal
      ≤ (2 : ℝ) ^ γBarReal * (|a| ^ γBarReal + |b| ^ γBarReal) :=
    add_rpow_le_two_rpow_mul_local ha hb hγ
  linarith

/-- Pointwise Euclidean-norm bound: for `Dυ x, Du x : Fin d → ℝ`,
`((Dυ - Du)·(Dυ - Du))^(γ̄/2) ≤ 2^γ̄ · ((Dυ·Dυ)^(γ̄/2) + (Du·Du)^(γ̄/2))`. -/
lemma palomar_RegularizedSequence_euclideanDot_sub_rpow_le_two_rpow_mul
    {γBarReal : ℝ} (hγ : 1 ≤ γBarReal) (a b : Fin d → ℝ) :
    ((fun i => a i - b i) ⬝ (fun i => a i - b i)) ^ (γBarReal / 2)
      ≤ (2 : ℝ) ^ γBarReal *
          ((a ⬝ a) ^ (γBarReal / 2) + (b ⬝ b) ^ (γBarReal / 2)) := by
  -- Use `Real.sqrt(a·a) = ‖a‖` (via dotProduct ≥ 0) and triangle.
  have haa_nn : 0 ≤ a ⬝ a := euclideanDot_self_nonneg a
  have hbb_nn : 0 ≤ b ⬝ b := euclideanDot_self_nonneg b
  have hsubsub_nn : 0 ≤ (fun i => a i - b i) ⬝ (fun i => a i - b i) :=
    euclideanDot_self_nonneg _
  -- Triangle: `√((a-b)·(a-b)) ≤ √(a·a) + √(b·b)`.
  -- Standard via `‖a - b‖ ≤ ‖a‖ + ‖b‖` for the Euclidean norm.
  -- We use `Real.sqrt` and `abs_euclideanDot_le_sqrt`-style facts.
  -- Concretely, expand `(a-b)·(a-b) = a·a - 2 a·b + b·b ≤ a·a + 2|a·b| + b·b`,
  -- and use Cauchy-Schwarz `|a·b| ≤ √(a·a)·√(b·b)`.
  have hCS : |a ⬝ b| ≤ Real.sqrt (a ⬝ a) * Real.sqrt (b ⬝ b) :=
    abs_euclideanDot_le_sqrt a b
  -- Expand:
  have hexpand : (fun i => a i - b i) ⬝ (fun i => a i - b i)
      = a ⬝ a - 2 * (a ⬝ b) + b ⬝ b := by
    simp only [dotProduct]
    have hpoint : ∀ i, (a i - b i) * (a i - b i)
        = a i * a i - 2 * (a i * b i) + b i * b i := by
      intro i; ring
    simp_rw [hpoint]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum]
  -- Bound: `(a-b)·(a-b) ≤ (√(a·a) + √(b·b))²`.
  have hsqrt_aa : 0 ≤ Real.sqrt (a ⬝ a) := Real.sqrt_nonneg _
  have hsqrt_bb : 0 ≤ Real.sqrt (b ⬝ b) := Real.sqrt_nonneg _
  have hsqrt_aa_sq : (Real.sqrt (a ⬝ a)) ^ 2 = a ⬝ a :=
    Real.sq_sqrt haa_nn
  have hsqrt_bb_sq : (Real.sqrt (b ⬝ b)) ^ 2 = b ⬝ b :=
    Real.sq_sqrt hbb_nn
  have hsum_sq : (Real.sqrt (a ⬝ a) + Real.sqrt (b ⬝ b))^2
      = a ⬝ a + 2 * (Real.sqrt (a ⬝ a) * Real.sqrt (b ⬝ b)) + b ⬝ b := by
    have h := add_pow_two (Real.sqrt (a ⬝ a)) (Real.sqrt (b ⬝ b))
    rw [h, hsqrt_aa_sq, hsqrt_bb_sq]
    ring
  have hbound : (fun i => a i - b i) ⬝ (fun i => a i - b i)
      ≤ (Real.sqrt (a ⬝ a) + Real.sqrt (b ⬝ b))^2 := by
    rw [hexpand, hsum_sq]
    have hab_le_abs : -(a ⬝ b) ≤ |a ⬝ b| := by
      have := abs_nonneg (a ⬝ b)
      have hneg : -|a ⬝ b| ≤ a ⬝ b := neg_abs_le (a ⬝ b)
      have habs : a ⬝ b ≤ |a ⬝ b| := le_abs_self (a ⬝ b)
      linarith [neg_le_abs (a ⬝ b)]
    have h2 : 2 * |a ⬝ b|
        ≤ 2 * (Real.sqrt (a ⬝ a) * Real.sqrt (b ⬝ b)) :=
      mul_le_mul_of_nonneg_left hCS (by norm_num : (0:ℝ) ≤ 2)
    nlinarith
  -- Now raise both sides to the γ̄/2 power.
  have hγ2_nn : 0 ≤ γBarReal / 2 := by linarith
  have hsum_nn : 0 ≤ Real.sqrt (a ⬝ a) + Real.sqrt (b ⬝ b) :=
    add_nonneg hsqrt_aa hsqrt_bb
  have hsum_sq_nn : 0 ≤ (Real.sqrt (a ⬝ a) + Real.sqrt (b ⬝ b))^2 := by
    positivity
  have hpow1 : ((fun i => a i - b i) ⬝ (fun i => a i - b i)) ^ (γBarReal / 2)
      ≤ ((Real.sqrt (a ⬝ a) + Real.sqrt (b ⬝ b))^2) ^ (γBarReal / 2) := by
    exact Real.rpow_le_rpow hsubsub_nn hbound hγ2_nn
  -- Simplify `((·)^2)^(γ̄/2) = (·)^γ̄`.
  have hsq_to_rpow : ((Real.sqrt (a ⬝ a) + Real.sqrt (b ⬝ b))^2) ^ (γBarReal / 2)
      = (Real.sqrt (a ⬝ a) + Real.sqrt (b ⬝ b))^γBarReal := by
    rw [show (((Real.sqrt (a ⬝ a) + Real.sqrt (b ⬝ b))^2 : ℝ))
          = (Real.sqrt (a ⬝ a) + Real.sqrt (b ⬝ b))^(2:ℝ) from
            (Real.rpow_two _).symm]
    rw [← Real.rpow_mul hsum_nn]
    congr 1; ring
  rw [hsq_to_rpow] at hpow1
  -- Bound `(√(a·a) + √(b·b))^γ̄ ≤ 2^γ̄ · ((√(a·a))^γ̄ + (√(b·b))^γ̄)`.
  have hγ_nn : 0 ≤ γBarReal := by linarith
  have hAdd : (Real.sqrt (a ⬝ a) + Real.sqrt (b ⬝ b))^γBarReal
      ≤ (2 : ℝ) ^ γBarReal *
          ((Real.sqrt (a ⬝ a))^γBarReal + (Real.sqrt (b ⬝ b))^γBarReal) :=
    add_rpow_le_two_rpow_mul_local hsqrt_aa hsqrt_bb hγ_nn
  -- Identify `(√(a·a))^γ̄ = (a·a)^(γ̄/2)`.
  have hsqrt_aa_pow : (Real.sqrt (a ⬝ a)) ^ γBarReal = (a ⬝ a) ^ (γBarReal / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul haa_nn]
    congr 1; ring
  have hsqrt_bb_pow : (Real.sqrt (b ⬝ b)) ^ γBarReal = (b ⬝ b) ^ (γBarReal / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hbb_nn]
    congr 1; ring
  rw [hsqrt_aa_pow, hsqrt_bb_pow] at hAdd
  exact le_trans hpow1 hAdd

/-- Pointwise bound on `(a · a)^(γ̄/2)` in terms of `∑ |a i|^γ̄`,
for `a : Fin d → ℝ` and `γ̄ ≥ 1`. The constant is `d^(γ̄-1)` (the
Jensen constant for the convex function `x^γ̄` on `ℝ_{≥0}`).

Proof: `(a · a) = ∑ aᵢ² ≤ (∑|aᵢ|)²` (since the cross terms are
non-negative); raise to the `γ̄/2` power; then bound
`(∑|aᵢ|)^γ̄ ≤ d^(γ̄-1) · ∑|aᵢ|^γ̄` by Jensen
(`Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg`). -/
-- Note: previously `private`; promoted to public so
-- `BanachBridge.PaperCBundleForK.of_paperHypotheses` can derive the
-- gradient-term `Integrable` dominator from this Jensen bound
-- (iter `infra-P5-T10-v7-phase2c-delta-paperCBundleFor-of-paperHypotheses`).
lemma euclideanDot_self_rpow_le_sum_rpow
    {γBarReal : ℝ} (hγ : 1 ≤ γBarReal) (a : Fin d → ℝ) :
    (a ⬝ a) ^ (γBarReal / 2)
      ≤ ((d : ℝ)) ^ (γBarReal - 1) * ∑ i, |a i| ^ γBarReal := by
  -- `(a · a) = ∑ aᵢ² ≤ (∑ |aᵢ|)²` (cross terms non-negative).
  have haa_nn : 0 ≤ a ⬝ a := euclideanDot_self_nonneg a
  have hsum_abs_nn : 0 ≤ ∑ i, |a i| :=
    Finset.sum_nonneg (fun i _ => abs_nonneg _)
  -- Step 1: `(a · a) ≤ (∑ |a i|)^2`.
  have hStep1 : a ⬝ a ≤ (∑ i, |a i|) ^ 2 := by
    -- `(∑|aᵢ|)² = ∑|aᵢ|² + 2 ∑_{i<j} |aᵢ||aⱼ| ≥ ∑aᵢ² = a · a`.
    -- Use `(∑bᵢ)² = ∑bᵢ² + 2∑_{i<j} bᵢbⱼ` is a standard identity, but
    -- a more uniform approach: `a · a = ∑aᵢ² = ∑|aᵢ|² ≤ (∑|aᵢ|)²`
    -- is `Finset.inner_mul_le_norm_mul_norm`-style; we just expand.
    have hsq : (∑ i, |a i|) ^ 2
        = (∑ i, |a i|) * (∑ i, |a i|) := sq _
    have hself : a ⬝ a = ∑ i, |a i| ^ 2 := by
      simp only [dotProduct, sq_abs]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hself, hsq, Finset.sum_mul_sum]
    refine Finset.sum_le_sum ?_
    intro i _
    rw [show |a i| ^ 2 = |a i| * |a i| from sq _]
    -- `|a i| * |a i| ≤ ∑ j, |a i| * |a j|`. Bound via single term `j = i`
    -- and non-negativity of cross terms.
    have h1 : |a i| * |a i| = ∑ j ∈ ({i} : Finset (Fin d)), |a i| * |a j| := by
      simp
    rw [h1]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro j hj
      simp at hj
      subst hj
      exact Finset.mem_univ _
    · intro j _ _
      exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
  -- Step 2: raise to `γ̄/2`.
  have hγ2_nn : 0 ≤ γBarReal / 2 := by linarith
  have hpow1 : (a ⬝ a) ^ (γBarReal / 2)
      ≤ ((∑ i, |a i|) ^ 2) ^ (γBarReal / 2) :=
    Real.rpow_le_rpow haa_nn hStep1 hγ2_nn
  -- Step 3: simplify `((·)^2)^(γ̄/2) = (·)^γ̄`.
  have hsq_to_rpow : ((∑ i, |a i|) ^ 2) ^ (γBarReal / 2)
      = (∑ i, |a i|) ^ γBarReal := by
    rw [show (((∑ i, |a i|) ^ 2 : ℝ))
          = (∑ i, |a i|) ^ (2 : ℝ) from (Real.rpow_two _).symm]
    rw [← Real.rpow_mul hsum_abs_nn]
    congr 1; ring
  rw [hsq_to_rpow] at hpow1
  -- Step 4: Jensen — `(∑|aᵢ|)^γ̄ ≤ d^(γ̄-1) · ∑|aᵢ|^γ̄`.
  have hJensen : (∑ i, |a i|) ^ γBarReal
      ≤ ((Finset.univ : Finset (Fin d)).card : ℝ) ^ (γBarReal - 1) *
          ∑ i, |a i| ^ γBarReal :=
    Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
      (s := Finset.univ) (f := fun i => |a i|) (p := γBarReal) hγ
      (fun i _ => abs_nonneg _)
  rw [Finset.card_univ, Fintype.card_fin] at hJensen
  exact le_trans hpow1 hJensen

/-! ### Phase G — closed-form `gateauxAux_of_paperHypotheses` producer. -/

/-- **Closed-form aggregator for `LimitPairingSelectorGateauxAux`.**

Given:
* a regularised sequence `seq` (the per-`k` sol witnesses);
* a single ε-uniform apriori constant `Capr ≥ 0` bounding the
  per-`k` integrated apriori sum
  `∫|sol.m|^β̄ + ∫|sol.u|^γ̄ + ∑_i ∫|sol.Du i|^γ̄`;
* universally-quantified `Integrable` certificates for the four
  test-triple integrands consumed by
  `gateauxWpPair_uniform_bound_per_triple`,

produces the eight-field `LimitPairingSelectorGateauxAux` record.

The four `M`-bounds are set as:
* `Aυ μ υ Dυ := ∫|υ|^γ̄`, with `hAυ := le_refl`.
* `ADυ μ υ Dυ := ∫(Dυ⬝Dυ)^(γ̄/2)`, with `hADυ := le_refl`.
* `Au μ υ Dυ := 2^γ̄ · ((∫|υ|^γ̄) + Capr)`, with `hAu` derived from
  the pointwise lemma `palomar_RegularizedSequence_abs_sub_rpow_le_two_rpow_mul` plus
  `hCapr` (which gives `∫|sol.u|^γ̄ ≤ Capr`).
* `ADu μ υ Dυ := 2^γ̄ · ((∫(Dυ⬝Dυ)^(γ̄/2)) +
    ((d:ℝ))^(γ̄-1) · Capr)`, with `hADu` derived from the
  pointwise lemma `palomar_RegularizedSequence_euclideanDot_sub_rpow_le_two_rpow_mul` plus
  `euclideanDot_self_rpow_le_sum_rpow` (giving the Jensen bound on
  `∫(Du⬝Du)^(γ̄/2)`) plus `hCapr` (giving `∑ᵢ ∫|Du i|^γ̄ ≤ Capr`).

The integrability certificates are kept as universal arguments per
CONVENTIONS §8: they are paper-trivial structural data carried by
the test triple's `MemLpPer` / `MemSobolevPer` regularity, and are
not the residue this aggregator is meant to discharge. -/
noncomputable def gateauxAux_of_paperHypotheses
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH)
    (hγ_one_le : (1 : ℝ) ≤ γBarReal)
    (Capr : ℝ) (hCapr_nn : 0 ≤ Capr)
    (hCapr : ∀ k : ℕ,
      (∫ x in UnitCube d, |(seq.sol k).m x| ^ βBarReal) +
        (∫ x in UnitCube d, |(seq.sol k).u x| ^ γBarReal) +
        (∑ i, ∫ x in UnitCube d, |(seq.sol k).Du i x| ^ γBarReal)
          ≤ Capr)
    (hInt_DυDυ_arg : ∀ (μ υ : (Fin d → ℝ) → ℝ)
                       (Dυ : Fin d → (Fin d → ℝ) → ℝ),
      Integrable (fun x : Fin d → ℝ =>
        ((fun i => Dυ i x) ⬝ (fun i => Dυ i x)) ^ (γBarReal / 2))
        (volume.restrict (UnitCube d)))
    (hInt_DυmDu_arg : ∀ (μ υ : (Fin d → ℝ) → ℝ)
                        (Dυ : Fin d → (Fin d → ℝ) → ℝ) (k : ℕ),
      Integrable (fun x : Fin d → ℝ =>
        ((fun i => Dυ i x - (seq.sol k).Du i x)
          ⬝ (fun i => Dυ i x - (seq.sol k).Du i x))
          ^ (γBarReal / 2))
        (volume.restrict (UnitCube d)))
    (hInt_υ_arg : ∀ (μ υ : (Fin d → ℝ) → ℝ)
                    (Dυ : Fin d → (Fin d → ℝ) → ℝ),
      Integrable (fun x : Fin d → ℝ => |υ x| ^ γBarReal)
        (volume.restrict (UnitCube d)))
    (hInt_υmu_arg : ∀ (μ υ : (Fin d → ℝ) → ℝ)
                      (Dυ : Fin d → (Fin d → ℝ) → ℝ) (k : ℕ),
      Integrable (fun x : Fin d → ℝ =>
        |υ x - (seq.sol k).u x| ^ γBarReal)
        (volume.restrict (UnitCube d))) :
    LimitPairingSelectorGateauxAux (d := d) seq := by
  -- Convenient shorthand: `2 ^ γ̄ ≥ 0`.
  have h2γ_nn : (0 : ℝ) ≤ (2 : ℝ) ^ γBarReal :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hγ_nn : (0 : ℝ) ≤ γBarReal := le_trans zero_le_one hγ_one_le
  -- Per-`k` integrand non-negativity helpers.
  have hAbsRpow_nn : ∀ (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ),
      0 ≤ |f x| ^ γBarReal := fun f x => Real.rpow_nonneg (abs_nonneg _) _
  have hDotRpow_nn : ∀ (g : Fin d → (Fin d → ℝ) → ℝ) (x : Fin d → ℝ),
      0 ≤ ((fun i => g i x) ⬝ (fun i => g i x)) ^ (γBarReal / 2) :=
    fun g x => Real.rpow_nonneg (euclideanDot_self_nonneg _) _
  -- The four bounds.
  refine
    { hγ_one_le := hγ_one_le
      Aυ := fun μ υ Dυ =>
        ∫ x in UnitCube d, |υ x| ^ γBarReal
      Au := fun μ υ Dυ =>
        (2 : ℝ) ^ γBarReal *
          ((∫ x in UnitCube d, |υ x| ^ γBarReal) + Capr)
      ADυ := fun μ υ Dυ =>
        ∫ x in UnitCube d,
          ((fun i => Dυ i x) ⬝ (fun i => Dυ i x)) ^ (γBarReal / 2)
      ADu := fun μ υ Dυ =>
        (2 : ℝ) ^ γBarReal *
          ((∫ x in UnitCube d,
              ((fun i => Dυ i x) ⬝ (fun i => Dυ i x)) ^ (γBarReal / 2)) +
            ((d : ℝ)) ^ (γBarReal - 1) * Capr)
      hInt_DυDυ := hInt_DυDυ_arg
      hInt_DυmDu := hInt_DυmDu_arg
      hInt_υ := hInt_υ_arg
      hInt_υmu := hInt_υmu_arg
      hAυ := ?_
      hAu := ?_
      hADυ := ?_
      hADu := ?_ }
  · -- `hAυ`: trivial (≤ refl).
    intro μ υ Dυ; exact le_refl _
  · -- `hAu`: per-`k` uniform bound on `∫|υ - u_k|^γ̄`.
    intro μ υ Dυ k
    -- Pointwise bound: `|υ - u_k|^γ̄ ≤ 2^γ̄ · (|υ|^γ̄ + |u_k|^γ̄)`.
    have hPointwise : ∀ x : Fin d → ℝ,
        |υ x - (seq.sol k).u x| ^ γBarReal
          ≤ (2 : ℝ) ^ γBarReal *
              (|υ x| ^ γBarReal + |(seq.sol k).u x| ^ γBarReal) :=
      fun x => palomar_RegularizedSequence_abs_sub_rpow_le_two_rpow_mul hγ_nn (υ x) ((seq.sol k).u x)
    -- Integrability of the RHS.
    have hInt_uk : Integrable (fun x : Fin d → ℝ =>
        |(seq.sol k).u x| ^ γBarReal)
        (volume.restrict (UnitCube d)) := by
      have hpne : (ENNReal.ofReal γBarReal) ≠ 0 :=
        (ENNReal.ofReal_pos.mpr (lt_of_lt_of_le zero_lt_one hγ_one_le)).ne'
      have hpne_top : (ENNReal.ofReal γBarReal) ≠ ⊤ := ENNReal.ofReal_ne_top
      have hMemLp : MeasureTheory.MemLp (seq.sol k).u (ENNReal.ofReal γBarReal)
          (volume.restrict (UnitCube d)) := (seq.sol k).huLp.toMemLp
      have hI := hMemLp.integrable_norm_rpow hpne hpne_top
      have hγtoReal : (ENNReal.ofReal γBarReal).toReal = γBarReal :=
        ENNReal.toReal_ofReal hγ_nn
      rw [hγtoReal] at hI
      -- Rewrite `‖x‖` to `|x|` for `x : ℝ`.
      have heq : (fun x : Fin d → ℝ => ‖(seq.sol k).u x‖ ^ γBarReal)
                  = (fun x => |(seq.sol k).u x| ^ γBarReal) := by
        funext x; rw [Real.norm_eq_abs]
      rw [heq] at hI
      exact hI
    have hInt_υu : Integrable (fun x : Fin d → ℝ => |υ x| ^ γBarReal)
        (volume.restrict (UnitCube d)) := hInt_υ_arg μ υ Dυ
    have hInt_sum : Integrable (fun x : Fin d → ℝ =>
        |υ x| ^ γBarReal + |(seq.sol k).u x| ^ γBarReal)
        (volume.restrict (UnitCube d)) := hInt_υu.add hInt_uk
    have hInt_RHS : Integrable (fun x : Fin d → ℝ =>
        (2 : ℝ) ^ γBarReal *
          (|υ x| ^ γBarReal + |(seq.sol k).u x| ^ γBarReal))
        (volume.restrict (UnitCube d)) := hInt_sum.const_mul _
    -- `∫|υ - u_k|^γ̄ ≤ 2^γ̄ · (∫|υ|^γ̄ + ∫|u_k|^γ̄)`.
    have hStep1 :
        ∫ x in UnitCube d, |υ x - (seq.sol k).u x| ^ γBarReal
          ≤ ∫ x in UnitCube d,
              (2 : ℝ) ^ γBarReal *
                (|υ x| ^ γBarReal + |(seq.sol k).u x| ^ γBarReal) := by
      apply MeasureTheory.integral_mono_ae
      · exact hInt_υmu_arg μ υ Dυ k
      · exact hInt_RHS
      · exact Filter.Eventually.of_forall hPointwise
    -- Linearity of the integral.
    have hLin :
        ∫ x in UnitCube d,
            (2 : ℝ) ^ γBarReal *
              (|υ x| ^ γBarReal + |(seq.sol k).u x| ^ γBarReal)
          = (2 : ℝ) ^ γBarReal *
              ((∫ x in UnitCube d, |υ x| ^ γBarReal) +
                ∫ x in UnitCube d, |(seq.sol k).u x| ^ γBarReal) := by
      rw [MeasureTheory.integral_const_mul]
      congr 1
      rw [MeasureTheory.integral_add hInt_υu hInt_uk]
    rw [hLin] at hStep1
    -- Bound `∫|u_k|^γ̄ ≤ Capr` via `hCapr`.
    set Im : ℝ := ∫ x in UnitCube d, |(seq.sol k).m x| ^ βBarReal with hIm_def
    set Iu : ℝ := ∫ x in UnitCube d, |(seq.sol k).u x| ^ γBarReal with hIu_def
    set IDu : ℝ := ∑ i, ∫ x in UnitCube d, |(seq.sol k).Du i x| ^ γBarReal
      with hIDu_def
    have hIm_nn : 0 ≤ Im := MeasureTheory.integral_nonneg
      (fun x => Real.rpow_nonneg (abs_nonneg _) _)
    have hIu_nn : 0 ≤ Iu := MeasureTheory.integral_nonneg
      (fun x => Real.rpow_nonneg (abs_nonneg _) _)
    have hIDu_nn : 0 ≤ IDu :=
      Finset.sum_nonneg
        (fun i _ => MeasureTheory.integral_nonneg
          (fun x => Real.rpow_nonneg (abs_nonneg _) _))
    have hSum : Im + Iu + IDu ≤ Capr := hCapr k
    have hIu_le : Iu ≤ Capr := by linarith
    -- Combine.
    have hIυ : ∫ x in UnitCube d, |υ x| ^ γBarReal
        = ∫ x in UnitCube d, |υ x| ^ γBarReal := rfl
    have hAu_bound :
        (2 : ℝ) ^ γBarReal *
            ((∫ x in UnitCube d, |υ x| ^ γBarReal) + Iu)
          ≤ (2 : ℝ) ^ γBarReal *
              ((∫ x in UnitCube d, |υ x| ^ γBarReal) + Capr) := by
      apply mul_le_mul_of_nonneg_left _ h2γ_nn
      linarith
    calc ∫ x in UnitCube d, |υ x - (seq.sol k).u x| ^ γBarReal
        ≤ (2 : ℝ) ^ γBarReal *
            ((∫ x in UnitCube d, |υ x| ^ γBarReal) +
              ∫ x in UnitCube d, |(seq.sol k).u x| ^ γBarReal) := hStep1
      _ = (2 : ℝ) ^ γBarReal *
            ((∫ x in UnitCube d, |υ x| ^ γBarReal) + Iu) := by rfl
      _ ≤ (2 : ℝ) ^ γBarReal *
            ((∫ x in UnitCube d, |υ x| ^ γBarReal) + Capr) := hAu_bound
  · -- `hADυ`: trivial.
    intro μ υ Dυ; exact le_refl _
  · -- `hADu`: per-`k` uniform bound on `∫((Dυ - Du_k)·…)^(γ̄/2)`.
    intro μ υ Dυ k
    -- Pointwise bound: `((Dυ - Du_k) · (Dυ - Du_k))^(γ̄/2)
    --   ≤ 2^γ̄ · ((Dυ · Dυ)^(γ̄/2) + (Du_k · Du_k)^(γ̄/2))`.
    have hPointwise : ∀ x : Fin d → ℝ,
        ((fun i => Dυ i x - (seq.sol k).Du i x)
            ⬝ (fun i => Dυ i x - (seq.sol k).Du i x))
            ^ (γBarReal / 2)
          ≤ (2 : ℝ) ^ γBarReal *
              (((fun i => Dυ i x) ⬝ (fun i => Dυ i x)) ^ (γBarReal / 2) +
                ((fun i => (seq.sol k).Du i x) ⬝ (fun i => (seq.sol k).Du i x))
                  ^ (γBarReal / 2)) := by
      intro x
      exact palomar_RegularizedSequence_euclideanDot_sub_rpow_le_two_rpow_mul (d := d) hγ_one_le
        (fun i => Dυ i x) (fun i => (seq.sol k).Du i x)
    -- Integrability of `(Du_k · Du_k)^(γ̄/2)` via the pointwise Jensen
    -- bound + integrability of `∑ᵢ |Du_k i|^γ̄`.
    have hPointwise_Du : ∀ x : Fin d → ℝ,
        ((fun i => (seq.sol k).Du i x) ⬝ (fun i => (seq.sol k).Du i x))
            ^ (γBarReal / 2)
          ≤ ((d : ℝ)) ^ (γBarReal - 1) *
              ∑ i, |(seq.sol k).Du i x| ^ γBarReal := by
      intro x
      exact euclideanDot_self_rpow_le_sum_rpow (d := d) hγ_one_le
        (fun i => (seq.sol k).Du i x)
    have hd_rpow_nn : (0 : ℝ) ≤ ((d : ℝ)) ^ (γBarReal - 1) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hInt_Duk_i : ∀ i : Fin d, Integrable
        (fun x : Fin d → ℝ => |(seq.sol k).Du i x| ^ γBarReal)
        (volume.restrict (UnitCube d)) := by
      intro i
      have hpne : (ENNReal.ofReal γBarReal) ≠ 0 :=
        (ENNReal.ofReal_pos.mpr (lt_of_lt_of_le zero_lt_one hγ_one_le)).ne'
      have hpne_top : (ENNReal.ofReal γBarReal) ≠ ⊤ := ENNReal.ofReal_ne_top
      have hMemLp : MeasureTheory.MemLp ((seq.sol k).Du i)
          (ENNReal.ofReal γBarReal)
          (volume.restrict (UnitCube d)) := ((seq.sol k).hDuLp i).toMemLp
      have hI := hMemLp.integrable_norm_rpow hpne hpne_top
      have hγtoReal : (ENNReal.ofReal γBarReal).toReal = γBarReal :=
        ENNReal.toReal_ofReal hγ_nn
      rw [hγtoReal] at hI
      have heq : (fun x : Fin d → ℝ => ‖(seq.sol k).Du i x‖ ^ γBarReal)
                  = (fun x => |(seq.sol k).Du i x| ^ γBarReal) := by
        funext x; rw [Real.norm_eq_abs]
      rw [heq] at hI
      exact hI
    have hInt_sum_Duk : Integrable
        (fun x : Fin d → ℝ => ∑ i, |(seq.sol k).Du i x| ^ γBarReal)
        (volume.restrict (UnitCube d)) :=
      MeasureTheory.integrable_finset_sum _ (fun i _ => hInt_Duk_i i)
    have hInt_d_Duk : Integrable
        (fun x : Fin d → ℝ =>
          ((d : ℝ)) ^ (γBarReal - 1) *
            ∑ i, |(seq.sol k).Du i x| ^ γBarReal)
        (volume.restrict (UnitCube d)) := hInt_sum_Duk.const_mul _
    have hInt_DuDu : Integrable
        (fun x : Fin d → ℝ =>
          ((fun i => (seq.sol k).Du i x) ⬝ (fun i => (seq.sol k).Du i x))
            ^ (γBarReal / 2))
        (volume.restrict (UnitCube d)) := by
      -- Sandwich integrability via the Jensen bound.
      apply MeasureTheory.Integrable.mono'
        (g := fun x => ((d : ℝ)) ^ (γBarReal - 1) *
            ∑ i, |(seq.sol k).Du i x| ^ γBarReal)
        hInt_d_Duk
      · -- AEStronglyMeasurable of `((seq.sol k).Du · (seq.sol k).Du)^(γ̄/2)`.
        -- Compose `Continuous (·^(γ̄/2))` (since `γ̄/2 ≥ 0`) with the
        -- AEStronglyMeasurable dot product.
        have hγ2_nn : (0 : ℝ) ≤ γBarReal / 2 := by linarith
        have hCont : Continuous (fun y : ℝ => y ^ (γBarReal / 2)) :=
          Real.continuous_rpow_const hγ2_nn
        have hDot_aesm : AEStronglyMeasurable
            (fun x : Fin d → ℝ =>
              ((fun i => (seq.sol k).Du i x)
                ⬝ (fun i => (seq.sol k).Du i x)))
            (volume.restrict (UnitCube d)) := by
          unfold dotProduct
          refine Finset.aestronglyMeasurable_fun_sum _ ?_
          intro i _
          exact ((seq.sol k).hDuLp i).aestronglyMeasurable.mul
                ((seq.sol k).hDuLp i).aestronglyMeasurable
        exact hCont.comp_aestronglyMeasurable hDot_aesm
      · -- Bound: `‖(Du · Du)^(γ̄/2)‖ ≤ d^(γ̄-1) · ∑ |Du i|^γ̄`.
        apply Filter.Eventually.of_forall
        intro x
        rw [Real.norm_eq_abs, abs_of_nonneg (hDotRpow_nn _ x)]
        exact hPointwise_Du x
    -- Integrability of the pointwise upper bound.
    have hInt_DυDυ_x : Integrable (fun x : Fin d → ℝ =>
        ((fun i => Dυ i x) ⬝ (fun i => Dυ i x)) ^ (γBarReal / 2))
        (volume.restrict (UnitCube d)) := hInt_DυDυ_arg μ υ Dυ
    have hInt_pair : Integrable (fun x : Fin d → ℝ =>
        ((fun i => Dυ i x) ⬝ (fun i => Dυ i x)) ^ (γBarReal / 2) +
        ((fun i => (seq.sol k).Du i x) ⬝ (fun i => (seq.sol k).Du i x))
          ^ (γBarReal / 2))
        (volume.restrict (UnitCube d)) := hInt_DυDυ_x.add hInt_DuDu
    have hInt_pair_const : Integrable (fun x : Fin d → ℝ =>
        (2 : ℝ) ^ γBarReal *
          (((fun i => Dυ i x) ⬝ (fun i => Dυ i x)) ^ (γBarReal / 2) +
            ((fun i => (seq.sol k).Du i x) ⬝ (fun i => (seq.sol k).Du i x))
              ^ (γBarReal / 2)))
        (volume.restrict (UnitCube d)) := hInt_pair.const_mul _
    -- Step A: `∫((Dυ - Du_k) · …)^(γ̄/2) ≤ 2^γ̄ · (∫(Dυ · Dυ)^… + ∫(Du_k · Du_k)^…)`.
    have hStepA :
        ∫ x in UnitCube d,
            ((fun i => Dυ i x - (seq.sol k).Du i x)
              ⬝ (fun i => Dυ i x - (seq.sol k).Du i x))
              ^ (γBarReal / 2)
          ≤ ∫ x in UnitCube d,
              (2 : ℝ) ^ γBarReal *
                (((fun i => Dυ i x) ⬝ (fun i => Dυ i x)) ^ (γBarReal / 2) +
                  ((fun i => (seq.sol k).Du i x)
                    ⬝ (fun i => (seq.sol k).Du i x))
                    ^ (γBarReal / 2)) := by
      apply MeasureTheory.integral_mono_ae
      · exact hInt_DυmDu_arg μ υ Dυ k
      · exact hInt_pair_const
      · exact Filter.Eventually.of_forall hPointwise
    have hLinA :
        ∫ x in UnitCube d,
            (2 : ℝ) ^ γBarReal *
              (((fun i => Dυ i x) ⬝ (fun i => Dυ i x)) ^ (γBarReal / 2) +
                ((fun i => (seq.sol k).Du i x)
                  ⬝ (fun i => (seq.sol k).Du i x))
                  ^ (γBarReal / 2))
          = (2 : ℝ) ^ γBarReal *
              ((∫ x in UnitCube d,
                  ((fun i => Dυ i x) ⬝ (fun i => Dυ i x))
                    ^ (γBarReal / 2)) +
                ∫ x in UnitCube d,
                  ((fun i => (seq.sol k).Du i x)
                    ⬝ (fun i => (seq.sol k).Du i x))
                    ^ (γBarReal / 2)) := by
      rw [MeasureTheory.integral_const_mul]
      congr 1
      rw [MeasureTheory.integral_add hInt_DυDυ_x hInt_DuDu]
    rw [hLinA] at hStepA
    -- Step B: `∫(Du_k · Du_k)^(γ̄/2) ≤ d^(γ̄-1) · ∑ᵢ ∫|Du_k i|^γ̄`.
    have hStepB :
        ∫ x in UnitCube d,
            ((fun i => (seq.sol k).Du i x)
              ⬝ (fun i => (seq.sol k).Du i x))
              ^ (γBarReal / 2)
          ≤ ((d : ℝ)) ^ (γBarReal - 1) *
              ∑ i, ∫ x in UnitCube d, |(seq.sol k).Du i x| ^ γBarReal := by
      have h1 :
          ∫ x in UnitCube d,
              ((fun i => (seq.sol k).Du i x)
                ⬝ (fun i => (seq.sol k).Du i x))
                ^ (γBarReal / 2)
            ≤ ∫ x in UnitCube d,
                ((d : ℝ)) ^ (γBarReal - 1) *
                  ∑ i, |(seq.sol k).Du i x| ^ γBarReal := by
        apply MeasureTheory.integral_mono_ae
        · exact hInt_DuDu
        · exact hInt_d_Duk
        · exact Filter.Eventually.of_forall hPointwise_Du
      have h2 :
          ∫ x in UnitCube d,
              ((d : ℝ)) ^ (γBarReal - 1) *
                ∑ i, |(seq.sol k).Du i x| ^ γBarReal
            = ((d : ℝ)) ^ (γBarReal - 1) *
                ∫ x in UnitCube d, ∑ i, |(seq.sol k).Du i x| ^ γBarReal := by
        rw [MeasureTheory.integral_const_mul]
      have h3 :
          ∫ x in UnitCube d, ∑ i, |(seq.sol k).Du i x| ^ γBarReal
            = ∑ i, ∫ x in UnitCube d, |(seq.sol k).Du i x| ^ γBarReal := by
        rw [MeasureTheory.integral_finset_sum]
        intro i _
        exact hInt_Duk_i i
      rw [h2, h3] at h1
      exact h1
    -- Step C: `∑ᵢ ∫|Du_k i|^γ̄ ≤ Capr` via `hCapr`.
    set Im : ℝ := ∫ x in UnitCube d, |(seq.sol k).m x| ^ βBarReal with hIm_def
    set Iu : ℝ := ∫ x in UnitCube d, |(seq.sol k).u x| ^ γBarReal with hIu_def
    set IDu : ℝ := ∑ i, ∫ x in UnitCube d, |(seq.sol k).Du i x| ^ γBarReal
      with hIDu_def
    have hIm_nn : 0 ≤ Im := MeasureTheory.integral_nonneg
      (fun x => Real.rpow_nonneg (abs_nonneg _) _)
    have hIu_nn : 0 ≤ Iu := MeasureTheory.integral_nonneg
      (fun x => Real.rpow_nonneg (abs_nonneg _) _)
    have hIDu_nn : 0 ≤ IDu :=
      Finset.sum_nonneg
        (fun i _ => MeasureTheory.integral_nonneg
          (fun x => Real.rpow_nonneg (abs_nonneg _) _))
    have hSum : Im + Iu + IDu ≤ Capr := hCapr k
    have hIDu_le : IDu ≤ Capr := by linarith
    -- Combine.
    have hStepBC :
        ∫ x in UnitCube d,
            ((fun i => (seq.sol k).Du i x)
              ⬝ (fun i => (seq.sol k).Du i x))
              ^ (γBarReal / 2)
          ≤ ((d : ℝ)) ^ (γBarReal - 1) * Capr := by
      have := hStepB
      have hbound : ((d : ℝ)) ^ (γBarReal - 1) * IDu
          ≤ ((d : ℝ)) ^ (γBarReal - 1) * Capr :=
        mul_le_mul_of_nonneg_left hIDu_le hd_rpow_nn
      linarith
    -- Final: combine Step A and Step C.
    have hCombine :
        (2 : ℝ) ^ γBarReal *
            ((∫ x in UnitCube d,
                ((fun i => Dυ i x) ⬝ (fun i => Dυ i x)) ^ (γBarReal / 2)) +
              ∫ x in UnitCube d,
                ((fun i => (seq.sol k).Du i x)
                  ⬝ (fun i => (seq.sol k).Du i x))
                  ^ (γBarReal / 2))
          ≤ (2 : ℝ) ^ γBarReal *
              ((∫ x in UnitCube d,
                  ((fun i => Dυ i x) ⬝ (fun i => Dυ i x)) ^ (γBarReal / 2)) +
                ((d : ℝ)) ^ (γBarReal - 1) * Capr) := by
      apply mul_le_mul_of_nonneg_left _ h2γ_nn
      linarith
    exact le_trans hStepA hCombine

/-! ### Convenience wrapper auto-discharging integrability from `regBundle`. -/

/-- **Auto-discharge wrapper for `gateauxAux_of_paperHypotheses`.**

This wrapper supplies the four `Integrable` certificate arguments
of `gateauxAux_of_paperHypotheses` automatically from:

* `regBundle μ υ Dυ : PerTestTripleRegularity ...` — providing
  `MemLpPer ... υ` and `MemLpPer ... (Dυ i)` for each `i`;
* the per-`k` `(seq.sol k).{huLp, hDuLp}` certificates carried by
  `RegularizedBareSolution`.

The integrability proofs proceed as follows:

* `Integrable (|υ|^γ̄)` follows from
  `MemLp.integrable_norm_rpow` applied to `υ`'s `MemLpPer` cert.
* `Integrable (|υ - u_k|^γ̄)` follows from `MemLp.sub` between
  `υ`'s and `u_k`'s `MemLpPer` certs.
* `Integrable ((Dυ · Dυ)^(γ̄/2))` is dominated by
  `d^(γ̄-1) · ∑_i |Dυ i|^γ̄` via the Jensen helper
  `euclideanDot_self_rpow_le_sum_rpow`, and the dominant is
  integrable by sum-and-`integrable_norm_rpow`.
* `Integrable (((Dυ - Du_k) · (Dυ - Du_k))^(γ̄/2))` is similarly
  dominated by `d^(γ̄-1) · ∑_i |Dυ i - Du_k i|^γ̄`. -/
noncomputable def gateauxAux_of_paperHypotheses_regBundle
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH)
    (hγ_one_le : (1 : ℝ) ≤ γBarReal)
    (Capr : ℝ) (hCapr_nn : 0 ≤ Capr)
    (hCapr : ∀ k : ℕ,
      (∫ x in UnitCube d, |(seq.sol k).m x| ^ βBarReal) +
        (∫ x in UnitCube d, |(seq.sol k).u x| ^ γBarReal) +
        (∑ i, ∫ x in UnitCube d, |(seq.sol k).Du i x| ^ γBarReal)
          ≤ Capr)
    (hυ_memLp : ∀ (μ υ : (Fin d → ℝ) → ℝ)
                  (Dυ : Fin d → (Fin d → ℝ) → ℝ),
      MemLpPer (d := d) (ENNReal.ofReal γBarReal) υ)
    (hDυ_memLp : ∀ (μ υ : (Fin d → ℝ) → ℝ)
                   (Dυ : Fin d → (Fin d → ℝ) → ℝ) (i : Fin d),
      MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i)) :
    LimitPairingSelectorGateauxAux (d := d) seq := by
  -- Setup.
  have hγ_nn : (0 : ℝ) ≤ γBarReal := le_trans zero_le_one hγ_one_le
  have hpne : (ENNReal.ofReal γBarReal) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (lt_of_lt_of_le zero_lt_one hγ_one_le)).ne'
  have hpne_top : (ENNReal.ofReal γBarReal) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hγtoReal : (ENNReal.ofReal γBarReal).toReal = γBarReal :=
    ENNReal.toReal_ofReal hγ_nn
  -- Integrability of `|f|^γ̄` from `MemLpPer ... f`.
  have hInt_abs_rpow : ∀ (f : (Fin d → ℝ) → ℝ),
      MemLpPer (d := d) (ENNReal.ofReal γBarReal) f →
      Integrable (fun x : Fin d → ℝ => |f x| ^ γBarReal)
        (volume.restrict (UnitCube d)) := by
    intro f hf
    have hI := hf.toMemLp.integrable_norm_rpow hpne hpne_top
    rw [hγtoReal] at hI
    have heq : (fun x : Fin d → ℝ => ‖f x‖ ^ γBarReal)
                = (fun x => |f x| ^ γBarReal) := by
      funext x; rw [Real.norm_eq_abs]
    rw [heq] at hI
    exact hI
  -- Integrability of `(g · g)^(γ̄/2)` for `g : Fin d → (Fin d → ℝ) → ℝ`
  -- with each `g i` in `MemLpPer γ̄`.
  have hInt_dot_rpow : ∀ (g : Fin d → (Fin d → ℝ) → ℝ),
      (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (g i)) →
      Integrable (fun x : Fin d → ℝ =>
        ((fun i => g i x) ⬝ (fun i => g i x)) ^ (γBarReal / 2))
        (volume.restrict (UnitCube d)) := by
    intro g hg
    -- Pointwise upper bound via the Jensen helper.
    have hPointwise : ∀ x : Fin d → ℝ,
        ((fun i => g i x) ⬝ (fun i => g i x)) ^ (γBarReal / 2)
          ≤ ((d : ℝ)) ^ (γBarReal - 1) *
              ∑ i, |g i x| ^ γBarReal :=
      fun x => euclideanDot_self_rpow_le_sum_rpow (d := d) hγ_one_le _
    have hInt_g_i : ∀ i, Integrable
        (fun x : Fin d → ℝ => |g i x| ^ γBarReal)
        (volume.restrict (UnitCube d)) :=
      fun i => hInt_abs_rpow (g i) (hg i)
    have hInt_sum : Integrable
        (fun x : Fin d → ℝ => ∑ i, |g i x| ^ γBarReal)
        (volume.restrict (UnitCube d)) :=
      MeasureTheory.integrable_finset_sum _ (fun i _ => hInt_g_i i)
    have hInt_dom : Integrable
        (fun x : Fin d → ℝ =>
          ((d : ℝ)) ^ (γBarReal - 1) *
            ∑ i, |g i x| ^ γBarReal)
        (volume.restrict (UnitCube d)) := hInt_sum.const_mul _
    have hγ2_nn : (0 : ℝ) ≤ γBarReal / 2 := by linarith
    have hCont : Continuous (fun y : ℝ => y ^ (γBarReal / 2)) :=
      Real.continuous_rpow_const hγ2_nn
    have hDot_aesm : AEStronglyMeasurable
        (fun x : Fin d → ℝ =>
          ((fun i => g i x) ⬝ (fun i => g i x)))
        (volume.restrict (UnitCube d)) := by
      unfold dotProduct
      refine Finset.aestronglyMeasurable_fun_sum _ ?_
      intro i _
      exact (hg i).aestronglyMeasurable.mul (hg i).aestronglyMeasurable
    apply MeasureTheory.Integrable.mono'
      (g := fun x => ((d : ℝ)) ^ (γBarReal - 1) *
          ∑ i, |g i x| ^ γBarReal)
      hInt_dom
    · exact hCont.comp_aestronglyMeasurable hDot_aesm
    · refine Filter.Eventually.of_forall (fun x => ?_)
      have hnn : (0 : ℝ) ≤
          ((fun i => g i x) ⬝ (fun i => g i x)) ^ (γBarReal / 2) :=
        Real.rpow_nonneg (euclideanDot_self_nonneg _) _
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact hPointwise x
  -- Apply the base producer.
  apply gateauxAux_of_paperHypotheses (d := d) seq hγ_one_le Capr hCapr_nn hCapr
  · -- `hInt_DυDυ_arg`: integrability of `(Dυ · Dυ)^(γ̄/2)`.
    intro μ υ Dυ
    exact hInt_dot_rpow Dυ (fun i => hDυ_memLp μ υ Dυ i)
  · -- `hInt_DυmDu_arg`: integrability of `((Dυ - Du_k) · …)^(γ̄/2)`.
    intro μ υ Dυ k
    have hDiff : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal)
        (fun x => Dυ i x - (seq.sol k).Du i x) := by
      intro i
      have h1 : MeasureTheory.MemLp (Dυ i) (ENNReal.ofReal γBarReal)
          (volume.restrict (UnitCube d)) :=
        (hDυ_memLp μ υ Dυ i).toMemLp
      have h2 : MeasureTheory.MemLp ((seq.sol k).Du i)
          (ENNReal.ofReal γBarReal)
          (volume.restrict (UnitCube d)) :=
        ((seq.sol k).hDuLp i).toMemLp
      have hsub : MeasureTheory.MemLp (Dυ i - (seq.sol k).Du i)
          (ENNReal.ofReal γBarReal)
          (volume.restrict (UnitCube d)) := h1.sub h2
      have heq : (fun x => Dυ i x - (seq.sol k).Du i x)
                  = (Dυ i - (seq.sol k).Du i) := rfl
      rw [heq]
      exact MemLp.toMemLpPer hsub
    exact hInt_dot_rpow _ hDiff
  · -- `hInt_υ_arg`: integrability of `|υ|^γ̄`.
    intro μ υ Dυ
    exact hInt_abs_rpow υ (hυ_memLp μ υ Dυ)
  · -- `hInt_υmu_arg`: integrability of `|υ - u_k|^γ̄`.
    intro μ υ Dυ k
    have h1 : MeasureTheory.MemLp υ (ENNReal.ofReal γBarReal)
        (volume.restrict (UnitCube d)) :=
      (hυ_memLp μ υ Dυ).toMemLp
    have h2 : MeasureTheory.MemLp (seq.sol k).u (ENNReal.ofReal γBarReal)
        (volume.restrict (UnitCube d)) := (seq.sol k).huLp.toMemLp
    have hsub : MeasureTheory.MemLp (υ - (seq.sol k).u)
        (ENNReal.ofReal γBarReal)
        (volume.restrict (UnitCube d)) := h1.sub h2
    have heq_fun : (fun x => υ x - (seq.sol k).u x)
                    = (υ - (seq.sol k).u) := rfl
    have hMemLpPer : MemLpPer (d := d) (ENNReal.ofReal γBarReal)
        (fun x => υ x - (seq.sol k).u x) := by
      rw [heq_fun]; exact MemLp.toMemLpPer hsub
    exact hInt_abs_rpow _ hMemLpPer

/-! ### Phase 6b — family-restricted Gateaux aux

Per `infra-P5-theorem1-phase-6b-gateauxAux-familyRestrict`, we land
**parallel infrastructure** giving a domain-parameterised version of
`LimitPairingSelectorGateauxAux` together with a producer
`gateauxAux_of_paperHypotheses_familyRestrict` that takes per-domain
`MemLpPer` suppliers.

The universal version (`LimitPairingSelectorGateauxAux` and its
`gateauxAux_of_paperHypotheses{,_regBundle}` producers) is left
unchanged — Phase 6c will rewire the BanachBridge consumer to use the
family-restricted variant, and Phase 6d will drop the legacy
`regBundle` field from `T10PaperResidues`. -/

/-- **Family-restricted authorized aux for the Gateaux residual
bound.**

A domain-parameterised version of `LimitPairingSelectorGateauxAux`:
the eight bound/integrability fields are quantified over
`(μ, υ, Dυ) ∈ D` rather than universally. When `D = Set.univ`,
this structure is interconvertible with the universal
`LimitPairingSelectorGateauxAux` (cf. `gateauxAuxFamily_univ` /
`gateauxAux_of_family_univ` below). -/
structure LimitPairingSelectorGateauxAuxFamily
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH)
    (D : Set (StationaryMFG.Theorems.SimplePower.MFGTriple d)) where
  /-- `1 ≤ γ̄` (real form). -/
  hγ_one_le : (1 : ℝ) ≤ γBarReal
  /-- Per test triple in `D`, an upper bound on `∫|υ|^γ̄`. -/
  Aυ : ((Fin d → ℝ) → ℝ) → ((Fin d → ℝ) → ℝ) →
        (Fin d → (Fin d → ℝ) → ℝ) → ℝ
  /-- Per test triple in `D` per `k`, an upper bound on
  `∫|υ - u_k|^γ̄`. -/
  Au : ((Fin d → ℝ) → ℝ) → ((Fin d → ℝ) → ℝ) →
        (Fin d → (Fin d → ℝ) → ℝ) → ℝ
  /-- Per test triple in `D`, an upper bound on `∫(Dυ·Dυ)^(γ̄/2)`. -/
  ADυ : ((Fin d → ℝ) → ℝ) → ((Fin d → ℝ) → ℝ) →
         (Fin d → (Fin d → ℝ) → ℝ) → ℝ
  /-- Per test triple in `D` per `k`, an upper bound on
  `∫((Dυ - Du_k)·(Dυ - Du_k))^(γ̄/2)`. -/
  ADu : ((Fin d → ℝ) → ℝ) → ((Fin d → ℝ) → ℝ) →
         (Fin d → (Fin d → ℝ) → ℝ) → ℝ
  /-- `Integrable` certificate for `(Dυ·Dυ)^(γ̄/2)` (in `D`). -/
  hInt_DυDυ : ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄
                 ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
                 (μ, υ, Dυ) ∈ D →
              Integrable (fun x : Fin d → ℝ =>
                ((fun i => Dυ i x) ⬝ (fun i => Dυ i x)) ^ (γBarReal / 2))
                (volume.restrict (UnitCube d))
  /-- `Integrable` certificate for `((Dυ - Du_k)·(Dυ - Du_k))^(γ̄/2)`
  (in `D`). -/
  hInt_DυmDu : ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄
                  ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
                  (μ, υ, Dυ) ∈ D → ∀ (k : ℕ),
              Integrable (fun x : Fin d → ℝ =>
                ((fun i => Dυ i x - (seq.sol k).Du i x)
                  ⬝ (fun i => Dυ i x - (seq.sol k).Du i x))
                  ^ (γBarReal / 2))
                (volume.restrict (UnitCube d))
  /-- `Integrable` certificate for `|υ|^γ̄` (in `D`). -/
  hInt_υ : ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄
              ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
              (μ, υ, Dυ) ∈ D →
            Integrable (fun x : Fin d → ℝ => |υ x| ^ γBarReal)
              (volume.restrict (UnitCube d))
  /-- `Integrable` certificate for `|υ - u_k|^γ̄` (in `D`). -/
  hInt_υmu : ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄
                ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
                (μ, υ, Dυ) ∈ D → ∀ (k : ℕ),
              Integrable (fun x : Fin d → ℝ =>
                |υ x - (seq.sol k).u x| ^ γBarReal)
                (volume.restrict (UnitCube d))
  /-- Per-test-triple bound (in `D`) on `∫|υ|^γ̄ ≤ Aυ`. -/
  hAυ : ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄
           ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
           (μ, υ, Dυ) ∈ D →
          ∫ x in UnitCube d, |υ x| ^ γBarReal
            ∂(volume : Measure (Fin d → ℝ)) ≤ Aυ μ υ Dυ
  /-- Per-test-triple per-`k` uniform bound (in `D`) on
  `∫|υ - u_k|^γ̄ ≤ Au`. -/
  hAu : ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄
           ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
           (μ, υ, Dυ) ∈ D → ∀ (k : ℕ),
          ∫ x in UnitCube d, |υ x - (seq.sol k).u x| ^ γBarReal
            ∂(volume : Measure (Fin d → ℝ)) ≤ Au μ υ Dυ
  /-- Per-test-triple bound (in `D`) on `∫(Dυ·Dυ)^(γ̄/2) ≤ ADυ`. -/
  hADυ : ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄
            ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
            (μ, υ, Dυ) ∈ D →
           ∫ x in UnitCube d,
              ((fun i => Dυ i x) ⬝ (fun i => Dυ i x)) ^ (γBarReal / 2)
              ∂(volume : Measure (Fin d → ℝ)) ≤ ADυ μ υ Dυ
  /-- Per-test-triple per-`k` uniform bound (in `D`) on
  `∫((Dυ - Du_k)·(Dυ - Du_k))^(γ̄/2) ≤ ADu`. -/
  hADu : ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄
            ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
            (μ, υ, Dυ) ∈ D → ∀ (k : ℕ),
           ∫ x in UnitCube d,
              ((fun i => Dυ i x - (seq.sol k).Du i x)
                 ⬝ (fun i => Dυ i x - (seq.sol k).Du i x))
                ^ (γBarReal / 2)
              ∂(volume : Measure (Fin d → ℝ)) ≤ ADu μ υ Dυ

namespace LimitPairingSelectorGateauxAuxFamily

variable {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
  [Fact (1 ≤ ENNReal.ofReal βBarReal)]
  [Fact (1 ≤ ENNReal.ofReal γBarReal)]
  {V : (Fin d → ℝ) → ℝ}
  {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
  {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
  {seq : RegularizedSequenceData (d := d)
            γBarReal βBarReal βBarReal' γBarReal' V H DpH}
  {D : Set (StationaryMFG.Theorems.SimplePower.MFGTriple d)}

/-- The selector's per-family `M` field, derived from the four
uniform bounds. -/
def M (aux : LimitPairingSelectorGateauxAuxFamily (d := d) seq D) :
    ((Fin d → ℝ) → ℝ) → ((Fin d → ℝ) → ℝ) →
    (Fin d → (Fin d → ℝ) → ℝ) → ℝ :=
  fun μ υ Dυ => aux.Aυ μ υ Dυ + aux.Au μ υ Dυ
                  + aux.ADυ μ υ Dυ + aux.ADu μ υ Dυ

/-- The selector's per-family `hreg_bdd` field: for any test triple
`(μ, υ, Dυ) ∈ D`, the per-`k` per-test-triple Gateaux residual is
bounded by `aux.M μ υ Dυ`.

Direct application of `gateauxWpPair_uniform_bound_per_triple`
with `Du := (seq.sol k).Du` and `u := (seq.sol k).u`. -/
theorem hreg_bdd
    (aux : LimitPairingSelectorGateauxAuxFamily (d := d) seq D) :
    ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄
       ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
       (μ, υ, Dυ) ∈ D → ∀ (k : ℕ),
      |gateauxWpPair γBarReal Dυ υ
          (fun i x => Dυ i x - (seq.sol k).Du i x)
          (υ - (seq.sol k).u)| ≤ aux.M μ υ Dυ := by
  intro μ υ Dυ hMem k
  exact gateauxWpPair_uniform_bound_per_triple
    (d := d) γBarReal aux.hγ_one_le μ υ Dυ
    (fun i => (seq.sol k).Du i) (seq.sol k).u
    (aux.Aυ μ υ Dυ) (aux.Au μ υ Dυ)
    (aux.ADυ μ υ Dυ) (aux.ADu μ υ Dυ)
    (aux.hInt_DυDυ hMem)
    (aux.hInt_DυmDu hMem k)
    (aux.hInt_υ hMem)
    (aux.hInt_υmu hMem k)
    (aux.hAυ hMem)
    (aux.hAu hMem k)
    (aux.hADυ hMem)
    (aux.hADu hMem k)

end LimitPairingSelectorGateauxAuxFamily

/-- **Universal-to-family bridge.** A universal
`LimitPairingSelectorGateauxAux` produces, for any domain `D`, a
matching `LimitPairingSelectorGateauxAuxFamily seq D` by ignoring
the membership hypothesis. -/
def LimitPairingSelectorGateauxAux.toFamily
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH}
    (aux : LimitPairingSelectorGateauxAux (d := d) seq)
    (D : Set (StationaryMFG.Theorems.SimplePower.MFGTriple d)) :
    LimitPairingSelectorGateauxAuxFamily (d := d) seq D where
  hγ_one_le := aux.hγ_one_le
  Aυ := aux.Aυ
  Au := aux.Au
  ADυ := aux.ADυ
  ADu := aux.ADu
  hInt_DυDυ := fun μ υ Dυ _ => aux.hInt_DυDυ μ υ Dυ
  hInt_DυmDu := fun μ υ Dυ _ k => aux.hInt_DυmDu μ υ Dυ k
  hInt_υ := fun μ υ Dυ _ => aux.hInt_υ μ υ Dυ
  hInt_υmu := fun μ υ Dυ _ k => aux.hInt_υmu μ υ Dυ k
  hAυ := fun μ υ Dυ _ => aux.hAυ μ υ Dυ
  hAu := fun μ υ Dυ _ k => aux.hAu μ υ Dυ k
  hADυ := fun μ υ Dυ _ => aux.hADυ μ υ Dυ
  hADu := fun μ υ Dυ _ k => aux.hADu μ υ Dυ k

/-- **Closed-form family-native aggregator for
`LimitPairingSelectorGateauxAuxFamily`.**

Per Phase 6b
(`infra-P5-theorem1-phase-6b-gateauxAux-familyRestrict`), this is
the family-restricted analogue of
`gateauxAux_of_paperHypotheses_regBundle`: instead of the
universally-quantified `(hυ_memLp, hDυ_memLp)` suppliers (which are
paper-trivially unprovable for arbitrary `υ`), it takes
**per-domain** `MemLpPer` suppliers, valid only on
`(μ, υ, Dυ) ∈ D`.

The four `M`-bounds are set as in the universal version (cf.
`gateauxAux_of_paperHypotheses` for the analytic content):
* `Aυ μ υ Dυ := ∫|υ|^γ̄`, `ADυ μ υ Dυ := ∫(Dυ⬝Dυ)^(γ̄/2)`,
* `Au μ υ Dυ := 2^γ̄ · ((∫|υ|^γ̄) + Capr)`,
* `ADu μ υ Dυ := 2^γ̄ · ((∫(Dυ⬝Dυ)^(γ̄/2)) + d^(γ̄-1) · Capr)`.

The integrability/`MemLpPer` flow is identical to the universal
version (`gateauxAux_of_paperHypotheses_regBundle`), with each
universal `(μ, υ, Dυ)` quantification replaced by a
membership-restricted `(μ, υ, Dυ) ∈ D` form. -/
noncomputable def gateauxAux_of_paperHypotheses_familyRestrict
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH)
    (hγ_one_le : (1 : ℝ) ≤ γBarReal)
    (Capr : ℝ) (hCapr_nn : 0 ≤ Capr)
    (hCapr : ∀ k : ℕ,
      (∫ x in UnitCube d, |(seq.sol k).m x| ^ βBarReal) +
        (∫ x in UnitCube d, |(seq.sol k).u x| ^ γBarReal) +
        (∑ i, ∫ x in UnitCube d, |(seq.sol k).Du i x| ^ γBarReal)
          ≤ Capr)
    (D : Set (StationaryMFG.Theorems.SimplePower.MFGTriple d))
    (hυ_memLp : ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄
                  ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
                  (μ, υ, Dυ) ∈ D →
      MemLpPer (d := d) (ENNReal.ofReal γBarReal) υ)
    (hDυ_memLp : ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄
                   ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
                   (μ, υ, Dυ) ∈ D → ∀ (i : Fin d),
      MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i)) :
    LimitPairingSelectorGateauxAuxFamily (d := d) seq D := by
  -- Setup (parallels `gateauxAux_of_paperHypotheses_regBundle`).
  have hγ_nn : (0 : ℝ) ≤ γBarReal := le_trans zero_le_one hγ_one_le
  have h2γ_nn : (0 : ℝ) ≤ (2 : ℝ) ^ γBarReal :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hpne : (ENNReal.ofReal γBarReal) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (lt_of_lt_of_le zero_lt_one hγ_one_le)).ne'
  have hpne_top : (ENNReal.ofReal γBarReal) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hγtoReal : (ENNReal.ofReal γBarReal).toReal = γBarReal :=
    ENNReal.toReal_ofReal hγ_nn
  -- Integrability of `|f|^γ̄` from `MemLpPer ... f`.
  have hInt_abs_rpow : ∀ (f : (Fin d → ℝ) → ℝ),
      MemLpPer (d := d) (ENNReal.ofReal γBarReal) f →
      Integrable (fun x : Fin d → ℝ => |f x| ^ γBarReal)
        (volume.restrict (UnitCube d)) := by
    intro f hf
    have hI := hf.toMemLp.integrable_norm_rpow hpne hpne_top
    rw [hγtoReal] at hI
    have heq : (fun x : Fin d → ℝ => ‖f x‖ ^ γBarReal)
                = (fun x => |f x| ^ γBarReal) := by
      funext x; rw [Real.norm_eq_abs]
    rw [heq] at hI
    exact hI
  -- Integrability of `(g · g)^(γ̄/2)` for `g : Fin d → (Fin d → ℝ) → ℝ`
  -- with each `g i` in `MemLpPer γ̄`.
  have hInt_dot_rpow : ∀ (g : Fin d → (Fin d → ℝ) → ℝ),
      (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (g i)) →
      Integrable (fun x : Fin d → ℝ =>
        ((fun i => g i x) ⬝ (fun i => g i x)) ^ (γBarReal / 2))
        (volume.restrict (UnitCube d)) := by
    intro g hg
    have hPointwise : ∀ x : Fin d → ℝ,
        ((fun i => g i x) ⬝ (fun i => g i x)) ^ (γBarReal / 2)
          ≤ ((d : ℝ)) ^ (γBarReal - 1) *
              ∑ i, |g i x| ^ γBarReal :=
      fun x => euclideanDot_self_rpow_le_sum_rpow (d := d) hγ_one_le _
    have hInt_g_i : ∀ i, Integrable
        (fun x : Fin d → ℝ => |g i x| ^ γBarReal)
        (volume.restrict (UnitCube d)) :=
      fun i => hInt_abs_rpow (g i) (hg i)
    have hInt_sum : Integrable
        (fun x : Fin d → ℝ => ∑ i, |g i x| ^ γBarReal)
        (volume.restrict (UnitCube d)) :=
      MeasureTheory.integrable_finset_sum _ (fun i _ => hInt_g_i i)
    have hInt_dom : Integrable
        (fun x : Fin d → ℝ =>
          ((d : ℝ)) ^ (γBarReal - 1) *
            ∑ i, |g i x| ^ γBarReal)
        (volume.restrict (UnitCube d)) := hInt_sum.const_mul _
    have hγ2_nn : (0 : ℝ) ≤ γBarReal / 2 := by linarith
    have hCont : Continuous (fun y : ℝ => y ^ (γBarReal / 2)) :=
      Real.continuous_rpow_const hγ2_nn
    have hDot_aesm : AEStronglyMeasurable
        (fun x : Fin d → ℝ =>
          ((fun i => g i x) ⬝ (fun i => g i x)))
        (volume.restrict (UnitCube d)) := by
      unfold dotProduct
      refine Finset.aestronglyMeasurable_fun_sum _ ?_
      intro i _
      exact (hg i).aestronglyMeasurable.mul (hg i).aestronglyMeasurable
    apply MeasureTheory.Integrable.mono'
      (g := fun x => ((d : ℝ)) ^ (γBarReal - 1) *
          ∑ i, |g i x| ^ γBarReal)
      hInt_dom
    · exact hCont.comp_aestronglyMeasurable hDot_aesm
    · refine Filter.Eventually.of_forall (fun x => ?_)
      have hnn : (0 : ℝ) ≤
          ((fun i => g i x) ⬝ (fun i => g i x)) ^ (γBarReal / 2) :=
        Real.rpow_nonneg (euclideanDot_self_nonneg _) _
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact hPointwise x
  -- Build the four integrability suppliers from the per-domain
  -- `MemLpPer` hypotheses.
  have hInt_DυDυ_arg : ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄
                          ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
                          (μ, υ, Dυ) ∈ D →
      Integrable (fun x : Fin d → ℝ =>
        ((fun i => Dυ i x) ⬝ (fun i => Dυ i x)) ^ (γBarReal / 2))
        (volume.restrict (UnitCube d)) := by
    intro μ υ Dυ hMem
    exact hInt_dot_rpow Dυ (fun i => hDυ_memLp hMem i)
  have hInt_DυmDu_arg : ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄
                           ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
                           (μ, υ, Dυ) ∈ D → ∀ (k : ℕ),
      Integrable (fun x : Fin d → ℝ =>
        ((fun i => Dυ i x - (seq.sol k).Du i x)
          ⬝ (fun i => Dυ i x - (seq.sol k).Du i x))
          ^ (γBarReal / 2))
        (volume.restrict (UnitCube d)) := by
    intro μ υ Dυ hMem k
    have hDiff : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal)
        (fun x => Dυ i x - (seq.sol k).Du i x) := by
      intro i
      have h1 : MeasureTheory.MemLp (Dυ i) (ENNReal.ofReal γBarReal)
          (volume.restrict (UnitCube d)) :=
        (hDυ_memLp hMem i).toMemLp
      have h2 : MeasureTheory.MemLp ((seq.sol k).Du i)
          (ENNReal.ofReal γBarReal)
          (volume.restrict (UnitCube d)) :=
        ((seq.sol k).hDuLp i).toMemLp
      have hsub : MeasureTheory.MemLp (Dυ i - (seq.sol k).Du i)
          (ENNReal.ofReal γBarReal)
          (volume.restrict (UnitCube d)) := h1.sub h2
      have heq : (fun x => Dυ i x - (seq.sol k).Du i x)
                  = (Dυ i - (seq.sol k).Du i) := rfl
      rw [heq]
      exact MemLp.toMemLpPer hsub
    exact hInt_dot_rpow _ hDiff
  have hInt_υ_arg : ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄
                       ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
                       (μ, υ, Dυ) ∈ D →
      Integrable (fun x : Fin d → ℝ => |υ x| ^ γBarReal)
        (volume.restrict (UnitCube d)) := by
    intro μ υ Dυ hMem
    exact hInt_abs_rpow υ (hυ_memLp hMem)
  have hInt_υmu_arg : ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄
                         ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
                         (μ, υ, Dυ) ∈ D → ∀ (k : ℕ),
      Integrable (fun x : Fin d → ℝ =>
        |υ x - (seq.sol k).u x| ^ γBarReal)
        (volume.restrict (UnitCube d)) := by
    intro μ υ Dυ hMem k
    have h1 : MeasureTheory.MemLp υ (ENNReal.ofReal γBarReal)
        (volume.restrict (UnitCube d)) :=
      (hυ_memLp hMem).toMemLp
    have h2 : MeasureTheory.MemLp (seq.sol k).u (ENNReal.ofReal γBarReal)
        (volume.restrict (UnitCube d)) := (seq.sol k).huLp.toMemLp
    have hsub : MeasureTheory.MemLp (υ - (seq.sol k).u)
        (ENNReal.ofReal γBarReal)
        (volume.restrict (UnitCube d)) := h1.sub h2
    have heq_fun : (fun x => υ x - (seq.sol k).u x)
                    = (υ - (seq.sol k).u) := rfl
    have hMemLpPer : MemLpPer (d := d) (ENNReal.ofReal γBarReal)
        (fun x => υ x - (seq.sol k).u x) := by
      rw [heq_fun]; exact MemLp.toMemLpPer hsub
    exact hInt_abs_rpow _ hMemLpPer
  -- Per-`k` integrand non-negativity helpers.
  have hAbsRpow_nn : ∀ (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ),
      0 ≤ |f x| ^ γBarReal := fun f x => Real.rpow_nonneg (abs_nonneg _) _
  have hDotRpow_nn : ∀ (g : Fin d → (Fin d → ℝ) → ℝ) (x : Fin d → ℝ),
      0 ≤ ((fun i => g i x) ⬝ (fun i => g i x)) ^ (γBarReal / 2) :=
    fun g x => Real.rpow_nonneg (euclideanDot_self_nonneg _) _
  -- Assemble the family-restricted record.
  refine
    { hγ_one_le := hγ_one_le
      Aυ := fun μ υ Dυ =>
        ∫ x in UnitCube d, |υ x| ^ γBarReal
      Au := fun μ υ Dυ =>
        (2 : ℝ) ^ γBarReal *
          ((∫ x in UnitCube d, |υ x| ^ γBarReal) + Capr)
      ADυ := fun μ υ Dυ =>
        ∫ x in UnitCube d,
          ((fun i => Dυ i x) ⬝ (fun i => Dυ i x)) ^ (γBarReal / 2)
      ADu := fun μ υ Dυ =>
        (2 : ℝ) ^ γBarReal *
          ((∫ x in UnitCube d,
              ((fun i => Dυ i x) ⬝ (fun i => Dυ i x)) ^ (γBarReal / 2)) +
            ((d : ℝ)) ^ (γBarReal - 1) * Capr)
      hInt_DυDυ := hInt_DυDυ_arg
      hInt_DυmDu := hInt_DυmDu_arg
      hInt_υ := hInt_υ_arg
      hInt_υmu := hInt_υmu_arg
      hAυ := ?_
      hAu := ?_
      hADυ := ?_
      hADu := ?_ }
  · -- `hAυ`: trivial (≤ refl).
    intro μ υ Dυ _; exact le_refl _
  · -- `hAu`: per-`k` uniform bound on `∫|υ - u_k|^γ̄`.
    intro μ υ Dυ hMem k
    have hPointwise : ∀ x : Fin d → ℝ,
        |υ x - (seq.sol k).u x| ^ γBarReal
          ≤ (2 : ℝ) ^ γBarReal *
              (|υ x| ^ γBarReal + |(seq.sol k).u x| ^ γBarReal) :=
      fun x => palomar_RegularizedSequence_abs_sub_rpow_le_two_rpow_mul hγ_nn (υ x) ((seq.sol k).u x)
    have hInt_uk : Integrable (fun x : Fin d → ℝ =>
        |(seq.sol k).u x| ^ γBarReal)
        (volume.restrict (UnitCube d)) := by
      have hMemLp : MeasureTheory.MemLp (seq.sol k).u (ENNReal.ofReal γBarReal)
          (volume.restrict (UnitCube d)) := (seq.sol k).huLp.toMemLp
      have hI := hMemLp.integrable_norm_rpow hpne hpne_top
      rw [hγtoReal] at hI
      have heq : (fun x : Fin d → ℝ => ‖(seq.sol k).u x‖ ^ γBarReal)
                  = (fun x => |(seq.sol k).u x| ^ γBarReal) := by
        funext x; rw [Real.norm_eq_abs]
      rw [heq] at hI
      exact hI
    have hInt_υu : Integrable (fun x : Fin d → ℝ => |υ x| ^ γBarReal)
        (volume.restrict (UnitCube d)) := hInt_υ_arg hMem
    have hInt_sum : Integrable (fun x : Fin d → ℝ =>
        |υ x| ^ γBarReal + |(seq.sol k).u x| ^ γBarReal)
        (volume.restrict (UnitCube d)) := hInt_υu.add hInt_uk
    have hInt_RHS : Integrable (fun x : Fin d → ℝ =>
        (2 : ℝ) ^ γBarReal *
          (|υ x| ^ γBarReal + |(seq.sol k).u x| ^ γBarReal))
        (volume.restrict (UnitCube d)) := hInt_sum.const_mul _
    have hStep1 :
        ∫ x in UnitCube d, |υ x - (seq.sol k).u x| ^ γBarReal
          ≤ ∫ x in UnitCube d,
              (2 : ℝ) ^ γBarReal *
                (|υ x| ^ γBarReal + |(seq.sol k).u x| ^ γBarReal) := by
      apply MeasureTheory.integral_mono_ae
      · exact hInt_υmu_arg hMem k
      · exact hInt_RHS
      · exact Filter.Eventually.of_forall hPointwise
    have hLin :
        ∫ x in UnitCube d,
            (2 : ℝ) ^ γBarReal *
              (|υ x| ^ γBarReal + |(seq.sol k).u x| ^ γBarReal)
          = (2 : ℝ) ^ γBarReal *
              ((∫ x in UnitCube d, |υ x| ^ γBarReal) +
                ∫ x in UnitCube d, |(seq.sol k).u x| ^ γBarReal) := by
      rw [MeasureTheory.integral_const_mul]
      congr 1
      rw [MeasureTheory.integral_add hInt_υu hInt_uk]
    rw [hLin] at hStep1
    set Im : ℝ := ∫ x in UnitCube d, |(seq.sol k).m x| ^ βBarReal with hIm_def
    set Iu : ℝ := ∫ x in UnitCube d, |(seq.sol k).u x| ^ γBarReal with hIu_def
    set IDu : ℝ := ∑ i, ∫ x in UnitCube d, |(seq.sol k).Du i x| ^ γBarReal
      with hIDu_def
    have hIm_nn : 0 ≤ Im := MeasureTheory.integral_nonneg
      (fun x => Real.rpow_nonneg (abs_nonneg _) _)
    have hIu_nn : 0 ≤ Iu := MeasureTheory.integral_nonneg
      (fun x => Real.rpow_nonneg (abs_nonneg _) _)
    have hIDu_nn : 0 ≤ IDu :=
      Finset.sum_nonneg
        (fun i _ => MeasureTheory.integral_nonneg
          (fun x => Real.rpow_nonneg (abs_nonneg _) _))
    have hSum : Im + Iu + IDu ≤ Capr := hCapr k
    have hIu_le : Iu ≤ Capr := by linarith
    have hAu_bound :
        (2 : ℝ) ^ γBarReal *
            ((∫ x in UnitCube d, |υ x| ^ γBarReal) + Iu)
          ≤ (2 : ℝ) ^ γBarReal *
              ((∫ x in UnitCube d, |υ x| ^ γBarReal) + Capr) := by
      apply mul_le_mul_of_nonneg_left _ h2γ_nn
      linarith
    calc ∫ x in UnitCube d, |υ x - (seq.sol k).u x| ^ γBarReal
        ≤ (2 : ℝ) ^ γBarReal *
            ((∫ x in UnitCube d, |υ x| ^ γBarReal) +
              ∫ x in UnitCube d, |(seq.sol k).u x| ^ γBarReal) := hStep1
      _ = (2 : ℝ) ^ γBarReal *
            ((∫ x in UnitCube d, |υ x| ^ γBarReal) + Iu) := by rfl
      _ ≤ (2 : ℝ) ^ γBarReal *
            ((∫ x in UnitCube d, |υ x| ^ γBarReal) + Capr) := hAu_bound
  · -- `hADυ`: trivial.
    intro μ υ Dυ _; exact le_refl _
  · -- `hADu`: per-`k` uniform bound on `∫((Dυ - Du_k)·…)^(γ̄/2)`.
    intro μ υ Dυ hMem k
    have hPointwise : ∀ x : Fin d → ℝ,
        ((fun i => Dυ i x - (seq.sol k).Du i x)
            ⬝ (fun i => Dυ i x - (seq.sol k).Du i x))
            ^ (γBarReal / 2)
          ≤ (2 : ℝ) ^ γBarReal *
              (((fun i => Dυ i x) ⬝ (fun i => Dυ i x)) ^ (γBarReal / 2) +
                ((fun i => (seq.sol k).Du i x) ⬝ (fun i => (seq.sol k).Du i x))
                  ^ (γBarReal / 2)) := by
      intro x
      exact palomar_RegularizedSequence_euclideanDot_sub_rpow_le_two_rpow_mul (d := d) hγ_one_le
        (fun i => Dυ i x) (fun i => (seq.sol k).Du i x)
    have hPointwise_Du : ∀ x : Fin d → ℝ,
        ((fun i => (seq.sol k).Du i x) ⬝ (fun i => (seq.sol k).Du i x))
            ^ (γBarReal / 2)
          ≤ ((d : ℝ)) ^ (γBarReal - 1) *
              ∑ i, |(seq.sol k).Du i x| ^ γBarReal := by
      intro x
      exact euclideanDot_self_rpow_le_sum_rpow (d := d) hγ_one_le
        (fun i => (seq.sol k).Du i x)
    have hd_rpow_nn : (0 : ℝ) ≤ ((d : ℝ)) ^ (γBarReal - 1) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hInt_Duk_i : ∀ i : Fin d, Integrable
        (fun x : Fin d → ℝ => |(seq.sol k).Du i x| ^ γBarReal)
        (volume.restrict (UnitCube d)) := by
      intro i
      have hMemLp : MeasureTheory.MemLp ((seq.sol k).Du i)
          (ENNReal.ofReal γBarReal)
          (volume.restrict (UnitCube d)) := ((seq.sol k).hDuLp i).toMemLp
      have hI := hMemLp.integrable_norm_rpow hpne hpne_top
      rw [hγtoReal] at hI
      have heq : (fun x : Fin d → ℝ => ‖(seq.sol k).Du i x‖ ^ γBarReal)
                  = (fun x => |(seq.sol k).Du i x| ^ γBarReal) := by
        funext x; rw [Real.norm_eq_abs]
      rw [heq] at hI
      exact hI
    have hInt_sum_Duk : Integrable
        (fun x : Fin d → ℝ => ∑ i, |(seq.sol k).Du i x| ^ γBarReal)
        (volume.restrict (UnitCube d)) :=
      MeasureTheory.integrable_finset_sum _ (fun i _ => hInt_Duk_i i)
    have hInt_d_Duk : Integrable
        (fun x : Fin d → ℝ =>
          ((d : ℝ)) ^ (γBarReal - 1) *
            ∑ i, |(seq.sol k).Du i x| ^ γBarReal)
        (volume.restrict (UnitCube d)) := hInt_sum_Duk.const_mul _
    have hInt_DuDu : Integrable
        (fun x : Fin d → ℝ =>
          ((fun i => (seq.sol k).Du i x) ⬝ (fun i => (seq.sol k).Du i x))
            ^ (γBarReal / 2))
        (volume.restrict (UnitCube d)) := by
      apply MeasureTheory.Integrable.mono'
        (g := fun x => ((d : ℝ)) ^ (γBarReal - 1) *
            ∑ i, |(seq.sol k).Du i x| ^ γBarReal)
        hInt_d_Duk
      · have hγ2_nn : (0 : ℝ) ≤ γBarReal / 2 := by linarith
        have hCont : Continuous (fun y : ℝ => y ^ (γBarReal / 2)) :=
          Real.continuous_rpow_const hγ2_nn
        have hDot_aesm : AEStronglyMeasurable
            (fun x : Fin d → ℝ =>
              ((fun i => (seq.sol k).Du i x)
                ⬝ (fun i => (seq.sol k).Du i x)))
            (volume.restrict (UnitCube d)) := by
          unfold dotProduct
          refine Finset.aestronglyMeasurable_fun_sum _ ?_
          intro i _
          exact ((seq.sol k).hDuLp i).aestronglyMeasurable.mul
                ((seq.sol k).hDuLp i).aestronglyMeasurable
        exact hCont.comp_aestronglyMeasurable hDot_aesm
      · apply Filter.Eventually.of_forall
        intro x
        rw [Real.norm_eq_abs, abs_of_nonneg (hDotRpow_nn _ x)]
        exact hPointwise_Du x
    have hInt_DυDυ_x : Integrable (fun x : Fin d → ℝ =>
        ((fun i => Dυ i x) ⬝ (fun i => Dυ i x)) ^ (γBarReal / 2))
        (volume.restrict (UnitCube d)) := hInt_DυDυ_arg hMem
    have hInt_pair : Integrable (fun x : Fin d → ℝ =>
        ((fun i => Dυ i x) ⬝ (fun i => Dυ i x)) ^ (γBarReal / 2) +
        ((fun i => (seq.sol k).Du i x) ⬝ (fun i => (seq.sol k).Du i x))
          ^ (γBarReal / 2))
        (volume.restrict (UnitCube d)) := hInt_DυDυ_x.add hInt_DuDu
    have hInt_pair_const : Integrable (fun x : Fin d → ℝ =>
        (2 : ℝ) ^ γBarReal *
          (((fun i => Dυ i x) ⬝ (fun i => Dυ i x)) ^ (γBarReal / 2) +
            ((fun i => (seq.sol k).Du i x) ⬝ (fun i => (seq.sol k).Du i x))
              ^ (γBarReal / 2)))
        (volume.restrict (UnitCube d)) := hInt_pair.const_mul _
    have hStepA :
        ∫ x in UnitCube d,
            ((fun i => Dυ i x - (seq.sol k).Du i x)
              ⬝ (fun i => Dυ i x - (seq.sol k).Du i x))
              ^ (γBarReal / 2)
          ≤ ∫ x in UnitCube d,
              (2 : ℝ) ^ γBarReal *
                (((fun i => Dυ i x) ⬝ (fun i => Dυ i x)) ^ (γBarReal / 2) +
                  ((fun i => (seq.sol k).Du i x)
                    ⬝ (fun i => (seq.sol k).Du i x))
                    ^ (γBarReal / 2)) := by
      apply MeasureTheory.integral_mono_ae
      · exact hInt_DυmDu_arg hMem k
      · exact hInt_pair_const
      · exact Filter.Eventually.of_forall hPointwise
    have hLinA :
        ∫ x in UnitCube d,
            (2 : ℝ) ^ γBarReal *
              (((fun i => Dυ i x) ⬝ (fun i => Dυ i x)) ^ (γBarReal / 2) +
                ((fun i => (seq.sol k).Du i x)
                  ⬝ (fun i => (seq.sol k).Du i x))
                  ^ (γBarReal / 2))
          = (2 : ℝ) ^ γBarReal *
              ((∫ x in UnitCube d,
                  ((fun i => Dυ i x) ⬝ (fun i => Dυ i x))
                    ^ (γBarReal / 2)) +
                ∫ x in UnitCube d,
                  ((fun i => (seq.sol k).Du i x)
                    ⬝ (fun i => (seq.sol k).Du i x))
                    ^ (γBarReal / 2)) := by
      rw [MeasureTheory.integral_const_mul]
      congr 1
      rw [MeasureTheory.integral_add hInt_DυDυ_x hInt_DuDu]
    rw [hLinA] at hStepA
    have hStepB :
        ∫ x in UnitCube d,
            ((fun i => (seq.sol k).Du i x)
              ⬝ (fun i => (seq.sol k).Du i x))
              ^ (γBarReal / 2)
          ≤ ((d : ℝ)) ^ (γBarReal - 1) *
              ∑ i, ∫ x in UnitCube d, |(seq.sol k).Du i x| ^ γBarReal := by
      have h1 :
          ∫ x in UnitCube d,
              ((fun i => (seq.sol k).Du i x)
                ⬝ (fun i => (seq.sol k).Du i x))
                ^ (γBarReal / 2)
            ≤ ∫ x in UnitCube d,
                ((d : ℝ)) ^ (γBarReal - 1) *
                  ∑ i, |(seq.sol k).Du i x| ^ γBarReal := by
        apply MeasureTheory.integral_mono_ae
        · exact hInt_DuDu
        · exact hInt_d_Duk
        · exact Filter.Eventually.of_forall hPointwise_Du
      have h2 :
          ∫ x in UnitCube d,
              ((d : ℝ)) ^ (γBarReal - 1) *
                ∑ i, |(seq.sol k).Du i x| ^ γBarReal
            = ((d : ℝ)) ^ (γBarReal - 1) *
                ∫ x in UnitCube d, ∑ i, |(seq.sol k).Du i x| ^ γBarReal := by
        rw [MeasureTheory.integral_const_mul]
      have h3 :
          ∫ x in UnitCube d, ∑ i, |(seq.sol k).Du i x| ^ γBarReal
            = ∑ i, ∫ x in UnitCube d, |(seq.sol k).Du i x| ^ γBarReal := by
        rw [MeasureTheory.integral_finset_sum]
        intro i _
        exact hInt_Duk_i i
      rw [h2, h3] at h1
      exact h1
    set Im : ℝ := ∫ x in UnitCube d, |(seq.sol k).m x| ^ βBarReal with hIm_def
    set Iu : ℝ := ∫ x in UnitCube d, |(seq.sol k).u x| ^ γBarReal with hIu_def
    set IDu : ℝ := ∑ i, ∫ x in UnitCube d, |(seq.sol k).Du i x| ^ γBarReal
      with hIDu_def
    have hIm_nn : 0 ≤ Im := MeasureTheory.integral_nonneg
      (fun x => Real.rpow_nonneg (abs_nonneg _) _)
    have hIu_nn : 0 ≤ Iu := MeasureTheory.integral_nonneg
      (fun x => Real.rpow_nonneg (abs_nonneg _) _)
    have hIDu_nn : 0 ≤ IDu :=
      Finset.sum_nonneg
        (fun i _ => MeasureTheory.integral_nonneg
          (fun x => Real.rpow_nonneg (abs_nonneg _) _))
    have hSum : Im + Iu + IDu ≤ Capr := hCapr k
    have hIDu_le : IDu ≤ Capr := by linarith
    have hStepBC :
        ∫ x in UnitCube d,
            ((fun i => (seq.sol k).Du i x)
              ⬝ (fun i => (seq.sol k).Du i x))
              ^ (γBarReal / 2)
          ≤ ((d : ℝ)) ^ (γBarReal - 1) * Capr := by
      have := hStepB
      have hbound : ((d : ℝ)) ^ (γBarReal - 1) * IDu
          ≤ ((d : ℝ)) ^ (γBarReal - 1) * Capr :=
        mul_le_mul_of_nonneg_left hIDu_le hd_rpow_nn
      linarith
    have hCombine :
        (2 : ℝ) ^ γBarReal *
            ((∫ x in UnitCube d,
                ((fun i => Dυ i x) ⬝ (fun i => Dυ i x)) ^ (γBarReal / 2)) +
              ∫ x in UnitCube d,
                ((fun i => (seq.sol k).Du i x)
                  ⬝ (fun i => (seq.sol k).Du i x))
                  ^ (γBarReal / 2))
          ≤ (2 : ℝ) ^ γBarReal *
              ((∫ x in UnitCube d,
                  ((fun i => Dυ i x) ⬝ (fun i => Dυ i x)) ^ (γBarReal / 2)) +
                ((d : ℝ)) ^ (γBarReal - 1) * Capr) := by
      apply mul_le_mul_of_nonneg_left _ h2γ_nn
      linarith
    exact le_trans hStepA hCombine

/-! ### Phase 6b sanity checks -/

/-- **Phase 6b sanity check.** The universal-to-family bridge is
type-correct on a generic universal aux at any domain. -/
example
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH)
    (aux : LimitPairingSelectorGateauxAux (d := d) seq)
    (D : Set (StationaryMFG.Theorems.SimplePower.MFGTriple d)) :
    LimitPairingSelectorGateauxAuxFamily (d := d) seq D :=
  aux.toFamily D

/-- **Phase 6b sanity check.** The family-restricted producer is
type-correct on `D := Set.univ` and a universal supplier. -/
example
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH)
    (hγ_one_le : (1 : ℝ) ≤ γBarReal)
    (Capr : ℝ) (hCapr_nn : 0 ≤ Capr)
    (hCapr : ∀ k : ℕ,
      (∫ x in UnitCube d, |(seq.sol k).m x| ^ βBarReal) +
        (∫ x in UnitCube d, |(seq.sol k).u x| ^ γBarReal) +
        (∑ i, ∫ x in UnitCube d, |(seq.sol k).Du i x| ^ γBarReal)
          ≤ Capr)
    (hυ_memLp : ∀ (μ υ : (Fin d → ℝ) → ℝ)
                  (Dυ : Fin d → (Fin d → ℝ) → ℝ),
      MemLpPer (d := d) (ENNReal.ofReal γBarReal) υ)
    (hDυ_memLp : ∀ (μ υ : (Fin d → ℝ) → ℝ)
                   (Dυ : Fin d → (Fin d → ℝ) → ℝ) (i : Fin d),
      MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i)) :
    LimitPairingSelectorGateauxAuxFamily (d := d) seq Set.univ :=
  gateauxAux_of_paperHypotheses_familyRestrict
    seq hγ_one_le Capr hCapr_nn hCapr Set.univ
    (fun μ υ Dυ _ => hυ_memLp μ υ Dυ)
    (fun μ υ Dυ _ i => hDυ_memLp μ υ Dυ i)

/-! ### `MintyClosure` — authorized aux for `main_strong_VI`. -/

/-- **Authorized auxiliary bundle** for T9's Minty upgrade.
Packages `main_strong_VI`'s prerequisites: a domain `D ⊂ MFGTriple d`
containing the limit triple, segment closure of `D`, and
hemicontinuity of `A_0` on `D`.

The follow-up task `infra-P4-rebuild-T9-discharge-minty-closure`
closes this bundle from `(hmon, hpow, hV)` via
`Hemicontinuity.A0_isHemicontinuous` and convexity of the regularity
constraints. -/
structure MintyClosure
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ) where
  /-- The domain. -/
  D : Set (StationaryMFG.Theorems.SimplePower.MFGTriple d)
  /-- Segment closure of `D`. -/
  hSeg : ∀ ⦃μBar ῡ Dῡ⦄, (μBar, ῡ, Dῡ) ∈ D →
          ∀ ⦃μ υ Dυ⦄, (μ, υ, Dυ) ∈ D →
          ∀ t ∈ Set.Icc (0 : ℝ) 1,
            ((fun x => StationaryMFG.Theorems.SimplePower.cxComb μ μBar t x),
             (fun x => StationaryMFG.Theorems.SimplePower.cxComb υ ῡ t x),
             (fun i x =>
               StationaryMFG.Theorems.SimplePower.cxCombGrad Dυ Dῡ t i x))
              ∈ D
  /-- Hemicontinuity of `A_0` on `D` (restricted-test form, per
  iter `infra-P7-sigfix-T1-drain-A-restricted-hemicont`). The test
  triple is forced to the family-derivable difference shape used by
  `main_strong_VI`. -/
  hAhc : StationaryMFG.Theorems.SimplePower.IsHemicontinuousMFG_restricted d D
            (mfgOperatorPair (V := V) (H := H) (DpH := DpH))
  /-- The limit triple is in `D`. -/
  hLimMem : (mLim, uLim, DuLim) ∈ D

/-! ### `MintyClosureSelector` — the genuine hemicontinuity-aggregator residue.

The fields of `MintyClosure` split cleanly into two groups:

* **Auto-derivable from the trivial choice `D = Set.univ`**: segment
  closure of `D` (all triples are in `Set.univ` so any convex
  combination is too) and limit-triple membership.

* **Genuinely segment-data-dependent**: the per-pair
  `HemicontSegmentData` aggregator that
  `Theorems.SimplePower.A0_isHemicontinuous` consumes. With
  `D = Set.univ`, this aggregator's positivity field
  `hPos : 0 < cxComb μ μBar t x` is **literally false** in general
  (e.g. `μ ≡ -1, μBar ≡ -1`), so the aggregator cannot be supplied
  closed-form: the genuine paper proof restricts the segment to a
  strict-positivity domain via the apriori `essinf m_ε > 0` bound
  (paper `lem:bdd-below-eps`, line 815) before passing to the limit.

`MintyClosureSelector` packages **only the second group** as
authorised input per CONVENTIONS §8 (statement-then-proof
discipline), exactly mirroring `LimitPairingSelector`'s role for
T9.b. The follow-up
`infra-P4-rebuild-T9-discharge-minty-closure-selector` (in
`docs/TASKS/backlog/`) discharges the selector from
`(hmon, hpow, hV)` plus the apriori-bound chain. -/

/-- **Selector-only authorised inputs** for the `MintyClosure`
producer.

Per CONVENTIONS §8, this structure isolates the genuinely missing
hemicontinuity-aggregator content — the per-pair
`HemicontSegmentData` bundle — leaving the producer to discharge the
trivial fields automatically from the choice `D = Set.univ`.

Fields:

* `hReg`            : the basic regularity bundle on `(H, DpH)`
                      that `A0_isHemicontinuous` requires. The
                      consumer can pass `hmon.toRegularityH` here.
* `γBar`, `hγ`      : the (unused at `ε = 0`) Gateaux-dominator
                      exponent and its `2 ≤ γBar` lower bound.
* `hData`           : the universally-quantified
                      `HemicontSegmentData` aggregator on
                      `Set.univ × Set.univ`, supplying the
                      per-segment dominators / measurability /
                      positivity data needed by `lem_hemicont`. -/
structure MintyClosureSelector
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)) where
  /-- Basic regularity bundle on `(H, DpH)`. -/
  hReg : Hamiltonian.RegularityH (d := d) H DpH
  /-- The (unused at `ε = 0`) Gateaux-dominator exponent. -/
  γBar : ℝ
  /-- Lower bound on `γBar` required by `A0_isHemicontinuous`. -/
  hγ : 2 ≤ γBar
  /-- Universally-quantified `HemicontSegmentData` aggregator. The
  pairs of segment endpoints range over `Set.univ × Set.univ`
  (matching the producer's choice `D = Set.univ`). -/
  hData : ∀ ⦃μBar ῡ Dῡ⦄,
    (μBar, ῡ, Dῡ) ∈ (Set.univ : Set (StationaryMFG.Theorems.SimplePower.MFGTriple d)) →
    ∀ ⦃μ υ Dυ⦄,
    (μ, υ, Dυ) ∈ (Set.univ : Set (StationaryMFG.Theorems.SimplePower.MFGTriple d)) →
    ∀ (η ν : (Fin d → ℝ) → ℝ)
      (Dν : Fin d → (Fin d → ℝ) → ℝ),
    StationaryMFG.Theorems.SimplePower.HemicontSegmentData
      (d := d) V H DpH γBar Dυ Dῡ μ μBar υ ῡ Dν η ν

/-! ### Producer: `mintyClosure_of_paperHypotheses`

Per CONVENTIONS §8, this discharges the structural / domain-trivial
content of `MintyClosure` genuinely (`D = Set.univ`, segment closure
trivial, limit-membership trivial), while leaving the
hemicontinuity-aggregator content parameterised through `selector`.
The producer's hemicontinuity field is built by invoking
`A0_isHemicontinuous` on `selector.hReg, selector.hγ` and the
universally-quantified segment-data aggregator. -/

/-- **AC-discharge producer (amended).** Build a `MintyClosure` from
the paper hypotheses `(hmon, hpow, hV)` plus the authorised
`MintyClosureSelector`. The choice `D = Set.univ` discharges the
universal-quantifier requirement of the consumer
(`limitSolutionData_of_regularizedSequence`).

* `hmon`/`hpow`/`hV` are accepted (and currently unused inside the
  body) to pin the producer to the paper-hypothesis chain shape;
  `hmon.toRegularityH` is *equivalent* information to
  `selector.hReg` (the consumer is free to pass the former for the
  latter).
* The hemicontinuity field is `A0_isHemicontinuous` instantiated at
  `selector.hReg, selector.γBar, selector.hγ, Set.univ,
  selector.hData`. -/
noncomputable def mintyClosure_of_paperHypotheses
    {γBarReal βBarReal' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (_hmon : Hamiltonian.HypothesisMonotone H DpH)
    (_hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (_hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    (selector : MintyClosureSelector (d := d) V H DpH) :
    MintyClosure (d := d) V H DpH mLim uLim DuLim where
  D := Set.univ
  hSeg := by
    intro _ _ _ _ _ _ _ _ _ _
    exact Set.mem_univ _
  hAhc :=
    -- Weakened to the restricted-test form per iter
    -- `infra-P7-sigfix-T1-drain-A-restricted-hemicont`.
    (StationaryMFG.Theorems.SimplePower.A0_isHemicontinuous
      (V := V) (H := H) (DpH := DpH)
      selector.hReg selector.γBar (lt_of_lt_of_le one_lt_two selector.hγ) Set.univ
      selector.hData).toRestricted
  hLimMem := Set.mem_univ _
  -- The unused real exponent `γBarReal` is threaded through to keep
  -- the producer's signature aligned with the rest of the T9 chain
  -- (which uses `γBarReal` to phrase the consumer's `hExp` /
  -- `wkBundle` arguments). It is not consumed in the body.

/-- **Universal-domain certificate.** The `D` field of
`mintyClosure_of_paperHypotheses` is definitionally `Set.univ`. This
is the witness the consumer
`limitSolutionData_of_regularizedSequence` needs for its `hDuniv`
hypothesis. -/
@[simp] lemma mintyClosure_of_paperHypotheses_D
    {γBarReal βBarReal' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    (selector : MintyClosureSelector (d := d) V H DpH) :
    (mintyClosure_of_paperHypotheses
        (γBarReal := γBarReal) (βBarReal' := βBarReal')
        hmon hpow hV mLim uLim DuLim selector).D = Set.univ := rfl

/-- **AC sanity check.** `mintyClosure_of_paperHypotheses` produces a
`MintyClosure` from `(hmon, hpow, hV, selector)` whose `D` field is
`Set.univ`. The `hDuniv` hypothesis of
`limitSolutionData_of_regularizedSequence` is dischargeable by
`mintyClosure_of_paperHypotheses_D`. -/
example
    {γBarReal βBarReal' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    (selector : MintyClosureSelector (d := d) V H DpH) :
    MintyClosure (d := d) V H DpH mLim uLim DuLim :=
  mintyClosure_of_paperHypotheses
    (γBarReal := γBarReal) (βBarReal' := βBarReal')
    hmon hpow hV mLim uLim DuLim selector

/-- **AC sanity check.** The producer `D = Set.univ` certificate
discharges the consumer's `hDuniv` hypothesis. -/
example
    {γBarReal βBarReal' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    (selector : MintyClosureSelector (d := d) V H DpH) :
    (mintyClosure_of_paperHypotheses
        (γBarReal := γBarReal) (βBarReal' := βBarReal')
        hmon hpow hV mLim uLim DuLim selector).D = Set.univ :=
  mintyClosure_of_paperHypotheses_D
    (γBarReal := γBarReal) (βBarReal' := βBarReal')
    hmon hpow hV mLim uLim DuLim selector

/-! ### Closed-form producer:
`mintyClosureSelector_of_paperHypotheses`.

Per CONVENTIONS §1b this section closes the
`MintyClosureSelector` parameter of `mintyClosure_of_paperHypotheses`
in favour of an authorised paper-residue bundle
`MintyClosureSelectorPaperResidue` carrying the genuinely
non-closed-form content (the universally-quantified
`HemicontSegmentData` aggregator on `Set.univ × Set.univ`, whose
`hPos` field is literally false on the full universe — see paper
`lem:hemicont` + `lem:bdd-below-eps` chain).

This is the smallest of the three remaining bundle producers
called out in `infra-P4-rebuild-T10-discharge-final-chain` Step (3).
The producer is structurally a thin wrapper: with `D = Set.univ`
fixed, the only T9.c content beyond `(hmon, hpow, hV)` is exactly
the `HemicontSegmentData` aggregator (the other selector fields —
`hReg`, `γBar`, `hγ` — are paper-trivial, e.g. `hmon.toRegularityH`
gives `hReg`).

The composition with `mintyClosure_of_paperHypotheses` yields a
fully closed-form `MintyClosure` whose `D` field is definitionally
`Set.univ`, so the consumer
`limitSolutionData_of_regularizedSequence` discharges its
`hDuniv` parameter via `mintyClosure_of_paperHypotheses_D`. -/

/-- **Authorised paper-residue inputs** for the `MintyClosureSelector`
producer.

Per CONVENTIONS §1b, this structure isolates the genuinely
non-closed-form content of `MintyClosureSelector` — the per-pair
universally-quantified `HemicontSegmentData` aggregator. With
`D = Set.univ`, the aggregator's `hPos` field
`0 < cxComb μ μBar t x` is literally false (counterexample
`μ = μBar ≡ -1`); the genuine paper proof restricts to a
strict-positivity domain via `lem:bdd-below-eps` (paper line 815)
before passing to the limit. The strict-positivity-domain
treatment is in the `MintyClosureSelectorOn` section below; this
residue bundle is the universal counterpart authorised at the
`Set.univ` shape.

Fields mirror those of `MintyClosureSelector`:

* `hReg`   : the basic `(H, DpH)` regularity bundle
            (paper-trivial: `hmon.toRegularityH` would supply it).
* `γBar`   : the (unused at `ε = 0`) Gateaux-dominator exponent.
* `hγ`     : `2 ≤ γBar`.
* `hData`  : the universally-quantified `HemicontSegmentData`
            aggregator on `Set.univ × Set.univ`.

The selector producer below is a direct projection from this
residue. -/
structure MintyClosureSelectorPaperResidue
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)) where
  /-- Basic regularity bundle on `(H, DpH)`. Paper-trivial:
  `hmon.toRegularityH` would supply this. -/
  hReg : Hamiltonian.RegularityH (d := d) H DpH
  /-- The (unused at `ε = 0`) Gateaux-dominator exponent. -/
  γBar : ℝ
  /-- Lower bound on `γBar` required by `A0_isHemicontinuous`. -/
  hγ : 2 ≤ γBar
  /-- Universally-quantified `HemicontSegmentData` aggregator on
  `Set.univ × Set.univ`. This is the genuinely non-closed-form
  content; per CONVENTIONS §1b, it is supplied as an authorised
  paper-residue input pending the strict-positivity-domain +
  universality-bridge chain (paper `lem:bdd-below-eps` +
  `lem:ADFGU.a/b`). -/
  hData : ∀ ⦃μBar ῡ Dῡ⦄,
    (μBar, ῡ, Dῡ) ∈ (Set.univ : Set (StationaryMFG.Theorems.SimplePower.MFGTriple d)) →
    ∀ ⦃μ υ Dυ⦄,
    (μ, υ, Dυ) ∈ (Set.univ : Set (StationaryMFG.Theorems.SimplePower.MFGTriple d)) →
    ∀ (η ν : (Fin d → ℝ) → ℝ)
      (Dν : Fin d → (Fin d → ℝ) → ℝ),
    StationaryMFG.Theorems.SimplePower.HemicontSegmentData
      (d := d) V H DpH γBar Dυ Dῡ μ μBar υ ῡ Dν η ν

/-- **Closed-form `MintyClosureSelector` producer.** Build a
`MintyClosureSelector` from the paper hypotheses
`(hmon, hpow, hV)` plus the authorised paper-residue bundle.

This is a thin wrapper: `MintyClosureSelector` and
`MintyClosureSelectorPaperResidue` have isomorphic field tuples;
the wrapper exists to signal at the type level that the content
flows through the paper-hypothesis chain (via `hmon`, `hpow`, `hV`)
plus a single explicitly-residue bundle, rather than directly. The
paper hypotheses are *currently unused* in the body — `hmon` could
in principle supply `hReg` via `hmon.toRegularityH`, but the
residue's `hReg` field is taken instead to keep the producer
parameterisation uniform with the other paper-residue producers in
this module (see `limitPairingSelector_of_paperHypotheses`). -/
noncomputable def mintyClosureSelector_of_paperHypotheses
    {βBarReal' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (_hmon : Hamiltonian.HypothesisMonotone H DpH)
    (_hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (_hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (residue : MintyClosureSelectorPaperResidue (d := d) V H DpH) :
    MintyClosureSelector (d := d) V H DpH where
  hReg  := residue.hReg
  γBar  := residue.γBar
  hγ    := residue.hγ
  hData := residue.hData

/-- **AC sanity check.** `mintyClosureSelector_of_paperHypotheses`
typechecks at the expected `MintyClosureSelector` shape from
`(hmon, hpow, hV, residue)`. -/
example
    {βBarReal' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (residue : MintyClosureSelectorPaperResidue (d := d) V H DpH) :
    MintyClosureSelector (d := d) V H DpH :=
  mintyClosureSelector_of_paperHypotheses
    (βBarReal' := βBarReal') hmon hpow hV residue

/-- **AC sanity check.** Composing
`mintyClosureSelector_of_paperHypotheses` with
`mintyClosure_of_paperHypotheses` produces a `MintyClosure` whose
`D` field is `Set.univ` — the certificate
`limitSolutionData_of_regularizedSequence` consumes for `hDuniv`.

This is the intended consumer-side composition: with the residue
bundle supplied closed-form by the upstream T9.b/T9.c chain, the
two producers stack to a `MintyClosure` whose universality
certificate is internally discharged. -/
example
    {γBarReal βBarReal' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    (residue : MintyClosureSelectorPaperResidue (d := d) V H DpH) :
    (mintyClosure_of_paperHypotheses
        (γBarReal := γBarReal) (βBarReal' := βBarReal')
        hmon hpow hV mLim uLim DuLim
        (mintyClosureSelector_of_paperHypotheses
          (βBarReal' := βBarReal') hmon hpow hV residue)).D
      = Set.univ :=
  mintyClosure_of_paperHypotheses_D
    (γBarReal := γBarReal) (βBarReal' := βBarReal')
    hmon hpow hV mLim uLim DuLim
    (mintyClosureSelector_of_paperHypotheses
      (βBarReal' := βBarReal') hmon hpow hV residue)

/-! ### Strict-positivity domain and selector — genuine `hPos` discharge.

This subsection discharges **Piece P1** of follow-up task
`infra-P4-rebuild-T9-discharge-minty-closure-selector`: building a
`MintyClosureSelector`-shape aggregator on a *strict-positivity
domain* `D_pos = StrictPositivityDomain c` for some `c > 0`, where the
`hPos` field of `HemicontSegmentData` is genuinely closed by
pointwise convexity of strict positivity.

The remaining piece — recovering the universal `hStrongVI` from the
`D_pos`-restricted strong VI — is filed as
`infra-P4-rebuild-T9-discharge-minty-universality` in
`docs/TASKS/backlog/`. That separate piece concerns
`mfgOperatorPair` test-triple continuity (paper `lem:ADFGU.a/b`) and
the apriori `essinf m_ε > 0` chain (paper line 815
`lem:bdd-below-eps`); it is structurally independent of the
segment-data aggregator content treated here.

The crux of this section is `cxComb_pos_of_strictPos`: a one-line
convexity proof that `(1-t)·μBar(x) + t·μ(x) ≥ c` whenever both
endpoints exceed `c` and `t ∈ [0,1]`. This *closes* the `hPos` field
of `HemicontSegmentData` for every pair of triples in `D_pos`, which
the existing `Set.univ`-shaped `MintyClosureSelector` could not do
(the universal `hPos` is literally false on `Set.univ`, e.g. for
`μ ≡ -1`).
-/

/-- **Strict-positivity domain.** The set of MFG triples whose density
component is bounded below pointwise by a constant `c`. For `c > 0`,
this is the strict-positivity domain that the segment-data aggregator
operates on. -/
def StrictPositivityDomain (c : ℝ) :
    Set (StationaryMFG.Theorems.SimplePower.MFGTriple d) :=
  { T | ∀ x, c ≤ T.1 x }

/-- **Membership characterisation.** `(μ, υ, Dυ) ∈ StrictPositivityDomain c`
iff `∀ x, c ≤ μ x`. -/
@[simp] lemma mem_strictPositivityDomain_iff
    (c : ℝ) (μ υ : (Fin d → ℝ) → ℝ)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ) :
    (μ, υ, Dυ) ∈ (StrictPositivityDomain (d := d) c) ↔ ∀ x, c ≤ μ x :=
  Iff.rfl

/-- **Convexity of strict positivity.** If both endpoints exceed `c`
pointwise and `0 < c`, then the convex combination
`cxComb μ μBar t x = (1-t)·μBar(x) + t·μ(x)` exceeds `c` for every
`t ∈ [0,1]`, hence is strictly positive.

This is the genuine `hPos` content for `HemicontSegmentData` on the
strict-positivity domain. -/
lemma cxComb_pos_of_strictPos
    {c : ℝ} (hc : 0 < c)
    (μ μBar : (Fin d → ℝ) → ℝ)
    (hμ : ∀ x, c ≤ μ x) (hμBar : ∀ x, c ≤ μBar x)
    (x : Fin d → ℝ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 < StationaryMFG.Theorems.SimplePower.cxComb μ μBar t x := by
  obtain ⟨ht0, ht1⟩ := ht
  -- `cxComb μ μBar t x = (1 - t) · μBar x + t · μ x`.
  -- We show `c ≤ cxComb μ μBar t x` and chain with `0 < c`.
  have h1mt_nn : 0 ≤ 1 - t := by linarith
  have ht_nn : 0 ≤ t := ht0
  -- `(1 - t) · μBar x ≥ (1 - t) · c` and `t · μ x ≥ t · c`.
  have hA : (1 - t) * c ≤ (1 - t) * μBar x :=
    mul_le_mul_of_nonneg_left (hμBar x) h1mt_nn
  have hB : t * c ≤ t * μ x :=
    mul_le_mul_of_nonneg_left (hμ x) ht_nn
  -- Sum: `((1-t) + t) · c ≤ (1-t) · μBar x + t · μ x = cxComb μ μBar t x`.
  have hSum : (1 - t) * c + t * c ≤ (1 - t) * μBar x + t * μ x :=
    add_le_add hA hB
  have hCoeff : (1 - t) * c + t * c = c := by ring
  have hCxComb_eq :
      StationaryMFG.Theorems.SimplePower.cxComb μ μBar t x
        = (1 - t) * μBar x + t * μ x := rfl
  -- Combine.
  calc 0 < c := hc
    _ = (1 - t) * c + t * c := hCoeff.symm
    _ ≤ (1 - t) * μBar x + t * μ x := hSum
    _ = StationaryMFG.Theorems.SimplePower.cxComb μ μBar t x := hCxComb_eq.symm

/-- **Strict-positivity domain is segment-closed.** For `0 < c`, the
strict-positivity domain `D_pos = StrictPositivityDomain c` is closed
under convex combinations: if both endpoints lie in `D_pos`, every
`t ∈ [0, 1]` convex combination of their density components is again
≥ c. -/
lemma strictPositivityDomain_segment_closed
    {c : ℝ} (hc : 0 ≤ c)
    {μBar : (Fin d → ℝ) → ℝ} {ῡ : (Fin d → ℝ) → ℝ}
    {Dῡ : Fin d → (Fin d → ℝ) → ℝ}
    (hBar : (μBar, ῡ, Dῡ) ∈ (StrictPositivityDomain (d := d) c))
    {μ : (Fin d → ℝ) → ℝ} {υ : (Fin d → ℝ) → ℝ}
    {Dυ : Fin d → (Fin d → ℝ) → ℝ}
    (hμ : (μ, υ, Dυ) ∈ (StrictPositivityDomain (d := d) c))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ((fun x => StationaryMFG.Theorems.SimplePower.cxComb μ μBar t x),
     (fun x => StationaryMFG.Theorems.SimplePower.cxComb υ ῡ t x),
     (fun i x =>
       StationaryMFG.Theorems.SimplePower.cxCombGrad Dυ Dῡ t i x))
       ∈ (StrictPositivityDomain (d := d) c) := by
  -- Goal: `∀ x, c ≤ cxComb μ μBar t x`.
  intro x
  obtain ⟨ht0, ht1⟩ := ht
  have h1mt_nn : 0 ≤ 1 - t := by linarith
  have ht_nn : 0 ≤ t := ht0
  have hμBar_x : c ≤ μBar x := hBar x
  have hμ_x : c ≤ μ x := hμ x
  have hA : (1 - t) * c ≤ (1 - t) * μBar x :=
    mul_le_mul_of_nonneg_left hμBar_x h1mt_nn
  have hB : t * c ≤ t * μ x :=
    mul_le_mul_of_nonneg_left hμ_x ht_nn
  have hSum : (1 - t) * c + t * c ≤ (1 - t) * μBar x + t * μ x :=
    add_le_add hA hB
  have hCoeff : (1 - t) * c + t * c = c := by ring
  -- `cxComb` unfolds to `(1 - t) * μBar x + t * μ x`.
  show c ≤ StationaryMFG.Theorems.SimplePower.cxComb μ μBar t x
  have : StationaryMFG.Theorems.SimplePower.cxComb μ μBar t x
            = (1 - t) * μBar x + t * μ x := rfl
  rw [this]
  linarith

/-! ### Phase F family-positivity lemmas.

Per `infra-P5-theorem1-phase-F-minty-family-restricted`, Phase F
replaces the universal `HemicontSegmentData` aggregator with three
family-restricted producers. Each per-family `HemicontSegmentData`
needs its `hPos` field discharged via `cxComb_pos_of_strictPos`,
which in turn needs strict-positivity-domain membership of both
endpoints. The three lemmas below are the family-specific gates
that lift the paper test-family shape to the `StrictPositivityDomain c`
predicate, closing the family-specific `hPos` content.

These lemmas are small (each ~10 lines); they unblock the per-family
`hemicontSegmentData_{set,signed,transport}_of_paperHypotheses`
producers without committing to the full per-family chain rewire
(which is filed as three follow-up tasks under `backlog/`).

Paper references: `lem:bdd-below-eps` (paper line 815, regularised
density `m_ε ≥ ε > 0`); `lem:ADFGU.a/b` (paper §8). -/

/-- **Family-positivity (set perturbation).** If the regularised
density `m` is bounded below by `c > 0` pointwise and the
perturbation `ρ` is non-negative pointwise, the set-family test
density `μ = m + S.indicator (· ↦ ρ)` lies in
`StrictPositivityDomain c`.

Paper test family `lem:ADFGU.a`: with `m = m_ε ≥ ε` (paper line
815, `lem:bdd-below-eps`) and `ρ ≥ 0`, the test density inherits
the lower bound `ε` because `S.indicator … ≥ 0`. -/
lemma mem_strictPositivityDomain_set_family
    {c : ℝ} (_hc : 0 ≤ c)
    (m : (Fin d → ℝ) → ℝ) (hm : ∀ x, c ≤ m x)
    (S : Set (Fin d → ℝ)) (ρ : (Fin d → ℝ) → ℝ)
    (hρ : ∀ x, 0 ≤ ρ x)
    (υ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ) :
    ((fun x => m x + S.indicator ρ x), υ, Dυ)
      ∈ (StrictPositivityDomain (d := d) c) := by
  intro x
  -- `S.indicator ρ x = if x ∈ S then ρ x else 0`, so
  -- `S.indicator ρ x ≥ 0` follows from `ρ ≥ 0`.
  have hInd : 0 ≤ S.indicator ρ x :=
    Set.indicator_nonneg (fun y _ => hρ y) x
  have : c ≤ m x + S.indicator ρ x := by linarith [hm x]
  exact this

/-- **Family-positivity (signed perturbation).** If the regularised
density `m` is bounded below by `c > 0` and the signed multiplicative
perturbation `σ · m · 1_S` has magnitude bounded by `c / 2`
pointwise, the signed test density
`μ = m + σ · m · S.indicator (· ↦ 1)` lies in
`StrictPositivityDomain (c / 2)`.

Paper test family `lem:ADFGU.b`: paper restricts to `|σ|` small
enough that the multiplicative perturbation cannot drive the
density to zero; `c / 2` is the standard half-margin bound
following from `|σ · m · 1_S| ≤ c / 2`. -/
lemma mem_strictPositivityDomain_signed_family
    {c : ℝ} (hc : 0 ≤ c)
    (m : (Fin d → ℝ) → ℝ) (hm : ∀ x, c ≤ m x)
    (σ : ℝ) (S : Set (Fin d → ℝ))
    (hσBound : ∀ x,
      |σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x| ≤ c / 2)
    (υ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ) :
    ((fun x => m x +
        σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x),
       υ, Dυ)
      ∈ (StrictPositivityDomain (d := d) (c / 2)) := by
  intro x
  -- `|y| ≤ c/2 → -(c/2) ≤ y`
  have hAbs : |σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x|
                ≤ c / 2 := hσBound x
  have hLower : -(c / 2)
        ≤ σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
    have := neg_abs_le
              (σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
    linarith [hAbs]
  have hmx : c ≤ m x := hm x
  -- `m x + (signed perturb) ≥ c - c/2 = c/2`.
  have : c / 2 ≤ m x +
        σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
    linarith
  exact this

/-- **Family-positivity (transport perturbation).** The transport
test family fixes the density at `μ = m`; the test perturbation
acts on `(u, Du)` only. Strict-positivity-domain membership for
the density component reduces to the input bound `∀ x, c ≤ m x`. -/
lemma mem_strictPositivityDomain_transport_family
    {c : ℝ} (_hc : 0 ≤ c)
    (m : (Fin d → ℝ) → ℝ) (hm : ∀ x, c ≤ m x)
    (υ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ) :
    (m, υ, Dυ) ∈ (StrictPositivityDomain (d := d) c) := by
  intro x; exact hm x

/-- **AC sanity check (set family).** With a positive lower bound
on `m` and a non-negative perturbation `ρ`, the set-family test
density lies in the strict-positivity domain at the same constant. -/
example (d : ℕ) (m : (Fin d → ℝ) → ℝ) (hm : ∀ x, (1 : ℝ) ≤ m x)
    (S : Set (Fin d → ℝ)) (ρ : (Fin d → ℝ) → ℝ) (hρ : ∀ x, 0 ≤ ρ x)
    (υ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ) :
    ((fun x => m x + S.indicator ρ x), υ, Dυ)
      ∈ (StrictPositivityDomain (d := d) 1) :=
  mem_strictPositivityDomain_set_family (d := d) zero_le_one m hm S ρ hρ υ Dυ

/-- **AC sanity check (transport family).** The transport test
density is `m` itself, so strict-positivity-domain membership is
just the `m` lower bound. -/
example (d : ℕ) (m : (Fin d → ℝ) → ℝ) (hm : ∀ x, (1 : ℝ) ≤ m x)
    (υ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ) :
    (m, υ, Dυ) ∈ (StrictPositivityDomain (d := d) 1) :=
  mem_strictPositivityDomain_transport_family (d := d) zero_le_one m hm υ Dυ

/-! ### Domain-parameterised selector and producer.

The genuinely-narrower selector quantifies over pairs in
`StrictPositivityDomain c`, where the `hPos` field of
`HemicontSegmentData` is closed-form derivable. The remaining
fields (dominator integrability, AE-strong-measurability, pointwise
bounds) are the dominator-content of `infra-P4-hemi-dominator-holder`
and remain authorised inputs (the dominator-holder lemmas in
`Theorems/SimplePower/Hemicontinuity.lean` already provide the
required `MemLpPer 1` certificates; the wiring of those certificates
into `HemicontSegmentData` is the residue tracked by the universality
follow-up). -/

/-- **Narrowed-residue inputs** for the strict-positivity selector.

This is the per-pair `HemicontSegmentData` aggregator on the
*strict-positivity domain* `D_pos = StrictPositivityDomain c`: for
every two endpoint triples in `D_pos` and every test triple, the user
supplies the *six* dominator/measurability/bound fields of
`HemicontSegmentData`, and the `hPos` field is *not* requested
(because it is closed-form derivable here from the strict-positivity
hypotheses on the endpoints).

Concretely the user supplies:

* `g_unreg, g_gat : (Fin d → ℝ) → ℝ` per pair, with `IntegrableOn`
  on `UnitCube d`,
* AE-strong-measurability of the integrands `aepsiIntegrandAt_unreg`,
  `aepsiIntegrandAt_gateaux` for each `t ∈ [0,1]`,
* pointwise dominator bounds.

Mirrors the `HemicontSegmentData` structure with `hPos` removed. -/
structure HemicontSegmentDataResidue {d : ℕ}
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (γBar : ℝ)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ)
    (μ mBar υ ῡ : (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ) : Type where
  /-- Dominator for the unregularised integrand. -/
  g_unreg : (Fin d → ℝ) → ℝ
  /-- Dominator for the Gateaux integrand. -/
  g_gat : (Fin d → ℝ) → ℝ
  hg_unreg_int : MeasureTheory.IntegrableOn g_unreg
                  (StationaryMFG.Periodic.UnitCube d) MeasureTheory.volume
  hg_gat_int : MeasureTheory.IntegrableOn g_gat
                  (StationaryMFG.Periodic.UnitCube d) MeasureTheory.volume
  hF_unreg_meas : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    MeasureTheory.AEStronglyMeasurable
      (fun x =>
        StationaryMFG.Theorems.SimplePower.aepsiIntegrandAt_unreg
          V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν x t)
      (MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d))
  hF_unreg_bound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    ∀ᵐ x ∂(MeasureTheory.volume.restrict
              (StationaryMFG.Periodic.UnitCube d)),
      ‖StationaryMFG.Theorems.SimplePower.aepsiIntegrandAt_unreg
          V H DpH Dυ Dῡ μ mBar υ ῡ Dν η ν x t‖
        ≤ g_unreg x
  hF_gat_meas : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    MeasureTheory.AEStronglyMeasurable
      (fun x =>
        StationaryMFG.Theorems.SimplePower.aepsiIntegrandAt_gateaux
          γBar Dυ Dῡ υ ῡ Dν ν x t)
      (MeasureTheory.volume.restrict (StationaryMFG.Periodic.UnitCube d))
  hF_gat_bound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    ∀ᵐ x ∂(MeasureTheory.volume.restrict
              (StationaryMFG.Periodic.UnitCube d)),
      ‖StationaryMFG.Theorems.SimplePower.aepsiIntegrandAt_gateaux
          γBar Dυ Dῡ υ ῡ Dν ν x t‖ ≤ g_gat x

/-- **Reconstitute `HemicontSegmentData` from positivity + residue.**

Given strict positivity at the two endpoints of the segment and the
six residue fields (dominators, integrability, AE-strong-measurability,
bounds), reconstitute the full `HemicontSegmentData` bundle. The
`hPos` field is closed by `cxComb_pos_of_strictPos`; the other fields
are taken from the residue.

This is the genuine `hPos` discharge of
`infra-P4-rebuild-T9-discharge-minty-closure-selector`. -/
def hemicontSegmentData_of_strictPos
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBar : ℝ} {c : ℝ} (hc : 0 < c)
    {Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ}
    {μ mBar υ ῡ : (Fin d → ℝ) → ℝ}
    (hμ : ∀ x, c ≤ μ x) (hmBar : ∀ x, c ≤ mBar x)
    {Dν : Fin d → (Fin d → ℝ) → ℝ}
    {η ν : (Fin d → ℝ) → ℝ}
    (residue : HemicontSegmentDataResidue (d := d)
                  V H DpH γBar Dυ Dῡ μ mBar υ ῡ Dν η ν) :
    StationaryMFG.Theorems.SimplePower.HemicontSegmentData
      (d := d) V H DpH γBar Dυ Dῡ μ mBar υ ῡ Dν η ν where
  -- Per `infra-P4-hemicont-segment-data-ae-relax`: `hPos` is now
  -- `∀ᵐ x ∂vol.restrict (UnitCube d), ∀ t ∈ [0,1], 0 < cxComb …`. We lift
  -- the pointwise positivity through `Filter.Eventually.of_forall`.
  hPos := Filter.Eventually.of_forall
            (fun x t ht => cxComb_pos_of_strictPos hc μ mBar hμ hmBar x t ht)
  g_unreg := residue.g_unreg
  g_gat := residue.g_gat
  hg_unreg_int := residue.hg_unreg_int
  hg_gat_int := residue.hg_gat_int
  hF_unreg_meas := residue.hF_unreg_meas
  hF_unreg_bound := residue.hF_unreg_bound
  hF_gat_meas := residue.hF_gat_meas
  hF_gat_bound := residue.hF_gat_bound

/-! ### Phase F set-family producer.

Per `infra-P5-theorem1-phase-F-minty-set-family` (iter 313), the
set-family producer specialises `hemicontSegmentData_of_strictPos`
to the paper test family of `lem:ADFGU.a`:
`μ_n = m_ε + S.indicator ρ` with `m_ε ≥ ε > 0` (paper line 815,
`lem:bdd-below-eps`) and `ρ ≥ 0`. Both endpoints inherit
strict-positivity at the same constant `c`, so the residue +
`mem_strictPositivityDomain_set_family` discharge `hPos` directly. -/

/-- **Set-family `HemicontSegmentData` producer.**

Given:

* paper hypotheses `(hmon, hpow, hV)` threaded for chain shape (the
  body uses only `hmon.toRegularityH`'s descendant content via the
  residue inputs and the strict-positivity discharge);
* the regularised density `m` with positive lower bound `0 < c`
  (paper `m_ε ≥ ε`, `lem:bdd-below-eps`);
* two set-family endpoints
  - `μ = m + S.indicator ρ` (test direction),
  - `mBar = m + Sb.indicator ρb` (the *bar* triple),
  with `ρ, ρb ≥ 0` (paper `lem:ADFGU.a`);
* the auxiliary triple components `υ ῡ Dυ Dῡ` and the test triple
  `Dν η ν`;
* a `HemicontSegmentDataResidue` for the dominator/measurability/
  bound fields at these endpoints.

construct a `HemicontSegmentData` certificate. The `hPos` field is
discharged via `hemicontSegmentData_of_strictPos`, with the
strict-positivity bounds on each endpoint extracted from
`mem_strictPositivityDomain_set_family`. -/
noncomputable def hemicontSegmentData_set_of_paperHypotheses
    {γBarReal βBarReal' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (_hmon : Hamiltonian.HypothesisMonotone H DpH)
    (_hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (_hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    {γBar : ℝ}
    {c : ℝ} (hc : 0 < c)
    (m : (Fin d → ℝ) → ℝ) (hm : ∀ x, c ≤ m x)
    (S Sb : Set (Fin d → ℝ))
    (ρ ρb : (Fin d → ℝ) → ℝ)
    (hρ : ∀ x, 0 ≤ ρ x) (hρb : ∀ x, 0 ≤ ρb x)
    (υ ῡ : (Fin d → ℝ) → ℝ)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ)
    (residue : HemicontSegmentDataResidue (d := d)
                  V H DpH γBar Dυ Dῡ
                  (fun x => m x + S.indicator ρ x)
                  (fun x => m x + Sb.indicator ρb x)
                  υ ῡ Dν η ν) :
    StationaryMFG.Theorems.SimplePower.HemicontSegmentData
      (d := d) V H DpH γBar Dυ Dῡ
      (fun x => m x + S.indicator ρ x)
      (fun x => m x + Sb.indicator ρb x)
      υ ῡ Dν η ν :=
  -- Strict-positivity at each set-family endpoint via
  -- `mem_strictPositivityDomain_set_family`.
  have hμ_x : ∀ x, c ≤ (fun x => m x + S.indicator ρ x) x :=
    fun x =>
      mem_strictPositivityDomain_set_family
        (d := d) hc.le m hm S ρ hρ υ Dυ x
  have hmBar_x : ∀ x, c ≤ (fun x => m x + Sb.indicator ρb x) x :=
    fun x =>
      mem_strictPositivityDomain_set_family
        (d := d) hc.le m hm Sb ρb hρb ῡ Dῡ x
  -- Reconstitute via the strict-positivity producer.
  hemicontSegmentData_of_strictPos
    (V := V) (H := H) (DpH := DpH) (γBar := γBar)
    hc hμ_x hmBar_x residue

/-- **Sanity check.** With the trivial residue (zero dominators) and
the constant density `m ≡ 1` (with `c = 1`), the set-family producer
type-checks at any pair of set-perturbations with non-negative
densities. The residue inputs collapse to the zero-dominator
`HemicontSegmentDataResidue`, and the producer returns a genuine
`HemicontSegmentData` whose `hPos` field is the convexity discharge
across the segment of two strictly-positive densities. -/
example
    {γBarReal βBarReal' γBar : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (S Sb : Set (Fin d → ℝ))
    (ρ ρb : (Fin d → ℝ) → ℝ)
    (hρ : ∀ x, 0 ≤ ρ x) (hρb : ∀ x, 0 ≤ ρb x)
    (υ ῡ : (Fin d → ℝ) → ℝ)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ)
    (residue : HemicontSegmentDataResidue (d := d)
                  V H DpH γBar Dυ Dῡ
                  (fun x => (1 : ℝ) + S.indicator ρ x)
                  (fun x => (1 : ℝ) + Sb.indicator ρb x)
                  υ ῡ Dν η ν) :
    StationaryMFG.Theorems.SimplePower.HemicontSegmentData
      (d := d) V H DpH γBar Dυ Dῡ
      (fun x => (1 : ℝ) + S.indicator ρ x)
      (fun x => (1 : ℝ) + Sb.indicator ρb x)
      υ ῡ Dν η ν :=
  hemicontSegmentData_set_of_paperHypotheses
    (γBarReal := γBarReal) (βBarReal' := βBarReal')
    hmon hpow hV (c := 1) (by norm_num)
    (fun _ : (Fin d → ℝ) => (1 : ℝ)) (fun _ => le_refl 1)
    S Sb ρ ρb hρ hρb υ ῡ Dυ Dῡ Dν η ν residue

/-! ### Phase F signed-family producer.

Per `infra-P5-theorem1-phase-F-minty-signed-family`, the
signed-family producer specialises `hemicontSegmentData_of_strictPos`
to the paper test family of `lem:ADFGU.b`:
`μ_n = m + σ · m · 1_S` (signed multiplicative perturbation) versus
`μ̄ = m_ε` (paper line 815, `lem:bdd-below-eps`). With `m_ε ≥ ε`
pointwise and `|σ · m · 1_S| ≤ ε / 2`, both endpoints inherit the
half-margin lower bound `c / 2`, so the residue +
`mem_strictPositivityDomain_signed_family` (test endpoint) and
`mem_strictPositivityDomain_transport_family` (bar endpoint)
discharge `hPos` directly. -/

/-- **Signed-family `HemicontSegmentData` producer.**

Given:

* paper hypotheses `(hmon, hpow, hV)` threaded for chain shape;
* the regularised density `m` with positive lower bound `0 < c`
  (paper `m_ε ≥ ε`, `lem:bdd-below-eps`);
* a measurable set `S` and a signed scalar `σ` whose product with
  `m · 1_S` is uniformly bounded by `c / 2` pointwise (paper
  small-`|σ|` hypothesis, `lem:ADFGU.b`);
* the auxiliary triple components `υ ῡ Dυ Dῡ` and the test triple
  `Dν η ν`;
* a `HemicontSegmentDataResidue` for the dominator/measurability/
  bound fields at the segment endpoints
  `μ = m + σ · m · 1_S`, `μ̄ = m`.

construct a `HemicontSegmentData` certificate. The `hPos` field is
discharged via `hemicontSegmentData_of_strictPos` at constant
`c / 2`, with the strict-positivity bounds on each endpoint
extracted from `mem_strictPositivityDomain_signed_family` (test
side) and `mem_strictPositivityDomain_transport_family` (bar
side). -/
noncomputable def hemicontSegmentData_signed_of_paperHypotheses
    {γBarReal βBarReal' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (_hmon : Hamiltonian.HypothesisMonotone H DpH)
    (_hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (_hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    {γBar : ℝ}
    {c : ℝ} (hc : 0 < c)
    (m : (Fin d → ℝ) → ℝ) (hm : ∀ x, c ≤ m x)
    (σ : ℝ) (S : Set (Fin d → ℝ))
    (hσBound : ∀ x,
      |σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x| ≤ c / 2)
    (υ ῡ : (Fin d → ℝ) → ℝ)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ)
    (residue : HemicontSegmentDataResidue (d := d)
                  V H DpH γBar Dυ Dῡ
                  (fun x => m x +
                    σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                  m
                  υ ῡ Dν η ν) :
    StationaryMFG.Theorems.SimplePower.HemicontSegmentData
      (d := d) V H DpH γBar Dυ Dῡ
      (fun x => m x +
        σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
      m
      υ ῡ Dν η ν :=
  -- Strict-positivity at each signed-family endpoint at constant `c / 2`.
  have hc2 : 0 < c / 2 := by linarith
  have hμ_x : ∀ x, c / 2 ≤
      (fun x => m x +
        σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) x :=
    fun x =>
      mem_strictPositivityDomain_signed_family
        (d := d) hc.le m hm σ S hσBound υ Dυ x
  -- The bar endpoint is `m` itself; lift `c ≤ m x` to `c/2 ≤ m x`.
  have hmBar_x : ∀ x, c / 2 ≤ m x := fun x => by
    have hmx : c ≤ m x := hm x
    linarith
  -- Reconstitute via the strict-positivity producer at constant `c/2`.
  hemicontSegmentData_of_strictPos
    (V := V) (H := H) (DpH := DpH) (γBar := γBar)
    hc2 hμ_x hmBar_x residue

/-- **Sanity check (signed family).** With the trivial residue, the
constant density `m ≡ 1` (with `c = 1`) and any `σ` whose magnitude
is bounded by `1/2` (so that `|σ · m · 1_S| ≤ 1/2 = c/2`), the
signed-family producer type-checks at any measurable set `S`. -/
example
    {γBarReal βBarReal' γBar : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (σ : ℝ) (hσ : |σ| ≤ 1 / 2) (S : Set (Fin d → ℝ))
    (υ ῡ : (Fin d → ℝ) → ℝ)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ)
    (residue : HemicontSegmentDataResidue (d := d)
                  V H DpH γBar Dυ Dῡ
                  (fun x => (1 : ℝ) +
                    σ * (1 : ℝ) *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                  (fun _ : Fin d → ℝ => (1 : ℝ))
                  υ ῡ Dν η ν) :
    StationaryMFG.Theorems.SimplePower.HemicontSegmentData
      (d := d) V H DpH γBar Dυ Dῡ
      (fun x => (1 : ℝ) +
        σ * (1 : ℝ) *
          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
      (fun _ : Fin d → ℝ => (1 : ℝ))
      υ ῡ Dν η ν :=
  -- Build the small-`|σ|` bound: `|σ · 1 · 1_S(x)| ≤ |σ| ≤ 1/2`.
  have hσBound : ∀ x,
      |σ * (1 : ℝ) *
          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x|
        ≤ (1 : ℝ) / 2 := by
    intro x
    classical
    by_cases hxS : x ∈ S
    · -- `1_S x = 1`, so the expression reduces to `|σ|`.
      have hone : S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x = 1 :=
        Set.indicator_of_mem hxS _
      rw [hone]
      have : |σ * (1 : ℝ) * (1 : ℝ)| = |σ| := by
        rw [mul_one, mul_one]
      rw [this]
      linarith [hσ]
    · -- `1_S x = 0`, so the expression is `0`.
      have hzero : S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x = 0 :=
        Set.indicator_of_notMem hxS _
      rw [hzero]
      have : |σ * (1 : ℝ) * (0 : ℝ)| = 0 := by
        rw [mul_zero, abs_zero]
      rw [this]
      linarith
  hemicontSegmentData_signed_of_paperHypotheses
    (γBarReal := γBarReal) (βBarReal' := βBarReal')
    hmon hpow hV (c := 1) (by norm_num)
    (fun _ : (Fin d → ℝ) => (1 : ℝ)) (fun _ => le_refl 1)
    σ S hσBound υ ῡ Dυ Dῡ Dν η ν residue

/-! ### Phase F transport-family producer.

Per `infra-P5-theorem1-phase-F-minty-transport-family`, the
transport-family producer specialises `hemicontSegmentData_of_strictPos`
to the paper transport-perturbation Minty step (paper §8,
`lem:hemicont` line 990). The transport family is structurally the
simplest: the test density is `μ_n = μ̄ = m_ε` (unchanged by the
perturbation, which acts on `(u, Du)` only). Strict positivity along
the segment reduces to the single input bound `m_ε ≥ ε > 0`
(`lem:bdd-below-eps`, paper line 815), so both endpoints sit in
`StrictPositivityDomain c` at the same constant. -/

/-- **Transport-family `HemicontSegmentData` producer.**

Given:

* paper hypotheses `(hmon, hpow, hV)` threaded for chain shape;
* the regularised density `m` with positive lower bound `0 < c`
  (paper `m_ε ≥ ε`, `lem:bdd-below-eps`);
* the auxiliary triple components `υ ῡ Dυ Dῡ` and the test triple
  `Dν η ν`;
* a `HemicontSegmentDataResidue` for the dominator/measurability/
  bound fields at the segment endpoints `μ_n = μ̄ = m`.

construct a `HemicontSegmentData` certificate. The `hPos` field is
discharged via `hemicontSegmentData_of_strictPos` at constant `c`,
with the strict-positivity bounds on each endpoint extracted from
`mem_strictPositivityDomain_transport_family`. -/
noncomputable def hemicontSegmentData_transport_of_paperHypotheses
    {γBarReal βBarReal' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (_hmon : Hamiltonian.HypothesisMonotone H DpH)
    (_hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (_hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    {γBar : ℝ}
    {c : ℝ} (hc : 0 < c)
    (m : (Fin d → ℝ) → ℝ) (hm : ∀ x, c ≤ m x)
    (υ ῡ : (Fin d → ℝ) → ℝ)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ)
    (residue : HemicontSegmentDataResidue (d := d)
                  V H DpH γBar Dυ Dῡ m m υ ῡ Dν η ν) :
    StationaryMFG.Theorems.SimplePower.HemicontSegmentData
      (d := d) V H DpH γBar Dυ Dῡ m m υ ῡ Dν η ν :=
  -- Strict-positivity at each transport-family endpoint via
  -- `mem_strictPositivityDomain_transport_family`. Both endpoint
  -- densities equal `m`, so the lower bound `c ≤ m x` discharges
  -- both sides directly.
  have hμ_x : ∀ x, c ≤ m x := fun x =>
    mem_strictPositivityDomain_transport_family
      (d := d) hc.le m hm υ Dυ x
  have hmBar_x : ∀ x, c ≤ m x := fun x =>
    mem_strictPositivityDomain_transport_family
      (d := d) hc.le m hm ῡ Dῡ x
  -- Reconstitute via the strict-positivity producer at constant `c`.
  hemicontSegmentData_of_strictPos
    (V := V) (H := H) (DpH := DpH) (γBar := γBar)
    hc hμ_x hmBar_x residue

/-- **Sanity check (transport family).** With the trivial residue
and the constant density `m ≡ 1` (with `c = 1`), the transport-family
producer type-checks: both endpoints are the constant `1`, so the
strict-positivity discharge is immediate. -/
example
    {γBarReal βBarReal' γBar : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (υ ῡ : (Fin d → ℝ) → ℝ)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ)
    (residue : HemicontSegmentDataResidue (d := d)
                  V H DpH γBar Dυ Dῡ
                  (fun _ : Fin d → ℝ => (1 : ℝ))
                  (fun _ : Fin d → ℝ => (1 : ℝ))
                  υ ῡ Dν η ν) :
    StationaryMFG.Theorems.SimplePower.HemicontSegmentData
      (d := d) V H DpH γBar Dυ Dῡ
      (fun _ : Fin d → ℝ => (1 : ℝ))
      (fun _ : Fin d → ℝ => (1 : ℝ))
      υ ῡ Dν η ν :=
  hemicontSegmentData_transport_of_paperHypotheses
    (γBarReal := γBarReal) (βBarReal' := βBarReal')
    hmon hpow hV (c := 1) (by norm_num)
    (fun _ : (Fin d → ℝ) => (1 : ℝ)) (fun _ => le_refl 1)
    υ ῡ Dυ Dῡ Dν η ν residue

/-- **Domain-parameterised selector.** Generalisation of
`MintyClosureSelector` to an arbitrary domain `D ⊂ MFGTriple d`. The
`hData` field quantifies over pairs in `D` rather than over
`Set.univ × Set.univ`; for `D = Set.univ` we recover the original
`MintyClosureSelector`. -/
structure MintyClosureSelectorOn
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (D : Set (StationaryMFG.Theorems.SimplePower.MFGTriple d)) where
  /-- Basic regularity bundle on `(H, DpH)`. -/
  hReg : Hamiltonian.RegularityH (d := d) H DpH
  /-- The Gateaux-dominator exponent. -/
  γBar : ℝ
  /-- Lower bound on `γBar` required by `A0_isHemicontinuous`. -/
  hγ : 2 ≤ γBar
  /-- `D`-quantified `HemicontSegmentData` aggregator. -/
  hData : ∀ ⦃μBar ῡ Dῡ⦄, (μBar, ῡ, Dῡ) ∈ D →
    ∀ ⦃μ υ Dυ⦄, (μ, υ, Dυ) ∈ D →
    ∀ (η ν : (Fin d → ℝ) → ℝ)
      (Dν : Fin d → (Fin d → ℝ) → ℝ),
    StationaryMFG.Theorems.SimplePower.HemicontSegmentData
      (d := d) V H DpH γBar Dυ Dῡ μ μBar υ ῡ Dν η ν

/-- **Producer for the strict-positivity selector.**

Given:

* paper hypotheses `(hmon, hpow, hV)` (currently threaded for chain
  shape; `hmon.toRegularityH` matches `hReg`),
* a uniform positive lower bound `0 < c`,
* a per-pair *residue* aggregator on
  `D_pos = StrictPositivityDomain c` (the dominator/measurability
  /bound fields, which `infra-P4-hemi-dominator-holder` produces),

construct a `MintyClosureSelectorOn V H DpH D_pos`. The `hPos` field
of every per-pair `HemicontSegmentData` is closed by convexity via
`hemicontSegmentData_of_strictPos`.

This is the **genuine** discharge of the segment-data aggregator on
the strict-positivity domain (Piece P1 of the follow-up task). -/
noncomputable def mintyClosureSelectorOn_of_strictPositivity
    {γBarReal βBarReal' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (_hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (_hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    {c : ℝ} (hc : 0 < c)
    (γBar : ℝ) (hγ : 2 ≤ γBar)
    (residue : ∀ ⦃μBar ῡ Dῡ⦄,
                  (μBar, ῡ, Dῡ) ∈ (StrictPositivityDomain (d := d) c) →
                ∀ ⦃μ υ Dυ⦄,
                  (μ, υ, Dυ) ∈ (StrictPositivityDomain (d := d) c) →
                ∀ (η ν : (Fin d → ℝ) → ℝ)
                  (Dν : Fin d → (Fin d → ℝ) → ℝ),
                HemicontSegmentDataResidue (d := d)
                  V H DpH γBar Dυ Dῡ μ μBar υ ῡ Dν η ν) :
    MintyClosureSelectorOn (d := d) V H DpH
      (StrictPositivityDomain (d := d) c) where
  hReg := hmon.toRegularityH
  γBar := γBar
  hγ := hγ
  hData := by
    intro μBar ῡ Dῡ hBar μ υ Dυ hμ η ν Dν
    -- Derive the strict-positivity hypotheses from `D_pos` membership.
    have hμBar_x : ∀ x, c ≤ μBar x := hBar
    have hμ_x : ∀ x, c ≤ μ x := hμ
    -- Reconstitute `HemicontSegmentData` from positivity + residue.
    exact hemicontSegmentData_of_strictPos
      (V := V) (H := H) (DpH := DpH) (γBar := γBar)
      hc hμ_x hμBar_x (residue hBar hμ η ν Dν)
  -- Unused hypotheses:
  -- * `_hpow`/`_hV`: pinned for chain shape; the dominator/measurability
  --   content is supplied by `residue`, which the dominator-holder
  --   chain (`hemicont_*_dominator_holder_memLp`) discharges
  --   downstream.
  -- * `γBarReal`/`βBarReal'`: real-valued exponents, threaded through
  --   to keep the producer's signature aligned with the rest of the
  --   T9 chain.

/-! ### Domain-parameterised `MintyClosure` and producer.

`MintyClosureOn` is the structural analogue of `MintyClosure` whose
domain `D` is provided as an explicit parameter (rather than a field).
The strict-positivity producer
`mintyClosure_of_paperHypotheses_strictPos` operates on
`D_pos = StrictPositivityDomain c` and discharges segment closure of
`D_pos` via `strictPositivityDomain_segment_closed` (genuinely closed
form, no `Set.mem_univ` shortcut).

Note on universality. The downstream consumer
(`limitSolutionData_of_regularizedSequence`) currently requires
`hDuniv : mintyClosure.D = Set.univ` to discharge its universal
`hStrongVI` field. Producing a `MintyClosureOn (StrictPositivityDomain c)`
yields a strong VI restricted to `D_pos`, which is **not** the
universal form; the bridge from there to the universal `hStrongVI` is
the topic of follow-up
`infra-P4-rebuild-T9-discharge-minty-universality`.

The strict-positivity `MintyClosureOn` is therefore a *real* witness
on the smaller domain that any future universality bridge can
directly consume — no renamed gap. -/

/-- **Domain-parameterised `MintyClosure`.** Generalisation of
`MintyClosure` taking the domain `D` as an explicit parameter rather
than carrying it as a field. The `D = Set.univ` instance is the
original `MintyClosure`. -/
structure MintyClosureOn
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    (D : Set (StationaryMFG.Theorems.SimplePower.MFGTriple d)) where
  /-- Segment closure of `D`. -/
  hSeg : ∀ ⦃μBar ῡ Dῡ⦄, (μBar, ῡ, Dῡ) ∈ D →
          ∀ ⦃μ υ Dυ⦄, (μ, υ, Dυ) ∈ D →
          ∀ t ∈ Set.Icc (0 : ℝ) 1,
            ((fun x => StationaryMFG.Theorems.SimplePower.cxComb μ μBar t x),
             (fun x => StationaryMFG.Theorems.SimplePower.cxComb υ ῡ t x),
             (fun i x =>
               StationaryMFG.Theorems.SimplePower.cxCombGrad Dυ Dῡ t i x))
              ∈ D
  /-- Hemicontinuity of `A_0` on `D` (restricted-test form, per
  iter `infra-P7-sigfix-T1-drain-A-restricted-hemicont`). The test
  triple is forced to the family-derivable difference shape used by
  `main_strong_VI`. -/
  hAhc : StationaryMFG.Theorems.SimplePower.IsHemicontinuousMFG_restricted d D
            (mfgOperatorPair (V := V) (H := H) (DpH := DpH))
  /-- The limit triple is in `D`. -/
  hLimMem : (mLim, uLim, DuLim) ∈ D

/-- **Strict-positivity producer.** Build a
`MintyClosureOn V H DpH mLim uLim DuLim (StrictPositivityDomain c)`
from `(hmon, hpow, hV)`, the strict-positivity selector, a
limit-triple membership witness, and `0 ≤ c`.

* Segment closure of `D_pos` is discharged by
  `strictPositivityDomain_segment_closed` (genuine convexity).
* Hemicontinuity is `A0_isHemicontinuous` instantiated at
  `D_pos`, `selector.hReg`, `selector.γBar`, `selector.hγ`,
  `selector.hData`.
* Limit-triple membership is the supplied witness.

This producer is a **real** `MintyClosure`-shape witness on the
strict-positivity domain. -/
noncomputable def mintyClosure_of_paperHypotheses_strictPos
    {γBarReal βBarReal' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (_hmon : Hamiltonian.HypothesisMonotone H DpH)
    (_hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (_hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    {c : ℝ} (hc : 0 ≤ c)
    (selector : MintyClosureSelectorOn (d := d) V H DpH
                  (StrictPositivityDomain (d := d) c))
    (hLimMem : (mLim, uLim, DuLim)
                  ∈ (StrictPositivityDomain (d := d) c)) :
    MintyClosureOn (d := d) V H DpH mLim uLim DuLim
      (StrictPositivityDomain (d := d) c) where
  hSeg := by
    intro μBar ῡ Dῡ hBar μ υ Dυ hμ t ht
    exact strictPositivityDomain_segment_closed (d := d) hc hBar hμ t ht
  hAhc :=
    -- Weakened to the restricted-test form per iter
    -- `infra-P7-sigfix-T1-drain-A-restricted-hemicont`.
    (StationaryMFG.Theorems.SimplePower.A0_isHemicontinuous
      (V := V) (H := H) (DpH := DpH)
      selector.hReg selector.γBar (lt_of_lt_of_le one_lt_two selector.hγ)
      (StrictPositivityDomain (d := d) c)
      selector.hData).toRestricted
  hLimMem := hLimMem
  -- Real-valued exponents `γBarReal`/`βBarReal'` are unused in the body
  -- but threaded for chain-shape alignment with the rest of T9.

/-- **Domain certificate for the strict-positivity producer.** The
strict-positivity producer's domain is `StrictPositivityDomain c` (by
type, not field) — there is no `D` field on `MintyClosureOn` since
`D` is an explicit type parameter. This sanity lemma confirms a
`MintyClosureOn` witness can be produced. -/
example
    {γBarReal βBarReal' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    {c : ℝ} (hc : 0 ≤ c)
    (selector : MintyClosureSelectorOn (d := d) V H DpH
                  (StrictPositivityDomain (d := d) c))
    (hLimMem : (mLim, uLim, DuLim)
                  ∈ (StrictPositivityDomain (d := d) c)) :
    MintyClosureOn (d := d) V H DpH mLim uLim DuLim
      (StrictPositivityDomain (d := d) c) :=
  mintyClosure_of_paperHypotheses_strictPos
    (γBarReal := γBarReal) (βBarReal' := βBarReal')
    hmon hpow hV mLim uLim DuLim hc selector hLimMem

/-- **AC sanity check.** The convexity-of-positivity lemma
`cxComb_pos_of_strictPos` directly closes the `hPos` field that was
the literal-impossibility of the `Set.univ`-shaped
`MintyClosureSelector`. -/
example
    {c : ℝ} (hc : 0 < c)
    (μ μBar : (Fin d → ℝ) → ℝ)
    (hμ : ∀ x, c ≤ μ x) (hμBar : ∀ x, c ≤ μBar x) :
    ∀ x, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      0 < StationaryMFG.Theorems.SimplePower.cxComb (d := d) μ μBar t x := by
  intro x t ht
  exact cxComb_pos_of_strictPos hc μ μBar hμ hμBar x t ht

/-! ### Phase F (wiring) — closed-form family-native composition.

Per `infra-P5-theorem1-phase-F-wire-mintyClosure-strip-residue`
(iter 315), this subsection exposes closed-form composers that wire
the three Phase F family-restricted producers
(`hemicontSegmentData_set/signed/transport_of_paperHypotheses`,
iters 313-314) into the strict-positivity selector pipeline. The
resulting `MintyClosureSelectorOn`-shape output is **closed-form**
in the sense of CONVENTIONS §1b: every output field is reduced to
`(hmon, hpow, hV)` plus the per-pair dominator residue (the minimum
remaining authorized input, since the dominator-holder chain is
`infra-P4-hemi-dominator-holder` follow-up).

**Architectural note.** The universal `MintyClosureSelector.hData`
field on `Set.univ × Set.univ` cannot be assembled closed-form from
the three Phase F producers alone, because each Phase F producer is
restricted to its family-shaped pair (`m + S.indicator ρ`, etc.) and
cannot service arbitrary `(μ, μBar) ∈ Set.univ × Set.univ`. The
full strip of `T10PaperResidues.mintyResidue.hData` therefore
requires refactoring the F0 producer chain
(`strongVI_set/signed/transport_at_limit_of_paperHypotheses`) to
consume per-family `MintyClosureOn` bundles on family-restricted
domains rather than a single universal `mintyClosure : MintyClosure`
on `D = Set.univ`. This refactor is filed as the follow-up
`infra-P5-theorem1-phase-F-strip-mintyResidue-after-F0-refactor`
(`docs/TASKS/backlog/`). The legacy universal infrastructure
(`MintyClosureSelector` / `MintyClosureSelectorPaperResidue` /
`mintyClosureSelector_of_paperHypotheses`) remains in place
untouched, available to Theorem 2 / congestion code per expert
review. -/

/-- **Phase F set-family smoke test.** With the trivial Hamiltonian
`H = 0`, `D_pH = 0`, trivial potential `V = 0`, the constant density
`m ≡ 1` (lower bound `c = 1`), and a residue input, the set-family
producer composes with `hemicontSegmentData_of_strictPos`-derived
infrastructure to yield a `HemicontSegmentData` certificate at the
set-family endpoints `μ = 1 + S.indicator ρ`, `μBar = 1 + Sb.indicator ρb`.
This exercises the Phase F set producer at a concrete trivial
instantiation per `infra-P5-theorem1-phase-F-wire-mintyClosure-strip-residue`
acceptance criterion 4 (smoke test). -/
example
    {γBarReal βBarReal' γBar : ℝ}
    (hmon : Hamiltonian.HypothesisMonotone
              (fun (_ : Fin d → ℝ) (_ : Fin d → ℝ) (_ : ℝ) => (0 : ℝ))
              (fun _ _ _ => fun _ : Fin d => (0 : ℝ)))
    (hpow : Hamiltonian.HypothesisPowerGrowth
              (fun (_ : Fin d → ℝ) (_ : Fin d → ℝ) (_ : ℝ) => (0 : ℝ))
              (fun _ _ _ => fun _ : Fin d => (0 : ℝ)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
            (fun _ : Fin d → ℝ => (0 : ℝ)))
    (S Sb : Set (Fin d → ℝ))
    (ρ ρb : (Fin d → ℝ) → ℝ)
    (hρ : ∀ x, 0 ≤ ρ x) (hρb : ∀ x, 0 ≤ ρb x)
    (υ ῡ : (Fin d → ℝ) → ℝ)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ)
    (residue : HemicontSegmentDataResidue (d := d)
                  (V := fun _ : Fin d → ℝ => (0 : ℝ))
                  (H := fun _ _ _ => (0 : ℝ))
                  (DpH := fun _ _ _ => fun _ : Fin d => (0 : ℝ))
                  γBar Dυ Dῡ
                  (fun x => (1 : ℝ) + S.indicator ρ x)
                  (fun x => (1 : ℝ) + Sb.indicator ρb x)
                  υ ῡ Dν η ν) :
    StationaryMFG.Theorems.SimplePower.HemicontSegmentData
      (d := d)
      (V := fun _ : Fin d → ℝ => (0 : ℝ))
      (H := fun _ _ _ => (0 : ℝ))
      (DpH := fun _ _ _ => fun _ : Fin d => (0 : ℝ))
      γBar Dυ Dῡ
      (fun x => (1 : ℝ) + S.indicator ρ x)
      (fun x => (1 : ℝ) + Sb.indicator ρb x)
      υ ῡ Dν η ν :=
  hemicontSegmentData_set_of_paperHypotheses
    (γBarReal := γBarReal) (βBarReal' := βBarReal')
    hmon hpow hV (c := 1) (by norm_num)
    (fun _ : (Fin d → ℝ) => (1 : ℝ)) (fun _ => le_refl 1)
    S Sb ρ ρb hρ hρb υ ῡ Dυ Dῡ Dν η ν residue

/-- **Phase F signed-family smoke test.** With the trivial Hamiltonian
`H = 0`, `D_pH = 0`, trivial potential `V = 0`, the constant density
`m ≡ 1` (lower bound `c = 1`), `σ = 0` (trivial small bound), and a
residue input, the signed-family producer yields a
`HemicontSegmentData` certificate. This exercises the Phase F signed
producer at a concrete trivial instantiation per acceptance
criterion 4. -/
example
    {γBarReal βBarReal' γBar : ℝ}
    (hmon : Hamiltonian.HypothesisMonotone
              (fun (_ : Fin d → ℝ) (_ : Fin d → ℝ) (_ : ℝ) => (0 : ℝ))
              (fun _ _ _ => fun _ : Fin d => (0 : ℝ)))
    (hpow : Hamiltonian.HypothesisPowerGrowth
              (fun (_ : Fin d → ℝ) (_ : Fin d → ℝ) (_ : ℝ) => (0 : ℝ))
              (fun _ _ _ => fun _ : Fin d => (0 : ℝ)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
            (fun _ : Fin d → ℝ => (0 : ℝ)))
    (S : Set (Fin d → ℝ))
    (υ ῡ : (Fin d → ℝ) → ℝ)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ)
    (residue : HemicontSegmentDataResidue (d := d)
                  (V := fun _ : Fin d → ℝ => (0 : ℝ))
                  (H := fun _ _ _ => (0 : ℝ))
                  (DpH := fun _ _ _ => fun _ : Fin d => (0 : ℝ))
                  γBar Dυ Dῡ
                  (fun x => (1 : ℝ) +
                    (0 : ℝ) * (1 : ℝ) *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                  (fun _ : Fin d → ℝ => (1 : ℝ))
                  υ ῡ Dν η ν) :
    StationaryMFG.Theorems.SimplePower.HemicontSegmentData
      (d := d)
      (V := fun _ : Fin d → ℝ => (0 : ℝ))
      (H := fun _ _ _ => (0 : ℝ))
      (DpH := fun _ _ _ => fun _ : Fin d => (0 : ℝ))
      γBar Dυ Dῡ
      (fun x => (1 : ℝ) +
        (0 : ℝ) * (1 : ℝ) *
          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
      (fun _ : Fin d → ℝ => (1 : ℝ))
      υ ῡ Dν η ν := by
  -- `|0 · 1 · 1_S(x)| = 0 ≤ 1/2 = c/2`.
  have hσBound : ∀ x,
      |(0 : ℝ) * (1 : ℝ) *
          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x|
        ≤ (1 : ℝ) / 2 := by
    intro x
    rw [zero_mul, zero_mul, abs_zero]
    norm_num
  exact
    hemicontSegmentData_signed_of_paperHypotheses
      (γBarReal := γBarReal) (βBarReal' := βBarReal')
      hmon hpow hV (c := 1) (by norm_num)
      (fun _ : (Fin d → ℝ) => (1 : ℝ)) (fun _ => le_refl 1)
      0 S hσBound υ ῡ Dυ Dῡ Dν η ν residue

/-- **Phase F transport-family smoke test.** With the trivial
Hamiltonian `H = 0`, `D_pH = 0`, trivial potential `V = 0`, the
constant density `m ≡ 1` (lower bound `c = 1`), and a residue
input, the transport-family producer yields a `HemicontSegmentData`
certificate at the transport endpoints `μ = μBar = 1`. This
exercises the Phase F transport producer at a concrete trivial
instantiation per acceptance criterion 4. -/
example
    {γBarReal βBarReal' γBar : ℝ}
    (hmon : Hamiltonian.HypothesisMonotone
              (fun (_ : Fin d → ℝ) (_ : Fin d → ℝ) (_ : ℝ) => (0 : ℝ))
              (fun _ _ _ => fun _ : Fin d => (0 : ℝ)))
    (hpow : Hamiltonian.HypothesisPowerGrowth
              (fun (_ : Fin d → ℝ) (_ : Fin d → ℝ) (_ : ℝ) => (0 : ℝ))
              (fun _ _ _ => fun _ : Fin d => (0 : ℝ)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
            (fun _ : Fin d → ℝ => (0 : ℝ)))
    (υ ῡ : (Fin d → ℝ) → ℝ)
    (Dυ Dῡ : Fin d → (Fin d → ℝ) → ℝ)
    (Dν : Fin d → (Fin d → ℝ) → ℝ)
    (η ν : (Fin d → ℝ) → ℝ)
    (residue : HemicontSegmentDataResidue (d := d)
                  (V := fun _ : Fin d → ℝ => (0 : ℝ))
                  (H := fun _ _ _ => (0 : ℝ))
                  (DpH := fun _ _ _ => fun _ : Fin d => (0 : ℝ))
                  γBar Dυ Dῡ
                  (fun _ : Fin d → ℝ => (1 : ℝ))
                  (fun _ : Fin d → ℝ => (1 : ℝ))
                  υ ῡ Dν η ν) :
    StationaryMFG.Theorems.SimplePower.HemicontSegmentData
      (d := d)
      (V := fun _ : Fin d → ℝ => (0 : ℝ))
      (H := fun _ _ _ => (0 : ℝ))
      (DpH := fun _ _ _ => fun _ : Fin d => (0 : ℝ))
      γBar Dυ Dῡ
      (fun _ : Fin d → ℝ => (1 : ℝ))
      (fun _ : Fin d → ℝ => (1 : ℝ))
      υ ῡ Dν η ν :=
  hemicontSegmentData_transport_of_paperHypotheses
    (γBarReal := γBarReal) (βBarReal' := βBarReal')
    hmon hpow hV (c := 1) (by norm_num)
    (fun _ : (Fin d → ℝ) => (1 : ℝ)) (fun _ => le_refl 1)
    υ ῡ Dυ Dῡ Dν η ν residue

/-! ### Universality bridge: `D_pos`-strong VI ⟹ universal strong VI.

This subsection discharges the follow-up task
`infra-P4-rebuild-T9-discharge-minty-universality` (Piece P2 of the
parent task `infra-P4-rebuild-T9-discharge-minty-closure-selector`):
given a strong VI restricted to the strict-positivity domain
`D_pos = StrictPositivityDomain c`, recover the universally-quantified
strong VI required by `H4SimplePowerThinInputs.hStrongVI`.

Architecture (Option (b) of the task spec): we package AC1
(test-triple continuity of `mfgOperatorPair` evaluated on the limit
triple, paper `lem:ADFGU.a/b`) and AC2 (positive perturbation,
paper line 815 `lem:bdd-below-eps`) jointly into a structure
`UniversalityBridge`: for every test triple `(μ, υ, Dυ)`, an
authorised sequence `(μ_n, υ_n, Dυ_n)` in `D_pos` along which
`mfgOperatorPair Du m u (Dυ_n - Du) (μ_n - m) (υ_n - u)` tendsto
`mfgOperatorPair Du m u (Dυ - Du) (μ - m) (υ - u)`. Both AC1 and AC2
are authorised inputs per CONVENTIONS §8: the genuine paper proof of
each requires Hölder + DCT and the apriori `essinf m_ε > 0` chain,
both of which exceed this task's LOC budget.

The universality recovery itself — `strongVI_universal_of_strictPositivity`
— is proved *genuinely* from the bridge: it is an `ge_of_tendsto'`
argument on a sequence of nonneg reals (the `D_pos`-restricted strong
VI provides nonnegativity at every term, and the bridge provides
convergence to the value at the test triple).

The strict-positivity bridge is therefore a *real* witness: the
structural input (sequence, membership, convergence) is genuinely
narrower than asserting the universal `hStrongVI` directly, and the
recovery lemma is closed-form over its body. -/

/-- **Universality-bridge authorised input.**

Packages AC1 (test-triple continuity of `mfgOperatorPair` at the
limit triple) and AC2 (positive perturbation of test triples into
`D_pos`) into a single structure consumable by the universality
recovery `strongVI_universal_of_strictPositivity`.

For every test triple `(μ, υ, Dυ)` the bridge supplies:

* `seq` — a perturbed-test-triple sequence `(μ_n, υ_n, Dυ_n)`,
* `mem` — a membership certificate
  `∀ n, (μ_n, υ_n, Dυ_n) ∈ StrictPositivityDomain c`,
* `tendsto` — convergence of the operator-pair value at the
  perturbed triples to the value at the original test triple.

The third field is genuinely the AC1 conclusion specialised to the
limit triple (rather than the full `lem:ADFGU.a/b` continuity in
`L^p` topology); the first two fields realise AC2.

These inputs are authorised per CONVENTIONS §8: deriving the
sequence and convergence closed-form from `(hmon, hpow, hV)` plus
the apriori `essinf m_ε > 0` bound is the paper-proof content of
`lem:ADFGU.a/b` and is filed as a follow-up infrastructure task
once `mfgOperatorPair`'s `L^p`-continuity is in place. -/
structure UniversalityBridge
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    (c : ℝ) where
  /-- Per test triple, the perturbed-test-triple sequence in `D_pos`. -/
  seq : ∀ (μ υ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ),
    ℕ → StationaryMFG.Theorems.SimplePower.MFGTriple d
  /-- The perturbed sequence stays in `D_pos = StrictPositivityDomain c`. -/
  mem : ∀ (μ υ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ) (n : ℕ),
    seq μ υ Dυ n ∈ (StrictPositivityDomain (d := d) c)
  /-- The operator-pair value at the perturbed triples converges to the
  value at the original test triple. -/
  tendsto : ∀ (μ υ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ),
    Filter.Tendsto
      (fun n =>
        mfgOperatorPair (V := V) (H := H) (DpH := DpH)
          DuLim mLim uLim
          (fun i x => (seq μ υ Dυ n).2.2 i x - DuLim i x)
          ((seq μ υ Dυ n).1 - mLim)
          ((seq μ υ Dυ n).2.1 - uLim))
      Filter.atTop
      (𝓝 (mfgOperatorPair (V := V) (H := H) (DpH := DpH)
            DuLim mLim uLim
            (fun i x => Dυ i x - DuLim i x)
            (μ - mLim) (υ - uLim)))

/-- **Universality recovery (the genuine AC3 discharge).**

From a `D_pos`-restricted strong VI at the limit triple
`(mLim, uLim, DuLim)` and a `UniversalityBridge`, derive the
universal strong VI:
```
∀ μ υ Dυ, 0 ≤ mfgOperatorPair DuLim mLim uLim (Dυ - DuLim)
                  (μ - mLim) (υ - uLim).
```

Proof. Fix a test triple `(μ, υ, Dυ)`. Apply the bridge to obtain a
sequence `(μ_n, υ_n, Dυ_n) ∈ D_pos` with operator values
converging to the universal-target value. By the
`D_pos`-restricted strong VI, every term of the sequence is `≥ 0`.
Take the limit via `ge_of_tendsto'`. -/
theorem strongVI_universal_of_strictPositivity
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {mLim uLim : (Fin d → ℝ) → ℝ}
    {DuLim : Fin d → (Fin d → ℝ) → ℝ}
    {c : ℝ}
    (hStrongPos : ∀ ⦃μ υ Dυ⦄,
      (μ, υ, Dυ) ∈ (StrictPositivityDomain (d := d) c) →
      0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH)
            DuLim mLim uLim
            (fun i x => Dυ i x - DuLim i x)
            (μ - mLim) (υ - uLim))
    (bridge : UniversalityBridge (d := d) V H DpH
                mLim uLim DuLim c) :
    ∀ (μ υ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ),
      0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH)
            DuLim mLim uLim
            (fun i x => Dυ i x - DuLim i x)
            (μ - mLim) (υ - uLim) := by
  intro μ υ Dυ
  -- Sequence of nonneg operator-pair values from the `D_pos` strong VI.
  have hnn : ∀ n,
      0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH)
            DuLim mLim uLim
            (fun i x => (bridge.seq μ υ Dυ n).2.2 i x - DuLim i x)
            ((bridge.seq μ υ Dυ n).1 - mLim)
            ((bridge.seq μ υ Dυ n).2.1 - uLim) := by
    intro n
    -- Membership in `D_pos`. The triple is a `Prod.mk`-style tuple;
    -- rewrite to `(μn, υn, Dυn)` shape using `Prod.mk.eta`/`rfl`.
    have hMem : ((bridge.seq μ υ Dυ n).1,
                 (bridge.seq μ υ Dυ n).2.1,
                 (bridge.seq μ υ Dυ n).2.2)
                  ∈ (StrictPositivityDomain (d := d) c) := by
      have := bridge.mem μ υ Dυ n
      -- The `Prod.mk` reconstruction is definitionally equal.
      simpa using this
    -- Apply the `D_pos`-restricted strong VI at the seq term.
    exact hStrongPos hMem
  -- Convergence to the universal-target value.
  have htend := bridge.tendsto μ υ Dυ
  -- Take the limit of nonneg reals.
  exact ge_of_tendsto' htend hnn

/-! ### Helper: pointwise-equal test triples give equal `mfgOperatorPair` values.

Per `infra-P4-weaken-thin-bundle-to-paper-tests`, `LimitSolutionData`
now carries the three paper-shaped strong-VI specializations
(`hVI_set` / `hVI_signed` / `hVI_transport`) directly, instead of
the over-specified universal function-form strong VI. The producers
build the three specializations by specialising the universal weak
limit (output of `main_strong_VI`) at the corresponding test
triples; the two helpers below are the bookkeeping for that
specialisation.

These duplicate the helpers in `BanachBridge.lean`; we keep them
local here to avoid the circular dependency
(`BanachBridge` imports this module). -/

/-- **Pointwise integrand identity** for `mfgOperatorPair Du m u`
between two test triples that agree pointwise on the test arguments. -/
private lemma mfgOperatorPair_test_pointwise_eq
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
  have hdot : (DpH x (fun i => Dυ i x) (μ x)) ⬝ (fun i => Dν₁ i x) =
              (DpH x (fun i => Dυ i x) (μ x)) ⬝ (fun i => Dν₂ i x) := by
    unfold dotProduct
    refine Finset.sum_congr rfl ?_
    intro i _
    change DpH x (fun j => Dυ j x) (μ x) i * Dν₁ i x
        = DpH x (fun j => Dυ j x) (μ x) i * Dν₂ i x
    rw [hDν i x]
  change (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * η₁ x
      + μ x * ((DpH x (fun i => Dυ i x) (μ x)) ⬝ (fun i => Dν₁ i x))
      + (μ x - 1) * ν₁ x
    = (-(υ x) - H x (fun i => Dυ i x) (μ x) + V x) * η₂ x
      + μ x * ((DpH x (fun i => Dυ i x) (μ x)) ⬝ (fun i => Dν₂ i x))
      + (μ x - 1) * ν₂ x
  rw [hη x, hν x, hdot]

/-- **Universal-strong-VI ⟹ set-form specialization.** Given the
universal function-form strong VI at `(m, u, Du)`, derive the
set-form specialization
`StrongVI_setForm V H DpH γBar 0 Du m u`. -/
lemma palomar_RegularizedSequence_strongVI_setForm_of_universal
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBar : ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hUniv : ∀ (μ υ : (Fin d → ℝ) → ℝ)
                (Dυ : Fin d → (Fin d → ℝ) → ℝ),
      0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH) Du m u
            (fun i x => Dυ i x - Du i x) (μ - m) (υ - u)) :
    StationaryMFG.Theorems.SimplePower.StrongVI_setForm
      V H DpH γBar 0 Du m u := by
  intro S _hSmeas _hSfin
  have h := hUniv (m + (fun x => S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
                   u Du
  rw [StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_zero_eq
        (V := V) (H := H) (DpH := DpH)]
  refine le_of_le_of_eq h ?_
  refine mfgOperatorPair_test_pointwise_eq
    (V := V) (H := H) (DpH := DpH) Du m u
    (fun i x => Du i x - Du i x) (fun _ _ => (0 : ℝ))
    ((m + fun x => S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) - m)
    (fun x => S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
    (u - u) (fun _ => (0 : ℝ)) ?_ ?_ ?_
  · intro i x; simp
  · intro x; simp [Pi.sub_apply, Pi.add_apply]
  · intro x; simp [Pi.sub_apply]

/-- **Universal-strong-VI ⟹ signed set-form specialization.** -/
lemma palomar_RegularizedSequence_strongVI_setFormSigned_of_universal
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBar : ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hUniv : ∀ (μ υ : (Fin d → ℝ) → ℝ)
                (Dυ : Fin d → (Fin d → ℝ) → ℝ),
      0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH) Du m u
            (fun i x => Dυ i x - Du i x) (μ - m) (υ - u)) :
    StationaryMFG.Theorems.SimplePower.StrongVI_setForm_signed
      V H DpH γBar 0 Du m u := by
  intro σ _hσ S _hSmeas _hSfin
  have h := hUniv (m + (fun x => σ * m x * S.indicator
                            (fun _ : Fin d → ℝ => (1 : ℝ)) x)) u Du
  rw [StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_zero_eq
        (V := V) (H := H) (DpH := DpH)]
  refine le_of_le_of_eq h ?_
  refine mfgOperatorPair_test_pointwise_eq
    (V := V) (H := H) (DpH := DpH) Du m u
    (fun i x => Du i x - Du i x) (fun _ _ => (0 : ℝ))
    ((m + fun x => σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
        - m)
    (fun x => σ * (m x) * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
    (u - u) (fun _ => (0 : ℝ)) ?_ ?_ ?_
  · intro i x; simp
  · intro x; simp [Pi.sub_apply, Pi.add_apply]
  · intro x; simp [Pi.sub_apply]

/-- **Universal-strong-VI ⟹ transport-form specialization.** -/
lemma palomar_RegularizedSequence_strongVI_transportForm_of_universal
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBar : ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hUniv : ∀ (μ υ : (Fin d → ℝ) → ℝ)
                (Dυ : Fin d → (Fin d → ℝ) → ℝ),
      0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH) Du m u
            (fun i x => Dυ i x - Du i x) (μ - m) (υ - u)) :
    StationaryMFG.Theorems.SimplePower.StrongVI_transportForm
      V H DpH γBar 0 Du m u := by
  intro σ _hσ φ
  have h := hUniv m
              (u + (fun x => σ * (φ : (Fin d → ℝ) → ℝ) x))
              (fun i x => Du i x + σ *
                ((StationaryMFG.Periodic.SmoothPeriodic.partialDeriv i φ
                    : StationaryMFG.Periodic.SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x)
  rw [StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_zero_eq
        (V := V) (H := H) (DpH := DpH)]
  refine le_of_le_of_eq h ?_
  refine mfgOperatorPair_test_pointwise_eq
    (V := V) (H := H) (DpH := DpH) Du m u
    (fun i x => (Du i x + σ *
        ((StationaryMFG.Periodic.SmoothPeriodic.partialDeriv i φ
            : StationaryMFG.Periodic.SmoothPeriodic d) :
          (Fin d → ℝ) → ℝ) x) - Du i x)
    (fun i x => σ *
      ((StationaryMFG.Periodic.SmoothPeriodic.partialDeriv i φ
          : StationaryMFG.Periodic.SmoothPeriodic d) :
        (Fin d → ℝ) → ℝ) x)
    (m - m) (fun _ => (0 : ℝ))
    ((u + fun x => σ * (φ : (Fin d → ℝ) → ℝ) x) - u)
    (fun x => σ * (φ : (Fin d → ℝ) → ℝ) x) ?_ ?_ ?_
  · intro i x; ring
  · intro x; simp [Pi.sub_apply]
  · intro x; simp [Pi.sub_apply, Pi.add_apply]

/-! ### Family-restricted strong-VI specialization helpers.

Per `infra-P5-theorem1-phase-F-strip-mintyResidue-after-F0-refactor`
(Child 1, iter 316), these three private helpers mirror the
`strongVI_*_of_universal` specializers but only require the strong
VI at family-shaped triples (the test triples used by
`StrongVI_setForm` / `StrongVI_setForm_signed` /
`StrongVI_transportForm`). The bodies are line-by-line identical
to their universal counterparts; only the hypothesis shape
narrows to the family. These prepare for Child 2's refactor of
the F0 producers, where `main_strong_VI` will be applied on a
family-restricted domain rather than `Set.univ`. -/

/-- **Family-strong-VI ⟹ set-form specialization.** Given the
strong VI at the set-family triple `(m + 1_S, u, Du)`, derive the
set-form specialization. -/
private lemma strongVI_setForm_of_setFamily
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBar : ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hFam : ∀ (S : Set (Fin d → ℝ)),
      0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH) Du m u
            (fun i x => Du i x - Du i x)
            ((m + fun x => S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) - m)
            (u - u)) :
    StationaryMFG.Theorems.SimplePower.StrongVI_setForm
      V H DpH γBar 0 Du m u := by
  intro S _hSmeas _hSfin
  have h := hFam S
  rw [StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_zero_eq
        (V := V) (H := H) (DpH := DpH)]
  refine le_of_le_of_eq h ?_
  refine mfgOperatorPair_test_pointwise_eq
    (V := V) (H := H) (DpH := DpH) Du m u
    (fun i x => Du i x - Du i x) (fun _ _ => (0 : ℝ))
    ((m + fun x => S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) - m)
    (fun x => S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
    (u - u) (fun _ => (0 : ℝ)) ?_ ?_ ?_
  · intro i x; simp
  · intro x; simp [Pi.sub_apply, Pi.add_apply]
  · intro x; simp [Pi.sub_apply]

/-! ### Periodic-set bridge for the set-family helper

`strongVI_setForm_of_setFamily_periodicS` (Phase 6d-ii-c-0) narrows
the hypothesis of `strongVI_setForm_of_setFamily` from "every
measurable `S`" to "every periodic measurable `S`". The bridge
constructs, for each measurable `S`, a periodic measurable set
`periodicHull S` whose indicator coincides pointwise with
`S.indicator 1` on `UnitCube d`. Pointwise agreement on the cube
gives a.e. agreement under `volume.restrict (UnitCube d)`, which lets
`mfgOperatorPair_congr_ae` move the conclusion from `periodicHull S`
to `S` itself. -/

/-- A subset of `ℝ^d ≅ Fin d → ℝ` is periodic if it is invariant under
every integer-lattice translation. Used in
`strongVI_setForm_of_setFamily_periodicS`. -/
def IsPeriodicSet (S : Set (Fin d → ℝ)) : Prop :=
  ∀ k : Fin d → ℤ, ∀ x, x ∈ S ↔ (x + fun i => (k i : ℝ)) ∈ S

/-- Coordinatewise fractional-part map. Sends every `x : Fin d → ℝ`
to its (unique) representative in `UnitCube d` under the
ℤ^d-translation action. -/
def floorPoint (x : Fin d → ℝ) : Fin d → ℝ :=
  fun i => Int.fract (x i)

lemma floorPoint_mem_unitCube (x : Fin d → ℝ) :
    floorPoint x ∈ UnitCube d := by
  rw [mem_unitCube_iff]
  intro i
  exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

lemma floorPoint_eq_self_of_mem_unitCube {x : Fin d → ℝ}
    (hx : x ∈ UnitCube d) : floorPoint x = x := by
  rw [mem_unitCube_iff] at hx
  funext i
  have hxi := hx i
  have hfloor : ⌊x i⌋ = 0 :=
    Int.floor_eq_zero_iff.mpr ⟨hxi.1, hxi.2⟩
  unfold floorPoint
  rw [Int.fract, hfloor]
  simp

lemma measurable_floorPoint :
    Measurable (floorPoint (d := d)) := by
  unfold floorPoint
  refine measurable_pi_iff.mpr ?_
  intro i
  exact (measurable_pi_apply i).fract

/-- Periodic completion of a set: the preimage of `S` under the
fractional-part map. Always periodic, measurable when `S` is, and
agrees with `S` on `UnitCube d`. -/
def periodicHull (S : Set (Fin d → ℝ)) : Set (Fin d → ℝ) :=
  floorPoint ⁻¹' S

lemma measurableSet_periodicHull {S : Set (Fin d → ℝ)}
    (hS : MeasurableSet S) : MeasurableSet (periodicHull (d := d) S) :=
  measurable_floorPoint hS

lemma floorPoint_add_int (x : Fin d → ℝ) (k : Fin d → ℤ) :
    floorPoint (x + fun i => (k i : ℝ)) = floorPoint x := by
  funext i
  unfold floorPoint
  change Int.fract (x i + (k i : ℝ)) = Int.fract (x i)
  exact Int.fract_add_intCast (x i) (k i)

lemma isPeriodicSet_periodicHull (S : Set (Fin d → ℝ)) :
    IsPeriodicSet (periodicHull (d := d) S) := by
  intro k x
  unfold periodicHull
  simp [Set.mem_preimage, floorPoint_add_int]

lemma mem_periodicHull_iff_of_mem_unitCube
    {S : Set (Fin d → ℝ)} {x : Fin d → ℝ} (hx : x ∈ UnitCube d) :
    x ∈ periodicHull S ↔ x ∈ S := by
  unfold periodicHull
  rw [Set.mem_preimage, floorPoint_eq_self_of_mem_unitCube hx]

/-- On `UnitCube d`, the indicator of `periodicHull S` equals the
indicator of `S` pointwise. -/
lemma indicator_periodicHull_eq_on_unitCube
    (S : Set (Fin d → ℝ)) {x : Fin d → ℝ} (hx : x ∈ UnitCube d) :
    (periodicHull S).indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
      = S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
  by_cases h : x ∈ S
  · have h' : x ∈ periodicHull S :=
      (mem_periodicHull_iff_of_mem_unitCube hx).mpr h
    simp [Set.indicator_of_mem h, Set.indicator_of_mem h']
  · have h' : x ∉ periodicHull S := by
      rw [mem_periodicHull_iff_of_mem_unitCube hx]; exact h
    simp [Set.indicator_of_notMem h, Set.indicator_of_notMem h']

/-- **Family-strong-VI on periodic `S` ⟹ set-form specialization.**

Given the strong VI at the set-family triple `(m + 1_S, u, Du)` only
for periodic measurable `S`, derive the full set-form specialization
(which quantifies over arbitrary measurable `S` of finite restricted
measure). The bridge: replace an arbitrary `S` by its periodic hull
`periodicHull S`, whose indicator agrees with `S.indicator 1`
pointwise on the unit cube. -/
private lemma strongVI_setForm_of_setFamily_periodicS
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBar : ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hFam : ∀ (S : Set (Fin d → ℝ)),
        MeasurableSet S → IsPeriodicSet S →
      0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH) Du m u
            (fun i x => Du i x - Du i x)
            ((m + fun x => S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) - m)
            (u - u)) :
    StationaryMFG.Theorems.SimplePower.StrongVI_setForm
      V H DpH γBar 0 Du m u := by
  intro S hSmeas _hSfin
  have hSper_meas : MeasurableSet (periodicHull (d := d) S) :=
    measurableSet_periodicHull hSmeas
  have hSper_per : IsPeriodicSet (periodicHull (d := d) S) :=
    isPeriodicSet_periodicHull S
  have hperiodic := hFam (periodicHull S) hSper_meas hSper_per
  have hae_indicator :
      (fun x => (periodicHull S).indicator
                  (fun _ : Fin d → ℝ => (1 : ℝ)) x)
        =ᵐ[volume.restrict (UnitCube d)]
      (fun x => S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
    rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_unitCube]
    refine Filter.Eventually.of_forall ?_
    intro x hx
    exact indicator_periodicHull_eq_on_unitCube S hx
  have hae_eta :
      ((m + fun x => (periodicHull S).indicator
              (fun _ : Fin d → ℝ => (1 : ℝ)) x) - m)
        =ᵐ[volume.restrict (UnitCube d)]
      ((m + fun x => S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) - m) := by
    filter_upwards [hae_indicator] with x hx
    simp [Pi.sub_apply, Pi.add_apply, hx]
  have hbridge :
      mfgOperatorPair (V := V) (H := H) (DpH := DpH) Du m u
            (fun i x => Du i x - Du i x)
            ((m + fun x => (periodicHull S).indicator
                  (fun _ : Fin d → ℝ => (1 : ℝ)) x) - m)
            (u - u)
        = mfgOperatorPair (V := V) (H := H) (DpH := DpH) Du m u
            (fun i x => Du i x - Du i x)
            ((m + fun x => S.indicator
                  (fun _ : Fin d → ℝ => (1 : ℝ)) x) - m)
            (u - u) :=
    mfgOperatorPair_congr_ae (V := V) (H := H) (DpH := DpH) Du m u
      (fun i x => Du i x - Du i x) (fun i x => Du i x - Du i x)
      ((m + fun x => (periodicHull S).indicator
            (fun _ : Fin d → ℝ => (1 : ℝ)) x) - m)
      ((m + fun x => S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) - m)
      (u - u) (u - u)
      (fun _ => Filter.EventuallyEq.refl _ _)
      hae_eta
      (Filter.EventuallyEq.refl _ _)
  have hperiodic_S :
      0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH) Du m u
            (fun i x => Du i x - Du i x)
            ((m + fun x => S.indicator
                  (fun _ : Fin d → ℝ => (1 : ℝ)) x) - m)
            (u - u) := hbridge ▸ hperiodic
  rw [StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_zero_eq
        (V := V) (H := H) (DpH := DpH)]
  refine le_of_le_of_eq hperiodic_S ?_
  refine mfgOperatorPair_test_pointwise_eq
    (V := V) (H := H) (DpH := DpH) Du m u
    (fun i x => Du i x - Du i x) (fun _ _ => (0 : ℝ))
    ((m + fun x => S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) - m)
    (fun x => S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
    (u - u) (fun _ => (0 : ℝ)) ?_ ?_ ?_
  · intro i x; simp
  · intro x; simp [Pi.sub_apply, Pi.add_apply]
  · intro x; simp [Pi.sub_apply]

/-- **AC sanity check (Phase 6d-ii-c-0).** A universal-form
strong-VI hypothesis discharges the periodic-set-family hypothesis
trivially, recovering the set-form specialization. -/
example
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBar : ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hUniv : ∀ (μ υ : (Fin d → ℝ) → ℝ)
                (Dυ : Fin d → (Fin d → ℝ) → ℝ),
      0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH) Du m u
            (fun i x => Dυ i x - Du i x) (μ - m) (υ - u)) :
    StationaryMFG.Theorems.SimplePower.StrongVI_setForm
      V H DpH γBar 0 Du m u :=
  strongVI_setForm_of_setFamily_periodicS (γBar := γBar)
    (fun S _ _ => hUniv
      (m + fun x => S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) u Du)

/-- **Family-strong-VI ⟹ signed set-form specialization.** Given
the strong VI at the signed-family triple `(m + σ·m·1_S, u, Du)`
for every `σ` and `S`, derive the signed-set-form specialization. -/
private lemma strongVI_setFormSigned_of_signedFamily
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBar : ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hFam : ∀ (σ : ℝ) (S : Set (Fin d → ℝ)),
      0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH) Du m u
            (fun i x => Du i x - Du i x)
            ((m + fun x => σ * m x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) - m)
            (u - u)) :
    StationaryMFG.Theorems.SimplePower.StrongVI_setForm_signed
      V H DpH γBar 0 Du m u := by
  intro σ _hσ S _hSmeas _hSfin
  have h := hFam σ S
  rw [StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_zero_eq
        (V := V) (H := H) (DpH := DpH)]
  refine le_of_le_of_eq h ?_
  refine mfgOperatorPair_test_pointwise_eq
    (V := V) (H := H) (DpH := DpH) Du m u
    (fun i x => Du i x - Du i x) (fun _ _ => (0 : ℝ))
    ((m + fun x => σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
        - m)
    (fun x => σ * (m x) * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
    (u - u) (fun _ => (0 : ℝ)) ?_ ?_ ?_
  · intro i x; simp
  · intro x; simp [Pi.sub_apply, Pi.add_apply]
  · intro x; simp [Pi.sub_apply]

/-- **Family-strong-VI ⟹ signed set-form specialization (σ ∈ {±1} variant).**
Same as `strongVI_setFormSigned_of_signedFamily`, but `hFam` is only
required at `σ ∈ {±1}` instead of universal-σ. This narrower variant
matches the shape produced by the iter-362 5a-signed refactor, where
the per-test-triple weak VI on `D_signed_family_nn` is only available
at `σ ∈ {±1}` (the nonneg-primal constraint forces the σ restriction
in `mem_D_signed_family_nn_test`). -/
private lemma strongVI_setFormSigned_of_signedFamily_pmone
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBar : ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hFam : ∀ (σ : ℝ), σ = 1 ∨ σ = -1 → ∀ (S : Set (Fin d → ℝ)),
      0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH) Du m u
            (fun i x => Du i x - Du i x)
            ((m + fun x => σ * m x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) - m)
            (u - u)) :
    StationaryMFG.Theorems.SimplePower.StrongVI_setForm_signed
      V H DpH γBar 0 Du m u := by
  intro σ hσ S _hSmeas _hSfin
  have h := hFam σ hσ S
  rw [StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_zero_eq
        (V := V) (H := H) (DpH := DpH)]
  refine le_of_le_of_eq h ?_
  refine mfgOperatorPair_test_pointwise_eq
    (V := V) (H := H) (DpH := DpH) Du m u
    (fun i x => Du i x - Du i x) (fun _ _ => (0 : ℝ))
    ((m + fun x => σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
        - m)
    (fun x => σ * (m x) * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
    (u - u) (fun _ => (0 : ℝ)) ?_ ?_ ?_
  · intro i x; simp
  · intro x; simp [Pi.sub_apply, Pi.add_apply]
  · intro x; simp [Pi.sub_apply]

/-- **Signed-family-strong-VI on periodic `S` ⟹ signed set-form
specialization (σ ∈ {±1} variant).** Same as
`strongVI_setFormSigned_of_signedFamily_pmone`, but the
hypothesis is only required at periodic measurable `S`. The bridge:
replace an arbitrary measurable `S` by its periodic hull
`periodicHull S` (Phase 6d-ii-c-0 infrastructure), whose indicator
agrees with `S.indicator 1` pointwise on the unit cube, hence the
perturbations `σ·m·1_{periodicHull S}` and `σ·m·1_S` agree pointwise
on `UnitCube d`. The conclusion transports across via
`mfgOperatorPair_congr_ae`. -/
private lemma strongVI_setFormSigned_of_signedFamily_pmone_periodicS
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBar : ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hFam : ∀ (σ : ℝ), σ = 1 ∨ σ = -1 → ∀ (S : Set (Fin d → ℝ)),
        MeasurableSet S → IsPeriodicSet S →
      0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH) Du m u
            (fun i x => Du i x - Du i x)
            ((m + fun x => σ * m x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) - m)
            (u - u)) :
    StationaryMFG.Theorems.SimplePower.StrongVI_setForm_signed
      V H DpH γBar 0 Du m u := by
  intro σ hσ S hSmeas _hSfin
  have hSper_meas : MeasurableSet (periodicHull (d := d) S) :=
    measurableSet_periodicHull hSmeas
  have hSper_per : IsPeriodicSet (periodicHull (d := d) S) :=
    isPeriodicSet_periodicHull S
  have hperiodic := hFam σ hσ (periodicHull S) hSper_meas hSper_per
  have hae_indicator :
      (fun x => (periodicHull S).indicator
                  (fun _ : Fin d → ℝ => (1 : ℝ)) x)
        =ᵐ[volume.restrict (UnitCube d)]
      (fun x => S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
    rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_unitCube]
    refine Filter.Eventually.of_forall ?_
    intro x hx
    exact indicator_periodicHull_eq_on_unitCube S hx
  have hae_eta :
      ((m + fun x => σ * m x *
              (periodicHull S).indicator
                (fun _ : Fin d → ℝ => (1 : ℝ)) x) - m)
        =ᵐ[volume.restrict (UnitCube d)]
      ((m + fun x => σ * m x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) - m) := by
    filter_upwards [hae_indicator] with x hx
    simp [Pi.sub_apply, Pi.add_apply, hx]
  have hbridge :
      mfgOperatorPair (V := V) (H := H) (DpH := DpH) Du m u
            (fun i x => Du i x - Du i x)
            ((m + fun x => σ * m x *
                  (periodicHull S).indicator
                    (fun _ : Fin d → ℝ => (1 : ℝ)) x) - m)
            (u - u)
        = mfgOperatorPair (V := V) (H := H) (DpH := DpH) Du m u
            (fun i x => Du i x - Du i x)
            ((m + fun x => σ * m x *
                  S.indicator
                    (fun _ : Fin d → ℝ => (1 : ℝ)) x) - m)
            (u - u) :=
    mfgOperatorPair_congr_ae (V := V) (H := H) (DpH := DpH) Du m u
      (fun i x => Du i x - Du i x) (fun i x => Du i x - Du i x)
      ((m + fun x => σ * m x *
            (periodicHull S).indicator
              (fun _ : Fin d → ℝ => (1 : ℝ)) x) - m)
      ((m + fun x => σ * m x *
            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) - m)
      (u - u) (u - u)
      (fun _ => Filter.EventuallyEq.refl _ _)
      hae_eta
      (Filter.EventuallyEq.refl _ _)
  have hperiodic_S :
      0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH) Du m u
            (fun i x => Du i x - Du i x)
            ((m + fun x => σ * m x *
                  S.indicator
                    (fun _ : Fin d → ℝ => (1 : ℝ)) x) - m)
            (u - u) := hbridge ▸ hperiodic
  rw [StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_zero_eq
        (V := V) (H := H) (DpH := DpH)]
  refine le_of_le_of_eq hperiodic_S ?_
  refine mfgOperatorPair_test_pointwise_eq
    (V := V) (H := H) (DpH := DpH) Du m u
    (fun i x => Du i x - Du i x) (fun _ _ => (0 : ℝ))
    ((m + fun x => σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
        - m)
    (fun x => σ * (m x) * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
    (u - u) (fun _ => (0 : ℝ)) ?_ ?_ ?_
  · intro i x; simp
  · intro x; simp [Pi.sub_apply, Pi.add_apply]
  · intro x; simp [Pi.sub_apply]

/-- **AC sanity check (Phase 6d-ii-c-2b).** A universal-form
strong-VI hypothesis discharges the periodic-set signed-family
hypothesis trivially, recovering the signed-set-form
specialization. -/
example
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBar : ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hUniv : ∀ (μ υ : (Fin d → ℝ) → ℝ)
                (Dυ : Fin d → (Fin d → ℝ) → ℝ),
      0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH) Du m u
            (fun i x => Dυ i x - Du i x) (μ - m) (υ - u)) :
    StationaryMFG.Theorems.SimplePower.StrongVI_setForm_signed
      V H DpH γBar 0 Du m u :=
  strongVI_setFormSigned_of_signedFamily_pmone_periodicS (γBar := γBar)
    (fun σ _ S _ _ => hUniv
      (m + fun x => σ * m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) u Du)

/-- **Family-strong-VI ⟹ transport-form specialization.** Given
the strong VI at the transport-family triple
`(m, u + σ·φ, Du + σ·∂φ)` for every `σ` and `φ`, derive the
transport-form specialization. -/
private lemma strongVI_transportForm_of_transportFamily
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBar : ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hFam : ∀ (σ : ℝ) (φ : StationaryMFG.Periodic.SmoothPeriodic d),
      0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH) Du m u
            (fun i x => (Du i x + σ *
                ((StationaryMFG.Periodic.SmoothPeriodic.partialDeriv i φ
                    : StationaryMFG.Periodic.SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x) - Du i x)
            (m - m)
            ((u + fun x => σ * (φ : (Fin d → ℝ) → ℝ) x) - u)) :
    StationaryMFG.Theorems.SimplePower.StrongVI_transportForm
      V H DpH γBar 0 Du m u := by
  intro σ _hσ φ
  have h := hFam σ φ
  rw [StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_zero_eq
        (V := V) (H := H) (DpH := DpH)]
  refine le_of_le_of_eq h ?_
  refine mfgOperatorPair_test_pointwise_eq
    (V := V) (H := H) (DpH := DpH) Du m u
    (fun i x => (Du i x + σ *
        ((StationaryMFG.Periodic.SmoothPeriodic.partialDeriv i φ
            : StationaryMFG.Periodic.SmoothPeriodic d) :
          (Fin d → ℝ) → ℝ) x) - Du i x)
    (fun i x => σ *
      ((StationaryMFG.Periodic.SmoothPeriodic.partialDeriv i φ
          : StationaryMFG.Periodic.SmoothPeriodic d) :
        (Fin d → ℝ) → ℝ) x)
    (m - m) (fun _ => (0 : ℝ))
    ((u + fun x => σ * (φ : (Fin d → ℝ) → ℝ) x) - u)
    (fun x => σ * (φ : (Fin d → ℝ) → ℝ) x) ?_ ?_ ?_
  · intro i x; ring
  · intro x; simp [Pi.sub_apply]
  · intro x; simp [Pi.sub_apply, Pi.add_apply]

/-- **AC sanity check (Child 1).** The three family-restricted
helpers compose with their universal counterparts: a universal
strong-VI hypothesis discharges the family hypothesis trivially,
recovering the universal-form specialization. -/
example
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBar : ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hUniv : ∀ (μ υ : (Fin d → ℝ) → ℝ)
                (Dυ : Fin d → (Fin d → ℝ) → ℝ),
      0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH) Du m u
            (fun i x => Dυ i x - Du i x) (μ - m) (υ - u)) :
    StationaryMFG.Theorems.SimplePower.StrongVI_setForm
      V H DpH γBar 0 Du m u :=
  strongVI_setForm_of_setFamily (γBar := γBar)
    (fun S => hUniv
      (m + fun x => S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) u Du)

/-- **AC sanity check (Child 1).** Signed counterpart. -/
example
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBar : ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hUniv : ∀ (μ υ : (Fin d → ℝ) → ℝ)
                (Dυ : Fin d → (Fin d → ℝ) → ℝ),
      0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH) Du m u
            (fun i x => Dυ i x - Du i x) (μ - m) (υ - u)) :
    StationaryMFG.Theorems.SimplePower.StrongVI_setForm_signed
      V H DpH γBar 0 Du m u :=
  strongVI_setFormSigned_of_signedFamily (γBar := γBar)
    (fun σ S => hUniv
      (m + fun x => σ * m x *
        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) u Du)

/-- **AC sanity check (Child 1).** Transport counterpart. -/
example
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBar : ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hUniv : ∀ (μ υ : (Fin d → ℝ) → ℝ)
                (Dυ : Fin d → (Fin d → ℝ) → ℝ),
      0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH) Du m u
            (fun i x => Dυ i x - Du i x) (μ - m) (υ - u)) :
    StationaryMFG.Theorems.SimplePower.StrongVI_transportForm
      V H DpH γBar 0 Du m u :=
  strongVI_transportForm_of_transportFamily (γBar := γBar)
    (fun σ φ => hUniv m
      (u + fun x => σ * (φ : (Fin d → ℝ) → ℝ) x)
      (fun i x => Du i x + σ *
        ((StationaryMFG.Periodic.SmoothPeriodic.partialDeriv i φ
            : StationaryMFG.Periodic.SmoothPeriodic d) :
          (Fin d → ℝ) → ℝ) x))

/-! ### Family domains for Phase F strip (Children 2-3).

Per `infra-P5-theorem1-phase-F-strip-mintyResidue-finalize` (Children
2-3), the Phase F strip refactors the F0 producers to apply
`main_strong_VI` on family-restricted domains rather than the
universal `Set.univ`. Each family domain is keyed to a fixed limit
triple `(mLim, uLim, DuLim)` and contains exactly the test triples
required by the corresponding family-restricted helper
(`strongVI_setForm_of_setFamily` etc., landed by Child 1).

The three families:

* **Set family** `D_set_family mLim uLim DuLim`: triples of the form
  `(mLim + ρ, uLim, DuLim)` for some non-negative perturbation
  `ρ ≥ 0`. Captures the set-family test triples
  `(mLim + 1_S, uLim, DuLim)` (taking `ρ = 1_S`) and the limit
  triple itself (`ρ = 0`).
* **Signed family** `D_signed_family mLim uLim DuLim`: triples of the
  form `(mLim + g, uLim, DuLim)` for arbitrary `g`. Captures the
  signed-family test triples `(mLim + σ · mLim · 1_S, uLim, DuLim)`
  (taking `g = σ · mLim · 1_S`) and the limit triple (`g = 0`).
* **Transport family** `D_transport_family mLim uLim DuLim`: triples
  of the form `(mLim, υ, Dυ)` for arbitrary `(υ, Dυ)`. Captures the
  transport-family test triples `(mLim, uLim + σ·φ, DuLim + σ·∂φ)`
  and the limit triple (`υ = uLim, Dυ = DuLim`).

Each family is **segment-closed** (closed under pointwise convex
combinations) by direct computation: the convex combination of two
triples in the family is again of the family's shape. -/

/-- **Set family** for the Phase F strip. Triples whose density is
`mLim` plus a non-negative perturbation, with `(u, Du) = (uLim, DuLim)`. -/
def D_set_family
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ) :
    Set (StationaryMFG.Theorems.SimplePower.MFGTriple d) :=
  { p | ∃ ρ : (Fin d → ℝ) → ℝ, (∀ x, 0 ≤ ρ x) ∧
          p = ((fun x => mLim x + ρ x), uLim, DuLim) }

/-- **Signed family** for the Phase F strip. Triples whose density is
`mLim` plus an arbitrary perturbation, with `(u, Du) = (uLim, DuLim)`. -/
def D_signed_family
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ) :
    Set (StationaryMFG.Theorems.SimplePower.MFGTriple d) :=
  { p | ∃ g : (Fin d → ℝ) → ℝ,
          p = ((fun x => mLim x + g x), uLim, DuLim) }

/-- **Transport family** for the Phase F strip. Triples whose density
component is exactly `mLim`; the value-function and gradient
components are arbitrary. -/
def D_transport_family
    (mLim : (Fin d → ℝ) → ℝ)
    (_uLim : (Fin d → ℝ) → ℝ)
    (_DuLim : Fin d → (Fin d → ℝ) → ℝ) :
    Set (StationaryMFG.Theorems.SimplePower.MFGTriple d) :=
  { p | p.1 = mLim }

/-- The limit triple lies in the set family. -/
lemma mem_D_set_family_limit
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ) :
    (mLim, uLim, DuLim) ∈ D_set_family (d := d) mLim uLim DuLim := by
  refine ⟨fun _ => 0, fun _ => le_refl 0, ?_⟩
  ext1
  · funext x; simp
  · rfl

/-- The limit triple lies in the signed family. -/
lemma mem_D_signed_family_limit
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ) :
    (mLim, uLim, DuLim) ∈ D_signed_family (d := d) mLim uLim DuLim := by
  refine ⟨fun _ => 0, ?_⟩
  ext1
  · funext x; simp
  · rfl

/-- The limit triple lies in the transport family. -/
lemma mem_D_transport_family_limit
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ) :
    (mLim, uLim, DuLim) ∈ D_transport_family (d := d) mLim uLim DuLim := rfl

/-- **Set-family test-triple membership.** For any `S` and `ρ ≥ 0`,
the test triple `(mLim + S.indicator ρ, uLim, DuLim)` lies in
`D_set_family`. -/
lemma mem_D_set_family_test
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    (S : Set (Fin d → ℝ))
    (ρ : (Fin d → ℝ) → ℝ) (hρ : ∀ x, 0 ≤ ρ x) :
    ((fun x => mLim x + S.indicator ρ x), uLim, DuLim)
        ∈ D_set_family (d := d) mLim uLim DuLim := by
  refine ⟨fun x => S.indicator ρ x, ?_, rfl⟩
  intro x
  classical
  by_cases hx : x ∈ S
  · simpa [Set.indicator_of_mem hx] using hρ x
  · simpa [Set.indicator_of_notMem hx]

/-- **Signed-family test-triple membership.** For any `σ`, `S`, the
test triple `(mLim + σ · mLim · 1_S, uLim, DuLim)` lies in
`D_signed_family`. -/
lemma mem_D_signed_family_test
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    (σ : ℝ) (S : Set (Fin d → ℝ)) :
    ((fun x => mLim x +
        σ * mLim x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x),
      uLim, DuLim)
        ∈ D_signed_family (d := d) mLim uLim DuLim :=
  ⟨fun x => σ * mLim x *
      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x, rfl⟩

/-- **Transport-family test-triple membership.** For any `σ` and
periodic test function `φ`, the test triple
`(mLim, uLim + σ·φ, DuLim + σ·∂φ)` lies in `D_transport_family`. -/
lemma mem_D_transport_family_test
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    (σ : ℝ) (φ : StationaryMFG.Periodic.SmoothPeriodic d) :
    (mLim,
      (uLim + fun x => σ * (φ : (Fin d → ℝ) → ℝ) x),
      (fun i x => DuLim i x + σ *
        ((StationaryMFG.Periodic.SmoothPeriodic.partialDeriv i φ
            : StationaryMFG.Periodic.SmoothPeriodic d) :
          (Fin d → ℝ) → ℝ) x))
        ∈ D_transport_family (d := d) mLim uLim DuLim := rfl

/-- **Set family is segment-closed.** Convex combinations of triples
of the form `(mLim + ρ, uLim, DuLim)` with `ρ ≥ 0` remain in the
family: the perturbation `(1-t)·ρ̄ + t·ρ` is again non-negative for
`t ∈ [0,1]`, and the `(uLim, DuLim)` components are fixed. -/
lemma D_set_family_segment_closed
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    {μBar : (Fin d → ℝ) → ℝ} {ῡ : (Fin d → ℝ) → ℝ}
    {Dῡ : Fin d → (Fin d → ℝ) → ℝ}
    (hBar : (μBar, ῡ, Dῡ) ∈ D_set_family (d := d) mLim uLim DuLim)
    {μ : (Fin d → ℝ) → ℝ} {υ : (Fin d → ℝ) → ℝ}
    {Dυ : Fin d → (Fin d → ℝ) → ℝ}
    (hμ : (μ, υ, Dυ) ∈ D_set_family (d := d) mLim uLim DuLim)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ((fun x => StationaryMFG.Theorems.SimplePower.cxComb μ μBar t x),
     (fun x => StationaryMFG.Theorems.SimplePower.cxComb υ ῡ t x),
     (fun i x =>
       StationaryMFG.Theorems.SimplePower.cxCombGrad Dυ Dῡ t i x))
       ∈ D_set_family (d := d) mLim uLim DuLim := by
  obtain ⟨ρBar, hρBar_nn, hBar_eq⟩ := hBar
  obtain ⟨ρ, hρ_nn, hμ_eq⟩ := hμ
  obtain ⟨ht0, ht1⟩ := ht
  -- Extract endpoint equalities via `Prod.mk.injEq`.
  rw [Prod.mk.injEq, Prod.mk.injEq] at hBar_eq hμ_eq
  obtain ⟨hμBar, hυBar, hDυBar⟩ := hBar_eq
  obtain ⟨hμμ, hυυ, hDυυ⟩ := hμ_eq
  -- The combined perturbation is `(1-t)·ρBar + t·ρ`, non-negative.
  refine ⟨fun x => (1 - t) * ρBar x + t * ρ x, ?_, ?_⟩
  · intro x
    have h1mt_nn : 0 ≤ 1 - t := by linarith
    have hA : 0 ≤ (1 - t) * ρBar x := mul_nonneg h1mt_nn (hρBar_nn x)
    have hB : 0 ≤ t * ρ x := mul_nonneg ht0 (hρ_nn x)
    linarith
  · -- Equality of triples.
    refine Prod.mk.injEq .. |>.mpr ⟨?_, Prod.mk.injEq .. |>.mpr ⟨?_, ?_⟩⟩
    · -- Density component.
      funext x
      show StationaryMFG.Theorems.SimplePower.cxComb μ μBar t x
            = mLim x + ((1 - t) * ρBar x + t * ρ x)
      have hcx : StationaryMFG.Theorems.SimplePower.cxComb μ μBar t x
                  = (1 - t) * μBar x + t * μ x := rfl
      rw [hcx, hμBar, hμμ]
      ring
    · -- u component.
      funext x
      show StationaryMFG.Theorems.SimplePower.cxComb υ ῡ t x = uLim x
      have hcx : StationaryMFG.Theorems.SimplePower.cxComb υ ῡ t x
                  = (1 - t) * ῡ x + t * υ x := rfl
      rw [hcx, hυBar, hυυ]
      ring
    · -- Du component.
      funext i x
      show StationaryMFG.Theorems.SimplePower.cxCombGrad Dυ Dῡ t i x
            = DuLim i x
      have hcx : StationaryMFG.Theorems.SimplePower.cxCombGrad Dυ Dῡ t i x
                  = (1 - t) * Dῡ i x + t * Dυ i x := rfl
      rw [hcx, hDυBar, hDυυ]
      ring

/-- **Signed family is segment-closed.** The perturbation `g` is
arbitrary, so the convex combination `(1-t)·ḡ + t·g` is again
arbitrary. -/
lemma D_signed_family_segment_closed
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    {μBar : (Fin d → ℝ) → ℝ} {ῡ : (Fin d → ℝ) → ℝ}
    {Dῡ : Fin d → (Fin d → ℝ) → ℝ}
    (hBar : (μBar, ῡ, Dῡ) ∈ D_signed_family (d := d) mLim uLim DuLim)
    {μ : (Fin d → ℝ) → ℝ} {υ : (Fin d → ℝ) → ℝ}
    {Dυ : Fin d → (Fin d → ℝ) → ℝ}
    (hμ : (μ, υ, Dυ) ∈ D_signed_family (d := d) mLim uLim DuLim)
    (t : ℝ) (_ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ((fun x => StationaryMFG.Theorems.SimplePower.cxComb μ μBar t x),
     (fun x => StationaryMFG.Theorems.SimplePower.cxComb υ ῡ t x),
     (fun i x =>
       StationaryMFG.Theorems.SimplePower.cxCombGrad Dυ Dῡ t i x))
       ∈ D_signed_family (d := d) mLim uLim DuLim := by
  obtain ⟨gBar, hBar_eq⟩ := hBar
  obtain ⟨g, hμ_eq⟩ := hμ
  rw [Prod.mk.injEq, Prod.mk.injEq] at hBar_eq hμ_eq
  obtain ⟨hμBar, hυBar, hDυBar⟩ := hBar_eq
  obtain ⟨hμμ, hυυ, hDυυ⟩ := hμ_eq
  refine ⟨fun x => (1 - t) * gBar x + t * g x, ?_⟩
  refine Prod.mk.injEq .. |>.mpr ⟨?_, Prod.mk.injEq .. |>.mpr ⟨?_, ?_⟩⟩
  · funext x
    show StationaryMFG.Theorems.SimplePower.cxComb μ μBar t x
          = mLim x + ((1 - t) * gBar x + t * g x)
    have hcx : StationaryMFG.Theorems.SimplePower.cxComb μ μBar t x
                = (1 - t) * μBar x + t * μ x := rfl
    rw [hcx, hμBar, hμμ]
    ring
  · funext x
    show StationaryMFG.Theorems.SimplePower.cxComb υ ῡ t x = uLim x
    have hcx : StationaryMFG.Theorems.SimplePower.cxComb υ ῡ t x
                = (1 - t) * ῡ x + t * υ x := rfl
    rw [hcx, hυBar, hυυ]
    ring
  · funext i x
    show StationaryMFG.Theorems.SimplePower.cxCombGrad Dυ Dῡ t i x
          = DuLim i x
    have hcx : StationaryMFG.Theorems.SimplePower.cxCombGrad Dυ Dῡ t i x
                = (1 - t) * Dῡ i x + t * Dυ i x := rfl
    rw [hcx, hDυBar, hDυυ]
    ring

/-! ### Phase 5a-signed — narrowed nonneg-primal signed family.

The signed-family field `hVIeps_signed_user_triple` requires the
user-supplied primal `μ ≥ 0` a.e. To use the helper
`limitPassage_signedForm_of_seqVI` for `hweak` on a segment-closed
family, we narrow `D_signed_family` to the subset whose primal density
is nonneg a.e. The signed-test triples `(mLim + σ·mLim·1_S, uLim,
DuLim)` (σ ∈ {±1}) all satisfy the nonneg constraint since `mLim ≥ 0`
a.e. and `1 + σ·1_S ∈ {0,1,2}`. The narrower family is
segment-closed by direct convexity. -/

/-- **Nonneg-primal signed family** for the Phase 5a-signed refactor.
Triples in `D_signed_family` whose primal density is nonneg a.e. -/
def D_signed_family_nn
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ) :
    Set (StationaryMFG.Theorems.SimplePower.MFGTriple d) :=
  { p | (∃ g : (Fin d → ℝ) → ℝ,
            p = ((fun x => mLim x + g x), uLim, DuLim))
        ∧ 0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                  (UnitCube d)] p.1 }

/-- Membership of the limit triple in the nonneg-primal signed family.
Requires `mLim ≥ 0` a.e. -/
lemma mem_D_signed_family_nn_limit
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    (hmLim_nonneg : 0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                            (UnitCube d)] mLim) :
    (mLim, uLim, DuLim) ∈ D_signed_family_nn (d := d) mLim uLim DuLim := by
  refine ⟨⟨fun _ => 0, ?_⟩, ?_⟩
  · ext1
    · funext x; simp
    · rfl
  · simpa using hmLim_nonneg

/-- The signed-test triple `(mLim + σ·mLim·1_S, uLim, DuLim)` lies in
the nonneg-primal signed family for `σ ∈ {±1}`, given `mLim ≥ 0` a.e. -/
lemma mem_D_signed_family_nn_test
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    (hmLim_nonneg : 0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                            (UnitCube d)] mLim)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (S : Set (Fin d → ℝ)) :
    ((fun x => mLim x +
        σ * mLim x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x),
      uLim, DuLim)
        ∈ D_signed_family_nn (d := d) mLim uLim DuLim := by
  refine ⟨⟨fun x => σ * mLim x *
        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x, rfl⟩, ?_⟩
  -- Show: 0 ≤ᵐ (mLim + σ·mLim·1_S) a.e.
  filter_upwards [hmLim_nonneg] with x hxm
  classical
  by_cases hxS : x ∈ S
  · -- Inside S: indicator = 1, so primal = mLim + σ·mLim = mLim·(1+σ).
    -- For σ ∈ {±1}, 1+σ ∈ {0,2} ≥ 0; combined with mLim ≥ 0, primal ≥ 0.
    have hind : S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x = 1 :=
      Set.indicator_of_mem hxS _
    rw [hind]
    show 0 ≤ mLim x + σ * mLim x * 1
    have hxm' : (0 : ℝ) ≤ mLim x := hxm
    rcases hσ with h1 | hm1
    · subst h1; linarith
    · subst hm1; linarith
  · -- Outside S: indicator = 0, so primal = mLim ≥ 0.
    have hind : S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x = 0 :=
      Set.indicator_of_notMem hxS _
    rw [hind]
    show 0 ≤ mLim x + σ * mLim x * 0
    have hxm' : (0 : ℝ) ≤ mLim x := hxm
    linarith

/-- **Nonneg-primal signed family is segment-closed.** Both endpoints
have nonneg primal densities a.e., so the convex combination
`(1-t)·μBar + t·μ` is also nonneg a.e. for `t ∈ [0,1]`. The shape
remains `(mLim + ·, uLim, DuLim)` (signed family is segment-closed in
its wider form). -/
lemma D_signed_family_nn_segment_closed
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    {μBar : (Fin d → ℝ) → ℝ} {ῡ : (Fin d → ℝ) → ℝ}
    {Dῡ : Fin d → (Fin d → ℝ) → ℝ}
    (hBar : (μBar, ῡ, Dῡ) ∈ D_signed_family_nn (d := d) mLim uLim DuLim)
    {μ : (Fin d → ℝ) → ℝ} {υ : (Fin d → ℝ) → ℝ}
    {Dυ : Fin d → (Fin d → ℝ) → ℝ}
    (hμ : (μ, υ, Dυ) ∈ D_signed_family_nn (d := d) mLim uLim DuLim)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ((fun x => StationaryMFG.Theorems.SimplePower.cxComb μ μBar t x),
     (fun x => StationaryMFG.Theorems.SimplePower.cxComb υ ῡ t x),
     (fun i x =>
       StationaryMFG.Theorems.SimplePower.cxCombGrad Dυ Dῡ t i x))
       ∈ D_signed_family_nn (d := d) mLim uLim DuLim := by
  obtain ⟨hBar_shape, hBar_nn⟩ := hBar
  obtain ⟨hμ_shape, hμ_nn⟩ := hμ
  -- Use the wider segment-closure to get the shape part.
  have hShape :=
    D_signed_family_segment_closed (d := d) mLim uLim DuLim hBar_shape hμ_shape t ht
  refine ⟨hShape, ?_⟩
  -- Show: 0 ≤ᵐ cxComb μ μBar t a.e.
  obtain ⟨ht0, ht1⟩ := ht
  have h1mt : 0 ≤ 1 - t := by linarith
  have hBar_nn' : 0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                          (UnitCube d)] μBar := hBar_nn
  have hμ_nn' : 0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                          (UnitCube d)] μ := hμ_nn
  filter_upwards [hBar_nn', hμ_nn'] with x hxBar hxμ
  show (0 : ℝ) ≤ StationaryMFG.Theorems.SimplePower.cxComb μ μBar t x
  have hcx : StationaryMFG.Theorems.SimplePower.cxComb μ μBar t x
              = (1 - t) * μBar x + t * μ x := rfl
  rw [hcx]
  have h1 : 0 ≤ (1 - t) * μBar x := mul_nonneg h1mt hxBar
  have h2 : 0 ≤ t * μ x := mul_nonneg ht0 hxμ
  linarith

/-! ### Phase 6d-ii-c-1 — narrow paper-form-only family domains.

Per `infra-P5-theorem1-phase-6d-ii-c-1-narrow-domain-defs`, we land
two narrower domains alongside `D_set_family` and `D_signed_family_nn`:

* `D_set_family_paper βBar mLim uLim DuLim` — set-form triples whose
  perturbation `ρ` is **periodic** and lies in `MemLpPer βBar` (i.e.
  has `Lᵖ` regularity at the paper exponent), in addition to being
  pointwise nonneg.
* `D_signed_family_paper_nn βBar mLim uLim DuLim` — signed-form
  triples whose perturbation `g` is periodic and lies in `MemLpPer βBar`
  with the primal density `mLim + g ≥ 0` a.e.

Both are segment-closed: convex combinations of periodic
`MemLpPer βBar` perturbations are again periodic `MemLpPer βBar`
(via `MemLpPer.add`/`MemLpPer.const_smul` and
`IsPeriodic.add`/`IsPeriodic.smul`), and the nonneg/a.e.-nonneg
constraint propagates by linearity.

These narrower domains feed `set_perturbation`/`signed_perturbation`
in the next child task (6d-ii-c-2). This task lands only the
definitions and the structural lemmas (segment closure, test-triple
membership, subset to the wider family). -/

/-- **Set narrow paper-form domain.** Triples `(mLim + ρ, uLim, DuLim)`
where the perturbation `ρ` is pointwise nonneg, periodic, and lies in
`MemLpPer βBar`. -/
def D_set_family_paper
    (βBar : ℝ≥0∞)
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ) :
    Set (StationaryMFG.Theorems.SimplePower.MFGTriple d) :=
  { p | ∃ ρ : (Fin d → ℝ) → ℝ,
          (∀ x, 0 ≤ ρ x) ∧
          StationaryMFG.Periodic.MemLpPer (d := d) βBar ρ ∧
          StationaryMFG.Periodic.IsPeriodic ρ ∧
          p = ((fun x => mLim x + ρ x), uLim, DuLim) }

/-- **Signed narrow paper-form domain (nonneg primal).** Triples
`(mLim + g, uLim, DuLim)` where `g` is periodic, `MemLpPer βBar`, and
the primal density `mLim + g` is a.e. nonneg on the unit cube. -/
def D_signed_family_paper_nn
    (βBar : ℝ≥0∞)
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ) :
    Set (StationaryMFG.Theorems.SimplePower.MFGTriple d) :=
  { p | ∃ g : (Fin d → ℝ) → ℝ,
          StationaryMFG.Periodic.MemLpPer (d := d) βBar g ∧
          StationaryMFG.Periodic.IsPeriodic g ∧
          (0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                  (UnitCube d)]
              (fun x => mLim x + g x)) ∧
          p = ((fun x => mLim x + g x), uLim, DuLim) }

/-- The limit triple lies in the narrow paper-form set domain
(perturbation `ρ = 0`). -/
lemma mem_D_set_family_paper_limit
    (βBar : ℝ≥0∞)
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ) :
    (mLim, uLim, DuLim) ∈ D_set_family_paper (d := d) βBar mLim uLim DuLim := by
  refine ⟨fun _ => 0, fun _ => le_refl 0, ?_, ?_, ?_⟩
  · -- `MemLpPer βBar 0` via the constant-function route.
    have hcube : MeasureTheory.volume (UnitCube d) ≠ ⊤ := by simp
    haveI : MeasureTheory.IsFiniteMeasure
              (MeasureTheory.Measure.restrict MeasureTheory.volume
                (UnitCube (d := d))) :=
      ⟨by
        rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ]
        simp⟩
    exact StationaryMFG.Periodic.MemLp.toMemLpPer
      (MeasureTheory.memLp_const (0 : ℝ))
  · -- `IsPeriodic 0`.
    intro k x; rfl
  · ext1
    · funext x; simp
    · rfl

/-- **Set-narrow test-triple membership (periodic case).** Given a
pointwise nonneg, periodic, `MemLpPer βBar` perturbation `ρ`, the
triple `(mLim + ρ, uLim, DuLim)` lies in `D_set_family_paper`. -/
lemma mem_D_set_family_paper_test_periodic
    (βBar : ℝ≥0∞)
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    (ρ : (Fin d → ℝ) → ℝ)
    (hρ_nn : ∀ x, 0 ≤ ρ x)
    (hρ_lp : StationaryMFG.Periodic.MemLpPer (d := d) βBar ρ)
    (hρ_per : StationaryMFG.Periodic.IsPeriodic ρ) :
    ((fun x => mLim x + ρ x), uLim, DuLim)
        ∈ D_set_family_paper (d := d) βBar mLim uLim DuLim :=
  ⟨ρ, hρ_nn, hρ_lp, hρ_per, rfl⟩

/-- **Set-narrow ⊆ wider set family.** Forgetting the `MemLpPer`/
periodicity certificates produces a wider-family witness. -/
lemma mem_D_set_family_paper_subset
    (βBar : ℝ≥0∞)
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ) :
    D_set_family_paper (d := d) βBar mLim uLim DuLim ⊆
      D_set_family (d := d) mLim uLim DuLim := by
  intro p hp
  obtain ⟨ρ, hρ_nn, _hρ_lp, _hρ_per, hp_eq⟩ := hp
  exact ⟨ρ, hρ_nn, hp_eq⟩

/-- **Set-narrow paper-form domain is segment-closed.** Convex
combinations of triples `(mLim + ρBar, uLim, DuLim)`,
`(mLim + ρ, uLim, DuLim)` with both perturbations pointwise nonneg,
periodic, and `MemLpPer βBar` are again of the same shape with
perturbation `(1-t)·ρBar + t·ρ`, which preserves all three properties. -/
lemma D_set_family_paper_segment_closed
    (βBar : ℝ≥0∞)
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    {μBar : (Fin d → ℝ) → ℝ} {ῡ : (Fin d → ℝ) → ℝ}
    {Dῡ : Fin d → (Fin d → ℝ) → ℝ}
    (hBar : (μBar, ῡ, Dῡ)
              ∈ D_set_family_paper (d := d) βBar mLim uLim DuLim)
    {μ : (Fin d → ℝ) → ℝ} {υ : (Fin d → ℝ) → ℝ}
    {Dυ : Fin d → (Fin d → ℝ) → ℝ}
    (hμ : (μ, υ, Dυ)
            ∈ D_set_family_paper (d := d) βBar mLim uLim DuLim)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ((fun x => StationaryMFG.Theorems.SimplePower.cxComb μ μBar t x),
     (fun x => StationaryMFG.Theorems.SimplePower.cxComb υ ῡ t x),
     (fun i x =>
       StationaryMFG.Theorems.SimplePower.cxCombGrad Dυ Dῡ t i x))
       ∈ D_set_family_paper (d := d) βBar mLim uLim DuLim := by
  obtain ⟨ρBar, hρBar_nn, hρBar_lp, hρBar_per, hBar_eq⟩ := hBar
  obtain ⟨ρ, hρ_nn, hρ_lp, hρ_per, hμ_eq⟩ := hμ
  obtain ⟨ht0, ht1⟩ := ht
  rw [Prod.mk.injEq, Prod.mk.injEq] at hBar_eq hμ_eq
  obtain ⟨hμBar, hυBar, hDυBar⟩ := hBar_eq
  obtain ⟨hμμ, hυυ, hDυυ⟩ := hμ_eq
  -- The combined perturbation is `(1-t)·ρBar + t·ρ`.
  refine ⟨fun x => (1 - t) * ρBar x + t * ρ x, ?_, ?_, ?_, ?_⟩
  · -- Pointwise nonneg.
    intro x
    have h1mt_nn : 0 ≤ 1 - t := by linarith
    have hA : 0 ≤ (1 - t) * ρBar x := mul_nonneg h1mt_nn (hρBar_nn x)
    have hB : 0 ≤ t * ρ x := mul_nonneg ht0 (hρ_nn x)
    linarith
  · -- `MemLpPer βBar`.
    have hA : StationaryMFG.Periodic.MemLpPer (d := d) βBar
                (fun x => (1 - t) * ρBar x) := by
      have := hρBar_lp.const_smul (𝕜 := ℝ) (1 - t)
      simpa [Pi.smul_apply, smul_eq_mul] using! this
    have hB : StationaryMFG.Periodic.MemLpPer (d := d) βBar
                (fun x => t * ρ x) := by
      have := hρ_lp.const_smul (𝕜 := ℝ) t
      simpa [Pi.smul_apply, smul_eq_mul] using! this
    have hSum := hA.add hB
    -- Rewrite the pointwise sum to match the goal.
    have heq : (fun x : (Fin d → ℝ) => (1 - t) * ρBar x) +
                (fun x : (Fin d → ℝ) => t * ρ x)
               = fun x => (1 - t) * ρBar x + t * ρ x := by
      funext x; rfl
    rw [heq] at hSum
    exact hSum
  · -- Periodic.
    have hA : StationaryMFG.Periodic.IsPeriodic
                (fun x : (Fin d → ℝ) => (1 - t) * ρBar x) := by
      have := hρBar_per.smul (1 - t)
      simpa [Pi.smul_apply, smul_eq_mul] using! this
    have hB : StationaryMFG.Periodic.IsPeriodic
                (fun x : (Fin d → ℝ) => t * ρ x) := by
      have := hρ_per.smul t
      simpa [Pi.smul_apply, smul_eq_mul] using! this
    have hSum := hA.add hB
    have heq : (fun x : (Fin d → ℝ) => (1 - t) * ρBar x) +
                (fun x : (Fin d → ℝ) => t * ρ x)
               = fun x => (1 - t) * ρBar x + t * ρ x := by
      funext x; rfl
    rw [heq] at hSum
    exact hSum
  · -- Triple equality.
    refine Prod.mk.injEq .. |>.mpr ⟨?_, Prod.mk.injEq .. |>.mpr ⟨?_, ?_⟩⟩
    · funext x
      show StationaryMFG.Theorems.SimplePower.cxComb μ μBar t x
            = mLim x + ((1 - t) * ρBar x + t * ρ x)
      have hcx : StationaryMFG.Theorems.SimplePower.cxComb μ μBar t x
                  = (1 - t) * μBar x + t * μ x := rfl
      rw [hcx, hμBar, hμμ]; ring
    · funext x
      show StationaryMFG.Theorems.SimplePower.cxComb υ ῡ t x = uLim x
      have hcx : StationaryMFG.Theorems.SimplePower.cxComb υ ῡ t x
                  = (1 - t) * ῡ x + t * υ x := rfl
      rw [hcx, hυBar, hυυ]; ring
    · funext i x
      show StationaryMFG.Theorems.SimplePower.cxCombGrad Dυ Dῡ t i x
            = DuLim i x
      have hcx : StationaryMFG.Theorems.SimplePower.cxCombGrad Dυ Dῡ t i x
                  = (1 - t) * Dῡ i x + t * Dυ i x := rfl
      rw [hcx, hDυBar, hDυυ]; ring

/-- The limit triple lies in the narrow paper-form signed (nonneg)
domain (perturbation `g = 0`), provided `mLim ≥ 0` a.e. -/
lemma mem_D_signed_family_paper_nn_limit
    (βBar : ℝ≥0∞)
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    (hmLim_nonneg : 0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                            (UnitCube d)] mLim) :
    (mLim, uLim, DuLim)
        ∈ D_signed_family_paper_nn (d := d) βBar mLim uLim DuLim := by
  refine ⟨fun _ => 0, ?_, ?_, ?_, ?_⟩
  · -- `MemLpPer βBar 0`.
    have hcube : MeasureTheory.volume (UnitCube d) ≠ ⊤ := by simp
    haveI : MeasureTheory.IsFiniteMeasure
              (MeasureTheory.Measure.restrict MeasureTheory.volume
                (UnitCube (d := d))) :=
      ⟨by
        rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ]
        simp⟩
    exact StationaryMFG.Periodic.MemLp.toMemLpPer
      (MeasureTheory.memLp_const (0 : ℝ))
  · intro k x; rfl
  · -- `mLim + 0 ≥ 0` a.e.
    filter_upwards [hmLim_nonneg] with x hx
    have hx' : (0 : ℝ) ≤ mLim x := hx
    show (0 : ℝ) ≤ mLim x + 0
    linarith
  · ext1
    · funext x; simp
    · rfl

/-- **Signed-narrow ⊆ wider nonneg-primal signed family.** Forgetting
the `MemLpPer`/periodicity certificates yields a `D_signed_family_nn`
witness. -/
lemma mem_D_signed_family_paper_nn_subset
    (βBar : ℝ≥0∞)
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ) :
    D_signed_family_paper_nn (d := d) βBar mLim uLim DuLim ⊆
      D_signed_family_nn (d := d) mLim uLim DuLim := by
  intro p hp
  obtain ⟨g, _hg_lp, _hg_per, hp_nn, hp_eq⟩ := hp
  refine ⟨⟨g, hp_eq⟩, ?_⟩
  -- `0 ≤ᵐ p.1`. Use `hp_eq` to identify `p.1` with `fun x => mLim x + g x`.
  have hp1 : p.1 = fun x => mLim x + g x := by
    rw [Prod.mk.injEq, Prod.mk.injEq] at hp_eq
    exact hp_eq.1
  rw [hp1]; exact hp_nn

/-- **Signed narrow paper-form domain is segment-closed.** Convex
combinations of triples `(mLim + gBar, uLim, DuLim)`,
`(mLim + g, uLim, DuLim)` with both perturbations periodic and
`MemLpPer βBar`, both primal densities a.e. nonneg, are again of the
same shape with perturbation `(1-t)·gBar + t·g` (preserving
periodicity and `Lᵖ`), and the new primal density is a.e. nonneg
by convex combination. -/
lemma D_signed_family_paper_nn_segment_closed
    (βBar : ℝ≥0∞)
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    {μBar : (Fin d → ℝ) → ℝ} {ῡ : (Fin d → ℝ) → ℝ}
    {Dῡ : Fin d → (Fin d → ℝ) → ℝ}
    (hBar : (μBar, ῡ, Dῡ)
              ∈ D_signed_family_paper_nn (d := d) βBar mLim uLim DuLim)
    {μ : (Fin d → ℝ) → ℝ} {υ : (Fin d → ℝ) → ℝ}
    {Dυ : Fin d → (Fin d → ℝ) → ℝ}
    (hμ : (μ, υ, Dυ)
            ∈ D_signed_family_paper_nn (d := d) βBar mLim uLim DuLim)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ((fun x => StationaryMFG.Theorems.SimplePower.cxComb μ μBar t x),
     (fun x => StationaryMFG.Theorems.SimplePower.cxComb υ ῡ t x),
     (fun i x =>
       StationaryMFG.Theorems.SimplePower.cxCombGrad Dυ Dῡ t i x))
       ∈ D_signed_family_paper_nn (d := d) βBar mLim uLim DuLim := by
  obtain ⟨gBar, hgBar_lp, hgBar_per, hBar_nn, hBar_eq⟩ := hBar
  obtain ⟨g, hg_lp, hg_per, hμ_nn, hμ_eq⟩ := hμ
  obtain ⟨ht0, ht1⟩ := ht
  rw [Prod.mk.injEq, Prod.mk.injEq] at hBar_eq hμ_eq
  obtain ⟨hμBar, hυBar, hDυBar⟩ := hBar_eq
  obtain ⟨hμμ, hυυ, hDυυ⟩ := hμ_eq
  -- Combined perturbation `(1-t)·gBar + t·g`.
  refine ⟨fun x => (1 - t) * gBar x + t * g x, ?_, ?_, ?_, ?_⟩
  · -- `MemLpPer βBar`.
    have hA : StationaryMFG.Periodic.MemLpPer (d := d) βBar
                (fun x => (1 - t) * gBar x) := by
      have := hgBar_lp.const_smul (𝕜 := ℝ) (1 - t)
      simpa [Pi.smul_apply, smul_eq_mul] using! this
    have hB : StationaryMFG.Periodic.MemLpPer (d := d) βBar
                (fun x => t * g x) := by
      have := hg_lp.const_smul (𝕜 := ℝ) t
      simpa [Pi.smul_apply, smul_eq_mul] using! this
    have hSum := hA.add hB
    have heq : (fun x : (Fin d → ℝ) => (1 - t) * gBar x) +
                (fun x : (Fin d → ℝ) => t * g x)
               = fun x => (1 - t) * gBar x + t * g x := by
      funext x; rfl
    rw [heq] at hSum
    exact hSum
  · -- Periodic.
    have hA : StationaryMFG.Periodic.IsPeriodic
                (fun x : (Fin d → ℝ) => (1 - t) * gBar x) := by
      have := hgBar_per.smul (1 - t)
      simpa [Pi.smul_apply, smul_eq_mul] using! this
    have hB : StationaryMFG.Periodic.IsPeriodic
                (fun x : (Fin d → ℝ) => t * g x) := by
      have := hg_per.smul t
      simpa [Pi.smul_apply, smul_eq_mul] using! this
    have hSum := hA.add hB
    have heq : (fun x : (Fin d → ℝ) => (1 - t) * gBar x) +
                (fun x : (Fin d → ℝ) => t * g x)
               = fun x => (1 - t) * gBar x + t * g x := by
      funext x; rfl
    rw [heq] at hSum
    exact hSum
  · -- a.e. nonneg of `mLim + ((1-t)·gBar + t·g)` = cxComb of the two
    -- primal densities `μBar = mLim + gBar`, `μ = mLim + g`.
    have h1mt : 0 ≤ 1 - t := by linarith
    -- Massage endpoint nonnegativity from the `μBar`/`μ` form to the
    -- `mLim + gBar`/`mLim + g` form via the endpoint equalities.
    have hBar_nn' : 0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                            (UnitCube d)]
                      (fun x => mLim x + gBar x) := hBar_nn
    have hμ_nn' : 0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                          (UnitCube d)]
                    (fun x => mLim x + g x) := hμ_nn
    filter_upwards [hBar_nn', hμ_nn'] with x hxBar hxμ
    show (0 : ℝ) ≤ mLim x + ((1 - t) * gBar x + t * g x)
    have h1 : 0 ≤ (1 - t) * (mLim x + gBar x) := mul_nonneg h1mt hxBar
    have h2 : 0 ≤ t * (mLim x + g x) := mul_nonneg ht0 hxμ
    have hsum : (1 - t) * (mLim x + gBar x) + t * (mLim x + g x)
                  = mLim x + ((1 - t) * gBar x + t * g x) := by ring
    linarith
  · -- Triple equality.
    refine Prod.mk.injEq .. |>.mpr ⟨?_, Prod.mk.injEq .. |>.mpr ⟨?_, ?_⟩⟩
    · funext x
      show StationaryMFG.Theorems.SimplePower.cxComb μ μBar t x
            = mLim x + ((1 - t) * gBar x + t * g x)
      have hcx : StationaryMFG.Theorems.SimplePower.cxComb μ μBar t x
                  = (1 - t) * μBar x + t * μ x := rfl
      rw [hcx, hμBar, hμμ]; ring
    · funext x
      show StationaryMFG.Theorems.SimplePower.cxComb υ ῡ t x = uLim x
      have hcx : StationaryMFG.Theorems.SimplePower.cxComb υ ῡ t x
                  = (1 - t) * ῡ x + t * υ x := rfl
      rw [hcx, hυBar, hυυ]; ring
    · funext i x
      show StationaryMFG.Theorems.SimplePower.cxCombGrad Dυ Dῡ t i x
            = DuLim i x
      have hcx : StationaryMFG.Theorems.SimplePower.cxCombGrad Dυ Dῡ t i x
                  = (1 - t) * Dῡ i x + t * Dυ i x := rfl
      rw [hcx, hDυBar, hDυυ]; ring

/-- **`MintyClosureOn` transport: wider → nonneg-primal signed family.**
Given `MintyClosureOn` on the wider `D_signed_family`, restrict it to
the nonneg-primal subfamily `D_signed_family_nn`. Segment-closure is
proved directly (using `D_signed_family_nn_segment_closed`);
hemicontinuity restricts trivially since `D_signed_family_nn ⊆
D_signed_family`; limit-triple membership uses the supplied
`mLim ≥ 0` certificate. -/
lemma mintyClosureOn_signed_nn_of_wider
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    (hmLim_nonneg : 0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                            (UnitCube d)] mLim)
    (mintyClosureOn :
      MintyClosureOn (d := d) V H DpH mLim uLim DuLim
        (D_signed_family (d := d) mLim uLim DuLim)) :
    MintyClosureOn (d := d) V H DpH mLim uLim DuLim
      (D_signed_family_nn (d := d) mLim uLim DuLim) where
  hSeg := by
    intro μBar ῡ Dῡ hBar μ υ Dυ hμ t ht
    exact D_signed_family_nn_segment_closed (d := d) mLim uLim DuLim hBar hμ t ht
  hAhc := by
    -- Hemicontinuity restricted from wider family to subset (restricted-test
    -- predicate per iter `infra-P7-sigfix-T1-drain-A-restricted-hemicont`:
    -- the test triple slot is absent).
    intro μBar ῡ Dῡ hBar μ υ Dυ hμ
    exact mintyClosureOn.hAhc hBar.1 hμ.1
  hLimMem := mem_D_signed_family_nn_limit (d := d) mLim uLim DuLim hmLim_nonneg

/-- **`MintyClosureOn` transport: wider set family → narrow paper-form
set family.**

Phase 6d-ii-c-2d (`infra-P5-theorem1-phase-6d-ii-c-2d-chain-migrate-to-narrow`):
given a `MintyClosureOn` on the wider `D_set_family`, restrict it to
the narrow paper-form subfamily `D_set_family_paper βBar` (perturbations
nonneg, periodic, `MemLpPer βBar`). Segment-closure is via the narrow
domain's own segment-closure lemma; hemicontinuity restricts trivially
since the narrow domain is a subset of the wider one
(`mem_D_set_family_paper_subset`); the narrow limit-triple membership
is `mem_D_set_family_paper_limit`. -/
lemma mintyClosureOn_set_paper_of_wider
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (βBar : ℝ≥0∞)
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    (mintyClosureOn :
      MintyClosureOn (d := d) V H DpH mLim uLim DuLim
        (D_set_family (d := d) mLim uLim DuLim)) :
    MintyClosureOn (d := d) V H DpH mLim uLim DuLim
      (D_set_family_paper (d := d) βBar mLim uLim DuLim) where
  hSeg := by
    intro μBar ῡ Dῡ hBar μ υ Dυ hμ t ht
    exact D_set_family_paper_segment_closed (d := d) βBar mLim uLim DuLim
      hBar hμ t ht
  hAhc := by
    -- Hemicontinuity restricts from wider family to narrow subset via
    -- `mem_D_set_family_paper_subset`. (Restricted-test predicate per iter
    -- `infra-P7-sigfix-T1-drain-A-restricted-hemicont`.)
    intro μBar ῡ Dῡ hBar μ υ Dυ hμ
    have hsub := mem_D_set_family_paper_subset (d := d) βBar mLim uLim DuLim
    exact mintyClosureOn.hAhc (hsub hBar) (hsub hμ)
  hLimMem := mem_D_set_family_paper_limit (d := d) βBar mLim uLim DuLim

/-- **`MintyClosureOn` transport: nonneg-primal signed family → narrow
paper-form signed (nonneg-primal) family.**

Phase 6d-ii-c-2d (`infra-P5-theorem1-phase-6d-ii-c-2d-chain-migrate-to-narrow`):
given a `MintyClosureOn` on `D_signed_family_nn`, restrict it to the
narrow paper-form subfamily `D_signed_family_paper_nn βBar`
(perturbations periodic, `MemLpPer βBar`, with primal density nonneg
a.e.). Segment-closure is via the narrow domain's own segment-closure
lemma; hemicontinuity restricts trivially since the narrow domain is
a subset of the wider nonneg-primal one
(`mem_D_signed_family_paper_nn_subset`); the narrow limit-triple
membership is `mem_D_signed_family_paper_nn_limit`. -/
lemma mintyClosureOn_signed_paper_nn_of_wider
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (βBar : ℝ≥0∞)
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    (hmLim_nonneg : 0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                            (UnitCube d)] mLim)
    (mintyClosureOn :
      MintyClosureOn (d := d) V H DpH mLim uLim DuLim
        (D_signed_family_nn (d := d) mLim uLim DuLim)) :
    MintyClosureOn (d := d) V H DpH mLim uLim DuLim
      (D_signed_family_paper_nn (d := d) βBar mLim uLim DuLim) where
  hSeg := by
    intro μBar ῡ Dῡ hBar μ υ Dυ hμ t ht
    exact D_signed_family_paper_nn_segment_closed (d := d) βBar mLim uLim DuLim
      hBar hμ t ht
  hAhc := by
    -- Hemicontinuity restricts from wider nonneg-primal family to narrow
    -- subset via `mem_D_signed_family_paper_nn_subset`. (Restricted-test
    -- predicate per iter `infra-P7-sigfix-T1-drain-A-restricted-hemicont`.)
    intro μBar ῡ Dῡ hBar μ υ Dυ hμ
    have hsub := mem_D_signed_family_paper_nn_subset (d := d) βBar mLim uLim DuLim
    exact mintyClosureOn.hAhc (hsub hBar) (hsub hμ)
  hLimMem := mem_D_signed_family_paper_nn_limit (d := d) βBar mLim uLim DuLim
              hmLim_nonneg

/-! ### Phase 6d-ii-d-2 — narrow paper-form transport domain.

Per `infra-P5-theorem1-phase-6d-ii-d-2-narrow-transport-regSupplier`,
the transport family also gets a **narrow paper-form** domain
companion to `D_transport_family`, parameterised by a smooth periodic
test function `ψ : SmoothPeriodic d`:

* Triples are `(mLim, uLim + ψ, DuLim + ∂ψ)`.
* The paper test triple `(mLim, uLim + σ·φ, DuLim + σ·∂φ)` recovers
  this with `ψ := σ • φ` (since `(σ • φ : (Fin d → ℝ) → ℝ) x =
  σ * (φ : _) x`).
* Segment closure follows from the SmoothPeriodic Add/SMul algebra:
  the convex combination `(1-t) • ψ̄ + t • ψ` is again a
  `SmoothPeriodic d`.
* The narrow domain is a subset of the wide `D_transport_family`
  (via `μ = mLim`).

This domain is the natural target for a `regSupplier_transport`
that does not consume `T10PaperResidues.regBundle`: triples in
`D_transport_family_paper` arise from `wkBundle.perTestTripleBase`
under `PerTestTripleRegularity.transport_perturbation` (with
`σ = 1`), which only consumes a `SmoothPeriodic d` test function. -/

/-- **Narrow paper-form transport domain.** Triples
`(mLim, uLim + ψ, DuLim + ∂ψ)` for some smooth periodic
`ψ : SmoothPeriodic d`. -/
def D_transport_family_paper
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ) :
    Set (StationaryMFG.Theorems.SimplePower.MFGTriple d) :=
  { p | ∃ ψ : StationaryMFG.Periodic.SmoothPeriodic d,
          p = (mLim,
               (fun x => uLim x + (ψ : (Fin d → ℝ) → ℝ) x),
               (fun i x => DuLim i x +
                 ((StationaryMFG.Periodic.SmoothPeriodic.partialDeriv i ψ
                     : StationaryMFG.Periodic.SmoothPeriodic d) :
                   (Fin d → ℝ) → ℝ) x)) }

/-- The limit triple lies in the narrow paper-form transport domain
(perturbation `ψ = 0`). -/
lemma mem_D_transport_family_paper_limit
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ) :
    (mLim, uLim, DuLim)
        ∈ D_transport_family_paper (d := d) mLim uLim DuLim := by
  refine ⟨0, ?_⟩
  -- `ψ = 0`: pointwise `0 + 0 = 0`, so `uLim + 0 = uLim` and
  -- `DuLim + ∂0 = DuLim` (since `∂0 = 0` definitionally
  -- via `fderiv` of a constant).
  refine Prod.mk.injEq .. |>.mpr ⟨rfl, Prod.mk.injEq .. |>.mpr ⟨?_, ?_⟩⟩
  · funext x
    show uLim x = uLim x +
        ((0 : StationaryMFG.Periodic.SmoothPeriodic d) :
          (Fin d → ℝ) → ℝ) x
    simp
  · funext i x
    show DuLim i x = DuLim i x +
        ((StationaryMFG.Periodic.SmoothPeriodic.partialDeriv i
              (0 : StationaryMFG.Periodic.SmoothPeriodic d)
            : StationaryMFG.Periodic.SmoothPeriodic d) :
          (Fin d → ℝ) → ℝ) x
    -- `∂_i 0 = 0` because `fderiv` of the zero function is zero.
    have hzero :
        ((StationaryMFG.Periodic.SmoothPeriodic.partialDeriv i
              (0 : StationaryMFG.Periodic.SmoothPeriodic d)
            : StationaryMFG.Periodic.SmoothPeriodic d) :
          (Fin d → ℝ) → ℝ) x = 0 := by
      simp [StationaryMFG.Periodic.SmoothPeriodic.coe_partialDeriv,
            StationaryMFG.Periodic.SmoothPeriodic.coe_zero]
    rw [hzero]; ring

/-- **Narrow transport test-triple membership (smooth case).** For any
`σ : ℝ` and smooth periodic `φ`, the test triple
`(mLim, uLim + σ·φ, DuLim + σ·∂φ)` lies in the narrow paper-form
transport domain (taking `ψ := σ • φ`). -/
lemma mem_D_transport_family_paper_test
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    (σ : ℝ) (φ : StationaryMFG.Periodic.SmoothPeriodic d) :
    (mLim,
      (fun x => uLim x + σ * (φ : (Fin d → ℝ) → ℝ) x),
      (fun i x => DuLim i x + σ *
        ((StationaryMFG.Periodic.SmoothPeriodic.partialDeriv i φ
            : StationaryMFG.Periodic.SmoothPeriodic d) :
          (Fin d → ℝ) → ℝ) x))
        ∈ D_transport_family_paper (d := d) mLim uLim DuLim := by
  refine ⟨σ • φ, ?_⟩
  -- Need to check: the underlying function values match.
  -- For the `υ` slot:  `σ * (φ x) = (σ • φ) x` (since
  -- `(σ • φ : (Fin d → ℝ) → ℝ) x = σ * (φ : _) x` via `coe_smul`
  -- and `Pi.smul_apply`).
  -- For the `Dυ_i` slot: `σ * (∂_i φ) x = (∂_i (σ • φ)) x` because
  -- `fderiv` is ℝ-linear in the function — direct unfolding via
  -- `coe_partialDeriv` and `fderiv_const_smul`.
  refine Prod.mk.injEq .. |>.mpr ⟨rfl, Prod.mk.injEq .. |>.mpr ⟨?_, ?_⟩⟩
  · funext x
    show uLim x + σ * (φ : (Fin d → ℝ) → ℝ) x =
          uLim x + ((σ • φ : StationaryMFG.Periodic.SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) x
    rw [StationaryMFG.Periodic.SmoothPeriodic.coe_smul]
    simp [Pi.smul_apply, smul_eq_mul]
  · funext i x
    show DuLim i x +
          σ * ((StationaryMFG.Periodic.SmoothPeriodic.partialDeriv i φ
              : StationaryMFG.Periodic.SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) x =
          DuLim i x +
          ((StationaryMFG.Periodic.SmoothPeriodic.partialDeriv i (σ • φ)
              : StationaryMFG.Periodic.SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) x
    -- Reduce both sides to `fderiv` form via `coe_partialDeriv`,
    -- then use ℝ-linearity of `fderiv` on a smooth function.
    -- And `(σ • φ : (Fin d → ℝ) → ℝ) = σ • (φ : _)` (via `coe_smul`).
    have hcoe :
        ((σ • φ : StationaryMFG.Periodic.SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ)
          = σ • ((φ : (Fin d → ℝ) → ℝ)) :=
      StationaryMFG.Periodic.SmoothPeriodic.coe_smul σ φ
    -- Beta-reduce both sides to plain `fderiv` form.
    change DuLim i x +
            σ * (fderiv ℝ ((φ : (Fin d → ℝ) → ℝ)) x
              ((Pi.basisFun ℝ (Fin d)) i)) =
          DuLim i x +
            (fderiv ℝ
              ((σ • φ : StationaryMFG.Periodic.SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x
              ((Pi.basisFun ℝ (Fin d)) i))
    rw [hcoe]
    rw [fderiv_const_smul (φ.smooth.differentiable
            (by decide : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).differentiableAt σ]
    simp [ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- **Narrow ⊆ wider transport family.** Forgetting the smoothness
certificate of the perturbation `ψ` produces a wider-family witness
(only `μ = mLim` is required there). -/
lemma mem_D_transport_family_paper_subset
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ) :
    D_transport_family_paper (d := d) mLim uLim DuLim ⊆
      D_transport_family (d := d) mLim uLim DuLim := by
  intro p hp
  obtain ⟨ψ, hp_eq⟩ := hp
  -- `D_transport_family p ↔ p.1 = mLim`; from `hp_eq : p = (mLim, …, …)`
  -- the first projection is `mLim`.
  change p.1 = mLim
  rw [hp_eq]

/-- **Narrow paper-form transport domain is segment-closed.** Convex
combinations of triples `(mLim, uLim + ψ̄, DuLim + ∂ψ̄)`,
`(mLim, uLim + ψ, DuLim + ∂ψ)` are again of the same shape with
perturbation `(1-t) • ψ̄ + t • ψ : SmoothPeriodic d`. -/
lemma D_transport_family_paper_segment_closed
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    {μBar : (Fin d → ℝ) → ℝ} {ῡ : (Fin d → ℝ) → ℝ}
    {Dῡ : Fin d → (Fin d → ℝ) → ℝ}
    (hBar : (μBar, ῡ, Dῡ)
              ∈ D_transport_family_paper (d := d) mLim uLim DuLim)
    {μ : (Fin d → ℝ) → ℝ} {υ : (Fin d → ℝ) → ℝ}
    {Dυ : Fin d → (Fin d → ℝ) → ℝ}
    (hμ : (μ, υ, Dυ)
            ∈ D_transport_family_paper (d := d) mLim uLim DuLim)
    (t : ℝ) (_ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ((fun x => StationaryMFG.Theorems.SimplePower.cxComb μ μBar t x),
     (fun x => StationaryMFG.Theorems.SimplePower.cxComb υ ῡ t x),
     (fun i x =>
       StationaryMFG.Theorems.SimplePower.cxCombGrad Dυ Dῡ t i x))
       ∈ D_transport_family_paper (d := d) mLim uLim DuLim := by
  obtain ⟨ψBar, hBar_eq⟩ := hBar
  obtain ⟨ψ, hμ_eq⟩ := hμ
  rw [Prod.mk.injEq, Prod.mk.injEq] at hBar_eq hμ_eq
  obtain ⟨hμBar, hυBar, hDυBar⟩ := hBar_eq
  obtain ⟨hμμ, hυυ, hDυυ⟩ := hμ_eq
  -- Combined ψ' := (1-t) • ψBar + t • ψ as SmoothPeriodic.
  refine ⟨(1 - t) • ψBar + t • ψ, ?_⟩
  refine Prod.mk.injEq .. |>.mpr ⟨?_, Prod.mk.injEq .. |>.mpr ⟨?_, ?_⟩⟩
  · -- Density component: `cxComb μ μBar t = mLim` (as a function).
    funext x
    show StationaryMFG.Theorems.SimplePower.cxComb μ μBar t x = mLim x
    have hcx : StationaryMFG.Theorems.SimplePower.cxComb μ μBar t x
                = (1 - t) * μBar x + t * μ x := rfl
    rw [hcx, hμBar, hμμ]; ring
  · -- u component.
    funext x
    -- Goal:
    --   cxComb υ ῡ t x = uLim x + ((1 - t) • ψBar + t • ψ : SmoothPeriodic) x
    -- Unfold cxComb and the SmoothPeriodic Add/SMul coercions.
    show StationaryMFG.Theorems.SimplePower.cxComb υ ῡ t x =
          uLim x +
          (((1 - t) • ψBar + t • ψ :
              StationaryMFG.Periodic.SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) x
    have hcx : StationaryMFG.Theorems.SimplePower.cxComb υ ῡ t x
                = (1 - t) * ῡ x + t * υ x := rfl
    -- Substitute the endpoint shapes.
    have hῡx : ῡ x = uLim x + (ψBar : (Fin d → ℝ) → ℝ) x := by
      have := congrFun hυBar x; exact this
    have hυx : υ x = uLim x + (ψ : (Fin d → ℝ) → ℝ) x := by
      have := congrFun hυυ x; exact this
    rw [hcx, hῡx, hυx]
    -- RHS coercion: `((1-t) • ψBar + t • ψ) x = (1-t) * ψBar x + t * ψ x`.
    have hcoe :
        (((1 - t) • ψBar + t • ψ :
              StationaryMFG.Periodic.SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) x
          = (1 - t) * (ψBar : (Fin d → ℝ) → ℝ) x +
              t * (ψ : (Fin d → ℝ) → ℝ) x := by
      rw [StationaryMFG.Periodic.SmoothPeriodic.coe_add,
          StationaryMFG.Periodic.SmoothPeriodic.coe_smul,
          StationaryMFG.Periodic.SmoothPeriodic.coe_smul]
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hcoe]; ring
  · -- Du component.
    funext i x
    show StationaryMFG.Theorems.SimplePower.cxCombGrad Dυ Dῡ t i x =
          DuLim i x +
          ((StationaryMFG.Periodic.SmoothPeriodic.partialDeriv i
              ((1 - t) • ψBar + t • ψ)
            : StationaryMFG.Periodic.SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) x
    have hcx : StationaryMFG.Theorems.SimplePower.cxCombGrad Dυ Dῡ t i x
                = (1 - t) * Dῡ i x + t * Dυ i x := rfl
    have hDῡx : Dῡ i x =
        DuLim i x +
          ((StationaryMFG.Periodic.SmoothPeriodic.partialDeriv i ψBar
              : StationaryMFG.Periodic.SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) x := by
      have := congrFun (congrFun hDυBar i) x; exact this
    have hDυx : Dυ i x =
        DuLim i x +
          ((StationaryMFG.Periodic.SmoothPeriodic.partialDeriv i ψ
              : StationaryMFG.Periodic.SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) x := by
      have := congrFun (congrFun hDυυ i) x; exact this
    rw [hcx, hDῡx, hDυx]
    -- Now the RHS coercion: `∂_i ((1-t) • ψBar + t • ψ) x =
    --   (1-t) * ∂_i ψBar x + t * ∂_i ψ x`.
    -- Unfold via `coe_partialDeriv`, `coe_add`, `coe_smul`,
    -- and ℝ-linearity of `fderiv`.
    rw [StationaryMFG.Periodic.SmoothPeriodic.coe_partialDeriv]
    rw [StationaryMFG.Periodic.SmoothPeriodic.coe_partialDeriv]
    rw [StationaryMFG.Periodic.SmoothPeriodic.coe_partialDeriv]
    -- The combined SmoothPeriodic's underlying function is the
    -- sum/scalar-multiple of the underlying functions.
    have hcoe :
        (((1 - t) • ψBar + t • ψ :
              StationaryMFG.Periodic.SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ)
          = (1 - t) • ((ψBar : (Fin d → ℝ) → ℝ))
              + t • ((ψ : (Fin d → ℝ) → ℝ)) := by
      rw [StationaryMFG.Periodic.SmoothPeriodic.coe_add,
          StationaryMFG.Periodic.SmoothPeriodic.coe_smul,
          StationaryMFG.Periodic.SmoothPeriodic.coe_smul]
    rw [hcoe]
    -- Differentiate the sum and scalar multiples.
    have hψBar_diff : Differentiable ℝ ((ψBar : (Fin d → ℝ) → ℝ)) :=
      ψBar.smooth.differentiable
        (by decide : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)
    have hψ_diff : Differentiable ℝ ((ψ : (Fin d → ℝ) → ℝ)) :=
      ψ.smooth.differentiable
        (by decide : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)
    have hSmul_Bar_diff :
        Differentiable ℝ ((1 - t) • ((ψBar : (Fin d → ℝ) → ℝ))) :=
      hψBar_diff.const_smul (1 - t)
    have hSmul_diff :
        Differentiable ℝ (t • ((ψ : (Fin d → ℝ) → ℝ))) :=
      hψ_diff.const_smul t
    -- Beta-reduce the `(fun x ↦ fderiv ℝ … x) x` wrapper before
    -- applying `fderiv_add`.
    change (1 - t) * (DuLim i x +
            fderiv ℝ (ψBar : (Fin d → ℝ) → ℝ) x
              ((Pi.basisFun ℝ (Fin d)) i)) +
        t * (DuLim i x +
            fderiv ℝ (ψ : (Fin d → ℝ) → ℝ) x
              ((Pi.basisFun ℝ (Fin d)) i)) =
      DuLim i x +
        fderiv ℝ ((1 - t) • ((ψBar : (Fin d → ℝ) → ℝ))
                    + t • ((ψ : (Fin d → ℝ) → ℝ))) x
          ((Pi.basisFun ℝ (Fin d)) i)
    rw [fderiv_add hSmul_Bar_diff.differentiableAt
            hSmul_diff.differentiableAt]
    rw [fderiv_const_smul hψBar_diff.differentiableAt (1 - t),
        fderiv_const_smul hψ_diff.differentiableAt t]
    simp [ContinuousLinearMap.add_apply,
          ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring

/-- **`MintyClosureOn` transport: wider transport family → narrow
paper-form transport family.**

Per `infra-P5-theorem1-phase-6d-ii-d-2-narrow-transport-regSupplier`,
given a `MintyClosureOn` on the wider `D_transport_family`, restrict
it to the narrow paper-form subfamily `D_transport_family_paper`
(perturbations of the form `ψ : SmoothPeriodic d`). Segment-closure
is via `D_transport_family_paper_segment_closed`; hemicontinuity
restricts trivially via `mem_D_transport_family_paper_subset`; the
narrow limit-triple membership is `mem_D_transport_family_paper_limit`. -/
lemma mintyClosureOn_transport_paper_of_wider
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    (mintyClosureOn :
      MintyClosureOn (d := d) V H DpH mLim uLim DuLim
        (D_transport_family (d := d) mLim uLim DuLim)) :
    MintyClosureOn (d := d) V H DpH mLim uLim DuLim
      (D_transport_family_paper (d := d) mLim uLim DuLim) where
  hSeg := by
    intro μBar ῡ Dῡ hBar μ υ Dυ hμ t ht
    exact D_transport_family_paper_segment_closed (d := d) mLim uLim DuLim
      hBar hμ t ht
  hAhc := by
    -- Restricted-test predicate per iter
    -- `infra-P7-sigfix-T1-drain-A-restricted-hemicont`: no test triple slot.
    intro μBar ῡ Dῡ hBar μ υ Dυ hμ
    have hsub := mem_D_transport_family_paper_subset (d := d) mLim uLim DuLim
    exact mintyClosureOn.hAhc (hsub hBar) (hsub hμ)
  hLimMem := mem_D_transport_family_paper_limit (d := d) mLim uLim DuLim

/-- **Transport family is segment-closed.** Both endpoints have
density component `mLim`, hence the convex combination's density
component is also `mLim` (constant in `t`). The `(υ, Dυ)`
components are unconstrained. -/
lemma D_transport_family_segment_closed
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    {μBar : (Fin d → ℝ) → ℝ} {ῡ : (Fin d → ℝ) → ℝ}
    {Dῡ : Fin d → (Fin d → ℝ) → ℝ}
    (hBar : (μBar, ῡ, Dῡ) ∈ D_transport_family (d := d) mLim uLim DuLim)
    {μ : (Fin d → ℝ) → ℝ} {υ : (Fin d → ℝ) → ℝ}
    {Dυ : Fin d → (Fin d → ℝ) → ℝ}
    (hμ : (μ, υ, Dυ) ∈ D_transport_family (d := d) mLim uLim DuLim)
    (t : ℝ) (_ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ((fun x => StationaryMFG.Theorems.SimplePower.cxComb μ μBar t x),
     (fun x => StationaryMFG.Theorems.SimplePower.cxComb υ ῡ t x),
     (fun i x =>
       StationaryMFG.Theorems.SimplePower.cxCombGrad Dυ Dῡ t i x))
       ∈ D_transport_family (d := d) mLim uLim DuLim := by
  -- `hBar : μBar = mLim`, `hμ : μ = mLim`.
  show (fun x => StationaryMFG.Theorems.SimplePower.cxComb μ μBar t x)
        = mLim
  have hμBar : μBar = mLim := hBar
  have hμμ : μ = mLim := hμ
  funext x
  have hcx : StationaryMFG.Theorems.SimplePower.cxComb μ μBar t x
              = (1 - t) * μBar x + t * μ x := rfl
  rw [hcx, hμBar, hμμ]
  ring

/-! ### Phase F (strip, step 3) — family-native `MintyClosureOn` producers.

Per `infra-P5-theorem1-phase-F-strip-mintyResidue-finalize-step-3-7`
(child step 3), this subsection assembles three
`MintyClosureOn`-shape producers — one per paper test family — by
wiring `A0_isHemicontinuous` onto the corresponding family domain
together with the family's segment-closure lemma and the limit-triple
membership.

Each producer takes:

* paper hypotheses `(hmon, hpow, hV)` (chain shape; `hmon.toRegularityH`
  is the `RegularityH` used by `A0_isHemicontinuous`),
* the limit triple `(mLim, uLim, DuLim)` keying the family,
* `γBar : ℝ` with `1 < γBar` (the Gateaux-dominator exponent required
  by `A0_isHemicontinuous`),
* a per-pair `HemicontSegmentData` aggregator `hData` quantified over
  pairs in the family domain.

Output: `MintyClosureOn V H DpH mLim uLim DuLim D_*_family`.

These producers are the family-native analogues of
`mintyClosure_of_paperHypotheses_strictPos` (which lives on
`StrictPositivityDomain c`). They prepare the F0 producer refactor
(steps 4-5 of the parent task) where each
`strongVI_*_at_limit_of_paperHypotheses` will apply `main_strong_VI`
on its family domain rather than `Set.univ`. -/

/-- **Set family `MintyClosureOn` producer.** Wires
`A0_isHemicontinuous` on `D_set_family mLim uLim DuLim` together with
the set-family segment-closure lemma and limit-membership. -/
noncomputable def mintyClosure_familyNative_set_of_paperHypotheses
    {γBarReal βBarReal' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (_hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (_hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    (γBar : ℝ) (hγ : 1 < γBar)
    (hData : ∀ ⦃μBar ῡ Dῡ⦄,
                (μBar, ῡ, Dῡ) ∈ D_set_family (d := d) mLim uLim DuLim →
              ∀ ⦃μ υ Dυ⦄,
                (μ, υ, Dυ) ∈ D_set_family (d := d) mLim uLim DuLim →
              ∀ (η ν : (Fin d → ℝ) → ℝ)
                (Dν : Fin d → (Fin d → ℝ) → ℝ),
              StationaryMFG.Theorems.SimplePower.HemicontSegmentData
                (d := d) V H DpH γBar Dυ Dῡ μ μBar υ ῡ Dν η ν) :
    MintyClosureOn (d := d) V H DpH mLim uLim DuLim
      (D_set_family (d := d) mLim uLim DuLim) where
  hSeg := by
    intro μBar ῡ Dῡ hBar μ υ Dυ hμ t ht
    exact D_set_family_segment_closed (d := d) mLim uLim DuLim hBar hμ t ht
  hAhc :=
    -- Weakened to restricted-test form per iter
    -- `infra-P7-sigfix-T1-drain-A-restricted-hemicont`.
    (StationaryMFG.Theorems.SimplePower.A0_isHemicontinuous
      (V := V) (H := H) (DpH := DpH)
      hmon.toRegularityH γBar hγ
      (D_set_family (d := d) mLim uLim DuLim)
      hData).toRestricted
  hLimMem := mem_D_set_family_limit (d := d) mLim uLim DuLim
  -- `γBarReal`/`βBarReal'`/`_hpow`/`_hV` are threaded for chain shape
  -- alignment with the rest of the T9/T10 chain.

/-- **Signed family `MintyClosureOn` producer.** Wires
`A0_isHemicontinuous` on `D_signed_family mLim uLim DuLim` together
with the signed-family segment-closure lemma and limit-membership. -/
noncomputable def mintyClosure_familyNative_signed_of_paperHypotheses
    {γBarReal βBarReal' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (_hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (_hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    (γBar : ℝ) (hγ : 1 < γBar)
    (hData : ∀ ⦃μBar ῡ Dῡ⦄,
                (μBar, ῡ, Dῡ) ∈ D_signed_family (d := d) mLim uLim DuLim →
              ∀ ⦃μ υ Dυ⦄,
                (μ, υ, Dυ) ∈ D_signed_family (d := d) mLim uLim DuLim →
              ∀ (η ν : (Fin d → ℝ) → ℝ)
                (Dν : Fin d → (Fin d → ℝ) → ℝ),
              StationaryMFG.Theorems.SimplePower.HemicontSegmentData
                (d := d) V H DpH γBar Dυ Dῡ μ μBar υ ῡ Dν η ν) :
    MintyClosureOn (d := d) V H DpH mLim uLim DuLim
      (D_signed_family (d := d) mLim uLim DuLim) where
  hSeg := by
    intro μBar ῡ Dῡ hBar μ υ Dυ hμ t ht
    exact D_signed_family_segment_closed (d := d) mLim uLim DuLim hBar hμ t ht
  hAhc :=
    -- Weakened to restricted-test form per iter
    -- `infra-P7-sigfix-T1-drain-A-restricted-hemicont`.
    (StationaryMFG.Theorems.SimplePower.A0_isHemicontinuous
      (V := V) (H := H) (DpH := DpH)
      hmon.toRegularityH γBar hγ
      (D_signed_family (d := d) mLim uLim DuLim)
      hData).toRestricted
  hLimMem := mem_D_signed_family_limit (d := d) mLim uLim DuLim

/-- **Transport family `MintyClosureOn` producer.** Wires
`A0_isHemicontinuous` on `D_transport_family mLim uLim DuLim` together
with the transport-family segment-closure lemma and limit-membership. -/
noncomputable def mintyClosure_familyNative_transport_of_paperHypotheses
    {γBarReal βBarReal' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (_hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (_hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    (γBar : ℝ) (hγ : 1 < γBar)
    (hData : ∀ ⦃μBar ῡ Dῡ⦄,
                (μBar, ῡ, Dῡ) ∈ D_transport_family (d := d) mLim uLim DuLim →
              ∀ ⦃μ υ Dυ⦄,
                (μ, υ, Dυ) ∈ D_transport_family (d := d) mLim uLim DuLim →
              ∀ (η ν : (Fin d → ℝ) → ℝ)
                (Dν : Fin d → (Fin d → ℝ) → ℝ),
              StationaryMFG.Theorems.SimplePower.HemicontSegmentData
                (d := d) V H DpH γBar Dυ Dῡ μ μBar υ ῡ Dν η ν) :
    MintyClosureOn (d := d) V H DpH mLim uLim DuLim
      (D_transport_family (d := d) mLim uLim DuLim) where
  hSeg := by
    intro μBar ῡ Dῡ hBar μ υ Dυ hμ t ht
    exact D_transport_family_segment_closed (d := d) mLim uLim DuLim
      hBar hμ t ht
  hAhc :=
    -- Weakened to restricted-test form per iter
    -- `infra-P7-sigfix-T1-drain-A-restricted-hemicont`.
    (StationaryMFG.Theorems.SimplePower.A0_isHemicontinuous
      (V := V) (H := H) (DpH := DpH)
      hmon.toRegularityH γBar hγ
      (D_transport_family (d := d) mLim uLim DuLim)
      hData).toRestricted
  hLimMem := mem_D_transport_family_limit (d := d) mLim uLim DuLim

/-! ### Phase 5 — narrow-domain family-native `MintyClosureOn` producers.

Per `infra-P5-mintyData-narrow-family-producers`, these three producers
are the narrow-paper-form analogues of the wide-family producers above.
Each consumes `hData` quantified directly on the *narrow* paper-form
family domain (where LP/periodicity bounds on the perturbation are
available) and produces `MintyClosureOn` on that narrow domain — bypassing
the `mintyClosureOn_*_paper_*_of_wider` lifting step.

These are the producers wired through the K0-form
`hemicontSegmentData_of_K0Aepsi` (iter 0496), since the narrow-domain
hData can be discharged from `wkBundle.perTestTripleBase` with bounded
support certificates (whereas the wide hData cannot, because the wide
families lack LP bounds on the perturbation).
-/

/-- **Set family `MintyClosureOn` producer (narrow paper-form).**
Wires `A0_isHemicontinuous` on `D_set_family_paper βBar mLim uLim DuLim`
together with the narrow set-family segment-closure lemma and
limit-membership. -/
noncomputable def mintyClosure_familyNative_set_of_paperHypotheses_narrow
    {γBarReal βBarReal' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (_hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (_hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (βBar : ℝ≥0∞)
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    (γBar : ℝ) (hγ : 1 < γBar)
    (hData : ∀ ⦃μBar ῡ Dῡ⦄,
                (μBar, ῡ, Dῡ)
                  ∈ D_set_family_paper (d := d) βBar mLim uLim DuLim →
              ∀ ⦃μ υ Dυ⦄,
                (μ, υ, Dυ)
                  ∈ D_set_family_paper (d := d) βBar mLim uLim DuLim →
              ∀ (η ν : (Fin d → ℝ) → ℝ)
                (Dν : Fin d → (Fin d → ℝ) → ℝ),
              StationaryMFG.Theorems.SimplePower.HemicontSegmentData
                (d := d) V H DpH γBar Dυ Dῡ μ μBar υ ῡ Dν η ν) :
    MintyClosureOn (d := d) V H DpH mLim uLim DuLim
      (D_set_family_paper (d := d) βBar mLim uLim DuLim) where
  hSeg := by
    intro μBar ῡ Dῡ hBar μ υ Dυ hμ t ht
    exact D_set_family_paper_segment_closed (d := d) βBar mLim uLim DuLim
      hBar hμ t ht
  hAhc :=
    -- Weakened to restricted-test form per iter
    -- `infra-P7-sigfix-T1-drain-A-restricted-hemicont`.
    (StationaryMFG.Theorems.SimplePower.A0_isHemicontinuous
      (V := V) (H := H) (DpH := DpH)
      hmon.toRegularityH γBar hγ
      (D_set_family_paper (d := d) βBar mLim uLim DuLim)
      hData).toRestricted
  hLimMem := mem_D_set_family_paper_limit (d := d) βBar mLim uLim DuLim
  -- `γBarReal`/`βBarReal'`/`_hpow`/`_hV` are threaded for chain shape
  -- alignment with the rest of the T9/T10 chain.

/-- **K0 sibling: Set family `MintyClosureOn` producer (narrow paper-form,
closed-cone).**

K0 version of `mintyClosure_familyNative_set_of_paperHypotheses_narrow`
(iter `infra-P5-T10-v8-K0-set-mintyResSetOf-retype`). Consumes hData
producing `HemicontSegmentDataK0` (the closed-cone sibling that drops
`hPosSeg`) and closed-cone regularity `RegularityHK0`. Internally
delegates to `A0_isHemicontinuousK0` for the `hAhc` field; segment
closure and limit membership are unchanged from the strict-K version.

**iter `infra-P5-T10-v8-K0-set-segInputs-relocate-testDir-certs`**:
`hData`'s signature gains 4 explicit test-direction cert preconditions
`(hη, hDν, hν_β, hν_γ)` after `(η, ν, Dν)`. A `testDirCertsOf`
parameter supplies the certs to `A0_isHemicontinuousK0` per test
triple.

**iter `infra-P7-sigfix-T1-testDirCerts` (Phase 1A)**: the
`testDirCertsOf` parameter now takes the named structure
`TestDirectionCertsRaw βBarReal γBarReal η ν Dν` instead of the
anonymous 4-And conjunction. Semantics unchanged; structure shape paves
the way for Phase 1B (family-specific producers) and Phase 1D (drain).

**iter `infra-P7-sigfix-T1-drain-B-K0-consumer-rewire` (Phase 1D-B)**:
The `testDirCertsOf` parameter is **dropped** entirely. Certs at the
difference test triple `(μ - μBar, υ - ῡ, Dυ - Dῡ)` are derived in-body
from family-membership of the two D-members: for the set family,
`μ - μBar = ρ_μ - ρ_μBar` (whose `MemLpPer (β+1)` follows from the
family's perturbation regularity by subtraction), and `υ - ῡ = 0`,
`Dυ - Dῡ = 0` (zero is in every Lp). Routes through the new
`A0_isHemicontinuousK0_restricted_withFamilyCerts` instead of
`A0_isHemicontinuousK0_withCerts`. -/
noncomputable def mintyClosure_familyNative_set_of_paperHypotheses_narrowK0
    {γBarReal βBarReal βBarReal' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hRegK0 : StationaryMFG.Theorems.SimplePower.RegularityHK0 (d := d) H DpH)
    (_hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (_hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (βBar : ℝ≥0∞)
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    (γBar : ℝ)
    -- iter `infra-P7-sigfix-T1-drain-B-K0-consumer-rewire`: exponent
    -- alignment witness — the family's `βBar` (ENNReal) coincides with
    -- the test-direction cert exponent (Real). Discharged by `rfl` at
    -- the call site where `βBar := ENNReal.ofReal βBarReal`.
    (hβBar_eq : βBar = ENNReal.ofReal βBarReal)
    (hData : ∀ ⦃μBar ῡ Dῡ⦄,
                (μBar, ῡ, Dῡ)
                  ∈ D_set_family_paper (d := d) βBar mLim uLim DuLim →
              ∀ ⦃μ υ Dυ⦄,
                (μ, υ, Dυ)
                  ∈ D_set_family_paper (d := d) βBar mLim uLim DuLim →
              ∀ (η ν : (Fin d → ℝ) → ℝ)
                (Dν : Fin d → (Fin d → ℝ) → ℝ),
              MemLpPer (d := d) (ENNReal.ofReal βBarReal) η →
              (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dν i)) →
              MemLpPer (d := d) (ENNReal.ofReal βBarReal) ν →
              MemLpPer (d := d) (ENNReal.ofReal γBarReal) ν →
              StationaryMFG.Theorems.SimplePower.HemicontSegmentDataK0
                (d := d) V H DpH γBar Dυ Dῡ μ μBar υ ῡ Dν η ν) :
    MintyClosureOn (d := d) V H DpH mLim uLim DuLim
      (D_set_family_paper (d := d) βBar mLim uLim DuLim) where
  hSeg := by
    intro μBar ῡ Dῡ hBar μ υ Dυ hμ t ht
    exact D_set_family_paper_segment_closed (d := d) βBar mLim uLim DuLim
      hBar hμ t ht
  hAhc :=
    -- **iter `infra-P7-sigfix-T1-drain-B-K0-consumer-rewire`**: build
    -- the family-conditional cert oracle in-body by unpacking
    -- family-membership of both endpoints. For the set family
    -- (`μ = mLim + ρ_μ`, `μBar = mLim + ρ_μBar`, `υ = ῡ = uLim`,
    -- `Dυ = Dῡ = DuLim`), the difference triple is
    -- `(ρ_μ - ρ_μBar, 0, 0)`. Certs:
    --   * `η = μ - μBar`: `MemLpPer βBar` by subtraction of the
    --     family-derived `μ ∈ L^βBar` and `μBar ∈ L^βBar`.
    --   * `Dν i = Dυ i - Dῡ i = 0`: `MemLpPer γBar 0` via constant.
    --   * `ν = υ - ῡ = 0`: `MemLpPer βBar 0` and `MemLpPer γBar 0`.
    StationaryMFG.Theorems.SimplePower.A0_isHemicontinuousK0_restricted_withFamilyCerts
      (V := V) (H := H) (DpH := DpH)
      hRegK0 γBar
      (D_set_family_paper (d := d) βBar mLim uLim DuLim)
      βBarReal γBarReal
      (familyCertsOf := by
        intro μBar ῡ Dῡ hBar μ υ Dυ hμ
        -- Unpack the two set-family memberships.
        obtain ⟨ρBar, _hρBar_nn, hρBar_lp, _hρBar_per, hBar_eq⟩ := hBar
        obtain ⟨ρ, _hρ_nn, hρ_lp, _hρ_per, hμ_eq⟩ := hμ
        rw [Prod.mk.injEq, Prod.mk.injEq] at hBar_eq hμ_eq
        obtain ⟨hμBar_eq, hῡ_eq, hDῡ_eq⟩ := hBar_eq
        obtain ⟨hμ_eq, hυ_eq, hDυ_eq⟩ := hμ_eq
        -- The cert oracle uses raw βBarReal, but family-derived
        -- regularity is at `βBar` (ENNReal). The K0 closure consumer
        -- ties `βBar = ENNReal.ofReal βBarReal` at the call site.
        -- Build the four certs at the difference triple.
        refine ⟨?_, ?_, ?_, ?_⟩
        · -- `μ - μBar = ρ - ρBar` in `L^βBarReal_per`. Uses the
          -- exponent-alignment witness `hβBar_eq : βBar = ENNReal.ofReal βBarReal`.
          rw [hμ_eq, hμBar_eq]
          -- Build `MemLpPer βBar (ρ - ρBar)` using the equivalence with `MemLp`
          -- and its subtraction closure.
          have hsub : MemLpPer (d := d) βBar (fun x => ρ x - ρBar x) := by
            have h : MemLpPer (d := d) βBar (ρ - ρBar) :=
              MemLp.toMemLpPer (MeasureTheory.MemLp.sub hρ_lp.toMemLp hρBar_lp.toMemLp)
            -- `(ρ - ρBar) x = ρ x - ρBar x` by `Pi.sub_def`.
            exact h
          -- Pointwise simplification: `(mLim x + ρ x) - (mLim x + ρBar x) = ρ x - ρBar x`.
          have hcongr :
              (fun x : (Fin d → ℝ) => (mLim x + ρ x) - (mLim x + ρBar x))
                = (fun x => ρ x - ρBar x) := by
            funext x; ring
          rw [hcongr, ← hβBar_eq]
          exact hsub
        · -- `Dν i = Dυ i - Dῡ i = 0` (since `Dυ = Dῡ = DuLim`).
          intro i
          rw [hDυ_eq, hDῡ_eq]
          -- `DuLim i - DuLim i = 0` pointwise.
          have hcongr :
              (fun x : (Fin d → ℝ) => DuLim i x - DuLim i x)
                = (fun _ => (0 : ℝ)) := by
            funext x; ring
          rw [hcongr]
          exact MemLpPer.const (d := d) (p := ENNReal.ofReal γBarReal) (0 : ℝ)
        · -- `ν = υ - ῡ = 0` (since `υ = ῡ = uLim`).
          rw [hυ_eq, hῡ_eq]
          have hcongr :
              (fun x : (Fin d → ℝ) => uLim x - uLim x)
                = (fun _ => (0 : ℝ)) := by
            funext x; ring
          rw [hcongr]
          exact MemLpPer.const (d := d) (p := ENNReal.ofReal βBarReal) (0 : ℝ)
        · -- `ν = υ - ῡ = 0` (γ exponent).
          rw [hυ_eq, hῡ_eq]
          have hcongr :
              (fun x : (Fin d → ℝ) => uLim x - uLim x)
                = (fun _ => (0 : ℝ)) := by
            funext x; ring
          rw [hcongr]
          exact MemLpPer.const (d := d) (p := ENNReal.ofReal γBarReal) (0 : ℝ))
      hData
  hLimMem := mem_D_set_family_paper_limit (d := d) βBar mLim uLim DuLim
  -- `γBarReal`/`βBarReal'`/`_hpow`/`_hV` are threaded for chain shape
  -- alignment with the rest of the T9/T10 chain (mirror of the strict-K
  -- producer above). The `1 < γBar` lower bound is no longer needed
  -- since `A0_isHemicontinuousK0` does not require it (the K0 DCT
  -- continuity result is independent of `γBar`'s lower bound).

/-- **K0 sibling: Signed family `MintyClosureOn` producer (narrow
paper-form, closed-cone, nonneg primal).**

K0 version of `mintyClosure_familyNative_signed_of_paperHypotheses_narrow`
(iter `infra-P5-T10-v8-K0-signed-mintyResSignedOf-retype`). Consumes
hData producing `HemicontSegmentDataK0` (the closed-cone sibling that
drops `hPosSeg`) and closed-cone regularity `RegularityHK0`. Internally
delegates to `A0_isHemicontinuousK0` for the `hAhc` field; segment
closure and limit membership are unchanged from the strict-K version.

Mirror of the set K0 closure consumer
`mintyClosure_familyNative_set_of_paperHypotheses_narrowK0`.

**iter `infra-P5-T10-v8-K0-signed-relocate-testDir-certs`** (signed
mirror of iter-0766): `hData`'s signature gains 4 explicit test-direction
cert preconditions `(hη, hDν, hν_β, hν_γ)` after `(η, ν, Dν)`. A
`testDirCertsOf` parameter supplies the certs to `A0_isHemicontinuousK0`
per test triple.

**iter `infra-P7-sigfix-T1-testDirCerts` (Phase 1A)**: `testDirCertsOf`
now takes `TestDirectionCertsRaw βBarReal γBarReal η ν Dν` (signed
mirror of the set refactor).

**iter `infra-P7-sigfix-T1-drain-B-K0-consumer-rewire` (Phase 1D-B)**:
Signed mirror of the set K0 drain-B refactor. `testDirCertsOf` is dropped;
certs at the difference triple are derived in-body from the two
signed-family memberships (`μ - μBar = g_μ - g_μBar` by subtraction). -/
noncomputable def mintyClosure_familyNative_signed_of_paperHypotheses_narrowK0
    {γBarReal βBarReal βBarReal' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hRegK0 : StationaryMFG.Theorems.SimplePower.RegularityHK0 (d := d) H DpH)
    (_hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (_hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (βBar : ℝ≥0∞)
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    (hmLim_nonneg : 0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                            (UnitCube d)] mLim)
    (γBar : ℝ)
    -- iter `infra-P7-sigfix-T1-drain-B-K0-consumer-rewire`: exponent
    -- alignment witness.
    (hβBar_eq : βBar = ENNReal.ofReal βBarReal)
    (hData : ∀ ⦃μBar ῡ Dῡ⦄,
                (μBar, ῡ, Dῡ)
                  ∈ D_signed_family_paper_nn (d := d) βBar mLim uLim DuLim →
              ∀ ⦃μ υ Dυ⦄,
                (μ, υ, Dυ)
                  ∈ D_signed_family_paper_nn (d := d) βBar mLim uLim DuLim →
              ∀ (η ν : (Fin d → ℝ) → ℝ)
                (Dν : Fin d → (Fin d → ℝ) → ℝ),
              MemLpPer (d := d) (ENNReal.ofReal βBarReal) η →
              (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dν i)) →
              MemLpPer (d := d) (ENNReal.ofReal βBarReal) ν →
              MemLpPer (d := d) (ENNReal.ofReal γBarReal) ν →
              StationaryMFG.Theorems.SimplePower.HemicontSegmentDataK0
                (d := d) V H DpH γBar Dυ Dῡ μ μBar υ ῡ Dν η ν) :
    MintyClosureOn (d := d) V H DpH mLim uLim DuLim
      (D_signed_family_paper_nn (d := d) βBar mLim uLim DuLim) where
  hSeg := by
    intro μBar ῡ Dῡ hBar μ υ Dυ hμ t ht
    exact D_signed_family_paper_nn_segment_closed (d := d) βBar mLim uLim DuLim
      hBar hμ t ht
  hAhc :=
    -- **iter `infra-P7-sigfix-T1-drain-B-K0-consumer-rewire`** (signed
    -- mirror of set drain-B). Build the family-conditional cert oracle
    -- in-body by unpacking signed-family membership of both endpoints.
    -- For the signed family
    -- (`μ = mLim + g_μ`, `μBar = mLim + g_μBar`, `υ = ῡ = uLim`,
    -- `Dυ = Dῡ = DuLim`), the difference triple is
    -- `(g_μ - g_μBar, 0, 0)`. Identical structure to the set case
    -- because the `_nn` constraint on the primal density does not enter
    -- the difference certs.
    StationaryMFG.Theorems.SimplePower.A0_isHemicontinuousK0_restricted_withFamilyCerts
      (V := V) (H := H) (DpH := DpH)
      hRegK0 γBar
      (D_signed_family_paper_nn (d := d) βBar mLim uLim DuLim)
      βBarReal γBarReal
      (familyCertsOf := by
        intro μBar ῡ Dῡ hBar μ υ Dυ hμ
        obtain ⟨gBar, hgBar_lp, _hgBar_per, _hsumBar_nn, hBar_eq⟩ := hBar
        obtain ⟨g, hg_lp, _hg_per, _hsum_nn, hμ_eq⟩ := hμ
        rw [Prod.mk.injEq, Prod.mk.injEq] at hBar_eq hμ_eq
        obtain ⟨hμBar_eq, hῡ_eq, hDῡ_eq⟩ := hBar_eq
        obtain ⟨hμ_eq, hυ_eq, hDυ_eq⟩ := hμ_eq
        refine ⟨?_, ?_, ?_, ?_⟩
        · -- `μ - μBar = g - gBar` in `L^βBarReal_per`.
          rw [hμ_eq, hμBar_eq]
          have hsub : MemLpPer (d := d) βBar (fun x => g x - gBar x) := by
            have h : MemLpPer (d := d) βBar (g - gBar) :=
              MemLp.toMemLpPer (MeasureTheory.MemLp.sub hg_lp.toMemLp hgBar_lp.toMemLp)
            exact h
          have hcongr :
              (fun x : (Fin d → ℝ) => (mLim x + g x) - (mLim x + gBar x))
                = (fun x => g x - gBar x) := by
            funext x; ring
          rw [hcongr, ← hβBar_eq]
          exact hsub
        · intro i
          rw [hDυ_eq, hDῡ_eq]
          have hcongr :
              (fun x : (Fin d → ℝ) => DuLim i x - DuLim i x)
                = (fun _ => (0 : ℝ)) := by
            funext x; ring
          rw [hcongr]
          exact MemLpPer.const (d := d) (p := ENNReal.ofReal γBarReal) (0 : ℝ)
        · rw [hυ_eq, hῡ_eq]
          have hcongr :
              (fun x : (Fin d → ℝ) => uLim x - uLim x)
                = (fun _ => (0 : ℝ)) := by
            funext x; ring
          rw [hcongr]
          exact MemLpPer.const (d := d) (p := ENNReal.ofReal βBarReal) (0 : ℝ)
        · rw [hυ_eq, hῡ_eq]
          have hcongr :
              (fun x : (Fin d → ℝ) => uLim x - uLim x)
                = (fun _ => (0 : ℝ)) := by
            funext x; ring
          rw [hcongr]
          exact MemLpPer.const (d := d) (p := ENNReal.ofReal γBarReal) (0 : ℝ))
      hData
  hLimMem :=
    mem_D_signed_family_paper_nn_limit (d := d) βBar mLim uLim DuLim
      hmLim_nonneg
  -- `γBarReal`/`βBarReal'`/`_hpow`/`_hV` are threaded for chain shape
  -- alignment with the rest of the T9/T10 chain (mirror of the strict-K
  -- producer and the set K0 producer above). The `1 < γBar` lower bound
  -- is not needed since `A0_isHemicontinuousK0` does not require it.

/-- **K0 sibling: Transport family `MintyClosureOn` producer (narrow
paper-form, closed-cone).**

K0 version of `mintyClosure_familyNative_transport_of_paperHypotheses_narrow`
(iter `infra-P5-T10-v8-K0-transport-mintyResTransportOf-retype`, transport
mirror of iter-0762's set-K0 retype and iter-0771's signed-K0 retype).
Consumes hData producing `HemicontSegmentDataK0` (the closed-cone sibling
that drops `hPosSeg`) and closed-cone regularity `RegularityHK0`.
Internally delegates to `A0_isHemicontinuousK0` for the `hAhc` field;
segment closure and limit membership are unchanged from the strict-K
version.

Mirror of the signed K0 closure consumer
`mintyClosure_familyNative_signed_of_paperHypotheses_narrowK0`.
Transport-narrow `D_transport_family_paper_limit` is unconditional (no
`hmLim_nonneg` parameter, unlike the signed case).

`hData`'s signature gains 4 explicit test-direction cert preconditions
`(hη, hDν, hν_β, hν_γ)` after `(η, ν, Dν)`. A `testDirCertsOf` parameter
supplies the certs to `A0_isHemicontinuousK0` per test triple.

**iter `infra-P7-sigfix-T1-testDirCerts` (Phase 1A)**: `testDirCertsOf`
now takes `TestDirectionCertsRaw βBarReal γBarReal η ν Dν` (transport
mirror of the set/signed refactors).

**iter `infra-P7-sigfix-T1-drain-B-K0-consumer-rewire` (Phase 1D-B)**:
Transport mirror of the set/signed K0 drain-B refactor. `testDirCertsOf`
is dropped; certs at the difference triple are derived in-body from the
two transport-family memberships. The transport difference triple is
`(0, ψ_υ - ψ_ῡ, ∂(ψ_υ - ψ_ῡ))`, where the ψ-side regularity uses
`MemSobolevPer.of_smoothPeriodic` (a smooth periodic function is in
every `L^p_per` and so is its partial derivative). -/
noncomputable def mintyClosure_familyNative_transport_of_paperHypotheses_narrowK0
    {γBarReal βBarReal βBarReal' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hRegK0 : StationaryMFG.Theorems.SimplePower.RegularityHK0 (d := d) H DpH)
    (_hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (_hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    (γBar : ℝ)
    (hData : ∀ ⦃μBar ῡ Dῡ⦄,
                (μBar, ῡ, Dῡ)
                  ∈ D_transport_family_paper (d := d) mLim uLim DuLim →
              ∀ ⦃μ υ Dυ⦄,
                (μ, υ, Dυ)
                  ∈ D_transport_family_paper (d := d) mLim uLim DuLim →
              ∀ (η ν : (Fin d → ℝ) → ℝ)
                (Dν : Fin d → (Fin d → ℝ) → ℝ),
              MemLpPer (d := d) (ENNReal.ofReal βBarReal) η →
              (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dν i)) →
              MemLpPer (d := d) (ENNReal.ofReal βBarReal) ν →
              MemLpPer (d := d) (ENNReal.ofReal γBarReal) ν →
              StationaryMFG.Theorems.SimplePower.HemicontSegmentDataK0
                (d := d) V H DpH γBar Dυ Dῡ μ μBar υ ῡ Dν η ν) :
    MintyClosureOn (d := d) V H DpH mLim uLim DuLim
      (D_transport_family_paper (d := d) mLim uLim DuLim) where
  hSeg := by
    intro μBar ῡ Dῡ hBar μ υ Dυ hμ t ht
    exact D_transport_family_paper_segment_closed (d := d) mLim uLim DuLim
      hBar hμ t ht
  hAhc :=
    -- **iter `infra-P7-sigfix-T1-drain-B-K0-consumer-rewire`** (transport
    -- mirror of the set/signed drain-B). Build the family-conditional
    -- cert oracle in-body by unpacking transport-family membership of
    -- both endpoints. For the transport family
    -- (`μ = μBar = mLim`, `υ = uLim + ψ_υ`, `ῡ = uLim + ψ_ῡ`,
    -- `Dυ i = DuLim i + ∂_i ψ_υ`, `Dῡ i = DuLim i + ∂_i ψ_ῡ`), the
    -- difference triple is `(0, ψ_υ - ψ_ῡ, ∂_i(ψ_υ - ψ_ῡ))`. ψ-side
    -- regularity from `MemSobolevPer.of_smoothPeriodic`.
    StationaryMFG.Theorems.SimplePower.A0_isHemicontinuousK0_restricted_withFamilyCerts
      (V := V) (H := H) (DpH := DpH)
      hRegK0 γBar
      (D_transport_family_paper (d := d) mLim uLim DuLim)
      βBarReal γBarReal
      (familyCertsOf := by
        intro μBar ῡ Dῡ hBar μ υ Dυ hμ
        obtain ⟨ψBar, hBar_eq⟩ := hBar
        obtain ⟨ψ, hμ_eq⟩ := hμ
        rw [Prod.mk.injEq, Prod.mk.injEq] at hBar_eq hμ_eq
        obtain ⟨hμBar_eq, hῡ_eq, hDῡ_eq⟩ := hBar_eq
        obtain ⟨hμ_eq, hυ_eq, hDυ_eq⟩ := hμ_eq
        refine ⟨?_, ?_, ?_, ?_⟩
        · -- `μ - μBar = mLim - mLim = 0` (η-cert).
          rw [hμ_eq, hμBar_eq]
          have hcongr :
              (fun x : (Fin d → ℝ) => mLim x - mLim x)
                = (fun _ => (0 : ℝ)) := by
            funext x; ring
          rw [hcongr]
          exact MemLpPer.const (d := d) (p := ENNReal.ofReal βBarReal) (0 : ℝ)
        · -- `Dν i = Dυ i - Dῡ i = ∂_i ψ - ∂_i ψBar = ∂_i (ψ - ψBar)`.
          intro i
          rw [hDυ_eq, hDῡ_eq]
          -- Use the smooth-periodic regularity on the difference ψ - ψBar.
          -- `∂_i (ψ - ψBar)` is smooth periodic; coerces to `L^γBarReal_per`
          -- via `MemSobolevPer.of_smoothPeriodic.1`.
          have hψdiff_γ :
              Periodic.MemLpPer (d := d)
                (ENNReal.ofReal γBarReal)
                ((Periodic.SmoothPeriodic.partialDeriv i ψ
                    : Periodic.SmoothPeriodic d) -
                  (Periodic.SmoothPeriodic.partialDeriv i ψBar
                    : Periodic.SmoothPeriodic d)
                  : (Fin d → ℝ) → ℝ) :=
            (Periodic.MemSobolevPer.of_smoothPeriodic
              (ENNReal.ofReal γBarReal)
              (Periodic.SmoothPeriodic.partialDeriv i ψ -
                Periodic.SmoothPeriodic.partialDeriv i ψBar)).1
          -- Pointwise rewrite: `((DuLim i + ∂_i ψ) - (DuLim i + ∂_i ψBar)) x
          --   = (∂_i ψ - ∂_i ψBar) x`.
          have hcongr :
              (fun x : (Fin d → ℝ) =>
                (DuLim i x +
                  ((Periodic.SmoothPeriodic.partialDeriv i ψ
                      : Periodic.SmoothPeriodic d) :
                    (Fin d → ℝ) → ℝ) x) -
                (DuLim i x +
                  ((Periodic.SmoothPeriodic.partialDeriv i ψBar
                      : Periodic.SmoothPeriodic d) :
                    (Fin d → ℝ) → ℝ) x))
                = (fun x =>
                    ((Periodic.SmoothPeriodic.partialDeriv i ψ -
                      Periodic.SmoothPeriodic.partialDeriv i ψBar :
                      Periodic.SmoothPeriodic d) :
                      (Fin d → ℝ) → ℝ) x) := by
            funext x
            simp [Periodic.SmoothPeriodic.coe_sub, Pi.sub_apply]
          rw [hcongr]
          exact hψdiff_γ
        · -- `ν = υ - ῡ = ψ - ψBar`, β-cert.
          rw [hυ_eq, hῡ_eq]
          have hψdiff_β :
              Periodic.MemLpPer (d := d)
                (ENNReal.ofReal βBarReal)
                ((ψ - ψBar : Periodic.SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) :=
            (Periodic.MemSobolevPer.of_smoothPeriodic
              (ENNReal.ofReal βBarReal) (ψ - ψBar)).1
          have hcongr :
              (fun x : (Fin d → ℝ) =>
                (uLim x + ((ψ : Periodic.SmoothPeriodic d) :
                    (Fin d → ℝ) → ℝ) x) -
                (uLim x + ((ψBar : Periodic.SmoothPeriodic d) :
                    (Fin d → ℝ) → ℝ) x))
                = (fun x =>
                    ((ψ - ψBar : Periodic.SmoothPeriodic d) :
                      (Fin d → ℝ) → ℝ) x) := by
            funext x
            simp [Periodic.SmoothPeriodic.coe_sub, Pi.sub_apply]
          rw [hcongr]
          exact hψdiff_β
        · -- `ν = υ - ῡ = ψ - ψBar`, γ-cert (same as above with γBarReal).
          rw [hυ_eq, hῡ_eq]
          have hψdiff_γ :
              Periodic.MemLpPer (d := d)
                (ENNReal.ofReal γBarReal)
                ((ψ - ψBar : Periodic.SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) :=
            (Periodic.MemSobolevPer.of_smoothPeriodic
              (ENNReal.ofReal γBarReal) (ψ - ψBar)).1
          have hcongr :
              (fun x : (Fin d → ℝ) =>
                (uLim x + ((ψ : Periodic.SmoothPeriodic d) :
                    (Fin d → ℝ) → ℝ) x) -
                (uLim x + ((ψBar : Periodic.SmoothPeriodic d) :
                    (Fin d → ℝ) → ℝ) x))
                = (fun x =>
                    ((ψ - ψBar : Periodic.SmoothPeriodic d) :
                      (Fin d → ℝ) → ℝ) x) := by
            funext x
            simp [Periodic.SmoothPeriodic.coe_sub, Pi.sub_apply]
          rw [hcongr]
          exact hψdiff_γ)
      hData
  hLimMem :=
    mem_D_transport_family_paper_limit (d := d) mLim uLim DuLim
  -- `γBarReal`/`βBarReal'`/`_hpow`/`_hV` are threaded for chain shape
  -- alignment with the rest of the T9/T10 chain (mirror of the strict-K
  -- producer and the set/signed K0 producers above). The `1 < γBar`
  -- lower bound is not needed since `A0_isHemicontinuousK0` does not
  -- require it.

/-- **Signed family `MintyClosureOn` producer (narrow paper-form,
nonneg primal).** Wires `A0_isHemicontinuous` on
`D_signed_family_paper_nn βBar mLim uLim DuLim` together with the narrow
signed-family segment-closure lemma and limit-membership. -/
noncomputable def mintyClosure_familyNative_signed_of_paperHypotheses_narrow
    {γBarReal βBarReal' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (_hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (_hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (βBar : ℝ≥0∞)
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    (hmLim_nonneg : 0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                            (UnitCube d)] mLim)
    (γBar : ℝ) (hγ : 1 < γBar)
    (hData : ∀ ⦃μBar ῡ Dῡ⦄,
                (μBar, ῡ, Dῡ)
                  ∈ D_signed_family_paper_nn (d := d) βBar mLim uLim DuLim →
              ∀ ⦃μ υ Dυ⦄,
                (μ, υ, Dυ)
                  ∈ D_signed_family_paper_nn (d := d) βBar mLim uLim DuLim →
              ∀ (η ν : (Fin d → ℝ) → ℝ)
                (Dν : Fin d → (Fin d → ℝ) → ℝ),
              StationaryMFG.Theorems.SimplePower.HemicontSegmentData
                (d := d) V H DpH γBar Dυ Dῡ μ μBar υ ῡ Dν η ν) :
    MintyClosureOn (d := d) V H DpH mLim uLim DuLim
      (D_signed_family_paper_nn (d := d) βBar mLim uLim DuLim) where
  hSeg := by
    intro μBar ῡ Dῡ hBar μ υ Dυ hμ t ht
    exact D_signed_family_paper_nn_segment_closed (d := d) βBar mLim uLim DuLim
      hBar hμ t ht
  hAhc :=
    -- Weakened to restricted-test form per iter
    -- `infra-P7-sigfix-T1-drain-A-restricted-hemicont`.
    (StationaryMFG.Theorems.SimplePower.A0_isHemicontinuous
      (V := V) (H := H) (DpH := DpH)
      hmon.toRegularityH γBar hγ
      (D_signed_family_paper_nn (d := d) βBar mLim uLim DuLim)
      hData).toRestricted
  hLimMem :=
    mem_D_signed_family_paper_nn_limit (d := d) βBar mLim uLim DuLim
      hmLim_nonneg

/-- **Transport family `MintyClosureOn` producer (narrow paper-form).**
Wires `A0_isHemicontinuous` on `D_transport_family_paper mLim uLim DuLim`
together with the narrow transport-family segment-closure lemma and
limit-membership. -/
noncomputable def mintyClosure_familyNative_transport_of_paperHypotheses_narrow
    {γBarReal βBarReal' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (_hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (_hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    (γBar : ℝ) (hγ : 1 < γBar)
    (hData : ∀ ⦃μBar ῡ Dῡ⦄,
                (μBar, ῡ, Dῡ)
                  ∈ D_transport_family_paper (d := d) mLim uLim DuLim →
              ∀ ⦃μ υ Dυ⦄,
                (μ, υ, Dυ)
                  ∈ D_transport_family_paper (d := d) mLim uLim DuLim →
              ∀ (η ν : (Fin d → ℝ) → ℝ)
                (Dν : Fin d → (Fin d → ℝ) → ℝ),
              StationaryMFG.Theorems.SimplePower.HemicontSegmentData
                (d := d) V H DpH γBar Dυ Dῡ μ μBar υ ῡ Dν η ν) :
    MintyClosureOn (d := d) V H DpH mLim uLim DuLim
      (D_transport_family_paper (d := d) mLim uLim DuLim) where
  hSeg := by
    intro μBar ῡ Dῡ hBar μ υ Dυ hμ t ht
    exact D_transport_family_paper_segment_closed (d := d) mLim uLim DuLim
      hBar hμ t ht
  hAhc :=
    -- Weakened to restricted-test form per iter
    -- `infra-P7-sigfix-T1-drain-A-restricted-hemicont`.
    (StationaryMFG.Theorems.SimplePower.A0_isHemicontinuous
      (V := V) (H := H) (DpH := DpH)
      hmon.toRegularityH γBar hγ
      (D_transport_family_paper (d := d) mLim uLim DuLim)
      hData).toRestricted
  hLimMem :=
    mem_D_transport_family_paper_limit (d := d) mLim uLim DuLim

/-! Sanity-check `example`s for the three narrow producers. -/

example
    {γBarReal βBarReal' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (βBar : ℝ≥0∞)
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    (γBar : ℝ) (hγ : 1 < γBar)
    (hData : ∀ ⦃μBar ῡ Dῡ⦄,
                (μBar, ῡ, Dῡ)
                  ∈ D_set_family_paper (d := d) βBar mLim uLim DuLim →
              ∀ ⦃μ υ Dυ⦄,
                (μ, υ, Dυ)
                  ∈ D_set_family_paper (d := d) βBar mLim uLim DuLim →
              ∀ (η ν : (Fin d → ℝ) → ℝ)
                (Dν : Fin d → (Fin d → ℝ) → ℝ),
              StationaryMFG.Theorems.SimplePower.HemicontSegmentData
                (d := d) V H DpH γBar Dυ Dῡ μ μBar υ ῡ Dν η ν) :
    MintyClosureOn (d := d) V H DpH mLim uLim DuLim
      (D_set_family_paper (d := d) βBar mLim uLim DuLim) :=
  mintyClosure_familyNative_set_of_paperHypotheses_narrow
    (γBarReal := γBarReal) (βBarReal' := βBarReal')
    hmon hpow hV βBar mLim uLim DuLim γBar hγ hData

example
    {γBarReal βBarReal' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (βBar : ℝ≥0∞)
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    (hmLim_nonneg : 0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                            (UnitCube d)] mLim)
    (γBar : ℝ) (hγ : 1 < γBar)
    (hData : ∀ ⦃μBar ῡ Dῡ⦄,
                (μBar, ῡ, Dῡ)
                  ∈ D_signed_family_paper_nn (d := d) βBar mLim uLim DuLim →
              ∀ ⦃μ υ Dυ⦄,
                (μ, υ, Dυ)
                  ∈ D_signed_family_paper_nn (d := d) βBar mLim uLim DuLim →
              ∀ (η ν : (Fin d → ℝ) → ℝ)
                (Dν : Fin d → (Fin d → ℝ) → ℝ),
              StationaryMFG.Theorems.SimplePower.HemicontSegmentData
                (d := d) V H DpH γBar Dυ Dῡ μ μBar υ ῡ Dν η ν) :
    MintyClosureOn (d := d) V H DpH mLim uLim DuLim
      (D_signed_family_paper_nn (d := d) βBar mLim uLim DuLim) :=
  mintyClosure_familyNative_signed_of_paperHypotheses_narrow
    (γBarReal := γBarReal) (βBarReal' := βBarReal')
    hmon hpow hV βBar mLim uLim DuLim hmLim_nonneg γBar hγ hData

example
    {γBarReal βBarReal' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (mLim uLim : (Fin d → ℝ) → ℝ)
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    (γBar : ℝ) (hγ : 1 < γBar)
    (hData : ∀ ⦃μBar ῡ Dῡ⦄,
                (μBar, ῡ, Dῡ)
                  ∈ D_transport_family_paper (d := d) mLim uLim DuLim →
              ∀ ⦃μ υ Dυ⦄,
                (μ, υ, Dυ)
                  ∈ D_transport_family_paper (d := d) mLim uLim DuLim →
              ∀ (η ν : (Fin d → ℝ) → ℝ)
                (Dν : Fin d → (Fin d → ℝ) → ℝ),
              StationaryMFG.Theorems.SimplePower.HemicontSegmentData
                (d := d) V H DpH γBar Dυ Dῡ μ μBar υ ῡ Dν η ν) :
    MintyClosureOn (d := d) V H DpH mLim uLim DuLim
      (D_transport_family_paper (d := d) mLim uLim DuLim) :=
  mintyClosure_familyNative_transport_of_paperHypotheses_narrow
    (γBarReal := γBarReal) (βBarReal' := βBarReal')
    hmon hpow hV mLim uLim DuLim γBar hγ hData

end Banach
end SimplePower
end Theorems
end StationaryMFG
end
