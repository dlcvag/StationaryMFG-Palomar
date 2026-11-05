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
public import StationaryMFG.Theorems.SimplePower.Banach.RegularizedSequence.Part3
import all StationaryMFG.Theorems.SimplePower.Banach.RegularizedSequence.Part3

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


/-! ### Phase F0 — family-native limit-passage producers.

Per `docs/THEOREM1_CLOSURE_PLAN.md` v4 §10, the T10 chain assembles
`H4SimplePowerInputs` directly from three paper-test-family
strong-VI specializations at the limit. The three producers below
consume `(hmon, hpow, hV, hExp, seq, wkBundle, pairing, mintyClosure,
hDuniv)` — the same inputs `limitSolutionData_of_regularizedSequence`
takes — and each produces one paper-test-family strong-VI conclusion
at the limit triple `(mLim, uLim, DuLim)`.

The body of each producer reuses the universal-form pipeline
(`limitPassage_to_weakVI` + `main_strong_VI`) to land the universal
strong VI internally, then specializes via the local helpers
`palomar_RegularizedSequence_strongVI_setForm_of_universal` /
`palomar_RegularizedSequence_strongVI_setFormSigned_of_universal` /
`palomar_RegularizedSequence_strongVI_transportForm_of_universal`. This is the family-native
*shape*. Per Phase F0 strip
(`infra-P5-theorem1-phase-F0-strip-hVI-eps-universal`, iter 310),
the residue field `hVI_eps_universal` was removed from
`LimitPairingSelectorPaperResidue`; the universal regularised-VI
input is now threaded as a separate authorised residue at the
chain level (`T10PaperResidues.hVI_eps_universalOf`). The
producers below still consume a `LimitPairingInputs` parameter
since they call `limitPassage_to_weakVI` internally; this is the
shape inherited from the legacy universal infrastructure, which
remains in place for Theorem 2 / congestion code.
-/

/-! ### Phase 5a-set — set-family-native limit-passage helper.

Per `infra-P5-theorem1-phase-5a-set-drop-hVI-eps-universal`, the helper
below produces the **set-family-restricted** weak VI at the limit triple
`(mLim, uLim, DuLim)` directly from the per-`k` regularised paper-family
VI `(seq.sol k).hVIeps_set`, bypassing the universal-shape
`limitPassage_to_weakVI` (and hence `LimitPassageInputData.hVI_eps`).

Concretely: given a non-negative perturbation `ρ`, we feed
`(seq.sol k).hVIeps_set Set.univ ...` (with primal density
`mLim + ρ`, value-function `uLim`, gradient `DuLim`) to obtain a
per-`k` regularised VI in `mfgOperatorEpsPair` form, bridge the
`Set.univ.indicator (mLim + ρ) =ᵐ mLim + ρ` shape via
`mfgOperatorEpsPair_congr_ae{,_primal}`, and apply
`limit_passage_weak_VI_of_eps`.

The returned conclusion is the weak VI at the limit triple at the
test triple `(mLim + ρ, uLim, DuLim)`, which is exactly the per-test-
triple input that `main_strong_VI` consumes for `D_set_family`. -/

theorem limitPassage_setForm_of_seqVI
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
    (hmLim_nonneg :
      0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
              (UnitCube d)] mLim)
    (hmLim_memLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal) mLim)
    (huLim_sob : MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) uLim)
    (hDuLim_memLp :
      ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (DuLim i))
    (hWeak_uLim : ∀ i, HasWeakDerivPer (d := d) i uLim (DuLim i))
    (ρ : (Fin d → ℝ) → ℝ)
    (hρ_nonneg : ∀ x, 0 ≤ ρ x)
    (hρ_memLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal) ρ)
    (hpair_conv :
      Filter.Tendsto (fun k =>
        mfgOperatorPair (V := V) (H := H) (DpH := DpH)
            DuLim (fun x => mLim x + ρ x) uLim
            (fun i x => DuLim i x - (seq.sol k).Du i x)
            ((fun x => mLim x + ρ x) - (seq.sol k).m)
            (uLim - (seq.sol k).u))
        Filter.atTop
        (𝓝 (mfgOperatorPair (V := V) (H := H) (DpH := DpH)
              DuLim (fun x => mLim x + ρ x) uLim
              (fun i x => DuLim i x - DuLim i x)
              ((fun x => mLim x + ρ x) - mLim)
              (uLim - uLim))))
    {M : ℝ}
    (hreg_bdd : ∀ k,
      |gateauxWpPair γBarReal DuLim uLim
          (fun i x => DuLim i x - (seq.sol k).Du i x)
          (uLim - (seq.sol k).u)| ≤ M) :
    0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH)
          DuLim (fun x => mLim x + ρ x) uLim
          (fun i x => DuLim i x - DuLim i x)
          ((fun x => mLim x + ρ x) - mLim)
          (uLim - uLim) := by
  -- Step 1: the perturbed density `mLim + ρ ≥ 0` a.e.
  set μLim : (Fin d → ℝ) → ℝ := fun x => mLim x + ρ x with hμLim_def
  have hμLim_nonneg :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        0 ≤ μLim x := by
    filter_upwards [hmLim_nonneg] with x hxm
    exact add_nonneg hxm (hρ_nonneg x)
  -- `MemLpPer βBar μLim` from `hmLim_memLp + hρ_memLp`.
  have hμLim_memLp :
      MemLpPer (d := d) (ENNReal.ofReal βBarReal) μLim :=
    Periodic.MemLpPer.add hmLim_memLp hρ_memLp
  -- The `Set.univ.indicator μLim` form needed by `hVIeps_set`.
  have hSμLim_memLp :
      MemLpPer (d := d) (ENNReal.ofReal βBarReal)
        (Set.univ.indicator μLim) := by
    have heq : (Set.univ.indicator μLim : (Fin d → ℝ) → ℝ) = μLim := by
      funext x; simp
    rw [heq]; exact hμLim_memLp
  -- Step 2: per-`k` regularised VI from `(seq.sol k).hVIeps_set`.
  have hVI_at_univ : ∀ k,
      0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal (seq.epsSeq k)
            DuLim (Set.univ.indicator μLim) uLim
            (fun i x => DuLim i x - (seq.sol k).Du i x)
            (Set.univ.indicator μLim - (seq.sol k).m)
            (uLim - (seq.sol k).u) := fun k =>
    (seq.sol k).hVIeps_set Set.univ MeasurableSet.univ μLim uLim DuLim
      hμLim_nonneg hSμLim_memLp huLim_sob hDuLim_memLp hWeak_uLim
  -- Step 3: bridge `Set.univ.indicator μLim` to `μLim` in both
  -- the primal density and the test-direction `η`.
  have hindicator_eq :
      (Set.univ.indicator μLim : (Fin d → ℝ) → ℝ) = μLim := by
    funext x; simp
  have hVI_eps_aligned : ∀ k,
      0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal (seq.epsSeq k)
            DuLim μLim uLim
            (fun i x => DuLim i x - (seq.sol k).Du i x)
            (μLim - (seq.sol k).m) (uLim - (seq.sol k).u) := by
    intro k
    have h := hVI_at_univ k
    -- Rewrite the primal `Set.univ.indicator μLim` to `μLim`.
    rw [hindicator_eq] at h
    exact h
  -- Step 4: apply `limit_passage_weak_VI_of_eps`.
  exact StationaryMFG.Theorems.SimplePower.limit_passage_weak_VI_of_eps
    (V := V) (H := H) (DpH := DpH)
    (γBar := γBarReal) (ε := seq.epsSeq)
    (μ := μLim) (υ := uLim) (Dυ := DuLim)
    (mε := fun k => (seq.sol k).m) (uε := fun k => (seq.sol k).u)
    (Duε := fun k => (seq.sol k).Du)
    (m := mLim) (u := uLim) (Du := DuLim)
    (fun k => (seq.heps_pos k).le) seq.heps_tendsto hVI_eps_aligned
    hpair_conv hreg_bdd

/-- Sanity check: `limitPassage_setForm_of_seqVI` typechecks. -/
example
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
    (hmLim_nonneg :
      0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
              (UnitCube d)] mLim)
    (hmLim_memLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal) mLim)
    (huLim_sob : MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) uLim)
    (hDuLim_memLp :
      ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (DuLim i))
    (hWeak_uLim : ∀ i, HasWeakDerivPer (d := d) i uLim (DuLim i))
    (ρ : (Fin d → ℝ) → ℝ)
    (hρ_nonneg : ∀ x, 0 ≤ ρ x)
    (hρ_memLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal) ρ)
    (hpair_conv :
      Filter.Tendsto (fun k =>
        mfgOperatorPair (V := V) (H := H) (DpH := DpH)
            DuLim (fun x => mLim x + ρ x) uLim
            (fun i x => DuLim i x - (seq.sol k).Du i x)
            ((fun x => mLim x + ρ x) - (seq.sol k).m)
            (uLim - (seq.sol k).u))
        Filter.atTop
        (𝓝 (mfgOperatorPair (V := V) (H := H) (DpH := DpH)
              DuLim (fun x => mLim x + ρ x) uLim
              (fun i x => DuLim i x - DuLim i x)
              ((fun x => mLim x + ρ x) - mLim)
              (uLim - uLim))))
    {M : ℝ}
    (hreg_bdd : ∀ k,
      |gateauxWpPair γBarReal DuLim uLim
          (fun i x => DuLim i x - (seq.sol k).Du i x)
          (uLim - (seq.sol k).u)| ≤ M) :
    0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH)
          DuLim (fun x => mLim x + ρ x) uLim
          (fun i x => DuLim i x - DuLim i x)
          ((fun x => mLim x + ρ x) - mLim)
          (uLim - uLim) :=
  limitPassage_setForm_of_seqVI seq mLim uLim DuLim
    hmLim_nonneg hmLim_memLp huLim_sob hDuLim_memLp hWeak_uLim
    ρ hρ_nonneg hρ_memLp hpair_conv hreg_bdd

/-! ### Phase 5a-signed — signed-family-native limit-passage helper.

Per `infra-P5-theorem1-phase-5a-signed-drop-hVI-eps-universal` (iter 362
retry, after iter 361's user-triple field unblocker), this helper
produces the **signed-family-restricted** weak VI at the limit triple
`(mLim, uLim, DuLim)` directly from the per-`k` regularised paper-family
VI `(seq.sol k).hVIeps_signed_user_triple`, bypassing the universal-shape
`limitPassage_to_weakVI` (and hence `LimitPassageInputData.hVI_eps`).

Unlike the set-family field, the signed-family field's perturbation
shape is `μ + σ·μ·1_S` (not free); we expose the `(σ, S, μ_user)`
parameters so the consumer can pin them. With `S := ∅` the perturbation
collapses to `μ_user`, covering arbitrary nonneg-primal triples
`(DuLim, μ_user, uLim)`; with σ ∈ {±1} and meas+finite `S`, it covers
the signed-test triple shape. -/

theorem limitPassage_signedForm_of_seqVI
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
    (huLim_sob : MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) uLim)
    (hDuLim_memLp :
      ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (DuLim i))
    (hWeak_uLim : ∀ i, HasWeakDerivPer (d := d) i uLim (DuLim i))
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (S : Set (Fin d → ℝ)) (hS : MeasurableSet S)
    (hSfin : (MeasureTheory.volume.restrict (UnitCube d)) S < ⊤)
    (μ_user : (Fin d → ℝ) → ℝ)
    (hμ_user_nonneg :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        0 ≤ μ_user x)
    (hμ_user_memLp :
      MemLpPer (d := d) (ENNReal.ofReal βBarReal) μ_user)
    (hpair_conv :
      Filter.Tendsto (fun k =>
        mfgOperatorPair (V := V) (H := H) (DpH := DpH)
            DuLim
            (fun x => μ_user x + σ * μ_user x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
            uLim
            (fun i x => DuLim i x - (seq.sol k).Du i x)
            ((fun x => μ_user x + σ * μ_user x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                - (seq.sol k).m)
            (uLim - (seq.sol k).u))
        Filter.atTop
        (𝓝 (mfgOperatorPair (V := V) (H := H) (DpH := DpH)
              DuLim
              (fun x => μ_user x + σ * μ_user x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              uLim
              (fun i x => DuLim i x - DuLim i x)
              ((fun x => μ_user x + σ * μ_user x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                  - mLim)
              (uLim - uLim))))
    {M : ℝ}
    (hreg_bdd : ∀ k,
      |gateauxWpPair γBarReal DuLim uLim
          (fun i x => DuLim i x - (seq.sol k).Du i x)
          (uLim - (seq.sol k).u)| ≤ M) :
    0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH)
          DuLim
          (fun x => μ_user x + σ * μ_user x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          uLim
          (fun i x => DuLim i x - DuLim i x)
          ((fun x => μ_user x + σ * μ_user x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              - mLim)
          (uLim - uLim) := by
  -- Step 1: per-`k` regularised VI from
  -- `(seq.sol k).hVIeps_signed_user_triple` at `(σ, S, μ_user, uLim, DuLim)`.
  have hVI_eps : ∀ k,
      0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal (seq.epsSeq k)
            DuLim
            (fun x => μ_user x + σ * μ_user x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
            uLim
            (fun i x => DuLim i x - (seq.sol k).Du i x)
            ((fun x => μ_user x + σ * μ_user x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                - (seq.sol k).m)
            (uLim - (seq.sol k).u) := fun k =>
    (seq.sol k).hVIeps_signed_user_triple σ hσ S hS hSfin μ_user uLim DuLim
      hμ_user_nonneg hμ_user_memLp huLim_sob hDuLim_memLp hWeak_uLim
  -- Step 2: apply `limit_passage_weak_VI_of_eps` with
  -- `μ := μ_user + σ·μ_user·1_S`, `υ := uLim`, `Dυ := DuLim`,
  -- limit `(mLim, uLim, DuLim)`.
  exact StationaryMFG.Theorems.SimplePower.limit_passage_weak_VI_of_eps
    (V := V) (H := H) (DpH := DpH)
    (γBar := γBarReal) (ε := seq.epsSeq)
    (μ := fun x => μ_user x + σ * μ_user x *
            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
    (υ := uLim) (Dυ := DuLim)
    (mε := fun k => (seq.sol k).m) (uε := fun k => (seq.sol k).u)
    (Duε := fun k => (seq.sol k).Du)
    (m := mLim) (u := uLim) (Du := DuLim)
    (fun k => (seq.heps_pos k).le) seq.heps_tendsto hVI_eps
    hpair_conv hreg_bdd

/-- Sanity check: `limitPassage_signedForm_of_seqVI` typechecks. -/
example
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
    (huLim_sob : MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) uLim)
    (hDuLim_memLp :
      ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (DuLim i))
    (hWeak_uLim : ∀ i, HasWeakDerivPer (d := d) i uLim (DuLim i))
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (S : Set (Fin d → ℝ)) (hS : MeasurableSet S)
    (hSfin : (MeasureTheory.volume.restrict (UnitCube d)) S < ⊤)
    (μ_user : (Fin d → ℝ) → ℝ)
    (hμ_user_nonneg :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        0 ≤ μ_user x)
    (hμ_user_memLp :
      MemLpPer (d := d) (ENNReal.ofReal βBarReal) μ_user)
    (hpair_conv :
      Filter.Tendsto (fun k =>
        mfgOperatorPair (V := V) (H := H) (DpH := DpH)
            DuLim
            (fun x => μ_user x + σ * μ_user x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
            uLim
            (fun i x => DuLim i x - (seq.sol k).Du i x)
            ((fun x => μ_user x + σ * μ_user x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                - (seq.sol k).m)
            (uLim - (seq.sol k).u))
        Filter.atTop
        (𝓝 (mfgOperatorPair (V := V) (H := H) (DpH := DpH)
              DuLim
              (fun x => μ_user x + σ * μ_user x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              uLim
              (fun i x => DuLim i x - DuLim i x)
              ((fun x => μ_user x + σ * μ_user x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                  - mLim)
              (uLim - uLim))))
    {M : ℝ}
    (hreg_bdd : ∀ k,
      |gateauxWpPair γBarReal DuLim uLim
          (fun i x => DuLim i x - (seq.sol k).Du i x)
          (uLim - (seq.sol k).u)| ≤ M) :
    0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH)
          DuLim
          (fun x => μ_user x + σ * μ_user x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          uLim
          (fun i x => DuLim i x - DuLim i x)
          ((fun x => μ_user x + σ * μ_user x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              - mLim)
          (uLim - uLim) :=
  limitPassage_signedForm_of_seqVI seq mLim uLim DuLim
    huLim_sob hDuLim_memLp hWeak_uLim σ hσ S hS hSfin
    μ_user hμ_user_nonneg hμ_user_memLp hpair_conv hreg_bdd

/-- **Phase 5a-signed corollary at `S := ∅`.** Specializing
`limitPassage_signedForm_of_seqVI` at `S := ∅` (so the perturbation
`μ + σ·μ·1_∅ = μ` collapses to the bare nonneg primal) produces the
weak VI at the un-perturbed test triple `(DuLim, μ_user, uLim)` for any
nonneg-primal `μ_user`. This is the form consumed by
`hStrongFamily_nn`'s `hweak` argument: it covers the full nonneg-primal
signed family `D_signed_family_nn`. -/
theorem limitPassage_signedForm_of_seqVI_empty
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
    (huLim_sob : MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) uLim)
    (hDuLim_memLp :
      ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (DuLim i))
    (hWeak_uLim : ∀ i, HasWeakDerivPer (d := d) i uLim (DuLim i))
    (μ_user : (Fin d → ℝ) → ℝ)
    (hμ_user_nonneg :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        0 ≤ μ_user x)
    (hμ_user_memLp :
      MemLpPer (d := d) (ENNReal.ofReal βBarReal) μ_user)
    (hpair_conv :
      Filter.Tendsto (fun k =>
        mfgOperatorPair (V := V) (H := H) (DpH := DpH)
            DuLim μ_user uLim
            (fun i x => DuLim i x - (seq.sol k).Du i x)
            (μ_user - (seq.sol k).m)
            (uLim - (seq.sol k).u))
        Filter.atTop
        (𝓝 (mfgOperatorPair (V := V) (H := H) (DpH := DpH)
              DuLim μ_user uLim
              (fun i x => DuLim i x - DuLim i x)
              (μ_user - mLim)
              (uLim - uLim))))
    {M : ℝ}
    (hreg_bdd : ∀ k,
      |gateauxWpPair γBarReal DuLim uLim
          (fun i x => DuLim i x - (seq.sol k).Du i x)
          (uLim - (seq.sol k).u)| ≤ M) :
    0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH)
          DuLim μ_user uLim
          (fun i x => DuLim i x - DuLim i x)
          (μ_user - mLim)
          (uLim - uLim) := by
  -- Apply the helper at `σ := 1`, `S := ∅`. The perturbation
  -- `μ_user + 1·μ_user·1_∅ = μ_user` collapses to the bare primal.
  have hempty_meas : MeasurableSet (∅ : Set (Fin d → ℝ)) :=
    MeasurableSet.empty
  have hempty_fin :
      (MeasureTheory.volume.restrict (UnitCube d))
          (∅ : Set (Fin d → ℝ)) < ⊤ := by
    simp
  -- Establish pointwise equality between perturbed and bare primal.
  have hperturbed_eq :
      (fun x => μ_user x + (1 : ℝ) * μ_user x *
                  (∅ : Set (Fin d → ℝ)).indicator
                    (fun _ : Fin d → ℝ => (1 : ℝ)) x) = μ_user := by
    funext x
    simp [Set.indicator_empty]
  -- Invoke the helper at `(σ, S) := (1, ∅)`, then bridge via
  -- `hperturbed_eq` to align with the un-perturbed test triple.
  have h := limitPassage_signedForm_of_seqVI (V := V) (H := H) (DpH := DpH)
    seq mLim uLim DuLim huLim_sob hDuLim_memLp hWeak_uLim
    (1 : ℝ) (Or.inl rfl) ∅ hempty_meas hempty_fin
    μ_user hμ_user_nonneg hμ_user_memLp
    (M := M) ?_ ?_
  · -- The helper output uses the perturbed primal; rewrite to the bare form.
    rw [hperturbed_eq] at h
    exact h
  · -- pairing convergence at the perturbed test triple = at the bare triple
    -- after `hperturbed_eq` rewrite.
    rw [hperturbed_eq]
    exact hpair_conv
  · -- Gateaux residual bound: independent of the primal perturbation.
    exact hreg_bdd

/-- **Phase 5a-transport per-family limit-passage helper.**
Consume the per-`k` transport-family regularised VI
`(seq.sol k).hVIeps_transport` and pass to the limit, producing the
unregularised weak VI at the test triple `(mLim, υ, Dυ)`.

Mirrors `limitPassage_setForm_of_seqVI` for the transport family. The
test-triple shape is `(mLim, υ, Dυ)` (primal density is exactly
`mLim`); the test value-function `υ` and gradient family `Dυ` are
arbitrary, supplied with their `MemSobolevPer`/`MemLpPer` certificates.

The per-`k` regularised VI from `(seq.sol k).hVIeps_transport` is
applied with `σ := mLim`, `υ := υ`, `φ := Dυ`. Then
`limit_passage_weak_VI_of_eps` delivers the limit. -/
theorem limitPassage_transportForm_of_seqVI
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
    (hmLim_nonneg :
      0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
              (UnitCube d)] mLim)
    (hmLim_memLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal) mLim)
    (υ : (Fin d → ℝ) → ℝ)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (hυ_memSob : MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ)
    (hDυ_memLp :
      ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i))
    (hWeak_υ : ∀ i, HasWeakDerivPer (d := d) i υ (Dυ i))
    (hpair_conv :
      Filter.Tendsto (fun k =>
        mfgOperatorPair (V := V) (H := H) (DpH := DpH)
            Dυ mLim υ
            (fun i x => Dυ i x - (seq.sol k).Du i x)
            (mLim - (seq.sol k).m)
            (υ - (seq.sol k).u))
        Filter.atTop
        (𝓝 (mfgOperatorPair (V := V) (H := H) (DpH := DpH)
              Dυ mLim υ
              (fun i x => Dυ i x - DuLim i x)
              (mLim - mLim)
              (υ - uLim))))
    {M : ℝ}
    (hreg_bdd : ∀ k,
      |gateauxWpPair γBarReal Dυ υ
          (fun i x => Dυ i x - (seq.sol k).Du i x)
          (υ - (seq.sol k).u)| ≤ M) :
    0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH)
          Dυ mLim υ
          (fun i x => Dυ i x - DuLim i x)
          (mLim - mLim)
          (υ - uLim) := by
  -- Step 1: per-`k` regularised transport-family VI at
  -- `(σ, υ, φ) := (mLim, υ, Dυ)`, sourced from `(seq.sol k).hVIeps_transport`.
  have hVI_eps : ∀ k,
      0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal (seq.epsSeq k)
            Dυ mLim υ
            (fun i x => Dυ i x - (seq.sol k).Du i x)
            (mLim - (seq.sol k).m) (υ - (seq.sol k).u) := fun k =>
    (seq.sol k).hVIeps_transport mLim υ Dυ hmLim_nonneg hmLim_memLp
      hυ_memSob hDυ_memLp hWeak_υ
  -- Step 2: apply `limit_passage_weak_VI_of_eps` with
  -- `μ := mLim`, `υ := υ`, `Dυ := Dυ`, limit `(mLim, uLim, DuLim)`.
  exact StationaryMFG.Theorems.SimplePower.limit_passage_weak_VI_of_eps
    (V := V) (H := H) (DpH := DpH)
    (γBar := γBarReal) (ε := seq.epsSeq)
    (μ := mLim) (υ := υ) (Dυ := Dυ)
    (mε := fun k => (seq.sol k).m) (uε := fun k => (seq.sol k).u)
    (Duε := fun k => (seq.sol k).Du)
    (m := mLim) (u := uLim) (Du := DuLim)
    (fun k => (seq.heps_pos k).le) seq.heps_tendsto hVI_eps
    hpair_conv hreg_bdd

/-- Sanity check: `limitPassage_transportForm_of_seqVI` typechecks. -/
example
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
    (hmLim_nonneg :
      0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
              (UnitCube d)] mLim)
    (hmLim_memLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal) mLim)
    (υ : (Fin d → ℝ) → ℝ)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (hυ_memSob : MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ)
    (hDυ_memLp :
      ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i))
    (hWeak_υ : ∀ i, HasWeakDerivPer (d := d) i υ (Dυ i))
    (hpair_conv :
      Filter.Tendsto (fun k =>
        mfgOperatorPair (V := V) (H := H) (DpH := DpH)
            Dυ mLim υ
            (fun i x => Dυ i x - (seq.sol k).Du i x)
            (mLim - (seq.sol k).m)
            (υ - (seq.sol k).u))
        Filter.atTop
        (𝓝 (mfgOperatorPair (V := V) (H := H) (DpH := DpH)
              Dυ mLim υ
              (fun i x => Dυ i x - DuLim i x)
              (mLim - mLim)
              (υ - uLim))))
    {M : ℝ}
    (hreg_bdd : ∀ k,
      |gateauxWpPair γBarReal Dυ υ
          (fun i x => Dυ i x - (seq.sol k).Du i x)
          (υ - (seq.sol k).u)| ≤ M) :
    0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH)
          Dυ mLim υ
          (fun i x => Dυ i x - DuLim i x)
          (mLim - mLim)
          (υ - uLim) :=
  limitPassage_transportForm_of_seqVI seq mLim uLim DuLim
    hmLim_nonneg hmLim_memLp υ Dυ hυ_memSob hDυ_memLp hWeak_υ
    hpair_conv hreg_bdd

/-- **F0 family producer (set form).** From the same inputs as
`limitSolutionData_of_regularizedSequence`, produce the set-form
strong VI at the limit triple `(mLim, uLim, DuLim)`.

Phase 4a (task `infra-P4-minty-family-native-4a-set`): now consumes a
per-family `MintyClosureOn D_set_family` certificate instead of a
universal `MintyClosure (D = Set.univ)` plus `hDuniv` shortcut. The
Minty argument runs on `D_set_family` via `main_strong_VI`, and the
final specialization to `StrongVI_setForm` uses
`strongVI_setForm_of_setFamily` (the family-shaped specializer
landed by Child 1 of the Phase F strip refactor).

**Phase 5a-set** (`infra-P5-theorem1-phase-5a-set-drop-hVI-eps-universal`):
the per-test-triple weak VI is now produced by the new helper
`limitPassage_setForm_of_seqVI`, which consumes the per-`k`
regularised paper-family VI `(seq.sol k).hVIeps_set` directly
(bypassing `pairing.data μ υ Dυ.hVI_eps`, hence bypassing
`T10PaperResidues.hVI_eps_universalOf` for the set family).
The pairing-convergence and Gateaux-residual inputs to the helper
are still sourced from `pairing.hpair_conv` and
`(pairing.data μ υ Dυ).hreg_bdd`, so the `pairing : LimitPairingInputs`
parameter remains. Full removal of that parameter is out of scope
for this child. -/
noncomputable def strongVI_set_at_limit_of_paperHypotheses
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (_hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (_hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (_hExp : SimplePowerExponentFacts γBarReal
                (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
                (ENNReal.ofReal βBarReal'))
    (seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH)
    (wkBundle : WeakLimitInputBundleAE (d := d) γBarReal βBarReal)
    (pairing : LimitPairingInputsFamily (d := d)
                  (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  (V := V) (H := H) (DpH := DpH)
                  seq wkBundle.mLim wkBundle.uLim wkBundle.DuLim
                  (D_set_family (d := d)
                     wkBundle.mLim wkBundle.uLim wkBundle.DuLim))
    (mintyClosureOn : MintyClosureOn (d := d) V H DpH
                       wkBundle.mLim wkBundle.uLim wkBundle.DuLim
                       (D_set_family (d := d)
                          wkBundle.mLim wkBundle.uLim wkBundle.DuLim)) :
    StationaryMFG.Theorems.SimplePower.StrongVI_setForm
      V H DpH γBarReal 0 wkBundle.DuLim wkBundle.mLim wkBundle.uLim := by
  -- Phase 6c-iii: `pairing` is now an `LimitPairingInputsFamily` at
  -- `D_set_family`; we derive `pairing.data` calls via the
  -- `mem_D_set_family_test` family membership.
  -- Per Phase 5a-set: per-test-triple weak VI on `D_set_family` is now
  -- produced by `limitPassage_setForm_of_seqVI`, which consumes
  -- `(seq.sol k).hVIeps_set` directly (bypassing the universal `hVI_eps`).
  let _ := hpow  -- mark used (the helper does not need `hpow` directly)
  have hStrongFamily :
      ∀ ⦃μ υ Dυ⦄, (μ, υ, Dυ) ∈ D_set_family (d := d)
                      wkBundle.mLim wkBundle.uLim wkBundle.DuLim →
        0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH)
              wkBundle.DuLim wkBundle.mLim wkBundle.uLim
              (fun i x => Dυ i x - wkBundle.DuLim i x)
              (μ - wkBundle.mLim) (υ - wkBundle.uLim) := by
    refine StationaryMFG.Theorems.SimplePower.main_strong_VI
      (V := V) (H := H) (DpH := DpH)
      (D := D_set_family (d := d)
              wkBundle.mLim wkBundle.uLim wkBundle.DuLim)
      mintyClosureOn.hSeg mintyClosureOn.hAhc mintyClosureOn.hLimMem ?_
    -- Per-test-triple weak VI for triples in `D_set_family`. Each such
    -- triple has shape `(mLim + ρ, uLim, DuLim)` for some `ρ ≥ 0`.
    intro μ υ Dυ hμ
    obtain ⟨ρ, hρ_nonneg, hpeq⟩ := hμ
    -- Decompose `(μ, υ, Dυ) = ((fun x => wkBundle.mLim x + ρ x), wkBundle.uLim, wkBundle.DuLim)`.
    rw [Prod.mk.injEq, Prod.mk.injEq] at hpeq
    obtain ⟨hμeq, hυeq, hDυeq⟩ := hpeq
    rw [hμeq, hυeq, hDυeq]
    -- The pairing-convergence and Gateaux bound at `(mLim+ρ, uLim, DuLim)`
    -- come from `pairing.hpair_conv` + `(pairing.data hμLim_mem).hreg_bdd`,
    -- where `hμLim_mem : (μLim, uLim, DuLim) ∈ D_set_family`.
    set μLim : (Fin d → ℝ) → ℝ := fun x => wkBundle.mLim x + ρ x with hμLim_def
    -- The triple `(μLim, uLim, DuLim) = ((fun x => mLim x + ρ x), uLim, DuLim)`
    -- lies in `D_set_family` by direct construction with the given `ρ`.
    have hμLim_mem :
        (μLim, wkBundle.uLim, wkBundle.DuLim)
            ∈ D_set_family (d := d)
                wkBundle.mLim wkBundle.uLim wkBundle.DuLim :=
      ⟨ρ, hρ_nonneg, rfl⟩
    -- `MemLpPer βBar ρ` from
    -- `(pairing.data hμLim_mem).hμ_memLp - wkBundle.hmLim_memLp`,
    -- transported across the pointwise equality
    -- `ρ =ᵐ μLim - mLim`.
    have hμLim_memLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal) μLim :=
      (pairing.data hμLim_mem).hμ_memLp
    have hρ_memLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal) ρ := by
      -- `ρ x = μLim x - wkBundle.mLim x` pointwise.
      have hsub : MeasureTheory.MemLp (μLim - wkBundle.mLim)
          (ENNReal.ofReal βBarReal)
          (MeasureTheory.volume.restrict (UnitCube d)) :=
        MeasureTheory.MemLp.sub hμLim_memLp.toMemLp wkBundle.hmLim_memLp.toMemLp
      have hae :
          (μLim - wkBundle.mLim)
            =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] ρ := by
        refine Filter.Eventually.of_forall ?_
        intro x; simp [hμLim_def, Pi.sub_apply]
      exact MemLp.toMemLpPer (hsub.ae_eq hae)
    -- Source `hpair_conv` from `pairing.hpair_conv hμLim_mem`.
    have hpair_full := pairing.hpair_conv hμLim_mem
    have hDu_eq := pairing.data_Du hμLim_mem
    have hm_eq := pairing.data_m hμLim_mem
    have hu_eq := pairing.data_u hμLim_mem
    have hDun_eq := pairing.data_Du_n hμLim_mem
    have hmn_eq := pairing.data_m_n hμLim_mem
    have hun_eq := pairing.data_u_n hμLim_mem
    rw [hDu_eq, hm_eq, hu_eq, hDun_eq, hmn_eq, hun_eq] at hpair_full
    -- Source `hreg_bdd` from `(pairing.data hμLim_mem).hreg_bdd`.
    have hreg :=
      (pairing.data hμLim_mem).hreg_bdd
    -- The `hreg` statement uses `(pairing.data …).Du_n k` and `u_n k`.
    -- We rewrite the *function* fields (`Du_n, u_n`); after the rewrites,
    -- the bound matches the helper's expected shape (the `Du_n`, `u_n`
    -- projections appear under a `(fun k => …) k` shape, definitionally
    -- equal to the direct form).
    rw [hDun_eq, hun_eq] at hreg
    -- Apply the new helper.
    exact limitPassage_setForm_of_seqVI seq
      wkBundle.mLim wkBundle.uLim wkBundle.DuLim
      wkBundle.hmLim_nonneg wkBundle.hmLim_memLp wkBundle.huLim_sob
      wkBundle.hDuLim_memLp_γ
      (fun i => wkBundle.huLim_DuLim_weakDeriv i)
      ρ hρ_nonneg hρ_memLp
      hpair_full
      hreg
  -- Specialize to the set-family test shape `(m + 1_S, u, Du)`.
  -- For each measurable set `S`, the test triple
  -- `(m + S.indicator (fun _ => 1), u, Du)` lies in `D_set_family`
  -- via `mem_D_set_family_test` (with `ρ = fun _ => 1`).
  have hFam :
      ∀ (S : Set (Fin d → ℝ)),
        0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH)
              wkBundle.DuLim wkBundle.mLim wkBundle.uLim
              (fun i x => wkBundle.DuLim i x - wkBundle.DuLim i x)
              ((wkBundle.mLim
                  + fun x => S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                  - wkBundle.mLim)
              (wkBundle.uLim - wkBundle.uLim) := by
    intro S
    have hμmem :
        ((fun x => wkBundle.mLim x +
            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x),
          wkBundle.uLim, wkBundle.DuLim)
            ∈ D_set_family (d := d)
                wkBundle.mLim wkBundle.uLim wkBundle.DuLim :=
      mem_D_set_family_test (d := d)
        wkBundle.mLim wkBundle.uLim wkBundle.DuLim
        S (fun _ => (1 : ℝ)) (fun _ => zero_le_one)
    have h := hStrongFamily hμmem
    -- The pointwise sum form `fun x ↦ mLim x + …` matches the `Pi.add`
    -- form `mLim + fun x ↦ …` definitionally.
    convert h using 2
  exact strongVI_setForm_of_setFamily (γBar := γBarReal) hFam

/-! ### Phase 6d-ii-c-2a — narrow paper-form set helper

Per `infra-P5-theorem1-phase-6d-ii-c-2a-strongVI-set-narrow-consume`,
this helper is a **new** companion to `strongVI_set_at_limit_of_paperHypotheses`
that consumes the *narrow* paper-form set domain `D_set_family_paper`
(perturbations are pointwise nonneg, **periodic**, and `MemLpPer βBar`).
It runs `main_strong_VI` on `D_set_family_paper` (which is segment-closed
by `D_set_family_paper_segment_closed`), and bridges to the public
`StrongVI_setForm` conclusion via `strongVI_setForm_of_setFamily_periodicS`.

The wider-domain `strongVI_set_at_limit_of_paperHypotheses` is **kept**
unchanged for the F0 chain consumer (`H4SimplePowerInputs_of_paperHypotheses_familyNative`)
which has not yet been migrated; the migration is filed as task c-2d. -/

/-- Periodic indicators are themselves periodic. -/
private lemma isPeriodic_indicator_one_of_isPeriodicSet
    {S : Set (Fin d → ℝ)} (hS : IsPeriodicSet (d := d) S) :
    StationaryMFG.Periodic.IsPeriodic
      (fun x : Fin d → ℝ => S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
  intro k x
  by_cases hx : x ∈ S
  · have hxk : (x + fun i => (k i : ℝ)) ∈ S := (hS k x).mp hx
    simp [Set.indicator_of_mem hx, Set.indicator_of_mem hxk]
  · have hxk : (x + fun i => (k i : ℝ)) ∉ S := fun h => hx ((hS k x).mpr h)
    simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem hxk]

/-- **F0 family producer (set form, narrow paper domain).** Companion
to `strongVI_set_at_limit_of_paperHypotheses` that consumes the narrow
paper-form domain `D_set_family_paper` (perturbations are pointwise
nonneg, periodic, and `MemLpPer βBar`).

Internally:

1. Apply `main_strong_VI` on `D_set_family_paper` using the supplied
   `mintyClosureOn` (segment closure is given by
   `D_set_family_paper_segment_closed`, threaded through the
   `mintyClosureOn.hSeg` field).
2. The resulting strong VI is quantified over triples in
   `D_set_family_paper`. Specialize to test triples
   `(mLim + S.indicator 1, uLim, DuLim)` for **periodic** measurable
   `S`: such an indicator is itself periodic (via
   `isPeriodic_indicator_one_of_isPeriodicSet`) and lies in
   `MemLpPer βBar` (`MemLp.indicator` against the constant `1`).
3. Bridge to the public `StrongVI_setForm` conclusion via
   `strongVI_setForm_of_setFamily_periodicS`. -/
noncomputable def strongVI_set_at_limit_of_paperHypotheses_paper
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (_hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (_hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (_hExp : SimplePowerExponentFacts γBarReal
                (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
                (ENNReal.ofReal βBarReal'))
    (seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH)
    (wkBundle : WeakLimitInputBundleAE (d := d) γBarReal βBarReal)
    (pairing : LimitPairingInputsFamily (d := d)
                  (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  (V := V) (H := H) (DpH := DpH)
                  seq wkBundle.mLim wkBundle.uLim wkBundle.DuLim
                  (D_set_family_paper (d := d)
                     (ENNReal.ofReal βBarReal)
                     wkBundle.mLim wkBundle.uLim wkBundle.DuLim))
    (mintyClosureOn : MintyClosureOn (d := d) V H DpH
                       wkBundle.mLim wkBundle.uLim wkBundle.DuLim
                       (D_set_family_paper (d := d)
                          (ENNReal.ofReal βBarReal)
                          wkBundle.mLim wkBundle.uLim wkBundle.DuLim)) :
    StationaryMFG.Theorems.SimplePower.StrongVI_setForm
      V H DpH γBarReal 0 wkBundle.DuLim wkBundle.mLim wkBundle.uLim := by
  let _ := hpow  -- mark used (helper does not call `hpow` directly)
  -- Step 1: strong VI on `D_set_family_paper` via `main_strong_VI`.
  have hStrongFamily :
      ∀ ⦃μ υ Dυ⦄, (μ, υ, Dυ) ∈ D_set_family_paper (d := d)
                      (ENNReal.ofReal βBarReal)
                      wkBundle.mLim wkBundle.uLim wkBundle.DuLim →
        0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH)
              wkBundle.DuLim wkBundle.mLim wkBundle.uLim
              (fun i x => Dυ i x - wkBundle.DuLim i x)
              (μ - wkBundle.mLim) (υ - wkBundle.uLim) := by
    refine StationaryMFG.Theorems.SimplePower.main_strong_VI
      (V := V) (H := H) (DpH := DpH)
      (D := D_set_family_paper (d := d)
              (ENNReal.ofReal βBarReal)
              wkBundle.mLim wkBundle.uLim wkBundle.DuLim)
      mintyClosureOn.hSeg mintyClosureOn.hAhc mintyClosureOn.hLimMem ?_
    -- Per-test-triple weak VI.
    intro μ υ Dυ hμ
    obtain ⟨ρ, hρ_nonneg, hρ_lp, _hρ_per, hpeq⟩ := hμ
    rw [Prod.mk.injEq, Prod.mk.injEq] at hpeq
    obtain ⟨hμeq, hυeq, hDυeq⟩ := hpeq
    rw [hμeq, hυeq, hDυeq]
    set μLim : (Fin d → ℝ) → ℝ := fun x => wkBundle.mLim x + ρ x with hμLim_def
    have hμLim_mem :
        (μLim, wkBundle.uLim, wkBundle.DuLim)
            ∈ D_set_family_paper (d := d)
                (ENNReal.ofReal βBarReal)
                wkBundle.mLim wkBundle.uLim wkBundle.DuLim :=
      ⟨ρ, hρ_nonneg, hρ_lp, _hρ_per, rfl⟩
    -- Source `hpair_conv` from `pairing.hpair_conv hμLim_mem`.
    have hpair_full := pairing.hpair_conv hμLim_mem
    have hDu_eq := pairing.data_Du hμLim_mem
    have hm_eq := pairing.data_m hμLim_mem
    have hu_eq := pairing.data_u hμLim_mem
    have hDun_eq := pairing.data_Du_n hμLim_mem
    have hmn_eq := pairing.data_m_n hμLim_mem
    have hun_eq := pairing.data_u_n hμLim_mem
    rw [hDu_eq, hm_eq, hu_eq, hDun_eq, hmn_eq, hun_eq] at hpair_full
    -- Source `hreg_bdd`.
    have hreg :=
      (pairing.data hμLim_mem).hreg_bdd
    rw [hDun_eq, hun_eq] at hreg
    -- Apply `limitPassage_setForm_of_seqVI`. Note: the narrow domain
    -- supplies `MemLpPer βBar ρ` directly (no need to derive it from
    -- `pairing.data`), which is the key win of the narrow domain.
    exact limitPassage_setForm_of_seqVI seq
      wkBundle.mLim wkBundle.uLim wkBundle.DuLim
      wkBundle.hmLim_nonneg wkBundle.hmLim_memLp wkBundle.huLim_sob
      wkBundle.hDuLim_memLp_γ
      (fun i => wkBundle.huLim_DuLim_weakDeriv i)
      ρ hρ_nonneg hρ_lp
      hpair_full
      hreg
  -- Step 2: specialize to periodic measurable test sets `S`.
  -- `S.indicator 1` is periodic (via `IsPeriodicSet`) and `MemLpPer βBar`
  -- (via `MemLp.indicator` against the constant `1`).
  have hFamPeriodic :
      ∀ (S : Set (Fin d → ℝ)),
        MeasurableSet S → IsPeriodicSet (d := d) S →
        0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH)
              wkBundle.DuLim wkBundle.mLim wkBundle.uLim
              (fun i x => wkBundle.DuLim i x - wkBundle.DuLim i x)
              ((wkBundle.mLim
                  + fun x => S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                  - wkBundle.mLim)
              (wkBundle.uLim - wkBundle.uLim) := by
    intro S hSmeas hSper
    -- `S.indicator 1` pointwise nonneg.
    have hIndic_nn :
        ∀ x, 0 ≤ S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
      intro x; by_cases hx : x ∈ S
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]
    -- `MemLpPer βBar (S.indicator 1)` via `MemLp.indicator` on a
    -- finite restricted measure (the cube has finite volume, so the
    -- constant `1` is `MemLp` on every restriction).
    have hcube : MeasureTheory.volume (UnitCube d) ≠ ⊤ := by simp
    haveI : MeasureTheory.IsFiniteMeasure
              (MeasureTheory.Measure.restrict MeasureTheory.volume
                (UnitCube (d := d))) :=
      ⟨by
        rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ]
        simp⟩
    have hConst_memLp :
        StationaryMFG.Periodic.MemLpPer (d := d)
          (ENNReal.ofReal βBarReal) (fun _ : Fin d → ℝ => (1 : ℝ)) :=
      StationaryMFG.Periodic.MemLp.toMemLpPer
        (MeasureTheory.memLp_const (1 : ℝ))
    have hIndic_memLp :
        StationaryMFG.Periodic.MemLpPer (d := d)
          (ENNReal.ofReal βBarReal)
          (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ))) :=
      MemLp.toMemLpPer (MeasureTheory.MemLp.indicator hSmeas.nullMeasurableSet hConst_memLp.toMemLp)
    -- The shape `S.indicator 1 : (Fin d → ℝ) → ℝ` is definitionally
    -- the lambda form `fun x => S.indicator 1 x`. Bridge via `funext`.
    have hIndic_lp_lam :
        StationaryMFG.Periodic.MemLpPer (d := d)
          (ENNReal.ofReal βBarReal)
          (fun x : Fin d → ℝ =>
            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := hIndic_memLp
    -- Periodicity of `S.indicator 1` from `IsPeriodicSet S`.
    have hIndic_per :
        StationaryMFG.Periodic.IsPeriodic
          (fun x : Fin d → ℝ =>
            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) :=
      isPeriodic_indicator_one_of_isPeriodicSet hSper
    -- Test-triple membership in the narrow paper-form domain.
    have hμmem :
        ((fun x => wkBundle.mLim x +
            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x),
          wkBundle.uLim, wkBundle.DuLim)
            ∈ D_set_family_paper (d := d)
                (ENNReal.ofReal βBarReal)
                wkBundle.mLim wkBundle.uLim wkBundle.DuLim :=
      mem_D_set_family_paper_test_periodic (d := d)
        (ENNReal.ofReal βBarReal)
        wkBundle.mLim wkBundle.uLim wkBundle.DuLim
        (fun x => S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
        hIndic_nn hIndic_lp_lam hIndic_per
    have h := hStrongFamily hμmem
    -- The pointwise sum form `fun x ↦ mLim x + …` matches the `Pi.add`
    -- form `mLim + fun x ↦ …` definitionally.
    convert h using 2
  -- Step 3: bridge to public `StrongVI_setForm` via the periodic-S
  -- specializer.
  exact strongVI_setForm_of_setFamily_periodicS (γBar := γBarReal)
    hFamPeriodic

/-- **F0 family producer (signed set form).**

Phase 4b (task `infra-P4-minty-family-native-4b-signed`): now consumes
a per-family `MintyClosureOn D_signed_family` certificate instead of a
universal `MintyClosure (D = Set.univ)` plus `hDuniv` shortcut. The
Minty argument runs on `D_signed_family` via `main_strong_VI`, and the
final specialization to `StrongVI_setForm_signed` uses
`strongVI_setFormSigned_of_signedFamily` (the family-shaped specializer
landed by Child 1 of the Phase F strip refactor).

**Phase 5a-signed** (`infra-P5-theorem1-phase-5a-signed-drop-hVI-eps-universal`,
iter 362 retry after iter 361's user-triple field unblocker): the
per-test-triple weak VI is now produced by the new helper
`limitPassage_signedForm_of_seqVI_empty`, which consumes the per-`k`
regularised paper-family VI `(seq.sol k).hVIeps_signed_user_triple`
directly (bypassing `pairing.data μ υ Dυ.hVI_eps`, hence bypassing
`T10PaperResidues.hVI_eps_universalOf` for the signed family). Because
the user-triple field requires a nonneg primal `μ ≥ 0`, the Minty step
runs on the narrowed family `D_signed_family_nn` (built from the wider
`mintyClosureOn` via `mintyClosureOn_signed_nn_of_wider`); signed-test
triples `(mLim + σ·mLim·1_S, uLim, DuLim)` for σ ∈ {±1} lie in the
narrower family by `mem_D_signed_family_nn_test`. The pairing-
convergence and Gateaux-residual inputs to the helper are still sourced
from `pairing.hpair_conv` and `(pairing.data μ υ Dυ).hreg_bdd`, so the
`pairing : LimitPairingInputs` parameter remains. Full removal of that
parameter is out of scope for this child. -/
noncomputable def strongVI_signed_at_limit_of_paperHypotheses
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
    (pairing : LimitPairingInputsFamily (d := d)
                  (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  (V := V) (H := H) (DpH := DpH)
                  seq wkBundle.mLim wkBundle.uLim wkBundle.DuLim
                  (D_signed_family_nn (d := d)
                     wkBundle.mLim wkBundle.uLim wkBundle.DuLim))
    (mintyClosureOn : MintyClosureOn (d := d) V H DpH
                       wkBundle.mLim wkBundle.uLim wkBundle.DuLim
                       (D_signed_family (d := d)
                          wkBundle.mLim wkBundle.uLim wkBundle.DuLim)) :
    StationaryMFG.Theorems.SimplePower.StrongVI_setForm_signed
      V H DpH γBarReal 0 wkBundle.DuLim wkBundle.mLim wkBundle.uLim := by
  -- Phase 6c-iii: `pairing` is now an `LimitPairingInputsFamily` at
  -- `D_signed_family_nn`. The narrowing to `D_signed_family_nn` (from
  -- the wider `D_signed_family` carried by `mintyClosureOn`) is
  -- pushed up into the family-domain choice of the pairing.
  -- Phase 5a-signed: narrow the family from `D_signed_family` to its
  -- nonneg-primal subfamily `D_signed_family_nn`, on which the
  -- helper-based `hWeak_per_triple` is well-defined.
  have mintyClosureOn_nn :=
    mintyClosureOn_signed_nn_of_wider (V := V) (H := H) (DpH := DpH)
      wkBundle.mLim wkBundle.uLim wkBundle.DuLim
      wkBundle.hmLim_nonneg mintyClosureOn
  -- Per-test-triple weak VI on the narrower nonneg-primal family,
  -- supplied via the new helper `limitPassage_signedForm_of_seqVI_empty`.
  -- For triples `(μ, υ, Dυ) ∈ D_signed_family_nn`, `υ = uLim, Dυ = DuLim`
  -- and `μ ≥ 0` a.e. The helper at `S := ∅` covers exactly this shape.
  have hWeak_per_triple_nn :
      ∀ ⦃μ υ Dυ⦄, (μ, υ, Dυ) ∈ D_signed_family_nn (d := d)
                      wkBundle.mLim wkBundle.uLim wkBundle.DuLim →
        0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
              (fun i x => Dυ i x - wkBundle.DuLim i x)
              (μ - wkBundle.mLim) (υ - wkBundle.uLim) := by
    intro μ υ Dυ hmem
    obtain ⟨⟨g, hpeq⟩, hμ_nn⟩ := hmem
    -- Decompose the triple: `μ = mLim + g, υ = uLim, Dυ = DuLim`.
    rw [Prod.mk.injEq, Prod.mk.injEq] at hpeq
    obtain ⟨hμeq, hυeq, hDυeq⟩ := hpeq
    rw [hμeq, hυeq, hDυeq]
    -- Build the family-membership of the (post-rewrite) triple in
    -- `D_signed_family_nn`. The witness `g` is the same; nonneg
    -- primal carries from `hμ_nn` after rewriting `μ`.
    have hμ_nn' :
        ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
          0 ≤ wkBundle.mLim x + g x := by
      have hμ_nn₀ :
          ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
            0 ≤ μ x := hμ_nn
      filter_upwards [hμ_nn₀] with x hx
      have : μ x = wkBundle.mLim x + g x := by rw [hμeq]
      rw [← this]
      exact hx
    have hμGmem :
        ((fun x => wkBundle.mLim x + g x), wkBundle.uLim, wkBundle.DuLim)
            ∈ D_signed_family_nn (d := d)
                wkBundle.mLim wkBundle.uLim wkBundle.DuLim := by
      refine ⟨⟨g, rfl⟩, ?_⟩
      -- Goal: `0 ≤ᵐ ((fun x => mLim x + g x), uLim, DuLim).1 = (fun x => mLim x + g x)`.
      simpa using! hμ_nn'
    -- Source `hμ_user_memLp` from `pairing.data hμGmem`.
    have hμ_memLp :
        MemLpPer (d := d) (ENNReal.ofReal βBarReal)
          (fun x => wkBundle.mLim x + g x) :=
      (pairing.data hμGmem).hμ_memLp
    -- Source `hpair_conv` and `hreg_bdd` from `pairing`.
    have hpair_full := pairing.hpair_conv hμGmem
    have hDu_eq := pairing.data_Du hμGmem
    have hm_eq := pairing.data_m hμGmem
    have hu_eq := pairing.data_u hμGmem
    have hDun_eq := pairing.data_Du_n hμGmem
    have hmn_eq := pairing.data_m_n hμGmem
    have hun_eq := pairing.data_u_n hμGmem
    rw [hDu_eq, hm_eq, hu_eq, hDun_eq, hmn_eq, hun_eq] at hpair_full
    have hreg :=
      (pairing.data hμGmem).hreg_bdd
    rw [hDun_eq, hun_eq] at hreg
    -- Apply the empty-set corollary helper. (`hμ_nn'` was constructed
    -- above for the `D_signed_family_nn` membership.)
    exact limitPassage_signedForm_of_seqVI_empty (V := V) (H := H) (DpH := DpH)
      seq wkBundle.mLim wkBundle.uLim wkBundle.DuLim
      wkBundle.huLim_sob wkBundle.hDuLim_memLp_γ
      (fun i => wkBundle.huLim_DuLim_weakDeriv i)
      (fun x => wkBundle.mLim x + g x) hμ_nn' hμ_memLp
      hpair_full hreg
  -- Upgrade weak VI to strong VI on `D_signed_family_nn` via `main_strong_VI`.
  have hStrongFamily_nn :
      ∀ ⦃μ υ Dυ⦄, (μ, υ, Dυ) ∈ D_signed_family_nn (d := d)
                      wkBundle.mLim wkBundle.uLim wkBundle.DuLim →
        0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH)
              wkBundle.DuLim wkBundle.mLim wkBundle.uLim
              (fun i x => Dυ i x - wkBundle.DuLim i x)
              (μ - wkBundle.mLim) (υ - wkBundle.uLim) := by
    refine StationaryMFG.Theorems.SimplePower.main_strong_VI
      (V := V) (H := H) (DpH := DpH)
      (D := D_signed_family_nn (d := d)
              wkBundle.mLim wkBundle.uLim wkBundle.DuLim)
      mintyClosureOn_nn.hSeg mintyClosureOn_nn.hAhc
      mintyClosureOn_nn.hLimMem ?_
    intro μ υ Dυ hμ
    exact hWeak_per_triple_nn hμ
  -- Specialize to the signed-family test shape `(m + σ·m·1_S, u, Du)`.
  -- For each `σ ∈ {±1}` and measurable set `S`, the signed-test triple
  -- lies in `D_signed_family_nn` via `mem_D_signed_family_nn_test`.
  have hFam :
      ∀ (σ : ℝ), σ = 1 ∨ σ = -1 → ∀ (S : Set (Fin d → ℝ)),
        0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH)
              wkBundle.DuLim wkBundle.mLim wkBundle.uLim
              (fun i x => wkBundle.DuLim i x - wkBundle.DuLim i x)
              ((wkBundle.mLim
                  + fun x => σ * wkBundle.mLim x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                  - wkBundle.mLim)
              (wkBundle.uLim - wkBundle.uLim) := by
    intro σ hσ S
    have hμmem :
        ((fun x => wkBundle.mLim x +
            σ * wkBundle.mLim x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x),
          wkBundle.uLim, wkBundle.DuLim)
            ∈ D_signed_family_nn (d := d)
                wkBundle.mLim wkBundle.uLim wkBundle.DuLim :=
      mem_D_signed_family_nn_test (d := d)
        wkBundle.mLim wkBundle.uLim wkBundle.DuLim
        wkBundle.hmLim_nonneg σ hσ S
    have h := hStrongFamily_nn hμmem
    -- The pointwise sum form `fun x ↦ mLim x + …` matches the `Pi.add`
    -- form `mLim + fun x ↦ …` definitionally.
    convert h using 2
  -- Specialize via the σ ∈ {±1}-restricted specializer
  -- `strongVI_setFormSigned_of_signedFamily_pmone`, which exactly
  -- matches the σ-restriction in `mem_D_signed_family_nn_test`.
  exact strongVI_setFormSigned_of_signedFamily_pmone (γBar := γBarReal) hFam

/-! ### Phase 6d-ii-c-2c — narrow paper-form signed helper

Per `infra-P5-theorem1-phase-6d-ii-c-2c-strongVI-signed-narrow-consume`,
this helper is a **new** companion to
`strongVI_signed_at_limit_of_paperHypotheses` that consumes the
*narrow* paper-form signed (nonneg-primal) domain
`D_signed_family_paper_nn` (perturbations are periodic and
`MemLpPer βBar`, with primal density a.e. nonneg). It runs
`main_strong_VI` on `D_signed_family_paper_nn` (segment-closed via
`D_signed_family_paper_nn_segment_closed`), and bridges to the
public `StrongVI_setForm_signed` conclusion via
`strongVI_setFormSigned_of_signedFamily_pmone_periodicS`.

The wider-domain `strongVI_signed_at_limit_of_paperHypotheses` is
**kept** unchanged for the F0 chain consumer, which has not yet
been migrated; that migration is filed as task c-2d. -/

/-- **F0 family producer (signed set form, narrow paper domain).**
Companion to `strongVI_signed_at_limit_of_paperHypotheses` that
consumes the narrow paper-form signed domain
`D_signed_family_paper_nn` (perturbations are periodic and
`MemLpPer βBar`, with primal density a.e. nonneg).

Internally:

1. Apply `main_strong_VI` on `D_signed_family_paper_nn` using the
   supplied `mintyClosureOn`. The per-test-triple weak VI is
   produced via `limitPassage_signedForm_of_seqVI_empty` (the
   same helper used in the wider variant — the narrow domain only
   adds periodicity/`Lᵖ` certificates which are not needed by the
   helper).
2. Specialize to test triples
   `(mLim + σ·mLim·1_S, uLim, DuLim)` for `σ ∈ {±1}` and
   **periodic** measurable `S`. Each such perturbation is
   periodic (via `wkBundle.hMlimPer` + indicator periodicity) and
   `MemLpPer βBar` (via `MemLp.indicator` on `σ • mLim`), so the
   triple lies in `D_signed_family_paper_nn`.
3. Bridge to the public `StrongVI_setForm_signed` via
   `strongVI_setFormSigned_of_signedFamily_pmone_periodicS`. -/
noncomputable def strongVI_signed_at_limit_of_paperHypotheses_paper
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
    (pairing : LimitPairingInputsFamily (d := d)
                  (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  (V := V) (H := H) (DpH := DpH)
                  seq wkBundle.mLim wkBundle.uLim wkBundle.DuLim
                  (D_signed_family_paper_nn (d := d)
                     (ENNReal.ofReal βBarReal)
                     wkBundle.mLim wkBundle.uLim wkBundle.DuLim))
    (mintyClosureOn : MintyClosureOn (d := d) V H DpH
                       wkBundle.mLim wkBundle.uLim wkBundle.DuLim
                       (D_signed_family_paper_nn (d := d)
                          (ENNReal.ofReal βBarReal)
                          wkBundle.mLim wkBundle.uLim wkBundle.DuLim)) :
    StationaryMFG.Theorems.SimplePower.StrongVI_setForm_signed
      V H DpH γBarReal 0 wkBundle.DuLim wkBundle.mLim wkBundle.uLim := by
  -- Step 1: per-test-triple weak VI on the narrow paper-form signed
  -- domain, supplied via `limitPassage_signedForm_of_seqVI_empty`.
  have hWeak_per_triple :
      ∀ ⦃μ υ Dυ⦄, (μ, υ, Dυ) ∈ D_signed_family_paper_nn (d := d)
                      (ENNReal.ofReal βBarReal)
                      wkBundle.mLim wkBundle.uLim wkBundle.DuLim →
        0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
              (fun i x => Dυ i x - wkBundle.DuLim i x)
              (μ - wkBundle.mLim) (υ - wkBundle.uLim) := by
    intro μ υ Dυ hmem
    obtain ⟨g, hg_lp, _hg_per, hμnn, hpeq⟩ := hmem
    -- Decompose the triple: `μ = mLim + g, υ = uLim, Dυ = DuLim`.
    rw [Prod.mk.injEq, Prod.mk.injEq] at hpeq
    obtain ⟨hμeq, hυeq, hDυeq⟩ := hpeq
    rw [hμeq, hυeq, hDυeq]
    -- Build the family-membership of the (post-rewrite) triple in
    -- `D_signed_family_paper_nn`.
    have hμGmem :
        ((fun x => wkBundle.mLim x + g x), wkBundle.uLim, wkBundle.DuLim)
            ∈ D_signed_family_paper_nn (d := d)
                (ENNReal.ofReal βBarReal)
                wkBundle.mLim wkBundle.uLim wkBundle.DuLim := by
      refine ⟨g, hg_lp, _hg_per, ?_, rfl⟩
      exact hμnn
    -- Source `μ_user` regularity from the narrow domain and `wkBundle`.
    have hμ_memLp :
        MemLpPer (d := d) (ENNReal.ofReal βBarReal)
          (fun x => wkBundle.mLim x + g x) := by
      -- `(mLim + g)` as bare-pointwise-sum equals the `Pi.add` form.
      have hsum :
          (fun x : (Fin d → ℝ) => wkBundle.mLim x + g x)
            = wkBundle.mLim + g := by
        funext x; rfl
      rw [hsum]
      exact wkBundle.hmLim_memLp.add hg_lp
    -- Source `hpair_conv` and `hreg_bdd` from `pairing`.
    have hpair_full := pairing.hpair_conv hμGmem
    have hDu_eq := pairing.data_Du hμGmem
    have hm_eq := pairing.data_m hμGmem
    have hu_eq := pairing.data_u hμGmem
    have hDun_eq := pairing.data_Du_n hμGmem
    have hmn_eq := pairing.data_m_n hμGmem
    have hun_eq := pairing.data_u_n hμGmem
    rw [hDu_eq, hm_eq, hu_eq, hDun_eq, hmn_eq, hun_eq] at hpair_full
    have hreg :=
      (pairing.data hμGmem).hreg_bdd
    rw [hDun_eq, hun_eq] at hreg
    -- Apply the empty-set corollary helper.
    exact limitPassage_signedForm_of_seqVI_empty (V := V) (H := H) (DpH := DpH)
      seq wkBundle.mLim wkBundle.uLim wkBundle.DuLim
      wkBundle.huLim_sob wkBundle.hDuLim_memLp_γ
      (fun i => wkBundle.huLim_DuLim_weakDeriv i)
      (fun x => wkBundle.mLim x + g x) hμnn hμ_memLp
      hpair_full hreg
  -- Step 2: upgrade weak VI to strong VI on `D_signed_family_paper_nn`
  -- via `main_strong_VI`.
  have hStrongFamily :
      ∀ ⦃μ υ Dυ⦄, (μ, υ, Dυ) ∈ D_signed_family_paper_nn (d := d)
                      (ENNReal.ofReal βBarReal)
                      wkBundle.mLim wkBundle.uLim wkBundle.DuLim →
        0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH)
              wkBundle.DuLim wkBundle.mLim wkBundle.uLim
              (fun i x => Dυ i x - wkBundle.DuLim i x)
              (μ - wkBundle.mLim) (υ - wkBundle.uLim) := by
    refine StationaryMFG.Theorems.SimplePower.main_strong_VI
      (V := V) (H := H) (DpH := DpH)
      (D := D_signed_family_paper_nn (d := d)
              (ENNReal.ofReal βBarReal)
              wkBundle.mLim wkBundle.uLim wkBundle.DuLim)
      mintyClosureOn.hSeg mintyClosureOn.hAhc mintyClosureOn.hLimMem ?_
    intro μ υ Dυ hμ
    exact hWeak_per_triple hμ
  -- Step 3: specialize to periodic measurable test sets `S` for σ ∈ {±1}.
  have hFamPeriodic :
      ∀ (σ : ℝ), σ = 1 ∨ σ = -1 → ∀ (S : Set (Fin d → ℝ)),
        MeasurableSet S → IsPeriodicSet (d := d) S →
        0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH)
              wkBundle.DuLim wkBundle.mLim wkBundle.uLim
              (fun i x => wkBundle.DuLim i x - wkBundle.DuLim i x)
              ((wkBundle.mLim
                  + fun x => σ * wkBundle.mLim x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                  - wkBundle.mLim)
              (wkBundle.uLim - wkBundle.uLim) := by
    intro σ hσ S hSmeas hSper
    -- The signed perturbation `g := σ · mLim · 1_S`.
    -- (a) `MemLpPer βBar (σ · mLim · 1_S)`.
    have hcube : MeasureTheory.volume (UnitCube d) ≠ ⊤ := by simp
    haveI : MeasureTheory.IsFiniteMeasure
              (MeasureTheory.Measure.restrict MeasureTheory.volume
                (UnitCube (d := d))) :=
      ⟨by
        rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ]
        simp⟩
    -- `σ • mLim ∈ MemLpPer βBar`.
    have hσm_memLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal)
                        (fun x => σ * wkBundle.mLim x) := by
      have hsmul := wkBundle.hmLim_memLp.const_smul (𝕜 := ℝ) σ
      -- `wkBundle.hmLim_memLp.const_smul` gives `MemLpPer βBar (σ • wkBundle.mLim)`;
      -- rewrite via the pointwise identity.
      have heq : (σ • (wkBundle.mLim : (Fin d → ℝ) → ℝ))
                    = fun x => σ * wkBundle.mLim x := by
        funext x; rfl
      exact heq ▸ hsmul
    -- Indicator-restricted version: `S.indicator (σ · mLim) ∈ MemLpPer βBar`.
    have hSσm_memLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal)
                        (S.indicator (fun x => σ * wkBundle.mLim x)) :=
      MemLp.toMemLpPer (MeasureTheory.MemLp.indicator hSmeas.nullMeasurableSet hσm_memLp.toMemLp)
    -- Pointwise rewrite to `σ · mLim x · 1_S(x)`.
    have hSσm_eq : ∀ x : Fin d → ℝ,
        S.indicator (fun x => σ * wkBundle.mLim x) x
          = σ * wkBundle.mLim x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
      intro x
      by_cases hx : x ∈ S
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]
    have hSσm_funEq :
        (S.indicator (fun x => σ * wkBundle.mLim x) : (Fin d → ℝ) → ℝ)
          = fun x => σ * wkBundle.mLim x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
      funext x; exact hSσm_eq x
    have hSσm_memLp' : MemLpPer (d := d) (ENNReal.ofReal βBarReal)
                          (fun x => σ * wkBundle.mLim x *
                              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
      rw [← hSσm_funEq]; exact hSσm_memLp
    -- (b) Periodicity of `σ · mLim · 1_S`.
    -- Periodicity of `1_S` from `IsPeriodicSet S`.
    have hIndic_per :
        StationaryMFG.Periodic.IsPeriodic
          (fun x : Fin d → ℝ =>
            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) :=
      isPeriodic_indicator_one_of_isPeriodicSet hSper
    -- Periodicity of `mLim · 1_S` (derive directly from `hMlimPer` and
    -- `hIndic_per`; we don't have a multiplication lemma for `IsPeriodic`).
    have hmLim_indic_per :
        StationaryMFG.Periodic.IsPeriodic
          (fun x : Fin d → ℝ => wkBundle.mLim x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
      intro k x
      -- `wkBundle.mLim = wkBundle.mRep.rep` (def); rewrite both factors
      -- via their respective periodicities.
      show wkBundle.mLim (x + fun i => (k i : ℝ)) *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ))
                (x + fun i => (k i : ℝ))
            = wkBundle.mLim x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
      have hM : wkBundle.mLim (x + fun i => (k i : ℝ)) = wkBundle.mLim x :=
        wkBundle.hMlimPer k x
      have hI :
          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ))
              (x + fun i => (k i : ℝ))
            = S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x :=
        hIndic_per k x
      rw [hM, hI]
    -- Periodicity of `σ · mLim · 1_S` via `IsPeriodic.smul`.
    have hSσm_per :
        StationaryMFG.Periodic.IsPeriodic
          (fun x : Fin d → ℝ => σ * wkBundle.mLim x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
      have h1 := hmLim_indic_per.smul σ
      have heq :
          (σ • (fun x : Fin d → ℝ => wkBundle.mLim x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
            = fun x => σ * wkBundle.mLim x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
        funext x
        show σ * (wkBundle.mLim x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              = σ * wkBundle.mLim x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
        ring
      rw [heq] at h1; exact h1
    -- (c) Primal density `mLim + σ · mLim · 1_S ≥ 0` a.e.
    have hμ_nn :
        ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
          (0 : ℝ) ≤ wkBundle.mLim x + σ * wkBundle.mLim x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
      filter_upwards [wkBundle.hmLim_nonneg] with x hxm
      classical
      by_cases hxS : x ∈ S
      · -- Inside S: indicator = 1, primal = mLim · (1+σ).
        have hind : S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x = 1 :=
          Set.indicator_of_mem hxS _
        rw [hind]
        have hxm' : (0 : ℝ) ≤ wkBundle.mLim x := hxm
        rcases hσ with h1 | hm1
        · subst h1; linarith
        · subst hm1; linarith
      · -- Outside S: indicator = 0, primal = mLim ≥ 0.
        have hind : S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x = 0 :=
          Set.indicator_of_notMem hxS _
        rw [hind]
        have hxm' : (0 : ℝ) ≤ wkBundle.mLim x := hxm
        linarith
    -- Test-triple membership in `D_signed_family_paper_nn`.
    have hμmem :
        ((fun x => wkBundle.mLim x +
            σ * wkBundle.mLim x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x),
          wkBundle.uLim, wkBundle.DuLim)
            ∈ D_signed_family_paper_nn (d := d)
                (ENNReal.ofReal βBarReal)
                wkBundle.mLim wkBundle.uLim wkBundle.DuLim := by
      refine ⟨fun x => σ * wkBundle.mLim x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x,
              hSσm_memLp', hSσm_per, ?_, rfl⟩
      exact hμ_nn
    have h := hStrongFamily hμmem
    -- The pointwise sum form `fun x ↦ mLim x + …` matches the `Pi.add`
    -- form `mLim + fun x ↦ …` definitionally.
    convert h using 2
  -- Step 4: bridge to public `StrongVI_setForm_signed` via the
  -- σ ∈ {±1}, periodic-S specializer.
  exact strongVI_setFormSigned_of_signedFamily_pmone_periodicS
    (γBar := γBarReal) hFamPeriodic

/-- **F0 family producer (transport form).**

Phase 4c (task `infra-P4-minty-family-native-4c-transport`): now consumes
a per-family `MintyClosureOn D_transport_family` certificate instead of a
universal `MintyClosure (D = Set.univ)` plus `hDuniv` shortcut. The
Minty argument runs on `D_transport_family` via `main_strong_VI`, and the
final specialization to `StrongVI_transportForm` uses
`strongVI_transportForm_of_transportFamily` (the family-shaped specializer
landed by Child 1 of the Phase F strip refactor).

**Phase 5a-transport** (`infra-P5-theorem1-phase-5a-transport-drop-hVI-eps-universal`):
the per-test-triple weak VI is now produced by the new helper
`limitPassage_transportForm_of_seqVI`, which consumes the per-`k`
regularised paper-family VI `(seq.sol k).hVIeps_transport` directly
(bypassing `pairing.data μ υ Dυ.hVI_eps`, hence bypassing
`T10PaperResidues.hVI_eps_universalOf` for the transport family).
Test-triple regularity (`MemSobolevPer γBar υ`, `MemLpPer γBar (Dυ i)`)
is supplied via the new `regSupplier` parameter; in the chain it is
sourced from `T10PaperResidues.regBundle`. The pairing-convergence
and Gateaux-residual inputs are still sourced from `pairing.hpair_conv`
and `(pairing.data μ υ Dυ).hreg_bdd`, so the `pairing : LimitPairingInputs`
parameter remains. Full removal of that parameter is out of scope. -/
noncomputable def strongVI_transport_at_limit_of_paperHypotheses
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
    (pairing : LimitPairingInputsFamily (d := d)
                  (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  (V := V) (H := H) (DpH := DpH)
                  seq wkBundle.mLim wkBundle.uLim wkBundle.DuLim
                  (D_transport_family (d := d)
                     wkBundle.mLim wkBundle.uLim wkBundle.DuLim))
    (mintyClosureOn : MintyClosureOn (d := d) V H DpH
                       wkBundle.mLim wkBundle.uLim wkBundle.DuLim
                       (D_transport_family (d := d)
                          wkBundle.mLim wkBundle.uLim wkBundle.DuLim))
    -- Per-test-triple regularity supplier. In the bridge it is
    -- discharged via `T10PaperResidues.regBundle` (a paper-trivial
    -- residue when test triples are smooth periodic).
    --
    -- **Phase 6d-i** (`infra-P5-theorem1-phase-6d-i-strongVI-transport-familyRestrict-regSupplier`):
    -- the supplier is now family-restricted to triples in
    -- `D_transport_family mLim uLim DuLim`. Triples in this family have
    -- the canonical form `(mLim, υ, Dυ)`, so callers can construct the
    -- supplier inline from `PerTestTripleRegularity.transport_perturbation`
    -- applied to `wkBundle.perTestTripleBase` (regBundle removal in 6d).
    (regSupplier :
      ∀ ⦃μ : (Fin d → ℝ) → ℝ⦄
        ⦃υ : (Fin d → ℝ) → ℝ⦄
        ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
          (μ, υ, Dυ) ∈ D_transport_family (d := d)
                          wkBundle.mLim wkBundle.uLim wkBundle.DuLim →
            MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ ∧
              ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i))
    -- **Phase 5 step3d** (`paperSolFor-final-phase5-hWeakDeriv-step3d-bareSolK_W-fields-take-hWeak_υ`):
    -- the W-form hVIeps_transport field now requires a weak-derivative
    -- tie on the user-supplied test pair `(υ, Dυ)`. Surfaced as a
    -- per-test-triple supplier mirroring `regSupplier`.
    (hWeakSupplier :
      ∀ ⦃μ : (Fin d → ℝ) → ℝ⦄
        ⦃υ : (Fin d → ℝ) → ℝ⦄
        ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
          (μ, υ, Dυ) ∈ D_transport_family (d := d)
                          wkBundle.mLim wkBundle.uLim wkBundle.DuLim →
            ∀ i, HasWeakDerivPer (d := d) i υ (Dυ i)) :
    StationaryMFG.Theorems.SimplePower.StrongVI_transportForm
      V H DpH γBarReal 0 wkBundle.DuLim wkBundle.mLim wkBundle.uLim := by
  -- Per Phase 5a-transport: per-test-triple weak VI on `D_transport_family`
  -- is now produced by `limitPassage_transportForm_of_seqVI`, which
  -- consumes `(seq.sol k).hVIeps_transport` directly (bypassing the
  -- universal `hVI_eps`).
  -- Upgrade weak VI to strong VI on `D_transport_family` via `main_strong_VI`.
  have hStrongFamily :
      ∀ ⦃μ υ Dυ⦄, (μ, υ, Dυ) ∈ D_transport_family (d := d)
                      wkBundle.mLim wkBundle.uLim wkBundle.DuLim →
        0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH)
              wkBundle.DuLim wkBundle.mLim wkBundle.uLim
              (fun i x => Dυ i x - wkBundle.DuLim i x)
              (μ - wkBundle.mLim) (υ - wkBundle.uLim) := by
    refine StationaryMFG.Theorems.SimplePower.main_strong_VI
      (V := V) (H := H) (DpH := DpH)
      (D := D_transport_family (d := d)
              wkBundle.mLim wkBundle.uLim wkBundle.DuLim)
      mintyClosureOn.hSeg mintyClosureOn.hAhc mintyClosureOn.hLimMem ?_
    -- Per-test-triple weak VI for triples in `D_transport_family`. Each
    -- such triple has shape `(mLim, υ, Dυ)` (i.e., `μ = mLim`).
    intro μ υ Dυ hμ
    -- `hμ : (μ, υ, Dυ).1 = mLim`, i.e., `μ = mLim`.
    have hμeq : μ = wkBundle.mLim := hμ
    -- The post-substitution triple `(mLim, υ, Dυ)` lies in
    -- `D_transport_family` definitionally (`.1 = mLim`).
    have hμmem :
        (wkBundle.mLim, υ, Dυ)
            ∈ D_transport_family (d := d)
                wkBundle.mLim wkBundle.uLim wkBundle.DuLim := rfl
    subst hμeq
    -- The pairing-convergence and Gateaux bound at `(mLim, υ, Dυ)`
    -- come from `pairing.hpair_conv hμmem` + `(pairing.data hμmem).hreg_bdd`.
    obtain ⟨hυ_memSob, hDυ_memLp⟩ := regSupplier hμmem
    have hpair_full := pairing.hpair_conv hμmem
    have hDu_eq := pairing.data_Du hμmem
    have hm_eq := pairing.data_m hμmem
    have hu_eq := pairing.data_u hμmem
    have hDun_eq := pairing.data_Du_n hμmem
    have hmn_eq := pairing.data_m_n hμmem
    have hun_eq := pairing.data_u_n hμmem
    rw [hDu_eq, hm_eq, hu_eq, hDun_eq, hmn_eq, hun_eq] at hpair_full
    have hreg :=
      (pairing.data hμmem).hreg_bdd
    rw [hDun_eq, hun_eq] at hreg
    -- Apply the new helper.
    exact limitPassage_transportForm_of_seqVI seq
      wkBundle.mLim wkBundle.uLim wkBundle.DuLim
      wkBundle.hmLim_nonneg wkBundle.hmLim_memLp
      υ Dυ hυ_memSob hDυ_memLp (hWeakSupplier hμmem)
      hpair_full
      hreg
  -- Specialize to the transport-family test shape
  -- `(mLim, uLim + σ·φ, DuLim + σ·∂φ)`. For each `σ ∈ ℝ` and smooth-
  -- periodic test function `φ`, the test triple lies in
  -- `D_transport_family` via `mem_D_transport_family_test`.
  have hFam :
      ∀ (σ : ℝ) (φ : StationaryMFG.Periodic.SmoothPeriodic d),
        0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH)
              wkBundle.DuLim wkBundle.mLim wkBundle.uLim
              (fun i x => (wkBundle.DuLim i x + σ *
                  ((StationaryMFG.Periodic.SmoothPeriodic.partialDeriv i φ
                      : StationaryMFG.Periodic.SmoothPeriodic d) :
                    (Fin d → ℝ) → ℝ) x) - wkBundle.DuLim i x)
              (wkBundle.mLim - wkBundle.mLim)
              ((wkBundle.uLim + fun x => σ * (φ : (Fin d → ℝ) → ℝ) x)
                  - wkBundle.uLim) := by
    intro σ φ
    have hμmem :
        (wkBundle.mLim,
          (wkBundle.uLim + fun x => σ * (φ : (Fin d → ℝ) → ℝ) x),
          (fun i x => wkBundle.DuLim i x + σ *
            ((StationaryMFG.Periodic.SmoothPeriodic.partialDeriv i φ
                : StationaryMFG.Periodic.SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) x))
            ∈ D_transport_family (d := d)
                wkBundle.mLim wkBundle.uLim wkBundle.DuLim :=
      mem_D_transport_family_test (d := d)
        wkBundle.mLim wkBundle.uLim wkBundle.DuLim σ φ
    exact hStrongFamily hμmem
  exact strongVI_transportForm_of_transportFamily (γBar := γBarReal) hFam

/-! ### Phase 6d-ii-d-2 — narrow paper-form transport helper

Per `infra-P5-theorem1-phase-6d-ii-d-2-narrow-transport-regSupplier`,
this helper is a **new** companion to
`strongVI_transport_at_limit_of_paperHypotheses` that consumes the
*narrow* paper-form transport domain `D_transport_family_paper`
(perturbations are smooth periodic). It runs `main_strong_VI` on
`D_transport_family_paper` (segment-closed via
`D_transport_family_paper_segment_closed`), and bridges to the
public `StrongVI_transportForm` conclusion via
`strongVI_transportForm_of_transportFamily`.

The wider-domain `strongVI_transport_at_limit_of_paperHypotheses`
is **kept** unchanged for callers that have not yet been migrated. -/

/-- **F0 family producer (transport form, narrow paper domain).**
Companion to `strongVI_transport_at_limit_of_paperHypotheses` that
consumes the narrow paper-form transport domain
`D_transport_family_paper` (perturbations are smooth periodic).

The narrow domain admits a `regSupplier_paper` discharged from
`wkBundle.perTestTripleBase` plus
`PerTestTripleRegularity.transport_perturbation` (no
`T10PaperResidues.regBundle` consumed). -/
noncomputable def strongVI_transport_at_limit_of_paperHypotheses_paper
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
    (pairing : LimitPairingInputsFamily (d := d)
                  (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  (V := V) (H := H) (DpH := DpH)
                  seq wkBundle.mLim wkBundle.uLim wkBundle.DuLim
                  (D_transport_family_paper (d := d)
                     wkBundle.mLim wkBundle.uLim wkBundle.DuLim))
    (mintyClosureOn : MintyClosureOn (d := d) V H DpH
                       wkBundle.mLim wkBundle.uLim wkBundle.DuLim
                       (D_transport_family_paper (d := d)
                          wkBundle.mLim wkBundle.uLim wkBundle.DuLim))
    (regSupplier :
      ∀ ⦃μ : (Fin d → ℝ) → ℝ⦄
        ⦃υ : (Fin d → ℝ) → ℝ⦄
        ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
          (μ, υ, Dυ) ∈ D_transport_family_paper (d := d)
                          wkBundle.mLim wkBundle.uLim wkBundle.DuLim →
            MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ ∧
              ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i))
    -- **Phase 5 step3d**: weak-derivative tie supplier per test triple.
    (hWeakSupplier :
      ∀ ⦃μ : (Fin d → ℝ) → ℝ⦄
        ⦃υ : (Fin d → ℝ) → ℝ⦄
        ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
          (μ, υ, Dυ) ∈ D_transport_family_paper (d := d)
                          wkBundle.mLim wkBundle.uLim wkBundle.DuLim →
            ∀ i, HasWeakDerivPer (d := d) i υ (Dυ i)) :
    StationaryMFG.Theorems.SimplePower.StrongVI_transportForm
      V H DpH γBarReal 0 wkBundle.DuLim wkBundle.mLim wkBundle.uLim := by
  -- Step 1: per-test-triple weak VI on the narrow paper-form transport
  -- domain. Each triple has shape `(mLim, uLim + ψ, DuLim + ∂ψ)`.
  have hStrongFamily :
      ∀ ⦃μ υ Dυ⦄, (μ, υ, Dυ) ∈ D_transport_family_paper (d := d)
                      wkBundle.mLim wkBundle.uLim wkBundle.DuLim →
        0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH)
              wkBundle.DuLim wkBundle.mLim wkBundle.uLim
              (fun i x => Dυ i x - wkBundle.DuLim i x)
              (μ - wkBundle.mLim) (υ - wkBundle.uLim) := by
    refine StationaryMFG.Theorems.SimplePower.main_strong_VI
      (V := V) (H := H) (DpH := DpH)
      (D := D_transport_family_paper (d := d)
              wkBundle.mLim wkBundle.uLim wkBundle.DuLim)
      mintyClosureOn.hSeg mintyClosureOn.hAhc mintyClosureOn.hLimMem ?_
    intro μ υ Dυ hμ
    -- Destructure the narrow membership: `(μ, υ, Dυ) =
    --   (mLim, uLim + ψ, DuLim + ∂ψ)` for some `ψ : SmoothPeriodic d`.
    obtain ⟨ψ, hpeq⟩ := hμ
    -- Build a parallel `hμmem` after the rewrite.
    have hμmem :
        (wkBundle.mLim,
          (fun x => wkBundle.uLim x + (ψ : (Fin d → ℝ) → ℝ) x),
          (fun i x => wkBundle.DuLim i x +
            ((StationaryMFG.Periodic.SmoothPeriodic.partialDeriv i ψ
                : StationaryMFG.Periodic.SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) x))
            ∈ D_transport_family_paper (d := d)
                wkBundle.mLim wkBundle.uLim wkBundle.DuLim :=
      ⟨ψ, rfl⟩
    rw [Prod.mk.injEq, Prod.mk.injEq] at hpeq
    obtain ⟨hμeq, hυeq, hDυeq⟩ := hpeq
    rw [hμeq, hυeq, hDυeq]
    -- Source `hpair_conv` and `hreg_bdd` from `pairing` at the
    -- post-rewrite triple.
    obtain ⟨hυ_memSob, hDυ_memLp⟩ := regSupplier hμmem
    have hpair_full := pairing.hpair_conv hμmem
    have hDu_eq := pairing.data_Du hμmem
    have hm_eq := pairing.data_m hμmem
    have hu_eq := pairing.data_u hμmem
    have hDun_eq := pairing.data_Du_n hμmem
    have hmn_eq := pairing.data_m_n hμmem
    have hun_eq := pairing.data_u_n hμmem
    rw [hDu_eq, hm_eq, hu_eq, hDun_eq, hmn_eq, hun_eq] at hpair_full
    have hreg :=
      (pairing.data hμmem).hreg_bdd
    rw [hDun_eq, hun_eq] at hreg
    exact limitPassage_transportForm_of_seqVI seq
      wkBundle.mLim wkBundle.uLim wkBundle.DuLim
      wkBundle.hmLim_nonneg wkBundle.hmLim_memLp
      _ _ hυ_memSob hDυ_memLp (hWeakSupplier hμmem)
      hpair_full
      hreg
  -- Step 2: specialize to the transport-family test shape
  -- `(mLim, uLim + σ·φ, DuLim + σ·∂φ)`. Each such test triple lies in
  -- the narrow domain via `mem_D_transport_family_paper_test`.
  have hFam :
      ∀ (σ : ℝ) (φ : StationaryMFG.Periodic.SmoothPeriodic d),
        0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH)
              wkBundle.DuLim wkBundle.mLim wkBundle.uLim
              (fun i x => (wkBundle.DuLim i x + σ *
                  ((StationaryMFG.Periodic.SmoothPeriodic.partialDeriv i φ
                      : StationaryMFG.Periodic.SmoothPeriodic d) :
                    (Fin d → ℝ) → ℝ) x) - wkBundle.DuLim i x)
              (wkBundle.mLim - wkBundle.mLim)
              ((wkBundle.uLim + fun x => σ * (φ : (Fin d → ℝ) → ℝ) x)
                  - wkBundle.uLim) := by
    intro σ φ
    have hμmem :
        (wkBundle.mLim,
          (fun x => wkBundle.uLim x + σ * (φ : (Fin d → ℝ) → ℝ) x),
          (fun i x => wkBundle.DuLim i x + σ *
            ((StationaryMFG.Periodic.SmoothPeriodic.partialDeriv i φ
                : StationaryMFG.Periodic.SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) x))
            ∈ D_transport_family_paper (d := d)
                wkBundle.mLim wkBundle.uLim wkBundle.DuLim :=
      mem_D_transport_family_paper_test (d := d)
        wkBundle.mLim wkBundle.uLim wkBundle.DuLim σ φ
    have h := hStrongFamily hμmem
    -- Match function shapes: `(uLim + fun x => σ * φ x)` (Pi.add form)
    -- vs `(fun x => uLim x + σ * φ x)` (pointwise) — these are
    -- definitionally equal.
    convert h using 2
  exact strongVI_transportForm_of_transportFamily (γBar := γBarReal) hFam

/-! ### Headline structure: `LimitSolutionData` -/

/-- **Headline T9 record.** Bare-function periodic limit triple
`(m, u, Du)` together with all the data `H4SimplePowerInputs`
consumes:
* `MemLpPer`/`MemSobolevPer` regularity,
* a.e. non-negativity of `m`,
* HJB-residual / residual·m / flux integrabilities,
* the **three paper-shaped strong-VI specializations** (set, signed,
  transport) of `A_0` at `(m, u, Du)`.

Per `infra-P4-weaken-thin-bundle-to-paper-tests`, this record
carries the three test-family specializations directly, instead of
the over-specified universal function-form strong VI; the latter
required a `UniversalityBridge` discharge in the strict-positivity
flavor (Cluster D) and is no longer on the critical path. -/
structure LimitSolutionData
    (γBar βBar : ℝ≥0∞)
    (γBarReal : ℝ)
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)) where
  /-- The limit density. -/
  m : (Fin d → ℝ) → ℝ
  /-- The limit value function. -/
  u : (Fin d → ℝ) → ℝ
  /-- Explicit weak-derivative family. -/
  Du : Fin d → (Fin d → ℝ) → ℝ
  /-- `m ∈ L^{βBar}_per`. -/
  hmLp : Periodic.MemLpPer βBar m
  /-- `u ∈ W^{1,γBar}_per`. -/
  huSob : Periodic.MemSobolevPer γBar u
  /-- `0 ≤ m` a.e. on the unit cube. -/
  hmNonneg :
    0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
            (UnitCube d)] m
  /-- HJB-residual integrability. -/
  hRes : MeasureTheory.Integrable
            (StationaryMFG.Theorems.SimplePower.hjbResidual V H Du m u)
            (MeasureTheory.volume.restrict (UnitCube d))
  /-- Residual·m integrability. -/
  hResM : MeasureTheory.Integrable
            (fun x =>
              StationaryMFG.Theorems.SimplePower.hjbResidual V H Du m u x
                * m x)
            (MeasureTheory.volume.restrict (UnitCube d))
  /-- Flux integrability. -/
  hFluxInt : MeasureTheory.Integrable
              (fun x =>
                StationaryMFG.Hamiltonian.mDpH DpH x
                  (fun i => Du i x) (m x))
              (MeasureTheory.volume.restrict (UnitCube d))
  /-- **Strong-VI set form at `ε = 0`** — paper test family for
  `lem:strong.is.strong` (a). -/
  hVI_set :
    StationaryMFG.Theorems.SimplePower.StrongVI_setForm
      V H DpH γBarReal 0 Du m u
  /-- **Strong-VI signed set form at `ε = 0`** — paper test family
  for `lem:strong.is.strong` (b). -/
  hVI_signed :
    StationaryMFG.Theorems.SimplePower.StrongVI_setForm_signed
      V H DpH γBarReal 0 Du m u
  /-- **Strong-VI transport form at `ε = 0`** — paper test family
  for `lem:strong.is.strong` (c). -/
  hVI_transport :
    StationaryMFG.Theorems.SimplePower.StrongVI_transportForm
      V H DpH γBarReal 0 Du m u

/-! ### Strict-positivity-restricted `LimitSolutionDataPos`.

Variant of `LimitSolutionData` whose strong VI field is restricted to
the strict-positivity domain `D_pos = StrictPositivityDomain c` (the
output of `mintyClosure_of_paperHypotheses_strictPos` + `main_strong_VI`),
augmented with a `UniversalityBridge` field that authorises AC1+AC2
of the universality recovery.

Conversion to the universal `LimitSolutionData` is
`LimitSolutionDataPos.toLimitSolutionData`, which uses
`strongVI_universal_of_strictPositivity` to discharge the universal
`hStrongVI`. -/
structure LimitSolutionDataPos
    (γBar βBar : ℝ≥0∞)
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)) where
  /-- The limit density. -/
  m : (Fin d → ℝ) → ℝ
  /-- The limit value function. -/
  u : (Fin d → ℝ) → ℝ
  /-- Explicit weak-derivative family. -/
  Du : Fin d → (Fin d → ℝ) → ℝ
  /-- `m ∈ L^{βBar}_per`. -/
  hmLp : Periodic.MemLpPer βBar m
  /-- `u ∈ W^{1,γBar}_per`. -/
  huSob : Periodic.MemSobolevPer γBar u
  /-- `0 ≤ m` a.e. on the unit cube. -/
  hmNonneg :
    0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
            (UnitCube d)] m
  /-- HJB-residual integrability. -/
  hRes : MeasureTheory.Integrable
            (StationaryMFG.Theorems.SimplePower.hjbResidual V H Du m u)
            (MeasureTheory.volume.restrict (UnitCube d))
  /-- Residual·m integrability. -/
  hResM : MeasureTheory.Integrable
            (fun x =>
              StationaryMFG.Theorems.SimplePower.hjbResidual V H Du m u x
                * m x)
            (MeasureTheory.volume.restrict (UnitCube d))
  /-- Flux integrability. -/
  hFluxInt : MeasureTheory.Integrable
              (fun x =>
                StationaryMFG.Hamiltonian.mDpH DpH x
                  (fun i => Du i x) (m x))
              (MeasureTheory.volume.restrict (UnitCube d))
  /-- The strict-positivity lower bound. -/
  c : ℝ
  /-- **`D_pos`-restricted function-form strong VI** for `A_0` at
  `(m, u, Du)`. For every test triple `(μ, υ, Dυ)` lying in the
  strict-positivity domain `StrictPositivityDomain c`,
  `0 ≤ mfgOperatorPair Du m u (Dυ - Du) (μ - m) (υ - u)`. -/
  hStrongVIPos : ∀ ⦃μ υ Dυ⦄,
    (μ, υ, Dυ) ∈ (StrictPositivityDomain (d := d) c) →
    0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH) Du m u
          (fun i x => Dυ i x - Du i x) (μ - m) (υ - u)
  /-- The universality bridge: AC1+AC2 authorised inputs that, jointly
  with `hStrongVIPos`, give the universal `hStrongVI` via
  `strongVI_universal_of_strictPositivity`. -/
  bridge : UniversalityBridge (d := d) V H DpH m u Du c

namespace LimitSolutionDataPos

variable {γBar βBar : ℝ≥0∞}
variable {V : (Fin d → ℝ) → ℝ}
variable {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
variable {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}

/-- **Convert to `LimitSolutionData`** by discharging the three
paper-shaped strong-VI specializations
(`hVI_set` / `hVI_signed` / `hVI_transport`) from the
`D_pos`-restricted `hStrongVIPos` plus the authorised `bridge`.

Pipeline: first reconstruct the universal function-form strong VI
via `strongVI_universal_of_strictPositivity` (the genuine AC3
discharge of `infra-P4-rebuild-T9-discharge-minty-universality`);
then specialise to the three paper test families via the local
helpers `strongVI_*Form_of_universal`. -/
def toLimitSolutionData
    (γBarReal : ℝ)
    (L : LimitSolutionDataPos (d := d) γBar βBar V H DpH) :
    LimitSolutionData (d := d) γBar βBar γBarReal V H DpH :=
  let hUniv :
      ∀ (μ υ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ),
        0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH) L.Du L.m L.u
              (fun i x => Dυ i x - L.Du i x) (μ - L.m) (υ - L.u) :=
    strongVI_universal_of_strictPositivity
      (V := V) (H := H) (DpH := DpH)
      (mLim := L.m) (uLim := L.u) (DuLim := L.Du)
      (c := L.c) L.hStrongVIPos L.bridge
  { m := L.m
    u := L.u
    Du := L.Du
    hmLp := L.hmLp
    huSob := L.huSob
    hmNonneg := L.hmNonneg
    hRes := L.hRes
    hResM := L.hResM
    hFluxInt := L.hFluxInt
    hVI_set := palomar_RegularizedSequence_strongVI_setForm_of_universal (γBar := γBarReal) hUniv
    hVI_signed :=
      palomar_RegularizedSequence_strongVI_setFormSigned_of_universal (γBar := γBarReal) hUniv
    hVI_transport :=
      palomar_RegularizedSequence_strongVI_transportForm_of_universal (γBar := γBarReal) hUniv }

end LimitSolutionDataPos

/-! ### `FinalIntegrabilityBundle` — authorized aux for the integrabilities.

Per the AC amendment, the three integrability fields of
`LimitSolutionData` (`hRes`, `hResM`, `hFluxInt`) are taken as
authorized inputs to the producer. They depend on the limit-triple
*bare* values, which the upstream chain must supply. -/

/-- **Authorized auxiliary bundle** packaging the three
integrability fields of `LimitSolutionData` at a given triple
`(m, u, Du)`. -/
structure FinalIntegrabilityBundle
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ) where
  /-- HJB-residual integrability. -/
  hRes : MeasureTheory.Integrable
            (StationaryMFG.Theorems.SimplePower.hjbResidual V H Du m u)
            (MeasureTheory.volume.restrict (UnitCube d))
  /-- Residual·m integrability. -/
  hResM : MeasureTheory.Integrable
            (fun x =>
              StationaryMFG.Theorems.SimplePower.hjbResidual V H Du m u x
                * m x)
            (MeasureTheory.volume.restrict (UnitCube d))
  /-- Flux integrability. -/
  hFluxInt : MeasureTheory.Integrable
              (fun x =>
                StationaryMFG.Hamiltonian.mDpH DpH x
                  (fun i => Du i x) (m x))
              (MeasureTheory.volume.restrict (UnitCube d))

/-! ### Producer: `limitSolutionData_of_regularizedSequence` -/

/-- **T9 producer.** Build a `LimitSolutionData` from
`(hmon, hpow, hV, hExp, seq)` plus the authorized auxiliary bundles.

Pipeline:
1. Use `seq` + `wkBundle` to feed
   `weakLimitData_of_regularizedSequence` (T8) and obtain the
   `WeakLimitInputData`. The chosen periodic limit triple
   `(mLim, uLim, DuLim)` of `wkBundle` becomes the limit triple of
   `LimitSolutionData`.
2. Per test triple `(μ, υ, Dυ)`, apply F.6's `limitPassage_to_weakVI`
   on `pairing.data μ υ Dυ` with the assembled `pairing.hpair_conv`,
   yielding the **weak** VI at `(mLim, uLim, DuLim)` for that test
   triple.
3. Collect the weak VI's into a domain-`D`-quantified form via
   `mintyClosure.D`, then apply `main_strong_VI` to obtain the
   **strong** VI on `D`.
4. The strong VI on `D` plus the universal-quantifier specialization
   (consumer's responsibility — here we directly land the universal
   form on the assumption that `D = Set.univ`) produces
   `hStrongVI`. To keep this lemma's quantifier shape independent
   of the choice of `D`, we land the strong VI **restricted to
   `D`-membership** of the test triple, then turn it into a
   universal hypothesis only when `D = Set.univ`.

   Per the AC amendment, the universal-quantifier discharge is the
   responsibility of `MintyClosure` (which is required to have
   `D = Set.univ` or otherwise contain every test triple of
   interest); this lemma's local argument is to apply
   `main_strong_VI` and post-compose with the consumer's domain
   membership.

5. The integrability fields are read off `finInt`. -/
noncomputable def limitSolutionData_of_regularizedSequence
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
    (pairing : LimitPairingInputs (d := d)
                  (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  (V := V) (H := H) (DpH := DpH)
                  seq wkBundle.mLim wkBundle.uLim wkBundle.DuLim)
    (mintyClosure : MintyClosure (d := d) V H DpH
                       wkBundle.mLim wkBundle.uLim wkBundle.DuLim)
    (hDuniv : mintyClosure.D = Set.univ)
    (finInt : FinalIntegrabilityBundle (d := d) V H DpH
                wkBundle.DuLim wkBundle.mLim wkBundle.uLim)
    -- **Phase 5b** (`infra-P5-theorem1-phase-5b-rebuild-pairing-on-noVI`).
    -- The legacy F.6 weak-VI passage `limitPassage_to_weakVI` reads
    -- `T.hVI_eps`, but `pairing.data μ υ Dυ` is now of the leaner
    -- `LimitPassageInputData_noVI` shape (the field is no longer
    -- carried). Reconstruct the universal `LimitPassageInputData` here
    -- via `of_noVI_withVI` plus an externally-supplied
    -- `hVI_eps_universal`.
    (hVI_eps_universal : ∀ (μ υ : (Fin d → ℝ) → ℝ)
        (Dυ : Fin d → (Fin d → ℝ) → ℝ) (k : ℕ),
        0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal (seq.epsSeq k) Dυ μ υ
              (fun i x => Dυ i x - (seq.sol k).Du i x)
              (μ - (seq.sol k).m) (υ - (seq.sol k).u)) :
    LimitSolutionData (d := d) (ENNReal.ofReal γBarReal)
      (ENNReal.ofReal βBarReal) γBarReal V H DpH := by
  -- The `wkBundle` already carries the F.5 outputs we need:
  -- `MemLpPer βBar mLim`, `MemSobolevPer γBar uLim`, `0 ≤ mLim a.e.`.
  -- (These are derivable from the rest of `wkBundle`'s contents via
  -- `extractWeakLimit`; carried as fields to avoid destructuring its
  -- existential conclusion.)
  -- Per-test-triple **weak** VI at the limit triple via F.6.
  have hWeak_per_triple :
      ∀ (μ υ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ),
        0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
              (fun i x => Dυ i x - wkBundle.DuLim i x)
              (μ - wkBundle.mLim) (υ - wkBundle.uLim) := by
    intro μ υ Dυ
    -- Phase 5b: rebuild a full `LimitPassageInputData` from the leaner
    -- `pairing.data μ υ Dυ` via `of_noVI_withVI` + `hVI_eps_universal`.
    -- Need to align the shape via `data_ε`, `data_m_n`, `data_u_n`,
    -- `data_Du_n` projections.
    have hε_eq := pairing.data_ε μ υ Dυ
    have hmn_eq := pairing.data_m_n μ υ Dυ
    have hun_eq := pairing.data_u_n μ υ Dυ
    have hDun_eq := pairing.data_Du_n μ υ Dυ
    let hVIeps : ∀ k,
        0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ((pairing.data μ υ Dυ).ε k) Dυ μ υ
              (fun i x => Dυ i x - (pairing.data μ υ Dυ).Du_n k i x)
              (μ - (pairing.data μ υ Dυ).m_n k)
              (υ - (pairing.data μ υ Dυ).u_n k) := by
      intro k
      rw [hε_eq, hmn_eq, hun_eq, hDun_eq]
      exact hVI_eps_universal μ υ Dυ k
    let Tfull : LimitPassageInputData (d := d) V H DpH
                  βBarReal βBarReal' γBarReal γBarReal' μ υ Dυ :=
      LimitPassageInputData_noVI.of_noVI_withVI
        (pairing.data μ υ Dυ) hVIeps
    -- Apply F.6 on `Tfull`.
    have hF6 := limitPassage_to_weakVI (V := V) (H := H) (DpH := DpH)
                  (T := Tfull)
                  (pairing.hpair_conv μ υ Dυ)
    -- `Tfull.{m, u, Du} = (pairing.data μ υ Dυ).{m, u, Du}` by
    -- `of_noVI_withVI` field definitions; the latter equals
    -- `wkBundle.{mLim, uLim, DuLim}` by the projection lemmas.
    have hDu : Tfull.Du = wkBundle.DuLim := pairing.data_Du μ υ Dυ
    have hm : Tfull.m = wkBundle.mLim := pairing.data_m μ υ Dυ
    have hu : Tfull.u = wkBundle.uLim := pairing.data_u μ υ Dυ
    rw [hDu, hm, hu] at hF6
    exact hF6
  -- Upgrade weak VI to **strong** VI via `main_strong_VI`.
  have hStrong :
      ∀ ⦃μ υ Dυ⦄, (μ, υ, Dυ) ∈ mintyClosure.D →
        0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH)
              wkBundle.DuLim wkBundle.mLim wkBundle.uLim
              (fun i x => Dυ i x - wkBundle.DuLim i x)
              (μ - wkBundle.mLim) (υ - wkBundle.uLim) := by
    refine StationaryMFG.Theorems.SimplePower.main_strong_VI
      (V := V) (H := H) (DpH := DpH) (D := mintyClosure.D)
      mintyClosure.hSeg mintyClosure.hAhc mintyClosure.hLimMem ?_
    intro μ υ Dυ _hμ
    exact hWeak_per_triple μ υ Dυ
  -- Discharge the universal `hStrongVI` via `D = Set.univ`.
  have hStrongUniv :
      ∀ (μ υ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ),
        0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH)
              wkBundle.DuLim wkBundle.mLim wkBundle.uLim
              (fun i x => Dυ i x - wkBundle.DuLim i x)
              (μ - wkBundle.mLim) (υ - wkBundle.uLim) := by
    intro μ υ Dυ
    have hμ : (μ, υ, Dυ) ∈ mintyClosure.D := by
      rw [hDuniv]; exact Set.mem_univ _
    exact hStrong hμ
  -- Specialize the universal strong VI to the three paper test
  -- families (set, signed, transport) via the helper lemmas above.
  -- Per `infra-P4-weaken-thin-bundle-to-paper-tests`, the headline
  -- record now stores these specializations directly.
  have hVI_set := palomar_RegularizedSequence_strongVI_setForm_of_universal (γBar := γBarReal) hStrongUniv
  have hVI_signed :=
    palomar_RegularizedSequence_strongVI_setFormSigned_of_universal (γBar := γBarReal) hStrongUniv
  have hVI_transport :=
    palomar_RegularizedSequence_strongVI_transportForm_of_universal (γBar := γBarReal) hStrongUniv
  -- Assemble.
  exact
    { m := wkBundle.mLim
      u := wkBundle.uLim
      Du := wkBundle.DuLim
      hmLp := wkBundle.hmLim_memLp
      huSob := wkBundle.huLim_sob
      hmNonneg := wkBundle.hmLim_nonneg
      hRes := finInt.hRes
      hResM := finInt.hResM
      hFluxInt := finInt.hFluxInt
      hVI_set := hVI_set
      hVI_signed := hVI_signed
      hVI_transport := hVI_transport }

/-! ### Strict-positivity-domain producer.

This producer is the strict-positivity-domain analogue of
`limitSolutionData_of_regularizedSequence`. It consumes a
`MintyClosureOn (StrictPositivityDomain c)` (real
`hPos`-genuine-discharge witness from
`mintyClosure_of_paperHypotheses_strictPos`) plus a `UniversalityBridge`
authorising AC1+AC2 of the universality recovery, and produces a
`LimitSolutionDataPos` carrying the `D_pos`-restricted strong VI plus
the bridge.

Composing with `LimitSolutionDataPos.toLimitSolutionData` then yields
a universal `LimitSolutionData` whose `hStrongVI` is genuinely derived
(via `strongVI_universal_of_strictPositivity`) from the
`D_pos`-restricted strong VI plus the bridge. -/

/-- **T9 producer (strict-positivity variant).** Build a
`LimitSolutionDataPos` from `(hmon, hpow, hV, hExp, seq, wkBundle,
pairing, mintyClosureOn, hLimMem, finInt, bridge)`.

Differences from `limitSolutionData_of_regularizedSequence`:

* Takes `MintyClosureOn (StrictPositivityDomain c)` instead of
  `MintyClosure` + `hDuniv = Set.univ`.
* Takes a `UniversalityBridge` for the universality recovery.
* Takes a limit-triple membership certificate
  `(mLim, uLim, DuLim) ∈ StrictPositivityDomain c` (downstream
  of paper line 815 `lem:bdd-below-eps`'s lim-inf passage).
* Outputs `LimitSolutionDataPos` (whose `hStrongVI` is restricted to
  `D_pos`); the universal-quantifier discharge is at the bridge layer
  via `LimitSolutionDataPos.toLimitSolutionData`.

The `D_pos`-restricted strong VI is built by `main_strong_VI` on
`MintyClosureOn`'s segment-closed and hemicontinuous domain. -/
noncomputable def limitSolutionData_of_regularizedSequence_strictPos
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
    (pairing : LimitPairingInputs (d := d)
                  (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  (V := V) (H := H) (DpH := DpH)
                  seq wkBundle.mLim wkBundle.uLim wkBundle.DuLim)
    {c : ℝ}
    (mintyClosureOn : MintyClosureOn (d := d) V H DpH
                        wkBundle.mLim wkBundle.uLim wkBundle.DuLim
                        (StrictPositivityDomain (d := d) c))
    (finInt : FinalIntegrabilityBundle (d := d) V H DpH
                wkBundle.DuLim wkBundle.mLim wkBundle.uLim)
    (bridge : UniversalityBridge (d := d) V H DpH
                wkBundle.mLim wkBundle.uLim wkBundle.DuLim c)
    -- Phase 5b: see `limitSolutionData_of_regularizedSequence`'s
    -- discussion. `pairing.data μ υ Dυ` is now `_noVI`; the legacy
    -- F.6 passage `limitPassage_to_weakVI` requires `hVI_eps`.
    (hVI_eps_universal : ∀ (μ υ : (Fin d → ℝ) → ℝ)
        (Dυ : Fin d → (Fin d → ℝ) → ℝ) (k : ℕ),
        0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal (seq.epsSeq k) Dυ μ υ
              (fun i x => Dυ i x - (seq.sol k).Du i x)
              (μ - (seq.sol k).m) (υ - (seq.sol k).u)) :
    LimitSolutionDataPos (d := d) (ENNReal.ofReal γBarReal)
      (ENNReal.ofReal βBarReal) V H DpH := by
  -- Per-test-triple **weak** VI at the limit triple via F.6.
  have hWeak_per_triple :
      ∀ (μ υ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ),
        0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH) Dυ μ υ
              (fun i x => Dυ i x - wkBundle.DuLim i x)
              (μ - wkBundle.mLim) (υ - wkBundle.uLim) := by
    intro μ υ Dυ
    -- Phase 5b: rebuild a full `LimitPassageInputData` from
    -- `pairing.data μ υ Dυ : LimitPassageInputData_noVI` plus the
    -- supplied `hVI_eps_universal`.
    have hε_eq := pairing.data_ε μ υ Dυ
    have hmn_eq := pairing.data_m_n μ υ Dυ
    have hun_eq := pairing.data_u_n μ υ Dυ
    have hDun_eq := pairing.data_Du_n μ υ Dυ
    let hVIeps : ∀ k,
        0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ((pairing.data μ υ Dυ).ε k) Dυ μ υ
              (fun i x => Dυ i x - (pairing.data μ υ Dυ).Du_n k i x)
              (μ - (pairing.data μ υ Dυ).m_n k)
              (υ - (pairing.data μ υ Dυ).u_n k) := by
      intro k
      rw [hε_eq, hmn_eq, hun_eq, hDun_eq]
      exact hVI_eps_universal μ υ Dυ k
    let Tfull : LimitPassageInputData (d := d) V H DpH
                  βBarReal βBarReal' γBarReal γBarReal' μ υ Dυ :=
      LimitPassageInputData_noVI.of_noVI_withVI
        (pairing.data μ υ Dυ) hVIeps
    have hF6 := limitPassage_to_weakVI (V := V) (H := H) (DpH := DpH)
                  (T := Tfull)
                  (pairing.hpair_conv μ υ Dυ)
    have hDu : Tfull.Du = wkBundle.DuLim := pairing.data_Du μ υ Dυ
    have hm : Tfull.m = wkBundle.mLim := pairing.data_m μ υ Dυ
    have hu : Tfull.u = wkBundle.uLim := pairing.data_u μ υ Dυ
    rw [hDu, hm, hu] at hF6
    exact hF6
  -- Upgrade weak VI to **`D_pos`-restricted strong** VI via `main_strong_VI`.
  have hStrongPos :
      ∀ ⦃μ υ Dυ⦄,
        (μ, υ, Dυ) ∈ (StrictPositivityDomain (d := d) c) →
        0 ≤ mfgOperatorPair (V := V) (H := H) (DpH := DpH)
              wkBundle.DuLim wkBundle.mLim wkBundle.uLim
              (fun i x => Dυ i x - wkBundle.DuLim i x)
              (μ - wkBundle.mLim) (υ - wkBundle.uLim) := by
    refine StationaryMFG.Theorems.SimplePower.main_strong_VI
      (V := V) (H := H) (DpH := DpH)
      (D := StrictPositivityDomain (d := d) c)
      mintyClosureOn.hSeg mintyClosureOn.hAhc mintyClosureOn.hLimMem ?_
    intro μ υ Dυ _hμ
    exact hWeak_per_triple μ υ Dυ
  -- Assemble the strict-positivity bundle.
  exact
    { m := wkBundle.mLim
      u := wkBundle.uLim
      Du := wkBundle.DuLim
      hmLp := wkBundle.hmLim_memLp
      huSob := wkBundle.huLim_sob
      hmNonneg := wkBundle.hmLim_nonneg
      hRes := finInt.hRes
      hResM := finInt.hResM
      hFluxInt := finInt.hFluxInt
      c := c
      hStrongVIPos := hStrongPos
      bridge := bridge }

/-! ### Compatibility: `LimitSolutionData → H4SimplePowerInputs`.

Per `infra-P4-weaken-thin-bundle-to-paper-tests`, the producer
chain now lands directly on the paper-shaped
`StationaryMFG.Theorems.SimplePower.H4SimplePowerInputs` (which is
the bundle consumed by `thm_main_simplePowerGrowth`). The two
records carry definitionally identical fields after the pivot
(modulo the legacy `(γBarReal : ℝ)` parameter, threaded through
unchanged); this is a direct-projection conversion. -/

/-! ### Phase F0 — family-native `H4SimplePowerInputs` assembly.

Per `docs/THEOREM1_CLOSURE_PLAN.md` v4 §10, the chain assembles
`H4SimplePowerInputs` directly from the three paper-test-family
strong-VI specializations rather than going through a universal
function-form intermediate. The producer below consumes the same
inputs as `limitSolutionData_of_regularizedSequence` but invokes the
three F0 family producers
`strongVI_set_at_limit_of_paperHypotheses` /
`strongVI_signed_at_limit_of_paperHypotheses` /
`strongVI_transport_at_limit_of_paperHypotheses` directly, making
the family-native shape visible at the assembly surface. -/

/-- **F0 family-native assembly.** Build the paper-shaped
`H4SimplePowerInputs` directly from the three F0 family producers
plus the integrability bundle, bypassing the universal-strong-VI
intermediate.

Phase 4a (task `infra-P4-minty-family-native-4a-set`): the set
branch now consumes a per-family `MintyClosureOn D_set_family`
certificate (`mintyClosureOn_set`).

Phase 4b (task `infra-P4-minty-family-native-4b-signed`): the signed
branch now consumes a per-family `MintyClosureOn D_signed_family`
certificate (`mintyClosureOn_signed`).

Phase 4c (task `infra-P4-minty-family-native-4c-transport`): the
transport branch now consumes a per-family
`MintyClosureOn D_transport_family` certificate
(`mintyClosureOn_transport`). All three families are now native. The
universal `mintyClosure`/`hDuniv` parameters are retained for now and
will be dropped by task 4d. -/
noncomputable def H4SimplePowerInputs_of_paperHypotheses_familyNative
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
    -- **Phase 6c-iv**: the helper now consumes three per-family
    -- `LimitPairingInputsFamily` records, one for each paper test
    -- family domain. Callers (e.g. the BanachBridge chain) can either
    -- build them directly via the per-family producer
    -- `limitPairingInputsFamily_of_regularizedSequence`, or convert
    -- a universal `LimitPairingInputs` via `LimitPairingInputs.toFamily`.
    --
    -- **Phase 6d-ii-c-2d** (`infra-P5-theorem1-phase-6d-ii-c-2d-chain-migrate-to-narrow`):
    -- the set / signed pairings now live on the **narrow paper-form**
    -- domains `D_set_family_paper βBar` / `D_signed_family_paper_nn βBar`
    -- (perturbations periodic and `MemLpPer βBar`), to feed the
    -- corresponding narrow-consuming F0 helpers
    -- `strongVI_set_at_limit_of_paperHypotheses_paper` /
    -- `strongVI_signed_at_limit_of_paperHypotheses_paper`. Wider-domain
    -- pairings (e.g. produced via `pairing.toFamily`) can be restricted
    -- to the narrow domains via
    -- `LimitPairingInputsFamily.subdomain` together with
    -- `mem_D_set_family_paper_subset` / `mem_D_signed_family_paper_nn_subset`.
    -- The transport pairing remains at `D_transport_family` (no narrow
    -- companion needed).
    (pairing_set : LimitPairingInputsFamily (d := d)
                  (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  (V := V) (H := H) (DpH := DpH)
                  seq wkBundle.mLim wkBundle.uLim wkBundle.DuLim
                  (D_set_family_paper (d := d)
                     (ENNReal.ofReal βBarReal)
                     wkBundle.mLim wkBundle.uLim wkBundle.DuLim))
    (pairing_signed : LimitPairingInputsFamily (d := d)
                  (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  (V := V) (H := H) (DpH := DpH)
                  seq wkBundle.mLim wkBundle.uLim wkBundle.DuLim
                  (D_signed_family_paper_nn (d := d)
                     (ENNReal.ofReal βBarReal)
                     wkBundle.mLim wkBundle.uLim wkBundle.DuLim))
    (pairing_transport : LimitPairingInputsFamily (d := d)
                  (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  (V := V) (H := H) (DpH := DpH)
                  seq wkBundle.mLim wkBundle.uLim wkBundle.DuLim
                  (D_transport_family_paper (d := d)
                     wkBundle.mLim wkBundle.uLim wkBundle.DuLim))
    (mintyClosureOn_set : MintyClosureOn (d := d) V H DpH
                       wkBundle.mLim wkBundle.uLim wkBundle.DuLim
                       (D_set_family_paper (d := d)
                          (ENNReal.ofReal βBarReal)
                          wkBundle.mLim wkBundle.uLim wkBundle.DuLim))
    (mintyClosureOn_signed : MintyClosureOn (d := d) V H DpH
                       wkBundle.mLim wkBundle.uLim wkBundle.DuLim
                       (D_signed_family_paper_nn (d := d)
                          (ENNReal.ofReal βBarReal)
                          wkBundle.mLim wkBundle.uLim wkBundle.DuLim))
    (mintyClosureOn_transport : MintyClosureOn (d := d) V H DpH
                       wkBundle.mLim wkBundle.uLim wkBundle.DuLim
                       (D_transport_family_paper (d := d)
                          wkBundle.mLim wkBundle.uLim wkBundle.DuLim))
    -- **Phase 6d-ii-d-2** (`infra-P5-theorem1-phase-6d-ii-d-2-narrow-transport-regSupplier`):
    -- the transport regSupplier is now family-restricted to the
    -- narrow paper-form domain `D_transport_family_paper` (triples of
    -- the form `(mLim, uLim + ψ, DuLim + ∂ψ)`). Callers can construct
    -- it inline via `wkBundle.perTestTripleBase` +
    -- `PerTestTripleRegularity.transport_perturbation`, without
    -- consuming `T10PaperResidues.regBundle`.
    (regSupplier_transport :
      ∀ ⦃μ : (Fin d → ℝ) → ℝ⦄
        ⦃υ : (Fin d → ℝ) → ℝ⦄
        ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
          (μ, υ, Dυ) ∈ D_transport_family_paper (d := d)
                          wkBundle.mLim wkBundle.uLim wkBundle.DuLim →
            MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ ∧
              ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i))
    -- **Phase 5 step3d** weak-derivative-tie supplier for the
    -- transport narrow domain. Mirrors `regSupplier_transport`.
    (hWeakSupplier_transport :
      ∀ ⦃μ : (Fin d → ℝ) → ℝ⦄
        ⦃υ : (Fin d → ℝ) → ℝ⦄
        ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
          (μ, υ, Dυ) ∈ D_transport_family_paper (d := d)
                          wkBundle.mLim wkBundle.uLim wkBundle.DuLim →
            ∀ i, HasWeakDerivPer (d := d) i υ (Dυ i))
    (finInt : FinalIntegrabilityBundle (d := d) V H DpH
                wkBundle.DuLim wkBundle.mLim wkBundle.uLim) :
    StationaryMFG.Theorems.SimplePower.H4SimplePowerInputs (d := d)
      γBarReal V H DpH (ENNReal.ofReal βBarReal)
      (ENNReal.ofReal γBarReal) where
  m := wkBundle.mLim
  u := wkBundle.uLim
  Du := wkBundle.DuLim
  mLp := wkBundle.hmLim_memLp
  uSob := wkBundle.huLim_sob
  m_nonneg := wkBundle.hmLim_nonneg
  hRes := finInt.hRes
  hResM := finInt.hResM
  hFluxInt := finInt.hFluxInt
  -- Phase 6c-iv: each helper consumes its dedicated family-restricted
  -- `LimitPairingInputsFamily` directly; the universal-to-family
  -- bridge `LimitPairingInputs.toFamily` (formerly applied here) has
  -- been pushed up into the caller.
  --
  -- **Phase 6d-ii-c-2d**: the set / signed branches now invoke the
  -- narrow-consuming F0 helpers (`*_paper` variants) on the narrow
  -- paper-form domains.
  --
  -- **Phase 6d-ii-d-2**: the transport branch now also invokes the
  -- narrow-consuming `*_paper` variant on
  -- `D_transport_family_paper`.
  hVI_set :=
    strongVI_set_at_limit_of_paperHypotheses_paper
      hmon hpow hV hExp seq wkBundle pairing_set mintyClosureOn_set
  hVI_signed :=
    strongVI_signed_at_limit_of_paperHypotheses_paper
      hmon hpow hV hExp seq wkBundle pairing_signed mintyClosureOn_signed
  hVI_transport :=
    strongVI_transport_at_limit_of_paperHypotheses_paper
      hmon hpow hV hExp seq wkBundle pairing_transport
      mintyClosureOn_transport regSupplier_transport hWeakSupplier_transport
  -- **G8a** (`infra-P8-g8a-T1-du-tie-conclusion`): surface the
  -- weak-gradient tie and the strict-`γ̄` `MemLpPer` of every
  -- gradient-limit component directly from the AE weak-limit bundle's
  -- own derived accessors (`huLim_DuLim_weakDeriv` / `hDuLim_memLp_γ`).
  -- Since `m, u, Du := wkBundle.{mLim, uLim, DuLim}`, these project
  -- with no further work — no new hypothesis is introduced.
  hDu_weakDeriv := fun i => wkBundle.huLim_DuLim_weakDeriv i
  hDu_memLp_γ := fun i => wkBundle.hDuLim_memLp_γ i
  -- **Phase 4d** (`infra-P4-drop-mintyResidue-universal-chain`): the
  -- universal `mintyClosure`/`hDuniv` parameters have been dropped;
  -- all three families now consume per-family `MintyClosureOn`
  -- certificates directly.


/-- **Phase 4d sanity check** (`infra-P4-drop-mintyResidue-universal-chain`).
Type-checks the refactored signature of
`H4SimplePowerInputs_of_paperHypotheses_familyNative`: the universal
`mintyClosure`/`hDuniv` parameters have been dropped, leaving only the
three per-family `MintyClosureOn` certificates (set / signed /
transport). All three families are now native.

**Phase 6d-ii-c-2d**
(`infra-P5-theorem1-phase-6d-ii-c-2d-chain-migrate-to-narrow`): the
chain now reads pairings + minty-closures at the **narrow paper-form**
domains for the set / signed branches. This sanity example takes a
universal `pairing : LimitPairingInputs` and wider-domain
`MintyClosureOn` records as inputs, and exhibits the bridge to the
narrow domains via `pairing.toFamily ... |>.subdomain` plus
`mintyClosureOn_set_paper_of_wider` /
`mintyClosureOn_signed_paper_nn_of_wider`. -/
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
    (pairing : LimitPairingInputs (d := d)
                  (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  (V := V) (H := H) (DpH := DpH)
                  seq wkBundle.mLim wkBundle.uLim wkBundle.DuLim)
    (mintyClosureOn_set : MintyClosureOn (d := d) V H DpH
                       wkBundle.mLim wkBundle.uLim wkBundle.DuLim
                       (D_set_family (d := d)
                          wkBundle.mLim wkBundle.uLim wkBundle.DuLim))
    (mintyClosureOn_signed : MintyClosureOn (d := d) V H DpH
                       wkBundle.mLim wkBundle.uLim wkBundle.DuLim
                       (D_signed_family (d := d)
                          wkBundle.mLim wkBundle.uLim wkBundle.DuLim))
    (mintyClosureOn_transport : MintyClosureOn (d := d) V H DpH
                       wkBundle.mLim wkBundle.uLim wkBundle.DuLim
                       (D_transport_family (d := d)
                          wkBundle.mLim wkBundle.uLim wkBundle.DuLim))
    (regSupplier_transport :
      ∀ ⦃μ : (Fin d → ℝ) → ℝ⦄
        ⦃υ : (Fin d → ℝ) → ℝ⦄
        ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
          (μ, υ, Dυ) ∈ D_transport_family_paper (d := d)
                          wkBundle.mLim wkBundle.uLim wkBundle.DuLim →
            MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ ∧
              ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i))
    (hWeakSupplier_transport :
      ∀ ⦃μ : (Fin d → ℝ) → ℝ⦄
        ⦃υ : (Fin d → ℝ) → ℝ⦄
        ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
          (μ, υ, Dυ) ∈ D_transport_family_paper (d := d)
                          wkBundle.mLim wkBundle.uLim wkBundle.DuLim →
            ∀ i, HasWeakDerivPer (d := d) i υ (Dυ i))
    (finInt : FinalIntegrabilityBundle (d := d) V H DpH
                wkBundle.DuLim wkBundle.mLim wkBundle.uLim) :
    StationaryMFG.Theorems.SimplePower.H4SimplePowerInputs (d := d)
      γBarReal V H DpH (ENNReal.ofReal βBarReal)
      (ENNReal.ofReal γBarReal) :=
  -- Narrow the wider universal pairing through `toFamily`, then the
  -- subset bridges, to land at the narrow paper-form domains.
  let pairing_set_narrow :=
    (pairing.toFamily (D_set_family (d := d)
        wkBundle.mLim wkBundle.uLim wkBundle.DuLim)).subdomain
      (mem_D_set_family_paper_subset (d := d)
        (ENNReal.ofReal βBarReal)
        wkBundle.mLim wkBundle.uLim wkBundle.DuLim)
  let pairing_signed_narrow :=
    (pairing.toFamily (D_signed_family_nn (d := d)
        wkBundle.mLim wkBundle.uLim wkBundle.DuLim)).subdomain
      (mem_D_signed_family_paper_nn_subset (d := d)
        (ENNReal.ofReal βBarReal)
        wkBundle.mLim wkBundle.uLim wkBundle.DuLim)
  -- **Phase 6d-ii-d-2**: narrow transport pairing analogously.
  let pairing_transport_narrow :=
    (pairing.toFamily (D_transport_family (d := d)
        wkBundle.mLim wkBundle.uLim wkBundle.DuLim)).subdomain
      (mem_D_transport_family_paper_subset (d := d)
        wkBundle.mLim wkBundle.uLim wkBundle.DuLim)
  -- Narrow the wider minty-closures.
  let mintyClosureOn_set_narrow :=
    mintyClosureOn_set_paper_of_wider (V := V) (H := H) (DpH := DpH)
      (ENNReal.ofReal βBarReal)
      wkBundle.mLim wkBundle.uLim wkBundle.DuLim mintyClosureOn_set
  let mintyClosureOn_signed_nn :=
    mintyClosureOn_signed_nn_of_wider (V := V) (H := H) (DpH := DpH)
      wkBundle.mLim wkBundle.uLim wkBundle.DuLim
      wkBundle.hmLim_nonneg mintyClosureOn_signed
  let mintyClosureOn_signed_narrow :=
    mintyClosureOn_signed_paper_nn_of_wider (V := V) (H := H) (DpH := DpH)
      (ENNReal.ofReal βBarReal)
      wkBundle.mLim wkBundle.uLim wkBundle.DuLim
      wkBundle.hmLim_nonneg mintyClosureOn_signed_nn
  let mintyClosureOn_transport_narrow :=
    mintyClosureOn_transport_paper_of_wider
      (V := V) (H := H) (DpH := DpH)
      wkBundle.mLim wkBundle.uLim wkBundle.DuLim mintyClosureOn_transport
  H4SimplePowerInputs_of_paperHypotheses_familyNative
    hmon hpow hV hExp seq wkBundle
    pairing_set_narrow
    pairing_signed_narrow
    pairing_transport_narrow
    mintyClosureOn_set_narrow mintyClosureOn_signed_narrow
    mintyClosureOn_transport_narrow regSupplier_transport
    hWeakSupplier_transport finInt

/-! ### Sanity-check unit `example`s -/

/-- **T9 sanity check.** `limitSolutionData_of_regularizedSequence`
produces a `LimitSolutionData`. Pin the type-shape and exercise
the producer with all authorized auxiliary bundles. -/
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
    (pairing : LimitPairingInputs (d := d)
                  (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  (V := V) (H := H) (DpH := DpH)
                  seq wkBundle.mLim wkBundle.uLim wkBundle.DuLim)
    (mintyClosure : MintyClosure (d := d) V H DpH
                       wkBundle.mLim wkBundle.uLim wkBundle.DuLim)
    (hDuniv : mintyClosure.D = Set.univ)
    (finInt : FinalIntegrabilityBundle (d := d) V H DpH
                wkBundle.DuLim wkBundle.mLim wkBundle.uLim)
    (hVI_eps_universal : ∀ (μ υ : (Fin d → ℝ) → ℝ)
        (Dυ : Fin d → (Fin d → ℝ) → ℝ) (k : ℕ),
        0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal (seq.epsSeq k) Dυ μ υ
              (fun i x => Dυ i x - (seq.sol k).Du i x)
              (μ - (seq.sol k).m) (υ - (seq.sol k).u)) :
    LimitSolutionData (d := d) (ENNReal.ofReal γBarReal)
      (ENNReal.ofReal βBarReal) γBarReal V H DpH :=
  limitSolutionData_of_regularizedSequence
    hmon hpow hV hExp seq wkBundle pairing mintyClosure hDuniv finInt
    hVI_eps_universal

/-- **T9 strict-positivity sanity check.** The strict-positivity
producer + bridge converter pipeline produces a universal
`LimitSolutionData` whose `hStrongVI` is genuinely derived from the
`D_pos`-restricted strong VI plus the authorised
`UniversalityBridge`, dropping the `D = Set.univ` shortcut. -/
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
    (pairing : LimitPairingInputs (d := d)
                  (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  (V := V) (H := H) (DpH := DpH)
                  seq wkBundle.mLim wkBundle.uLim wkBundle.DuLim)
    {c : ℝ}
    (mintyClosureOn : MintyClosureOn (d := d) V H DpH
                        wkBundle.mLim wkBundle.uLim wkBundle.DuLim
                        (StrictPositivityDomain (d := d) c))
    (finInt : FinalIntegrabilityBundle (d := d) V H DpH
                wkBundle.DuLim wkBundle.mLim wkBundle.uLim)
    (bridge : UniversalityBridge (d := d) V H DpH
                wkBundle.mLim wkBundle.uLim wkBundle.DuLim c)
    (hVI_eps_universal : ∀ (μ υ : (Fin d → ℝ) → ℝ)
        (Dυ : Fin d → (Fin d → ℝ) → ℝ) (k : ℕ),
        0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal (seq.epsSeq k) Dυ μ υ
              (fun i x => Dυ i x - (seq.sol k).Du i x)
              (μ - (seq.sol k).m) (υ - (seq.sol k).u)) :
    LimitSolutionData (d := d) (ENNReal.ofReal γBarReal)
      (ENNReal.ofReal βBarReal) γBarReal V H DpH :=
  (limitSolutionData_of_regularizedSequence_strictPos
      hmon hpow hV hExp seq wkBundle pairing
      mintyClosureOn finInt bridge
      hVI_eps_universal).toLimitSolutionData γBarReal

/-! ## `PerTestTripleRegularity`: a reusable per-test-triple regularity record

Per the in-flight task `infra-P4-refactor-test-triple-regularity`, we
package the regularity hypotheses needed by every paper test triple
`(μ, υ, Dυ)` into a single structure, plus the three constructors
matching the test families used by the proof of
`lem:strong.is.strong` (FGU-monotone_revised.tex, lines 1147–1186):

* `set_perturbation`: `μ = m + f` (paper: `f = 1_S` for `S` measurable,
  `υ = u`, `Dυ = Du`).
* `signed_perturbation`: `μ = m + σ·m·g` (paper: `g = 1_S` with sign
  `σ ∈ {±1}` and `‖g‖_∞ ≤ 1`), `υ = u`, `Dυ = Du`.
* `transport_perturbation`: `μ = m`, `υ = u + σ·φ`, `Dυ_i = Du_i + σ·∂_iφ`
  for `φ : SmoothPeriodic d` and a real scalar `σ`.

This is **pure infrastructure** — it is not wired into any AC closure
yet (the AC3 selector lemmas that consume it land in the follow-up
backlog task `infra-P4-pairing-selector-AC3-strongVI-bare-test-triple`).
-/

/-- **Per-test-triple regularity record.**

Bundles the regularity needed by a paper test triple `(μ, υ, Dυ)`
against the `Aepsi` strong-VI inequality:

* `μ` lies in `L^βBar` on the torus and is periodic;
* `υ` lies in `L^γBar`, is periodic, and has weak partial derivatives
  `Dυ_i` in each direction;
* each `Dυ_i` lies in `L^γBar` and is periodic.

Every AC2/AC3/AC4/AC5/AC6 selector consumes a single such record
rather than the previous parameter-list of separate hypotheses. -/
structure PerTestTripleRegularity
    (βBar γBar : ℝ≥0∞)
    (μ υ : (Fin d → ℝ) → ℝ)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ) where
  /-- `μ` is `L^βBar_per`. -/
  hμ_memLp : Periodic.MemLpPer (d := d) βBar μ
  /-- `υ` is `L^γBar_per`. -/
  hυ_memLp : Periodic.MemLpPer (d := d) γBar υ
  /-- Each weak-derivative component `Dυ i` is `L^γBar_per`. -/
  hDυ_memLp : ∀ i, Periodic.MemLpPer (d := d) γBar (Dυ i)
  /-- `μ` is periodic. -/
  hμ_periodic : Periodic.IsPeriodic μ
  /-- `υ` is periodic. -/
  hυ_periodic : Periodic.IsPeriodic υ
  /-- Each weak-derivative component is periodic. -/
  hDυ_periodic : ∀ i, Periodic.IsPeriodic (Dυ i)
  /-- The weak-derivative tie: each `Dυ i` is the `i`-th weak partial
  derivative of `υ`. -/
  hWeakDeriv : ∀ i, Periodic.HasWeakDerivPer i υ (Dυ i)

namespace PerTestTripleRegularity

variable {βBar γBar : ℝ≥0∞}

/-- **`ofMemLpAndSobolev`** — direct packaging from the seven primitive
hypotheses. Mostly useful for tests; the perturbation-style
constructors below are what clients actually call. -/
def ofMemLpAndSobolev
    {μ υ : (Fin d → ℝ) → ℝ} {Dυ : Fin d → (Fin d → ℝ) → ℝ}
    (hμ_memLp : Periodic.MemLpPer (d := d) βBar μ)
    (hυ_memLp : Periodic.MemLpPer (d := d) γBar υ)
    (hDυ_memLp : ∀ i, Periodic.MemLpPer (d := d) γBar (Dυ i))
    (hμ_periodic : Periodic.IsPeriodic μ)
    (hυ_periodic : Periodic.IsPeriodic υ)
    (hDυ_periodic : ∀ i, Periodic.IsPeriodic (Dυ i))
    (hWeakDeriv : ∀ i, Periodic.HasWeakDerivPer i υ (Dυ i)) :
    PerTestTripleRegularity (d := d) βBar γBar μ υ Dυ where
  hμ_memLp := hμ_memLp
  hυ_memLp := hυ_memLp
  hDυ_memLp := hDυ_memLp
  hμ_periodic := hμ_periodic
  hυ_periodic := hυ_periodic
  hDυ_periodic := hDυ_periodic
  hWeakDeriv := hWeakDeriv

/-- **Function-level congruence.** Per
`infra-P5-theorem1-phase-6d-ii-d-2-narrow-transport-regSupplier`:
`PerTestTripleRegularity` cares about the underlying functions only
up to pointwise equality (each component field is invariant under
funext, since `MemLpPer`/`IsPeriodic`/`HasWeakDerivPer` are statable
on bare functions). This lemma transports a regularity record along
funext-style equalities of the three component functions. -/
def congr_funs
    {μ μ' υ υ' : (Fin d → ℝ) → ℝ}
    {Dυ Dυ' : Fin d → (Fin d → ℝ) → ℝ}
    (base : PerTestTripleRegularity (d := d) βBar γBar μ υ Dυ)
    (hμ : ∀ x, μ x = μ' x)
    (hυ : ∀ x, υ x = υ' x)
    (hDυ : ∀ i x, Dυ i x = Dυ' i x) :
    PerTestTripleRegularity (d := d) βBar γBar μ' υ' Dυ' := by
  have hμ_eq : μ = μ' := funext hμ
  have hυ_eq : υ = υ' := funext hυ
  have hDυ_eq : Dυ = Dυ' := funext (fun i => funext (hDυ i))
  rw [← hμ_eq, ← hυ_eq, ← hDυ_eq]
  exact base

/-- **`ofSmoothPeriodic`** — `(μ, υ, Dυ)` are all smooth periodic.

Given two smooth periodic functions `μSmooth` and `υSmooth`, the
classical partial derivatives of `υSmooth` provide the
weak-derivative family, and all `MemLpPer` certificates follow from
`MemSobolevPer.of_smoothPeriodic`. -/
def ofSmoothPeriodic
    (βBar γBar : ℝ≥0∞) (μSmooth υSmooth : Periodic.SmoothPeriodic d) :
    PerTestTripleRegularity (d := d) βBar γBar
      ((μSmooth : (Fin d → ℝ) → ℝ))
      ((υSmooth : (Fin d → ℝ) → ℝ))
      (fun i =>
        ((Periodic.SmoothPeriodic.partialDeriv i υSmooth :
            Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ)) where
  hμ_memLp :=
    (Periodic.MemSobolevPer.of_smoothPeriodic (d := d) βBar μSmooth).1
  hυ_memLp :=
    (Periodic.MemSobolevPer.of_smoothPeriodic (d := d) γBar υSmooth).1
  hDυ_memLp := fun i =>
    (Periodic.MemSobolevPer.of_smoothPeriodic (d := d) γBar
        (Periodic.SmoothPeriodic.partialDeriv i υSmooth)).1
  hμ_periodic := μSmooth.periodic
  hυ_periodic := υSmooth.periodic
  hDυ_periodic := fun i =>
    (Periodic.SmoothPeriodic.partialDeriv i υSmooth).periodic
  hWeakDeriv := fun i =>
    Periodic.HasWeakDerivPer.of_contDiff i υSmooth

/-- **`set_perturbation`** — `μ = m + f`, `υ = u`, `Dυ = Du`.

Given upstream `(m, u, Du)` regularity and a periodic perturbation
`f : (Fin d → ℝ) → ℝ` with `f ∈ L^βBar_per`, build the regularity
record for `(m + f, u, Du)`.

The paper test family is `f = 1_S` for a measurable set `S` of
finite measure (its periodic indicator is in `L^βBar` for any
`βBar ≥ 1` since the unit cube has finite measure). The constructor
only uses the structural fact that `f` is a periodic `L^βBar`
function, so it covers the indicator case (with
`f := Set.indicator S 1`) and any other periodic non-negative
perturbation. -/
def set_perturbation
    {m u : (Fin d → ℝ) → ℝ} {Du : Fin d → (Fin d → ℝ) → ℝ}
    (base : PerTestTripleRegularity (d := d) βBar γBar m u Du)
    {f : (Fin d → ℝ) → ℝ}
    (hf_memLp : Periodic.MemLpPer (d := d) βBar f)
    (hf_periodic : Periodic.IsPeriodic f) :
    PerTestTripleRegularity (d := d) βBar γBar
      (fun x => m x + f x) u Du where
  hμ_memLp := by
    have hsum : Periodic.MemLpPer (d := d) βBar (m + f) :=
      Periodic.MemLpPer.add base.hμ_memLp hf_memLp
    have heq : (fun x => m x + f x) = m + f := rfl
    rw [heq]; exact hsum
  hυ_memLp := base.hυ_memLp
  hDυ_memLp := base.hDυ_memLp
  hμ_periodic := by
    intro k x
    have hm := base.hμ_periodic k x
    have hf := hf_periodic k x
    change m (x + fun i => (k i : ℝ)) + f (x + fun i => (k i : ℝ)) =
          m x + f x
    rw [hm, hf]
  hυ_periodic := base.hυ_periodic
  hDυ_periodic := base.hDυ_periodic
  hWeakDeriv := base.hWeakDeriv

/-- **`signed_perturbation`** — `μ = m + σ·m·g`, `υ = u`, `Dυ = Du`.

Paper form: `μ = m(1 ± φ/‖φ‖_∞)` with `φ ∈ C^∞(𝕋^d)`. We model `g`
as an a.e.-strongly-measurable, periodic function with the
pointwise bound `‖g x‖ ≤ M` a.e. on the unit cube — which is
exactly what `Set.indicator S 1` (the paper's `1_S` form, after the
`σ` sign absorption) satisfies with `M = 1`, and what `φ/‖φ‖_∞`
satisfies with `M = 1` after rescaling.

The crucial regularity step is `MemLpPer βBar (m·g)` via
`MeasureTheory.MemLp.of_le_mul` against `M·‖m‖`. -/
def signed_perturbation
    {m u : (Fin d → ℝ) → ℝ} {Du : Fin d → (Fin d → ℝ) → ℝ}
    (base : PerTestTripleRegularity (d := d) βBar γBar m u Du)
    (σ : ℝ) {g : (Fin d → ℝ) → ℝ} {M : ℝ}
    (hg_meas :
      MeasureTheory.AEStronglyMeasurable g
        (MeasureTheory.Measure.restrict MeasureTheory.volume
          (Periodic.UnitCube d)))
    (hg_bound :
      ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume
          (Periodic.UnitCube d)),
        ‖g x‖ ≤ M)
    (hg_periodic : Periodic.IsPeriodic g) :
    PerTestTripleRegularity (d := d) βBar γBar
      (fun x => m x + σ * (m x * g x)) u Du where
  hμ_memLp := by
    -- Step 1: `MemLpPer βBar (m·g)` via `MemLp.of_le_mul`.
    have hm_meas := base.hμ_memLp.aestronglyMeasurable
    have hmg_meas :
        MeasureTheory.AEStronglyMeasurable (fun x => m x * g x)
          (MeasureTheory.Measure.restrict MeasureTheory.volume
            (Periodic.UnitCube d)) := hm_meas.mul hg_meas
    have hmg_memLp :
        Periodic.MemLpPer (d := d) βBar (fun x => m x * g x) := by
      refine MemLp.toMemLpPer (MeasureTheory.MemLp.of_le_mul (g := m) (c := M)
        base.hμ_memLp.toMemLp hmg_meas ?_)
      filter_upwards [hg_bound] with x hx
      have : ‖m x * g x‖ = ‖m x‖ * ‖g x‖ := by
        simp [Real.norm_eq_abs]
      rw [this]
      have hnn_m : 0 ≤ ‖m x‖ := norm_nonneg _
      have hbound : ‖m x‖ * ‖g x‖ ≤ ‖m x‖ * M :=
        mul_le_mul_of_nonneg_left hx hnn_m
      have hcomm : M * ‖m x‖ = ‖m x‖ * M := mul_comm _ _
      rw [hcomm]; exact hbound
    -- Step 2: `MemLpPer βBar (σ·m·g)`.
    have hsmul :
        Periodic.MemLpPer (d := d) βBar
          (fun x => σ * (m x * g x)) := by
      have h1 := Periodic.MemLpPer.const_smul (𝕜 := ℝ) hmg_memLp σ
      have heq :
          (σ • (fun x => m x * g x))
            = fun x => σ * (m x * g x) := by
        funext x; simp [Pi.smul_apply, smul_eq_mul]
      rw [← heq]; exact h1
    -- Step 3: `MemLpPer βBar (m + σ·m·g)`.
    have hsum := Periodic.MemLpPer.add base.hμ_memLp hsmul
    have heq :
        (m + (fun x => σ * (m x * g x)))
          = fun x => m x + σ * (m x * g x) := rfl
    rw [← heq]; exact hsum
  hυ_memLp := base.hυ_memLp
  hDυ_memLp := base.hDυ_memLp
  hμ_periodic := by
    intro k x
    have hm := base.hμ_periodic k x
    have hg := hg_periodic k x
    change m (x + fun i => (k i : ℝ)) +
            σ * (m (x + fun i => (k i : ℝ))
                  * g (x + fun i => (k i : ℝ))) =
          m x + σ * (m x * g x)
    rw [hm, hg]
  hυ_periodic := base.hυ_periodic
  hDυ_periodic := base.hDυ_periodic
  hWeakDeriv := base.hWeakDeriv

/-! ### Helpers for `transport_perturbation`

The two helpers below specialise the additivity / scalar closure of
`HasWeakDerivPer` to the cases needed for the smooth transport
perturbation `υ + σ·φ`. They are stated locally, with assumptions
chosen so the integrability conditions for `periodicIntegral_add`
are easy to discharge from continuity of the smooth pieces. -/

open MeasureTheory in
private lemma hasWeakDerivPer_smul_smoothRight
    (i : Fin d) (σ : ℝ) (φ : Periodic.SmoothPeriodic d) :
    Periodic.HasWeakDerivPer i
      (fun x => σ * (φ : (Fin d → ℝ) → ℝ) x)
      (fun x => σ *
        ((Periodic.SmoothPeriodic.partialDeriv i φ :
            Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ) x) := by
  -- Use the smooth-classical case `HasWeakDerivPer.of_contDiff i φ`
  -- and close under `(σ·)`.
  have h := Periodic.HasWeakDerivPer.of_contDiff i φ
  refine ⟨?_, ?_⟩
  · -- `MemLpPer 1 (σ • ∂_iφ)`.
    have hL : Periodic.MemLpPer (d := d) 1
        ((Periodic.SmoothPeriodic.partialDeriv i φ :
            Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ) := h.1
    have hsmul := Periodic.MemLpPer.const_smul (𝕜 := ℝ) hL σ
    have heq :
        (σ • ((Periodic.SmoothPeriodic.partialDeriv i φ :
              Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ))
          = fun x => σ *
            ((Periodic.SmoothPeriodic.partialDeriv i φ :
                Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ) x := by
      funext x; simp [Pi.smul_apply, smul_eq_mul]
    rw [← heq]; exact hsmul
  · intro ψ
    -- LHS: `∫ (σ * ∂_iφ x) * ψ x = σ * ∫ ∂_iφ x * ψ x`.
    have hLHS_eq :
        (fun x => σ *
            ((Periodic.SmoothPeriodic.partialDeriv i φ :
                Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ) x *
            (ψ : (Fin d → ℝ) → ℝ) x)
          = fun x => σ •
            (((Periodic.SmoothPeriodic.partialDeriv i φ :
                Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ) x *
              (ψ : (Fin d → ℝ) → ℝ) x) := by
      funext x; simp [smul_eq_mul]; ring
    have hRHS_eq :
        (fun x => σ * (φ : (Fin d → ℝ) → ℝ) x *
            ((Periodic.SmoothPeriodic.partialDeriv i ψ :
                Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ) x)
          = fun x => σ •
            ((φ : (Fin d → ℝ) → ℝ) x *
              ((Periodic.SmoothPeriodic.partialDeriv i ψ :
                  Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ) x) := by
      funext x; simp [smul_eq_mul]; ring
    rw [hLHS_eq, hRHS_eq]
    rw [Periodic.periodicIntegral_smul (𝕜 := ℝ) σ
          (fun x => ((Periodic.SmoothPeriodic.partialDeriv i φ :
                Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ) x *
            (ψ : (Fin d → ℝ) → ℝ) x)]
    rw [Periodic.periodicIntegral_smul (𝕜 := ℝ) σ
          (fun x => (φ : (Fin d → ℝ) → ℝ) x *
            ((Periodic.SmoothPeriodic.partialDeriv i ψ :
                Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ) x)]
    rw [h.2 ψ]
    simp [smul_eq_mul]

open MeasureTheory in
/-- The integral identity for `(u + σ·φ, Du i + σ·∂_iφ)` directly, by
splitting and applying linearity to *both* sides. The integrability
requirements on the LHS are met by `Du i ∈ L¹_per` (from `base.hWeakDeriv`)
and continuity of `ψ`; on the RHS, by `u ∈ L¹_per` (from
`MemLpPer.mono_exponent` since `1 ≤ γBar` and the cube has finite
measure) and continuity of `∂_iψ`. -/
private lemma hasWeakDerivPer_add_smoothRight
    (i : Fin d) (σ : ℝ) (φ : Periodic.SmoothPeriodic d)
    {u : (Fin d → ℝ) → ℝ} {Du : (Fin d → ℝ) → ℝ}
    (hu_memLp : Periodic.MemLpPer (d := d) 1 u)
    (hWD : Periodic.HasWeakDerivPer i u Du) :
    Periodic.HasWeakDerivPer i
      (fun x => u x + σ * (φ : (Fin d → ℝ) → ℝ) x)
      (fun x => Du x +
        σ * ((Periodic.SmoothPeriodic.partialDeriv i φ :
            Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ) x) := by
  have hPart := hasWeakDerivPer_smul_smoothRight i σ φ
  refine ⟨?_, ?_⟩
  · -- `MemLpPer 1 (Du + σ·∂_iφ)`.
    have h1 : Periodic.MemLpPer (d := d) 1 Du := hWD.1
    have h2 := hPart.1
    have hsum := Periodic.MemLpPer.add h1 h2
    have heq :
        (Du + (fun x => σ *
          ((Periodic.SmoothPeriodic.partialDeriv i φ :
              Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ) x))
          = fun x => Du x +
            σ * ((Periodic.SmoothPeriodic.partialDeriv i φ :
                Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ) x := rfl
    rw [← heq]; exact hsum
  · intro ψ
    -- Notation shortcuts.
    set Diφ : (Fin d → ℝ) → ℝ :=
      ((Periodic.SmoothPeriodic.partialDeriv i φ :
          Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ) with hDiφ
    set σDiφ : (Fin d → ℝ) → ℝ := fun x => σ * Diφ x with hσDiφ
    set ψcoe : (Fin d → ℝ) → ℝ := ((ψ : (Fin d → ℝ) → ℝ)) with hψcoe
    set Diψ : (Fin d → ℝ) → ℝ :=
      ((Periodic.SmoothPeriodic.partialDeriv i ψ :
          Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ) with hDiψ
    set σφ : (Fin d → ℝ) → ℝ :=
      fun x => σ * (φ : (Fin d → ℝ) → ℝ) x with hσφ
    -- LHS: split as `(Du · ψ) + (σ·Diφ · ψ)` pointwise.
    have hLHS_eq :
        (fun x => (Du x + σDiφ x) * ψcoe x)
          = (fun x => Du x * ψcoe x)
              + (fun x => σDiφ x * ψcoe x) := by
      funext x; simp [hσDiφ]; ring
    -- RHS integrand: split as `(u · Diψ) + (σφ · Diψ)`.
    have hRHS_eq :
        (fun x => (u x + σφ x) * Diψ x)
          = (fun x => u x * Diψ x) + (fun x => σφ x * Diψ x) := by
      funext x; simp [hσφ]; ring
    -- Build integrability of all four product integrands.
    have hcompact :
        IsCompact (Set.pi Set.univ
          (fun _ : Fin d => Set.Icc (0 : ℝ) 1)) :=
      isCompact_univ_pi (fun _ => isCompact_Icc)
    have hsub : Periodic.UnitCube d ⊆
        Set.pi Set.univ (fun _ : Fin d => Set.Icc (0 : ℝ) 1) := by
      intro x hx j _
      exact Set.Ico_subset_Icc_self
        ((Periodic.mem_unitCube_iff.mp hx) j)
    have hψ_cont : Continuous ψcoe := ψ.smooth.continuous
    have hDiψ_cont : Continuous Diψ :=
      (Periodic.SmoothPeriodic.partialDeriv i ψ).smooth.continuous
    have hφ_cont : Continuous ((φ : (Fin d → ℝ) → ℝ)) :=
      φ.smooth.continuous
    have hDiφ_cont : Continuous Diφ :=
      (Periodic.SmoothPeriodic.partialDeriv i φ).smooth.continuous
    have hσφ_cont : Continuous σφ := by
      simpa [hσφ] using! (continuous_const.mul hφ_cont)
    have hσDiφ_cont : Continuous σDiφ := by
      simpa [hσDiφ] using! (continuous_const.mul hDiφ_cont)
    -- `Du · ψ` integrable: `Du ∈ L¹_per`, and `ψ` is continuous and
    -- bounded on the unit cube (which sits in a compact superset).
    obtain ⟨Cψ, hCψ⟩ :=
      hcompact.bddAbove_image hψ_cont.norm.continuousOn
    obtain ⟨CDiψ, hCDiψ⟩ :=
      hcompact.bddAbove_image hDiψ_cont.norm.continuousOn
    have h_bdd_ψ :
        ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume
                  (Periodic.UnitCube d)),
          ‖ψcoe x‖ ≤ Cψ := by
      refine (MeasureTheory.ae_restrict_iff'
          Periodic.measurableSet_unitCube).2 ?_
      refine Filter.Eventually.of_forall ?_
      intro x hx
      apply hCψ
      refine ⟨x, hsub hx, rfl⟩
    have h_bdd_Diψ :
        ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume
                  (Periodic.UnitCube d)),
          ‖Diψ x‖ ≤ CDiψ := by
      refine (MeasureTheory.ae_restrict_iff'
          Periodic.measurableSet_unitCube).2 ?_
      refine Filter.Eventually.of_forall ?_
      intro x hx
      apply hCDiψ
      refine ⟨x, hsub hx, rfl⟩
    have hDu_int : IntegrableOn Du (Periodic.UnitCube d) :=
      hWD.integrableOn
    have hu_int : IntegrableOn u (Periodic.UnitCube d) :=
      (MeasureTheory.memLp_one_iff_integrable).1 hu_memLp
    -- `Du · ψ` integrable: `Du ∈ L¹`, `ψ` bounded.
    have hDuψ_int : IntegrableOn (fun x => Du x * ψcoe x)
        (Periodic.UnitCube d) :=
      Integrable.mul_bdd hDu_int hψ_cont.aestronglyMeasurable h_bdd_ψ
    -- `σDiφ · ψ` integrable: σDiφ continuous on cube ⇒ bounded ⇒ in L¹.
    have hσDiφ_int :
        IntegrableOn σDiφ (Periodic.UnitCube d) :=
      (hσDiφ_cont.locallyIntegrable.integrableOn_isCompact
          hcompact).mono_set hsub
    have hσDiφψ_int :
        IntegrableOn (fun x => σDiφ x * ψcoe x)
          (Periodic.UnitCube d) :=
      Integrable.mul_bdd hσDiφ_int hψ_cont.aestronglyMeasurable h_bdd_ψ
    -- `u · Diψ` integrable.
    have huDiψ_int : IntegrableOn (fun x => u x * Diψ x)
        (Periodic.UnitCube d) :=
      Integrable.mul_bdd hu_int hDiψ_cont.aestronglyMeasurable h_bdd_Diψ
    -- `σφ · Diψ` integrable.
    have hσφ_int :
        IntegrableOn σφ (Periodic.UnitCube d) :=
      (hσφ_cont.locallyIntegrable.integrableOn_isCompact
          hcompact).mono_set hsub
    have hσφDiψ_int :
        IntegrableOn (fun x => σφ x * Diψ x)
          (Periodic.UnitCube d) :=
      Integrable.mul_bdd hσφ_int hDiψ_cont.aestronglyMeasurable h_bdd_Diψ
    -- Apply `periodicIntegral_add` on both sides, then plug in the
    -- two component IBP identities.
    rw [hLHS_eq, hRHS_eq]
    rw [Periodic.periodicIntegral_add hDuψ_int hσDiφψ_int]
    rw [Periodic.periodicIntegral_add huDiψ_int hσφDiψ_int]
    -- Use the identities `∫ Du·ψ = -∫ u·Diψ` and `∫ σDiφ·ψ = -∫ σφ·Diψ`.
    have hWD_eq :
        Periodic.periodicIntegral (fun x => Du x * ψcoe x) =
          - Periodic.periodicIntegral (fun x => u x * Diψ x) := hWD.2 ψ
    have hPart_eq :
        Periodic.periodicIntegral (fun x => σDiφ x * ψcoe x) =
          - Periodic.periodicIntegral (fun x => σφ x * Diψ x) := by
      have := hPart.2 ψ
      -- `hPart.2 ψ` already gives us this with `σDiφ` / `σφ` macros;
      -- match the integrand shapes.
      simpa [hσDiφ, hσφ, hDiψ, mul_comm, mul_left_comm, mul_assoc]
        using this
    rw [hWD_eq, hPart_eq]
    ring

/-- **`transport_perturbation`** — `μ = m`, `υ = u + σ·φ`,
`Dυ_i = Du_i + σ·∂_iφ`.

Paper form: `(μ, υ) = (m, u ± φ)` for `φ ∈ W^{1,γBar}(𝕋^d)`. We take
the smoother form `φ : SmoothPeriodic d`, which is the case used in
the proof of `lem:strong.is.strong` (where `φ ∈ C^∞`). The closure
under multiplication by a real scalar `σ` lets us absorb the `±`
into `σ ∈ {±1}`.

The `hγ_one_le` hypothesis (consistent with paper assumption
`γBar > 1`) is used only to deduce `u ∈ L¹_per` from `u ∈ L^γBar_per`,
which is in turn needed to make the integration-by-parts identity
in `hWeakDeriv` honest. -/
def transport_perturbation
    {m u : (Fin d → ℝ) → ℝ} {Du : Fin d → (Fin d → ℝ) → ℝ}
    (base : PerTestTripleRegularity (d := d) βBar γBar m u Du)
    (hγ_one_le : (1 : ℝ≥0∞) ≤ γBar)
    (σ : ℝ) (φ : Periodic.SmoothPeriodic d) :
    PerTestTripleRegularity (d := d) βBar γBar
      m
      (fun x => u x + σ * (φ : (Fin d → ℝ) → ℝ) x)
      (fun i x => Du i x +
        σ * ((Periodic.SmoothPeriodic.partialDeriv i φ :
                Periodic.SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) x) where
  hμ_memLp := base.hμ_memLp
  hυ_memLp := by
    have hφ_memLp : Periodic.MemLpPer (d := d) γBar
        ((φ : (Fin d → ℝ) → ℝ)) :=
      (Periodic.MemSobolevPer.of_smoothPeriodic (d := d) γBar φ).1
    have hsmul :
        Periodic.MemLpPer (d := d) γBar
          (fun x => σ * (φ : (Fin d → ℝ) → ℝ) x) := by
      have h1 := Periodic.MemLpPer.const_smul (𝕜 := ℝ) hφ_memLp σ
      have heq : (σ • ((φ : (Fin d → ℝ) → ℝ)))
          = fun x => σ * (φ : (Fin d → ℝ) → ℝ) x := by
        funext x; simp [Pi.smul_apply, smul_eq_mul]
      rw [← heq]; exact h1
    have hsum := Periodic.MemLpPer.add base.hυ_memLp hsmul
    have heq : (u + (fun x => σ * (φ : (Fin d → ℝ) → ℝ) x))
        = fun x => u x + σ * (φ : (Fin d → ℝ) → ℝ) x := rfl
    rw [← heq]; exact hsum
  hDυ_memLp := by
    intro i
    have hpart_memLp : Periodic.MemLpPer (d := d) γBar
        ((Periodic.SmoothPeriodic.partialDeriv i φ :
              Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ) :=
      (Periodic.MemSobolevPer.of_smoothPeriodic (d := d) γBar
          (Periodic.SmoothPeriodic.partialDeriv i φ)).1
    have hsmul :
        Periodic.MemLpPer (d := d) γBar
          (fun x => σ *
            ((Periodic.SmoothPeriodic.partialDeriv i φ :
                  Periodic.SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x) := by
      have h1 := Periodic.MemLpPer.const_smul (𝕜 := ℝ) hpart_memLp σ
      have heq :
          (σ • ((Periodic.SmoothPeriodic.partialDeriv i φ :
                    Periodic.SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ))
            = fun x => σ *
              ((Periodic.SmoothPeriodic.partialDeriv i φ :
                    Periodic.SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x := by
        funext x; simp [Pi.smul_apply, smul_eq_mul]
      rw [← heq]; exact h1
    have hsum := Periodic.MemLpPer.add (base.hDυ_memLp i) hsmul
    have heq :
        (Du i + (fun x => σ *
          ((Periodic.SmoothPeriodic.partialDeriv i φ :
                Periodic.SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) x))
          = fun x => Du i x +
            σ * ((Periodic.SmoothPeriodic.partialDeriv i φ :
                  Periodic.SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) x := rfl
    rw [← heq]; exact hsum
  hμ_periodic := base.hμ_periodic
  hυ_periodic := by
    intro k x
    have hu := base.hυ_periodic k x
    have hφ := φ.periodic k x
    change u (x + fun i => (k i : ℝ)) +
            σ * (φ : (Fin d → ℝ) → ℝ) (x + fun i => (k i : ℝ)) =
          u x + σ * (φ : (Fin d → ℝ) → ℝ) x
    rw [hu, hφ]
  hDυ_periodic := by
    intro i k x
    have hDu := base.hDυ_periodic i k x
    have hpart :=
      (Periodic.SmoothPeriodic.partialDeriv i φ).periodic k x
    change Du i (x + fun j => (k j : ℝ)) +
            σ * ((Periodic.SmoothPeriodic.partialDeriv i φ :
                  Periodic.SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) (x + fun j => (k j : ℝ)) =
          Du i x +
            σ * ((Periodic.SmoothPeriodic.partialDeriv i φ :
                  Periodic.SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x
    rw [hDu, hpart]
  hWeakDeriv := by
    intro i
    -- Reduce `u ∈ L^γBar_per` to `u ∈ L^1_per` via `mono_exponent`.
    haveI : MeasureTheory.IsFiniteMeasure
        (MeasureTheory.Measure.restrict MeasureTheory.volume
          (Periodic.UnitCube d)) := by
      refine ⟨?_⟩
      rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ]
      simp
    have hu_L1 : Periodic.MemLpPer (d := d) 1 u := by
      have hLp : MeasureTheory.MemLp u γBar
          (MeasureTheory.Measure.restrict MeasureTheory.volume
            (Periodic.UnitCube d)) := base.hυ_memLp
      have := MeasureTheory.MemLp.mono_exponent hLp hγ_one_le
      exact MemLp.toMemLpPer this
    exact hasWeakDerivPer_add_smoothRight i σ φ hu_L1 (base.hWeakDeriv i)

end PerTestTripleRegularity

/-! ### Phase 6a — `WeakLimitInputBundle.perTestTripleBase` -/

/-- **Phase 6a — base per-test-triple regularity from a
`WeakLimitInputBundle`.**

Pack the existing structural fields of `WeakLimitInputBundle`
(`hmLim_memLp`, `huLim_sob.1`, `hMlimPer`, `hUlimPer`) together with
the new `hDuLim_periodic` field and the derived `huLim_DuLim_weakDeriv`
weak-derivative tie into a `PerTestTripleRegularity` record indexed by
the bundle's own `(mLim, uLim, DuLim)` triple at `(βBar, γBar)`.

This is the **base** record. The perturbation-style refinements
(`set_perturbation`, `signed_perturbation`, `transport_perturbation`)
build on top of it for each paper test family. The strict-`γ̄`
`MemLpPer` for every gradient component is supplied by
`WeakLimitInputBundle.hDuLim_memLp_γ`. -/
theorem WeakLimitInputBundle.perTestTripleBase
    {γBarReal βBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (wkBundle : WeakLimitInputBundle (d := d) γBarReal βBarReal) :
    PerTestTripleRegularity (d := d)
      (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
      wkBundle.mLim wkBundle.uLim wkBundle.DuLim where
  hμ_memLp := wkBundle.hmLim_memLp
  hυ_memLp := wkBundle.huLim_sob.1
  hDυ_memLp := fun i => wkBundle.hDuLim_memLp_γ i
  hμ_periodic := wkBundle.hMlimPer
  hυ_periodic := wkBundle.hUlimPer
  hDυ_periodic := wkBundle.hDuLim_periodic
  hWeakDeriv := fun i => wkBundle.huLim_DuLim_weakDeriv i

/-- **Phase 6a — sanity check.** `perTestTripleBase` is well-typed and
projectable on a generic `WeakLimitInputBundle`. -/
example
    {γBarReal βBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (wkBundle : WeakLimitInputBundle (d := d) γBarReal βBarReal) :
    PerTestTripleRegularity (d := d)
      (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
      wkBundle.mLim wkBundle.uLim wkBundle.DuLim :=
  wkBundle.perTestTripleBase

/-- **AC3 — base per-test-triple regularity from a
`WeakLimitInputBundleAE`.** Mirrors `WeakLimitInputBundle.perTestTripleBase`
on the AE-native bundle, packing the structural fields together with
the derived weak-derivative tie. -/
theorem WeakLimitInputBundleAE.perTestTripleBase
    {γBarReal βBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (B : WeakLimitInputBundleAE (d := d) γBarReal βBarReal) :
    PerTestTripleRegularity (d := d)
      (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
      B.mLim B.uLim B.DuLim where
  hμ_memLp := B.hmLim_memLp
  hυ_memLp := B.huLim_sob.1
  hDυ_memLp := fun i => B.hDuLim_memLp_γ i
  hμ_periodic := B.hMlimPer
  hυ_periodic := B.hUlimPer
  hDυ_periodic := B.hDuLim_periodic
  hWeakDeriv := fun i => B.huLim_DuLim_weakDeriv i

/-- **AC4 sanity check.** `perTestTripleBase` is projectable on any
`WeakLimitInputBundleAE`. -/
example
    {γBarReal βBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (B : WeakLimitInputBundleAE (d := d) γBarReal βBarReal) :
    PerTestTripleRegularity (d := d)
      (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
      B.mLim B.uLim B.DuLim :=
  B.perTestTripleBase

/-! ### Sanity-check `example`s -/

/-- `ofSmoothPeriodic` sanity check. -/
example (βBar γBar : ℝ≥0∞) (μSmooth υSmooth : Periodic.SmoothPeriodic d) :
    PerTestTripleRegularity (d := d) βBar γBar
      ((μSmooth : (Fin d → ℝ) → ℝ))
      ((υSmooth : (Fin d → ℝ) → ℝ))
      (fun i =>
        ((Periodic.SmoothPeriodic.partialDeriv i υSmooth :
            Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ)) :=
  PerTestTripleRegularity.ofSmoothPeriodic βBar γBar μSmooth υSmooth

/-- `set_perturbation` sanity check. -/
example {βBar γBar : ℝ≥0∞}
    {m u : (Fin d → ℝ) → ℝ} {Du : Fin d → (Fin d → ℝ) → ℝ}
    (base : PerTestTripleRegularity (d := d) βBar γBar m u Du)
    {f : (Fin d → ℝ) → ℝ}
    (hf_memLp : Periodic.MemLpPer (d := d) βBar f)
    (hf_periodic : Periodic.IsPeriodic f) :
    PerTestTripleRegularity (d := d) βBar γBar
      (fun x => m x + f x) u Du :=
  PerTestTripleRegularity.set_perturbation base hf_memLp hf_periodic

/-- `signed_perturbation` sanity check. -/
example {βBar γBar : ℝ≥0∞}
    {m u : (Fin d → ℝ) → ℝ} {Du : Fin d → (Fin d → ℝ) → ℝ}
    (base : PerTestTripleRegularity (d := d) βBar γBar m u Du)
    (σ : ℝ) {g : (Fin d → ℝ) → ℝ} {M : ℝ}
    (hg_meas :
      MeasureTheory.AEStronglyMeasurable g
        (MeasureTheory.Measure.restrict MeasureTheory.volume
          (Periodic.UnitCube d)))
    (hg_bound :
      ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume
          (Periodic.UnitCube d)),
        ‖g x‖ ≤ M)
    (hg_periodic : Periodic.IsPeriodic g) :
    PerTestTripleRegularity (d := d) βBar γBar
      (fun x => m x + σ * (m x * g x)) u Du :=
  PerTestTripleRegularity.signed_perturbation base σ
    hg_meas hg_bound hg_periodic

/-- `transport_perturbation` sanity check. -/
example {βBar γBar : ℝ≥0∞}
    {m u : (Fin d → ℝ) → ℝ} {Du : Fin d → (Fin d → ℝ) → ℝ}
    (base : PerTestTripleRegularity (d := d) βBar γBar m u Du)
    (hγ_one_le : (1 : ℝ≥0∞) ≤ γBar)
    (σ : ℝ) (φ : Periodic.SmoothPeriodic d) :
    PerTestTripleRegularity (d := d) βBar γBar
      m
      (fun x => u x + σ * (φ : (Fin d → ℝ) → ℝ) x)
      (fun i x => Du i x +
        σ * ((Periodic.SmoothPeriodic.partialDeriv i φ :
                Periodic.SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) x) :=
  PerTestTripleRegularity.transport_perturbation base hγ_one_le σ φ

/-! ## AC3: three specialized strong-VI lemmas at the perturbation triple

Per `infra-P4-pairing-selector-AC3-strongVI-bare-test-triple`, the
Option-B pivot drops the contradictory universal-test-triple shape
and ships **three** specialized strong-VI lemmas — one per paper
test family — at the regularized solution `(sol.m, sol.u, sol.Du)`.

Each lemma takes a `RegularizedBareSolution` plus the perturbation
parameters (a measurable set `S` of finite measure for set/signed,
a smooth periodic `φ` for transport) plus the matching
`PerTestTripleRegularity` record (built via
`PerTestTripleRegularity.{set,signed,transport}_perturbation`), and
concludes the strong VI at the perturbation triple.

The proofs invoke the per-family fields `hVIeps_set`,
`hVIeps_signed`, `hVIeps_transport` of `RegularizedBareSolution`
(which already encode the analytic content: the Banach round-trip
through `Aepsi_CLM_op_apply` + `mfgOperatorEpsPair_congr_ae` was
discharged inside the children C/D of the two-domain redesign that
produce these fields). The remaining work is structural: identify
the perturbation form's `(μ, υ, Dυ)` with the field's expected
shape, then pointwise/`=ᵐ` rewrites to land the conclusion in the
perturbation form.

The `PerTestTripleRegularity` record is consumed only as a witness
of which test triple the strong VI is stated at; its regularity
data is read off directly. Hence these lemmas are quotient-boundary
clean: no raw `Lp.coeFn` outside the (already-discharged) Banach
round-trip in `hVIeps_*`. -/

/-- **`strongVI_set_at_eps`** — the strong VI at the set-perturbation
triple `(sol.m + 𝟙_S, sol.u, sol.Du)`.

Inputs:
* `sol : RegularizedBareSolution` at parameter `ε`.
* `S : Set (Fin d → ℝ)` measurable.
* A `PerTestTripleRegularity` record for the perturbation triple
  (built via `PerTestTripleRegularity.set_perturbation` from a base
  record for `(sol.m, sol.u, sol.Du)`, with
  `f := S.indicator (fun _ => 1)`).

Conclusion: `0 ≤ mfgOperatorEpsPair γBarReal ε sol.Du
                   (sol.m + 𝟙_S) sol.u 0 𝟙_S 0`.

Proof: apply `sol.hVIeps_set` with `S := Set.univ` and
`ρ := sol.m + S.indicator (fun _ => 1)`, then transport via
`mfgOperatorEpsPair_congr_ae` (test direction:
`sol.Du - sol.Du =ᵐ 0`, `(univ.indicator ρ) - sol.m =ᵐ 𝟙_S`,
`sol.u - sol.u =ᵐ 0`) and a pointwise `Set.indicator_univ`
unfold for the primal density. -/
theorem strongVI_set_at_eps
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal')
    (S : Set (Fin d → ℝ)) (_hS : MeasurableSet S)
    (_reg : PerTestTripleRegularity (d := d)
              (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
              (fun x => sol.m x + S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              sol.u sol.Du) :
    0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          sol.Du
          (fun x => sol.m x + S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          sol.u
          (fun _ _ => (0 : ℝ))
          (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)))
          (fun _ => (0 : ℝ)) := by
  -- The `_reg` record carries the MemLpPer/MemSobolevPer
  -- certificates for the perturbation triple `(ρ, sol.u, sol.Du)`,
  -- which we feed to the (now tightened) `sol.hVIeps_set` field.
  -- The analytic content is supplied by `sol.hVIeps_set`. The
  -- measurability of `S` is not needed since we apply `hVIeps_set` at
  -- `Set.univ` (matching shape only).
  -- Apply `hVIeps_set` with `S := Set.univ` and
  -- `ρ := sol.m + S.indicator 1` (≥ 0 a.e. via `sol.hmNonneg`).
  set f : (Fin d → ℝ) → ℝ :=
    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) with hf_def
  set ρ : (Fin d → ℝ) → ℝ := fun x => sol.m x + f x with hρ_def
  have hρ_nn :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        0 ≤ ρ x := by
    have hf_nn : ∀ x, 0 ≤ f x := by
      intro x
      by_cases hxS : x ∈ S
      · simp [hf_def, Set.indicator_of_mem hxS]
      · simp [hf_def, Set.indicator_of_notMem hxS]
    filter_upwards [sol.hmNonneg] with x hxm
    exact add_nonneg hxm (hf_nn x)
  -- MemLpPer βBar (Set.univ.indicator ρ): rewrite via indicator_univ
  -- and use `_reg.hμ_memLp` (which is `MemLpPer βBar ρ`).
  have hSρ_memLp :
      MemLpPer (d := d) (ENNReal.ofReal βBarReal)
        (Set.univ.indicator ρ) := by
    have heq : (Set.univ.indicator ρ : (Fin d → ℝ) → ℝ) = ρ := by
      funext x; simp
    rw [heq]; exact _reg.hμ_memLp
  -- MemSobolevPer γBar sol.u: pair `_reg.hυ_memLp` with the
  -- weak-derivative tie `_reg.hWeakDeriv` (witness family `Dυ = sol.Du`).
  have hυ_memSob :
      MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) sol.u :=
    ⟨_reg.hυ_memLp, ⟨sol.Du, _reg.hWeakDeriv⟩⟩
  have hDυ_memLp :
      ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (sol.Du i) :=
    _reg.hDυ_memLp
  have hVI := sol.hVIeps_set Set.univ MeasurableSet.univ ρ sol.u sol.Du
                hρ_nn hSρ_memLp hυ_memSob hDυ_memLp sol.hWeakDeriv
  -- Transport to the desired conclusion via `mfgOperatorEpsPair_congr_ae`.
  -- LHS conclusion has direction `(0, f, 0)` and primal density `ρ`.
  -- RHS of `hVIeps_set` has direction
  -- `(sol.Du - sol.Du, univ.indicator ρ - sol.m, sol.u - sol.u)`
  -- (the latter two as `Pi.sub`) and primal density `univ.indicator ρ`.
  have hindicator_univ :
      ∀ x, Set.univ.indicator ρ x = ρ x := by
    intro x; simp
  have hDν_ae : ∀ i,
      (fun x => sol.Du i x - sol.Du i x)
        =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
      (fun _ : Fin d → ℝ => (0 : ℝ)) := by
    intro i
    refine Filter.Eventually.of_forall ?_
    intro x; simp
  have hη_ae :
      (Set.univ.indicator ρ - sol.m)
        =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
      f := by
    refine Filter.Eventually.of_forall ?_
    intro x
    change Set.univ.indicator ρ x - sol.m x = f x
    rw [hindicator_univ x]
    simp [hρ_def]
  have hν_ae :
      (sol.u - sol.u)
        =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
      (fun _ : Fin d → ℝ => (0 : ℝ)) := by
    refine Filter.Eventually.of_forall ?_
    intro x; simp [Pi.sub_apply]
  -- Apply `mfgOperatorEpsPair_congr_ae` to rewrite the direction
  -- `(Dν, η, ν)` in `hVI`.
  have hcongr := mfgOperatorEpsPair_congr_ae
    (V := V) (H := H) (DpH := DpH)
    γBarReal ε
    sol.Du (Set.univ.indicator ρ) sol.u
    (fun i x => sol.Du i x - sol.Du i x)
    (fun (_ : Fin d) (_ : Fin d → ℝ) => (0 : ℝ))
    (Set.univ.indicator ρ - sol.m)
    f
    (sol.u - sol.u)
    (fun _ : Fin d → ℝ => (0 : ℝ))
    hDν_ae hη_ae hν_ae
  rw [hcongr] at hVI
  -- Now rewrite the primal density `Set.univ.indicator ρ → ρ` (pointwise eq).
  have hρ_eq : Set.univ.indicator ρ = ρ := by
    funext x; exact hindicator_univ x
  rw [hρ_eq] at hVI
  -- `ρ = fun x => sol.m x + f x` is by `set` definition.
  exact hVI

/-- **`strongVI_signed_at_eps`** — the strong VI at the signed-perturbation
triple `(sol.m + σ · sol.m · 𝟙_S, sol.u, sol.Du)`.

Inputs:
* `sol : RegularizedBareSolution`.
* A sign `σ ∈ {+1, -1}`.
* A measurable set `S` of finite restricted-cube measure.
* A `PerTestTripleRegularity` record for the perturbation triple.

The conclusion is `0 ≤ mfgOperatorEpsPair ...` at the perturbation
triple, in the paper-exact `StrongVI_setForm_signed` shape (`hVIeps_signed`).

Proof: direct invocation of `sol.hVIeps_signed`. The
`hVIeps_signed` field already has the perturbation-form shape; the
only adjustment is matching `σ * m x * 1_S x` vs
`σ * (m x * 1_S x)` (these are equal by `mul_assoc`). -/
theorem strongVI_signed_at_eps
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal')
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (S : Set (Fin d → ℝ)) (hS : MeasurableSet S)
    (hSfin : (MeasureTheory.volume.restrict (UnitCube d)) S < ⊤)
    (_reg : PerTestTripleRegularity (d := d)
              (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
              (fun x => sol.m x +
                σ * (sol.m x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
              sol.u sol.Du) :
    0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          sol.Du
          (fun x => sol.m x +
            σ * (sol.m x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
          sol.u
          (fun _ _ => (0 : ℝ))
          (fun x => σ * (sol.m x *
            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
          (fun _ => (0 : ℝ)) := by
  -- The `_reg` record is consumed structurally.
  have hVI := sol.hVIeps_signed σ hσ S hS hSfin
  -- `hVIeps_signed` produces the same shape modulo `σ * m * 1_S`
  -- vs `σ * (m * 1_S)` (associativity). Reduce via
  -- `mfgOperatorEpsPair_congr_ae` on the *primal* density and the
  -- direction's `η` slot.
  have hμ_eq :
      (fun x => sol.m x + σ * sol.m x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
        = (fun x => sol.m x + σ *
                  (sol.m x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)) := by
    funext x; ring
  have hη_eq :
      (fun x => σ * sol.m x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
        = (fun x => σ * (sol.m x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)) := by
    funext x; ring
  rw [hμ_eq, hη_eq] at hVI
  exact hVI

/-- **`strongVI_transport_at_eps`** — the strong VI at the
transport-perturbation triple
`(sol.m, sol.u + σ·φ, sol.Du + σ·∂φ)`.

Inputs:
* `sol : RegularizedBareSolution`.
* A real scalar `σ` (paper takes `σ ∈ {±1}`; the field is stronger
  and accepts any `σ`).
* A smooth periodic `φ : SmoothPeriodic d`.
* A `PerTestTripleRegularity` record for the perturbation triple.

The conclusion is `0 ≤ mfgOperatorEpsPair ...` at the perturbation
triple, with directions `(σ·∂φ, 0, σ·φ)`.

Proof: invoke `sol.hVIeps_transport` with `σ := sol.m` (which is
`≥ 0` a.e. by `sol.hmNonneg`), `υ := sol.u + σ·φ`,
`φ_test := sol.Du + σ·∂φ`. The resulting direction
`((Du + σ·∂φ) - Du, m - m, (u + σ·φ) - u) = (σ·∂φ, 0, σ·φ)` is
matched via `mfgOperatorEpsPair_congr_ae`. -/
theorem strongVI_transport_at_eps
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal')
    (σ : ℝ) (φ : Periodic.SmoothPeriodic d)
    (_reg : PerTestTripleRegularity (d := d)
              (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
              sol.m
              (fun x => sol.u x + σ * (φ : (Fin d → ℝ) → ℝ) x)
              (fun i x => sol.Du i x +
                σ * ((Periodic.SmoothPeriodic.partialDeriv i φ :
                        Periodic.SmoothPeriodic d) :
                    (Fin d → ℝ) → ℝ) x)) :
    0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          (fun i x => sol.Du i x +
            σ * ((Periodic.SmoothPeriodic.partialDeriv i φ :
                    Periodic.SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x)
          sol.m
          (fun x => sol.u x + σ * (φ : (Fin d → ℝ) → ℝ) x)
          (fun i x =>
            σ * ((Periodic.SmoothPeriodic.partialDeriv i φ :
                    Periodic.SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x)
          (fun _ => (0 : ℝ))
          (fun x => σ * (φ : (Fin d → ℝ) → ℝ) x) := by
  -- The `_reg` record carries the MemLpPer/MemSobolevPer
  -- certificates for the perturbation triple `(sol.m, υTest, φTest)`,
  -- which we feed to the (now tightened) `sol.hVIeps_transport`
  -- field.
  -- Apply `hVIeps_transport` with `σ := sol.m`, υ-test = u + σ·φ,
  -- φ-test = Du + σ·∂φ.
  set φTest : Fin d → (Fin d → ℝ) → ℝ :=
    fun i x => sol.Du i x +
      σ * ((Periodic.SmoothPeriodic.partialDeriv i φ :
              Periodic.SmoothPeriodic d) :
          (Fin d → ℝ) → ℝ) x with hφTest_def
  set υTest : (Fin d → ℝ) → ℝ :=
    fun x => sol.u x + σ * (φ : (Fin d → ℝ) → ℝ) x with hυTest_def
  -- MemLpPer βBar sol.m: from `_reg.hμ_memLp` (its primal density is
  -- already `sol.m`).
  have hσ_memLp :
      MemLpPer (d := d) (ENNReal.ofReal βBarReal) sol.m :=
    _reg.hμ_memLp
  -- MemSobolevPer γBar υTest: pair `_reg.hυ_memLp` with the
  -- weak-derivative tie (witness family `φTest`, supplied by `_reg`).
  have hυTest_memSob :
      MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υTest :=
    ⟨_reg.hυ_memLp, ⟨φTest, _reg.hWeakDeriv⟩⟩
  have hφTest_memLp :
      ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (φTest i) :=
    _reg.hDυ_memLp
  have hVI := sol.hVIeps_transport sol.m υTest φTest sol.hmNonneg
                hσ_memLp hυTest_memSob hφTest_memLp _reg.hWeakDeriv
  -- `hVI` shape: direction `((φTest - sol.Du), (sol.m - sol.m), (υTest - sol.u))`
  -- where the latter two are `Pi.sub`.
  -- Target shape: direction `(σ·∂φ, 0, σ·φ)`.
  have hDν_ae : ∀ i,
      (fun x => φTest i x - sol.Du i x)
        =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
      (fun x =>
        σ * ((Periodic.SmoothPeriodic.partialDeriv i φ :
                Periodic.SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) x) := by
    intro i
    refine Filter.Eventually.of_forall ?_
    intro x
    simp [hφTest_def]
  have hη_ae :
      (sol.m - sol.m)
        =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
      (fun _ : Fin d → ℝ => (0 : ℝ)) := by
    refine Filter.Eventually.of_forall ?_
    intro x; simp [Pi.sub_apply]
  have hν_ae :
      (υTest - sol.u)
        =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
      (fun x => σ * (φ : (Fin d → ℝ) → ℝ) x) := by
    refine Filter.Eventually.of_forall ?_
    intro x
    simp [Pi.sub_apply, hυTest_def]
  have hcongr := mfgOperatorEpsPair_congr_ae
    (V := V) (H := H) (DpH := DpH)
    γBarReal ε
    φTest sol.m υTest
    (fun i x => φTest i x - sol.Du i x)
    (fun i x =>
      σ * ((Periodic.SmoothPeriodic.partialDeriv i φ :
              Periodic.SmoothPeriodic d) :
          (Fin d → ℝ) → ℝ) x)
    (sol.m - sol.m)
    (fun _ : Fin d → ℝ => (0 : ℝ))
    (υTest - sol.u)
    (fun x => σ * (φ : (Fin d → ℝ) → ℝ) x)
    hDν_ae hη_ae hν_ae
  rw [hcongr] at hVI
  exact hVI

/-! ### Sanity-check `example`s for the three AC3 strong-VI lemmas -/

/-- Sanity check: `strongVI_set_at_eps` typechecks. -/
example
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal')
    (S : Set (Fin d → ℝ)) (hS : MeasurableSet S)
    (reg : PerTestTripleRegularity (d := d)
              (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
              (fun x => sol.m x + S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              sol.u sol.Du) :
    0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          sol.Du
          (fun x => sol.m x + S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          sol.u
          (fun _ _ => (0 : ℝ))
          (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)))
          (fun _ => (0 : ℝ)) :=
  strongVI_set_at_eps sol S hS reg

/-- Sanity check: `strongVI_signed_at_eps` typechecks. -/
example
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal')
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (S : Set (Fin d → ℝ)) (hS : MeasurableSet S)
    (hSfin : (MeasureTheory.volume.restrict (UnitCube d)) S < ⊤)
    (reg : PerTestTripleRegularity (d := d)
              (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
              (fun x => sol.m x +
                σ * (sol.m x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
              sol.u sol.Du) :
    0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          sol.Du
          (fun x => sol.m x +
            σ * (sol.m x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
          sol.u
          (fun _ _ => (0 : ℝ))
          (fun x => σ * (sol.m x *
            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
          (fun _ => (0 : ℝ)) :=
  strongVI_signed_at_eps sol σ hσ S hS hSfin reg

/-- Sanity check: `strongVI_transport_at_eps` typechecks. -/
example
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal')
    (σ : ℝ) (φ : Periodic.SmoothPeriodic d)
    (reg : PerTestTripleRegularity (d := d)
              (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
              sol.m
              (fun x => sol.u x + σ * (φ : (Fin d → ℝ) → ℝ) x)
              (fun i x => sol.Du i x +
                σ * ((Periodic.SmoothPeriodic.partialDeriv i φ :
                        Periodic.SmoothPeriodic d) :
                    (Fin d → ℝ) → ℝ) x)) :
    0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          (fun i x => sol.Du i x +
            σ * ((Periodic.SmoothPeriodic.partialDeriv i φ :
                    Periodic.SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x)
          sol.m
          (fun x => sol.u x + σ * (φ : (Fin d → ℝ) → ℝ) x)
          (fun i x =>
            σ * ((Periodic.SmoothPeriodic.partialDeriv i φ :
                    Periodic.SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x)
          (fun _ => (0 : ℝ))
          (fun x => σ * (φ : (Fin d → ℝ) → ℝ) x) :=
  strongVI_transport_at_eps sol σ φ reg

/-! ### W^{1,γ̄}-tester variant of `strongVI_transport_at_eps`

The smooth-tester `strongVI_transport_at_eps` (above) only invokes
`sol.hVIeps_transport`, which itself (by construction in
`AssemblyContext.lean:569`) accepts arbitrary `MemSobolevPer (γ̄)` test
value-functions and `MemLpPer (γ̄)` test gradient fields. Hence the
smooth tester is a strict specialisation of the underlying field.

This section lifts the smooth-tester wrapper to a `MemSobolevPer (γ̄)`
tester, closing the dependency child filed back in iter 462 by
`infra-P5-theorem1-closed-phase1-hVIeps-transport-extend-to-MemSobolevPer-tester`.
The version takes:
* a real scalar `σ`,
* a bare `varphi : (Fin d → ℝ) → ℝ` with `MemLpPer (γ̄) varphi`,
* an explicit weak-derivative witness family
  `Dvarphi : Fin d → (Fin d → ℝ) → ℝ` with
  `HasWeakDerivPer i varphi (Dvarphi i)` and
  `MemLpPer (γ̄) (Dvarphi i)` for every `i`.

Proof strategy: build the `MemSobolevPer (γ̄)` certificate for the
perturbation `sol.u + σ·varphi` by additivity (`HasWeakDerivPer.add` /
`MemLpPer.add`) and scalar mult (`HasWeakDerivPer.const_smul` /
`MemLpPer.const_smul`); feed the result to `sol.hVIeps_transport`;
reshape the conclusion via `mfgOperatorEpsPair_congr_ae`. -/

/-- **`strongVI_transport_at_eps_W1`** — `W^{1,γ̄}_per`-tester version
of the strong VI at the transport-perturbation triple
`(sol.m, sol.u + σ·varphi, sol.Du + σ·Dvarphi)`.

Inputs:
* `sol : RegularizedBareSolution`.
* A real scalar `σ` (paper takes `σ ∈ {±1}`; the field is stronger
  and accepts any `σ`).
* A bare `varphi : (Fin d → ℝ) → ℝ` together with `MemLpPer (γ̄)
  varphi`, an explicit weak-derivative witness `Dvarphi : Fin d →
  (Fin d → ℝ) → ℝ` with `HasWeakDerivPer i varphi (Dvarphi i)` and
  `MemLpPer (γ̄) (Dvarphi i)` for every `i`. (These together
  certify `varphi ∈ W^{1,γ̄}_per`.)
* The exponent `γBarReal` is assumed `≥ 1` so that `MemLpPer (γ̄) ⊆
  L¹_per` (used by the linearity step in `HasWeakDerivPer.add`).

Conclusion: `0 ≤ mfgOperatorEpsPair ...` at the transport-perturbation
triple, with directions `(σ·Dvarphi, 0, σ·varphi)`. -/
theorem strongVI_transport_at_eps_W1
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal')
    (hp_ge_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal γBarReal)
    (σ : ℝ)
    (varphi : (Fin d → ℝ) → ℝ)
    (Dvarphi : Fin d → (Fin d → ℝ) → ℝ)
    (h_varphi_memLp : MemLpPer (d := d) (ENNReal.ofReal γBarReal) varphi)
    (h_Dvarphi_weak : ∀ i, HasWeakDerivPer (d := d) i varphi (Dvarphi i))
    (h_Dvarphi_memLp :
      ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dvarphi i)) :
    0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          (fun i x => sol.Du i x + σ * Dvarphi i x)
          sol.m
          (fun x => sol.u x + σ * varphi x)
          (fun i x => σ * Dvarphi i x)
          (fun _ => (0 : ℝ))
          (fun x => σ * varphi x) := by
  -- Names matching the smooth-tester proof for clarity.
  set φTest : Fin d → (Fin d → ℝ) → ℝ :=
    fun i x => sol.Du i x + σ * Dvarphi i x with hφTest_def
  set υTest : (Fin d → ℝ) → ℝ :=
    fun x => sol.u x + σ * varphi x with hυTest_def
  -- σ-perturbed `MemLpPer` certs for `varphi` and each `Dvarphi i`.
  have h_sigma_varphi_memLp :
      MemLpPer (d := d) (ENNReal.ofReal γBarReal)
        (fun x => σ * varphi x) := by
    have := h_varphi_memLp.const_smul (𝕜 := ℝ) σ
    -- `(σ • varphi) x = σ * varphi x` pointwise.
    have hpt :
        (σ • varphi : (Fin d → ℝ) → ℝ) = fun x => σ * varphi x := by
      funext x; simp [Pi.smul_apply, smul_eq_mul]
    rw [hpt] at this
    exact this
  have h_sigma_Dvarphi_memLp : ∀ i,
      MemLpPer (d := d) (ENNReal.ofReal γBarReal)
        (fun x => σ * Dvarphi i x) := by
    intro i
    have := (h_Dvarphi_memLp i).const_smul (𝕜 := ℝ) σ
    have hpt :
        (σ • Dvarphi i : (Fin d → ℝ) → ℝ) = fun x => σ * Dvarphi i x := by
      funext x; simp [Pi.smul_apply, smul_eq_mul]
    rw [hpt] at this
    exact this
  -- `MemLpPer γ̄ υTest`.
  have hυTest_memLp :
      MemLpPer (d := d) (ENNReal.ofReal γBarReal) υTest := by
    -- `υTest = sol.u + σ * varphi`.
    have hadd := sol.huLp.add h_sigma_varphi_memLp
    -- `(sol.u + (fun x => σ * varphi x)) x = sol.u x + σ * varphi x`.
    have hpt :
        (sol.u + (fun x => σ * varphi x) : (Fin d → ℝ) → ℝ)
          = υTest := by
      funext x; simp [hυTest_def, Pi.add_apply]
    rw [hpt] at hadd
    exact hadd
  -- `MemLpPer γ̄ (φTest i)` for each `i`.
  have hφTest_memLp : ∀ i,
      MemLpPer (d := d) (ENNReal.ofReal γBarReal) (φTest i) := by
    intro i
    have hadd := (sol.hDuLp i).add (h_sigma_Dvarphi_memLp i)
    have hpt :
        (sol.Du i + (fun x => σ * Dvarphi i x) : (Fin d → ℝ) → ℝ)
          = φTest i := by
      funext x; simp [hφTest_def, Pi.add_apply]
    rw [hpt] at hadd
    exact hadd
  -- `HasWeakDerivPer i υTest (φTest i)` for each `i`.
  have hυTest_weakDeriv : ∀ i,
      HasWeakDerivPer (d := d) i υTest (φTest i) := by
    intro i
    -- `σ * varphi` has weak derivative `σ * Dvarphi i`.
    have h_sigma : HasWeakDerivPer (d := d) i
        (fun x => σ * varphi x) (fun x => σ * Dvarphi i x) :=
      (h_Dvarphi_weak i).const_smul σ
    -- `sol.u + σ * varphi` has weak derivative
    -- `sol.Du i + σ * Dvarphi i`. The Lp hypothesis on each summand uses
    -- `hp_ge_one` to ensure `Lᵖ ⊆ L¹` on the unit cube.
    have hadd := HasWeakDerivPer.add (p := ENNReal.ofReal γBarReal)
      hp_ge_one sol.huLp h_sigma_varphi_memLp
      (sol.hWeakDeriv i) h_sigma
    -- Reshape `(fun x => sol.u x + σ * varphi x)` and the derivative.
    have hpt_f : (fun x : Fin d → ℝ => sol.u x + σ * varphi x) = υTest := by
      funext x; simp [hυTest_def]
    have hpt_g :
        (fun x : Fin d → ℝ => sol.Du i x + σ * Dvarphi i x) = φTest i := by
      funext x; simp [hφTest_def]
    rw [hpt_f, hpt_g] at hadd
    exact hadd
  -- `MemSobolevPer γ̄ υTest`.
  have hυTest_memSob :
      MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υTest :=
    ⟨hυTest_memLp, ⟨φTest, hυTest_weakDeriv⟩⟩
  -- Apply the underlying field at `(σ := sol.m, υ := υTest, φ := φTest)`.
  have hVI := sol.hVIeps_transport sol.m υTest φTest sol.hmNonneg
                sol.hmLp hυTest_memSob hφTest_memLp hυTest_weakDeriv
  -- Reshape via `mfgOperatorEpsPair_congr_ae` to the target direction
  -- `(σ·Dvarphi, 0, σ·varphi)` — same shape as the smooth-tester proof.
  have hDν_ae : ∀ i,
      (fun x => φTest i x - sol.Du i x)
        =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
      (fun x => σ * Dvarphi i x) := by
    intro i
    refine Filter.Eventually.of_forall ?_
    intro x
    simp [hφTest_def]
  have hη_ae :
      (sol.m - sol.m)
        =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
      (fun _ : Fin d → ℝ => (0 : ℝ)) := by
    refine Filter.Eventually.of_forall ?_
    intro x; simp [Pi.sub_apply]
  have hν_ae :
      (υTest - sol.u)
        =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
      (fun x => σ * varphi x) := by
    refine Filter.Eventually.of_forall ?_
    intro x
    simp [Pi.sub_apply, hυTest_def]
  have hcongr := mfgOperatorEpsPair_congr_ae
    (V := V) (H := H) (DpH := DpH)
    γBarReal ε
    φTest sol.m υTest
    (fun i x => φTest i x - sol.Du i x)
    (fun i x => σ * Dvarphi i x)
    (sol.m - sol.m)
    (fun _ : Fin d → ℝ => (0 : ℝ))
    (υTest - sol.u)
    (fun x => σ * varphi x)
    hDν_ae hη_ae hν_ae
  rw [hcongr] at hVI
  exact hVI

/-- Sanity check: `strongVI_transport_at_eps_W1` typechecks. -/
example
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal')
    (hp_ge_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal γBarReal)
    (σ : ℝ)
    (varphi : (Fin d → ℝ) → ℝ)
    (Dvarphi : Fin d → (Fin d → ℝ) → ℝ)
    (h_varphi_memLp : MemLpPer (d := d) (ENNReal.ofReal γBarReal) varphi)
    (h_Dvarphi_weak : ∀ i, HasWeakDerivPer (d := d) i varphi (Dvarphi i))
    (h_Dvarphi_memLp :
      ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dvarphi i)) :
    0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          (fun i x => sol.Du i x + σ * Dvarphi i x)
          sol.m
          (fun x => sol.u x + σ * varphi x)
          (fun i x => σ * Dvarphi i x)
          (fun _ => (0 : ℝ))
          (fun x => σ * varphi x) :=
  strongVI_transport_at_eps_W1 sol hp_ge_one σ varphi Dvarphi
    h_varphi_memLp h_Dvarphi_weak h_Dvarphi_memLp

/-! ### Perturbed-primal strong-transport VI at `varphi = sol.u`

Specialising `strongVI_transport_at_eps_W1` at the test pair
`(varphi, Dvarphi) := (sol.u, sol.Du)` yields the **perturbed-primal**
strong-transport VI (paper line 1185, `eq:Aepsi.strong-ineq` at
`(μ,υ) = (m, u + σ·u_ε)`). The Sobolev membership for `sol.u` is
read off `sol.huLp` / `sol.hWeakDeriv` / `sol.hDuLp` directly.

The conclusion's integrand has H/D_pH/`|·|^{γ̄−2}` evaluated at the
**perturbed primal** `((1+s)·sol.Du, sol.m, (1+s)·sol.u)`. The σ → 0
reduction (which collapses the `1+s` slots back to the bare primal)
is the σ-bridge sibling task; it is **not** done here.

Per CONVENTIONS §1b/§8, integrability of the two integrand families
(at the perturbed primal) is taken as authorised inputs. Both reduce
to the standard product-of-`Lᵝ´·Lᵝ`/`Lᵞ´·Lᵞ` integrability at the
perturbed primal, but `sol.hInt` only provides this at the *bare*
primal `(sol.Du, sol.m, sol.u)`; perturbed-primal integrability is a
follow-up workstream filed as a separate child task. -/

/-- **`strongTransport_at_uEpsi_perturbed`** — the perturbed-primal
strong-transport VI.

Direct specialisation of `strongVI_transport_at_eps_W1` at
`varphi := sol.u`, `Dvarphi := sol.Du`, σ := s. The
`mfgOperatorEpsPair` output is unfolded definitionally into
`mfgOperatorPair + ε·gateauxWpPair`, and the two integrals are
combined via integrability of the per-summand integrands (taken as
authorised inputs).

Conclusion: the displayed integrand at the perturbed primal
`((1+s)·sol.Du, sol.m, (1+s)·sol.u)`, with test triple
`(s·sol.Du, 0, s·sol.u)`. -/
theorem strongTransport_at_uEpsi_perturbed
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal')
    (hp_ge_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal γBarReal)
    (s : ℝ)
    -- Integrability of the simplified mfg-pair integrand at the
    -- perturbed primal (authorised input; cf. `MFGOpEpsAuxHyps` at
    -- the perturbed primal).
    (hI_A : IntegrableOn
      (fun x =>
        sol.m x * (DpH x (fun i => sol.Du i x + s * sol.Du i x) (sol.m x)
                      ⬝ (fun i => s * sol.Du i x))
          + (sol.m x - 1) * (s * sol.u x))
      (UnitCube d))
    -- Integrability of the gateaux-pair integrand at the perturbed primal.
    (hI_B : IntegrableOn
      (fun x =>
        vecAbsPowMinusTwo γBarReal
              (fun i => sol.Du i x + s * sol.Du i x)
            * ((fun i => sol.Du i x + s * sol.Du i x)
               ⬝ (fun i => s * sol.Du i x))
          + absPowMinusTwo γBarReal
              (sol.u x + s * sol.u x)
            * ((sol.u x + s * sol.u x)
               * (s * sol.u x)))
      (UnitCube d)) :
    0 ≤
    ∫ x in UnitCube d,
        (sol.m x * (DpH x (fun i => sol.Du i x + s * sol.Du i x) (sol.m x)
                      ⬝ (fun i => s * sol.Du i x))
          + (sol.m x - 1) * (s * sol.u x)
          + ε * (vecAbsPowMinusTwo γBarReal
                    (fun i => sol.Du i x + s * sol.Du i x)
                    * ((fun i => sol.Du i x + s * sol.Du i x)
                       ⬝ (fun i => s * sol.Du i x))
                  + absPowMinusTwo γBarReal
                      (sol.u x + s * sol.u x)
                    * ((sol.u x + s * sol.u x)
                       * (s * sol.u x))))
        ∂volume := by
  -- Step 1: apply the W^{1,γ̄} tester at varphi := sol.u, Dvarphi := sol.Du.
  have hVI := strongVI_transport_at_eps_W1 sol hp_ge_one s sol.u sol.Du
                sol.huLp sol.hWeakDeriv sol.hDuLp
  -- Step 2: unfold mfgOperatorEpsPair definitionally to
  --   mfgOperatorPair + ε * gateauxWpPair.
  unfold mfgOperatorEpsPair mfgOperatorPair gateauxWpPair at hVI
  -- Step 3: simplify the mfg-pair integrand by killing the `· * 0` term.
  set Aint : (Fin d → ℝ) → ℝ := fun x =>
    sol.m x * (DpH x (fun i => sol.Du i x + s * sol.Du i x) (sol.m x)
                  ⬝ (fun i => s * sol.Du i x))
      + (sol.m x - 1) * (s * sol.u x) with hAint_def
  set Bint : (Fin d → ℝ) → ℝ := fun x =>
    vecAbsPowMinusTwo γBarReal
          (fun i => sol.Du i x + s * sol.Du i x)
        * ((fun i => sol.Du i x + s * sol.Du i x)
           ⬝ (fun i => s * sol.Du i x))
      + absPowMinusTwo γBarReal
          (sol.u x + s * sol.u x)
        * ((sol.u x + s * sol.u x)
           * (s * sol.u x)) with hBint_def
  -- The `mfgOperatorPair`-integrand at our test triple equals `Aint`
  -- pointwise (since the η-component is `fun _ => 0`).
  have hA_pt :
      ∀ x,
        (-(sol.u x + s * sol.u x)
            - H x (fun i => sol.Du i x + s * sol.Du i x) (sol.m x) + V x)
              * ((fun _ : Fin d → ℝ => (0 : ℝ)) x)
          + sol.m x
              * (DpH x (fun i => sol.Du i x + s * sol.Du i x) (sol.m x)
                  ⬝ (fun i => s * sol.Du i x))
          + (sol.m x - 1) * (s * sol.u x)
        = Aint x := by
    intro x
    simp [hAint_def]
  -- The `gateauxWpPair`-integrand at our test triple equals `Bint` literally.
  have hB_pt :
      ∀ x,
        vecAbsPowMinusTwo γBarReal
              (fun i => sol.Du i x + s * sol.Du i x)
            * ((fun i => sol.Du i x + s * sol.Du i x)
               ⬝ (fun i => s * sol.Du i x))
          + absPowMinusTwo γBarReal
              (sol.u x + s * sol.u x)
            * ((sol.u x + s * sol.u x)
               * (s * sol.u x)) = Bint x := by
    intro x
    simp [hBint_def]
  -- Rewrite the two integrals inside `hVI` to be `∫ Aint` and `∫ Bint`.
  rw [setIntegral_congr_fun measurableSet_unitCube
        (fun x _ => hA_pt x),
      setIntegral_congr_fun measurableSet_unitCube
        (fun x _ => hB_pt x)] at hVI
  -- Step 4: combine `(∫ Aint) + ε * (∫ Bint)` into `∫ (Aint + ε * Bint)`.
  have hgoal_combined :
      ∫ x in UnitCube d, (Aint x + ε * Bint x) ∂volume
        = (∫ x in UnitCube d, Aint x ∂volume)
          + ε * (∫ x in UnitCube d, Bint x ∂volume) := by
    rw [MeasureTheory.integral_add hI_A (hI_B.const_mul ε),
        MeasureTheory.integral_const_mul]
  -- The goal integrand equals `Aint + ε * Bint` pointwise.
  have hgoal_pt :
      ∀ x,
        sol.m x * (DpH x (fun i => sol.Du i x + s * sol.Du i x) (sol.m x)
                      ⬝ (fun i => s * sol.Du i x))
          + (sol.m x - 1) * (s * sol.u x)
          + ε * (vecAbsPowMinusTwo γBarReal
                    (fun i => sol.Du i x + s * sol.Du i x)
                    * ((fun i => sol.Du i x + s * sol.Du i x)
                       ⬝ (fun i => s * sol.Du i x))
                  + absPowMinusTwo γBarReal
                      (sol.u x + s * sol.u x)
                    * ((sol.u x + s * sol.u x)
                       * (s * sol.u x)))
          = Aint x + ε * Bint x := by
    intro x
    simp [hAint_def, hBint_def]
  rw [setIntegral_congr_fun measurableSet_unitCube
        (fun x _ => hgoal_pt x), hgoal_combined]
  exact hVI

/-- Sanity check: `strongTransport_at_uEpsi_perturbed` typechecks. -/
example
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal')
    (hp_ge_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal γBarReal)
    (s : ℝ)
    (hI_A : IntegrableOn
      (fun x =>
        sol.m x * (DpH x (fun i => sol.Du i x + s * sol.Du i x) (sol.m x)
                      ⬝ (fun i => s * sol.Du i x))
          + (sol.m x - 1) * (s * sol.u x))
      (UnitCube d))
    (hI_B : IntegrableOn
      (fun x =>
        vecAbsPowMinusTwo γBarReal
              (fun i => sol.Du i x + s * sol.Du i x)
            * ((fun i => sol.Du i x + s * sol.Du i x)
               ⬝ (fun i => s * sol.Du i x))
          + absPowMinusTwo γBarReal
              (sol.u x + s * sol.u x)
            * ((sol.u x + s * sol.u x)
               * (s * sol.u x)))
      (UnitCube d)) :
    0 ≤
    ∫ x in UnitCube d,
        (sol.m x * (DpH x (fun i => sol.Du i x + s * sol.Du i x) (sol.m x)
                      ⬝ (fun i => s * sol.Du i x))
          + (sol.m x - 1) * (s * sol.u x)
          + ε * (vecAbsPowMinusTwo γBarReal
                    (fun i => sol.Du i x + s * sol.Du i x)
                    * ((fun i => sol.Du i x + s * sol.Du i x)
                       ⬝ (fun i => s * sol.Du i x))
                  + absPowMinusTwo γBarReal
                      (sol.u x + s * sol.u x)
                    * ((sol.u x + s * sol.u x)
                       * (s * sol.u x))))
        ∂volume :=
  strongTransport_at_uEpsi_perturbed sol hp_ge_one s hI_A hI_B

/-! ## AC6 — Compose AC1–AC5 into `limitPairingSelector_of_paperHypotheses`

Per the in-flight task `infra-P4-pairing-selector-AC6-genuine-producer`,
this final orchestration closes the pairing-selector chain by building
a `LimitPairingSelector` from `(hmon, hpow, hV, hExp, seq, wkBundle,
regBundle, gateauxAux, residue)` — pure record assembly threading
AC1–AC5 producers.

The genuine Path-A residues that none of AC1–AC5 can close on their
own (strict positivity of the test density `μ`, dominator
`MemLpPer`-membership for the Hamiltonian estimates, periodic-rep
selector for arbitrary `MemLpPer q` testers, smooth-tester
convergence + uniform `L^p`-bound for the F.5 weak limits, and the
strict-`γ̄` `MemLpPer` on the chosen `wkBundle.DuLim` per
coordinate) are bundled in a single
`LimitPairingSelectorPaperResidue` record per CONVENTIONS §8. Each
field of the residue is an authorised input named after a follow-up
backlog task (`infra-P4-ADFGU-test-triple-dominator-closure`,
`infra-P4-pairing-selector-AC1-density-Lq-bare`,
`infra-P4-rebuild-T9-discharge-pairing-inputs-selector`, etc.). Per
Phase F0 strip
(`infra-P5-theorem1-phase-F0-strip-hVI-eps-universal`, iter 310),
the universal regularised-VI residue has been lifted out of this
record; it is now supplied as a separate authorised parameter to
`limitPairingSelector_of_paperHypotheses` (and at the chain level
via `T10PaperResidues.hVI_eps_universalOf`). The legacy
`LimitPassageInputData.hVI_eps` field in `Closure.lean` remains in
place for Theorem 2 / congestion code per expert review. -/

/-- **Authorised paper-residue bundle for the AC6 producer.**

Per CONVENTIONS §8, this structure isolates the genuinely Path-A
residues that none of AC1–AC5 can discharge from
`(hmon, hpow, hV, hExp, seq, wkBundle, regBundle)` alone. Each field
is named after the follow-up task that closes it.

Fields:

* `hpqβ`, `hpqγ` — the two real-valued Hölder conjugacies; structurally
  derivable from `hExp.βConj/γConj` modulo `ENNReal.toReal_ofReal`,
  taken here as direct residues to avoid threading the `toReal`
  identities through every callsite.

* `hDuLim_memLp_γ` — strict-`γ̄` `MemLpPer` of every coordinate of
  `wkBundle.DuLim`. Note: `wkBundle.huLim_sob` carries an
  *existentially-quantified* weak-derivative family that need not be
  `wkBundle.DuLim`; the strict-`γ̄` `MemLpPer` on `DuLim` itself is
  a Path-A residue.

* `hμ_pos`, `hg_meas`, `hG_HJB_mem`, `hF_meas`, `hG_flux_mem` — per
  test triple, the strict-positivity / measurability /
  dominator-`MemLpPer` inputs that
  `Hamiltonian.{flux,g}_memLp_*_at_test` (AC2) consume. The HJB
  upper-bound `h_upper` (with constant `C' := hpow.C`) is now read
  off the new `hpow.H_upper_pointwise` field of
  `HypothesisPowerGrowth` directly (see paper Lemma `lem:ADFGU`,
  `eq:boundsH`); it is no longer a residue. The dominator closures
  from `(μ ∈ L^β̄, υ ∈ L^γ̄, Dυ ∈ L^γ̄, V ∈ L^β̄')` are filed
  as `infra-P4-ADFGU-test-triple-dominator-closure`; the strict
  positivity matches the paper's `essinf μ > 0` constraint
  (`Source/FGU-monotone_revised.tex` lines 303, 1330).

* `hμMinusOne_memLp` — the `(μ - 1) ∈ L^{γ̄'}_per` mass-defect
  multiplier; structurally derivable from `regBundle.hμ_memLp` plus
  the paper inequality `γ̄' ≤ β̄` (`gammaBar'_le_betaBar`), taken here
  as a residue to avoid threading the `ENNReal`-side inequality
  through the orchestration.

* `hWeakConv_*_uniformBound`, `hWeakConv_*_smoothTester`,
  `hWeakConv_*_select` (one triple per component `m`, `u`, `Du i`) —
  the inputs to AC2-bare's
  `weakConvPairing_universal_of_smoothTester_density`: a uniform
  `lpNormPer` bound on the sequence, the smooth-tester convergence
  (paper F.5 product weak convergence specialised to smooth
  testers), and the periodic-representative selector
  (`infra-P4-pairing-selector-AC1-density-Lq-bare`).

**Phase F0 strip note** (`infra-P5-theorem1-phase-F0-strip-hVI-eps-universal`,
iter 310). The legacy `hVI_eps_universal` field — the universal
regularised-VI input to F.6's `LimitPassageInputData.hVI_eps` — has
been removed from this residue. Theorem 1's chain now sources the
universal regularised-VI directly from `T10PaperResidues` (see
`BanachBridge.lean`), where it is supplied as a separate authorised
residue. The legacy `LimitPairingSelector` /
`limitPairingInputs_of_regularizedSequence` plumbing — which still
threads this universal weak-VI input as a separate parameter —
remains in place untouched, available to Theorem 2 / congestion
code per expert review. AC6's `limitPairingSelector_of_paperHypotheses`
producer now takes the universal weak-VI as a separate explicit
parameter (paralleling
`limitPairingInputs_of_regularizedSequence`'s shape).
-/
structure LimitPairingSelectorPaperResidue
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH)
    (wkBundle : WeakLimitInputBundleAE (d := d) γBarReal βBarReal)
    -- **`infra-P5-T10-D5-hmu-pos-shape-audit`** (Outcome A): the
    -- residue is now indexed by a family domain `D : Set (MFGTriple d)`
    -- so the strict-positivity field `hμ_pos` consumes a family-membership
    -- hypothesis `(μ, υ, Dυ) ∈ D`, matching the paper's "admissible test
    -- triples" framing of `essinf μ > 0`
    -- (`Source/FGU-monotone_revised.tex` lines 303 / 1330).
    (D : Set (StationaryMFG.Theorems.SimplePower.MFGTriple d)) where
  -- **`infra-P5-theorem1-remove-pairingResidue-hpq-dependency`** (Formalizer
  -- iter 0493). The Hölder-conjugacy fields `hpqβ`/`hpqγ` have been removed:
  -- they are now derived in-place by downstream producers via
  -- `hpqBeta_paperResidue` / `hpqGamma_paperResidue` from `(_hExp, hpow,
  -- hβBarEq, hβBar'Eq, hγBarEq, hγBar'Eq)`. The producer-side bridge is
  -- a closed-form derivation; no per-residue Hölder data is consumed.
  -- **Phase H5b strip**
  -- (`infra-P5-theorem1-phase-H5b-drop-hDuLim-memLp-from-finIntResidue`).
  -- The legacy field `hDuLim_memLp_γ` (strict-`γ̄` `MemLpPer` on every
  -- coordinate of `wkBundle.DuLim`) has been removed: it is now derived
  -- structurally inside `limitPairingSelector_of_paperHypotheses` from
  -- `wkBundle.hDuLim_memLp_γ` (Lp.memLp + MemLp.ae_eq via
  -- `auxAeOfClusterPoint`).
  /-- **Family-scoped a.e. non-negativity**
  (`infra-P5-T10-v7-phase4-hmu-posAuth-drain`, iter 0580 audit).
  For every test triple `(μ, υ, Dυ)` admissible in the family domain
  `D`, the density `μ` is a.e. non-negative on the unit cube. This
  is the paper-faithful weakening of the previous strict-positivity
  shape: the three paper families
  (`D_set_family_paper`, `D_signed_family_paper_nn`,
  `D_transport_family_paper`) all contain the unperturbed limit
  triple where `μ = mLim`, so strict positivity `0 < μ` is
  unprovable. The downstream consumers (HJB / flux `MemLpPer`)
  switch to the `_nonneg` variants
  `Hamiltonian.g_memLp_betaBar'_nonneg` /
  `Hamiltonian.flux_memLp_gammaBar'_nonneg`. -/
  hμ_nonneg : ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄
                ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
              (μ, υ, Dυ) ∈ D →
              0 ≤ᵐ[MeasureTheory.volume.restrict (Periodic.UnitCube d)] μ
  -- **`infra-P5-T10-drop-pairingResidueOf`** (Formalizer iter): the
  -- AE strong measurability fields `hg_meas` (HJB multiplier
  -- `g = -υ - H(·, Dυ, μ) + V`) and `hF_meas` (flux `μ · DpH(·, Dυ, μ)_i`)
  -- have been removed. They are now derived in-place inside
  -- `limitPairingSelectorFamily_of_paperHypotheses_at` from the
  -- per-test-triple `MemLpPer` data supplied by `regSupplier_D`,
  -- the joint measurabilities `hpow.measurable_H` /
  -- `hpow.measurable_DpH` (inherited from `RegularityH`), and the
  -- threaded-through `hV : MemLpPer βBar' V` paper hypothesis,
  -- via `Measurable.comp_aemeasurable`. The remaining single field
  -- `hμ_pos` is the paper's `essinf μ > 0` authorisation.
  --
  -- **`infra-P5-T10-drop-pairingResidueOf-final-hmu-pos`** (Option A):
  -- the wrapping `T10PaperResidues.pairingResidueOf` field has been
  -- dropped; the residual `hμ_pos` content is now exposed as the slim
  -- flat field `T10PaperResidues.hμ_posOf`. This single-field
  -- `LimitPairingSelectorPaperResidue` structure remains here as the
  -- consumer-side shape and is constructed inline at the chain site
  -- in `simplePowerThinChain_of_paperHypotheses`.
  -- **Phase H2 strip note**
  -- (`infra-P5-theorem1-phase-H2-discharge-weak-pairing-residues`,
  -- iter ≥311). The three universal weak-pairing certificates
  -- `h_weak_m`, `h_weak_u`, `h_weak_Du` have been **dropped from this
  -- residue** and lifted out as separate authorised parameters of
  -- `limitPairingSelector_of_paperHypotheses` (and threaded through
  -- `T10PaperResidues.h_weak_{m,u,Du}Of` at the chain level), mirroring
  -- the F0 strip of `hVI_eps_universal`. The discharge pattern is
  -- structural: AC2-bare's universal-form constructor
  -- `weakConvPairing_universal_of_smoothTester_density` requires three
  -- ingredients (smooth-tester convergence, uniform `lpNormPer`
  -- bound, and `AEPeriodicRep` density selector
  -- `infra-P4-pairing-selector-AC1-density-Lq-bare`) that are not
  -- bundled into `WeakLimitInputBundle`; the certificates therefore
  -- remain authorised paper inputs but are no longer surfaced through
  -- `LimitPairingSelectorPaperResidue`.

/-- **Sanity check** for `infra-P5-T10-drop-pairingResidueOf` (Formalizer
iter): `LimitPairingSelectorPaperResidue` can be constructed from just
the single paper-residue field `hμ_pos` (the AE strong measurability
fields `hg_meas` / `hF_meas` are now derived in-place inside
`limitPairingSelectorFamily_of_paperHypotheses_at`; the Hölder fields
`hpqβ` / `hpqγ` were earlier dropped per
`infra-P5-theorem1-remove-pairingResidue-hpq-dependency`). -/
example
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH)
    (wkBundle : WeakLimitInputBundleAE (d := d) γBarReal βBarReal)
    (D : Set (StationaryMFG.Theorems.SimplePower.MFGTriple d))
    (hμ_nonneg : ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄
                   ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
                  (μ, υ, Dυ) ∈ D →
                  0 ≤ᵐ[MeasureTheory.volume.restrict (Periodic.UnitCube d)] μ) :
    LimitPairingSelectorPaperResidue (d := d)
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      (V := V) (H := H) (DpH := DpH) hpow seq wkBundle D :=
  { hμ_nonneg := hμ_nonneg }

/-- **AC6 producer (genuine).** Compose AC1–AC5 into a
`LimitPairingSelector` from `(hmon, hpow, hV, hExp, seq, wkBundle,
regBundle, gateauxAux, residue)`.

The fields of the produced selector are wired as follows:

* `hpqβ`, `hpqγ` — read off `residue` (structurally derivable from
  `hExp.βConj/γConj` modulo `ENNReal.toReal_ofReal`).
* `hDuLim_memLp_γ` — read off `residue.hDuLim_memLp_γ`.
* `hυ_memLp`, `hDυ_memLp`, `hμ_memLp` per test triple — read off
  `regBundle μ υ Dυ`.
* `hg_memLp`, `hflux_memLp`, `hμMinusOne_memLp` per test triple —
  produced by `Hamiltonian.g_memLp_betaBar'_at_test`,
  `Hamiltonian.flux_memLp_gammaBar'_at_test`, and
  `residue.hμMinusOne_memLp` respectively (AC2).
* `h_weak_m`, `h_weak_u`, `h_weak_Du` — read off `residue` (Path-A
  residues from AC2-bare; closed by
  `infra-P4-pairing-selector-AC1-density-Lq-bare`).
* `hVI_eps_set/_signed/_transport` per `k` — read off the
  `(seq.sol k).hVIeps_set/_signed/_transport` fields directly
  (these match the paper-family universal shapes byte-for-byte).
* `M`, `hreg_bdd` per test triple — read off `gateauxAux.M` /
  `gateauxAux.hreg_bdd` (AC4).
* `hpair_conv` per test triple — built by constructing a
  `LimitPassageInputData` from the upstream fields and applying
  `LimitPassageInputData.tendsto_mfgOperatorPair_assembled` (AC5). -/
noncomputable def limitPairingSelector_of_paperHypotheses
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (_hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (_hExp : SimplePowerExponentFacts γBarReal
                (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
                (ENNReal.ofReal βBarReal'))
    -- **`infra-P5-T10-v7-phase4-hmu-posAuth-drain`** (iter 0580 audit).
    -- The HJB `MemLpPer β̄'` discharge has migrated to the
    -- non-strict-positivity variant `g_memLp_betaBar'_nonneg`, which
    -- consumes the three paper-`(a:Hat0)` riders.
    -- `hFin` is derived in-body via
    -- `Hamiltonian.Hext_finite_at_zero_of_powerGrowth`.
    (hHat0 : StationaryMFG.Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : StationaryMFG.Hamiltonian.H_zero_eq_Hext (d := d) H)
    (seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH)
    (wkBundle : WeakLimitInputBundleAE (d := d) γBarReal βBarReal)
    (regBundle : ∀ (μ υ : (Fin d → ℝ) → ℝ)
                    (Dυ : Fin d → (Fin d → ℝ) → ℝ),
                   PerTestTripleRegularity (d := d)
                     (ENNReal.ofReal βBarReal)
                     (ENNReal.ofReal γBarReal) μ υ Dυ)
    (gateauxAux : LimitPairingSelectorGateauxAux (d := d) seq)
    (hβBarEq : βBarReal = hpow.β + 1)
    (hγBarEq : γBarReal = hpow.α * (hpow.β + 1) / hpow.β)
    (hβBar'Eq : βBarReal' = (hpow.β + 1) / hpow.β)
    (hγBar'Eq : γBarReal' = hpow.α * (hpow.β + 1) / hpow.β /
                              (hpow.α * (hpow.β + 1) / hpow.β - 1))
    -- **`infra-P5-T10-D5-hmu-pos-shape-audit`** (Outcome A): the
    -- residue is now indexed by `Set.univ`. After
    -- `infra-P5-T10-v7-phase4-hmu-posAuth-drain` (iter 0580) the
    -- field `hμ_pos` was retyped to `hμ_nonneg`, consumed below at the
    -- universal `Set.mem_univ _`.
    (residue : LimitPairingSelectorPaperResidue (d := d)
                  (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  (V := V) (H := H) (DpH := DpH) hpow seq wkBundle
                  Set.univ)
    -- **Phase 5b** (`infra-P5-theorem1-phase-5b-rebuild-pairing-on-noVI`).
    -- The legacy `hVI_eps_universal` parameter has been dropped: the
    -- `hpair_conv` proof below now invokes
    -- `tendsto_mfgOperatorPair_assembled_noVI` against the leaner
    -- `LimitPassageInputData_noVI` shape, which never reads
    -- `hVI_eps`.
    -- **Phase H2 strip**
    -- (`infra-P5-theorem1-phase-H2-discharge-weak-pairing-residues`).
    -- The three universal weak-pairing certificates have been lifted
    -- out of `LimitPairingSelectorPaperResidue` and are now supplied
    -- as separate authorised parameters, mirroring the F0 strip of
    -- `hVI_eps_universal`.
    --
    -- **`infra-P5-theorem1-remove-pairingResidue-hpq-dependency`** (Formalizer
    -- iter 0493): the parameter types now reference
    -- `hpqBeta_paperResidue _hExp ...` / `hpqGamma_paperResidue _hExp ...`
    -- instead of `residue.hpqβ` / `residue.hpqγ`, which are no longer
    -- fields of `LimitPairingSelectorPaperResidue`.
    (h_weak_m_universal : WeakConvPairing_universal (d := d)
                            (hpqBeta_paperResidue (d := d) hpow _hExp
                              hβBarEq hβBar'Eq)
                            (fun k => (seq.sol k).m) wkBundle.mLim)
    (h_weak_u_universal : WeakConvPairing_universal (d := d)
                            (hpqGamma_paperResidue (d := d) hpow _hExp
                              hγBarEq hγBar'Eq)
                            (fun k => (seq.sol k).u) wkBundle.uLim)
    (h_weak_Du_universal : ∀ i,
        WeakConvPairing_universal (d := d)
          (hpqGamma_paperResidue (d := d) hpow _hExp hγBarEq hγBar'Eq)
          (fun k => (seq.sol k).Du i) (wkBundle.DuLim i)) :
    LimitPairingSelector (d := d)
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      (V := V) (H := H) (DpH := DpH)
      seq wkBundle.mLim wkBundle.uLim wkBundle.DuLim :=
  -- Phase G — derive the dominator memberships in closed form from
  -- `(hpow, hV)` + the per-test-triple regularity supplied by `regBundle`.
  -- The exponent equalities `hβBarEq`, `hγBarEq`, `hβBar'Eq`, `hγBar'Eq`
  -- bridge the abstract residue exponents to the paper formulas
  -- (β̄ = β+1, γ̄ = α(β+1)/β, β̄' = (β+1)/β, γ̄' = γ̄/(γ̄-1)).
  -- `hV` is now consumed by `g_dominator_memLp_betaBar'`.
  -- `μ` exponent: `ENNReal.ofReal βBarReal = ENNReal.ofReal (hpow.β+1)`.
  let hβ_cast : ENNReal.ofReal βBarReal = ENNReal.ofReal (hpow.β + 1) :=
    by rw [hβBarEq]
  let hγ_cast : ENNReal.ofReal γBarReal
                  = ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β) :=
    by rw [hγBarEq]
  let hβ'_cast : ENNReal.ofReal βBarReal'
                  = ENNReal.ofReal ((hpow.β + 1) / hpow.β) :=
    by rw [hβBar'Eq]
  let hγ'_cast : ENNReal.ofReal γBarReal'
                  = ENNReal.ofReal
                      (hpow.α * (hpow.β + 1) / hpow.β /
                       (hpow.α * (hpow.β + 1) / hpow.β - 1)) :=
    by rw [hγBar'Eq]
  -- Cast the test-triple `MemLpPer` from abstract exponents to paper formulas.
  let hμ_paper : ∀ (μ υ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ),
      Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1)) μ :=
    fun μ υ Dυ => hβ_cast ▸ (regBundle μ υ Dυ).hμ_memLp
  let hυ_paper : ∀ (μ υ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ),
      Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) υ :=
    fun μ υ Dυ => hγ_cast ▸ (regBundle μ υ Dυ).hυ_memLp
  let hDυ_paper : ∀ (μ υ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ)
      (i : Fin d),
      Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) (Dυ i) :=
    fun μ υ Dυ i => hγ_cast ▸ (regBundle μ υ Dυ).hDυ_memLp i
  -- `V ∈ L^{β̄'}` cast to paper exponent.
  let hV_paper : Periodic.MemLpPer (d := d)
                    (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) V :=
    hβ'_cast ▸ hV
  -- HJB-side dominator: `g_dominator_memLp_betaBar'` produces it at
  -- `ENNReal.ofReal ((β+1)/β) = ENNReal.ofReal βBarReal'`.
  let hG_HJB_mem : ∀ (μ υ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ),
              Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal')
                (fun x : (Fin d → ℝ) =>
                  hpow.C * (‖fun i => Dυ i x‖ ^ hpow.α + 1)
                    + hpow.C * (μ x ^ hpow.β + 1)
                    + |υ x| + |V x|) :=
    fun μ υ Dυ =>
      hβ'_cast ▸
        (Hamiltonian.g_dominator_memLp_betaBar' (h := hpow)
          V υ μ Dυ (hμ_paper μ υ Dυ) (hυ_paper μ υ Dυ)
          (hDυ_paper μ υ Dυ) hV_paper hpow.hC)
  -- Flux-side dominator: `flux_dominator_memLp_gammaBar'` produces it at
  -- the paper γ̄' formula = `ENNReal.ofReal γBarReal'`.
  let hG_flux_mem : ∀ (μ υ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ),
                 Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
                   (fun x : (Fin d → ℝ) =>
                     hpow.C * (μ x * ‖fun j => Dυ j x‖ ^ (hpow.α - 1)
                                + μ x ^ (1 + hpow.β - hpow.β / hpow.α)
                                + μ x)) :=
    fun μ υ Dυ =>
      hγ'_cast ▸
        (Hamiltonian.flux_dominator_memLp_gammaBar' (h := hpow)
          μ Dυ (hμ_paper μ υ Dυ) (hDυ_paper μ υ Dυ))
  -- **Phase H1 strip discharge** of `hμMinusOne_memLp` (formerly a
  -- `LimitPairingSelectorPaperResidue` field, now derived in-place).
  -- Uses `Hamiltonian.gammaBar'_le_betaBar` (paper `eq:gamma` inclusion
  -- `γ̄' ≤ β̄`) plus `Hamiltonian.μMinusOne_memLp_of_betaBar` at
  -- `(p := β̄, q := γ̄')`, with the paper-exponent equalities
  -- `hβBarEq, hγBar'Eq` bridging the abstract exponents to the
  -- canonical `(α, β)` shape. Adapted from the analogous discharge in
  -- `Banach.AssemblyContext.lean` (lines 5300-5314, 5358-5363).
  have hγ'_le_β :
      ENNReal.ofReal γBarReal' ≤ ENNReal.ofReal βBarReal := by
    have hle_real : γBarReal' ≤ βBarReal := by
      rw [hγBar'Eq, hβBarEq]
      have h_paper := Hamiltonian.gammaBar'_le_betaBar hpow.hα hpow.hβ
      -- `h_paper : α(β+1)/β / (α(β+1)/β - 1) ≤ β + 1` matches our
      -- exponents after substitution.
      exact h_paper
    exact ENNReal.ofReal_le_ofReal hle_real
  let hμMinusOne_memLp_derived :
      ∀ (μ υ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ),
        Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
          (fun x => μ x - 1) :=
    fun μ _υ _Dυ =>
      Hamiltonian.μMinusOne_memLp_of_betaBar (d := d)
        (p := ENNReal.ofReal βBarReal) (q := ENNReal.ofReal γBarReal')
        μ (regBundle μ _υ _Dυ).hμ_memLp hγ'_le_β ENNReal.ofReal_ne_top
  -- **`infra-P5-T10-drop-pairingResidueOf`** (Formalizer iter):
  -- in-place AE strong measurability discharge of the HJB-multiplier
  -- `g(x) := -υ(x) - H(x, Dυ, μ) + V(x)` and the per-coordinate flux
  -- `flux_i(x) := μ(x) · D_pH(x, Dυ, μ)_i`, replacing the dropped
  -- residue fields `residue.hg_meas` / `residue.hF_meas`. Uses
  -- `hpow.measurable_H` / `hpow.measurable_DpH` (inherited via
  -- `RegularityH`), the per-test-triple `MemLpPer` data from
  -- `regBundle`, and the threaded `hV : MemLpPer βBar' V`.
  let hV_aesm :
      MeasureTheory.AEStronglyMeasurable V
        (MeasureTheory.Measure.restrict MeasureTheory.volume
          (Periodic.UnitCube d)) :=
    hV.aestronglyMeasurable
  let hxpm_aem :
      ∀ (μ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ),
        AEMeasurable
          (fun x : (Fin d → ℝ) =>
            (x, (fun i : Fin d => Dυ i x), μ x))
          (MeasureTheory.Measure.restrict MeasureTheory.volume
            (Periodic.UnitCube d)) :=
    fun μ Dυ =>
      let hμ_aem :=
        (regBundle μ (fun _ => 0) Dυ).hμ_memLp.aestronglyMeasurable.aemeasurable
      let hDυ_aem : ∀ i, AEMeasurable (Dυ i)
                          (MeasureTheory.Measure.restrict MeasureTheory.volume
                            (Periodic.UnitCube d)) :=
        fun i => (regBundle μ (fun _ => 0) Dυ).hDυ_memLp i
                  |>.aestronglyMeasurable.aemeasurable
      let hDυ_pi_aem : AEMeasurable
          (fun x : (Fin d → ℝ) => fun i : Fin d => Dυ i x)
          (MeasureTheory.Measure.restrict MeasureTheory.volume
            (Periodic.UnitCube d)) :=
        aemeasurable_pi_iff.mpr hDυ_aem
      measurable_id.aemeasurable.prodMk (hDυ_pi_aem.prodMk hμ_aem)
  let hH_aesm :
      ∀ (μ υ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ),
        MeasureTheory.AEStronglyMeasurable
          (fun x => H x (fun i => Dυ i x) (μ x))
          (MeasureTheory.Measure.restrict MeasureTheory.volume
            (Periodic.UnitCube d)) :=
    fun μ _υ Dυ =>
      (hpow.measurable_H.comp_aemeasurable
        (hxpm_aem μ Dυ)).aestronglyMeasurable
  let hg_meas_derived :
      ∀ (μ υ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ),
        MeasureTheory.AEStronglyMeasurable
          (fun x => -(υ x) - H x (fun i => Dυ i x) (μ x) + V x)
          (MeasureTheory.Measure.restrict MeasureTheory.volume
            (Periodic.UnitCube d)) :=
    fun μ υ Dυ =>
      let hυ_aesm := (regBundle μ υ Dυ).hυ_memLp.aestronglyMeasurable
      ((hυ_aesm.neg.sub (hH_aesm μ υ Dυ)).add hV_aesm)
  let hDpH_coord_aem :
      ∀ (μ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ) (i : Fin d),
        AEMeasurable
          (fun x => DpH x (fun j => Dυ j x) (μ x) i)
          (MeasureTheory.Measure.restrict MeasureTheory.volume
            (Periodic.UnitCube d)) :=
    fun μ Dυ i =>
      let hDpH_full : AEMeasurable
          (fun x : (Fin d → ℝ) => DpH x (fun j => Dυ j x) (μ x))
          (MeasureTheory.Measure.restrict MeasureTheory.volume
            (Periodic.UnitCube d)) :=
        hpow.measurable_DpH.comp_aemeasurable (hxpm_aem μ Dυ)
      hDpH_full.eval i
  let hF_meas_derived :
      ∀ (μ υ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ) (i : Fin d),
        MeasureTheory.AEStronglyMeasurable
          (fun x => μ x * DpH x (fun j => Dυ j x) (μ x) i)
          (MeasureTheory.Measure.restrict MeasureTheory.volume
            (Periodic.UnitCube d)) :=
    fun μ _υ Dυ i =>
      let hμ_aem :=
        (regBundle μ _υ Dυ).hμ_memLp.aestronglyMeasurable.aemeasurable
      (hμ_aem.mul (hDpH_coord_aem μ Dυ i)).aestronglyMeasurable
  -- **Phase 6e**: derive `hpqβ`/`hpqγ` from `_hExp` via the new
  -- `holder_beta_of_exp` / `holder_gamma_of_exp` helpers, instead of
  -- consuming `residue.hpqβ` / `residue.hpqγ`. Positivity of the
  -- real-valued exponents follows from `(hpow.hα, hpow.hβ)` and the
  -- paper-form equalities `(hβBarEq, hβBar'Eq, hγBarEq, hγBar'Eq)`.
  have h_β_pos : (0 : ℝ) < βBarReal := by
    rw [hβBarEq]; linarith [hpow.hβ]
  have h_β'_pos : (0 : ℝ) < βBarReal' := by
    rw [hβBar'Eq]
    have hβ1 : (0 : ℝ) < hpow.β + 1 := by linarith [hpow.hβ]
    exact div_pos hβ1 hpow.hβ
  have h_γ_pos : (0 : ℝ) < γBarReal := by
    rw [hγBarEq]
    have hα0 : (0 : ℝ) < hpow.α := lt_trans zero_lt_one hpow.hα
    have hβ1 : (0 : ℝ) < hpow.β + 1 := by linarith [hpow.hβ]
    exact div_pos (mul_pos hα0 hβ1) hpow.hβ
  have h_γ'_eq : γBarReal' = γBarReal / (γBarReal - 1) := by
    rw [hγBar'Eq, hγBarEq]
  have hpqβ_derived : βBarReal.HolderConjugate βBarReal' :=
    holder_beta_of_exp _hExp h_β_pos.le h_β'_pos.le
  have hpqγ_derived : γBarReal.HolderConjugate γBarReal' :=
    holder_gamma_of_exp _hExp h_γ_pos.le h_γ'_eq
  { hpqβ := hpqβ_derived
    hpqγ := hpqγ_derived
    -- Phase H5b: derived from `wkBundle.auxAeOfClusterPoint` instead of
    -- the dropped `residue.hDuLim_memLp_γ` field.
    hDuLim_memLp_γ := wkBundle.hDuLim_memLp_γ
    hυ_memLp := fun μ υ Dυ => (regBundle μ υ Dυ).hυ_memLp
    hDυ_memLp := fun μ υ Dυ i => (regBundle μ υ Dυ).hDυ_memLp i
    hμ_memLp := fun μ υ Dυ => (regBundle μ υ Dυ).hμ_memLp
    hg_memLp := fun μ υ Dυ =>
      -- AC2 ADFGU.a — HJB-multiplier in `L^{β̄'}_per`. Migrated to
      -- the non-strict-positivity variant `g_memLp_q_nonneg` (iter
      -- `infra-P5-T10-v7-phase4-hmu-posAuth-drain`), which consumes
      -- `0 ≤ᵐ μ` (sourced from the family-scoped `residue.hμ_nonneg`)
      -- and the three Hat0 riders `(hHat0, hFin, hAgree)`; `hFin` is
      -- derived from `(hpow, hHat0)` via
      -- `Hext_finite_at_zero_of_powerGrowth`.
      Hamiltonian.g_memLp_q_nonneg (h := hpow) hHat0
        (Hamiltonian.Hext_finite_at_zero_of_powerGrowth hpow hHat0) hAgree
        V υ μ Dυ
        (residue.hμ_nonneg (μ := μ) (υ := υ) (Dυ := Dυ) (Set.mem_univ _))
        (hg_meas_derived μ υ Dυ)
        (hG_HJB_mem μ υ Dυ)
    hflux_memLp := fun μ υ Dυ i =>
      -- AC2 ADFGU.b — flux per coord in `L^{γ̄'}_per`. Migrated to
      -- the non-strict-positivity variant `flux_memLp_gammaBar'_nonneg`
      -- (iter `infra-P5-T10-v7-phase4-hmu-posAuth-drain`), which
      -- consumes `0 ≤ᵐ μ` and handles the boundary `μ x = 0` by
      -- pointwise-zero of the flux integrand.
      Hamiltonian.flux_memLp_gammaBar'_nonneg (h := hpow)
        μ Dυ i
        (residue.hμ_nonneg (μ := μ) (υ := υ) (Dυ := Dυ) (Set.mem_univ _))
        (hF_meas_derived μ υ Dυ i)
        (hG_flux_mem μ υ Dυ)
    hμMinusOne_memLp := hμMinusOne_memLp_derived
    h_weak_m := h_weak_m_universal
    h_weak_u := h_weak_u_universal
    h_weak_Du := h_weak_Du_universal
    hVI_eps_set := fun k => (seq.sol k).hVIeps_set
    hVI_eps_signed := fun k => (seq.sol k).hVIeps_signed
    hVI_eps_transport := fun k => (seq.sol k).hVIeps_transport
    M := gateauxAux.M
    hreg_bdd := gateauxAux.hreg_bdd
    hpair_conv := by
      -- AC5 — assembled `mfgOperatorPair` convergence built from a
      -- `LimitPassageInputData_noVI` per test triple. Phase 5b: the
      -- universal `hVI_eps` field is no longer needed (the assembled
      -- pairing convergence uses `tendsto_mfgOperatorPair_assembled_noVI`,
      -- whose proof body does not read `hVI_eps`).
      intro μ υ Dυ
      let T : LimitPassageInputData_noVI (d := d) V H DpH
                βBarReal βBarReal' γBarReal γBarReal' μ υ Dυ :=
        { hpqβ := hpqβ_derived
          hpqγ := hpqγ_derived
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
          hυ_memLp := (regBundle μ υ Dυ).hυ_memLp
          hDu_n_memLp := fun k i => (seq.sol k).hDuLp i
          -- Phase H5b: derived from `wkBundle.auxAeOfClusterPoint`
          -- instead of the dropped `residue.hDuLim_memLp_γ` field.
          hDu_memLp := wkBundle.hDuLim_memLp_γ
          hDυ_memLp := fun i => (regBundle μ υ Dυ).hDυ_memLp i
          hμ_memLp := (regBundle μ υ Dυ).hμ_memLp
          hg_memLp := Hamiltonian.g_memLp_q_nonneg (h := hpow) hHat0
                        (Hamiltonian.Hext_finite_at_zero_of_powerGrowth
                          hpow hHat0) hAgree
                        V υ μ Dυ
                        (residue.hμ_nonneg (μ := μ) (υ := υ) (Dυ := Dυ)
                          (Set.mem_univ _))
                        (hg_meas_derived μ υ Dυ)
                        (hG_HJB_mem μ υ Dυ)
          hflux_memLp := fun i =>
            Hamiltonian.flux_memLp_gammaBar'_nonneg (h := hpow)
              μ Dυ i
              (residue.hμ_nonneg (μ := μ) (υ := υ) (Dυ := Dυ)
                (Set.mem_univ _))
              (hF_meas_derived μ υ Dυ i)
              (hG_flux_mem μ υ Dυ)
          hμMinusOne_memLp := hμMinusOne_memLp_derived μ υ Dυ
          h_weak_m := h_weak_m_universal
          h_weak_u := h_weak_u_universal
          h_weak_Du := h_weak_Du_universal
          M := gateauxAux.M μ υ Dυ
          hreg_bdd := gateauxAux.hreg_bdd μ υ Dυ }
      exact T.tendsto_mfgOperatorPair_assembled_noVI }

/-- **AC6 sanity check.** Composing
`limitPairingSelector_of_paperHypotheses` with
`limitPairingInputs_of_regularizedSequence` lets the consumer
construct `LimitPairingInputs` directly from
`(hmon, hpow, hV, hExp, seq, wkBundle, regBundle, gateauxAux,
residue)` — the `LimitPairingSelector` parameter has been
**eliminated** in favour of the genuine paper-residue bundle. -/
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
    (hHat0 : StationaryMFG.Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : StationaryMFG.Hamiltonian.H_zero_eq_Hext (d := d) H)
    (seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH)
    (wkBundle : WeakLimitInputBundleAE (d := d) γBarReal βBarReal)
    (regBundle : ∀ (μ υ : (Fin d → ℝ) → ℝ)
                    (Dυ : Fin d → (Fin d → ℝ) → ℝ),
                   PerTestTripleRegularity (d := d)
                     (ENNReal.ofReal βBarReal)
                     (ENNReal.ofReal γBarReal) μ υ Dυ)
    (gateauxAux : LimitPairingSelectorGateauxAux (d := d) seq)
    (hβBarEq : βBarReal = hpow.β + 1)
    (hγBarEq : γBarReal = hpow.α * (hpow.β + 1) / hpow.β)
    (hβBar'Eq : βBarReal' = (hpow.β + 1) / hpow.β)
    (hγBar'Eq : γBarReal' = hpow.α * (hpow.β + 1) / hpow.β /
                              (hpow.α * (hpow.β + 1) / hpow.β - 1))
    -- `infra-P5-T10-D5-hmu-pos-shape-audit` (Outcome A): residue at
    -- `Set.univ` to recover the universal API for this sanity-check.
    (residue : LimitPairingSelectorPaperResidue (d := d)
                  (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  (V := V) (H := H) (DpH := DpH) hpow seq wkBundle
                  Set.univ)
    -- Phase 5b: the legacy `hVI_eps_universal` parameter has been
    -- dropped from both producers (see
    -- `infra-P5-theorem1-phase-5b-rebuild-pairing-on-noVI`).
    -- Phase H2 strip: the three universal weak-pairing certificates
    -- are now separate authorised residues
    -- (see `infra-P5-theorem1-phase-H2-discharge-weak-pairing-residues`).
    -- `infra-P5-theorem1-remove-pairingResidue-hpq-dependency` (Formalizer
    -- iter 0493): typed via `hpq{Beta,Gamma}_paperResidue` instead of
    -- `residue.hpq{β,γ}` (those fields no longer exist).
    (h_weak_m_universal : WeakConvPairing_universal (d := d)
                            (hpqBeta_paperResidue (d := d) hpow hExp
                              hβBarEq hβBar'Eq)
                            (fun k => (seq.sol k).m) wkBundle.mLim)
    (h_weak_u_universal : WeakConvPairing_universal (d := d)
                            (hpqGamma_paperResidue (d := d) hpow hExp
                              hγBarEq hγBar'Eq)
                            (fun k => (seq.sol k).u) wkBundle.uLim)
    (h_weak_Du_universal : ∀ i,
        WeakConvPairing_universal (d := d)
          (hpqGamma_paperResidue (d := d) hpow hExp hγBarEq hγBar'Eq)
          (fun k => (seq.sol k).Du i) (wkBundle.DuLim i)) :
    LimitPairingInputs (d := d)
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      (V := V) (H := H) (DpH := DpH)
      seq wkBundle.mLim wkBundle.uLim wkBundle.DuLim :=
  limitPairingInputs_of_regularizedSequence
    hmon hpow hV hExp seq wkBundle
    (limitPairingSelector_of_paperHypotheses
       hmon hpow hV hExp hHat0 hAgree seq wkBundle regBundle gateauxAux
       hβBarEq hγBarEq hβBar'Eq hγBar'Eq residue
       h_weak_m_universal h_weak_u_universal h_weak_Du_universal)

/-! ### Phase 6d-ii — per-family direct producers for
`LimitPairingSelectorFamily`

Per `infra-P5-theorem1-phase-6d-ii-build-pairingFamily-direct`, we
land three per-family producers
`limitPairingSelectorFamily_{set,signed,transport}_of_paperHypotheses`
that build a `LimitPairingSelectorFamily` directly *without* going
through the universal `limitPairingSelector_of_paperHypotheses`
chain. Each producer takes a **per-family**
`PerTestTripleRegularity` supplier (gated on
`(μ, υ, Dυ) ∈ D_<family>`) plus the standard `(hmon, hpow, hV,
hExp, seq, wkBundle, gateauxAux, residue, h_weak_*)` inputs, and
produces the family-restricted selector at the matching family
domain.

Implementation strategy: a single generic `limitPairingSelectorFamily_of_paperHypotheses_at`
producer at *any* `D : Set (MFGTriple d)` does the structural
plumbing once (a literal family-restricted port of
`limitPairingSelector_of_paperHypotheses`). The three named
specialisations apply it at `D_set_family`,
`D_signed_family_nn`, and `D_transport_family` respectively.

These producers do **not** reference `T10PaperResidues.regBundle`:
they consume only the per-family supplier passed in. The follow-up
phase 6d-ii-c will refine the bridge so the per-family supplier is
itself derived from `wkBundle.perTestTripleBase` plus the per-family
`PerTestTripleRegularity._perturbation` constructors (under a
narrowed strongVI family domain), at which point
`T10PaperResidues.regBundle` can be dropped entirely (phase
6d-ii-d). -/

/-- **Phase 6d-ii — generic family-restricted AC6 producer.**

Family-restricted port of `limitPairingSelector_of_paperHypotheses`
at any domain `D : Set (MFGTriple d)`. The per-family
`regSupplier_D` provides per-test-triple regularity on `D`; the
remaining inputs are unchanged.

The body is structurally identical to
`limitPairingSelector_of_paperHypotheses`; every occurrence of
`regBundle μ υ Dυ` in the universal version is replaced by
`regSupplier_D hMem` where `hMem : (μ, υ, Dυ) ∈ D`. Per-test-triple
fields of the residue (`hμ_pos`, `hg_meas`, `hF_meas`) are still
taken at the universal `(μ, υ, Dυ)` shape, so the universal
`residue` is reused unchanged. -/
noncomputable def limitPairingSelectorFamily_of_paperHypotheses_at
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (_hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (_hExp : SimplePowerExponentFacts γBarReal
                (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
                (ENNReal.ofReal βBarReal'))
    -- iter `infra-P5-T10-v7-phase4-hmu-posAuth-drain`: paper-`(a:Hat0)`
    -- riders threaded through for the HJB-side `g_memLp_q_nonneg`
    -- discharge. `hFin` is derived in-body via
    -- `Hext_finite_at_zero_of_powerGrowth`.
    (hHat0 : StationaryMFG.Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : StationaryMFG.Hamiltonian.H_zero_eq_Hext (d := d) H)
    (seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH)
    (wkBundle : WeakLimitInputBundleAE (d := d) γBarReal βBarReal)
    (D : Set (StationaryMFG.Theorems.SimplePower.MFGTriple d))
    (regSupplier_D :
      ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄
        ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
        (μ, υ, Dυ) ∈ D →
          PerTestTripleRegularity (d := d)
            (ENNReal.ofReal βBarReal)
            (ENNReal.ofReal γBarReal) μ υ Dυ)
    (gateauxAux : LimitPairingSelectorGateauxAuxFamily (d := d) seq D)
    (hβBarEq : βBarReal = hpow.β + 1)
    (hγBarEq : γBarReal = hpow.α * (hpow.β + 1) / hpow.β)
    (hβBar'Eq : βBarReal' = (hpow.β + 1) / hpow.β)
    (hγBar'Eq : γBarReal' = hpow.α * (hpow.β + 1) / hpow.β /
                              (hpow.α * (hpow.β + 1) / hpow.β - 1))
    -- `infra-P5-T10-D5-hmu-pos-shape-audit` (Outcome A): residue
    -- typed at the consumer's family domain `D`. The strict-positivity
    -- field `hμ_pos` consumes the family-membership hypothesis `hMem`
    -- already in scope at every call site.
    (residue : LimitPairingSelectorPaperResidue (d := d)
                  (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  (V := V) (H := H) (DpH := DpH) hpow seq wkBundle D)
    -- `infra-P5-theorem1-remove-pairingResidue-hpq-dependency` (Formalizer
    -- iter 0493): typed via `hpq{Beta,Gamma}_paperResidue` instead of
    -- `residue.hpq{β,γ}` (those fields no longer exist).
    (h_weak_m_universal : WeakConvPairing_universal (d := d)
                            (hpqBeta_paperResidue (d := d) hpow _hExp
                              hβBarEq hβBar'Eq)
                            (fun k => (seq.sol k).m) wkBundle.mLim)
    (h_weak_u_universal : WeakConvPairing_universal (d := d)
                            (hpqGamma_paperResidue (d := d) hpow _hExp
                              hγBarEq hγBar'Eq)
                            (fun k => (seq.sol k).u) wkBundle.uLim)
    (h_weak_Du_universal : ∀ i,
        WeakConvPairing_universal (d := d)
          (hpqGamma_paperResidue (d := d) hpow _hExp hγBarEq hγBar'Eq)
          (fun k => (seq.sol k).Du i) (wkBundle.DuLim i)) :
    LimitPairingSelectorFamily (d := d)
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      (V := V) (H := H) (DpH := DpH)
      seq wkBundle.mLim wkBundle.uLim wkBundle.DuLim D :=
  -- Cast the abstract exponents to paper formulas, mirroring the
  -- universal AC6 producer (`limitPairingSelector_of_paperHypotheses`).
  let hβ_cast : ENNReal.ofReal βBarReal = ENNReal.ofReal (hpow.β + 1) :=
    by rw [hβBarEq]
  let hγ_cast : ENNReal.ofReal γBarReal
                  = ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β) :=
    by rw [hγBarEq]
  let hβ'_cast : ENNReal.ofReal βBarReal'
                  = ENNReal.ofReal ((hpow.β + 1) / hpow.β) :=
    by rw [hβBar'Eq]
  let hγ'_cast : ENNReal.ofReal γBarReal'
                  = ENNReal.ofReal
                      (hpow.α * (hpow.β + 1) / hpow.β /
                       (hpow.α * (hpow.β + 1) / hpow.β - 1)) :=
    by rw [hγBar'Eq]
  let hμ_paper : ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄
                   ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
                   (μ, υ, Dυ) ∈ D →
      Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1)) μ :=
    fun _ _ _ hMem => hβ_cast ▸ (regSupplier_D hMem).hμ_memLp
  let hυ_paper : ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄
                   ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
                   (μ, υ, Dυ) ∈ D →
      Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) υ :=
    fun _ _ _ hMem => hγ_cast ▸ (regSupplier_D hMem).hυ_memLp
  let hDυ_paper : ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄
                    ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
                    (μ, υ, Dυ) ∈ D → ∀ (i : Fin d),
      Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) (Dυ i) :=
    fun _ _ _ hMem i => hγ_cast ▸ (regSupplier_D hMem).hDυ_memLp i
  let hV_paper : Periodic.MemLpPer (d := d)
                    (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) V :=
    hβ'_cast ▸ hV
  let hG_HJB_mem :
      ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄
        ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
        (μ, υ, Dυ) ∈ D →
        Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal')
          (fun x : (Fin d → ℝ) =>
            hpow.C * (‖fun i => Dυ i x‖ ^ hpow.α + 1)
              + hpow.C * (μ x ^ hpow.β + 1)
              + |υ x| + |V x|) :=
    fun μ υ Dυ hMem =>
      hβ'_cast ▸
        (Hamiltonian.g_dominator_memLp_betaBar' (h := hpow)
          V υ μ Dυ (hμ_paper hMem) (hυ_paper hMem)
          (hDυ_paper hMem) hV_paper hpow.hC)
  let hG_flux_mem :
      ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄
        ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
        (μ, υ, Dυ) ∈ D →
        Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
          (fun x : (Fin d → ℝ) =>
            hpow.C * (μ x * ‖fun j => Dυ j x‖ ^ (hpow.α - 1)
                       + μ x ^ (1 + hpow.β - hpow.β / hpow.α)
                       + μ x)) :=
    fun μ υ Dυ hMem =>
      hγ'_cast ▸
        (Hamiltonian.flux_dominator_memLp_gammaBar' (h := hpow)
          μ Dυ (hμ_paper hMem) (hDυ_paper hMem))
  have hγ'_le_β :
      ENNReal.ofReal γBarReal' ≤ ENNReal.ofReal βBarReal := by
    have hle_real : γBarReal' ≤ βBarReal := by
      rw [hγBar'Eq, hβBarEq]
      exact Hamiltonian.gammaBar'_le_betaBar hpow.hα hpow.hβ
    exact ENNReal.ofReal_le_ofReal hle_real
  let hμMinusOne_memLp_derived :
      ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄
        ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
        (μ, υ, Dυ) ∈ D →
        Periodic.MemLpPer (d := d) (ENNReal.ofReal γBarReal')
          (fun x => μ x - 1) :=
    fun _ _ _ hMem =>
      Hamiltonian.μMinusOne_memLp_of_betaBar (d := d)
        (p := ENNReal.ofReal βBarReal) (q := ENNReal.ofReal γBarReal')
        _ (regSupplier_D hMem).hμ_memLp hγ'_le_β ENNReal.ofReal_ne_top
  -- **`infra-P5-T10-drop-pairingResidueOf`** (Formalizer iter):
  -- in-place AE strong measurability discharge of the HJB-multiplier
  -- `g` and the per-coordinate flux `flux_i`, replacing the dropped
  -- residue fields `residue.hg_meas` / `residue.hF_meas`. Uses
  -- `hpow.measurable_H` / `hpow.measurable_DpH` (inherited via
  -- `RegularityH`), the per-test-triple `MemLpPer` data from
  -- `regSupplier_D`, and the threaded `hV : MemLpPer βBar' V`.
  let hV_aesm :
      MeasureTheory.AEStronglyMeasurable V
        (MeasureTheory.Measure.restrict MeasureTheory.volume
          (Periodic.UnitCube d)) :=
    hV.aestronglyMeasurable
  let hxpm_aem :
      ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄
        ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
        (μ, υ, Dυ) ∈ D →
        AEMeasurable
          (fun x : (Fin d → ℝ) =>
            (x, (fun i : Fin d => Dυ i x), μ x))
          (MeasureTheory.Measure.restrict MeasureTheory.volume
            (Periodic.UnitCube d)) :=
    fun μ _ Dυ hMem =>
      let hμ_aem :=
        (regSupplier_D hMem).hμ_memLp.aestronglyMeasurable.aemeasurable
      let hDυ_aem : ∀ i, AEMeasurable (Dυ i)
                          (MeasureTheory.Measure.restrict MeasureTheory.volume
                            (Periodic.UnitCube d)) :=
        fun i => (regSupplier_D hMem).hDυ_memLp i
                  |>.aestronglyMeasurable.aemeasurable
      let hDυ_pi_aem : AEMeasurable
          (fun x : (Fin d → ℝ) => fun i : Fin d => Dυ i x)
          (MeasureTheory.Measure.restrict MeasureTheory.volume
            (Periodic.UnitCube d)) :=
        aemeasurable_pi_iff.mpr hDυ_aem
      measurable_id.aemeasurable.prodMk (hDυ_pi_aem.prodMk hμ_aem)
  let hg_meas_derived :
      ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄
        ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
        (μ, υ, Dυ) ∈ D →
        MeasureTheory.AEStronglyMeasurable
          (fun x => -(υ x) - H x (fun i => Dυ i x) (μ x) + V x)
          (MeasureTheory.Measure.restrict MeasureTheory.volume
            (Periodic.UnitCube d)) :=
    fun _ _ _ hMem =>
      let hυ_aesm := (regSupplier_D hMem).hυ_memLp.aestronglyMeasurable
      let hH_aesm : MeasureTheory.AEStronglyMeasurable _
          (MeasureTheory.Measure.restrict MeasureTheory.volume
            (Periodic.UnitCube d)) :=
        (hpow.measurable_H.comp_aemeasurable
          (hxpm_aem hMem)).aestronglyMeasurable
      ((hυ_aesm.neg.sub hH_aesm).add hV_aesm)
  let hF_meas_derived :
      ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄
        ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
        (μ, υ, Dυ) ∈ D → ∀ (i : Fin d),
        MeasureTheory.AEStronglyMeasurable
          (fun x => μ x * DpH x (fun j => Dυ j x) (μ x) i)
          (MeasureTheory.Measure.restrict MeasureTheory.volume
            (Periodic.UnitCube d)) :=
    fun _ _ _ hMem i =>
      let hμ_aem :=
        (regSupplier_D hMem).hμ_memLp.aestronglyMeasurable.aemeasurable
      let hDpH_full : AEMeasurable _
          (MeasureTheory.Measure.restrict MeasureTheory.volume
            (Periodic.UnitCube d)) :=
        hpow.measurable_DpH.comp_aemeasurable (hxpm_aem hMem)
      (hμ_aem.mul (hDpH_full.eval i)).aestronglyMeasurable
  -- **Phase 6e**: derive `hpqβ`/`hpqγ` from `_hExp` via the new
  -- `holder_beta_of_exp` / `holder_gamma_of_exp` helpers, instead of
  -- consuming `residue.hpqβ` / `residue.hpqγ`. (Mirrors the universal
  -- producer above.)
  have h_β_pos : (0 : ℝ) < βBarReal := by
    rw [hβBarEq]; linarith [hpow.hβ]
  have h_β'_pos : (0 : ℝ) < βBarReal' := by
    rw [hβBar'Eq]
    have hβ1 : (0 : ℝ) < hpow.β + 1 := by linarith [hpow.hβ]
    exact div_pos hβ1 hpow.hβ
  have h_γ_pos : (0 : ℝ) < γBarReal := by
    rw [hγBarEq]
    have hα0 : (0 : ℝ) < hpow.α := lt_trans zero_lt_one hpow.hα
    have hβ1 : (0 : ℝ) < hpow.β + 1 := by linarith [hpow.hβ]
    exact div_pos (mul_pos hα0 hβ1) hpow.hβ
  have h_γ'_eq : γBarReal' = γBarReal / (γBarReal - 1) := by
    rw [hγBar'Eq, hγBarEq]
  have hpqβ_derived : βBarReal.HolderConjugate βBarReal' :=
    holder_beta_of_exp _hExp h_β_pos.le h_β'_pos.le
  have hpqγ_derived : γBarReal.HolderConjugate γBarReal' :=
    holder_gamma_of_exp _hExp h_γ_pos.le h_γ'_eq
  { hpqβ := hpqβ_derived
    hpqγ := hpqγ_derived
    hDuLim_memLp_γ := wkBundle.hDuLim_memLp_γ
    hυ_memLp := fun _ _ _ hMem => (regSupplier_D hMem).hυ_memLp
    hDυ_memLp := fun _ _ _ hMem i => (regSupplier_D hMem).hDυ_memLp i
    hμ_memLp := fun _ _ _ hMem => (regSupplier_D hMem).hμ_memLp
    hg_memLp := fun μ υ Dυ hMem =>
      -- iter `infra-P5-T10-v7-phase4-hmu-posAuth-drain`: migrated to
      -- `g_memLp_q_nonneg` (consumes `0 ≤ᵐ μ` and Hat0 riders).
      Hamiltonian.g_memLp_q_nonneg (h := hpow) hHat0
        (Hamiltonian.Hext_finite_at_zero_of_powerGrowth hpow hHat0) hAgree
        V υ μ Dυ (residue.hμ_nonneg hMem)
        (hg_meas_derived hMem)
        (hG_HJB_mem hMem)
    hflux_memLp := fun μ υ Dυ hMem i =>
      -- iter `infra-P5-T10-v7-phase4-hmu-posAuth-drain`: migrated to
      -- `flux_memLp_gammaBar'_nonneg` (consumes `0 ≤ᵐ μ`).
      Hamiltonian.flux_memLp_gammaBar'_nonneg (h := hpow)
        μ Dυ i (residue.hμ_nonneg hMem)
        (hF_meas_derived hMem i)
        (hG_flux_mem hMem)
    hμMinusOne_memLp := fun _ _ _ hMem => hμMinusOne_memLp_derived hMem
    h_weak_m := h_weak_m_universal
    h_weak_u := h_weak_u_universal
    h_weak_Du := h_weak_Du_universal
    hVI_eps_set := fun k => (seq.sol k).hVIeps_set
    hVI_eps_signed := fun k => (seq.sol k).hVIeps_signed
    hVI_eps_transport := fun k => (seq.sol k).hVIeps_transport
    M := gateauxAux.M
    hreg_bdd := fun _μ _υ _Dυ hMem k => gateauxAux.hreg_bdd hMem k
    hpair_conv := by
      intro μ υ Dυ hMem
      let T : LimitPassageInputData_noVI (d := d) V H DpH
                βBarReal βBarReal' γBarReal γBarReal' μ υ Dυ :=
        { hpqβ := hpqβ_derived
          hpqγ := hpqγ_derived
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
          hυ_memLp := (regSupplier_D hMem).hυ_memLp
          hDu_n_memLp := fun k i => (seq.sol k).hDuLp i
          hDu_memLp := wkBundle.hDuLim_memLp_γ
          hDυ_memLp := fun i => (regSupplier_D hMem).hDυ_memLp i
          hμ_memLp := (regSupplier_D hMem).hμ_memLp
          hg_memLp := Hamiltonian.g_memLp_q_nonneg (h := hpow) hHat0
                        (Hamiltonian.Hext_finite_at_zero_of_powerGrowth
                          hpow hHat0) hAgree
                        V υ μ Dυ (residue.hμ_nonneg hMem)
                        (hg_meas_derived hMem)
                        (hG_HJB_mem hMem)
          hflux_memLp := fun i =>
            Hamiltonian.flux_memLp_gammaBar'_nonneg (h := hpow)
              μ Dυ i (residue.hμ_nonneg hMem)
              (hF_meas_derived hMem i)
              (hG_flux_mem hMem)
          hμMinusOne_memLp := hμMinusOne_memLp_derived hMem
          h_weak_m := h_weak_m_universal
          h_weak_u := h_weak_u_universal
          h_weak_Du := h_weak_Du_universal
          M := gateauxAux.M μ υ Dυ
          hreg_bdd := gateauxAux.hreg_bdd hMem }
      exact T.tendsto_mfgOperatorPair_assembled_noVI }

/-- **Phase 6d-ii — set-family direct producer.** Specialisation of
`limitPairingSelectorFamily_of_paperHypotheses_at` at
`D_set_family wkBundle.{mLim, uLim, DuLim}`. -/
noncomputable def limitPairingSelectorFamily_set_of_paperHypotheses
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
    (hHat0 : StationaryMFG.Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : StationaryMFG.Hamiltonian.H_zero_eq_Hext (d := d) H)
    (seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH)
    (wkBundle : WeakLimitInputBundleAE (d := d) γBarReal βBarReal)
    (regSupplier_set :
      ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄
        ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
        (μ, υ, Dυ) ∈ D_set_family (d := d)
                        wkBundle.mLim wkBundle.uLim wkBundle.DuLim →
          PerTestTripleRegularity (d := d)
            (ENNReal.ofReal βBarReal)
            (ENNReal.ofReal γBarReal) μ υ Dυ)
    (gateauxAux : LimitPairingSelectorGateauxAuxFamily (d := d) seq
                    (D_set_family (d := d)
                      wkBundle.mLim wkBundle.uLim wkBundle.DuLim))
    (hβBarEq : βBarReal = hpow.β + 1)
    (hγBarEq : γBarReal = hpow.α * (hpow.β + 1) / hpow.β)
    (hβBar'Eq : βBarReal' = (hpow.β + 1) / hpow.β)
    (hγBar'Eq : γBarReal' = hpow.α * (hpow.β + 1) / hpow.β /
                              (hpow.α * (hpow.β + 1) / hpow.β - 1))
    -- `infra-P5-T10-D5-hmu-pos-shape-audit` (Outcome A): residue
    -- typed at `D_set_family wkBundle.{mLim,uLim,DuLim}`.
    (residue : LimitPairingSelectorPaperResidue (d := d)
                  (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  (V := V) (H := H) (DpH := DpH) hpow seq wkBundle
                  (D_set_family (d := d)
                    wkBundle.mLim wkBundle.uLim wkBundle.DuLim))
    -- `infra-P5-theorem1-remove-pairingResidue-hpq-dependency` (Formalizer
    -- iter 0493): typed via `hpq{Beta,Gamma}_paperResidue` instead of
    -- `residue.hpq{β,γ}` (those fields no longer exist).
    (h_weak_m_universal : WeakConvPairing_universal (d := d)
                            (hpqBeta_paperResidue (d := d) hpow hExp
                              hβBarEq hβBar'Eq)
                            (fun k => (seq.sol k).m) wkBundle.mLim)
    (h_weak_u_universal : WeakConvPairing_universal (d := d)
                            (hpqGamma_paperResidue (d := d) hpow hExp
                              hγBarEq hγBar'Eq)
                            (fun k => (seq.sol k).u) wkBundle.uLim)
    (h_weak_Du_universal : ∀ i,
        WeakConvPairing_universal (d := d)
          (hpqGamma_paperResidue (d := d) hpow hExp hγBarEq hγBar'Eq)
          (fun k => (seq.sol k).Du i) (wkBundle.DuLim i)) :
    LimitPairingSelectorFamily (d := d)
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      (V := V) (H := H) (DpH := DpH)
      seq wkBundle.mLim wkBundle.uLim wkBundle.DuLim
      (D_set_family (d := d)
        wkBundle.mLim wkBundle.uLim wkBundle.DuLim) :=
  limitPairingSelectorFamily_of_paperHypotheses_at
    hmon hpow hV hExp hHat0 hAgree seq wkBundle
    (D_set_family (d := d)
      wkBundle.mLim wkBundle.uLim wkBundle.DuLim)
    regSupplier_set gateauxAux
    hβBarEq hγBarEq hβBar'Eq hγBar'Eq residue
    h_weak_m_universal h_weak_u_universal h_weak_Du_universal

/-- **Phase 6d-ii — signed-family direct producer.** Specialisation
of `limitPairingSelectorFamily_of_paperHypotheses_at` at
`D_signed_family_nn wkBundle.{mLim, uLim, DuLim}`. -/
noncomputable def limitPairingSelectorFamily_signed_of_paperHypotheses
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
    (hHat0 : StationaryMFG.Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : StationaryMFG.Hamiltonian.H_zero_eq_Hext (d := d) H)
    (seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH)
    (wkBundle : WeakLimitInputBundleAE (d := d) γBarReal βBarReal)
    (regSupplier_signed :
      ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄
        ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
        (μ, υ, Dυ) ∈ D_signed_family_nn (d := d)
                        wkBundle.mLim wkBundle.uLim wkBundle.DuLim →
          PerTestTripleRegularity (d := d)
            (ENNReal.ofReal βBarReal)
            (ENNReal.ofReal γBarReal) μ υ Dυ)
    (gateauxAux : LimitPairingSelectorGateauxAuxFamily (d := d) seq
                    (D_signed_family_nn (d := d)
                      wkBundle.mLim wkBundle.uLim wkBundle.DuLim))
    (hβBarEq : βBarReal = hpow.β + 1)
    (hγBarEq : γBarReal = hpow.α * (hpow.β + 1) / hpow.β)
    (hβBar'Eq : βBarReal' = (hpow.β + 1) / hpow.β)
    (hγBar'Eq : γBarReal' = hpow.α * (hpow.β + 1) / hpow.β /
                              (hpow.α * (hpow.β + 1) / hpow.β - 1))
    -- `infra-P5-T10-D5-hmu-pos-shape-audit` (Outcome A): residue
    -- typed at `D_signed_family_nn wkBundle.{mLim,uLim,DuLim}`.
    (residue : LimitPairingSelectorPaperResidue (d := d)
                  (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  (V := V) (H := H) (DpH := DpH) hpow seq wkBundle
                  (D_signed_family_nn (d := d)
                    wkBundle.mLim wkBundle.uLim wkBundle.DuLim))
    -- `infra-P5-theorem1-remove-pairingResidue-hpq-dependency` (Formalizer
    -- iter 0493): typed via `hpq{Beta,Gamma}_paperResidue` instead of
    -- `residue.hpq{β,γ}` (those fields no longer exist).
    (h_weak_m_universal : WeakConvPairing_universal (d := d)
                            (hpqBeta_paperResidue (d := d) hpow hExp
                              hβBarEq hβBar'Eq)
                            (fun k => (seq.sol k).m) wkBundle.mLim)
    (h_weak_u_universal : WeakConvPairing_universal (d := d)
                            (hpqGamma_paperResidue (d := d) hpow hExp
                              hγBarEq hγBar'Eq)
                            (fun k => (seq.sol k).u) wkBundle.uLim)
    (h_weak_Du_universal : ∀ i,
        WeakConvPairing_universal (d := d)
          (hpqGamma_paperResidue (d := d) hpow hExp hγBarEq hγBar'Eq)
          (fun k => (seq.sol k).Du i) (wkBundle.DuLim i)) :
    LimitPairingSelectorFamily (d := d)
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      (V := V) (H := H) (DpH := DpH)
      seq wkBundle.mLim wkBundle.uLim wkBundle.DuLim
      (D_signed_family_nn (d := d)
        wkBundle.mLim wkBundle.uLim wkBundle.DuLim) :=
  limitPairingSelectorFamily_of_paperHypotheses_at
    hmon hpow hV hExp hHat0 hAgree seq wkBundle
    (D_signed_family_nn (d := d)
      wkBundle.mLim wkBundle.uLim wkBundle.DuLim)
    regSupplier_signed gateauxAux
    hβBarEq hγBarEq hβBar'Eq hγBar'Eq residue
    h_weak_m_universal h_weak_u_universal h_weak_Du_universal

/-- **Phase 6d-ii — transport-family direct producer.** Specialisation
of `limitPairingSelectorFamily_of_paperHypotheses_at` at
`D_transport_family wkBundle.{mLim, uLim, DuLim}`. -/
noncomputable def limitPairingSelectorFamily_transport_of_paperHypotheses
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
    (hHat0 : StationaryMFG.Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : StationaryMFG.Hamiltonian.H_zero_eq_Hext (d := d) H)
    (seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH)
    (wkBundle : WeakLimitInputBundleAE (d := d) γBarReal βBarReal)
    (regSupplier_transport :
      ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄
        ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
        (μ, υ, Dυ) ∈ D_transport_family (d := d)
                        wkBundle.mLim wkBundle.uLim wkBundle.DuLim →
          PerTestTripleRegularity (d := d)
            (ENNReal.ofReal βBarReal)
            (ENNReal.ofReal γBarReal) μ υ Dυ)
    (gateauxAux : LimitPairingSelectorGateauxAuxFamily (d := d) seq
                    (D_transport_family (d := d)
                      wkBundle.mLim wkBundle.uLim wkBundle.DuLim))
    (hβBarEq : βBarReal = hpow.β + 1)
    (hγBarEq : γBarReal = hpow.α * (hpow.β + 1) / hpow.β)
    (hβBar'Eq : βBarReal' = (hpow.β + 1) / hpow.β)
    (hγBar'Eq : γBarReal' = hpow.α * (hpow.β + 1) / hpow.β /
                              (hpow.α * (hpow.β + 1) / hpow.β - 1))
    -- `infra-P5-T10-D5-hmu-pos-shape-audit` (Outcome A): residue
    -- typed at `D_transport_family wkBundle.{mLim,uLim,DuLim}`.
    (residue : LimitPairingSelectorPaperResidue (d := d)
                  (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  (V := V) (H := H) (DpH := DpH) hpow seq wkBundle
                  (D_transport_family (d := d)
                    wkBundle.mLim wkBundle.uLim wkBundle.DuLim))
    -- `infra-P5-theorem1-remove-pairingResidue-hpq-dependency` (Formalizer
    -- iter 0493): typed via `hpq{Beta,Gamma}_paperResidue` instead of
    -- `residue.hpq{β,γ}` (those fields no longer exist).
    (h_weak_m_universal : WeakConvPairing_universal (d := d)
                            (hpqBeta_paperResidue (d := d) hpow hExp
                              hβBarEq hβBar'Eq)
                            (fun k => (seq.sol k).m) wkBundle.mLim)
    (h_weak_u_universal : WeakConvPairing_universal (d := d)
                            (hpqGamma_paperResidue (d := d) hpow hExp
                              hγBarEq hγBar'Eq)
                            (fun k => (seq.sol k).u) wkBundle.uLim)
    (h_weak_Du_universal : ∀ i,
        WeakConvPairing_universal (d := d)
          (hpqGamma_paperResidue (d := d) hpow hExp hγBarEq hγBar'Eq)
          (fun k => (seq.sol k).Du i) (wkBundle.DuLim i)) :
    LimitPairingSelectorFamily (d := d)
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      (V := V) (H := H) (DpH := DpH)
      seq wkBundle.mLim wkBundle.uLim wkBundle.DuLim
      (D_transport_family (d := d)
        wkBundle.mLim wkBundle.uLim wkBundle.DuLim) :=
  limitPairingSelectorFamily_of_paperHypotheses_at
    hmon hpow hV hExp hHat0 hAgree seq wkBundle
    (D_transport_family (d := d)
      wkBundle.mLim wkBundle.uLim wkBundle.DuLim)
    regSupplier_transport gateauxAux
    hβBarEq hγBarEq hβBar'Eq hγBar'Eq residue
    h_weak_m_universal h_weak_u_universal h_weak_Du_universal

/-! ### Closed-form producer:
`finalIntegrabilityBundle_of_paperHypotheses`.

Per CONVENTIONS §1b, the three integrability fields of
`FinalIntegrabilityBundle` (`hRes`, `hResM`, `hFluxInt`) at the
*bare* weak-limit triple `(mLim, uLim, DuLim)` are nonlinear estimates
that depend on global growth bounds on `H` / `DpH` (extractable from
`hpow`) plus Hölder products and Sobolev embeddings at the limit
exponents — none of which are presently available closed-form in our
toolkit. The task spec authorises paper-residue inputs for fields
whose genuine proof requires Mathlib lemmas not yet present.

Following the pattern of `mintyClosure_of_paperHypotheses` and its
authorised companion `MintyClosureSelectorPaperResidue`, we package
the three integrability claims as a paper-residue record at the
weak-limit triple, and the producer simply projects them into a
`FinalIntegrabilityBundle`. The paper hypotheses `(hmon, hpow, hV,
hExp)` plus `seq` and `wkBundle` are pinned through to keep the
producer's signature aligned with the rest of the T9 chain (none of
them are consumed in the body — the residue carries the genuine
integrability content).
-/

/-- **Authorised paper-residue inputs** for
`finalIntegrabilityBundle_of_paperHypotheses`.

Packages the three integrability claims at the weak-limit bare triple
`(mLim, uLim, DuLim)` exactly as required by `FinalIntegrabilityBundle`. -/
structure FinalIntegrabilityPaperResidue
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    (mLim uLim : (Fin d → ℝ) → ℝ) where
  /-- HJB-residual integrability at the limit triple. -/
  hRes : MeasureTheory.Integrable
            (StationaryMFG.Theorems.SimplePower.hjbResidual V H DuLim mLim uLim)
            (MeasureTheory.volume.restrict (UnitCube d))
  /-- Residual·m integrability at the limit triple. -/
  hResM : MeasureTheory.Integrable
            (fun x =>
              StationaryMFG.Theorems.SimplePower.hjbResidual V H DuLim mLim uLim x
                * mLim x)
            (MeasureTheory.volume.restrict (UnitCube d))
  /-- Flux integrability at the limit triple. -/
  hFluxInt : MeasureTheory.Integrable
              (fun x =>
                StationaryMFG.Hamiltonian.mDpH DpH x
                  (fun i => DuLim i x) (mLim x))
              (MeasureTheory.volume.restrict (UnitCube d))

/-- **Closed-form producer.** Build a `FinalIntegrabilityBundle` from
the paper hypotheses `(hmon, hpow, hV, hExp)`, the regularized
sequence `seq`, the weak-limit bundle `wkBundle`, and the
authorised paper-residue inputs.

Per CONVENTIONS §1b, the three `Integrable` fields are read off the
`FinalIntegrabilityPaperResidue` directly. The paper hypotheses
`(hmon, hpow, hV, hExp)`, `seq`, and `wkBundle` are pinned for chain
shape — they are *not* consumed in the body. The bundle is reported at
the weak-limit triple `(wkBundle.mLim, wkBundle.uLim, wkBundle.DuLim)`. -/
noncomputable def finalIntegrabilityBundle_of_paperHypotheses
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
    (_seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH)
    (wkBundle : WeakLimitInputBundleAE (d := d) γBarReal βBarReal)
    (residue : FinalIntegrabilityPaperResidue (d := d)
                  V H DpH wkBundle.DuLim wkBundle.mLim wkBundle.uLim) :
    FinalIntegrabilityBundle (d := d) V H DpH
      wkBundle.DuLim wkBundle.mLim wkBundle.uLim where
  hRes := residue.hRes
  hResM := residue.hResM
  hFluxInt := residue.hFluxInt

/-- **Sanity check.** `finalIntegrabilityBundle_of_paperHypotheses`
constructs a `FinalIntegrabilityBundle` and one of its integrability
fields can be projected. -/
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
    (residue : FinalIntegrabilityPaperResidue (d := d)
                  V H DpH wkBundle.DuLim wkBundle.mLim wkBundle.uLim) :
    MeasureTheory.Integrable
      (StationaryMFG.Theorems.SimplePower.hjbResidual V H
        wkBundle.DuLim wkBundle.mLim wkBundle.uLim)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
  (finalIntegrabilityBundle_of_paperHypotheses
      hmon hpow hV hExp seq wkBundle residue).hRes

/-! ### Phase H3 / H4 — discharge final integrability from a Lp residue.

Per tasks
`infra-P5-theorem1-phase-H3-discharge-final-integrability-residues`
(Phase H3) and
`infra-P5-theorem1-phase-H4-discharge-hFluxInt`
(Phase H4), we replace the three `Integrable` claims of
`FinalIntegrabilityPaperResidue` by:

* a strictly-stronger `MemLpPer βBar'` Lp claim on the HJB residual
  (Phase H3) — discharges `hRes` (via L¹-reduction on the finite-measure
  unit cube) and `hResM` (via the periodic Hölder pairing
  `MemLpPer.integrable_mul` at conjugate exponents `(βBar', βBar)`,
  which is encoded by `hExp.βConj`);
* the strict-`γ̄` `MemLpPer` certificate on every coordinate of `DuLim`
  (Phase H4) — discharges `hFluxInt` via
  `Hamiltonian.mDpH_integrable_of_memLpPer` (which combines the
  pointwise dominator bound `mDpH_pointwise_bound` with the
  `MemLpPer γ̄'`-closure of the dominator
  `flux_dominator_memLp_gammaBar'` and `MemLp.mono_exponent` to L¹).

The Phase H4 discharge needs the power-growth bundle `hpow` (for the
exponent identities `β̄ = β + 1`, `γ̄ = α(β+1)/β`); flux measurability
is now derived structurally from the bundle (Phase H5c strip — see
`WeakLimitInputBundle.hFlux_meas`). -/

/-- **Lp-strengthened paper-residue inputs.** A drop-in replacement
for `FinalIntegrabilityPaperResidue` whose sole field is the
*strictly stronger* `MemLpPer βBar'` Lp claim on the HJB residual.
The producer `finalIntegrabilityPaperResidue_of_lpResidue` derives
all three `Integrable` claims (`hRes`, `hResM`, `hFluxInt`) from this
plus the bundle. -/
structure FinalIntegrabilityPaperResidueLp
    (βBar' : ℝ≥0∞) (γBarReal : ℝ)
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (DuLim : Fin d → (Fin d → ℝ) → ℝ)
    (mLim uLim : (Fin d → ℝ) → ℝ) : Prop where
  -- **Phase H5b strip**
  -- (`infra-P5-theorem1-phase-H5b-drop-hDuLim-memLp-from-finIntResidue`).
  -- The legacy field `hDuLim_memLp_γ` (strict-`γ̄` `MemLpPer` of every
  -- coordinate of `DuLim`) has been removed: it is now derived
  -- structurally inside `finalIntegrabilityPaperResidue_of_lpResidue`
  -- from `wkBundle.hDuLim_memLp_γ` (Lp.memLp + MemLp.ae_eq via
  -- `auxAeOfClusterPoint`).
  -- **Phase H5c strip**
  -- (`infra-P5-theorem1-phase-H5c-drop-hFlux-meas-from-finIntResidue`).
  -- The legacy field `hFlux_meas` (a.e. strong measurability of the flux
  -- vector field `x ↦ mDpH DpH x (fun i => DuLim i x) (mLim x)`) has been
  -- removed: it is now derived structurally inside
  -- `finalIntegrabilityPaperResidue_of_lpResidue` from
  -- `WeakLimitInputBundle.hFlux_meas hpow wkBundle`.
  -- **Phase H5d strip**
  -- (`infra-P5-theorem1-phase-H5d-derive-hRes-Lp-collapse-finIntResidue`).
  -- The legacy field `hRes_Lp` (HJB-residual `MemLpPer βBar'`) has been
  -- removed: it is now derived structurally from
  -- `WeakLimitInputBundle.hRes_Lp hpow hHat0 hFin hAgree hV
  -- hβBarPaper hγBarPaper wkBundle`. As a result this structure
  -- currently has zero fields; it is retained as a `Prop`-shaped
  -- placeholder so existing call sites in `BanachBridge.lean` need
  -- only delete their `hRes_Lp := …` clause. A subsequent task may
  -- delete the structure entirely once `T10PaperResidues.finIntResidue`
  -- is removed.
  /-- Trivially-true marker field; the structure is currently
  vacuous following the H5b/H5c/H5d strips. -/
  trivial : True

/-- **Phase H3 + H4 producer.** Discharge all three integrability
fields of `FinalIntegrabilityPaperResidue` from the Lp-strengthened
residue plus the power-growth bundle.

Pipeline:
* `hRes` from `lpRes.hRes_Lp` via `MemLp.mono_exponent` to L¹ on the
  finite-measure unit cube (uses `1 ≤ βBar'`, automatic from
  `hExp.βConj.symm.lt`), then `memLp_one_iff_integrable`.
* `hResM` from `lpRes.hRes_Lp : MemLpPer βBar' (residual)` and
  `wkBundle.hmLim_memLp : MemLpPer βBar mLim` via the periodic
  Hölder lemma `MemLpPer.integrable_mul` at the conjugate pair
  `(βBar', βBar)` (Hölder conjugacy from `hExp.βConj`).
* `hFluxInt` from `Hamiltonian.mDpH_integrable_of_memLpPer` applied
  to `wkBundle.hmLim_memLp` (rewritten to the `hpow.β + 1` exponent
  shape via `hβBarPaper`), `wkBundle.hDuLim_memLp_γ` (rewritten to the
  `hpow.α * (hpow.β + 1) / hpow.β` shape via `hγBarPaper`),
  `wkBundle.hmLim_nonneg`, and `WeakLimitInputBundle.hFlux_meas hpow
  wkBundle` (the Phase H5c structurally-derived flux measurability). -/
noncomputable def finalIntegrabilityPaperResidue_of_lpResidue
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
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
            (ENNReal.ofReal βBarReal') V)
    (hExp : SimplePowerExponentFacts γBarReal
                (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
                (ENNReal.ofReal βBarReal'))
    (hβBarPaper : βBarReal = hpow.β + 1)
    (hγBarPaper : γBarReal = hpow.α * (hpow.β + 1) / hpow.β)
    (hβBar'Paper : βBarReal' = (hpow.β + 1) / hpow.β)
    (wkBundle : WeakLimitInputBundleAE (d := d) γBarReal βBarReal)
    (_lpRes : FinalIntegrabilityPaperResidueLp (d := d)
                (ENNReal.ofReal βBarReal') γBarReal V H DpH
                wkBundle.DuLim wkBundle.mLim wkBundle.uLim) :
    FinalIntegrabilityPaperResidue (d := d) V H DpH
      wkBundle.DuLim wkBundle.mLim wkBundle.uLim := by
  -- Finite-measure instance on the restricted unit cube (project-internal).
  haveI : MeasureTheory.IsFiniteMeasure
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)).restrict
        (UnitCube d)) :=
    Periodic.Saturator.instIsFiniteMeasureRestrictUnitCube
  -- **Phase H5d** — derive the legacy `hRes_Lp` content structurally
  -- from `WeakLimitInputBundle.hRes_Lp` (which itself reduces to
  -- `Hamiltonian.g_memLp_betaBar'_nonneg` via `(hpow, hHat0, hFin, hAgree)`).
  have hV' : Periodic.MemLpPer (d := d)
              (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) V := by
    rw [show ENNReal.ofReal ((hpow.β + 1) / hpow.β)
          = ENNReal.ofReal βBarReal' from by rw [hβBar'Paper]]
    exact hV
  have hRes_Lp_derived :
      Periodic.MemLpPer (d := d)
        (ENNReal.ofReal ((hpow.β + 1) / hpow.β))
        (StationaryMFG.Theorems.SimplePower.hjbResidual V H
          wkBundle.DuLim wkBundle.mLim wkBundle.uLim) :=
    WeakLimitInputBundleAE.hRes_Lp (d := d)
      hpow hHat0 hFin hAgree hV' hβBarPaper hγBarPaper wkBundle
  have hRes_Lp :
      Periodic.MemLpPer (d := d)
        (ENNReal.ofReal βBarReal')
        (StationaryMFG.Theorems.SimplePower.hjbResidual V H
          wkBundle.DuLim wkBundle.mLim wkBundle.uLim) := by
    rw [show ENNReal.ofReal βBarReal'
          = ENNReal.ofReal ((hpow.β + 1) / hpow.β) from by rw [hβBar'Paper]]
    exact hRes_Lp_derived
  -- Step 1: derive `hRes` from `hRes_Lp` via L¹-reduction on a finite-measure space.
  have h_one_le_βBar' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal βBarReal' :=
    le_of_lt hExp.betaBar'_one_lt
  have h_memLp_one :
      MeasureTheory.MemLp
        (StationaryMFG.Theorems.SimplePower.hjbResidual V H
          wkBundle.DuLim wkBundle.mLim wkBundle.uLim)
        1
        (MeasureTheory.volume.restrict (UnitCube d)) :=
    hRes_Lp.toMemLp.mono_exponent h_one_le_βBar'
  have hRes : MeasureTheory.Integrable
        (StationaryMFG.Theorems.SimplePower.hjbResidual V H
          wkBundle.DuLim wkBundle.mLim wkBundle.uLim)
        (MeasureTheory.volume.restrict (UnitCube d)) :=
    MeasureTheory.memLp_one_iff_integrable.mp h_memLp_one
  -- Step 2: derive `hResM` from Hölder pairing `(βBar', βBar)`.
  -- The periodic Hölder lemma needs real-valued exponents and a
  -- `Real.HolderConjugate` certificate — which `hExp.βConj` provides
  -- once we identify `(ENNReal.ofReal βBarReal').toReal = βBarReal'`
  -- and `(ENNReal.ofReal βBarReal).toReal = βBarReal`.
  have h_βBar_lt_top : (ENNReal.ofReal βBarReal) < ⊤ := hExp.βBar_lt_top
  have h_βBar'_lt_top : (ENNReal.ofReal βBarReal') < ⊤ := hExp.betaBar'_lt_top
  have h_βBar_pos : 0 < (ENNReal.ofReal βBarReal) :=
    lt_of_lt_of_le (by exact_mod_cast (one_pos : (0 : ℝ≥0∞) < 1))
      (le_of_lt hExp.βBar_one_lt)
  have h_βBar'_pos : 0 < (ENNReal.ofReal βBarReal') :=
    lt_of_lt_of_le (by exact_mod_cast (one_pos : (0 : ℝ≥0∞) < 1))
      h_one_le_βBar'
  have h_toReal_βBar : (ENNReal.ofReal βBarReal).toReal = βBarReal := by
    have h_pos : 0 < βBarReal := by
      have : (0 : ℝ≥0∞) < ENNReal.ofReal βBarReal := h_βBar_pos
      exact (ENNReal.ofReal_pos).mp this
    exact ENNReal.toReal_ofReal h_pos.le
  have h_toReal_βBar' : (ENNReal.ofReal βBarReal').toReal = βBarReal' := by
    have h_pos : 0 < βBarReal' := by
      have : (0 : ℝ≥0∞) < ENNReal.ofReal βBarReal' := h_βBar'_pos
      exact (ENNReal.ofReal_pos).mp this
    exact ENNReal.toReal_ofReal h_pos.le
  -- Reshape `hExp.βConj : Real.HolderConjugate βBar βBar'` (after `toReal`).
  have hβConj_real : Real.HolderConjugate βBarReal' βBarReal := by
    have := hExp.βConj  -- HolderConjugate βBar.toReal βBar'.toReal
    rw [h_toReal_βBar, h_toReal_βBar'] at this
    exact this.symm
  -- Apply the periodic Hölder lemma. The Lp residue and `hmLim_memLp`
  -- are stated at the ENNReal exponents `ofReal βBar'` / `ofReal βBar`,
  -- which match what `MemLpPer.integrable_mul` consumes.
  have hResM : MeasureTheory.Integrable
        (fun x =>
          StationaryMFG.Theorems.SimplePower.hjbResidual V H
            wkBundle.DuLim wkBundle.mLim wkBundle.uLim x
            * wkBundle.mLim x)
        (MeasureTheory.volume.restrict (UnitCube d)) := by
    have hInt :=
      Periodic.MemLpPer.integrable_mul (d := d) hβConj_real
        hRes_Lp wkBundle.hmLim_memLp
    -- `IntegrableOn f s μ := Integrable f (μ.restrict s)` by definition.
    exact hInt
  -- Step 3 (Phase H4): derive `hFluxInt` via
  -- `Hamiltonian.mDpH_integrable_of_memLpPer`, after rewriting the
  -- exponents in `wkBundle.hmLim_memLp` and `lpRes.hDuLim_memLp_γ`
  -- to the `hpow`-shape consumed by the Hamiltonian lemma.
  have hm_memLp' :
      Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1))
        wkBundle.mLim := by
    rw [show ENNReal.ofReal (hpow.β + 1) = ENNReal.ofReal βBarReal from by
          rw [hβBarPaper]]
    exact wkBundle.hmLim_memLp
  have hDu_memLp' :
      ∀ i, Periodic.MemLpPer (d := d)
              (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))
              (wkBundle.DuLim i) := by
    intro i
    rw [show ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)
        = ENNReal.ofReal γBarReal from by rw [hγBarPaper]]
    -- Phase H5b: derived from `wkBundle.auxAeOfClusterPoint` instead of
    -- the dropped `lpRes.hDuLim_memLp_γ` field.
    exact wkBundle.hDuLim_memLp_γ i
  have hFluxInt : MeasureTheory.Integrable
        (fun x =>
          StationaryMFG.Hamiltonian.mDpH DpH x
            (fun i => wkBundle.DuLim i x) (wkBundle.mLim x))
        (MeasureTheory.volume.restrict (UnitCube d)) :=
    Hamiltonian.mDpH_integrable_of_memLpPer (d := d) hpow
      wkBundle.mLim wkBundle.DuLim
      wkBundle.hmLim_nonneg hm_memLp' hDu_memLp'
      (WeakLimitInputBundleAE.hFlux_meas (d := d) hpow wkBundle)
  -- Assemble.
  exact
    { hRes := hRes
      hResM := hResM
      hFluxInt := hFluxInt }

/-- **Sanity check.** `finalIntegrabilityPaperResidue_of_lpResidue`
constructs a `FinalIntegrabilityPaperResidue` from the Lp residue,
and one of its derived integrability fields can be projected. -/
example
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
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
            (ENNReal.ofReal βBarReal') V)
    (hExp : SimplePowerExponentFacts γBarReal
                (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
                (ENNReal.ofReal βBarReal'))
    (hβBarPaper : βBarReal = hpow.β + 1)
    (hγBarPaper : γBarReal = hpow.α * (hpow.β + 1) / hpow.β)
    (hβBar'Paper : βBarReal' = (hpow.β + 1) / hpow.β)
    (wkBundle : WeakLimitInputBundleAE (d := d) γBarReal βBarReal)
    (lpRes : FinalIntegrabilityPaperResidueLp (d := d)
                (ENNReal.ofReal βBarReal') γBarReal V H DpH
                wkBundle.DuLim wkBundle.mLim wkBundle.uLim) :
    MeasureTheory.Integrable
      (fun x =>
        StationaryMFG.Theorems.SimplePower.hjbResidual V H
          wkBundle.DuLim wkBundle.mLim wkBundle.uLim x
          * wkBundle.mLim x)
      (MeasureTheory.volume.restrict (UnitCube d)) :=
  (finalIntegrabilityPaperResidue_of_lpResidue
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      hpow hHat0 hFin hAgree hV hExp hβBarPaper hγBarPaper hβBar'Paper
      wkBundle lpRes).hResM

/-- **Phase H4 unit test.** The flux-integrability discharge inside
`finalIntegrabilityPaperResidue_of_lpResidue` is exposed via the
`hFluxInt` projection. -/
example
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
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
            (ENNReal.ofReal βBarReal') V)
    (hExp : SimplePowerExponentFacts γBarReal
                (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
                (ENNReal.ofReal βBarReal'))
    (hβBarPaper : βBarReal = hpow.β + 1)
    (hγBarPaper : γBarReal = hpow.α * (hpow.β + 1) / hpow.β)
    (hβBar'Paper : βBarReal' = (hpow.β + 1) / hpow.β)
    (wkBundle : WeakLimitInputBundleAE (d := d) γBarReal βBarReal)
    (lpRes : FinalIntegrabilityPaperResidueLp (d := d)
                (ENNReal.ofReal βBarReal') γBarReal V H DpH
                wkBundle.DuLim wkBundle.mLim wkBundle.uLim) :
    MeasureTheory.Integrable
      (fun x =>
        StationaryMFG.Hamiltonian.mDpH DpH x
          (fun i => wkBundle.DuLim i x) (wkBundle.mLim x))
      (MeasureTheory.volume.restrict (UnitCube d)) :=
  (finalIntegrabilityPaperResidue_of_lpResidue
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      hpow hHat0 hFin hAgree hV hExp hβBarPaper hγBarPaper hβBar'Paper
      wkBundle lpRes).hFluxInt

/-! ### Closed-form producer:
`weakLimitInputBundle_of_paperHypotheses`.

Per CONVENTIONS §1b, this thin wrapper composes the paper-hypothesis
chain `(hmon, hpow, hV, hExp, seq)` with an authorised paper-residue
input `WeakLimitSelector` (the Path-A obstruction on the
periodic-representative selection — see the docstring above
`WeakLimitSelector`). Internally it routes `hExp` and `selector`
through the AC1 producer
`weakLimitInputBundle_of_regularizedSequence`, which already
discharges reflexivity and strong-dual separability of the Banach
pair from `hExp` via `Periodic.lpSobolev_product_isReflexive`
and `Periodic.lpSobolev_product_strongDual_separable`.

The `seq.uniformBound` field is what supports the existence of a
weak limit point through Banach–Alaoglu in the paper proof; here
the actual limit point is supplied through the explicit
`WeakLimitSelector` residue (Path-A obstruction filed as
`infra-P4-rebuild-T9-discharge-weak-limit-bundle-selector`).

Mirrors the residue-bundle pattern used by
`mintyClosureSelector_of_paperHypotheses` and
`finalIntegrabilityBundle_of_paperHypotheses`. -/

/-- **Closed-form `WeakLimitInputBundle` producer.** Build a
`WeakLimitInputBundle` from the paper hypotheses
`(hmon, hpow, hV, hExp)`, the regularized sequence `seq` (its
`uniformBound` field is the input that justifies weak compactness
in the paper proof), and the authorised paper-residue
`WeakLimitSelector` (Path-A obstruction on the periodic
representative selection).

Per CONVENTIONS §1b, the abstract weak-compactness / Banach–Alaoglu
extraction step is handled through the explicit `selector`
parameter; the structural reflexivity & strong-dual separability
fields are derived automatically from `hExp` via the existing AC1
producer `weakLimitInputBundle_of_regularizedSequence`.

The paper hypotheses `(hmon, hpow, hV)` and `seq` are pinned
through to keep the producer's signature aligned with the rest of
the T9 chain (see `mintyClosureSelector_of_paperHypotheses`,
`finalIntegrabilityBundle_of_paperHypotheses`,
`limitPairingSelector_of_paperHypotheses`); they are not consumed
in the body. -/
noncomputable def weakLimitInputBundle_of_paperHypotheses
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (_hmon : Hamiltonian.HypothesisMonotone H DpH)
    (_hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (_hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (hExp : SimplePowerExponentFacts γBarReal
              (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
              (ENNReal.ofReal βBarReal'))
    (_seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH)
    (selector : WeakLimitSelector (d := d) γBarReal βBarReal) :
    WeakLimitInputBundle (d := d) γBarReal βBarReal :=
  weakLimitInputBundle_of_regularizedSequence
    (βBarReal' := βBarReal') hExp selector

/-- **Sanity check.** `weakLimitInputBundle_of_paperHypotheses`
constructs a `WeakLimitInputBundle` and the `hRefl` field can be
projected. -/
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
    (selector : WeakLimitSelector (d := d) γBarReal βBarReal) :
    Periodic.IsReflexiveNormedSpace
      (Periodic.LpPer (ENNReal.ofReal βBarReal) d
        × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d) :=
  (weakLimitInputBundle_of_paperHypotheses
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      hmon hpow hV hExp seq selector).hRefl

/-! ### Closed-form AE-native producer:
`weakLimitInputBundleAE_of_paperHypotheses`.

Per Phase 3b of the Theorem 1 closure plan, this AE-native producer
consumes a `WeakLimitExtraction` (chosen cluster point `w` plus an
AE-native `WeakLimitSelectorAE … w`) and returns the parallel
AE-native bundle `WeakLimitInputBundleAE`. **Crucially**, the body
**never** consumes `extr.auxOther` — every field is read off
`extr.selector` and `extr.w`, with the chosen-`w` agreement supplied
by direct `AEPeriodicRep.ae_eq` projections. Reflexivity and strong-
dual separability are derived from `hExp` via
`Periodic.lpSobolev_product_isReflexive` and
`Periodic.lpSobolev_product_strongDual_separable`.

This is the AE-native sibling of `weakLimitInputBundle_of_paperHypotheses`,
skipping the `WeakLimitSelectorAE.toWeakLimitSelector` round-trip. -/

/-- **Closed-form `WeakLimitInputBundleAE` producer.** Build a
`WeakLimitInputBundleAE` from the paper hypotheses
`(hmon, hpow, hV, hExp, seq)` and a `WeakLimitExtraction` (chosen
cluster point `w` plus an AE-native selector). The body consumes
**only** `extr.selector` and `extr.w` — the residual `auxOther` field
is never touched.

Per CONVENTIONS §1b, reflexivity & strong-dual separability are
derived from `hExp` via `Periodic.lpSobolev_product_isReflexive` and
`Periodic.lpSobolev_product_strongDual_separable`. The remaining
fields are read off `extr.selector`, with the AE-`MemLpPer`
transports through `AEPeriodicRep.ae_eq` (cf. `WeakLimitSelectorAE.{
hmLim_memLp, huLim_memLp}`) and the `MemSobolevPer` field assembled
via `Periodic.HasWeakDerivPer.of_weak_limit` (parallel to
`WeakLimitSelectorAE.toWeakLimitSelector`).

The paper hypotheses `(hmon, hpow, hV)` and `seq` are pinned through
to keep the producer's signature aligned with the rest of the T9
chain (parallel to `weakLimitInputBundle_of_paperHypotheses`); they
are not consumed in the body. -/
noncomputable def weakLimitInputBundleAE_of_paperHypotheses
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (_hmon : Hamiltonian.HypothesisMonotone H DpH)
    (_hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (_hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (hExp : SimplePowerExponentFacts γBarReal
              (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
              (ENNReal.ofReal βBarReal'))
    (_seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH)
    (extr : WeakLimitExtraction (d := d) γBarReal βBarReal) :
    WeakLimitInputBundleAE (d := d) γBarReal βBarReal := by
  -- Step 1: derive `0 < βBarReal` from `1 < ENNReal.ofReal βBarReal`.
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
  -- Step 2: real-side positivity of `βBarReal'` from `hExp`.
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
  -- Step 3: `γBar` setup with conjugate `γBarPrime = γBar/(γBar-1)`.
  have h_one_lt_γBarReal : (1 : ℝ) < γBarReal := hExp.γBar_one_lt_real
  have h_γBarReal_pos : (0 : ℝ) < γBarReal := by linarith
  let γBarPrimeReal : ℝ := γBarReal / (γBarReal - 1)
  have h_γBar_minus_one_pos : (0 : ℝ) < γBarReal - 1 := by linarith
  have h_γBarPrimeReal_pos : (0 : ℝ) < γBarPrimeReal :=
    div_pos h_γBarReal_pos h_γBar_minus_one_pos
  have h_one_lt_γBarPrimeReal : (1 : ℝ) < γBarPrimeReal := by
    show (1 : ℝ) < γBarReal / (γBarReal - 1)
    rw [lt_div_iff₀ h_γBar_minus_one_pos, one_mul]
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
    show Real.HolderConjugate γBarReal (γBarReal / (γBarReal - 1))
    exact this
  have hγConj_enn :
      ENNReal.HolderConjugate (ENNReal.ofReal γBarReal)
        (ENNReal.ofReal γBarPrimeReal) :=
    Real.HolderConjugate.ennrealOfReal hγConj_real
  haveI : ENNReal.HolderConjugate (ENNReal.ofReal γBarReal)
            (ENNReal.ofReal γBarPrimeReal) := hγConj_enn
  -- Step 4: `βBar ≠ ∞` and `γBar ≠ ∞`.
  have h_βBar_ne_top : (ENNReal.ofReal βBarReal) ≠ ∞ :=
    ENNReal.ofReal_ne_top
  have h_γBar_ne_top : (ENNReal.ofReal γBarReal) ≠ ∞ :=
    ENNReal.ofReal_ne_top
  -- Step 5: reflexivity & separability via the discharged infrastructure.
  have hRefl :
      Periodic.IsReflexiveNormedSpace
        (Periodic.LpPer (ENNReal.ofReal βBarReal) d
          × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d) :=
    Periodic.lpSobolev_product_isReflexive (d := d)
      (ENNReal.ofReal βBarReal) (ENNReal.ofReal βBarReal')
      (ENNReal.ofReal γBarReal) (ENNReal.ofReal γBarPrimeReal)
      hExp.βBar_one_lt h_βBar_ne_top hExp.gammaBar_one_lt h_γBar_ne_top
  have hSep :
      TopologicalSpace.SeparableSpace
        (StrongDual ℝ
          (Periodic.LpPer (ENNReal.ofReal βBarReal) d
            × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d)) :=
    Periodic.lpSobolev_product_strongDual_separable (d := d)
      (ENNReal.ofReal βBarReal) (ENNReal.ofReal βBarReal')
      (ENNReal.ofReal γBarReal) (ENNReal.ofReal γBarPrimeReal)
      hExp.βBar_one_lt h_βBar_ne_top hExp.gammaBar_one_lt h_γBar_ne_top
  -- Step 6: assemble the AE-native bundle from `extr.selector` and `extr.w`
  -- only — `extr.auxOther` is never read.
  exact
    { hRefl := hRefl
      hSep := hSep
      w := extr.w
      mRep := extr.selector.mRep
      uRep := extr.selector.uRep
      DuRep := extr.selector.DuRep
      hDuRep_memLp := extr.selector.hDuRep_memLp
      seqRepU := extr.selector.seqRepU
      seqRepDu := extr.selector.seqRepDu
      hSeqRepWeak := extr.selector.hSeqRepWeak
      hConvU := extr.selector.hConvU
      hConvDu := extr.selector.hConvDu
      hmRep_nonneg := extr.selector.hmRep_nonneg
      hMlimPer := extr.selector.mRep.periodic
      hUlimPer := extr.selector.uRep.periodic
      hDuLim_periodic := fun i => (extr.selector.DuRep i).periodic
      hmLim_memLp := extr.selector.hmLim_memLp
      huLim_sob :=
        ⟨extr.selector.huLim_memLp,
          ⟨fun i => (extr.selector.DuRep i).rep,
            fun i =>
              Periodic.HasWeakDerivPer.of_weak_limit
                (i := i) (u_n := extr.selector.seqRepU)
                (Du_n := fun n => extr.selector.seqRepDu n i)
                (u := extr.selector.uRep.rep)
                (Du := (extr.selector.DuRep i).rep)
                (extr.selector.hDuRep_memLp i)
                (fun n => extr.selector.hSeqRepWeak n i)
                (by
                  intro ψ
                  have h := extr.selector.hConvU id strictMono_id ψ
                  simpa using h)
                (by
                  intro ψ
                  have h := extr.selector.hConvDu id strictMono_id i ψ
                  simpa using h)⟩⟩ }

/-- **Phase 3c-ii AE-leaner producer.**

Identical to `weakLimitInputBundleAE_of_paperHypotheses` except it
consumes a `WeakLimitExtractionAE` (chosen cluster point + AE selector,
no `auxOther`). The body is a verbatim copy of
`weakLimitInputBundleAE_of_paperHypotheses` with the `extr.auxOther`
field-read removed (the legacy producer never reads it anyway, per the
docstring of `weakLimitInputBundleAE_of_paperHypotheses`). -/
noncomputable def weakLimitInputBundleAE_of_paperHypotheses_AE
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (_hmon : Hamiltonian.HypothesisMonotone H DpH)
    (_hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (_hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (hExp : SimplePowerExponentFacts γBarReal
              (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
              (ENNReal.ofReal βBarReal'))
    (_seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH)
    (extr : WeakLimitExtractionAE (d := d) γBarReal βBarReal) :
    WeakLimitInputBundleAE (d := d) γBarReal βBarReal := by
  -- Step 1: derive `0 < βBarReal` from `1 < ENNReal.ofReal βBarReal`.
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
  -- Step 2: real-side positivity of `βBarReal'` from `hExp`.
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
  -- Step 3: `γBar` setup with conjugate `γBarPrime = γBar/(γBar-1)`.
  have h_one_lt_γBarReal : (1 : ℝ) < γBarReal := hExp.γBar_one_lt_real
  have h_γBarReal_pos : (0 : ℝ) < γBarReal := by linarith
  let γBarPrimeReal : ℝ := γBarReal / (γBarReal - 1)
  have h_γBar_minus_one_pos : (0 : ℝ) < γBarReal - 1 := by linarith
  have h_γBarPrimeReal_pos : (0 : ℝ) < γBarPrimeReal :=
    div_pos h_γBarReal_pos h_γBar_minus_one_pos
  have h_one_lt_γBarPrimeReal : (1 : ℝ) < γBarPrimeReal := by
    show (1 : ℝ) < γBarReal / (γBarReal - 1)
    rw [lt_div_iff₀ h_γBar_minus_one_pos, one_mul]
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
    show Real.HolderConjugate γBarReal (γBarReal / (γBarReal - 1))
    exact this
  have hγConj_enn :
      ENNReal.HolderConjugate (ENNReal.ofReal γBarReal)
        (ENNReal.ofReal γBarPrimeReal) :=
    Real.HolderConjugate.ennrealOfReal hγConj_real
  haveI : ENNReal.HolderConjugate (ENNReal.ofReal γBarReal)
            (ENNReal.ofReal γBarPrimeReal) := hγConj_enn
  -- Step 4: `βBar ≠ ∞` and `γBar ≠ ∞`.
  have h_βBar_ne_top : (ENNReal.ofReal βBarReal) ≠ ∞ :=
    ENNReal.ofReal_ne_top
  have h_γBar_ne_top : (ENNReal.ofReal γBarReal) ≠ ∞ :=
    ENNReal.ofReal_ne_top
  -- Step 5: reflexivity & separability via the discharged infrastructure.
  have hRefl :
      Periodic.IsReflexiveNormedSpace
        (Periodic.LpPer (ENNReal.ofReal βBarReal) d
          × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d) :=
    Periodic.lpSobolev_product_isReflexive (d := d)
      (ENNReal.ofReal βBarReal) (ENNReal.ofReal βBarReal')
      (ENNReal.ofReal γBarReal) (ENNReal.ofReal γBarPrimeReal)
      hExp.βBar_one_lt h_βBar_ne_top hExp.gammaBar_one_lt h_γBar_ne_top
  have hSep :
      TopologicalSpace.SeparableSpace
        (StrongDual ℝ
          (Periodic.LpPer (ENNReal.ofReal βBarReal) d
            × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d)) :=
    Periodic.lpSobolev_product_strongDual_separable (d := d)
      (ENNReal.ofReal βBarReal) (ENNReal.ofReal βBarReal')
      (ENNReal.ofReal γBarReal) (ENNReal.ofReal γBarPrimeReal)
      hExp.βBar_one_lt h_βBar_ne_top hExp.gammaBar_one_lt h_γBar_ne_top
  -- Step 6: assemble the AE-native bundle from `extr.selector` and `extr.w`.
  exact
    { hRefl := hRefl
      hSep := hSep
      w := extr.w
      mRep := extr.selector.mRep
      uRep := extr.selector.uRep
      DuRep := extr.selector.DuRep
      hDuRep_memLp := extr.selector.hDuRep_memLp
      seqRepU := extr.selector.seqRepU
      seqRepDu := extr.selector.seqRepDu
      hSeqRepWeak := extr.selector.hSeqRepWeak
      hConvU := extr.selector.hConvU
      hConvDu := extr.selector.hConvDu
      hmRep_nonneg := extr.selector.hmRep_nonneg
      hMlimPer := extr.selector.mRep.periodic
      hUlimPer := extr.selector.uRep.periodic
      hDuLim_periodic := fun i => (extr.selector.DuRep i).periodic
      hmLim_memLp := extr.selector.hmLim_memLp
      huLim_sob :=
        ⟨extr.selector.huLim_memLp,
          ⟨fun i => (extr.selector.DuRep i).rep,
            fun i =>
              Periodic.HasWeakDerivPer.of_weak_limit
                (i := i) (u_n := extr.selector.seqRepU)
                (Du_n := fun n => extr.selector.seqRepDu n i)
                (u := extr.selector.uRep.rep)
                (Du := (extr.selector.DuRep i).rep)
                (extr.selector.hDuRep_memLp i)
                (fun n => extr.selector.hSeqRepWeak n i)
                (by
                  intro ψ
                  have h := extr.selector.hConvU id strictMono_id ψ
                  simpa using h)
                (by
                  intro ψ
                  have h := extr.selector.hConvDu id strictMono_id i ψ
                  simpa using h)⟩⟩ }

/-- **AC4 sanity check.** `weakLimitInputBundleAE_of_paperHypotheses`
constructs a `WeakLimitInputBundleAE` and the `hRefl` field can be
projected. Mirrors the existing legacy sanity `example` directly above. -/
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
    (extr : WeakLimitExtraction (d := d) γBarReal βBarReal) :
    Periodic.IsReflexiveNormedSpace
      (Periodic.LpPer (ENNReal.ofReal βBarReal) d
        × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d) :=
  (weakLimitInputBundleAE_of_paperHypotheses
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      hmon hpow hV hExp seq extr).hRefl

/-! ### Helper: build `WeakLimitInputData_noAux` from `(hExp, seq)` -/

/-- Helper for `weakLimitExtractionAE_of_uniform_apriori`: build the
`WeakLimitInputData_noAux` bundle from `(hExp, seq)` plus the
discharged `hRefl`/`hSep` and the conjugate-`γBar'` hypotheses. -/
noncomputable def palomar_RegularizedSequence_weakLimitInputDataNoAux_of_paperHypotheses
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH)
    (γBarPrimeReal : ℝ)
    [Fact (1 ≤ ENNReal.ofReal γBarPrimeReal)]
    (hγConj_enn :
      ENNReal.HolderConjugate (ENNReal.ofReal γBarReal)
        (ENNReal.ofReal γBarPrimeReal))
    (h_γBar_ne_top : (ENNReal.ofReal γBarReal) ≠ ∞)
    (hRefl : Periodic.IsReflexiveNormedSpace
              (Periodic.LpPer (ENNReal.ofReal βBarReal) d
                × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d))
    (hSep : TopologicalSpace.SeparableSpace
              (StrongDual ℝ
                (Periodic.LpPer (ENNReal.ofReal βBarReal) d
                  × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d))) :
    WeakLimitInputData_noAux (d := d)
      (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal) :=
  -- A.e.-equality between bare components and Lp coercions of
  -- `(seq.sol n).toBanachPair`.
  let hcoeM : ∀ n,
      (⇑((seq.sol n).toBanachPair.1) : (Fin d → ℝ) → ℝ)
        =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
          (seq.sol n).m := fun n =>
    MeasureTheory.MemLp.coeFn_toLp (seq.sol n).hmLp
  let hcoeU : ∀ n,
      (⇑((seq.sol n).toBanachPair.2.1) : (Fin d → ℝ) → ℝ)
        =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
          (seq.sol n).u := fun n =>
    MeasureTheory.MemLp.coeFn_toLp (seq.sol n).huLp
  let hcoeDu : ∀ n i,
      (⇑((seq.sol n).toBanachPair.2.2 i) : (Fin d → ℝ) → ℝ)
        =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
          (seq.sol n).Du i := fun n i =>
    MeasureTheory.MemLp.coeFn_toLp ((seq.sol n).hDuLp i)
  { v_n := fun k => (seq.sol k).toBanachPair
    hBound := by
      obtain ⟨C, hC⟩ := seq.uniformBound
      refine isBounded_iff_forall_norm_le.mpr ⟨C, ?_⟩
      intro v hv
      rcases hv with ⟨k, rfl⟩
      exact hC k
    hMpos := by
      intro k
      filter_upwards [hcoeM k, (seq.sol k).hmNonneg] with x hx hxnn
      rw [hx]; exact hxnn
    hRefl := hRefl
    hSep := hSep
    seqRepU := fun n => (seq.sol n).u
    seqRepDu := fun n i => (seq.sol n).Du i
    hSeqRepU_aeEq := fun n => (hcoeU n).symm
    hSeqRepDu_aeEq := fun n i => (hcoeDu n i).symm
    hSeqRepWeak := fun n i => (seq.sol n).hWeakDeriv i
    hConvU := by
      intro φ _ w hwlim ψ
      have hPair :=
        tendsto_smoothTester_of_banachWeak_pair_snd_val
          (γBar' := ENNReal.ofReal γBarPrimeReal) hγConj_enn h_γBar_ne_top
          (fun k => (seq.sol (φ k)).toBanachPair) w hwlim ψ
      have hLHS_fn :
          (fun k => Periodic.periodicIntegral
            (fun x =>
              (⇑((seq.sol (φ k)).toBanachPair.2.1)) x *
                (ψ : (Fin d → ℝ) → ℝ) x))
          = (fun k => Periodic.periodicIntegral
            (fun x =>
              (seq.sol (φ k)).u x * (ψ : (Fin d → ℝ) → ℝ) x)) := by
        funext k
        unfold Periodic.periodicIntegral
        apply MeasureTheory.integral_congr_ae
        filter_upwards [hcoeU (φ k)] with x hx
        rw [hx]
      rw [hLHS_fn] at hPair
      exact hPair
    hConvDu := by
      intro φ _ w hwlim i ψ
      have hPair :=
        tendsto_smoothTester_of_banachWeak_pair_snd_grad
          (γBar' := ENNReal.ofReal γBarPrimeReal) hγConj_enn h_γBar_ne_top
          (fun k => (seq.sol (φ k)).toBanachPair) w hwlim i ψ
      have hLHS_fn :
          (fun k => Periodic.periodicIntegral
            (fun x =>
              (⇑((seq.sol (φ k)).toBanachPair.2.2 i)) x *
                (ψ : (Fin d → ℝ) → ℝ) x))
          = (fun k => Periodic.periodicIntegral
            (fun x =>
              (seq.sol (φ k)).Du i x * (ψ : (Fin d → ℝ) → ℝ) x)) := by
        funext k
        unfold Periodic.periodicIntegral
        apply MeasureTheory.integral_congr_ae
        filter_upwards [hcoeDu (φ k) i] with x hx
        rw [hx]
      rw [hLHS_fn] at hPair
      exact hPair }

/-! ### Final assembly: `weakLimitExtractionAE_of_uniform_apriori`

Per `infra-P4-weakLimitExtractionAE-of-uniform-apriori-finalAssembly`.

Compose the three landed pieces:

* `extractWeakLimit_noAux` (from `Banach/Closure.lean`): given a
  `WeakLimitInputData_noAux`, extract a Banach-pair cluster point
  `w`, periodic bare-function limits `(mLim, uLim, DuLim)` and the
  abstract weak-`Tendsto`.
* `aeSelectorData_of_extractWeakLimit_outputs`: package the
  destructured F.5 outputs as an `AESelectorData_of_extractWeakLimit`
  (the chosen-`w` `(mRep, uRep, DuRep, hmRep_nonneg)` slice).
* `tendsto_smoothTester_of_banachWeak_pair_{snd_val,snd_grad}` (from
  `Banach/WeakLimit.lean`): convert the abstract `WeakSpace`-tendsto
  to a smooth-tester integral pairing tendsto on each factor.

Assembles a fully constructive `WeakLimitExtractionAE` from
`(hExp, seq)` alone — no residue parameter. The body subsequences
the entire sequence by F.5's strict-mono index `φ_F5` so that the
selector's `hConvU`/`hConvDu` fields (universally quantified over
strict-mono `φ : ℕ → ℕ`) can be discharged for arbitrary `φ` by
composing the F.5 weak-tendsto with `StrictMono.tendsto_atTop`.

**HMinty-1 refactor** (Route 1): the public producer now returns a
`WeakLimitSubsequenceData`, which additionally carries the F.5
strict-mono index `idx := φ_F5` and the abstract Banach-pair
`WeakSpace`-tendsto `hWeakSpace_tendsto := hφlim`. The legacy
`weakLimitExtractionAE_of_uniform_apriori` is then the `.extraction`
projection of this richer producer, so all existing callers continue
to work unchanged. -/
theorem palomar_RegularizedSequence_nonempty_weakLimitSubsequenceData_of_uniform_apriori
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
              γBarReal βBarReal βBarReal' γBarReal' V H DpH) :
    Nonempty (WeakLimitSubsequenceData (d := d) γBarReal βBarReal seq) := by
  -- ===== Step A: Hölder-conjugate setup (mirrors AE bundle producer). =====
  -- A.1: real-side positivity of `βBarReal`.
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
  -- A.2: real-side positivity of `βBarReal'`.
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
  -- A.3: γ-side conjugate setup.
  have h_one_lt_γBarReal : (1 : ℝ) < γBarReal := hExp.γBar_one_lt_real
  have h_γBarReal_pos : (0 : ℝ) < γBarReal := by linarith
  let γBarPrimeReal : ℝ := γBarReal / (γBarReal - 1)
  have h_γBar_minus_one_pos : (0 : ℝ) < γBarReal - 1 := by linarith
  have h_γBarPrimeReal_pos : (0 : ℝ) < γBarPrimeReal :=
    div_pos h_γBarReal_pos h_γBar_minus_one_pos
  have h_one_lt_γBarPrimeReal : (1 : ℝ) < γBarPrimeReal := by
    show (1 : ℝ) < γBarReal / (γBarReal - 1)
    rw [lt_div_iff₀ h_γBar_minus_one_pos, one_mul]
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
    show Real.HolderConjugate γBarReal (γBarReal / (γBarReal - 1))
    exact this
  have hγConj_enn :
      ENNReal.HolderConjugate (ENNReal.ofReal γBarReal)
        (ENNReal.ofReal γBarPrimeReal) :=
    Real.HolderConjugate.ennrealOfReal hγConj_real
  -- A.4: `βBar ≠ ∞` and `γBar ≠ ∞`.
  have h_βBar_ne_top : (ENNReal.ofReal βBarReal) ≠ ∞ :=
    ENNReal.ofReal_ne_top
  have h_γBar_ne_top : (ENNReal.ofReal γBarReal) ≠ ∞ :=
    ENNReal.ofReal_ne_top
  -- A.5: reflexivity & separability.
  have hRefl :
      Periodic.IsReflexiveNormedSpace
        (Periodic.LpPer (ENNReal.ofReal βBarReal) d
          × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d) :=
    Periodic.lpSobolev_product_isReflexive (d := d)
      (ENNReal.ofReal βBarReal) (ENNReal.ofReal βBarReal')
      (ENNReal.ofReal γBarReal) (ENNReal.ofReal γBarPrimeReal)
      hExp.βBar_one_lt h_βBar_ne_top hExp.gammaBar_one_lt h_γBar_ne_top
  have hSep :
      TopologicalSpace.SeparableSpace
        (StrongDual ℝ
          (Periodic.LpPer (ENNReal.ofReal βBarReal) d
            × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d)) :=
    Periodic.lpSobolev_product_strongDual_separable (d := d)
      (ENNReal.ofReal βBarReal) (ENNReal.ofReal βBarReal')
      (ENNReal.ofReal γBarReal) (ENNReal.ofReal γBarPrimeReal)
      hExp.βBar_one_lt h_βBar_ne_top hExp.gammaBar_one_lt h_γBar_ne_top
  -- ===== Step B: assemble `WeakLimitInputData_noAux` via helper. =====
  let T : WeakLimitInputData_noAux (d := d)
            (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal) :=
    palomar_RegularizedSequence_weakLimitInputDataNoAux_of_paperHypotheses (d := d)
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      seq γBarPrimeReal hγConj_enn h_γBar_ne_top hRefl hSep
  -- ===== Step C: invoke `extractWeakLimit_noAux`. =====
  -- The conclusion of `extractWeakLimit_noAux` is a `Prop`-valued
  -- 14-tuple existential. Since the goal is now `Nonempty (...)`, a
  -- `Prop`, we can use `obtain` directly.
  obtain ⟨φ_F5, w, mLim, uLim, DuLim,
          hmono, hMae, hUae, hDuae,
          hMlim_memLp, hUlim_sob, hMlimPer, hUlimPer,
          _hMmeas, _hUmeas, hWeakLim, hMlim_nonneg, hφlim⟩ :=
    extractWeakLimit_noAux T
  -- ===== Step D: package selector data. =====
  -- `MemLpPer 1 (DuLim i)` follows from the extracted `hWeakLim` field.
  have hDuLim_memLp1 : ∀ i, Periodic.MemLpPer (d := d) 1 (DuLim i) :=
    fun i => (hWeakLim i).memLpPer
  -- Periodicities of `DuLim i`. The F.5 conclusion provides
  -- `IsPeriodic uLim`, but periodicity of `DuLim i` is *not* a
  -- separate field of `extractWeakLimit_noAux`. We derive it from the
  -- internal `bareCoeFnOfLpPer` construction: in fact, looking at the
  -- F.5 body, `DuLim i = (bareCoeFnOfLpPer (w.2.2 i)).rep`, which
  -- structurally has `.periodic`. Since the conclusion carries only
  -- the existential statements (no internal construction visible),
  -- we extract from the `hUlim_sob` Sobolev witness — but its weak-
  -- derivative family is *not* `DuLim` (Sobolev's `Exists` packs an
  -- internal witness). The right way: F.5's existential conclusion
  -- doesn't carry per-`i` periodicity of `DuLim i` directly. We
  -- instead bypass: AE-equality with `⇑(w.2.2 i)` plus the fact that
  -- AE-equality on the cube doesn't force pointwise periodicity. So
  -- we need a different route: re-extract from `bareCoeFnOfLpPer`-
  -- style. Cheapest workaround: pick the periodic representative
  -- `bareCoeFnOfLpPer (w.2.2 i)` directly here, instead of the F.5-
  -- internal one. They are a.e.-equal and both periodic.
  -- Actually `hDuae i` only says `DuLim i =ᵐ ⇑(w.2.2 i)`. We just
  -- replace `DuLim i` with our own periodic representative.
  let DuLim' : Fin d → (Fin d → ℝ) → ℝ :=
    fun i => (Periodic.bareCoeFnOfLpPer (d := d) (w.2.2 i)).rep
  have hDuLim'_per : ∀ i, Periodic.IsPeriodic (DuLim' i) :=
    fun i => (Periodic.bareCoeFnOfLpPer (d := d) (w.2.2 i)).periodic
  have hDuLim'_ae : ∀ i, DuLim' i
      =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ) :=
    fun i => (Periodic.bareCoeFnOfLpPer (d := d) (w.2.2 i)).ae_eq
  have hDuLim'_eq_DuLim : ∀ i, DuLim' i
      =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        DuLim i := by
    intro i
    refine (hDuLim'_ae i).trans ?_
    exact (hDuae i).symm
  -- Replace `DuLim` with `DuLim'` for the selector. Need to also
  -- update `hWeakLim'`, `hDuLim_memLp1'`.
  have hDuLim'_memLp1 : ∀ i, Periodic.MemLpPer (d := d) 1 (DuLim' i) := by
    intro i
    have h1 := hDuLim_memLp1 i
    -- `DuLim' i =ᵐ DuLim i`.
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq
      (μ := MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d))
      (hDuLim'_eq_DuLim i).symm h1.toMemLp)
  have hWeakLim' : ∀ i, Periodic.HasWeakDerivPer (d := d) i uLim (DuLim' i) :=
    fun i => (hWeakLim i).congr_ae (hDuLim'_memLp1 i) (hDuLim'_eq_DuLim i).symm
  -- ===== Step E: build the `WeakLimitSelectorAE`. =====
  -- Test-function convergence at the chosen `w` via the F.5 weak-Tendsto
  -- `hφlim`, then bridge LHS to bare `(seq.sol _).u`/`Du i` and RHS to
  -- the chosen `AEPeriodicRep.rep` `uLim`/`DuLim i` using the F.5 a.e.-
  -- equalities `hUae`/`hDuae`.
  -- The selector's `hConvU` quantifies over arbitrary `φ`; we discharge
  -- by composing `hφlim` with `φ.tendsto_atTop`, applying the
  -- pair_snd_val corollary, then bridging.
  have hFiveU :
      ∀ ψ : Periodic.SmoothPeriodic d,
        Tendsto
          (fun k => Periodic.periodicIntegral
              (fun x =>
                (seq.sol (φ_F5 k)).u x * (ψ : (Fin d → ℝ) → ℝ) x))
          atTop
          (𝓝 (Periodic.periodicIntegral
              (fun x => uLim x * (ψ : (Fin d → ℝ) → ℝ) x))) := by
    intro ψ
    -- Apply the noAux bundle's `hConvU` at `φ = φ_F5`. The `T.hConvU`
    -- field signature already returns convergence with `⇑w.2.1` on the
    -- RHS; bridge to `uLim` via `hUae`.
    have h := T.hConvU φ_F5 hmono w hφlim ψ
    -- `h : Tendsto (fun k => ∫ (seq.sol (φ_F5 k)).u · ψ) → ∫ ⇑w.2.1 · ψ`.
    -- Rewrite RHS via `hUae : uLim =ᵐ ⇑w.2.1`.
    have h_int_eq :
        Periodic.periodicIntegral
          (fun x => uLim x * (ψ : (Fin d → ℝ) → ℝ) x) =
        Periodic.periodicIntegral
          (fun x => (⇑w.2.1) x * (ψ : (Fin d → ℝ) → ℝ) x) := by
      unfold Periodic.periodicIntegral
      apply MeasureTheory.integral_congr_ae
      filter_upwards [hUae] with x hx
      rw [hx]
    rw [h_int_eq]
    exact h
  have hFiveDu :
      ∀ i, ∀ ψ : Periodic.SmoothPeriodic d,
        Tendsto
          (fun k => Periodic.periodicIntegral
              (fun x =>
                (seq.sol (φ_F5 k)).Du i x * (ψ : (Fin d → ℝ) → ℝ) x))
          atTop
          (𝓝 (Periodic.periodicIntegral
              (fun x => DuLim' i x * (ψ : (Fin d → ℝ) → ℝ) x))) := by
    intro i ψ
    have h := T.hConvDu φ_F5 hmono w hφlim i ψ
    have h_int_eq :
        Periodic.periodicIntegral
          (fun x => DuLim' i x * (ψ : (Fin d → ℝ) → ℝ) x) =
        Periodic.periodicIntegral
          (fun x => (⇑(w.2.2 i)) x * (ψ : (Fin d → ℝ) → ℝ) x) := by
      unfold Periodic.periodicIntegral
      apply MeasureTheory.integral_congr_ae
      filter_upwards [hDuLim'_ae i] with x hx
      rw [hx]
    rw [h_int_eq]
    exact h
  -- The `WeakLimitSelectorAE` requires `hConvU`/`hConvDu` for arbitrary
  -- strict-mono `φ`. We sequence-side use the F.5-subsequenced
  -- `seqRepU_sub n := (seq.sol (φ_F5 n)).u` and discharge for further
  -- `φ` by composing with `StrictMono.tendsto_atTop`.
  let selector :
      WeakLimitSelectorAE (d := d) γBarReal βBarReal w :=
    { mRep :=
        { rep := mLim
          periodic := hMlimPer
          ae_eq := hMae }
      uRep :=
        { rep := uLim
          periodic := hUlimPer
          ae_eq := hUae }
      DuRep := fun i =>
        { rep := DuLim' i
          periodic := hDuLim'_per i
          ae_eq := hDuLim'_ae i }
      hDuRep_memLp := hDuLim'_memLp1
      seqRepU := fun n => (seq.sol (φ_F5 n)).u
      seqRepDu := fun n i => (seq.sol (φ_F5 n)).Du i
      hSeqRepWeak := fun n i => (seq.sol (φ_F5 n)).hWeakDeriv i
      hConvU := by
        intro φ hφ ψ
        -- Compose F.5 tendsto with `φ.tendsto_atTop`.
        have hcomp := (hFiveU ψ).comp (hφ.tendsto_atTop)
        exact hcomp
      hConvDu := by
        intro φ hφ i ψ
        have hcomp := (hFiveDu i ψ).comp (hφ.tendsto_atTop)
        exact hcomp
      hmRep_nonneg := hMlim_nonneg }
  -- ===== Step F: wrap. =====
  exact ⟨{ idx := φ_F5
           idx_strict := hmono
           extraction := { w := w, selector := selector }
           hWeakSpace_tendsto := hφlim }⟩

/-- **Final assembly producer (HMinty-1 form).** Public wrapper around
the `Nonempty`-witness theorem, extracting a concrete
`WeakLimitSubsequenceData` via `Nonempty.some`. Exposes the F.5
strict-mono index `idx` and the abstract Banach-pair `WeakSpace`-tendsto
`hWeakSpace_tendsto` (Route-1 hook for HMinty-2). -/
noncomputable def weakLimitSubsequenceData_of_uniform_apriori
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
              γBarReal βBarReal βBarReal' γBarReal' V H DpH) :
    WeakLimitSubsequenceData (d := d) γBarReal βBarReal seq :=
  (palomar_RegularizedSequence_nonempty_weakLimitSubsequenceData_of_uniform_apriori
    (βBarReal' := βBarReal') (γBarReal' := γBarReal') hExp seq).some

/-- **Final assembly producer (legacy surface).** Backward-compatible
extractor returning `WeakLimitExtractionAE`. Post-HMinty-1, this is
just the `.extraction` projection of
`weakLimitSubsequenceData_of_uniform_apriori`, so existing callers
continue to work without change. The richer data (F.5 index + abstract
weak-tendsto) is available via `weakLimitSubsequenceData_of_uniform_apriori`
for HMinty-2 and onward. -/
noncomputable def weakLimitExtractionAE_of_uniform_apriori
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
              γBarReal βBarReal βBarReal' γBarReal' V H DpH) :
    WeakLimitExtractionAE (d := d) γBarReal βBarReal :=
  (weakLimitSubsequenceData_of_uniform_apriori
    (βBarReal' := βBarReal') (γBarReal' := γBarReal') hExp seq).extraction

/-- **Sanity check** for `weakLimitExtractionAE_of_uniform_apriori`:
the producer constructs a `WeakLimitExtractionAE` from `(hExp, seq)`
without any residue parameter. -/
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
              γBarReal βBarReal βBarReal' γBarReal' V H DpH) :
    WeakLimitExtractionAE (d := d) γBarReal βBarReal :=
  weakLimitExtractionAE_of_uniform_apriori
    (βBarReal' := βBarReal') (γBarReal' := γBarReal') hExp seq

/-! ## HMinty-2 — `ExtractedWeakPairingData` producer

Per `infra-P5-T10-v7-HMinty-2-ExtractedWeakPairingData` (Route-1, per
`docs/HMINTY_ROUTE.md`). The producer below packages, from a single
`RegularizedSequenceData`:

* an extracted (subsequenced) `RegularizedSequenceData`,
* the AE-native `WeakLimitInputBundleAE` over that subsequence,
* three **universal** `WeakConvPairing_universal` certificates
  (one each for `m`, `u`, `Du i`),

via the Route-1 bridge `weakConvPairing_universal_of_toWeakSpace_conv`
(Banach/WeakPairing.lean:454) fed by the abstract product Banach-pair
weak-tendsto carried in `WeakLimitSubsequenceData.hWeakSpace_tendsto`.

The three universal pairings replace the role of the soon-to-be-dropped
`h_minty_limit_auth` auth parameter in `T10PaperResidues`; see HMinty-3
for the rewire. -/

namespace WeakLimitSubsequenceData

variable {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
variable [Fact (1 ≤ ENNReal.ofReal βBarReal)]
variable [Fact (1 ≤ ENNReal.ofReal γBarReal)]
variable {V : (Fin d → ℝ) → ℝ}
variable {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
variable {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}

/-- **HMinty-2 (step A3a).** Reindexed `RegularizedSequenceData` along
`D.idx`: the operating sequence after extraction. By definition
`(D.seqSub.sol n) = (seq.sol (D.idx n))` and similarly for `epsSeq`. -/
noncomputable def seqSub
    {seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH}
    (D : WeakLimitSubsequenceData (d := d) γBarReal βBarReal seq) :
    RegularizedSequenceData (d := d)
      γBarReal βBarReal βBarReal' γBarReal' V H DpH :=
  seq.subseq D.idx D.idx_strict.tendsto_atTop

/-- **HMinty-2 (step A3b).** AE-native input bundle at the cluster
point `D.extraction.w`, with sequence-side fields sourced from the
subsequenced `seqSub`. The bundle's `seqRepU n = (D.seqSub.sol n).u`
and `seqRepDu n i = (D.seqSub.sol n).Du i` hold definitionally because
the `WeakLimitSubsequenceData` was constructed so that
`D.extraction.selector.seqRepU n = (seq.sol (D.idx n)).u`. -/
noncomputable def toWeakLimitInputBundleAE
    {seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH}
    (D : WeakLimitSubsequenceData (d := d) γBarReal βBarReal seq)
    (hExp : SimplePowerExponentFacts γBarReal
              (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
              (ENNReal.ofReal βBarReal')) :
    WeakLimitInputBundleAE (d := d) γBarReal βBarReal := by
  -- Step 1: derive `0 < βBarReal` from `1 < ENNReal.ofReal βBarReal`.
  have h_one_lt_βBarReal : (1 : ℝ) < βBarReal := by
    by_contra hle
    push_neg at hle
    have h1 : ENNReal.ofReal βBarReal ≤ (1 : ℝ≥0∞) := by
      calc ENNReal.ofReal βBarReal
          ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal hle
        _ = 1 := ENNReal.ofReal_one
    exact absurd hExp.βBar_one_lt (not_lt_of_ge h1)
  have h_βBarReal_pos : (0 : ℝ) < βBarReal := by linarith
  -- Step 2: real-side positivity of `βBarReal'` from `hExp`.
  have h_one_lt_βBar' : (1 : ℝ≥0∞) < ENNReal.ofReal βBarReal' :=
    hExp.betaBar'_one_lt
  have h_βBarReal'_pos : (0 : ℝ) < βBarReal' := by
    by_contra hle
    push_neg at hle
    have h_zero : ENNReal.ofReal βBarReal' = 0 :=
      ENNReal.ofReal_eq_zero.mpr hle
    rw [h_zero] at h_one_lt_βBar'
    exact absurd h_one_lt_βBar' (by simp)
  have h_one_le_βBar' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal βBarReal' :=
    h_one_lt_βBar'.le
  haveI : Fact (1 ≤ ENNReal.ofReal βBarReal') := ⟨h_one_le_βBar'⟩
  -- Step 3: γ-side conjugate setup.
  have h_one_lt_γBarReal : (1 : ℝ) < γBarReal := hExp.γBar_one_lt_real
  have h_γBarReal_pos : (0 : ℝ) < γBarReal := by linarith
  let γBarPrimeReal : ℝ := γBarReal / (γBarReal - 1)
  have h_γBar_minus_one_pos : (0 : ℝ) < γBarReal - 1 := by linarith
  have h_γBarPrimeReal_pos : (0 : ℝ) < γBarPrimeReal :=
    div_pos h_γBarReal_pos h_γBar_minus_one_pos
  have h_one_lt_γBarPrimeReal : (1 : ℝ) < γBarPrimeReal := by
    show (1 : ℝ) < γBarReal / (γBarReal - 1)
    rw [lt_div_iff₀ h_γBar_minus_one_pos, one_mul]
    linarith
  have h_one_le_γBarPrime : (1 : ℝ≥0∞) ≤ ENNReal.ofReal γBarPrimeReal := by
    have h1 : ENNReal.ofReal 1 ≤ ENNReal.ofReal γBarPrimeReal :=
      ENNReal.ofReal_le_ofReal h_one_lt_γBarPrimeReal.le
    simpa using h1
  haveI : Fact (1 ≤ ENNReal.ofReal γBarPrimeReal) := ⟨h_one_le_γBarPrime⟩
  -- Conjugacy instances (needed by `lpSobolev_product_isReflexive`).
  have h_βBar_toReal_eq : (ENNReal.ofReal βBarReal).toReal = βBarReal :=
    ENNReal.toReal_ofReal h_βBarReal_pos.le
  have h_βBar'_toReal_eq : (ENNReal.ofReal βBarReal').toReal = βBarReal' :=
    ENNReal.toReal_ofReal h_βBarReal'_pos.le
  have hβConj_real : Real.HolderConjugate βBarReal βBarReal' := by
    have := hExp.βConj
    rw [h_βBar_toReal_eq, h_βBar'_toReal_eq] at this
    exact this
  haveI hβConj_enn : ENNReal.HolderConjugate
      (ENNReal.ofReal βBarReal) (ENNReal.ofReal βBarReal') :=
    Real.HolderConjugate.ennrealOfReal hβConj_real
  have h_γBar_toReal_eq : (ENNReal.ofReal γBarReal).toReal = γBarReal :=
    ENNReal.toReal_ofReal h_γBarReal_pos.le
  have hγConj_real : Real.HolderConjugate γBarReal γBarPrimeReal := by
    have := hExp.γConj
    rw [h_γBar_toReal_eq] at this
    show Real.HolderConjugate γBarReal (γBarReal / (γBarReal - 1))
    exact this
  haveI hγConj_enn : ENNReal.HolderConjugate
      (ENNReal.ofReal γBarReal) (ENNReal.ofReal γBarPrimeReal) :=
    Real.HolderConjugate.ennrealOfReal hγConj_real
  -- Step 4: `βBar ≠ ∞` and `γBar ≠ ∞`.
  have h_βBar_ne_top : (ENNReal.ofReal βBarReal) ≠ ∞ :=
    ENNReal.ofReal_ne_top
  have h_γBar_ne_top : (ENNReal.ofReal γBarReal) ≠ ∞ :=
    ENNReal.ofReal_ne_top
  -- Step 5: reflexivity & separability via the discharged infrastructure.
  have hRefl :
      Periodic.IsReflexiveNormedSpace
        (Periodic.LpPer (ENNReal.ofReal βBarReal) d
          × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d) :=
    Periodic.lpSobolev_product_isReflexive (d := d)
      (ENNReal.ofReal βBarReal) (ENNReal.ofReal βBarReal')
      (ENNReal.ofReal γBarReal) (ENNReal.ofReal γBarPrimeReal)
      hExp.βBar_one_lt h_βBar_ne_top hExp.gammaBar_one_lt h_γBar_ne_top
  have hSep :
      TopologicalSpace.SeparableSpace
        (StrongDual ℝ
          (Periodic.LpPer (ENNReal.ofReal βBarReal) d
            × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d)) :=
    Periodic.lpSobolev_product_strongDual_separable (d := d)
      (ENNReal.ofReal βBarReal) (ENNReal.ofReal βBarReal')
      (ENNReal.ofReal γBarReal) (ENNReal.ofReal γBarPrimeReal)
      hExp.βBar_one_lt h_βBar_ne_top hExp.gammaBar_one_lt h_γBar_ne_top
  -- Step 6: assemble the AE-native bundle from `D.extraction.selector`
  -- and `D.extraction.w`. The sequence-side fields are unconstrained by
  -- the bundle type; we wire them through from `D.extraction.selector`
  -- (which already has them indexed at `D.idx`, hence aligned with
  -- `D.seqSub` by definitional equality on `seq.subseq`).
  exact
    { hRefl := hRefl
      hSep := hSep
      w := D.extraction.w
      mRep := D.extraction.selector.mRep
      uRep := D.extraction.selector.uRep
      DuRep := D.extraction.selector.DuRep
      hDuRep_memLp := D.extraction.selector.hDuRep_memLp
      seqRepU := D.extraction.selector.seqRepU
      seqRepDu := D.extraction.selector.seqRepDu
      hSeqRepWeak := D.extraction.selector.hSeqRepWeak
      hConvU := D.extraction.selector.hConvU
      hConvDu := D.extraction.selector.hConvDu
      hmRep_nonneg := D.extraction.selector.hmRep_nonneg
      hMlimPer := D.extraction.selector.mRep.periodic
      hUlimPer := D.extraction.selector.uRep.periodic
      hDuLim_periodic := fun i => (D.extraction.selector.DuRep i).periodic
      hmLim_memLp := D.extraction.selector.hmLim_memLp
      huLim_sob :=
        ⟨D.extraction.selector.huLim_memLp,
          ⟨fun i => (D.extraction.selector.DuRep i).rep,
            fun i =>
              Periodic.HasWeakDerivPer.of_weak_limit
                (i := i) (u_n := D.extraction.selector.seqRepU)
                (Du_n := fun n => D.extraction.selector.seqRepDu n i)
                (u := D.extraction.selector.uRep.rep)
                (Du := (D.extraction.selector.DuRep i).rep)
                (D.extraction.selector.hDuRep_memLp i)
                (fun n => D.extraction.selector.hSeqRepWeak n i)
                (by
                  intro ψ
                  have h := D.extraction.selector.hConvU id strictMono_id ψ
                  simpa using h)
                (by
                  intro ψ
                  have h := D.extraction.selector.hConvDu id strictMono_id i ψ
                  simpa using h)⟩⟩ }

end WeakLimitSubsequenceData

/-! ### `ExtractedWeakPairingData` structure and producer

The structure bundles `(seq, wkBundle, h_weak_{m,u,Du})` at paper
Hölder exponents `(hpqBeta_paper hpow, hpqGamma_paper hpow)`. The
producer chains:

* HMinty-1's `weakLimitSubsequenceData_of_uniform_apriori` for `D`;
* `D.seqSub`, `D.toWeakLimitInputBundleAE hExp` for `(seq, wkBundle)`;
* `weakConvPairing_universal_of_toWeakSpace_conv` for each universal
  pairing, fed by `D.hWeakSpace_tendsto` composed with the projection
  CLM (`fst`, `snd ∘ fst`, `(proj i) ∘ snd ∘ snd`). -/

/-- **HMinty-2 (step A4 surface).** Operating-data bundle returned by
`extractedWeakPairingData_of_regularizedSequence`. -/
structure ExtractedWeakPairingData
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (seq0 : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH) where
  /-- The extracted subsequence — operating data for downstream. -/
  seq : RegularizedSequenceData (d := d)
          γBarReal βBarReal βBarReal' γBarReal' V H DpH
  /-- The reindexing function `idx : ℕ → ℕ` from the original
  full sequence `seq0` to the extracted subsequence `seq`. Used by
  the chain consumer (HMinty-3 rewire) to reindex any per-`k` data
  that was originally indexed by the full-sequence index (such as
  the integrated apriori sum bound). -/
  idx : ℕ → ℕ
  /-- Pointwise reindexing of the m-component of the regularised
  bare solution: `(seq.sol k).m = (seq0.sol (idx k)).m`. Used by
  the chain consumer (HMinty-3) to reindex the apriori-sum bound. -/
  seq_m_eq : ∀ k : ℕ, (seq.sol k).m = (seq0.sol (idx k)).m
  /-- Pointwise reindexing of the u-component of the regularised
  bare solution: `(seq.sol k).u = (seq0.sol (idx k)).u`. -/
  seq_u_eq : ∀ k : ℕ, (seq.sol k).u = (seq0.sol (idx k)).u
  /-- Pointwise reindexing of the Du-component of the regularised
  bare solution: `(seq.sol k).Du i = (seq0.sol (idx k)).Du i`. -/
  seq_Du_eq : ∀ (k : ℕ) (i : Fin d),
    (seq.sol k).Du i = (seq0.sol (idx k)).Du i
  /-- The AE-native limit bundle on `seq`. -/
  wkBundle : WeakLimitInputBundleAE (d := d) γBarReal βBarReal
  /-- Universal weak-pairing for the `m`-side, at paper Hölder
  exponents `(betaBar hpow.β, betaBar' hpow.β)`. -/
  h_weak_m :
    WeakConvPairing_universal
      (hpqBeta_paper hpow)
      (fun k => (seq.sol k).m) wkBundle.mLim
  /-- Universal weak-pairing for the `u`-side, at paper Hölder
  exponents `(gammaBar hpow.α hpow.β, gammaBar' hpow.α hpow.β)`. -/
  h_weak_u :
    WeakConvPairing_universal
      (hpqGamma_paper hpow)
      (fun k => (seq.sol k).u) wkBundle.uLim
  /-- Universal weak-pairing for each gradient component, at paper
  Hölder exponents `(gammaBar hpow.α hpow.β, gammaBar' hpow.α hpow.β)`. -/
  h_weak_Du : ∀ i,
    WeakConvPairing_universal
      (hpqGamma_paper hpow)
      (fun k => (seq.sol k).Du i) (wkBundle.DuLim i)

/-- **HMinty-2 — main producer (step A4).** Compose:
* HMinty-1's `weakLimitSubsequenceData_of_uniform_apriori` to extract
  a weakly converging subsequence `D`;
* `D.seqSub` and `D.toWeakLimitInputBundleAE hExp` to get the
  operating sequence and AE-native bundle;
* the Route-1 bridge `weakConvPairing_universal_of_toWeakSpace_conv`
  applied to each component projection of `D.hWeakSpace_tendsto`.

The paper-form exponent equations `hβBarPaper`, `hβBar'Paper`,
`hγBarPaper`, `hγBar'Paper` reconcile the *structural* `βBarReal,
γBarReal, βBarReal', γBarReal'` parameters with the *paper* exponents
`(betaBar hpow.β, betaBar' hpow.β, gammaBar hpow.α hpow.β,
gammaBar' hpow.α hpow.β)` that appear in `hpqBeta_paper hpow` and
`hpqGamma_paper hpow`. They are pure-data equations supplied by the
chain caller (`simplePowerThinChain_of_paperHypotheses` already has
them — see BanachBridge.lean:2711–2715). -/
noncomputable def extractedWeakPairingData_of_regularizedSequence
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (hExp : SimplePowerExponentFacts γBarReal
              (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
              (ENNReal.ofReal βBarReal'))
    (hβBarPaper : βBarReal = hpow.β + 1)
    (hβBar'Paper : βBarReal' = (hpow.β + 1) / hpow.β)
    (hγBarPaper : γBarReal = hpow.α * (hpow.β + 1) / hpow.β)
    (hγBar'Paper : γBarReal' = hpow.α * (hpow.β + 1) / hpow.β /
                                 (hpow.α * (hpow.β + 1) / hpow.β - 1))
    (seq0 : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH) :
    ExtractedWeakPairingData (d := d) hpow seq0 := by
  -- ===== Step 0: paper-exponent translation. =====
  -- Identify the paper-conjugate exponents in `hpq*_paper hpow` with
  -- the structural ones via the supplied equations.
  have hβ_paper_eq : Hamiltonian.betaBar hpow.β = βBarReal := by
    unfold Hamiltonian.betaBar; linarith
  have hβ'_paper_eq : Hamiltonian.betaBar' hpow.β = βBarReal' := by
    unfold Hamiltonian.betaBar'
    rw [hβBar'Paper]
  have hγ_paper_eq : Hamiltonian.gammaBar hpow.α hpow.β = γBarReal := by
    unfold Hamiltonian.gammaBar
    linarith
  have hγ'_paper_eq :
      Hamiltonian.gammaBar' hpow.α hpow.β = γBarReal' := by
    unfold Hamiltonian.gammaBar' Hamiltonian.gammaBar
    rw [hγBar'Paper]
  -- ===== Step 1: invoke HMinty-1 producer. =====
  let D : WeakLimitSubsequenceData (d := d) γBarReal βBarReal seq0 :=
    weakLimitSubsequenceData_of_uniform_apriori
      (βBarReal' := βBarReal') (γBarReal' := γBarReal') hExp seq0
  -- ===== Step 2: reindexed sequence + bundle. =====
  let seq : RegularizedSequenceData (d := d)
              γBarReal βBarReal βBarReal' γBarReal' V H DpH := D.seqSub
  let wkBundle : WeakLimitInputBundleAE (d := d) γBarReal βBarReal :=
    D.toWeakLimitInputBundleAE hExp
  -- ===== Step 3: discharge β/γ-side Fact and HolderConjugate locally. =====
  have h_one_lt_βBarReal : (1 : ℝ) < βBarReal := by
    by_contra hle
    push_neg at hle
    have h1 : ENNReal.ofReal βBarReal ≤ (1 : ℝ≥0∞) := by
      calc ENNReal.ofReal βBarReal
          ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal hle
        _ = 1 := ENNReal.ofReal_one
    exact absurd hExp.βBar_one_lt (not_lt_of_ge h1)
  have h_βBarReal_pos : (0 : ℝ) < βBarReal := by linarith
  have h_one_lt_βBar' : (1 : ℝ≥0∞) < ENNReal.ofReal βBarReal' :=
    hExp.betaBar'_one_lt
  have h_βBarReal'_pos : (0 : ℝ) < βBarReal' := by
    by_contra hle
    push_neg at hle
    have h_zero : ENNReal.ofReal βBarReal' = 0 :=
      ENNReal.ofReal_eq_zero.mpr hle
    rw [h_zero] at h_one_lt_βBar'
    exact absurd h_one_lt_βBar' (by simp)
  have h_one_le_βBar' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal βBarReal' :=
    h_one_lt_βBar'.le
  haveI hFactβ' : Fact (1 ≤ ENNReal.ofReal βBarReal') := ⟨h_one_le_βBar'⟩
  have h_one_lt_γBarReal : (1 : ℝ) < γBarReal := hExp.γBar_one_lt_real
  have h_γBarReal_pos : (0 : ℝ) < γBarReal := by linarith
  have h_γBar_minus_one_pos : (0 : ℝ) < γBarReal - 1 := by linarith
  have h_γBarReal'_pos : (0 : ℝ) < γBarReal' := by
    rw [hγBar'Paper]
    -- `γBarReal' = γBarReal / (γBarReal - 1)`, positive by Step 1.
    have hnum_pos : (0 : ℝ) < hpow.α * (hpow.β + 1) / hpow.β :=
      hγBarPaper ▸ h_γBarReal_pos
    have hden_pos : (0 : ℝ) < hpow.α * (hpow.β + 1) / hpow.β - 1 :=
      hγBarPaper ▸ h_γBar_minus_one_pos
    exact div_pos hnum_pos hden_pos
  have h_βBar_toReal_eq : (ENNReal.ofReal βBarReal).toReal = βBarReal :=
    ENNReal.toReal_ofReal h_βBarReal_pos.le
  have h_βBar'_toReal_eq : (ENNReal.ofReal βBarReal').toReal = βBarReal' :=
    ENNReal.toReal_ofReal h_βBarReal'_pos.le
  have h_γBar_toReal_eq : (ENNReal.ofReal γBarReal).toReal = γBarReal :=
    ENNReal.toReal_ofReal h_γBarReal_pos.le
  have h_γBar'_toReal_eq : (ENNReal.ofReal γBarReal').toReal = γBarReal' :=
    ENNReal.toReal_ofReal h_γBarReal'_pos.le
  have hβConj_real : Real.HolderConjugate βBarReal βBarReal' := by
    have := hExp.βConj
    rw [h_βBar_toReal_eq, h_βBar'_toReal_eq] at this
    exact this
  have hβConj_enn :
      ENNReal.HolderConjugate (ENNReal.ofReal βBarReal)
        (ENNReal.ofReal βBarReal') :=
    Real.HolderConjugate.ennrealOfReal hβConj_real
  haveI hHCβ : ENNReal.HolderConjugate (ENNReal.ofReal βBarReal)
            (ENNReal.ofReal βBarReal') := hβConj_enn
  have hγConj_real : Real.HolderConjugate γBarReal γBarReal' := by
    -- `hExp.γConj : γBarReal.HolderConjugate (γBarReal / (γBarReal - 1))`.
    -- Goal: `γBarReal.HolderConjugate γBarReal'`. Rewrite the goal's
    -- `γBarReal'` to `γBarReal / (γBarReal - 1)`.
    have hγ'_alt : γBarReal' = γBarReal / (γBarReal - 1) := by
      -- `γBarReal = hpow.α * (β + 1) / β = γBarPaper`; substituting,
      -- `γBarReal' = γBarReal / (γBarReal - 1)` def-eq via `hγBar'Paper`.
      rw [hγBar'Paper, hγBarPaper]
    rw [hγ'_alt]
    have := hExp.γConj
    rw [h_γBar_toReal_eq] at this
    exact this
  have hγConj_enn :
      ENNReal.HolderConjugate (ENNReal.ofReal γBarReal)
        (ENNReal.ofReal γBarReal') :=
    Real.HolderConjugate.ennrealOfReal hγConj_real
  haveI hHCγ : ENNReal.HolderConjugate (ENNReal.ofReal γBarReal)
            (ENNReal.ofReal γBarReal') := hγConj_enn
  -- `Fact (1 ≤ ofReal γBarReal')` from `HolderConjugate.symm.lt`.
  haveI hFactγ' : Fact (1 ≤ ENNReal.ofReal γBarReal') := by
    refine ⟨?_⟩
    have h1 : ENNReal.ofReal 1 ≤ ENNReal.ofReal γBarReal' :=
      ENNReal.ofReal_le_ofReal hγConj_real.symm.lt.le
    simpa using h1
  -- AE-coincidence between bare components and Lp coercions.
  have hcoeM : ∀ n,
      (seq.sol n).m
        =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
          (⇑((seq.sol n).toBanachPair.1) : (Fin d → ℝ) → ℝ) := by
    intro n
    -- `(seq.sol n).toBanachPair.1 = (seq.sol n).hmLp.toLp` def-eq.
    exact (MeasureTheory.MemLp.coeFn_toLp (seq.sol n).hmLp).symm
  have hcoeU : ∀ n,
      (seq.sol n).u
        =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
          (⇑((seq.sol n).toBanachPair.2.1) : (Fin d → ℝ) → ℝ) := by
    intro n
    exact (MeasureTheory.MemLp.coeFn_toLp (seq.sol n).huLp).symm
  have hcoeDu : ∀ n i,
      (seq.sol n).Du i
        =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
          (⇑((seq.sol n).toBanachPair.2.2 i) : (Fin d → ℝ) → ℝ) := by
    intro n i
    exact (MeasureTheory.MemLp.coeFn_toLp ((seq.sol n).hDuLp i)).symm
  -- AE-coincidence of bare-limit with Lp coercions at the chosen `w`.
  have hLimM : wkBundle.mLim
        =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
          (⇑(wkBundle.w.1) : (Fin d → ℝ) → ℝ) := wkBundle.mRep.ae_eq
  have hLimU : wkBundle.uLim
        =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
          (⇑(wkBundle.w.2.1) : (Fin d → ℝ) → ℝ) := wkBundle.uRep.ae_eq
  have hLimDu : ∀ i, wkBundle.DuLim i
        =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
          (⇑(wkBundle.w.2.2 i) : (Fin d → ℝ) → ℝ) :=
    fun i => (wkBundle.DuRep i).ae_eq
  -- The product weak-tendsto, on `seq = D.seqSub` directly.
  -- `D.hWeakSpace_tendsto : Tendsto (fun k => toWeakSpace ℝ ... ((seq0.sol (D.idx k)).toBanachPair)) → ...`
  -- and `(seq0.sol (D.idx k)).toBanachPair = (D.seqSub.sol k).toBanachPair` def-eq.
  have hWeak_pair :
      Tendsto
        (fun k => (toWeakSpace ℝ
          (Periodic.LpPer (ENNReal.ofReal βBarReal) d
            × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d))
            ((seq.sol k).toBanachPair))
        atTop
        (𝓝 ((toWeakSpace ℝ
          (Periodic.LpPer (ENNReal.ofReal βBarReal) d
            × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d))
              wkBundle.w)) := D.hWeakSpace_tendsto
  -- Injectivity facts used by `WeakBilin.tendsto_iff_forall_eval_tendsto`.
  have h_inj_prod :
      Function.Injective
        ⇑(topDualPairing ℝ
            (Periodic.LpPer (ENNReal.ofReal βBarReal) d
              × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d)).flip := by
    intro x y hxy
    refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 ?_
    intro g
    have h_app := congrArg
      (fun (L : ((Periodic.LpPer (ENNReal.ofReal βBarReal) d
                    × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d)
                      →L[ℝ] ℝ) →ₗ[ℝ] ℝ) => L g) hxy
    simpa using h_app
  -- Universal-Λ form on the product Banach pair (from `hWeak_pair`).
  have hΛ_prod :
      ∀ Λ : (Periodic.LpPer (ENNReal.ofReal βBarReal) d
                × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d) →L[ℝ] ℝ,
        Tendsto (fun n => Λ ((seq.sol n).toBanachPair)) atTop
          (𝓝 (Λ wkBundle.w)) := by
    intro Λ
    have hh := (WeakBilin.tendsto_iff_forall_eval_tendsto
      (B := (topDualPairing ℝ
              (Periodic.LpPer (ENNReal.ofReal βBarReal) d
                × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d)).flip)
      h_inj_prod).mp hWeak_pair Λ
    simpa using! hh
  -- ===== Helper for each component: invoke
  -- `weakConvPairing_universal_of_weakDual_conv`. =====
  -- The CLM signature requires `Fact (1 ≤ ofReal p)` for the
  -- *paper* p; we have it for the *structural* p. We bridge with the
  -- paper-form equation. Same for `q`.
  haveI hFact_paperβ : Fact (1 ≤ ENNReal.ofReal (Hamiltonian.betaBar hpow.β)) := by
    rw [hβ_paper_eq]; infer_instance
  haveI hFact_paperβ' : Fact (1 ≤ ENNReal.ofReal (Hamiltonian.betaBar' hpow.β)) := by
    rw [hβ'_paper_eq]; infer_instance
  haveI hFact_paperγ : Fact (1 ≤ ENNReal.ofReal (Hamiltonian.gammaBar hpow.α hpow.β)) := by
    rw [hγ_paper_eq]; infer_instance
  haveI hFact_paperγ' : Fact (1 ≤ ENNReal.ofReal (Hamiltonian.gammaBar' hpow.α hpow.β)) := by
    rw [hγ'_paper_eq]; infer_instance
  -- ===== m-side: build `WeakConvPairing_universal (hpqBeta_paper hpow) m _ _`. =====
  -- Strategy: rewrite the universal predicate to the structural βBar
  -- via `hβ_paper_eq`/`hβ'_paper_eq`, then discharge there.
  have h_weak_m :
      WeakConvPairing_universal
        (d := d) (hpqBeta_paper hpow)
        (fun k => (seq.sol k).m) wkBundle.mLim := by
    -- Unfold the universal predicate to its definition.
    intro φ hφ
    -- `hφ : MemLpPer (ofReal (betaBar' hpow.β)) φ`.
    -- Rewrite to `MemLpPer (ofReal βBarReal') φ` via `hβ'_paper_eq`.
    have hφ' : MemLpPer (d := d) (ENNReal.ofReal βBarReal') φ := by
      rw [← hβ'_paper_eq]; exact hφ
    -- The universal weak-pairing certificate at structural exponents.
    have h_struct :
        WeakConvPairing_universal (d := d) hβConj_real
          (fun k => (seq.sol k).m) wkBundle.mLim := by
      refine weakConvPairing_universal_of_weakDual_conv hβConj_real
        (F_n := fun k => (seq.sol k).toBanachPair.1)
        (F := wkBundle.w.1)
        ?_ ?_ ?_ ?_ ?_
      · -- hF_n_ae : `(seq.sol k).m =ᵐ ⇑((seq.sol k).toBanachPair.1)`.
        intro n; exact hcoeM n
      · -- hF_ae : `wkBundle.mLim =ᵐ ⇑(wkBundle.w.1)`.
        exact hLimM
      · -- universal-Λ form on the single factor, from the product one
        -- via composition with `fst_clm`.
        intro Λ
        -- `fst_clm` extracts the first factor.
        set fst_clm : (Periodic.LpPer (ENNReal.ofReal βBarReal) d
                        × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d)
                          →L[ℝ] Periodic.LpPer (ENNReal.ofReal βBarReal) d :=
          ContinuousLinearMap.fst ℝ _ _ with hfst
        have := hΛ_prod (Λ.comp fst_clm)
        -- `(Λ.comp fst_clm) z = Λ z.1`.
        simpa [hfst] using this
      · -- Λφ : caller-supplied integral-pairing CLM.
        intro φ' hφ'
        -- The CLM `G ↦ ∫ G · φ'`.
        exact ((ContinuousLinearMap.mul ℝ ℝ).lpPairing
          (μ := MeasureTheory.Measure.restrict MeasureTheory.volume
                  (UnitCube d))
          (ENNReal.ofReal βBarReal)
          (ENNReal.ofReal βBarReal')).flip (Periodic.MemLpPer.toLp hφ')
      · -- Λφ_apply identity.
        intro φ' hφ' G
        change ((ContinuousLinearMap.mul ℝ ℝ).lpPairing
                  (μ := MeasureTheory.Measure.restrict MeasureTheory.volume
                          (UnitCube d))
                  (ENNReal.ofReal βBarReal)
                  (ENNReal.ofReal βBarReal')).flip
                  (Periodic.MemLpPer.toLp hφ') G
                = _
        rw [ContinuousLinearMap.flip_apply]
        have h := ContinuousLinearMap.lpPairing_eq_integral
          (μ := MeasureTheory.Measure.restrict MeasureTheory.volume
                  (UnitCube d))
          (p := ENNReal.ofReal βBarReal)
          (q := ENNReal.ofReal βBarReal')
          (B := ContinuousLinearMap.mul ℝ ℝ) G
          (Periodic.MemLpPer.toLp hφ')
        rw [h]
        apply integral_congr_ae
        have h_ae :
            ⇑(Periodic.MemLpPer.toLp hφ') =ᵐ[MeasureTheory.Measure.restrict
                MeasureTheory.volume (UnitCube d)]
              φ' :=
          MeasureTheory.MemLp.coeFn_toLp hφ'
        filter_upwards [h_ae] with x hx
        change (G x) * (⇑(Periodic.MemLpPer.toLp hφ') x)
            = (G x) * (φ' x)
        rw [hx]
    -- Specialise at `φ` to get the integral pairing.
    exact h_struct φ hφ'
  -- ===== u-side: same pattern with `snd ∘ fst` projection. =====
  have h_weak_u :
      WeakConvPairing_universal
        (d := d) (hpqGamma_paper hpow)
        (fun k => (seq.sol k).u) wkBundle.uLim := by
    intro φ hφ
    have hφ' : MemLpPer (d := d) (ENNReal.ofReal γBarReal') φ := by
      rw [← hγ'_paper_eq]; exact hφ
    have h_struct :
        WeakConvPairing_universal (d := d) hγConj_real
          (fun k => (seq.sol k).u) wkBundle.uLim := by
      refine weakConvPairing_universal_of_weakDual_conv hγConj_real
        (F_n := fun k => (seq.sol k).toBanachPair.2.1)
        (F := wkBundle.w.2.1)
        ?_ ?_ ?_ ?_ ?_
      · intro n; exact hcoeU n
      · exact hLimU
      · intro Λ
        set proj_clm : (Periodic.LpPer (ENNReal.ofReal βBarReal) d
                          × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d)
                            →L[ℝ] Periodic.LpPer (ENNReal.ofReal γBarReal) d :=
          (ContinuousLinearMap.fst ℝ
              (Periodic.LpPer (ENNReal.ofReal γBarReal) d)
              (Fin d → Periodic.LpPer (ENNReal.ofReal γBarReal) d)).comp
            (ContinuousLinearMap.snd ℝ _ _) with hproj
        have := hΛ_prod (Λ.comp proj_clm)
        simpa [hproj] using this
      · intro φ' hφ'
        exact ((ContinuousLinearMap.mul ℝ ℝ).lpPairing
          (μ := MeasureTheory.Measure.restrict MeasureTheory.volume
                  (UnitCube d))
          (ENNReal.ofReal γBarReal)
          (ENNReal.ofReal γBarReal')).flip (Periodic.MemLpPer.toLp hφ')
      · intro φ' hφ' G
        change ((ContinuousLinearMap.mul ℝ ℝ).lpPairing
                  (μ := MeasureTheory.Measure.restrict MeasureTheory.volume
                          (UnitCube d))
                  (ENNReal.ofReal γBarReal)
                  (ENNReal.ofReal γBarReal')).flip
                  (Periodic.MemLpPer.toLp hφ') G
                = _
        rw [ContinuousLinearMap.flip_apply]
        have h := ContinuousLinearMap.lpPairing_eq_integral
          (μ := MeasureTheory.Measure.restrict MeasureTheory.volume
                  (UnitCube d))
          (p := ENNReal.ofReal γBarReal)
          (q := ENNReal.ofReal γBarReal')
          (B := ContinuousLinearMap.mul ℝ ℝ) G
          (Periodic.MemLpPer.toLp hφ')
        rw [h]
        apply integral_congr_ae
        have h_ae :
            ⇑(Periodic.MemLpPer.toLp hφ') =ᵐ[MeasureTheory.Measure.restrict
                MeasureTheory.volume (UnitCube d)]
              φ' :=
          MeasureTheory.MemLp.coeFn_toLp hφ'
        filter_upwards [h_ae] with x hx
        change (G x) * (⇑(Periodic.MemLpPer.toLp hφ') x)
            = (G x) * (φ' x)
        rw [hx]
    exact h_struct φ hφ'
  -- ===== Du-side: per-coord, with `(proj i) ∘ snd ∘ snd` projection. =====
  have h_weak_Du : ∀ i,
      WeakConvPairing_universal
        (d := d) (hpqGamma_paper hpow)
        (fun k => (seq.sol k).Du i) (wkBundle.DuLim i) := by
    intro i φ hφ
    have hφ' : MemLpPer (d := d) (ENNReal.ofReal γBarReal') φ := by
      rw [← hγ'_paper_eq]; exact hφ
    have h_struct :
        WeakConvPairing_universal (d := d) hγConj_real
          (fun k => (seq.sol k).Du i) (wkBundle.DuLim i) := by
      refine weakConvPairing_universal_of_weakDual_conv hγConj_real
        (F_n := fun k => (seq.sol k).toBanachPair.2.2 i)
        (F := wkBundle.w.2.2 i)
        ?_ ?_ ?_ ?_ ?_
      · intro n; exact hcoeDu n i
      · exact hLimDu i
      · intro Λ
        set grad_clm : (Periodic.LpPer (ENNReal.ofReal βBarReal) d
                          × Periodic.SobolevPerLp 1 (ENNReal.ofReal γBarReal) d)
                            →L[ℝ] Periodic.LpPer (ENNReal.ofReal γBarReal) d :=
          (ContinuousLinearMap.proj (R := ℝ)
              (φ := fun _ : Fin d => Periodic.LpPer (ENNReal.ofReal γBarReal) d) i).comp
            ((ContinuousLinearMap.snd ℝ
                (Periodic.LpPer (ENNReal.ofReal γBarReal) d)
                (Fin d → Periodic.LpPer (ENNReal.ofReal γBarReal) d)).comp
              (ContinuousLinearMap.snd ℝ _ _)) with hgrad
        have := hΛ_prod (Λ.comp grad_clm)
        simpa [hgrad] using this
      · intro φ' hφ'
        exact ((ContinuousLinearMap.mul ℝ ℝ).lpPairing
          (μ := MeasureTheory.Measure.restrict MeasureTheory.volume
                  (UnitCube d))
          (ENNReal.ofReal γBarReal)
          (ENNReal.ofReal γBarReal')).flip (Periodic.MemLpPer.toLp hφ')
      · intro φ' hφ' G
        change ((ContinuousLinearMap.mul ℝ ℝ).lpPairing
                  (μ := MeasureTheory.Measure.restrict MeasureTheory.volume
                          (UnitCube d))
                  (ENNReal.ofReal γBarReal)
                  (ENNReal.ofReal γBarReal')).flip
                  (Periodic.MemLpPer.toLp hφ') G
                = _
        rw [ContinuousLinearMap.flip_apply]
        have h := ContinuousLinearMap.lpPairing_eq_integral
          (μ := MeasureTheory.Measure.restrict MeasureTheory.volume
                  (UnitCube d))
          (p := ENNReal.ofReal γBarReal)
          (q := ENNReal.ofReal γBarReal')
          (B := ContinuousLinearMap.mul ℝ ℝ) G
          (Periodic.MemLpPer.toLp hφ')
        rw [h]
        apply integral_congr_ae
        have h_ae :
            ⇑(Periodic.MemLpPer.toLp hφ') =ᵐ[MeasureTheory.Measure.restrict
                MeasureTheory.volume (UnitCube d)]
              φ' :=
          MeasureTheory.MemLp.coeFn_toLp hφ'
        filter_upwards [h_ae] with x hx
        change (G x) * (⇑(Periodic.MemLpPer.toLp hφ') x)
            = (G x) * (φ' x)
        rw [hx]
    exact h_struct φ hφ'
  -- ===== Step 4: package. =====
  exact
    { seq := seq
      idx := D.idx
      seq_m_eq := fun _ => rfl
      seq_u_eq := fun _ => rfl
      seq_Du_eq := fun _ _ => rfl
      wkBundle := wkBundle
      h_weak_m := h_weak_m
      h_weak_u := h_weak_u
      h_weak_Du := h_weak_Du }

/-! ## Minty/δ-limit bridge: `hVIeps_set ⇒ StrongVI_setForm`

Per the iter-396 task `infra-P4-strongVI-set-of-hVIeps-set-Minty`,
discharge the Minty/δ-limit bridge from the regularised set-form
VI field `RegularizedBareSolution.hVIeps_set` (operator at the
*test point* `(Du, S.indicator ρ, υ)`) to the paper's
`StrongVI_setForm` (operator at the *base point*
`(sol.Du, sol.m, sol.u)`).

The argument is the standard Minty step at a paper-fixed regularised
solution:

* Apply `sol.hVIeps_set` at `(Set.univ, ρ_n := sol.m + tn · 1_S, sol.u, sol.Du)`
  with `tn := 1/((n:ℝ)+1) > 0`.
* Identify the resulting test triple with `(0, tn · 1_S, 0)` via
  `Set.indicator_univ` and `mfgOperatorEpsPair_congr_ae`.
* Factor `tn` out of the test triple via
  `mfgOperatorEpsPair_test_smul`. Combined with `tn > 0`, drop `tn`.
* Pass `n → ∞` via the operator-continuity certificate `hCont`
  (authorised input, CONVENTIONS §8) to land at the operator
  evaluated at the base `(sol.Du, sol.m, sol.u)`.

The continuity certificate `hCont` is the analytic content
(continuity of `H` and `D_pH` in the third argument plus DCT on
the unit cube). Following the precedent of
`hVIeps_set_of_KAepsi_VI` (input side) and
`hVIeps_signed_of_KAepsi_VI`, we accept it as an authorised
hypothesis at this level. -/

open MeasureTheory Filter
open StationaryMFG.Periodic
open StationaryMFG.Theorems.SimplePower (StrongVI_setForm)

/-- **Minty/δ-limit bridge** from the regularised set-form VI field
`RegularizedBareSolution.hVIeps_set` to the paper's
`StrongVI_setForm` at the base point `(sol.Du, sol.m, sol.u)`.

The continuity certificate `hCont` (operator continuity in the
third argument along the strict-positive perturbation
`μ_n := sol.m + (1/(n+1)) · 1_S`) is taken as an authorised input
per CONVENTIONS §8; its discharge from `RegularityH` plus AC2
dominators follows the pattern of
`mfgOperatorEpsPair_tendsto_set_perturbation` and is filed as a
sibling task. -/
theorem strongVI_setForm_of_hVIeps_set
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal')
    -- `MemLpPer βBar 1_S` for every measurable `S` of finite
    -- restricted-cube measure (authorised: routine on a finite
    -- measure since `1_S` is bounded by `1`; threaded as input to
    -- avoid recomputing the indicator-`Lᵝ` machinery here).
    (hIndicMemLp :
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (volume.restrict (UnitCube d)) S < ∞ →
        MemLpPer (d := d) (ENNReal.ofReal βBarReal)
          (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ))))
    -- Authorised input (CONVENTIONS §8): operator-continuity along
    -- the strict-positive perturbation
    -- `ρ_n := sol.m + (1/(n+1)) · 1_S`, with the test triple held
    -- at `(0, 1_S, 0)` (no scaling). Filed under
    -- `infra-P4-mfg-operator-eps-tendsto-along-set-additive-perturbation`.
    (hCont :
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (volume.restrict (UnitCube d)) S < ∞ →
        Filter.Tendsto
          (fun n : ℕ =>
            mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε
              sol.Du
              (fun x => sol.m x + (1 / ((n : ℝ) + 1)) *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              sol.u
              (fun _ _ => (0 : ℝ))
              (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)))
              (fun _ => (0 : ℝ)))
          Filter.atTop
          (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                γBarReal ε
                sol.Du sol.m sol.u
                (fun _ _ => (0 : ℝ))
                (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)))
                (fun _ => (0 : ℝ))))) :
    StrongVI_setForm V H DpH γBarReal ε sol.Du sol.m sol.u := by
  classical
  intro S hS_meas hS_fin
  -- Shorthand.
  set f : (Fin d → ℝ) → ℝ :=
    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) with hf_def
  -- Per-`n` step: `0 ≤ mfgOperatorEpsPair … sol.Du (sol.m + tn · 1_S) sol.u 0 1_S 0`.
  have hStep :
      ∀ n : ℕ,
        0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε
              sol.Du
              (fun x => sol.m x + (1 / ((n : ℝ) + 1)) * f x)
              sol.u
              (fun _ _ => (0 : ℝ))
              f
              (fun _ => (0 : ℝ)) := by
    intro n
    -- `tn := 1/(n+1) > 0`.
    set tn : ℝ := 1 / ((n : ℝ) + 1) with htn_def
    have htn_pos : (0 : ℝ) < tn := by
      have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      exact div_pos one_pos hpos
    -- Pointwise nonnegativity of `f = 1_S`.
    have hf_nn : ∀ x, 0 ≤ f x := by
      intro x
      by_cases hxS : x ∈ S
      · simp [hf_def, Set.indicator_of_mem hxS]
      · simp [hf_def, Set.indicator_of_notMem hxS]
    -- Apply `sol.hVIeps_set` with `(Set.univ, ρ_n, sol.u, sol.Du)`,
    -- `ρ_n := sol.m + tn · f`.
    set ρ : (Fin d → ℝ) → ℝ := fun x => sol.m x + tn * f x with hρ_def
    -- `0 ≤ ρ` a.e. on the cube.
    have hρ_nn :
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          0 ≤ ρ x := by
      filter_upwards [sol.hmNonneg] with x hxm
      have hsmul_nn : 0 ≤ tn * f x := mul_nonneg htn_pos.le (hf_nn x)
      change 0 ≤ sol.m x + tn * f x
      linarith
    -- `MemLpPer βBar (Set.univ.indicator ρ)`: rewrite via
    -- `Set.indicator_univ`; `ρ ∈ Lᵝ` from `sol.hmLp + (tn · 1_S) ∈ Lᵝ`.
    have hf_memLp :
        MemLpPer (d := d) (ENNReal.ofReal βBarReal) f :=
      hIndicMemLp S hS_meas hS_fin
    have htn_f_memLp :
        MemLpPer (d := d) (ENNReal.ofReal βBarReal)
          (fun x => tn * f x) := by
      have h := MemLpPer.const_smul (c := tn) hf_memLp
      have heq : (tn • f : (Fin d → ℝ) → ℝ) = fun x => tn * f x := by
        funext x
        change tn • f x = tn * f x
        simp [smul_eq_mul]
      rw [heq] at h
      exact h
    have hρ_memLp :
        MemLpPer (d := d) (ENNReal.ofReal βBarReal) ρ := by
      have h := MemLpPer.add sol.hmLp htn_f_memLp
      have heq : (sol.m + (fun x => tn * f x) : (Fin d → ℝ) → ℝ)
                = ρ := by
        funext x; simp [hρ_def]
      rw [heq] at h
      exact h
    have hSρ_memLp :
        MemLpPer (d := d) (ENNReal.ofReal βBarReal)
          (Set.univ.indicator ρ) := by
      have heq : (Set.univ.indicator ρ : (Fin d → ℝ) → ℝ) = ρ := by
        funext x; simp
      rw [heq]; exact hρ_memLp
    -- `MemSobolevPer γBar sol.u`.
    have hu_memSob :
        MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) sol.u :=
      sol.memSobolevPer_u
    -- `MemLpPer γBar (sol.Du i)`.
    have hDu_memLp :
        ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (sol.Du i) :=
      sol.hDuLp
    -- The field invocation.
    have hVI := sol.hVIeps_set Set.univ MeasurableSet.univ ρ sol.u sol.Du
                  hρ_nn hSρ_memLp hu_memSob hDu_memLp sol.hWeakDeriv
    -- After invocation, `hVI` reads:
    --   0 ≤ mfgOperatorEpsPair γBar ε sol.Du (Set.univ.indicator ρ) sol.u
    --         (fun i x => sol.Du i x - sol.Du i x)
    --         (Set.univ.indicator ρ - sol.m) (sol.u - sol.u)
    -- Step 1: rewrite primal density via `Set.indicator_univ`
    -- (point-equality; OK to substitute throughout).
    have hρ_eq : Set.univ.indicator ρ = ρ := by
      funext x; simp
    rw [hρ_eq] at hVI
    -- Step 2: rewrite the test triple `(0, ρ - sol.m, 0)` via
    -- `mfgOperatorEpsPair_congr_ae`.
    have hDν_ae : ∀ i,
        (fun x => sol.Du i x - sol.Du i x)
          =ᵐ[volume.restrict (UnitCube d)]
        (fun _ : Fin d → ℝ => (0 : ℝ)) := by
      intro i
      refine Filter.Eventually.of_forall ?_
      intro x; simp
    have hη_ae :
        (ρ - sol.m)
          =ᵐ[volume.restrict (UnitCube d)]
        (fun x => tn * f x) := by
      refine Filter.Eventually.of_forall ?_
      intro x
      change ρ x - sol.m x = tn * f x
      simp [hρ_def]
    have hν_ae :
        (sol.u - sol.u)
          =ᵐ[volume.restrict (UnitCube d)]
        (fun _ : Fin d → ℝ => (0 : ℝ)) := by
      refine Filter.Eventually.of_forall ?_
      intro x; simp [Pi.sub_apply]
    have hcongr := mfgOperatorEpsPair_congr_ae
      (V := V) (H := H) (DpH := DpH)
      γBarReal ε
      sol.Du ρ sol.u
      (fun i x => sol.Du i x - sol.Du i x)
      (fun (_ : Fin d) (_ : Fin d → ℝ) => (0 : ℝ))
      (ρ - sol.m)
      (fun x => tn * f x)
      (sol.u - sol.u)
      (fun _ : Fin d → ℝ => (0 : ℝ))
      hDν_ae hη_ae hν_ae
    rw [hcongr] at hVI
    -- Step 3: factor `tn` out of the test triple via
    -- `mfgOperatorEpsPair_test_smul` (with `c = tn`,
    -- `Dν = (fun _ _ => 0)`, `η = f`, `ν = (fun _ => 0)`).
    have hsmul := mfgOperatorEpsPair_test_smul
      (V := V) (H := H) (DpH := DpH)
      γBarReal ε
      sol.Du ρ sol.u
      tn
      (fun (_ : Fin d) (_ : Fin d → ℝ) => (0 : ℝ))
      f
      (fun _ : Fin d → ℝ => (0 : ℝ))
    -- The `_test_smul` LHS has shape
    -- `(fun i => tn • (fun _ => 0))`, `(tn • f)`, `(tn • fun _ => 0)`.
    -- Identify these with the shapes appearing in `hVI`.
    have hDν_smul_eq :
        (fun i : Fin d => tn • ((fun (_ : Fin d) (_ : Fin d → ℝ) => (0 : ℝ)) i))
          = (fun (_ : Fin d) (_ : Fin d → ℝ) => (0 : ℝ)) := by
      funext i; funext x
      change tn • (0 : ℝ) = (0 : ℝ)
      simp
    have hη_smul_eq :
        (tn • f : (Fin d → ℝ) → ℝ) = fun x => tn * f x := by
      funext x
      change tn • f x = tn * f x
      simp [smul_eq_mul]
    have hν_smul_eq :
        (tn • (fun _ : Fin d → ℝ => (0 : ℝ)) : (Fin d → ℝ) → ℝ)
          = (fun _ : Fin d → ℝ => (0 : ℝ)) := by
      funext x
      change tn • (0 : ℝ) = (0 : ℝ)
      simp
    rw [hDν_smul_eq, hη_smul_eq, hν_smul_eq] at hsmul
    -- Now `hsmul`:
    --   mfgOperatorEpsPair γBar ε sol.Du ρ sol.u 0 (tn * f) 0
    --     = tn * mfgOperatorEpsPair γBar ε sol.Du ρ sol.u 0 f 0
    rw [hsmul] at hVI
    -- `hVI : 0 ≤ tn * mfgOperatorEpsPair … sol.Du ρ sol.u 0 f 0`,
    -- with `tn > 0`. Divide by `tn` via `mul_nonneg_iff_of_pos_left`.
    have hVI' :
        0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε
              sol.Du ρ sol.u
              (fun _ _ => (0 : ℝ))
              f
              (fun _ => (0 : ℝ)) :=
      (mul_nonneg_iff_of_pos_left htn_pos).mp hVI
    -- ρ is exactly `fun x => sol.m x + tn * f x`.
    exact hVI'
  -- Pass `n → ∞` via `hCont`.
  exact ge_of_tendsto' (hCont S hS_meas hS_fin) hStep

/-! ### Unit example for `strongVI_setForm_of_hVIeps_set`

Type-shape pin: from a `RegularizedBareSolution` plus the two
authorised inputs (`hIndicMemLp` and `hCont`), `strongVI_setForm_of_hVIeps_set`
delivers `StrongVI_setForm V H DpH γBar ε sol.Du sol.m sol.u`. -/
example
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal')
    (hIndicMemLp :
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (volume.restrict (UnitCube d)) S < ∞ →
        MemLpPer (d := d) (ENNReal.ofReal βBarReal)
          (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ))))
    (hCont :
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (volume.restrict (UnitCube d)) S < ∞ →
        Filter.Tendsto
          (fun n : ℕ =>
            mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε
              sol.Du
              (fun x => sol.m x + (1 / ((n : ℝ) + 1)) *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              sol.u
              (fun _ _ => (0 : ℝ))
              (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)))
              (fun _ => (0 : ℝ)))
          Filter.atTop
          (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                γBarReal ε
                sol.Du sol.m sol.u
                (fun _ _ => (0 : ℝ))
                (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)))
                (fun _ => (0 : ℝ))))) :
    StrongVI_setForm V H DpH γBarReal ε sol.Du sol.m sol.u :=
  strongVI_setForm_of_hVIeps_set sol hIndicMemLp hCont

/-! ### Phase 2 of expert post-iter-412 plan — package the two
Minty-bridge inputs

Per `infra-P4-rewire-hStrongVI_set-via-strongVI_setForm_of_hVIeps_set`,
package the two authorised inputs (`hIndicMemLp` and `hCont`) of
`strongVI_setForm_of_hVIeps_set` into a single bundle
`SetAdditiveContinuityInputs sol`. The wrapper
`hStrongVI_set_of_regularized_solution` then derives the paper's
`StrongVI_setForm` field at `(sol.Du, sol.m, sol.u)` from this
bundle in one step.

Downstream consumers (`bClass_hHJB`, `fromCAndAuthorised`,
the closed-paper residue producer) can take the smaller bundle
instead of the full `StrongVI_setForm` field; the discharge of
`SetAdditiveContinuityInputs` from existing
`mfgOperatorEpsPair_tendsto_set_*` machinery is filed as a
sibling task. -/

/-- **Phase 2 (iter-412 plan): authorised-input bundle for the
Minty/δ-limit bridge to `StrongVI_setForm`.**

Packages the two authorised inputs of
`strongVI_setForm_of_hVIeps_set`:

* `hIndicMemLp` — for every measurable `S` of finite restricted-cube
  measure, `1_S ∈ Lᵝ` on the unit cube;
* `hCont` — operator-continuity along the strict-positive
  perturbation `μ_n := sol.m + (1/(n+1)) · 1_S`, with the test triple
  fixed at `(0, 1_S, 0)`.

Both inputs are authorised at this level per CONVENTIONS §1b /§8;
their discharge from existing
`mfgOperatorEpsPair_tendsto_set_*` machinery is filed as a sibling
task (see the `hCont`-side authorised input doc on
`strongVI_setForm_of_hVIeps_set`). -/
structure SetAdditiveContinuityInputs
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal') : Prop where
  /-- For every measurable `S ⊆ UnitCube d` of finite restricted-cube
  measure, the indicator `1_S` lies in `Lᵝ` on the cube. -/
  hIndicMemLp :
    ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
      (volume.restrict (UnitCube d)) S < ∞ →
      MemLpPer (d := d) (ENNReal.ofReal βBarReal)
        (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)))
  /-- Operator-continuity along the strict-positive perturbation
  `μ_n := sol.m + (1/(n+1)) · 1_S` (test triple fixed at
  `(0, 1_S, 0)`). -/
  hCont :
    ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
      (volume.restrict (UnitCube d)) S < ∞ →
      Filter.Tendsto
        (fun n : ℕ =>
          mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            sol.Du
            (fun x => sol.m x + (1 / ((n : ℝ) + 1)) *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
            sol.u
            (fun _ _ => (0 : ℝ))
            (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)))
            (fun _ => (0 : ℝ)))
        Filter.atTop
        (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε
              sol.Du sol.m sol.u
              (fun _ _ => (0 : ℝ))
              (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)))
              (fun _ => (0 : ℝ))))

/-- **Phase 2 (iter-412 plan): closed-form derivation of
`StrongVI_setForm` from the authorised-input bundle.**

Given a `RegularizedBareSolution` and a
`SetAdditiveContinuityInputs sol` bundle, deliver the paper's
`StrongVI_setForm` at the base point `(sol.Du, sol.m, sol.u)`.

This is a one-line projection through `strongVI_setForm_of_hVIeps_set`:
the bundle merely repackages the two inputs that the Minty bridge
already consumes individually. -/
theorem hStrongVI_set_of_regularized_solution
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal')
    (hSet : SetAdditiveContinuityInputs sol) :
    StrongVI_setForm V H DpH γBarReal ε sol.Du sol.m sol.u :=
  strongVI_setForm_of_hVIeps_set sol hSet.hIndicMemLp hSet.hCont

/-! ### Unit example for `hStrongVI_set_of_regularized_solution`

Type-shape pin: from a `RegularizedBareSolution` and a
`SetAdditiveContinuityInputs sol` bundle,
`hStrongVI_set_of_regularized_solution` delivers
`StrongVI_setForm V H DpH γBar ε sol.Du sol.m sol.u`. -/
example
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal')
    (hSet : SetAdditiveContinuityInputs sol) :
    StrongVI_setForm V H DpH γBarReal ε sol.Du sol.m sol.u :=
  hStrongVI_set_of_regularized_solution sol hSet

/-! ### Phase 3 of expert post-iter-412 plan — partial discharge of
`SetAdditiveContinuityInputs` from existing infrastructure

Per `infra-P4-discharge-SetAdditiveContinuityInputs-from-tendsto`,
we discharge the *easy* half of the bundle directly:

* `indicMemLp_universal`: for every measurable set `S` (no finite-measure
  hypothesis is even needed beyond the cube being a finite measure
  domain, which is already the carrier measure), the indicator
  `1_S` lies in `Lᵝ` on the cube. Routine via `MemLp.indicator`
  applied to `memLp_const 1`.

The harder half — discharging `hCont` from paper hypotheses — is
filed as the sibling task
`infra-P4-mfgOperatorEpsPair-tendsto-set-additive-perturbation`,
because no existing aggregator has the right perturbation shape:
the `hCont` field uses the additive perturbation
`fun x => sol.m x + (1/(n+1)) · 1_S x` together with the test triple
`(0, 1_S, 0)`, while the existing `set / transport / signed-*`
aggregators all use mass shapes of the form `(…) + 1/(n+1)` (constant
shift), not `sol.m + (1/(n+1)) · 1_S`. Those aggregators are
therefore not pointwise-equal to the `hCont` integrand modulo
`mfgOperatorEpsPair_congr_ae`, and a dedicated aggregator is needed.

The producer `of_hCont` below assembles the bundle from a paper-level
`hCont` certificate alone, using `indicMemLp_universal` to discharge
`hIndicMemLp`. Once the child task lands the dedicated aggregator,
`of_paperHypotheses` will follow as a one-line wrapper around
`of_hCont`. -/

/-- **Universal discharge of `hIndicMemLp` for `SetAdditiveContinuityInputs`.**

For every measurable `S ⊆ ℝ^d`, the indicator `1_S` lies in
`MemLpPer βBar` on the unit cube. The cube has finite measure, so
`fun _ => (1 : ℝ)` is in `MemLp` on `(volume.restrict (UnitCube d))`,
and `MemLp.indicator` then gives the indicator. The finite-measure
hypothesis on `S` from the original `hIndicMemLp` field is not used
in this universal discharge.

This is the indicator half of the discharge filed in
`infra-P4-discharge-SetAdditiveContinuityInputs-from-tendsto`. -/
theorem indicMemLp_universal
    {βBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    (S : Set (Fin d → ℝ)) (hS : MeasurableSet S) :
    MemLpPer (d := d) (ENNReal.ofReal βBarReal)
      (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ))) := by
  -- The cube has finite measure, so `memLp_const 1` is available.
  have hcube_fin :
      IsFiniteMeasure
        (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ]
    simp
  have h_one : MemLp (fun _ : (Fin d → ℝ) => (1 : ℝ))
      (ENNReal.ofReal βBarReal)
      (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) :=
    memLp_const (1 : ℝ)
  have h_indic := h_one.indicator (s := S) hS.nullMeasurableSet
  exact MemLp.toMemLpPer h_indic

/-- **Partial producer for `SetAdditiveContinuityInputs`** (Phase 3
of iter-412 plan): assemble the bundle from a paper-level `hCont`
certificate, discharging `hIndicMemLp` via `indicMemLp_universal`.

Once the dedicated aggregator
`mfgOperatorEpsPair_tendsto_set_additive_perturbation_of_paperHypotheses`
(filed as a sibling task) lands, the full
`SetAdditiveContinuityInputs.of_paperHypotheses` will follow as a
one-line wrapper around this producer with `hCont` discharged
internally. -/
theorem SetAdditiveContinuityInputs.of_hCont
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal')
    (hCont :
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (volume.restrict (UnitCube d)) S < ∞ →
        Filter.Tendsto
          (fun n : ℕ =>
            mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε
              sol.Du
              (fun x => sol.m x + (1 / ((n : ℝ) + 1)) *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              sol.u
              (fun _ _ => (0 : ℝ))
              (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)))
              (fun _ => (0 : ℝ)))
          Filter.atTop
          (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                γBarReal ε
                sol.Du sol.m sol.u
                (fun _ _ => (0 : ℝ))
                (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)))
                (fun _ => (0 : ℝ))))) :
    SetAdditiveContinuityInputs (βBarReal' := βBarReal')
      (γBarReal' := γBarReal') sol :=
  { hIndicMemLp := fun S hS _ =>
      indicMemLp_universal (βBarReal := βBarReal) S hS
    hCont := hCont }

/-- Sanity-check `example` for `SetAdditiveContinuityInputs.of_hCont`.

Type-shape pin: given a `RegularizedBareSolution` and the operator-
continuity certificate `hCont`, `of_hCont` produces the full
`SetAdditiveContinuityInputs sol` bundle by discharging the indicator-
`Lᵝ` half via `indicMemLp_universal`. -/
example
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (sol : RegularizedBareSolution d ε V H DpH
              γBarReal βBarReal βBarReal' γBarReal')
    (hCont :
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (volume.restrict (UnitCube d)) S < ∞ →
        Filter.Tendsto
          (fun n : ℕ =>
            mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε
              sol.Du
              (fun x => sol.m x + (1 / ((n : ℝ) + 1)) *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              sol.u
              (fun _ _ => (0 : ℝ))
              (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)))
              (fun _ => (0 : ℝ)))
          Filter.atTop
          (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                γBarReal ε
                sol.Du sol.m sol.u
                (fun _ _ => (0 : ℝ))
                (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)))
                (fun _ => (0 : ℝ))))) :
    SetAdditiveContinuityInputs (βBarReal' := βBarReal')
      (γBarReal' := γBarReal') sol :=
  SetAdditiveContinuityInputs.of_hCont sol hCont

/-! ### Phase A — headline aggregator
`mfgOperatorEpsPair_tendsto_set_additive_perturbation`

Per `infra-P4-mfgOperatorEpsPair-tendsto-set-additive-perturbation`,
this is the headline aggregator for the additive perturbation shape

```
μ_n := sol.m + (1/(n+1)) · 1_S,    μ_∞ := sol.m
```

with the test triple held *constant* in `n` at `(0, 1_S, 0)`, i.e.
`(Dν, η, ν) = ((fun _ _ => 0), 1_S, (fun _ => 0))`.

The simplifying observation is that with `Dν = 0` and `ν = 0`, two of
the three `mfgOperatorPair` summands are pointwise zero in the
integrand:

* the flux summand `μ_n · (DpH(...) ⬝ Dν) = μ_n · 0 = 0`,
* the mass summand `(μ_n - 1) · ν = (μ_n - 1) · 0 = 0`.

Their integrals therefore equal `0` (regardless of `n`), so the
corresponding `Tendsto` factors collapse to `tendsto_const_nhds` and
the integrability inputs collapse to integrability of the zero
function.

The sole non-trivial summand is the HJB pair

```
(-sol.u(x) - H(x, sol.Du(x), μ_n x) + V x) · (1_S x).
```

Its `Tendsto` along `n → ∞` is taken as an authorised input at the
headline-aggregator level; the child task
`infra-P4-mfgOperatorEpsPair-tendsto-set-additive-perturbation-paperHyp`
will discharge it from paper hypotheses + dominator certificates.

The headline aggregator routes through
`mfgOperatorEpsPair_tendsto_of_summands` with the constant-test-side
collapses applied directly. -/

theorem mfgOperatorEpsPair_tendsto_set_additive_perturbation
    {ε γBar : ℝ}
    (Dυ : Fin d → (Fin d → ℝ) → ℝ) (υ : (Fin d → ℝ) → ℝ)
    (m : (Fin d → ℝ) → ℝ)
    (S : Set (Fin d → ℝ))
    -- HJB summand integrability at the perturbation `μ_n`.
    (h_int1_n : ∀ n : ℕ,
      Integrable (fun x =>
        (-(υ x) - H x (fun i => Dυ i x)
              (m x + (1 / ((n : ℝ) + 1)) *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) + V x)
          * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
        (volume.restrict (UnitCube d)))
    -- HJB summand integrability at the limit `μ_∞ = m`.
    (h_int1_lim :
      Integrable (fun x =>
        (-(υ x) - H x (fun i => Dυ i x) (m x) + V x)
          * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
        (volume.restrict (UnitCube d)))
    -- HJB integrand-level tendsto (authorised input; the child task
    -- discharges it from H-continuity + dominators).
    (h_tendsto1 :
      Filter.Tendsto
        (fun n : ℕ => ∫ x in UnitCube d,
          (-(υ x) - H x (fun i => Dυ i x)
                (m x + (1 / ((n : ℝ) + 1)) *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) + V x)
            * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
        Filter.atTop
        (𝓝 (∫ x in UnitCube d,
          (-(υ x) - H x (fun i => Dυ i x) (m x) + V x)
            * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))) :
    Filter.Tendsto
      (fun n : ℕ =>
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBar ε
          Dυ
          (fun x => m x + (1 / ((n : ℝ) + 1)) *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          υ
          (fun _ _ => (0 : ℝ))
          (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)))
          (fun _ => (0 : ℝ)))
      Filter.atTop
      (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBar ε
            Dυ m υ
            (fun _ _ => (0 : ℝ))
            (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)))
            (fun _ => (0 : ℝ)))) := by
  -- Apply the consumer-level compositional lemma, with summands 2/3
  -- discharged via pointwise zero (test side `(0, 0)`).
  set μm : Measure (Fin d → ℝ) := volume.restrict (UnitCube d) with hμm
  -- Summand 2 (flux) integrand is pointwise zero: `μ · (DpH ⬝ 0) = 0`.
  -- We show this equals `(fun _ => 0)` and hence is integrable; the
  -- tendsto becomes `tendsto_const_nhds`.
  have h_dot_zero : ∀ (x : Fin d → ℝ) (μx : ℝ),
      DpH x (fun i => Dυ i x) μx ⬝ (fun _ : Fin d => (0 : ℝ)) = 0 := by
    intro x μx
    -- `v ⬝ 0 = 0`.
    unfold StationaryMFG.Hamiltonian.euclideanDot
    simp
  have h_int2_eq_n : ∀ n : ℕ,
      (fun x =>
        (m x + (1 / ((n : ℝ) + 1)) *
            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          * (DpH x (fun i => Dυ i x)
                (m x + (1 / ((n : ℝ) + 1)) *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              ⬝ (fun i => (0 : ℝ))))
        = (fun _ => (0 : ℝ)) := by
    intro n
    funext x
    rw [h_dot_zero]
    ring
  have h_int2_eq_lim :
      (fun x =>
        m x * (DpH x (fun i => Dυ i x) (m x)
            ⬝ (fun i => (0 : ℝ))))
        = (fun _ => (0 : ℝ)) := by
    funext x
    rw [h_dot_zero]
    ring
  have h_int2_n : ∀ n : ℕ,
      Integrable (fun x =>
        (m x + (1 / ((n : ℝ) + 1)) *
            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          * (DpH x (fun i => Dυ i x)
                (m x + (1 / ((n : ℝ) + 1)) *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              ⬝ (fun i => (0 : ℝ)))) μm := by
    intro n
    rw [h_int2_eq_n n]
    exact integrable_zero _ _ _
  have h_int2_lim :
      Integrable (fun x =>
        m x * (DpH x (fun i => Dυ i x) (m x)
            ⬝ (fun i => (0 : ℝ)))) μm := by
    rw [h_int2_eq_lim]
    exact integrable_zero _ _ _
  -- Summand 3 (mass) integrand is pointwise zero: `(μ - 1) · 0 = 0`.
  have h_int3_eq_n : ∀ n : ℕ,
      (fun x =>
        ((m x + (1 / ((n : ℝ) + 1)) *
            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) - 1)
          * (0 : ℝ))
        = (fun _ => (0 : ℝ)) := by
    intro n; funext x; ring
  have h_int3_eq_lim :
      (fun x => (m x - 1) * (0 : ℝ)) = (fun _ => (0 : ℝ)) := by
    funext x; ring
  have h_int3_n : ∀ n : ℕ,
      Integrable (fun x =>
        ((m x + (1 / ((n : ℝ) + 1)) *
            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) - 1)
          * (0 : ℝ)) μm := by
    intro n; rw [h_int3_eq_n n]; exact integrable_zero _ _ _
  have h_int3_lim :
      Integrable (fun x => (m x - 1) * (0 : ℝ)) μm := by
    rw [h_int3_eq_lim]; exact integrable_zero _ _ _
  -- Summand 2 / 3 integral-tendstos: both reduce to `tendsto_const_nhds 0`.
  have h_tendsto2 :
      Filter.Tendsto
        (fun n : ℕ => ∫ x in UnitCube d,
          (m x + (1 / ((n : ℝ) + 1)) *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
            * (DpH x (fun i => Dυ i x)
                (m x + (1 / ((n : ℝ) + 1)) *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                ⬝ (fun i => (0 : ℝ))))
        Filter.atTop
        (𝓝 (∫ x in UnitCube d,
          m x * (DpH x (fun i => Dυ i x) (m x)
              ⬝ (fun i => (0 : ℝ))))) := by
    have h1 : ∀ n : ℕ,
        (∫ x in UnitCube d,
            (m x + (1 / ((n : ℝ) + 1)) *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              * (DpH x (fun i => Dυ i x)
                  (m x + (1 / ((n : ℝ) + 1)) *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                  ⬝ (fun i => (0 : ℝ))))
          = 0 := by
      intro n
      rw [show (fun x =>
            (m x + (1 / ((n : ℝ) + 1)) *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
            * (DpH x (fun i => Dυ i x)
                (m x + (1 / ((n : ℝ) + 1)) *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                ⬝ (fun i => (0 : ℝ))))
          = (fun _ => (0 : ℝ)) from h_int2_eq_n n]
      simp
    have h2 : (∫ x in UnitCube d,
        m x * (DpH x (fun i => Dυ i x) (m x)
            ⬝ (fun i => (0 : ℝ)))) = 0 := by
      rw [h_int2_eq_lim]; simp
    rw [h2]
    have : (fun n : ℕ => ∫ x in UnitCube d,
        (m x + (1 / ((n : ℝ) + 1)) *
            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          * (DpH x (fun i => Dυ i x)
              (m x + (1 / ((n : ℝ) + 1)) *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              ⬝ (fun i => (0 : ℝ))))
        = (fun _ => (0 : ℝ)) := by
      funext n; exact h1 n
    rw [this]
    exact tendsto_const_nhds
  have h_tendsto3 :
      Filter.Tendsto
        (fun n : ℕ => ∫ x in UnitCube d,
          ((m x + (1 / ((n : ℝ) + 1)) *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) - 1)
            * (0 : ℝ))
        Filter.atTop
        (𝓝 (∫ x in UnitCube d, (m x - 1) * (0 : ℝ))) := by
    have h1 : ∀ n : ℕ,
        (∫ x in UnitCube d,
            ((m x + (1 / ((n : ℝ) + 1)) *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) - 1)
              * (0 : ℝ)) = 0 := by
      intro n
      rw [h_int3_eq_n n]; simp
    have h2 : (∫ x in UnitCube d, (m x - 1) * (0 : ℝ)) = 0 := by
      rw [h_int3_eq_lim]; simp
    rw [h2]
    have : (fun n : ℕ => ∫ x in UnitCube d,
        ((m x + (1 / ((n : ℝ) + 1)) *
            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) - 1)
          * (0 : ℝ))
        = (fun _ => (0 : ℝ)) := by
      funext n; exact h1 n
    rw [this]
    exact tendsto_const_nhds
  -- Apply the consumer-level lemma.
  -- Consumer positional args: Dυ, υ, Dν, ν; named: μN, μInf, ηN, ηInf.
  -- Our problem: Dν = 0, ν = 0 (constant), ηN = ηInf = 1_S (constant).
  exact mfgOperatorEpsPair_tendsto_of_summands
    (V := V) (H := H) (DpH := DpH) (γBar := γBar) (ε := ε)
    Dυ υ (fun _ _ => (0 : ℝ)) (fun _ => (0 : ℝ))
    (μN := fun n x =>
      m x + (1 / ((n : ℝ) + 1)) *
        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
    (μInf := m)
    (ηN := fun _ => (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ))))
    (ηInf := S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)))
    h_int1_n h_int2_n h_int3_n
    h_int1_lim h_int2_lim h_int3_lim
    h_tendsto1 h_tendsto2 h_tendsto3

/-! ### Sanity-check `example` for the headline additive-perturbation
aggregator.

Type-shape pin: given the three discharge inputs (HJB integrability
at `μ_n` and `μ_∞`, and HJB integral-level tendsto), the headline
aggregator produces the `mfgOperatorEpsPair`-tendsto along the
additive perturbation `m + (1/(n+1)) · 1_S`. -/
example
    {ε γBar : ℝ}
    (Dυ : Fin d → (Fin d → ℝ) → ℝ) (υ : (Fin d → ℝ) → ℝ)
    (m : (Fin d → ℝ) → ℝ)
    (S : Set (Fin d → ℝ))
    (h_int1_n : ∀ n : ℕ,
      Integrable (fun x =>
        (-(υ x) - H x (fun i => Dυ i x)
              (m x + (1 / ((n : ℝ) + 1)) *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) + V x)
          * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
        (volume.restrict (UnitCube d)))
    (h_int1_lim :
      Integrable (fun x =>
        (-(υ x) - H x (fun i => Dυ i x) (m x) + V x)
          * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
        (volume.restrict (UnitCube d)))
    (h_tendsto1 :
      Filter.Tendsto
        (fun n : ℕ => ∫ x in UnitCube d,
          (-(υ x) - H x (fun i => Dυ i x)
                (m x + (1 / ((n : ℝ) + 1)) *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) + V x)
            * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
        Filter.atTop
        (𝓝 (∫ x in UnitCube d,
          (-(υ x) - H x (fun i => Dυ i x) (m x) + V x)
            * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))) :
    Filter.Tendsto
      (fun n : ℕ =>
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBar ε
          Dυ
          (fun x => m x + (1 / ((n : ℝ) + 1)) *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          υ
          (fun _ _ => (0 : ℝ))
          (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)))
          (fun _ => (0 : ℝ)))
      Filter.atTop
      (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBar ε
            Dυ m υ
            (fun _ _ => (0 : ℝ))
            (S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)))
            (fun _ => (0 : ℝ)))) :=
  mfgOperatorEpsPair_tendsto_set_additive_perturbation
    Dυ υ m S h_int1_n h_int1_lim h_tendsto1

end Banach
end SimplePower
end Theorems
end StationaryMFG
end
