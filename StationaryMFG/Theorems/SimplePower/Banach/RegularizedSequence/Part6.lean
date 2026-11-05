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
public import StationaryMFG.Theorems.SimplePower.Banach.RegularizedSequence.Part4
import all StationaryMFG.Theorems.SimplePower.Banach.RegularizedSequence.Part4
public import StationaryMFG.Theorems.SimplePower.Banach.RegularizedSequence.Part5
import all StationaryMFG.Theorems.SimplePower.Banach.RegularizedSequence.Part5

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
open MeasureTheory Filter
open StationaryMFG.Periodic
open StationaryMFG.Theorems.SimplePower (StrongVI_setForm)
open StationaryMFG.Theorems.SimplePower (StrongVI_setForm_signed)


/-! ## W-form transport-family Minty supplier — `hVIeps_transport_of_KAepsi_W_VI`

Sibling task `paperSolFor-final-phase5-hWeakDeriv-step3b-W-form-Minty-transport`
of the iter-0701/0702 W-form Minty suppliers. The transport family
inline-builds `qn := banachPairOfBare (σ + 1/(n+1)) υ φ ...`, so —
unlike the signed family — the test point's `υ`/`Dυ` factors are
user-supplied and the K_Aepsi_W weak-derivative tie is NOT inherited
from `q`. The W-form statement therefore carries an extra
`hWeak_υ : ∀ i, HasWeakDerivPer i υ (φ i)` hypothesis (paper-faithful;
in the paper the test direction is in the Sobolev space and the
weak-derivative tie is automatic).

The proof is a near-copy of `hVIeps_transport_of_KAepsi_VI`
(line 1414), with the substantive change being:

* `hVI` quantifier: `q' ∈ K_Aepsi → q' ∈ K_Aepsi_W` (refined cone).
* Per-`n` test point: replace inline `qn := banachPairOfBare …` with
  the named `transportFamily_test_point_perturbed` (iter 0696).
* `qn ∈ K_Aepsi_W` discharged via
  `transportFamily_test_point_perturbed_mem_K_Aepsi_W` (iter 0696).
* The `Aepsi_CLM_opK_apply_of_mem` rewrite still needs
  `qn ∈ K_Aepsi`, recovered via `K_Aepsi_W_subset_K_Aepsi`.

This consumer is dispatched to by
`paperSection8_hMinty_transport_W_of_paperHypotheses` in
`BanachBridge.lean`. No new authorisation parameter. -/

/-- **W-form sibling of `hVIeps_transport_of_KAepsi_VI`.** Same shape,
but the weak VI is `K_Aepsi_W`-quantified and the test pair `(υ, φ)`
carries a weak-derivative tie. No new authorisation parameter. -/
theorem hVIeps_transport_of_KAepsi_W_VI
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (auxHypsK : ∀ q ∈ K_Aepsi d βBarReal γBarReal,
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V H DpH (fun i => ⇑(q.2.2 i)) (⇑q.1) (⇑q.2.1))
    (q : XBanach d βBarReal γBarReal)
    (hVI : ∀ q' ∈ K_Aepsi_W d βBarReal γBarReal,
              0 ≤ Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
                    (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                    V H DpH auxHypsK ε q' (q' - q))
    (σ υ : (Fin d → ℝ) → ℝ) (φ : Fin d → (Fin d → ℝ) → ℝ)
    (hσ_nn : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ σ x)
    (hσ_memLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal) σ)
    (hυ_memSob : MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ)
    (hφ_memLp : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (φ i))
    -- W-form addition: weak-derivative tie for the test pair `(υ, φ)`.
    (hWeak_υ : ∀ i, HasWeakDerivPer (d := d) i υ (φ i))
    (hCont :
      Filter.Tendsto
        (fun n : ℕ =>
          mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            φ
            (fun x => σ x + 1 / ((n : ℝ) + 1))
            υ
            (fun i x => φ i x - DuOf q i x)
            (fun x => σ x + 1 / ((n : ℝ) + 1) - mOf q x)
            (υ - uOf q))
        Filter.atTop
        (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε
              φ σ υ
              (fun i x => φ i x - DuOf q i x)
              (σ - mOf q) (υ - uOf q)))) :
    0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          φ σ υ
          (fun i x => φ i x - DuOf q i x)
          (σ - mOf q) (υ - uOf q) := by
  classical
  haveI hcubeFin :
      IsFiniteMeasure (MeasureTheory.Measure.restrict
        MeasureTheory.volume (UnitCube (d := d))) :=
    ⟨by
      rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ]
      simp⟩
  -- Per-`n` perturbation step (mirror of K-form proof).
  have hStep :
      ∀ n : ℕ,
        0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε
              φ
              (fun x => σ x + 1 / ((n : ℝ) + 1))
              υ
              (fun i x => φ i x - DuOf q i x)
              (fun x => σ x + 1 / ((n : ℝ) + 1) - mOf q x)
              (υ - uOf q) := by
    intro n
    -- Build the named W-form transport-family test point and its
    -- K_Aepsi_W membership (iter 0696).
    set qn : XBanach d βBarReal γBarReal :=
      transportFamily_test_point_perturbed (βBarReal := βBarReal)
        (γBarReal := γBarReal) n hσ_memLp hυ_memSob hφ_memLp with hqn_def
    have hqn_KW : qn ∈ K_Aepsi_W d βBarReal γBarReal :=
      transportFamily_test_point_perturbed_mem_K_Aepsi_W
        (βBarReal := βBarReal) (γBarReal := γBarReal)
        n hσ_nn hσ_memLp hυ_memSob hφ_memLp hWeak_υ
    -- Descend to `qn ∈ K_Aepsi` for the `Aepsi_CLM_opK_apply_of_mem` rewrite.
    have hqn_K : qn ∈ K_Aepsi d βBarReal γBarReal :=
      K_Aepsi_W_subset_K_Aepsi d βBarReal γBarReal hqn_KW
    -- Reconstruct the same `MemLpPer βBar` certificate for `μ_n` that
    -- `transportFamily_test_point_perturbed` consumed (definitional).
    have hcst_memLp :
        MemLpPer (d := d) (ENNReal.ofReal βBarReal)
          (fun _ : Fin d → ℝ => (1 / ((n : ℝ) + 1) : ℝ)) :=
      MemLp.toMemLpPer (memLp_const _)
    have hμn_memLp :
        MemLpPer (d := d) (ENNReal.ofReal βBarReal)
          (fun x => σ x + 1 / ((n : ℝ) + 1)) :=
      show MemLpPer (d := d) (ENNReal.ofReal βBarReal)
          (((σ : (Fin d → ℝ) → ℝ)
              + (fun _ => (1 / ((n : ℝ) + 1) : ℝ)))) from
        MemLpPer.add hσ_memLp hcst_memLp
    have hqn1 : qn.1 = hμn_memLp.toLp := rfl
    have hqn21 : qn.2.1 = hυ_memSob.1.toLp := rfl
    have hqn22 : ∀ i, qn.2.2 i = (hφ_memLp i).toLp := fun _ => rfl
    -- a.e.-equalities.
    have hqn1_ae :
        (⇑qn.1 : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
          fun x => σ x + 1 / ((n : ℝ) + 1) := by
      rw [hqn1]
      exact MeasureTheory.MemLp.coeFn_toLp hμn_memLp
    have hqn21_ae :
        (⇑qn.2.1 : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] υ := by
      rw [hqn21]
      exact MeasureTheory.MemLp.coeFn_toLp hυ_memSob.1
    have hqn22_ae : ∀ i,
        (⇑(qn.2.2 i) : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] φ i := by
      intro i; rw [hqn22 i]
      exact MeasureTheory.MemLp.coeFn_toLp (hφ_memLp i)
    -- Apply the K_Aepsi_W-form weak VI at `qn`.
    have hVIn : 0 ≤ Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  V H DpH auxHypsK ε qn (qn - q) :=
      hVI qn hqn_KW
    -- Unfold via `Aepsi_CLM_opK_apply_of_mem` using `qn ∈ K_Aepsi`.
    rw [Aepsi_CLM_opK_apply_of_mem (γBarReal := γBarReal) (βBarReal := βBarReal)
          (βBarReal' := βBarReal') (γBarReal' := γBarReal')
          V H DpH auxHypsK ε hqn_K (qn - q)] at hVIn
    -- Identify the test triple `((qn-q).2.2, (qn-q).1, (qn-q).2.1)`
    -- with the bare differences via `Lp.coeFn_sub`.
    have hsub1_ae :
        (⇑((qn - q).1) : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
          fun x => (σ x + 1 / ((n : ℝ) + 1)) - mOf q x := by
      have hpair : (qn - q).1 = qn.1 - q.1 := rfl
      rw [hpair]
      have hsub := MeasureTheory.Lp.coeFn_sub qn.1 q.1
      filter_upwards [hsub, hqn1_ae] with x hxsub hxqn1
      have hxsub' : ⇑(qn.1 - q.1) x = ⇑qn.1 x - ⇑q.1 x := hxsub
      rw [hxsub', hxqn1]
      rfl
    have hsub21_ae :
        (⇑((qn - q).2.1) : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
          υ - uOf q := by
      have hpair : (qn - q).2.1 = qn.2.1 - q.2.1 := rfl
      rw [hpair]
      have hsub := MeasureTheory.Lp.coeFn_sub qn.2.1 q.2.1
      filter_upwards [hsub, hqn21_ae] with x hxsub hxqn21
      have hxsub' : ⇑(qn.2.1 - q.2.1) x = ⇑qn.2.1 x - ⇑q.2.1 x := hxsub
      change _ = υ x - uOf q x
      rw [hxsub', hxqn21]
      rfl
    have hsub22_ae : ∀ i,
        (⇑((qn - q).2.2 i) : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
          fun x => φ i x - DuOf q i x := by
      intro i
      have hpair : (qn - q).2.2 i = qn.2.2 i - q.2.2 i := rfl
      rw [hpair]
      have hsub := MeasureTheory.Lp.coeFn_sub (qn.2.2 i) (q.2.2 i)
      filter_upwards [hsub, hqn22_ae i] with x hxsub hxqn22
      have hxsub' : ⇑(qn.2.2 i - q.2.2 i) x
                      = ⇑(qn.2.2 i) x - ⇑(q.2.2 i) x := hxsub
      change _ = φ i x - DuOf q i x
      rw [hxsub', hxqn22]
      rfl
    -- Replace the test triple in `hVIn` with the bare differences.
    rw [mfgOperatorEpsPair_congr_ae (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          (fun i => ⇑(qn.2.2 i)) (⇑qn.1) (⇑qn.2.1)
          (fun i => ⇑((qn - q).2.2 i))
          (fun i x => φ i x - DuOf q i x)
          (⇑((qn - q).1))
          (fun x => (σ x + 1 / ((n : ℝ) + 1)) - mOf q x)
          (⇑((qn - q).2.1)) (υ - uOf q)
          hsub22_ae hsub1_ae hsub21_ae] at hVIn
    -- Replace the primal triple.
    rw [mfgOperatorEpsPair_primal_congr_ae (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          (Du₁ := fun i => ⇑(qn.2.2 i))
          (Du₂ := φ)
          (m₁ := ⇑qn.1)
          (m₂ := fun x => σ x + 1 / ((n : ℝ) + 1))
          (u₁ := ⇑qn.2.1) (u₂ := υ)
          (fun i x => φ i x - DuOf q i x)
          (fun x => (σ x + 1 / ((n : ℝ) + 1)) - mOf q x)
          (υ - uOf q)
          hqn1_ae hqn21_ae hqn22_ae] at hVIn
    exact hVIn
  -- Pass `n → ∞` using the operator-continuity hypothesis.
  exact ge_of_tendsto' hCont hStep

/-! ## W-form signed user-probe Minty supplier — `hVIeps_signed_user_probe_of_KAepsi_W_VI`

W-form sibling of `hVIeps_signed_user_probe_of_KAepsi_VI` (line 770).
The signed user-probe family inline-builds `qn := banachPairOfBare
(mOf q + σ · mOf q · 1_S + 1/(n+1)) υ Dυ ...`, so — unlike the signed
family — the test point's `υ`/`Dυ` factors are user-supplied and the
K_Aepsi_W weak-derivative tie is NOT inherited from `q`. The W-form
statement therefore carries an extra
`hWeak_υ : ∀ i, HasWeakDerivPer i υ (Dυ i)` hypothesis (paper-faithful;
in the paper the test direction is in the Sobolev space and the
weak-derivative tie is automatic).

The proof is a near-copy of `hVIeps_signed_user_probe_of_KAepsi_VI`,
with the substantive change being:

* `hVI` quantifier: `q' ∈ K_Aepsi → q' ∈ K_Aepsi_W` (refined cone).
* `q ∈ K0_Aepsi → q ∈ K0_Aepsi_W`. Descend via `K0_Aepsi_W_subset_K0_Aepsi`
  for the `mOf q ≥ 0` a.e. fact still consumed by the strict-positivity
  argument.
* Per-`n` test point: replace inline `qn := banachPairOfBare …` with
  the named `signedUserProbeFamily_test_point_perturbed`.
* `qn ∈ K_Aepsi_W` discharged via
  `signedUserProbeFamily_test_point_perturbed_mem_K_Aepsi_W`.
* The `Aepsi_CLM_opK_apply_of_mem` rewrite still needs `qn ∈ K_Aepsi`,
  recovered via `K_Aepsi_W_subset_K_Aepsi`.

This consumer is dispatched to by
`paperSection8_hMinty_signed_user_probe_W_of_paperHypotheses` in
`BanachBridge.lean`. No new authorisation parameter. -/

/-- **W-form sibling of `hVIeps_signed_user_probe_of_KAepsi_VI`.**
Same shape, but the weak VI is `K_Aepsi_W`-quantified and the test
pair `(υ, Dυ)` carries a weak-derivative tie. No new authorisation
parameter. -/
theorem hVIeps_signed_user_probe_of_KAepsi_W_VI
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (auxHypsK : ∀ q ∈ K_Aepsi d βBarReal γBarReal,
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V H DpH (fun i => ⇑(q.2.2 i)) (⇑q.1) (⇑q.2.1))
    (q : XBanach d βBarReal γBarReal)
    -- K0_Aepsi_W membership of `q`: refined non-negativity cone.
    (hq_K0_W : q ∈ K0_Aepsi_W d βBarReal γBarReal)
    -- The K_Aepsi_W-form weak VI.
    (hVI : ∀ q' ∈ K_Aepsi_W d βBarReal γBarReal,
              0 ≤ Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
                    (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                    V H DpH auxHypsK ε q' (q' - q))
    -- Paper-exact test-family parameters.
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (S : Set (Fin d → ℝ)) (hS : MeasurableSet S)
    (_hSfin : (MeasureTheory.volume.restrict (UnitCube d)) S < ⊤)
    -- User-supplied probe `(υ, Dυ)` with Banach-embedding certificates.
    (υ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (hυ_memSob : MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ)
    (hDυ_memLp : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i))
    -- W-form addition: weak-derivative tie for the test pair `(υ, Dυ)`.
    (hWeak_υ : ∀ i, HasWeakDerivPer (d := d) i υ (Dυ i))
    -- Authorised input (CONVENTIONS §8): operator-continuity along
    -- the strict-positive perturbation.
    (hCont :
      Filter.Tendsto
        (fun n : ℕ =>
          mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            Dυ
            (fun x => mOf q x + σ * mOf q x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                        + 1 / ((n : ℝ) + 1))
            υ
            (fun i x => Dυ i x - DuOf q i x)
            (fun x => (mOf q x + σ * mOf q x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                        + 1 / ((n : ℝ) + 1)) - mOf q x)
            (fun x => υ x - uOf q x))
        Filter.atTop
        (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε
              Dυ
              (fun x => mOf q x + σ * mOf q x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              υ
              (fun i x => Dυ i x - DuOf q i x)
              (fun x => σ * mOf q x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              (fun x => υ x - uOf q x)))) :
    0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          Dυ
          (fun x => mOf q x + σ * mOf q x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          υ
          (fun i x => Dυ i x - DuOf q i x)
          (fun x => σ * mOf q x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          (fun x => υ x - uOf q x) := by
  classical
  haveI hcubeFin :
      IsFiniteMeasure (MeasureTheory.Measure.restrict
        MeasureTheory.volume (UnitCube (d := d))) :=
    ⟨by
      rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ]
      simp⟩
  -- Descend `q ∈ K0_Aepsi_W → q ∈ K0_Aepsi` for `mOf q ≥ 0` a.e.
  have hq_K0 : q ∈ K0_Aepsi d βBarReal γBarReal :=
    K0_Aepsi_W_subset_K0_Aepsi d βBarReal γBarReal hq_K0_W
  -- Sign bound: `σ ∈ {±1}` ⇒ `-1 ≤ σ`.
  have hσ_lb : (-1 : ℝ) ≤ σ := by
    rcases hσ with hσ | hσ <;> simp [hσ]
  -- `mOf q` Lp embeddability and a.e. nonnegativity.
  have hm_memLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal) (mOf q) :=
    memLpPer_of_lpPer (d := d) q.1
  have hm_nn : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
                  0 ≤ mOf q x := hq_K0
  -- The signed multiplicative perturbation `σ • mOf q` is `MemLpPer`.
  have hσm_memLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal)
                      (fun x => σ * mOf q x) := by
    have hsmul := hm_memLp.const_smul (𝕜 := ℝ) σ
    have heq : (σ • (mOf q : (Fin d → ℝ) → ℝ))
                  = fun x => σ * mOf q x := rfl
    rw [heq] at hsmul; exact hsmul
  -- The indicator-restricted version.
  have hSσm_memLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal)
                      (S.indicator (fun x => σ * mOf q x)) :=
    MemLp.toMemLpPer (MeasureTheory.MemLp.indicator hS.nullMeasurableSet hσm_memLp.toMemLp)
  -- Pointwise rewrite: indicator of σ•m equals (σ•m)·1_S.
  have hSσm_funEq :
      (S.indicator (fun x => σ * mOf q x) : (Fin d → ℝ) → ℝ)
        = fun x => σ * mOf q x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
    funext x
    by_cases hx : x ∈ S
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  -- Lp embeddability of `(fun x => σ * mOf q x * S.indicator 1 x)`.
  have hSσm_memLp' : MemLpPer (d := d) (ENNReal.ofReal βBarReal)
                        (fun x => σ * mOf q x *
                                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
    rw [← hSσm_funEq]; exact hSσm_memLp
  -- The "base" perturbation `mF := mOf q + σ · mOf q · 1_S` is `MemLpPer`.
  have hmF_memLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal)
                      (fun x => mOf q x + σ * mOf q x *
                                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
    have h := MemLpPer.add hm_memLp hSσm_memLp'
    have heq :
        ((mOf q : (Fin d → ℝ) → ℝ)
            + (fun x => σ * mOf q x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
          = fun x => mOf q x + σ * mOf q x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := rfl
    rw [← heq]; exact h
  -- Per-`n` strict-positive perturbation step.
  have hStep :
      ∀ n : ℕ,
        0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε
              Dυ
              (fun x => mOf q x + σ * mOf q x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                          + 1 / ((n : ℝ) + 1))
              υ
              (fun i x => Dυ i x - DuOf q i x)
              (fun x => (mOf q x + σ * mOf q x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                          + 1 / ((n : ℝ) + 1)) - mOf q x)
              (fun x => υ x - uOf q x) := by
    intro n
    -- `MemLpPer βBar` for the constant function `1/(n+1)`.
    have hcst_memLp :
        MemLpPer (d := d) (ENNReal.ofReal βBarReal)
          (fun _ : Fin d → ℝ => (1 / ((n : ℝ) + 1) : ℝ)) :=
      MemLp.toMemLpPer (memLp_const _)
    -- `MemLpPer βBar` for the perturbed density `mF + 1/(n+1)`.
    have hμn_memLp :
        MemLpPer (d := d) (ENNReal.ofReal βBarReal)
          (fun x => mOf q x + σ * mOf q x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                      + 1 / ((n : ℝ) + 1)) := by
      have h := MemLpPer.add hmF_memLp hcst_memLp
      have heq :
          ((fun x => mOf q x + σ * mOf q x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              + (fun _ => (1 / ((n : ℝ) + 1) : ℝ)))
            = fun x => mOf q x + σ * mOf q x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                        + 1 / ((n : ℝ) + 1) := rfl
      rw [← heq]; exact h
    -- Build the named W-form test point and its K_Aepsi_W membership.
    set qn : XBanach d βBarReal γBarReal :=
      signedUserProbeFamily_test_point_perturbed (βBarReal := βBarReal)
        (γBarReal := γBarReal) n q σ hμn_memLp hυ_memSob hDυ_memLp with hqn_def
    have hqn_KW : qn ∈ K_Aepsi_W d βBarReal γBarReal :=
      signedUserProbeFamily_test_point_perturbed_mem_K_Aepsi_W
        (βBarReal := βBarReal) (γBarReal := γBarReal)
        n q σ hσ hμn_memLp hυ_memSob hDυ_memLp hWeak_υ hm_nn
    -- Descend to `qn ∈ K_Aepsi` for the `Aepsi_CLM_opK_apply_of_mem` rewrite.
    have hqn_K : qn ∈ K_Aepsi d βBarReal γBarReal :=
      K_Aepsi_W_subset_K_Aepsi d βBarReal γBarReal hqn_KW
    -- Componentwise identification with the `toLp` images.
    have hqn1 : qn.1 = hμn_memLp.toLp := rfl
    have hqn21 : qn.2.1 = hυ_memSob.1.toLp := rfl
    have hqn22 : ∀ i, qn.2.2 i = (hDυ_memLp i).toLp := fun _ => rfl
    -- a.e.-equalities.
    have hqn1_ae :
        (⇑qn.1 : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
          fun x => mOf q x + σ * mOf q x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                    + 1 / ((n : ℝ) + 1) := by
      rw [hqn1]
      exact MeasureTheory.MemLp.coeFn_toLp hμn_memLp
    have hqn21_ae :
        (⇑qn.2.1 : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] υ := by
      rw [hqn21]
      exact MeasureTheory.MemLp.coeFn_toLp hυ_memSob.1
    have hqn22_ae : ∀ i,
        (⇑(qn.2.2 i) : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] Dυ i := by
      intro i; rw [hqn22 i]
      exact MeasureTheory.MemLp.coeFn_toLp (hDυ_memLp i)
    -- Apply the K_Aepsi_W-form weak VI at `qn`.
    have hVIn : 0 ≤ Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  V H DpH auxHypsK ε qn (qn - q) :=
      hVI qn hqn_KW
    -- Unfold via `Aepsi_CLM_opK_apply_of_mem` using `qn ∈ K_Aepsi`.
    rw [Aepsi_CLM_opK_apply_of_mem (γBarReal := γBarReal) (βBarReal := βBarReal)
          (βBarReal' := βBarReal') (γBarReal' := γBarReal')
          V H DpH auxHypsK ε hqn_K (qn - q)] at hVIn
    -- Identify the test-triple differences via `Lp.coeFn_sub`.
    have hsub1_ae :
        (⇑((qn - q).1) : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
          fun x => (mOf q x + σ * mOf q x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                      + 1 / ((n : ℝ) + 1)) - mOf q x := by
      have hpair : (qn - q).1 = qn.1 - q.1 := rfl
      rw [hpair]
      have hsub := MeasureTheory.Lp.coeFn_sub qn.1 q.1
      filter_upwards [hsub, hqn1_ae] with x hxsub hxqn1
      have hxsub' : ⇑(qn.1 - q.1) x = ⇑qn.1 x - ⇑q.1 x := hxsub
      rw [hxsub', hxqn1]
      rfl
    have hsub21_ae :
        (⇑((qn - q).2.1) : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
          fun x => υ x - uOf q x := by
      have hpair : (qn - q).2.1 = qn.2.1 - q.2.1 := rfl
      rw [hpair]
      have hsub := MeasureTheory.Lp.coeFn_sub qn.2.1 q.2.1
      filter_upwards [hsub, hqn21_ae] with x hxsub hxqn21
      have hxsub' : ⇑(qn.2.1 - q.2.1) x = ⇑qn.2.1 x - ⇑q.2.1 x := hxsub
      change _ = υ x - uOf q x
      rw [hxsub', hxqn21]
      rfl
    have hsub22_ae : ∀ i,
        (⇑((qn - q).2.2 i) : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
          fun x => Dυ i x - DuOf q i x := by
      intro i
      have hpair : (qn - q).2.2 i = qn.2.2 i - q.2.2 i := rfl
      rw [hpair]
      have hsub := MeasureTheory.Lp.coeFn_sub (qn.2.2 i) (q.2.2 i)
      filter_upwards [hsub, hqn22_ae i] with x hxsub hxqn22
      have hxsub' : ⇑(qn.2.2 i - q.2.2 i) x
                      = ⇑(qn.2.2 i) x - ⇑(q.2.2 i) x := hxsub
      change _ = Dυ i x - DuOf q i x
      rw [hxsub', hxqn22]
      rfl
    -- Replace the test triple.
    rw [mfgOperatorEpsPair_congr_ae (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          (fun i => ⇑(qn.2.2 i)) (⇑qn.1) (⇑qn.2.1)
          (fun i => ⇑((qn - q).2.2 i))
          (fun i x => Dυ i x - DuOf q i x)
          (⇑((qn - q).1))
          (fun x => (mOf q x + σ * mOf q x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                      + 1 / ((n : ℝ) + 1)) - mOf q x)
          (⇑((qn - q).2.1))
          (fun x => υ x - uOf q x)
          hsub22_ae hsub1_ae hsub21_ae] at hVIn
    -- Replace the primal triple.
    rw [mfgOperatorEpsPair_primal_congr_ae (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          (Du₁ := fun i => ⇑(qn.2.2 i))
          (Du₂ := Dυ)
          (m₁ := ⇑qn.1)
          (m₂ := fun x => mOf q x + σ * mOf q x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                          + 1 / ((n : ℝ) + 1))
          (u₁ := ⇑qn.2.1) (u₂ := υ)
          (fun i x => Dυ i x - DuOf q i x)
          (fun x => (mOf q x + σ * mOf q x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                      + 1 / ((n : ℝ) + 1)) - mOf q x)
          (fun x => υ x - uOf q x)
          hqn1_ae hqn21_ae hqn22_ae] at hVIn
    exact hVIn
  -- Pass `n → ∞` using the operator-continuity hypothesis.
  exact ge_of_tendsto' hCont hStep

/-! ## W-form signed user-triple Minty supplier — `hVIeps_signed_user_triple_of_KAepsi_W_VI`

W-form sibling of `hVIeps_signed_user_triple_of_KAepsi_VI` (line 1095).
The signed user-triple family inline-builds `qn := banachPairOfBare
(μ + σ · μ · 1_S + 1/(n+1)) υ Dυ ...` for a user-supplied primal
density `μ` and user-supplied test probe `(υ, Dυ)`. As with the
user-probe variant, the K_Aepsi_W weak-derivative tie is NOT
inherited from `q` (because `υ`/`Dυ` are user-supplied), so the
W-form statement carries an extra
`hWeak_υ : ∀ i, HasWeakDerivPer i υ (Dυ i)` hypothesis (paper-faithful;
in the paper the test direction lives in the Sobolev space and the
weak-derivative tie is automatic).

The proof is a near-copy of `hVIeps_signed_user_probe_of_KAepsi_W_VI`,
with the substantive change being the user-supplied `μ` in place of
`mOf q` in the perturbed density. The K0_Aepsi non-negativity
descent from `K0_Aepsi_W → K0_Aepsi` is no longer needed (no `mOf q`
strict-positivity argument); the user supplies `hμ_nn` directly.

* `hVI` quantifier: `q' ∈ K_Aepsi → q' ∈ K_Aepsi_W` (refined cone).
* Per-`n` test point: replace inline `qn := banachPairOfBare …` with
  the named `signedUserTripleFamily_test_point_perturbed`.
* `qn ∈ K_Aepsi_W` discharged via
  `signedUserTripleFamily_test_point_perturbed_mem_K_Aepsi_W`.
* The `Aepsi_CLM_opK_apply_of_mem` rewrite still needs `qn ∈ K_Aepsi`,
  recovered via `K_Aepsi_W_subset_K_Aepsi`.

This consumer is dispatched to by
`paperSection8_hMinty_signed_user_triple_W_of_paperHypotheses` in
`BanachBridge.lean`. No new authorisation parameter. -/

/-- **W-form sibling of `hVIeps_signed_user_triple_of_KAepsi_VI`.**
Same shape, but the weak VI is `K_Aepsi_W`-quantified and the test
pair `(υ, Dυ)` carries a weak-derivative tie. No new authorisation
parameter. -/
theorem hVIeps_signed_user_triple_of_KAepsi_W_VI
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (auxHypsK : ∀ q ∈ K_Aepsi d βBarReal γBarReal,
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V H DpH (fun i => ⇑(q.2.2 i)) (⇑q.1) (⇑q.2.1))
    (q : XBanach d βBarReal γBarReal)
    -- The K_Aepsi_W-form weak VI.
    (hVI : ∀ q' ∈ K_Aepsi_W d βBarReal γBarReal,
              0 ≤ Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
                    (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                    V H DpH auxHypsK ε q' (q' - q))
    -- Paper-exact test-family parameters.
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (S : Set (Fin d → ℝ)) (hS : MeasurableSet S)
    (_hSfin : (MeasureTheory.volume.restrict (UnitCube d)) S < ⊤)
    -- User-supplied primal density `μ` plus probe `(υ, Dυ)` with
    -- Banach-embedding certificates.
    (μ υ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (hμ_nn : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ μ x)
    (hμ_memLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal) μ)
    (hυ_memSob : MemSobolevPer (d := d) (ENNReal.ofReal γBarReal) υ)
    (hDυ_memLp : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dυ i))
    -- W-form addition: weak-derivative tie for the test pair `(υ, Dυ)`.
    (hWeak_υ : ∀ i, HasWeakDerivPer (d := d) i υ (Dυ i))
    -- Authorised input (CONVENTIONS §8): operator-continuity along
    -- the strict-positive perturbation
    -- `μ_n := μ + σ · μ · 1_S + 1/(n+1)` at the user triple.
    (hCont :
      Filter.Tendsto
        (fun n : ℕ =>
          mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε
            Dυ
            (fun x => μ x + σ * μ x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                        + 1 / ((n : ℝ) + 1))
            υ
            (fun i x => Dυ i x - DuOf q i x)
            (fun x => (μ x + σ * μ x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                        + 1 / ((n : ℝ) + 1)) - mOf q x)
            (fun x => υ x - uOf q x))
        Filter.atTop
        (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε
              Dυ
              (fun x => μ x + σ * μ x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              υ
              (fun i x => Dυ i x - DuOf q i x)
              (fun x => (μ x + σ * μ x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                          - mOf q x)
              (fun x => υ x - uOf q x)))) :
    0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          Dυ
          (fun x => μ x + σ * μ x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          υ
          (fun i x => Dυ i x - DuOf q i x)
          (fun x => (μ x + σ * μ x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                      - mOf q x)
          (fun x => υ x - uOf q x) := by
  classical
  haveI hcubeFin :
      IsFiniteMeasure (MeasureTheory.Measure.restrict
        MeasureTheory.volume (UnitCube (d := d))) :=
    ⟨by
      rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ]
      simp⟩
  -- Sign bound: `σ ∈ {±1}` ⇒ `-1 ≤ σ`.
  have hσ_lb : (-1 : ℝ) ≤ σ := by
    rcases hσ with hσ | hσ <;> simp [hσ]
  -- The signed multiplicative perturbation `σ • μ` is `MemLpPer`.
  have hσμ_memLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal)
                      (fun x => σ * μ x) := by
    have hsmul := hμ_memLp.const_smul (𝕜 := ℝ) σ
    have heq : (σ • (μ : (Fin d → ℝ) → ℝ))
                  = fun x => σ * μ x := rfl
    rw [heq] at hsmul; exact hsmul
  -- The indicator-restricted version.
  have hSσμ_memLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal)
                      (S.indicator (fun x => σ * μ x)) :=
    MemLp.toMemLpPer (MeasureTheory.MemLp.indicator hS.nullMeasurableSet hσμ_memLp.toMemLp)
  -- Pointwise rewrite: indicator of σ•μ equals (σ•μ)·1_S.
  have hSσμ_funEq :
      (S.indicator (fun x => σ * μ x) : (Fin d → ℝ) → ℝ)
        = fun x => σ * μ x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
    funext x
    by_cases hx : x ∈ S
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  -- Lp embeddability of `(fun x => σ * μ x * S.indicator 1 x)`.
  have hSσμ_memLp' : MemLpPer (d := d) (ENNReal.ofReal βBarReal)
                        (fun x => σ * μ x *
                                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
    rw [← hSσμ_funEq]; exact hSσμ_memLp
  -- The "base" perturbation `μF := μ + σ · μ · 1_S` is `MemLpPer`.
  have hμF_memLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal)
                      (fun x => μ x + σ * μ x *
                                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
    have h := MemLpPer.add hμ_memLp hSσμ_memLp'
    have heq :
        ((μ : (Fin d → ℝ) → ℝ)
            + (fun x => σ * μ x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
          = fun x => μ x + σ * μ x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := rfl
    rw [← heq]; exact h
  -- Per-`n` strict-positive perturbation step.
  have hStep :
      ∀ n : ℕ,
        0 ≤ mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε
              Dυ
              (fun x => μ x + σ * μ x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                          + 1 / ((n : ℝ) + 1))
              υ
              (fun i x => Dυ i x - DuOf q i x)
              (fun x => (μ x + σ * μ x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                          + 1 / ((n : ℝ) + 1)) - mOf q x)
              (fun x => υ x - uOf q x) := by
    intro n
    -- `MemLpPer βBar` for the constant function `1/(n+1)`.
    have hcst_memLp :
        MemLpPer (d := d) (ENNReal.ofReal βBarReal)
          (fun _ : Fin d → ℝ => (1 / ((n : ℝ) + 1) : ℝ)) :=
      MemLp.toMemLpPer (memLp_const _)
    -- `MemLpPer βBar` for the perturbed density `μF + 1/(n+1)`.
    have hμn_memLp :
        MemLpPer (d := d) (ENNReal.ofReal βBarReal)
          (fun x => μ x + σ * μ x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                      + 1 / ((n : ℝ) + 1)) := by
      have h := MemLpPer.add hμF_memLp hcst_memLp
      have heq :
          ((fun x => μ x + σ * μ x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              + (fun _ => (1 / ((n : ℝ) + 1) : ℝ)))
            = fun x => μ x + σ * μ x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                        + 1 / ((n : ℝ) + 1) := rfl
      rw [← heq]; exact h
    -- Build the named W-form test point and its K_Aepsi_W membership.
    set qn : XBanach d βBarReal γBarReal :=
      signedUserTripleFamily_test_point_perturbed (βBarReal := βBarReal)
        (γBarReal := γBarReal) n σ hμn_memLp hυ_memSob hDυ_memLp with hqn_def
    have hqn_KW : qn ∈ K_Aepsi_W d βBarReal γBarReal :=
      signedUserTripleFamily_test_point_perturbed_mem_K_Aepsi_W
        (βBarReal := βBarReal) (γBarReal := γBarReal)
        n σ hσ hμn_memLp hυ_memSob hDυ_memLp hWeak_υ hμ_nn
    -- Descend to `qn ∈ K_Aepsi` for the `Aepsi_CLM_opK_apply_of_mem` rewrite.
    have hqn_K : qn ∈ K_Aepsi d βBarReal γBarReal :=
      K_Aepsi_W_subset_K_Aepsi d βBarReal γBarReal hqn_KW
    -- Componentwise identification with the `toLp` images.
    have hqn1 : qn.1 = hμn_memLp.toLp := rfl
    have hqn21 : qn.2.1 = hυ_memSob.1.toLp := rfl
    have hqn22 : ∀ i, qn.2.2 i = (hDυ_memLp i).toLp := fun _ => rfl
    -- a.e.-equalities.
    have hqn1_ae :
        (⇑qn.1 : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
          fun x => μ x + σ * μ x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                    + 1 / ((n : ℝ) + 1) := by
      rw [hqn1]
      exact MeasureTheory.MemLp.coeFn_toLp hμn_memLp
    have hqn21_ae :
        (⇑qn.2.1 : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] υ := by
      rw [hqn21]
      exact MeasureTheory.MemLp.coeFn_toLp hυ_memSob.1
    have hqn22_ae : ∀ i,
        (⇑(qn.2.2 i) : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)] Dυ i := by
      intro i; rw [hqn22 i]
      exact MeasureTheory.MemLp.coeFn_toLp (hDυ_memLp i)
    -- Apply the K_Aepsi_W-form weak VI at `qn`.
    have hVIn : 0 ≤ Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
                  (βBarReal' := βBarReal') (γBarReal' := γBarReal')
                  V H DpH auxHypsK ε qn (qn - q) :=
      hVI qn hqn_KW
    -- Unfold via `Aepsi_CLM_opK_apply_of_mem` using `qn ∈ K_Aepsi`.
    rw [Aepsi_CLM_opK_apply_of_mem (γBarReal := γBarReal) (βBarReal := βBarReal)
          (βBarReal' := βBarReal') (γBarReal' := γBarReal')
          V H DpH auxHypsK ε hqn_K (qn - q)] at hVIn
    -- Identify the test-triple differences via `Lp.coeFn_sub`.
    have hsub1_ae :
        (⇑((qn - q).1) : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
          fun x => (μ x + σ * μ x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                      + 1 / ((n : ℝ) + 1)) - mOf q x := by
      have hpair : (qn - q).1 = qn.1 - q.1 := rfl
      rw [hpair]
      have hsub := MeasureTheory.Lp.coeFn_sub qn.1 q.1
      filter_upwards [hsub, hqn1_ae] with x hxsub hxqn1
      have hxsub' : ⇑(qn.1 - q.1) x = ⇑qn.1 x - ⇑q.1 x := hxsub
      rw [hxsub', hxqn1]
      rfl
    have hsub21_ae :
        (⇑((qn - q).2.1) : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
          fun x => υ x - uOf q x := by
      have hpair : (qn - q).2.1 = qn.2.1 - q.2.1 := rfl
      rw [hpair]
      have hsub := MeasureTheory.Lp.coeFn_sub qn.2.1 q.2.1
      filter_upwards [hsub, hqn21_ae] with x hxsub hxqn21
      have hxsub' : ⇑(qn.2.1 - q.2.1) x = ⇑qn.2.1 x - ⇑q.2.1 x := hxsub
      change _ = υ x - uOf q x
      rw [hxsub', hxqn21]
      rfl
    have hsub22_ae : ∀ i,
        (⇑((qn - q).2.2 i) : (Fin d → ℝ) → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (UnitCube d)]
          fun x => Dυ i x - DuOf q i x := by
      intro i
      have hpair : (qn - q).2.2 i = qn.2.2 i - q.2.2 i := rfl
      rw [hpair]
      have hsub := MeasureTheory.Lp.coeFn_sub (qn.2.2 i) (q.2.2 i)
      filter_upwards [hsub, hqn22_ae i] with x hxsub hxqn22
      have hxsub' : ⇑(qn.2.2 i - q.2.2 i) x
                      = ⇑(qn.2.2 i) x - ⇑(q.2.2 i) x := hxsub
      change _ = Dυ i x - DuOf q i x
      rw [hxsub', hxqn22]
      rfl
    -- Replace the test triple.
    rw [mfgOperatorEpsPair_congr_ae (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          (fun i => ⇑(qn.2.2 i)) (⇑qn.1) (⇑qn.2.1)
          (fun i => ⇑((qn - q).2.2 i))
          (fun i x => Dυ i x - DuOf q i x)
          (⇑((qn - q).1))
          (fun x => (μ x + σ * μ x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                      + 1 / ((n : ℝ) + 1)) - mOf q x)
          (⇑((qn - q).2.1))
          (fun x => υ x - uOf q x)
          hsub22_ae hsub1_ae hsub21_ae] at hVIn
    -- Replace the primal triple.
    rw [mfgOperatorEpsPair_primal_congr_ae (V := V) (H := H) (DpH := DpH)
          γBarReal ε
          (Du₁ := fun i => ⇑(qn.2.2 i))
          (Du₂ := Dυ)
          (m₁ := ⇑qn.1)
          (m₂ := fun x => μ x + σ * μ x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                          + 1 / ((n : ℝ) + 1))
          (u₁ := ⇑qn.2.1) (u₂ := υ)
          (fun i x => Dυ i x - DuOf q i x)
          (fun x => (μ x + σ * μ x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                      + 1 / ((n : ℝ) + 1)) - mOf q x)
          (fun x => υ x - uOf q x)
          hqn1_ae hqn21_ae hqn22_ae] at hVIn
    exact hVIn
  -- Pass `n → ∞` using the operator-continuity hypothesis.
  exact ge_of_tendsto' hCont hStep

end Banach
end SimplePower
end Theorems
end StationaryMFG

end
