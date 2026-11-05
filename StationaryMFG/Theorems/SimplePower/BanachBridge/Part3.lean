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
public import StationaryMFG.Theorems.SimplePower.BanachBridge.Part1
import all StationaryMFG.Theorems.SimplePower.BanachBridge.Part1
public import StationaryMFG.Theorems.SimplePower.BanachBridge.Part2
import all StationaryMFG.Theorems.SimplePower.BanachBridge.Part2

@[expose] public section

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


/-- **`signedUserTripleCont_of_paperHypotheses_of_aestronglyMeasurable_of_rc0`**
— AE-strong-measurable, Hext-free `_of_rc0` wrapper around the strict
`signedUserTripleCont_of_paperHypotheses_of_rc0`. -/
noncomputable def signedUserTripleCont_of_paperHypotheses_of_aestronglyMeasurable_of_rc0
    {d : ℕ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (hRegH : Hamiltonian.RegularityH (d := d) H DpH)
    (hH_rc0 :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ∀ p : Fin d → ℝ,
          Filter.Tendsto (fun m : ℝ => H x p m) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
            (nhds (H x p 0)))
    [Fact (1 ≤ ENNReal.ofReal (hpow.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))]
    {ε : ℝ}
    (q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
            (hpow.β + 1) (hpow.α * (hpow.β + 1) / hpow.β))
    (hq_K0 : q ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi d
              (hpow.β + 1) (hpow.α * (hpow.β + 1) / hpow.β))
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (S : Set (Fin d → ℝ)) (hS : MeasurableSet S)
    (μ υ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (hμ_nn : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
                  0 ≤ μ x)
    (hμ_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (hpow.β + 1)) μ)
    (hυ_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) υ)
    (hDυ_memLp : ∀ i, Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) (Dυ i))
    (hV_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) V) :
    Filter.Tendsto
      (fun n : ℕ =>
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          (hpow.α * (hpow.β + 1) / hpow.β) ε
          Dυ
          (fun x =>
            μ x + σ * μ x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
              + 1 / ((n : ℝ) + 1))
          υ
          (fun i x => Dυ i x -
            StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
          (fun x =>
            (μ x + σ * μ x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
              + 1 / ((n : ℝ) + 1)) -
            StationaryMFG.Theorems.SimplePower.Banach.mOf q x)
          (fun x => υ x -
            StationaryMFG.Theorems.SimplePower.Banach.uOf q x))
      Filter.atTop
      (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            (hpow.α * (hpow.β + 1) / hpow.β) ε
            Dυ
            (fun x =>
              μ x + σ * μ x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
            υ
            (fun i x => Dυ i x -
              StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
            (fun x =>
              (μ x + σ * μ x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) -
              StationaryMFG.Theorems.SimplePower.Banach.mOf q x)
            (fun x => υ x -
              StationaryMFG.Theorems.SimplePower.Banach.uOf q x))) := by
  classical
  set μ' : (Fin d → ℝ) → ℝ := hμ_memLp.aestronglyMeasurable.mk μ
    with hμ'_def
  set υ' : (Fin d → ℝ) → ℝ := hυ_memLp.aestronglyMeasurable.mk υ
    with hυ'_def
  set Dυ' : Fin d → (Fin d → ℝ) → ℝ :=
    fun i => (hDυ_memLp i).aestronglyMeasurable.mk (Dυ i)
    with hDυ'_def
  have hμ'_meas : Measurable μ' :=
    hμ_memLp.aestronglyMeasurable.measurable_mk
  have hυ'_meas : Measurable υ' :=
    hυ_memLp.aestronglyMeasurable.measurable_mk
  have hDυ'_meas : ∀ i, Measurable (Dυ' i) := fun i =>
    (hDυ_memLp i).aestronglyMeasurable.measurable_mk
  have hμ'_ae :
      μ =ᵐ[MeasureTheory.volume.restrict (Periodic.UnitCube d)] μ' :=
    hμ_memLp.aestronglyMeasurable.ae_eq_mk
  have hυ'_ae :
      υ =ᵐ[MeasureTheory.volume.restrict (Periodic.UnitCube d)] υ' :=
    hυ_memLp.aestronglyMeasurable.ae_eq_mk
  have hDυ'_ae : ∀ i,
      Dυ i =ᵐ[MeasureTheory.volume.restrict (Periodic.UnitCube d)] Dυ' i :=
    fun i => (hDυ_memLp i).aestronglyMeasurable.ae_eq_mk
  have hμ'_memLp : Periodic.MemLpPer (d := d)
      (ENNReal.ofReal (hpow.β + 1)) μ' :=
    hμ_memLp.congr_ae_unitCube hμ'_ae
  have hυ'_memLp : Periodic.MemLpPer (d := d)
      (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) υ' :=
    hυ_memLp.congr_ae_unitCube hυ'_ae
  have hDυ'_memLp : ∀ i, Periodic.MemLpPer (d := d)
      (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) (Dυ' i) := fun i =>
    (hDυ_memLp i).congr_ae_unitCube (hDυ'_ae i)
  have hμ'_nn : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
                  0 ≤ μ' x := by
    filter_upwards [hμ_nn, hμ'_ae] with x hxnn hxeq
    rw [← hxeq]; exact hxnn
  have h_prime :=
    signedUserTripleCont_of_paperHypotheses_of_rc0
      (V := V) (H := H) (DpH := DpH)
      hpow hRegH hH_rc0 (ε := ε)
      q hq_K0 σ hσ S hS μ' υ' Dυ'
      hμ'_meas hυ'_meas hDυ'_meas
      hμ'_nn hμ'_memLp hυ'_memLp hDυ'_memLp hV_memLp
  have hDνdiff_ae : ∀ i,
      (fun x : (Fin d → ℝ) =>
          Dυ' i x - StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
        =ᵐ[MeasureTheory.volume.restrict (Periodic.UnitCube d)]
      (fun x : (Fin d → ℝ) =>
          Dυ i x - StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x) := by
    intro i
    filter_upwards [hDυ'_ae i] with x hx
    rw [← hx]
  have hνdiff_ae :
      (fun x : (Fin d → ℝ) =>
          υ' x - StationaryMFG.Theorems.SimplePower.Banach.uOf q x)
        =ᵐ[MeasureTheory.volume.restrict (Periodic.UnitCube d)]
      (fun x : (Fin d → ℝ) =>
          υ x - StationaryMFG.Theorems.SimplePower.Banach.uOf q x) := by
    filter_upwards [hυ'_ae] with x hx
    rw [← hx]
  have hDυprim_ae : ∀ i,
      Dυ' i =ᵐ[MeasureTheory.volume.restrict (Periodic.UnitCube d)] Dυ i :=
    fun i => (hDυ'_ae i).symm
  have hυprim_ae :
      υ' =ᵐ[MeasureTheory.volume.restrict (Periodic.UnitCube d)] υ :=
    hυ'_ae.symm
  have hμseq_ae : ∀ n : ℕ,
      (fun x : (Fin d → ℝ) =>
          μ' x + σ * μ' x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
            + 1 / ((n : ℝ) + 1))
        =ᵐ[MeasureTheory.volume.restrict (Periodic.UnitCube d)]
      (fun x : (Fin d → ℝ) =>
          μ x + σ * μ x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
            + 1 / ((n : ℝ) + 1)) := by
    intro n
    filter_upwards [hμ'_ae] with x hx
    rw [← hx]
  have hηseq_ae : ∀ n : ℕ,
      (fun x : (Fin d → ℝ) =>
          (μ' x + σ * μ' x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
            + 1 / ((n : ℝ) + 1)) -
          StationaryMFG.Theorems.SimplePower.Banach.mOf q x)
        =ᵐ[MeasureTheory.volume.restrict (Periodic.UnitCube d)]
      (fun x : (Fin d → ℝ) =>
          (μ x + σ * μ x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
            + 1 / ((n : ℝ) + 1)) -
          StationaryMFG.Theorems.SimplePower.Banach.mOf q x) := by
    intro n
    filter_upwards [hμ'_ae] with x hx
    rw [← hx]
  have hμlim_ae :
      (fun x : (Fin d → ℝ) =>
          μ' x + σ * μ' x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
        =ᵐ[MeasureTheory.volume.restrict (Periodic.UnitCube d)]
      (fun x : (Fin d → ℝ) =>
          μ x + σ * μ x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
    filter_upwards [hμ'_ae] with x hx
    rw [← hx]
  have hηlim_ae :
      (fun x : (Fin d → ℝ) =>
          (μ' x + σ * μ' x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) -
          StationaryMFG.Theorems.SimplePower.Banach.mOf q x)
        =ᵐ[MeasureTheory.volume.restrict (Periodic.UnitCube d)]
      (fun x : (Fin d → ℝ) =>
          (μ x + σ * μ x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) -
          StationaryMFG.Theorems.SimplePower.Banach.mOf q x) := by
    filter_upwards [hμ'_ae] with x hx
    rw [← hx]
  have hSeq_eq : ∀ n : ℕ,
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
        (hpow.α * (hpow.β + 1) / hpow.β) ε
        Dυ'
        (fun x =>
          μ' x + σ * μ' x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
            + 1 / ((n : ℝ) + 1))
        υ'
        (fun i x => Dυ' i x -
          StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
        (fun x =>
          (μ' x + σ * μ' x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
            + 1 / ((n : ℝ) + 1)) -
          StationaryMFG.Theorems.SimplePower.Banach.mOf q x)
        (fun x => υ' x -
          StationaryMFG.Theorems.SimplePower.Banach.uOf q x)
      =
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
        (hpow.α * (hpow.β + 1) / hpow.β) ε
        Dυ
        (fun x =>
          μ x + σ * μ x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
            + 1 / ((n : ℝ) + 1))
        υ
        (fun i x => Dυ i x -
          StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
        (fun x =>
          (μ x + σ * μ x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
            + 1 / ((n : ℝ) + 1)) -
          StationaryMFG.Theorems.SimplePower.Banach.mOf q x)
        (fun x => υ x -
          StationaryMFG.Theorems.SimplePower.Banach.uOf q x) := by
    intro n
    rw [mfgOperatorEpsPair_congr_ae_primal (V := V) (H := H) (DpH := DpH)
          (γBar := hpow.α * (hpow.β + 1) / hpow.β) (ε := ε)
          Dυ' Dυ
          (fun x =>
            μ' x + σ * μ' x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
              + 1 / ((n : ℝ) + 1))
          (fun x =>
            μ x + σ * μ x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
              + 1 / ((n : ℝ) + 1))
          υ' υ
          (fun i x => Dυ' i x -
            StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
          (fun x =>
            (μ' x + σ * μ' x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
              + 1 / ((n : ℝ) + 1)) -
            StationaryMFG.Theorems.SimplePower.Banach.mOf q x)
          (fun x => υ' x -
            StationaryMFG.Theorems.SimplePower.Banach.uOf q x)
          hDυprim_ae (hμseq_ae n) hυprim_ae]
    rw [mfgOperatorEpsPair_congr_ae (V := V) (H := H) (DpH := DpH)
          (γBar := hpow.α * (hpow.β + 1) / hpow.β) (ε := ε)
          Dυ
          (fun x =>
            μ x + σ * μ x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
              + 1 / ((n : ℝ) + 1))
          υ
          (fun i x => Dυ' i x -
            StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
          (fun i x => Dυ i x -
            StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
          (fun x =>
            (μ' x + σ * μ' x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
              + 1 / ((n : ℝ) + 1)) -
            StationaryMFG.Theorems.SimplePower.Banach.mOf q x)
          (fun x =>
            (μ x + σ * μ x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
              + 1 / ((n : ℝ) + 1)) -
            StationaryMFG.Theorems.SimplePower.Banach.mOf q x)
          (fun x => υ' x -
            StationaryMFG.Theorems.SimplePower.Banach.uOf q x)
          (fun x => υ x -
            StationaryMFG.Theorems.SimplePower.Banach.uOf q x)
          hDνdiff_ae (hηseq_ae n) hνdiff_ae]
  have hLim_eq :
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
        (hpow.α * (hpow.β + 1) / hpow.β) ε
        Dυ'
        (fun x =>
          μ' x + σ * μ' x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
        υ'
        (fun i x => Dυ' i x -
          StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
        (fun x =>
          (μ' x + σ * μ' x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) -
          StationaryMFG.Theorems.SimplePower.Banach.mOf q x)
        (fun x => υ' x -
          StationaryMFG.Theorems.SimplePower.Banach.uOf q x)
      =
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
        (hpow.α * (hpow.β + 1) / hpow.β) ε
        Dυ
        (fun x =>
          μ x + σ * μ x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
        υ
        (fun i x => Dυ i x -
          StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
        (fun x =>
          (μ x + σ * μ x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) -
          StationaryMFG.Theorems.SimplePower.Banach.mOf q x)
        (fun x => υ x -
          StationaryMFG.Theorems.SimplePower.Banach.uOf q x) := by
    rw [mfgOperatorEpsPair_congr_ae_primal (V := V) (H := H) (DpH := DpH)
          (γBar := hpow.α * (hpow.β + 1) / hpow.β) (ε := ε)
          Dυ' Dυ
          (fun x =>
            μ' x + σ * μ' x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          (fun x =>
            μ x + σ * μ x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          υ' υ
          (fun i x => Dυ' i x -
            StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
          (fun x =>
            (μ' x + σ * μ' x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) -
            StationaryMFG.Theorems.SimplePower.Banach.mOf q x)
          (fun x => υ' x -
            StationaryMFG.Theorems.SimplePower.Banach.uOf q x)
          hDυprim_ae hμlim_ae hυprim_ae]
    rw [mfgOperatorEpsPair_congr_ae (V := V) (H := H) (DpH := DpH)
          (γBar := hpow.α * (hpow.β + 1) / hpow.β) (ε := ε)
          Dυ
          (fun x =>
            μ x + σ * μ x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          υ
          (fun i x => Dυ' i x -
            StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
          (fun i x => Dυ i x -
            StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
          (fun x =>
            (μ' x + σ * μ' x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) -
            StationaryMFG.Theorems.SimplePower.Banach.mOf q x)
          (fun x =>
            (μ x + σ * μ x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) -
            StationaryMFG.Theorems.SimplePower.Banach.mOf q x)
          (fun x => υ' x -
            StationaryMFG.Theorems.SimplePower.Banach.uOf q x)
          (fun x => υ x -
            StationaryMFG.Theorems.SimplePower.Banach.uOf q x)
          hDνdiff_ae hηlim_ae hνdiff_ae]
  have h_seq_funext :
      (fun n : ℕ =>
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          (hpow.α * (hpow.β + 1) / hpow.β) ε
          Dυ'
          (fun x =>
            μ' x + σ * μ' x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
              + 1 / ((n : ℝ) + 1))
          υ'
          (fun i x => Dυ' i x -
            StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
          (fun x =>
            (μ' x + σ * μ' x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
              + 1 / ((n : ℝ) + 1)) -
            StationaryMFG.Theorems.SimplePower.Banach.mOf q x)
          (fun x => υ' x -
            StationaryMFG.Theorems.SimplePower.Banach.uOf q x))
      =
      (fun n : ℕ =>
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          (hpow.α * (hpow.β + 1) / hpow.β) ε
          Dυ
          (fun x =>
            μ x + σ * μ x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
              + 1 / ((n : ℝ) + 1))
          υ
          (fun i x => Dυ i x -
            StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
          (fun x =>
            (μ x + σ * μ x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
              + 1 / ((n : ℝ) + 1)) -
            StationaryMFG.Theorems.SimplePower.Banach.mOf q x)
          (fun x => υ x -
            StationaryMFG.Theorems.SimplePower.Banach.uOf q x)) := by
    funext n; exact hSeq_eq n
  rw [h_seq_funext, hLim_eq] at h_prime
  exact h_prime

/-! ### `paperSolFor-minty-signed` — ε-level signed-family Minty conclusion

The producer `paperSection8_hMinty_signed_of_paperHypotheses` discharges
the `hMinty_signed` field of `PaperSolForK V H DpH hpow k`. Per the
`infra-P5-T10-v7-paperSolFor-pre-scope` audit (Child #6,
`docs/PAPERSOLFOR_SCOPE.md` D-pre.4), the ε-level signed-family Minty
conclusion at the specific Browder–Minty witness `q` extracted by
`exists_regularizedBareSolution_K` is delivered by the existing chain
```
mfgOperatorEpsPair_tendsto_signed_perturbation_of_paperHypotheses
  + hVIeps_signed_of_KAepsi_VI
```
(both in `Banach/RegularizedSequence.lean`). The first builds the
operator-continuity `Tendsto` certificate at the strict-positive
perturbation `μ_n := m + σ·m·1_S + 1/(n+1)` from the per-query residue
dominator bundle `SignedTendstoResidueOf`; the second uses that
`Tendsto` to upgrade the K_Aepsi-form weak VI (extracted internally
inside `exists_regularizedBareSolution_K` via
`exists_banachVI_at_eps_KAepsi` + `hemicont_upgrade`) to the strong
signed-family VI at the bare-function endpoints.

This is the **ε-level layer** (`mfgOperatorEpsPair`), *not* the
δ-limit `signedSegInputsAuth` layer; the two have distinct types and
domains (per `docs/PAPERSOLFOR_SCOPE.md` D-pre.4).

The producer takes the same six paper hypotheses as the existing
`regularizedSequenceData_of_paperHypotheses`
(`Banach/RegularizedSequence.lean:7378`) plus the per-query residue
supplier `residueOf_signed : ∀ q hq_K0 σ hσ S hS hSfin, SignedTendstoResidueOf
…`. No new authorisation parameter is introduced. This is the
signed-family analog of `paperSection8_hMinty_set_of_paperHypotheses`
(landed iter 0605, mirroring the same pattern). -/

/-- **ε-level signed-family Minty producer.**

Given the paper hypotheses `(hpow, hRegH, hHat0, hFin, hAgree)` and a
per-query residue supplier `residueOf_signed`, build the
`hMinty_signed` field of `PaperSolForK V H DpH hpow k` at the paper-
canonical exponents.

The field body is universally quantified over `(ctx, q, hq_K0, hVI)` and
over the signed test data `(σ, hσ, S, hS, hSfin)` with `σ ∈ {±1}` and
`S` a finite-measure measurable set. The discharge dispatches to:

* `Banach.mfgOperatorEpsPair_tendsto_signed_perturbation_of_paperHypotheses`
  for the ε-level operator-continuity `Tendsto` along
  `μ_n := mOf q + σ · mOf q · 1_S + 1/(n+1)`, fed by the residue's HJB
  dominator bundle `(Gh, hGh_memLp, hGh_bd)`; and
* `Banach.hVIeps_signed_of_KAepsi_VI` for the strong-VI upgrade from
  the K_Aepsi-form weak VI.

Reuse pattern: this is the per-`k` slice of the `hMinty_signed` argument
to `exists_regularizedBareSolution_K` constructed inside
`regularizedSequenceData_of_paperHypotheses`
(`Banach/RegularizedSequence.lean:7183-7195`), specialised at
`ε := paperEpsSeq k` and the paper-canonical exponent quadruple. -/
noncomputable def paperSection8_hMinty_signed_of_paperHypotheses
    {d : ℕ}
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (hRegH : Hamiltonian.RegularityH (d := d) H DpH)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hFin : Hamiltonian.Hext_finite_at_zero (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    (k : ℕ)
    [Fact (1 ≤ ENNReal.ofReal (hpow.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))]
    -- Per-query residue supplier for the signed family.
    (residueOf_signed :
      ∀ (q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
                (hpow.β + 1)
                (hpow.α * (hpow.β + 1) / hpow.β)),
        q ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi d
              (hpow.β + 1)
              (hpow.α * (hpow.β + 1) / hpow.β) →
        ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
        ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
          (MeasureTheory.volume.restrict (Periodic.UnitCube d)) S < ⊤ →
            StationaryMFG.Theorems.SimplePower.Banach.SignedTendstoResidueOf
              (d := d) (V := V) (H := H) (DpH := DpH)
              (βBarReal := hpow.β + 1)
              (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
              hpow q σ S) :
    ∀ (ctx : StationaryMFG.Theorems.SimplePower.Banach.AepsiUniformContextK
              (d := d) (paperEpsSeq k) V H DpH
              (hpow.α * (hpow.β + 1) / hpow.β)
              (hpow.β + 1)
              ((hpow.β + 1) / hpow.β)
              ((hpow.α * (hpow.β + 1) / hpow.β)
                / (hpow.α * (hpow.β + 1) / hpow.β - 1))),
    ∀ (q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
              (hpow.β + 1)
              (hpow.α * (hpow.β + 1) / hpow.β)),
      q ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi d
              (hpow.β + 1)
              (hpow.α * (hpow.β + 1) / hpow.β) →
      (∀ q' ∈ StationaryMFG.Theorems.SimplePower.Banach.K_Aepsi d
                (hpow.β + 1)
                (hpow.α * (hpow.β + 1) / hpow.β),
          0 ≤ StationaryMFG.Theorems.SimplePower.Banach.Aepsi_CLM_opK
                (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
                (βBarReal := hpow.β + 1)
                (βBarReal' := (hpow.β + 1) / hpow.β)
                (γBarReal' := (hpow.α * (hpow.β + 1) / hpow.β)
                                / (hpow.α * (hpow.β + 1) / hpow.β - 1))
                V H DpH ctx.auxHypsK (paperEpsSeq k) q' (q' - q)) →
      ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)) S < ⊤ →
          0 ≤ mfgOperatorEpsPair
                (V := V) (H := H) (DpH := DpH)
                (hpow.α * (hpow.β + 1) / hpow.β) (paperEpsSeq k)
                (StationaryMFG.Theorems.SimplePower.Banach.DuOf q)
                (fun x => StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
                            σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                (StationaryMFG.Theorems.SimplePower.Banach.uOf q)
                (fun _ _ => (0 : ℝ))
                (fun x => σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                (fun _ => (0 : ℝ)) := by
  -- Derive the `SimplePowerExponentFacts` bundle at the paper exponents from
  -- `hpow`. This is the same cast used by
  -- `paperSection8_hMinty_set_of_paperHypotheses` (see above, ~line 5220).
  set βBarReal : ℝ := hpow.β + 1 with hβBarReal_def
  set γBarReal : ℝ := hpow.α * (hpow.β + 1) / hpow.β with hγBarReal_def
  set βBarReal' : ℝ := (hpow.β + 1) / hpow.β with hβBarReal'_def
  have hExp_paper :
      SimplePowerExponentFacts
          (SimplePowerExponentFacts.paperGammaBarReal hpow.α hpow.β)
          (SimplePowerExponentFacts.paperBetaBar hpow.β)
          (SimplePowerExponentFacts.paperGammaBar hpow.α hpow.β)
          (SimplePowerExponentFacts.paperBetaBarPrime hpow.β) :=
    SimplePowerExponentFacts.ofPowerGrowth hpow
  have hExp :
      SimplePowerExponentFacts γBarReal
          (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
          (ENNReal.ofReal βBarReal') := by
    have h1 :
        (SimplePowerExponentFacts.paperBetaBar hpow.β)
          = ENNReal.ofReal βBarReal := by
      simp [SimplePowerExponentFacts.paperBetaBar, hβBarReal_def]
    have h2 :
        (SimplePowerExponentFacts.paperGammaBar hpow.α hpow.β)
          = ENNReal.ofReal γBarReal := by
      simp [SimplePowerExponentFacts.paperGammaBar, hγBarReal_def]
    have h3 :
        (SimplePowerExponentFacts.paperBetaBarPrime hpow.β)
          = ENNReal.ofReal βBarReal' := by
      simp [SimplePowerExponentFacts.paperBetaBarPrime, hβBarReal'_def]
    have h4 :
        (SimplePowerExponentFacts.paperGammaBarReal hpow.α hpow.β)
          = γBarReal := by
      simp [SimplePowerExponentFacts.paperGammaBarReal, hγBarReal_def]
    have := hExp_paper
    rw [h1, h2, h3, h4] at this
    exact this
  -- Closure over the universal `(ctx, q, hq_K0, hVI)` and the signed test
  -- data `(σ, hσ, S, hS, hSfin)`.
  intro ctx q hq_K0 hVI σ hσ S hS hSfin
  -- Extract the per-query signed-family residue dominator bundle.
  set r :=
    residueOf_signed q hq_K0 σ hσ S hS hSfin with hr_def
  -- Build the ε-level operator-continuity `Tendsto` certificate along
  -- `μ_n := mOf q + σ · mOf q · 1_S + 1/(n+1)`.
  have hCont :=
    StationaryMFG.Theorems.SimplePower.Banach.mfgOperatorEpsPair_tendsto_signed_perturbation_of_paperHypotheses_of_aestronglyMeasurable
      (ε := paperEpsSeq k)
      (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
      (βBarReal := hpow.β + 1)
      (βBarReal' := (hpow.β + 1) / hpow.β)
      (γBarReal' := (hpow.α * (hpow.β + 1) / hpow.β)
                      / (hpow.α * (hpow.β + 1) / hpow.β - 1))
      hpow hRegH hExp hHat0 hFin hAgree
      (StationaryMFG.Theorems.SimplePower.Banach.DuOf q)
      (StationaryMFG.Theorems.SimplePower.Banach.uOf q)
      (StationaryMFG.Theorems.SimplePower.Banach.mOf q) V σ hσ S hS
      r.hm r.hV r.hu r.hDu r.hm_memLp r.hm_nn
      r.Gh r.hGh_memLp r.hGh_bd
  -- Upgrade the K_Aepsi-form weak VI to the strong signed-family VI at the
  -- bare-function endpoints.
  exact StationaryMFG.Theorems.SimplePower.Banach.hVIeps_signed_of_KAepsi_VI
    ctx.auxHypsK q hq_K0 hVI σ hσ S hS hSfin hCont

/-! ### Hext-free `_of_rc0` signed Minty producer (T3 step 8)

ε-generic, `Hext_finite_at_zero`-free sibling of
`paperSection8_hMinty_signed_of_paperHypotheses`; same two swaps as the
set `_of_rc0` producer (takes `hH_rc0`, routes through the step-7 signed
aesm→rc0 bridge). -/
open StationaryMFG.Theorems.SimplePower.Banach in
noncomputable def paperSection8_hMinty_signed_of_paperHypotheses_of_rc0
    {d : ℕ}
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (hRegH : Hamiltonian.RegularityH (d := d) H DpH)
    (hH_rc0 :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ∀ p : Fin d → ℝ,
          Filter.Tendsto (fun m : ℝ => H x p m) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
            (nhds (H x p 0)))
    {ε : ℝ}
    [Fact (1 ≤ ENNReal.ofReal (hpow.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))]
    -- Per-query residue supplier for the signed family.
    (residueOf_signed :
      ∀ (q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
                (hpow.β + 1)
                (hpow.α * (hpow.β + 1) / hpow.β)),
        q ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi d
              (hpow.β + 1)
              (hpow.α * (hpow.β + 1) / hpow.β) →
        ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
        ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
          (MeasureTheory.volume.restrict (Periodic.UnitCube d)) S < ⊤ →
            StationaryMFG.Theorems.SimplePower.Banach.SignedTendstoResidueOf
              (d := d) (V := V) (H := H) (DpH := DpH)
              (βBarReal := hpow.β + 1)
              (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
              hpow q σ S) :
    ∀ (ctx : StationaryMFG.Theorems.SimplePower.Banach.AepsiUniformContextK
              (d := d) ε V H DpH
              (hpow.α * (hpow.β + 1) / hpow.β)
              (hpow.β + 1)
              ((hpow.β + 1) / hpow.β)
              ((hpow.α * (hpow.β + 1) / hpow.β)
                / (hpow.α * (hpow.β + 1) / hpow.β - 1))),
    ∀ (q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
              (hpow.β + 1)
              (hpow.α * (hpow.β + 1) / hpow.β)),
      q ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi d
              (hpow.β + 1)
              (hpow.α * (hpow.β + 1) / hpow.β) →
      (∀ q' ∈ StationaryMFG.Theorems.SimplePower.Banach.K_Aepsi d
                (hpow.β + 1)
                (hpow.α * (hpow.β + 1) / hpow.β),
          0 ≤ StationaryMFG.Theorems.SimplePower.Banach.Aepsi_CLM_opK
                (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
                (βBarReal := hpow.β + 1)
                (βBarReal' := (hpow.β + 1) / hpow.β)
                (γBarReal' := (hpow.α * (hpow.β + 1) / hpow.β)
                                / (hpow.α * (hpow.β + 1) / hpow.β - 1))
                V H DpH ctx.auxHypsK ε q' (q' - q)) →
      ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)) S < ⊤ →
          0 ≤ mfgOperatorEpsPair
                (V := V) (H := H) (DpH := DpH)
                (hpow.α * (hpow.β + 1) / hpow.β) ε
                (StationaryMFG.Theorems.SimplePower.Banach.DuOf q)
                (fun x => StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
                            σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                (StationaryMFG.Theorems.SimplePower.Banach.uOf q)
                (fun _ _ => (0 : ℝ))
                (fun x => σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                (fun _ => (0 : ℝ)) := by
  set βBarReal : ℝ := hpow.β + 1 with hβBarReal_def
  set γBarReal : ℝ := hpow.α * (hpow.β + 1) / hpow.β with hγBarReal_def
  set βBarReal' : ℝ := (hpow.β + 1) / hpow.β with hβBarReal'_def
  have hExp_paper :
      SimplePowerExponentFacts
          (SimplePowerExponentFacts.paperGammaBarReal hpow.α hpow.β)
          (SimplePowerExponentFacts.paperBetaBar hpow.β)
          (SimplePowerExponentFacts.paperGammaBar hpow.α hpow.β)
          (SimplePowerExponentFacts.paperBetaBarPrime hpow.β) :=
    SimplePowerExponentFacts.ofPowerGrowth hpow
  have hExp :
      SimplePowerExponentFacts γBarReal
          (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
          (ENNReal.ofReal βBarReal') := by
    have h1 :
        (SimplePowerExponentFacts.paperBetaBar hpow.β)
          = ENNReal.ofReal βBarReal := by
      simp [SimplePowerExponentFacts.paperBetaBar, hβBarReal_def]
    have h2 :
        (SimplePowerExponentFacts.paperGammaBar hpow.α hpow.β)
          = ENNReal.ofReal γBarReal := by
      simp [SimplePowerExponentFacts.paperGammaBar, hγBarReal_def]
    have h3 :
        (SimplePowerExponentFacts.paperBetaBarPrime hpow.β)
          = ENNReal.ofReal βBarReal' := by
      simp [SimplePowerExponentFacts.paperBetaBarPrime, hβBarReal'_def]
    have h4 :
        (SimplePowerExponentFacts.paperGammaBarReal hpow.α hpow.β)
          = γBarReal := by
      simp [SimplePowerExponentFacts.paperGammaBarReal, hγBarReal_def]
    have := hExp_paper
    rw [h1, h2, h3, h4] at this
    exact this
  intro ctx q hq_K0 hVI σ hσ S hS hSfin
  set r :=
    residueOf_signed q hq_K0 σ hσ S hS hSfin with hr_def
  have hCont :=
    StationaryMFG.Theorems.SimplePower.Banach.mfgOperatorEpsPair_tendsto_signed_perturbation_of_paperHypotheses_of_aestronglyMeasurable_of_rc0
      (ε := ε)
      (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
      (βBarReal := hpow.β + 1)
      (βBarReal' := (hpow.β + 1) / hpow.β)
      (γBarReal' := (hpow.α * (hpow.β + 1) / hpow.β)
                      / (hpow.α * (hpow.β + 1) / hpow.β - 1))
      hpow hRegH hExp hH_rc0
      (StationaryMFG.Theorems.SimplePower.Banach.DuOf q)
      (StationaryMFG.Theorems.SimplePower.Banach.uOf q)
      (StationaryMFG.Theorems.SimplePower.Banach.mOf q) V σ hσ S hS
      r.hm r.hV r.hu r.hDu r.hm_memLp r.hm_nn
      r.Gh r.hGh_memLp r.hGh_bd
  exact StationaryMFG.Theorems.SimplePower.Banach.hVIeps_signed_of_KAepsi_VI
    ctx.auxHypsK q hq_K0 hVI σ hσ S hS hSfin hCont

/-- **`measurable_H`-free signed-family Minty producer** (D2b-1c-ii-c4b).

`aeMeasH`-input sibling of
`paperSection8_hMinty_signed_of_paperHypotheses_of_rc0`: it drops the
strict `RegularityH`/`HypothesisPowerGrowth` binders and instead consumes
the genuine individual H field (bare exponents `α β`, `hcont_H_pm`),
routing the inner operator tendsto through the aesm-input `_of_aeMeasH`
keystone
`mfgOperatorEpsPair_tendsto_signed_perturbation_of_paperHypotheses_of_aestronglyMeasurable_of_rc0_of_aeMeasH`,
which takes the boundary H AE composites (carried by the bare residue
bundle `SignedTendstoResidueOfBare`) instead of `hRegH.measurable_H`.

This is instantiable at `H := HdeltaK0`: the H AE composites are supplied
by `aemeasurable_HdeltaK0_comp_of_rc0`. The strict `_of_rc0` producer
above is left byte-for-byte intact for T1/T2. -/
noncomputable def paperSection8_hMinty_signed_of_paperHypotheses_of_rc0_of_aeMeasH
    {d : ℕ}
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    {C α β : ℝ} (hα : 1 < α) (hβ : 0 < β)
    (hcont_H_pm :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ContinuousOn (fun (pm : (Fin d → ℝ) × ℝ) => H x pm.1 pm.2)
          {pm | 0 < pm.2})
    (hH_rc0 :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ∀ p : Fin d → ℝ,
          Filter.Tendsto (fun m : ℝ => H x p m) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
            (nhds (H x p 0)))
    {ε : ℝ}
    [Fact (1 ≤ ENNReal.ofReal (β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (α * (β + 1) / β))]
    -- Per-query bare-exponent residue supplier for the signed family.
    (residueOf_signed :
      ∀ (q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
                (β + 1)
                (α * (β + 1) / β)),
        q ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi d
              (β + 1)
              (α * (β + 1) / β) →
        ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
        ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
          (MeasureTheory.volume.restrict (Periodic.UnitCube d)) S < ⊤ →
            StationaryMFG.Theorems.SimplePower.Banach.SignedTendstoResidueOfBare
              (d := d) (V := V) (H := H) (DpH := DpH)
              (βBarReal := β + 1)
              (γBarReal := α * (β + 1) / β)
              β q σ S) :
    ∀ (ctx : StationaryMFG.Theorems.SimplePower.Banach.AepsiUniformContextK
              (d := d) ε V H DpH
              (α * (β + 1) / β)
              (β + 1)
              ((β + 1) / β)
              ((α * (β + 1) / β)
                / (α * (β + 1) / β - 1))),
    ∀ (q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
              (β + 1)
              (α * (β + 1) / β)),
      q ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi d
              (β + 1)
              (α * (β + 1) / β) →
      (∀ q' ∈ StationaryMFG.Theorems.SimplePower.Banach.K_Aepsi d
                (β + 1)
                (α * (β + 1) / β),
          0 ≤ StationaryMFG.Theorems.SimplePower.Banach.Aepsi_CLM_opK
                (γBarReal := α * (β + 1) / β)
                (βBarReal := β + 1)
                (βBarReal' := (β + 1) / β)
                (γBarReal' := (α * (β + 1) / β)
                                / (α * (β + 1) / β - 1))
                V H DpH ctx.auxHypsK ε q' (q' - q)) →
      ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)) S < ⊤ →
          0 ≤ mfgOperatorEpsPair
                (V := V) (H := H) (DpH := DpH)
                (α * (β + 1) / β) ε
                (StationaryMFG.Theorems.SimplePower.Banach.DuOf q)
                (fun x => StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
                            σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                (StationaryMFG.Theorems.SimplePower.Banach.uOf q)
                (fun _ _ => (0 : ℝ))
                (fun x => σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                (fun _ => (0 : ℝ)) := by
  set βBarReal : ℝ := β + 1 with hβBarReal_def
  set γBarReal : ℝ := α * (β + 1) / β with hγBarReal_def
  set βBarReal' : ℝ := (β + 1) / β with hβBarReal'_def
  -- Bare-exponent `SimplePowerExponentFacts` from `standardPaper`.
  have hExp_paper :
      SimplePowerExponentFacts
          (SimplePowerExponentFacts.paperGammaBarReal α β)
          (SimplePowerExponentFacts.paperBetaBar β)
          (SimplePowerExponentFacts.paperGammaBar α β)
          (SimplePowerExponentFacts.paperBetaBarPrime β) :=
    SimplePowerExponentFacts.standardPaper hα hβ
  have hExp :
      SimplePowerExponentFacts γBarReal
          (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
          (ENNReal.ofReal βBarReal') := by
    have h1 :
        (SimplePowerExponentFacts.paperBetaBar β)
          = ENNReal.ofReal βBarReal := by
      simp [SimplePowerExponentFacts.paperBetaBar, hβBarReal_def]
    have h2 :
        (SimplePowerExponentFacts.paperGammaBar α β)
          = ENNReal.ofReal γBarReal := by
      simp [SimplePowerExponentFacts.paperGammaBar, hγBarReal_def]
    have h3 :
        (SimplePowerExponentFacts.paperBetaBarPrime β)
          = ENNReal.ofReal βBarReal' := by
      simp [SimplePowerExponentFacts.paperBetaBarPrime, hβBarReal'_def]
    have h4 :
        (SimplePowerExponentFacts.paperGammaBarReal α β)
          = γBarReal := by
      simp [SimplePowerExponentFacts.paperGammaBarReal, hγBarReal_def]
    have := hExp_paper
    rw [h1, h2, h3, h4] at this
    exact this
  intro ctx q hq_K0 hVI σ hσ S hS hSfin
  set r :=
    residueOf_signed q hq_K0 σ hσ S hS hSfin with hr_def
  -- `measurable_H`-free aesm-input keystone (D2b-1c-ii-c4b).
  have hCont :=
    StationaryMFG.Theorems.SimplePower.Banach.mfgOperatorEpsPair_tendsto_signed_perturbation_of_paperHypotheses_of_aestronglyMeasurable_of_rc0_of_aeMeasH
      (ε := ε)
      (γBarReal := α * (β + 1) / β)
      (β := β) (H := H) (DpH := DpH) hβ hcont_H_pm hH_rc0
      (StationaryMFG.Theorems.SimplePower.Banach.DuOf q)
      (StationaryMFG.Theorems.SimplePower.Banach.uOf q)
      (StationaryMFG.Theorems.SimplePower.Banach.mOf q) V σ hσ S hS
      r.hm r.hV r.hu r.hDu r.hm_memLp r.hm_nn
      r.hHcomp_ae_n r.hHcomp_ae_lim
      r.Gh r.hGh_memLp r.hGh_bd
  exact StationaryMFG.Theorems.SimplePower.Banach.hVIeps_signed_of_KAepsi_VI
    ctx.auxHypsK q hq_K0 hVI σ hσ S hS hSfin hCont

/-! ### `paperSolFor-final-phase5-hWeakDeriv-step3b-W-form-Minty-signed`
— W-form signed-family Minty producer

Iter-0702 phase of the 6-phase `paperSolFor-final-phase5-hWeakDeriv`
plan. W-form sibling of `paperSection8_hMinty_signed_of_paperHypotheses`
(immediately above), supplying the **refined-cone** signed-family
Minty inequality.

Differences from the K-form sibling:

* Witness: takes `q ∈ K0_Aepsi_W d βBar γBar` (refined non-negativity
  cone) instead of `K0_Aepsi`.
* VI: takes `hVI` quantifying over `q' ∈ K_Aepsi_W d βBar γBar`.
* Context: takes `ctx : AepsiUniformContextK_W` instead of
  `AepsiUniformContextK`.
* Backing analytic lemma: dispatches to
  `Banach.hVIeps_signed_of_KAepsi_W_VI` (iter 0702) instead of
  `hVIeps_signed_of_KAepsi_VI`.

Unlike the set-family W-form producer, no extra `hWeak_υ` hypothesis
is required: the signed-family test point's `υ`/`Dυ` factors equal
`q`'s definitionally (`qn.2 = q.2`), so the weak-derivative tie
inherits from `q ∈ K0_Aepsi_W` automatically. The residue supplier
is the same `SignedTendstoResidueOf` consumed by the K-form sibling
(the residue dominator bundle is at the bare-function layer); the
descent `K0_Aepsi_W → K0_Aepsi` for that consumer is via
`K0_Aepsi_W_subset_K0_Aepsi`.

No new authorisation parameter. -/

/-- **ε-level signed-family W-form Minty producer.** Builds the
W-form `hMinty_signed` field at the paper-canonical exponents. -/
noncomputable def paperSection8_hMinty_signed_W_of_paperHypotheses
    {d : ℕ}
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (hRegH : Hamiltonian.RegularityH (d := d) H DpH)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hFin : Hamiltonian.Hext_finite_at_zero (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    (k : ℕ)
    [Fact (1 ≤ ENNReal.ofReal (hpow.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))]
    -- Per-query residue supplier for the signed family (identical to
    -- the K-form sibling's, since the residue is at the bare-function
    -- level).
    (residueOf_signed :
      ∀ (q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
                (hpow.β + 1)
                (hpow.α * (hpow.β + 1) / hpow.β)),
        q ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi d
              (hpow.β + 1)
              (hpow.α * (hpow.β + 1) / hpow.β) →
        ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
        ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
          (MeasureTheory.volume.restrict (Periodic.UnitCube d)) S < ⊤ →
            StationaryMFG.Theorems.SimplePower.Banach.SignedTendstoResidueOf
              (d := d) (V := V) (H := H) (DpH := DpH)
              (βBarReal := hpow.β + 1)
              (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
              hpow q σ S) :
    ∀ (ctx : StationaryMFG.Theorems.SimplePower.Banach.AepsiUniformContextK_W
              (d := d) (paperEpsSeq k) V H DpH
              (hpow.α * (hpow.β + 1) / hpow.β)
              (hpow.β + 1)
              ((hpow.β + 1) / hpow.β)
              ((hpow.α * (hpow.β + 1) / hpow.β)
                / (hpow.α * (hpow.β + 1) / hpow.β - 1))),
    ∀ (q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
              (hpow.β + 1)
              (hpow.α * (hpow.β + 1) / hpow.β)),
      q ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi_W d
              (hpow.β + 1)
              (hpow.α * (hpow.β + 1) / hpow.β) →
      (∀ q' ∈ StationaryMFG.Theorems.SimplePower.Banach.K_Aepsi_W d
                (hpow.β + 1)
                (hpow.α * (hpow.β + 1) / hpow.β),
          0 ≤ StationaryMFG.Theorems.SimplePower.Banach.Aepsi_CLM_opK
                (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
                (βBarReal := hpow.β + 1)
                (βBarReal' := (hpow.β + 1) / hpow.β)
                (γBarReal' := (hpow.α * (hpow.β + 1) / hpow.β)
                                / (hpow.α * (hpow.β + 1) / hpow.β - 1))
                V H DpH ctx.auxHypsK (paperEpsSeq k) q' (q' - q)) →
      ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)) S < ⊤ →
          0 ≤ mfgOperatorEpsPair
                (V := V) (H := H) (DpH := DpH)
                (hpow.α * (hpow.β + 1) / hpow.β) (paperEpsSeq k)
                (StationaryMFG.Theorems.SimplePower.Banach.DuOf q)
                (fun x => StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
                            σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                (StationaryMFG.Theorems.SimplePower.Banach.uOf q)
                (fun _ _ => (0 : ℝ))
                (fun x => σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                (fun _ => (0 : ℝ)) := by
  -- Derive the `SimplePowerExponentFacts` bundle at the paper exponents from
  -- `hpow`. Same cast as the K-form sibling.
  set βBarReal : ℝ := hpow.β + 1 with hβBarReal_def
  set γBarReal : ℝ := hpow.α * (hpow.β + 1) / hpow.β with hγBarReal_def
  set βBarReal' : ℝ := (hpow.β + 1) / hpow.β with hβBarReal'_def
  have hExp_paper :
      SimplePowerExponentFacts
          (SimplePowerExponentFacts.paperGammaBarReal hpow.α hpow.β)
          (SimplePowerExponentFacts.paperBetaBar hpow.β)
          (SimplePowerExponentFacts.paperGammaBar hpow.α hpow.β)
          (SimplePowerExponentFacts.paperBetaBarPrime hpow.β) :=
    SimplePowerExponentFacts.ofPowerGrowth hpow
  have hExp :
      SimplePowerExponentFacts γBarReal
          (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
          (ENNReal.ofReal βBarReal') := by
    have h1 :
        (SimplePowerExponentFacts.paperBetaBar hpow.β)
          = ENNReal.ofReal βBarReal := by
      simp [SimplePowerExponentFacts.paperBetaBar, hβBarReal_def]
    have h2 :
        (SimplePowerExponentFacts.paperGammaBar hpow.α hpow.β)
          = ENNReal.ofReal γBarReal := by
      simp [SimplePowerExponentFacts.paperGammaBar, hγBarReal_def]
    have h3 :
        (SimplePowerExponentFacts.paperBetaBarPrime hpow.β)
          = ENNReal.ofReal βBarReal' := by
      simp [SimplePowerExponentFacts.paperBetaBarPrime, hβBarReal'_def]
    have h4 :
        (SimplePowerExponentFacts.paperGammaBarReal hpow.α hpow.β)
          = γBarReal := by
      simp [SimplePowerExponentFacts.paperGammaBarReal, hγBarReal_def]
    have := hExp_paper
    rw [h1, h2, h3, h4] at this
    exact this
  -- Closure over `(ctx, q, hq_K0_W, hVI)` and the signed test data.
  intro ctx q hq_K0_W hVI σ hσ S hS hSfin
  -- Descend `q ∈ K0_Aepsi_W → q ∈ K0_Aepsi` for the residue supplier.
  have hq_K0 :
      q ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi d
            βBarReal γBarReal :=
    StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi_W_subset_K0_Aepsi
      d βBarReal γBarReal hq_K0_W
  -- Extract the per-query signed-family residue dominator bundle.
  set r :=
    residueOf_signed q hq_K0 σ hσ S hS hSfin with hr_def
  -- Build the ε-level operator-continuity `Tendsto` certificate.
  have hCont :=
    StationaryMFG.Theorems.SimplePower.Banach.mfgOperatorEpsPair_tendsto_signed_perturbation_of_paperHypotheses_of_aestronglyMeasurable
      (ε := paperEpsSeq k)
      (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
      (βBarReal := hpow.β + 1)
      (βBarReal' := (hpow.β + 1) / hpow.β)
      (γBarReal' := (hpow.α * (hpow.β + 1) / hpow.β)
                      / (hpow.α * (hpow.β + 1) / hpow.β - 1))
      hpow hRegH hExp hHat0 hFin hAgree
      (StationaryMFG.Theorems.SimplePower.Banach.DuOf q)
      (StationaryMFG.Theorems.SimplePower.Banach.uOf q)
      (StationaryMFG.Theorems.SimplePower.Banach.mOf q) V σ hσ S hS
      r.hm r.hV r.hu r.hDu r.hm_memLp r.hm_nn
      r.Gh r.hGh_memLp r.hGh_bd
  -- Upgrade via the W-form `hVIeps_signed_of_KAepsi_W_VI`.
  exact StationaryMFG.Theorems.SimplePower.Banach.hVIeps_signed_of_KAepsi_W_VI
    ctx.auxHypsK q hq_K0_W hVI σ hσ S hS hSfin hCont

/-! ### `paperSolFor-minty-signed-user-probe` — ε-level signed-family
**user-probe** Minty conclusion

The producer `paperSection8_hMinty_signed_user_probe_of_paperHypotheses`
discharges the `hMinty_signed_user_probe` field of `PaperSolForK V H DpH
hpow k`. Per the `infra-P5-T10-v7-paperSolFor-pre-scope` audit
(Child #8), the user-probe variant differs from the iter-0611
`hMinty_signed` variant by allowing the test gradient/value probe
`(Dυ, υ)` to be **user-supplied** (rather than hardcoded at the
witness's own `DuOf q, uOf q`).

The chain `hVIeps_signed_user_probe_of_KAepsi_VI` (Child D′,
`Banach/RegularizedSequence.lean:770`) already implements the
ε-level Minty discharge at the user-probe shape, parametrised by
its own operator-continuity certificate `hCont` along
`μ_n := mOf q + σ · mOf q · 1_S + 1/(n+1)` at the user probe
`(Dυ, υ)`.

Mirroring iter-0611, the producer takes the same six paper hypotheses
plus a **per-query user-probe continuity supplier**
`hSignedUserProbeCont` (the same shape consumed by
`regularizedSequenceData_of_paperHypotheses`, see
`Banach/RegularizedSequence.lean:7484-7518`). No new
authorisation parameter is introduced. The supplier is *not* a
global `T10PaperResidues` auth; it is a regular function parameter
the chain-level consumer (filed as a future closure task)
discharges by Hölder/Lp dominator control along the paper-canonical
power-growth hypotheses, paralleling
`mfgOperatorEpsPair_tendsto_signed_perturbation_of_paperHypotheses`. -/

/-- **ε-level signed-family user-probe Minty producer.**

Given the paper hypotheses `(hpow, hRegH, hHat0, hFin, hAgree)` and a
per-query user-probe operator-continuity supplier
`hSignedUserProbeCont`, build the `hMinty_signed_user_probe` field of
`PaperSolForK V H DpH hpow k` at the paper-canonical exponents.

The field body is universally quantified over `(ctx, q, hq_K0, hVI)`,
the signed test data `(σ, hσ, S, hS, hSfin)`, and the user probe
`(υ, Dυ)` with its Banach-embedding certificates
`(hυ_memSob, hDυ_memLp)`. The discharge dispatches to
`Banach.hVIeps_signed_user_probe_of_KAepsi_VI` (Child D′), consuming
the per-query continuity certificate supplied by
`hSignedUserProbeCont`.

Reuse pattern: this is the per-`k` slice of the
`hMinty_signed_user_probe` argument to
`exists_regularizedBareSolution_K` constructed inside
`regularizedSequenceData_of_paperHypotheses`
(`Banach/RegularizedSequence.lean:7633-7638`), specialised at
`ε := paperEpsSeq k` and the paper-canonical exponent quadruple.

The same `(hpow, hRegH, hHat0, hFin, hAgree)` paper hypotheses are
taken for shape parity with the iter-0605/0611 signed/set producers,
although the present discharge consumes none of them directly: the
analytic content is fully contained in the user-probe continuity
supplier. This mirrors iter-0611's choice to preserve the
six-hypothesis signature for downstream auth-count counting. -/
noncomputable def paperSection8_hMinty_signed_user_probe_of_paperHypotheses
    {d : ℕ}
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (_hRegH : Hamiltonian.RegularityH (d := d) H DpH)
    (_hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (_hFin : Hamiltonian.Hext_finite_at_zero (d := d) H)
    (_hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    (k : ℕ)
    [Fact (1 ≤ ENNReal.ofReal (hpow.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))]
    -- Per-query user-probe operator-continuity supplier (analytic input,
    -- CONVENTIONS §8). Mirrors `hSignedUserProbeCont` of
    -- `regularizedSequenceData_of_paperHypotheses`
    -- (`Banach/RegularizedSequence.lean:7484-7518`). The future closure
    -- task derives this from the paper power-growth/Hölder dominator
    -- control along `μ_n := mOf q + σ · mOf q · 1_S + 1/(n+1)` at the
    -- user probe `(Dυ, υ)`.
    (hSignedUserProbeCont :
      ∀ (q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
                (hpow.β + 1)
                (hpow.α * (hpow.β + 1) / hpow.β)),
        q ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi d
              (hpow.β + 1)
              (hpow.α * (hpow.β + 1) / hpow.β) →
        ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
        ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
          (MeasureTheory.volume.restrict (Periodic.UnitCube d)) S < ⊤ →
        ∀ (υ : (Fin d → ℝ) → ℝ)
          (Dυ : Fin d → (Fin d → ℝ) → ℝ),
          Periodic.MemSobolevPer (d := d)
            (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) υ →
          (∀ i, Periodic.MemLpPer (d := d)
                  (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) (Dυ i)) →
            Filter.Tendsto
              (fun n : ℕ =>
                mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                  (hpow.α * (hpow.β + 1) / hpow.β) (paperEpsSeq k)
                  Dυ
                  (fun x =>
                    StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
                      σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                      + 1 / ((n : ℝ) + 1))
                  υ
                  (fun i x => Dυ i x -
                    StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
                  (fun x =>
                    (StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
                      σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                      + 1 / ((n : ℝ) + 1)) -
                    StationaryMFG.Theorems.SimplePower.Banach.mOf q x)
                  (fun x => υ x -
                    StationaryMFG.Theorems.SimplePower.Banach.uOf q x))
              Filter.atTop
              (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                    (hpow.α * (hpow.β + 1) / hpow.β) (paperEpsSeq k)
                    Dυ
                    (fun x =>
                      StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
                        σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                    υ
                    (fun i x => Dυ i x -
                      StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
                    (fun x =>
                      σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                    (fun x => υ x -
                      StationaryMFG.Theorems.SimplePower.Banach.uOf q x)))) :
    ∀ (ctx : StationaryMFG.Theorems.SimplePower.Banach.AepsiUniformContextK
              (d := d) (paperEpsSeq k) V H DpH
              (hpow.α * (hpow.β + 1) / hpow.β)
              (hpow.β + 1)
              ((hpow.β + 1) / hpow.β)
              ((hpow.α * (hpow.β + 1) / hpow.β)
                / (hpow.α * (hpow.β + 1) / hpow.β - 1))),
    ∀ (q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
              (hpow.β + 1)
              (hpow.α * (hpow.β + 1) / hpow.β)),
      q ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi d
              (hpow.β + 1)
              (hpow.α * (hpow.β + 1) / hpow.β) →
      (∀ q' ∈ StationaryMFG.Theorems.SimplePower.Banach.K_Aepsi d
                (hpow.β + 1)
                (hpow.α * (hpow.β + 1) / hpow.β),
          0 ≤ StationaryMFG.Theorems.SimplePower.Banach.Aepsi_CLM_opK
                (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
                (βBarReal := hpow.β + 1)
                (βBarReal' := (hpow.β + 1) / hpow.β)
                (γBarReal' := (hpow.α * (hpow.β + 1) / hpow.β)
                                / (hpow.α * (hpow.β + 1) / hpow.β - 1))
                V H DpH ctx.auxHypsK (paperEpsSeq k) q' (q' - q)) →
      ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)) S < ⊤ →
      ∀ (υ : (Fin d → ℝ) → ℝ)
        (Dυ : Fin d → (Fin d → ℝ) → ℝ),
        Periodic.MemSobolevPer (d := d)
          (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) υ →
        (∀ i, Periodic.MemLpPer (d := d)
                (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) (Dυ i)) →
        (∀ i, Periodic.HasWeakDerivPer (d := d) i υ (Dυ i)) →
          0 ≤ mfgOperatorEpsPair
                (V := V) (H := H) (DpH := DpH)
                (hpow.α * (hpow.β + 1) / hpow.β) (paperEpsSeq k)
                Dυ
                (fun x => StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
                            σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                υ
                (fun i x => Dυ i x -
                  StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
                (fun x => σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                (fun x => υ x -
                  StationaryMFG.Theorems.SimplePower.Banach.uOf q x) := by
  -- Closure over the universal `(ctx, q, hq_K0, hVI)`, the signed test
  -- data `(σ, hσ, S, hS, hSfin)`, and the user probe `(υ, Dυ)` with its
  -- Banach-embedding certificates.
  -- **Phase 5 step3d**: `_hWeak_υ` slot consumed but unused.
  intro ctx q hq_K0 hVI σ hσ S hS hSfin υ Dυ hυ_memSob hDυ_memLp _hWeak_υ
  -- Dispatch to the Child D′ user-probe Minty discharge, consuming the
  -- per-query operator-continuity certificate from
  -- `hSignedUserProbeCont`.
  exact StationaryMFG.Theorems.SimplePower.Banach.hVIeps_signed_user_probe_of_KAepsi_VI
    ctx.auxHypsK q hq_K0 hVI σ hσ S hS hSfin υ Dυ hυ_memSob hDυ_memLp
    (hSignedUserProbeCont q hq_K0 σ hσ S hS hSfin υ Dυ hυ_memSob hDυ_memLp)

/-! ### `paperSolFor-final-phase5-hWeakDeriv-step3b` — W-form signed
**user-probe** Minty producer

W-form sibling of `paperSection8_hMinty_signed_user_probe_of_paperHypotheses`
(immediately above), supplying the **refined-cone** signed user-probe
Minty inequality.

Differences from the K-form sibling:

* Witness: takes `q ∈ K0_Aepsi_W d βBar γBar` (refined non-negativity
  cone) instead of `K0_Aepsi`.
* VI: takes `hVI` quantifying over `q' ∈ K_Aepsi_W d βBar γBar`.
* Context: takes `ctx : AepsiUniformContextK_W` instead of
  `AepsiUniformContextK`.
* Extra hypothesis: `hWeak_υ : ∀ i, HasWeakDerivPer i υ (Dυ i)` for
  the user-supplied test pair (per iter-0683 directive, retype the
  W-form statement to take the weak-derivative tie as a paper-faithful
  hypothesis, not as a new auth).
* Backing analytic lemma: dispatches to
  `Banach.hVIeps_signed_user_probe_of_KAepsi_W_VI` instead of
  `hVIeps_signed_user_probe_of_KAepsi_VI`.

The per-query continuity supplier `hSignedUserProbeCont` is unchanged
(operator-continuity certificate at the bare-function layer). The
descent `K0_Aepsi_W → K0_Aepsi` for the supplier is via
`K0_Aepsi_W_subset_K0_Aepsi`.

No new authorisation parameter. -/

/-- **ε-level signed-family user-probe W-form Minty producer.** Builds
the W-form `hMinty_signed_user_probe` field at the paper-canonical
exponents. -/
noncomputable def paperSection8_hMinty_signed_user_probe_W_of_paperHypotheses
    {d : ℕ}
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (_hRegH : Hamiltonian.RegularityH (d := d) H DpH)
    (_hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (_hFin : Hamiltonian.Hext_finite_at_zero (d := d) H)
    (_hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    (k : ℕ)
    [Fact (1 ≤ ENNReal.ofReal (hpow.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))]
    -- Per-query user-probe operator-continuity supplier (analytic input,
    -- CONVENTIONS §8). Identical shape to the K-form sibling's supplier
    -- since the continuity is at the bare-function layer.
    (hSignedUserProbeCont :
      ∀ (q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
                (hpow.β + 1)
                (hpow.α * (hpow.β + 1) / hpow.β)),
        q ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi d
              (hpow.β + 1)
              (hpow.α * (hpow.β + 1) / hpow.β) →
        ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
        ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
          (MeasureTheory.volume.restrict (Periodic.UnitCube d)) S < ⊤ →
        ∀ (υ : (Fin d → ℝ) → ℝ)
          (Dυ : Fin d → (Fin d → ℝ) → ℝ),
          Periodic.MemSobolevPer (d := d)
            (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) υ →
          (∀ i, Periodic.MemLpPer (d := d)
                  (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) (Dυ i)) →
            Filter.Tendsto
              (fun n : ℕ =>
                mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                  (hpow.α * (hpow.β + 1) / hpow.β) (paperEpsSeq k)
                  Dυ
                  (fun x =>
                    StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
                      σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                      + 1 / ((n : ℝ) + 1))
                  υ
                  (fun i x => Dυ i x -
                    StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
                  (fun x =>
                    (StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
                      σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                      + 1 / ((n : ℝ) + 1)) -
                    StationaryMFG.Theorems.SimplePower.Banach.mOf q x)
                  (fun x => υ x -
                    StationaryMFG.Theorems.SimplePower.Banach.uOf q x))
              Filter.atTop
              (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                    (hpow.α * (hpow.β + 1) / hpow.β) (paperEpsSeq k)
                    Dυ
                    (fun x =>
                      StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
                        σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                    υ
                    (fun i x => Dυ i x -
                      StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
                    (fun x =>
                      σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                    (fun x => υ x -
                      StationaryMFG.Theorems.SimplePower.Banach.uOf q x)))) :
    ∀ (ctx : StationaryMFG.Theorems.SimplePower.Banach.AepsiUniformContextK_W
              (d := d) (paperEpsSeq k) V H DpH
              (hpow.α * (hpow.β + 1) / hpow.β)
              (hpow.β + 1)
              ((hpow.β + 1) / hpow.β)
              ((hpow.α * (hpow.β + 1) / hpow.β)
                / (hpow.α * (hpow.β + 1) / hpow.β - 1))),
    ∀ (q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
              (hpow.β + 1)
              (hpow.α * (hpow.β + 1) / hpow.β)),
      q ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi_W d
              (hpow.β + 1)
              (hpow.α * (hpow.β + 1) / hpow.β) →
      (∀ q' ∈ StationaryMFG.Theorems.SimplePower.Banach.K_Aepsi_W d
                (hpow.β + 1)
                (hpow.α * (hpow.β + 1) / hpow.β),
          0 ≤ StationaryMFG.Theorems.SimplePower.Banach.Aepsi_CLM_opK
                (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
                (βBarReal := hpow.β + 1)
                (βBarReal' := (hpow.β + 1) / hpow.β)
                (γBarReal' := (hpow.α * (hpow.β + 1) / hpow.β)
                                / (hpow.α * (hpow.β + 1) / hpow.β - 1))
                V H DpH ctx.auxHypsK (paperEpsSeq k) q' (q' - q)) →
      ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)) S < ⊤ →
      ∀ (υ : (Fin d → ℝ) → ℝ)
        (Dυ : Fin d → (Fin d → ℝ) → ℝ),
        Periodic.MemSobolevPer (d := d)
          (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) υ →
        (∀ i, Periodic.MemLpPer (d := d)
                (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) (Dυ i)) →
        (∀ i, Periodic.HasWeakDerivPer (d := d) i υ (Dυ i)) →
          0 ≤ mfgOperatorEpsPair
                (V := V) (H := H) (DpH := DpH)
                (hpow.α * (hpow.β + 1) / hpow.β) (paperEpsSeq k)
                Dυ
                (fun x => StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
                            σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                υ
                (fun i x => Dυ i x -
                  StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
                (fun x => σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                (fun x => υ x -
                  StationaryMFG.Theorems.SimplePower.Banach.uOf q x) := by
  -- Closure over the universal `(ctx, q, hq_K0_W, hVI)`, the signed test
  -- data `(σ, hσ, S, hS, hSfin)`, the user probe `(υ, Dυ)` with its
  -- Banach-embedding certificates, and the W-form `hWeak_υ` hypothesis.
  intro ctx q hq_K0_W hVI σ hσ S hS hSfin υ Dυ hυ_memSob hDυ_memLp hWeak_υ
  -- Descend `q ∈ K0_Aepsi_W → q ∈ K0_Aepsi` for the supplier.
  have hq_K0 :
      q ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi d
            (hpow.β + 1) (hpow.α * (hpow.β + 1) / hpow.β) :=
    StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi_W_subset_K0_Aepsi
      d (hpow.β + 1) (hpow.α * (hpow.β + 1) / hpow.β) hq_K0_W
  -- Dispatch to the W-form user-probe Minty discharge, consuming the
  -- per-query operator-continuity certificate from `hSignedUserProbeCont`.
  exact StationaryMFG.Theorems.SimplePower.Banach.hVIeps_signed_user_probe_of_KAepsi_W_VI
    ctx.auxHypsK q hq_K0_W hVI σ hσ S hS hSfin υ Dυ hυ_memSob hDυ_memLp hWeak_υ
    (hSignedUserProbeCont q hq_K0 σ hσ S hS hSfin υ Dυ hυ_memSob hDυ_memLp)

/-! ### `paperSolFor-minty-transport` — ε-level transport-family Minty
conclusion

The producer `paperSection8_hMinty_transport_of_paperHypotheses` discharges
the `hMinty_transport` field of `PaperSolForK V H DpH hpow k`. This is the
fourth of the five Minty producers (Phase D4.2 closure-band v7) and the
**last base Minty family**; it unblocks the side-inputs sweep.

Per the `infra-P5-T10-v7-paperSolFor-pre-scope` audit (Child #7), the
ε-level transport-family Minty conclusion at the specific Browder–Minty
witness `q` extracted by `exists_regularizedBareSolution_K` is delivered
by the existing chain
```
mfgOperatorEpsPair_tendsto_transport_perturbation_of_paperHypotheses
  + hVIeps_transport_of_KAepsi_VI
```
(both in `Banach/RegularizedSequence.lean`). The first builds the
operator-continuity `Tendsto` certificate at the strict-positive
perturbation `μ_n := σ + 1/(n+1)` (where `σ ≥ 0` a.e. is the user-supplied
test density) from the per-query residue dominator bundle
`TransportTendstoResidueOf`; the second uses that `Tendsto` to upgrade
the K_Aepsi-form weak VI to the strong transport-family VI at the bare-
function endpoints.

This is the **ε-level layer** (`mfgOperatorEpsPair`), *not* the
δ-limit `transportSegInputsAuth` layer; the two have distinct types
and domains (per `docs/PAPERSOLFOR_SCOPE.md` D-pre.4).

The producer takes the same six paper hypotheses as the existing
`regularizedSequenceData_of_paperHypotheses` (`Banach/
RegularizedSequence.lean:7378`) plus the per-query residue supplier
`residueOf_transport : ∀ q hq_K0 σ υ φ …, TransportTendstoResidueOf …`.
No new authorisation parameter is introduced. This mirrors the iter-
0605 (set), iter-0611 (signed), iter-0612 (signed-user-probe) producers
above.

**Phase 0 audit summary (recorded inline; see task notes for full text):**
The three existing per-query suppliers consumed by iter-0605/0611/0612
(`residueOf_set`, `residueOf_signed`, `hSignedUserProbeCont`) are NOT
derivable from the paper hypotheses `(hpow, hRegH, hHat0, hFin, hAgree)`
alone — they package the abstract dominator certificates
(`Gh, Eh, Gf, Ef, Gm, Em` + their `MemLpPer` + a.e. bounds) needed by
the operator-continuity aggregator. The same is true of
`residueOf_transport` here. These per-query suppliers are NOT global
auths on `T10PaperResidues.of_paperHypotheses`; they are consumed at
the per-`k`/per-query level (same shape used by
`regularizedSequenceData_of_paperHypotheses`, lines 7196-7210). The
final `PaperSolForK.of_paperHypotheses` aggregator (Phase 4 of the
rewire plan) will need to instantiate these suppliers internally via
the planned Hamiltonian power-growth/Hölder dominator construction
lemmas, paralleling the `Eh_*`/`Gf_*`/`Gm_*`/`Em_*`/`Gh_*`/`Ef_*`
estimates already in `Hamiltonian/Estimates.lean`. **Flagged as a
critical concern for `paperSolFor-final`:** if these dominator-bundle
construction lemmas don't yet exist at the paper-hypothesis level, the
aggregator cannot drain the per-query suppliers without them. -/

/-- **ε-level transport-family Minty producer.**

Given the paper hypotheses `(hpow, hRegH, hHat0, hFin, hAgree)` and a
per-query residue supplier `residueOf_transport`, build the
`hMinty_transport` field of `PaperSolForK V H DpH hpow k` at the paper-
canonical exponents.

The field body is universally quantified over `(ctx, q, hq_K0, hVI)` and
over the transport test data `(σ, υ, φ)` with `σ ≥ 0` a.e. and Banach-
embedding certificates `(hσ_memLp, hυ_memSob, hφ_memLp)`. The discharge
dispatches to:

* `Banach.mfgOperatorEpsPair_tendsto_transport_perturbation_of_paperHypotheses`
  for the ε-level operator-continuity `Tendsto` along
  `μ_n := σ + 1/(n+1)`, fed by the residue's full six-dominator bundle
  `(Gh, Eh, Gf, Ef, Gm, Em)`; and
* `Banach.hVIeps_transport_of_KAepsi_VI` for the strong-VI upgrade from
  the K_Aepsi-form weak VI.

Reuse pattern: this is the per-`k` slice of the `hMinty_transport`
argument to `exists_regularizedBareSolution_K` constructed inside
`regularizedSequenceData_of_paperHypotheses`
(`Banach/RegularizedSequence.lean:7196-7211`), specialised at
`ε := paperEpsSeq k` and the paper-canonical exponent quadruple. -/
noncomputable def paperSection8_hMinty_transport_of_paperHypotheses
    {d : ℕ}
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (hRegH : Hamiltonian.RegularityH (d := d) H DpH)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hFin : Hamiltonian.Hext_finite_at_zero (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    (k : ℕ)
    [Fact (1 ≤ ENNReal.ofReal (hpow.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))]
    -- Per-query residue supplier for the transport family.
    (residueOf_transport :
      ∀ (q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
                (hpow.β + 1)
                (hpow.α * (hpow.β + 1) / hpow.β)),
        q ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi d
              (hpow.β + 1)
              (hpow.α * (hpow.β + 1) / hpow.β) →
        ∀ (σ υ : (Fin d → ℝ) → ℝ)
          (φ : Fin d → (Fin d → ℝ) → ℝ),
          (∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
              0 ≤ σ x) →
          Periodic.MemLpPer (d := d)
            (ENNReal.ofReal (hpow.β + 1)) σ →
          Periodic.MemSobolevPer (d := d)
            (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) υ →
          (∀ i, Periodic.MemLpPer (d := d)
                  (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))
                  (φ i)) →
            StationaryMFG.Theorems.SimplePower.Banach.TransportTendstoResidueOf
              (d := d) (V := V) (H := H) (DpH := DpH)
              (βBarReal := hpow.β + 1)
              (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
              hpow q σ υ φ) :
    ∀ (ctx : StationaryMFG.Theorems.SimplePower.Banach.AepsiUniformContextK
              (d := d) (paperEpsSeq k) V H DpH
              (hpow.α * (hpow.β + 1) / hpow.β)
              (hpow.β + 1)
              ((hpow.β + 1) / hpow.β)
              ((hpow.α * (hpow.β + 1) / hpow.β)
                / (hpow.α * (hpow.β + 1) / hpow.β - 1))),
    ∀ (q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
              (hpow.β + 1)
              (hpow.α * (hpow.β + 1) / hpow.β)),
      q ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi d
              (hpow.β + 1)
              (hpow.α * (hpow.β + 1) / hpow.β) →
      (∀ q' ∈ StationaryMFG.Theorems.SimplePower.Banach.K_Aepsi d
                (hpow.β + 1)
                (hpow.α * (hpow.β + 1) / hpow.β),
          0 ≤ StationaryMFG.Theorems.SimplePower.Banach.Aepsi_CLM_opK
                (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
                (βBarReal := hpow.β + 1)
                (βBarReal' := (hpow.β + 1) / hpow.β)
                (γBarReal' := (hpow.α * (hpow.β + 1) / hpow.β)
                                / (hpow.α * (hpow.β + 1) / hpow.β - 1))
                V H DpH ctx.auxHypsK (paperEpsSeq k) q' (q' - q)) →
      ∀ (σ υ : (Fin d → ℝ) → ℝ)
        (φ : Fin d → (Fin d → ℝ) → ℝ),
        (∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
            0 ≤ σ x) →
        Periodic.MemLpPer (d := d)
          (ENNReal.ofReal (hpow.β + 1)) σ →
        Periodic.MemSobolevPer (d := d)
          (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) υ →
        (∀ i, Periodic.MemLpPer (d := d)
                (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) (φ i)) →
        (∀ i, Periodic.HasWeakDerivPer (d := d) i υ (φ i)) →
          0 ≤ mfgOperatorEpsPair
                (V := V) (H := H) (DpH := DpH)
                (hpow.α * (hpow.β + 1) / hpow.β) (paperEpsSeq k)
                φ σ υ
                (fun i x => φ i x -
                  StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
                (σ - StationaryMFG.Theorems.SimplePower.Banach.mOf q)
                (υ - StationaryMFG.Theorems.SimplePower.Banach.uOf q) := by
  -- Derive the `SimplePowerExponentFacts` bundle at the paper exponents from
  -- `hpow`. This is the same cast used by
  -- `paperSection8_hMinty_set_of_paperHypotheses` (see above, ~line 5220).
  set βBarReal : ℝ := hpow.β + 1 with hβBarReal_def
  set γBarReal : ℝ := hpow.α * (hpow.β + 1) / hpow.β with hγBarReal_def
  set βBarReal' : ℝ := (hpow.β + 1) / hpow.β with hβBarReal'_def
  have hExp_paper :
      SimplePowerExponentFacts
          (SimplePowerExponentFacts.paperGammaBarReal hpow.α hpow.β)
          (SimplePowerExponentFacts.paperBetaBar hpow.β)
          (SimplePowerExponentFacts.paperGammaBar hpow.α hpow.β)
          (SimplePowerExponentFacts.paperBetaBarPrime hpow.β) :=
    SimplePowerExponentFacts.ofPowerGrowth hpow
  have hExp :
      SimplePowerExponentFacts γBarReal
          (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
          (ENNReal.ofReal βBarReal') := by
    have h1 :
        (SimplePowerExponentFacts.paperBetaBar hpow.β)
          = ENNReal.ofReal βBarReal := by
      simp [SimplePowerExponentFacts.paperBetaBar, hβBarReal_def]
    have h2 :
        (SimplePowerExponentFacts.paperGammaBar hpow.α hpow.β)
          = ENNReal.ofReal γBarReal := by
      simp [SimplePowerExponentFacts.paperGammaBar, hγBarReal_def]
    have h3 :
        (SimplePowerExponentFacts.paperBetaBarPrime hpow.β)
          = ENNReal.ofReal βBarReal' := by
      simp [SimplePowerExponentFacts.paperBetaBarPrime, hβBarReal'_def]
    have h4 :
        (SimplePowerExponentFacts.paperGammaBarReal hpow.α hpow.β)
          = γBarReal := by
      simp [SimplePowerExponentFacts.paperGammaBarReal, hγBarReal_def]
    have := hExp_paper
    rw [h1, h2, h3, h4] at this
    exact this
  -- Closure over the universal `(ctx, q, hq_K0, hVI)` and the transport
  -- test data `(σ, υ, φ)` with its non-negativity and Banach-embedding
  -- certificates.
  -- **Phase 5 step3d**: `_hWeak_υ` consumed as a slot but unused.
  intro ctx q hq_K0 hVI σ υ φ hσ_nn hσ_memLp hυ_memSob hφ_memLp _hWeak_υ
  -- Extract the per-query transport-family residue dominator bundle.
  set r :=
    residueOf_transport q hq_K0 σ υ φ hσ_nn
      hσ_memLp hυ_memSob hφ_memLp with hr_def
  -- Build the ε-level operator-continuity `Tendsto` certificate along
  -- `μ_n := σ + 1/(n+1)`.
  have hCont :=
    StationaryMFG.Theorems.SimplePower.Banach.mfgOperatorEpsPair_tendsto_transport_perturbation_of_paperHypotheses_of_aestronglyMeasurable
      (ε := paperEpsSeq k)
      (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
      (βBarReal := hpow.β + 1)
      (βBarReal' := (hpow.β + 1) / hpow.β)
      (γBarReal' := (hpow.α * (hpow.β + 1) / hpow.β)
                      / (hpow.α * (hpow.β + 1) / hpow.β - 1))
      hpow hRegH hExp hHat0 hFin hAgree
      φ υ (StationaryMFG.Theorems.SimplePower.Banach.uOf q)
      (StationaryMFG.Theorems.SimplePower.Banach.DuOf q)
      (StationaryMFG.Theorems.SimplePower.Banach.mOf q) V σ
      r.hσ r.hm r.hV r.hυ r.hu r.hφ r.hDu hσ_nn hσ_memLp
      r.Gh r.Eh r.hGh_memLp r.hEh_memLp r.hGh_bd r.hEh_bd
      r.Gf r.Ef r.hGf_memLp r.hEf_memLp r.hGf_bd r.hEf_bd
      r.Gm r.Em r.hGm_memLp r.hEm_memLp r.hGm_bd r.hEm_bd
  -- Upgrade the K_Aepsi-form weak VI to the strong transport-family VI at
  -- the bare-function endpoints.
  exact StationaryMFG.Theorems.SimplePower.Banach.hVIeps_transport_of_KAepsi_VI
    ctx.auxHypsK q hVI σ υ φ hσ_nn
    hσ_memLp hυ_memSob hφ_memLp hCont

/-! ### Hext-free `_of_rc0` transport Minty producer (T3 step 8)

ε-generic, `Hext_finite_at_zero`-free sibling of
`paperSection8_hMinty_transport_of_paperHypotheses`; same two swaps as
the set/signed `_of_rc0` producers (takes `hH_rc0`, routes through the
step-7 transport aesm→rc0 bridge). -/
open StationaryMFG.Theorems.SimplePower.Banach in
noncomputable def paperSection8_hMinty_transport_of_paperHypotheses_of_rc0
    {d : ℕ}
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (hRegH : Hamiltonian.RegularityH (d := d) H DpH)
    (hH_rc0 :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ∀ p : Fin d → ℝ,
          Filter.Tendsto (fun m : ℝ => H x p m) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
            (nhds (H x p 0)))
    {ε : ℝ}
    [Fact (1 ≤ ENNReal.ofReal (hpow.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))]
    -- Per-query residue supplier for the transport family.
    (residueOf_transport :
      ∀ (q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
                (hpow.β + 1)
                (hpow.α * (hpow.β + 1) / hpow.β)),
        q ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi d
              (hpow.β + 1)
              (hpow.α * (hpow.β + 1) / hpow.β) →
        ∀ (σ υ : (Fin d → ℝ) → ℝ)
          (φ : Fin d → (Fin d → ℝ) → ℝ),
          (∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
              0 ≤ σ x) →
          Periodic.MemLpPer (d := d)
            (ENNReal.ofReal (hpow.β + 1)) σ →
          Periodic.MemSobolevPer (d := d)
            (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) υ →
          (∀ i, Periodic.MemLpPer (d := d)
                  (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))
                  (φ i)) →
            StationaryMFG.Theorems.SimplePower.Banach.TransportTendstoResidueOf
              (d := d) (V := V) (H := H) (DpH := DpH)
              (βBarReal := hpow.β + 1)
              (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
              hpow q σ υ φ) :
    ∀ (ctx : StationaryMFG.Theorems.SimplePower.Banach.AepsiUniformContextK
              (d := d) ε V H DpH
              (hpow.α * (hpow.β + 1) / hpow.β)
              (hpow.β + 1)
              ((hpow.β + 1) / hpow.β)
              ((hpow.α * (hpow.β + 1) / hpow.β)
                / (hpow.α * (hpow.β + 1) / hpow.β - 1))),
    ∀ (q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
              (hpow.β + 1)
              (hpow.α * (hpow.β + 1) / hpow.β)),
      q ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi d
              (hpow.β + 1)
              (hpow.α * (hpow.β + 1) / hpow.β) →
      (∀ q' ∈ StationaryMFG.Theorems.SimplePower.Banach.K_Aepsi d
                (hpow.β + 1)
                (hpow.α * (hpow.β + 1) / hpow.β),
          0 ≤ StationaryMFG.Theorems.SimplePower.Banach.Aepsi_CLM_opK
                (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
                (βBarReal := hpow.β + 1)
                (βBarReal' := (hpow.β + 1) / hpow.β)
                (γBarReal' := (hpow.α * (hpow.β + 1) / hpow.β)
                                / (hpow.α * (hpow.β + 1) / hpow.β - 1))
                V H DpH ctx.auxHypsK ε q' (q' - q)) →
      ∀ (σ υ : (Fin d → ℝ) → ℝ)
        (φ : Fin d → (Fin d → ℝ) → ℝ),
        (∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
            0 ≤ σ x) →
        Periodic.MemLpPer (d := d)
          (ENNReal.ofReal (hpow.β + 1)) σ →
        Periodic.MemSobolevPer (d := d)
          (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) υ →
        (∀ i, Periodic.MemLpPer (d := d)
                (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) (φ i)) →
        (∀ i, Periodic.HasWeakDerivPer (d := d) i υ (φ i)) →
          0 ≤ mfgOperatorEpsPair
                (V := V) (H := H) (DpH := DpH)
                (hpow.α * (hpow.β + 1) / hpow.β) ε
                φ σ υ
                (fun i x => φ i x -
                  StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
                (σ - StationaryMFG.Theorems.SimplePower.Banach.mOf q)
                (υ - StationaryMFG.Theorems.SimplePower.Banach.uOf q) := by
  set βBarReal : ℝ := hpow.β + 1 with hβBarReal_def
  set γBarReal : ℝ := hpow.α * (hpow.β + 1) / hpow.β with hγBarReal_def
  set βBarReal' : ℝ := (hpow.β + 1) / hpow.β with hβBarReal'_def
  have hExp_paper :
      SimplePowerExponentFacts
          (SimplePowerExponentFacts.paperGammaBarReal hpow.α hpow.β)
          (SimplePowerExponentFacts.paperBetaBar hpow.β)
          (SimplePowerExponentFacts.paperGammaBar hpow.α hpow.β)
          (SimplePowerExponentFacts.paperBetaBarPrime hpow.β) :=
    SimplePowerExponentFacts.ofPowerGrowth hpow
  have hExp :
      SimplePowerExponentFacts γBarReal
          (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
          (ENNReal.ofReal βBarReal') := by
    have h1 :
        (SimplePowerExponentFacts.paperBetaBar hpow.β)
          = ENNReal.ofReal βBarReal := by
      simp [SimplePowerExponentFacts.paperBetaBar, hβBarReal_def]
    have h2 :
        (SimplePowerExponentFacts.paperGammaBar hpow.α hpow.β)
          = ENNReal.ofReal γBarReal := by
      simp [SimplePowerExponentFacts.paperGammaBar, hγBarReal_def]
    have h3 :
        (SimplePowerExponentFacts.paperBetaBarPrime hpow.β)
          = ENNReal.ofReal βBarReal' := by
      simp [SimplePowerExponentFacts.paperBetaBarPrime, hβBarReal'_def]
    have h4 :
        (SimplePowerExponentFacts.paperGammaBarReal hpow.α hpow.β)
          = γBarReal := by
      simp [SimplePowerExponentFacts.paperGammaBarReal, hγBarReal_def]
    have := hExp_paper
    rw [h1, h2, h3, h4] at this
    exact this
  intro ctx q hq_K0 hVI σ υ φ hσ_nn hσ_memLp hυ_memSob hφ_memLp _hWeak_υ
  set r :=
    residueOf_transport q hq_K0 σ υ φ hσ_nn
      hσ_memLp hυ_memSob hφ_memLp with hr_def
  have hCont :=
    StationaryMFG.Theorems.SimplePower.Banach.mfgOperatorEpsPair_tendsto_transport_perturbation_of_paperHypotheses_of_aestronglyMeasurable_of_rc0
      (ε := ε)
      (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
      (βBarReal := hpow.β + 1)
      (βBarReal' := (hpow.β + 1) / hpow.β)
      (γBarReal' := (hpow.α * (hpow.β + 1) / hpow.β)
                      / (hpow.α * (hpow.β + 1) / hpow.β - 1))
      hpow hRegH hExp hH_rc0
      φ υ (StationaryMFG.Theorems.SimplePower.Banach.uOf q)
      (StationaryMFG.Theorems.SimplePower.Banach.DuOf q)
      (StationaryMFG.Theorems.SimplePower.Banach.mOf q) V σ
      r.hσ r.hm r.hV r.hυ r.hu r.hφ r.hDu hσ_nn hσ_memLp
      r.Gh r.Eh r.hGh_memLp r.hEh_memLp r.hGh_bd r.hEh_bd
      r.Gf r.Ef r.hGf_memLp r.hEf_memLp r.hGf_bd r.hEf_bd
      r.Gm r.Em r.hGm_memLp r.hEm_memLp r.hGm_bd r.hEm_bd
  exact StationaryMFG.Theorems.SimplePower.Banach.hVIeps_transport_of_KAepsi_VI
    ctx.auxHypsK q hVI σ υ φ hσ_nn
    hσ_memLp hυ_memSob hφ_memLp hCont

/-- **`measurable_H`-free transport-family Minty producer** (D2b-1c-ii-c4b).

`aeMeasH`-input sibling of
`paperSection8_hMinty_transport_of_paperHypotheses_of_rc0`: it drops the
strict `RegularityH`/`HypothesisPowerGrowth` binders and instead consumes
the genuine individual H/DpH fields (bare exponents `α β`, `hDpH_meas`,
`hcont_H_pm`, `hcont_DpH_pm`, `hDpH_upper`), routing the inner operator
tendsto through the aesm-input `_of_aeMeasH` keystone
`mfgOperatorEpsPair_tendsto_transport_perturbation_of_paperHypotheses_of_aestronglyMeasurable_of_rc0_of_aeMeasH`,
which takes the boundary H AE composites (carried by the bare residue
bundle `TransportTendstoResidueOfBare`) instead of `hRegH.measurable_H`.

This is instantiable at `H := HdeltaK0`: the H AE composites are supplied
by `aemeasurable_HdeltaK0_comp_of_rc0`. The strict `_of_rc0` producer
above is left byte-for-byte intact for T1/T2. -/
noncomputable def paperSection8_hMinty_transport_of_paperHypotheses_of_rc0_of_aeMeasH
    {d : ℕ}
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    {C α β : ℝ} (hα : 1 < α) (hβ : 0 < β)
    (hDpH_meas : Measurable
      (fun (xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ) => DpH xpm.1 xpm.2.1 xpm.2.2))
    (hcont_H_pm :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ContinuousOn (fun (pm : (Fin d → ℝ) × ℝ) => H x pm.1 pm.2)
          {pm | 0 < pm.2})
    (hcont_DpH_pm :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ContinuousOn (fun (pm : (Fin d → ℝ) × ℝ) => DpH x pm.1 pm.2)
          {pm | 0 < pm.2})
    (hDpH_upper :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ∀ p m, 0 < m →
          ‖DpH x p m‖ ≤ C * (‖p‖ ^ (α - 1) + m ^ (β - β / α) + 1))
    (hH_rc0 :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ∀ p : Fin d → ℝ,
          Filter.Tendsto (fun m : ℝ => H x p m) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
            (nhds (H x p 0)))
    {ε : ℝ}
    [Fact (1 ≤ ENNReal.ofReal (β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (α * (β + 1) / β))]
    -- Per-query bare-exponent residue supplier for the transport family.
    (residueOf_transport :
      ∀ (q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
                (β + 1)
                (α * (β + 1) / β)),
        q ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi d
              (β + 1)
              (α * (β + 1) / β) →
        ∀ (σ υ : (Fin d → ℝ) → ℝ)
          (φ : Fin d → (Fin d → ℝ) → ℝ),
          (∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
              0 ≤ σ x) →
          Periodic.MemLpPer (d := d)
            (ENNReal.ofReal (β + 1)) σ →
          Periodic.MemSobolevPer (d := d)
            (ENNReal.ofReal (α * (β + 1) / β)) υ →
          (∀ i, Periodic.MemLpPer (d := d)
                  (ENNReal.ofReal (α * (β + 1) / β))
                  (φ i)) →
            StationaryMFG.Theorems.SimplePower.Banach.TransportTendstoResidueOfBare
              (d := d) (V := V) (H := H) (DpH := DpH)
              (βBarReal := β + 1)
              (γBarReal := α * (β + 1) / β)
              β q σ υ φ) :
    ∀ (ctx : StationaryMFG.Theorems.SimplePower.Banach.AepsiUniformContextK
              (d := d) ε V H DpH
              (α * (β + 1) / β)
              (β + 1)
              ((β + 1) / β)
              ((α * (β + 1) / β)
                / (α * (β + 1) / β - 1))),
    ∀ (q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
              (β + 1)
              (α * (β + 1) / β)),
      q ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi d
              (β + 1)
              (α * (β + 1) / β) →
      (∀ q' ∈ StationaryMFG.Theorems.SimplePower.Banach.K_Aepsi d
                (β + 1)
                (α * (β + 1) / β),
          0 ≤ StationaryMFG.Theorems.SimplePower.Banach.Aepsi_CLM_opK
                (γBarReal := α * (β + 1) / β)
                (βBarReal := β + 1)
                (βBarReal' := (β + 1) / β)
                (γBarReal' := (α * (β + 1) / β)
                                / (α * (β + 1) / β - 1))
                V H DpH ctx.auxHypsK ε q' (q' - q)) →
      ∀ (σ υ : (Fin d → ℝ) → ℝ)
        (φ : Fin d → (Fin d → ℝ) → ℝ),
        (∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
            0 ≤ σ x) →
        Periodic.MemLpPer (d := d)
          (ENNReal.ofReal (β + 1)) σ →
        Periodic.MemSobolevPer (d := d)
          (ENNReal.ofReal (α * (β + 1) / β)) υ →
        (∀ i, Periodic.MemLpPer (d := d)
                (ENNReal.ofReal (α * (β + 1) / β)) (φ i)) →
        (∀ i, Periodic.HasWeakDerivPer (d := d) i υ (φ i)) →
          0 ≤ mfgOperatorEpsPair
                (V := V) (H := H) (DpH := DpH)
                (α * (β + 1) / β) ε
                φ σ υ
                (fun i x => φ i x -
                  StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
                (σ - StationaryMFG.Theorems.SimplePower.Banach.mOf q)
                (υ - StationaryMFG.Theorems.SimplePower.Banach.uOf q) := by
  set βBarReal : ℝ := β + 1 with hβBarReal_def
  set γBarReal : ℝ := α * (β + 1) / β with hγBarReal_def
  set βBarReal' : ℝ := (β + 1) / β with hβBarReal'_def
  -- Bare-exponent `SimplePowerExponentFacts` from `standardPaper`.
  have hExp_paper :
      SimplePowerExponentFacts
          (SimplePowerExponentFacts.paperGammaBarReal α β)
          (SimplePowerExponentFacts.paperBetaBar β)
          (SimplePowerExponentFacts.paperGammaBar α β)
          (SimplePowerExponentFacts.paperBetaBarPrime β) :=
    SimplePowerExponentFacts.standardPaper hα hβ
  have hExp :
      SimplePowerExponentFacts γBarReal
          (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
          (ENNReal.ofReal βBarReal') := by
    have h1 :
        (SimplePowerExponentFacts.paperBetaBar β)
          = ENNReal.ofReal βBarReal := by
      simp [SimplePowerExponentFacts.paperBetaBar, hβBarReal_def]
    have h2 :
        (SimplePowerExponentFacts.paperGammaBar α β)
          = ENNReal.ofReal γBarReal := by
      simp [SimplePowerExponentFacts.paperGammaBar, hγBarReal_def]
    have h3 :
        (SimplePowerExponentFacts.paperBetaBarPrime β)
          = ENNReal.ofReal βBarReal' := by
      simp [SimplePowerExponentFacts.paperBetaBarPrime, hβBarReal'_def]
    have h4 :
        (SimplePowerExponentFacts.paperGammaBarReal α β)
          = γBarReal := by
      simp [SimplePowerExponentFacts.paperGammaBarReal, hγBarReal_def]
    have := hExp_paper
    rw [h1, h2, h3, h4] at this
    exact this
  intro ctx q hq_K0 hVI σ υ φ hσ_nn hσ_memLp hυ_memSob hφ_memLp _hWeak_υ
  set r :=
    residueOf_transport q hq_K0 σ υ φ hσ_nn
      hσ_memLp hυ_memSob hφ_memLp with hr_def
  -- `measurable_H`-free aesm-input keystone (D2b-1c-ii-c4b).
  have hCont :=
    StationaryMFG.Theorems.SimplePower.Banach.mfgOperatorEpsPair_tendsto_transport_perturbation_of_paperHypotheses_of_aestronglyMeasurable_of_rc0_of_aeMeasH
      (ε := ε)
      (γBarReal := α * (β + 1) / β)
      (βBarReal := β + 1)
      (βBarReal' := (β + 1) / β)
      (γBarReal' := (α * (β + 1) / β)
                      / (α * (β + 1) / β - 1))
      (C := C) (α := α) (β := β)
      hα hβ hDpH_meas hcont_H_pm hcont_DpH_pm hDpH_upper hExp hH_rc0
      φ υ (StationaryMFG.Theorems.SimplePower.Banach.uOf q)
      (StationaryMFG.Theorems.SimplePower.Banach.DuOf q)
      (StationaryMFG.Theorems.SimplePower.Banach.mOf q) V σ
      r.hσ r.hm r.hV r.hυ r.hu r.hφ r.hDu hσ_nn hσ_memLp
      r.hHcomp_ae_n r.hHcomp_ae_lim
      r.Gh r.Eh r.hGh_memLp r.hEh_memLp r.hGh_bd r.hEh_bd
      r.Gf r.Ef r.hGf_memLp r.hEf_memLp r.hGf_bd r.hEf_bd
      r.Gm r.Em r.hGm_memLp r.hEm_memLp r.hGm_bd r.hEm_bd
  exact StationaryMFG.Theorems.SimplePower.Banach.hVIeps_transport_of_KAepsi_VI
    ctx.auxHypsK q hVI σ υ φ hσ_nn
    hσ_memLp hυ_memSob hφ_memLp hCont

/-! ### `paperSolFor-final-phase5-hWeakDeriv-step3b` — W-form transport-family
Minty producer

W-form sibling of `paperSection8_hMinty_transport_of_paperHypotheses`
(iter-0701/0702 W-form Minty suppliers programme). The transport family
test point is built inline as `qn := banachPairOfBare (σ + 1/(n+1)) υ φ …`,
so — unlike the signed family — the test point's `υ`/`Dυ` factors are
user-supplied and the K_Aepsi_W weak-derivative tie is NOT inherited
from `q`. The W-form statement therefore takes an extra
`hWeak_υ : ∀ i, HasWeakDerivPer i υ (φ i)` hypothesis (paper-faithful;
in the paper the test direction lies in the Sobolev space and the
weak-derivative tie is automatic).

Differences from the K-form sibling:

* Witness: takes `q ∈ K0_Aepsi_W d βBar γBar` (refined non-negativity
  cone) instead of `K0_Aepsi`.
* VI: takes `hVI` quantifying over `q' ∈ K_Aepsi_W d βBar γBar`.
* Context: takes `ctx : AepsiUniformContextK_W` instead of
  `AepsiUniformContextK`.
* Extra hypothesis: `hWeak_υ : ∀ i, HasWeakDerivPer i υ (φ i)` for
  the user-supplied test pair.
* Backing analytic lemma: dispatches to
  `Banach.hVIeps_transport_of_KAepsi_W_VI` instead of
  `hVIeps_transport_of_KAepsi_VI`.

The residue supplier `residueOf_transport : … TransportTendstoResidueOf`
is unchanged (residue dominator bundle is at the bare-function layer).
The descent `K0_Aepsi_W → K0_Aepsi` for the residue supplier goes via
`K0_Aepsi_W_subset_K0_Aepsi`.

No new authorisation parameter. -/

/-- **ε-level transport-family W-form Minty producer.** Builds the
W-form `hMinty_transport` field at the paper-canonical exponents. -/
noncomputable def paperSection8_hMinty_transport_W_of_paperHypotheses
    {d : ℕ}
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (hRegH : Hamiltonian.RegularityH (d := d) H DpH)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hFin : Hamiltonian.Hext_finite_at_zero (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    (k : ℕ)
    [Fact (1 ≤ ENNReal.ofReal (hpow.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))]
    -- Per-query residue supplier for the transport family (identical
    -- to the K-form sibling's, since the residue is at the bare-function
    -- level).
    (residueOf_transport :
      ∀ (q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
                (hpow.β + 1)
                (hpow.α * (hpow.β + 1) / hpow.β)),
        q ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi d
              (hpow.β + 1)
              (hpow.α * (hpow.β + 1) / hpow.β) →
        ∀ (σ υ : (Fin d → ℝ) → ℝ)
          (φ : Fin d → (Fin d → ℝ) → ℝ),
          (∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
              0 ≤ σ x) →
          Periodic.MemLpPer (d := d)
            (ENNReal.ofReal (hpow.β + 1)) σ →
          Periodic.MemSobolevPer (d := d)
            (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) υ →
          (∀ i, Periodic.MemLpPer (d := d)
                  (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))
                  (φ i)) →
            StationaryMFG.Theorems.SimplePower.Banach.TransportTendstoResidueOf
              (d := d) (V := V) (H := H) (DpH := DpH)
              (βBarReal := hpow.β + 1)
              (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
              hpow q σ υ φ) :
    ∀ (ctx : StationaryMFG.Theorems.SimplePower.Banach.AepsiUniformContextK_W
              (d := d) (paperEpsSeq k) V H DpH
              (hpow.α * (hpow.β + 1) / hpow.β)
              (hpow.β + 1)
              ((hpow.β + 1) / hpow.β)
              ((hpow.α * (hpow.β + 1) / hpow.β)
                / (hpow.α * (hpow.β + 1) / hpow.β - 1))),
    ∀ (q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
              (hpow.β + 1)
              (hpow.α * (hpow.β + 1) / hpow.β)),
      q ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi_W d
              (hpow.β + 1)
              (hpow.α * (hpow.β + 1) / hpow.β) →
      (∀ q' ∈ StationaryMFG.Theorems.SimplePower.Banach.K_Aepsi_W d
                (hpow.β + 1)
                (hpow.α * (hpow.β + 1) / hpow.β),
          0 ≤ StationaryMFG.Theorems.SimplePower.Banach.Aepsi_CLM_opK
                (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
                (βBarReal := hpow.β + 1)
                (βBarReal' := (hpow.β + 1) / hpow.β)
                (γBarReal' := (hpow.α * (hpow.β + 1) / hpow.β)
                                / (hpow.α * (hpow.β + 1) / hpow.β - 1))
                V H DpH ctx.auxHypsK (paperEpsSeq k) q' (q' - q)) →
      ∀ (σ υ : (Fin d → ℝ) → ℝ)
        (φ : Fin d → (Fin d → ℝ) → ℝ),
        (∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
            0 ≤ σ x) →
        Periodic.MemLpPer (d := d)
          (ENNReal.ofReal (hpow.β + 1)) σ →
        Periodic.MemSobolevPer (d := d)
          (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) υ →
        (∀ i, Periodic.MemLpPer (d := d)
                (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) (φ i)) →
        (∀ i, Periodic.HasWeakDerivPer (d := d) i υ (φ i)) →
          0 ≤ mfgOperatorEpsPair
                (V := V) (H := H) (DpH := DpH)
                (hpow.α * (hpow.β + 1) / hpow.β) (paperEpsSeq k)
                φ σ υ
                (fun i x => φ i x -
                  StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
                (σ - StationaryMFG.Theorems.SimplePower.Banach.mOf q)
                (υ - StationaryMFG.Theorems.SimplePower.Banach.uOf q) := by
  -- Derive `SimplePowerExponentFacts` at the paper exponents.
  set βBarReal : ℝ := hpow.β + 1 with hβBarReal_def
  set γBarReal : ℝ := hpow.α * (hpow.β + 1) / hpow.β with hγBarReal_def
  set βBarReal' : ℝ := (hpow.β + 1) / hpow.β with hβBarReal'_def
  have hExp_paper :
      SimplePowerExponentFacts
          (SimplePowerExponentFacts.paperGammaBarReal hpow.α hpow.β)
          (SimplePowerExponentFacts.paperBetaBar hpow.β)
          (SimplePowerExponentFacts.paperGammaBar hpow.α hpow.β)
          (SimplePowerExponentFacts.paperBetaBarPrime hpow.β) :=
    SimplePowerExponentFacts.ofPowerGrowth hpow
  have hExp :
      SimplePowerExponentFacts γBarReal
          (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
          (ENNReal.ofReal βBarReal') := by
    have h1 :
        (SimplePowerExponentFacts.paperBetaBar hpow.β)
          = ENNReal.ofReal βBarReal := by
      simp [SimplePowerExponentFacts.paperBetaBar, hβBarReal_def]
    have h2 :
        (SimplePowerExponentFacts.paperGammaBar hpow.α hpow.β)
          = ENNReal.ofReal γBarReal := by
      simp [SimplePowerExponentFacts.paperGammaBar, hγBarReal_def]
    have h3 :
        (SimplePowerExponentFacts.paperBetaBarPrime hpow.β)
          = ENNReal.ofReal βBarReal' := by
      simp [SimplePowerExponentFacts.paperBetaBarPrime, hβBarReal'_def]
    have h4 :
        (SimplePowerExponentFacts.paperGammaBarReal hpow.α hpow.β)
          = γBarReal := by
      simp [SimplePowerExponentFacts.paperGammaBarReal, hγBarReal_def]
    have := hExp_paper
    rw [h1, h2, h3, h4] at this
    exact this
  -- Closure: bind universal `(ctx, q, hq_K0_W, hVI)` and the transport
  -- test data with its non-negativity, Banach-embedding certificates,
  -- and the W-form `hWeak_υ` hypothesis.
  intro ctx q hq_K0_W hVI σ υ φ hσ_nn hσ_memLp hυ_memSob hφ_memLp hWeak_υ
  -- Descend `q ∈ K0_Aepsi_W → q ∈ K0_Aepsi` for the residue supplier.
  have hq_K0 :
      q ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi d
            βBarReal γBarReal :=
    StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi_W_subset_K0_Aepsi
      d βBarReal γBarReal hq_K0_W
  -- Extract the per-query transport-family residue dominator bundle.
  set r :=
    residueOf_transport q hq_K0 σ υ φ hσ_nn
      hσ_memLp hυ_memSob hφ_memLp with hr_def
  -- Build the ε-level operator-continuity `Tendsto` certificate along
  -- `μ_n := σ + 1/(n+1)`. Identical call as the K-form sibling.
  have hCont :=
    StationaryMFG.Theorems.SimplePower.Banach.mfgOperatorEpsPair_tendsto_transport_perturbation_of_paperHypotheses_of_aestronglyMeasurable
      (ε := paperEpsSeq k)
      (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
      (βBarReal := hpow.β + 1)
      (βBarReal' := (hpow.β + 1) / hpow.β)
      (γBarReal' := (hpow.α * (hpow.β + 1) / hpow.β)
                      / (hpow.α * (hpow.β + 1) / hpow.β - 1))
      hpow hRegH hExp hHat0 hFin hAgree
      φ υ (StationaryMFG.Theorems.SimplePower.Banach.uOf q)
      (StationaryMFG.Theorems.SimplePower.Banach.DuOf q)
      (StationaryMFG.Theorems.SimplePower.Banach.mOf q) V σ
      r.hσ r.hm r.hV r.hυ r.hu r.hφ r.hDu hσ_nn hσ_memLp
      r.Gh r.Eh r.hGh_memLp r.hEh_memLp r.hGh_bd r.hEh_bd
      r.Gf r.Ef r.hGf_memLp r.hEf_memLp r.hGf_bd r.hEf_bd
      r.Gm r.Em r.hGm_memLp r.hEm_memLp r.hGm_bd r.hEm_bd
  -- Upgrade via the W-form `hVIeps_transport_of_KAepsi_W_VI`.
  exact StationaryMFG.Theorems.SimplePower.Banach.hVIeps_transport_of_KAepsi_W_VI
    ctx.auxHypsK q hVI σ υ φ hσ_nn
    hσ_memLp hυ_memSob hφ_memLp hWeak_υ hCont

/-! ### `paperSolFor-minty-signed-user-triple` — ε-level signed-family
**user-triple** Minty conclusion

The producer `paperSection8_hMinty_signed_user_triple_of_paperHypotheses`
discharges the `hMinty_signed_user_triple` field of
`PaperSolForK V H DpH hpow k`. This is the **fifth and last** Minty
producer (Phase D4.2 closure-band v7); it completes the base Minty
producer family and unblocks the supplier-closure pass.

Per the `infra-P5-T10-v7-paperSolFor-pre-scope` audit (Child #9), the
user-triple variant differs from the iter-0612 `hMinty_signed_user_probe`
variant by allowing the **primal density** in the perturbation
`μ_n := μ + σ · μ · 1_S + 1/(n+1)` to be a user-supplied `μ`
(rather than hardcoded at the witness's own `mOf q`), in addition to
the user-supplied probe `(Dυ, υ)`. The strict-positive admissibility
argument is unchanged: `μ ≥ 0` plus `1 + σ · 1_S ∈ [0, 2]`.

The chain `hVIeps_signed_user_triple_of_KAepsi_VI`
(`Banach/RegularizedSequence.lean:1095`) already implements the
ε-level Minty discharge at the user-triple shape, parametrised by its
own operator-continuity certificate `hCont` along
`μ_n := μ + σ · μ · 1_S + 1/(n+1)` at the user probe `(Dυ, υ)`.

Mirroring iter-0611/0612, the producer takes the same six paper
hypotheses plus a **per-query user-triple continuity supplier**
`hSignedUserTripleCont`. No new authorisation parameter is introduced.
The supplier is *not* a global `T10PaperResidues` auth; it is a
regular function parameter that the chain-level consumer (filed as
`paperSolFor-supplier-user-triple-cont`, a future closure task)
discharges by Hölder/Lp dominator control along the paper-canonical
power-growth hypotheses. -/

/-- **ε-level signed-family user-triple Minty producer.**

Given the paper hypotheses `(hpow, hRegH, hHat0, hFin, hAgree)` and a
per-query user-triple operator-continuity supplier
`hSignedUserTripleCont`, build the `hMinty_signed_user_triple` field
of `PaperSolForK V H DpH hpow k` at the paper-canonical exponents.

The field body is universally quantified over `(ctx, q, hq_K0, hVI)`,
the signed test data `(σ, hσ, S, hS, hSfin)`, the user primal density
`μ` (with `0 ≤ μ` a.e. and `MemLpPer βBar` embeddability), and the
user probe `(υ, Dυ)` with its Banach-embedding certificates
`(hυ_memSob, hDυ_memLp)`. The discharge dispatches to
`Banach.hVIeps_signed_user_triple_of_KAepsi_VI` (Child D″), consuming
the per-query continuity certificate supplied by
`hSignedUserTripleCont`.

The same `(hpow, hRegH, hHat0, hFin, hAgree)` paper hypotheses are
taken for shape parity with the iter-0605/0611/0612/0613 producers,
although the present discharge consumes none of them directly: the
analytic content is fully contained in the user-triple continuity
supplier. This mirrors iter-0611/0612's choice to preserve the
six-hypothesis signature for downstream auth-count counting. -/
noncomputable def paperSection8_hMinty_signed_user_triple_of_paperHypotheses
    {d : ℕ}
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (_hRegH : Hamiltonian.RegularityH (d := d) H DpH)
    (_hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (_hFin : Hamiltonian.Hext_finite_at_zero (d := d) H)
    (_hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    (k : ℕ)
    [Fact (1 ≤ ENNReal.ofReal (hpow.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))]
    -- Per-query user-triple operator-continuity supplier (analytic input,
    -- CONVENTIONS §8). Future closure task `paperSolFor-supplier-user-
    -- triple-cont` derives this from the paper power-growth/Hölder
    -- dominator control along `μ_n := μ + σ · μ · 1_S + 1/(n+1)` at the
    -- user probe `(Dυ, υ)` and user primal density `μ`.
    (hSignedUserTripleCont :
      ∀ (q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
                (hpow.β + 1)
                (hpow.α * (hpow.β + 1) / hpow.β)),
        q ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi d
              (hpow.β + 1)
              (hpow.α * (hpow.β + 1) / hpow.β) →
        ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
        ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
          (MeasureTheory.volume.restrict (Periodic.UnitCube d)) S < ⊤ →
        ∀ (μ υ : (Fin d → ℝ) → ℝ)
          (Dυ : Fin d → (Fin d → ℝ) → ℝ),
          (∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
              0 ≤ μ x) →
          Periodic.MemLpPer (d := d)
            (ENNReal.ofReal (hpow.β + 1)) μ →
          Periodic.MemSobolevPer (d := d)
            (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) υ →
          (∀ i, Periodic.MemLpPer (d := d)
                  (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) (Dυ i)) →
            Filter.Tendsto
              (fun n : ℕ =>
                mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                  (hpow.α * (hpow.β + 1) / hpow.β) (paperEpsSeq k)
                  Dυ
                  (fun x =>
                    μ x + σ * μ x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                      + 1 / ((n : ℝ) + 1))
                  υ
                  (fun i x => Dυ i x -
                    StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
                  (fun x =>
                    (μ x + σ * μ x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                      + 1 / ((n : ℝ) + 1)) -
                    StationaryMFG.Theorems.SimplePower.Banach.mOf q x)
                  (fun x => υ x -
                    StationaryMFG.Theorems.SimplePower.Banach.uOf q x))
              Filter.atTop
              (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                    (hpow.α * (hpow.β + 1) / hpow.β) (paperEpsSeq k)
                    Dυ
                    (fun x =>
                      μ x + σ * μ x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                    υ
                    (fun i x => Dυ i x -
                      StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
                    (fun x =>
                      (μ x + σ * μ x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) -
                      StationaryMFG.Theorems.SimplePower.Banach.mOf q x)
                    (fun x => υ x -
                      StationaryMFG.Theorems.SimplePower.Banach.uOf q x)))) :
    ∀ (ctx : StationaryMFG.Theorems.SimplePower.Banach.AepsiUniformContextK
              (d := d) (paperEpsSeq k) V H DpH
              (hpow.α * (hpow.β + 1) / hpow.β)
              (hpow.β + 1)
              ((hpow.β + 1) / hpow.β)
              ((hpow.α * (hpow.β + 1) / hpow.β)
                / (hpow.α * (hpow.β + 1) / hpow.β - 1))),
    ∀ (q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
              (hpow.β + 1)
              (hpow.α * (hpow.β + 1) / hpow.β)),
      q ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi d
              (hpow.β + 1)
              (hpow.α * (hpow.β + 1) / hpow.β) →
      (∀ q' ∈ StationaryMFG.Theorems.SimplePower.Banach.K_Aepsi d
                (hpow.β + 1)
                (hpow.α * (hpow.β + 1) / hpow.β),
          0 ≤ StationaryMFG.Theorems.SimplePower.Banach.Aepsi_CLM_opK
                (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
                (βBarReal := hpow.β + 1)
                (βBarReal' := (hpow.β + 1) / hpow.β)
                (γBarReal' := (hpow.α * (hpow.β + 1) / hpow.β)
                                / (hpow.α * (hpow.β + 1) / hpow.β - 1))
                V H DpH ctx.auxHypsK (paperEpsSeq k) q' (q' - q)) →
      ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)) S < ⊤ →
      ∀ (μ υ : (Fin d → ℝ) → ℝ)
        (Dυ : Fin d → (Fin d → ℝ) → ℝ),
        (∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
            0 ≤ μ x) →
        Periodic.MemLpPer (d := d)
          (ENNReal.ofReal (hpow.β + 1)) μ →
        Periodic.MemSobolevPer (d := d)
          (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) υ →
        (∀ i, Periodic.MemLpPer (d := d)
                (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) (Dυ i)) →
        (∀ i, Periodic.HasWeakDerivPer (d := d) i υ (Dυ i)) →
          0 ≤ mfgOperatorEpsPair
                (V := V) (H := H) (DpH := DpH)
                (hpow.α * (hpow.β + 1) / hpow.β) (paperEpsSeq k)
                Dυ
                (fun x => μ x + σ * μ x *
                              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                υ
                (fun i x => Dυ i x -
                  StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
                (fun x => (μ x + σ * μ x *
                              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                          - StationaryMFG.Theorems.SimplePower.Banach.mOf q x)
                (fun x => υ x -
                  StationaryMFG.Theorems.SimplePower.Banach.uOf q x) := by
  -- Closure over the universal `(ctx, q, hq_K0, hVI)`, the signed test
  -- data `(σ, hσ, S, hS, hSfin)`, the user primal density `μ` with its
  -- non-negativity and Lp certificates, and the user probe `(υ, Dυ)` with
  -- its Banach-embedding certificates.
  -- **Phase 5 step3d**: `_hWeak_υ` slot consumed but unused.
  intro ctx q hq_K0 hVI σ hσ S hS hSfin μ υ Dυ hμ_nn hμ_memLp hυ_memSob hDυ_memLp _hWeak_υ
  -- Dispatch to the Child D″ user-triple Minty discharge, consuming the
  -- per-query operator-continuity certificate from
  -- `hSignedUserTripleCont`.
  exact StationaryMFG.Theorems.SimplePower.Banach.hVIeps_signed_user_triple_of_KAepsi_VI
    ctx.auxHypsK q hq_K0 hVI σ hσ S hS hSfin μ υ Dυ
    hμ_nn hμ_memLp hυ_memSob hDυ_memLp
    (hSignedUserTripleCont q hq_K0 σ hσ S hS hSfin μ υ Dυ
      hμ_nn hμ_memLp hυ_memSob hDυ_memLp)

/-! ### Hext-free `_of_rc0` user-probe/triple Minty producers (T3 step 8b)

ε-generic, `Hext_finite_at_zero`-free siblings of the
`paperSection8_hMinty_signed_user_{probe,triple}_of_paperHypotheses`
producers. Instead of taking an external
`hSignedUser{Probe,Triple}Cont` supplier, they build the per-query
operator-continuity certificate IN-BODY via the new Hext-free
`_of_rc0` AE-strong-measurable continuity wrappers, taking `hH_rc0`
(accepted T3 rider) and `hV_memLp` in place of `(hHat0, hFin,
hAgree)`. The discharge dispatches to the same VI consumers
`hVIeps_signed_user_{probe,triple}_of_KAepsi_VI`. -/

/-- **ε-level signed-family user-probe Minty producer (Hext-free
`_of_rc0`).** Composes the Hext-free continuity wrapper
`signedUserProbeCont_of_paperHypotheses_of_aestronglyMeasurable_of_rc0`
with the VI consumer `hVIeps_signed_user_probe_of_KAepsi_VI`. -/
noncomputable def paperSection8_hMinty_signed_user_probe_of_paperHypotheses_of_rc0
    {d : ℕ}
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (hRegH : Hamiltonian.RegularityH (d := d) H DpH)
    (hH_rc0 :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ∀ p : Fin d → ℝ,
          Filter.Tendsto (fun m : ℝ => H x p m) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
            (nhds (H x p 0)))
    (hV_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) V)
    (k : ℕ)
    [Fact (1 ≤ ENNReal.ofReal (hpow.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))] :
    ∀ (ctx : StationaryMFG.Theorems.SimplePower.Banach.AepsiUniformContextK
              (d := d) (paperEpsSeq k) V H DpH
              (hpow.α * (hpow.β + 1) / hpow.β)
              (hpow.β + 1)
              ((hpow.β + 1) / hpow.β)
              ((hpow.α * (hpow.β + 1) / hpow.β)
                / (hpow.α * (hpow.β + 1) / hpow.β - 1))),
    ∀ (q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
              (hpow.β + 1)
              (hpow.α * (hpow.β + 1) / hpow.β)),
      q ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi d
              (hpow.β + 1)
              (hpow.α * (hpow.β + 1) / hpow.β) →
      (∀ q' ∈ StationaryMFG.Theorems.SimplePower.Banach.K_Aepsi d
                (hpow.β + 1)
                (hpow.α * (hpow.β + 1) / hpow.β),
          0 ≤ StationaryMFG.Theorems.SimplePower.Banach.Aepsi_CLM_opK
                (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
                (βBarReal := hpow.β + 1)
                (βBarReal' := (hpow.β + 1) / hpow.β)
                (γBarReal' := (hpow.α * (hpow.β + 1) / hpow.β)
                                / (hpow.α * (hpow.β + 1) / hpow.β - 1))
                V H DpH ctx.auxHypsK (paperEpsSeq k) q' (q' - q)) →
      ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)) S < ⊤ →
      ∀ (υ : (Fin d → ℝ) → ℝ)
        (Dυ : Fin d → (Fin d → ℝ) → ℝ),
        Periodic.MemSobolevPer (d := d)
          (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) υ →
        (∀ i, Periodic.MemLpPer (d := d)
                (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) (Dυ i)) →
        (∀ i, Periodic.HasWeakDerivPer (d := d) i υ (Dυ i)) →
          0 ≤ mfgOperatorEpsPair
                (V := V) (H := H) (DpH := DpH)
                (hpow.α * (hpow.β + 1) / hpow.β) (paperEpsSeq k)
                Dυ
                (fun x => StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
                            σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                υ
                (fun i x => Dυ i x -
                  StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
                (fun x => σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                (fun x => υ x -
                  StationaryMFG.Theorems.SimplePower.Banach.uOf q x) := by
  intro ctx q hq_K0 hVI σ hσ S hS hSfin υ Dυ hυ_memSob hDυ_memLp _hWeak_υ
  exact StationaryMFG.Theorems.SimplePower.Banach.hVIeps_signed_user_probe_of_KAepsi_VI
    ctx.auxHypsK q hq_K0 hVI σ hσ S hS hSfin υ Dυ hυ_memSob hDυ_memLp
    (signedUserProbeCont_of_paperHypotheses_of_aestronglyMeasurable_of_rc0
      (V := V) (H := H) (DpH := DpH)
      hpow hRegH hH_rc0 (ε := paperEpsSeq k)
      q hq_K0 σ hσ S hS υ Dυ hυ_memSob.1 hDυ_memLp hV_memLp)

/-- **ε-level signed-family user-triple Minty producer (Hext-free
`_of_rc0`).** Composes the Hext-free continuity wrapper
`signedUserTripleCont_of_paperHypotheses_of_aestronglyMeasurable_of_rc0`
with the VI consumer `hVIeps_signed_user_triple_of_KAepsi_VI`. -/
noncomputable def paperSection8_hMinty_signed_user_triple_of_paperHypotheses_of_rc0
    {d : ℕ}
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (hRegH : Hamiltonian.RegularityH (d := d) H DpH)
    (hH_rc0 :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ∀ p : Fin d → ℝ,
          Filter.Tendsto (fun m : ℝ => H x p m) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
            (nhds (H x p 0)))
    (hV_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) V)
    (k : ℕ)
    [Fact (1 ≤ ENNReal.ofReal (hpow.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))] :
    ∀ (ctx : StationaryMFG.Theorems.SimplePower.Banach.AepsiUniformContextK
              (d := d) (paperEpsSeq k) V H DpH
              (hpow.α * (hpow.β + 1) / hpow.β)
              (hpow.β + 1)
              ((hpow.β + 1) / hpow.β)
              ((hpow.α * (hpow.β + 1) / hpow.β)
                / (hpow.α * (hpow.β + 1) / hpow.β - 1))),
    ∀ (q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
              (hpow.β + 1)
              (hpow.α * (hpow.β + 1) / hpow.β)),
      q ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi d
              (hpow.β + 1)
              (hpow.α * (hpow.β + 1) / hpow.β) →
      (∀ q' ∈ StationaryMFG.Theorems.SimplePower.Banach.K_Aepsi d
                (hpow.β + 1)
                (hpow.α * (hpow.β + 1) / hpow.β),
          0 ≤ StationaryMFG.Theorems.SimplePower.Banach.Aepsi_CLM_opK
                (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
                (βBarReal := hpow.β + 1)
                (βBarReal' := (hpow.β + 1) / hpow.β)
                (γBarReal' := (hpow.α * (hpow.β + 1) / hpow.β)
                                / (hpow.α * (hpow.β + 1) / hpow.β - 1))
                V H DpH ctx.auxHypsK (paperEpsSeq k) q' (q' - q)) →
      ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)) S < ⊤ →
      ∀ (μ υ : (Fin d → ℝ) → ℝ)
        (Dυ : Fin d → (Fin d → ℝ) → ℝ),
        (∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
            0 ≤ μ x) →
        Periodic.MemLpPer (d := d)
          (ENNReal.ofReal (hpow.β + 1)) μ →
        Periodic.MemSobolevPer (d := d)
          (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) υ →
        (∀ i, Periodic.MemLpPer (d := d)
                (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) (Dυ i)) →
        (∀ i, Periodic.HasWeakDerivPer (d := d) i υ (Dυ i)) →
          0 ≤ mfgOperatorEpsPair
                (V := V) (H := H) (DpH := DpH)
                (hpow.α * (hpow.β + 1) / hpow.β) (paperEpsSeq k)
                Dυ
                (fun x => μ x + σ * μ x *
                              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                υ
                (fun i x => Dυ i x -
                  StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
                (fun x => (μ x + σ * μ x *
                              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                          - StationaryMFG.Theorems.SimplePower.Banach.mOf q x)
                (fun x => υ x -
                  StationaryMFG.Theorems.SimplePower.Banach.uOf q x) := by
  intro ctx q hq_K0 hVI σ hσ S hS hSfin μ υ Dυ hμ_nn hμ_memLp hυ_memSob hDυ_memLp _hWeak_υ
  exact StationaryMFG.Theorems.SimplePower.Banach.hVIeps_signed_user_triple_of_KAepsi_VI
    ctx.auxHypsK q hq_K0 hVI σ hσ S hS hSfin μ υ Dυ
    hμ_nn hμ_memLp hυ_memSob hDυ_memLp
    (signedUserTripleCont_of_paperHypotheses_of_aestronglyMeasurable_of_rc0
      (V := V) (H := H) (DpH := DpH)
      hpow hRegH hH_rc0 (ε := paperEpsSeq k)
      q hq_K0 σ hσ S hS μ υ Dυ hμ_nn hμ_memLp hυ_memSob.1 hDυ_memLp hV_memLp)

/-! ### `_of_aeMeasH` user-probe/triple Minty producers (D2b-1c-ii-c4c)

`measurable_H`-free, `aeMeasH`-input siblings of the strict
`paperSection8_hMinty_signed_user_{probe,triple}_of_paperHypotheses_of_rc0`
producers above. They drop the `RegularityH`/`HypothesisPowerGrowth`
binders and instead consume the genuine individual H/DpH fields (bare
exponents `α β`, `hDpH_meas`, `hcont_H_pm`, `hcont_DpH_pm`,
`hDpH_upper`), routing the per-query operator tendsto through the
aesm-input transport `_of_aeMeasH` keystone
`mfgOperatorEpsPair_tendsto_transport_perturbation_of_paperHypotheses_of_aestronglyMeasurable_of_rc0_of_aeMeasH`
instantiated at the probe/triple transport density
`σ := μ + σ_scalar · μ · 𝟙_S` (probe: `μ := mOf q`; triple: `μ`
user-supplied). The probe/triple test/perturbation shapes coincide
syntactically with the transport keystone's output at this `σ`, so no
fresh keystone or residue bundle is required: the transport bare
residue bundle `TransportTendstoResidueOfBare` at the probe/triple
`σ` supplies the AE composites and six dominators.

This is the five-family aesm-input coverage capstone. Instantiable at
`H := HdeltaK0`: the H AE composites are supplied by
`aemeasurable_HdeltaK0_comp_of_rc0`. The strict `_of_rc0` producers
above are left byte-for-byte intact for T1/T2. -/

/-- **ε-level signed-family user-probe Minty producer (`_of_aeMeasH`).**
Routes the inner operator tendsto through the transport `_of_aeMeasH`
keystone at `σ := mOf q + σ_scalar · mOf q · 𝟙_S`, then dispatches to
the VI consumer `hVIeps_signed_user_probe_of_KAepsi_VI`. -/
noncomputable def paperSection8_hMinty_signed_user_probe_of_paperHypotheses_of_rc0_of_aeMeasH
    {d : ℕ}
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    {C α β : ℝ} (hα : 1 < α) (hβ : 0 < β)
    (hDpH_meas : Measurable
      (fun (xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ) => DpH xpm.1 xpm.2.1 xpm.2.2))
    (hcont_H_pm :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ContinuousOn (fun (pm : (Fin d → ℝ) × ℝ) => H x pm.1 pm.2)
          {pm | 0 < pm.2})
    (hcont_DpH_pm :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ContinuousOn (fun (pm : (Fin d → ℝ) × ℝ) => DpH x pm.1 pm.2)
          {pm | 0 < pm.2})
    (hDpH_upper :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ∀ p m, 0 < m →
          ‖DpH x p m‖ ≤ C * (‖p‖ ^ (α - 1) + m ^ (β - β / α) + 1))
    (hH_rc0 :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ∀ p : Fin d → ℝ,
          Filter.Tendsto (fun m : ℝ => H x p m) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
            (nhds (H x p 0)))
    {ε : ℝ}
    [Fact (1 ≤ ENNReal.ofReal (β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (α * (β + 1) / β))]
    -- Per-query bare-exponent residue supplier (transport bundle at the
    -- probe density `σ := mOf q + σ_scalar · mOf q · 𝟙_S`).
    (residueOf_probe :
      ∀ (q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
                (β + 1)
                (α * (β + 1) / β)),
        q ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi d
              (β + 1)
              (α * (β + 1) / β) →
        ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
        ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
          (MeasureTheory.volume.restrict (Periodic.UnitCube d)) S < ⊤ →
        ∀ (υ : (Fin d → ℝ) → ℝ)
          (Dυ : Fin d → (Fin d → ℝ) → ℝ),
          Periodic.MemSobolevPer (d := d)
            (ENNReal.ofReal (α * (β + 1) / β)) υ →
          (∀ i, Periodic.MemLpPer (d := d)
                  (ENNReal.ofReal (α * (β + 1) / β)) (Dυ i)) →
            StationaryMFG.Theorems.SimplePower.Banach.TransportTendstoResidueOfBare
              (d := d) (V := V) (H := H) (DpH := DpH)
              (βBarReal := β + 1)
              (γBarReal := α * (β + 1) / β)
              β q
              (fun x => StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
                          σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              υ Dυ) :
    ∀ (ctx : StationaryMFG.Theorems.SimplePower.Banach.AepsiUniformContextK
              (d := d) ε V H DpH
              (α * (β + 1) / β)
              (β + 1)
              ((β + 1) / β)
              ((α * (β + 1) / β)
                / (α * (β + 1) / β - 1))),
    ∀ (q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
              (β + 1)
              (α * (β + 1) / β)),
      q ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi d
              (β + 1)
              (α * (β + 1) / β) →
      (∀ q' ∈ StationaryMFG.Theorems.SimplePower.Banach.K_Aepsi d
                (β + 1)
                (α * (β + 1) / β),
          0 ≤ StationaryMFG.Theorems.SimplePower.Banach.Aepsi_CLM_opK
                (γBarReal := α * (β + 1) / β)
                (βBarReal := β + 1)
                (βBarReal' := (β + 1) / β)
                (γBarReal' := (α * (β + 1) / β)
                                / (α * (β + 1) / β - 1))
                V H DpH ctx.auxHypsK ε q' (q' - q)) →
      ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)) S < ⊤ →
      ∀ (υ : (Fin d → ℝ) → ℝ)
        (Dυ : Fin d → (Fin d → ℝ) → ℝ),
        Periodic.MemSobolevPer (d := d)
          (ENNReal.ofReal (α * (β + 1) / β)) υ →
        (∀ i, Periodic.MemLpPer (d := d)
                (ENNReal.ofReal (α * (β + 1) / β)) (Dυ i)) →
        (∀ i, Periodic.HasWeakDerivPer (d := d) i υ (Dυ i)) →
          0 ≤ mfgOperatorEpsPair
                (V := V) (H := H) (DpH := DpH)
                (α * (β + 1) / β) ε
                Dυ
                (fun x => StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
                            σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                υ
                (fun i x => Dυ i x -
                  StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
                (fun x => σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                (fun x => υ x -
                  StationaryMFG.Theorems.SimplePower.Banach.uOf q x) := by
  set βBarReal : ℝ := β + 1 with hβBarReal_def
  set γBarReal : ℝ := α * (β + 1) / β with hγBarReal_def
  set βBarReal' : ℝ := (β + 1) / β with hβBarReal'_def
  -- Bare-exponent `SimplePowerExponentFacts` from `standardPaper`.
  have hExp_paper :
      SimplePowerExponentFacts
          (SimplePowerExponentFacts.paperGammaBarReal α β)
          (SimplePowerExponentFacts.paperBetaBar β)
          (SimplePowerExponentFacts.paperGammaBar α β)
          (SimplePowerExponentFacts.paperBetaBarPrime β) :=
    SimplePowerExponentFacts.standardPaper hα hβ
  have hExp :
      SimplePowerExponentFacts γBarReal
          (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
          (ENNReal.ofReal βBarReal') := by
    have h1 :
        (SimplePowerExponentFacts.paperBetaBar β)
          = ENNReal.ofReal βBarReal := by
      simp [SimplePowerExponentFacts.paperBetaBar, hβBarReal_def]
    have h2 :
        (SimplePowerExponentFacts.paperGammaBar α β)
          = ENNReal.ofReal γBarReal := by
      simp [SimplePowerExponentFacts.paperGammaBar, hγBarReal_def]
    have h3 :
        (SimplePowerExponentFacts.paperBetaBarPrime β)
          = ENNReal.ofReal βBarReal' := by
      simp [SimplePowerExponentFacts.paperBetaBarPrime, hβBarReal'_def]
    have h4 :
        (SimplePowerExponentFacts.paperGammaBarReal α β)
          = γBarReal := by
      simp [SimplePowerExponentFacts.paperGammaBarReal, hγBarReal_def]
    have := hExp_paper
    rw [h1, h2, h3, h4] at this
    exact this
  intro ctx q hq_K0 hVI σ hσ S hS hSfin υ Dυ hυ_memSob hDυ_memLp _hWeak_υ
  -- Probe transport density `σ_fn := mOf q + σ · mOf q · 𝟙_S`.
  set σ_fn : (Fin d → ℝ) → ℝ :=
    fun x => StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
              σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
    with hσ_fn_def
  -- `mOf q` Lp / a.e.-nonnegativity facts.
  have hm_memLp : Periodic.MemLpPer (d := d)
      (ENNReal.ofReal (β + 1))
      (StationaryMFG.Theorems.SimplePower.Banach.mOf q) :=
    StationaryMFG.Theorems.SimplePower.Banach.memLpPer_of_lpPer (d := d) q.1
  have hm_nn : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
                  0 ≤ StationaryMFG.Theorems.SimplePower.Banach.mOf q x := hq_K0
  -- `σ_fn ≥ 0` a.e. (`mOf q ≥ 0` and `σ ∈ {±1}`).
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
    change 0 ≤ StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
              σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
    have h_eq :
        StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
            σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
          = StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
              (1 + σ * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by ring
    rw [h_eq]; exact mul_nonneg hxnn hfactor_nn
  -- `σ_fn ∈ L^{β+1}_per`.
  have hsmul : Periodic.MemLpPer (d := d) (ENNReal.ofReal (β + 1))
      (fun x => σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x) := by
    have := hm_memLp.const_smul (𝕜 := ℝ) σ
    have heq : (σ • (StationaryMFG.Theorems.SimplePower.Banach.mOf q :
                  (Fin d → ℝ) → ℝ))
                = fun x => σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x :=
      rfl
    rw [heq] at this; exact this
  have hSind : Periodic.MemLpPer (d := d) (ENNReal.ofReal (β + 1))
      (S.indicator (fun x => σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x)) :=
    MemLp.toMemLpPer (MeasureTheory.MemLp.indicator hS.nullMeasurableSet hsmul.toMemLp)
  have hInd_funEq :
      (S.indicator (fun x => σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x) :
          (Fin d → ℝ) → ℝ)
        = fun x => σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
    funext x
    by_cases hx : x ∈ S
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have hInd_memLp : Periodic.MemLpPer (d := d)
      (ENNReal.ofReal (β + 1))
      (fun x => σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
    rw [← hInd_funEq]; exact hSind
  have hσ_fn_memLp : Periodic.MemLpPer (d := d)
      (ENNReal.ofReal (β + 1)) σ_fn := by
    have := Periodic.MemLpPer.add hm_memLp hInd_memLp
    simpa only [hσ_fn_def, Pi.add_def] using this
  -- Extract the per-query transport residue bundle at `σ_fn`.
  set r :=
    residueOf_probe q hq_K0 σ hσ S hS hSfin υ Dυ hυ_memSob hDυ_memLp
    with hr_def
  -- Operator-continuity certificate via the transport `_of_aeMeasH` keystone.
  have hCont :=
    StationaryMFG.Theorems.SimplePower.Banach.mfgOperatorEpsPair_tendsto_transport_perturbation_of_paperHypotheses_of_aestronglyMeasurable_of_rc0_of_aeMeasH
      (ε := ε)
      (γBarReal := α * (β + 1) / β)
      (βBarReal := β + 1)
      (βBarReal' := (β + 1) / β)
      (γBarReal' := (α * (β + 1) / β)
                      / (α * (β + 1) / β - 1))
      (C := C) (α := α) (β := β)
      hα hβ hDpH_meas hcont_H_pm hcont_DpH_pm hDpH_upper hExp hH_rc0
      Dυ υ (StationaryMFG.Theorems.SimplePower.Banach.uOf q)
      (StationaryMFG.Theorems.SimplePower.Banach.DuOf q)
      (StationaryMFG.Theorems.SimplePower.Banach.mOf q) V σ_fn
      r.hσ r.hm r.hV r.hυ r.hu r.hφ r.hDu hσ_fn_nn hσ_fn_memLp
      r.hHcomp_ae_n r.hHcomp_ae_lim
      r.Gh r.Eh r.hGh_memLp r.hEh_memLp r.hGh_bd r.hEh_bd
      r.Gf r.Ef r.hGf_memLp r.hEf_memLp r.hGf_bd r.hEf_bd
      r.Gm r.Em r.hGm_memLp r.hEm_memLp r.hGm_bd r.hEm_bd
  -- The transport keystone delivers the regularized sequence at
  -- `σ_fn = mOf q + σ·mOf q·𝟙_S` and the limit at mass-difference
  -- `σ_fn - mOf q`. For the probe VI the limit mass-difference is the
  -- cancelled form `σ·mOf q·𝟙_S`. They agree everywhere, so rewrite the
  -- limit operator's η-argument via `mfgOperatorEpsPair_congr_ae`.
  have hη_lim_eq :
      (σ_fn - StationaryMFG.Theorems.SimplePower.Banach.mOf q)
        =ᵐ[MeasureTheory.volume.restrict (Periodic.UnitCube d)]
      (fun x => σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    change σ_fn x - StationaryMFG.Theorems.SimplePower.Banach.mOf q x
        = σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
    simp only [hσ_fn_def]; ring
  have hLim_eq :
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          (α * (β + 1) / β) ε
          Dυ σ_fn υ
          (fun i x => Dυ i x -
            StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
          (σ_fn - StationaryMFG.Theorems.SimplePower.Banach.mOf q)
          (υ - StationaryMFG.Theorems.SimplePower.Banach.uOf q)
      =
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          (α * (β + 1) / β) ε
          Dυ σ_fn υ
          (fun i x => Dυ i x -
            StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
          (fun x => σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          (υ - StationaryMFG.Theorems.SimplePower.Banach.uOf q) :=
    StationaryMFG.Solutions.MFG.mfgOperatorEpsPair_congr_ae
      (V := V) (H := H) (DpH := DpH) (α * (β + 1) / β) ε
      Dυ σ_fn υ
      (fun i x => Dυ i x -
        StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
      (fun i x => Dυ i x -
        StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
      (σ_fn - StationaryMFG.Theorems.SimplePower.Banach.mOf q)
      (fun x => σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
      (υ - StationaryMFG.Theorems.SimplePower.Banach.uOf q)
      (υ - StationaryMFG.Theorems.SimplePower.Banach.uOf q)
      (fun _ => Filter.EventuallyEq.rfl) hη_lim_eq Filter.EventuallyEq.rfl
  rw [hLim_eq] at hCont
  -- Dispatch to the user-probe VI consumer. The (rewritten) keystone output
  -- now matches the probe `hCont` shape (`σ_fn` unfolds definitionally).
  exact StationaryMFG.Theorems.SimplePower.Banach.hVIeps_signed_user_probe_of_KAepsi_VI
    ctx.auxHypsK q hq_K0 hVI σ hσ S hS hSfin υ Dυ hυ_memSob hDυ_memLp hCont

/-- **ε-level signed-family user-triple Minty producer (`_of_aeMeasH`).**
Routes the inner operator tendsto through the transport `_of_aeMeasH`
keystone at `σ := μ + σ_scalar · μ · 𝟙_S` (user primal density `μ`),
then dispatches to the VI consumer
`hVIeps_signed_user_triple_of_KAepsi_VI`. -/
noncomputable def paperSection8_hMinty_signed_user_triple_of_paperHypotheses_of_rc0_of_aeMeasH
    {d : ℕ}
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    {C α β : ℝ} (hα : 1 < α) (hβ : 0 < β)
    (hDpH_meas : Measurable
      (fun (xpm : (Fin d → ℝ) × (Fin d → ℝ) × ℝ) => DpH xpm.1 xpm.2.1 xpm.2.2))
    (hcont_H_pm :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ContinuousOn (fun (pm : (Fin d → ℝ) × ℝ) => H x pm.1 pm.2)
          {pm | 0 < pm.2})
    (hcont_DpH_pm :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ContinuousOn (fun (pm : (Fin d → ℝ) × ℝ) => DpH x pm.1 pm.2)
          {pm | 0 < pm.2})
    (hDpH_upper :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ∀ p m, 0 < m →
          ‖DpH x p m‖ ≤ C * (‖p‖ ^ (α - 1) + m ^ (β - β / α) + 1))
    (hH_rc0 :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ∀ p : Fin d → ℝ,
          Filter.Tendsto (fun m : ℝ => H x p m) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
            (nhds (H x p 0)))
    {ε : ℝ}
    [Fact (1 ≤ ENNReal.ofReal (β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (α * (β + 1) / β))]
    -- Per-query bare-exponent residue supplier (transport bundle at the
    -- triple density `σ := μ + σ_scalar · μ · 𝟙_S`).
    (residueOf_triple :
      ∀ (q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
                (β + 1)
                (α * (β + 1) / β)),
        q ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi d
              (β + 1)
              (α * (β + 1) / β) →
        ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
        ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
          (MeasureTheory.volume.restrict (Periodic.UnitCube d)) S < ⊤ →
        ∀ (μ υ : (Fin d → ℝ) → ℝ)
          (Dυ : Fin d → (Fin d → ℝ) → ℝ),
          (∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
              0 ≤ μ x) →
          Periodic.MemLpPer (d := d)
            (ENNReal.ofReal (β + 1)) μ →
          Periodic.MemSobolevPer (d := d)
            (ENNReal.ofReal (α * (β + 1) / β)) υ →
          (∀ i, Periodic.MemLpPer (d := d)
                  (ENNReal.ofReal (α * (β + 1) / β)) (Dυ i)) →
            StationaryMFG.Theorems.SimplePower.Banach.TransportTendstoResidueOfBare
              (d := d) (V := V) (H := H) (DpH := DpH)
              (βBarReal := β + 1)
              (γBarReal := α * (β + 1) / β)
              β q
              (fun x => μ x +
                          σ * μ x *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              υ Dυ) :
    ∀ (ctx : StationaryMFG.Theorems.SimplePower.Banach.AepsiUniformContextK
              (d := d) ε V H DpH
              (α * (β + 1) / β)
              (β + 1)
              ((β + 1) / β)
              ((α * (β + 1) / β)
                / (α * (β + 1) / β - 1))),
    ∀ (q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
              (β + 1)
              (α * (β + 1) / β)),
      q ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi d
              (β + 1)
              (α * (β + 1) / β) →
      (∀ q' ∈ StationaryMFG.Theorems.SimplePower.Banach.K_Aepsi d
                (β + 1)
                (α * (β + 1) / β),
          0 ≤ StationaryMFG.Theorems.SimplePower.Banach.Aepsi_CLM_opK
                (γBarReal := α * (β + 1) / β)
                (βBarReal := β + 1)
                (βBarReal' := (β + 1) / β)
                (γBarReal' := (α * (β + 1) / β)
                                / (α * (β + 1) / β - 1))
                V H DpH ctx.auxHypsK ε q' (q' - q)) →
      ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)) S < ⊤ →
      ∀ (μ υ : (Fin d → ℝ) → ℝ)
        (Dυ : Fin d → (Fin d → ℝ) → ℝ),
        (∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
            0 ≤ μ x) →
        Periodic.MemLpPer (d := d)
          (ENNReal.ofReal (β + 1)) μ →
        Periodic.MemSobolevPer (d := d)
          (ENNReal.ofReal (α * (β + 1) / β)) υ →
        (∀ i, Periodic.MemLpPer (d := d)
                (ENNReal.ofReal (α * (β + 1) / β)) (Dυ i)) →
        (∀ i, Periodic.HasWeakDerivPer (d := d) i υ (Dυ i)) →
          0 ≤ mfgOperatorEpsPair
                (V := V) (H := H) (DpH := DpH)
                (α * (β + 1) / β) ε
                Dυ
                (fun x => μ x + σ * μ x *
                              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                υ
                (fun i x => Dυ i x -
                  StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
                (fun x => (μ x + σ * μ x *
                              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                          - StationaryMFG.Theorems.SimplePower.Banach.mOf q x)
                (fun x => υ x -
                  StationaryMFG.Theorems.SimplePower.Banach.uOf q x) := by
  set βBarReal : ℝ := β + 1 with hβBarReal_def
  set γBarReal : ℝ := α * (β + 1) / β with hγBarReal_def
  set βBarReal' : ℝ := (β + 1) / β with hβBarReal'_def
  -- Bare-exponent `SimplePowerExponentFacts` from `standardPaper`.
  have hExp_paper :
      SimplePowerExponentFacts
          (SimplePowerExponentFacts.paperGammaBarReal α β)
          (SimplePowerExponentFacts.paperBetaBar β)
          (SimplePowerExponentFacts.paperGammaBar α β)
          (SimplePowerExponentFacts.paperBetaBarPrime β) :=
    SimplePowerExponentFacts.standardPaper hα hβ
  have hExp :
      SimplePowerExponentFacts γBarReal
          (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
          (ENNReal.ofReal βBarReal') := by
    have h1 :
        (SimplePowerExponentFacts.paperBetaBar β)
          = ENNReal.ofReal βBarReal := by
      simp [SimplePowerExponentFacts.paperBetaBar, hβBarReal_def]
    have h2 :
        (SimplePowerExponentFacts.paperGammaBar α β)
          = ENNReal.ofReal γBarReal := by
      simp [SimplePowerExponentFacts.paperGammaBar, hγBarReal_def]
    have h3 :
        (SimplePowerExponentFacts.paperBetaBarPrime β)
          = ENNReal.ofReal βBarReal' := by
      simp [SimplePowerExponentFacts.paperBetaBarPrime, hβBarReal'_def]
    have h4 :
        (SimplePowerExponentFacts.paperGammaBarReal α β)
          = γBarReal := by
      simp [SimplePowerExponentFacts.paperGammaBarReal, hγBarReal_def]
    have := hExp_paper
    rw [h1, h2, h3, h4] at this
    exact this
  intro ctx q hq_K0 hVI σ hσ S hS hSfin μ υ Dυ hμ_nn hμ_memLp hυ_memSob hDυ_memLp _hWeak_υ
  -- Triple transport density `σ_fn := μ + σ · μ · 𝟙_S`.
  set σ_fn : (Fin d → ℝ) → ℝ :=
    fun x => μ x +
              σ * μ x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
    with hσ_fn_def
  have hσ_lb : (-1 : ℝ) ≤ σ := by rcases hσ with h | h <;> simp [h]
  have hσ_ub : σ ≤ 1 := by rcases hσ with h | h <;> simp [h]
  -- `σ_fn ≥ 0` a.e. (`μ ≥ 0` and `σ ∈ {±1}`).
  have hσ_fn_nn :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        0 ≤ σ_fn x := by
    filter_upwards [hμ_nn] with x hxnn
    have hfactor_nn :
        0 ≤ 1 + σ * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
      by_cases hxS : x ∈ S
      · rw [Set.indicator_of_mem hxS]; simp only [mul_one]; linarith
      · rw [Set.indicator_of_notMem hxS]; simp
    change 0 ≤ μ x + σ * μ x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
    have h_eq :
        μ x + σ * μ x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
          = μ x * (1 + σ * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
      ring
    rw [h_eq]; exact mul_nonneg hxnn hfactor_nn
  -- `σ_fn ∈ L^{β+1}_per`.
  have hsmul : Periodic.MemLpPer (d := d) (ENNReal.ofReal (β + 1))
      (fun x => σ * μ x) := by
    have := hμ_memLp.const_smul (𝕜 := ℝ) σ
    have heq : (σ • (μ : (Fin d → ℝ) → ℝ))
                = fun x => σ * μ x := rfl
    rw [heq] at this; exact this
  have hSind : Periodic.MemLpPer (d := d) (ENNReal.ofReal (β + 1))
      (S.indicator (fun x => σ * μ x)) :=
    MemLp.toMemLpPer (MeasureTheory.MemLp.indicator hS.nullMeasurableSet hsmul.toMemLp)
  have hInd_funEq :
      (S.indicator (fun x => σ * μ x) : (Fin d → ℝ) → ℝ)
        = fun x => σ * μ x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
    funext x
    by_cases hx : x ∈ S
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have hInd_memLp : Periodic.MemLpPer (d := d)
      (ENNReal.ofReal (β + 1))
      (fun x => σ * μ x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
    rw [← hInd_funEq]; exact hSind
  have hσ_fn_memLp : Periodic.MemLpPer (d := d)
      (ENNReal.ofReal (β + 1)) σ_fn := by
    have := Periodic.MemLpPer.add hμ_memLp hInd_memLp
    simpa only [hσ_fn_def, Pi.add_def] using this
  -- Extract the per-query transport residue bundle at `σ_fn`.
  set r :=
    residueOf_triple q hq_K0 σ hσ S hS hSfin μ υ Dυ hμ_nn hμ_memLp hυ_memSob
      hDυ_memLp with hr_def
  -- Operator-continuity certificate via the transport `_of_aeMeasH` keystone.
  have hCont :=
    StationaryMFG.Theorems.SimplePower.Banach.mfgOperatorEpsPair_tendsto_transport_perturbation_of_paperHypotheses_of_aestronglyMeasurable_of_rc0_of_aeMeasH
      (ε := ε)
      (γBarReal := α * (β + 1) / β)
      (βBarReal := β + 1)
      (βBarReal' := (β + 1) / β)
      (γBarReal' := (α * (β + 1) / β)
                      / (α * (β + 1) / β - 1))
      (C := C) (α := α) (β := β)
      hα hβ hDpH_meas hcont_H_pm hcont_DpH_pm hDpH_upper hExp hH_rc0
      Dυ υ (StationaryMFG.Theorems.SimplePower.Banach.uOf q)
      (StationaryMFG.Theorems.SimplePower.Banach.DuOf q)
      (StationaryMFG.Theorems.SimplePower.Banach.mOf q) V σ_fn
      r.hσ r.hm r.hV r.hυ r.hu r.hφ r.hDu hσ_fn_nn hσ_fn_memLp
      r.hHcomp_ae_n r.hHcomp_ae_lim
      r.Gh r.Eh r.hGh_memLp r.hEh_memLp r.hGh_bd r.hEh_bd
      r.Gf r.Ef r.hGf_memLp r.hEf_memLp r.hGf_bd r.hEf_bd
      r.Gm r.Em r.hGm_memLp r.hEm_memLp r.hGm_bd r.hEm_bd
  -- Dispatch to the user-triple VI consumer.
  exact StationaryMFG.Theorems.SimplePower.Banach.hVIeps_signed_user_triple_of_KAepsi_VI
    ctx.auxHypsK q hq_K0 hVI σ hσ S hS hSfin μ υ Dυ
    hμ_nn hμ_memLp hυ_memSob hDυ_memLp hCont

/-! ### `paperSolFor-final-phase5-hWeakDeriv-step3b` — W-form signed
**user-triple** Minty producer

W-form sibling of `paperSection8_hMinty_signed_user_triple_of_paperHypotheses`
(immediately above), supplying the **refined-cone** signed user-triple
Minty inequality. Completes Phase 1 of the iter-0683 W-form Minty
producer family (last sibling).

Differences from the K-form sibling:

* Witness: takes `q ∈ K0_Aepsi_W d βBar γBar` (refined non-negativity
  cone) instead of `K0_Aepsi`.
* VI: takes `hVI` quantifying over `q' ∈ K_Aepsi_W d βBar γBar`.
* Context: takes `ctx : AepsiUniformContextK_W` instead of
  `AepsiUniformContextK`.
* Extra hypothesis: `hWeak_υ : ∀ i, HasWeakDerivPer i υ (Dυ i)` for
  the user-supplied test pair (per iter-0683 directive, retype the
  W-form statement to take the weak-derivative tie as a paper-faithful
  hypothesis, not as a new auth).
* Backing analytic lemma: dispatches to
  `Banach.hVIeps_signed_user_triple_of_KAepsi_W_VI` instead of
  `hVIeps_signed_user_triple_of_KAepsi_VI`.

The per-query continuity supplier `hSignedUserTripleCont` is unchanged
(operator-continuity certificate at the bare-function layer). The
descent `K0_Aepsi_W → K0_Aepsi` for the supplier is via
`K0_Aepsi_W_subset_K0_Aepsi`.

No new authorisation parameter. -/

/-- **ε-level signed-family user-triple W-form Minty producer.** Builds
the W-form `hMinty_signed_user_triple` field at the paper-canonical
exponents. -/
noncomputable def paperSection8_hMinty_signed_user_triple_W_of_paperHypotheses
    {d : ℕ}
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (_hRegH : Hamiltonian.RegularityH (d := d) H DpH)
    (_hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (_hFin : Hamiltonian.Hext_finite_at_zero (d := d) H)
    (_hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    (k : ℕ)
    [Fact (1 ≤ ENNReal.ofReal (hpow.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))]
    -- Per-query user-triple operator-continuity supplier (analytic input,
    -- CONVENTIONS §8). Identical shape to the K-form sibling's supplier
    -- since the continuity is at the bare-function layer.
    (hSignedUserTripleCont :
      ∀ (q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
                (hpow.β + 1)
                (hpow.α * (hpow.β + 1) / hpow.β)),
        q ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi d
              (hpow.β + 1)
              (hpow.α * (hpow.β + 1) / hpow.β) →
        ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
        ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
          (MeasureTheory.volume.restrict (Periodic.UnitCube d)) S < ⊤ →
        ∀ (μ υ : (Fin d → ℝ) → ℝ)
          (Dυ : Fin d → (Fin d → ℝ) → ℝ),
          (∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
              0 ≤ μ x) →
          Periodic.MemLpPer (d := d)
            (ENNReal.ofReal (hpow.β + 1)) μ →
          Periodic.MemSobolevPer (d := d)
            (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) υ →
          (∀ i, Periodic.MemLpPer (d := d)
                  (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) (Dυ i)) →
            Filter.Tendsto
              (fun n : ℕ =>
                mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                  (hpow.α * (hpow.β + 1) / hpow.β) (paperEpsSeq k)
                  Dυ
                  (fun x =>
                    μ x + σ * μ x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                      + 1 / ((n : ℝ) + 1))
                  υ
                  (fun i x => Dυ i x -
                    StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
                  (fun x =>
                    (μ x + σ * μ x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                      + 1 / ((n : ℝ) + 1)) -
                    StationaryMFG.Theorems.SimplePower.Banach.mOf q x)
                  (fun x => υ x -
                    StationaryMFG.Theorems.SimplePower.Banach.uOf q x))
              Filter.atTop
              (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                    (hpow.α * (hpow.β + 1) / hpow.β) (paperEpsSeq k)
                    Dυ
                    (fun x =>
                      μ x + σ * μ x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                    υ
                    (fun i x => Dυ i x -
                      StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
                    (fun x =>
                      (μ x + σ * μ x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) -
                      StationaryMFG.Theorems.SimplePower.Banach.mOf q x)
                    (fun x => υ x -
                      StationaryMFG.Theorems.SimplePower.Banach.uOf q x)))) :
    ∀ (ctx : StationaryMFG.Theorems.SimplePower.Banach.AepsiUniformContextK_W
              (d := d) (paperEpsSeq k) V H DpH
              (hpow.α * (hpow.β + 1) / hpow.β)
              (hpow.β + 1)
              ((hpow.β + 1) / hpow.β)
              ((hpow.α * (hpow.β + 1) / hpow.β)
                / (hpow.α * (hpow.β + 1) / hpow.β - 1))),
    ∀ (q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
              (hpow.β + 1)
              (hpow.α * (hpow.β + 1) / hpow.β)),
      q ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi_W d
              (hpow.β + 1)
              (hpow.α * (hpow.β + 1) / hpow.β) →
      (∀ q' ∈ StationaryMFG.Theorems.SimplePower.Banach.K_Aepsi_W d
                (hpow.β + 1)
                (hpow.α * (hpow.β + 1) / hpow.β),
          0 ≤ StationaryMFG.Theorems.SimplePower.Banach.Aepsi_CLM_opK
                (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
                (βBarReal := hpow.β + 1)
                (βBarReal' := (hpow.β + 1) / hpow.β)
                (γBarReal' := (hpow.α * (hpow.β + 1) / hpow.β)
                                / (hpow.α * (hpow.β + 1) / hpow.β - 1))
                V H DpH ctx.auxHypsK (paperEpsSeq k) q' (q' - q)) →
      ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)) S < ⊤ →
      ∀ (μ υ : (Fin d → ℝ) → ℝ)
        (Dυ : Fin d → (Fin d → ℝ) → ℝ),
        (∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
            0 ≤ μ x) →
        Periodic.MemLpPer (d := d)
          (ENNReal.ofReal (hpow.β + 1)) μ →
        Periodic.MemSobolevPer (d := d)
          (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) υ →
        (∀ i, Periodic.MemLpPer (d := d)
                (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) (Dυ i)) →
        (∀ i, Periodic.HasWeakDerivPer (d := d) i υ (Dυ i)) →
          0 ≤ mfgOperatorEpsPair
                (V := V) (H := H) (DpH := DpH)
                (hpow.α * (hpow.β + 1) / hpow.β) (paperEpsSeq k)
                Dυ
                (fun x => μ x + σ * μ x *
                              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                υ
                (fun i x => Dυ i x -
                  StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
                (fun x => (μ x + σ * μ x *
                              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                          - StationaryMFG.Theorems.SimplePower.Banach.mOf q x)
                (fun x => υ x -
                  StationaryMFG.Theorems.SimplePower.Banach.uOf q x) := by
  -- Closure over the universal `(ctx, q, hq_K0_W, hVI)`, the signed test
  -- data `(σ, hσ, S, hS, hSfin)`, the user primal density `μ` with its
  -- non-negativity and Lp certificates, the user probe `(υ, Dυ)` with
  -- its Banach-embedding certificates, and the W-form `hWeak_υ`
  -- hypothesis.
  intro ctx q hq_K0_W hVI σ hσ S hS hSfin μ υ Dυ hμ_nn hμ_memLp
        hυ_memSob hDυ_memLp hWeak_υ
  -- Descend `q ∈ K0_Aepsi_W → q ∈ K0_Aepsi` for the supplier.
  have hq_K0 :
      q ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi d
            (hpow.β + 1) (hpow.α * (hpow.β + 1) / hpow.β) :=
    StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi_W_subset_K0_Aepsi
      d (hpow.β + 1) (hpow.α * (hpow.β + 1) / hpow.β) hq_K0_W
  -- Dispatch to the W-form user-triple Minty discharge, consuming the
  -- per-query operator-continuity certificate from
  -- `hSignedUserTripleCont`.
  exact StationaryMFG.Theorems.SimplePower.Banach.hVIeps_signed_user_triple_of_KAepsi_W_VI
    ctx.auxHypsK q hVI σ hσ S hS hSfin μ υ Dυ
    hμ_nn hμ_memLp hυ_memSob hDυ_memLp hWeak_υ
    (hSignedUserTripleCont q hq_K0 σ hσ S hS hSfin μ υ Dυ
      hμ_nn hμ_memLp hυ_memSob hDυ_memLp)

/-! ### Phase D4.3 — per-`k` C-class authorisation bundle

Per `infra-P5-T10-D4-3-cBundleD41-discharge`: the single residual
`:= by exact sorry` inside `T10PaperResidues.of_paperHypotheses` is the
`cBundleD41 k` per-`k` `CBundleD41Stub` witness. To discharge it
without depending on the still-pending Du-chain `_int` migration
(deferred D4.0d), we follow the same B-class authorisation pattern
used by D4.2's `PaperSolForK`: package the per-`k` C-class fields of
`AprioriUniformPerSolHypothesesC` as a single B-class authorised input
`PaperCBundleForK`.

The fields are universally quantified over the `sol` produced by
`Classical.choice` of `exists_regularizedBareSolution_K`'s `Nonempty`
conclusion (mirroring `PaperSolForK`'s nine paper-side inputs), so the
consumer instantiates them with the specific `sol` extracted inside
the proof.

The packaged `CBundleD41Stub` is then assembled with `epsTerms`
fixed at `paperEpsTerms (paperEpsSeq k) γ̄ sol`, so the
canonical-`epsTerms` identification `epsTerms_eq` discharges by `rfl`,
preserving the D4.1 deliverable. -/

/-- **Per-`k` C-class authorisation bundle** for the `cBundleD41`
discharge of `T10PaperResidues.of_paperHypotheses`.

Carries the nine C-class fields of `AprioriUniformPerSolHypothesesC`
at the paper-canonical exponents, universally quantified over the
bare solution `sol` extracted via `Classical.choice` from
`exists_regularizedBareSolution_K`'s `Nonempty` conclusion. The
V-bound triple is fixed at `(0, 0, 0)` to match the existing
`T10PaperResidues.of_paperHypotheses` D2 cheap-scalar discharge
(`Vbound = Vint_bound = Vβp_bound = 0`).

The `epsTerms` field is *not* carried here — it is supplied
definitionally as `paperEpsTerms (paperEpsSeq k) γ̄ sol` at the call
site, so the `epsTerms_eq` certificate of `CBundleD41Stub` discharges
by `rfl`.

This is the D4.3 analogue of `PaperSolForK`: a single B-class
authorised input bundling the per-`k` C-class analytic content
(integrability/non-negativity of the paper regulariser residue,
AE non-negativity of `m`, periodicity of `u` and `Du`,
Sobolev-embedding integrability of `|u|^{β̄'}`, plus the
paper-canonical `vData : AprioriVData` integral V-bound record).
The analytic discharge of each field is filed as a future per-field
child task; this bundle packages the content in the paper-faithful
per-`k` shape, mirroring the iter-0533 `hμ_posAuth_*`,
iter-0539/0540/0541 `*SegInputsAuth`, and Phase D4.2 `paperSolFor`
patterns.

**Phase 1 sub-deliverable D4.1c-d
(`infra-P5-T10-D4-1c-d-drop-hVbnd-PaperCBundleForK`):** the
transitional triple `(hVbnd, hVint, hVβp)` previously carried at
`Vbound = Vint_bound = Vβp_bound = 0` is now removed. The pointwise
`|V| ≤ 0` content is relocated to a separate `paperHVbndAuth`
parameter on `T10PaperResidues.of_paperHypotheses` so this bundle
contains only paper-canonical content (cleanly aligned with the
target `PaperCBundleForKFinal` shape of v7 plan §0.1).

**Phase 1 sub-deliverable D4.1c-e
(`infra-P5-T10-D4-1c-e-replace-hMpos-hmNonneg`):** the legacy
strict-positivity field `hMpos : 0 < sol.m` has been dropped from
this bundle. The paper-faithful shape carries only AE non-negativity
(`hmNonneg`); the strict-positivity content required downstream by
the C-class consumer `AprioriUniformPerSolHypothesesC_int.hMpos` is
now isolated behind a separate B-class authorisation parameter
`paperHMposAuth` on `T10PaperResidues.of_paperHypotheses`
(parallel to `paperHVbndAuth` from D4.1c-d). Both transitional
authorisations are flagged for joint elimination in v7 Phase 4 via
the `μ_n := μ + 1/n` perturbation. -/
structure PaperCBundleForK
    {d : ℕ}
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (k : ℕ) where
  /-- AE non-negativity of the paper regulariser residue
  `paperEpsTerms (paperEpsSeq k) γ̄ sol`. -/
  hEpsNN :
    ∀ (sol : StationaryMFG.Theorems.SimplePower.Banach.RegularizedBareSolution
              d (paperEpsSeq k) V H DpH
              (Hamiltonian.gammaBar hpow.α hpow.β)
              (hpow.β + 1)
              (Hamiltonian.betaBar' hpow.β)
              (Hamiltonian.gammaBar' hpow.α hpow.β)),
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        0 ≤ paperEpsTerms (V := V) (H := H) (DpH := DpH)
              (paperEpsSeq k)
              (Hamiltonian.gammaBar hpow.α hpow.β) sol x
  /-- Integrability of the paper regulariser residue on the unit cube. -/
  hEpsInt :
    ∀ (sol : StationaryMFG.Theorems.SimplePower.Banach.RegularizedBareSolution
              d (paperEpsSeq k) V H DpH
              (Hamiltonian.gammaBar hpow.α hpow.β)
              (hpow.β + 1)
              (Hamiltonian.betaBar' hpow.β)
              (Hamiltonian.gammaBar' hpow.α hpow.β)),
      MeasureTheory.Integrable
        (paperEpsTerms (V := V) (H := H) (DpH := DpH)
          (paperEpsSeq k)
          (Hamiltonian.gammaBar hpow.α hpow.β) sol)
        (MeasureTheory.volume.restrict (Periodic.UnitCube d))
  /-- AE non-negativity of the primal density `sol.m` (paper-faithful
  shape: `0 ≤ m`).

  **Phase 1 sub-deliverable D4.1c-e
  (`infra-P5-T10-D4-1c-e-replace-hMpos-hmNonneg`):** the legacy
  strict-positivity field `hMpos : 0 < sol.m` has been dropped.
  The strict-positivity content required by the C-class consumer
  `AprioriUniformPerSolHypothesesC_int.hMpos` at the
  `T10PaperResidues.of_paperHypotheses` call site is now isolated
  behind the dedicated B-class authorisation parameter
  `paperHMposAuth` (parallel to `paperHVbndAuth` from D4.1c-d).
  Eliminating that auth parameter is gated on retyping the
  `AprioriUniformPerSolHypothesesC_int` consumer to accept
  `hmNonneg : 0 ≤ᵐ sol.m` (or via the `μ_n := μ + 1/n` perturbation
  argument planned for v7 Phase 4). -/
  hmNonneg :
    ∀ (sol : StationaryMFG.Theorems.SimplePower.Banach.RegularizedBareSolution
              d (paperEpsSeq k) V H DpH
              (Hamiltonian.gammaBar hpow.α hpow.β)
              (hpow.β + 1)
              (Hamiltonian.betaBar' hpow.β)
              (Hamiltonian.gammaBar' hpow.α hpow.β)),
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        0 ≤ sol.m x
  /-- Paper-faithful integral V-data record `AprioriVData` carrying
  the two integral V-bounds `∫|V| ≤ Vint_bound` and
  `∫|V|^{β̄'} ≤ Vβp_bound`, derivable directly from
  `hV : MemLpPer (ENNReal.ofReal (β̄' β)) V` via
  `AprioriVData.of_hV` (D4.0a producer, reflexive choice).
  Replaces the transitional triple `(hVbnd, hVint, hVβp)` previously
  carried in this bundle (dropped in
  `infra-P5-T10-D4-1c-d-drop-hVbnd-PaperCBundleForK`). The pointwise
  `|V| ≤ 0` shape forced `V = 0` a.e. (impossible for general
  `V ∈ L^{β̄'}`); the integral form `vData` is the paper-canonical
  form. Per
  `infra-P5-T10-D4-4-PaperCBundleForK-fix-scaffolding`. -/
  vData :
    StationaryMFG.Theorems.SimplePower.Banach.AprioriVData
      (d := d)
      (Hamiltonian.betaBar' hpow.β) V
  /-- A.e.-periodicity of the primal value `sol.u`.

  **Phase 2c-δ retype**
  (`infra-P5-T10-v7-phase2c-delta-paperCBundleFor-of-paperHypotheses`):
  retyped from pointwise `IsPeriodic sol.u` to
  `Periodic.AEPeriodic sol.u`, matching the v7 Phase 2a retype of
  `RegularizedBareSolution.hu_per` and the v7 Phase 2c-γ retype of
  `AprioriUniformPerSolHypothesesC_int.hu_per`. This lets
  `PaperCBundleForK.of_paperHypotheses` source the field directly from
  `sol.hu_per` (no `AEPeriodic.ofPeriodic` wrapper needed). -/
  hu_per :
    ∀ (sol : StationaryMFG.Theorems.SimplePower.Banach.RegularizedBareSolution
              d (paperEpsSeq k) V H DpH
              (Hamiltonian.gammaBar hpow.α hpow.β)
              (hpow.β + 1)
              (Hamiltonian.betaBar' hpow.β)
              (Hamiltonian.gammaBar' hpow.α hpow.β)),
      Periodic.AEPeriodic (d := d) sol.u
  /-- A.e.-periodicity of each gradient component `sol.Du i`.

  **Phase 2c-δ retype**: parallel to `hu_per`. -/
  hDu_per :
    ∀ (sol : StationaryMFG.Theorems.SimplePower.Banach.RegularizedBareSolution
              d (paperEpsSeq k) V H DpH
              (Hamiltonian.gammaBar hpow.α hpow.β)
              (hpow.β + 1)
              (Hamiltonian.betaBar' hpow.β)
              (Hamiltonian.gammaBar' hpow.α hpow.β)),
      ∀ i, Periodic.AEPeriodic (d := d) (sol.Du i)
  /-- Sobolev-embedding integrability of `|sol.u|^{β̄'}` on the cube. -/
  hUbetap_int :
    ∀ (sol : StationaryMFG.Theorems.SimplePower.Banach.RegularizedBareSolution
              d (paperEpsSeq k) V H DpH
              (Hamiltonian.gammaBar hpow.α hpow.β)
              (hpow.β + 1)
              (Hamiltonian.betaBar' hpow.β)
              (Hamiltonian.gammaBar' hpow.α hpow.β)),
      MeasureTheory.Integrable
        (fun x => |sol.u x| ^ Hamiltonian.betaBar' hpow.β)
        (MeasureTheory.volume.restrict (Periodic.UnitCube d))

/-- **Closed producer for `PaperCBundleForK`** (v7 Phase 2c-δ,
`infra-P5-T10-v7-phase2c-delta-paperCBundleFor-of-paperHypotheses`).

Builds the per-`k` paper-canonical C-class bundle directly from the
B-class authorised inputs `(V, H, DpH, hpow, hV)` — no
`paperCBundleFor` parameter required. The three substantive
sub-proofs are:

* `hEpsNN`: `paperEpsTerms ≥ 0` a.e., via `mul_nonneg`,
  `Real.rpow_nonneg`, and `euclideanDot_self_nonneg`.
* `hEpsInt`: `paperEpsTerms ∈ L¹` on the cube. The gradient term
  `(Du⬝Du)^(γ̄/2)` is dominated by `(d:ℝ)^(γ̄-1) · ∑ᵢ |Du i|^γ̄`
  (Jensen, via `Banach.euclideanDot_self_rpow_le_sum_rpow`), and
  each `|Du i|^γ̄ ∈ L¹` via `MemLp.integrable_norm_rpow` on
  `sol.hDuLp i`. The `|u|^γ̄` term comes from `sol.huLp` similarly.
  Each term is then scaled by `ε = paperEpsSeq k` via
  `Integrable.const_mul`.
* `hUbetap_int`: via `uBetap_int_of_memLpPer_gamma`.

The remaining fields are pure plumbing:
`hmNonneg := sol.hmNonneg`, `vData := AprioriVData.of_hV`,
`hu_per := sol.hu_per`, `hDu_per := sol.hDu_per` (all AE-periodic
after the Phase 2c-α/β/γ retypes).

**Auth count drop**: with this producer, the `paperCBundleFor`
parameter of `T10PaperResidues.of_paperHypotheses` is no longer
needed — it is constructed in-body via this producer. Auth count
10 → 9 B-class authorised inputs. -/
noncomputable def PaperCBundleForK.of_paperHypotheses
    {d : ℕ}
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (hV : Periodic.MemLpPer (d := d)
            (ENNReal.ofReal (Hamiltonian.betaBar' hpow.β)) V)
    (k : ℕ) :
    PaperCBundleForK (d := d) V H DpH hpow k where
  hEpsNN := by
    intro sol
    refine Filter.Eventually.of_forall (fun x => ?_)
    -- `paperEpsTerms x = ε * (Du⬝Du)^(γ̄/2) + ε * |u|^γ̄`, both
    -- non-negative since `ε > 0`, `Du⬝Du ≥ 0`, `|u| ≥ 0`.
    have hε_nn : 0 ≤ paperEpsSeq k := (paperEpsSeq_pos k).le
    have hdot_nn :
        0 ≤ ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x)) :=
      StationaryMFG.Theorems.SimplePower.Banach.euclideanDot_self_nonneg _
    have hgrad_nn :
        0 ≤ ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
              ^ (Hamiltonian.gammaBar hpow.α hpow.β / 2) :=
      Real.rpow_nonneg hdot_nn _
    have hu_nn :
        0 ≤ |sol.u x| ^ Hamiltonian.gammaBar hpow.α hpow.β :=
      Real.rpow_nonneg (abs_nonneg _) _
    unfold paperEpsTerms
    exact add_nonneg (mul_nonneg hε_nn hgrad_nn)
                     (mul_nonneg hε_nn hu_nn)
  hEpsInt := by
    intro sol
    have hα_le : (1 : ℝ) ≤ hpow.α := hpow.hα.le
    have hβ_pos : 0 < hpow.β := hpow.hβ
    have hγ_pos : 0 < Hamiltonian.gammaBar hpow.α hpow.β :=
      Hamiltonian.gammaBar_pos hpow.α hpow.β
        (lt_of_lt_of_le zero_lt_one hα_le) hβ_pos
    have hγ_one_le : (1 : ℝ) ≤ Hamiltonian.gammaBar hpow.α hpow.β :=
      (Hamiltonian.one_lt_gammaBar hpow.α hpow.β hpow.hα hβ_pos).le
    have hγ_nn : 0 ≤ Hamiltonian.gammaBar hpow.α hpow.β := hγ_pos.le
    have hp_ne_zero : ENNReal.ofReal (Hamiltonian.gammaBar hpow.α hpow.β) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr hγ_pos).ne'
    have hp_ne_top : ENNReal.ofReal (Hamiltonian.gammaBar hpow.α hpow.β) ≠ ⊤ :=
      ENNReal.ofReal_ne_top
    have hp_toReal :
        (ENNReal.ofReal (Hamiltonian.gammaBar hpow.α hpow.β)).toReal
          = Hamiltonian.gammaBar hpow.α hpow.β :=
      ENNReal.toReal_ofReal hγ_nn
    -- Step 1: `|sol.u|^γ̄ ∈ L¹` via `MemLp.integrable_norm_rpow` on
    -- `sol.huLp`, realigning `‖u x‖ = |u x|` a.e.
    have hu_pow_int : MeasureTheory.Integrable
        (fun x => |sol.u x| ^ Hamiltonian.gammaBar hpow.α hpow.β)
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)) := by
      have hL : MeasureTheory.MemLp sol.u
          (ENNReal.ofReal (Hamiltonian.gammaBar hpow.α hpow.β))
          (MeasureTheory.volume.restrict (Periodic.UnitCube d)) :=
        sol.huLp
      have hI : MeasureTheory.Integrable
          (fun x => ‖sol.u x‖ ^
            (ENNReal.ofReal (Hamiltonian.gammaBar hpow.α hpow.β)).toReal)
          (MeasureTheory.volume.restrict (Periodic.UnitCube d)) :=
        hL.integrable_norm_rpow hp_ne_zero hp_ne_top
      rw [hp_toReal] at hI
      refine hI.congr ?_
      refine Filter.Eventually.of_forall (fun x => ?_)
      simp [Real.norm_eq_abs]
    -- Step 2: per-coord `|sol.Du i|^γ̄ ∈ L¹` via the same route.
    have hcoord_int : ∀ i, MeasureTheory.Integrable
        (fun x => |sol.Du i x| ^ Hamiltonian.gammaBar hpow.α hpow.β)
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)) := by
      intro i
      have hL : MeasureTheory.MemLp (sol.Du i)
          (ENNReal.ofReal (Hamiltonian.gammaBar hpow.α hpow.β))
          (MeasureTheory.volume.restrict (Periodic.UnitCube d)) :=
        sol.hDuLp i
      have hI : MeasureTheory.Integrable
          (fun x => ‖sol.Du i x‖ ^
            (ENNReal.ofReal (Hamiltonian.gammaBar hpow.α hpow.β)).toReal)
          (MeasureTheory.volume.restrict (Periodic.UnitCube d)) :=
        hL.integrable_norm_rpow hp_ne_zero hp_ne_top
      rw [hp_toReal] at hI
      refine hI.congr ?_
      refine Filter.Eventually.of_forall (fun x => ?_)
      simp [Real.norm_eq_abs]
    -- Step 3: the sum-over-coords is integrable.
    have hsum_int : MeasureTheory.Integrable
        (fun x => ∑ i : Fin d,
                    |sol.Du i x| ^ Hamiltonian.gammaBar hpow.α hpow.β)
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)) :=
      MeasureTheory.integrable_finset_sum (Finset.univ)
        (fun i _ => hcoord_int i)
    -- Step 4: `(d:ℝ)^(γ̄-1) · (sum) ∈ L¹` via `const_mul`.
    have hScaledSum_int : MeasureTheory.Integrable
        (fun x => ((d : ℝ)) ^ (Hamiltonian.gammaBar hpow.α hpow.β - 1) *
                  ∑ i : Fin d,
                    |sol.Du i x| ^ Hamiltonian.gammaBar hpow.α hpow.β)
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)) :=
      hsum_int.const_mul _
    -- Step 5: dominate the gradient term `(Du⬝Du)^(γ̄/2)` pointwise.
    have hDu_aemeas : ∀ i, AEMeasurable (sol.Du i)
          (MeasureTheory.volume.restrict (Periodic.UnitCube d)) :=
      fun i => (sol.hDuLp i).aestronglyMeasurable.aemeasurable
    have hself_aemeas : AEMeasurable
        (fun x : (Fin d → ℝ) =>
          (fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)) := by
      unfold StationaryMFG.Hamiltonian.euclideanDot
      exact Finset.aemeasurable_fun_sum (Finset.univ)
        (fun i _ => (hDu_aemeas i).mul (hDu_aemeas i))
    have hgrad_aemeas : AEMeasurable
        (fun x => ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
                    ^ (Hamiltonian.gammaBar hpow.α hpow.β / 2))
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)) :=
      hself_aemeas.pow_const _
    have hgrad_int : MeasureTheory.Integrable
        (fun x => ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
                    ^ (Hamiltonian.gammaBar hpow.α hpow.β / 2))
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)) := by
      refine hScaledSum_int.mono' ?meas ?dom
      case meas => exact hgrad_aemeas.aestronglyMeasurable
      case dom =>
        refine Filter.Eventually.of_forall ?_
        intro x
        have hpoint :
            ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
                ^ (Hamiltonian.gammaBar hpow.α hpow.β / 2)
              ≤ ((d : ℝ)) ^ (Hamiltonian.gammaBar hpow.α hpow.β - 1) *
                  ∑ i, |sol.Du i x| ^ Hamiltonian.gammaBar hpow.α hpow.β :=
          StationaryMFG.Theorems.SimplePower.Banach.euclideanDot_self_rpow_le_sum_rpow
            (d := d) hγ_one_le (fun i => sol.Du i x)
        have hnn :
            0 ≤ ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
                  ^ (Hamiltonian.gammaBar hpow.α hpow.β / 2) :=
          Real.rpow_nonneg
            (StationaryMFG.Theorems.SimplePower.Banach.euclideanDot_self_nonneg _) _
        rw [Real.norm_eq_abs, abs_of_nonneg hnn]
        exact hpoint
    -- Step 6: scale both summands by `ε = paperEpsSeq k` and combine.
    have hgrad_eps_int : MeasureTheory.Integrable
        (fun x => paperEpsSeq k *
          ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
            ^ (Hamiltonian.gammaBar hpow.α hpow.β / 2))
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)) :=
      hgrad_int.const_mul (paperEpsSeq k)
    have hu_eps_int : MeasureTheory.Integrable
        (fun x => paperEpsSeq k *
          |sol.u x| ^ Hamiltonian.gammaBar hpow.α hpow.β)
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)) :=
      hu_pow_int.const_mul (paperEpsSeq k)
    -- The sum matches `paperEpsTerms (paperEpsSeq k)
    -- (gammaBar hpow.α hpow.β) sol` definitionally.
    exact hgrad_eps_int.add hu_eps_int
  hmNonneg := fun sol => sol.hmNonneg
  vData := StationaryMFG.Theorems.SimplePower.Banach.AprioriVData.of_hV
    (β := hpow.β) hpow.hβ V hV
  hu_per := fun sol => sol.hu_per
  hDu_per := fun sol i => sol.hDu_per i
  hUbetap_int := fun sol =>
    StationaryMFG.Theorems.SimplePower.Banach.uBetap_int_of_memLpPer_gamma
      (α := hpow.α) (β := hpow.β) hpow.hα.le hpow.hβ sol.huLp


/-! ### `PaperSolForSideInputs` — 9-field per-`sol` side-input bundle
(`paperSolFor-side-inputs`, iter db57a9)

Packaged form of the 9 paper-side authorisation slots consumed by
`RegularizedPaperSolutionData.of_regularizedBareSolution`
(`Banach/RegularizedSequence.lean:28209`). The struct is parameterised
by a specific `sol : RegularizedBareSolution …` at the
paper-canonical exponent quadruple
`(γ̄, β̄, β̄', γ̄') = (paperGammaBar, paperBetaBar, paperBetaBarPrime,
paperGammaBarPrime)`.

This iteration lands the **struct definition** plus the constructor
`PaperSolForSideInputs.of_paperHypotheses_partial` that discharges
the 3 mechanically-trivial fields and takes the 6 remaining real-work
fields as parameters. Per the iter db57a9 scope review (audit
summary in task `paperSolFor-side-inputs`), the 6 remaining fields
each require dedicated analytic work and are deferred to follow-up
children:

* `hResM`, `hMUH_int`, `hRHS_int` — Hölder integrability of
  `m · (HJ-residual)`, `m · (u + H − V)`, and the line-1212 RHS.
* `hCont_signed` — DCT continuity for the `m + (1/(n+1))·σ·(m·1_S)`
  perturbation (different shape from
  `mfgOperatorEpsPair_tendsto_signed_perturbation_of_paperHypotheses`).
* `hVI_pos` / `hVI_neg` — transport-VI σ→0 Minty bridge via
  `strongTransport_at_uEpsi_hVI_{pos,neg}_of_perturbed`. -/

/-- The 9-field per-`sol` side-input bundle consumed by
`RegularizedPaperSolutionData.of_regularizedBareSolution`. Each field
matches that consumer's argument shape byte-for-byte. -/
structure PaperSolForSideInputs
    {d : ℕ}
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (k : ℕ)
    [Fact (1 ≤ ENNReal.ofReal (hpow.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))]
    (sol : StationaryMFG.Theorems.SimplePower.Banach.RegularizedBareSolution
              d (paperEpsSeq k) V H DpH
              (Hamiltonian.gammaBar hpow.α hpow.β)
              (hpow.β + 1)
              (Hamiltonian.betaBar' hpow.β)
              (Hamiltonian.gammaBar' hpow.α hpow.β)) where
  /-- ρ-perturbed primal `MemLpPer βBar` cert. -/
  hRhoMemLp :
    ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
    ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
      (MeasureTheory.volume.restrict (Periodic.UnitCube d)) S < ∞ →
    ∀ n : ℕ,
      Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1))
        (fun x => sol.m x + (1 / ((n : ℝ) + 1)) * σ *
                    (sol.m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
  /-- σ-scaled primal indicator `MemLpPer` cert. -/
  hSigmaMIndicMemLp :
    ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
    ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
      (MeasureTheory.volume.restrict (Periodic.UnitCube d)) S < ∞ →
      Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1))
        (fun x => σ * sol.m x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
  /-- Signed-perturbed continuity. -/
  hCont_signed :
    ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
    ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
      (MeasureTheory.volume.restrict (Periodic.UnitCube d)) S < ∞ →
      Filter.Tendsto
        (fun n : ℕ =>
          mfgOperatorEpsPair
            (V := V) (H := H) (DpH := DpH)
            (Hamiltonian.gammaBar hpow.α hpow.β) (paperEpsSeq k)
            sol.Du
            (fun x => sol.m x + (1 / ((n : ℝ) + 1)) * σ *
                        (sol.m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
            sol.u
            (fun _ _ => (0 : ℝ))
            (fun x => σ * sol.m x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
            (fun _ => (0 : ℝ)))
        Filter.atTop
        (𝓝 (mfgOperatorEpsPair
              (V := V) (H := H) (DpH := DpH)
              (Hamiltonian.gammaBar hpow.α hpow.β) (paperEpsSeq k)
              sol.Du sol.m sol.u
              (fun _ _ => (0 : ℝ))
              (fun x => σ * sol.m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              (fun _ => (0 : ℝ))))
  /-- HJB-residual × `m` integrability. -/
  hResM :
    MeasureTheory.Integrable
      (fun x =>
        StationaryMFG.Theorems.SimplePower.hjbResidual V H sol.Du sol.m sol.u x
          * sol.m x)
      (MeasureTheory.volume.restrict (Periodic.UnitCube d))
  /-- VI-positive direction lower bound. -/
  hVI_pos :
    (0 : ℝ) ≤
    ∫ x in Periodic.UnitCube d,
        (sol.m x * ((DpH x (fun i => sol.Du i x) (sol.m x))
                      ⬝ (fun i => sol.Du i x))
          + (sol.m x - 1) * sol.u x
          + (paperEpsSeq k) *
              ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
                ^ (Hamiltonian.gammaBar hpow.α hpow.β / 2)
          + (paperEpsSeq k) * |sol.u x| ^ Hamiltonian.gammaBar hpow.α hpow.β)
        ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
  /-- VI-negative direction upper bound. -/
  hVI_neg :
    ∫ x in Periodic.UnitCube d,
        (sol.m x * ((DpH x (fun i => sol.Du i x) (sol.m x))
                      ⬝ (fun i => sol.Du i x))
          + (sol.m x - 1) * sol.u x
          + (paperEpsSeq k) *
              ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
                ^ (Hamiltonian.gammaBar hpow.α hpow.β / 2)
          + (paperEpsSeq k) * |sol.u x| ^ Hamiltonian.gammaBar hpow.α hpow.β)
        ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
      ≤ (0 : ℝ)
  /-- `u` integrability. -/
  hu_int :
    MeasureTheory.Integrable sol.u
      (MeasureTheory.volume.restrict (Periodic.UnitCube d))
  /-- `m * (u + H − V)` integrability. -/
  hMUH_int :
    MeasureTheory.Integrable
      (fun x => sol.m x *
        (sol.u x + H x (fun i => sol.Du i x) (sol.m x) - V x))
      (MeasureTheory.volume.restrict (Periodic.UnitCube d))
  /-- Paper-line-1212 RHS integrability. -/
  hRHS_int :
    MeasureTheory.Integrable
      (fun x =>
        sol.m x * (-H x (fun i => sol.Du i x) (sol.m x)
                  + (DpH x (fun i => sol.Du i x) (sol.m x))
                      ⬝ (fun i => sol.Du i x))
          + V x * sol.m x
          + (paperEpsSeq k) *
              ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
                ^ (Hamiltonian.gammaBar hpow.α hpow.β / 2)
          + (paperEpsSeq k) * |sol.u x| ^ Hamiltonian.gammaBar hpow.α hpow.β)
      (MeasureTheory.volume.restrict (Periodic.UnitCube d))

/-! ### Phase 1 of the iter-0622 v2 plan — integrability side inputs
(`paperSolFor-side-inputs-hResM-hMUH-hRHS`)

The three lemmas below close the integrability fields `hResM`,
`hMUH_int`, `hRHS_int` of `PaperSolForSideInputs` directly from
paper hypotheses + `(sol, cBundle)`. They are adapted from the
in-body T10 discharge in `thm_main_simplePowerGrowth_concrete`
(specifically the `hRes_Lp_k` → `hMresidual_int_k` / `hMu_int_k` /
`hMDpHDu_int_k` chain and the `hRHSbelow_int_k` recombination
identity), repackaged as standalone closed lemmas. The downstream
`of_paperHypotheses_partial` constructor consumes them in place of
the prior explicit `hResM_in` / `hMUH_int_in` / `hRHS_int_in`
parameters. -/

/-- Local helper: a finite-measure instance on the restricted unit cube.
Used in the integrability-side-input lemmas below to invoke
`MemLpPer.mono_exponent_finite` and similar finite-measure ambient
lemmas. -/
private lemma _root_.StationaryMFG.Theorems.SimplePower.UnitCube.isFiniteMeasure_restrict
    {d : ℕ} :
    MeasureTheory.IsFiniteMeasure
      (MeasureTheory.Measure.restrict
        MeasureTheory.volume (Periodic.UnitCube (d := d))) :=
  ⟨by
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ]
    simp⟩

/-- Closed producer for the `hResM` field of `PaperSolForSideInputs`.
HJB-residual × `m` integrability, derived from the residual `MemLpPer
(β̄')` (via `g_memLp_betaBar'_nonneg`) and the primal `MemLpPer (β+1)`
on `m` via Hölder pair `(β̄', β̄) = ((β+1)/β, β+1)`.

Adapted from the in-body `hRes_Lp_k` + `hMresidual_int_k` discharge in
`thm_main_simplePowerGrowth_concrete` (this file, ~lines 2754–2894). -/
lemma paperSolFor_hResM_of_paperHypotheses
    {d : ℕ}
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (hV : Periodic.MemLpPer (d := d)
            (ENNReal.ofReal (Hamiltonian.betaBar' hpow.β)) V)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    (k : ℕ)
    (sol : StationaryMFG.Theorems.SimplePower.Banach.RegularizedBareSolution
              d (paperEpsSeq k) V H DpH
              (Hamiltonian.gammaBar hpow.α hpow.β)
              (hpow.β + 1)
              (Hamiltonian.betaBar' hpow.β)
              (Hamiltonian.gammaBar' hpow.α hpow.β)) :
    MeasureTheory.Integrable
      (fun x =>
        StationaryMFG.Theorems.SimplePower.hjbResidual V H sol.Du sol.m sol.u x
          * sol.m x)
      (MeasureTheory.volume.restrict (Periodic.UnitCube d)) := by
  -- Derived finiteness rider for `Hext` from `hpow + hHat0`.
  have hFin : Hamiltonian.Hext_finite_at_zero (d := d) H :=
    Hamiltonian.Hext_finite_at_zero_of_powerGrowth hpow hHat0
  -- Build residual `MemLpPer (β̄')` via `g_memLp_betaBar'_nonneg`.
  have hu_aemeas : AEMeasurable sol.u
                    (MeasureTheory.volume.restrict (Periodic.UnitCube d)) :=
    sol.huLp.aestronglyMeasurable.aemeasurable
  have hDu_aemeas : ∀ i, AEMeasurable (sol.Du i)
                    (MeasureTheory.volume.restrict (Periodic.UnitCube d)) :=
    fun i => (sol.hDuLp i).aestronglyMeasurable.aemeasurable
  have hm_aemeas : AEMeasurable sol.m
                    (MeasureTheory.volume.restrict (Periodic.UnitCube d)) :=
    sol.hmLp.aestronglyMeasurable.aemeasurable
  have hV_aemeas : AEMeasurable V
                    (MeasureTheory.volume.restrict (Periodic.UnitCube d)) :=
    hV.aestronglyMeasurable.aemeasurable
  have hDu_pi_aemeas :
      AEMeasurable (fun x : (Fin d → ℝ) =>
                    (fun i : Fin d => sol.Du i x))
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)) :=
    AEMeasurable.of_eval hDu_aemeas
  have hxpm : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        (x, (fun i : Fin d => sol.Du i x), sol.m x))
      (MeasureTheory.volume.restrict (Periodic.UnitCube d)) :=
    measurable_id.aemeasurable.prodMk
      (hDu_pi_aemeas.prodMk hm_aemeas)
  have hH_aemeas : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        H x (fun i => sol.Du i x) (sol.m x))
      (MeasureTheory.volume.restrict (Periodic.UnitCube d)) :=
    hpow.measurable_H.comp_aemeasurable hxpm
  have hg_meas :
      MeasureTheory.AEStronglyMeasurable
        (fun x : (Fin d → ℝ) =>
          -(sol.u x)
            - H x (fun i => sol.Du i x) (sol.m x)
            + V x)
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)) :=
    ((hu_aemeas.neg.sub hH_aemeas).add hV_aemeas).aestronglyMeasurable
  -- Apply `g_memLp_betaBar'_nonneg`. The result has exponent
  -- `(hpow.β + 1) / hpow.β = betaBar' hpow.β`.
  have hres_raw :=
    Hamiltonian.g_memLp_betaBar'_nonneg
      (d := d) hpow hHat0 hFin hAgree
      V sol.u sol.m sol.Du
      sol.hmNonneg hg_meas sol.hmLp sol.huLp sol.hDuLp hV
  -- Identify with `hjbResidual`. `betaBar' hpow.β = (β+1)/β` definitionally.
  have hRes_Lp : Periodic.MemLpPer (d := d)
      (ENNReal.ofReal (Hamiltonian.betaBar' hpow.β))
      (StationaryMFG.Theorems.SimplePower.hjbResidual
        V H sol.Du sol.m sol.u) := by
    exact hres_raw
  -- Hölder pair `(β̄', β̄)`: `hpqBeta_paper hpow` gives `β̄.HolderConjugate β̄'`;
  -- take `.symm` for the residual-then-m direction.
  have hβConj : Real.HolderConjugate (Hamiltonian.betaBar' hpow.β)
                                      (Hamiltonian.betaBar hpow.β) :=
    (StationaryMFG.Theorems.SimplePower.Banach.hpqBeta_paper hpow).symm
  -- `m ∈ L^{β+1} = L^{β̄}`.
  have hmLp_β : Periodic.MemLpPer (d := d)
                  (ENNReal.ofReal (Hamiltonian.betaBar hpow.β))
                  sol.m := by
    have h := sol.hmLp
    simpa [Hamiltonian.betaBar] using h
  -- Hölder integrability `residual * m`.
  have hInt :
      MeasureTheory.IntegrableOn
        (fun x =>
          StationaryMFG.Theorems.SimplePower.hjbResidual
            V H sol.Du sol.m sol.u x * sol.m x)
        (Periodic.UnitCube d) :=
    Periodic.MemLpPer.integrable_mul (d := d) hβConj hRes_Lp hmLp_β
  exact hInt

/-- Closed producer for the `hMUH_int` field of `PaperSolForSideInputs`.
Integrability of `m · (u + H − V)`, derived by observing that
`u + H − V = −(hjbResidual)`, so this integrand is `−(m · residual)`,
which lies in `L^1` by `paperSolFor_hResM_of_paperHypotheses`. -/
lemma paperSolFor_hMUH_int_of_paperHypotheses
    {d : ℕ}
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (hV : Periodic.MemLpPer (d := d)
            (ENNReal.ofReal (Hamiltonian.betaBar' hpow.β)) V)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    (k : ℕ)
    (sol : StationaryMFG.Theorems.SimplePower.Banach.RegularizedBareSolution
              d (paperEpsSeq k) V H DpH
              (Hamiltonian.gammaBar hpow.α hpow.β)
              (hpow.β + 1)
              (Hamiltonian.betaBar' hpow.β)
              (Hamiltonian.gammaBar' hpow.α hpow.β)) :
    MeasureTheory.Integrable
      (fun x => sol.m x *
        (sol.u x + H x (fun i => sol.Du i x) (sol.m x) - V x))
      (MeasureTheory.volume.restrict (Periodic.UnitCube d)) := by
  -- `hResM`: integrability of `residual * m`.
  have hResM := paperSolFor_hResM_of_paperHypotheses
    (d := d) V H DpH hpow hV hHat0 hAgree k sol
  -- Algebraic identity: `m * (u + H - V) = -(residual * m)`, since
  -- `residual = -u - H + V`, so `u + H - V = -residual`.
  refine (hResM.neg).congr ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  show -(StationaryMFG.Theorems.SimplePower.hjbResidual V H sol.Du sol.m sol.u x
            * sol.m x)
      = sol.m x * (sol.u x + H x (fun i => sol.Du i x) (sol.m x) - V x)
  unfold StationaryMFG.Theorems.SimplePower.hjbResidual
  ring

/-- Closed producer for the `hRHS_int` field of `PaperSolForSideInputs`.
Integrability of the paper-line-1212 RHS integrand. Reuses the four
ingredients from the earlier T10 discharge of `hRHSbelow_int_k`:

* `m · residual` (= `paperSolFor_hResM_of_paperHypotheses`),
* `m · u` via Hölder pair `(β̄, β̄')` plus `cBundle.hUbetap_int`
  (mirrors `hMu_int_k`),
* `m · (DpH ⬝ Du)` via the `mDpH` flux infrastructure (mirrors
  `hMDpHDu_int_k`),
* `cBundle.hEpsInt sol` for the regulariser term.

Then the algebraic identity
`m·(-H + DpH·Du) + V·m + epsTerms = m·residual + m·u + m·(DpH·Du) + epsTerms`
(the `-m·V` and `+V·m` cancel pointwise) bridges to the RHS goal shape. -/
lemma paperSolFor_hRHS_int_of_paperHypotheses
    {d : ℕ}
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (hV : Periodic.MemLpPer (d := d)
            (ENNReal.ofReal (Hamiltonian.betaBar' hpow.β)) V)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    (k : ℕ)
    (sol : StationaryMFG.Theorems.SimplePower.Banach.RegularizedBareSolution
              d (paperEpsSeq k) V H DpH
              (Hamiltonian.gammaBar hpow.α hpow.β)
              (hpow.β + 1)
              (Hamiltonian.betaBar' hpow.β)
              (Hamiltonian.gammaBar' hpow.α hpow.β))
    (cBundle : PaperCBundleForK V H DpH hpow k) :
    MeasureTheory.Integrable
      (fun x =>
        sol.m x * (-H x (fun i => sol.Du i x) (sol.m x)
                  + (DpH x (fun i => sol.Du i x) (sol.m x))
                      ⬝ (fun i => sol.Du i x))
          + V x * sol.m x
          + (paperEpsSeq k) *
              ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
                ^ (Hamiltonian.gammaBar hpow.α hpow.β / 2)
          + (paperEpsSeq k) * |sol.u x| ^ Hamiltonian.gammaBar hpow.α hpow.β)
      (MeasureTheory.volume.restrict (Periodic.UnitCube d)) := by
  haveI : MeasureTheory.IsFiniteMeasure
      (MeasureTheory.volume.restrict (Periodic.UnitCube (d := d))) :=
    StationaryMFG.Theorems.SimplePower.UnitCube.isFiniteMeasure_restrict
  -- ----- Ingredient 1: `m · residual ∈ L^1` -----
  have hMresidual_int :
      MeasureTheory.Integrable
        (fun x => sol.m x *
          StationaryMFG.Theorems.SimplePower.hjbResidual
            V H sol.Du sol.m sol.u x)
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)) := by
    have h := paperSolFor_hResM_of_paperHypotheses
      (d := d) V H DpH hpow hV hHat0 hAgree k sol
    refine h.congr ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    ring
  -- ----- Ingredient 2: `m · u ∈ L^1` via Hölder `(β̄, β̄')` -----
  have hβ_pos : 0 < hpow.β := hpow.hβ
  have hβ1_pos : 0 < hpow.β + 1 := by linarith
  have hβBar'_pos : 0 < Hamiltonian.betaBar' hpow.β := by
    unfold Hamiltonian.betaBar'
    exact div_pos hβ1_pos hβ_pos
  have hβConj : Real.HolderConjugate (Hamiltonian.betaBar' hpow.β)
                                      (Hamiltonian.betaBar hpow.β) :=
    (StationaryMFG.Theorems.SimplePower.Banach.hpqBeta_paper hpow).symm
  -- `MemLpPer (β̄') u`: derived from `cBundle.hUbetap_int` via
  -- `integrable_norm_rpow_iff` (mirrors `hMu_int_k`'s Step 3).
  have hu_pow_int : MeasureTheory.Integrable
      (fun x => |sol.u x| ^ Hamiltonian.betaBar' hpow.β)
      (MeasureTheory.volume.restrict (Periodic.UnitCube d)) :=
    cBundle.hUbetap_int sol
  have hu_norm_int : MeasureTheory.Integrable
      (fun x => ‖sol.u x‖ ^ Hamiltonian.betaBar' hpow.β)
      (MeasureTheory.volume.restrict (Periodic.UnitCube d)) := by
    refine hu_pow_int.congr ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    simp [Real.norm_eq_abs]
  have hu_aesm : MeasureTheory.AEStronglyMeasurable sol.u
      (MeasureTheory.volume.restrict (Periodic.UnitCube d)) :=
    sol.huLp.aestronglyMeasurable
  have hp_zero : ENNReal.ofReal (Hamiltonian.betaBar' hpow.β) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hβBar'_pos).ne'
  have hp_top : ENNReal.ofReal (Hamiltonian.betaBar' hpow.β) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have h_toReal_βBar' :
      (ENNReal.ofReal (Hamiltonian.betaBar' hpow.β)).toReal
        = Hamiltonian.betaBar' hpow.β :=
    ENNReal.toReal_ofReal hβBar'_pos.le
  have hu_norm_int' : MeasureTheory.Integrable
      (fun x => ‖sol.u x‖ ^
                  (ENNReal.ofReal (Hamiltonian.betaBar' hpow.β)).toReal)
      (MeasureTheory.volume.restrict (Periodic.UnitCube d)) := by
    rw [h_toReal_βBar']; exact hu_norm_int
  have hu_memLp : MeasureTheory.MemLp sol.u
      (ENNReal.ofReal (Hamiltonian.betaBar' hpow.β))
      (MeasureTheory.volume.restrict (Periodic.UnitCube d)) :=
    (MeasureTheory.integrable_norm_rpow_iff hu_aesm hp_zero hp_top).mp
      hu_norm_int'
  have hu_lp : Periodic.MemLpPer (d := d)
      (ENNReal.ofReal (Hamiltonian.betaBar' hpow.β)) sol.u := hu_memLp
  -- `m ∈ L^{β̄}` (`= L^{β+1}`).
  have hmLp_β : Periodic.MemLpPer (d := d)
                  (ENNReal.ofReal (Hamiltonian.betaBar hpow.β))
                  sol.m := by
    have h := sol.hmLp
    simpa [Hamiltonian.betaBar] using h
  -- Apply Hölder pairing `(β̄', β̄)` to `u · m`.
  have hUM_int :
      MeasureTheory.IntegrableOn
        (fun x => sol.u x * sol.m x)
        (Periodic.UnitCube d) :=
    Periodic.MemLpPer.integrable_mul (d := d) hβConj hu_lp hmLp_β
  have hMu_int :
      MeasureTheory.Integrable
        (fun x => sol.m x * sol.u x)
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)) := by
    have h : MeasureTheory.Integrable
        (fun x => sol.u x * sol.m x)
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)) := hUM_int
    refine h.congr ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    ring
  -- ----- Ingredient 3: `m · (DpH ⬝ Du) ∈ L^1` (mDpH flux Hölder) -----
  -- Adapted from `hMDpHDu_int_k` (this file, ~lines 3040–3282).
  have hMDpHDu_int :
      MeasureTheory.Integrable
        (fun x => sol.m x *
          ((DpH x (fun i => sol.Du i x) (sol.m x)) ⬝
              (fun i => sol.Du i x)))
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)) := by
    -- Set the structure exponent `γ := α(β+1)/β = γ̄`.
    set γ : ℝ := hpow.α * (hpow.β + 1) / hpow.β with hγ_def
    have hα_pos : 0 < hpow.α := lt_trans zero_lt_one hpow.hα
    have hγpos : 0 < γ := by
      rw [hγ_def]
      exact div_pos (mul_pos hα_pos hβ1_pos) hβ_pos
    -- γ̄' (the Hölder conjugate of γ on ℝ).
    set γ' : ℝ := γ / (γ - 1) with hγ'_def
    -- Measurabilities.
    have hDu_aemeas : ∀ i, AEMeasurable (sol.Du i)
                      (MeasureTheory.volume.restrict (Periodic.UnitCube d)) :=
      fun i => (sol.hDuLp i).aestronglyMeasurable.aemeasurable
    have hm_aemeas : AEMeasurable sol.m
                      (MeasureTheory.volume.restrict (Periodic.UnitCube d)) :=
      sol.hmLp.aestronglyMeasurable.aemeasurable
    have hDu_pi_aemeas :
        AEMeasurable (fun x : (Fin d → ℝ) =>
                      (fun i : Fin d => sol.Du i x))
          (MeasureTheory.volume.restrict (Periodic.UnitCube d)) :=
      AEMeasurable.of_eval hDu_aemeas
    have hxpm : AEMeasurable
        (fun x : (Fin d → ℝ) =>
          (x, (fun i : Fin d => sol.Du i x), sol.m x))
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)) :=
      measurable_id.aemeasurable.prodMk
        (hDu_pi_aemeas.prodMk hm_aemeas)
    have hDpH_aemeas : AEMeasurable
        (fun x : (Fin d → ℝ) =>
          DpH x (fun i => sol.Du i x) (sol.m x))
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)) :=
      hpow.measurable_DpH.comp_aemeasurable hxpm
    -- L^p sources.
    have hμ_Lp : Periodic.MemLpPer (d := d)
                  (ENNReal.ofReal (hpow.β + 1)) sol.m := sol.hmLp
    have hDu_Lp : ∀ i, Periodic.MemLpPer (d := d)
                  (ENNReal.ofReal γ) (sol.Du i) := sol.hDuLp
    have hμ_nn : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
                  0 ≤ sol.m x := sol.hmNonneg
    -- Dominator membership.
    have hG_mem :
        Periodic.MemLpPer
          (ENNReal.ofReal (γ / (γ - 1)))
          (fun x : (Fin d → ℝ) =>
            hpow.C * (sol.m x *
                ‖fun j => sol.Du j x‖ ^ (hpow.α - 1)
              + sol.m x ^ (1 + hpow.β - hpow.β / hpow.α)
              + sol.m x)) :=
      Hamiltonian.mDpH_dominator_memLpPer_gammaBar' hpow sol.m sol.Du hμ_Lp hDu_Lp
    -- AE strong measurability of the flux vector field.
    have hF_meas :
        MeasureTheory.AEStronglyMeasurable
          (fun x : (Fin d → ℝ) =>
            Hamiltonian.mDpH DpH x
              (fun i => sol.Du i x) (sol.m x))
          (MeasureTheory.volume.restrict (Periodic.UnitCube d)) := by
      unfold Hamiltonian.mDpH
      exact (hm_aemeas.smul hDpH_aemeas).aestronglyMeasurable
    -- Pointwise bound `‖mDpH …‖ ≤ G x` a.e., handling `m = 0`.
    have hF_le :
        ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
          ‖Hamiltonian.mDpH DpH x
              (fun i => sol.Du i x) (sol.m x)‖
            ≤ hpow.C * (sol.m x *
                  ‖fun j => sol.Du j x‖ ^ (hpow.α - 1)
                + sol.m x ^ (1 + hpow.β - hpow.β / hpow.α)
                + sol.m x) := by
      filter_upwards [Hamiltonian.mDpH_pointwise_bound hpow
                        (fun x => fun i => sol.Du i x), hμ_nn]
        with x hxbnd hxnn
      rcases lt_or_eq_of_le hxnn with hxpos | hxz
      · exact hxbnd (sol.m x) hxpos
      · have hmzero : sol.m x = 0 := hxz.symm
        have hLHS : Hamiltonian.mDpH DpH x
            (fun i => sol.Du i x) (sol.m x) = 0 := by
          unfold Hamiltonian.mDpH
          rw [hmzero, zero_smul]
        rw [hLHS, norm_zero]
        have hα1_nn : 0 ≤ ‖fun j => sol.Du j x‖ ^ (hpow.α - 1) :=
          Real.rpow_nonneg (norm_nonneg _) _
        have hμα_nn :
            0 ≤ sol.m x ^ (1 + hpow.β - hpow.β / hpow.α) :=
          Real.rpow_nonneg hxnn _
        have hsum_nn :
            0 ≤ sol.m x *
                ‖fun j => sol.Du j x‖ ^ (hpow.α - 1)
              + sol.m x ^ (1 + hpow.β - hpow.β / hpow.α)
              + sol.m x := by
          have h1 : 0 ≤ sol.m x *
                ‖fun j => sol.Du j x‖ ^ (hpow.α - 1) :=
            mul_nonneg hxnn hα1_nn
          linarith
        exact mul_nonneg hpow.hC.le hsum_nn
    -- Vector `MemLpPer γ̄' (mDpH DpH ·)`.
    have hF_lp :
        Periodic.MemLpPer
          (ENNReal.ofReal (γ / (γ - 1)))
          (fun x : (Fin d → ℝ) =>
            Hamiltonian.mDpH DpH x
              (fun i => sol.Du i x) (sol.m x)) := by
      refine Hamiltonian.mDpH_mem_Lp_gammaBar'
        (q := ENNReal.ofReal (γ / (γ - 1)))
        (m := sol.m)
        (Du := fun x => fun i => sol.Du i x)
        (F := fun x => Hamiltonian.mDpH DpH x
                (fun i => sol.Du i x) (sol.m x))
        (C := hpow.C) (α := hpow.α) (β := hpow.β)
        hF_meas hF_le hG_mem
    -- Per-coordinate `MemLpPer γ̄' ((mDpH ...) i)`.
    have hF_coord_lp : ∀ i, Periodic.MemLpPer (d := d)
        (ENNReal.ofReal γ')
        (fun x : (Fin d → ℝ) =>
          Hamiltonian.mDpH DpH x
            (fun i => sol.Du i x) (sol.m x) i) := by
      intro i
      have hcoord_meas :
          MeasureTheory.AEStronglyMeasurable
            (fun x : (Fin d → ℝ) =>
              Hamiltonian.mDpH DpH x
                (fun i => sol.Du i x)
                (sol.m x) i)
            (MeasureTheory.volume.restrict (Periodic.UnitCube d)) := by
        unfold Hamiltonian.mDpH
        have h := (hm_aemeas.smul hDpH_aemeas)
        exact (h.eval i).aestronglyMeasurable
      have hcoord_le : ∀ x,
          ‖Hamiltonian.mDpH DpH x
              (fun i => sol.Du i x)
              (sol.m x) i‖
            ≤ ‖Hamiltonian.mDpH DpH x
                (fun i => sol.Du i x)
                (sol.m x)‖ :=
        fun x => norm_le_pi_norm _ i
      have : MeasureTheory.MemLp
          (fun x : (Fin d → ℝ) =>
            Hamiltonian.mDpH DpH x
              (fun i => sol.Du i x) (sol.m x) i)
          (ENNReal.ofReal γ')
          (MeasureTheory.volume.restrict (Periodic.UnitCube d)) := by
        refine MeasureTheory.MemLp.mono (hF_lp.toMemLp) hcoord_meas ?_
        refine Filter.Eventually.of_forall (fun x => ?_)
        exact hcoord_le x
      exact MemLp.toMemLpPer this
    -- Hölder conjugacy `(γ', γ)` on ℝ.
    have hγ_one_lt : 1 < γ := by
      rw [hγ_def]
      have h := Hamiltonian.one_lt_gammaBar hpow.α hpow.β hpow.hα hpow.hβ
      simpa [Hamiltonian.gammaBar] using h
    have hγConj_real : Real.HolderConjugate γ' γ := by
      have : Real.HolderConjugate γ γ' := by
        rw [hγ'_def]
        exact Real.HolderConjugate.conjExponent hγ_one_lt
      exact this.symm
    -- Per-`i` Hölder integrability.
    have hcoord_int : ∀ i, MeasureTheory.Integrable
        (fun x =>
          Hamiltonian.mDpH DpH x
              (fun i => sol.Du i x)
              (sol.m x) i
          * sol.Du i x)
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)) := by
      intro i
      have hI :=
        Periodic.MemLpPer.integrable_mul (d := d) hγConj_real
          (hF_coord_lp i) (sol.hDuLp i)
      exact hI
    -- Sum over `i`.
    have hsum_int : MeasureTheory.Integrable
        (fun x => ∑ i : Fin d,
          Hamiltonian.mDpH DpH x
              (fun i => sol.Du i x)
              (sol.m x) i
          * sol.Du i x)
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)) :=
      MeasureTheory.integrable_finset_sum (Finset.univ)
        (fun i _ => hcoord_int i)
    -- Pointwise identity `m · (DpH ⬝ Du) = ∑ i, (mDpH …)_i · Du_i`.
    refine hsum_int.congr ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    show (∑ i : Fin d,
            Hamiltonian.mDpH DpH x
              (fun i => sol.Du i x)
              (sol.m x) i
            * sol.Du i x)
        = sol.m x *
          ((DpH x (fun i => sol.Du i x)
              (sol.m x)) ⬝
            (fun i => sol.Du i x))
    unfold Hamiltonian.mDpH Hamiltonian.euclideanDot
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  -- ----- Ingredient 4: `paperEpsTerms (paperEpsSeq k) γ̄ sol ∈ L^1` -----
  have hEpsInt :
      MeasureTheory.Integrable
        (paperEpsTerms (V := V) (H := H) (DpH := DpH)
          (paperEpsSeq k)
          (Hamiltonian.gammaBar hpow.α hpow.β) sol)
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)) :=
    cBundle.hEpsInt sol
  -- ----- Recombine via algebraic identity -----
  -- Build the candidate sum `m·residual + m·u + m·(DpH·Du) + epsTerms`.
  have hsum : MeasureTheory.Integrable
      (fun x =>
        sol.m x *
            StationaryMFG.Theorems.SimplePower.hjbResidual
              V H sol.Du sol.m sol.u x
          + sol.m x * sol.u x
          + sol.m x *
              ((DpH x (fun i => sol.Du i x)
                    (sol.m x))
                ⬝ (fun i => sol.Du i x))
          + paperEpsTerms (V := V) (H := H) (DpH := DpH)
              (paperEpsSeq k)
              (Hamiltonian.gammaBar hpow.α hpow.β) sol x)
      (MeasureTheory.volume.restrict (Periodic.UnitCube d)) :=
    ((hMresidual_int.add hMu_int).add hMDpHDu_int).add hEpsInt
  -- Bridge to the goal shape via pointwise algebraic identity.
  refine hsum.congr ?_
  refine Filter.Eventually.of_forall ?_
  intro x
  -- Both sides unfold `hjbResidual` and `paperEpsTerms`, then collect.
  -- Use `simp` to expand the definitions, then `ring` to equate.
  simp only [StationaryMFG.Theorems.SimplePower.hjbResidual, paperEpsTerms]
  ring

/-! ### Phase 2 Step 2 — closed producer for `hCont_signed`
(`paperSolFor-side-inputs-hCont-signed-step2-banach-bridge`)

The Step-1 wrapper
`mfgOperatorEpsPair_tendsto_signed_indicator_scaling_of_paperHypotheses`
(`Banach/RegularizedSequence.lean`, end-of-file) requires
**`Measurable`** witnesses on `sol.m, sol.u, sol.Du i, V`. But the
caller (`of_paperHypotheses_partial`) only has the
`AEStronglyMeasurable` certificates encoded in `sol.{hmLp, huLp,
hDuLp}` and `hV.aestronglyMeasurable`. The closed producer below
bridges the gap via the standard `.aestronglyMeasurable.mk` pattern:

* extract measurable representatives `m', u', Du'` for `sol.m, sol.u,
  sol.Du i` (each a.e.-equal to the original on the cube),
* invoke the underlying aggregator
  `mfgOperatorEpsPair_tendsto_set_signed_perturbation_of_paperHypotheses`
  at `(m', u', Du', V)` directly (rather than via Step 1, which is
  bundled at `sol`'s level), building the dominator envelope `Gh`
  in-body from `m', u', Du'`,
* bridge the resulting `Tendsto` back to the conclusion at
  `(sol.m, sol.u, sol.Du)` via `mfgOperatorEpsPair_congr_ae` (test
  triple) + `mfgOperatorEpsPair_congr_ae_primal` (primal triple).

`V` requires its own measurability witness; that's a tiny hygiene
input added to `of_paperHypotheses_partial`. -/

/-- Closed producer for the `hCont_signed` field of
`PaperSolForSideInputs`: operator continuity of the regularised MFG
pairing along the signed-indicator-scaling perturbation
`μ_n := m + (1/(n+1)) · σ · (m · 1_S)`, derived from paper hypotheses
plus `(sol, Measurable V)`. Bridges Step 1 (`Banach/RegularizedSequence`)
from the `Measurable`-witness side to the `AEStronglyMeasurable`-only
side via measurable representatives + `mfgOperatorEpsPair_congr_ae`. -/
lemma paperSolFor_hCont_signed_of_paperHypotheses
    {d : ℕ}
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (hRegH : Hamiltonian.RegularityH (d := d) H DpH)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    (hV : Periodic.MemLpPer (d := d)
            (ENNReal.ofReal (Hamiltonian.betaBar' hpow.β)) V)
    (k : ℕ)
    (sol : StationaryMFG.Theorems.SimplePower.Banach.RegularizedBareSolution
              d (paperEpsSeq k) V H DpH
              (Hamiltonian.gammaBar hpow.α hpow.β)
              (hpow.β + 1)
              (Hamiltonian.betaBar' hpow.β)
              (Hamiltonian.gammaBar' hpow.α hpow.β)) :
    ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
    ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
      (MeasureTheory.volume.restrict (Periodic.UnitCube d)) S < ∞ →
      Filter.Tendsto
        (fun n : ℕ =>
          mfgOperatorEpsPair
            (V := V) (H := H) (DpH := DpH)
            (Hamiltonian.gammaBar hpow.α hpow.β) (paperEpsSeq k)
            sol.Du
            (fun x => sol.m x + (1 / ((n : ℝ) + 1)) * σ *
                        (sol.m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
            sol.u
            (fun _ _ => (0 : ℝ))
            (fun x => σ * sol.m x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
            (fun _ => (0 : ℝ)))
        Filter.atTop
        (𝓝 (mfgOperatorEpsPair
              (V := V) (H := H) (DpH := DpH)
              (Hamiltonian.gammaBar hpow.α hpow.β) (paperEpsSeq k)
              sol.Du sol.m sol.u
              (fun _ _ => (0 : ℝ))
              (fun x => σ * sol.m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              (fun _ => (0 : ℝ)))) := by
  intro σ hσ S hS _hSmeas
  -- Standing positivity facts (mirrors Step 1 setup).
  have hα_pos : 0 < hpow.α := lt_trans one_pos hpow.hα
  have hβ_pos : 0 < hpow.β := hpow.hβ
  have hbb_pos : 0 < hpow.β + 1 := by linarith
  have hβp_pos : 0 < (hpow.β + 1) / hpow.β := div_pos hbb_pos hβ_pos
  -- `Hext_finite_at_zero` is derived from `(hpow, hHat0)`.
  have hHFin : Hamiltonian.Hext_finite_at_zero (d := d) H :=
    Hamiltonian.Hext_finite_at_zero_of_powerGrowth hpow hHat0
  -- Measurable representative of `V` derived from
  -- `hV : MemLpPer ... V`, replacing the dropped `hV_meas : Measurable V`
  -- input (iter post-0627, child task `paperSolFor-final-phase4-aux-hV-meas`).
  -- The underlying aggregator
  -- `mfgOperatorEpsPair_tendsto_set_signed_perturbation_of_paperHypotheses`
  -- requires `Measurable V`; we route through `V'` and bridge back to
  -- the original `V`-parameterised conclusion via
  -- `mfgOperatorEpsPair_congr_V_ae` at the end of the proof.
  set V' : (Fin d → ℝ) → ℝ := hV.aestronglyMeasurable.mk V with hV'_def
  have hV'_meas : Measurable V' := hV.aestronglyMeasurable.measurable_mk
  have hV_ae :
      V =ᵐ[MeasureTheory.volume.restrict (Periodic.UnitCube d)] V' :=
    hV.aestronglyMeasurable.ae_eq_mk
  -- Transport `hV` along `V =ᵐ V'`.
  have hV_repl : Periodic.MemLpPer (d := d)
                   (ENNReal.ofReal (Hamiltonian.betaBar' hpow.β)) V' :=
    hV.congr_ae_unitCube hV_ae
  -- Extract measurable representatives for `sol.m, sol.u, sol.Du i`.
  -- Each is `Measurable` and a.e.-equal to the original on the cube.
  set m' : (Fin d → ℝ) → ℝ :=
      sol.hmLp.aestronglyMeasurable.mk sol.m with hm'_def
  set u' : (Fin d → ℝ) → ℝ :=
      sol.huLp.aestronglyMeasurable.mk sol.u with hu'_def
  set Du' : Fin d → (Fin d → ℝ) → ℝ :=
      fun i => (sol.hDuLp i).aestronglyMeasurable.mk (sol.Du i) with hDu'_def
  have hm'_meas : Measurable m' :=
    sol.hmLp.aestronglyMeasurable.measurable_mk
  have hu'_meas : Measurable u' :=
    sol.huLp.aestronglyMeasurable.measurable_mk
  have hDu'_meas : ∀ i, Measurable (Du' i) := fun i =>
    (sol.hDuLp i).aestronglyMeasurable.measurable_mk
  -- a.e. equalities (note direction `=ᵐ` ).
  have hm'_ae : sol.m =ᵐ[MeasureTheory.volume.restrict (Periodic.UnitCube d)] m' :=
    sol.hmLp.aestronglyMeasurable.ae_eq_mk
  have hu'_ae : sol.u =ᵐ[MeasureTheory.volume.restrict (Periodic.UnitCube d)] u' :=
    sol.huLp.aestronglyMeasurable.ae_eq_mk
  have hDu'_ae : ∀ i,
      sol.Du i =ᵐ[MeasureTheory.volume.restrict (Periodic.UnitCube d)] Du' i :=
    fun i => (sol.hDuLp i).aestronglyMeasurable.ae_eq_mk
  -- Transport `MemLpPer`-certificates onto the representatives.
  have hm'_memLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1)) m' :=
    sol.hmLp.congr_ae_unitCube hm'_ae
  -- Transport `m ≥ 0` a.e. onto `m'`.
  have hm'_nn :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)), 0 ≤ m' x := by
    filter_upwards [sol.hmNonneg, hm'_ae] with x hxnn hxeq
    rw [← hxeq]; exact hxnn
  -- Build the test mass `μEnv := 2 * |m'|` and its `MemLpPer (β+1)`
  -- certificate (used by `g_dominator_memLp_betaBar'`).
  set μEnv : (Fin d → ℝ) → ℝ := fun x => 2 * |m' x| with hμEnv_def
  have hμEnv_memLp : Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1)) μEnv := by
    have h_abs : Periodic.MemLpPer (ENNReal.ofReal (hpow.β + 1))
                  (fun x => |m' x|) := by
      have := hm'_memLp.toMemLp.norm
      have h := MemLp.toMemLpPer this
      have heq : (fun x : (Fin d → ℝ) => ‖m' x‖)
                = (fun x : (Fin d → ℝ) => |m' x|) := by
        funext x; exact Real.norm_eq_abs _
      rw [heq] at h
      exact h
    have h_smul := Periodic.MemLpPer.const_smul (𝕜 := ℝ) h_abs 2
    have heq : ((2 : ℝ) • fun x : (Fin d → ℝ) => |m' x|) = μEnv := by
      funext x; simp [hμEnv_def, Pi.smul_apply, smul_eq_mul]
    rw [heq] at h_smul
    exact h_smul
  -- `u' ∈ L^{γ̄}_per` and `Du' i ∈ L^{γ̄}_per` (transported from `sol`).
  have hu'_memLp_γ :
      Periodic.MemLpPer (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) u' := by
    have := sol.huLp.congr_ae_unitCube hu'_ae
    simpa [Hamiltonian.gammaBar] using this
  have hDu'_memLp_γ : ∀ i,
      Periodic.MemLpPer (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))
        (Du' i) := by
    intro i
    have := (sol.hDuLp i).congr_ae_unitCube (hDu'_ae i)
    simpa [Hamiltonian.gammaBar] using this
  -- Build the dominator envelope `Gh` and its `MemLpPer ((β+1)/β)` cert.
  -- Uses `|V' x|` (not `|V x|`) so that the pointwise bound and the
  -- `Lp` certificate both apply to the `V'`-parameterised aggregator.
  set Gh : (Fin d → ℝ) → ℝ :=
    fun x => hpow.C * (‖fun i => Du' i x‖ ^ hpow.α + 1)
              + hpow.C * (μEnv x ^ hpow.β + 1)
              + |u' x| + |V' x| with hGh_def
  have hGh_memLp :
      Periodic.MemLpPer (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Gh := by
    -- `hV_repl` is already at the exponent `(β+1)/β = betaBar' β`.
    have hV'' : Periodic.MemLpPer
                (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) V' := by
      simpa [Hamiltonian.betaBar'] using hV_repl
    exact Hamiltonian.g_dominator_memLp_betaBar' hpow V' u' μEnv
      Du' hμEnv_memLp hu'_memLp_γ hDu'_memLp_γ hV'' hpow.hC
  -- Pointwise dominator bound `‖-u' - H(Du', μ_n) + V'‖ ≤ Gh` for each `n`.
  have hGh_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ‖-(u' x) - H x (fun i => Du' i x)
              (m' x + (1 / ((n : ℝ) + 1)) * σ *
                (m' x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
              + V' x‖
          ≤ Gh x := by
    intro n
    have habs :=
      Hamiltonian.H_abs_bound_nonneg_of_hHat0 hpow hHat0 hHFin hAgree
    have hσ_abs : |σ| ≤ 1 := by rcases hσ with h | h <;> simp [h]
    have h_one_div_nn : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by
      have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      exact le_of_lt (div_pos one_pos this)
    have h_one_div_le_one : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      rw [div_le_one hpos]
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
      linarith
    filter_upwards [habs, hm'_nn] with x hx_abs hx_m_nn
    set μn : ℝ := m' x + (1 / ((n : ℝ) + 1)) * σ *
                  (m' x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
      with hμn_def
    have hInd_nn : 0 ≤ S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
      by_cases hxS : x ∈ S
      · simp [Set.indicator_of_mem hxS]
      · simp [Set.indicator_of_notMem hxS]
    have hInd_le_one : S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x ≤ 1 := by
      by_cases hxS : x ∈ S
      · simp [Set.indicator_of_mem hxS]
      · simp [Set.indicator_of_notMem hxS]
    have h_factor_nn : 0 ≤ 1 + (1 / ((n : ℝ) + 1)) * σ *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
      have h_prod_abs :
          |(1 / ((n : ℝ) + 1)) * σ *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x| ≤ 1 := by
        rw [abs_mul, abs_mul]
        have h_one_div_abs : |(1 : ℝ) / ((n : ℝ) + 1)| ≤ 1 := by
          rw [abs_of_nonneg h_one_div_nn]; exact h_one_div_le_one
        have h_ind_abs :
            |S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x| ≤ 1 := by
          rw [abs_of_nonneg hInd_nn]; exact hInd_le_one
        have h1 : |1 / ((n : ℝ) + 1)| * |σ| ≤ 1 * 1 :=
          mul_le_mul h_one_div_abs hσ_abs (abs_nonneg _) zero_le_one
        have h2 : |1 / ((n : ℝ) + 1)| * |σ| *
                    |S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x|
                  ≤ 1 * 1 * 1 :=
          mul_le_mul h1 h_ind_abs (abs_nonneg _) (by norm_num)
        linarith [h2]
      have h_prod_ge_neg_one :
          -1 ≤ (1 / ((n : ℝ) + 1)) * σ *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
        have := neg_abs_le ((1 / ((n : ℝ) + 1)) * σ *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
        linarith [h_prod_abs]
      linarith
    have h_factor_le_two : 1 + (1 / ((n : ℝ) + 1)) * σ *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x ≤ 2 := by
      have h_prod_abs :
          |(1 / ((n : ℝ) + 1)) * σ *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x| ≤ 1 := by
        rw [abs_mul, abs_mul]
        have h_one_div_abs : |(1 : ℝ) / ((n : ℝ) + 1)| ≤ 1 := by
          rw [abs_of_nonneg h_one_div_nn]; exact h_one_div_le_one
        have h_ind_abs :
            |S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x| ≤ 1 := by
          rw [abs_of_nonneg hInd_nn]; exact hInd_le_one
        have h1 : |1 / ((n : ℝ) + 1)| * |σ| ≤ 1 * 1 :=
          mul_le_mul h_one_div_abs hσ_abs (abs_nonneg _) zero_le_one
        have h2 : |1 / ((n : ℝ) + 1)| * |σ| *
                    |S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x|
                  ≤ 1 * 1 * 1 :=
          mul_le_mul h1 h_ind_abs (abs_nonneg _) (by norm_num)
        linarith [h2]
      have h_prod_le_one :
          (1 / ((n : ℝ) + 1)) * σ *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x ≤ 1 :=
        le_of_abs_le h_prod_abs
      linarith
    have hμn_eq : μn = m' x * (1 + (1 / ((n : ℝ) + 1)) * σ *
                            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
      rw [hμn_def]; ring
    have hμn_nn : 0 ≤ μn := by
      rw [hμn_eq]; exact mul_nonneg hx_m_nn h_factor_nn
    have hμn_le : μn ≤ 2 * |m' x| := by
      rw [hμn_eq]
      have h_mabs : |m' x| = m' x := abs_of_nonneg hx_m_nn
      rw [h_mabs]
      calc m' x * (1 + (1 / ((n : ℝ) + 1)) * σ *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          ≤ m' x * 2 := by
            exact mul_le_mul_of_nonneg_left h_factor_le_two hx_m_nn
        _ = 2 * m' x := by ring
    have hμEnv_at : μEnv x = 2 * |m' x| := rfl
    have hμn_β_le : μn ^ hpow.β ≤ μEnv x ^ hpow.β := by
      rw [hμEnv_at]
      exact Real.rpow_le_rpow hμn_nn hμn_le hβ_pos.le
    have hμEnv_nn_x : 0 ≤ μEnv x := by
      rw [hμEnv_at]
      have : 0 ≤ |m' x| := abs_nonneg _
      linarith
    have habs1 : |-(u' x) - H x (fun i => Du' i x) μn + V' x|
        ≤ |-(u' x) - H x (fun i => Du' i x) μn| + |V' x| := abs_add_le _ _
    have habs2 : |-(u' x) - H x (fun i => Du' i x) μn|
        ≤ |u' x| + |H x (fun i => Du' i x) μn| := by
      have := abs_sub (-(u' x)) (H x (fun i => Du' i x) μn)
      rw [abs_neg] at this
      linarith
    have hC_nn : 0 ≤ hpow.C := hpow.hC.le
    have hα_term_nn : 0 ≤ ‖fun i => Du' i x‖ ^ hpow.α + 1 := by
      have h1 : 0 ≤ ‖fun i => Du' i x‖ ^ hpow.α :=
        Real.rpow_nonneg (norm_nonneg _) _
      linarith
    have hH_bd := hx_abs (fun i => Du' i x) μn hμn_nn
    have hH_abs_env : |H x (fun i => Du' i x) μn|
        ≤ hpow.C * (‖fun i => Du' i x‖ ^ hpow.α + 1)
            + hpow.C * (μEnv x ^ hpow.β + 1) := by
      have hμn_β_nn : 0 ≤ μn ^ hpow.β := Real.rpow_nonneg hμn_nn _
      have h1 : hpow.C * (μn ^ hpow.β + 1)
            ≤ hpow.C * (μEnv x ^ hpow.β + 1) := by
        apply mul_le_mul_of_nonneg_left _ hC_nn
        linarith
      linarith
    show ‖-(u' x) - H x (fun i => Du' i x) μn + V' x‖ ≤ Gh x
    rw [Real.norm_eq_abs]
    simp only [hGh_def]
    linarith [habs1, habs2, hH_abs_env]
  -- Apply the underlying aggregator with the measurable representatives.
  -- We pass `V'` (a measurable representative of `V`) instead of `V`;
  -- the resulting `Tendsto` is for the `V'`-parameterised operator and
  -- will be bridged back to the `V`-parameterised conclusion via
  -- `mfgOperatorEpsPair_congr_V_ae` at the end of the proof.
  have h_tendsto :=
    StationaryMFG.Theorems.SimplePower.Banach.mfgOperatorEpsPair_tendsto_set_signed_perturbation_of_paperHypotheses
      (V := V') (H := H) (DpH := DpH)
      (ε := paperEpsSeq k)
      (γBar := Hamiltonian.gammaBar hpow.α hpow.β)
      hpow hRegH hHat0 hHFin hAgree
      Du' u' m' σ hσ S hS
      hm'_meas hV'_meas hu'_meas hDu'_meas hm'_nn hm'_memLp
      Gh hGh_memLp hGh_bd
  -- Bridge the conclusion from (m', u', Du') back to (sol.m, sol.u, sol.Du)
  -- via the primal+test congr_ae lemmas. The Tendsto target at the
  -- primal slot uses the perturbed mass; the test triple uses
  -- σ · m · 1_S in the η-slot.
  -- Step A: re-express each `mfgOperatorEpsPair` on the (m', u', Du')
  -- side in terms of (sol.m, sol.u, sol.Du), using congr_ae primal +
  -- congr_ae test.
  -- Build the relevant a.e. equalities for sequence and limit terms.
  have hPert_ae : ∀ n : ℕ,
      (fun x => m' x + (1 / ((n : ℝ) + 1)) * σ *
                  (m' x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
        =ᵐ[MeasureTheory.volume.restrict (Periodic.UnitCube d)]
      (fun x => sol.m x + (1 / ((n : ℝ) + 1)) * σ *
                  (sol.m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)) := by
    intro n
    filter_upwards [hm'_ae] with x hxm
    rw [← hxm]
  have hTestη_ae :
      (fun x => σ * m' x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
        =ᵐ[MeasureTheory.volume.restrict (Periodic.UnitCube d)]
      (fun x => σ * sol.m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
    filter_upwards [hm'_ae] with x hxm
    rw [← hxm]
  -- Apply congr_ae lemmas to rewrite each term in h_tendsto. The
  -- chain operates on the `V'`-parameterised pairings (matching
  -- `h_tendsto`); a final V→V' bridge via `mfgOperatorEpsPair_congr_V_ae`
  -- below transports the result to the `V`-parameterised conclusion.
  -- For each `n`, the sequence term equals the corresponding original.
  have hSeq_eq : ∀ n : ℕ,
      mfgOperatorEpsPair (V := V') (H := H) (DpH := DpH)
        (Hamiltonian.gammaBar hpow.α hpow.β) (paperEpsSeq k)
        Du'
        (fun x => m' x + (1 / ((n : ℝ) + 1)) * σ *
                    (m' x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
        u'
        (fun _ _ => (0 : ℝ))
        (fun x => σ * m' x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
        (fun _ => (0 : ℝ))
      =
      mfgOperatorEpsPair (V := V') (H := H) (DpH := DpH)
        (Hamiltonian.gammaBar hpow.α hpow.β) (paperEpsSeq k)
        sol.Du
        (fun x => sol.m x + (1 / ((n : ℝ) + 1)) * σ *
                    (sol.m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
        sol.u
        (fun _ _ => (0 : ℝ))
        (fun x => σ * sol.m x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
        (fun _ => (0 : ℝ)) := by
    intro n
    -- First substitute primal (Du', m'-perturbed, u') -> (sol.Du, perturbed sol.m, sol.u).
    rw [mfgOperatorEpsPair_congr_ae_primal (V := V') (H := H) (DpH := DpH)
          (γBar := Hamiltonian.gammaBar hpow.α hpow.β)
          (ε := paperEpsSeq k)
          Du' sol.Du
          (fun x => m' x + (1 / ((n : ℝ) + 1)) * σ *
                      (m' x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
          (fun x => sol.m x + (1 / ((n : ℝ) + 1)) * σ *
                      (sol.m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
          u' sol.u
          (fun _ _ => (0 : ℝ))
          (fun x => σ * m' x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          (fun _ => (0 : ℝ))
          (fun i => (hDu'_ae i).symm) (hPert_ae n) hu'_ae.symm]
    -- Then substitute test (η = σ · m' · 1_S) -> (σ · sol.m · 1_S).
    rw [mfgOperatorEpsPair_congr_ae (V := V') (H := H) (DpH := DpH)
          (γBar := Hamiltonian.gammaBar hpow.α hpow.β)
          (ε := paperEpsSeq k)
          sol.Du
          (fun x => sol.m x + (1 / ((n : ℝ) + 1)) * σ *
                      (sol.m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
          sol.u
          (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ))
          (fun x => σ * m' x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          (fun x => σ * sol.m x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ))
          (fun _ => Filter.EventuallyEq.refl _ _)
          hTestη_ae
          (Filter.EventuallyEq.refl _ _)]
  -- For the limit term, primal is (sol.Du, sol.m, sol.u); same bridge.
  have hLim_eq :
      mfgOperatorEpsPair (V := V') (H := H) (DpH := DpH)
        (Hamiltonian.gammaBar hpow.α hpow.β) (paperEpsSeq k)
        Du' m' u'
        (fun _ _ => (0 : ℝ))
        (fun x => σ * m' x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
        (fun _ => (0 : ℝ))
      =
      mfgOperatorEpsPair (V := V') (H := H) (DpH := DpH)
        (Hamiltonian.gammaBar hpow.α hpow.β) (paperEpsSeq k)
        sol.Du sol.m sol.u
        (fun _ _ => (0 : ℝ))
        (fun x => σ * sol.m x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
        (fun _ => (0 : ℝ)) := by
    rw [mfgOperatorEpsPair_congr_ae_primal (V := V') (H := H) (DpH := DpH)
          (γBar := Hamiltonian.gammaBar hpow.α hpow.β)
          (ε := paperEpsSeq k)
          Du' sol.Du m' sol.m u' sol.u
          (fun _ _ => (0 : ℝ))
          (fun x => σ * m' x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          (fun _ => (0 : ℝ))
          (fun i => (hDu'_ae i).symm) hm'_ae.symm hu'_ae.symm]
    rw [mfgOperatorEpsPair_congr_ae (V := V') (H := H) (DpH := DpH)
          (γBar := Hamiltonian.gammaBar hpow.α hpow.β)
          (ε := paperEpsSeq k)
          sol.Du sol.m sol.u
          (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ))
          (fun x => σ * m' x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          (fun x => σ * sol.m x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ))
          (fun _ => Filter.EventuallyEq.refl _ _)
          hTestη_ae
          (Filter.EventuallyEq.refl _ _)]
  -- Transport h_tendsto via the two pointwise rewrites.
  have h_seq_funext :
      (fun n : ℕ =>
        mfgOperatorEpsPair (V := V') (H := H) (DpH := DpH)
          (Hamiltonian.gammaBar hpow.α hpow.β) (paperEpsSeq k)
          Du'
          (fun x => m' x + (1 / ((n : ℝ) + 1)) * σ *
                      (m' x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
          u'
          (fun _ _ => (0 : ℝ))
          (fun x => σ * m' x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          (fun _ => (0 : ℝ)))
      =
      (fun n : ℕ =>
        mfgOperatorEpsPair (V := V') (H := H) (DpH := DpH)
          (Hamiltonian.gammaBar hpow.α hpow.β) (paperEpsSeq k)
          sol.Du
          (fun x => sol.m x + (1 / ((n : ℝ) + 1)) * σ *
                      (sol.m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
          sol.u
          (fun _ _ => (0 : ℝ))
          (fun x => σ * sol.m x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          (fun _ => (0 : ℝ))) := by
    funext n; exact hSeq_eq n
  rw [h_seq_funext, hLim_eq] at h_tendsto
  -- Bridge `V' → V` via `mfgOperatorEpsPair_congr_V_ae`, applied
  -- separately to each sequence term and to the limit.
  have hV_ae_symm :
      V' =ᵐ[MeasureTheory.volume.restrict (Periodic.UnitCube d)] V :=
    hV_ae.symm
  -- Pointwise equality on the sequence: each `n`-term agrees with the
  -- `V`-version by `mfgOperatorEpsPair_congr_V_ae`.
  have hSeqV_eq : ∀ n : ℕ,
      mfgOperatorEpsPair (V := V') (H := H) (DpH := DpH)
        (Hamiltonian.gammaBar hpow.α hpow.β) (paperEpsSeq k)
        sol.Du
        (fun x => sol.m x + (1 / ((n : ℝ) + 1)) * σ *
                    (sol.m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
        sol.u
        (fun _ _ => (0 : ℝ))
        (fun x => σ * sol.m x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
        (fun _ => (0 : ℝ))
      =
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
        (Hamiltonian.gammaBar hpow.α hpow.β) (paperEpsSeq k)
        sol.Du
        (fun x => sol.m x + (1 / ((n : ℝ) + 1)) * σ *
                    (sol.m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
        sol.u
        (fun _ _ => (0 : ℝ))
        (fun x => σ * sol.m x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
        (fun _ => (0 : ℝ)) := fun n =>
    mfgOperatorEpsPair_congr_V_ae V' V H DpH
      (Hamiltonian.gammaBar hpow.α hpow.β) (paperEpsSeq k)
      sol.Du
      (fun x => sol.m x + (1 / ((n : ℝ) + 1)) * σ *
                  (sol.m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
      sol.u
      (fun _ _ => (0 : ℝ))
      (fun x => σ * sol.m x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
      (fun _ => (0 : ℝ))
      hV_ae_symm
  have hLimV_eq :
      mfgOperatorEpsPair (V := V') (H := H) (DpH := DpH)
        (Hamiltonian.gammaBar hpow.α hpow.β) (paperEpsSeq k)
        sol.Du sol.m sol.u
        (fun _ _ => (0 : ℝ))
        (fun x => σ * sol.m x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
        (fun _ => (0 : ℝ))
      =
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
        (Hamiltonian.gammaBar hpow.α hpow.β) (paperEpsSeq k)
        sol.Du sol.m sol.u
        (fun _ _ => (0 : ℝ))
        (fun x => σ * sol.m x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
        (fun _ => (0 : ℝ)) :=
    mfgOperatorEpsPair_congr_V_ae V' V H DpH
      (Hamiltonian.gammaBar hpow.α hpow.β) (paperEpsSeq k)
      sol.Du sol.m sol.u
      (fun _ _ => (0 : ℝ))
      (fun x => σ * sol.m x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
      (fun _ => (0 : ℝ))
      hV_ae_symm
  have h_seq_V_funext :
      (fun n : ℕ =>
        mfgOperatorEpsPair (V := V') (H := H) (DpH := DpH)
          (Hamiltonian.gammaBar hpow.α hpow.β) (paperEpsSeq k)
          sol.Du
          (fun x => sol.m x + (1 / ((n : ℝ) + 1)) * σ *
                      (sol.m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
          sol.u
          (fun _ _ => (0 : ℝ))
          (fun x => σ * sol.m x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          (fun _ => (0 : ℝ)))
      =
      (fun n : ℕ =>
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          (Hamiltonian.gammaBar hpow.α hpow.β) (paperEpsSeq k)
          sol.Du
          (fun x => sol.m x + (1 / ((n : ℝ) + 1)) * σ *
                      (sol.m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
          sol.u
          (fun _ _ => (0 : ℝ))
          (fun x => σ * sol.m x *
                      S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          (fun _ => (0 : ℝ))) := by
    funext n; exact hSeqV_eq n
  rw [h_seq_V_funext, hLimV_eq] at h_tendsto
  exact h_tendsto

/-! ### Phase 3 — closed producer for `hVI_pos` / `hVI_neg`
(`paperSolFor-side-inputs-hVI-pos-neg`, iter 0625)

The transport-VI Minty bridge.

Closes Phase 3 of the iter-0622 v2 plan: produces the
`hVI_pos`/`hVI_neg` pair of `PaperSolForSideInputs` from
`(sol, paper hypotheses)` together with the four authorised
"transport" inputs (`hDpH_cont`, `hmeas_pos`, `hmeas_neg`, and the
per-`n` integrability of the two summand families at the perturbed
primal).

The body:

* discharges `hStep_pos` / `hStep_neg` via
  `strongTransport_at_uEpsi_perturbed` at `s = ±1/(n+1)`;
* feeds them, plus `hβBarPaper`, `hγBarPaper`, `hγ`, `hDpH_cont`,
  `hmeas_pos`, `hmeas_neg`, into `strongTransport_at_uEpsi_unconditional`
  to obtain the unperturbed strong-transport equality;
* splits the equality into `≥ 0` and `≤ 0`.

### `hu_nn_ae` audit (iter 0625)

`strongTransport_at_uEpsi_unconditional` previously asked for
`hu_nn_ae : ∀ᵐ x, 0 ≤ sol.u x`. Direct inspection of the chain
(`Banach/RegularizedSequence.lean`, `_pointwise_tendsto` /
`_hCont_pos` / `_hCont_neg`) showed that this hypothesis was declared
but never used in any body. The companion refactor in this iteration
drops `hu_nn_ae` from those four signatures; no new authorisation is
introduced. -/

/-- Closed producer for the `hVI_pos`/`hVI_neg` pair of
`PaperSolForSideInputs`: the transport-VI inequalities (paper lines
1205–1216), derived from `(sol, paper hypotheses)` plus the four
authorised transport inputs. Built by feeding
`strongTransport_at_uEpsi_perturbed` (per-`n` perturbed VI at
`s = ±1/(n+1)`) into `strongTransport_at_uEpsi_unconditional` (σ → 0
Minty bridge), then splitting the resulting equality.

The integrability authorisations `hI_A_pos n` / `hI_B_pos n` /
`hI_A_neg n` / `hI_B_neg n` match the input shapes of
`strongTransport_at_uEpsi_perturbed` byte-for-byte (the two summand
integrands at the perturbed primal `((1+s)·sol.Du, sol.m, (1+s)·sol.u)`
with `s = ±1/(n+1)`). The dominator-shape authorisations `hmeas_pos`
and `hmeas_neg` cover the a.e.-strong-measurability of the rescaled
integrand `Iperturb/s_n` required by DCT in the unconditional bridge.
The single global continuity `hDpH_cont : ∀ x, Continuous (DpH x · m)`
at the bare primal is the pointwise paper-faithful regularity input,
matching the consumer shape of `_unconditional`. -/
lemma paperSolFor_hVI_pos_neg_of_paperHypotheses
    {d : ℕ}
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (k : ℕ)
    (sol : StationaryMFG.Theorems.SimplePower.Banach.RegularizedBareSolution
              d (paperEpsSeq k) V H DpH
              (Hamiltonian.gammaBar hpow.α hpow.β)
              (hpow.β + 1)
              (Hamiltonian.betaBar' hpow.β)
              (Hamiltonian.gammaBar' hpow.α hpow.β))
    -- A.e. strong measurability of the rescaled perturbed integrand
    -- `Iperturb/s_n` at `s_n = ±1/(n+1)`.
    (hmeas_pos :
      ∀ n : ℕ,
        AEStronglyMeasurable
          (fun x =>
            StationaryMFG.Theorems.SimplePower.Banach.strongTransportPerturbedIntegrand
              sol (1 / ((n : ℝ) + 1)) x / (1 / ((n : ℝ) + 1)))
          (MeasureTheory.volume.restrict (Periodic.UnitCube d)))
    (hmeas_neg :
      ∀ n : ℕ,
        AEStronglyMeasurable
          (fun x =>
            StationaryMFG.Theorems.SimplePower.Banach.strongTransportPerturbedIntegrand
              sol (-(1 / ((n : ℝ) + 1))) x / (-(1 / ((n : ℝ) + 1))))
          (MeasureTheory.volume.restrict (Periodic.UnitCube d)))
    -- Per-`n` integrability inputs of the second summand family at
    -- the perturbed primal (consumed by `strongTransport_at_uEpsi_perturbed`).
    -- Iter post-0631 (paperSolFor-final-phase4-aux-hI-A, 2026-05-17):
    -- the `hI_A_pos` / `hI_A_neg` inputs were dropped; both are now
    -- derived in-body from `hpow + sol` via
    -- `Banach.strongTransport_hI_A_of_sol` (the generic `s ∈ [-1,1] \ {0}`
    -- variant), specialized at `s = ±1/(n+1)`.
    -- Iter post-0635 (paperSolFor-final-phase4-aux-hI-B, 2026-05-17):
    -- the `hI_B_pos` / `hI_B_neg` inputs are likewise dropped; both are
    -- now derived in-body from `hpow + sol` via
    -- `Banach.strongTransport_hI_B_of_sol` (the generic `s ∈ [-1,1] \ {0}`
    -- variant, with ε-scaling), specialized at `s = ±1/(n+1)`.
    :
    -- The two halves of the strong-transport equality at `φ = u_ε`.
    ((0 : ℝ) ≤
      ∫ x in Periodic.UnitCube d,
          (sol.m x * ((DpH x (fun i => sol.Du i x) (sol.m x))
                        ⬝ (fun i => sol.Du i x))
            + (sol.m x - 1) * sol.u x
            + (paperEpsSeq k) *
                ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
                  ^ (Hamiltonian.gammaBar hpow.α hpow.β / 2)
            + (paperEpsSeq k) * |sol.u x| ^ Hamiltonian.gammaBar hpow.α hpow.β)
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))) ∧
    (∫ x in Periodic.UnitCube d,
          (sol.m x * ((DpH x (fun i => sol.Du i x) (sol.m x))
                        ⬝ (fun i => sol.Du i x))
            + (sol.m x - 1) * sol.u x
            + (paperEpsSeq k) *
                ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
                  ^ (Hamiltonian.gammaBar hpow.α hpow.β / 2)
            + (paperEpsSeq k) * |sol.u x| ^ Hamiltonian.gammaBar hpow.α hpow.β)
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
        ≤ (0 : ℝ)) := by
  -- Paper exponent identifications: `βBarReal := hpow.β + 1` and
  -- `γBarReal := gammaBar hpow.α hpow.β` are the sol's own type
  -- parameters; the equalities are `rfl` modulo `gammaBar` unfolding.
  have hβBarPaper : (hpow.β + 1 : ℝ) = hpow.β + 1 := rfl
  have hγBarPaper :
      Hamiltonian.gammaBar hpow.α hpow.β
        = hpow.α * (hpow.β + 1) / hpow.β := rfl
  -- `1 ≤ γ̄` from `1 < α`, `0 < β`.
  have hγ : (1 : ℝ) ≤ Hamiltonian.gammaBar hpow.α hpow.β :=
    le_of_lt (Hamiltonian.one_lt_gammaBar hpow.α hpow.β hpow.hα hpow.hβ)
  -- `1 ≤ γ̄` as an ENNReal (for `strongTransport_at_uEpsi_perturbed`).
  have hγENN : (1 : ℝ≥0∞) ≤
      ENNReal.ofReal (Hamiltonian.gammaBar hpow.α hpow.β) := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
    have hγ_nn : (0 : ℝ) ≤ Hamiltonian.gammaBar hpow.α hpow.β :=
      le_trans (by norm_num : (0:ℝ) ≤ 1) hγ
    exact (ENNReal.ofReal_le_ofReal_iff hγ_nn).mpr hγ
  -- Derive per-`n` integrabilities `hI_A_{pos,neg}` from the generic
  -- `s ∈ [-1, 1] \ {0}` integrability lemma in
  -- `Banach.strongTransport_hI_A_of_sol` (Phase-4 aux closure, iter
  -- post-0631, paperSolFor-final-phase4-aux-hI-A).
  have hI_A_pos :
      ∀ n : ℕ,
        MeasureTheory.IntegrableOn
          (fun x =>
            sol.m x * (DpH x (fun i => sol.Du i x +
                              (1 / ((n : ℝ) + 1)) * sol.Du i x) (sol.m x)
                          ⬝ (fun i => (1 / ((n : ℝ) + 1)) * sol.Du i x))
              + (sol.m x - 1) * ((1 / ((n : ℝ) + 1)) * sol.u x))
          (Periodic.UnitCube d) := by
    intro n
    -- `s := 1/(n+1) ∈ (0, 1] ⊂ [-1, 1] \ {0}`.
    have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
    have hs_pos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hs_le_one : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hn1_pos]; linarith
    have hs_mem : (1 / ((n : ℝ) + 1)) ∈ Set.Icc (-1 : ℝ) 1 :=
      ⟨by linarith, hs_le_one⟩
    have hs_ne : (1 / ((n : ℝ) + 1)) ≠ 0 := hs_pos.ne'
    exact StationaryMFG.Theorems.SimplePower.Banach.strongTransport_hI_A_of_sol
      sol hpow rfl rfl hpow.toRegularityH
      (1 / ((n : ℝ) + 1)) hs_mem hs_ne
  have hI_A_neg :
      ∀ n : ℕ,
        MeasureTheory.IntegrableOn
          (fun x =>
            sol.m x * (DpH x (fun i => sol.Du i x +
                              (-(1 / ((n : ℝ) + 1))) * sol.Du i x) (sol.m x)
                          ⬝ (fun i => (-(1 / ((n : ℝ) + 1))) * sol.Du i x))
              + (sol.m x - 1) * ((-(1 / ((n : ℝ) + 1))) * sol.u x))
          (Periodic.UnitCube d) := by
    intro n
    have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
    have hs_pos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hs_le_one : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hn1_pos]; linarith
    have hs_mem : (-(1 / ((n : ℝ) + 1))) ∈ Set.Icc (-1 : ℝ) 1 :=
      ⟨by linarith, by linarith⟩
    have hs_ne : (-(1 / ((n : ℝ) + 1))) ≠ 0 := neg_ne_zero.mpr hs_pos.ne'
    exact StationaryMFG.Theorems.SimplePower.Banach.strongTransport_hI_A_of_sol
      sol hpow rfl rfl hpow.toRegularityH
      (-(1 / ((n : ℝ) + 1))) hs_mem hs_ne
  -- Derive per-`n` integrabilities `hI_B_{pos,neg}` from the generic
  -- `s ∈ [-1, 1] \ {0}` integrability lemma in
  -- `Banach.strongTransport_hI_B_of_sol` (Phase-4 aux closure, iter
  -- post-0635, paperSolFor-final-phase4-aux-hI-B; ε-scaling variant).
  have hε_ne : paperEpsSeq k ≠ 0 := (paperEpsSeq_pos k).ne'
  have hI_B_pos :
      ∀ n : ℕ,
        MeasureTheory.IntegrableOn
          (fun x =>
            StationaryMFG.Solutions.MFG.vecAbsPowMinusTwo
              (Hamiltonian.gammaBar hpow.α hpow.β)
              (fun i => sol.Du i x + (1 / ((n : ℝ) + 1)) * sol.Du i x)
                * ((fun i => sol.Du i x + (1 / ((n : ℝ) + 1)) * sol.Du i x)
                    ⬝ (fun i => (1 / ((n : ℝ) + 1)) * sol.Du i x))
              + StationaryMFG.Solutions.MFG.absPowMinusTwo
                  (Hamiltonian.gammaBar hpow.α hpow.β)
                  (sol.u x + (1 / ((n : ℝ) + 1)) * sol.u x)
                * ((sol.u x + (1 / ((n : ℝ) + 1)) * sol.u x)
                    * ((1 / ((n : ℝ) + 1)) * sol.u x)))
          (Periodic.UnitCube d) := by
    intro n
    have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
    have hs_pos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hs_le_one : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hn1_pos]; linarith
    have hs_mem : (1 / ((n : ℝ) + 1)) ∈ Set.Icc (-1 : ℝ) 1 :=
      ⟨by linarith, hs_le_one⟩
    have hs_ne : (1 / ((n : ℝ) + 1)) ≠ 0 := hs_pos.ne'
    exact StationaryMFG.Theorems.SimplePower.Banach.strongTransport_hI_B_of_sol
      sol hγ hε_ne (1 / ((n : ℝ) + 1)) hs_mem hs_ne
  have hI_B_neg :
      ∀ n : ℕ,
        MeasureTheory.IntegrableOn
          (fun x =>
            StationaryMFG.Solutions.MFG.vecAbsPowMinusTwo
              (Hamiltonian.gammaBar hpow.α hpow.β)
              (fun i => sol.Du i x + (-(1 / ((n : ℝ) + 1))) * sol.Du i x)
                * ((fun i => sol.Du i x + (-(1 / ((n : ℝ) + 1))) * sol.Du i x)
                    ⬝ (fun i => (-(1 / ((n : ℝ) + 1))) * sol.Du i x))
              + StationaryMFG.Solutions.MFG.absPowMinusTwo
                  (Hamiltonian.gammaBar hpow.α hpow.β)
                  (sol.u x + (-(1 / ((n : ℝ) + 1))) * sol.u x)
                * ((sol.u x + (-(1 / ((n : ℝ) + 1))) * sol.u x)
                    * ((-(1 / ((n : ℝ) + 1))) * sol.u x)))
          (Periodic.UnitCube d) := by
    intro n
    have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
    have hs_pos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hs_le_one : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hn1_pos]; linarith
    have hs_mem : (-(1 / ((n : ℝ) + 1))) ∈ Set.Icc (-1 : ℝ) 1 :=
      ⟨by linarith, by linarith⟩
    have hs_ne : (-(1 / ((n : ℝ) + 1))) ≠ 0 := neg_ne_zero.mpr hs_pos.ne'
    exact StationaryMFG.Theorems.SimplePower.Banach.strongTransport_hI_B_of_sol
      sol hγ hε_ne (-(1 / ((n : ℝ) + 1))) hs_mem hs_ne
  -- Per-`n` step inputs from `strongTransport_at_uEpsi_perturbed`.
  have hStep_pos :
      ∀ n : ℕ,
        (0 : ℝ) ≤
        ∫ x in Periodic.UnitCube d,
          StationaryMFG.Theorems.SimplePower.Banach.strongTransportPerturbedIntegrand
            sol (1 / ((n : ℝ) + 1)) x
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) := by
    intro n
    -- Unfold `strongTransportPerturbedIntegrand` at the goal to match
    -- the conclusion of `strongTransport_at_uEpsi_perturbed`.
    show (0 : ℝ) ≤
      ∫ x in Periodic.UnitCube d,
        StationaryMFG.Theorems.SimplePower.Banach.strongTransportPerturbedIntegrand
          sol (1 / ((n : ℝ) + 1)) x
        ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
    unfold StationaryMFG.Theorems.SimplePower.Banach.strongTransportPerturbedIntegrand
    exact StationaryMFG.Theorems.SimplePower.Banach.strongTransport_at_uEpsi_perturbed
      sol hγENN (1 / ((n : ℝ) + 1)) (hI_A_pos n) (hI_B_pos n)
  have hStep_neg :
      ∀ n : ℕ,
        (0 : ℝ) ≤
        ∫ x in Periodic.UnitCube d,
          StationaryMFG.Theorems.SimplePower.Banach.strongTransportPerturbedIntegrand
            sol (-(1 / ((n : ℝ) + 1))) x
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) := by
    intro n
    show (0 : ℝ) ≤
      ∫ x in Periodic.UnitCube d,
        StationaryMFG.Theorems.SimplePower.Banach.strongTransportPerturbedIntegrand
          sol (-(1 / ((n : ℝ) + 1))) x
        ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
    unfold StationaryMFG.Theorems.SimplePower.Banach.strongTransportPerturbedIntegrand
    exact StationaryMFG.Theorems.SimplePower.Banach.strongTransport_at_uEpsi_perturbed
      sol hγENN (-(1 / ((n : ℝ) + 1))) (hI_A_neg n) (hI_B_neg n)
  -- The unconditional strong-transport equality.
  have hEq :
      (0 : ℝ) =
      ∫ x in Periodic.UnitCube d,
          (sol.m x * ((DpH x (fun i => sol.Du i x) (sol.m x))
                        ⬝ (fun i => sol.Du i x))
            + (sol.m x - 1) * sol.u x
            + (paperEpsSeq k) *
                ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
                  ^ (Hamiltonian.gammaBar hpow.α hpow.β / 2)
            + (paperEpsSeq k) *
                |sol.u x| ^ Hamiltonian.gammaBar hpow.α hpow.β)
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) :=
    StationaryMFG.Theorems.SimplePower.Banach.strongTransport_at_uEpsi_unconditional
      sol hpow hβBarPaper hγBarPaper
      hmeas_pos hmeas_neg hStep_pos hStep_neg
  refine ⟨?_, ?_⟩
  · -- `≥ 0` half: `0 = ∫ …` ⇒ `0 ≤ ∫ …`.
    exact le_of_eq hEq
  · -- `≤ 0` half: `0 = ∫ …` ⇒ `∫ … ≤ 0`.
    exact ge_of_eq hEq

/-! ### `PaperSolForSideInputs.of_paperHypotheses_partial`
(iter db57a9, iter db57a9-2 shrink; iter 0625 Phase 3 wiring)

Full discharger for the 9-field side-input bundle: builds the 3
mechanically-trivial fields (`hRhoMemLp`, `hSigmaMIndicMemLp`,
`hu_int`) directly from `sol`, closes the 3 integrability fields
(`hResM`, `hMUH_int`, `hRHS_int`) via the three closed lemmas above
(iter db57a9-2, Phase 1 of the iter-0622 v2 plan), closes the
`hCont_signed` field via the Phase 2 Step 2 producer
`paperSolFor_hCont_signed_of_paperHypotheses`, and closes
`hVI_pos`/`hVI_neg` via the Phase 3 producer
`paperSolFor_hVI_pos_neg_of_paperHypotheses` (iter 0625). All 9
fields are now constructed in-body; the constructor name retains the
`_partial` suffix for backwards compatibility with downstream
callers. -/

/-- Full constructor for `PaperSolForSideInputs`: discharges the
3 mechanically-trivial fields (`hRhoMemLp`, `hSigmaMIndicMemLp`,
`hu_int`) from `sol` alone, closes the 3 integrability fields
(`hResM`, `hMUH_int`, `hRHS_int`) via the three closed lemmas
`paperSolFor_{hResM,hMUH_int,hRHS_int}_of_paperHypotheses` (Phase 1
of the iter-0622 v2 plan), closes `hCont_signed` via
`paperSolFor_hCont_signed_of_paperHypotheses` (Phase 2 Step 2),
and closes `hVI_pos` / `hVI_neg` via
`paperSolFor_hVI_pos_neg_of_paperHypotheses` (Phase 3, iter 0625).

The Phase 2 `hRegH` and `hV_meas` inputs are needed by the
`hCont_signed` producer (the latter is a trivial hygiene input —
concrete `V` carries it for free). The Phase 3 transport-VI inputs
(`hDpH_cont`, `hmeas_pos`, `hmeas_neg`, and the four per-`n`
integrabilities `hI_A_pos`, `hI_B_pos`, `hI_A_neg`, `hI_B_neg`) are
authorised paper hypotheses matching the consumer shapes of
`strongTransport_at_uEpsi_perturbed` and `strongTransport_at_uEpsi_unconditional`
byte-for-byte. -/
noncomputable def PaperSolForSideInputs.of_paperHypotheses_partial
    {d : ℕ}
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (k : ℕ)
    [Fact (1 ≤ ENNReal.ofReal (hpow.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))]
    (sol : StationaryMFG.Theorems.SimplePower.Banach.RegularizedBareSolution
              d (paperEpsSeq k) V H DpH
              (Hamiltonian.gammaBar hpow.α hpow.β)
              (hpow.β + 1)
              (Hamiltonian.betaBar' hpow.β)
              (Hamiltonian.gammaBar' hpow.α hpow.β))
    -- Paper hypotheses needed to close the 3 integrability fields
    -- (`hResM`, `hMUH_int`, `hRHS_int`) via the closed lemmas
    -- `paperSolFor_{hResM,hMUH_int,hRHS_int}_of_paperHypotheses` (Phase 1
    -- of the iter-0622 v2 plan).
    (hV : Periodic.MemLpPer (d := d)
            (ENNReal.ofReal (Hamiltonian.betaBar' hpow.β)) V)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    (cBundle : PaperCBundleForK V H DpH hpow k)
    -- Extra paper hypotheses needed by the Phase 2 Step 2 producer
    -- `paperSolFor_hCont_signed_of_paperHypotheses` (DCT operator
    -- continuity). The `hV_meas : Measurable V` slot was dropped in
    -- iter post-0627 (child task `paperSolFor-final-phase4-aux-hV-meas`):
    -- the producer now extracts a measurable representative of `V`
    -- internally from `hV : MemLpPer ... V`.
    (hRegH : Hamiltonian.RegularityH (d := d) H DpH)
    -- Authorised transport-VI inputs needed by the Phase 3 producer
    -- `paperSolFor_hVI_pos_neg_of_paperHypotheses` (iter 0625).
    -- Iter post-0631 (paperSolFor-final-phase4-aux-hDpH-cont, 2026-05-17):
    -- the global `hDpH_cont : ∀ x, Continuous fun p => DpH x p (sol.m x)`
    -- input was dropped; the producer now derives the a.e.-pointwise
    -- Tendsto of the perturbed transport quotient inline from
    -- `hpow + sol.hmNonneg` via
    -- `strongTransportPerturbedIntegrand_pointwise_tendsto_of_powerGrowth`.
    (hmeas_pos :
      ∀ n : ℕ,
        AEStronglyMeasurable
          (fun x =>
            StationaryMFG.Theorems.SimplePower.Banach.strongTransportPerturbedIntegrand
              sol (1 / ((n : ℝ) + 1)) x / (1 / ((n : ℝ) + 1)))
          (MeasureTheory.volume.restrict (Periodic.UnitCube d)))
    (hmeas_neg :
      ∀ n : ℕ,
        AEStronglyMeasurable
          (fun x =>
            StationaryMFG.Theorems.SimplePower.Banach.strongTransportPerturbedIntegrand
              sol (-(1 / ((n : ℝ) + 1))) x / (-(1 / ((n : ℝ) + 1))))
          (MeasureTheory.volume.restrict (Periodic.UnitCube d)))
    -- Iter post-0631 (paperSolFor-final-phase4-aux-hI-A, 2026-05-17):
    -- `hI_A_pos` / `hI_A_neg` dropped — derived in-body inside
    -- `paperSolFor_hVI_pos_neg_of_paperHypotheses` via
    -- `Banach.strongTransport_hI_A_of_sol`.
    -- Iter post-0635 (paperSolFor-final-phase4-aux-hI-B, 2026-05-17):
    -- `hI_B_pos` / `hI_B_neg` dropped likewise — derived in-body inside
    -- `paperSolFor_hVI_pos_neg_of_paperHypotheses` via
    -- `Banach.strongTransport_hI_B_of_sol` (ε-scaling variant).
    :
    PaperSolForSideInputs (d := d) V H DpH hpow k sol where
  hRhoMemLp := by
    -- `sol.m + (1/(n+1)) * σ * (sol.m * 1_S) = sol.m + c · (S.indicator sol.m)`
    -- where `c = (1/(n+1)) * σ` is a scalar. Use `MemLpPer.add` +
    -- `MemLp.indicator` + scalar closure.
    intro σ _hσ S hS _hSmeas n
    -- Finite-measure instance on the restricted cube (needed for some
    -- ambient lemmas; lightweight).
    haveI : MeasureTheory.IsFiniteMeasure
              (MeasureTheory.Measure.restrict
                MeasureTheory.volume (Periodic.UnitCube (d := d))) :=
      ⟨by
        rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ]
        simp⟩
    -- `S.indicator sol.m ∈ L^{β+1}_per`.
    have hSm_memLp :
        Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1))
          (S.indicator sol.m) :=
      MemLp.toMemLpPer (MeasureTheory.MemLp.indicator hS.nullMeasurableSet sol.hmLp.toMemLp)
    -- Scale by `(1/(n+1)) * σ`.
    have hScaled :
        Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1))
          (((1 / ((n : ℝ) + 1)) * σ) • S.indicator sol.m) :=
      Periodic.MemLpPer.const_smul (𝕜 := ℝ) hSm_memLp _
    -- Add `sol.m`.
    have hSum := sol.hmLp.add hScaled
    -- Pointwise rewrite the goal into this shape.
    have hPt :
        ∀ x,
          sol.m x + (1 / ((n : ℝ) + 1)) * σ *
                      (sol.m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
            = (sol.m + ((1 / ((n : ℝ) + 1)) * σ) • S.indicator sol.m) x := by
      intro x
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hx : x ∈ S
      · simp [Set.indicator_of_mem hx, mul_comm]
      · simp [Set.indicator_of_notMem hx]
    -- Transport `hSum` along `hPt`.
    apply MemLp.toMemLpPer
    refine (MeasureTheory.memLp_congr_ae ?_).mp hSum.toMemLp
    refine Filter.Eventually.of_forall (fun x => ?_)
    exact (hPt x).symm
  hSigmaMIndicMemLp := by
    -- `σ * sol.m * 1_S = σ • (S.indicator sol.m)` pointwise.
    intro σ _hσ S hS _hSmeas
    haveI : MeasureTheory.IsFiniteMeasure
              (MeasureTheory.Measure.restrict
                MeasureTheory.volume (Periodic.UnitCube (d := d))) :=
      ⟨by
        rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ]
        simp⟩
    have hSm_memLp :
        Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1))
          (S.indicator sol.m) :=
      MemLp.toMemLpPer (MeasureTheory.MemLp.indicator hS.nullMeasurableSet sol.hmLp.toMemLp)
    have hScaled :
        Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1))
          (σ • S.indicator sol.m) :=
      Periodic.MemLpPer.const_smul (𝕜 := ℝ) hSm_memLp _
    have hPt :
        ∀ x, σ * sol.m x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
              = (σ • S.indicator sol.m) x := by
      intro x
      simp only [Pi.smul_apply, smul_eq_mul]
      by_cases hx : x ∈ S
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]
    apply MemLp.toMemLpPer
    refine (MeasureTheory.memLp_congr_ae ?_).mp hScaled.toMemLp
    refine Filter.Eventually.of_forall (fun x => ?_)
    exact (hPt x).symm
  hCont_signed :=
    paperSolFor_hCont_signed_of_paperHypotheses
      (d := d) V H DpH hpow hRegH hHat0 hAgree hV k sol
  hResM :=
    paperSolFor_hResM_of_paperHypotheses
      (d := d) V H DpH hpow hV hHat0 hAgree k sol
  hVI_pos :=
    (paperSolFor_hVI_pos_neg_of_paperHypotheses
      (d := d) V H DpH hpow k sol hmeas_pos hmeas_neg).1
  hVI_neg :=
    (paperSolFor_hVI_pos_neg_of_paperHypotheses
      (d := d) V H DpH hpow k sol hmeas_pos hmeas_neg).2
  hu_int := by
    -- `sol.u ∈ L^γ_per` with `γ ≥ 1`, finite measure on `UnitCube`.
    haveI : MeasureTheory.IsFiniteMeasure
              (MeasureTheory.Measure.restrict
                MeasureTheory.volume (Periodic.UnitCube (d := d))) :=
      ⟨by
        rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ]
        simp⟩
    -- The `Fact (1 ≤ ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))`
    -- instance unfolds `γBar` definitionally.
    have hγ_ge_one : (1 : ℝ≥0∞) ≤
        ENNReal.ofReal (Hamiltonian.gammaBar hpow.α hpow.β) := by
      simpa [Hamiltonian.gammaBar] using
        (inferInstance :
          Fact (1 ≤ ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))).out
    exact sol.huLp.toMemLp.integrable hγ_ge_one
  hMUH_int :=
    paperSolFor_hMUH_int_of_paperHypotheses
      (d := d) V H DpH hpow hV hHat0 hAgree k sol
  hRHS_int :=
    paperSolFor_hRHS_int_of_paperHypotheses
      (d := d) V H DpH hpow hV hHat0 hAgree k sol cBundle

/-! ### Phase 4 alias — closed `PaperSolForSideInputs.of_paperHypotheses`
(`paperSolFor-final`, iter post-0626, Phase 4 partial)

Closed alias for the 9-field side-input constructor. All nine fields are
discharged in-body of `of_paperHypotheses_partial` (iters 0622–0626); the
present alias preserves the public name `of_paperHypotheses` for downstream
callers (notably the Phase 5 `PaperSolForK.of_paperHypotheses` aggregator
filed as a follow-up task).

The alias forwards every argument of `_partial` byte-for-byte. The
`hmon`/`hHat0`/`hAgree` paper inputs are **not** consumed by the in-body
discharges (the closed producers thread them only via `hpow`-derived
constants and `hV`-derived Lp data), so they are not present in this
alias's signature; downstream Phase 5 callers may pass them explicitly to
the eventual `PaperSolForK.of_paperHypotheses` constructor.

**Caveat on Phase 4 closure.** Per the `paperSolFor-final` task spec, the
ultimate Phase 4 closed form takes only the eight paper hypotheses
`(hmon, hpow, hV, hHat0, hAgree, k, sol, cBundle)`. After the Pass A
discharge of `hRegH` (iter post-0627, child task
`paperSolFor-final-phase4-derive-auxiliaries`) and the iter-post-0627
discharge of `hV_meas` (child task `paperSolFor-final-phase4-aux-hV-meas`,
which routes through a measurable representative of `V` derived from
`hV`), the alias still threads the six auxiliary inputs
`(hDpH_cont, hmeas_pos, hmeas_neg, hI_A_pos, hI_B_pos, hI_A_neg,
hI_B_neg)` consumed by the operator-continuity and transport-VI
producers, because their derivation from `(hmon, hpow, hV, hHat0,
hAgree)` alone is non-trivial analytic content (filed as per-input
children `paperSolFor-final-phase4-aux-*`). Once those children land,
the remaining auxiliary arguments will be dropped from this alias's
signature and the task spec's ideal Phase 4 shape will be realised. -/

noncomputable def PaperSolForSideInputs.of_paperHypotheses
    {d : ℕ}
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (k : ℕ)
    [Fact (1 ≤ ENNReal.ofReal (hpow.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))]
    (sol : StationaryMFG.Theorems.SimplePower.Banach.RegularizedBareSolution
              d (paperEpsSeq k) V H DpH
              (Hamiltonian.gammaBar hpow.α hpow.β)
              (hpow.β + 1)
              (Hamiltonian.betaBar' hpow.β)
              (Hamiltonian.gammaBar' hpow.α hpow.β))
    (hV : Periodic.MemLpPer (d := d)
            (ENNReal.ofReal (Hamiltonian.betaBar' hpow.β)) V)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    (cBundle : PaperCBundleForK V H DpH hpow k)
    -- Iter post-0631 (paperSolFor-final-phase4-aux-hI-A, 2026-05-17):
    -- `hI_A_pos` / `hI_A_neg` dropped — derived in-body via
    -- `Banach.strongTransport_hI_A_of_sol`.
    -- Iter post-0635 (paperSolFor-final-phase4-aux-hI-B, 2026-05-17):
    -- `hI_B_pos` / `hI_B_neg` dropped — derived in-body via
    -- `Banach.strongTransport_hI_B_of_sol` (ε-scaling variant).
    :
    PaperSolForSideInputs (d := d) V H DpH hpow k sol :=
  -- Phase 4, Pass A (iter post-0627, child of
  -- `paperSolFor-final-phase4-derive-auxiliaries`): the `hRegH` field
  -- of the partial constructor is derived in-body via the parent
  -- projection on `HypothesisPowerGrowth` (which `extends RegularityH`).
  -- Iter post-0627 (child `paperSolFor-final-phase4-aux-hV-meas`): the
  -- `hV_meas` field is now derived internally inside
  -- `paperSolFor_hCont_signed_of_paperHypotheses`.
  -- Iter post-0627 (child `paperSolFor-final-phase4-aux-hmeas-pos-neg`):
  -- the `hmeas_pos` / `hmeas_neg` slots are now derived in-body from
  -- `hpow.toRegularityH.measurable_DpH` and the per-component
  -- `MemLpPer.aestronglyMeasurable` carried by `sol`, via
  -- `strongTransportPerturbedIntegrand_div_aestronglyMeasurable`.
  -- This shrinks the alias signature from 15 → 13 arguments. The
  -- remaining four auxiliary inputs (`hDpH_cont`, `hI_A_pos`,
  -- `hI_B_pos`, `hI_A_neg`, `hI_B_neg`) are not paper-derivable from
  -- `(hpow, hV, hHat0, hAgree)` alone in this iteration; see the
  -- per-input child tasks `paperSolFor-final-phase4-aux-*` for the
  -- residual derivations.
  let hmeas_pos :
      ∀ n : ℕ,
        AEStronglyMeasurable
          (fun x =>
            StationaryMFG.Theorems.SimplePower.Banach.strongTransportPerturbedIntegrand
              sol (1 / ((n : ℝ) + 1)) x / (1 / ((n : ℝ) + 1)))
          (MeasureTheory.volume.restrict (Periodic.UnitCube d)) :=
    fun n =>
      Banach.strongTransportPerturbedIntegrand_div_aestronglyMeasurable
        (sol := sol) hpow.toRegularityH.measurable_DpH
        (1 / ((n : ℝ) + 1))
  let hmeas_neg :
      ∀ n : ℕ,
        AEStronglyMeasurable
          (fun x =>
            StationaryMFG.Theorems.SimplePower.Banach.strongTransportPerturbedIntegrand
              sol (-(1 / ((n : ℝ) + 1))) x / (-(1 / ((n : ℝ) + 1))))
          (MeasureTheory.volume.restrict (Periodic.UnitCube d)) :=
    fun n =>
      Banach.strongTransportPerturbedIntegrand_div_aestronglyMeasurable
        (sol := sol) hpow.toRegularityH.measurable_DpH
        (-(1 / ((n : ℝ) + 1)))
  PaperSolForSideInputs.of_paperHypotheses_partial
    (d := d) V H DpH hpow k sol hV hHat0 hAgree cBundle
    hpow.toRegularityH hmeas_pos hmeas_neg

/-! ### Phase 5 partial aggregator — `PaperSolForK.of_paperHypotheses_partial`
(`paperSolFor-final-phase5-aggregator`, iter post-0628)

Partial aggregator that produces a `PaperSolForK V H DpH hpow k`
from:

* the paper hypotheses `(hmon, hpow, hV, hHat0, hAgree)` together
  with the regularity rider `hRegH`,
* the analytic-residue bundle `hAnalytic : PaperSection8AnalyticResiduesMin`
  (stored verbatim in the `hAnalytic` field of `PaperSolForK`),
* the 5 per-query Minty residue / continuity suppliers consumed by
  `paperSection8_hMinty_{set, signed, transport,
  signed_user_probe, signed_user_triple}_of_paperHypotheses`, and
* 7 `∀ sol, …`-quantified per-`sol` auxiliary inputs consumed by
  `PaperSolForSideInputs.of_paperHypotheses` (`hV_meas`, `hDpH_cont`,
  `hmeas_pos`, `hmeas_neg`, `hI_A_pos`, `hI_B_pos`, `hI_A_neg`,
  `hI_B_neg`) together with the per-`sol` C-class authorisation
  bundle `cBundleOf`.

This concentrates *all* remaining authorisation slots in a single
public surface, unblocking Phase 6 to consume the partial form
directly. The Phase-5 closure follow-up
`paperSolFor-final-phase5-aggregator-closed` drops these auxiliaries
once the in-flight `paperSolFor-final-phase4-aux-*` children land
their closed producers.

The 5 Minty fields are discharged by direct application of the
matching `paperSection8_hMinty_*_of_paperHypotheses` producer. The
9 per-`sol` side-input fields are discharged by opening with
`intro sol` and projecting the relevant field from
`PaperSolForSideInputs.of_paperHypotheses V H DpH hpow k sol hV
hHat0 hAgree (cBundleOf sol) (hV_meas sol) …`. The finiteness
rider `hFin` consumed inside the Minty producers is derived in-body
via `Hamiltonian.Hext_finite_at_zero_of_powerGrowth hpow hHat0`. -/

/-- **Partial aggregator** (`paperSolFor-final-phase5-aggregator`,
iter post-0628).

Produces a `PaperSolForK V H DpH hpow k` from the paper hypotheses
`(hmon, hpow, hV, hHat0, hAgree, hRegH)`, the analytic-residue
bundle `hAnalytic`, the 5 per-query Minty suppliers, and the 7
∀-`sol`-quantified per-`sol` auxiliary inputs (plus the per-`sol`
C-class bundle supplier). See the module docstring above for the
closure roadmap. -/
noncomputable def PaperSolForK.of_paperHypotheses_partial
    {d : ℕ}
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hmon : Hamiltonian.HypothesisMonotone (d := d) H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (hV : Periodic.MemLpPer (d := d)
            (ENNReal.ofReal (Hamiltonian.betaBar' hpow.β)) V)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    (hRegH : Hamiltonian.RegularityH (d := d) H DpH)
    (k : ℕ)
    [Fact (1 ≤ ENNReal.ofReal (hpow.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))]
    (hAnalytic :
      StationaryMFG.Theorems.SimplePower.Banach.PaperSection8AnalyticResiduesMin
        (d := d)
        (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
        (βBarReal := hpow.β + 1)
        (βBarReal' := (hpow.β + 1) / hpow.β)
        (γBarReal' := (hpow.α * (hpow.β + 1) / hpow.β)
                        / (hpow.α * (hpow.β + 1) / hpow.β - 1))
        (paperEpsSeq k) V H DpH hpow)
    -- Per-query residue / continuity suppliers (one per Minty family).
    (residueOf_set :
      ∀ (q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
                (hpow.β + 1)
                (hpow.α * (hpow.β + 1) / hpow.β)),
        q ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi d
              (hpow.β + 1)
              (hpow.α * (hpow.β + 1) / hpow.β) →
        ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        ∀ (ρ υ : (Fin d → ℝ) → ℝ)
          (Dυ : Fin d → (Fin d → ℝ) → ℝ),
          (∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
              0 ≤ ρ x) →
          Periodic.MemLpPer (d := d)
            (ENNReal.ofReal (hpow.β + 1)) (S.indicator ρ) →
          Periodic.MemSobolevPer (d := d)
            (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) υ →
          (∀ i, Periodic.MemLpPer (d := d)
                  (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))
                  (Dυ i)) →
            StationaryMFG.Theorems.SimplePower.Banach.SetTendstoResidueOf
              (d := d) (V := V) (H := H) (DpH := DpH)
              (βBarReal := hpow.β + 1)
              (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
              hpow q S ρ υ Dυ)
    (residueOf_signed :
      ∀ (q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
                (hpow.β + 1)
                (hpow.α * (hpow.β + 1) / hpow.β)),
        q ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi d
              (hpow.β + 1)
              (hpow.α * (hpow.β + 1) / hpow.β) →
        ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
        ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
          (MeasureTheory.volume.restrict (Periodic.UnitCube d)) S < ⊤ →
            StationaryMFG.Theorems.SimplePower.Banach.SignedTendstoResidueOf
              (d := d) (V := V) (H := H) (DpH := DpH)
              (βBarReal := hpow.β + 1)
              (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
              hpow q σ S)
    (residueOf_transport :
      ∀ (q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
                (hpow.β + 1)
                (hpow.α * (hpow.β + 1) / hpow.β)),
        q ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi d
              (hpow.β + 1)
              (hpow.α * (hpow.β + 1) / hpow.β) →
        ∀ (σ υ : (Fin d → ℝ) → ℝ)
          (φ : Fin d → (Fin d → ℝ) → ℝ),
          (∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
              0 ≤ σ x) →
          Periodic.MemLpPer (d := d)
            (ENNReal.ofReal (hpow.β + 1)) σ →
          Periodic.MemSobolevPer (d := d)
            (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) υ →
          (∀ i, Periodic.MemLpPer (d := d)
                  (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))
                  (φ i)) →
            StationaryMFG.Theorems.SimplePower.Banach.TransportTendstoResidueOf
              (d := d) (V := V) (H := H) (DpH := DpH)
              (βBarReal := hpow.β + 1)
              (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
              hpow q σ υ φ)
    (hSignedUserProbeCont :
      ∀ (q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
                (hpow.β + 1)
                (hpow.α * (hpow.β + 1) / hpow.β)),
        q ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi d
              (hpow.β + 1)
              (hpow.α * (hpow.β + 1) / hpow.β) →
        ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
        ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
          (MeasureTheory.volume.restrict (Periodic.UnitCube d)) S < ⊤ →
        ∀ (υ : (Fin d → ℝ) → ℝ)
          (Dυ : Fin d → (Fin d → ℝ) → ℝ),
          Periodic.MemSobolevPer (d := d)
            (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) υ →
          (∀ i, Periodic.MemLpPer (d := d)
                  (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) (Dυ i)) →
            Filter.Tendsto
              (fun n : ℕ =>
                mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                  (hpow.α * (hpow.β + 1) / hpow.β) (paperEpsSeq k)
                  Dυ
                  (fun x =>
                    StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
                      σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                      + 1 / ((n : ℝ) + 1))
                  υ
                  (fun i x => Dυ i x -
                    StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
                  (fun x =>
                    (StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
                      σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                      + 1 / ((n : ℝ) + 1)) -
                    StationaryMFG.Theorems.SimplePower.Banach.mOf q x)
                  (fun x => υ x -
                    StationaryMFG.Theorems.SimplePower.Banach.uOf q x))
              Filter.atTop
              (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                    (hpow.α * (hpow.β + 1) / hpow.β) (paperEpsSeq k)
                    Dυ
                    (fun x =>
                      StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
                        σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                    υ
                    (fun i x => Dυ i x -
                      StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
                    (fun x =>
                      σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                    (fun x => υ x -
                      StationaryMFG.Theorems.SimplePower.Banach.uOf q x))))
    (hSignedUserTripleCont :
      ∀ (q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
                (hpow.β + 1)
                (hpow.α * (hpow.β + 1) / hpow.β)),
        q ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi d
              (hpow.β + 1)
              (hpow.α * (hpow.β + 1) / hpow.β) →
        ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
        ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
          (MeasureTheory.volume.restrict (Periodic.UnitCube d)) S < ⊤ →
        ∀ (μ υ : (Fin d → ℝ) → ℝ)
          (Dυ : Fin d → (Fin d → ℝ) → ℝ),
          (∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
              0 ≤ μ x) →
          Periodic.MemLpPer (d := d)
            (ENNReal.ofReal (hpow.β + 1)) μ →
          Periodic.MemSobolevPer (d := d)
            (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) υ →
          (∀ i, Periodic.MemLpPer (d := d)
                  (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) (Dυ i)) →
            Filter.Tendsto
              (fun n : ℕ =>
                mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                  (hpow.α * (hpow.β + 1) / hpow.β) (paperEpsSeq k)
                  Dυ
                  (fun x =>
                    μ x + σ * μ x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                      + 1 / ((n : ℝ) + 1))
                  υ
                  (fun i x => Dυ i x -
                    StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
                  (fun x =>
                    (μ x + σ * μ x *
                        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                      + 1 / ((n : ℝ) + 1)) -
                    StationaryMFG.Theorems.SimplePower.Banach.mOf q x)
                  (fun x => υ x -
                    StationaryMFG.Theorems.SimplePower.Banach.uOf q x))
              Filter.atTop
              (𝓝 (mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                    (hpow.α * (hpow.β + 1) / hpow.β) (paperEpsSeq k)
                    Dυ
                    (fun x =>
                      μ x + σ * μ x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
                    υ
                    (fun i x => Dυ i x -
                      StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
                    (fun x =>
                      (μ x + σ * μ x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) -
                      StationaryMFG.Theorems.SimplePower.Banach.mOf q x)
                    (fun x => υ x -
                      StationaryMFG.Theorems.SimplePower.Banach.uOf q x))))
    -- Per-`sol` C-class authorisation bundle supplier.
    (cBundleOf :
      ∀ (sol : StationaryMFG.Theorems.SimplePower.Banach.RegularizedBareSolution
                d (paperEpsSeq k) V H DpH
                (hpow.α * (hpow.β + 1) / hpow.β)
                (hpow.β + 1)
                ((hpow.β + 1) / hpow.β)
                ((hpow.α * (hpow.β + 1) / hpow.β)
                  / (hpow.α * (hpow.β + 1) / hpow.β - 1))),
        PaperCBundleForK V H DpH hpow k)
    -- Per-`sol` auxiliary inputs consumed by
    -- `PaperSolForSideInputs.of_paperHypotheses` (filed as
    -- `paperSolFor-final-phase4-aux-*` follow-ups). The `hV_meas`
    -- slot was dropped in iter post-0627 (child task
    -- `paperSolFor-final-phase4-aux-hV-meas`); the side-input
    -- constructor now derives a measurable representative of `V`
    -- internally from `hV`. The `hDpH_cont` slot was dropped in iter
    -- post-0631 (child task `paperSolFor-final-phase4-aux-hDpH-cont`,
    -- 2026-05-17 re-scoping): the side-input constructor now derives
    -- the a.e.-pointwise Tendsto of the perturbed transport quotient
    -- inline from `hpow + sol.hmNonneg` via
    -- `strongTransportPerturbedIntegrand_pointwise_tendsto_of_powerGrowth`.
    -- The `hmeas_pos` / `hmeas_neg` ∀-`sol`-quantified per-`n`
    -- AE-strong-measurability slots were dropped in iter post-0627
    -- (child task `paperSolFor-final-phase4-aux-hmeas-pos-neg`);
    -- both are now derived inside `PaperSolForSideInputs.of_paperHypotheses`
    -- via `strongTransportPerturbedIntegrand_div_aestronglyMeasurable`
    -- from `hpow.toRegularityH.measurable_DpH` and the per-component
    -- `MemLpPer.aestronglyMeasurable` carried by `sol`.
    -- Iter post-0631 (paperSolFor-final-phase4-aux-hI-A, 2026-05-17):
    -- `hI_A_pos` / `hI_A_neg` ∀-`sol` slots dropped — derived in-body
    -- inside `PaperSolForSideInputs.of_paperHypotheses` via
    -- `Banach.strongTransport_hI_A_of_sol`.
    -- Iter post-0635 (paperSolFor-final-phase4-aux-hI-B, 2026-05-17):
    -- `hI_B_pos` / `hI_B_neg` ∀-`sol` slots dropped likewise — derived
    -- in-body via `Banach.strongTransport_hI_B_of_sol` (ε-scaling).
    :
    PaperSolForK V H DpH hpow k :=
  -- Derive the finiteness rider for `Hext` from `hpow + hHat0` (Phase 8c).
  let hFin : Hamiltonian.Hext_finite_at_zero (d := d) H :=
    Hamiltonian.Hext_finite_at_zero_of_powerGrowth hpow hHat0
  -- Local helper: per-`sol` `PaperSolForSideInputs` bundle.
  let sideOf :
      ∀ (sol : StationaryMFG.Theorems.SimplePower.Banach.RegularizedBareSolution
                d (paperEpsSeq k) V H DpH
                (hpow.α * (hpow.β + 1) / hpow.β)
                (hpow.β + 1)
                ((hpow.β + 1) / hpow.β)
                ((hpow.α * (hpow.β + 1) / hpow.β)
                  / (hpow.α * (hpow.β + 1) / hpow.β - 1))),
        PaperSolForSideInputs (d := d) V H DpH hpow k sol :=
    fun sol =>
      PaperSolForSideInputs.of_paperHypotheses
        (d := d) V H DpH hpow k sol hV hHat0 hAgree (cBundleOf sol)
  { hAnalytic := hAnalytic
    hMinty_set :=
      paperSection8_hMinty_set_W_of_paperHypotheses
        (d := d) V H DpH hpow hRegH hHat0 hFin hAgree k residueOf_set
    hMinty_signed :=
      paperSection8_hMinty_signed_W_of_paperHypotheses
        (d := d) V H DpH hpow hRegH hHat0 hFin hAgree k residueOf_signed
    hMinty_transport :=
      paperSection8_hMinty_transport_W_of_paperHypotheses
        (d := d) V H DpH hpow hRegH hHat0 hFin hAgree k residueOf_transport
    hMinty_signed_user_probe :=
      paperSection8_hMinty_signed_user_probe_W_of_paperHypotheses
        (d := d) V H DpH hpow hRegH hHat0 hFin hAgree k hSignedUserProbeCont
    hMinty_signed_user_triple :=
      paperSection8_hMinty_signed_user_triple_W_of_paperHypotheses
        (d := d) V H DpH hpow hRegH hHat0 hFin hAgree k hSignedUserTripleCont
    hRhoMemLp := fun sol => (sideOf sol).hRhoMemLp
    hSigmaMIndicMemLp := fun sol => (sideOf sol).hSigmaMIndicMemLp
    hCont_signed := fun sol => (sideOf sol).hCont_signed
    hResM := fun sol => (sideOf sol).hResM
    hVI_pos := fun sol => (sideOf sol).hVI_pos
    hVI_neg := fun sol => (sideOf sol).hVI_neg
    hu_int := fun sol => (sideOf sol).hu_int
    hMUH_int := fun sol => (sideOf sol).hMUH_int
    hRHS_int := fun sol => (sideOf sol).hRHS_int }

/-! ### Phase 5 closed aggregator — `PaperSolForK.of_paperHypotheses`
(`paperSolFor-final-phase6-drain`, iter 0714)

Closed alias for the partial aggregator above: produces a
`PaperSolForK V H DpH hpow k` purely from paper hypotheses
`(hmon, hpow, hV, hHat0, hAgree)` plus the dimension positivity
typeclass `[Fact (0 < d)]` (paper Theorem 1 assumes `d ≥ 1`).

All 9 per-input slots of `_partial` are discharged by the in-tree
closed producers landed iters 0668–0713:

* `hAnalytic` — `PaperSection8AnalyticResiduesMin.of_paperHypotheses`
  (Coercivity/Integrability.lean:2649, iter 0708 step4 drop of
  `hWeakDeriv`).
* `residueOf_set` — `setTendstoResidueOf_of_paperHypotheses`
  (BanachBridge.lean:6493, iter 0713 retype of `SetTendstoResidueOf.hρ`
  to `AEStronglyMeasurable (S.indicator ρ)`).
* `residueOf_signed` — `signedTendstoResidueOf_of_paperHypotheses`
  (BanachBridge.lean:7001, iter 0710 drop of `Measurable V`).
* `residueOf_transport` — `transportTendstoResidueOf_of_paperHypotheses`
  (BanachBridge.lean:6776).
* `hSignedUserProbeCont` —
  `signedUserProbeCont_of_paperHypotheses_of_aestronglyMeasurable`
  (BanachBridge.lean:7422, iter 0710 AE wrapper).
* `hSignedUserTripleCont` —
  `signedUserTripleCont_of_paperHypotheses_of_aestronglyMeasurable`
  (BanachBridge.lean:8116, iter 0710 AE wrapper).
* `cBundleOf` — `PaperCBundleForK.of_paperHypotheses`
  (BanachBridge.lean:10229).

The `hRegH` rider is derived from `hpow.toRegularityH` (parent
projection on `HypothesisPowerGrowth`, which extends `RegularityH`),
per the user's iter-0714 directive ("use `hpow.toRegularityH`, NOT a
new `hRegH` parameter").

The finiteness rider `hFin` consumed by the four W-form Minty
producers requiring it (signed, signed-user-probe, signed-user-triple,
transport) is derived in-body via
`Hamiltonian.Hext_finite_at_zero_of_powerGrowth hpow hHat0` (Phase
8c). -/

/-- **Closed aggregator** (`paperSolFor-final-phase6-drain`, iter
0714).

Produces a `PaperSolForK V H DpH hpow k` from the paper hypotheses
`(hmon, hpow, hV, hHat0, hAgree)` and `[Fact (0 < d)]`. Body is a
thin forwarder over `_partial`, with all 9 per-input slots filled by
their respective closed producers. -/
noncomputable def PaperSolForK.of_paperHypotheses
    {d : ℕ}
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hmon : Hamiltonian.HypothesisMonotone (d := d) H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (hV : Periodic.MemLpPer (d := d)
            (ENNReal.ofReal (Hamiltonian.betaBar' hpow.β)) V)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    (k : ℕ)
    [Fact (0 < d)]
    [Fact (1 ≤ ENNReal.ofReal (hpow.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))] :
    PaperSolForK V H DpH hpow k :=
  -- Derive the regularity and finiteness riders from paper hypotheses.
  let hRegH : Hamiltonian.RegularityH (d := d) H DpH := hpow.toRegularityH
  let hFin : Hamiltonian.Hext_finite_at_zero (d := d) H :=
    Hamiltonian.Hext_finite_at_zero_of_powerGrowth hpow hHat0
  -- `hV` is stored at `Hamiltonian.betaBar' hpow.β = (hpow.β + 1) / hpow.β`
  -- by `Hamiltonian.betaBar'` definitional unfold; this is the shape
  -- consumed by the closed producers.
  have hV' : Periodic.MemLpPer (d := d)
              (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) V := hV
  PaperSolForK.of_paperHypotheses_partial
    (d := d) V H DpH hmon hpow hV hHat0 hAgree hRegH k
    (hAnalytic :=
      StationaryMFG.Theorems.SimplePower.Banach.PaperSection8AnalyticResiduesMin.of_paperHypotheses
        (d := d) (ε := paperEpsSeq k) (paperEpsSeq_pos k)
        hmon hpow hHat0 hAgree hV')
    (residueOf_set := fun q _hq S hS ρ υ Dυ hρ_nn hSρ_memLp hυ_memSob hDυ_memLp =>
      setTendstoResidueOf_of_paperHypotheses
        (V := V) (H := H) (DpH := DpH)
        hpow q S hS ρ υ Dυ
        hυ_memSob.1.aestronglyMeasurable
        (fun i => (hDυ_memLp i).aestronglyMeasurable)
        hSρ_memLp hυ_memSob.1 hDυ_memLp hV' hρ_nn)
    (residueOf_signed := fun q hq σ hσ S hS _hSfin =>
      signedTendstoResidueOf_of_paperHypotheses
        (V := V) (H := H) (DpH := DpH)
        hpow q σ hσ S hS hV'
        (StationaryMFG.Theorems.SimplePower.Banach.mem_K0_Aepsi_iff.mp hq))
    (residueOf_transport := fun q _hq σ υ φ hσ_nn hσ_memLp hυ_memSob hφ_memLp =>
      transportTendstoResidueOf_of_paperHypotheses
        (V := V) (H := H) (DpH := DpH)
        hpow q σ υ φ
        hσ_memLp.aestronglyMeasurable
        hυ_memSob.1.aestronglyMeasurable
        (fun i => (hφ_memLp i).aestronglyMeasurable)
        hσ_memLp hυ_memSob.1 hφ_memLp hV' hσ_nn)
    (hSignedUserProbeCont := fun q hq σ hσ S hS _hSfin υ Dυ hυ_memSob hDυ_memLp =>
      signedUserProbeCont_of_paperHypotheses_of_aestronglyMeasurable
        (V := V) (H := H) (DpH := DpH)
        hpow hRegH hHat0 hFin hAgree (ε := paperEpsSeq k)
        q hq σ hσ S hS υ Dυ hυ_memSob.1 hDυ_memLp hV')
    (hSignedUserTripleCont := fun q hq σ hσ S hS _hSfin μ υ Dυ hμ_nn hμ_memLp hυ_memSob hDυ_memLp =>
      signedUserTripleCont_of_paperHypotheses_of_aestronglyMeasurable
        (V := V) (H := H) (DpH := DpH)
        hpow hRegH hHat0 hFin hAgree (ε := paperEpsSeq k)
        q hq σ hσ S hS μ υ Dυ hμ_nn hμ_memLp hυ_memSob.1 hDυ_memLp hV')
    (cBundleOf := fun _sol => PaperCBundleForK.of_paperHypotheses V H DpH hpow hV k)

/-! ### Phase 6 — closed `T10PaperResidues.of_paperHypotheses`
(`paperSolFor-final-phase6-drain`, iter 0714)

Relocated from its pre-0714 position (line ~10420) to after the
closed `PaperSolForK.of_paperHypotheses` aggregator (defined just
above), so that the in-body `let paperSolFor` binding can invoke
the closed alias. The body content is otherwise unchanged from
the pre-0714 form except for the iter-0714 `paperSolFor` drain. -/

/-- **Diagnostic constructor (D0 stub) for `T10PaperResidues`.**

Argument list is exactly the paper-faithful signature
`(V, H, DpH, hmon, hpow, hV, hHat0, hAgree, hHextCont)` — i.e., what
`thm_main_simplePowerGrowth_paper` should ultimately take *minus* the
`residues` parameter. The body is a `refine` against the
`T10PaperResidues` constructor with one `?`-named placeholder per
field, each closed by `sorry`. This is the single sanctioned
introduction of `sorry` in the project (per task
`infra-P5-T10-of-paperHypotheses-diagnostic-stub`); each placeholder
will be discharged in turn by Phases D1–D6 of the Theorem-1 closure
plan, after which this constructor will be sorry-free and replace the
explicit `residues` parameter in `thm_main_simplePowerGrowth_paper`.

**Explicit boundary joint-continuity rider** (iter
`infra-P5-T10-v8-K0-Hext-rider-thread-through-T10`, 2026-05-21): the
producer carries one additional paper-side hypothesis,
`hHextCont : HypothesisHextJointCont H`, parallel to `hHat0` and
`hAgree`. The rider formalizes the joint continuity of `(p, m) ↦
H(x, p, m)` on the closed half-plane `{m ≥ 0}` that the paper uses
implicitly at line 1038 of `Source/FGU-monotone_revised.tex` to read
off the boundary value of `H` from its right-hand limit `Hext`. The
rider is consumed downstream by the v8 K0 regularity producer (step
6+ of the 2026-05-21 plan); it is **not** an authorisation parameter
on `T10PaperResidues` (auth count stays at 3).

**Placeholder → phase map.**

* `epsSeq`, `epsSeq_pos`, `epsSeq_tendsto`, `Vbound`, `Vint_bound`,
  `Vβp_bound`, `hVint_nn`, `hVβp_nn` — Phase **D2** (cheap scalar
  layer).
* `paperSol`, `cBundles`, `epsTerms_align` — Phase **D4** (paperSol
  per-`k` regularised solution + alignment).
* iter `infra-P5-T10-drop-hu_measRaw-hDu_measRaw-final`: Phase **D3**
  (measurability cascade) is empty — `hu_measRaw`/`hDu_measRaw` have
  been removed from `T10PaperResidues`.
* `mintyResSetOf`, `mintyResSignedOf`, `mintyResTransportOf` — Phase
  **D6** (Minty residues).
* `hμ_posOf` — Phase **D5** (strict positivity).
* `h_weak_mOf`, `h_weak_uOf`, `h_weak_DuOf` — Phase **D1**
  (weak-pairings audit).
-/
noncomputable def T10PaperResidues.of_paperHypotheses
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hmon : HypothesisMonotone H DpH)
    (hpow : HypothesisPowerGrowth H DpH)
    (hV : Periodic.MemLpPer
            (ENNReal.ofReal (Hamiltonian.betaBar' hpow.β)) V)
    (hHat0 : StationaryMFG.Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : StationaryMFG.Hamiltonian.H_zero_eq_Hext (d := d) H)
    -- **Step 5 of v8 K0 plan** (2026-05-21,
    -- `infra-P5-T10-v8-K0-Hext-rider-thread-through-T10`): explicit
    -- paper-side joint-continuity rider for the extended Hamiltonian
    -- on the closed half-plane `{m ≥ 0}`. The paper's hemicontinuity
    -- argument at line 1038 of `Source/FGU-monotone_revised.tex` uses
    -- this continuity implicitly; we make it explicit alongside
    -- `hHat0` and `hAgree`. **NOT** a B-class authorisation parameter
    -- on `T10PaperResidues` (auth count stays at 3).
    (hHextCont : StationaryMFG.Hamiltonian.HypothesisHextJointCont (d := d) H)
    -- **iter `infra-P6-K0-drop-hbeta-ge-one`** (THE CAPSTONE, 2026-05-22):
    -- the analytic side condition `1 ≤ hpow.β` parameter has been
    -- **dropped**. The three `mintyRes{Set,Signed,Transport}Of` field
    -- types are now `*FamilyNarrowMintyResidueK0Min` (iter 0796), and the
    -- three discharge sites below call the minimal-shape closed producers
    -- `*FamilyNarrowSegInputsK0_closed_min_of_paperHypotheses`
    -- (iters 0792/0793/0794), which drop the over-specified `bΔm1`
    -- dominator slot — the only consumer of `hβ_ge_one`. Theorem 1 is
    -- now paper-faithful: relies only on `hpow.hβ : 0 < hpow.β` (built
    -- into `HypothesisPowerGrowth`). Mirrors the minimal-shape
    -- consumer chain `mintyData{Set,Signed,Transport}NarrowK0Min_of_paperHypotheses`
    -- (iter 0797).
    -- Dimension positivity typeclass (paper Theorem 1 assumes `d ≥ 1`).
    -- Added iter 0714 (`paperSolFor-final-phase6-drain`) for the
    -- in-body `PaperSolForK.of_paperHypotheses` call; not a B-class
    -- authorisation (typeclass instance).
    [Fact (0 < d)]
    -- **`infra-P5-T10-v7-phase4-hmu-posAuth-drain`** (iter 0580
    -- audit). The three auth parameters
    -- `hμ_posAuth_{set,signed,transport}` (formerly here, strict
    -- positivity authorisations) have been **drained**: strict
    -- positivity `0 < μ` is impossible to derive paper-faithfully
    -- because each paper-family domain contains the unperturbed
    -- limit triple where `μ = mLim`, and the paper only gives
    -- `mLim ≥ 0`. The downstream consumers have been migrated to
    -- the `_nonneg` variants
    -- (`Hamiltonian.g_memLp_q_nonneg`,
    --  `Hamiltonian.flux_memLp_gammaBar'_nonneg`), and the three
    -- `hμ_posOf_*` fields of `T10PaperResidues` now hold the
    -- paper-faithful `0 ≤ᵐ μ` shape. Each is discharged in-body
    -- from the family-membership witness plus
    -- `wkBundle.hmRep_nonneg`. Auth count drops 9 → 6.
    -- **Phase D6 step 7 — set-family per-test-pair segment-data
    -- authorisation** (`infra-P5-T10-D6-set-residue-discharge`).
    --
    -- **iter `infra-P5-T10-v8-K0-set-final-drain-body`**
    -- (2026-05-21, step 5/5 of the v8 K0 set-drain refined plan):
    -- the `setSegInputsAuth` B-class parameter has been **drained**.
    -- The per-test-pair `SetFamilyNarrowSegInputsK0` record is now
    -- produced in-body by `setFamilyNarrowSegInputsK0_closed_of_paperHypotheses`
    -- (defined at BanachBridge.lean:7741), threading the paper
    -- hypotheses, the derived `hExp`, `hF_HJB_meas`, `hF_flux_meas`,
    -- the Hölder pair via `hpqBeta_paper`/`hpqGamma_paper`, and the
    -- paper-side rider `hβ_ge_one` (introduced above). Auth count
    -- drops 3 → 2 (`signedSegInputsAuth` + `transportSegInputsAuth`
    -- remain).
    -- **Phase D6 step 6 — signed-family per-test-pair segment-data
    -- authorisation** (`infra-P5-T10-D6-signed-residue-discharge`).
    --
    -- **iter `infra-P5-T10-v8-K0-signed-auth-drain`** (2026-05-21,
    -- step 10b of 10 of the v8 K0 plan): the `signedSegInputsAuth`
    -- B-class parameter has been **drained**. The per-test-pair
    -- `SignedFamilyNarrowSegInputsK0` record is now produced in-body by
    -- `signedFamilyNarrowSegInputsK0_closed_of_paperHypotheses`
    -- (BanachBridge.lean:9046), threading the paper hypotheses, the
    -- derived analytic riders (`hExp`, `hF_HJB_meas`, `hF_flux_meas`),
    -- the Hölder pair via `hpqBeta_paper`/`hpqGamma_paper`, the
    -- paper-side rider `hβ_ge_one`, and the signed-family-membership
    -- selectors via `Classical.choose`. Auth count drops 2 → 1
    -- (`transportSegInputsAuth` remains).
    -- **Phase D6 step 5 — transport-family per-test-pair segment-data
    -- authorisation** (`infra-P5-T10-D6-transport-residue-discharge`).
    --
    -- B-class authorised input (paper-faithful, family-scoped). Per the
    -- iter-0534 D6 audit's risk register, the per-test-pair segment-data
    -- record `TransportFamilyNarrowSegInputs` carries:
    --   * two `MFGOpEpsAuxHyps` certificates (`aux₁`/`aux₂`) at lifted
    --     Banach pairs (analytic discharge via
    --     `auxHyps_K0_at_setPaperTriple` + a.e.-coercion transport,
    --     audit-estimated ~200 LOC per pair);
    --   * nine `bΔ_*`/`bG_*` dominator certificates (each ~50–100 LOC of
    --     pointwise-power + `MemLpPer.add` analysis);
    --   * `hPosSeg` (segment strict positivity at `(mLim, mLim)`, which
    --     reduces to `0 < mLim x` since `cxComb mLim mLim t x = mLim x`,
    --     supplied by `hμ_posAuth_transport`);
    --   * test-direction regularity certificates `hη/hDν/hν_β/hν_γ`;
    --   * Carathéodory measurability certificates `hF_unreg_meas_bare`
    --     and `hF_gat_meas_bare` (already analytic via
    --     `hF_unreg_meas_bare_transport_paper` /
    --     `hF_gat_meas_bare_transport_paper`).
    --
    -- The total analytic content (~700–1000 LOC) is filed as a future
    -- per-pair discharge child task; this single authorised input
    -- packages it in the paper-faithful per-test-pair shape, mirroring
    -- the iter-0533 hypothesis-shape pattern (one parameter per family
    -- domain, scoped to the family's perturbation type and the
    -- weak-limit triple).
    -- **iter `infra-P5-T10-v8-K0-transport-auth-drain`** (2026-05-21,
    -- step 10c of 10 of the v8 K0 plan — **THE FINAL AUTH DRAIN**): the
    -- `transportSegInputsAuth` B-class parameter has been **drained**.
    -- The per-test-pair `TransportFamilyNarrowSegInputsK0` record is now
    -- produced in-body by the closed paper-faithful producer
    -- `transportFamilyNarrowSegInputsK0_closed_of_paperHypotheses`
    -- (BanachBridge.lean:10531, iter 0781), threading the paper
    -- hypotheses, the derived analytic riders (`hExp`, `hF_HJB_meas`,
    -- `hF_flux_meas`), the Hölder pair via `hpqBeta_paper` /
    -- `hpqGamma_paper`, the paper-side rider `hβ_ge_one`, the primal
    -- a.e.-nonneg `wkBundle.hmRep_nonneg`, and the two smooth-periodic
    -- perturbations `(ψ₁, ψ₂)` extracted from `D_transport_family_paper`
    -- membership via `Classical.choose`. The four test-direction
    -- regularity certs `(hη, hDν, hν_β, hν_γ)` (relocated from the
    -- record to the segInputsOf signature in
    -- `infra-P5-T10-v8-K0-transport-mintyResTransportOf-retype`) are
    -- now actively consumed by the closed producer (no longer ignored).
    -- Auth count drops 1 → 0. **Theorem 1 is now fully formalized from
    -- paper hypotheses + `hHextCont` + `hβ_ge_one` riders alone.**
    -- Mirror of the set drain (iter 0770) and signed drain (iter 0776).
    -- **Phase D1 final — Minty / hemicontinuity-upgrade limit
    -- authorisation** (`infra-P5-T10-D1-hoist-h-subseq-authorisation`;
    -- renamed under `infra-P5-T10-v7-phase6-h-minty-limit-auth` per the
    -- paper review 2026-05-11).
    --
    -- **HMinty-3 (`infra-P5-T10-v7-HMinty-3-rewire-and-drain`)** — the
    -- `h_minty_limit_auth` B-class authorisation has been **drained**.
    -- The three universal weak-pairing certificates
    -- `h_weak_{m,u,Du}Of` (formerly fields of `T10PaperResidues`, now
    -- deleted) are sourced in-body of
    -- `simplePowerThinChain_of_paperHypotheses` from the HMinty-2
    -- producer `extractedWeakPairingData_of_regularizedSequence`,
    -- which extracts a weakly converging subsequence and builds the
    -- pairings via the Route-1 bridge
    -- `weakConvPairing_universal_of_toWeakSpace_conv`. The paper's
    -- Banach–Alaoglu extraction + Minty / hemicontinuity-upgrade
    -- argument is fully discharged in-tree (cf. paper lines 832–841
    -- and `lem:strong.is.strong` paper line 1311). Auth count drops
    -- 5 → 4.
    -- **Phase D4.2 — per-`k` paper-form regularised solution data
    -- authorisation** (`infra-P5-T10-D4-2-paperSol-discharge`).
    --
    -- B-class authorised input (paper-faithful, per-`k`) packaging the
    -- per-`k` analytic + Minty + paper-side inputs needed to assemble a
    -- `RegularizedPaperSolutionData` at `ε = paperEpsSeq k` via the
    -- canonical chain
    -- `aepsiUniformContextK_of_paperHypotheses_closed_paper +
    -- exists_regularizedBareSolution_K +
    -- RegularizedPaperSolutionData.of_regularizedBareSolution`. The
    -- bundle struct `PaperSolForK` consolidates the 14 per-`k` inputs
    -- (one analytic-residue bundle, five Minty/δ-limit premises, nine
    -- paper-side inputs) into a single B-class authorised parameter,
    -- mirroring the iter-0533 `hμ_posAuth_*`,
    -- iter-0539/0540/0541 `*SegInputsAuth`, and Phase D1
    -- `h_minty_limit_auth` (formerly `h_subseq_uniqueness_auth`) patterns.
    -- **Phase D4.2 paperSolFor drain** (`paperSolFor-final-phase6-drain`,
    -- iter 0714). The B-class `paperSolFor` per-`k` parameter (formerly
    -- here) has been **drained**. The per-`k` `PaperSolForK` bundle is
    -- now constructed in-body via the closed producer
    -- `PaperSolForK.of_paperHypotheses V H DpH hmon hpow hV hHat0 hAgree k`
    -- (appended after `PaperSolForK.of_paperHypotheses_partial`), which
    -- derives each field from the paper hypotheses via the closed
    -- producers chain landed iters 0668–0713. Auth count drops 4 → 3.
    -- **Phase D4.3 — per-`k` C-class authorisation bundle**
    -- (DRAINED iter
    -- `infra-P5-T10-v7-phase2c-delta-paperCBundleFor-of-paperHypotheses`).
    --
    -- The B-class `paperCBundleFor` parameter (formerly here) has been
    -- removed. The per-`k` C-class bundle `PaperCBundleForK V H DpH
    -- hpow k` is now constructed in-body via the closed producer
    -- `PaperCBundleForK.of_paperHypotheses V H DpH hpow hV k`, which
    -- derives each field directly from the paper's existing B-class
    -- authorised inputs `(V, H, DpH, hpow, hV)`. Auth count 10 → 9.
    --
    -- The `epsTerms` field of the resulting bundle is still set
    -- definitionally to `paperEpsTerms (paperEpsSeq k) γ̄ sol`, so the
    -- canonical-`epsTerms` identification certificate `epsTerms_eq`
    -- of `CBundleD41Stub` still discharges by `rfl` (D4.1
    -- deliverable preserved).
    -- **Phase 1 sub-deliverable D4.1c-d (DRAINED iter
    -- `infra-P5-T10-v7-drain-paperHVbndAuth`)**: the transitional
    -- `paperHVbndAuth : ∀ k, ∀ᵐ x, |V x| ≤ 0` authorisation has been
    -- removed. The `AprioriUniformPerSolHypothesesC_int` C-class
    -- structure no longer carries an `hVbnd` field, since the canonical
    -- `_paperHypotheses_int` consumer's body has zero `hVbnd`
    -- references (verified iter 0563). Auth count 11 → 10.
    -- **Phase 1 sub-deliverable D4.1c-e
    -- (`infra-P5-T10-D4-1c-e-replace-hMpos-hmNonneg`):** historical
    -- breadcrumb. The transitional strict-positivity field
    -- `hMpos : 0 < sol.m` previously carried on `PaperCBundleForK k`
    -- was relocated here as a dedicated B-class authorisation
    -- parameter `paperHMposAuth`. After the 5-step HMpos drain
    -- (HMpos-0 boundary helpers, HMpos-1 base nonneg apriori,
    -- HMpos-2 integral chain siblings, HMpos-3 C_int retype to
    -- `hmNonneg`, HMpos-4 bridge and drain — this iteration), the
    -- canonical `_paperHypotheses_int` body consumes
    -- `apriori_aggregate_bound_residue_form_int_aePeriodic_nonneg`,
    -- so the strict-positivity authorisation is no longer needed.
    -- The per-`k` C-class field `hmNonneg : 0 ≤ᵐ sol.m` is now
    -- sourced directly from `(paperSolStub k).sol.hmNonneg` (a
    -- built-in field of `RegularizedBareSolution`). Auth count drops
    -- 6 → 5. Iter `infra-P5-T10-v7-HMpos-4-bridge-and-drain`.
    -- **Phase 2a iter 2 (`AEPeriodic`-typed):** the periodicity
    -- authorisation parameters `paperHuPerAuth`/`paperHDuPerAuth`
    -- previously carried here have been **eliminated**. The
    -- `RegularizedBareSolution.{hu_per, hDu_per}` fields are now
    -- typed as `Periodic.AEPeriodic` and constructed in-body inside
    -- `exists_regularizedBareSolution_K` via
    -- `Periodic.bareCoeFnOfLpPer`. No external authorisation needed.
    -- **iter `infra-P5-T10-v7-drain-paperHVbndAuth`**: drained
    -- `paperHVbndAuth` (impossible `|V| ≤ 0` content). Auth count
    -- 11 → 10 B-class authorised inputs. -/
    :
    letI : Fact (1 ≤ ENNReal.ofReal (Hamiltonian.betaBar hpow.β)) :=
      Hamiltonian.fact_one_le_ofReal_betaBar hpow.hβ
    letI : Fact (1 ≤ ENNReal.ofReal (Hamiltonian.gammaBar hpow.α hpow.β)) :=
      Hamiltonian.fact_one_le_ofReal_gammaBar hpow.hα hpow.hβ
    T10PaperResidues
      (d := d)
      (Hamiltonian.gammaBar hpow.α hpow.β)
      (Hamiltonian.betaBar hpow.β)
      (Hamiltonian.betaBar' hpow.β)
      (Hamiltonian.gammaBar' hpow.α hpow.β)
      V H DpH hpow := by
  -- Suppress `unused variable` warnings on the eight paper-hypothesis
  -- arguments while every field is still `sorry`. After the D1–D6
  -- phases land, each argument is consumed by at least one field
  -- producer and these `_` bindings are deleted.
  let _ := hmon
  let _ := hHat0
  let _ := hAgree
  -- **Step 5 of v8 K0 plan** (2026-05-21,
  -- `infra-P5-T10-v8-K0-Hext-rider-thread-through-T10`): the
  -- joint-continuity rider is threaded through the producer for
  -- downstream `RegularityHK0` construction (step 6+). No consumer in
  -- this body yet — suppress unused-variable warning.
  let _ := hHextCont
  -- Introduce the two `Fact` instances needed to elaborate
  -- `T10PaperResidues …` at the paper-canonical exponents.
  haveI : Fact (1 ≤ ENNReal.ofReal (Hamiltonian.betaBar hpow.β)) :=
    Hamiltonian.fact_one_le_ofReal_betaBar hpow.hβ
  haveI : Fact (1 ≤ ENNReal.ofReal (Hamiltonian.gammaBar hpow.α hpow.β)) :=
    Hamiltonian.fact_one_le_ofReal_gammaBar hpow.hα hpow.hβ
  -- **Phase 2c-δ drain**
  -- (`infra-P5-T10-v7-phase2c-delta-paperCBundleFor-of-paperHypotheses`):
  -- the `paperCBundleFor` B-class parameter has been removed.
  -- The per-`k` C-class bundle is now constructed in-body via the
  -- closed producer `PaperCBundleForK.of_paperHypotheses`, deriving
  -- each field directly from `(V, H, DpH, hpow, hV)`. Auth count
  -- 10 → 9.
  let paperCBundleFor : ∀ k : ℕ, PaperCBundleForK V H DpH hpow k :=
    fun k => PaperCBundleForK.of_paperHypotheses V H DpH hpow hV k
  -- D1 — Minty / hemicontinuity-upgrade limit premise: **drained**
  -- (`infra-P5-T10-v7-HMinty-3-rewire-and-drain`). The
  -- `h_minty_limit_auth` B-class parameter (formerly here) has been
  -- removed; the three universal weak-pairing certificates
  -- `h_weak_{m,u,Du}Of` (formerly fields of `T10PaperResidues`) have
  -- been deleted. The chain consumer
  -- `simplePowerThinChain_of_paperHypotheses` now sources the three
  -- universal weak-pairings directly from the in-tree HMinty-2
  -- producer `extractedWeakPairingData_of_regularizedSequence`,
  -- bypassing the residue indirection. Auth count drops 5 → 4.
  -- D4.1 — canonical-`paperEpsTerms` rewiring
  -- (`infra-P5-T10-D4-1-canonical-paperEpsTerms`). Hoist the per-`k`
  -- `RegularizedPaperSolutionData` stub once so the `cBundles k`
  -- discharge can refer to `(paperSolStub k).sol` while building its
  -- `epsTerms` field with the canonical paper formula `paperEpsTerms`.
  -- The `cBundleD41 k` stub packages the C-class record with the
  -- canonical-`epsTerms` identification certificate, so
  -- `epsTerms_align` discharges by `congrFun (cBundleD41 k).epsTerms_eq x`
  -- (no longer an `exact sorry`). The remaining two D4 sorries (the
  -- `paperSolStub` itself and the packaged `cBundleD41` per-`k` stub)
  -- are deferred to D4.2/D4.3. Net `sorry` count: 3 → 2.
  -- D4.2 — discharge the `paperSolStub` per-`k` `RegularizedPaperSolutionData`
  -- via the canonical chain
  -- `aepsiUniformContextK_of_paperHypotheses_closed_paper +
  -- exists_regularizedBareSolution_K +
  -- RegularizedPaperSolutionData.of_regularizedBareSolution`, threading
  -- the per-`k` B-class authorised inputs from `paperSolFor k`
  -- (`infra-P5-T10-D4-2-paperSol-discharge`).
  -- Add the unfolded-form `Fact` instances expected by the chain
  -- (`Hamiltonian.betaBar hpow.β = hpow.β + 1` and
  -- `Hamiltonian.gammaBar hpow.α hpow.β = hpow.α * (hpow.β + 1) / hpow.β`
  -- are definitional, but typeclass synthesis does not auto-unfold).
  haveI : Fact (1 ≤ ENNReal.ofReal (hpow.β + 1)) :=
    Hamiltonian.fact_one_le_ofReal_betaBar hpow.hβ
  haveI : Fact (1 ≤ ENNReal.ofReal
                    (hpow.α * (hpow.β + 1) / hpow.β)) :=
    Hamiltonian.fact_one_le_ofReal_gammaBar hpow.hα hpow.hβ
  -- **Phase D4.2 paperSolFor drain** (`paperSolFor-final-phase6-drain`,
  -- iter 0714): the per-`k` `PaperSolForK` bundle is now constructed
  -- in-body via the closed producer
  -- `PaperSolForK.of_paperHypotheses` (closed alias of `_partial`),
  -- which threads through the closed producers chain landed iters
  -- 0668–0713 (step3a/3b/3d/step4 + V-meas-bridge-signed-suppliers
  -- + set-ρ-meas-supplier).
  -- The closed alias `PaperSolForK.of_paperHypotheses` is defined
  -- downstream (lexically AFTER `_partial`); reference it via the
  -- fully-qualified name to bypass the lexical-order constraint on
  -- this in-body call.
  let paperSolFor : ∀ k : ℕ, PaperSolForK V H DpH hpow k :=
    fun k =>
      StationaryMFG.Theorems.SimplePower.PaperSolForK.of_paperHypotheses
        V H DpH hmon hpow hV hHat0 hAgree k
  let paperSolStub : ∀ k : ℕ,
      StationaryMFG.Theorems.SimplePower.Banach.RegularizedPaperSolutionData
        (d := d) (paperEpsSeq k) V H DpH
        (StationaryMFG.Hamiltonian.gammaBar hpow.α hpow.β)
        (hpow.β + 1) (Hamiltonian.betaBar' hpow.β)
        (Hamiltonian.gammaBar' hpow.α hpow.β) hpow := fun k =>
    -- Step 1 — build the per-`k` refined-domain `AepsiUniformContextK_W`
    -- at the paper exponents via the W-form aggregator
    -- `aepsiUniformContextK_W_of_paperHypotheses_closed_paper_min`
    -- (iter 0700, step 3a of the iter-0694 split).
    let ctx :=
      StationaryMFG.Theorems.SimplePower.Banach.aepsiUniformContextK_W_of_paperHypotheses_closed_paper_min
        (paperEpsSeq_pos k) hmon hpow hV (paperSolFor k).hAnalytic
    -- Step 2 — extract a `RegularizedBareSolution` via
    -- `exists_regularizedBareSolution_K_W` + `Classical.choice` on the
    -- `Nonempty` conclusion. The W-form consumer recovers the weak-derivative
    -- tie internally from `K0_Aepsi_W`-membership via
    -- `hasWeakDerivPer_of_mem_K0_Aepsi_W`, eliminating the legacy
    -- `hWeakDeriv` authorisation.
    let sol :=
      Classical.choice
        (StationaryMFG.Theorems.SimplePower.Banach.exists_regularizedBareSolution_K_W
          (paperEpsSeq_pos k) ctx
          ((paperSolFor k).hMinty_set ctx)
          ((paperSolFor k).hMinty_signed ctx)
          ((paperSolFor k).hMinty_transport ctx)
          ((paperSolFor k).hMinty_signed_user_probe ctx)
          ((paperSolFor k).hMinty_signed_user_triple ctx))
    -- Step 3 — enrich `sol` with the three paper-side identities via
    -- `RegularizedPaperSolutionData.of_regularizedBareSolution`.
    StationaryMFG.Theorems.SimplePower.Banach.RegularizedPaperSolutionData.of_regularizedBareSolution
      (hpow := hpow) sol
      ((paperSolFor k).hRhoMemLp sol) ((paperSolFor k).hSigmaMIndicMemLp sol)
      ((paperSolFor k).hCont_signed sol) ((paperSolFor k).hResM sol)
      ((paperSolFor k).hVI_pos sol) ((paperSolFor k).hVI_neg sol)
      ((paperSolFor k).hu_int sol) ((paperSolFor k).hMUH_int sol)
      ((paperSolFor k).hRHS_int sol)
  -- D4.3 — discharge the per-`k` `CBundleD41Stub` from the B-class
  -- authorised bundle `paperCBundleFor k`
  -- (`infra-P5-T10-D4-3-cBundleD41-discharge`). Each C-class field
  -- of `AprioriUniformPerSolHypothesesC` is sourced from the
  -- corresponding field of `paperCBundleFor k`, instantiated at the
  -- specific `(paperSolStub k).sol` extracted via `Classical.choice`
  -- inside `paperSolStub`. The `epsTerms_eq` identification closes
  -- by `rfl` since `epsTerms := paperEpsTerms …` is set
  -- definitionally to the canonical paper formula (D4.1 deliverable).
  let cBundleD41 : ∀ k : ℕ,
      CBundleD41Stub (d := d) (V := V) (H := H) (DpH := DpH) hpow
        (paperSolStub k).sol
        (paperEpsSeq k)
        (StationaryMFG.Hamiltonian.gammaBar hpow.α hpow.β) := fun k =>
    -- **Phase 1 sub-task 1c-a/-b (v7 plan, D4.1c-a/-b)**: the packaged
    -- `bundle` field is now typed against the integral V-data sibling
    -- `AprioriUniformPerSolHypothesesC_int`.
    -- **iter `infra-P5-T10-v7-drain-paperHVbndAuth`**: the transitional
    -- `Vbound`/`hVbnd` content has been dropped from the C_int structure
    -- entirely (canonical `_paperHypotheses_int` body has zero `hVbnd`
    -- references). The dedicated `paperHVbndAuth` authorisation has been
    -- drained correspondingly.
    -- **Phase 1 sub-deliverable D4.1c-e** (iter
    -- `infra-P5-T10-v7-HMpos-4-bridge-and-drain`): the transitional
    -- `hmNonneg : 0 ≤ᵐ sol.m` field is now sourced directly from
    -- `(paperSolStub k).sol.hmNonneg` — a built-in field of
    -- `RegularizedBareSolution` (see `AssemblyContext.lean:443`).
    -- The legacy `paperHMposAuth` B-class authorisation has been
    -- drained; auth count drops 6 → 5.
    { bundle :=
        { epsTerms    := paperEpsTerms (V := V) (H := H) (DpH := DpH)
                          (paperEpsSeq k)
                          (StationaryMFG.Hamiltonian.gammaBar hpow.α hpow.β)
                          (paperSolStub k).sol
          hEpsNN      := (paperCBundleFor k).hEpsNN (paperSolStub k).sol
          hEpsInt     := (paperCBundleFor k).hEpsInt (paperSolStub k).sol
          -- **HMpos-4 drain** (iter
          -- `infra-P5-T10-v7-HMpos-4-bridge-and-drain`):
          -- `AprioriUniformPerSolHypothesesC_int` carries
          -- `hmNonneg : 0 ≤ m` (HMpos-3 retype). Source this directly
          -- from `(paperSolStub k).sol.hmNonneg`; the auxiliary
          -- `paperHMposAuth` B-class authorisation is now drained.
          hmNonneg    := (paperSolStub k).sol.hmNonneg
          vData       := (paperCBundleFor k).vData
          -- **Phase 2c-δ retype**
          -- (`infra-P5-T10-v7-phase2c-delta-paperCBundleFor-of-paperHypotheses`):
          -- `PaperCBundleForK.hu_per`/`hDu_per` are now `Periodic.AEPeriodic`
          -- (matching `AprioriUniformPerSolHypothesesC_int.hu_per`/`hDu_per`
          -- after the Phase 2c-γ retype); no `AEPeriodic.ofPeriodic`
          -- wrapper needed.
          hu_per      := (paperCBundleFor k).hu_per (paperSolStub k).sol
          hDu_per     := fun i =>
                          (paperCBundleFor k).hDu_per (paperSolStub k).sol i
          hUbetap_int := (paperCBundleFor k).hUbetap_int (paperSolStub k).sol }
      epsTerms_eq := rfl }
  change T10PaperResidues (d := d)
      (Hamiltonian.gammaBar hpow.α hpow.β)
      (Hamiltonian.betaBar hpow.β)
      (Hamiltonian.betaBar' hpow.β)
      (Hamiltonian.gammaBar' hpow.α hpow.β) V H DpH hpow
  · refine
      { epsSeq           := ?epsSeq
        epsSeq_pos       := ?epsSeq_pos
        epsSeq_tendsto   := ?epsSeq_tendsto
        paperSol         := ?paperSol
        cBundles         := ?cBundles
        epsTerms_align   := ?epsTerms_align
        mintyResSetOf    := ?mintyResSetOf
        mintyResSignedOf := ?mintyResSignedOf
        mintyResTransportOf := ?mintyResTransportOf
        hμ_posOf_set        := ?hμ_posOf_set
        hμ_posOf_signed     := ?hμ_posOf_signed
        hμ_posOf_transport  := ?hμ_posOf_transport }
      -- **HMinty-3 drain** (`infra-P5-T10-v7-HMinty-3-rewire-and-drain`):
      -- the four legacy fields `h_subseq_uniqueness`, `h_weak_mOf`,
      -- `h_weak_uOf`, `h_weak_DuOf` have been removed from
      -- `T10PaperResidues`. The chain consumer
      -- `simplePowerThinChain_of_paperHypotheses` now sources the
      -- three universal weak-pairings from the HMinty-2 producer
      -- `extractedWeakPairingData_of_regularizedSequence`.
    -- D2 — cheap scalar layer (discharged via `paperEpsSeq`).
    -- **Phase 1 sub-task 1b (v7 plan)**: the V-bound triple
    -- `(Vbound, Vint_bound, Vβp_bound)` and the associated non-negativity
    -- predicates `(hVint_nn, hVβp_nn)` have been dropped from the
    -- `T10PaperResidues` surface; the corresponding `case` arms below
    -- are removed. The V-bound triple is now hardcoded to `(0, 0, 0)`
    -- in the `cBundles` field type (matching the existing
    -- `paperCBundleFor` discharge), and the unique consumer
    -- (`simplePowerThinChain_of_paperHypotheses`) passes literal `0`s.
    case epsSeq           => exact paperEpsSeq
    case epsSeq_pos       => exact paperEpsSeq_pos
    case epsSeq_tendsto   => exact paperEpsSeq_tendsto
    -- D4 — paperSol per-`k` regularised solution + alignment.
    -- After `infra-P5-T10-D4-1-canonical-paperEpsTerms`:
    -- * `paperSol` is the hoisted `paperSolStub` (single sorry).
    -- * `cBundles` is the `.bundle` projection of `cBundleD41 k` (single
    --   sorry; the packaged stub `CBundleD41Stub` also carries the
    --   canonical-`epsTerms` identification certificate).
    -- * `epsTerms_align` discharges via `congrFun (cBundleD41 k).epsTerms_eq x`,
    --   which unpacks the bundled function-level identification to the
    --   pointwise residue. No `sorry` here.
    -- Net `sorry` count: 3 → 2 (the dropped one is the former
    -- `epsTerms_align` `exact sorry`).
    case paperSol         => exact paperSolStub
    case cBundles         => exact fun k => (cBundleD41 k).bundle
    case epsTerms_align   =>
      intro k x
      exact congrFun (cBundleD41 k).epsTerms_eq x
    -- iter `infra-P5-T10-drop-hu_measRaw-hDu_measRaw-final`: D3
    -- (measurability cascade) is empty — `hu_measRaw`/`hDu_measRaw`
    -- have been removed from `T10PaperResidues`.
    -- D6 step 7 — set-family Minty residue discharge.
    -- **iter `infra-P5-T10-v8-K0-set-mintyResSetOf-retype`**:
    -- Produces the K0 sibling `SetFamilyNarrowMintyResidueK0` (the
    -- field type has been swapped above) from the paper-scalar bundle
    -- `T10PaperScalars_of_paperHypotheses` plus the K0-retyped
    -- B-class input `setSegInputsAuth` (which now returns
    -- `SetFamilyNarrowSegInputsK0`). The set residue carries an
    -- extra `ρ₁_nn` field, read directly off the
    -- `D_set_family_paper` membership witness via
    -- `(Classical.choose_spec hμ).1`. The structure has the same
    -- scalar fields as the strict-K version, but the `segInputsOf`
    -- return type is now K0; the constructor literal automatically
    -- elaborates to the K0 residue since the field's declared type
    -- on `T10PaperResidues` is `SetFamilyNarrowMintyResidueK0`.
    case mintyResSetOf =>
      intro wkBundle
      -- Shared paper-scalar bundle at the paper-canonical exponents.
      have scalars :
          T10PaperScalars (d := d) V H DpH hpow :=
        T10PaperScalars_of_paperHypotheses (d := d)
          V H DpH hpow hV hHat0 hAgree
      -- **iter `infra-P5-T10-v8-K0-set-final-drain-body`** (step 5/5,
      -- 2026-05-21): the per-test-pair K0 segment-data is now produced
      -- in-body by the closed paper-faithful producer
      -- `setFamilyNarrowSegInputsK0_closed_of_paperHypotheses`
      -- (BanachBridge.lean:7741), threading paper hypotheses, derived
      -- analytic riders, family-membership-derived perturbation certs,
      -- and per-test-pair regularity certs. The B-class
      -- `setSegInputsAuth` parameter has been removed; auth count
      -- drops 3 → 2.
      -- Derived analytic riders for the closed producer.
      let hExp :
          StationaryMFG.Theorems.SimplePower.SimplePowerExponentFacts
            (Hamiltonian.gammaBar hpow.α hpow.β)
            (ENNReal.ofReal (Hamiltonian.betaBar hpow.β))
            (ENNReal.ofReal (Hamiltonian.gammaBar hpow.α hpow.β))
            (ENNReal.ofReal (Hamiltonian.betaBar' hpow.β)) :=
        StationaryMFG.Theorems.SimplePower.SimplePowerExponentFacts.ofPowerGrowth hpow
      have hF_HJB_meas :=
        StationaryMFG.Theorems.SimplePower.Banach.paperSection8_hF_HJB_meas_of_powerGrowth
          (d := d) (βBarReal := Hamiltonian.betaBar hpow.β)
          (γBarReal := Hamiltonian.gammaBar hpow.α hpow.β)
          (βBarReal' := Hamiltonian.betaBar' hpow.β)
          (γBarReal' := Hamiltonian.gammaBar' hpow.α hpow.β)
          (V := V) (H := H) (DpH := DpH) hpow hV
      have hF_flux_meas :=
        StationaryMFG.Theorems.SimplePower.Banach.paperSection8_hF_flux_meas_of_powerGrowth
          (d := d) (βBarReal := Hamiltonian.betaBar hpow.β)
          (γBarReal := Hamiltonian.gammaBar hpow.α hpow.β)
          (βBarReal' := Hamiltonian.betaBar' hpow.β)
          (γBarReal' := Hamiltonian.gammaBar' hpow.α hpow.β)
          (V := V) (H := H) (DpH := DpH) hpow
      have hβ_holder :
          (Hamiltonian.betaBar hpow.β).HolderConjugate
            (Hamiltonian.betaBar' hpow.β) :=
        StationaryMFG.Theorems.SimplePower.Banach.hpqBeta_paper
          (d := d) hpow
      have hγ_holder :
          (Hamiltonian.gammaBar hpow.α hpow.β).HolderConjugate
            (Hamiltonian.gammaBar' hpow.α hpow.β) :=
        StationaryMFG.Theorems.SimplePower.Banach.hpqGamma_paper
          (d := d) hpow
      have hβTop :
          ENNReal.ofReal (Hamiltonian.gammaBar hpow.α hpow.β) ≠ ⊤ :=
        ENNReal.ofReal_ne_top
      have hγ'_le_β :
          ENNReal.ofReal (Hamiltonian.gammaBar' hpow.α hpow.β)
            ≤ ENNReal.ofReal (Hamiltonian.betaBar hpow.β) := by
        refine ENNReal.ofReal_le_ofReal ?_
        -- `gammaBar' α β ≤ betaBar β` follows from
        -- `Hamiltonian.gammaBar'_le_betaBar`.
        have h := Hamiltonian.gammaBar'_le_betaBar hpow.hα hpow.hβ
        -- `Hamiltonian.gammaBar'_le_betaBar` gives
        -- `gammaBar α β / (gammaBar α β - 1) ≤ β + 1`, i.e.
        -- `gammaBar' α β ≤ betaBar β` by unfolding both sides.
        exact h
      exact
        { hHat0       := scalars.hHat0
          hAgree      := scalars.hAgree
          hβconj      := scalars.hβconj
          hγconj      := scalars.hγconj
          hγ_one_lt   := scalars.hγ_one_lt
          hγBar_eq    := scalars.hγBar_eq
          hV_conj     := scalars.hV_conj
          -- Per-test-pair K0 segment-data: now built in-body via the
          -- closed paper-faithful producer (no more `setSegInputsAuth`).
          -- The 4 test-direction certs (η, ν, Dν regularity) are threaded
          -- from the `segInputsOf` signature.
          segInputsOf := fun {_ _ _} hBar {_ _ _} hμ η ν Dν hη hDν hν_β hν_γ =>
            setFamilyNarrowSegInputsK0_closed_min_of_paperHypotheses
              (d := d)
              (γBarReal := Hamiltonian.gammaBar hpow.α hpow.β)
              (βBarReal := Hamiltonian.betaBar hpow.β)
              (βBarReal' := Hamiltonian.betaBar' hpow.β)
              (γBarReal' := Hamiltonian.gammaBar' hpow.α hpow.β)
              (γBar := Hamiltonian.gammaBar hpow.α hpow.β)
              (V := V) (H := H) (DpH := DpH)
              hmon hpow hHat0 hHextCont hAgree hV hExp
              rfl rfl rfl rfl
              hβ_holder hγ_holder hβTop hγ'_le_β
              rfl
              (mLim := wkBundle.mLim) (uLim := wkBundle.uLim)
              (DuLim := wkBundle.DuLim)
              wkBundle.hmLim_memLp wkBundle.huLim_sob
              (fun i => wkBundle.hDuLim_memLp_γ i)
              wkBundle.hmRep_nonneg
              hF_HJB_meas hF_flux_meas
              (ρ₁ := Classical.choose hμ) (ρ₂ := Classical.choose hBar)
              (Classical.choose_spec hμ).2.1
              (Classical.choose_spec hBar).2.1
              (Classical.choose_spec hμ).1
              (Classical.choose_spec hBar).1
              η ν Dν hη hDν hν_β hν_γ
          -- Pointwise nonneg of the first perturbation `ρ₁` from
          -- `D_set_family_paper` membership.
          ρ₁_nn := fun {_ _ _} _hBar {_ _ _} hμ =>
            (Classical.choose_spec hμ).1 }
    -- D6 step 6 — signed-family Minty residue discharge
    -- (`infra-P5-T10-D6-signed-residue-discharge`, iter-0534 audit
    -- step 6). Produces `SignedFamilyNarrowMintyResidue` from the
    -- paper-scalar bundle `T10PaperScalars_of_paperHypotheses`
    -- (iter 0535) plus the new authorised B-class input
    -- `signedSegInputsAuth` for the per-test-pair segment-data
    -- record. The signed residue (unlike the transport residue)
    -- carries no primal-side `hmLim_nn` field — the per-pair joint
    -- nonneg `0 ≤ᵐ mLim + g_i` is read off `D_signed_family_paper_nn`
    -- membership directly inside the per-pair segment-data producer.
    case mintyResSignedOf =>
      intro wkBundle
      -- Shared paper-scalar bundle at the paper-canonical exponents.
      have scalars :
          T10PaperScalars (d := d) V H DpH hpow :=
        T10PaperScalars_of_paperHypotheses (d := d)
          V H DpH hpow hV hHat0 hAgree
      -- **iter `infra-P5-T10-v8-K0-signed-auth-drain`** (2026-05-21,
      -- step 10b of 10): the per-test-pair K0 segment-data is now
      -- produced in-body by the closed paper-faithful producer
      -- `signedFamilyNarrowSegInputsK0_closed_of_paperHypotheses`
      -- (BanachBridge.lean:9046), threading paper hypotheses, derived
      -- analytic riders, signed family-membership-derived perturbation
      -- certs (selected via `Classical.choose` on the `_nn` narrow
      -- domain), and per-test-pair regularity certs. The B-class
      -- `signedSegInputsAuth` parameter has been removed; auth count
      -- drops 2 → 1.  Mirror of the set drain (iter 0770).
      -- Derived analytic riders for the closed producer.
      let hExp :
          StationaryMFG.Theorems.SimplePower.SimplePowerExponentFacts
            (Hamiltonian.gammaBar hpow.α hpow.β)
            (ENNReal.ofReal (Hamiltonian.betaBar hpow.β))
            (ENNReal.ofReal (Hamiltonian.gammaBar hpow.α hpow.β))
            (ENNReal.ofReal (Hamiltonian.betaBar' hpow.β)) :=
        StationaryMFG.Theorems.SimplePower.SimplePowerExponentFacts.ofPowerGrowth hpow
      have hF_HJB_meas :=
        StationaryMFG.Theorems.SimplePower.Banach.paperSection8_hF_HJB_meas_of_powerGrowth
          (d := d) (βBarReal := Hamiltonian.betaBar hpow.β)
          (γBarReal := Hamiltonian.gammaBar hpow.α hpow.β)
          (βBarReal' := Hamiltonian.betaBar' hpow.β)
          (γBarReal' := Hamiltonian.gammaBar' hpow.α hpow.β)
          (V := V) (H := H) (DpH := DpH) hpow hV
      have hF_flux_meas :=
        StationaryMFG.Theorems.SimplePower.Banach.paperSection8_hF_flux_meas_of_powerGrowth
          (d := d) (βBarReal := Hamiltonian.betaBar hpow.β)
          (γBarReal := Hamiltonian.gammaBar hpow.α hpow.β)
          (βBarReal' := Hamiltonian.betaBar' hpow.β)
          (γBarReal' := Hamiltonian.gammaBar' hpow.α hpow.β)
          (V := V) (H := H) (DpH := DpH) hpow
      have hβ_holder :
          (Hamiltonian.betaBar hpow.β).HolderConjugate
            (Hamiltonian.betaBar' hpow.β) :=
        StationaryMFG.Theorems.SimplePower.Banach.hpqBeta_paper
          (d := d) hpow
      have hγ_holder :
          (Hamiltonian.gammaBar hpow.α hpow.β).HolderConjugate
            (Hamiltonian.gammaBar' hpow.α hpow.β) :=
        StationaryMFG.Theorems.SimplePower.Banach.hpqGamma_paper
          (d := d) hpow
      have hβTop :
          ENNReal.ofReal (Hamiltonian.gammaBar hpow.α hpow.β) ≠ ⊤ :=
        ENNReal.ofReal_ne_top
      have hγ'_le_β :
          ENNReal.ofReal (Hamiltonian.gammaBar' hpow.α hpow.β)
            ≤ ENNReal.ofReal (Hamiltonian.betaBar hpow.β) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h := Hamiltonian.gammaBar'_le_betaBar hpow.hα hpow.hβ
        exact h
      exact
        { hHat0       := scalars.hHat0
          hAgree      := scalars.hAgree
          hβconj      := scalars.hβconj
          hγconj      := scalars.hγconj
          hγ_one_lt   := scalars.hγ_one_lt
          hγBar_eq    := scalars.hγBar_eq
          hV_conj     := scalars.hV_conj
          -- Per-test-pair K0 signed segment-data: now built in-body via
          -- the closed paper-faithful producer (no more
          -- `signedSegInputsAuth`). The four test-direction certs
          -- `(hη, hDν, hν_β, hν_γ)` are threaded from the `segInputsOf`
          -- signature into the closed producer.
          --
          -- Signed family membership `D_signed_family_paper_nn` unpacks
          -- as `⟨g, hg_lp, hg_per, hjoint_nn, p_eq⟩` (see
          -- `RegularizedSequence.lean:17190`). The joint nonneg comes in
          -- the `fun x => mLim x + g x` form; the closed producer
          -- expects the `(mLim + g) x` form, so we transport via
          -- `.mono` + `Pi.add_apply`. The joint `MemLpPer βBar (mLim + g_i)`
          -- is built from `wkBundle.hmLim_memLp.add hg_lp`.
          segInputsOf := fun {_ _ _} hBar {_ _ _} hμ η ν Dν hη hDν hν_β hν_γ =>
            let g₁ := Classical.choose hμ
            let g₂ := Classical.choose hBar
            let hg₁_lp := (Classical.choose_spec hμ).1
            let hg₂_lp := (Classical.choose_spec hBar).1
            let hjoint₁_nn0 := (Classical.choose_spec hμ).2.2.1
            let hjoint₂_nn0 := (Classical.choose_spec hBar).2.2.1
            -- Convert nonneg from `(fun x => mLim x + g x)` form to
            -- `(mLim + g) x` form (both reduce to the same value).
            have hjoint₁_nn :
                ∀ᵐ x ∂(MeasureTheory.Measure.restrict
                          MeasureTheory.volume (UnitCube d)),
                  0 ≤ (wkBundle.mLim + g₁) x := by
              refine hjoint₁_nn0.mono ?_
              intro x hx
              simpa [Pi.add_apply] using hx
            have hjoint₂_nn :
                ∀ᵐ x ∂(MeasureTheory.Measure.restrict
                          MeasureTheory.volume (UnitCube d)),
                  0 ≤ (wkBundle.mLim + g₂) x := by
              refine hjoint₂_nn0.mono ?_
              intro x hx
              simpa [Pi.add_apply] using hx
            -- Joint Lᵝ-membership of `mLim + g_i` (paper-faithful sum).
            have hmg₁_β : Periodic.MemLpPer (d := d)
                (ENNReal.ofReal (Hamiltonian.betaBar hpow.β))
                (wkBundle.mLim + g₁) :=
              wkBundle.hmLim_memLp.add hg₁_lp
            have hmg₂_β : Periodic.MemLpPer (d := d)
                (ENNReal.ofReal (Hamiltonian.betaBar hpow.β))
                (wkBundle.mLim + g₂) :=
              wkBundle.hmLim_memLp.add hg₂_lp
            signedFamilyNarrowSegInputsK0_closed_min_of_paperHypotheses
              (d := d)
              (γBarReal := Hamiltonian.gammaBar hpow.α hpow.β)
              (βBarReal := Hamiltonian.betaBar hpow.β)
              (βBarReal' := Hamiltonian.betaBar' hpow.β)
              (γBarReal' := Hamiltonian.gammaBar' hpow.α hpow.β)
              (γBar := Hamiltonian.gammaBar hpow.α hpow.β)
              (V := V) (H := H) (DpH := DpH)
              hmon hpow hHat0 hHextCont hAgree hV hExp
              rfl rfl rfl rfl
              hβ_holder hγ_holder hβTop hγ'_le_β
              rfl
              (mLim := wkBundle.mLim) (uLim := wkBundle.uLim)
              (DuLim := wkBundle.DuLim)
              wkBundle.hmLim_memLp wkBundle.huLim_sob
              (fun i => wkBundle.hDuLim_memLp_γ i)
              hF_HJB_meas hF_flux_meas
              (g₁ := g₁) (g₂ := g₂) hg₁_lp hg₂_lp
              hmg₁_β hmg₂_β hjoint₁_nn hjoint₂_nn
              η ν Dν hη hDν hν_β hν_γ }
    -- D6 step 5 — transport-family Minty residue discharge
    -- (`infra-P5-T10-D6-transport-residue-discharge`, iter-0534 audit
    -- step 5). Produces `TransportFamilyNarrowMintyResidueK0` from
    -- the paper-scalar bundle `T10PaperScalars_of_paperHypotheses`
    -- (iter 0535) plus the authorised B-class input
    -- `transportSegInputsAuth` for the per-test-pair segment-data
    -- record. The single primal-side nonneg `hmLim_nn` is supplied
    -- by `wkBundle.hmRep_nonneg` (the limit triple's a.e. nonneg).
    --
    -- **iter `infra-P5-T10-v8-K0-transport-auth-drain`** (2026-05-21,
    -- step 10c of 10 of the v8 K0 plan — THE FINAL AUTH DRAIN): the
    -- per-test-pair K0 transport segment-data is now produced in-body
    -- by the closed paper-faithful producer
    -- `transportFamilyNarrowSegInputsK0_closed_of_paperHypotheses`
    -- (BanachBridge.lean:10531), threading paper hypotheses, derived
    -- analytic riders, the two transport perturbations selected from
    -- `D_transport_family_paper` membership via `Classical.choose`, the
    -- primal a.e.-nonneg `wkBundle.hmRep_nonneg`, and the four
    -- test-direction regularity certs (now actively consumed). The
    -- B-class `transportSegInputsAuth` parameter has been removed; auth
    -- count drops 1 → 0. Mirror of the signed drain (iter 0776).
    case mintyResTransportOf =>
      intro wkBundle
      -- Shared paper-scalar bundle at the paper-canonical exponents.
      have scalars :
          T10PaperScalars (d := d) V H DpH hpow :=
        T10PaperScalars_of_paperHypotheses (d := d)
          V H DpH hpow hV hHat0 hAgree
      -- Derived analytic riders for the closed producer.
      let hExp :
          StationaryMFG.Theorems.SimplePower.SimplePowerExponentFacts
            (Hamiltonian.gammaBar hpow.α hpow.β)
            (ENNReal.ofReal (Hamiltonian.betaBar hpow.β))
            (ENNReal.ofReal (Hamiltonian.gammaBar hpow.α hpow.β))
            (ENNReal.ofReal (Hamiltonian.betaBar' hpow.β)) :=
        StationaryMFG.Theorems.SimplePower.SimplePowerExponentFacts.ofPowerGrowth hpow
      have hF_HJB_meas :=
        StationaryMFG.Theorems.SimplePower.Banach.paperSection8_hF_HJB_meas_of_powerGrowth
          (d := d) (βBarReal := Hamiltonian.betaBar hpow.β)
          (γBarReal := Hamiltonian.gammaBar hpow.α hpow.β)
          (βBarReal' := Hamiltonian.betaBar' hpow.β)
          (γBarReal' := Hamiltonian.gammaBar' hpow.α hpow.β)
          (V := V) (H := H) (DpH := DpH) hpow hV
      have hF_flux_meas :=
        StationaryMFG.Theorems.SimplePower.Banach.paperSection8_hF_flux_meas_of_powerGrowth
          (d := d) (βBarReal := Hamiltonian.betaBar hpow.β)
          (γBarReal := Hamiltonian.gammaBar hpow.α hpow.β)
          (βBarReal' := Hamiltonian.betaBar' hpow.β)
          (γBarReal' := Hamiltonian.gammaBar' hpow.α hpow.β)
          (V := V) (H := H) (DpH := DpH) hpow
      have hβ_holder :
          (Hamiltonian.betaBar hpow.β).HolderConjugate
            (Hamiltonian.betaBar' hpow.β) :=
        StationaryMFG.Theorems.SimplePower.Banach.hpqBeta_paper
          (d := d) hpow
      have hγ_holder :
          (Hamiltonian.gammaBar hpow.α hpow.β).HolderConjugate
            (Hamiltonian.gammaBar' hpow.α hpow.β) :=
        StationaryMFG.Theorems.SimplePower.Banach.hpqGamma_paper
          (d := d) hpow
      have hβTop :
          ENNReal.ofReal (Hamiltonian.gammaBar hpow.α hpow.β) ≠ ⊤ :=
        ENNReal.ofReal_ne_top
      have hγ'_le_β :
          ENNReal.ofReal (Hamiltonian.gammaBar' hpow.α hpow.β)
            ≤ ENNReal.ofReal (Hamiltonian.betaBar hpow.β) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h := Hamiltonian.gammaBar'_le_betaBar hpow.hα hpow.hβ
        exact h
      exact
        { hHat0       := scalars.hHat0
          hAgree      := scalars.hAgree
          hβconj      := scalars.hβconj
          hγconj      := scalars.hγconj
          hγ_one_lt   := scalars.hγ_one_lt
          hγBar_eq    := scalars.hγBar_eq
          hV_conj     := scalars.hV_conj
          hmLim_nn    := wkBundle.hmRep_nonneg
          -- Per-test-pair K0 transport segment-data: built in-body via
          -- the closed paper-faithful producer (no more
          -- `transportSegInputsAuth`). The two transport perturbations
          -- `(ψ₁, ψ₂)` are extracted from `D_transport_family_paper`
          -- membership (`⟨ψ, p_eq⟩` shape) via `Classical.choose`. The
          -- four test-direction certs `(hη, hDν, hν_β, hν_γ)` are
          -- threaded into the closed producer.
          segInputsOf := fun {_ _ _} hBar {_ _ _} hμ η ν Dν hη hDν hν_β hν_γ =>
            transportFamilyNarrowSegInputsK0_closed_min_of_paperHypotheses
              (d := d)
              (γBarReal := Hamiltonian.gammaBar hpow.α hpow.β)
              (βBarReal := Hamiltonian.betaBar hpow.β)
              (βBarReal' := Hamiltonian.betaBar' hpow.β)
              (γBarReal' := Hamiltonian.gammaBar' hpow.α hpow.β)
              (γBar := Hamiltonian.gammaBar hpow.α hpow.β)
              (V := V) (H := H) (DpH := DpH)
              hmon hpow hHat0 hHextCont hAgree hV hExp
              rfl rfl rfl rfl
              hβ_holder hγ_holder hβTop hγ'_le_β
              rfl
              (mLim := wkBundle.mLim) (uLim := wkBundle.uLim)
              (DuLim := wkBundle.DuLim)
              wkBundle.hmLim_memLp wkBundle.huLim_sob
              (fun i => wkBundle.hDuLim_memLp_γ i)
              wkBundle.hmRep_nonneg
              hF_HJB_meas hF_flux_meas
              (Classical.choose hμ) (Classical.choose hBar)
              η ν Dν hη hDν hν_β hν_γ }
    -- **`infra-P5-T10-v7-phase4-hmu-posAuth-drain`** (iter 0580
    -- audit). D5 — a.e. non-negativity is now discharged **in-body**
    -- from the family-membership witness plus `wkBundle.hmRep_nonneg`.
    -- The three auth parameters `hμ_posAuth_{set,signed,transport}`
    -- (formerly strict-positivity authorisations) have been drained.
    case hμ_posOf_set        =>
      -- `D_set_family_paper` membership unpacks as
      -- `⟨ρ, ρ_nn, ρ_lp, ρ_per, p_eq⟩` with `p_eq : (μ,υ,Dυ) =
      -- (mLim + ρ, uLim, DuLim)`. Combine `wkBundle.hmRep_nonneg`
      -- (`0 ≤ᵐ mLim`) with `ρ_nn : ∀ x, 0 ≤ ρ x` (pointwise) to
      -- conclude `0 ≤ᵐ mLim + ρ`.
      intro _seq wkBundle μ _υ _Dυ hMem
      rcases hMem with ⟨ρ, hρ_nn, _hρ_lp, _hρ_per, hp_eq⟩
      rw [Prod.mk.injEq, Prod.mk.injEq] at hp_eq
      obtain ⟨hμ_eq, _hυ_eq, _hDυ_eq⟩ := hp_eq
      subst hμ_eq
      filter_upwards [wkBundle.hmRep_nonneg] with x hxm
      have : (0 : ℝ) ≤ wkBundle.mLim x + ρ x :=
        add_nonneg hxm (hρ_nn x)
      exact this
    case hμ_posOf_signed     =>
      -- `D_signed_family_paper_nn` membership unpacks as
      -- `⟨g, g_lp, g_per, hSum_nn, p_eq⟩` with
      -- `hSum_nn : 0 ≤ᵐ (mLim + g)` already (by definition of
      -- the `_nn` narrow family). Just transport.
      intro _seq wkBundle μ _υ _Dυ hMem
      rcases hMem with ⟨g, _hg_lp, _hg_per, hSum_nn, hp_eq⟩
      rw [Prod.mk.injEq, Prod.mk.injEq] at hp_eq
      obtain ⟨hμ_eq, _hυ_eq, _hDυ_eq⟩ := hp_eq
      subst hμ_eq
      exact hSum_nn
    case hμ_posOf_transport  =>
      -- `D_transport_family_paper` membership unpacks as
      -- `⟨ψ, p_eq⟩` with `p_eq.1 : μ = mLim`. Read off
      -- `wkBundle.hmRep_nonneg`.
      intro _seq wkBundle μ _υ _Dυ hMem
      rcases hMem with ⟨_ψ, hp_eq⟩
      rw [Prod.mk.injEq, Prod.mk.injEq] at hp_eq
      obtain ⟨hμ_eq, _hυ_eq, _hDυ_eq⟩ := hp_eq
      subst hμ_eq
      exact wkBundle.hmRep_nonneg

/-! ### Paper-facing headline corollary -/

/-- **Theorem 1 — existence under simple power growth.**

This is the public statement of paper `thm:main-simple.power.growth`.
The hypotheses are Lasry–Lions monotonicity, simple power growth,
`V ∈ L^{β̄'}_per`, existence of the right-hand limits at zero, and agreement
of the supplied values `H x p 0` with those limits.

The finiteness of the limits and joint continuity on `{m ≥ 0}` are proved
internally by `Hext_finite_at_zero_of_powerGrowth` and
`HypothesisHextJointCont.of_powerGrowth`. In particular, joint continuity
is not an additional hypothesis. The residue bundle used by the internal
existence theorem is also constructed in the proof.

The conclusion gives a strong solution with the paper exponents
`β̄ = β + 1`, `γ̄ = α(β+1)/β`, and `β̄' = (β+1)/β`. Each returned `Du i`
is explicitly tied to the weak derivative of `u` and belongs to `L^{γ̄}`. -/
theorem thm_main_simplePowerGrowth_paper
    [Fact (0 < d)]
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hmon : HypothesisMonotone H DpH)
    (hpow : HypothesisPowerGrowth H DpH)
    (hV : Periodic.MemLpPer
            (ENNReal.ofReal (Hamiltonian.betaBar' hpow.β)) V)
    (hHat0 : StationaryMFG.Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : StationaryMFG.Hamiltonian.H_zero_eq_Hext (d := d) H)
    :
    ∃ (m u : (Fin d → ℝ) → ℝ) (Du : Fin d → (Fin d → ℝ) → ℝ),
      IsStrongSolution V H (StationaryMFG.Hamiltonian.JsimpleExt DpH) Du m u
        ∧ Periodic.MemLpPer
            (ENNReal.ofReal (Hamiltonian.betaBar hpow.β)) m
        ∧ Periodic.MemSobolevPer
            (ENNReal.ofReal (Hamiltonian.gammaBar hpow.α hpow.β)) u
        ∧ (∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ m x)
        ∧ (∀ i, Periodic.HasWeakDerivPer (d := d) i u (Du i))
        ∧ (∀ i, Periodic.MemLpPer
            (ENNReal.ofReal (Hamiltonian.gammaBar hpow.α hpow.β)) (Du i)) := by
  have hFin : StationaryMFG.Hamiltonian.Hext_finite_at_zero (d := d) H :=
    StationaryMFG.Hamiltonian.Hext_finite_at_zero_of_powerGrowth hpow hHat0
  have hHextCont : StationaryMFG.Hamiltonian.HypothesisHextJointCont (d := d) H :=
    StationaryMFG.Hamiltonian.HypothesisHextJointCont.of_powerGrowth
      hmon hpow hHat0 hAgree
  let residues :=
    T10PaperResidues.of_paperHypotheses (d := d)
      V H DpH hmon hpow hV hHat0 hAgree hHextCont
  exact thm_main_simplePowerGrowth_concrete (d := d)
    V H DpH hmon hpow hV hHat0 hFin hAgree hHextCont residues

/-- The public theorem requires no separate boundary joint-continuity proof. -/
example {d : ℕ} [Fact (0 < d)]
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hmon : HypothesisMonotone H DpH)
    (hpow : HypothesisPowerGrowth H DpH)
    (hV : Periodic.MemLpPer
            (ENNReal.ofReal (Hamiltonian.betaBar' hpow.β)) V)
    (hHat0 : StationaryMFG.Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : StationaryMFG.Hamiltonian.H_zero_eq_Hext (d := d) H) :
    ∃ (m u : (Fin d → ℝ) → ℝ) (Du : Fin d → (Fin d → ℝ) → ℝ),
      IsStrongSolution V H (StationaryMFG.Hamiltonian.JsimpleExt DpH) Du m u
        ∧ Periodic.MemLpPer
            (ENNReal.ofReal (Hamiltonian.betaBar hpow.β)) m
        ∧ Periodic.MemSobolevPer
            (ENNReal.ofReal (Hamiltonian.gammaBar hpow.α hpow.β)) u
        ∧ (∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ m x)
        ∧ (∀ i, Periodic.HasWeakDerivPer (d := d) i u (Du i))
        ∧ (∀ i, Periodic.MemLpPer
            (ENNReal.ofReal (Hamiltonian.gammaBar hpow.α hpow.β)) (Du i)) :=
  thm_main_simplePowerGrowth_paper (d := d)
    V H DpH hmon hpow hV hHat0 hAgree

end SimplePower
end Theorems
end StationaryMFG
