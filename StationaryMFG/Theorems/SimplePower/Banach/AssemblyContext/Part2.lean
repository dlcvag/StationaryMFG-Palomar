module

public import StationaryMFG.Theorems.SimplePower.Banach.AbstractLifts
public import StationaryMFG.Theorems.SimplePower.Banach.AprioriDischarge
public import StationaryMFG.Theorems.SimplePower.Banach.Operator
public import StationaryMFG.Theorems.SimplePower.Banach.ExponentFacts
public import StationaryMFG.Hamiltonian.Assumptions
public import StationaryMFG.Hamiltonian.Estimates
public import StationaryMFG.Monotone.AbstractWeak
public import StationaryMFG.Periodic.Reflexive
public import StationaryMFG.Periodic.LpReflexive
public import StationaryMFG.Theorems.SimplePower.Banach.AssemblyContext.Part1
import all StationaryMFG.Theorems.SimplePower.Banach.AssemblyContext.Part1

@[expose] public section

noncomputable section
namespace StationaryMFG
namespace Theorems
namespace SimplePower
namespace Banach
open MeasureTheory Set
open StationaryMFG.Periodic
open StationaryMFG.Hamiltonian
open scoped ENNReal
variable {d : ℕ}
variable {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
variable {V : (Fin d → ℝ) → ℝ}
variable {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
variable {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
open StationaryMFG.Monotone (IsMonotone IsHemicontinuous IsCoerciveAt)
open StationaryMFG.Periodic (IsReflexiveNormedSpace HasWeakDerivPer
  MemLpPer MemSobolevPer)
open StationaryMFG.Solutions.MFG (mfgOperatorEpsPair absPowMinusTwo
  vecAbsPowMinusTwo)
open StationaryMFG.Theorems.SimplePower (HemicontSegmentData
  cxComb cxCombGrad aepsiIntegrandAt_unreg aepsiIntegrandAt_gateaux
  IsHK0AbsDominator IsmDpHK0Dominator
  aepsiIntegrandAt_unreg_pointwise_bound_K0)


/-! ### `auxHypsK0` + `hWeakDerivK0` field-level producers
(`paperSolFor-auxHypsK0`)

The two field-level producers below realize the `auxHypsK0` and
`hWeakDerivK0` fields of `PaperSection8AnalyticResidues` from the
paper hypotheses plus the closed/measurable feeders.

**Inclusion direction (expert review 2026-05-15).**
`K_Aepsi ⊆ K0_Aepsi` (strict-positive inside nonneg), see
`K_Aepsi_subset_K0_Aepsi` in `Banach/AbstractLifts.lean`. Hence the
K_Aepsi-form producer `auxHyps_of_paperHypotheses_on_KAepsi`
**cannot** be restricted downward to discharge the K0 quantifier —
the K_Aepsi-form only covers strictly-positive `q`, whereas
`K0_Aepsi` contains additional nonneg `q` not in `K_Aepsi`.

**Correct route.** Use the K0-specific producer
`auxHyps_K0_at_setPaperTriple` (line 4698), threaded with its
dominator/measurability inputs:

* paper-exponent residues (definitional at paper exponents);
* Hölder pairs from `SimplePowerExponentFacts.paper_holderConjugate_*`;
* the K0-form abs bound uses `(hHat0, hAgree)` (not `(C', h_upper)`);
* `hF_HJB_meas` and `hF_flux_meas` (from
  `paperSection8_hF_HJB_meas_of_powerGrowth` and
  `paperSection8_hF_flux_meas_of_powerGrowth`);
* `hG_HJB_dom`, `hG_flux_dom`, `hG_grad_mem`, `hG_val_mem`
  (discharged inline via the same closures used in
  `auxHyps_of_paperHypotheses_on_KAepsi`, but with the unifying
  constant `hpow.C` driving `hG_HJB_dom`).

For `hWeakDerivK0`: we adapt `aepsi_weakDerivTie_of_paperHypotheses_legacy`
(line 3243), which is an identity bridge from a per-K0 residue to the
`hWeakDeriv` conclusion on `K0_Aepsi`. -/

/-- **K0 supplier producer.** Produces the `auxHypsK0` field of
`PaperSection8AnalyticResidues`: a per-`K0_Aepsi`-element
`MFGOpEpsAuxHyps` certificate.

Mirrors `auxHyps_of_paperHypotheses_on_KAepsi` but for the closed
nonneg cone `K0_Aepsi`. The K0 form replaces strict positivity
`0 < m` with `0 ≤ m` a.e., and uses `(hHat0, hAgree)` (driving
`Hamiltonian.H_abs_bound_nonneg_of_hHat0`) instead of a caller-
supplied `(C', h_upper)`. -/
theorem paperSection8_auxHypsK0_of_paperHypotheses
    {d : ℕ}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (hExp : SimplePowerExponentFacts γBarReal
                (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
                (ENNReal.ofReal βBarReal'))
    -- Paper-exponent identification residues (definitional at paper
    -- exponents).
    (hβBar_eq : βBarReal = hpow.β + 1)
    (hγBar_eq : γBarReal = hpow.α * (hpow.β + 1) / hpow.β)
    (hβBar'_eq : βBarReal' = (hpow.β + 1) / hpow.β)
    (hγBar'_eq : γBarReal' = γBarReal / (γBarReal - 1))
    -- Hölder-pair residues.
    (hβ : βBarReal.HolderConjugate βBarReal')
    (hγ : γBarReal.HolderConjugate γBarReal')
    (hβTop : ENNReal.ofReal γBarReal ≠ ⊤)
    (hγ'_le_β : ENNReal.ofReal γBarReal' ≤ ENNReal.ofReal βBarReal)
    -- Measurability witnesses (universal-q residue).
    (hF_HJB_meas :
      ∀ q : XBanach d βBarReal γBarReal,
        AEStronglyMeasurable
          (fun x => -(uOf q x) - H x (fun i => DuOf q i x) (mOf q x) + V x)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (hF_flux_meas :
      ∀ q : XBanach d βBarReal γBarReal, ∀ i,
        AEStronglyMeasurable
          (fun x => mOf q x * DpH x (fun j => DuOf q j x) (mOf q x) i)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d))) :
    ∀ q ∈ K0_Aepsi d βBarReal γBarReal,
      MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
        V H DpH (DuOf q) (mOf q) (uOf q) := by
  -- Standing positivity / bound facts.
  have hα_pos : 0 < hpow.α := lt_trans Real.zero_lt_one hpow.hα
  have hβ_pos : 0 < hpow.β := hpow.hβ
  have hβ1_pos : 0 < hpow.β + 1 := by linarith
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
  intro q hq_K0
  -- `q ∈ K0_Aepsi` ⇒ `0 ≤ mOf q a.e.`.
  have hμ_nn :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)), 0 ≤ mOf q x := hq_K0
  -- `MemLpPer` certificates from the Lp components of `q`.
  have hmLp : MemLpPer (d := d) (ENNReal.ofReal βBarReal) (mOf q) :=
    memLpPer_of_lpPer (d := d) q.1
  have huLp : MemLpPer (d := d) (ENNReal.ofReal γBarReal) (uOf q) :=
    memLpPer_of_lpPer (d := d) q.2.1
  have hDuLp : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (DuOf q i) := by
    intro i; exact memLpPer_of_lpPer (d := d) (q.2.2 i)
  -- Reframe the test-triple regularity at the paper exponents.
  have hμ_paperBetaBar : MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1)) (mOf q) := by
    rw [← hβBar_eq]; exact hmLp
  have hυ_paperGammaBar :
      MemLpPer (d := d) (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))
        (uOf q) := by
    rw [← hγBar_eq]; exact huLp
  have hDυ_paperGammaBar : ∀ i,
      MemLpPer (d := d) (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))
        (DuOf q i) := by
    intro i; rw [← hγBar_eq]; exact hDuLp i
  have hV_paperBetaBar' : MemLpPer (d := d)
      (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) V := by
    rw [← hβBar'_eq]; exact hV
  -- Discharge `hG_HJB_dom` via `g_dominator_memLp_betaBar'` with the
  -- unifying constant `C' := hpow.C` (K0 form).
  have hG_HJB_dom_paper :
      MemLpPer (d := d) (ENNReal.ofReal ((hpow.β + 1) / hpow.β))
        (fun x : (Fin d → ℝ) =>
          hpow.C * (‖fun i => DuOf q i x‖ ^ hpow.α + 1)
            + hpow.C * (mOf q x ^ hpow.β + 1)
            + |uOf q x| + |V x|) :=
    Hamiltonian.g_dominator_memLp_betaBar' hpow V (uOf q) (mOf q) (DuOf q)
      hμ_paperBetaBar hυ_paperGammaBar hDυ_paperGammaBar hV_paperBetaBar'
      hpow.hC
  have hG_HJB_dom :
      MemLpPer (d := d) (ENNReal.ofReal βBarReal')
        (fun x : (Fin d → ℝ) =>
          hpow.C * (‖fun i => DuOf q i x‖ ^ hpow.α + 1)
            + hpow.C * (mOf q x ^ hpow.β + 1)
            + |uOf q x| + |V x|) := by
    rw [hβBar'_eq]; exact hG_HJB_dom_paper
  -- Discharge `hG_flux_dom` via `flux_dominator_memLp_gammaBar'`.
  have hG_flux_dom_paper :
      MemLpPer (d := d)
        (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β /
          (hpow.α * (hpow.β + 1) / hpow.β - 1)))
        (fun x : (Fin d → ℝ) =>
          hpow.C * (mOf q x * ‖fun j => DuOf q j x‖ ^ (hpow.α - 1)
                      + mOf q x ^ (1 + hpow.β - hpow.β / hpow.α) + mOf q x)) :=
    Hamiltonian.flux_dominator_memLp_gammaBar' hpow (mOf q) (DuOf q)
      hμ_paperBetaBar hDυ_paperGammaBar
  have hG_flux_dom :
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (fun x : (Fin d → ℝ) =>
          hpow.C * (mOf q x * ‖fun j => DuOf q j x‖ ^ (hpow.α - 1)
                      + mOf q x ^ (1 + hpow.β - hpow.β / hpow.α) + mOf q x)) := by
    have hγ'_paper_eq :
        γBarReal' = hpow.α * (hpow.β + 1) / hpow.β /
                    (hpow.α * (hpow.β + 1) / hpow.β - 1) := by
      rw [hγBar'_eq, hγBar_eq]
    rw [hγ'_paper_eq]; exact hG_flux_dom_paper
  -- Discharge `hG_grad_mem` and `hG_val_mem` via the new closures.
  have hG_grad_mem : ∀ i,
      MemLpPer (d := d) (ENNReal.ofReal γBarReal')
        (G_grad γBarReal (DuOf q) i) := by
    intro i
    exact G_grad_memLpPer_gammaBar' hγBar_one_lt_real hγBar'_eq
            (DuOf q) hDuLp i
  have hG_val_mem :
      MemLpPer (d := d) (ENNReal.ofReal γBarReal') (G_val γBarReal (uOf q)) :=
    G_val_memLpPer_gammaBar' hγBar_one_lt_real hγBar'_eq (uOf q) huLp
  -- Assemble via the K0 per-triple feeder.
  exact auxHyps_K0_at_setPaperTriple
    (γBarReal := γBarReal) (βBarReal := βBarReal)
    (βBarReal' := βBarReal') (γBarReal' := γBarReal')
    hmon hpow hHat0 hAgree hV hExp (DuOf q) (mOf q) (uOf q)
    hβ hγ hβTop hγ'_le_β hμ_nn
    (hF_HJB_meas q) (hF_flux_meas q)
    hG_HJB_dom hG_flux_dom hmLp hG_grad_mem hG_val_mem

/-- **Weak-derivative tie producer (refined cone).** Produces the
`hWeakDerivK0` field of `PaperSection8AnalyticResidues{Min}`: a per-
`K0_Aepsi_W`-element weak-derivative pairing tying each gradient
component `DuOf q i` to the value component `uOf q`.

Iter post-0707 (Phase 5 step 4): the field is retyped to consume the
refined non-negativity cone `K0_Aepsi_W` (which carries the weak-
derivative tie structurally), so the producer no longer needs an
external `hWeakDeriv` residue parameter. The body is the direct
projection `hasWeakDerivPer_of_mem_K0_Aepsi_W`. -/
theorem paperSection8_hWeakDerivK0_of_paperHypotheses
    {d : ℕ}
    {γBarReal βBarReal βBarReal' : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (_hmon : Hamiltonian.HypothesisMonotone H DpH)
    (_hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (_hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (_hExp : SimplePowerExponentFacts γBarReal
                (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
                (ENNReal.ofReal βBarReal')) :
    ∀ q ∈ K0_Aepsi_W d βBarReal γBarReal,
      ∀ i, HasWeakDerivPer (d := d) i (uOf q) (DuOf q i) :=
  fun _q hq => hasWeakDerivPer_of_mem_K0_Aepsi_W hq

/-! ### Optional bundle: `PaperSection8AuxHypsK0Fields`

The two K0-quantified composition fields `auxHypsK0` and
`hWeakDerivK0` of `PaperSection8AnalyticResidues` are bundled below
as a separate small struct. Rationale: `PaperSection8ClosedMeasFields`
is the partial bundle for closed/mostly-closed analytic-measurability
fields, and the K0-quantified composition fields here are filed in a
distinct bundle because their producers have a different shape
(they consume per-q paper-exponent identifications + a K0 weak-deriv
residue, vs. the universal `(hpow, hV, hγ)` shape of the closed-meas
bundle).

The two fields can be assembled separately or via
`PaperSection8AuxHypsK0Fields.of_paperHypotheses` below. -/

/-- **Paper §8 K0-quantified-composition bundle.**

Carries the two K0-quantified composition fields of
`PaperSection8AnalyticResidues`:

* `auxHypsK0` — `∀ q ∈ K0_Aepsi …, MFGOpEpsAuxHyps … (DuOf q) …`;
* `hWeakDerivK0` — `∀ q ∈ K0_Aepsi_W …, ∀ i, HasWeakDerivPer …`
  (Phase 5 step 4 retype, iter post-0707). The refined cone
  `K0_Aepsi_W` carries the weak-derivative tie structurally, so the
  field is discharged by direct projection. -/
structure PaperSection8AuxHypsK0Fields
    {d : ℕ}
    (γBarReal βBarReal βBarReal' γBarReal' : ℝ)
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)) : Prop where
  /-- `K0` supplier residue (`MFGOpEpsAuxHyps` on `K0_Aepsi`). -/
  auxHypsK0 : ∀ q ∈ K0_Aepsi d βBarReal γBarReal,
                MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                  V H DpH (DuOf q) (mOf q) (uOf q)
  /-- Per-`K0_Aepsi_W` weak-derivative tie (refined cone, iter post-0707). -/
  hWeakDerivK0 :
    ∀ q ∈ K0_Aepsi_W d βBarReal γBarReal,
      ∀ i, HasWeakDerivPer (d := d) i (uOf q) (DuOf q i)

/-- **Bundle producer.** Assembles a `PaperSection8AuxHypsK0Fields`
from the paper hypotheses plus the paper-exponent / Hölder /
measurability / weak-derivative residues. -/
theorem PaperSection8AuxHypsK0Fields.of_paperHypotheses
    {d : ℕ}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (hExp : SimplePowerExponentFacts γBarReal
                (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
                (ENNReal.ofReal βBarReal'))
    (hβBar_eq : βBarReal = hpow.β + 1)
    (hγBar_eq : γBarReal = hpow.α * (hpow.β + 1) / hpow.β)
    (hβBar'_eq : βBarReal' = (hpow.β + 1) / hpow.β)
    (hγBar'_eq : γBarReal' = γBarReal / (γBarReal - 1))
    (hβ : βBarReal.HolderConjugate βBarReal')
    (hγ : γBarReal.HolderConjugate γBarReal')
    (hβTop : ENNReal.ofReal γBarReal ≠ ⊤)
    (hγ'_le_β : ENNReal.ofReal γBarReal' ≤ ENNReal.ofReal βBarReal)
    (hF_HJB_meas :
      ∀ q : XBanach d βBarReal γBarReal,
        AEStronglyMeasurable
          (fun x => -(uOf q x) - H x (fun i => DuOf q i x) (mOf q x) + V x)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (hF_flux_meas :
      ∀ q : XBanach d βBarReal γBarReal, ∀ i,
        AEStronglyMeasurable
          (fun x => mOf q x * DpH x (fun j => DuOf q j x) (mOf q x) i)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d))) :
    PaperSection8AuxHypsK0Fields
      (d := d) γBarReal βBarReal βBarReal' γBarReal' V H DpH where
  auxHypsK0 :=
    paperSection8_auxHypsK0_of_paperHypotheses
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      hmon hpow hHat0 hAgree hV hExp
      hβBar_eq hγBar_eq hβBar'_eq hγBar'_eq
      hβ hγ hβTop hγ'_le_β hF_HJB_meas hF_flux_meas
  hWeakDerivK0 :=
    paperSection8_hWeakDerivK0_of_paperHypotheses
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal')
      hmon hpow hV hExp

/-- **Paper §8 analytic residues** (group-C).

Bundle of the 13 analytic residues that the closed-form aggregator
threads as authorised paper-§8 inputs (CONVENTIONS §1b). Discharging any
of these is filed as a sibling backlog task; the present aggregator
simply forwards them.

Field meaning (cf. the closed-form aggregator above):

* `h_upper`, `h_slice` — paper line 944 / Hyp-A `(a:H)` general-upper-
  bound facts (convexity of `H` in `p`).
* `hF_HJB_meas`, `hF_flux_meas`, `hF_unreg_meas`, `hF_gat_meas` —
  measurability residues from `Hamiltonian/*.lean` plus the
  axis-mix measure hypothesis.
* `hScalarMono`, `hVecMono` — `absPowMinusTwo` / `vecAbsPowMinusTwo`
  monotonicity (already in the project, just threaded).
* `Ccoerc`, `hbound_residue` — coercivity supplier (paper line 982).
* `hSegRes` — segment integrand `MemLpPer` dominator (paper §8.3).
* `auxHypsK0`, `hWeakDerivK0` — `K0` supplier and per-`K0` weak-
  derivative tie. -/
structure PaperSection8AnalyticResidues
    {d : ℕ}
    (γBarReal βBarReal βBarReal' γBarReal' : ℝ)
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (ε : ℝ)
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH) where
  /-- Paper-line-944 general upper bound (Hyp-A `(a:H)`). -/
  h_upper :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      ∀ p mm, 0 < mm →
        H x p mm ≤ hpow.C * (‖p‖ ^ hpow.α + 1) - (mm ^ hpow.β) / hpow.C
  /-- HJB-flux measurability (universal-`q` form). -/
  hF_HJB_meas :
    ∀ q : XBanach d βBarReal γBarReal,
      AEStronglyMeasurable
        (fun x => -(uOf q x) - H x (fun i => DuOf q i x) (mOf q x) + V x)
        (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d))
  /-- Flux measurability (universal-`q` form). -/
  hF_flux_meas :
    ∀ q : XBanach d βBarReal γBarReal, ∀ i,
      AEStronglyMeasurable
        (fun x => mOf q x * DpH x (fun j => DuOf q j x) (mOf q x) i)
        (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d))
  /-- Scalar monotonicity for `absPowMinusTwo γBarReal`. -/
  hScalarMono :
    ∀ s t : ℝ,
      0 ≤ (absPowMinusTwo γBarReal t * t - absPowMinusTwo γBarReal s * s)
            * (t - s)
  /-- Vector monotonicity for `vecAbsPowMinusTwo γBarReal`. -/
  hVecMono :
    ∀ v w : Fin d → ℝ,
      0 ≤ (vecAbsPowMinusTwo γBarReal v • v - vecAbsPowMinusTwo γBarReal w • w)
            ⬝ (v - w)
  /-- Scaled-gauge coercivity scaling (paper line 982, `λ > 0`). -/
  lamCoerc : ℝ
  /-- Positivity of the scaled-gauge scaling. -/
  hlamCoerc : 0 < lamCoerc
  /-- Coercivity constant (paper line 982). -/
  Ccoerc : ℝ
  /-- Scaled-gauge coercivity bound on the cobounded × principal `K_Aepsi`
  filter. The gauge exponent is `coercivityGaugeExponent βBarReal γBarReal
  = min β̄ γ̄` (not bare `γBarReal`): see the docstring of
  `coercivityGaugeExponent` for the rationale (Path B fix, iter 0644+). -/
  hbound_residue :
    ∀ᶠ v in (Bornology.cobounded (XBanach d βBarReal γBarReal)
                ⊓ Filter.principal (K_Aepsi d βBarReal γBarReal)),
      lamCoerc * aepsiCoerciveGauge (βBarReal := βBarReal) (γBarReal := γBarReal)
          (coercivityGaugeExponent βBarReal γBarReal) v - Ccoerc ≤
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε (fun i => ⇑(v.2.2 i)) (⇑v.1) (⇑v.2.1)
            (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1)
          - mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε (fun _ _ => 0) (fun _ => 1) (fun _ => 0)
              (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1)
  /-- Hemicontinuity slice bound (paper §8 hemicontinuity). -/
  h_slice :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      ∀ p m, 0 < m →
        H x p m ≤ -(m ^ hpow.β) / hpow.C + hpow.C + hpow.C * ‖p‖ ^ hpow.α
                + hpow.C * ‖p‖ * (m ^ (hpow.β - hpow.β / hpow.α) + 1)
  /-- Segment integrand `MemLpPer` dominator. -/
  hSegRes : ∀ (u v : XBanach d βBarReal γBarReal),
              u ∈ K_Aepsi d βBarReal γBarReal →
              v ∈ K_Aepsi d βBarReal γBarReal →
              ∀ (w : XBanach d βBarReal γBarReal),
    MemLpPer (d := d) (ENNReal.ofReal βBarReal) (⇑w.1) ∧
    (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal)
                  (fun x => ⇑(w.2.2 i) x)) ∧
    MemLpPer (d := d) (ENNReal.ofReal βBarReal) (⇑w.2.1) ∧
    MemLpPer (d := d) (ENNReal.ofReal γBarReal) (⇑w.2.1) ∧
    MemLpPer (d := d) (ENNReal.ofReal βBarReal')
      (fun x => |uOf u x| + |uOf v x|) ∧
    MemLpPer (d := d) (ENNReal.ofReal βBarReal')
      (fun x =>
        ‖fun i => |DuOf u i x| + |DuOf v i x|‖ ^ hpow.α + 1) ∧
    MemLpPer (d := d) (ENNReal.ofReal βBarReal')
      (fun x => (|mOf u x| + |mOf v x|) ^ hpow.β + 1) ∧
    MemLpPer (d := d) (ENNReal.ofReal γBarReal')
      (fun x => (|mOf u x| + |mOf v x|)
          * ‖fun i => |DuOf u i x| + |DuOf v i x|‖ ^ (hpow.α - 1)) ∧
    MemLpPer (d := d) (ENNReal.ofReal γBarReal')
      (fun x => (|mOf u x| + |mOf v x|)
          ^ (1 + hpow.β - hpow.β / hpow.α)) ∧
    MemLpPer (d := d) (ENNReal.ofReal γBarReal')
      (fun x => |mOf u x| + |mOf v x|) ∧
    MemLpPer (d := d) (ENNReal.ofReal βBarReal')
      (fun x => (|mOf u x| + |mOf v x|) + 1) ∧
    MemLpPer (d := d) (ENNReal.ofReal γBarReal')
      (fun x =>
        (∑ i, (|DuOf u i x| + |DuOf v i x|) ^ (2 : ℕ))
            ^ ((γBarReal - 1) / 2)) ∧
    MemLpPer (d := d) (ENNReal.ofReal γBarReal')
      (fun x => (|uOf u x| + |uOf v x|) ^ (γBarReal - 1))
  /-- Unregularised segment-integrand measurability. -/
  hF_unreg_meas : ∀ (u v : XBanach d βBarReal γBarReal),
              u ∈ K_Aepsi d βBarReal γBarReal →
              v ∈ K_Aepsi d βBarReal γBarReal →
              ∀ (w : XBanach d βBarReal γBarReal),
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x => aepsiIntegrandAt_unreg V H DpH
                    (DuOf v) (DuOf u) (mOf v) (mOf u)
                    (uOf v) (uOf u)
                    (fun i => ⇑(w.2.2 i)) (⇑w.1) (⇑w.2.1) x t)
        (MeasureTheory.volume.restrict (UnitCube d))
  /-- Gateaux segment-integrand measurability. -/
  hF_gat_meas : ∀ (u v : XBanach d βBarReal γBarReal),
              u ∈ K_Aepsi d βBarReal γBarReal →
              v ∈ K_Aepsi d βBarReal γBarReal →
              ∀ (w : XBanach d βBarReal γBarReal),
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x => aepsiIntegrandAt_gateaux γBarReal
                    (DuOf v) (DuOf u) (uOf v) (uOf u)
                    (fun i => ⇑(w.2.2 i)) (⇑w.2.1) x t)
        (MeasureTheory.volume.restrict (UnitCube d))
  /-- `K0` supplier residue (`MFGOpEpsAuxHyps` on `K0_Aepsi`). -/
  auxHypsK0 : ∀ q ∈ K0_Aepsi d βBarReal γBarReal,
                MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                  V H DpH (DuOf q) (mOf q) (uOf q)
  /-- Per-`K0_Aepsi_W` weak-derivative tie (refined cone, iter post-0707). -/
  hWeakDerivK0 :
    ∀ q ∈ K0_Aepsi_W d βBarReal γBarReal,
      ∀ i, HasWeakDerivPer (d := d) i (uOf q) (DuOf q i)

/-! ## Minimal segment-residue shape (paper-faithful)

The `hSegRes` field of `PaperSection8AnalyticResidues` packages the 13
conjuncts that the iter-0606 producer attempted to discharge wholesale.
Two of those conjuncts are **over-specified** relative to what the
hemicontinuity producer chain genuinely consumes after the relaxed
Hölder routing:

* (3) `MemLpPer βBar (⇑w.2.1)` — redundant when paired with the existing
  conjunct (4) `MemLpPer γBar (⇑w.2.1)`; demoting to `L^β̄` requires
  `β̄ ≤ γ̄`, equivalently `β ≤ α`, which is **not** a paper hypothesis.
* (11) `MemLpPer βBar' (m + 1)` — redundant when paired with the
  existing conjunct (10) `MemLpPer γBar' m`; the embedding to `L^β̄'`
  requires `β̄' ≤ β̄`, equivalently `1 ≤ β`, which is **not** a paper
  hypothesis. The naive pointwise route `m ≤ m^β + 1` is false for
  `0 < β < 1` and large `m`, so no paper-faithful pointwise discharge
  exists.

`PaperSection8SegmentResiduesMin` carries only the **11 paper-faithful
conjuncts**, omitting (3) and (11). The hemicontinuity producer chain
(`hemicontSegmentData_of_KAepsi` and `g_unreg_natural_integrableOn`)
can be re-routed to consume this minimal shape directly:

* Term 5 of `g_unreg_natural` `((|m̅|+|μ|)+1) * |ν|` splits as
  `(|m̅|+|μ|)*|ν| + |ν|`; the first piece is integrable via the
  `(γ̄', γ̄)` Hölder pair using conjunct (10) `hΔm` and conjunct (4)
  `hν_γ`; the second piece is integrable on the unit cube (finite
  measure) using `hν_γ` and `1 ≤ γ̄`.
* Conjunct (3) `hν_β` is unused once Term 5 is re-routed.

The replacement of `PaperSection8AnalyticResidues.hSegRes` with the
minimal shape, the consumer-chain relaxation, and the producer chain
from `(hpow, hV)` are tracked by a sibling backlog task. The present
declaration is **statement-only**: it lands the paper-faithful shape so
downstream work can reference it without committing to the consumer
refactor in this iteration.

Note: the forward adapter `PaperSection8SegmentResiduesMin.ofFull`
extracts the minimal conjuncts from the full 13-conjunct `hSegRes`
field by simple projection, requiring **no** exponent inequalities. -/

/-- **Paper-faithful minimal segment-residue shape.**

Per-pair, per-test `MemLpPer p`-of-power residues that the relaxed
hemicontinuity producer chain genuinely consumes. The 11 conjuncts here
exclude the two over-specified conjuncts of the legacy 13-conjunct
shape (`hν_β : MemLpPer βBar ν` and `hΔm1 : MemLpPer βBar' (m + 1)`),
both of which would require paper-forbidden exponent embeddings to
discharge.

Forward direction (extraction from the legacy shape) is given by
`PaperSection8SegmentResiduesMin.ofFull`. The producer from
`(hpow, hV)` and the consumer-chain relaxation are sibling tasks. -/
structure PaperSection8SegmentResiduesMin
    {d : ℕ}
    (γBarReal βBarReal βBarReal' γBarReal' : ℝ)
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH) : Prop where
  /-- Per-pair, per-test `MemLpPer p`-of-power residues — **11**
  conjuncts, paper-faithful. -/
  out : ∀ (u v : XBanach d βBarReal γBarReal),
              u ∈ K_Aepsi d βBarReal γBarReal →
              v ∈ K_Aepsi d βBarReal γBarReal →
              ∀ (w : XBanach d βBarReal γBarReal),
    -- (1) Test-`m` regularity at `βBar`.
    MemLpPer (d := d) (ENNReal.ofReal βBarReal) (⇑w.1) ∧
    -- (2) Test-`Du` regularity at `γBar` (component-wise).
    (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal)
                  (fun x => ⇑(w.2.2 i) x)) ∧
    -- (3) Test-`u` regularity at `γBar`. **No** sibling conjunct at
    --     `βBar` (the legacy `MemLpPer βBar w.2.1` was over-specified).
    MemLpPer (d := d) (ENNReal.ofReal γBarReal) (⇑w.2.1) ∧
    -- (4) `|u u|+|u v| ∈ L^β̄'`.
    MemLpPer (d := d) (ENNReal.ofReal βBarReal')
      (fun x => |uOf u x| + |uOf v x|) ∧
    -- (5) `‖|Du u|+|Du v|‖^α + 1 ∈ L^β̄'`.
    MemLpPer (d := d) (ENNReal.ofReal βBarReal')
      (fun x =>
        ‖fun i => |DuOf u i x| + |DuOf v i x|‖ ^ hpow.α + 1) ∧
    -- (6) `(|m u|+|m v|)^β + 1 ∈ L^β̄'`.
    MemLpPer (d := d) (ENNReal.ofReal βBarReal')
      (fun x => (|mOf u x| + |mOf v x|) ^ hpow.β + 1) ∧
    -- (7) Δm · ‖ΔDu‖^(α-1) ∈ L^γ̄'.
    MemLpPer (d := d) (ENNReal.ofReal γBarReal')
      (fun x => (|mOf u x| + |mOf v x|)
          * ‖fun i => |DuOf u i x| + |DuOf v i x|‖ ^ (hpow.α - 1)) ∧
    -- (8) `Δm^(1 + β - β/α) ∈ L^γ̄'`.
    MemLpPer (d := d) (ENNReal.ofReal γBarReal')
      (fun x => (|mOf u x| + |mOf v x|)
          ^ (1 + hpow.β - hpow.β / hpow.α)) ∧
    -- (9) `Δm ∈ L^γ̄'`. This subsumes the legacy `(Δm + 1) ∈ L^β̄'`
    --     conjunct once Term 5 of `g_unreg_natural` is re-routed via
    --     the `(γ̄', γ̄)` Hölder pair plus finite-measure integrability
    --     of `|ν| ∈ L^γ̄`.
    MemLpPer (d := d) (ENNReal.ofReal γBarReal')
      (fun x => |mOf u x| + |mOf v x|) ∧
    -- (10) Gateaux gradient power: `(∑(|Du u i|+|Du v i|)^2)^((γ̄-1)/2)
    --      ∈ L^γ̄'`.
    MemLpPer (d := d) (ENNReal.ofReal γBarReal')
      (fun x =>
        (∑ i, (|DuOf u i x| + |DuOf v i x|) ^ (2 : ℕ))
            ^ ((γBarReal - 1) / 2)) ∧
    -- (11) Gateaux value power: `(|u u|+|u v|)^(γ̄-1) ∈ L^γ̄'`.
    MemLpPer (d := d) (ENNReal.ofReal γBarReal')
      (fun x => (|uOf u x| + |uOf v x|) ^ (γBarReal - 1))

/-- **Forward adapter (statement-only).** Extract the paper-faithful 11
conjuncts of `PaperSection8SegmentResiduesMin` from the legacy
13-conjunct `hSegRes` field of `PaperSection8AnalyticResidues`. This is
a pure projection — it drops the two over-specified conjuncts
(`MemLpPer βBar w.2.1` and `MemLpPer βBar' (m + 1)`) and so uses no
exponent inequalities beyond what the source field already supplies. -/
theorem PaperSection8SegmentResiduesMin.ofFull
    {d : ℕ}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {hpow : Hamiltonian.HypothesisPowerGrowth H DpH}
    (hAnalytic : PaperSection8AnalyticResidues
                    (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    ε V H DpH hpow) :
    PaperSection8SegmentResiduesMin
      (d := d) γBarReal βBarReal βBarReal' γBarReal' H DpH hpow where
  out := by
    intro u v hu hv w
    obtain ⟨h1, h2, _h3_drop, h4, h5, h6, h7, h8, h9, h10, _h11_drop,
            h12, h13⟩ :=
      hAnalytic.hSegRes u v hu hv w
    exact ⟨h1, h2, h4, h5, h6, h7, h8, h9, h10, h12, h13⟩

/-! ### Exponent-keyed segment-residue shape: `PaperSection8SegmentResiduesMinExp`

The AE-route gate (Phase 7, T3 real-drain) forbids threading a
`HypothesisPowerGrowth (HdeltaPos hweak ε) …` term in the type of a
forwarded field. The structure `PaperSection8SegmentResiduesMin` only
ever uses its `hpow` parameter as `hpow.α` / `hpow.β`, so the entire
segment-residue side is exponent-driven and can be retyped at bare
exponents `(αExp βExp : ℝ)` taken straight from `hweak.α` / `hweak.β`.

`PaperSection8SegmentResiduesMinExp` is a verbatim copy of
`PaperSection8SegmentResiduesMin` with `hpow.α ↦ αExp`, `hpow.β ↦ βExp`
and the `hpow` parameter dropped. The bridge
`PaperSection8SegmentResiduesMin.ofExp` / `.toExp` are definitional
constructor wraps (the two struct bodies coincide when `αExp = hpow.α`,
`βExp = hpow.β`), so the legacy `hpow`-keyed surface is left intact for
T1/T2 while the AE chain consumes the exponent-keyed shape. -/

/-- **Exponent-keyed minimal segment-residue shape.** Verbatim copy of
`PaperSection8SegmentResiduesMin` with the `hpow` parameter replaced by
bare exponents `(αExp βExp : ℝ)`. Consumed by the AE-route producer
chain (where the exponents are `hweak.α` / `hweak.β`), so no
`HypothesisPowerGrowth` term appears in the field type. -/
structure PaperSection8SegmentResiduesMinExp
    {d : ℕ}
    (γBarReal βBarReal βBarReal' γBarReal' : ℝ)
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (αExp βExp : ℝ) : Prop where
  /-- Per-pair, per-test `MemLpPer p`-of-power residues — **11**
  conjuncts, paper-faithful, at bare exponents `αExp`, `βExp`. -/
  out : ∀ (u v : XBanach d βBarReal γBarReal),
              u ∈ K_Aepsi d βBarReal γBarReal →
              v ∈ K_Aepsi d βBarReal γBarReal →
              ∀ (w : XBanach d βBarReal γBarReal),
    MemLpPer (d := d) (ENNReal.ofReal βBarReal) (⇑w.1) ∧
    (∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal)
                  (fun x => ⇑(w.2.2 i) x)) ∧
    MemLpPer (d := d) (ENNReal.ofReal γBarReal) (⇑w.2.1) ∧
    MemLpPer (d := d) (ENNReal.ofReal βBarReal')
      (fun x => |uOf u x| + |uOf v x|) ∧
    MemLpPer (d := d) (ENNReal.ofReal βBarReal')
      (fun x =>
        ‖fun i => |DuOf u i x| + |DuOf v i x|‖ ^ αExp + 1) ∧
    MemLpPer (d := d) (ENNReal.ofReal βBarReal')
      (fun x => (|mOf u x| + |mOf v x|) ^ βExp + 1) ∧
    MemLpPer (d := d) (ENNReal.ofReal γBarReal')
      (fun x => (|mOf u x| + |mOf v x|)
          * ‖fun i => |DuOf u i x| + |DuOf v i x|‖ ^ (αExp - 1)) ∧
    MemLpPer (d := d) (ENNReal.ofReal γBarReal')
      (fun x => (|mOf u x| + |mOf v x|)
          ^ (1 + βExp - βExp / αExp)) ∧
    MemLpPer (d := d) (ENNReal.ofReal γBarReal')
      (fun x => |mOf u x| + |mOf v x|) ∧
    MemLpPer (d := d) (ENNReal.ofReal γBarReal')
      (fun x =>
        (∑ i, (|DuOf u i x| + |DuOf v i x|) ^ (2 : ℕ))
            ^ ((γBarReal - 1) / 2)) ∧
    MemLpPer (d := d) (ENNReal.ofReal γBarReal')
      (fun x => (|uOf u x| + |uOf v x|) ^ (γBarReal - 1))

/-- **Bridge `MinExp → Min`.** Re-key the exponent-keyed shape at
`hpow.α` / `hpow.β` back to the `hpow`-keyed shape. Definitional: the
two struct bodies coincide after `αExp = hpow.α`, `βExp = hpow.β`. -/
theorem PaperSection8SegmentResiduesMin.ofExp
    {d : ℕ}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (h : PaperSection8SegmentResiduesMinExp
          (d := d) γBarReal βBarReal βBarReal' γBarReal' hpow.α hpow.β) :
    PaperSection8SegmentResiduesMin
      (d := d) γBarReal βBarReal βBarReal' γBarReal' H DpH hpow :=
  ⟨h.out⟩

/-- **Bridge `Min → MinExp`.** Re-key the `hpow`-keyed shape to the
exponent-keyed shape at `hpow.α` / `hpow.β`. Definitional inverse of
`ofExp`. -/
theorem PaperSection8SegmentResiduesMin.toExp
    {d : ℕ}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH}
    (h : PaperSection8SegmentResiduesMin
          (d := d) γBarReal βBarReal βBarReal' γBarReal' H DpH hpow) :
    PaperSection8SegmentResiduesMinExp
      (d := d) γBarReal βBarReal βBarReal' γBarReal' hpow.α hpow.β :=
  ⟨h.out⟩

/-! ### Paper-faithful sibling: `PaperSection8AnalyticResiduesMin`

Sibling of `PaperSection8AnalyticResidues` whose only difference is
that the over-specified 13-conjunct segment-residue field `hSegRes` is
replaced by the paper-faithful 11-conjunct
`PaperSection8SegmentResiduesMin` (field `hSegMin`). All other 12
fields retain their existing types.

Placed after `PaperSection8SegmentResiduesMin` and its `ofFull` adapter
so that the `hSegMin` field type is in scope. The forward adapter
`PaperSection8AnalyticResidues.toMin` (immediately below this struct)
lets legacy callers that produce the full 13-conjunct bundle continue
to feed downstream consumers that now take the minimal 11-conjunct
bundle. -/

/-- **Paper-faithful sibling of `PaperSection8AnalyticResidues`.**

Identical to `PaperSection8AnalyticResidues` modulo replacing the single
13-conjunct field `hSegRes` with the 11-conjunct paper-faithful
`hSegMin : PaperSection8SegmentResiduesMin`. All other 12 fields are
verbatim copies.

This is the bundle consumed by the active Theorem 1 / `paperSolFor`
path via `aepsiUniformContextK_of_paperHypotheses_closed_paper_min`. -/
structure PaperSection8AnalyticResiduesMin
    {d : ℕ}
    (γBarReal βBarReal βBarReal' γBarReal' : ℝ)
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (ε : ℝ)
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH) where
  /-- Paper-line-944 general upper bound (Hyp-A `(a:H)`). -/
  h_upper :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      ∀ p mm, 0 < mm →
        H x p mm ≤ hpow.C * (‖p‖ ^ hpow.α + 1) - (mm ^ hpow.β) / hpow.C
  /-- HJB-flux measurability (universal-`q` form). -/
  hF_HJB_meas :
    ∀ q : XBanach d βBarReal γBarReal,
      AEStronglyMeasurable
        (fun x => -(uOf q x) - H x (fun i => DuOf q i x) (mOf q x) + V x)
        (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d))
  /-- Flux measurability (universal-`q` form). -/
  hF_flux_meas :
    ∀ q : XBanach d βBarReal γBarReal, ∀ i,
      AEStronglyMeasurable
        (fun x => mOf q x * DpH x (fun j => DuOf q j x) (mOf q x) i)
        (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d))
  /-- Scalar monotonicity for `absPowMinusTwo γBarReal`. -/
  hScalarMono :
    ∀ s t : ℝ,
      0 ≤ (absPowMinusTwo γBarReal t * t - absPowMinusTwo γBarReal s * s)
            * (t - s)
  /-- Vector monotonicity for `vecAbsPowMinusTwo γBarReal`. -/
  hVecMono :
    ∀ v w : Fin d → ℝ,
      0 ≤ (vecAbsPowMinusTwo γBarReal v • v - vecAbsPowMinusTwo γBarReal w • w)
            ⬝ (v - w)
  /-- Scaled-gauge coercivity scaling (paper line 982, `λ > 0`). -/
  lamCoerc : ℝ
  /-- Positivity of the scaled-gauge scaling. -/
  hlamCoerc : 0 < lamCoerc
  /-- Coercivity constant (paper line 982). -/
  Ccoerc : ℝ
  /-- Scaled-gauge coercivity bound on the cobounded × principal `K_Aepsi`
  filter. The gauge exponent is `coercivityGaugeExponent βBarReal γBarReal
  = min β̄ γ̄` (not bare `γBarReal`): see the docstring of
  `coercivityGaugeExponent` for the rationale (Path B fix, iter 0644+). -/
  hbound_residue :
    ∀ᶠ v in (Bornology.cobounded (XBanach d βBarReal γBarReal)
                ⊓ Filter.principal (K_Aepsi d βBarReal γBarReal)),
      lamCoerc * aepsiCoerciveGauge (βBarReal := βBarReal) (γBarReal := γBarReal)
          (coercivityGaugeExponent βBarReal γBarReal) v - Ccoerc ≤
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
            γBarReal ε (fun i => ⇑(v.2.2 i)) (⇑v.1) (⇑v.2.1)
            (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1)
          - mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε (fun _ _ => 0) (fun _ => 1) (fun _ => 0)
              (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1)
  /-- Hemicontinuity slice bound (paper §8 hemicontinuity). -/
  h_slice :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
      ∀ p m, 0 < m →
        H x p m ≤ -(m ^ hpow.β) / hpow.C + hpow.C + hpow.C * ‖p‖ ^ hpow.α
                + hpow.C * ‖p‖ * (m ^ (hpow.β - hpow.β / hpow.α) + 1)
  /-- Paper-faithful 11-conjunct segment integrand bundle. Replaces the
  legacy 13-conjunct `hSegRes` field of `PaperSection8AnalyticResidues`. -/
  hSegMin : PaperSection8SegmentResiduesMin
              (d := d) γBarReal βBarReal βBarReal' γBarReal' H DpH hpow
  /-- Unregularised segment-integrand measurability. -/
  hF_unreg_meas : ∀ (u v : XBanach d βBarReal γBarReal),
              u ∈ K_Aepsi d βBarReal γBarReal →
              v ∈ K_Aepsi d βBarReal γBarReal →
              ∀ (w : XBanach d βBarReal γBarReal),
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x => aepsiIntegrandAt_unreg V H DpH
                    (DuOf v) (DuOf u) (mOf v) (mOf u)
                    (uOf v) (uOf u)
                    (fun i => ⇑(w.2.2 i)) (⇑w.1) (⇑w.2.1) x t)
        (MeasureTheory.volume.restrict (UnitCube d))
  /-- Gateaux segment-integrand measurability. -/
  hF_gat_meas : ∀ (u v : XBanach d βBarReal γBarReal),
              u ∈ K_Aepsi d βBarReal γBarReal →
              v ∈ K_Aepsi d βBarReal γBarReal →
              ∀ (w : XBanach d βBarReal γBarReal),
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x => aepsiIntegrandAt_gateaux γBarReal
                    (DuOf v) (DuOf u) (uOf v) (uOf u)
                    (fun i => ⇑(w.2.2 i)) (⇑w.2.1) x t)
        (MeasureTheory.volume.restrict (UnitCube d))
  /-- `K0` supplier residue (`MFGOpEpsAuxHyps` on `K0_Aepsi`). -/
  auxHypsK0 : ∀ q ∈ K0_Aepsi d βBarReal γBarReal,
                MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                  V H DpH (DuOf q) (mOf q) (uOf q)
  /-- Per-`K0_Aepsi_W` weak-derivative tie (refined cone, iter post-0707). -/
  hWeakDerivK0 :
    ∀ q ∈ K0_Aepsi_W d βBarReal γBarReal,
      ∀ i, HasWeakDerivPer (d := d) i (uOf q) (DuOf q i)

/-- **Forward adapter: legacy → minimal analytic bundle.**

Project a `PaperSection8AnalyticResidues` (legacy 13-conjunct `hSegRes`)
to the paper-faithful `PaperSection8AnalyticResiduesMin` (11-conjunct
`hSegMin`). All 12 surviving fields project verbatim; `hSegMin` is
produced via `PaperSection8SegmentResiduesMin.ofFull`. -/
noncomputable def PaperSection8AnalyticResidues.toMin
    {d : ℕ}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {ε : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {hpow : Hamiltonian.HypothesisPowerGrowth H DpH}
    (h : PaperSection8AnalyticResidues
          (d := d) γBarReal βBarReal βBarReal' γBarReal'
          ε V H DpH hpow) :
    PaperSection8AnalyticResiduesMin
      (d := d) γBarReal βBarReal βBarReal' γBarReal'
      ε V H DpH hpow where
  h_upper := h.h_upper
  hF_HJB_meas := h.hF_HJB_meas
  hF_flux_meas := h.hF_flux_meas
  hScalarMono := h.hScalarMono
  hVecMono := h.hVecMono
  lamCoerc := h.lamCoerc
  hlamCoerc := h.hlamCoerc
  Ccoerc := h.Ccoerc
  hbound_residue := h.hbound_residue
  h_slice := h.h_slice
  hSegMin := PaperSection8SegmentResiduesMin.ofFull h
  hF_unreg_meas := h.hF_unreg_meas
  hF_gat_meas := h.hF_gat_meas
  auxHypsK0 := h.auxHypsK0
  hWeakDerivK0 := h.hWeakDerivK0

/-! ## Producer for `PaperSection8SegmentResiduesMin` from `hpow`

The producer `paperSection8_segmentResiduesMin_of_paperHypotheses` builds
the 11-conjunct paper-faithful minimal segment-residue bundle from `hpow`
alone, **without** any non-paper side conditions (in particular, neither
`β ≤ α` nor `1 ≤ β`). The corresponding legacy 13-conjunct producer
required those two side conditions only for the two over-specified
conjuncts that the `_min` shape drops.

Each surviving conjunct is discharged by reducing to one of the existing
dominator lemmas in `Hamiltonian/Estimates.lean`, using only paper-faithful
exponent facts (`betaBar'_le_gammaBar` and `gammaBar'_le_betaBar`).

The three private helpers `memLpPer_abs_add_abs`, `memLpPer_pi_of_coord_local`,
and `holderTriple_betaBar_gammaBarOverAlphaMinus1_gammaBar_local` are
restored verbatim from the iter-0606 producer (commit `a190e09`). -/

-- Adapted from internal `hSum` step of
-- `Hamiltonian.g_dominator_memLp_betaBar'` (iter 0606, commit a190e09).
/-- **Helper:** if `f, g ∈ MemLpPer p`, then `|f| + |g| ∈ MemLpPer p`. -/
private lemma memLpPer_abs_add_abs
    {d : ℕ} {p : ℝ≥0∞} {f g : (Fin d → ℝ) → ℝ}
    (hf : MemLpPer (d := d) p f) (hg : MemLpPer (d := d) p g) :
    MemLpPer (d := d) p (fun x => |f x| + |g x|) := by
  have hfabs : MemLpPer (d := d) p (fun x => |f x|) := by
    have := hf.toMemLp.norm
    have heq : (fun x => ‖f x‖) = fun x => |f x| := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at this
    exact MemLp.toMemLpPer this
  have hgabs : MemLpPer (d := d) p (fun x => |g x|) := by
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

-- Adapted from `Hamiltonian.Estimates.memLpPer_pi_of_coord`
-- (iter 0606, commit a190e09).
/-- **Helper:** the vector-valued promotion of a family of MemLpPer functions.
If each coordinate `Dυ i ∈ MemLpPer p`, then `x ↦ fun i => Dυ i x ∈ MemLpPer p`
(as a `Fin d → ℝ`-valued function). -/
private lemma memLpPer_pi_of_coord_local
    {d : ℕ} {p : ℝ≥0∞} (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (hDυ : ∀ i, MemLpPer (d := d) p (Dυ i)) :
    MemLpPer (d := d) p
      (fun x : (Fin d → ℝ) => fun i : Fin d => Dυ i x) := by
  haveI : IsFiniteMeasure
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube (d := d))) :=
    ⟨by
      rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ]
      simp⟩
  set Dom : (Fin d → ℝ) → ℝ := fun x => ∑ i : Fin d, |Dυ i x| with hDom_def
  have habs_memLp : ∀ i, MemLpPer (d := d) p (fun x => |Dυ i x|) := by
    intro i
    have h := (hDυ i).toMemLp.norm
    have heq : (fun x => ‖Dυ i x‖) = fun x => |Dυ i x| := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at h
    exact MemLp.toMemLpPer h
  have hDom_memLp : MemLpPer (d := d) p Dom := by
    have hsum :
        MeasureTheory.MemLp
          (fun x => ∑ i : Fin d, (fun x => |Dυ i x|) x) p
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
      memLp_finset_sum (Finset.univ : Finset (Fin d))
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

-- Adapted from `Hamiltonian.Estimates.holderTriple_betaBar_gammaBarOverAlphaMinus1_gammaBar'`
-- (iter 0606, commit a190e09).
/-- **Helper:** Hölder triple `(β+1, γ̄/(α-1), γ̄')` for `α > 1, β > 0`. -/
private theorem holderTriple_betaBar_gammaBarOverAlphaMinus1_gammaBar_local
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

/-- **`PaperSection8SegmentResiduesMin` producer from `hpow`.**

Build the 11-conjunct paper-faithful minimal segment-residue bundle from
`hpow` alone, with **no** non-paper side conditions. The corresponding
legacy 13-conjunct producer required `β ≤ α` and `1 ≤ β` only for the
two over-specified conjuncts (legacy h3 and h11) that the `_min` shape
drops. The 11 surviving conjuncts are discharged by reductions to the
four dominator lemmas in `Hamiltonian/Estimates.lean`
(`g_dominator_memLp_betaBar'`, `flux_dominator_memLp_gammaBar'`,
`G_grad_memLpPer_gammaBar'`, `G_val_memLpPer_gammaBar'`) applied to the
summed-abs quantities at the endpoints.

The `out` field unpacks to the 11 conjuncts in their `_min`-struct order,
matching the consumer chain in `Aepsi_hemicont_of_paperHypotheses_min`. -/
theorem paperSection8_segmentResiduesMin_of_paperHypotheses
    {d : ℕ}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (hβBar_eq : βBarReal = hpow.β + 1)
    (hγBar_eq : γBarReal = hpow.α * (hpow.β + 1) / hpow.β)
    (hβBar'_eq : βBarReal' = (hpow.β + 1) / hpow.β)
    (hγBar'_eq : γBarReal' = γBarReal / (γBarReal - 1)) :
    PaperSection8SegmentResiduesMin
      (d := d) γBarReal βBarReal βBarReal' γBarReal' H DpH hpow := by
  -- Standing positivity facts.
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
  haveI : IsFiniteMeasure
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube (d := d))) :=
    ⟨by
      rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ]
      simp⟩
  refine ⟨?_⟩
  intro u v _hu_K _hv_K w
  -- `MemLpPer` certificates from the Lp components of `u`, `v`, `w`.
  have hmLp_u : MemLpPer (d := d) (ENNReal.ofReal βBarReal) (mOf u) :=
    memLpPer_of_lpPer (d := d) u.1
  have hmLp_v : MemLpPer (d := d) (ENNReal.ofReal βBarReal) (mOf v) :=
    memLpPer_of_lpPer (d := d) v.1
  have huLp_u : MemLpPer (d := d) (ENNReal.ofReal γBarReal) (uOf u) :=
    memLpPer_of_lpPer (d := d) u.2.1
  have huLp_v : MemLpPer (d := d) (ENNReal.ofReal γBarReal) (uOf v) :=
    memLpPer_of_lpPer (d := d) v.2.1
  have hDuLp_u : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (DuOf u i) := by
    intro i; exact memLpPer_of_lpPer (d := d) (u.2.2 i)
  have hDuLp_v : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (DuOf v i) := by
    intro i; exact memLpPer_of_lpPer (d := d) (v.2.2 i)
  -- `MemLpPer` certificates from the Lp components of `w`.
  have hmLp_w : MemLpPer (d := d) (ENNReal.ofReal βBarReal) (⇑w.1) :=
    memLpPer_of_lpPer (d := d) w.1
  have huLp_w : MemLpPer (d := d) (ENNReal.ofReal γBarReal) (⇑w.2.1) :=
    memLpPer_of_lpPer (d := d) w.2.1
  have hDuLp_w : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (⇑(w.2.2 i)) := by
    intro i; exact memLpPer_of_lpPer (d := d) (w.2.2 i)
  -- Notation for the ENNReal exponents.
  set βBarE : ℝ≥0∞ := ENNReal.ofReal βBarReal with hβBarE_def
  set γBarE : ℝ≥0∞ := ENNReal.ofReal γBarReal with hγBarE_def
  set βBar'E : ℝ≥0∞ := ENNReal.ofReal βBarReal' with hβBar'E_def
  set γBar'E : ℝ≥0∞ := ENNReal.ofReal γBarReal' with hγBar'E_def
  -- Auxiliary summed-abs functions.
  set μSum : (Fin d → ℝ) → ℝ := fun x => |mOf u x| + |mOf v x| with hμSum_def
  set υSum : (Fin d → ℝ) → ℝ := fun x => |uOf u x| + |uOf v x| with hυSum_def
  set DυSum : Fin d → (Fin d → ℝ) → ℝ :=
    fun i x => |DuOf u i x| + |DuOf v i x| with hDυSum_def
  -- `μSum ∈ MemLpPer βBarE`.
  have hμSum_β : MemLpPer (d := d) βBarE μSum := by
    rw [hβBarE_def, hμSum_def]
    exact memLpPer_abs_add_abs hmLp_u hmLp_v
  -- `υSum ∈ MemLpPer γBarE`.
  have hυSum_γ : MemLpPer (d := d) γBarE υSum := by
    rw [hγBarE_def, hυSum_def]
    exact memLpPer_abs_add_abs huLp_u huLp_v
  -- `DυSum i ∈ MemLpPer γBarE` for each `i`.
  have hDυSum_γ : ∀ i, MemLpPer (d := d) γBarE (DυSum i) := by
    intro i
    rw [hγBarE_def, hDυSum_def]
    exact memLpPer_abs_add_abs (hDuLp_u i) (hDuLp_v i)
  -- Restate `μSum` at the paper exponent `β + 1`.
  have hμSum_paperβ :
      MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1)) μSum := by
    rw [← hβBar_eq]; exact hμSum_β
  -- Constants 1 helpers.
  have hone_β' : MemLpPer (d := d) βBar'E (fun _ : (Fin d → ℝ) => (1 : ℝ)) :=
    MemLp.toMemLpPer (MeasureTheory.memLp_const (1 : ℝ))
  -- Paper-faithful standing fact: `βBarReal' ≤ γBarReal` (paper `eq:gamma`).
  have hβ'_le_γ_real : βBarReal' ≤ γBarReal := by
    rw [hβBar'_eq, hγBar_eq]
    have h := Hamiltonian.betaBar'_le_gammaBar (hpow.hα.le) hβ_pos
    simp only [Hamiltonian.betaBar', Hamiltonian.gammaBar] at h
    exact h
  have hβ'_le_γ : βBar'E ≤ γBarE := by
    rw [hβBar'E_def, hγBarE_def]
    exact ENNReal.ofReal_le_ofReal hβ'_le_γ_real
  have hγTop : γBarE ≠ ⊤ := by rw [hγBarE_def]; exact ENNReal.ofReal_ne_top
  -- Paper-faithful standing fact: `γBarReal' ≤ βBarReal` (paper `eq:gamma`).
  have hγ'_le_β_real : γBarReal' ≤ βBarReal := by
    rw [hγBar'_eq, hγBar_eq, hβBar_eq]
    have h := Hamiltonian.gammaBar'_le_betaBar hpow.hα hβ_pos
    exact h
  have hγ'_le_β : γBar'E ≤ βBarE := by
    rw [hγBar'E_def, hβBarE_def]
    exact ENNReal.ofReal_le_ofReal hγ'_le_β_real
  have hβTop : βBarE ≠ ⊤ := by rw [hβBarE_def]; exact ENNReal.ofReal_ne_top
  -- Note: `hγBar'_eq` already a paper-exponent identity; derive a real
  -- exponent identity restated at the paper exponents.
  have hγ'_paper_eq : γBarReal' =
      hpow.α * (hpow.β + 1) / hpow.β /
        (hpow.α * (hpow.β + 1) / hpow.β - 1) := by
    rw [hγBar'_eq, hγBar_eq]
  -- The conjunct assembly proper (11 conjuncts in `_min`-struct order).
  refine ⟨hmLp_w, hDuLp_w, huLp_w, ?h4, ?h5, ?h6, ?h7, ?h8, ?h9, ?h10, ?h11⟩
  -- (4) MemLpPer βBar' (|uOf u| + |uOf v|).
  case h4 =>
    exact MemLpPer.mono_exponent_finite hβ'_le_γ hγTop hυSum_γ
  -- (5) MemLpPer βBar' (‖DυSum ·‖^α + 1).
  -- Adapted from the `hT_Du` step of `Hamiltonian.g_dominator_memLp_betaBar'`.
  case h5 =>
    -- Vector-valued `DυSum_vec ∈ L^{γBar}` via the helper `memLpPer_pi_of_coord_local`.
    have hDυSum_vec :
        MemLpPer (d := d) γBarE
          (fun x : (Fin d → ℝ) => fun j : Fin d => DυSum j x) :=
      memLpPer_pi_of_coord_local (p := γBarE) DυSum hDυSum_γ
    set qE : ℝ≥0∞ := ENNReal.ofReal hpow.α with hqE_def
    have hqE_toReal : qE.toReal = hpow.α := by
      rw [hqE_def]; exact ENNReal.toReal_ofReal hα_pos.le
    have hT_a :
        MemLp (fun x : (Fin d → ℝ) =>
                ‖(fun j : Fin d => DυSum j x)‖ ^ qE.toReal)
              (γBarE / qE)
              (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
      MeasureTheory.MemLp.norm_rpow_div hDυSum_vec.toMemLp qE
    -- Identify `γBarE / qE = βBar'E` (paper key identity `γ̄/α = β̄'`).
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
        MemLpPer (d := d) βBar'E
          (fun x : (Fin d → ℝ) =>
            ‖fun j => |DuOf u j x| + |DuOf v j x|‖ ^ hpow.α) := by
      have := MemLp.toMemLpPer hT_a
      rw [hdiv] at this
      exact this
    -- Add `1`.
    have hsum := hT_b.add hone_β'
    have heqf :
        ((fun x : (Fin d → ℝ) =>
          ‖fun j => |DuOf u j x| + |DuOf v j x|‖ ^ hpow.α)
          + (fun _ : (Fin d → ℝ) => (1 : ℝ)))
        = (fun x : (Fin d → ℝ) =>
          ‖fun j => |DuOf u j x| + |DuOf v j x|‖ ^ hpow.α + 1) := by
      funext x; simp [Pi.add_apply]
    rw [heqf] at hsum
    exact hsum
  -- (6) MemLpPer βBar' ((μSum)^β + 1).
  -- Adapted from the `hT_mb` step of `g_dominator_memLp_betaBar'`.
  case h6 =>
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
    -- Identify `βBarE / qE = βBar'E`.
    have hdiv : βBarE / qE = βBar'E := by
      rw [hβBarE_def, hqE_def, hβBar'E_def, hβBar_eq, hβBar'_eq,
        ← ENNReal.ofReal_div_of_pos hβ_pos]
    have heq :
        (fun x : (Fin d → ℝ) => |μSum x| ^ qE.toReal)
        = (fun x : (Fin d → ℝ) => |μSum x| ^ hpow.β) := by
      funext x; rw [hqE_toReal]
    rw [heq] at hT_a
    -- Convert to `MemLpPer βBar'E (fun x => |μSum x|^β)`.
    have hT_b : MemLpPer (d := d) βBar'E
        (fun x : (Fin d → ℝ) => |μSum x| ^ hpow.β) := by
      have := MemLp.toMemLpPer hT_a
      rw [hdiv] at this
      exact this
    -- Bound `μSum^β` by `|μSum|^β` (μSum ≥ 0, so they're equal).
    have hμSum_nn : ∀ x, 0 ≤ μSum x := fun x => by
      rw [hμSum_def]; exact add_nonneg (abs_nonneg _) (abs_nonneg _)
    have hT_c : MemLpPer (d := d) βBar'E
        (fun x : (Fin d → ℝ) => μSum x ^ hpow.β) := by
      have heq : (fun x : (Fin d → ℝ) => μSum x ^ hpow.β)
                = (fun x : (Fin d → ℝ) => |μSum x| ^ hpow.β) := by
        funext x; rw [abs_of_nonneg (hμSum_nn x)]
      rw [heq]; exact hT_b
    -- Add `1`.
    have hsum := hT_c.add hone_β'
    have heqf :
        ((fun x : (Fin d → ℝ) => μSum x ^ hpow.β)
          + (fun _ : (Fin d → ℝ) => (1 : ℝ)))
        = (fun x : (Fin d → ℝ) => (|mOf u x| + |mOf v x|) ^ hpow.β + 1) := by
      funext x; simp [Pi.add_apply, hμSum_def]
    rw [heqf] at hsum
    exact hsum
  -- (7) MemLpPer γBar' (μSum * ‖DυSum ·‖^(α-1)).
  -- Adapted from the `hT1` step of `flux_dominator_memLp_gammaBar'`.
  case h7 =>
    -- Vector-valued `DυSum_vec ∈ L^{γBar}`.
    have hDυSum_vec :
        MemLpPer (d := d) γBarE
          (fun x : (Fin d → ℝ) => fun j : Fin d => DυSum j x) :=
      memLpPer_pi_of_coord_local (p := γBarE) DυSum hDυSum_γ
    set qE : ℝ≥0∞ := ENNReal.ofReal (hpow.α - 1) with hqE_def
    have hqE_toReal : qE.toReal = hpow.α - 1 := by
      rw [hqE_def]; exact ENNReal.toReal_ofReal hαm1_pos.le
    have hT1a :
        MeasureTheory.MemLp (fun x : (Fin d → ℝ) =>
                ‖(fun j : Fin d => DυSum j x)‖ ^ qE.toReal)
              (γBarE / qE)
              (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
      MeasureTheory.MemLp.norm_rpow_div hDυSum_vec.toMemLp qE
    -- Identify `γBarE / qE = ENNReal.ofReal (α(β+1)/β/(α-1))`.
    have hdiv :
        γBarE / qE = ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β / (hpow.α - 1)) := by
      rw [hγBarE_def, hqE_def, hγBar_eq, ← ENNReal.ofReal_div_of_pos hαm1_pos]
    have heq :
        (fun x : (Fin d → ℝ) =>
          ‖(fun j : Fin d => DυSum j x)‖ ^ qE.toReal)
        = (fun x : (Fin d → ℝ) =>
          ‖fun j : Fin d => |DuOf u j x| + |DuOf v j x|‖ ^ (hpow.α - 1)) := by
      funext x; rw [hqE_toReal]
    rw [heq] at hT1a
    have hT1b :
        MemLpPer (d := d)
          (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β / (hpow.α - 1)))
          (fun x : (Fin d → ℝ) =>
            ‖fun j : Fin d => |DuOf u j x| + |DuOf v j x|‖ ^ (hpow.α - 1)) := by
      have := MemLp.toMemLpPer hT1a
      rw [hdiv] at this
      exact this
    -- Hölder real triple `(β+1, α(β+1)/β/(α-1), α(β+1)/β/(α(β+1)/β - 1))`.
    have hHT_real :
        Real.HolderTriple (hpow.β + 1)
          (hpow.α * (hpow.β + 1) / hpow.β / (hpow.α - 1))
          (hpow.α * (hpow.β + 1) / hpow.β /
              (hpow.α * (hpow.β + 1) / hpow.β - 1)) :=
      holderTriple_betaBar_gammaBarOverAlphaMinus1_gammaBar_local
        hpow.hα hpow.hβ
    haveI hHT_enn :
        ENNReal.HolderTriple (ENNReal.ofReal (hpow.β + 1))
          (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β / (hpow.α - 1)))
          (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β /
              (hpow.α * (hpow.β + 1) / hpow.β - 1))) :=
      hHT_real.ennrealOfReal
    -- Apply Hölder with μSum at β+1 first and hT1b at γ̄/(α-1) second.
    have hT1c :
        MeasureTheory.MemLp
          (fun x : (Fin d → ℝ) =>
            μSum x * ‖fun j => |DuOf u j x| + |DuOf v j x|‖ ^ (hpow.α - 1))
          (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β /
              (hpow.α * (hpow.β + 1) / hpow.β - 1)))
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
      (hμSum_paperβ.toMemLp.fun_mul hT1b.toMemLp : _)
    have hres :
        MemLpPer (d := d)
          (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β /
              (hpow.α * (hpow.β + 1) / hpow.β - 1)))
          (fun x : (Fin d → ℝ) =>
            (|mOf u x| + |mOf v x|) *
              ‖fun j => |DuOf u j x| + |DuOf v j x|‖ ^ (hpow.α - 1)) := by
      have := MemLp.toMemLpPer hT1c
      -- `μSum x = |mOf u x| + |mOf v x|`, definitional.
      convert this using 1
    -- Now restate at `γBar'E`.
    have hexp_eq : γBar'E =
        ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β /
            (hpow.α * (hpow.β + 1) / hpow.β - 1)) := by
      rw [hγBar'E_def, hγ'_paper_eq]
    rw [hexp_eq]; exact hres
  -- (8) MemLpPer γBar' (μSum ^ (1 + β - β/α)).
  -- Adapted from the `hT2` step of `flux_dominator_memLp_gammaBar'`.
  case h8 =>
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
    -- Identify `(β+1) / (β+1 - β/α) = γ̄/(γ̄-1) = γ̄'` at paper exponents.
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
        MemLpPer (d := d) γBar'E
          (fun x : (Fin d → ℝ) => |μSum x| ^ (hpow.β + 1 - hpow.β / hpow.α)) := by
      have := MemLp.toMemLpPer hT2a
      rw [hdiv_eq] at this
      exact this
    -- Pointwise bound: `‖μSum x ^ (1+β-β/α)‖ ≤ 1 * ‖|μSum x|^(β+1 - β/α)‖`.
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
        MemLpPer (d := d) γBar'E
          (fun x : (Fin d → ℝ) => μSum x ^ (1 + hpow.β - hpow.β / hpow.α)) :=
      MemLp.toMemLpPer (MeasureTheory.MemLp.of_le_mul hT2b.toMemLp hmeas hbound)
    -- Restate target as `(|mOf u x| + |mOf v x|) ^ (1 + β - β/α)` (μSum unfolds).
    convert hT2c using 1
  -- (9) MemLpPer γBar' (μSum).
  -- Use mono_exponent from βBar to γBar' (since γBar' ≤ βBar).
  case h9 =>
    have hT10 : MemLpPer (d := d) γBar'E μSum :=
      MemLpPer.mono_exponent_finite hγ'_le_β hβTop hμSum_β
    convert hT10 using 1
  -- (10) MemLpPer γBar' ((∑ i, (DυSum i x)^2)^((γBar-1)/2)).
  case h10 =>
    -- Route: each `(DυSum i x)^2 ∈ L^(γBar/2)` via `MemLp.norm_rpow_div` at
    -- exponent 2. Sum closure gives `∑ i, (DυSum i x)^2 ∈ L^(γBar/2)`. Then
    -- raising to `(γBar-1)/2` gives exponent `(γBar/2)/((γBar-1)/2) = γBar/(γBar-1) = γBar'`.
    set q2E : ℝ≥0∞ := (2 : ℝ≥0∞) with hq2E_def
    have hq2E_top : q2E ≠ ⊤ := by rw [hq2E_def]; decide
    have hq2E_toReal : q2E.toReal = 2 := by rw [hq2E_def]; rfl
    have hSq_each : ∀ i,
        MeasureTheory.MemLp
          (fun x : (Fin d → ℝ) => ‖DυSum i x‖ ^ q2E.toReal)
          (γBarE / q2E)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
      fun i => MeasureTheory.MemLp.norm_rpow_div (hDυSum_γ i).toMemLp q2E
    -- Convert from `‖·‖^2` to `·^2` (via `Real.norm_eq_abs` and `|x|^2 = x^2`).
    have hSq_each' : ∀ i,
        MemLpPer (d := d) (γBarE / q2E)
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
    -- Sum closure: `∑ i, (DυSum i x)^2 ∈ L^(γBar/2)`.
    have hSumSq :
        MemLpPer (d := d) (γBarE / q2E)
          (fun x : (Fin d → ℝ) => ∑ i, (DυSum i x) ^ (2 : ℕ)) := by
      have hsum : MeasureTheory.MemLp
          (fun x : (Fin d → ℝ) => ∑ i : Fin d, (fun x => (DυSum i x) ^ (2 : ℕ)) x)
          (γBarE / q2E)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
        refine memLp_finset_sum (Finset.univ : Finset (Fin d)) ?_
        intro i _; exact (hSq_each' i).toMemLp
      exact MemLp.toMemLpPer hsum
    -- Raise to `(γBar-1)/2` via `MemLp.norm_rpow_div`.
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
    -- Identify `(γBar/2)/((γ-1)/2) = γ/(γ-1) = γBar'`.
    have hdiv_eq : (γBarE / q2E) / qE = γBar'E := by
      rw [hq2E_def, hqE_def, hγBarE_def, hγBar'E_def, hγBar'_eq,
          ← ENNReal.ofReal_ofNat (n := 2),
          ← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
          ← ENNReal.ofReal_div_of_pos hexp12_pos]
      congr 1
      have hγne : γBarReal ≠ 0 := hγBarReal_pos.ne'
      have hγm1ne : γBarReal - 1 ≠ 0 := hγm1_pos.ne'
      field_simp
    -- `∑ i, (DυSum i x)^2 ≥ 0` so `‖·‖ = ·`.
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
        MemLpPer (d := d) γBar'E
          (fun x : (Fin d → ℝ) =>
            (∑ i, (DυSum i x) ^ (2 : ℕ)) ^ ((γBarReal - 1) / 2)) := by
      have := MemLp.toMemLpPer hRpow
      rw [hdiv_eq] at this
      exact this
    convert hres using 1
  -- (11) MemLpPer γBar' (υSum ^ (γBar - 1)).
  case h11 =>
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
    have hres : MemLpPer (d := d) γBar'E
        (fun x : (Fin d → ℝ) => υSum x ^ (γBarReal - 1)) := by
      have := MemLp.toMemLpPer hRpow
      rw [hdiv] at this
      exact this
    convert hres using 1

/-- **`PaperSection8SegmentResiduesMinExp` producer from bare exponents.**

Verbatim copy of `paperSection8_segmentResiduesMin_of_paperHypotheses`
with `hpow.α ↦ αExp`, `hpow.β ↦ βExp`, `hpow.hα ↦ hαExp`,
`hpow.hβ ↦ hβExp`, and the `hpow` parameter dropped. The producer takes
the exponents and their positivity directly (the AE route instantiates
them at `hweak.α` / `hweak.β`), so no `HypothesisPowerGrowth` term
appears in the hypotheses. -/
theorem paperSection8_segmentResiduesMinExp_of_exponents
    {d : ℕ}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (αExp βExp : ℝ) (hαExp : 1 < αExp) (hβExp : 0 < βExp)
    (hβBar_eq : βBarReal = βExp + 1)
    (hγBar_eq : γBarReal = αExp * (βExp + 1) / βExp)
    (hβBar'_eq : βBarReal' = (βExp + 1) / βExp)
    (hγBar'_eq : γBarReal' = γBarReal / (γBarReal - 1)) :
    PaperSection8SegmentResiduesMinExp
      (d := d) γBarReal βBarReal βBarReal' γBarReal' αExp βExp := by
  -- Standing positivity facts.
  have hα_pos : 0 < αExp := lt_trans Real.zero_lt_one hαExp
  have hβ_pos : 0 < βExp := hβExp
  have hβ1_pos : 0 < βExp + 1 := by linarith
  have hαm1_pos : 0 < αExp - 1 := by linarith [hαExp]
  have hβBarReal_pos : 0 < βBarReal := by rw [hβBar_eq]; exact hβ1_pos
  have hγBarReal_pos : 0 < γBarReal := by
    rw [hγBar_eq]
    exact div_pos (mul_pos hα_pos hβ1_pos) hβ_pos
  have hγBar_one_lt_real : 1 < γBarReal := by
    rw [hγBar_eq]; rw [lt_div_iff₀ hβ_pos, one_mul]
    have : (βExp + 1) < αExp * (βExp + 1) := by
      have : (1 : ℝ) * (βExp + 1) < αExp * (βExp + 1) :=
        mul_lt_mul_of_pos_right hαExp hβ1_pos
      simpa using this
    linarith
  have hβBarReal'_pos : 0 < βBarReal' := by
    rw [hβBar'_eq]; exact div_pos hβ1_pos hβ_pos
  have hγBarReal'_pos : 0 < γBarReal' := by
    rw [hγBar'_eq]; exact div_pos hγBarReal_pos (by linarith)
  -- Finite-measure instance on the unit cube.
  haveI : IsFiniteMeasure
      (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube (d := d))) :=
    ⟨by
      rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ]
      simp⟩
  refine ⟨?_⟩
  intro u v _hu_K _hv_K w
  -- `MemLpPer` certificates from the Lp components of `u`, `v`, `w`.
  have hmLp_u : MemLpPer (d := d) (ENNReal.ofReal βBarReal) (mOf u) :=
    memLpPer_of_lpPer (d := d) u.1
  have hmLp_v : MemLpPer (d := d) (ENNReal.ofReal βBarReal) (mOf v) :=
    memLpPer_of_lpPer (d := d) v.1
  have huLp_u : MemLpPer (d := d) (ENNReal.ofReal γBarReal) (uOf u) :=
    memLpPer_of_lpPer (d := d) u.2.1
  have huLp_v : MemLpPer (d := d) (ENNReal.ofReal γBarReal) (uOf v) :=
    memLpPer_of_lpPer (d := d) v.2.1
  have hDuLp_u : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (DuOf u i) := by
    intro i; exact memLpPer_of_lpPer (d := d) (u.2.2 i)
  have hDuLp_v : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (DuOf v i) := by
    intro i; exact memLpPer_of_lpPer (d := d) (v.2.2 i)
  -- `MemLpPer` certificates from the Lp components of `w`.
  have hmLp_w : MemLpPer (d := d) (ENNReal.ofReal βBarReal) (⇑w.1) :=
    memLpPer_of_lpPer (d := d) w.1
  have huLp_w : MemLpPer (d := d) (ENNReal.ofReal γBarReal) (⇑w.2.1) :=
    memLpPer_of_lpPer (d := d) w.2.1
  have hDuLp_w : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (⇑(w.2.2 i)) := by
    intro i; exact memLpPer_of_lpPer (d := d) (w.2.2 i)
  -- Notation for the ENNReal exponents.
  set βBarE : ℝ≥0∞ := ENNReal.ofReal βBarReal with hβBarE_def
  set γBarE : ℝ≥0∞ := ENNReal.ofReal γBarReal with hγBarE_def
  set βBar'E : ℝ≥0∞ := ENNReal.ofReal βBarReal' with hβBar'E_def
  set γBar'E : ℝ≥0∞ := ENNReal.ofReal γBarReal' with hγBar'E_def
  -- Auxiliary summed-abs functions.
  set μSum : (Fin d → ℝ) → ℝ := fun x => |mOf u x| + |mOf v x| with hμSum_def
  set υSum : (Fin d → ℝ) → ℝ := fun x => |uOf u x| + |uOf v x| with hυSum_def
  set DυSum : Fin d → (Fin d → ℝ) → ℝ :=
    fun i x => |DuOf u i x| + |DuOf v i x| with hDυSum_def
  -- `μSum ∈ MemLpPer βBarE`.
  have hμSum_β : MemLpPer (d := d) βBarE μSum := by
    rw [hβBarE_def, hμSum_def]
    exact memLpPer_abs_add_abs hmLp_u hmLp_v
  -- `υSum ∈ MemLpPer γBarE`.
  have hυSum_γ : MemLpPer (d := d) γBarE υSum := by
    rw [hγBarE_def, hυSum_def]
    exact memLpPer_abs_add_abs huLp_u huLp_v
  -- `DυSum i ∈ MemLpPer γBarE` for each `i`.
  have hDυSum_γ : ∀ i, MemLpPer (d := d) γBarE (DυSum i) := by
    intro i
    rw [hγBarE_def, hDυSum_def]
    exact memLpPer_abs_add_abs (hDuLp_u i) (hDuLp_v i)
  -- Restate `μSum` at the paper exponent `β + 1`.
  have hμSum_paperβ :
      MemLpPer (d := d) (ENNReal.ofReal (βExp + 1)) μSum := by
    rw [← hβBar_eq]; exact hμSum_β
  -- Constants 1 helpers.
  have hone_β' : MemLpPer (d := d) βBar'E (fun _ : (Fin d → ℝ) => (1 : ℝ)) :=
    MemLp.toMemLpPer (MeasureTheory.memLp_const (1 : ℝ))
  -- Paper-faithful standing fact: `βBarReal' ≤ γBarReal` (paper `eq:gamma`).
  have hβ'_le_γ_real : βBarReal' ≤ γBarReal := by
    rw [hβBar'_eq, hγBar_eq]
    have h := Hamiltonian.betaBar'_le_gammaBar (hαExp.le) hβ_pos
    simp only [Hamiltonian.betaBar', Hamiltonian.gammaBar] at h
    exact h
  have hβ'_le_γ : βBar'E ≤ γBarE := by
    rw [hβBar'E_def, hγBarE_def]
    exact ENNReal.ofReal_le_ofReal hβ'_le_γ_real
  have hγTop : γBarE ≠ ⊤ := by rw [hγBarE_def]; exact ENNReal.ofReal_ne_top
  -- Paper-faithful standing fact: `γBarReal' ≤ βBarReal` (paper `eq:gamma`).
  have hγ'_le_β_real : γBarReal' ≤ βBarReal := by
    rw [hγBar'_eq, hγBar_eq, hβBar_eq]
    have h := Hamiltonian.gammaBar'_le_betaBar hαExp hβ_pos
    exact h
  have hγ'_le_β : γBar'E ≤ βBarE := by
    rw [hγBar'E_def, hβBarE_def]
    exact ENNReal.ofReal_le_ofReal hγ'_le_β_real
  have hβTop : βBarE ≠ ⊤ := by rw [hβBarE_def]; exact ENNReal.ofReal_ne_top
  -- Note: `hγBar'_eq` already a paper-exponent identity; derive a real
  -- exponent identity restated at the paper exponents.
  have hγ'_paper_eq : γBarReal' =
      αExp * (βExp + 1) / βExp /
        (αExp * (βExp + 1) / βExp - 1) := by
    rw [hγBar'_eq, hγBar_eq]
  -- The conjunct assembly proper (11 conjuncts in `_min`-struct order).
  refine ⟨hmLp_w, hDuLp_w, huLp_w, ?h4, ?h5, ?h6, ?h7, ?h8, ?h9, ?h10, ?h11⟩
  -- (4) MemLpPer βBar' (|uOf u| + |uOf v|).
  case h4 =>
    exact MemLpPer.mono_exponent_finite hβ'_le_γ hγTop hυSum_γ
  -- (5) MemLpPer βBar' (‖DυSum ·‖^α + 1).
  case h5 =>
    have hDυSum_vec :
        MemLpPer (d := d) γBarE
          (fun x : (Fin d → ℝ) => fun j : Fin d => DυSum j x) :=
      memLpPer_pi_of_coord_local (p := γBarE) DυSum hDυSum_γ
    set qE : ℝ≥0∞ := ENNReal.ofReal αExp with hqE_def
    have hqE_toReal : qE.toReal = αExp := by
      rw [hqE_def]; exact ENNReal.toReal_ofReal hα_pos.le
    have hT_a :
        MemLp (fun x : (Fin d → ℝ) =>
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
          ‖(fun j : Fin d => DυSum j x)‖ ^ αExp) := by
      funext x; rw [hqE_toReal]
    rw [heq] at hT_a
    have hT_b :
        MemLpPer (d := d) βBar'E
          (fun x : (Fin d → ℝ) =>
            ‖fun j => |DuOf u j x| + |DuOf v j x|‖ ^ αExp) := by
      have := MemLp.toMemLpPer hT_a
      rw [hdiv] at this
      exact this
    have hsum := hT_b.add hone_β'
    have heqf :
        ((fun x : (Fin d → ℝ) =>
          ‖fun j => |DuOf u j x| + |DuOf v j x|‖ ^ αExp)
          + (fun _ : (Fin d → ℝ) => (1 : ℝ)))
        = (fun x : (Fin d → ℝ) =>
          ‖fun j => |DuOf u j x| + |DuOf v j x|‖ ^ αExp + 1) := by
      funext x; simp [Pi.add_apply]
    rw [heqf] at hsum
    exact hsum
  -- (6) MemLpPer βBar' ((μSum)^β + 1).
  case h6 =>
    set qE : ℝ≥0∞ := ENNReal.ofReal βExp with hqE_def
    have hqE_toReal : qE.toReal = βExp := by
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
        = (fun x : (Fin d → ℝ) => |μSum x| ^ βExp) := by
      funext x; rw [hqE_toReal]
    rw [heq] at hT_a
    have hT_b : MemLpPer (d := d) βBar'E
        (fun x : (Fin d → ℝ) => |μSum x| ^ βExp) := by
      have := MemLp.toMemLpPer hT_a
      rw [hdiv] at this
      exact this
    have hμSum_nn : ∀ x, 0 ≤ μSum x := fun x => by
      rw [hμSum_def]; exact add_nonneg (abs_nonneg _) (abs_nonneg _)
    have hT_c : MemLpPer (d := d) βBar'E
        (fun x : (Fin d → ℝ) => μSum x ^ βExp) := by
      have heq : (fun x : (Fin d → ℝ) => μSum x ^ βExp)
                = (fun x : (Fin d → ℝ) => |μSum x| ^ βExp) := by
        funext x; rw [abs_of_nonneg (hμSum_nn x)]
      rw [heq]; exact hT_b
    have hsum := hT_c.add hone_β'
    have heqf :
        ((fun x : (Fin d → ℝ) => μSum x ^ βExp)
          + (fun _ : (Fin d → ℝ) => (1 : ℝ)))
        = (fun x : (Fin d → ℝ) => (|mOf u x| + |mOf v x|) ^ βExp + 1) := by
      funext x; simp [Pi.add_apply, hμSum_def]
    rw [heqf] at hsum
    exact hsum
  -- (7) MemLpPer γBar' (μSum * ‖DυSum ·‖^(α-1)).
  case h7 =>
    have hDυSum_vec :
        MemLpPer (d := d) γBarE
          (fun x : (Fin d → ℝ) => fun j : Fin d => DυSum j x) :=
      memLpPer_pi_of_coord_local (p := γBarE) DυSum hDυSum_γ
    set qE : ℝ≥0∞ := ENNReal.ofReal (αExp - 1) with hqE_def
    have hqE_toReal : qE.toReal = αExp - 1 := by
      rw [hqE_def]; exact ENNReal.toReal_ofReal hαm1_pos.le
    have hT1a :
        MeasureTheory.MemLp (fun x : (Fin d → ℝ) =>
                ‖(fun j : Fin d => DυSum j x)‖ ^ qE.toReal)
              (γBarE / qE)
              (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
      MeasureTheory.MemLp.norm_rpow_div hDυSum_vec.toMemLp qE
    have hdiv :
        γBarE / qE = ENNReal.ofReal (αExp * (βExp + 1) / βExp / (αExp - 1)) := by
      rw [hγBarE_def, hqE_def, hγBar_eq, ← ENNReal.ofReal_div_of_pos hαm1_pos]
    have heq :
        (fun x : (Fin d → ℝ) =>
          ‖(fun j : Fin d => DυSum j x)‖ ^ qE.toReal)
        = (fun x : (Fin d → ℝ) =>
          ‖fun j : Fin d => |DuOf u j x| + |DuOf v j x|‖ ^ (αExp - 1)) := by
      funext x; rw [hqE_toReal]
    rw [heq] at hT1a
    have hT1b :
        MemLpPer (d := d)
          (ENNReal.ofReal (αExp * (βExp + 1) / βExp / (αExp - 1)))
          (fun x : (Fin d → ℝ) =>
            ‖fun j : Fin d => |DuOf u j x| + |DuOf v j x|‖ ^ (αExp - 1)) := by
      have := MemLp.toMemLpPer hT1a
      rw [hdiv] at this
      exact this
    have hHT_real :
        Real.HolderTriple (βExp + 1)
          (αExp * (βExp + 1) / βExp / (αExp - 1))
          (αExp * (βExp + 1) / βExp /
              (αExp * (βExp + 1) / βExp - 1)) :=
      holderTriple_betaBar_gammaBarOverAlphaMinus1_gammaBar_local
        hαExp hβExp
    haveI hHT_enn :
        ENNReal.HolderTriple (ENNReal.ofReal (βExp + 1))
          (ENNReal.ofReal (αExp * (βExp + 1) / βExp / (αExp - 1)))
          (ENNReal.ofReal (αExp * (βExp + 1) / βExp /
              (αExp * (βExp + 1) / βExp - 1))) :=
      hHT_real.ennrealOfReal
    have hT1c :
        MeasureTheory.MemLp
          (fun x : (Fin d → ℝ) =>
            μSum x * ‖fun j => |DuOf u j x| + |DuOf v j x|‖ ^ (αExp - 1))
          (ENNReal.ofReal (αExp * (βExp + 1) / βExp /
              (αExp * (βExp + 1) / βExp - 1)))
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) :=
      (hμSum_paperβ.toMemLp.fun_mul hT1b.toMemLp : _)
    have hres :
        MemLpPer (d := d)
          (ENNReal.ofReal (αExp * (βExp + 1) / βExp /
              (αExp * (βExp + 1) / βExp - 1)))
          (fun x : (Fin d → ℝ) =>
            (|mOf u x| + |mOf v x|) *
              ‖fun j => |DuOf u j x| + |DuOf v j x|‖ ^ (αExp - 1)) := by
      have := MemLp.toMemLpPer hT1c
      convert this using 1
    have hexp_eq : γBar'E =
        ENNReal.ofReal (αExp * (βExp + 1) / βExp /
            (αExp * (βExp + 1) / βExp - 1)) := by
      rw [hγBar'E_def, hγ'_paper_eq]
    rw [hexp_eq]; exact hres
  -- (8) MemLpPer γBar' (μSum ^ (1 + β - β/α)).
  case h8 =>
    have hβα_pos : 0 < βExp / αExp := div_pos hβ_pos hα_pos
    have hβα_lt : βExp / αExp < βExp + 1 := by
      have h1 : βExp / αExp ≤ βExp := by
        rw [div_le_iff₀ hα_pos]
        nlinarith [hαExp, hβ_pos]
      linarith
    have hexp_pos : 0 < βExp + 1 - βExp / αExp := by linarith
    set qE : ℝ≥0∞ := ENNReal.ofReal (βExp + 1 - βExp / αExp) with hqE_def
    have hqE_toReal : qE.toReal = βExp + 1 - βExp / αExp := by
      rw [hqE_def]; exact ENNReal.toReal_ofReal hexp_pos.le
    have hT2a :
        MeasureTheory.MemLp (fun x : (Fin d → ℝ) => |μSum x| ^ qE.toReal)
              ((ENNReal.ofReal (βExp + 1)) / qE)
              (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
      have h1 := MeasureTheory.MemLp.norm_rpow_div hμSum_paperβ.toMemLp qE
      have heq :
          (fun x : (Fin d → ℝ) => ‖μSum x‖ ^ qE.toReal)
          = fun x : (Fin d → ℝ) => |μSum x| ^ qE.toReal := by
        funext x; rw [Real.norm_eq_abs]
      rw [heq] at h1
      exact h1
    have hβne : βExp ≠ 0 := hβ_pos.ne'
    have hαne : αExp ≠ 0 := hα_pos.ne'
    have hbb_ne : βExp + 1 ≠ 0 := hβ1_pos.ne'
    have hβbβα_ne : βExp + 1 - βExp / αExp ≠ 0 := hexp_pos.ne'
    have hgb_gt_one : 1 < αExp * (βExp + 1) / βExp := by
      rw [lt_div_iff₀ hβ_pos]; nlinarith [hαExp, hβ_pos]
    have hγb_ne : αExp * (βExp + 1) / βExp ≠ 0 := by
      have : 0 < αExp * (βExp + 1) / βExp :=
        div_pos (mul_pos hα_pos hβ1_pos) hβ_pos
      exact this.ne'
    have hγbm1_ne : αExp * (βExp + 1) / βExp - 1 ≠ 0 := by linarith
    have hdiv_eq :
        (ENNReal.ofReal (βExp + 1)) / qE = γBar'E := by
      rw [hqE_def, hγBar'E_def, hγBar'_eq, hγBar_eq,
        ← ENNReal.ofReal_div_of_pos hexp_pos]
      congr 1
      field_simp
    have heq :
        (fun x : (Fin d → ℝ) => |μSum x| ^ qE.toReal)
        = (fun x : (Fin d → ℝ) => |μSum x| ^ (βExp + 1 - βExp / αExp)) := by
      funext x; rw [hqE_toReal]
    rw [heq] at hT2a
    have hT2b :
        MemLpPer (d := d) γBar'E
          (fun x : (Fin d → ℝ) => |μSum x| ^ (βExp + 1 - βExp / αExp)) := by
      have := MemLp.toMemLpPer hT2a
      rw [hdiv_eq] at this
      exact this
    have hsh : (1 : ℝ) + βExp - βExp / αExp
                  = βExp + 1 - βExp / αExp := by ring
    have hbound :
        ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)),
          ‖μSum x ^ (1 + βExp - βExp / αExp)‖ ≤
            (1 : ℝ) * ‖|μSum x| ^ (βExp + 1 - βExp / αExp)‖ := by
      refine Filter.Eventually.of_forall ?_
      intro x
      rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul, hsh]
      have habs := Real.abs_rpow_le_abs_rpow (μSum x) (βExp + 1 - βExp / αExp)
      have hrhs_nn : 0 ≤ |μSum x| ^ (βExp + 1 - βExp / αExp) :=
        Real.rpow_nonneg (abs_nonneg _) _
      rw [abs_of_nonneg hrhs_nn]
      exact habs
    have hmeas :
        MeasureTheory.AEStronglyMeasurable
          (fun x : (Fin d → ℝ) => μSum x ^ (1 + βExp - βExp / αExp))
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
      have h_exp_nn : (0 : ℝ) ≤ 1 + βExp - βExp / αExp := by linarith [hexp_pos]
      have hcont : Continuous (fun y : ℝ => y ^ (1 + βExp - βExp / αExp)) :=
        Real.continuous_rpow_const h_exp_nn
      exact hcont.comp_aestronglyMeasurable hμSum_β.aestronglyMeasurable
    have hT2c :
        MemLpPer (d := d) γBar'E
          (fun x : (Fin d → ℝ) => μSum x ^ (1 + βExp - βExp / αExp)) :=
      MemLp.toMemLpPer (MeasureTheory.MemLp.of_le_mul hT2b.toMemLp hmeas hbound)
    convert hT2c using 1
  -- (9) MemLpPer γBar' (μSum).
  case h9 =>
    have hT10 : MemLpPer (d := d) γBar'E μSum :=
      MemLpPer.mono_exponent_finite hγ'_le_β hβTop hμSum_β
    convert hT10 using 1
  -- (10) MemLpPer γBar' ((∑ i, (DυSum i x)^2)^((γBar-1)/2)).
  case h10 =>
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
        MemLpPer (d := d) (γBarE / q2E)
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
        MemLpPer (d := d) (γBarE / q2E)
          (fun x : (Fin d → ℝ) => ∑ i, (DυSum i x) ^ (2 : ℕ)) := by
      have hsum : MeasureTheory.MemLp
          (fun x : (Fin d → ℝ) => ∑ i : Fin d, (fun x => (DυSum i x) ^ (2 : ℕ)) x)
          (γBarE / q2E)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)) := by
        refine memLp_finset_sum (Finset.univ : Finset (Fin d)) ?_
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
        MemLpPer (d := d) γBar'E
          (fun x : (Fin d → ℝ) =>
            (∑ i, (DυSum i x) ^ (2 : ℕ)) ^ ((γBarReal - 1) / 2)) := by
      have := MemLp.toMemLpPer hRpow
      rw [hdiv_eq] at this
      exact this
    convert hres using 1
  -- (11) MemLpPer γBar' (υSum ^ (γBar - 1)).
  case h11 =>
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
    have hres : MemLpPer (d := d) γBar'E
        (fun x : (Fin d → ℝ) => υSum x ^ (γBarReal - 1)) := by
      have := MemLp.toMemLpPer hRpow
      rw [hdiv] at this
      exact this
    convert hres using 1

/-! ## Paper-faithful hemicontinuity composition: `_paperHypotheses_min`

`Aepsi_hemicont_of_paperHypotheses_min` mirrors the legacy
`Aepsi_hemicont_of_paperHypotheses` but consumes the 11-conjunct
`PaperSection8SegmentResiduesMin` instead of the inline 13-conjunct
`hSegRes` supplier. Routes through `hemicontSegmentData_of_KAepsi_min`,
which itself routes through `g_unreg_natural_integrableOn_min`. No
new exponent inequalities are introduced; in particular, neither
of the paper-forbidden side conditions removed by Phase 0
(see the docstring of `aepsiUniformContextK_of_paperHypotheses_closed_paper`)
reappears in the chain. -/

/-- **Paper-faithful sibling of `Aepsi_hemicont_of_paperHypotheses`.**

Same conclusion as the legacy composition theorem but consumes the
minimal 11-conjunct `PaperSection8SegmentResiduesMin` shape, dropping
the two over-specified residues. The active-path sibling for the
hemicontinuity feeder in the closed-form aggregator. -/
theorem Aepsi_hemicont_of_paperHypotheses_min
    {d : ℕ}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)] [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (auxHypsK : ∀ q ∈ K_Aepsi d βBarReal γBarReal,
                  MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
                    V H DpH (fun i => ⇑(q.2.2 i)) (⇑q.1) (⇑q.2.1))
    {ε : ℝ}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (h_slice :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          H x p m ≤ -(m ^ hpow.β) / hpow.C + hpow.C + hpow.C * ‖p‖ ^ hpow.α
                  + hpow.C * ‖p‖ * (m ^ (hpow.β - hpow.β / hpow.α) + 1))
    (hReg : RegularityH (d := d) H DpH)
    (hγ : 1 < γBarReal)
    (hβconj : βBarReal'.HolderConjugate βBarReal)
    (hγconj : γBarReal'.HolderConjugate γBarReal)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (hSegMin : PaperSection8SegmentResiduesMin
      (d := d) γBarReal βBarReal βBarReal' γBarReal' H DpH hpow)
    (hF_unreg_meas : ∀ (u v : XBanach d βBarReal γBarReal),
                u ∈ K_Aepsi d βBarReal γBarReal →
                v ∈ K_Aepsi d βBarReal γBarReal →
                ∀ (w : XBanach d βBarReal γBarReal),
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        MeasureTheory.AEStronglyMeasurable
          (fun x => aepsiIntegrandAt_unreg V H DpH
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
          (MeasureTheory.volume.restrict (UnitCube d))) :
    Monotone.IsHemicontinuous (X := XBanach d βBarReal γBarReal)
      (K_Aepsi d βBarReal γBarReal)
      (Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        V H DpH auxHypsK ε) := by
  refine isHemicontinuous_Aepsi_CLM_K_Aepsi (γBarReal := γBarReal)
    (βBarReal := βBarReal) (βBarReal' := βBarReal') (γBarReal' := γBarReal')
    V H DpH auxHypsK hReg hγ ?_
  intro u v hu hv w
  -- Unpack the 11 paper-faithful conjuncts.
  obtain ⟨hη, hDν, hν_γ,
          hΔυ, hΔp_pow, hΔm_pow, hΔm_grad, hΔm_endpoint, hΔm,
          hG_grad, hG_val⟩ :=
    hSegMin.out u v hu hv w
  -- Apply the paper-faithful producer at `q₁ := v`, `q₂ := u`,
  -- `γBar := γBarReal`.
  exact hemicontSegmentData_of_KAepsi_min (γBarReal := γBarReal)
    (βBarReal := βBarReal) (βBarReal' := βBarReal') (γBarReal' := γBarReal')
    (γBar := γBarReal) (V := V) (H := H) (DpH := DpH)
    hv hu (auxHypsK v hv) (auxHypsK u hu)
    hβconj hγconj hpow h_slice hγ
    (fun i => ⇑(w.2.2 i)) (⇑w.1) (⇑w.2.1)
    hη hDν hν_γ rfl
    hV hΔυ hΔp_pow hΔm_pow hΔm_grad hΔm_endpoint hΔm
    hG_grad hG_val
    (hF_unreg_meas u v hu hv w) (hF_gat_meas u v hu hv w)

/-! ### Paper-faithful sibling aggregator: `aepsiUniformContextK_of_paperHypotheses_min`

Sibling of `aepsiUniformContextK_of_paperHypotheses` whose only change
is to consume the paper-faithful 11-conjunct `PaperSection8SegmentResiduesMin`
instead of the inline 13-conjunct `hSegRes`, and to route the
hemicontinuity feeder through `Aepsi_hemicont_of_paperHypotheses_min`.

All other parameters (monotonicity, coercivity, K0 supplier, weak-derivative
tie, etc.) and downstream calls (`Aepsi_mono_of_paperHypotheses`,
`Aepsi_coercive_of_paperHypotheses`, `auxHyps_of_paperHypotheses_on_KAepsi`,
`mfgOpEps_uniformAux_of_perPairAuxHyps`) are unchanged from the legacy
aggregator. This isolates the paper-faithful relaxation to the
hemicontinuity feeder. -/

/-- **Paper-faithful sibling of `aepsiUniformContextK_of_paperHypotheses`.**

Build a K_Aepsi-form abstract-VI context `AepsiUniformContextK` from the
paper hypotheses, threading the residue parameters of the four
K_Aepsi-form feeders. Differs from the legacy aggregator only in
consuming `PaperSection8SegmentResiduesMin` (11 paper-faithful
conjuncts) for the hemicontinuity feeder rather than the legacy
13-conjunct inline `hSegRes`. -/
noncomputable def aepsiUniformContextK_of_paperHypotheses_min
    {d : ℕ}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {ε : ℝ}
    (hε : 0 < ε)
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (hExp : SimplePowerExponentFacts γBarReal
                (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
                (ENNReal.ofReal βBarReal'))
    (hβBar_eq : βBarReal = hpow.β + 1)
    (hγBar_eq : γBarReal = hpow.α * (hpow.β + 1) / hpow.β)
    (hβBar'_eq : βBarReal' = (hpow.β + 1) / hpow.β)
    (hγBar'_eq : γBarReal' = γBarReal / (γBarReal - 1))
    (hβ : βBarReal.HolderConjugate βBarReal')
    (hγ : γBarReal.HolderConjugate γBarReal')
    (hβTop : ENNReal.ofReal γBarReal ≠ ⊤)
    (hγ'_le_β : ENNReal.ofReal γBarReal' ≤ ENNReal.ofReal βBarReal)
    (C' : ℝ) (hC'_pos : 0 < C')
    (h_upper :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ p mm, 0 < mm →
          H x p mm ≤ C' * (‖p‖ ^ hpow.α + 1) - (mm ^ hpow.β) / C')
    (hF_HJB_meas :
      ∀ q : XBanach d βBarReal γBarReal,
        AEStronglyMeasurable
          (fun x => -(uOf q x) - H x (fun i => DuOf q i x) (mOf q x) + V x)
          (MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)))
    (hF_flux_meas :
      ∀ q : XBanach d βBarReal γBarReal, ∀ i,
        AEStronglyMeasurable
          (fun x => mOf q x * DpH x (fun j => DuOf q j x) (mOf q x) i)
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
          mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
              γBarReal ε (fun i => ⇑(v.2.2 i)) (⇑v.1) (⇑v.2.1)
              (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1)
            - mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
                γBarReal ε (fun _ _ => 0) (fun _ => 1) (fun _ => 0)
                (fun i => ⇑(v.2.2 i)) ((⇑v.1) - 1) (⇑v.2.1))
    (h_slice :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ p m, 0 < m →
          H x p m ≤ -(m ^ hpow.β) / hpow.C + hpow.C + hpow.C * ‖p‖ ^ hpow.α
                  + hpow.C * ‖p‖ * (m ^ (hpow.β - hpow.β / hpow.α) + 1))
    (hReg : RegularityH (d := d) H DpH)
    (hγ2 : 1 < γBarReal)
    (hβconj : βBarReal'.HolderConjugate βBarReal)
    (hγconj : γBarReal'.HolderConjugate γBarReal)
    -- Paper-faithful 11-conjunct segment residues (replaces the legacy
    -- 13-conjunct inline `hSegRes`).
    (hSegMin : PaperSection8SegmentResiduesMin
      (d := d) γBarReal βBarReal βBarReal' γBarReal' H DpH hpow)
    (hF_unreg_meas : ∀ (u v : XBanach d βBarReal γBarReal),
                u ∈ K_Aepsi d βBarReal γBarReal →
                v ∈ K_Aepsi d βBarReal γBarReal →
                ∀ (w : XBanach d βBarReal γBarReal),
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        MeasureTheory.AEStronglyMeasurable
          (fun x => aepsiIntegrandAt_unreg V H DpH
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
                    V H DpH (DuOf q) (mOf q) (uOf q))
    (hWeakDerivK0 :
      ∀ q ∈ K0_Aepsi d βBarReal γBarReal,
        ∀ i, HasWeakDerivPer (d := d) i (uOf q) (DuOf q i)) :
    AepsiUniformContextK (d := d) ε V H DpH γBarReal βBarReal
      βBarReal' γBarReal' := by
  classical
  -- Build the K_Aepsi-indexed `auxHypsK` supplier.
  set auxHypsK :
      ∀ q ∈ K_Aepsi d βBarReal γBarReal,
        MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
          V H DpH (fun i => ⇑(q.2.2 i)) (⇑q.1) (⇑q.2.1) :=
    auxHyps_of_paperHypotheses_on_KAepsi
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      hmon hpow hV hExp
      hβBar_eq hγBar_eq hβBar'_eq hγBar'_eq
      hβ hγ hβTop hγ'_le_β
      C' hC'_pos h_upper hF_HJB_meas hF_flux_meas
    with hauxHypsK_def
  -- Reflexivity of the Banach pair, derived from `hExp` via
  -- `lpSobolev_product_isReflexive`. (Identical to the legacy aggregator.)
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
    have h_βBar_ne_top : (ENNReal.ofReal βBarReal) ≠ ∞ :=
      ENNReal.ofReal_ne_top
    have h_γBar_ne_top : (ENNReal.ofReal γBarReal) ≠ ∞ :=
      ENNReal.ofReal_ne_top
    exact StationaryMFG.Periodic.lpSobolev_product_isReflexive (d := d)
      (ENNReal.ofReal βBarReal) (ENNReal.ofReal βBarReal')
      (ENNReal.ofReal γBarReal) (ENNReal.ofReal γBarPrimeReal)
      hExp.βBar_one_lt h_βBar_ne_top hExp.gammaBar_one_lt h_γBar_ne_top
  -- Build the four feeder outputs (monotonicity, coercivity unchanged;
  -- hemicontinuity routed through the `_min` sibling).
  have hMono :
      Monotone.IsMonotone (X := XBanach d βBarReal γBarReal)
        (K_Aepsi d βBarReal γBarReal)
        (Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
          (βBarReal' := βBarReal') (γBarReal' := γBarReal')
          V H DpH auxHypsK ε) :=
    Aepsi_mono_of_paperHypotheses (γBarReal := γBarReal)
      (βBarReal := βBarReal) (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      V H DpH auxHypsK hmon hε.le hScalarMono hVecMono
  have hCoerc :
      Monotone.IsCoerciveAt (X := XBanach d βBarReal γBarReal)
        (K_Aepsi d βBarReal γBarReal)
        (Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
          (βBarReal' := βBarReal') (γBarReal' := γBarReal')
          V H DpH auxHypsK ε)
        (qRef_simplePower d βBarReal γBarReal) :=
    Aepsi_coercive_of_paperHypotheses_scaled (γBarReal := γBarReal)
      (βBarReal := βBarReal) (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      V H DpH auxHypsK ε κCoerc hκCoerc lamCoerc hlamCoerc Ccoerc hbound_residue
  have hHC :
      Monotone.IsHemicontinuous (X := XBanach d βBarReal γBarReal)
        (K_Aepsi d βBarReal γBarReal)
        (Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
          (βBarReal' := βBarReal') (γBarReal' := γBarReal')
          V H DpH auxHypsK ε) :=
    Aepsi_hemicont_of_paperHypotheses_min (γBarReal := γBarReal)
      (βBarReal := βBarReal) (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      V H DpH auxHypsK hpow h_slice hReg hγ2 hβconj hγconj hV
      hSegMin hF_unreg_meas hF_gat_meas
  have hAux :
      MFGOpEpsUniformAux (d := d) ε V H DpH γBarReal βBarReal βBarReal' γBarReal'
        (K0_Aepsi d βBarReal γBarReal) :=
    mfgOpEps_uniformAux_of_perPairAuxHyps ε
      (K0_Aepsi d βBarReal γBarReal) auxHypsK0
  exact {
    hReflexive := hReflexive
    auxHypsK := auxHypsK
    qRef := qRef_simplePower d βBarReal γBarReal
    hqRef := qRef_simplePower_mem_K_Aepsi d βBarReal γBarReal
    aux := hAux
    hMono := hMono
    hHC := hHC
    hCoerc := hCoerc
    hWeakDeriv := hWeakDerivK0
  }

/-! ## Refined-domain paper-exponent producer (Step 3a)

Step 3a of the iter-0694 five-child split of
`paperSolFor-final-phase5-hWeakDeriv-refined-domain-final` (filed iter
0699 after the step-4 first attempt revealed the consumer of Step 3
was orphaned).

This section lands `aepsiUniformContextK_W_of_paperHypotheses_closed_paper_min`:
the refined-domain sibling of
`aepsiUniformContextK_of_paperHypotheses_closed_paper_min` that
delivers an `AepsiUniformContextK_W` (rather than an
`AepsiUniformContextK`) at the paper exponents.

The refinement is purely on the `K_Aepsi_W ⊆ K_Aepsi` side: the
Browder–Minty fields (`hMono`, `hHC`, `hCoerc`) are obtained from the
K-form producers and restricted to the smaller cone via
`K_Aepsi_W_subset_K_Aepsi`. The base-point membership
`qRef_simplePower ∈ K_Aepsi_W` is discharged inline via the
qRef a.e.-zero identities and `hasWeakDerivPer_zero_zero`.

Per the iter-0683 directive (eliminate `hWeakDeriv`, never migrate):
**no new authorisation parameter** is introduced in the signature.
The weak-derivative tie on the K0_Aepsi_W cone is purely structural
(`hasWeakDerivPer_of_mem_K0_Aepsi_W`), so it does not appear on the
producer. -/

/-- **Zero-zero weak-derivative tie** (auxiliary). The constant zero
function on `Fin d → ℝ` has zero as a weak partial derivative in every
coordinate direction. Used for the `qRef_simplePower` membership in
`K_Aepsi_W` in the producer below. Adapted from
`StationaryMFG.Theorems.Congestion.Domain.hasWeakDerivPer_zero_zero`. -/
private lemma hasWeakDerivPer_zero_zero_aux
    {d : ℕ} (i : Fin d) :
    HasWeakDerivPer (d := d) i
      (fun _ : (Fin d → ℝ) => (0 : ℝ))
      (fun _ : (Fin d → ℝ) => (0 : ℝ)) := by
  haveI : MeasureTheory.IsFiniteMeasure
      (MeasureTheory.Measure.restrict
        (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
        (UnitCube d)) :=
    Periodic.Saturator.instIsFiniteMeasureRestrictUnitCube
  refine ⟨?_, ?_⟩
  · -- `MemLpPer 1 (fun _ => 0)`.
    exact MemLp.toMemLpPer (MeasureTheory.memLp_const (0 : ℝ))
  · intro φ
    have h0a : (fun x : Fin d → ℝ =>
        (0 : ℝ) * (φ : (Fin d → ℝ) → ℝ) x) = (fun _ => (0 : ℝ)) := by
      funext x; ring
    have h0b : (fun x : Fin d → ℝ => (0 : ℝ) *
        ((Periodic.SmoothPeriodic.partialDeriv i φ : Periodic.SmoothPeriodic d) :
            (Fin d → ℝ) → ℝ) x) = (fun _ => (0 : ℝ)) := by
      funext x; ring
    rw [h0a, h0b]
    simp [periodicIntegral_const]

/-- **`qRef_simplePower` lies in the refined strict-positivity cone
`K_Aepsi_W`.**

The `m`-factor is a.e. `1 > 0` (already in `K_Aepsi`), the gradient
factors are a.e. `0` (hence AEPeriodic via `aePeriodic_DuOf`, and the
weak-derivative tie transports from `hasWeakDerivPer_zero_zero` via
`HasWeakDerivPer.congr_ae_unitCube`). -/
theorem qRef_simplePower_mem_K_Aepsi_W
    (d : ℕ) (βBarReal γBarReal : ℝ)
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)] :
    qRef_simplePower d βBarReal γBarReal
      ∈ K_Aepsi_W d βBarReal γBarReal := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · -- K_Aepsi slot.
    exact qRef_simplePower_mem_K_Aepsi d βBarReal γBarReal
  · -- AEPeriodic on each gradient coordinate.
    intro i
    exact aePeriodic_DuOf (qRef_simplePower d βBarReal γBarReal) i
  · -- Weak-derivative tie: `HasWeakDerivPer i (uOf qRef) (DuOf qRef i)`.
    intro i
    -- Base case: `HasWeakDerivPer i 0 0`.
    have h0 : HasWeakDerivPer (d := d) i
                (fun _ : (Fin d → ℝ) => (0 : ℝ))
                (fun _ : (Fin d → ℝ) => (0 : ℝ)) :=
      hasWeakDerivPer_zero_zero_aux i
    -- Transport along `uOf qRef =ᵐ 0` and `DuOf qRef i =ᵐ 0`.
    have h_uOf_ae : (fun _ : (Fin d → ℝ) => (0 : ℝ))
                    =ᵐ[MeasureTheory.Measure.restrict
                          (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
                          (UnitCube d)]
                    uOf (qRef_simplePower d βBarReal γBarReal) :=
      (qRef_simplePower_uOf_ae d βBarReal γBarReal).symm
    have h_DuOf_ae : (fun _ : (Fin d → ℝ) => (0 : ℝ))
                    =ᵐ[MeasureTheory.Measure.restrict
                          (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
                          (UnitCube d)]
                    DuOf (qRef_simplePower d βBarReal γBarReal) i :=
      (qRef_simplePower_DuOf_ae d βBarReal γBarReal i).symm
    -- The target `MemLpPer 1` for the transported derivative.
    haveI : MeasureTheory.IsFiniteMeasure
        (MeasureTheory.Measure.restrict
          (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
          (UnitCube d)) :=
      Periodic.Saturator.instIsFiniteMeasureRestrictUnitCube
    have hγ : (1 : ℝ≥0∞) ≤ ENNReal.ofReal γBarReal := Fact.out
    have hDuOf_qRef_memLp1 :
        MemLpPer (d := d) 1
          ((⇑((qRef_simplePower d βBarReal γBarReal).2.2 i)
              : (Fin d → ℝ) → ℝ)) :=
      StationaryMFG.Solutions.MFG.memLpPer_one_of_mono hγ
        (memLpPer_of_lpPer (d := d)
          ((qRef_simplePower d βBarReal γBarReal).2.2 i))
    have hDuOf_memLp1 :
        MemLpPer (d := d) 1
          (DuOf (qRef_simplePower d βBarReal γBarReal) i) := by
      simp only [DuOf_def]
      exact hDuOf_qRef_memLp1
    exact h0.congr_ae_unitCube h_uOf_ae hDuOf_memLp1 h_DuOf_ae

/-- **Paper-exponent refined-domain closed-form producer (`_min` sibling).**

Build an `AepsiUniformContextK_W` from the four primary paper hypotheses
`(hε, hmon, hpow, hV)`, plus a paper-faithful analytic bundle
`hAnalytic : PaperSection8AnalyticResiduesMin …`. The refined-domain
sibling of `aepsiUniformContextK_of_paperHypotheses_closed_paper_min`
that delivers a context typed at `K_Aepsi_W` rather than `K_Aepsi`.

Per the iter-0697 design, the `auxHypsK` supplier remains typed at
`K_Aepsi` (the `Aepsi_CLM_opK` API constraint), and the K0-form
`aux` supplier is restricted to `K0_Aepsi_W` via
`K0_Aepsi_W_subset_K0_Aepsi`. The three Browder–Minty fields
(`hMono`, `hHC`, `hCoerc`) are restricted from `K_Aepsi` to
`K_Aepsi_W` via the inclusion `K_Aepsi_W ⊆ K_Aepsi`.

Per the iter-0683 directive: no new authorisation parameter is added;
the weak-derivative tie on the refined cone is structural via
`hasWeakDerivPer_of_mem_K0_Aepsi_W`. -/
noncomputable def aepsiUniformContextK_W_of_paperHypotheses_closed_paper_min
    {d : ℕ}
    {ε : ℝ}
    (hε : 0 < ε)
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) V)
    [hβBarFact : Fact (1 ≤ ENNReal.ofReal (hpow.β + 1))]
    [hγBarFact : Fact (1 ≤ ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))]
    (hAnalytic : PaperSection8AnalyticResiduesMin
                    (d := d)
                    (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
                    (βBarReal := hpow.β + 1)
                    (βBarReal' := (hpow.β + 1) / hpow.β)
                    (γBarReal' := (hpow.α * (hpow.β + 1) / hpow.β)
                                    / (hpow.α * (hpow.β + 1) / hpow.β - 1))
                    ε V H DpH hpow) :
    AepsiUniformContextK_W (d := d) ε V H DpH
      (hpow.α * (hpow.β + 1) / hpow.β)
      (hpow.β + 1)
      ((hpow.β + 1) / hpow.β)
      ((hpow.α * (hpow.β + 1) / hpow.β)
        / (hpow.α * (hpow.β + 1) / hpow.β - 1)) := by
  classical
  -- Local abbreviations for the paper exponents.
  set βBarReal : ℝ := hpow.β + 1 with hβBarReal_def
  set γBarReal : ℝ := hpow.α * (hpow.β + 1) / hpow.β with hγBarReal_def
  set βBarReal' : ℝ := (hpow.β + 1) / hpow.β with hβBarReal'_def
  set γBarReal' : ℝ := γBarReal / (γBarReal - 1) with hγBarReal'_def
  -- The exponent-bundle `hExp` from `hpow` (cast to real-valued exponents).
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
  -- Group-B equality residues — definitional at the paper exponents.
  have hβBar_eq : βBarReal = hpow.β + 1 := hβBarReal_def
  have hγBar_eq : γBarReal = hpow.α * (hpow.β + 1) / hpow.β := hγBarReal_def
  have hβBar'_eq : βBarReal' = (hpow.β + 1) / hpow.β := hβBarReal'_def
  -- Hölder conjugacies.
  have hβ : βBarReal.HolderConjugate βBarReal' :=
    SimplePowerExponentFacts.paper_holderConjugate_betaBar hpow.hβ
  have hγ : γBarReal.HolderConjugate γBarReal' := by
    have := SimplePowerExponentFacts.paper_holderConjugate_gammaBar
              hpow.hα hpow.hβ
    exact this
  have hβTop : ENNReal.ofReal γBarReal ≠ ⊤ := hExp.gammaBar_lt_top.ne
  have hγ'_le_β : ENNReal.ofReal γBarReal' ≤ ENNReal.ofReal βBarReal := by
    have hle_real : γBarReal' ≤ βBarReal := by
      rw [hγBarReal'_def, hγBarReal_def, hβBarReal_def]
      have h_paper := Hamiltonian.gammaBar'_le_betaBar hpow.hα hpow.hβ
      simpa only [Hamiltonian.gammaBar', Hamiltonian.gammaBar,
                 Hamiltonian.betaBar] using h_paper
    exact ENNReal.ofReal_le_ofReal hle_real
  have hβ_gt1 : 1 < βBarReal := hβ.lt
  have hγBar_one_lt : 1 < γBarReal := hExp.γBar_one_lt_real
  -- Build the K_Aepsi-indexed `auxHypsK` supplier directly (this is what
  -- the K-form aggregator built internally; we inline it here to avoid
  -- the K-form's now-incompatible `hWeakDerivK0` consumption after the
  -- iter-post-0707 K0_Aepsi_W retype).
  let auxHypsK :
      ∀ q ∈ K_Aepsi d βBarReal γBarReal,
        MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
          V H DpH (fun i => ⇑(q.2.2 i)) (⇑q.1) (⇑q.2.1) :=
    auxHyps_of_paperHypotheses_on_KAepsi
      (γBarReal := γBarReal) (βBarReal := βBarReal)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      hmon hpow hV hExp
      hβBar_eq hγBar_eq hβBar'_eq hγBarReal'_def
      hβ hγ hβTop hγ'_le_β
      hpow.C hpow.hC hAnalytic.h_upper hAnalytic.hF_HJB_meas hAnalytic.hF_flux_meas
  -- Reflexivity of the Banach pair (Phase 1), derived from `hExp`.
  have hReflexive :
      Periodic.IsReflexiveNormedSpace (XBanach d βBarReal γBarReal) := by
    have h_one_lt_βBarReal : (1 : ℝ) < βBarReal := hβ_gt1
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
    have h_βBar_ne_top : (ENNReal.ofReal βBarReal) ≠ ∞ :=
      ENNReal.ofReal_ne_top
    have h_γBar_ne_top : (ENNReal.ofReal γBarReal) ≠ ∞ :=
      ENNReal.ofReal_ne_top
    exact StationaryMFG.Periodic.lpSobolev_product_isReflexive (d := d)
      (ENNReal.ofReal βBarReal) (ENNReal.ofReal βBarReal')
      (ENNReal.ofReal γBarReal) (ENNReal.ofReal γBarPrimeReal)
      hExp.βBar_one_lt h_βBar_ne_top hExp.gammaBar_one_lt h_γBar_ne_top
  -- Canonical W-form base point: the same `qRef_simplePower` as the
  -- K-form, with K_W-membership built directly.
  let qRefW : XBanach d βBarReal γBarReal :=
    qRef_simplePower d βBarReal γBarReal
  have hqRef_W : qRefW ∈ K_Aepsi_W d βBarReal γBarReal :=
    qRef_simplePower_mem_K_Aepsi_W d βBarReal γBarReal
  -- K-form monotonicity / hemicontinuity at the new auxHypsK.
  have hScalarMono := hAnalytic.hScalarMono
  have hVecMono := hAnalytic.hVecMono
  have hMono_K :
      Monotone.IsMonotone (X := XBanach d βBarReal γBarReal)
        (K_Aepsi d βBarReal γBarReal)
        (Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
          (βBarReal' := βBarReal') (γBarReal' := γBarReal')
          V H DpH auxHypsK ε) :=
    Aepsi_mono_of_paperHypotheses (γBarReal := γBarReal)
      (βBarReal := βBarReal) (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      V H DpH auxHypsK hmon hε.le hScalarMono hVecMono
  have hβconj : βBarReal'.HolderConjugate βBarReal := hβ.symm
  have hγconj : γBarReal'.HolderConjugate γBarReal := hγ.symm
  have hHC_K :
      Monotone.IsHemicontinuous (X := XBanach d βBarReal γBarReal)
        (K_Aepsi d βBarReal γBarReal)
        (Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
          (βBarReal' := βBarReal') (γBarReal' := γBarReal')
          V H DpH auxHypsK ε) :=
    Aepsi_hemicont_of_paperHypotheses_min (γBarReal := γBarReal)
      (βBarReal := βBarReal) (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      V H DpH auxHypsK hpow hAnalytic.h_slice hpow.toRegularityH hγBar_one_lt
      hβconj hγconj hV
      hAnalytic.hSegMin hAnalytic.hF_unreg_meas hAnalytic.hF_gat_meas
  -- K0-aux record (restricted to K0_Aepsi_W via `.mono`).
  have hAux_K :
      MFGOpEpsUniformAux (d := d) ε V H DpH γBarReal βBarReal βBarReal' γBarReal'
        (K0_Aepsi d βBarReal γBarReal) :=
    mfgOpEps_uniformAux_of_perPairAuxHyps ε
      (K0_Aepsi d βBarReal γBarReal) hAnalytic.auxHypsK0
  have hAux_W : MFGOpEpsUniformAux (d := d) ε V H DpH γBarReal βBarReal
                  βBarReal' γBarReal' (K0_Aepsi_W d βBarReal γBarReal) :=
    hAux_K.mono (K0_Aepsi_W_subset_K0_Aepsi d βBarReal γBarReal)
  -- Restrict monotonicity from K_Aepsi to K_Aepsi_W.
  have hMono_W :
      Monotone.IsMonotone (X := XBanach d βBarReal γBarReal)
        (K_Aepsi_W d βBarReal γBarReal)
        (Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
          (βBarReal' := βBarReal') (γBarReal' := γBarReal')
          V H DpH auxHypsK ε) := by
    intro v₁ hv₁ v₂ hv₂
    exact hMono_K (K_Aepsi_W_subset_K_Aepsi d βBarReal γBarReal hv₁)
                  (K_Aepsi_W_subset_K_Aepsi d βBarReal γBarReal hv₂)
  -- Restrict hemicontinuity from K_Aepsi to K_Aepsi_W.
  have hHC_W :
      Monotone.IsHemicontinuous (X := XBanach d βBarReal γBarReal)
        (K_Aepsi_W d βBarReal γBarReal)
        (Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
          (βBarReal' := βBarReal') (γBarReal' := γBarReal')
          V H DpH auxHypsK ε) := by
    intro u hu v hv w
    exact hHC_K (K_Aepsi_W_subset_K_Aepsi d βBarReal γBarReal hu)
                (K_Aepsi_W_subset_K_Aepsi d βBarReal γBarReal hv) w
  -- Build coercivity directly at `qRefW = qRef_simplePower`.
  have hCoerc_K :
      Monotone.IsCoerciveAt (X := XBanach d βBarReal γBarReal)
        (K_Aepsi d βBarReal γBarReal)
        (Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
          (βBarReal' := βBarReal') (γBarReal' := γBarReal')
          V H DpH auxHypsK ε)
        qRefW :=
    Aepsi_coercive_of_paperHypotheses_scaled (γBarReal := γBarReal)
      (βBarReal := βBarReal) (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      V H DpH auxHypsK ε
      (coercivityGaugeExponent βBarReal γBarReal)
      (one_lt_coercivityGaugeExponent hβ_gt1 hγBar_one_lt)
      hAnalytic.lamCoerc hAnalytic.hlamCoerc
      hAnalytic.Ccoerc hAnalytic.hbound_residue
  -- Restrict coercivity from K_Aepsi to K_Aepsi_W (same base point).
  have hCoerc_W :
      Monotone.IsCoerciveAt (X := XBanach d βBarReal γBarReal)
        (K_Aepsi_W d βBarReal γBarReal)
        (Aepsi_CLM_opK (γBarReal := γBarReal) (βBarReal := βBarReal)
          (βBarReal' := βBarReal') (γBarReal' := γBarReal')
          V H DpH auxHypsK ε)
        qRefW := by
    refine ⟨hqRef_W, ?_⟩
    have h_filt_le :
        Monotone.coerciveFilter (K_Aepsi_W d βBarReal γBarReal)
          ≤ Monotone.coerciveFilter (K_Aepsi d βBarReal γBarReal) := by
      unfold Monotone.coerciveFilter
      exact inf_le_inf_left _
        (Filter.principal_mono.mpr
          (K_Aepsi_W_subset_K_Aepsi d βBarReal γBarReal))
    exact hCoerc_K.tendsto.mono_left h_filt_le
  exact {
    hReflexive := hReflexive
    auxHypsK := auxHypsK
    qRef := qRefW
    hqRef := hqRef_W
    aux := hAux_W
    hMono := hMono_W
    hHC := hHC_W
    hCoerc := hCoerc_W
  }

/-- **Sanity-check `example`** for the refined-domain paper-exponent
specialisation (`_min` sibling).

`aepsiUniformContextK_W_of_paperHypotheses_closed_paper_min` accepts
the four primary paper hypotheses `(hε, hmon, hpow, hV)` plus the
paper-faithful analytic bundle `hAnalytic` and delivers an
`AepsiUniformContextK_W` at the paper exponents. -/
example
    {d : ℕ}
    {ε : ℝ}
    (hε : 0 < ε)
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : Hamiltonian.HypothesisMonotone H DpH)
    (hpow : Hamiltonian.HypothesisPowerGrowth H DpH)
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) V)
    [Fact (1 ≤ ENNReal.ofReal (hpow.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))]
    (hAnalytic : PaperSection8AnalyticResiduesMin
                    (d := d)
                    (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
                    (βBarReal := hpow.β + 1)
                    (βBarReal' := (hpow.β + 1) / hpow.β)
                    (γBarReal' := (hpow.α * (hpow.β + 1) / hpow.β)
                                    / (hpow.α * (hpow.β + 1) / hpow.β - 1))
                    ε V H DpH hpow) :
    AepsiUniformContextK_W (d := d) ε V H DpH
      (hpow.α * (hpow.β + 1) / hpow.β)
      (hpow.β + 1)
      ((hpow.β + 1) / hpow.β)
      ((hpow.α * (hpow.β + 1) / hpow.β)
        / (hpow.α * (hpow.β + 1) / hpow.β - 1)) :=
  aepsiUniformContextK_W_of_paperHypotheses_closed_paper_min
    hε hmon hpow hV hAnalytic


/-! ## Bare→Banach lift for set-narrow paper-form endpoints (Child A)

This section lands `bareToBanachPair_set_paper`: the lift that turns a
weak-limit triple `(mLim, uLim, DuLim)` plus a periodic, pointwise
nonneg, `MemLpPer βBar` perturbation `ρ` into a Banach pair
`q : XBanach d βBarReal γBarReal` whose primal projections agree
a.e.-on the unit cube with the bare-function endpoints
`(mLim + ρ, uLim, DuLim)`. The pair is built via
`MeasureTheory.MemLp.toLp` on the `m`-component and via
`Periodic.MemSobolevPer.toLpSobolev` on the `u`-component.

The four `bareToBanachPair_set_paper_*_ae_eq` lemmas establish the
a.e.-coercion identities, and `bareToBanachPair_set_paper_mem_K0Aepsi`
discharges K0-membership from the pointwise nonneg hypotheses on
`mLim` and `ρ`.

Per Child A of `infra-P5-mintyData-bareToBanach-bridge-set`, this lift
takes the underlying bare-function fields directly rather than a full
`WeakLimitInputBundleAE`: the bundle is defined in
`Banach/RegularizedSequence.lean`, which **imports** this file, so a
bundle-shaped input would create an import cycle. Call sites in or
after `RegularizedSequence` supply the fields by projection. -/

/-- **Bare→Banach lift for set-narrow paper-form endpoints.**

Given a bare-function weak-limit triple `(mLim, uLim, DuLim)` together
with the standard `MemLpPer` / `MemSobolevPer` regularity certificates
and a periodic, pointwise-nonneg, `MemLpPer βBar` perturbation `ρ`,
produce the Banach pair `q : XBanach d βBarReal γBarReal` whose
primal projections agree a.e. with `(mLim + ρ, uLim, DuLim)`. -/
noncomputable def bareToBanachPair_set_paper
    {d : ℕ} {βBarReal γBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {mLim uLim : (Fin d → ℝ) → ℝ}
    {DuLim : Fin d → (Fin d → ℝ) → ℝ}
    (hmLim_memLp : Periodic.MemLpPer (d := d)
                      (ENNReal.ofReal βBarReal) mLim)
    (huLim_sob : Periodic.MemSobolevPer (d := d)
                      (ENNReal.ofReal γBarReal) uLim)
    (hDuLim_memLp_γ : ∀ i, Periodic.MemLpPer (d := d)
                              (ENNReal.ofReal γBarReal) (DuLim i))
    {ρ : (Fin d → ℝ) → ℝ}
    (hρ_lp : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) ρ) :
    XBanach d βBarReal γBarReal :=
  ⟨(hmLim_memLp.add hρ_lp).toLp,
   huLim_sob.toLpSobolev (g := DuLim) hDuLim_memLp_γ⟩

/-- **A.e.-coercion identity (m-component).**

The Banach `m`-component of `bareToBanachPair_set_paper` agrees a.e.
on the unit cube with the bare-function endpoint `mLim + ρ`. -/
lemma bareToBanachPair_set_paper_mOf_ae_eq
    {d : ℕ} {βBarReal γBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {mLim uLim : (Fin d → ℝ) → ℝ}
    {DuLim : Fin d → (Fin d → ℝ) → ℝ}
    (hmLim_memLp : Periodic.MemLpPer (d := d)
                      (ENNReal.ofReal βBarReal) mLim)
    (huLim_sob : Periodic.MemSobolevPer (d := d)
                      (ENNReal.ofReal γBarReal) uLim)
    (hDuLim_memLp_γ : ∀ i, Periodic.MemLpPer (d := d)
                              (ENNReal.ofReal γBarReal) (DuLim i))
    {ρ : (Fin d → ℝ) → ℝ}
    (hρ_lp : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) ρ) :
    mOf (bareToBanachPair_set_paper (d := d) (βBarReal := βBarReal)
            (γBarReal := γBarReal)
            (DuLim := DuLim)
            hmLim_memLp huLim_sob hDuLim_memLp_γ hρ_lp)
      =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        (mLim + ρ) := by
  -- `mOf q = ⇑q.1` definitionally; `q.1 = (hmLim_memLp.add hρ_lp).toLp`.
  -- `MemLp.coeFn_toLp` gives `⇑(MemLp.toLp f hf) =ᵐ f`.
  have h := MeasureTheory.MemLp.coeFn_toLp
              (hmLim_memLp.add hρ_lp).toMemLp
  -- `h : ⇑((hmLim_memLp.add hρ_lp).toLp) =ᵐ mLim + ρ` (since `MemLp.toLp f hf`
  -- has `f` definitionally `mLim + ρ`).
  exact h

/-- **A.e.-coercion identity (u-component).**

The Banach `u`-value-component of `bareToBanachPair_set_paper` agrees
a.e. on the unit cube with the bare-function endpoint `uLim`. -/
lemma bareToBanachPair_set_paper_uOf_ae_eq
    {d : ℕ} {βBarReal γBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {mLim uLim : (Fin d → ℝ) → ℝ}
    {DuLim : Fin d → (Fin d → ℝ) → ℝ}
    (hmLim_memLp : Periodic.MemLpPer (d := d)
                      (ENNReal.ofReal βBarReal) mLim)
    (huLim_sob : Periodic.MemSobolevPer (d := d)
                      (ENNReal.ofReal γBarReal) uLim)
    (hDuLim_memLp_γ : ∀ i, Periodic.MemLpPer (d := d)
                              (ENNReal.ofReal γBarReal) (DuLim i))
    {ρ : (Fin d → ℝ) → ℝ}
    (hρ_lp : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) ρ) :
    uOf (bareToBanachPair_set_paper (d := d) (βBarReal := βBarReal)
            (γBarReal := γBarReal)
            (DuLim := DuLim)
            hmLim_memLp huLim_sob hDuLim_memLp_γ hρ_lp)
      =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        uLim := by
  -- `uOf q = ⇑q.2.1`; `q.2 = huLim_sob.toLpSobolev hDuLim_memLp_γ`,
  -- whose first projection is `huLim_sob.1.toLp`.
  exact MeasureTheory.MemLp.coeFn_toLp huLim_sob.1

/-- **A.e.-coercion identity (Du-component).**

The Banach `Du`-component of `bareToBanachPair_set_paper` agrees a.e.
on the unit cube with the bare-function endpoint `DuLim i` for every
coordinate `i`. -/
lemma bareToBanachPair_set_paper_DuOf_ae_eq
    {d : ℕ} {βBarReal γBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {mLim uLim : (Fin d → ℝ) → ℝ}
    {DuLim : Fin d → (Fin d → ℝ) → ℝ}
    (hmLim_memLp : Periodic.MemLpPer (d := d)
                      (ENNReal.ofReal βBarReal) mLim)
    (huLim_sob : Periodic.MemSobolevPer (d := d)
                      (ENNReal.ofReal γBarReal) uLim)
    (hDuLim_memLp_γ : ∀ i, Periodic.MemLpPer (d := d)
                              (ENNReal.ofReal γBarReal) (DuLim i))
    {ρ : (Fin d → ℝ) → ℝ}
    (hρ_lp : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) ρ)
    (i : Fin d) :
    DuOf (bareToBanachPair_set_paper (d := d) (βBarReal := βBarReal)
            (γBarReal := γBarReal)
            (DuLim := DuLim)
            hmLim_memLp huLim_sob hDuLim_memLp_γ hρ_lp) i
      =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        DuLim i := by
  -- `DuOf q i = ⇑(q.2.2 i)`; `q.2.2 i = (hDuLim_memLp_γ i).toLp`.
  exact MeasureTheory.MemLp.coeFn_toLp (hDuLim_memLp_γ i)

/-- **K0-membership of the set-narrow lift.**

If `mLim` is a.e. nonneg on the unit cube and the perturbation `ρ` is
pointwise nonneg, then the Banach `m`-component of
`bareToBanachPair_set_paper` is a.e. nonneg on the unit cube; that is,
the lifted pair lies in the closed nonneg cone `K0_Aepsi`. -/
lemma bareToBanachPair_set_paper_mem_K0Aepsi
    {d : ℕ} {βBarReal γBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
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
    {ρ : (Fin d → ℝ) → ℝ}
    (hρ_nn : ∀ x, 0 ≤ ρ x)
    (hρ_lp : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) ρ) :
    bareToBanachPair_set_paper (d := d) (βBarReal := βBarReal)
        (γBarReal := γBarReal)
        (DuLim := DuLim)
        hmLim_memLp huLim_sob hDuLim_memLp_γ hρ_lp
      ∈ K0_Aepsi d βBarReal γBarReal := by
  -- Unfold K0-membership: a.e. `0 ≤ ⇑q.1`.
  -- We have `⇑q.1 =ᵐ mLim + ρ` by `bareToBanachPair_set_paper_mOf_ae_eq`,
  -- and `0 ≤ mLim + ρ` follows from `hmLim_nn` and `hρ_nn`.
  have hmOf_eq :=
    bareToBanachPair_set_paper_mOf_ae_eq (d := d)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hρ_lp
  -- `mOf q = ⇑q.1` by `mOf_def`, so the goal `0 ≤ ⇑q.1` is the same
  -- a.e. statement as `0 ≤ mOf q`.
  show ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume
              (UnitCube d)),
        0 ≤ (⇑(bareToBanachPair_set_paper (d := d) (βBarReal := βBarReal)
                  (γBarReal := γBarReal) (DuLim := DuLim)
                  hmLim_memLp huLim_sob hDuLim_memLp_γ hρ_lp).1
              : (Fin d → ℝ) → ℝ) x
  filter_upwards [hmLim_nn, hmOf_eq] with x hx_nn hx_eq
  -- `hx_eq : mOf q x = (mLim + ρ) x`. Goal is `0 ≤ ⇑q.1 x`, which is
  -- `0 ≤ mOf q x` since `mOf q = ⇑q.1` definitionally.
  change 0 ≤ mOf (bareToBanachPair_set_paper (d := d) (βBarReal := βBarReal)
                  (γBarReal := γBarReal) (DuLim := DuLim)
                  hmLim_memLp huLim_sob hDuLim_memLp_γ hρ_lp) x
  rw [hx_eq]
  show 0 ≤ mLim x + ρ x
  exact add_nonneg hx_nn (hρ_nn x)

/-- **Sanity-check `example`** for the set-narrow paper-form lift.

The lift produces a Banach pair, the three a.e.-coercion identities
project to the bare-function endpoints, and K0-membership is
discharged from the nonneg hypotheses. -/
example
    {d : ℕ} {βBarReal γBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
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
    {ρ : (Fin d → ℝ) → ℝ}
    (hρ_nn : ∀ x, 0 ≤ ρ x)
    (hρ_lp : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) ρ) :
    ∃ q : XBanach d βBarReal γBarReal,
      q ∈ K0_Aepsi d βBarReal γBarReal ∧
        mOf q =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                    (UnitCube d)] (mLim + ρ) ∧
        uOf q =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                    (UnitCube d)] uLim ∧
        ∀ i, DuOf q i =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                            (UnitCube d)] DuLim i := by
  refine ⟨bareToBanachPair_set_paper (d := d) (βBarReal := βBarReal)
              (γBarReal := γBarReal) (DuLim := DuLim)
              hmLim_memLp huLim_sob hDuLim_memLp_γ hρ_lp,
          ?_, ?_, ?_, ?_⟩
  · exact bareToBanachPair_set_paper_mem_K0Aepsi
            (uLim := uLim) hmLim_memLp huLim_sob hDuLim_memLp_γ
            hmLim_nn hρ_nn hρ_lp
  · exact bareToBanachPair_set_paper_mOf_ae_eq
            hmLim_memLp huLim_sob hDuLim_memLp_γ hρ_lp
  · exact bareToBanachPair_set_paper_uOf_ae_eq
            (mLim := mLim) hmLim_memLp huLim_sob hDuLim_memLp_γ hρ_lp
  · intro i
    exact bareToBanachPair_set_paper_DuOf_ae_eq
            (mLim := mLim) hmLim_memLp huLim_sob hDuLim_memLp_γ hρ_lp i

/-! ## Bare→Banach lift for transport-narrow paper-form endpoints (Child A)

This section lands `bareToBanachPair_transport_paper`: the lift that turns
a weak-limit triple `(mLim, uLim, DuLim)` plus a `SmoothPeriodic d`
test-direction shift `ψ` into a Banach pair `q : XBanach d βBarReal γBarReal`
whose primal projections agree a.e. on the unit cube with the
bare-function endpoints `(mLim, uLim + ψ, DuLim i + ∂ᵢψ)`.

Unlike the set-narrow lift, the perturbation lives on the
`u` / `Du`-side: `u` is shifted by the smooth periodic test direction
and the gradient is shifted by its (classical = weak) partial
derivatives. The shift's `MemLpPer γBar`-regularity for every `γ̄` follows
from the smooth-periodic L^∞-bound packaged by
`Periodic.MemSobolevPer.of_smoothPeriodic`.
-/

/-- **Bare→Banach lift for transport-narrow paper-form endpoints.**

Given a bare-function weak-limit triple `(mLim, uLim, DuLim)` together
with the standard `MemLpPer` / `MemSobolevPer` regularity certificates
and a smooth periodic test direction `ψ : SmoothPeriodic d`, produce the
Banach pair `q : XBanach d βBarReal γBarReal` whose primal projections
agree a.e. on the unit cube with the shifted endpoints
`(mLim, uLim + ψ, fun i => DuLim i + ∂ᵢψ)`. -/
noncomputable def bareToBanachPair_transport_paper
    {d : ℕ} {βBarReal γBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {mLim uLim : (Fin d → ℝ) → ℝ}
    {DuLim : Fin d → (Fin d → ℝ) → ℝ}
    (hmLim_memLp : Periodic.MemLpPer (d := d)
                      (ENNReal.ofReal βBarReal) mLim)
    (huLim_sob : Periodic.MemSobolevPer (d := d)
                      (ENNReal.ofReal γBarReal) uLim)
    (hDuLim_memLp_γ : ∀ i, Periodic.MemLpPer (d := d)
                              (ENNReal.ofReal γBarReal) (DuLim i))
    (ψ : Periodic.SmoothPeriodic d) :
    XBanach d βBarReal γBarReal :=
  ⟨hmLim_memLp.toLp,
   ((huLim_sob.1.add
        ((Periodic.MemSobolevPer.of_smoothPeriodic
            (ENNReal.ofReal γBarReal) ψ).1)).toLp,
    fun i => ((hDuLim_memLp_γ i).add
        ((Periodic.MemSobolevPer.of_smoothPeriodic
            (ENNReal.ofReal γBarReal)
            (Periodic.SmoothPeriodic.partialDeriv i ψ)).1)).toLp)⟩

/-- **A.e.-coercion identity (m-component).**

The Banach `m`-component of `bareToBanachPair_transport_paper` agrees
a.e. on the unit cube with the bare-function endpoint `mLim`. -/
lemma bareToBanachPair_transport_paper_mOf_ae_eq
    {d : ℕ} {βBarReal γBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {mLim uLim : (Fin d → ℝ) → ℝ}
    {DuLim : Fin d → (Fin d → ℝ) → ℝ}
    (hmLim_memLp : Periodic.MemLpPer (d := d)
                      (ENNReal.ofReal βBarReal) mLim)
    (huLim_sob : Periodic.MemSobolevPer (d := d)
                      (ENNReal.ofReal γBarReal) uLim)
    (hDuLim_memLp_γ : ∀ i, Periodic.MemLpPer (d := d)
                              (ENNReal.ofReal γBarReal) (DuLim i))
    (ψ : Periodic.SmoothPeriodic d) :
    mOf (bareToBanachPair_transport_paper (d := d) (βBarReal := βBarReal)
            (γBarReal := γBarReal)
            (DuLim := DuLim)
            hmLim_memLp huLim_sob hDuLim_memLp_γ ψ)
      =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        mLim := by
  -- `mOf q = ⇑q.1 = ⇑(hmLim_memLp.toLp)`; `MemLp.coeFn_toLp` finishes.
  exact MeasureTheory.MemLp.coeFn_toLp hmLim_memLp

/-- **A.e.-coercion identity (u-component).**

The Banach `u`-value-component of `bareToBanachPair_transport_paper`
agrees a.e. on the unit cube with the shifted endpoint `uLim + ψ`. -/
lemma bareToBanachPair_transport_paper_uOf_ae_eq
    {d : ℕ} {βBarReal γBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {mLim uLim : (Fin d → ℝ) → ℝ}
    {DuLim : Fin d → (Fin d → ℝ) → ℝ}
    (hmLim_memLp : Periodic.MemLpPer (d := d)
                      (ENNReal.ofReal βBarReal) mLim)
    (huLim_sob : Periodic.MemSobolevPer (d := d)
                      (ENNReal.ofReal γBarReal) uLim)
    (hDuLim_memLp_γ : ∀ i, Periodic.MemLpPer (d := d)
                              (ENNReal.ofReal γBarReal) (DuLim i))
    (ψ : Periodic.SmoothPeriodic d) :
    uOf (bareToBanachPair_transport_paper (d := d) (βBarReal := βBarReal)
            (γBarReal := γBarReal)
            (DuLim := DuLim)
            hmLim_memLp huLim_sob hDuLim_memLp_γ ψ)
      =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        (uLim + (ψ : (Fin d → ℝ) → ℝ)) := by
  -- `uOf q = ⇑q.2.1 = ⇑((huLim_sob.1.add hψ_lp).toLp)`; `MemLp.coeFn_toLp`
  -- gives `⇑(MemLp.toLp f hf) =ᵐ f`, which here is `uLim + ψ`.
  have hψ_lp : Periodic.MemLpPer (d := d)
                  (ENNReal.ofReal γBarReal) ((ψ : (Fin d → ℝ) → ℝ)) :=
    (Periodic.MemSobolevPer.of_smoothPeriodic
        (ENNReal.ofReal γBarReal) ψ).1
  exact MeasureTheory.MemLp.coeFn_toLp
          (huLim_sob.1.add hψ_lp : MeasureTheory.MemLp _ _ _)

/-- **A.e.-coercion identity (Du-component).**

The Banach `Du`-component of `bareToBanachPair_transport_paper` agrees
a.e. on the unit cube with the shifted endpoint `DuLim i + ∂ᵢψ` for
every coordinate `i`. -/
lemma bareToBanachPair_transport_paper_DuOf_ae_eq
    {d : ℕ} {βBarReal γBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {mLim uLim : (Fin d → ℝ) → ℝ}
    {DuLim : Fin d → (Fin d → ℝ) → ℝ}
    (hmLim_memLp : Periodic.MemLpPer (d := d)
                      (ENNReal.ofReal βBarReal) mLim)
    (huLim_sob : Periodic.MemSobolevPer (d := d)
                      (ENNReal.ofReal γBarReal) uLim)
    (hDuLim_memLp_γ : ∀ i, Periodic.MemLpPer (d := d)
                              (ENNReal.ofReal γBarReal) (DuLim i))
    (ψ : Periodic.SmoothPeriodic d) (i : Fin d) :
    DuOf (bareToBanachPair_transport_paper (d := d) (βBarReal := βBarReal)
            (γBarReal := γBarReal)
            (DuLim := DuLim)
            hmLim_memLp huLim_sob hDuLim_memLp_γ ψ) i
      =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (UnitCube d)]
        (DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ
                      : (Fin d → ℝ) → ℝ)) := by
  -- `DuOf q i = ⇑(q.2.2 i) = ⇑(((hDuLim_memLp_γ i).add (hDPsi_lp)).toLp)`.
  have hDPsi_lp : Periodic.MemLpPer (d := d)
                  (ENNReal.ofReal γBarReal)
                  ((Periodic.SmoothPeriodic.partialDeriv i ψ
                      : (Fin d → ℝ) → ℝ)) :=
    (Periodic.MemSobolevPer.of_smoothPeriodic
        (ENNReal.ofReal γBarReal)
        (Periodic.SmoothPeriodic.partialDeriv i ψ)).1
  exact MeasureTheory.MemLp.coeFn_toLp
          ((hDuLim_memLp_γ i).add hDPsi_lp : MeasureTheory.MemLp _ _ _)

/-- **K0-membership of the transport-narrow lift.**

If `mLim` is a.e. nonneg on the unit cube, then the Banach `m`-component
of `bareToBanachPair_transport_paper` is a.e. nonneg on the unit cube;
that is, the lifted pair lies in the closed nonneg cone `K0_Aepsi`.

Unlike the set-narrow lift, the transport perturbation acts on the
`u` / `Du`-side only, so the `m`-component is exactly `mLim` (up to
`MemLp.toLp` a.e.-equality) and no pointwise nonneg input on a
perturbation is required. -/
lemma bareToBanachPair_transport_paper_mem_K0Aepsi
    {d : ℕ} {βBarReal γBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
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
    (ψ : Periodic.SmoothPeriodic d) :
    bareToBanachPair_transport_paper (d := d) (βBarReal := βBarReal)
        (γBarReal := γBarReal)
        (DuLim := DuLim)
        hmLim_memLp huLim_sob hDuLim_memLp_γ ψ
      ∈ K0_Aepsi d βBarReal γBarReal := by
  -- `mOf q =ᵐ mLim` by `bareToBanachPair_transport_paper_mOf_ae_eq`,
  -- and `mOf q = ⇑q.1` definitionally (`mOf_def`); transport
  -- `hmLim_nn` across the a.e.-equality.
  have hmOf_eq :=
    bareToBanachPair_transport_paper_mOf_ae_eq (d := d)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ ψ
  show ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume
              (UnitCube d)),
        0 ≤ (⇑(bareToBanachPair_transport_paper (d := d)
                  (βBarReal := βBarReal) (γBarReal := γBarReal)
                  (DuLim := DuLim)
                  hmLim_memLp huLim_sob hDuLim_memLp_γ ψ).1
              : (Fin d → ℝ) → ℝ) x
  filter_upwards [hmLim_nn, hmOf_eq] with x hx_nn hx_eq
  -- `hx_eq : mOf q x = mLim x`; goal is `0 ≤ ⇑q.1 x = mOf q x`.
  change 0 ≤ mOf (bareToBanachPair_transport_paper (d := d)
                  (βBarReal := βBarReal) (γBarReal := γBarReal)
                  (DuLim := DuLim)
                  hmLim_memLp huLim_sob hDuLim_memLp_γ ψ) x
  rw [hx_eq]
  exact hx_nn

/-- **Sanity-check `example`** for the transport-narrow paper-form lift.

The lift produces a Banach pair, and the three a.e.-coercion identities
project to the bare-function endpoints `(mLim, uLim + ψ, DuLim i + ∂ᵢψ)`. -/
example
    {d : ℕ} {βBarReal γBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {mLim uLim : (Fin d → ℝ) → ℝ}
    {DuLim : Fin d → (Fin d → ℝ) → ℝ}
    (hmLim_memLp : Periodic.MemLpPer (d := d)
                      (ENNReal.ofReal βBarReal) mLim)
    (huLim_sob : Periodic.MemSobolevPer (d := d)
                      (ENNReal.ofReal γBarReal) uLim)
    (hDuLim_memLp_γ : ∀ i, Periodic.MemLpPer (d := d)
                              (ENNReal.ofReal γBarReal) (DuLim i))
    (ψ : Periodic.SmoothPeriodic d) :
    ∃ q : XBanach d βBarReal γBarReal,
      mOf q =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                  (UnitCube d)] mLim ∧
      uOf q =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                  (UnitCube d)] (uLim + (ψ : (Fin d → ℝ) → ℝ)) ∧
      ∀ i, DuOf q i =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                          (UnitCube d)]
              (DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ
                            : (Fin d → ℝ) → ℝ)) := by
  refine ⟨bareToBanachPair_transport_paper (d := d) (βBarReal := βBarReal)
              (γBarReal := γBarReal) (DuLim := DuLim)
              hmLim_memLp huLim_sob hDuLim_memLp_γ ψ,
          ?_, ?_, ?_⟩
  · exact bareToBanachPair_transport_paper_mOf_ae_eq
            (uLim := uLim) hmLim_memLp huLim_sob hDuLim_memLp_γ ψ
  · exact bareToBanachPair_transport_paper_uOf_ae_eq
            (mLim := mLim) hmLim_memLp huLim_sob hDuLim_memLp_γ ψ
  · intro i
    exact bareToBanachPair_transport_paper_DuOf_ae_eq
            (mLim := mLim) hmLim_memLp huLim_sob hDuLim_memLp_γ ψ i

/-! ## Set-narrow segment `MemLpPer` bundle (Child B)

This section packages the **nine `MemLpPer p`-of-power certificates**
required by `hemicontSegmentData_of_K0Aepsi` (lines 4353–4374 of this
file) as a self-contained record `SetPaperSegMemLpBundle`, together
with a producer `segMemLpBundle_of_setPaper` that builds the bundle
from bare-function endpoint data.

### Strategy

The two endpoints `q₁, q₂` come from the Child A lift
`bareToBanachPair_set_paper` applied to a common weak-limit triple
`(mLim, uLim, DuLim)` and two perturbations `ρ₁, ρ₂`. The four
a.e.-coercion identities established by Child A
(`bareToBanachPair_set_paper_{m,u,Du}Of_ae_eq`) give

* `mOf qᵢ =ᵐ mLim + ρᵢ`,
* `uOf qᵢ =ᵐ uLim`,
* `DuOf qᵢ i' =ᵐ DuLim i'`.

So each of the nine bound expressions in
`(mOf q₁, mOf q₂, uOf q₁, uOf q₂, DuOf q₁, DuOf q₂)` is a.e. equal to
the same expression in `(mLim + ρ₁, mLim + ρ₂, uLim, uLim, DuLim, DuLim)`.
We ask the caller to supply nine `MemLpPer` certificates for the bare
expressions, and use `MeasureTheory.MemLp.ae_eq` to transport them to
the Banach versions. -/

/-- **Set-narrow segment `MemLpPer` bundle.**

The nine `MemLpPer p`-of-power certificates required by
`hemicontSegmentData_of_K0Aepsi` for two Banach endpoints
`q₁, q₂ : XBanach d βBarReal γBarReal` and `HypothesisPowerGrowth`
exponents `h.α, h.β`, with `Lᵖ` exponents `βBarReal'` and `γBarReal'`
(typically Hölder conjugates of `βBarReal, γBarReal`) and an unrelated
`γBar` (used in the gateaux power). -/
structure SetPaperSegMemLpBundle
    {d : ℕ} {βBarReal γBarReal βBarReal' γBarReal' γBar : ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (q₁ q₂ : XBanach d βBarReal γBarReal)
    (h : HypothesisPowerGrowth (d := d) H DpH) (_γBar : ℝ := γBar) where
  /-- `|u| + |u|` in `L^{β̄'}`. -/
  hΔυ : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x => |uOf q₂ x| + |uOf q₁ x|)
  /-- `‖|Du| + |Du|‖^α + 1` in `L^{β̄'}`. -/
  hΔp_pow : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x =>
                ‖fun i => |DuOf q₂ i x| + |DuOf q₁ i x|‖ ^ h.α + 1)
  /-- `(|m| + |m|)^β + 1` in `L^{β̄'}`. -/
  hΔm_pow : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x => (|mOf q₂ x| + |mOf q₁ x|) ^ h.β + 1)
  /-- `(|m| + |m|) · ‖|Du| + |Du|‖^{α-1}` in `L^{γ̄'}`. -/
  hΔm_grad : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => (|mOf q₂ x| + |mOf q₁ x|)
                  * ‖fun i => |DuOf q₂ i x| + |DuOf q₁ i x|‖ ^ (h.α - 1))
  /-- `(|m| + |m|)^{1+β-β/α}` in `L^{γ̄'}`. -/
  hΔm_endpoint : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => (|mOf q₂ x| + |mOf q₁ x|) ^ (1 + h.β - h.β / h.α))
  /-- `|m| + |m|` in `L^{γ̄'}`. -/
  hΔm : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => |mOf q₂ x| + |mOf q₁ x|)
  /-- `(|m| + |m|) + 1` in `L^{β̄'}`. -/
  hΔm1 : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x => (|mOf q₂ x| + |mOf q₁ x|) + 1)
  /-- `(∑ i, (|Du| + |Du|)^2)^{(γBar-1)/2}` in `L^{γ̄'}`. -/
  hG_grad : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x =>
                (∑ i, (|DuOf q₂ i x| + |DuOf q₁ i x|) ^ (2 : ℕ))
                    ^ ((γBar - 1) / 2))
  /-- `(|u| + |u|)^{γBar-1}` in `L^{γ̄'}`. -/
  hG_val : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => (|uOf q₂ x| + |uOf q₁ x|) ^ (γBar - 1))

/-- **Producer `segMemLpBundle_of_setPaper`.**

Given the Child A inputs (a bare-function weak-limit triple
`(mLim, uLim, DuLim)` with `MemLpPer` / `MemSobolevPer` regularity, and
two periodic, pointwise-nonneg, `MemLpPer βBar` perturbations `ρ₁, ρ₂`)
together with nine bare-function `MemLpPer` certificates for the
expressions in `(mLim, ρ₁, ρ₂, uLim, DuLim)` corresponding to the nine
bundle fields, produce the `SetPaperSegMemLpBundle` for the lifted
endpoints `q₁ := lift(ρ₁), q₂ := lift(ρ₂)`. -/
noncomputable def segMemLpBundle_of_setPaper
    {d : ℕ} {βBarReal γBarReal βBarReal' γBarReal' γBar : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
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
    (h : HypothesisPowerGrowth (d := d) H DpH)
    -- Bare-function certificates: each is the same shape as the
    -- corresponding bundle field but with the projections expanded by
    -- the Child A a.e.-coercions.
    (bΔυ : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x => |uLim x| + |uLim x|))
    (bΔp_pow : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x =>
                ‖fun i => |DuLim i x| + |DuLim i x|‖ ^ h.α + 1))
    (bΔm_pow : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x =>
                (|(mLim + ρ₂) x| + |(mLim + ρ₁) x|) ^ h.β + 1))
    (bΔm_grad : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => (|(mLim + ρ₂) x| + |(mLim + ρ₁) x|)
                  * ‖fun i => |DuLim i x| + |DuLim i x|‖ ^ (h.α - 1)))
    (bΔm_endpoint : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x =>
                (|(mLim + ρ₂) x| + |(mLim + ρ₁) x|) ^
                  (1 + h.β - h.β / h.α)))
    (bΔm : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => |(mLim + ρ₂) x| + |(mLim + ρ₁) x|))
    (bΔm1 : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x => (|(mLim + ρ₂) x| + |(mLim + ρ₁) x|) + 1))
    (bG_grad : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x =>
                (∑ i, (|DuLim i x| + |DuLim i x|) ^ (2 : ℕ))
                    ^ ((γBar - 1) / 2)))
    (bG_val : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => (|uLim x| + |uLim x|) ^ (γBar - 1))) :
    SetPaperSegMemLpBundle (d := d) (βBarReal := βBarReal)
        (γBarReal := γBarReal) (βBarReal' := βBarReal')
        (γBarReal' := γBarReal') (γBar := γBar)
        (H := H) (DpH := DpH)
      (bareToBanachPair_set_paper (d := d) (βBarReal := βBarReal)
        (γBarReal := γBarReal) (DuLim := DuLim)
        hmLim_memLp huLim_sob hDuLim_memLp_γ hρ₁_lp)
      (bareToBanachPair_set_paper (d := d) (βBarReal := βBarReal)
        (γBarReal := γBarReal) (DuLim := DuLim)
        hmLim_memLp huLim_sob hDuLim_memLp_γ hρ₂_lp)
      h := by
  -- Abbreviations for the two lifted Banach pairs.
  set q₁ := bareToBanachPair_set_paper (d := d) (βBarReal := βBarReal)
        (γBarReal := γBarReal) (DuLim := DuLim)
        hmLim_memLp huLim_sob hDuLim_memLp_γ hρ₁_lp with hq₁_def
  set q₂ := bareToBanachPair_set_paper (d := d) (βBarReal := βBarReal)
        (γBarReal := γBarReal) (DuLim := DuLim)
        hmLim_memLp huLim_sob hDuLim_memLp_γ hρ₂_lp with hq₂_def
  -- The four a.e.-coercion identities from Child A.
  have hm₁ :
      mOf q₁ =ᵐ[MeasureTheory.Measure.restrict
                  MeasureTheory.volume (UnitCube d)] (mLim + ρ₁) :=
    bareToBanachPair_set_paper_mOf_ae_eq (d := d)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hρ₁_lp
  have hm₂ :
      mOf q₂ =ᵐ[MeasureTheory.Measure.restrict
                  MeasureTheory.volume (UnitCube d)] (mLim + ρ₂) :=
    bareToBanachPair_set_paper_mOf_ae_eq (d := d)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hρ₂_lp
  have hu₁ :
      uOf q₁ =ᵐ[MeasureTheory.Measure.restrict
                  MeasureTheory.volume (UnitCube d)] uLim :=
    bareToBanachPair_set_paper_uOf_ae_eq (d := d)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hρ₁_lp
  have hu₂ :
      uOf q₂ =ᵐ[MeasureTheory.Measure.restrict
                  MeasureTheory.volume (UnitCube d)] uLim :=
    bareToBanachPair_set_paper_uOf_ae_eq (d := d)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hρ₂_lp
  have hDu₁ : ∀ i,
      DuOf q₁ i =ᵐ[MeasureTheory.Measure.restrict
                      MeasureTheory.volume (UnitCube d)] DuLim i := fun i =>
    bareToBanachPair_set_paper_DuOf_ae_eq (d := d)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hρ₁_lp i
  have hDu₂ : ∀ i,
      DuOf q₂ i =ᵐ[MeasureTheory.Measure.restrict
                      MeasureTheory.volume (UnitCube d)] DuLim i := fun i =>
    bareToBanachPair_set_paper_DuOf_ae_eq (d := d)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hρ₂_lp i
  -- We will transport each bare cert via `MemLp.ae_eq` after producing
  -- the corresponding `=ᵐ` witness by `filter_upwards`.
  refine
    { hΔυ := ?_, hΔp_pow := ?_, hΔm_pow := ?_, hΔm_grad := ?_,
      hΔm_endpoint := ?_, hΔm := ?_, hΔm1 := ?_,
      hG_grad := ?_, hG_val := ?_ }
  · -- `hΔυ`: `|uOf q₂| + |uOf q₁|` =ᵐ `|uLim| + |uLim|`.
    have heq :
        (fun x => |uLim x| + |uLim x|)
          =ᵐ[MeasureTheory.Measure.restrict
                MeasureTheory.volume (UnitCube d)]
            (fun x => |uOf q₂ x| + |uOf q₁ x|) := by
      filter_upwards [hu₁, hu₂] with x hx₁ hx₂
      simp [hx₁, hx₂]
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq heq bΔυ.toMemLp)
  · -- `hΔp_pow`.
    have heq :
        (fun x =>
            ‖fun i => |DuLim i x| + |DuLim i x|‖ ^ h.α + 1)
          =ᵐ[MeasureTheory.Measure.restrict
                MeasureTheory.volume (UnitCube d)]
            (fun x =>
              ‖fun i => |DuOf q₂ i x| + |DuOf q₁ i x|‖ ^ h.α + 1) := by
      have hDuAll :
          ∀ᵐ x ∂(MeasureTheory.Measure.restrict
                  MeasureTheory.volume (UnitCube d)),
            ∀ i, DuOf q₁ i x = DuLim i x ∧ DuOf q₂ i x = DuLim i x := by
        rw [MeasureTheory.ae_all_iff]
        intro i
        filter_upwards [hDu₁ i, hDu₂ i] with x ha hb
        exact ⟨ha, hb⟩
      filter_upwards [hDuAll] with x hx
      have hfun :
          (fun i => |DuLim i x| + |DuLim i x|)
            = (fun i => |DuOf q₂ i x| + |DuOf q₁ i x|) := by
        funext i
        rcases hx i with ⟨h₁, h₂⟩
        simp [h₁, h₂]
      rw [hfun]
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq heq bΔp_pow.toMemLp)
  · -- `hΔm_pow`.
    have heq :
        (fun x => (|(mLim + ρ₂) x| + |(mLim + ρ₁) x|) ^ h.β + 1)
          =ᵐ[MeasureTheory.Measure.restrict
                MeasureTheory.volume (UnitCube d)]
            (fun x => (|mOf q₂ x| + |mOf q₁ x|) ^ h.β + 1) := by
      filter_upwards [hm₁, hm₂] with x hx₁ hx₂
      simp [hx₁, hx₂]
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq heq bΔm_pow.toMemLp)
  · -- `hΔm_grad`.
    have heq :
        (fun x => (|(mLim + ρ₂) x| + |(mLim + ρ₁) x|)
            * ‖fun i => |DuLim i x| + |DuLim i x|‖ ^ (h.α - 1))
          =ᵐ[MeasureTheory.Measure.restrict
                MeasureTheory.volume (UnitCube d)]
            (fun x => (|mOf q₂ x| + |mOf q₁ x|)
              * ‖fun i => |DuOf q₂ i x| + |DuOf q₁ i x|‖ ^ (h.α - 1)) := by
      have hDuAll :
          ∀ᵐ x ∂(MeasureTheory.Measure.restrict
                  MeasureTheory.volume (UnitCube d)),
            ∀ i, DuOf q₁ i x = DuLim i x ∧ DuOf q₂ i x = DuLim i x := by
        rw [MeasureTheory.ae_all_iff]
        intro i
        filter_upwards [hDu₁ i, hDu₂ i] with x ha hb
        exact ⟨ha, hb⟩
      filter_upwards [hm₁, hm₂, hDuAll] with x hx₁ hx₂ hxDu
      have hfun :
          (fun i => |DuLim i x| + |DuLim i x|)
            = (fun i => |DuOf q₂ i x| + |DuOf q₁ i x|) := by
        funext i
        rcases hxDu i with ⟨h₁, h₂⟩
        simp [h₁, h₂]
      simp [hx₁, hx₂, hfun]
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq heq bΔm_grad.toMemLp)
  · -- `hΔm_endpoint`.
    have heq :
        (fun x => (|(mLim + ρ₂) x| + |(mLim + ρ₁) x|)
            ^ (1 + h.β - h.β / h.α))
          =ᵐ[MeasureTheory.Measure.restrict
                MeasureTheory.volume (UnitCube d)]
            (fun x => (|mOf q₂ x| + |mOf q₁ x|)
              ^ (1 + h.β - h.β / h.α)) := by
      filter_upwards [hm₁, hm₂] with x hx₁ hx₂
      simp [hx₁, hx₂]
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq heq bΔm_endpoint.toMemLp)
  · -- `hΔm`.
    have heq :
        (fun x => |(mLim + ρ₂) x| + |(mLim + ρ₁) x|)
          =ᵐ[MeasureTheory.Measure.restrict
                MeasureTheory.volume (UnitCube d)]
            (fun x => |mOf q₂ x| + |mOf q₁ x|) := by
      filter_upwards [hm₁, hm₂] with x hx₁ hx₂
      simp [hx₁, hx₂]
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq heq bΔm.toMemLp)
  · -- `hΔm1`.
    have heq :
        (fun x => (|(mLim + ρ₂) x| + |(mLim + ρ₁) x|) + 1)
          =ᵐ[MeasureTheory.Measure.restrict
                MeasureTheory.volume (UnitCube d)]
            (fun x => (|mOf q₂ x| + |mOf q₁ x|) + 1) := by
      filter_upwards [hm₁, hm₂] with x hx₁ hx₂
      simp [hx₁, hx₂]
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq heq bΔm1.toMemLp)
  · -- `hG_grad`.
    have heq :
        (fun x =>
            (∑ i, (|DuLim i x| + |DuLim i x|) ^ (2 : ℕ))
              ^ ((γBar - 1) / 2))
          =ᵐ[MeasureTheory.Measure.restrict
                MeasureTheory.volume (UnitCube d)]
            (fun x =>
              (∑ i, (|DuOf q₂ i x| + |DuOf q₁ i x|) ^ (2 : ℕ))
                ^ ((γBar - 1) / 2)) := by
      have hDuAll :
          ∀ᵐ x ∂(MeasureTheory.Measure.restrict
                  MeasureTheory.volume (UnitCube d)),
            ∀ i, DuOf q₁ i x = DuLim i x ∧ DuOf q₂ i x = DuLim i x := by
        rw [MeasureTheory.ae_all_iff]
        intro i
        filter_upwards [hDu₁ i, hDu₂ i] with x ha hb
        exact ⟨ha, hb⟩
      filter_upwards [hDuAll] with x hx
      have hsum :
          (∑ i, (|DuLim i x| + |DuLim i x|) ^ (2 : ℕ))
            = ∑ i, (|DuOf q₂ i x| + |DuOf q₁ i x|) ^ (2 : ℕ) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        rcases hx i with ⟨h₁, h₂⟩
        simp [h₁, h₂]
      rw [hsum]
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq heq bG_grad.toMemLp)
  · -- `hG_val`.
    have heq :
        (fun x => (|uLim x| + |uLim x|) ^ (γBar - 1))
          =ᵐ[MeasureTheory.Measure.restrict
                MeasureTheory.volume (UnitCube d)]
            (fun x => (|uOf q₂ x| + |uOf q₁ x|) ^ (γBar - 1)) := by
      filter_upwards [hu₁, hu₂] with x hx₁ hx₂
      simp [hx₁, hx₂]
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq heq bG_val.toMemLp)

/-- **Sanity-check `example`** for the set-narrow segment `MemLpPer`
bundle. Given the Child A inputs and nine bare-function `MemLpPer`
certificates for the bound expressions in `(mLim, ρ₁, ρ₂, uLim, DuLim)`,
the bundle is produced for the lifted endpoints. -/
example
    {d : ℕ} {βBarReal γBarReal βBarReal' γBarReal' γBar : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
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
    (h : HypothesisPowerGrowth (d := d) H DpH)
    (bΔυ : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x => |uLim x| + |uLim x|))
    (bΔp_pow : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x =>
                ‖fun i => |DuLim i x| + |DuLim i x|‖ ^ h.α + 1))
    (bΔm_pow : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x =>
                (|(mLim + ρ₂) x| + |(mLim + ρ₁) x|) ^ h.β + 1))
    (bΔm_grad : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => (|(mLim + ρ₂) x| + |(mLim + ρ₁) x|)
                  * ‖fun i => |DuLim i x| + |DuLim i x|‖ ^ (h.α - 1)))
    (bΔm_endpoint : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x =>
                (|(mLim + ρ₂) x| + |(mLim + ρ₁) x|) ^
                  (1 + h.β - h.β / h.α)))
    (bΔm : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => |(mLim + ρ₂) x| + |(mLim + ρ₁) x|))
    (bΔm1 : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x => (|(mLim + ρ₂) x| + |(mLim + ρ₁) x|) + 1))
    (bG_grad : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x =>
                (∑ i, (|DuLim i x| + |DuLim i x|) ^ (2 : ℕ))
                    ^ ((γBar - 1) / 2)))
    (bG_val : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => (|uLim x| + |uLim x|) ^ (γBar - 1))) :
    SetPaperSegMemLpBundle (d := d) (βBarReal := βBarReal)
        (γBarReal := γBarReal) (βBarReal' := βBarReal')
        (γBarReal' := γBarReal') (γBar := γBar)
        (H := H) (DpH := DpH)
      (bareToBanachPair_set_paper (d := d) (βBarReal := βBarReal)
        (γBarReal := γBarReal) (DuLim := DuLim)
        hmLim_memLp huLim_sob hDuLim_memLp_γ hρ₁_lp)
      (bareToBanachPair_set_paper (d := d) (βBarReal := βBarReal)
        (γBarReal := γBarReal) (DuLim := DuLim)
        hmLim_memLp huLim_sob hDuLim_memLp_γ hρ₂_lp)
      h :=
  segMemLpBundle_of_setPaper (d := d) (βBarReal := βBarReal)
    (γBarReal := γBarReal) (βBarReal' := βBarReal')
    (γBarReal' := γBarReal') (γBar := γBar)
    (H := H) (DpH := DpH)
    hmLim_memLp huLim_sob hDuLim_memLp_γ hρ₁_lp hρ₂_lp h
    bΔυ bΔp_pow bΔm_pow bΔm_grad bΔm_endpoint bΔm bΔm1 bG_grad bG_val

/-! ## Final composer: `hemicontSegmentData_set_narrow_of_paperHypotheses`
(Child D)

Headline composer that builds, from the bare-function paper-form
weak-limit triple `(mLim, uLim, DuLim)`, two perturbations `ρ₁, ρ₂`,
their nine `MemLpPer` segment-power dominator certs, the K_Aepsi-form
per-endpoint `MFGOpEpsAuxHyps` records, and a B-class strict-positivity
certificate `hPosSeg` at the bare endpoints `(mLim+ρ₁, mLim+ρ₂)`, the
final bare-function-parameterised `HemicontSegmentData` bundle for
the set-family narrow domain.

The composer combines:
* Child A `bareToBanachPair_set_paper` (Banach lift) +
  `bareToBanachPair_set_paper_mem_K0Aepsi` (K0 membership),
* Child B `segMemLpBundle_of_setPaper` (nine MemLpPer dominator certs),
* Child C `isHK0AbsDominator_of_paperHypotheses`,
  `isMDpHK0Dominator_of_paperHypotheses` (K0 dominator producers),
* iter 0499 `hemicontSegmentData_of_K0Aepsi` (K0-form producer), and
* iter 0499 `HemicontSegmentData.ae_eq` (bare-function transport).

The output bundle is `HemicontSegmentData V H DpH γBar DuLim DuLim
(mLim + ρ₁) (mLim + ρ₂) uLim uLim Dν η ν`. -/
noncomputable def hemicontSegmentData_set_narrow_of_paperHypotheses
    {d : ℕ} {γBarReal βBarReal βBarReal' γBarReal' γBar : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    -- Paper hypotheses (Child C inputs).
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    -- Hölder-pair facts on the real exponents.
    (hβconj : βBarReal'.HolderConjugate βBarReal)
    (hγconj : γBarReal'.HolderConjugate γBarReal)
    -- Bare-function weak-limit triple regularity.
    {mLim uLim : (Fin d → ℝ) → ℝ}
    {DuLim : Fin d → (Fin d → ℝ) → ℝ}
    (hmLim_memLp : Periodic.MemLpPer (d := d)
                      (ENNReal.ofReal βBarReal) mLim)
    (huLim_sob : Periodic.MemSobolevPer (d := d)
                      (ENNReal.ofReal γBarReal) uLim)
    (hDuLim_memLp_γ : ∀ i, Periodic.MemLpPer (d := d)
                              (ENNReal.ofReal γBarReal) (DuLim i))
    -- Pointwise nonneg of `mLim` (a.e.) and pointwise nonneg of the
    -- perturbations (used by Child A to discharge K0 membership).
    (hmLim_nn : 0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                      (UnitCube d)] mLim)
    -- Perturbations.
    {ρ₁ ρ₂ : (Fin d → ℝ) → ℝ}
    (hρ₁_nn : ∀ x, 0 ≤ ρ₁ x)
    (hρ₂_nn : ∀ x, 0 ≤ ρ₂ x)
    (hρ₁_lp : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) ρ₁)
    (hρ₂_lp : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) ρ₂)
    -- Per-endpoint `MFGOpEpsAuxHyps` records at the lifted Banach
    -- projections (caller-supplied; documentary for the K0 producer).
    (aux₁ : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
              V H DpH
              (DuOf (bareToBanachPair_set_paper (d := d)
                      (βBarReal := βBarReal) (γBarReal := γBarReal)
                      (DuLim := DuLim)
                      hmLim_memLp huLim_sob hDuLim_memLp_γ hρ₁_lp))
              (mOf (bareToBanachPair_set_paper (d := d)
                      (βBarReal := βBarReal) (γBarReal := γBarReal)
                      (DuLim := DuLim)
                      hmLim_memLp huLim_sob hDuLim_memLp_γ hρ₁_lp))
              (uOf (bareToBanachPair_set_paper (d := d)
                      (βBarReal := βBarReal) (γBarReal := γBarReal)
                      (DuLim := DuLim)
                      hmLim_memLp huLim_sob hDuLim_memLp_γ hρ₁_lp)))
    (aux₂ : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
              V H DpH
              (DuOf (bareToBanachPair_set_paper (d := d)
                      (βBarReal := βBarReal) (γBarReal := γBarReal)
                      (DuLim := DuLim)
                      hmLim_memLp huLim_sob hDuLim_memLp_γ hρ₂_lp))
              (mOf (bareToBanachPair_set_paper (d := d)
                      (βBarReal := βBarReal) (γBarReal := γBarReal)
                      (DuLim := DuLim)
                      hmLim_memLp huLim_sob hDuLim_memLp_γ hρ₂_lp))
              (uOf (bareToBanachPair_set_paper (d := d)
                      (βBarReal := βBarReal) (γBarReal := γBarReal)
                      (DuLim := DuLim)
                      hmLim_memLp huLim_sob hDuLim_memLp_γ hρ₂_lp)))
    -- Nine bare-function `MemLpPer p`-of-power certificates (Child B).
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
    (bΔm1 : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x => (|(mLim + ρ₂) x| + |(mLim + ρ₁) x|) + 1))
    (bG_grad : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x =>
                (∑ i, (|DuLim i x| + |DuLim i x|) ^ (2 : ℕ))
                    ^ ((γBar - 1) / 2)))
    (bG_val : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => (|uLim x| + |uLim x|) ^ (γBar - 1)))
    -- B-class caller-supplied strict-positivity certificate at the
    -- bare endpoints `(mLim + ρ₁, mLim + ρ₂)` (e.g. from a
    -- perturbation residue `μ_n := μ + 1/n`).
    (hPosSeg : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
                ∀ t ∈ Set.Icc (0 : ℝ) 1,
                  0 < cxComb (mLim + ρ₁) (mLim + ρ₂) t x)
    -- The product-form Gateaux pointwise bound requires `1 < γBar`.
    (hγ_one_lt : 1 < γBar)
    -- Test direction with its `MemLpPer`-regularity.
    (Dν : Fin d → (Fin d → ℝ) → ℝ) (η ν : (Fin d → ℝ) → ℝ)
    (hη : MemLpPer (d := d) (ENNReal.ofReal βBarReal) η)
    (hDν : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dν i))
    (hν_β : MemLpPer (d := d) (ENNReal.ofReal βBarReal) ν)
    (hν_γ : MemLpPer (d := d) (ENNReal.ofReal γBarReal) ν)
    (hγBar_eq : γBar = γBarReal)
    -- `V`-regularity at the conjugate exponent.
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    -- Caratheodory measurability of the segment integrands at the
    -- **bare** endpoints (genuinely test-direction-dependent residues).
    (hF_unreg_meas_bare : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x => aepsiIntegrandAt_unreg V H DpH
                    DuLim DuLim (mLim + ρ₁) (mLim + ρ₂)
                    uLim uLim Dν η ν x t)
        (MeasureTheory.volume.restrict (UnitCube d)))
    (hF_gat_meas_bare : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x => aepsiIntegrandAt_gateaux γBar
                    DuLim DuLim uLim uLim Dν ν x t)
        (MeasureTheory.volume.restrict (UnitCube d))) :
    HemicontSegmentData V H DpH γBar
      DuLim DuLim (mLim + ρ₁) (mLim + ρ₂)
      uLim uLim Dν η ν := by
  -- Build the two Banach pairs via Child A.
  set q₁ := bareToBanachPair_set_paper (d := d) (βBarReal := βBarReal)
              (γBarReal := γBarReal) (DuLim := DuLim)
              hmLim_memLp huLim_sob hDuLim_memLp_γ hρ₁_lp with hq₁_def
  set q₂ := bareToBanachPair_set_paper (d := d) (βBarReal := βBarReal)
              (γBarReal := γBarReal) (DuLim := DuLim)
              hmLim_memLp huLim_sob hDuLim_memLp_γ hρ₂_lp with hq₂_def
  -- K0 memberships from Child A.
  have hq₁_K0 : q₁ ∈ K0_Aepsi d βBarReal γBarReal :=
    bareToBanachPair_set_paper_mem_K0Aepsi (uLim := uLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hmLim_nn hρ₁_nn hρ₁_lp
  have hq₂_K0 : q₂ ∈ K0_Aepsi d βBarReal γBarReal :=
    bareToBanachPair_set_paper_mem_K0Aepsi (uLim := uLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hmLim_nn hρ₂_nn hρ₂_lp
  -- The four a.e.-coercion identities from Child A.
  have hm₁ :
      mOf q₁ =ᵐ[MeasureTheory.Measure.restrict
                  MeasureTheory.volume (UnitCube d)] (mLim + ρ₁) :=
    bareToBanachPair_set_paper_mOf_ae_eq (d := d)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hρ₁_lp
  have hm₂ :
      mOf q₂ =ᵐ[MeasureTheory.Measure.restrict
                  MeasureTheory.volume (UnitCube d)] (mLim + ρ₂) :=
    bareToBanachPair_set_paper_mOf_ae_eq (d := d)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hρ₂_lp
  have hu₁ :
      uOf q₁ =ᵐ[MeasureTheory.Measure.restrict
                  MeasureTheory.volume (UnitCube d)] uLim :=
    bareToBanachPair_set_paper_uOf_ae_eq (d := d)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hρ₁_lp
  have hu₂ :
      uOf q₂ =ᵐ[MeasureTheory.Measure.restrict
                  MeasureTheory.volume (UnitCube d)] uLim :=
    bareToBanachPair_set_paper_uOf_ae_eq (d := d)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hρ₂_lp
  have hDu₁ : ∀ i,
      DuOf q₁ i =ᵐ[MeasureTheory.Measure.restrict
                      MeasureTheory.volume (UnitCube d)] DuLim i := fun i =>
    bareToBanachPair_set_paper_DuOf_ae_eq (d := d)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hρ₁_lp i
  have hDu₂ : ∀ i,
      DuOf q₂ i =ᵐ[MeasureTheory.Measure.restrict
                      MeasureTheory.volume (UnitCube d)] DuLim i := fun i =>
    bareToBanachPair_set_paper_DuOf_ae_eq (d := d)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hρ₂_lp i
  -- Child B: build the `SetPaperSegMemLpBundle`.
  have segBundle :=
    segMemLpBundle_of_setPaper (d := d) (βBarReal := βBarReal)
      (γBarReal := γBarReal) (βBarReal' := βBarReal')
      (γBarReal' := γBarReal') (γBar := γBar)
      (H := H) (DpH := DpH)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hρ₁_lp hρ₂_lp hpow
      bΔυ bΔp_pow bΔm_pow bΔm_grad bΔm_endpoint bΔm bΔm1 bG_grad bG_val
  -- Child C: K0 dominator certs at `(mOf q₁, mOf q₂, DuOf q₁, DuOf q₂)`.
  have hHabs_K0 :
      IsHK0AbsDominator (d := d) hpow (mOf q₁) (mOf q₂)
                          (DuOf q₁) (DuOf q₂) hpow.C :=
    isHK0AbsDominator_of_paperHypotheses hpow hHat0 hAgree
      (mOf q₁) (mOf q₂) (DuOf q₁) (DuOf q₂)
  have hmDpH_K0 :
      IsmDpHK0Dominator (d := d) hpow (mOf q₁) (mOf q₂)
                          (DuOf q₁) (DuOf q₂) :=
    isMDpHK0Dominator_of_paperHypotheses hpow hHat0 hAgree
      (mOf q₁) (mOf q₂) (DuOf q₁) (DuOf q₂)
  -- Transport `hPosSeg` backwards from `(mLim+ρ₁, mLim+ρ₂)` to
  -- `(mOf q₁, mOf q₂)` via `cxComb_congr_ae` (using `hm₁.symm, hm₂.symm`).
  have hPosSeg_q :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          0 < cxComb (mOf q₁) (mOf q₂) t x := by
    -- Use `cxComb_congr_ae` with `hm₁.symm : (mLim+ρ₁) =ᵐ mOf q₁` and
    -- `hm₂.symm : (mLim+ρ₂) =ᵐ mOf q₂`.
    have hcomb :
        ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
          ∀ t : ℝ,
            cxComb (mLim + ρ₁) (mLim + ρ₂) t x = cxComb (mOf q₁) (mOf q₂) t x :=
      cxComb_congr_ae hm₁.symm hm₂.symm
    filter_upwards [hPosSeg, hcomb] with x hPosx hcombx t ht
    have := hPosx t ht
    rw [hcombx t] at this
    exact this
  -- Transport the nine bare-function `MemLpPer` certs to the Banach
  -- coercions: this is exactly the content of `segBundle`. Unpack it.
  obtain ⟨bhΔυ, bhΔp_pow, bhΔm_pow, bhΔm_grad, bhΔm_endpoint,
          bhΔm, bhΔm1, bhG_grad, bhG_val⟩ := segBundle
  -- Build the bare measurability witnesses pulled back to `(qᵢ-coercions)`.
  -- Use the a.e.-equality of the integrand functions.
  have hF_unreg_eq :=
    aepsiIntegrandAt_unreg_congr_ae V H DpH Dν η ν
      hm₁ hm₂ hu₁ hu₂ hDu₁ hDu₂
  have hF_gat_eq :=
    aepsiIntegrandAt_gateaux_congr_ae γBar Dν ν
      hu₁ hu₂ hDu₁ hDu₂
  have hF_unreg_meas_q :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        MeasureTheory.AEStronglyMeasurable
          (fun x => aepsiIntegrandAt_unreg V H DpH
                      (DuOf q₁) (DuOf q₂) (mOf q₁) (mOf q₂)
                      (uOf q₁) (uOf q₂) Dν η ν x t)
          (MeasureTheory.volume.restrict (UnitCube d)) := by
    intro t ht
    have hmeas := hF_unreg_meas_bare t ht
    refine hmeas.congr ?_
    filter_upwards [hF_unreg_eq] with x hx
    exact (hx t).symm
  have hF_gat_meas_q :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        MeasureTheory.AEStronglyMeasurable
          (fun x => aepsiIntegrandAt_gateaux γBar
                      (DuOf q₁) (DuOf q₂) (uOf q₁) (uOf q₂) Dν ν x t)
          (MeasureTheory.volume.restrict (UnitCube d)) := by
    intro t ht
    have hmeas := hF_gat_meas_bare t ht
    refine hmeas.congr ?_
    filter_upwards [hF_gat_eq] with x hx
    exact (hx t).symm
  -- Call the K0 producer to get the bundle at the Banach coercions.
  have dataQ :
      HemicontSegmentData V H DpH γBar
        (DuOf q₁) (DuOf q₂) (mOf q₁) (mOf q₂)
        (uOf q₁) (uOf q₂) Dν η ν :=
    hemicontSegmentData_of_K0Aepsi (γBarReal := γBarReal)
      (βBarReal := βBarReal) (βBarReal' := βBarReal')
      (γBarReal' := γBarReal') (γBar := γBar) (V := V)
      hq₁_K0 hq₂_K0 aux₁ aux₂ hβconj hγconj hpow
      hpow.C hpow.hC hHabs_K0 hmDpH_K0 hPosSeg_q
      hγ_one_lt Dν η ν hη hDν hν_β hν_γ hγBar_eq
      hV bhΔυ bhΔp_pow bhΔm_pow bhΔm_grad bhΔm_endpoint
      bhΔm bhΔm1 bhG_grad bhG_val hF_unreg_meas_q hF_gat_meas_q
  -- Transport the bundle from `(mOf qᵢ, …)` to `(mLim + ρᵢ, uLim, …)`.
  exact HemicontSegmentData.ae_eq V H DpH γBar Dν η ν
    hm₁ hm₂ hu₁ hu₂ hDu₁ hDu₂ dataQ

/-- **Sanity-check `example`** for the Child D headline composer.
At symbolic inputs, `hemicontSegmentData_set_narrow_of_paperHypotheses`
produces the bare-function-parameterised `HemicontSegmentData`. -/
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
    {ρ₁ ρ₂ : (Fin d → ℝ) → ℝ}
    (hρ₁_nn : ∀ x, 0 ≤ ρ₁ x) (hρ₂_nn : ∀ x, 0 ≤ ρ₂ x)
    (hρ₁_lp : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) ρ₁)
    (hρ₂_lp : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) ρ₂)
    (aux₁ : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
              V H DpH
              (DuOf (bareToBanachPair_set_paper (d := d)
                      (βBarReal := βBarReal) (γBarReal := γBarReal)
                      (DuLim := DuLim)
                      hmLim_memLp huLim_sob hDuLim_memLp_γ hρ₁_lp))
              (mOf (bareToBanachPair_set_paper (d := d)
                      (βBarReal := βBarReal) (γBarReal := γBarReal)
                      (DuLim := DuLim)
                      hmLim_memLp huLim_sob hDuLim_memLp_γ hρ₁_lp))
              (uOf (bareToBanachPair_set_paper (d := d)
                      (βBarReal := βBarReal) (γBarReal := γBarReal)
                      (DuLim := DuLim)
                      hmLim_memLp huLim_sob hDuLim_memLp_γ hρ₁_lp)))
    (aux₂ : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
              V H DpH
              (DuOf (bareToBanachPair_set_paper (d := d)
                      (βBarReal := βBarReal) (γBarReal := γBarReal)
                      (DuLim := DuLim)
                      hmLim_memLp huLim_sob hDuLim_memLp_γ hρ₂_lp))
              (mOf (bareToBanachPair_set_paper (d := d)
                      (βBarReal := βBarReal) (γBarReal := γBarReal)
                      (DuLim := DuLim)
                      hmLim_memLp huLim_sob hDuLim_memLp_γ hρ₂_lp))
              (uOf (bareToBanachPair_set_paper (d := d)
                      (βBarReal := βBarReal) (γBarReal := γBarReal)
                      (DuLim := DuLim)
                      hmLim_memLp huLim_sob hDuLim_memLp_γ hρ₂_lp)))
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
    (bΔm1 : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x => (|(mLim + ρ₂) x| + |(mLim + ρ₁) x|) + 1))
    (bG_grad : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x =>
                (∑ i, (|DuLim i x| + |DuLim i x|) ^ (2 : ℕ))
                    ^ ((γBar - 1) / 2)))
    (bG_val : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => (|uLim x| + |uLim x|) ^ (γBar - 1)))
    (hPosSeg : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
                ∀ t ∈ Set.Icc (0 : ℝ) 1,
                  0 < cxComb (mLim + ρ₁) (mLim + ρ₂) t x)
    (hγ_one_lt : 1 < γBar)
    (Dν : Fin d → (Fin d → ℝ) → ℝ) (η ν : (Fin d → ℝ) → ℝ)
    (hη : MemLpPer (d := d) (ENNReal.ofReal βBarReal) η)
    (hDν : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dν i))
    (hν_β : MemLpPer (d := d) (ENNReal.ofReal βBarReal) ν)
    (hν_γ : MemLpPer (d := d) (ENNReal.ofReal γBarReal) ν)
    (hγBar_eq : γBar = γBarReal)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (hF_unreg_meas_bare : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x => aepsiIntegrandAt_unreg V H DpH
                    DuLim DuLim (mLim + ρ₁) (mLim + ρ₂)
                    uLim uLim Dν η ν x t)
        (MeasureTheory.volume.restrict (UnitCube d)))
    (hF_gat_meas_bare : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x => aepsiIntegrandAt_gateaux γBar
                    DuLim DuLim uLim uLim Dν ν x t)
        (MeasureTheory.volume.restrict (UnitCube d))) :
    HemicontSegmentData V H DpH γBar
      DuLim DuLim (mLim + ρ₁) (mLim + ρ₂)
      uLim uLim Dν η ν :=
  hemicontSegmentData_set_narrow_of_paperHypotheses
    (γBarReal := γBarReal) (βBarReal := βBarReal)
    (βBarReal' := βBarReal') (γBarReal' := γBarReal') (γBar := γBar)
    (V := V) (H := H) (DpH := DpH)
    hpow hHat0 hAgree hβconj hγconj
    hmLim_memLp huLim_sob hDuLim_memLp_γ hmLim_nn
    hρ₁_nn hρ₂_nn hρ₁_lp hρ₂_lp aux₁ aux₂
    bΔυ bΔp_pow bΔm_pow bΔm_grad bΔm_endpoint bΔm bΔm1 bG_grad bG_val
    hPosSeg hγ_one_lt Dν η ν hη hDν hν_β hν_γ hγBar_eq hV
    hF_unreg_meas_bare hF_gat_meas_bare

/-! ## Signed-narrow K0-membership and headline composer

For the signed family `D_signed_family_paper_nn`, the perturbation `g`
is *not* required pointwise nonneg — only the joint primal `mLim + g`
is a.e. nonneg on the unit cube. The bare→Banach lift
`bareToBanachPair_set_paper` is shape-agnostic and applies verbatim
(it only consumes the `MemLpPer βBar`-regularity of `g`). The single
material change is in the K0-membership discharge: instead of
`add_nonneg hmLim_nn hρ_nn` we feed the joint a.e.-nonneg directly.
The headline composer
`hemicontSegmentData_signed_narrow_of_paperHypotheses` then mirrors
its set-narrow sibling, swapping out only the K0 step. -/

/-- **K0-membership of the bare→Banach lift, joint-nonneg variant.**

Same as `bareToBanachPair_set_paper_mem_K0Aepsi`, but takes the joint
a.e.-nonnegativity `0 ≤ᵐ mLim + g` directly (rather than separate
`hmLim_nn` and `hρ_nn` from which `add_nonneg` reconstructs the joint
hypothesis). This is the form needed by the signed-family residue,
where the perturbation `g` may itself be sign-changing. -/
lemma bareToBanachPair_set_paper_mem_K0Aepsi_jointNN
    {d : ℕ} {βBarReal γBarReal : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {mLim uLim : (Fin d → ℝ) → ℝ}
    {DuLim : Fin d → (Fin d → ℝ) → ℝ}
    (hmLim_memLp : Periodic.MemLpPer (d := d)
                      (ENNReal.ofReal βBarReal) mLim)
    (huLim_sob : Periodic.MemSobolevPer (d := d)
                      (ENNReal.ofReal γBarReal) uLim)
    (hDuLim_memLp_γ : ∀ i, Periodic.MemLpPer (d := d)
                              (ENNReal.ofReal γBarReal) (DuLim i))
    {g : (Fin d → ℝ) → ℝ}
    (hg_lp : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) g)
    (hjoint_nn :
      0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
              (UnitCube d)] (fun x => mLim x + g x)) :
    bareToBanachPair_set_paper (d := d) (βBarReal := βBarReal)
        (γBarReal := γBarReal)
        (DuLim := DuLim)
        hmLim_memLp huLim_sob hDuLim_memLp_γ hg_lp
      ∈ K0_Aepsi d βBarReal γBarReal := by
  have hmOf_eq :=
    bareToBanachPair_set_paper_mOf_ae_eq (d := d)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hg_lp
  show ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume
              (UnitCube d)),
        0 ≤ (⇑(bareToBanachPair_set_paper (d := d) (βBarReal := βBarReal)
                  (γBarReal := γBarReal) (DuLim := DuLim)
                  hmLim_memLp huLim_sob hDuLim_memLp_γ hg_lp).1
              : (Fin d → ℝ) → ℝ) x
  filter_upwards [hjoint_nn, hmOf_eq] with x hx_nn hx_eq
  change 0 ≤ mOf (bareToBanachPair_set_paper (d := d) (βBarReal := βBarReal)
                  (γBarReal := γBarReal) (DuLim := DuLim)
                  hmLim_memLp huLim_sob hDuLim_memLp_γ hg_lp) x
  rw [hx_eq]
  -- `hx_eq : mOf q x = (mLim + g) x`, `hx_nn : 0 ≤ (fun x => mLim x + g x) x`.
  show 0 ≤ mLim x + g x
  exact hx_nn

/-- **Final composer (signed family, narrow paper-form, nonneg primal).**

Mirrors `hemicontSegmentData_set_narrow_of_paperHypotheses`, but for the
signed-family narrow domain `D_signed_family_paper_nn`: the perturbations
`g₁, g₂` are not required pointwise nonneg; instead the joint primals
`mLim + g₁, mLim + g₂` are each a.e. nonneg on the unit cube.
Internally the signed K0 producer
`bareToBanachPair_set_paper_mem_K0Aepsi_jointNN` replaces the set
producer `bareToBanachPair_set_paper_mem_K0Aepsi`; the rest of the
proof (Child B segment-`Lᵖ` bundle, Child C K0 dominators, K0-form
`hemicontSegmentData_of_K0Aepsi`, and `HemicontSegmentData.ae_eq`
transport) is shape-identical to the set version. -/
noncomputable def hemicontSegmentData_signed_narrow_of_paperHypotheses
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
    -- Signed-family perturbations: only `MemLpPer` regularity is required.
    {g₁ g₂ : (Fin d → ℝ) → ℝ}
    (hg₁_lp : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) g₁)
    (hg₂_lp : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) g₂)
    -- Joint primal a.e.-nonnegativity at each endpoint.
    (hjoint₁_nn :
      0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
              (UnitCube d)] (fun x => mLim x + g₁ x))
    (hjoint₂_nn :
      0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
              (UnitCube d)] (fun x => mLim x + g₂ x))
    (aux₁ : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
              V H DpH
              (DuOf (bareToBanachPair_set_paper (d := d)
                      (βBarReal := βBarReal) (γBarReal := γBarReal)
                      (DuLim := DuLim)
                      hmLim_memLp huLim_sob hDuLim_memLp_γ hg₁_lp))
              (mOf (bareToBanachPair_set_paper (d := d)
                      (βBarReal := βBarReal) (γBarReal := γBarReal)
                      (DuLim := DuLim)
                      hmLim_memLp huLim_sob hDuLim_memLp_γ hg₁_lp))
              (uOf (bareToBanachPair_set_paper (d := d)
                      (βBarReal := βBarReal) (γBarReal := γBarReal)
                      (DuLim := DuLim)
                      hmLim_memLp huLim_sob hDuLim_memLp_γ hg₁_lp)))
    (aux₂ : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
              V H DpH
              (DuOf (bareToBanachPair_set_paper (d := d)
                      (βBarReal := βBarReal) (γBarReal := γBarReal)
                      (DuLim := DuLim)
                      hmLim_memLp huLim_sob hDuLim_memLp_γ hg₂_lp))
              (mOf (bareToBanachPair_set_paper (d := d)
                      (βBarReal := βBarReal) (γBarReal := γBarReal)
                      (DuLim := DuLim)
                      hmLim_memLp huLim_sob hDuLim_memLp_γ hg₂_lp))
              (uOf (bareToBanachPair_set_paper (d := d)
                      (βBarReal := βBarReal) (γBarReal := γBarReal)
                      (DuLim := DuLim)
                      hmLim_memLp huLim_sob hDuLim_memLp_γ hg₂_lp)))
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
    (bΔm1 : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x => (|(mLim + g₂) x| + |(mLim + g₁) x|) + 1))
    (bG_grad : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x =>
                (∑ i, (|DuLim i x| + |DuLim i x|) ^ (2 : ℕ))
                    ^ ((γBar - 1) / 2)))
    (bG_val : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => (|uLim x| + |uLim x|) ^ (γBar - 1)))
    (hPosSeg : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
                ∀ t ∈ Set.Icc (0 : ℝ) 1,
                  0 < cxComb (mLim + g₁) (mLim + g₂) t x)
    (hγ_one_lt : 1 < γBar)
    (Dν : Fin d → (Fin d → ℝ) → ℝ) (η ν : (Fin d → ℝ) → ℝ)
    (hη : MemLpPer (d := d) (ENNReal.ofReal βBarReal) η)
    (hDν : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dν i))
    (hν_β : MemLpPer (d := d) (ENNReal.ofReal βBarReal) ν)
    (hν_γ : MemLpPer (d := d) (ENNReal.ofReal γBarReal) ν)
    (hγBar_eq : γBar = γBarReal)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (hF_unreg_meas_bare : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x => aepsiIntegrandAt_unreg V H DpH
                    DuLim DuLim (mLim + g₁) (mLim + g₂)
                    uLim uLim Dν η ν x t)
        (MeasureTheory.volume.restrict (UnitCube d)))
    (hF_gat_meas_bare : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x => aepsiIntegrandAt_gateaux γBar
                    DuLim DuLim uLim uLim Dν ν x t)
        (MeasureTheory.volume.restrict (UnitCube d))) :
    HemicontSegmentData V H DpH γBar
      DuLim DuLim (mLim + g₁) (mLim + g₂)
      uLim uLim Dν η ν := by
  -- Build the two Banach pairs via Child A.
  set q₁ := bareToBanachPair_set_paper (d := d) (βBarReal := βBarReal)
              (γBarReal := γBarReal) (DuLim := DuLim)
              hmLim_memLp huLim_sob hDuLim_memLp_γ hg₁_lp with hq₁_def
  set q₂ := bareToBanachPair_set_paper (d := d) (βBarReal := βBarReal)
              (γBarReal := γBarReal) (DuLim := DuLim)
              hmLim_memLp huLim_sob hDuLim_memLp_γ hg₂_lp with hq₂_def
  -- K0 memberships from the joint-NN variant of Child A.
  have hq₁_K0 : q₁ ∈ K0_Aepsi d βBarReal γBarReal :=
    bareToBanachPair_set_paper_mem_K0Aepsi_jointNN (uLim := uLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hg₁_lp hjoint₁_nn
  have hq₂_K0 : q₂ ∈ K0_Aepsi d βBarReal γBarReal :=
    bareToBanachPair_set_paper_mem_K0Aepsi_jointNN (uLim := uLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hg₂_lp hjoint₂_nn
  -- The four a.e.-coercion identities from Child A.
  have hm₁ :
      mOf q₁ =ᵐ[MeasureTheory.Measure.restrict
                  MeasureTheory.volume (UnitCube d)] (mLim + g₁) :=
    bareToBanachPair_set_paper_mOf_ae_eq (d := d)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hg₁_lp
  have hm₂ :
      mOf q₂ =ᵐ[MeasureTheory.Measure.restrict
                  MeasureTheory.volume (UnitCube d)] (mLim + g₂) :=
    bareToBanachPair_set_paper_mOf_ae_eq (d := d)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hg₂_lp
  have hu₁ :
      uOf q₁ =ᵐ[MeasureTheory.Measure.restrict
                  MeasureTheory.volume (UnitCube d)] uLim :=
    bareToBanachPair_set_paper_uOf_ae_eq (d := d)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hg₁_lp
  have hu₂ :
      uOf q₂ =ᵐ[MeasureTheory.Measure.restrict
                  MeasureTheory.volume (UnitCube d)] uLim :=
    bareToBanachPair_set_paper_uOf_ae_eq (d := d)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hg₂_lp
  have hDu₁ : ∀ i,
      DuOf q₁ i =ᵐ[MeasureTheory.Measure.restrict
                      MeasureTheory.volume (UnitCube d)] DuLim i := fun i =>
    bareToBanachPair_set_paper_DuOf_ae_eq (d := d)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hg₁_lp i
  have hDu₂ : ∀ i,
      DuOf q₂ i =ᵐ[MeasureTheory.Measure.restrict
                      MeasureTheory.volume (UnitCube d)] DuLim i := fun i =>
    bareToBanachPair_set_paper_DuOf_ae_eq (d := d)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hg₂_lp i
  -- Child B: build the `SetPaperSegMemLpBundle`.
  have segBundle :=
    segMemLpBundle_of_setPaper (d := d) (βBarReal := βBarReal)
      (γBarReal := γBarReal) (βBarReal' := βBarReal')
      (γBarReal' := γBarReal') (γBar := γBar)
      (H := H) (DpH := DpH)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hg₁_lp hg₂_lp hpow
      bΔυ bΔp_pow bΔm_pow bΔm_grad bΔm_endpoint bΔm bΔm1 bG_grad bG_val
  -- Child C: K0 dominator certs.
  have hHabs_K0 :
      IsHK0AbsDominator (d := d) hpow (mOf q₁) (mOf q₂)
                          (DuOf q₁) (DuOf q₂) hpow.C :=
    isHK0AbsDominator_of_paperHypotheses hpow hHat0 hAgree
      (mOf q₁) (mOf q₂) (DuOf q₁) (DuOf q₂)
  have hmDpH_K0 :
      IsmDpHK0Dominator (d := d) hpow (mOf q₁) (mOf q₂)
                          (DuOf q₁) (DuOf q₂) :=
    isMDpHK0Dominator_of_paperHypotheses hpow hHat0 hAgree
      (mOf q₁) (mOf q₂) (DuOf q₁) (DuOf q₂)
  -- Transport `hPosSeg` backwards from `(mLim+g₁, mLim+g₂)` to
  -- `(mOf q₁, mOf q₂)`.
  have hPosSeg_q :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          0 < cxComb (mOf q₁) (mOf q₂) t x := by
    have hcomb :
        ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
          ∀ t : ℝ,
            cxComb (mLim + g₁) (mLim + g₂) t x = cxComb (mOf q₁) (mOf q₂) t x :=
      cxComb_congr_ae hm₁.symm hm₂.symm
    filter_upwards [hPosSeg, hcomb] with x hPosx hcombx t ht
    have := hPosx t ht
    rw [hcombx t] at this
    exact this
  obtain ⟨bhΔυ, bhΔp_pow, bhΔm_pow, bhΔm_grad, bhΔm_endpoint,
          bhΔm, bhΔm1, bhG_grad, bhG_val⟩ := segBundle
  have hF_unreg_eq :=
    aepsiIntegrandAt_unreg_congr_ae V H DpH Dν η ν
      hm₁ hm₂ hu₁ hu₂ hDu₁ hDu₂
  have hF_gat_eq :=
    aepsiIntegrandAt_gateaux_congr_ae γBar Dν ν
      hu₁ hu₂ hDu₁ hDu₂
  have hF_unreg_meas_q :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        MeasureTheory.AEStronglyMeasurable
          (fun x => aepsiIntegrandAt_unreg V H DpH
                      (DuOf q₁) (DuOf q₂) (mOf q₁) (mOf q₂)
                      (uOf q₁) (uOf q₂) Dν η ν x t)
          (MeasureTheory.volume.restrict (UnitCube d)) := by
    intro t ht
    have hmeas := hF_unreg_meas_bare t ht
    refine hmeas.congr ?_
    filter_upwards [hF_unreg_eq] with x hx
    exact (hx t).symm
  have hF_gat_meas_q :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        MeasureTheory.AEStronglyMeasurable
          (fun x => aepsiIntegrandAt_gateaux γBar
                      (DuOf q₁) (DuOf q₂) (uOf q₁) (uOf q₂) Dν ν x t)
          (MeasureTheory.volume.restrict (UnitCube d)) := by
    intro t ht
    have hmeas := hF_gat_meas_bare t ht
    refine hmeas.congr ?_
    filter_upwards [hF_gat_eq] with x hx
    exact (hx t).symm
  have dataQ :
      HemicontSegmentData V H DpH γBar
        (DuOf q₁) (DuOf q₂) (mOf q₁) (mOf q₂)
        (uOf q₁) (uOf q₂) Dν η ν :=
    hemicontSegmentData_of_K0Aepsi (γBarReal := γBarReal)
      (βBarReal := βBarReal) (βBarReal' := βBarReal')
      (γBarReal' := γBarReal') (γBar := γBar) (V := V)
      hq₁_K0 hq₂_K0 aux₁ aux₂ hβconj hγconj hpow
      hpow.C hpow.hC hHabs_K0 hmDpH_K0 hPosSeg_q
      hγ_one_lt Dν η ν hη hDν hν_β hν_γ hγBar_eq
      hV bhΔυ bhΔp_pow bhΔm_pow bhΔm_grad bhΔm_endpoint
      bhΔm bhΔm1 bhG_grad bhG_val hF_unreg_meas_q hF_gat_meas_q
  exact HemicontSegmentData.ae_eq V H DpH γBar Dν η ν
    hm₁ hm₂ hu₁ hu₂ hDu₁ hDu₂ dataQ


/-! ## Transport-narrow segment `MemLpPer` bundle (Child B, transport-family)

This section packages the **nine `MemLpPer p`-of-power certificates**
required by `hemicontSegmentData_of_K0Aepsi` for the **transport-narrow**
domain into a self-contained record `TransportPaperSegMemLpBundle`,
together with a producer `segMemLpBundle_of_transportPaper` that builds
the bundle from bare-function endpoint data and two smooth periodic
test directions `ψ₁, ψ₂`.

### Strategy (parallel to set-narrow iter 0502)

The two endpoints `q₁, q₂` come from the iter-0510 Child A
transport-narrow lift `bareToBanachPair_transport_paper` applied to a
common weak-limit triple `(mLim, uLim, DuLim)` and two perturbations
`ψ₁, ψ₂`. The three a.e.-coercion identities established by Child A
(`bareToBanachPair_transport_paper_{m,u,Du}Of_ae_eq`) give

* `mOf qᵢ =ᵐ mLim`,
* `uOf qᵢ =ᵐ uLim + ψᵢ`,
* `DuOf qᵢ i' =ᵐ DuLim i' + ∂ᵢ'ψᵢ`.

So each of the nine bound expressions in
`(mOf q₁, mOf q₂, uOf q₁, uOf q₂, DuOf q₁, DuOf q₂)` is a.e. equal to
the corresponding expression in
`(mLim, mLim, uLim+ψ₁, uLim+ψ₂, DuLim+∂ψ₁, DuLim+∂ψ₂)`. The caller
supplies nine bare expressions in this last form, and we transport
them to the Banach versions via `MeasureTheory.MemLp.ae_eq`. (The
bare certs in turn are produced from `MemLpPer` certs of the
weak-limit `uLim, DuLim, mLim` powers via triangle inequality and
`MemSobolevPer.of_smoothPeriodic`'s L^∞-closure for the ψ pieces; that
is the caller's job, not the producer's.) -/

/-- **Transport-narrow segment `MemLpPer` bundle.**

The nine `MemLpPer p`-of-power certificates required by
`hemicontSegmentData_of_K0Aepsi` for two Banach endpoints
`q₁, q₂ : XBanach d βBarReal γBarReal` and `HypothesisPowerGrowth`
exponents `h.α, h.β`, with `Lᵖ` exponents `βBarReal'` and `γBarReal'`
(typically Hölder conjugates of `βBarReal, γBarReal`) and an unrelated
`γBar` (used in the gateaux power).

The fields are stated in terms of `mOf qⱼ, uOf qⱼ, DuOf qⱼ` exactly as
in `SetPaperSegMemLpBundle` — only the producer differs (transport-
narrow lift vs. set-narrow lift). -/
structure TransportPaperSegMemLpBundle
    {d : ℕ} {βBarReal γBarReal βBarReal' γBarReal' γBar : ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (q₁ q₂ : XBanach d βBarReal γBarReal)
    (h : HypothesisPowerGrowth (d := d) H DpH) (_γBar : ℝ := γBar) where
  /-- `|u| + |u|` in `L^{β̄'}`. -/
  hΔυ : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x => |uOf q₂ x| + |uOf q₁ x|)
  /-- `‖|Du| + |Du|‖^α + 1` in `L^{β̄'}`. -/
  hΔp_pow : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x =>
                ‖fun i => |DuOf q₂ i x| + |DuOf q₁ i x|‖ ^ h.α + 1)
  /-- `(|m| + |m|)^β + 1` in `L^{β̄'}`. -/
  hΔm_pow : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x => (|mOf q₂ x| + |mOf q₁ x|) ^ h.β + 1)
  /-- `(|m| + |m|) · ‖|Du| + |Du|‖^{α-1}` in `L^{γ̄'}`. -/
  hΔm_grad : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => (|mOf q₂ x| + |mOf q₁ x|)
                  * ‖fun i => |DuOf q₂ i x| + |DuOf q₁ i x|‖ ^ (h.α - 1))
  /-- `(|m| + |m|)^{1+β-β/α}` in `L^{γ̄'}`. -/
  hΔm_endpoint : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => (|mOf q₂ x| + |mOf q₁ x|) ^ (1 + h.β - h.β / h.α))
  /-- `|m| + |m|` in `L^{γ̄'}`. -/
  hΔm : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => |mOf q₂ x| + |mOf q₁ x|)
  /-- `(|m| + |m|) + 1` in `L^{β̄'}`. -/
  hΔm1 : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x => (|mOf q₂ x| + |mOf q₁ x|) + 1)
  /-- `(∑ i, (|Du| + |Du|)^2)^{(γBar-1)/2}` in `L^{γ̄'}`. -/
  hG_grad : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x =>
                (∑ i, (|DuOf q₂ i x| + |DuOf q₁ i x|) ^ (2 : ℕ))
                    ^ ((γBar - 1) / 2))
  /-- `(|u| + |u|)^{γBar-1}` in `L^{γ̄'}`. -/
  hG_val : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => (|uOf q₂ x| + |uOf q₁ x|) ^ (γBar - 1))

/-- **Producer `segMemLpBundle_of_transportPaper`.**

Given the Child A inputs (a bare-function weak-limit triple
`(mLim, uLim, DuLim)` with `MemLpPer` / `MemSobolevPer` regularity, and
two smooth periodic test directions `ψ₁, ψ₂`) together with nine
bare-function `MemLpPer` certificates for the expressions in
`(mLim, uLim+ψ₁, uLim+ψ₂, DuLim+∂ψ₁, DuLim+∂ψ₂)` corresponding to the
nine bundle fields, produce the `TransportPaperSegMemLpBundle` for the
lifted endpoints
`q₁ := bareToBanachPair_transport_paper … ψ₁`,
`q₂ := bareToBanachPair_transport_paper … ψ₂`.

The triangle-inequality / smooth-periodic ψ closure work that derives
each bare cert from `MemLpPer` certificates of the weak-limit triple is
the caller's responsibility; this producer only handles the a.e.
transport from the bare-function form to the Banach-projection form. -/
noncomputable def segMemLpBundle_of_transportPaper
    {d : ℕ} {βBarReal γBarReal βBarReal' γBarReal' γBar : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {mLim uLim : (Fin d → ℝ) → ℝ}
    {DuLim : Fin d → (Fin d → ℝ) → ℝ}
    (hmLim_memLp : Periodic.MemLpPer (d := d)
                      (ENNReal.ofReal βBarReal) mLim)
    (huLim_sob : Periodic.MemSobolevPer (d := d)
                      (ENNReal.ofReal γBarReal) uLim)
    (hDuLim_memLp_γ : ∀ i, Periodic.MemLpPer (d := d)
                              (ENNReal.ofReal γBarReal) (DuLim i))
    (ψ₁ ψ₂ : Periodic.SmoothPeriodic d)
    (h : HypothesisPowerGrowth (d := d) H DpH)
    -- Bare-function certificates: each is the same shape as the
    -- corresponding bundle field but with the projections expanded by
    -- the iter-0510 Child A a.e.-coercions.
    (bΔυ : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x => |(uLim + (ψ₂ : (Fin d → ℝ) → ℝ)) x|
                          + |(uLim + (ψ₁ : (Fin d → ℝ) → ℝ)) x|))
    (bΔp_pow : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x =>
                ‖fun i =>
                    |(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₂
                                  : (Fin d → ℝ) → ℝ)) x|
                  + |(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₁
                                  : (Fin d → ℝ) → ℝ)) x|‖ ^ h.α + 1))
    (bΔm_pow : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x => (|mLim x| + |mLim x|) ^ h.β + 1))
    (bΔm_grad : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => (|mLim x| + |mLim x|)
                  * ‖fun i =>
                      |(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₂
                                    : (Fin d → ℝ) → ℝ)) x|
                    + |(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₁
                                    : (Fin d → ℝ) → ℝ)) x|‖ ^ (h.α - 1)))
    (bΔm_endpoint : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => (|mLim x| + |mLim x|) ^ (1 + h.β - h.β / h.α)))
    (bΔm : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => |mLim x| + |mLim x|))
    (bΔm1 : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x => (|mLim x| + |mLim x|) + 1))
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
                          ^ (γBar - 1))) :
    TransportPaperSegMemLpBundle (d := d) (βBarReal := βBarReal)
        (γBarReal := γBarReal) (βBarReal' := βBarReal')
        (γBarReal' := γBarReal') (γBar := γBar)
        (H := H) (DpH := DpH)
      (bareToBanachPair_transport_paper (d := d) (βBarReal := βBarReal)
        (γBarReal := γBarReal) (DuLim := DuLim)
        hmLim_memLp huLim_sob hDuLim_memLp_γ ψ₁)
      (bareToBanachPair_transport_paper (d := d) (βBarReal := βBarReal)
        (γBarReal := γBarReal) (DuLim := DuLim)
        hmLim_memLp huLim_sob hDuLim_memLp_γ ψ₂)
      h := by
  -- Abbreviations for the two lifted Banach pairs.
  set q₁ := bareToBanachPair_transport_paper (d := d) (βBarReal := βBarReal)
        (γBarReal := γBarReal) (DuLim := DuLim)
        hmLim_memLp huLim_sob hDuLim_memLp_γ ψ₁ with hq₁_def
  set q₂ := bareToBanachPair_transport_paper (d := d) (βBarReal := βBarReal)
        (γBarReal := γBarReal) (DuLim := DuLim)
        hmLim_memLp huLim_sob hDuLim_memLp_γ ψ₂ with hq₂_def
  -- The three a.e.-coercion identities from iter-0510 Child A.
  have hm₁ :
      mOf q₁ =ᵐ[MeasureTheory.Measure.restrict
                  MeasureTheory.volume (UnitCube d)] mLim :=
    bareToBanachPair_transport_paper_mOf_ae_eq (d := d)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ ψ₁
  have hm₂ :
      mOf q₂ =ᵐ[MeasureTheory.Measure.restrict
                  MeasureTheory.volume (UnitCube d)] mLim :=
    bareToBanachPair_transport_paper_mOf_ae_eq (d := d)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ ψ₂
  have hu₁ :
      uOf q₁ =ᵐ[MeasureTheory.Measure.restrict
                  MeasureTheory.volume (UnitCube d)]
          (uLim + (ψ₁ : (Fin d → ℝ) → ℝ)) :=
    bareToBanachPair_transport_paper_uOf_ae_eq (d := d)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ ψ₁
  have hu₂ :
      uOf q₂ =ᵐ[MeasureTheory.Measure.restrict
                  MeasureTheory.volume (UnitCube d)]
          (uLim + (ψ₂ : (Fin d → ℝ) → ℝ)) :=
    bareToBanachPair_transport_paper_uOf_ae_eq (d := d)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ ψ₂
  have hDu₁ : ∀ i,
      DuOf q₁ i =ᵐ[MeasureTheory.Measure.restrict
                      MeasureTheory.volume (UnitCube d)]
          (DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₁
                        : (Fin d → ℝ) → ℝ)) := fun i =>
    bareToBanachPair_transport_paper_DuOf_ae_eq (d := d)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ ψ₁ i
  have hDu₂ : ∀ i,
      DuOf q₂ i =ᵐ[MeasureTheory.Measure.restrict
                      MeasureTheory.volume (UnitCube d)]
          (DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₂
                        : (Fin d → ℝ) → ℝ)) := fun i =>
    bareToBanachPair_transport_paper_DuOf_ae_eq (d := d)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ ψ₂ i
  -- Transport each bare cert via `MemLp.ae_eq`.
  refine
    { hΔυ := ?_, hΔp_pow := ?_, hΔm_pow := ?_, hΔm_grad := ?_,
      hΔm_endpoint := ?_, hΔm := ?_, hΔm1 := ?_,
      hG_grad := ?_, hG_val := ?_ }
  · -- `hΔυ`: u-side fields use `hu₁, hu₂`.
    have heq :
        (fun x => |(uLim + (ψ₂ : (Fin d → ℝ) → ℝ)) x|
                    + |(uLim + (ψ₁ : (Fin d → ℝ) → ℝ)) x|)
          =ᵐ[MeasureTheory.Measure.restrict
                MeasureTheory.volume (UnitCube d)]
            (fun x => |uOf q₂ x| + |uOf q₁ x|) := by
      filter_upwards [hu₁, hu₂] with x hx₁ hx₂
      simp [hx₁, hx₂]
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq heq bΔυ.toMemLp)
  · -- `hΔp_pow`: Du-side field, uses `hDu₁, hDu₂`.
    have heq :
        (fun x =>
            ‖fun i =>
                |(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₂
                              : (Fin d → ℝ) → ℝ)) x|
              + |(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₁
                              : (Fin d → ℝ) → ℝ)) x|‖ ^ h.α + 1)
          =ᵐ[MeasureTheory.Measure.restrict
                MeasureTheory.volume (UnitCube d)]
            (fun x =>
              ‖fun i => |DuOf q₂ i x| + |DuOf q₁ i x|‖ ^ h.α + 1) := by
      have hDuAll :
          ∀ᵐ x ∂(MeasureTheory.Measure.restrict
                  MeasureTheory.volume (UnitCube d)),
            ∀ i, DuOf q₁ i x = (DuLim i + (Periodic.SmoothPeriodic.partialDeriv
                  i ψ₁ : (Fin d → ℝ) → ℝ)) x ∧
                 DuOf q₂ i x = (DuLim i + (Periodic.SmoothPeriodic.partialDeriv
                  i ψ₂ : (Fin d → ℝ) → ℝ)) x := by
        rw [MeasureTheory.ae_all_iff]
        intro i
        filter_upwards [hDu₁ i, hDu₂ i] with x ha hb
        exact ⟨ha, hb⟩
      filter_upwards [hDuAll] with x hx
      have hfun :
          (fun i => |(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₂
                                  : (Fin d → ℝ) → ℝ)) x|
                  + |(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₁
                                  : (Fin d → ℝ) → ℝ)) x|)
            = (fun i => |DuOf q₂ i x| + |DuOf q₁ i x|) := by
        funext i
        rcases hx i with ⟨h₁, h₂⟩
        simp [h₁, h₂]
      rw [hfun]
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq heq bΔp_pow.toMemLp)
  · -- `hΔm_pow`: m-side, uses `hm₁, hm₂`.
    have heq :
        (fun x => (|mLim x| + |mLim x|) ^ h.β + 1)
          =ᵐ[MeasureTheory.Measure.restrict
                MeasureTheory.volume (UnitCube d)]
            (fun x => (|mOf q₂ x| + |mOf q₁ x|) ^ h.β + 1) := by
      filter_upwards [hm₁, hm₂] with x hx₁ hx₂
      simp [hx₁, hx₂]
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq heq bΔm_pow.toMemLp)
  · -- `hΔm_grad`: m × Du-side; uses `hm, hDu`.
    have heq :
        (fun x => (|mLim x| + |mLim x|)
            * ‖fun i =>
                |(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₂
                              : (Fin d → ℝ) → ℝ)) x|
              + |(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₁
                              : (Fin d → ℝ) → ℝ)) x|‖ ^ (h.α - 1))
          =ᵐ[MeasureTheory.Measure.restrict
                MeasureTheory.volume (UnitCube d)]
            (fun x => (|mOf q₂ x| + |mOf q₁ x|)
              * ‖fun i => |DuOf q₂ i x| + |DuOf q₁ i x|‖ ^ (h.α - 1)) := by
      have hDuAll :
          ∀ᵐ x ∂(MeasureTheory.Measure.restrict
                  MeasureTheory.volume (UnitCube d)),
            ∀ i, DuOf q₁ i x = (DuLim i + (Periodic.SmoothPeriodic.partialDeriv
                  i ψ₁ : (Fin d → ℝ) → ℝ)) x ∧
                 DuOf q₂ i x = (DuLim i + (Periodic.SmoothPeriodic.partialDeriv
                  i ψ₂ : (Fin d → ℝ) → ℝ)) x := by
        rw [MeasureTheory.ae_all_iff]
        intro i
        filter_upwards [hDu₁ i, hDu₂ i] with x ha hb
        exact ⟨ha, hb⟩
      filter_upwards [hm₁, hm₂, hDuAll] with x hx₁ hx₂ hxDu
      have hfun :
          (fun i => |(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₂
                                  : (Fin d → ℝ) → ℝ)) x|
                  + |(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₁
                                  : (Fin d → ℝ) → ℝ)) x|)
            = (fun i => |DuOf q₂ i x| + |DuOf q₁ i x|) := by
        funext i
        rcases hxDu i with ⟨h₁, h₂⟩
        simp [h₁, h₂]
      rw [hx₁, hx₂, hfun]
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq heq bΔm_grad.toMemLp)
  · -- `hΔm_endpoint`: m-side.
    have heq :
        (fun x => (|mLim x| + |mLim x|) ^ (1 + h.β - h.β / h.α))
          =ᵐ[MeasureTheory.Measure.restrict
                MeasureTheory.volume (UnitCube d)]
            (fun x => (|mOf q₂ x| + |mOf q₁ x|)
              ^ (1 + h.β - h.β / h.α)) := by
      filter_upwards [hm₁, hm₂] with x hx₁ hx₂
      simp [hx₁, hx₂]
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq heq bΔm_endpoint.toMemLp)
  · -- `hΔm`: m-side.
    have heq :
        (fun x => |mLim x| + |mLim x|)
          =ᵐ[MeasureTheory.Measure.restrict
                MeasureTheory.volume (UnitCube d)]
            (fun x => |mOf q₂ x| + |mOf q₁ x|) := by
      filter_upwards [hm₁, hm₂] with x hx₁ hx₂
      simp [hx₁, hx₂]
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq heq bΔm.toMemLp)
  · -- `hΔm1`: m-side.
    have heq :
        (fun x => (|mLim x| + |mLim x|) + 1)
          =ᵐ[MeasureTheory.Measure.restrict
                MeasureTheory.volume (UnitCube d)]
            (fun x => (|mOf q₂ x| + |mOf q₁ x|) + 1) := by
      filter_upwards [hm₁, hm₂] with x hx₁ hx₂
      simp [hx₁, hx₂]
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq heq bΔm1.toMemLp)
  · -- `hG_grad`: Du-side ∑ over coords.
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
              (∑ i, (|DuOf q₂ i x| + |DuOf q₁ i x|) ^ (2 : ℕ))
                ^ ((γBar - 1) / 2)) := by
      have hDuAll :
          ∀ᵐ x ∂(MeasureTheory.Measure.restrict
                  MeasureTheory.volume (UnitCube d)),
            ∀ i, DuOf q₁ i x = (DuLim i + (Periodic.SmoothPeriodic.partialDeriv
                  i ψ₁ : (Fin d → ℝ) → ℝ)) x ∧
                 DuOf q₂ i x = (DuLim i + (Periodic.SmoothPeriodic.partialDeriv
                  i ψ₂ : (Fin d → ℝ) → ℝ)) x := by
        rw [MeasureTheory.ae_all_iff]
        intro i
        filter_upwards [hDu₁ i, hDu₂ i] with x ha hb
        exact ⟨ha, hb⟩
      filter_upwards [hDuAll] with x hx
      have hsum :
          (∑ i,
              (|(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₂
                            : (Fin d → ℝ) → ℝ)) x|
                + |(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₁
                            : (Fin d → ℝ) → ℝ)) x|) ^ (2 : ℕ))
            = ∑ i, (|DuOf q₂ i x| + |DuOf q₁ i x|) ^ (2 : ℕ) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        rcases hx i with ⟨h₁, h₂⟩
        simp [h₁, h₂]
      rw [hsum]
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq heq bG_grad.toMemLp)
  · -- `hG_val`: u-side power.
    have heq :
        (fun x => (|(uLim + (ψ₂ : (Fin d → ℝ) → ℝ)) x|
                    + |(uLim + (ψ₁ : (Fin d → ℝ) → ℝ)) x|) ^ (γBar - 1))
          =ᵐ[MeasureTheory.Measure.restrict
                MeasureTheory.volume (UnitCube d)]
            (fun x => (|uOf q₂ x| + |uOf q₁ x|) ^ (γBar - 1)) := by
      filter_upwards [hu₁, hu₂] with x hx₁ hx₂
      simp [hx₁, hx₂]
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq heq bG_val.toMemLp)

/-- **Sanity-check `example`** for the transport-narrow segment
`MemLpPer` bundle. Given the iter-0510 Child A inputs and nine
bare-function `MemLpPer` certificates for the bound expressions in
`(mLim, uLim+ψ₁, uLim+ψ₂, DuLim+∂ψ₁, DuLim+∂ψ₂)`, the bundle is
produced for the lifted endpoints. -/
example
    {d : ℕ} {βBarReal γBarReal βBarReal' γBarReal' γBar : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {mLim uLim : (Fin d → ℝ) → ℝ}
    {DuLim : Fin d → (Fin d → ℝ) → ℝ}
    (hmLim_memLp : Periodic.MemLpPer (d := d)
                      (ENNReal.ofReal βBarReal) mLim)
    (huLim_sob : Periodic.MemSobolevPer (d := d)
                      (ENNReal.ofReal γBarReal) uLim)
    (hDuLim_memLp_γ : ∀ i, Periodic.MemLpPer (d := d)
                              (ENNReal.ofReal γBarReal) (DuLim i))
    (ψ₁ ψ₂ : Periodic.SmoothPeriodic d)
    (h : HypothesisPowerGrowth (d := d) H DpH)
    (bΔυ : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x => |(uLim + (ψ₂ : (Fin d → ℝ) → ℝ)) x|
                          + |(uLim + (ψ₁ : (Fin d → ℝ) → ℝ)) x|))
    (bΔp_pow : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x =>
                ‖fun i =>
                    |(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₂
                                  : (Fin d → ℝ) → ℝ)) x|
                  + |(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₁
                                  : (Fin d → ℝ) → ℝ)) x|‖ ^ h.α + 1))
    (bΔm_pow : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x => (|mLim x| + |mLim x|) ^ h.β + 1))
    (bΔm_grad : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => (|mLim x| + |mLim x|)
                  * ‖fun i =>
                      |(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₂
                                    : (Fin d → ℝ) → ℝ)) x|
                    + |(DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₁
                                    : (Fin d → ℝ) → ℝ)) x|‖ ^ (h.α - 1)))
    (bΔm_endpoint : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => (|mLim x| + |mLim x|) ^ (1 + h.β - h.β / h.α)))
    (bΔm : MemLpPer (d := d) (ENNReal.ofReal γBarReal')
              (fun x => |mLim x| + |mLim x|))
    (bΔm1 : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x => (|mLim x| + |mLim x|) + 1))
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
                          ^ (γBar - 1))) :
    TransportPaperSegMemLpBundle (d := d) (βBarReal := βBarReal)
        (γBarReal := γBarReal) (βBarReal' := βBarReal')
        (γBarReal' := γBarReal') (γBar := γBar)
        (H := H) (DpH := DpH)
      (bareToBanachPair_transport_paper (d := d) (βBarReal := βBarReal)
        (γBarReal := γBarReal) (DuLim := DuLim)
        hmLim_memLp huLim_sob hDuLim_memLp_γ ψ₁)
      (bareToBanachPair_transport_paper (d := d) (βBarReal := βBarReal)
        (γBarReal := γBarReal) (DuLim := DuLim)
        hmLim_memLp huLim_sob hDuLim_memLp_γ ψ₂)
      h :=
  segMemLpBundle_of_transportPaper (d := d) (βBarReal := βBarReal)
    (γBarReal := γBarReal) (βBarReal' := βBarReal')
    (γBarReal' := γBarReal') (γBar := γBar)
    (H := H) (DpH := DpH)
    hmLim_memLp huLim_sob hDuLim_memLp_γ ψ₁ ψ₂ h
    bΔυ bΔp_pow bΔm_pow bΔm_grad bΔm_endpoint bΔm bΔm1 bG_grad bG_val


/-! ## Final composer: `hemicontSegmentData_transport_narrow_of_paperHypotheses`
(Child D, transport family)

Mirrors `hemicontSegmentData_set_narrow_of_paperHypotheses`, but for the
transport-narrow domain `D_transport_family_paper`: the perturbations
`ψ₁, ψ₂ : Periodic.SmoothPeriodic d` act on the `u/Du`-side, leaving
the primal `m`-component fixed at `mLim`. The composer combines the
iter-0510 Child A `bareToBanachPair_transport_paper` lift (and its
K0-membership variant), the iter-0511 Child B
`segMemLpBundle_of_transportPaper` segment-`MemLpPer` bundle, the
iter-0512 K0-membership lemma (already covered by Child A), the
Child C K0 dominator producers `isHK0AbsDominator_of_paperHypotheses`,
`isMDpHK0Dominator_of_paperHypotheses`, the K0-form producer
`hemicontSegmentData_of_K0Aepsi`, and the bare-function transport
`HemicontSegmentData.ae_eq`. -/
noncomputable def hemicontSegmentData_transport_narrow_of_paperHypotheses
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
    -- fixed, so we do not need a perturbation-side nonneg hypothesis).
    (hmLim_nn : 0 ≤ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume
                      (UnitCube d)] mLim)
    -- Transport-family perturbations: smooth periodic test directions.
    (ψ₁ ψ₂ : Periodic.SmoothPeriodic d)
    (aux₁ : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
              V H DpH
              (DuOf (bareToBanachPair_transport_paper (d := d)
                      (βBarReal := βBarReal) (γBarReal := γBarReal)
                      (DuLim := DuLim)
                      hmLim_memLp huLim_sob hDuLim_memLp_γ ψ₁))
              (mOf (bareToBanachPair_transport_paper (d := d)
                      (βBarReal := βBarReal) (γBarReal := γBarReal)
                      (DuLim := DuLim)
                      hmLim_memLp huLim_sob hDuLim_memLp_γ ψ₁))
              (uOf (bareToBanachPair_transport_paper (d := d)
                      (βBarReal := βBarReal) (γBarReal := γBarReal)
                      (DuLim := DuLim)
                      hmLim_memLp huLim_sob hDuLim_memLp_γ ψ₁)))
    (aux₂ : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
              V H DpH
              (DuOf (bareToBanachPair_transport_paper (d := d)
                      (βBarReal := βBarReal) (γBarReal := γBarReal)
                      (DuLim := DuLim)
                      hmLim_memLp huLim_sob hDuLim_memLp_γ ψ₂))
              (mOf (bareToBanachPair_transport_paper (d := d)
                      (βBarReal := βBarReal) (γBarReal := γBarReal)
                      (DuLim := DuLim)
                      hmLim_memLp huLim_sob hDuLim_memLp_γ ψ₂))
              (uOf (bareToBanachPair_transport_paper (d := d)
                      (βBarReal := βBarReal) (γBarReal := γBarReal)
                      (DuLim := DuLim)
                      hmLim_memLp huLim_sob hDuLim_memLp_γ ψ₂)))
    -- Nine bare-function `MemLpPer p`-of-power certificates (Child B).
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
    (bΔm1 : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x => (|mLim x| + |mLim x|) + 1))
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
    -- B-class strict-positivity certificate at the bare endpoints.
    -- Transport leaves `m` fixed at `mLim`, so this is `0 < cxComb mLim mLim t x`.
    (hPosSeg : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
                ∀ t ∈ Set.Icc (0 : ℝ) 1,
                  0 < cxComb mLim mLim t x)
    (hγ_one_lt : 1 < γBar)
    (Dν : Fin d → (Fin d → ℝ) → ℝ) (η ν : (Fin d → ℝ) → ℝ)
    (hη : MemLpPer (d := d) (ENNReal.ofReal βBarReal) η)
    (hDν : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dν i))
    (hν_β : MemLpPer (d := d) (ENNReal.ofReal βBarReal) ν)
    (hν_γ : MemLpPer (d := d) (ENNReal.ofReal γBarReal) ν)
    (hγBar_eq : γBar = γBarReal)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (hF_unreg_meas_bare : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x => aepsiIntegrandAt_unreg V H DpH
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
    HemicontSegmentData V H DpH γBar
      (fun i => DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₁
                            : (Fin d → ℝ) → ℝ))
      (fun i => DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₂
                            : (Fin d → ℝ) → ℝ))
      mLim mLim
      (uLim + (ψ₁ : (Fin d → ℝ) → ℝ))
      (uLim + (ψ₂ : (Fin d → ℝ) → ℝ))
      Dν η ν := by
  -- Build the two Banach pairs via Child A (transport).
  set q₁ := bareToBanachPair_transport_paper (d := d) (βBarReal := βBarReal)
              (γBarReal := γBarReal) (DuLim := DuLim)
              hmLim_memLp huLim_sob hDuLim_memLp_γ ψ₁ with hq₁_def
  set q₂ := bareToBanachPair_transport_paper (d := d) (βBarReal := βBarReal)
              (γBarReal := γBarReal) (DuLim := DuLim)
              hmLim_memLp huLim_sob hDuLim_memLp_γ ψ₂ with hq₂_def
  -- K0 memberships: transport leaves `m` fixed at `mLim`, so `hmLim_nn` suffices.
  have hq₁_K0 : q₁ ∈ K0_Aepsi d βBarReal γBarReal :=
    bareToBanachPair_transport_paper_mem_K0Aepsi (uLim := uLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hmLim_nn ψ₁
  have hq₂_K0 : q₂ ∈ K0_Aepsi d βBarReal γBarReal :=
    bareToBanachPair_transport_paper_mem_K0Aepsi (uLim := uLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ hmLim_nn ψ₂
  -- The six a.e.-coercion identities from Child A.
  have hm₁ :
      mOf q₁ =ᵐ[MeasureTheory.Measure.restrict
                  MeasureTheory.volume (UnitCube d)] mLim :=
    bareToBanachPair_transport_paper_mOf_ae_eq (d := d)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ ψ₁
  have hm₂ :
      mOf q₂ =ᵐ[MeasureTheory.Measure.restrict
                  MeasureTheory.volume (UnitCube d)] mLim :=
    bareToBanachPair_transport_paper_mOf_ae_eq (d := d)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ ψ₂
  have hu₁ :
      uOf q₁ =ᵐ[MeasureTheory.Measure.restrict
                  MeasureTheory.volume (UnitCube d)]
          (uLim + (ψ₁ : (Fin d → ℝ) → ℝ)) :=
    bareToBanachPair_transport_paper_uOf_ae_eq (d := d)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ ψ₁
  have hu₂ :
      uOf q₂ =ᵐ[MeasureTheory.Measure.restrict
                  MeasureTheory.volume (UnitCube d)]
          (uLim + (ψ₂ : (Fin d → ℝ) → ℝ)) :=
    bareToBanachPair_transport_paper_uOf_ae_eq (d := d)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ ψ₂
  have hDu₁ : ∀ i,
      DuOf q₁ i =ᵐ[MeasureTheory.Measure.restrict
                      MeasureTheory.volume (UnitCube d)]
          (DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₁
                        : (Fin d → ℝ) → ℝ)) := fun i =>
    bareToBanachPair_transport_paper_DuOf_ae_eq (d := d)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ ψ₁ i
  have hDu₂ : ∀ i,
      DuOf q₂ i =ᵐ[MeasureTheory.Measure.restrict
                      MeasureTheory.volume (UnitCube d)]
          (DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₂
                        : (Fin d → ℝ) → ℝ)) := fun i =>
    bareToBanachPair_transport_paper_DuOf_ae_eq (d := d)
      (βBarReal := βBarReal) (γBarReal := γBarReal)
      (mLim := mLim) (uLim := uLim) (DuLim := DuLim)
      hmLim_memLp huLim_sob hDuLim_memLp_γ ψ₂ i
  -- Child B: transport-paper segment-`MemLpPer` bundle.
  have segBundle :=
    segMemLpBundle_of_transportPaper (d := d) (βBarReal := βBarReal)
      (γBarReal := γBarReal) (βBarReal' := βBarReal')
      (γBarReal' := γBarReal') (γBar := γBar)
      (H := H) (DpH := DpH)
      hmLim_memLp huLim_sob hDuLim_memLp_γ ψ₁ ψ₂ hpow
      bΔυ bΔp_pow bΔm_pow bΔm_grad bΔm_endpoint bΔm bΔm1 bG_grad bG_val
  -- Child C: K0 dominator certs.
  have hHabs_K0 :
      IsHK0AbsDominator (d := d) hpow (mOf q₁) (mOf q₂)
                          (DuOf q₁) (DuOf q₂) hpow.C :=
    isHK0AbsDominator_of_paperHypotheses hpow hHat0 hAgree
      (mOf q₁) (mOf q₂) (DuOf q₁) (DuOf q₂)
  have hmDpH_K0 :
      IsmDpHK0Dominator (d := d) hpow (mOf q₁) (mOf q₂)
                          (DuOf q₁) (DuOf q₂) :=
    isMDpHK0Dominator_of_paperHypotheses hpow hHat0 hAgree
      (mOf q₁) (mOf q₂) (DuOf q₁) (DuOf q₂)
  -- Transport `hPosSeg` backwards from `(mLim, mLim)` to `(mOf q₁, mOf q₂)`.
  have hPosSeg_q :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          0 < cxComb (mOf q₁) (mOf q₂) t x := by
    have hcomb :
        ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
          ∀ t : ℝ,
            cxComb mLim mLim t x = cxComb (mOf q₁) (mOf q₂) t x :=
      cxComb_congr_ae hm₁.symm hm₂.symm
    filter_upwards [hPosSeg, hcomb] with x hPosx hcombx t ht
    have := hPosx t ht
    rw [hcombx t] at this
    exact this
  obtain ⟨bhΔυ, bhΔp_pow, bhΔm_pow, bhΔm_grad, bhΔm_endpoint,
          bhΔm, bhΔm1, bhG_grad, bhG_val⟩ := segBundle
  -- Build the bare measurability witnesses pulled back to `(qᵢ-coercions)`
  -- via the a.e.-equality of the integrand functions.
  have hF_unreg_eq :=
    aepsiIntegrandAt_unreg_congr_ae V H DpH Dν η ν
      hm₁ hm₂ hu₁ hu₂ hDu₁ hDu₂
  have hF_gat_eq :=
    aepsiIntegrandAt_gateaux_congr_ae γBar Dν ν
      hu₁ hu₂ hDu₁ hDu₂
  have hF_unreg_meas_q :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        MeasureTheory.AEStronglyMeasurable
          (fun x => aepsiIntegrandAt_unreg V H DpH
                      (DuOf q₁) (DuOf q₂) (mOf q₁) (mOf q₂)
                      (uOf q₁) (uOf q₂) Dν η ν x t)
          (MeasureTheory.volume.restrict (UnitCube d)) := by
    intro t ht
    have hmeas := hF_unreg_meas_bare t ht
    refine hmeas.congr ?_
    filter_upwards [hF_unreg_eq] with x hx
    exact (hx t).symm
  have hF_gat_meas_q :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        MeasureTheory.AEStronglyMeasurable
          (fun x => aepsiIntegrandAt_gateaux γBar
                      (DuOf q₁) (DuOf q₂) (uOf q₁) (uOf q₂) Dν ν x t)
          (MeasureTheory.volume.restrict (UnitCube d)) := by
    intro t ht
    have hmeas := hF_gat_meas_bare t ht
    refine hmeas.congr ?_
    filter_upwards [hF_gat_eq] with x hx
    exact (hx t).symm
  have dataQ :
      HemicontSegmentData V H DpH γBar
        (DuOf q₁) (DuOf q₂) (mOf q₁) (mOf q₂)
        (uOf q₁) (uOf q₂) Dν η ν :=
    hemicontSegmentData_of_K0Aepsi (γBarReal := γBarReal)
      (βBarReal := βBarReal) (βBarReal' := βBarReal')
      (γBarReal' := γBarReal') (γBar := γBar) (V := V)
      hq₁_K0 hq₂_K0 aux₁ aux₂ hβconj hγconj hpow
      hpow.C hpow.hC hHabs_K0 hmDpH_K0 hPosSeg_q
      hγ_one_lt Dν η ν hη hDν hν_β hν_γ hγBar_eq
      hV bhΔυ bhΔp_pow bhΔm_pow bhΔm_grad bhΔm_endpoint
      bhΔm bhΔm1 bhG_grad bhG_val hF_unreg_meas_q hF_gat_meas_q
  exact HemicontSegmentData.ae_eq V H DpH γBar Dν η ν
    hm₁ hm₂ hu₁ hu₂ hDu₁ hDu₂ dataQ

/-- **Sanity-check `example`** for the Child D headline composer
(transport-narrow). At symbolic inputs,
`hemicontSegmentData_transport_narrow_of_paperHypotheses` produces the
bare-function-parameterised `HemicontSegmentData` with the perturbed
`u/Du`-side (and the primal `m`-side fixed at `mLim`). -/
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
    (aux₁ : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
              V H DpH
              (DuOf (bareToBanachPair_transport_paper (d := d)
                      (βBarReal := βBarReal) (γBarReal := γBarReal)
                      (DuLim := DuLim)
                      hmLim_memLp huLim_sob hDuLim_memLp_γ ψ₁))
              (mOf (bareToBanachPair_transport_paper (d := d)
                      (βBarReal := βBarReal) (γBarReal := γBarReal)
                      (DuLim := DuLim)
                      hmLim_memLp huLim_sob hDuLim_memLp_γ ψ₁))
              (uOf (bareToBanachPair_transport_paper (d := d)
                      (βBarReal := βBarReal) (γBarReal := γBarReal)
                      (DuLim := DuLim)
                      hmLim_memLp huLim_sob hDuLim_memLp_γ ψ₁)))
    (aux₂ : MFGOpEpsAuxHyps (d := d) γBarReal βBarReal βBarReal' γBarReal'
              V H DpH
              (DuOf (bareToBanachPair_transport_paper (d := d)
                      (βBarReal := βBarReal) (γBarReal := γBarReal)
                      (DuLim := DuLim)
                      hmLim_memLp huLim_sob hDuLim_memLp_γ ψ₂))
              (mOf (bareToBanachPair_transport_paper (d := d)
                      (βBarReal := βBarReal) (γBarReal := γBarReal)
                      (DuLim := DuLim)
                      hmLim_memLp huLim_sob hDuLim_memLp_γ ψ₂))
              (uOf (bareToBanachPair_transport_paper (d := d)
                      (βBarReal := βBarReal) (γBarReal := γBarReal)
                      (DuLim := DuLim)
                      hmLim_memLp huLim_sob hDuLim_memLp_γ ψ₂)))
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
    (bΔm1 : MemLpPer (d := d) (ENNReal.ofReal βBarReal')
              (fun x => (|mLim x| + |mLim x|) + 1))
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
    (hPosSeg : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
                ∀ t ∈ Set.Icc (0 : ℝ) 1,
                  0 < cxComb mLim mLim t x)
    (hγ_one_lt : 1 < γBar)
    (Dν : Fin d → (Fin d → ℝ) → ℝ) (η ν : (Fin d → ℝ) → ℝ)
    (hη : MemLpPer (d := d) (ENNReal.ofReal βBarReal) η)
    (hDν : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBarReal) (Dν i))
    (hν_β : MemLpPer (d := d) (ENNReal.ofReal βBarReal) ν)
    (hν_γ : MemLpPer (d := d) (ENNReal.ofReal γBarReal) ν)
    (hγBar_eq : γBar = γBarReal)
    (hV : MemLpPer (d := d) (ENNReal.ofReal βBarReal') V)
    (hF_unreg_meas_bare : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasureTheory.AEStronglyMeasurable
        (fun x => aepsiIntegrandAt_unreg V H DpH
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
    HemicontSegmentData V H DpH γBar
      (fun i => DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₁
                            : (Fin d → ℝ) → ℝ))
      (fun i => DuLim i + (Periodic.SmoothPeriodic.partialDeriv i ψ₂
                            : (Fin d → ℝ) → ℝ))
      mLim mLim
      (uLim + (ψ₁ : (Fin d → ℝ) → ℝ))
      (uLim + (ψ₂ : (Fin d → ℝ) → ℝ))
      Dν η ν :=
  hemicontSegmentData_transport_narrow_of_paperHypotheses
    (γBarReal := γBarReal) (βBarReal := βBarReal)
    (βBarReal' := βBarReal') (γBarReal' := γBarReal') (γBar := γBar)
    (V := V) (H := H) (DpH := DpH)
    hpow hHat0 hAgree hβconj hγconj
    hmLim_memLp huLim_sob hDuLim_memLp_γ hmLim_nn
    ψ₁ ψ₂ aux₁ aux₂
    bΔυ bΔp_pow bΔm_pow bΔm_grad bΔm_endpoint bΔm bΔm1 bG_grad bG_val
    hPosSeg hγ_one_lt Dν η ν hη hDν hν_β hν_γ hγBar_eq hV
    hF_unreg_meas_bare hF_gat_meas_bare

/-! ## v7 Phase 2b — paper-`|u|^{β̄'}` integrability via finite-measure
exponent inclusion

The cheap finite-measure exponent inclusion `MemLpPer γ̄ u
→ Integrable (|u|^{β̄'})` on the unit cube. The unit cube has volume
`1` (finite measure), so `MemLp` is monotone in the exponent, and
`MemLp p u → Integrable (‖u‖^p.toReal)` for any `p ≠ 0, ∞` (here
`p := β̄' β`). The exponent inequality `β̄'(β) ≤ γ̄(α, β)` holds
whenever `α ≥ 1, β > 0` via `Hamiltonian.betaBar'_le_gammaBar`.

This unblocks the `hUbetap_int` field of `PaperCBundleForK` (v7 Phase 2c)
and is the cheap (no-gradient) Sobolev-style residue inclusion of the
paper. -/

/-- **v7 Phase 2b producer.** From `MemLpPer γ̄ u` on the unit cube,
derive the paper's `|u|^{β̄'}` integrability. The unit cube has finite
volume `1`, so `MemLp` is monotone in the exponent
(`MemLpPer.mono_exponent_finite`); we then route through Mathlib's
`MemLp.integrable_norm_rpow`, which reads off `Integrable (‖u‖^p.toReal)`
from `MemLp p u` on a finite measure for `p ≠ 0, ∞`.

The exponent ordering `β̄'(β) ≤ γ̄(α, β)` is the dual identity
`γ̄ = α · β̄'` together with `α ≥ 1, β̄' > 0` — packaged here as
`Hamiltonian.betaBar'_le_gammaBar`. -/
theorem uBetap_int_of_memLpPer_gamma
    {α β : ℝ} (hα : 1 ≤ α) (hβ : 0 < β) {u : (Fin d → ℝ) → ℝ}
    (h : Periodic.MemLpPer
            (ENNReal.ofReal (Hamiltonian.gammaBar α β)) u) :
    MeasureTheory.Integrable
        (fun x => |u x| ^ Hamiltonian.betaBar' β)
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)) := by
  -- Step 1. Real exponent inequality `β̄' β ≤ γ̄ α β`.
  have h_exp_le : Hamiltonian.betaBar' β ≤ Hamiltonian.gammaBar α β :=
    Hamiltonian.betaBar'_le_gammaBar hα hβ
  -- Step 2. Lift to ENNReal.
  have h_betap_pos : 0 < Hamiltonian.betaBar' β := by
    unfold Hamiltonian.betaBar'
    exact div_pos (by linarith) hβ
  have h_betap_nn : 0 ≤ Hamiltonian.betaBar' β := h_betap_pos.le
  have h_gamma_nn : 0 ≤ Hamiltonian.gammaBar α β := by
    have hαpos : 0 < α := lt_of_lt_of_le zero_lt_one hα
    have : 0 < Hamiltonian.gammaBar α β :=
      Hamiltonian.gammaBar_pos α β hαpos hβ
    exact this.le
  have h_enn_le : ENNReal.ofReal (Hamiltonian.betaBar' β)
                    ≤ ENNReal.ofReal (Hamiltonian.gammaBar α β) :=
    ENNReal.ofReal_le_ofReal h_exp_le
  -- Step 3. The exponent `γ̄ α β` lifts to a finite ENNReal.
  have h_gamma_ne_top :
      ENNReal.ofReal (Hamiltonian.gammaBar α β) ≠ ⊤ := by
    exact ENNReal.ofReal_ne_top
  -- Step 4. Apply finite-measure exponent monotonicity to obtain
  -- `MemLpPer (β̄') u`.
  have h_betap : Periodic.MemLpPer
                    (ENNReal.ofReal (Hamiltonian.betaBar' β)) u :=
    Periodic.MemLpPer.mono_exponent_finite h_enn_le h_gamma_ne_top h
  -- Step 5. Convert to `Integrable (‖u‖^(β̄').toReal)` via Mathlib's
  -- `MemLp.integrable_norm_rpow`. We need `(ENNReal.ofReal _) ≠ 0, ∞`.
  have h_betap_ne_zero :
      ENNReal.ofReal (Hamiltonian.betaBar' β) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero]
    push_neg
    exact h_betap_pos
  have h_betap_ne_top :
      ENNReal.ofReal (Hamiltonian.betaBar' β) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have h_int_norm :
      MeasureTheory.Integrable
          (fun x => ‖u x‖ ^
            (ENNReal.ofReal (Hamiltonian.betaBar' β)).toReal)
          (MeasureTheory.volume.restrict (Periodic.UnitCube d)) :=
    h_betap.toMemLp.integrable_norm_rpow h_betap_ne_zero h_betap_ne_top
  -- Step 6. Identify `(ENNReal.ofReal r).toReal = r` for `r ≥ 0` and
  -- `‖u x‖ = |u x|` for real-valued `u`.
  have h_toReal :
      (ENNReal.ofReal (Hamiltonian.betaBar' β)).toReal
        = Hamiltonian.betaBar' β :=
    ENNReal.toReal_ofReal h_betap_nn
  have h_pointwise :
      (fun x => ‖u x‖ ^
            (ENNReal.ofReal (Hamiltonian.betaBar' β)).toReal)
        = (fun x => |u x| ^ Hamiltonian.betaBar' β) := by
    funext x
    rw [Real.norm_eq_abs, h_toReal]
  rw [h_pointwise] at h_int_norm
  exact h_int_norm

end Banach
end SimplePower
end Theorems
end StationaryMFG

end
