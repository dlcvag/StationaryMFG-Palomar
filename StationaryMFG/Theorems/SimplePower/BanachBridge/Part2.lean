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

theorem simplePowerThinChain_of_paperHypotheses
    {γBar : ℝ}
    {betaBar gammaBar betaBar' : ℝ≥0∞}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    [Fact (1 ≤ ENNReal.ofReal βBarReal)]
    [Fact (1 ≤ ENNReal.ofReal γBarReal)]
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hmon : HypothesisMonotone H DpH)
    (hpow : HypothesisPowerGrowth H DpH)
    (hV : Periodic.MemLpPer (ENNReal.ofReal βBarReal') V)
    (hHat0 : StationaryMFG.Hamiltonian.HypothesisHat0 (d := d) H)
    (hFin : StationaryMFG.Hamiltonian.Hext_finite_at_zero (d := d) H)
    (hAgree : StationaryMFG.Hamiltonian.H_zero_eq_Hext (d := d) H)
    -- **iter `infra-P5-T10-v8-K0-set-mintyResSetOf-retype`**: explicit
    -- paper-side joint-continuity rider for the extended Hamiltonian
    -- on the closed half-plane `{m ≥ 0}`. Consumed in-body to construct
    -- the `RegularityHK0` value used by the K0 set-family Minty closure
    -- consumer. NOT a B-class authorisation parameter (analytic rider).
    (hHextCont : StationaryMFG.Hamiltonian.HypothesisHextJointCont (d := d) H)
    -- **iter `infra-P5-T10-v8-K0-set-segInputs-relocate-testDir-certs`**:
    -- Paper-faithful per-test-pair test-direction regularity producer.
    -- For any test triple `(η, ν, Dν)`, supplies the four `MemLpPer`
    -- certificates `(hη, hDν, hν_β, hν_γ)` consumed by the K0 segment-data
    -- composer. NOT a B-class authorisation (paper-faithful analytic rider).
    --
    -- **iter `infra-P7-sigfix-T1-testDirCerts` (Phase 1A, 2026-05-24)**:
    -- the anonymous 4-And conjunction was replaced by the named structure
    -- `TestDirectionCerts hpow η ν Dν`.
    --
    -- **iter `infra-P7-sigfix-T1-drain-C-public-headlines` (Phase 1D,
    -- 2026-05-24)**: the universal `testDirCertsOf` oracle parameter is
    -- *dropped* from this public signature. After drain-A (Minty closure
    -- restricted to a family) and drain-B (K0 closure consumers refactored
    -- to source test-direction certs from family membership + `wkBundle`
    -- regularity rather than a universal oracle), the parameter is no
    -- longer used in the body — its discharge has been migrated to the
    -- family-conditional producers `testDirectionCerts_of_{set,signed,
    -- transport}_family` invoked inside the K0 closure consumers
    -- themselves. Theorem 1 is now `testDirCertsOf`-free.
    (hExp : SimplePowerExponentFacts γBarReal
              (ENNReal.ofReal βBarReal) (ENNReal.ofReal γBarReal)
              (ENNReal.ofReal βBarReal'))
    (residues : T10PaperResidues
                  (d := d) γBarReal βBarReal βBarReal' γBarReal' V H DpH hpow)
    (_hγBar_eq : γBarReal = γBar)
    (_hβBar_eq : ENNReal.ofReal βBarReal = betaBar)
    (_hγBar_eq' : ENNReal.ofReal γBarReal = gammaBar)
    (_hβBar'_eq : ENNReal.ofReal βBarReal' = betaBar')
    (hβBarPaper : βBarReal = hpow.β + 1)
    (hγBarPaper : γBarReal = hpow.α * (hpow.β + 1) / hpow.β)
    (hβBar'Paper : βBarReal' = (hpow.β + 1) / hpow.β)
    (hγBar'Paper : γBarReal' = hpow.α * (hpow.β + 1) / hpow.β /
                                 (hpow.α * (hpow.β + 1) / hpow.β - 1)) :
    Nonempty (H4SimplePowerInputs (d := d)
                γBar V H DpH betaBar gammaBar) := by
  -- Substitute the equalities so the goal lands at the `Real`-shaped
  -- exponents that the producer chain operates on.
  subst _hγBar_eq
  subst _hβBar_eq
  subst _hγBar_eq'
  subst _hβBar'_eq
  -- **Phase 2b T10 shrink**
  -- (`infra-P5-theorem1-phase-2b-T10-aprioriResidue-shrink`):
  -- substitute the paper-form exponent equalities so that the structure
  -- exponents `(βBarReal, γBarReal)` reduce to `(hpow.β + 1,
  -- gammaBar hpow.α hpow.β)` — this aligns the new `T10PaperResidues`
  -- fields' paper-form exponents with the chain's structure exponents.
  subst hβBarPaper
  subst hγBarPaper
  -- **Phase 1 of expert post-iter-412 plan**
  -- (`infra-P5-theorem1-remove-pairingResidue-hpq-dependency`):
  -- The `T10PaperResidues.h_weak_*Of` fields are now typed via
  -- `hpqBeta_paper hpow` / `hpqGamma_paper hpow`, exposing the paper
  -- exponents `(betaBar hpow.β, betaBar' hpow.β)` and
  -- `(gammaBar hpow.α hpow.β, gammaBar' hpow.α hpow.β)`. Under the
  -- paper-form equalities `hβBar'Paper`/`hγBar'Paper`, the residue
  -- field props match the consumer's expected props at
  -- `(βBarReal, βBarReal')` / `(γBarReal, γBarReal')` modulo
  -- `Eq.mpr`-bridging — supplied at each `*_at` call site below.
  -- Re-export the structure-level `Fact` instance under the
  -- `gammaBar`-folded form so producers consuming
  -- `Fact (1 ≤ ENNReal.ofReal (gammaBar hpow.α hpow.β))` can synthesise it.
  -- (`gammaBar α β = α * (β+1)/β` definitionally, but instance synthesis
  -- does not unfold `def`s.)
  haveI : Fact (1 ≤ ENNReal.ofReal
      (StationaryMFG.Hamiltonian.gammaBar hpow.α hpow.β)) := by
    show Fact (1 ≤ ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))
    infer_instance
  -- Step 1: T7 — regularized sequence.
  -- The per-`k` sol and the closed-form ε-uniform apriori constant are
  -- now built in-body via the iter-400 closed-paper producer
  -- `aprioriUniformResidueInputs_of_paperHypotheses_closedPaper`,
  -- consuming the smaller per-`k` C-class bundle + 4 authorised
  -- B-class inputs from `T10PaperResidues` (iter
  -- `infra-P5-T10-v7-HMinty-3-rewire-and-drain`: 5 → 4 after draining
  -- the Minty / hemicontinuity-upgrade limit authorisation
  -- `h_minty_limit_auth` via the 4-step HMinty plan; prior iter
  -- `infra-P5-T10-v7-HMpos-4-bridge-and-drain`: 6 → 5 after draining
  -- the strict-positivity authorisation `paperHMposAuth` via the
  -- 5-step HMpos plan; prior iter
  -- `infra-P5-T10-v7-phase4-hmu-posAuth-drain`: 9 → 6 after draining
  -- `hμ_posAuth_{set,signed,transport}` via the strict→nonneg
  -- consumer migration; prior iter
  -- `infra-P5-T10-v7-phase2c-delta-paperCBundleFor-of-paperHypotheses`
  -- went 10 → 9 by draining `paperCBundleFor`).
  have hβpos : 0 < hpow.β + 1 := by have := hpow.hβ; linarith
  have hγpos : 0 < StationaryMFG.Hamiltonian.gammaBar hpow.α hpow.β :=
    lt_trans zero_lt_one hExp.γBar_one_lt_real
  -- iter `infra-P5-T10-drop-hu_measRaw-hDu_measRaw-final`:
  -- per-`k` AE strong measurability of `u_k` and each `Du_k i`
  -- *with respect to `volume`* (not the cube-restricted measure).
  -- Derived from `MemLpPer + IsPeriodic` via
  -- `MemLpPer.locallyIntegrable_of_periodic.aestronglyMeasurable`.
  have hγBar_one_le : (1 : ℝ≥0∞) ≤
      ENNReal.ofReal (StationaryMFG.Hamiltonian.gammaBar hpow.α hpow.β) := by
    have h1 : (1 : ℝ) ≤ StationaryMFG.Hamiltonian.gammaBar hpow.α hpow.β :=
      hExp.γBar_one_lt_real.le
    have := ENNReal.ofReal_le_ofReal h1
    simpa using this
  -- **Phase 2c-γ migration** (`infra-P5-T10-v7-phase2c-gamma-int-bundles-aePeriodic`):
  -- after retyping `AprioriUniformPerSolHypothesesC_int.hu_per`/`hDu_per`
  -- to `Periodic.AEPeriodic`, the previous derivation route
  -- `MemLpPer.locallyIntegrable_of_periodic.aestronglyMeasurable` (which
  -- required pointwise `IsPeriodic`) is no longer available. The
  -- canonical `_int` producer has been relaxed to take cube-restricted
  -- measurability instead of whole-`volume`, so we now source these
  -- directly from `MemLpPer.aestronglyMeasurable`.
  have hu_aesm_volume : ∀ k : ℕ,
      MeasureTheory.AEStronglyMeasurable (residues.sol k).u
        (MeasureTheory.volume.restrict
          (StationaryMFG.Periodic.UnitCube d)) :=
    fun k => (residues.sol k).huLp.aestronglyMeasurable
  have hDu_aesm_volume : ∀ k : ℕ, ∀ i : Fin d,
      MeasureTheory.AEStronglyMeasurable ((residues.sol k).Du i)
        (MeasureTheory.volume.restrict
          (StationaryMFG.Periodic.UnitCube d)) :=
    fun k i => ((residues.sol k).hDuLp i).aestronglyMeasurable
  -- Convert `hV : MemLpPer (ofReal βBarReal') V` to the paper-form
  -- exponent `betaBar' hpow.β = (hpow.β + 1)/hpow.β` via `hβBar'Paper`.
  have hV_paper :
      Periodic.MemLpPer
        (ENNReal.ofReal (StationaryMFG.Hamiltonian.betaBar' hpow.β)) V := by
    have hbb : StationaryMFG.Hamiltonian.betaBar' hpow.β = βBarReal' := by
      simp [StationaryMFG.Hamiltonian.betaBar', hβBar'Paper]
    simpa [hbb] using hV
  -- **iter 419 / drop-`hRes_Lp`**: derive per-`k` HJB-residual
  -- `MemLpPer βBar'` from `g_memLp_betaBar'_nonneg`. Mirrors
  -- `Banach.WeakLimitInputBundle.hRes_Lp` (per-`k` flavour). Inputs:
  -- `(hpow, hHat0, hFin, hAgree)` (paper hypotheses), `(sol k).hmNonneg`
  -- (from `RegularizedBareSolution`), `(sol k).{hmLp, huLp, hDuLp}`
  -- (after δ-reducing `gammaBar` to `α(β+1)/β`), `hV_paper`, plus
  -- per-`k` measurabilities `(hm_measRaw, hu_measRaw, hDu_measRaw,
  -- hV_meas)` to assemble `AEStronglyMeasurable` of the residual.
  let hRes_Lp_k : ∀ k : ℕ,
      Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (StationaryMFG.Hamiltonian.betaBar' hpow.β))
        (StationaryMFG.Theorems.SimplePower.hjbResidual
          V H (residues.sol k).Du (residues.sol k).m (residues.sol k).u) :=
    fun k => by
      -- `MemLpPer (ENNReal.ofReal (β+1)) m` from `(sol k).hmLp`.
      -- The structure exponent `βBarReal` was `subst`ed to `hpow.β + 1`.
      have hμ : Periodic.MemLpPer (d := d)
                  (ENNReal.ofReal (hpow.β + 1)) (residues.sol k).m :=
        (residues.sol k).hmLp
      -- `MemLpPer (ENNReal.ofReal (α(β+1)/β)) u` from `(sol k).huLp`.
      -- After `subst hγBarPaper`, the structure exponent
      -- `γBarReal = hpow.α * (hpow.β + 1) / hpow.β`; `gammaBar` is
      -- definitionally equal.
      have hυ : Periodic.MemLpPer (d := d)
                  (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))
                  (residues.sol k).u := (residues.sol k).huLp
      have hDυ : ∀ i, Periodic.MemLpPer (d := d)
                  (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))
                  ((residues.sol k).Du i) := (residues.sol k).hDuLp
      -- Build a.e.-strong measurability of the residual from the
      -- `MemLpPer` witnesses on `(sol k).{u, Du, m}` and `hV`.
      -- iter `infra-P5-T10-drop-hu_measRaw-hDu_measRaw-final`: `u`/`Du`
      -- AE measurabilities now sourced from per-`k` `MemLpPer` (no
      -- longer raw fields on `T10PaperResidues`).
      have hu_aemeas : AEMeasurable (residues.sol k).u
                        (MeasureTheory.volume.restrict (UnitCube d)) :=
        (residues.sol k).huLp.aestronglyMeasurable.aemeasurable
      have hDu_aemeas : ∀ i, AEMeasurable ((residues.sol k).Du i)
                        (MeasureTheory.volume.restrict (UnitCube d)) :=
        fun i => ((residues.sol k).hDuLp i).aestronglyMeasurable.aemeasurable
      -- iter `infra-P5-T10-drop-hm_measRaw-hV_meas-final`: `hm`/`hV`
      -- now sourced from `MemLpPer` witnesses (no longer raw fields).
      have hm_aemeas : AEMeasurable (residues.sol k).m
                        (MeasureTheory.volume.restrict (UnitCube d)) :=
        (residues.sol k).hmLp.aestronglyMeasurable.aemeasurable
      have hV_aemeas : AEMeasurable V
                        (MeasureTheory.volume.restrict (UnitCube d)) :=
        hV.aestronglyMeasurable.aemeasurable
      have hDu_pi_aemeas :
          AEMeasurable (fun x : (Fin d → ℝ) =>
                        (fun i : Fin d => (residues.sol k).Du i x))
            (MeasureTheory.volume.restrict (UnitCube d)) :=
        AEMeasurable.of_eval hDu_aemeas
      have hxpm : AEMeasurable
          (fun x : (Fin d → ℝ) =>
            (x, (fun i : Fin d => (residues.sol k).Du i x),
              (residues.sol k).m x))
          (MeasureTheory.volume.restrict (UnitCube d)) :=
        measurable_id.aemeasurable.prodMk
          (hDu_pi_aemeas.prodMk hm_aemeas)
      have hH_aemeas : AEMeasurable
          (fun x : (Fin d → ℝ) =>
            H x (fun i => (residues.sol k).Du i x)
              ((residues.sol k).m x))
          (MeasureTheory.volume.restrict (UnitCube d)) :=
        hpow.measurable_H.comp_aemeasurable hxpm
      have hg_meas :
          MeasureTheory.AEStronglyMeasurable
            (fun x : (Fin d → ℝ) =>
              -((residues.sol k).u x)
                - H x (fun i => (residues.sol k).Du i x)
                    ((residues.sol k).m x)
                + V x)
            (MeasureTheory.volume.restrict (UnitCube d)) :=
        ((hu_aemeas.neg.sub hH_aemeas).add hV_aemeas).aestronglyMeasurable
      -- Apply `g_memLp_betaBar'_nonneg`. The result has exponent
      -- `(hpow.β + 1) / hpow.β` which equals `betaBar' hpow.β` by `rfl`.
      have hres :=
        StationaryMFG.Hamiltonian.g_memLp_betaBar'_nonneg
          (d := d) hpow hHat0 hFin hAgree
          V (residues.sol k).u (residues.sol k).m (residues.sol k).Du
          (residues.sol k).hmNonneg hg_meas hμ hυ hDυ hV_paper
      -- Identify with `hjbResidual`. `betaBar' hpow.β = (hpow.β + 1)/hpow.β`
      -- definitionally, and the `hjbResidual` body matches the producer's
      -- output body.
      change Periodic.MemLpPer _ (fun x =>
        -(residues.sol k).u x - H x (fun i => (residues.sol k).Du i x)
          ((residues.sol k).m x) + V x)
      exact hres
  -- **iter 419+ / `hMresidual_int_k`**: per-`k` integrability of
  -- `m · residual` via Hölder pair `(βBar', βBar) = (βBarReal',
  -- hpow.β + 1)`. Mirrors `hResM` in
  -- `finalIntegrabilityPaperResidue_of_lpResidue` (lines 21383–21406 of
  -- `RegularizedSequence.lean`), adapted to the per-`k` solution.
  have hβBar'_pos : 0 < βBarReal' := by
    rw [hβBar'Paper]
    have hβ_pos : 0 < hpow.β := hpow.hβ
    exact div_pos hβpos hβ_pos
  have h_toReal_βBar : (ENNReal.ofReal (hpow.β + 1)).toReal = hpow.β + 1 :=
    ENNReal.toReal_ofReal hβpos.le
  have h_toReal_βBar' : (ENNReal.ofReal βBarReal').toReal = βBarReal' :=
    ENNReal.toReal_ofReal hβBar'_pos.le
  -- `hExp.βConj : HolderConjugate (ofReal (hpow.β+1)).toReal
  --                                (ofReal βBarReal').toReal`.
  -- Take `.symm` to get the (βBar', βBar) form expected by
  -- `MemLpPer.integrable_mul`'s call below (residual then m).
  have hβConj_real : Real.HolderConjugate βBarReal' (hpow.β + 1) := by
    have h := hExp.βConj
    rw [h_toReal_βBar, h_toReal_βBar'] at h
    exact h.symm
  -- Identify the residual's exponent `betaBar' hpow.β = (β+1)/β` with
  -- `βBarReal'` via `hβBar'Paper.symm`.
  have hβBar'_eq_paper : (StationaryMFG.Hamiltonian.betaBar' hpow.β) = βBarReal' := by
    simp [StationaryMFG.Hamiltonian.betaBar', hβBar'Paper]
  have hMresidual_int_k : ∀ k : ℕ, MeasureTheory.Integrable
            (fun x => (residues.sol k).m x *
              StationaryMFG.Theorems.SimplePower.hjbResidual
                V H (residues.sol k).Du (residues.sol k).m
                (residues.sol k).u x)
            (MeasureTheory.volume.restrict (UnitCube d)) := by
    intro k
    -- Recast residual exponent to `ENNReal.ofReal βBarReal'`.
    have hRes_Lp_k' : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal βBarReal')
        (StationaryMFG.Theorems.SimplePower.hjbResidual
          V H (residues.sol k).Du (residues.sol k).m (residues.sol k).u) := by
      have h := hRes_Lp_k k
      rw [hβBar'_eq_paper] at h
      exact h
    -- Apply periodic Hölder integrability: residual · m on the cube.
    have hInt :
        MeasureTheory.IntegrableOn
          (fun x =>
            StationaryMFG.Theorems.SimplePower.hjbResidual
              V H (residues.sol k).Du (residues.sol k).m
              (residues.sol k).u x
            * (residues.sol k).m x)
          (UnitCube d) :=
      Periodic.MemLpPer.integrable_mul (d := d) hβConj_real
        hRes_Lp_k' (residues.sol k).hmLp
    -- Commute the product to land at `m · residual`.
    have hInt' : MeasureTheory.Integrable
        (fun x =>
          StationaryMFG.Theorems.SimplePower.hjbResidual
            V H (residues.sol k).Du (residues.sol k).m
            (residues.sol k).u x
          * (residues.sol k).m x)
        (MeasureTheory.volume.restrict (UnitCube d)) := hInt
    refine hInt'.congr ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    ring
  -- **iter post-419 / drop-`hMbetaRaw`**: derive per-`k`
  -- integrability of `m^β` from `(sol k).hmLp` (`MemLpPer (β+1) m`)
  -- via `Periodic.MemLpPer.mono_exponent_finite` (descend to L^β on
  -- the finite-measure cube) followed by `MemLp.integrable_norm_rpow`,
  -- realigning `‖m‖^β = m^β` a.e. via `(sol k).hmNonneg`.
  have hMbeta_int_k : ∀ k : ℕ, MeasureTheory.Integrable
            (fun x => (residues.sol k).m x ^ hpow.β)
            (MeasureTheory.volume.restrict (UnitCube d)) := by
    intro k
    have hβ_pos : 0 < hpow.β := hpow.hβ
    have hβ1_pos : 0 < hpow.β + 1 := by linarith
    have hle : ENNReal.ofReal hpow.β ≤ ENNReal.ofReal (hpow.β + 1) :=
      ENNReal.ofReal_le_ofReal (by linarith)
    have htop : ENNReal.ofReal (hpow.β + 1) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hmemLp_β1 : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (hpow.β + 1)) (residues.sol k).m :=
      (residues.sol k).hmLp
    have hmemLp_β : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal hpow.β) (residues.sol k).m :=
      Periodic.MemLpPer.mono_exponent_finite hle htop hmemLp_β1
    have hp_ne_zero : ENNReal.ofReal hpow.β ≠ 0 :=
      (ENNReal.ofReal_pos.mpr hβ_pos).ne'
    have hp_ne_top : ENNReal.ofReal hpow.β ≠ ⊤ := ENNReal.ofReal_ne_top
    have hmL : MeasureTheory.MemLp (residues.sol k).m
        (ENNReal.ofReal hpow.β)
        (MeasureTheory.volume.restrict (UnitCube d)) := hmemLp_β
    have hint_norm : MeasureTheory.Integrable
        (fun x => ‖(residues.sol k).m x‖ ^ (ENNReal.ofReal hpow.β).toReal)
        (MeasureTheory.volume.restrict (UnitCube d)) :=
      hmL.integrable_norm_rpow hp_ne_zero hp_ne_top
    have hp_toReal : (ENNReal.ofReal hpow.β).toReal = hpow.β :=
      ENNReal.toReal_ofReal hβ_pos.le
    rw [hp_toReal] at hint_norm
    refine hint_norm.congr ?_
    have hmnn := (residues.sol k).hmNonneg
    filter_upwards [hmnn] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx]
  -- **iter post-420 / drop-`hRHSaboveRaw`**: derive per-`k`
  -- integrability of `|V| + C·(m^β + 1)` from `hV : MemLpPer βBar' V`
  -- (descended to L¹ via `MemLp.integrable`, then `Integrable.abs` to
  -- get `|V| ∈ L¹`), the existing `hMbeta_int_k` (`m^β ∈ L¹`), and
  -- `integrable_const 1` on the finite-measure cube; combined via
  -- `Integrable.add` and `Integrable.const_mul`.
  have hRHSabove_int_k : ∀ k : ℕ, MeasureTheory.Integrable
            (fun x => |V x| + hpow.C * ((residues.sol k).m x ^ hpow.β + 1))
            (MeasureTheory.volume.restrict (UnitCube d)) := by
    haveI : MeasureTheory.IsFiniteMeasure
        (MeasureTheory.volume.restrict (UnitCube (d := d))) :=
      ⟨by
        rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ]
        simp⟩
    have h_one_le_βBar' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal βBarReal' :=
      hExp.betaBar'_one_lt.le
    have hV_int : MeasureTheory.Integrable V
        (MeasureTheory.volume.restrict (UnitCube d)) :=
      hV.toMemLp.integrable h_one_le_βBar'
    have hAbsV_int : MeasureTheory.Integrable (fun x => |V x|)
        (MeasureTheory.volume.restrict (UnitCube d)) :=
      hV_int.abs
    intro k
    have hMbeta1_int : MeasureTheory.Integrable
        (fun x => (residues.sol k).m x ^ hpow.β + 1)
        (MeasureTheory.volume.restrict (UnitCube d)) :=
      (hMbeta_int_k k).add (MeasureTheory.integrable_const 1)
    have hCMbeta1_int : MeasureTheory.Integrable
        (fun x => hpow.C * ((residues.sol k).m x ^ hpow.β + 1))
        (MeasureTheory.volume.restrict (UnitCube d)) :=
      hMbeta1_int.const_mul hpow.C
    exact hAbsV_int.add hCMbeta1_int
  -- **iter 424 / `hMu_int_k`** (`infra-P5-theorem1-T10-derive-mU-int-inline`):
  -- per-`k` integrability of `m · u` via Hölder pair
  -- `(βBar', βBar) = (βBarReal', hpow.β + 1)`. Sources:
  -- * `(residues.sol k).hmLp : MemLpPer (ofReal (β+1)) m`
  -- * `(residues.cBundles k).hUbetap_int : Integrable (|u|^βBar' h.β)`
  --   plus `residues.hu_measRaw k`, upgraded to `MemLpPer βBar' u` via
  --   Mathlib's `integrable_norm_rpow_iff` (after realigning the
  --   exponent `betaBar' hpow.β = βBarReal'` and identifying
  --   `‖u x‖ = |u x|` for real `u`).
  -- * `hβConj_real : Real.HolderConjugate βBarReal' (hpow.β + 1)`.
  have hMu_int_k : ∀ k : ℕ, MeasureTheory.Integrable
      (fun x => (residues.sol k).m x * (residues.sol k).u x)
      (MeasureTheory.volume.restrict (UnitCube d)) := by
    intro k
    -- Step 1: realign exponent. `(cBundles k).hUbetap_int` has
    -- exponent `betaBar' hpow.β`; rewrite to `βBarReal'`.
    have hu_pow_int : MeasureTheory.Integrable
        (fun x => |(residues.sol k).u x| ^ βBarReal')
        (MeasureTheory.volume.restrict (UnitCube d)) := by
      have h := (residues.cBundles k).hUbetap_int
      rw [hβBar'_eq_paper] at h
      exact h
    -- Step 2: identify `|u x|` with `‖u x‖` for `u : (Fin d → ℝ) → ℝ`.
    have hu_norm_int : MeasureTheory.Integrable
        (fun x => ‖(residues.sol k).u x‖ ^ βBarReal')
        (MeasureTheory.volume.restrict (UnitCube d)) := by
      refine hu_pow_int.congr ?_
      refine Filter.Eventually.of_forall (fun x => ?_)
      simp [Real.norm_eq_abs]
    -- Step 3: upgrade to `MemLp u (ofReal βBarReal')` via
    -- `integrable_norm_rpow_iff`.
    -- iter `infra-P5-T10-drop-hu_measRaw-hDu_measRaw-final`: source
    -- AE strong measurability directly from `(sol k).huLp`.
    have hu_aesm : MeasureTheory.AEStronglyMeasurable
        (residues.sol k).u
        (MeasureTheory.volume.restrict (UnitCube d)) :=
      (residues.sol k).huLp.aestronglyMeasurable
    have hp_zero : ENNReal.ofReal βBarReal' ≠ 0 :=
      (ENNReal.ofReal_pos.mpr hβBar'_pos).ne'
    have hp_top : ENNReal.ofReal βBarReal' ≠ ⊤ := ENNReal.ofReal_ne_top
    have hu_norm_int' : MeasureTheory.Integrable
        (fun x => ‖(residues.sol k).u x‖ ^
                    (ENNReal.ofReal βBarReal').toReal)
        (MeasureTheory.volume.restrict (UnitCube d)) := by
      rw [h_toReal_βBar']; exact hu_norm_int
    have hu_memLp : MeasureTheory.MemLp (residues.sol k).u
        (ENNReal.ofReal βBarReal')
        (MeasureTheory.volume.restrict (UnitCube d)) :=
      (MeasureTheory.integrable_norm_rpow_iff hu_aesm hp_zero hp_top).mp
        hu_norm_int'
    -- Step 4: wrap as `MemLpPer βBar' u` (defeq to MemLp on the
    -- restricted measure).
    have hu_lp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal βBarReal') (residues.sol k).u := hu_memLp
    -- Step 5: apply Hölder pairing `(βBar', βBar)` to `u · m`, then
    -- commute to land at `m · u`.
    have hUM_int :
        MeasureTheory.IntegrableOn
          (fun x => (residues.sol k).u x * (residues.sol k).m x)
          (UnitCube d) :=
      Periodic.MemLpPer.integrable_mul (d := d) hβConj_real
        hu_lp (residues.sol k).hmLp
    have hUM_int' : MeasureTheory.Integrable
        (fun x => (residues.sol k).u x * (residues.sol k).m x)
        (MeasureTheory.volume.restrict (UnitCube d)) := hUM_int
    refine hUM_int'.congr ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    ring
  -- **iter 425 / `hMDpHDu_int_k`** (`infra-P5-theorem1-T10-derive-mDpH-Du-int-inline`):
  -- per-`k` integrability of `m · (DpH ⬝ Du)` via the algebraic
  -- identity `m · (DpH ⬝ Du) = ∑ i, (mDpH …)_i · Du i` plus per-coord
  -- Hölder pair `(γBar', γBar)`. Mirrors `hFluxInt` discharge in
  -- `finalIntegrabilityPaperResidue_of_lpResidue` (lines 21407–21435
  -- of `RegularizedSequence.lean`), adapted from the weak-limit
  -- triple `(wkBundle.{mLim, DuLim})` to the per-`k`
  -- `(sol k).{m, Du}`.
  have hMDpHDu_int_k : ∀ k : ℕ, MeasureTheory.Integrable
      (fun x => (residues.sol k).m x *
        ((DpH x (fun i => (residues.sol k).Du i x)
                ((residues.sol k).m x)) ⬝
            (fun i => (residues.sol k).Du i x)))
      (MeasureTheory.volume.restrict (UnitCube d)) := by
    intro k
    -- Set the structure exponents.
    set γ : ℝ := hpow.α * (hpow.β + 1) / hpow.β with hγ_def
    have hγpos' : 0 < γ := hγpos
    -- Per-`k` measurabilities. iter `infra-P5-T10-drop-hu_measRaw-hDu_measRaw-final`:
    -- `hDu`/`hu` AE measurabilities now sourced from per-`k` `MemLpPer`
    -- witnesses (no longer raw fields on `T10PaperResidues`).
    have hDu_aemeas : ∀ i, AEMeasurable ((residues.sol k).Du i)
                      (MeasureTheory.volume.restrict (UnitCube d)) :=
      fun i => ((residues.sol k).hDuLp i).aestronglyMeasurable.aemeasurable
    have hm_aemeas : AEMeasurable (residues.sol k).m
                      (MeasureTheory.volume.restrict (UnitCube d)) :=
      (residues.sol k).hmLp.aestronglyMeasurable.aemeasurable
    have hDu_pi_aemeas :
        AEMeasurable (fun x : (Fin d → ℝ) =>
                      (fun i : Fin d => (residues.sol k).Du i x))
          (MeasureTheory.volume.restrict (UnitCube d)) :=
      AEMeasurable.of_eval hDu_aemeas
    have hxpm : AEMeasurable
        (fun x : (Fin d → ℝ) =>
          (x, (fun i : Fin d => (residues.sol k).Du i x),
            (residues.sol k).m x))
        (MeasureTheory.volume.restrict (UnitCube d)) :=
      measurable_id.aemeasurable.prodMk
        (hDu_pi_aemeas.prodMk hm_aemeas)
    have hDpH_aemeas : AEMeasurable
        (fun x : (Fin d → ℝ) =>
          DpH x (fun i => (residues.sol k).Du i x)
            ((residues.sol k).m x))
        (MeasureTheory.volume.restrict (UnitCube d)) :=
      hpow.measurable_DpH.comp_aemeasurable hxpm
    -- Step 1: `MemLpPer γBar' (mDpH DpH ·)` (vector field).
    -- Mirrors steps 1–3 of `Hamiltonian.mDpH_integrable_of_memLpPer`
    -- (Estimates.lean lines 1607–1702): dominator membership, pointwise
    -- bound (extended to `m = 0`), then `mDpH_mem_Lp_gammaBar'`.
    have hμ_Lp : Periodic.MemLpPer (d := d)
                  (ENNReal.ofReal (hpow.β + 1)) (residues.sol k).m :=
      (residues.sol k).hmLp
    have hDu_Lp : ∀ i, Periodic.MemLpPer (d := d)
                  (ENNReal.ofReal γ) ((residues.sol k).Du i) :=
      (residues.sol k).hDuLp
    have hμ_nn : ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
                  0 ≤ (residues.sol k).m x := (residues.sol k).hmNonneg
    -- Dominator membership.
    have hG_mem :
        Periodic.MemLpPer
          (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β /
            (hpow.α * (hpow.β + 1) / hpow.β - 1)))
          (fun x : (Fin d → ℝ) =>
            hpow.C * ((residues.sol k).m x *
                ‖fun j => (residues.sol k).Du j x‖ ^ (hpow.α - 1)
              + (residues.sol k).m x ^ (1 + hpow.β - hpow.β / hpow.α)
              + (residues.sol k).m x)) :=
      StationaryMFG.Hamiltonian.mDpH_dominator_memLpPer_gammaBar' hpow
        (residues.sol k).m (residues.sol k).Du hμ_Lp hDu_Lp
    -- AE strong measurability of the flux vector field
    -- `mDpH DpH x (Du x) (m x) = m x • DpH x (Du x) (m x)`.
    have hF_meas :
        MeasureTheory.AEStronglyMeasurable
          (fun x : (Fin d → ℝ) =>
            StationaryMFG.Hamiltonian.mDpH DpH x
              (fun i => (residues.sol k).Du i x) ((residues.sol k).m x))
          (MeasureTheory.volume.restrict (UnitCube d)) := by
      unfold StationaryMFG.Hamiltonian.mDpH
      exact (hm_aemeas.smul hDpH_aemeas).aestronglyMeasurable
    -- Pointwise bound `‖mDpH …‖ ≤ G x` a.e., extending
    -- `mDpH_pointwise_bound` (which assumes `m x > 0`) to `m x ≥ 0`.
    have hF_le :
        ∀ᵐ x ∂(MeasureTheory.volume.restrict (UnitCube d)),
          ‖StationaryMFG.Hamiltonian.mDpH DpH x
              (fun i => (residues.sol k).Du i x) ((residues.sol k).m x)‖
            ≤ hpow.C * ((residues.sol k).m x *
                  ‖fun j => (residues.sol k).Du j x‖ ^ (hpow.α - 1)
                + (residues.sol k).m x ^ (1 + hpow.β - hpow.β / hpow.α)
                + (residues.sol k).m x) := by
      filter_upwards [StationaryMFG.Hamiltonian.mDpH_pointwise_bound hpow
                        (fun x => fun i => (residues.sol k).Du i x), hμ_nn]
        with x hxbnd hxnn
      rcases lt_or_eq_of_le hxnn with hxpos | hxz
      · exact hxbnd ((residues.sol k).m x) hxpos
      · -- `m x = 0`: LHS is `‖0 • v‖ = 0`, RHS is non-negative.
        have hmzero : (residues.sol k).m x = 0 := hxz.symm
        have hLHS : StationaryMFG.Hamiltonian.mDpH DpH x
            (fun i => (residues.sol k).Du i x) ((residues.sol k).m x) = 0 := by
          unfold StationaryMFG.Hamiltonian.mDpH
          rw [hmzero, zero_smul]
        rw [hLHS, norm_zero]
        have hα1_nn : 0 ≤ ‖fun j => (residues.sol k).Du j x‖ ^ (hpow.α - 1) :=
          Real.rpow_nonneg (norm_nonneg _) _
        have hμα_nn :
            0 ≤ (residues.sol k).m x ^ (1 + hpow.β - hpow.β / hpow.α) :=
          Real.rpow_nonneg hxnn _
        have hsum_nn :
            0 ≤ (residues.sol k).m x *
                ‖fun j => (residues.sol k).Du j x‖ ^ (hpow.α - 1)
              + (residues.sol k).m x ^ (1 + hpow.β - hpow.β / hpow.α)
              + (residues.sol k).m x := by
          have h1 : 0 ≤ (residues.sol k).m x *
                ‖fun j => (residues.sol k).Du j x‖ ^ (hpow.α - 1) :=
            mul_nonneg hxnn hα1_nn
          linarith
        exact mul_nonneg hpow.hC.le hsum_nn
    -- Vector `MemLpPer γBar' (mDpH DpH ·)`.
    have hF_lp :
        Periodic.MemLpPer
          (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β /
            (hpow.α * (hpow.β + 1) / hpow.β - 1)))
          (fun x : (Fin d → ℝ) =>
            StationaryMFG.Hamiltonian.mDpH DpH x
              (fun i => (residues.sol k).Du i x) ((residues.sol k).m x)) := by
      refine StationaryMFG.Hamiltonian.mDpH_mem_Lp_gammaBar'
        (q := ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β /
                (hpow.α * (hpow.β + 1) / hpow.β - 1)))
        (m := (residues.sol k).m)
        (Du := fun x => fun i => (residues.sol k).Du i x)
        (F := fun x => StationaryMFG.Hamiltonian.mDpH DpH x
                (fun i => (residues.sol k).Du i x) ((residues.sol k).m x))
        (C := hpow.C) (α := hpow.α) (β := hpow.β)
        hF_meas hF_le hG_mem
    -- Recast to `MemLpPer (ofReal γBarReal')` via `hγBar'Paper.symm`.
    have hF_lp' : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal γBarReal')
        (fun x : (Fin d → ℝ) =>
          StationaryMFG.Hamiltonian.mDpH DpH x
            (fun i => (residues.sol k).Du i x) ((residues.sol k).m x)) := by
      have hbb : hpow.α * (hpow.β + 1) / hpow.β /
                  (hpow.α * (hpow.β + 1) / hpow.β - 1) = γBarReal' :=
        hγBar'Paper.symm
      rw [show ENNReal.ofReal γBarReal'
            = ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β /
                (hpow.α * (hpow.β + 1) / hpow.β - 1)) from by rw [hbb]]
      exact hF_lp
    -- Step 2: per-coordinate `MemLpPer γBar' ((mDpH ...) i)` via
    -- `MemLp.mono` against the vector norm bound `‖F i‖ ≤ ‖F‖`.
    have hF_coord_lp : ∀ i, Periodic.MemLpPer (d := d)
        (ENNReal.ofReal γBarReal')
        (fun x : (Fin d → ℝ) =>
          StationaryMFG.Hamiltonian.mDpH DpH x
            (fun i => (residues.sol k).Du i x) ((residues.sol k).m x) i) := by
      intro i
      -- AE strong measurability of the coordinate `(mDpH ...) i`.
      have hcoord_meas :
          MeasureTheory.AEStronglyMeasurable
            (fun x : (Fin d → ℝ) =>
              StationaryMFG.Hamiltonian.mDpH DpH x
                (fun i => (residues.sol k).Du i x)
                ((residues.sol k).m x) i)
            (MeasureTheory.volume.restrict (UnitCube d)) := by
        unfold StationaryMFG.Hamiltonian.mDpH
        -- AE-measurable version: extract coordinate `i` via `AEMeasurable.eval`.
        have h := (hm_aemeas.smul hDpH_aemeas)
        exact (h.eval i).aestronglyMeasurable
      -- Pointwise `‖F i‖ ≤ ‖F‖`.
      have hcoord_le : ∀ x,
          ‖StationaryMFG.Hamiltonian.mDpH DpH x
              (fun i => (residues.sol k).Du i x)
              ((residues.sol k).m x) i‖
            ≤ ‖StationaryMFG.Hamiltonian.mDpH DpH x
                (fun i => (residues.sol k).Du i x)
                ((residues.sol k).m x)‖ :=
        fun x => norm_le_pi_norm _ i
      -- Apply `MemLp.mono`.
      have : MeasureTheory.MemLp
          (fun x : (Fin d → ℝ) =>
            StationaryMFG.Hamiltonian.mDpH DpH x
              (fun i => (residues.sol k).Du i x) ((residues.sol k).m x) i)
          (ENNReal.ofReal γBarReal')
          (MeasureTheory.volume.restrict (UnitCube d)) := by
        refine MeasureTheory.MemLp.mono (hF_lp'.toMemLp) hcoord_meas ?_
        refine Filter.Eventually.of_forall (fun x => ?_)
        exact hcoord_le x
      exact MemLp.toMemLpPer this
    -- Step 3: Hölder conjugacy `(γBarReal', γBarReal)`.
    -- `hExp.γConj : Real.HolderConjugate gammaBar.toReal
    --                                  (gammaBar.toReal/(gammaBar.toReal-1))`.
    -- After substitutions, `gammaBar = ofReal γBarReal` with
    -- `γBarReal = α(β+1)/β = γ`. We rewrite via `hγBar'Paper.symm`.
    have h_toReal_γBar : (ENNReal.ofReal γ).toReal = γ :=
      ENNReal.toReal_ofReal hγpos.le
    have hγConj_real : Real.HolderConjugate γBarReal' γ := by
      have h := hExp.γConj
      -- `hExp.γConj` is at `gammaBar.toReal`. After `subst`, the
      -- structure exponent `gammaBar = ENNReal.ofReal γ`, so
      -- `gammaBar.toReal = γ`.
      rw [h_toReal_γBar] at h
      -- `h : Real.HolderConjugate γ (γ/(γ-1))`.
      -- Goal: `HolderConjugate γBarReal' γ`. Use `.symm` after
      -- bridging via `hγBar'Paper.symm`.
      have hbb : γ / (γ - 1) = γBarReal' := hγBar'Paper.symm
      rw [hbb] at h
      exact h.symm
    -- Step 4: per-`i` Hölder integrability.
    have hcoord_int : ∀ i, MeasureTheory.Integrable
        (fun x =>
          StationaryMFG.Hamiltonian.mDpH DpH x
              (fun i => (residues.sol k).Du i x)
              ((residues.sol k).m x) i
          * (residues.sol k).Du i x)
        (MeasureTheory.volume.restrict (UnitCube d)) := by
      intro i
      have hI :=
        Periodic.MemLpPer.integrable_mul (d := d) hγConj_real
          (hF_coord_lp i) ((residues.sol k).hDuLp i)
      exact hI
    -- Step 5: sum over `i : Fin d`.
    have hsum_int : MeasureTheory.Integrable
        (fun x => ∑ i : Fin d,
          StationaryMFG.Hamiltonian.mDpH DpH x
              (fun i => (residues.sol k).Du i x)
              ((residues.sol k).m x) i
          * (residues.sol k).Du i x)
        (MeasureTheory.volume.restrict (UnitCube d)) :=
      MeasureTheory.integrable_finset_sum (Finset.univ)
        (fun i _ => hcoord_int i)
    -- Step 6: identify `m · (DpH ⬝ Du) = ∑ i, (mDpH …)_i · Du_i`
    -- pointwise via `mDpH = m • DpH`, `Pi.smul_apply`, `euclideanDot`,
    -- and `Finset.mul_sum`.
    refine hsum_int.congr ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    -- Compute both sides at `x`.
    -- RHS: `∑ i, ((m x) • DpH x (Du x) (m x)) i * Du i x
    --      = ∑ i, m x * (DpH ...) i * Du i x
    --      = m x * ∑ i, (DpH ...) i * Du i x
    --      = m x * (DpH ... ⬝ Du)`.
    show (∑ i : Fin d,
            StationaryMFG.Hamiltonian.mDpH DpH x
              (fun i => (residues.sol k).Du i x)
              ((residues.sol k).m x) i
            * (residues.sol k).Du i x)
        = (residues.sol k).m x *
          ((DpH x (fun i => (residues.sol k).Du i x)
              ((residues.sol k).m x)) ⬝
            (fun i => (residues.sol k).Du i x))
    unfold StationaryMFG.Hamiltonian.mDpH StationaryMFG.Hamiltonian.euclideanDot
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  -- **iter post-425 / `hRHSbelow_int_k`** (`infra-P5-theorem1-T10-drop-hRHSbelowRaw-final`):
  -- per-`k` integrability of the paper RHS lower-bound integrand
  -- combining the four ingredients
  --   `hMresidual_int_k`, `hMu_int_k`, `hMDpHDu_int_k`, `(cBundles k).hEpsInt`.
  -- Algebraic identity: `hjbResidual = -u - H + V` ⇒ `-H = hjbResidual + u - V`,
  -- hence `m·(-H + DpH·Du) + V·m + epsTerms
  --        = m·hjbResidual + m·u + m·(DpH·Du) + epsTerms`
  -- (the `-m·V` and `+V·m` cancel pointwise).
  have hRHSbelow_int_k : ∀ k : ℕ, MeasureTheory.Integrable
      (fun x =>
        (residues.sol k).m x *
            (-H x (fun i => (residues.sol k).Du i x) ((residues.sol k).m x)
              + (DpH x (fun i => (residues.sol k).Du i x)
                    ((residues.sol k).m x))
                  ⬝ (fun i => (residues.sol k).Du i x))
          + V x * (residues.sol k).m x
          + (residues.cBundles k).epsTerms x)
      (MeasureTheory.volume.restrict (UnitCube d)) := by
    intro k
    have hsum : MeasureTheory.Integrable
        (fun x =>
          (residues.sol k).m x *
              StationaryMFG.Theorems.SimplePower.hjbResidual
                V H (residues.sol k).Du (residues.sol k).m
                (residues.sol k).u x
            + (residues.sol k).m x * (residues.sol k).u x
            + (residues.sol k).m x *
                ((DpH x (fun i => (residues.sol k).Du i x)
                      ((residues.sol k).m x))
                  ⬝ (fun i => (residues.sol k).Du i x))
            + (residues.cBundles k).epsTerms x)
        (MeasureTheory.volume.restrict (UnitCube d)) :=
      (((hMresidual_int_k k).add (hMu_int_k k)).add
          (hMDpHDu_int_k k)).add (residues.cBundles k).hEpsInt
    refine hsum.congr ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    simp [StationaryMFG.Theorems.SimplePower.hjbResidual]
    ring
  -- **iter post-419 / drop-`hDu_norm_intRaw`**: derive per-`k`
  -- integrability of `‖Du‖^γ̄` from per-coord `(sol k).hDuLp i` via
  -- `MemLp.integrable_norm_rpow`, dominated by the finite sum
  -- `∑ i, ‖Du i x‖^γ̄` (sup-norm bound `‖v‖ ≤ max_i |v_i|` on
  -- `Fin d → ℝ`).
  have hDu_norm_int_k : ∀ k : ℕ, MeasureTheory.Integrable
      (fun x => ‖(fun i => (residues.sol k).Du i x)‖ ^
                  StationaryMFG.Hamiltonian.gammaBar hpow.α hpow.β)
      (MeasureTheory.volume.restrict (UnitCube d)) := by
    intro k
    set γ : ℝ := StationaryMFG.Hamiltonian.gammaBar hpow.α hpow.β with hγ_def
    have hγ_nn : 0 ≤ γ := hγpos.le
    have hp_ne_zero : ENNReal.ofReal γ ≠ 0 :=
      (ENNReal.ofReal_pos.mpr hγpos).ne'
    have hp_ne_top : ENNReal.ofReal γ ≠ ⊤ := ENNReal.ofReal_ne_top
    have hp_toReal : (ENNReal.ofReal γ).toReal = γ :=
      ENNReal.toReal_ofReal hγ_nn
    -- Per-coordinate integrability of `‖Du i‖ ^ γ̄`.
    have hcoord_int : ∀ i, MeasureTheory.Integrable
        (fun x => ‖(residues.sol k).Du i x‖ ^ γ)
        (MeasureTheory.volume.restrict (UnitCube d)) := by
      intro i
      have hmemLp_i : Periodic.MemLpPer (d := d)
          (ENNReal.ofReal γ) ((residues.sol k).Du i) :=
        (residues.sol k).hDuLp i
      have hL : MeasureTheory.MemLp ((residues.sol k).Du i)
          (ENNReal.ofReal γ)
          (MeasureTheory.volume.restrict (UnitCube d)) := hmemLp_i
      have hI : MeasureTheory.Integrable
          (fun x => ‖(residues.sol k).Du i x‖ ^ (ENNReal.ofReal γ).toReal)
          (MeasureTheory.volume.restrict (UnitCube d)) :=
        hL.integrable_norm_rpow hp_ne_zero hp_ne_top
      simpa [hp_toReal] using hI
    -- Sum-of-coordinates is integrable.
    have hsum_int : MeasureTheory.Integrable
        (fun x => ∑ i : Fin d, ‖(residues.sol k).Du i x‖ ^ γ)
        (MeasureTheory.volume.restrict (UnitCube d)) :=
      MeasureTheory.integrable_finset_sum (Finset.univ) (fun i _ => hcoord_int i)
    -- AE strong measurability of the target via the per-coord
    -- AE measurabilities. iter `infra-P5-T10-drop-hu_measRaw-hDu_measRaw-final`:
    -- per-coord AE measurabilities now sourced from `(sol k).hDuLp i`.
    have hDu_aemeas : ∀ i, AEMeasurable ((residues.sol k).Du i)
                      (MeasureTheory.volume.restrict (UnitCube d)) :=
      fun i => ((residues.sol k).hDuLp i).aestronglyMeasurable.aemeasurable
    have hDu_pi_aemeas :
        AEMeasurable (fun x : (Fin d → ℝ) =>
                      (fun i : Fin d => (residues.sol k).Du i x))
          (MeasureTheory.volume.restrict (UnitCube d)) :=
      AEMeasurable.of_eval hDu_aemeas
    have htarget_aemeas : AEMeasurable
        (fun x : (Fin d → ℝ) =>
          ‖(fun i => (residues.sol k).Du i x)‖ ^ γ)
        (MeasureTheory.volume.restrict (UnitCube d)) :=
      hDu_pi_aemeas.norm.pow_const γ
    -- The pointwise dominator: `‖v‖^γ ≤ ∑ i, ‖v i‖^γ`.
    -- For `v : Fin d → ℝ`, the sup norm `‖v‖ = ⨆ i, ‖v i‖` so
    -- `‖v‖^γ = (max_i ‖v i‖)^γ ≤ ∑ i, ‖v i‖^γ` (each summand ≥ 0,
    -- and `max_i a_i = a_{i₀}` for some `i₀`).
    have hpoint_le : ∀ x,
        ‖(fun i => (residues.sol k).Du i x)‖ ^ γ
          ≤ ∑ i : Fin d, ‖(residues.sol k).Du i x‖ ^ γ := by
      intro x
      by_cases hd : d = 0
      · -- Empty index: `Fin 0 → ℝ` has `‖_‖ = 0`, RHS sum is 0,
        -- LHS `0^γ = 0` since `γ ≠ 0`.
        subst hd
        have hL : ‖(fun i => (residues.sol k).Du i x)‖ = 0 := by
          apply le_antisymm _ (norm_nonneg _)
          refine (pi_norm_le_iff_of_nonneg (le_refl (0 : ℝ))).mpr ?_
          intro i; exact i.elim0
        have hγ_ne : γ ≠ 0 := ne_of_gt hγpos
        simp [hL, Real.zero_rpow hγ_ne]
      · -- Non-empty index: pick `i₀` realising the sup.
        haveI : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero hd⟩⟩
        -- Each `‖Du i x‖^γ ≥ 0`.
        have hnn : ∀ i, 0 ≤ ‖(residues.sol k).Du i x‖ ^ γ :=
          fun i => Real.rpow_nonneg (norm_nonneg _) _
        -- Identify the maximiser `i₀`.
        obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin d,
            ‖(fun i => (residues.sol k).Du i x)‖ = ‖(residues.sol k).Du i₀ x‖ := by
          -- The Pi-norm on a finite product is `Finset.sup` of the
          -- coordinate norms; use that `Fin d` is non-empty.
          refine ⟨Classical.choose (Finset.exists_max_image
              (Finset.univ : Finset (Fin d))
              (fun i => ‖(residues.sol k).Du i x‖)
              ⟨⟨0, Nat.pos_of_ne_zero hd⟩, Finset.mem_univ _⟩), ?_⟩
          -- Use `pi_norm_le_iff_of_nonneg` on both sides.
          set j := Classical.choose (Finset.exists_max_image
              (Finset.univ : Finset (Fin d))
              (fun i => ‖(residues.sol k).Du i x‖)
              ⟨⟨0, Nat.pos_of_ne_zero hd⟩, Finset.mem_univ _⟩)
          have hj := Classical.choose_spec (Finset.exists_max_image
              (Finset.univ : Finset (Fin d))
              (fun i => ‖(residues.sol k).Du i x‖)
              ⟨⟨0, Nat.pos_of_ne_zero hd⟩, Finset.mem_univ _⟩)
          obtain ⟨_, hjmax⟩ := hj
          apply le_antisymm
          · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr ?_
            intro i
            exact hjmax i (Finset.mem_univ _)
          · exact norm_le_pi_norm (fun i => (residues.sol k).Du i x) j
        -- Now `‖v‖^γ = ‖Du i₀ x‖^γ ≤ ∑ i, ‖Du i x‖^γ`.
        rw [hi₀]
        exact Finset.single_le_sum
          (f := fun i => ‖(residues.sol k).Du i x‖ ^ γ)
          (s := (Finset.univ : Finset (Fin d)))
          (fun i _ => hnn i) (Finset.mem_univ i₀)
    -- The integrand is nonnegative.
    have hf_nn : ∀ x, 0 ≤
        ‖(fun i => (residues.sol k).Du i x)‖ ^ γ :=
      fun x => Real.rpow_nonneg (norm_nonneg _) _
    -- Integrability via `Integrable.mono'` against the dominating sum.
    refine hsum_int.mono' ?meas ?dom
    case meas =>
      exact htarget_aemeas.aestronglyMeasurable
    case dom =>
      refine Filter.Eventually.of_forall ?_
      intro x
      rw [Real.norm_eq_abs, abs_of_nonneg (hf_nn x)]
      exact hpoint_le x
  -- **iter `infra-P5-T10-v7-drain-paperHVbndAuth`**: per-`k`
  -- integrability of `|V| · m` (Hölder pair `(βBarReal', β+1)`, with
  -- `hβConj_real` already in scope above) and of `m` (L^{β+1} ⊂ L^1 on
  -- the finite-measure cube). These are the four extras consumed by
  -- the canonical `_paperHypotheses_int` aggregator after dropping the
  -- impossible `hVbnd : ∀ᵐ x, |V x| ≤ 0` field.
  --
  -- Build `|V| · m` integrability: bridge `V·m` (via Hölder) to `|V|·m`
  -- by congruence of integrands. We have `Periodic.MemLpPer.integrable_mul
  -- hβConj_real hV (residues.sol k).hmLp` giving `Integrable (V·m)`,
  -- but we need `Integrable (|V|·m)`. Since `(sol k).m ≥ 0` a.e., we
  -- have `|V·m| = |V|·m` a.e., so use `.abs` then realign via congr.
  have hVm_int_k : ∀ k : ℕ, MeasureTheory.Integrable
      (fun x => |V x| * (residues.sol k).m x)
      (MeasureTheory.volume.restrict (UnitCube d)) := by
    intro k
    have hVm : MeasureTheory.IntegrableOn
        (fun x => V x * (residues.sol k).m x) (UnitCube d) :=
      Periodic.MemLpPer.integrable_mul (d := d) hβConj_real hV
        (residues.sol k).hmLp
    have hVm' : MeasureTheory.Integrable
        (fun x => V x * (residues.sol k).m x)
        (MeasureTheory.volume.restrict (UnitCube d)) := hVm
    have hAbsVm : MeasureTheory.Integrable
        (fun x => |V x * (residues.sol k).m x|)
        (MeasureTheory.volume.restrict (UnitCube d)) := hVm'.abs
    refine hAbsVm.congr ?_
    have hmnn := (residues.sol k).hmNonneg
    filter_upwards [hmnn] with x hx
    rw [abs_mul, abs_of_nonneg hx]
  haveI : MeasureTheory.IsFiniteMeasure
      (MeasureTheory.volume.restrict (UnitCube (d := d))) :=
    ⟨by
      rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ]
      simp⟩
  have hβ1_pos : 0 < hpow.β + 1 := by have := hpow.hβ; linarith
  have hM_int_k : ∀ k : ℕ, MeasureTheory.Integrable (residues.sol k).m
      (MeasureTheory.volume.restrict (UnitCube d)) := fun k =>
    -- `m ∈ L^{β+1}` on the finite-measure cube, so `m ∈ L^1`.
    (residues.sol k).hmLp.toMemLp.integrable
      (by
        rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
        exact ENNReal.ofReal_le_ofReal (by linarith [hpow.hβ]))
  let aprioriResidue :
      StationaryMFG.Theorems.SimplePower.Banach.AprioriUniformResidueInputs
        (d := d) V H DpH
        (StationaryMFG.Hamiltonian.gammaBar hpow.α hpow.β)
        (hpow.β + 1) βBarReal' γBarReal' :=
    -- **Phase 1 sub-task 1c-c (v7 plan, D4.1c-c)**: route through the
    -- integral V-data residue producer
    -- `aprioriUniformResidueInputs_of_paperHypotheses_closedPaper_setInputs_int`.
    -- **iter `infra-P5-T10-v7-drain-paperHVbndAuth`**: that producer
    -- has been retyped to drop the transitional `Vbound`/`hVbnd`
    -- parameters and to take 4 extras (`hV_meas`, `hm_meas`,
    -- `hVm_int`, `hM_int`) for the canonical `_paperHypotheses_int`
    -- aggregator. The extras are derived inline from `hV_paper`,
    -- `(residues.sol k).hmLp`, and the existing Hölder pair
    -- `(βBar', β+1)` (mirrors `hMu_int_k` derivation above).
    --
    -- **iter 417 / drop-`hStrongVI_set`**: build per-`k`
    -- `SetAdditiveContinuityInputs (sol k)` from paper hypotheses +
    -- per-`k` measurabilities + dominator data via the iter-417
    -- producer `SetAdditiveContinuityInputs.of_paperHypotheses`, then
    -- consume the iter-414 `_setInputs` residue producer.
    -- **HMpos-3 retype**: `_setInputs_int` now threads three Hamiltonian
    -- extras (`hHat0`, `hFin`, `hAgree`) into `_paperHypotheses_int`,
    -- which calls the `_nonneg` aggregator sibling.
    StationaryMFG.Theorems.SimplePower.Banach.aprioriUniformResidueInputs_of_paperHypotheses_closedPaper_setInputs_int
      hmon hpow hHat0 hFin hAgree hV_paper hV
      -- Uniform `vData : AprioriVData (betaBar' hpow.β) V`, supplied
      -- by the D4.0a producer `AprioriVData.of_hV` from `hV_paper`.
      (StationaryMFG.Theorems.SimplePower.Banach.AprioriVData.of_hV
        (β := hpow.β) hpow.hβ V hV_paper)
      residues.epsSeq residues.epsSeq_pos residues.epsSeq_tendsto
      residues.sol residues.cBundles
      hRes_Lp_k
      (fun k =>
        -- **iter `infra-P5-T10-drop-setDominator-from-residues`**: replace
        -- the per-`k` dominator triple `(setDominator, setDominator_memLp,
        -- setDominator_bd)` with the closed-form derivation
        -- `SetAdditiveContinuityInputs.of_paperHypotheses_closed`,
        -- which builds the dominator internally from `(hpow, hHat0, hFin,
        -- hAgree, sol k, hV_paper)` via
        -- `setDominator_of_paperHypotheses`.
        StationaryMFG.Theorems.SimplePower.Banach.SetAdditiveContinuityInputs.of_paperHypotheses_closed
          hpow hpow.toRegularityH hHat0 hFin hAgree
          (residues.sol k) hV_paper
          ((residues.sol k).hmLp.aestronglyMeasurable.aemeasurable)
          (hV.aestronglyMeasurable.aemeasurable)
          ((residues.sol k).huLp.aestronglyMeasurable.aemeasurable)
          (fun i => ((residues.sol k).hDuLp i).aestronglyMeasurable.aemeasurable))
      (fun k =>
        StationaryMFG.Theorems.SimplePower.Banach.hIdentityRaw_of_regularizedPaperSolutionData_int
          (residues.paperSol k) (residues.cBundles k)
          (residues.epsTerms_align k))
      hRHSabove_int_k hMbeta_int_k hRHSbelow_int_k
      hu_aesm_volume hDu_aesm_volume hDu_norm_int_k
      (fun _k => (residues.paperSol _k).h_lagr)
      -- Four extras for canonical `_paperHypotheses_int`:
      hV_paper.aestronglyMeasurable
      (fun k => (residues.sol k).hmLp.aestronglyMeasurable)
      hVm_int_k
      hM_int_k
  let seq0 :
      StationaryMFG.Theorems.SimplePower.Banach.RegularizedSequenceData
        (d := d) (StationaryMFG.Hamiltonian.gammaBar hpow.α hpow.β)
        (hpow.β + 1) βBarReal' γBarReal' V H DpH :=
    StationaryMFG.Theorems.SimplePower.Banach.regularizedSequenceData_of_aprioriResidue
      aprioriResidue hβpos hγpos
  -- **HMinty-3 rewire (`infra-P5-T10-v7-HMinty-3-rewire-and-drain`)**.
  -- The previous chain `let seq := … ; let wkBundle :=
  -- weakLimitInputBundleAE_of_paperHypotheses_AE seq …` is replaced
  -- with the HMinty-2 producer
  -- `extractedWeakPairingData_of_regularizedSequence`, which returns an
  -- `ExtractedWeakPairingData` bundle containing:
  --   * the EXTRACTED subsequence `W.seq` (not the original `seq0`);
  --   * the AE-native weak-limit bundle `W.wkBundle` over the
  --     subsequence;
  --   * three universal weak-pairings `W.h_weak_{m,u,Du}` at the
  --     paper Hölder exponents, replacing the role of the legacy
  --     `T10PaperResidues.h_weak_{m,u,Du}Of` indirection (now deleted).
  -- The remaining chain consumers (Step 4 onward) use `seq` and
  -- `wkBundle` as before — they are now sourced from `W`. This drops
  -- the `h_minty_limit_auth` B-class authorisation; the universal
  -- pairings are sourced in-tree via the Route-1 bridge
  -- `weakConvPairing_universal_of_toWeakSpace_conv`.
  let W :=
    StationaryMFG.Theorems.SimplePower.Banach.extractedWeakPairingData_of_regularizedSequence
      (d := d) hpow hExp rfl hβBar'Paper rfl hγBar'Paper seq0
  let seq :
      StationaryMFG.Theorems.SimplePower.Banach.RegularizedSequenceData
        (d := d) (StationaryMFG.Hamiltonian.gammaBar hpow.α hpow.β)
        (hpow.β + 1) βBarReal' γBarReal' V H DpH :=
    W.seq
  let wkBundle :
      StationaryMFG.Theorems.SimplePower.Banach.WeakLimitInputBundleAE
        (d := d) (StationaryMFG.Hamiltonian.gammaBar hpow.α hpow.β) (hpow.β + 1) :=
    W.wkBundle
  -- The `wkBundle.{mLim,uLim,DuLim}` are definitionally the selector's.
  -- **Phase 4d** (`infra-P4-drop-mintyResidue-universal-chain`): the
  -- universal Minty-closure selector chain (`mintySelector`, `mintyClosure`,
  -- `hDuniv`) has been dropped. The three per-family `MintyClosureOn`
  -- certificates are now built directly from the per-family residues
  -- `residues.mintyData{Set,Signed,Transport}Of wkBundle` via
  -- `mintyClosure_familyNative_{set,signed,transport}_of_paperHypotheses`
  -- (see Step 8 below).
  -- Step 5: pairing selector.
  -- **`infra-P5-T10-drop-pairingResidueOf-final-hmu-pos`** (Option A):
  -- the `pairingResidueOf` field has been dropped from
  -- `T10PaperResidues`; its sole non-vacuous content is now the slim
  -- flat field `hμ_posOf`, and the wrapping
  -- `LimitPairingSelectorPaperResidue` record is constructed inline
  -- here.
  --
  -- **`infra-P5-T10-D5-hmu-pos-shape-audit`** (Outcome A): we now
  -- build three family-scoped pairing residues, one per paper-form
  -- family domain, sourced from the three flat fields
  -- `residues.hμ_posOf_{set,signed,transport}`. Each is consumed by
  -- the corresponding `_at` call below.
  let pairingResidue_set :
      StationaryMFG.Theorems.SimplePower.Banach.LimitPairingSelectorPaperResidue
        (d := d) (γBarReal := StationaryMFG.Hamiltonian.gammaBar hpow.α hpow.β)
        (βBarReal := hpow.β + 1)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        (V := V) (H := H) (DpH := DpH) hpow seq wkBundle
        (StationaryMFG.Theorems.SimplePower.Banach.D_set_family_paper (d := d)
          (ENNReal.ofReal (hpow.β + 1))
          wkBundle.mLim wkBundle.uLim wkBundle.DuLim) :=
    { hμ_nonneg := residues.hμ_posOf_set seq wkBundle }
  let pairingResidue_signed :
      StationaryMFG.Theorems.SimplePower.Banach.LimitPairingSelectorPaperResidue
        (d := d) (γBarReal := StationaryMFG.Hamiltonian.gammaBar hpow.α hpow.β)
        (βBarReal := hpow.β + 1)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        (V := V) (H := H) (DpH := DpH) hpow seq wkBundle
        (StationaryMFG.Theorems.SimplePower.Banach.D_signed_family_paper_nn (d := d)
          (ENNReal.ofReal (hpow.β + 1))
          wkBundle.mLim wkBundle.uLim wkBundle.DuLim) :=
    { hμ_nonneg := residues.hμ_posOf_signed seq wkBundle }
  let pairingResidue_transport :
      StationaryMFG.Theorems.SimplePower.Banach.LimitPairingSelectorPaperResidue
        (d := d) (γBarReal := StationaryMFG.Hamiltonian.gammaBar hpow.α hpow.β)
        (βBarReal := hpow.β + 1)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        (V := V) (H := H) (DpH := DpH) hpow seq wkBundle
        (StationaryMFG.Theorems.SimplePower.Banach.D_transport_family_paper (d := d)
          wkBundle.mLim wkBundle.uLim wkBundle.DuLim) :=
    { hμ_nonneg := residues.hμ_posOf_transport seq wkBundle }
  -- **Phase 1 of expert post-iter-412 plan**
  -- (`infra-P5-theorem1-remove-pairingResidue-hpq-dependency`, Formalizer
  -- iter 0493).
  --
  -- The `T10PaperResidues.h_weak_*Of` fields are typed via
  -- `hpqBeta_paper hpow` / `hpqGamma_paper hpow` (paper exponents
  -- `(βBar = β+1, βBar' = (β+1)/β)` and
  -- `(γBar = α(β+1)/β, γBar' = γBar/(γBar-1))`). The consumer
  -- `limitPairingSelectorFamily_of_paperHypotheses_at` now expects them
  -- typed via `hpqBeta_paperResidue hpow hExp hβBarPaper hβBar'Paper`
  -- (and the `Gamma` analogue) at the **structure exponents**
  -- `(βBarReal, βBarReal')` / `(γBarReal, γBarReal')`. Under
  -- `hβBar'Paper` / `hγBar'Paper`, the underlying weak-pairing predicate
  -- bodies coincide (`WeakConvPairing_universal` only consumes the
  -- second exponent `q`, which agrees up to the rewrites
  -- `hβBar'_eq` / `hγBar'_eq`). We bridge by transport along the
  -- equalities exactly as before, only the **proof term** in the
  -- `WeakConvPairing_universal` slot changes from
  -- `pairingResidue.hpqβ` / `pairingResidue.hpqγ` (no longer fields)
  -- to `hpqBeta_paperResidue ...` / `hpqGamma_paperResidue ...`.
  have hβBar'_eq : (hpow.β + 1) / hpow.β = βBarReal' := hβBar'Paper.symm
  have hγBar'_eq :
      hpow.α * (hpow.β + 1) / hpow.β /
        (hpow.α * (hpow.β + 1) / hpow.β - 1) = γBarReal' :=
    hγBar'Paper.symm
  -- **HMinty-3 rewire (`infra-P5-T10-v7-HMinty-3-rewire-and-drain`)**.
  -- The three universal weak-pairing certificates were previously
  -- sourced from the `T10PaperResidues.h_weak_{m,u,Du}Of` fields (now
  -- deleted), which themselves were fed by `h_minty_limit_auth` (also
  -- now dropped). They are now sourced directly from the HMinty-2
  -- producer's output `W.h_weak_{m,u,Du}`. The bridging transport
  -- along `hβBar'_eq` / `hγBar'_eq` is retained (the consumer
  -- `limitPairingSelectorFamily_of_paperHypotheses_at` expects the
  -- residue-form variant `hpqBeta_paperResidue` /
  -- `hpqGamma_paperResidue`, whereas `W.h_weak_*` uses
  -- `hpqBeta_paper` / `hpqGamma_paper`).
  let h_weak_m_bridged :
      StationaryMFG.Theorems.SimplePower.Banach.WeakConvPairing_universal
        (d := d)
        (StationaryMFG.Theorems.SimplePower.Banach.hpqBeta_paperResidue
          (d := d) hpow hExp rfl hβBar'Paper)
        (fun k => (seq.sol k).m) wkBundle.mLim := by
    have h := W.h_weak_m
    show ∀ φ : (Fin d → ℝ) → ℝ,
        StationaryMFG.Periodic.MemLpPer (ENNReal.ofReal βBarReal') φ →
        Filter.Tendsto (fun n =>
            ∫ x in StationaryMFG.Periodic.UnitCube d,
              (seq.sol n).m x * φ x)
          Filter.atTop
          (nhds (∫ x in StationaryMFG.Periodic.UnitCube d,
              wkBundle.mLim x * φ x))
    intro φ hφ
    apply h φ
    show StationaryMFG.Periodic.MemLpPer
            (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) φ
    rw [hβBar'_eq]
    exact hφ
  let h_weak_u_bridged :
      StationaryMFG.Theorems.SimplePower.Banach.WeakConvPairing_universal
        (d := d)
        (StationaryMFG.Theorems.SimplePower.Banach.hpqGamma_paperResidue
          (d := d) hpow hExp rfl hγBar'Paper)
        (fun k => (seq.sol k).u) wkBundle.uLim := by
    have h := W.h_weak_u
    show ∀ φ : (Fin d → ℝ) → ℝ,
        StationaryMFG.Periodic.MemLpPer (ENNReal.ofReal γBarReal') φ →
        Filter.Tendsto (fun n =>
            ∫ x in StationaryMFG.Periodic.UnitCube d,
              (seq.sol n).u x * φ x)
          Filter.atTop
          (nhds (∫ x in StationaryMFG.Periodic.UnitCube d,
              wkBundle.uLim x * φ x))
    intro φ hφ
    apply h φ
    show StationaryMFG.Periodic.MemLpPer
            (ENNReal.ofReal
              (hpow.α * (hpow.β + 1) / hpow.β /
                (hpow.α * (hpow.β + 1) / hpow.β - 1))) φ
    rw [hγBar'_eq]
    exact hφ
  let h_weak_Du_bridged :
      ∀ i,
        StationaryMFG.Theorems.SimplePower.Banach.WeakConvPairing_universal
          (d := d)
          (StationaryMFG.Theorems.SimplePower.Banach.hpqGamma_paperResidue
            (d := d) hpow hExp rfl hγBar'Paper)
          (fun k => (seq.sol k).Du i) (wkBundle.DuLim i) := by
    intro i
    have h := W.h_weak_Du i
    show ∀ φ : (Fin d → ℝ) → ℝ,
        StationaryMFG.Periodic.MemLpPer (ENNReal.ofReal γBarReal') φ →
        Filter.Tendsto (fun n =>
            ∫ x in StationaryMFG.Periodic.UnitCube d,
              (seq.sol n).Du i x * φ x)
          Filter.atTop
          (nhds (∫ x in StationaryMFG.Periodic.UnitCube d,
              wkBundle.DuLim i x * φ x))
    intro φ hφ
    apply h φ
    show StationaryMFG.Periodic.MemLpPer
            (ENNReal.ofReal
              (hpow.α * (hpow.β + 1) / hpow.β /
                (hpow.α * (hpow.β + 1) / hpow.β - 1))) φ
    rw [hγBar'_eq]
    exact hφ
  -- Phase G — closed-form Gateaux aggregator.
  --
  -- The universal `gateauxAux` build (Phase 6d-ii-d-3) has been replaced
  -- by three per-family `gateauxAux_<family>` builds via
  -- `gateauxAux_of_paperHypotheses_familyRestrict` at the three narrow
  -- paper-form domains. The per-family `MemLpPer` suppliers are sourced
  -- from the per-family `regSupplier_<family>_paper` records (built below
  -- from `wkBundle.perTestTripleBase` plus `PerTestTripleRegularity`'s
  -- `set_perturbation` / `transport_perturbation` constructors). The
  -- legacy `T10PaperResidues.regBundle` field has been removed.
  have hγ_one_le : (1 : ℝ) ≤ (StationaryMFG.Hamiltonian.gammaBar hpow.α hpow.β) := hExp.γBar_one_lt_real.le
  -- **Phase 6d-ii** (`infra-P5-theorem1-phase-6d-ii-build-pairingFamily-direct`).
  -- The universal `pairingSelector` / `pairing` build has been
  -- replaced by three per-family direct producers
  -- `limitPairingSelectorFamily_{set,signed,transport}_of_paperHypotheses`.
  --
  -- **Phase 6d-ii-d-1** (this step,
  -- `infra-P5-theorem1-phase-6d-ii-d-1-narrow-pairingFamily-set-signed`):
  -- the set / signed per-family `regSupplier_<family>` are now built
  -- at the **narrow paper-form** domains
  -- `D_set_family_paper βBar` / `D_signed_family_paper_nn βBar`
  -- directly from `wkBundle.perTestTripleBase` plus the
  -- `PerTestTripleRegularity.set_perturbation` constructor (the
  -- perturbation `ρ` / `g` carries `MemLpPer βBar` and `IsPeriodic`,
  -- which is exactly what `set_perturbation` consumes — for the
  -- signed family the same constructor applies because the
  -- regularity record reads only `MemLpPer`/`IsPeriodic` of the
  -- additive perturbation, ignoring the nonneg-primal certificate).
  -- The pairing-selector build is then routed through the generic
  -- `limitPairingSelectorFamily_of_paperHypotheses_at` at the narrow
  -- domain, dropping the wider-domain `*_set_of_paperHypotheses` /
  -- `*_signed_of_paperHypotheses` wrappers and the subsequent
  -- `.subdomain` step.
  let regSupplier_set_paper :
      ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄
        ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
        (μ, υ, Dυ) ∈ StationaryMFG.Theorems.SimplePower.Banach.D_set_family_paper
                        (d := d) (ENNReal.ofReal (hpow.β + 1))
                        wkBundle.mLim wkBundle.uLim wkBundle.DuLim →
          StationaryMFG.Theorems.SimplePower.Banach.PerTestTripleRegularity
            (d := d) (ENNReal.ofReal (hpow.β + 1))
            (ENNReal.ofReal (StationaryMFG.Hamiltonian.gammaBar hpow.α hpow.β)) μ υ Dυ := by
    intro μ υ Dυ hMem
    rcases hMem with ⟨ρ, _hρ_nn, hρ_memLp, hρ_periodic, hEq⟩
    rw [Prod.mk.injEq, Prod.mk.injEq] at hEq
    obtain ⟨hμ_eq, hυ_eq, hDυ_eq⟩ := hEq
    subst hμ_eq; subst hυ_eq; subst hDυ_eq
    exact StationaryMFG.Theorems.SimplePower.Banach.PerTestTripleRegularity.set_perturbation
      wkBundle.perTestTripleBase hρ_memLp hρ_periodic
  let regSupplier_signed_paper :
      ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄
        ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
        (μ, υ, Dυ) ∈ StationaryMFG.Theorems.SimplePower.Banach.D_signed_family_paper_nn
                        (d := d) (ENNReal.ofReal (hpow.β + 1))
                        wkBundle.mLim wkBundle.uLim wkBundle.DuLim →
          StationaryMFG.Theorems.SimplePower.Banach.PerTestTripleRegularity
            (d := d) (ENNReal.ofReal (hpow.β + 1))
            (ENNReal.ofReal (StationaryMFG.Hamiltonian.gammaBar hpow.α hpow.β)) μ υ Dυ := by
    intro μ υ Dυ hMem
    rcases hMem with ⟨g, hg_memLp, hg_periodic, _hμ_nn, hEq⟩
    rw [Prod.mk.injEq, Prod.mk.injEq] at hEq
    obtain ⟨hμ_eq, hυ_eq, hDυ_eq⟩ := hEq
    subst hμ_eq; subst hυ_eq; subst hDυ_eq
    exact StationaryMFG.Theorems.SimplePower.Banach.PerTestTripleRegularity.set_perturbation
      wkBundle.perTestTripleBase hg_memLp hg_periodic
  -- **Phase 6d-ii-d-2** (`infra-P5-theorem1-phase-6d-ii-d-2-narrow-transport-regSupplier`):
  -- the transport regSupplier-perTriple is now built at the **narrow
  -- paper-form** domain `D_transport_family_paper`, sourced from
  -- `wkBundle.perTestTripleBase` plus
  -- `PerTestTripleRegularity.transport_perturbation`. Triples in this narrow
  -- domain have shape `(mLim, uLim + ψ, DuLim + ∂ψ)` for some
  -- `ψ : SmoothPeriodic d`; we destructure the membership and apply
  -- `transport_perturbation` at `σ = 1`. The function-shape mismatch
  -- (`1 * ψ x` vs `ψ x`) is closed via
  -- `PerTestTripleRegularity.congr_funs`.
  let regSupplier_transport_perTriple :
      ∀ ⦃μ υ : (Fin d → ℝ) → ℝ⦄
        ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
        (μ, υ, Dυ) ∈ StationaryMFG.Theorems.SimplePower.Banach.D_transport_family_paper
                        (d := d) wkBundle.mLim wkBundle.uLim wkBundle.DuLim →
          StationaryMFG.Theorems.SimplePower.Banach.PerTestTripleRegularity
            (d := d) (ENNReal.ofReal (hpow.β + 1))
            (ENNReal.ofReal (StationaryMFG.Hamiltonian.gammaBar hpow.α hpow.β)) μ υ Dυ := by
    intro μ υ Dυ hMem
    rcases hMem with ⟨ψ, hEq⟩
    rw [Prod.mk.injEq, Prod.mk.injEq] at hEq
    obtain ⟨hμ_eq, hυ_eq, hDυ_eq⟩ := hEq
    subst hμ_eq; subst hυ_eq; subst hDυ_eq
    -- `transport_perturbation base hγ_one_le 1 ψ` produces the
    -- regularity record at `(mLim, uLim + 1·ψ, DuLim + 1·∂ψ)`.
    -- Bridge to the `1·ψ x = ψ x` form via `congr_funs`.
    have hγ_one_le_ennreal : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (StationaryMFG.Hamiltonian.gammaBar hpow.α hpow.β) := by
      have h1 : (1 : ℝ) ≤ (StationaryMFG.Hamiltonian.gammaBar hpow.α hpow.β) := hExp.γBar_one_lt_real.le
      have hpos : (0 : ℝ) ≤ 1 := zero_le_one
      have h := ENNReal.ofReal_le_ofReal h1
      simpa [ENNReal.ofReal_one] using h
    have hbase :=
      StationaryMFG.Theorems.SimplePower.Banach.PerTestTripleRegularity.transport_perturbation
        (d := d) wkBundle.perTestTripleBase
        hγ_one_le_ennreal (1 : ℝ) ψ
    exact StationaryMFG.Theorems.SimplePower.Banach.PerTestTripleRegularity.congr_funs
      hbase
      (fun _ => rfl)
      (fun x => by show wkBundle.uLim x + 1 * (ψ : (Fin d → ℝ) → ℝ) x =
                          wkBundle.uLim x + (ψ : (Fin d → ℝ) → ℝ) x; ring)
      (fun i x => by
        show wkBundle.DuLim i x + 1 *
              ((StationaryMFG.Periodic.SmoothPeriodic.partialDeriv i ψ
                  : StationaryMFG.Periodic.SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x =
            wkBundle.DuLim i x +
              ((StationaryMFG.Periodic.SmoothPeriodic.partialDeriv i ψ
                  : StationaryMFG.Periodic.SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x
        ring)
  -- **Phase 6d-ii-d-3**: build three per-family `gateauxAux_<family>`
  -- via the family-restricted aggregator. The per-family `MemLpPer`
  -- suppliers project the corresponding fields of the per-family
  -- `regSupplier_<family>_paper` records (themselves built from
  -- `wkBundle.perTestTripleBase` plus `set_perturbation` /
  -- `transport_perturbation` per 6d-ii-d-1/2).
  -- **HMinty-3 rewire** (`infra-P5-T10-v7-HMinty-3-rewire-and-drain`).
  -- After the rewire `seq := W.seq`, the apriori-sum bound expects the
  -- subsequenced sequence: `(seq.sol k).{m,u,Du} = (seq0.sol (W.idx
  -- k)).{m,u,Du}` (by `W.seq_{m,u,Du}_eq k`). We reindex
  -- `aprioriResidue.uniformConstant_bound` through `W.idx`. The
  -- pointwise component identities are supplied by the structure
  -- fields `seq_{m,u,Du}_eq`, each `rfl` by the producer's definition
  -- of `seq := D.seqSub = seq0.subseq D.idx _`. Note that
  -- `seq0 = regularizedSequenceData_of_aprioriResidue aprioriResidue _
  -- _`, so `(seq0.sol n).{m,u,Du} = (aprioriResidue.sol n).{m,u,Du}`
  -- holds by `rfl` (the producer's `sol := R.sol` field).
  have hCapr_reindexed : ∀ k : ℕ,
      (∫ x in StationaryMFG.Periodic.UnitCube d,
          |(seq.sol k).m x| ^ (hpow.β + 1)) +
        (∫ x in StationaryMFG.Periodic.UnitCube d,
          |(seq.sol k).u x| ^
            (StationaryMFG.Hamiltonian.gammaBar hpow.α hpow.β)) +
        (∑ i, ∫ x in StationaryMFG.Periodic.UnitCube d,
          |(seq.sol k).Du i x| ^
            (StationaryMFG.Hamiltonian.gammaBar hpow.α hpow.β))
          ≤ aprioriResidue.uniformConstant := by
    intro k
    have h := aprioriResidue.uniformConstant_bound (W.idx k)
    -- Pointwise component equations from the `ExtractedWeakPairingData`
    -- structure.
    have hm : (seq.sol k).m = (seq0.sol (W.idx k)).m := W.seq_m_eq k
    have hu : (seq.sol k).u = (seq0.sol (W.idx k)).u := W.seq_u_eq k
    have hDu : ∀ i, (seq.sol k).Du i = (seq0.sol (W.idx k)).Du i :=
      fun i => W.seq_Du_eq k i
    -- `seq0.sol = aprioriResidue.sol` by the def-eq inside
    -- `regularizedSequenceData_of_aprioriResidue` (the `sol := R.sol`
    -- field). So `(seq0.sol n).{m,u,Du i} = (aprioriResidue.sol n).{m,u,Du i}`.
    simp only [hm, hu, hDu] at *
    exact h
  let gateauxAux_set :=
    StationaryMFG.Theorems.SimplePower.Banach.gateauxAux_of_paperHypotheses_familyRestrict
      seq hγ_one_le
      aprioriResidue.uniformConstant
      aprioriResidue.uniformConstant_nn
      hCapr_reindexed
      (StationaryMFG.Theorems.SimplePower.Banach.D_set_family_paper (d := d)
        (ENNReal.ofReal (hpow.β + 1))
        wkBundle.mLim wkBundle.uLim wkBundle.DuLim)
      (fun _μ _υ _Dυ hMem => (regSupplier_set_paper hMem).hυ_memLp)
      (fun _μ _υ _Dυ hMem i => (regSupplier_set_paper hMem).hDυ_memLp i)
  let gateauxAux_signed :=
    StationaryMFG.Theorems.SimplePower.Banach.gateauxAux_of_paperHypotheses_familyRestrict
      seq hγ_one_le
      aprioriResidue.uniformConstant
      aprioriResidue.uniformConstant_nn
      hCapr_reindexed
      (StationaryMFG.Theorems.SimplePower.Banach.D_signed_family_paper_nn (d := d)
        (ENNReal.ofReal (hpow.β + 1))
        wkBundle.mLim wkBundle.uLim wkBundle.DuLim)
      (fun _μ _υ _Dυ hMem => (regSupplier_signed_paper hMem).hυ_memLp)
      (fun _μ _υ _Dυ hMem i => (regSupplier_signed_paper hMem).hDυ_memLp i)
  let gateauxAux_transport :=
    StationaryMFG.Theorems.SimplePower.Banach.gateauxAux_of_paperHypotheses_familyRestrict
      seq hγ_one_le
      aprioriResidue.uniformConstant
      aprioriResidue.uniformConstant_nn
      hCapr_reindexed
      (StationaryMFG.Theorems.SimplePower.Banach.D_transport_family_paper (d := d)
        wkBundle.mLim wkBundle.uLim wkBundle.DuLim)
      (fun _μ _υ _Dυ hMem => (regSupplier_transport_perTriple hMem).hυ_memLp)
      (fun _μ _υ _Dυ hMem i => (regSupplier_transport_perTriple hMem).hDυ_memLp i)
  let pairingSelectorFamily_set :=
    -- Phase 6d-ii-d-1: build the set selector directly at the narrow
    -- paper-form domain via the generic `*_at` producer (bypassing
    -- the wider-domain `_set_of_paperHypotheses` wrapper).
    -- iter `infra-P5-T10-v7-phase4-hmu-posAuth-drain`: thread the
    -- Hat0 riders `(hHat0, hAgree)` for the migrated `_nonneg` HJB
    -- discharge.
    StationaryMFG.Theorems.SimplePower.Banach.limitPairingSelectorFamily_of_paperHypotheses_at
      hmon hpow hV hExp hHat0 hAgree seq wkBundle
      (StationaryMFG.Theorems.SimplePower.Banach.D_set_family_paper (d := d)
        (ENNReal.ofReal (hpow.β + 1))
        wkBundle.mLim wkBundle.uLim wkBundle.DuLim)
      regSupplier_set_paper gateauxAux_set
      rfl rfl hβBar'Paper hγBar'Paper pairingResidue_set
      h_weak_m_bridged
      h_weak_u_bridged
      h_weak_Du_bridged
  let pairingSelectorFamily_signed :=
    -- Phase 6d-ii-d-1: build the signed selector directly at the
    -- narrow paper-form domain.
    StationaryMFG.Theorems.SimplePower.Banach.limitPairingSelectorFamily_of_paperHypotheses_at
      hmon hpow hV hExp hHat0 hAgree seq wkBundle
      (StationaryMFG.Theorems.SimplePower.Banach.D_signed_family_paper_nn (d := d)
        (ENNReal.ofReal (hpow.β + 1))
        wkBundle.mLim wkBundle.uLim wkBundle.DuLim)
      regSupplier_signed_paper gateauxAux_signed
      rfl rfl hβBar'Paper hγBar'Paper pairingResidue_signed
      h_weak_m_bridged
      h_weak_u_bridged
      h_weak_Du_bridged
  let pairingSelectorFamily_transport :=
    -- Phase 6d-ii-d-2: build the transport selector directly at the
    -- narrow paper-form domain `D_transport_family_paper` via the
    -- generic `*_at` producer (bypassing the wider-domain
    -- `_transport_of_paperHypotheses` wrapper).
    StationaryMFG.Theorems.SimplePower.Banach.limitPairingSelectorFamily_of_paperHypotheses_at
      hmon hpow hV hExp hHat0 hAgree seq wkBundle
      (StationaryMFG.Theorems.SimplePower.Banach.D_transport_family_paper (d := d)
        wkBundle.mLim wkBundle.uLim wkBundle.DuLim)
      regSupplier_transport_perTriple gateauxAux_transport
      rfl rfl hβBar'Paper hγBar'Paper pairingResidue_transport
      h_weak_m_bridged
      h_weak_u_bridged
      h_weak_Du_bridged
  -- Step 6: per-family pairing inputs (Phase 6d-ii — direct from the
  -- per-family selectors, no universal `pairing` build).
  --
  -- **Phase 6d-ii-d-1**: the set / signed pairing inputs are now
  -- built directly at the narrow paper-form domains, dropping the
  -- previous `pairing_<family>_wide → pairing_<family>` `.subdomain`
  -- bridge. The transport pairing remains at `D_transport_family`
  -- (Step 2 of 6d-ii-d).
  let pairing_set :=
    StationaryMFG.Theorems.SimplePower.Banach.limitPairingInputsFamily_of_regularizedSequence
      hmon hpow hV hExp seq wkBundle
      (StationaryMFG.Theorems.SimplePower.Banach.D_set_family_paper (d := d)
        (ENNReal.ofReal (hpow.β + 1))
        wkBundle.mLim wkBundle.uLim wkBundle.DuLim)
      pairingSelectorFamily_set
  let pairing_signed :=
    StationaryMFG.Theorems.SimplePower.Banach.limitPairingInputsFamily_of_regularizedSequence
      hmon hpow hV hExp seq wkBundle
      (StationaryMFG.Theorems.SimplePower.Banach.D_signed_family_paper_nn (d := d)
        (ENNReal.ofReal (hpow.β + 1))
        wkBundle.mLim wkBundle.uLim wkBundle.DuLim)
      pairingSelectorFamily_signed
  let pairing_transport :=
    StationaryMFG.Theorems.SimplePower.Banach.limitPairingInputsFamily_of_regularizedSequence
      hmon hpow hV hExp seq wkBundle
      (StationaryMFG.Theorems.SimplePower.Banach.D_transport_family_paper (d := d)
        wkBundle.mLim wkBundle.uLim wkBundle.DuLim)
      pairingSelectorFamily_transport
  -- Step 7: final-integrability bundle. Uses
  -- `wkBundle.{mLim,uLim,DuLim}` (definitionally the inline-constructed
  -- `weakLimitExtractionAE_of_uniform_apriori` selector's projections;
  -- the surface `T10PaperResidues.weakSelector` field was dropped in
  -- `infra-P5-T10-drop-weakSelector`).
  --
  -- The legacy `residues.finIntResidue` field has been removed
  -- (Phase H5d): `FinalIntegrabilityPaperResidueLp` is vacuous, so we
  -- supply the `⟨trivial⟩` constructor inline, then discharge the
  -- three `Integrable` claims via `finalIntegrabilityPaperResidue_of_lpResidue`,
  -- and wrap through `finalIntegrabilityBundle_of_paperHypotheses`.
  let finIntLpRes :
      StationaryMFG.Theorems.SimplePower.Banach.FinalIntegrabilityPaperResidueLp
        (d := d) (ENNReal.ofReal βBarReal') (StationaryMFG.Hamiltonian.gammaBar hpow.α hpow.β) V H DpH
        wkBundle.DuLim wkBundle.mLim wkBundle.uLim :=
    ⟨trivial⟩
  let finIntPaper :
      StationaryMFG.Theorems.SimplePower.Banach.FinalIntegrabilityPaperResidue
        (d := d) V H DpH wkBundle.DuLim wkBundle.mLim wkBundle.uLim :=
    StationaryMFG.Theorems.SimplePower.Banach.finalIntegrabilityPaperResidue_of_lpResidue
      (γBarReal := StationaryMFG.Hamiltonian.gammaBar hpow.α hpow.β)
      (βBarReal := hpow.β + 1)
      (βBarReal' := βBarReal') (γBarReal' := γBarReal')
      hpow hHat0 hFin hAgree hV hExp rfl rfl hβBar'Paper
      wkBundle finIntLpRes
  let finInt :
      StationaryMFG.Theorems.SimplePower.Banach.FinalIntegrabilityBundle
        (d := d) V H DpH wkBundle.DuLim wkBundle.mLim wkBundle.uLim :=
    StationaryMFG.Theorems.SimplePower.Banach.finalIntegrabilityBundle_of_paperHypotheses
      hmon hpow hV hExp seq wkBundle finIntPaper
  -- Step 8: family-native assembly of `H4SimplePowerInputs`.
  -- Per Phase F0 (THEOREM1_CLOSURE_PLAN v4 §10), the assembly invokes
  -- the three F0 family producers
  -- `strongVI_{set,signed,transport}_at_limit_of_paperHypotheses`
  -- directly, bypassing the `LimitSolutionData` intermediate. The
  -- regularised-VI input is no longer threaded through the chain
  -- (Phase 5b): `LimitPairingInputs.data` returns the leaner
  -- `LimitPassageInputData_noVI` shape. The legacy
  -- `limitSolutionData_of_regularizedSequence{,_strictPos}` producers
  -- (unused by Theorem 1) keep an explicit `hVI_eps_universal`
  -- parameter for future Theorem 2 / congestion code reuse.
  --
  -- **Phase 4d** (`infra-P4-drop-mintyResidue-universal-chain`): the
  -- three per-family `MintyClosureOn` certificates are now built
  -- directly from the per-family residues
  -- `residues.mintyData{Set,Signed,Transport}Of wkBundle` via
  -- `mintyClosure_familyNative_{set,signed,transport}_of_paperHypotheses`,
  -- bypassing the universal `mintyClosure`/`hDuniv` chain (which has
  -- been dropped). The Gateaux exponent is `(StationaryMFG.Hamiltonian.gammaBar hpow.α hpow.β)`, with the
  -- `1 < γBar` lower bound supplied by `hExp.γBar_one_lt_real`.
  --
  -- **Phase 6d-ii-c-2d**
  -- (`infra-P5-theorem1-phase-6d-ii-c-2d-chain-migrate-to-narrow`):
  -- the F0 chain consumer now reads the set / signed minty-closures at
  -- the **narrow paper-form** domains. The signed branch builds the
  -- wider version and then narrows via `mintyClosureOn_signed_nn_of_wider`
  -- followed by `mintyClosureOn_signed_paper_nn_of_wider`.
  --
  -- **iter `infra-P5-mintyData-discharge-set-family-wire-final`** (this
  -- step): the **set** branch is now built directly at the narrow
  -- paper-form domain `D_set_family_paper (ENNReal.ofReal (hpow.β + 1))`
  -- via `mintyClosure_familyNative_set_of_paperHypotheses_narrow`,
  -- consuming the per-pair `HemicontSegmentData` aggregator produced by
  -- `mintyDataSetNarrow_of_paperHypotheses` from
  -- `residues.mintyResSetOf wkBundle`. The legacy wide build +
  -- `mintyClosureOn_set_paper_of_wider` narrowing has been dropped.
  -- **iter `infra-P5-T10-v8-K0-set-mintyResSetOf-retype`**: the set
  -- branch now consumes the **K0** chain. The producer is
  -- `mintyDataSetNarrowK0_of_paperHypotheses` (returning a
  -- `HemicontSegmentDataK0` aggregator), and the consumer is the K0
  -- closure builder `mintyClosure_familyNative_set_of_paperHypotheses_narrowK0`.
  -- The K0 path bypasses the strict-positivity hypothesis `hPosSeg` —
  -- segment a.e.-nonneg comes from `K0_Aepsi_segment_pos_nn` inside
  -- the K0 composer. Closed-cone regularity `RegularityHK0` is
  -- produced in-body from `(hpow, hHextCont)` via
  -- `regularityHK0_of_powerGrowth_and_HextJointCont`.
  have hRegK0 :
      StationaryMFG.Theorems.SimplePower.RegularityHK0 (d := d) H DpH :=
    StationaryMFG.Theorems.SimplePower.regularityHK0_of_powerGrowth_and_HextJointCont
      hpow hHextCont
  let mintyClosureOn_set :
      StationaryMFG.Theorems.SimplePower.Banach.MintyClosureOn (d := d)
        V H DpH wkBundle.mLim wkBundle.uLim wkBundle.DuLim
        (StationaryMFG.Theorems.SimplePower.Banach.D_set_family_paper
            (d := d) (ENNReal.ofReal (hpow.β + 1))
            wkBundle.mLim wkBundle.uLim wkBundle.DuLim) :=
    StationaryMFG.Theorems.SimplePower.Banach.mintyClosure_familyNative_set_of_paperHypotheses_narrowK0
      (γBarReal := StationaryMFG.Hamiltonian.gammaBar hpow.α hpow.β)
      (βBarReal := hpow.β + 1)
      (βBarReal' := βBarReal')
      hRegK0 hpow hV
      (ENNReal.ofReal (hpow.β + 1))
      wkBundle.mLim wkBundle.uLim wkBundle.DuLim
      (StationaryMFG.Hamiltonian.gammaBar hpow.α hpow.β)
      -- iter `infra-P7-sigfix-T1-drain-B-K0-consumer-rewire`: exponent
      -- alignment witness. `βBar := ENNReal.ofReal (hpow.β + 1)` and
      -- `βBarReal := hpow.β + 1`, so equality is `rfl`.
      (hβBar_eq := rfl)
      (mintyDataSetNarrowK0Min_of_paperHypotheses
        (γBarReal := StationaryMFG.Hamiltonian.gammaBar hpow.α hpow.β)
        (βBarReal := hpow.β + 1)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        (γBar := StationaryMFG.Hamiltonian.gammaBar hpow.α hpow.β)
        hpow wkBundle (residues.mintyResSetOf wkBundle))
  -- **iter `infra-P5-mintyData-discharge-signed-family`**: the
  -- **signed** branch is now built directly at the narrow paper-form
  -- domain `D_signed_family_paper_nn (ENNReal.ofReal (hpow.β + 1))`.
  --
  -- **iter `infra-P5-T10-v8-K0-signed-mintyResSignedOf-retype`** (signed
  -- mirror of iter-0762's set retype): the signed branch now consumes
  -- the **K0** chain. The producer is
  -- `mintyDataSignedNarrowK0_of_paperHypotheses` (returning a
  -- `HemicontSegmentDataK0` aggregator), and the consumer is the K0
  -- closure builder
  -- `mintyClosure_familyNative_signed_of_paperHypotheses_narrowK0`.
  -- The K0 path bypasses the strict-positivity hypothesis `hPosSeg` —
  -- segment a.e.-nonneg comes from `K0_Aepsi_segment_pos_nn` inside the
  -- K0 composer. Closed-cone regularity `RegularityHK0` is the same
  -- `hRegK0` built earlier for the set branch.
  let mintyClosureOn_signed :
      StationaryMFG.Theorems.SimplePower.Banach.MintyClosureOn (d := d)
        V H DpH wkBundle.mLim wkBundle.uLim wkBundle.DuLim
        (StationaryMFG.Theorems.SimplePower.Banach.D_signed_family_paper_nn
            (d := d) (ENNReal.ofReal (hpow.β + 1))
            wkBundle.mLim wkBundle.uLim wkBundle.DuLim) :=
    StationaryMFG.Theorems.SimplePower.Banach.mintyClosure_familyNative_signed_of_paperHypotheses_narrowK0
      (γBarReal := StationaryMFG.Hamiltonian.gammaBar hpow.α hpow.β)
      (βBarReal := hpow.β + 1)
      (βBarReal' := βBarReal')
      hRegK0 hpow hV
      (ENNReal.ofReal (hpow.β + 1))
      wkBundle.mLim wkBundle.uLim wkBundle.DuLim
      wkBundle.hmLim_nonneg
      (StationaryMFG.Hamiltonian.gammaBar hpow.α hpow.β)
      -- iter `infra-P7-sigfix-T1-drain-B-K0-consumer-rewire`: exponent
      -- alignment witness `βBar = ENNReal.ofReal βBarReal` (here both
      -- equal `ENNReal.ofReal (hpow.β + 1)`).
      (hβBar_eq := rfl)
      (mintyDataSignedNarrowK0Min_of_paperHypotheses
        (γBarReal := StationaryMFG.Hamiltonian.gammaBar hpow.α hpow.β)
        (βBarReal := hpow.β + 1)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        (γBar := StationaryMFG.Hamiltonian.gammaBar hpow.α hpow.β)
        hpow wkBundle (residues.mintyResSignedOf wkBundle))
  -- **iter `infra-P5-mintyData-transport-rewire-T10`**: the **transport**
  -- branch is now built directly at the narrow paper-form domain
  -- `D_transport_family_paper`.
  --
  -- **iter `infra-P5-T10-v8-K0-transport-mintyResTransportOf-retype`**
  -- (transport mirror of iter-0762's set retype and iter-0771's signed
  -- retype): the transport branch now consumes the **K0** chain. The
  -- producer is `mintyDataTransportNarrowK0_of_paperHypotheses` (returning
  -- a `HemicontSegmentDataK0` aggregator), and the consumer is the K0
  -- closure builder `mintyClosure_familyNative_transport_of_paperHypotheses_narrowK0`.
  -- The K0 path bypasses the strict-positivity hypothesis `hPosSeg` —
  -- segment a.e.-nonneg comes from `K0_Aepsi_segment_pos_nn` inside
  -- the K0 composer. Closed-cone regularity `RegularityHK0` is the same
  -- `hRegK0` built earlier for the set/signed branches.
  let mintyClosureOn_transport :
      StationaryMFG.Theorems.SimplePower.Banach.MintyClosureOn (d := d)
        V H DpH wkBundle.mLim wkBundle.uLim wkBundle.DuLim
        (StationaryMFG.Theorems.SimplePower.Banach.D_transport_family_paper
            (d := d) wkBundle.mLim wkBundle.uLim wkBundle.DuLim) :=
    StationaryMFG.Theorems.SimplePower.Banach.mintyClosure_familyNative_transport_of_paperHypotheses_narrowK0
      (γBarReal := StationaryMFG.Hamiltonian.gammaBar hpow.α hpow.β)
      (βBarReal := hpow.β + 1)
      (βBarReal' := βBarReal')
      hRegK0 hpow hV
      wkBundle.mLim wkBundle.uLim wkBundle.DuLim
      (StationaryMFG.Hamiltonian.gammaBar hpow.α hpow.β)
      -- iter `infra-P7-sigfix-T1-drain-B-K0-consumer-rewire`: transport
      -- K0 consumer no longer takes any test-direction cert oracle —
      -- the transport family carries its own smooth-periodic regularity
      -- on the difference triple via `MemSobolevPer.of_smoothPeriodic`.
      (mintyDataTransportNarrowK0Min_of_paperHypotheses
        (γBarReal := StationaryMFG.Hamiltonian.gammaBar hpow.α hpow.β)
        (βBarReal := hpow.β + 1)
        (βBarReal' := βBarReal') (γBarReal' := γBarReal')
        (γBar := StationaryMFG.Hamiltonian.gammaBar hpow.α hpow.β)
        hpow wkBundle (residues.mintyResTransportOf wkBundle))
  -- **Phase 6d-ii-d-2** (`infra-P5-theorem1-phase-6d-ii-d-2-narrow-transport-regSupplier`):
  -- the transport regularity supplier consumed by the F0 chain
  -- consumer is now built at the narrow paper-form domain
  -- `D_transport_family_paper`, sourced from
  -- `wkBundle.perTestTripleBase` plus
  -- `PerTestTripleRegularity.transport_perturbation`.
  let regSupplier_transport :
      ∀ ⦃μ : (Fin d → ℝ) → ℝ⦄
        ⦃υ : (Fin d → ℝ) → ℝ⦄
        ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
          (μ, υ, Dυ) ∈ StationaryMFG.Theorems.SimplePower.Banach.D_transport_family_paper
                          (d := d) wkBundle.mLim wkBundle.uLim wkBundle.DuLim →
            Periodic.MemSobolevPer (d := d) (ENNReal.ofReal (StationaryMFG.Hamiltonian.gammaBar hpow.α hpow.β)) υ ∧
              ∀ i, Periodic.MemLpPer (d := d)
                      (ENNReal.ofReal (StationaryMFG.Hamiltonian.gammaBar hpow.α hpow.β)) (Dυ i) := by
    intro μ υ Dυ hMem
    -- Discharge via the per-triple regularity.
    have R := regSupplier_transport_perTriple hMem
    exact ⟨⟨R.hυ_memLp, ⟨Dυ, R.hWeakDeriv⟩⟩, R.hDυ_memLp⟩
  -- **Phase 5 step3d** weak-derivative-tie supplier on the transport
  -- narrow domain. Source: `regSupplier_transport_perTriple` carries
  -- `hWeakDeriv` per triple.
  let hWeakSupplier_transport :
      ∀ ⦃μ : (Fin d → ℝ) → ℝ⦄
        ⦃υ : (Fin d → ℝ) → ℝ⦄
        ⦃Dυ : Fin d → (Fin d → ℝ) → ℝ⦄,
          (μ, υ, Dυ) ∈ StationaryMFG.Theorems.SimplePower.Banach.D_transport_family_paper
                          (d := d) wkBundle.mLim wkBundle.uLim wkBundle.DuLim →
            ∀ i, Periodic.HasWeakDerivPer (d := d) i υ (Dυ i) := by
    intro μ υ Dυ hMem
    exact (regSupplier_transport_perTriple hMem).hWeakDeriv
  -- **Phase 6d-ii**: the per-family `LimitPairingInputsFamily`
  -- records `pairing_{set,signed,transport}` are now built directly
  -- (via `limitPairingInputsFamily_of_regularizedSequence` from each
  -- per-family direct selector), bypassing the universal
  -- `pairing : LimitPairingInputs` and `pairing.toFamily` chain.
  exact
    ⟨StationaryMFG.Theorems.SimplePower.Banach.H4SimplePowerInputs_of_paperHypotheses_familyNative
        hmon hpow hV hExp seq wkBundle
        pairing_set pairing_signed pairing_transport
        mintyClosureOn_set mintyClosureOn_signed mintyClosureOn_transport
        regSupplier_transport hWeakSupplier_transport finInt⟩

/-- **Theorem 1 — concrete aggregator** (paper line 314,
`thm:main-simple.power.growth`).

Under the four paper hypotheses
* `hmon : HypothesisMonotone H DpH` (Assumption `onH.monotone`),
* `hpow : HypothesisPowerGrowth H DpH` (Assumption `onH.powergrowth`),
* `hV : V ∈ L^{β̄'}_per`,
* `hHat0 : HypothesisHat0 H` (Assumption `(a:Hat0)`),

plus the authorised paper-residue bundle `T10PaperResidues`
(Option (b); CONVENTIONS §1b), there exists a strong solution
`(m, u) ∈ L^{β̄}_per × W^{1,γ̄}_per` to Problem `prob.smfg` in the
sense of Definition `def:strong`.

**Phase B (THEOREM1_CLOSURE_PLAN §6).** The exponents at the public
surface are pinned to the paper-canonical formulas
`β̄ = β + 1`, `γ̄ = α(β+1)/β`, `β̄' = (β+1)/β`,
`γ̄' = γ̄ / (γ̄ - 1)` (`Hamiltonian.betaBar`, `Hamiltonian.gammaBar`,
`Hamiltonian.betaBar'`, `Hamiltonian.gammaBar'`), at the values
of `(α, β)` carried by `hpow`. Consequently the bundle
`SimplePowerExponentFacts …` is no longer a public-surface
parameter — it is derived in-body from `hpow` via
`SimplePowerExponentFacts.ofPowerGrowth`.

The Phase C0 hypothesis `hHat0` reflects the paper preamble of
`def:strong` (paper line 261), which lists `(a:Hat0)` among the
regularity assumptions on `H`: in the set `{m=0}` the expression
`H(x, Du, m)` is to be evaluated via the canonical extension
`Hamiltonian.Hext`. The Lean predicate `IsStrongSolution_HJB`
evaluates raw `H x p (m x)`; on `{m > 0}` this coincides with `Hext`
(see `IsStrongSolution_HJB.Hext_residual_eq_on_pos`), and the
`{m = 0}` reading is captured by `hHat0` itself. See
`docs/THEOREM1_CLOSURE_PLAN.md` Phase C0
(`infra-P5-theorem1-phase-C0-Hamiltonian-extension-Hext`).

The proof is a one-line aggregator: extract a witness `T` via
`simplePowerThinChain_of_paperHypotheses` (now sorry-free; the linear
pipeline of eight closed-form aggregators consumes the residue bundle)
and assemble the headline existential from `T`'s fields, invoking
`main_conclude_isStrongSolution` for the strong-solution conjunct.

The headline existential exposes the six conjuncts of paper
`def:strong`: HJB+transport (`IsStrongSolution`), `m ∈ L^{β̄}_per`,
`u ∈ W^{1,γ̄}_per`, `m ≥ 0` a.e. on the torus, and **(G8a)** the
weak-gradient tie `∀ i, HasWeakDerivPer i u (Du i)` together with
`∀ i, MemLpPer (ofReal γ̄) (Du i)` — the latter two surfaced from
`T.{hDu_weakDeriv, hDu_memLp_γ}` (iter
`infra-P8-g8a-T1-du-tie-conclusion`). -/
theorem thm_main_simplePowerGrowth_concrete
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hmon : HypothesisMonotone H DpH)
    (hpow : HypothesisPowerGrowth H DpH)
    (hV : Periodic.MemLpPer
            (ENNReal.ofReal (Hamiltonian.betaBar' hpow.β)) V)
    (hHat0 : StationaryMFG.Hamiltonian.HypothesisHat0 (d := d) H)
    (hFin : StationaryMFG.Hamiltonian.Hext_finite_at_zero (d := d) H)
    (hAgree : StationaryMFG.Hamiltonian.H_zero_eq_Hext (d := d) H)
    -- **iter `infra-P5-T10-v8-K0-set-mintyResSetOf-retype`**: joint-cont
    -- rider for `Hext` on the closed half-plane. Threaded to
    -- `simplePowerThinChain_of_paperHypotheses` for K0 set-family
    -- Minty closure. NOT a B-class authorisation (analytic rider).
    (hHextCont : StationaryMFG.Hamiltonian.HypothesisHextJointCont (d := d) H)
    -- **iter `infra-P5-T10-v8-K0-set-segInputs-relocate-testDir-certs`**
    -- (historical): test-direction regularity producer was previously
    -- threaded as a universal oracle `testDirCertsOf`. **iter
    -- `infra-P7-sigfix-T1-drain-C-public-headlines` (Phase 1D)**: the
    -- oracle is dropped here. See `simplePowerThinChain_of_paperHypotheses`
    -- for the full historical comment.
    (residues :
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
        V H DpH hpow) :
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
  -- Phase B (THEOREM1_CLOSURE_PLAN §6): introduce the `Fact` instances
  -- once-and-for-all from `hpow.hα, hpow.hβ`, and derive the exponent
  -- bundle `hExp := SimplePowerExponentFacts.ofPowerGrowth hpow`.
  haveI : Fact (1 ≤ ENNReal.ofReal (Hamiltonian.betaBar hpow.β)) :=
    Hamiltonian.fact_one_le_ofReal_betaBar hpow.hβ
  haveI : Fact (1 ≤ ENNReal.ofReal (Hamiltonian.gammaBar hpow.α hpow.β)) :=
    Hamiltonian.fact_one_le_ofReal_gammaBar hpow.hα hpow.hβ
  -- Note: `paperGammaBarReal hpow.α hpow.β = gammaBar hpow.α hpow.β`,
  -- `paperBetaBar hpow.β = ENNReal.ofReal (betaBar hpow.β)`, etc., by
  -- definitional unfolding (see `Hamiltonian/Basic.lean` and
  -- `SimplePower/Banach/ExponentFacts.lean`). We rely on this defeq.
  let hExp :
      SimplePowerExponentFacts
        (Hamiltonian.gammaBar hpow.α hpow.β)
        (ENNReal.ofReal (Hamiltonian.betaBar hpow.β))
        (ENNReal.ofReal (Hamiltonian.gammaBar hpow.α hpow.β))
        (ENNReal.ofReal (Hamiltonian.betaBar' hpow.β)) :=
    SimplePowerExponentFacts.ofPowerGrowth hpow
  -- Extract a witness `T : H4SimplePowerInputs ...` of the upstream
  -- chain via the bundle-form named obligation.
  obtain ⟨T⟩ :=
    simplePowerThinChain_of_paperHypotheses (d := d)
      (γBar := Hamiltonian.gammaBar hpow.α hpow.β)
      (betaBar := ENNReal.ofReal (Hamiltonian.betaBar hpow.β))
      (gammaBar := ENNReal.ofReal (Hamiltonian.gammaBar hpow.α hpow.β))
      (betaBar' := ENNReal.ofReal (Hamiltonian.betaBar' hpow.β))
      (γBarReal := Hamiltonian.gammaBar hpow.α hpow.β)
      (βBarReal := Hamiltonian.betaBar hpow.β)
      (βBarReal' := Hamiltonian.betaBar' hpow.β)
      (γBarReal' := Hamiltonian.gammaBar' hpow.α hpow.β)
      V H DpH hmon hpow hV hHat0 hFin hAgree hHextCont hExp
      residues
      rfl rfl rfl rfl rfl rfl rfl rfl
  refine ⟨T.m, T.u, T.Du, ?_, T.mLp, T.uSob, T.m_nonneg,
    T.hDu_weakDeriv, T.hDu_memLp_γ⟩
  exact (main_conclude_isStrongSolution
            (γBar := Hamiltonian.gammaBar hpow.α hpow.β)
            V H DpH
            T.hRes T.hResM T.hFluxInt
            T.hVI_set T.hVI_signed T.hVI_transport).flux_mDpH_to_JsimpleExt

/-! ### Sanity-check examples

The trivial Hamiltonian `H = 0`, `D_pH = 0`, `V = 0` together with the
canonical pair `m = 1`, `u = 0`, `Du = 0` realises every field of
`H4SimplePowerThinInputs`: each integrand vanishes, so the
integrability hypotheses hold, and the function-form strong VI is
identically `0 ≤ 0`. The first example below witnesses
`Nonempty (H4SimplePowerThinInputs …)` directly on the trivial data
(making the bundle visibly non-vacuous). The second example exercises
`thm_main_simplePowerGrowth_concrete` end-to-end on a hypothetical
Hamiltonian satisfying the paper hypotheses. -/

/-- The trivial-data Hamiltonian admits a `H4SimplePowerThinInputs`
witness with `m = 1`, `u = 0`, `Du = 0`. Provided as a sanity check
that the thin-input bundle is non-vacuous on the trivial data. -/
def trivialThinInputs (d : ℕ) :
    H4SimplePowerThinInputs (d := d) (γBar := (2 : ℝ))
      (V := fun _ : Fin d → ℝ => (0 : ℝ))
      (H := fun _ _ _ => (0 : ℝ))
      (DpH := fun _ _ _ => (0 : Fin d → ℝ))
      (betaBar := (2 : ℝ≥0∞)) (gammaBar := (2 : ℝ≥0∞)) where
  m := fun _ => (1 : ℝ)
  u := fun _ => (0 : ℝ)
  Du := fun _ _ => (0 : ℝ)
  mLp := by
    have : IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
      ⟨by
        rw [Measure.restrict_apply MeasurableSet.univ]
        simp⟩
    exact MemLp.toMemLpPer (memLp_const (1 : ℝ))
  uSob :=
    MemSobolevPer.of_smoothPeriodic (d := d) (2 : ℝ≥0∞)
      (0 : SmoothPeriodic d)
  m_nonneg :=
    MeasureTheory.ae_of_all _ (fun _ => zero_le_one)
  hRes := by
    have h0 : hjbResidual (d := d)
        (fun _ : Fin d → ℝ => (0 : ℝ))
        (fun _ _ _ => (0 : ℝ))
        (fun _ _ => (0 : ℝ))
        (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ))
        = (fun _ => (0 : ℝ)) := by
      funext x; unfold hjbResidual; simp
    rw [h0]
    exact integrable_zero _ _ _
  hResM := by
    have h0 : (fun x : Fin d → ℝ => hjbResidual (d := d)
        (fun _ : Fin d → ℝ => (0 : ℝ))
        (fun _ _ _ => (0 : ℝ))
        (fun _ _ => (0 : ℝ))
        (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ)) x
        * ((fun _ : Fin d → ℝ => (1 : ℝ)) x))
        = (fun _ => (0 : ℝ)) := by
      funext x; unfold hjbResidual; simp
    rw [h0]
    exact integrable_zero _ _ _
  hFluxInt := by
    have h0 : (fun x : Fin d → ℝ =>
        StationaryMFG.Hamiltonian.mDpH (fun _ _ _ => (0 : Fin d → ℝ)) x
          (fun i => (fun _ _ => (0 : ℝ)) i x)
          ((fun _ => (1 : ℝ)) x))
        = (fun _ => (0 : Fin d → ℝ)) := by
      funext x
      unfold StationaryMFG.Hamiltonian.mDpH
      simp
    rw [h0]
    exact integrable_zero _ _ _
  hStrongVI := by
    intro μ υ Dυ
    -- The integrand of `mfgOperatorPair` vanishes pointwise on the
    -- trivial data: each summand is killed by `V = 0`, `H = 0`,
    -- `DpH = 0`, `(μ - 1)*υ + (1 - 1)*υ` and `m = 1` collapses.
    have hzero :
        mfgOperatorPair (d := d)
            (V := fun _ => (0 : ℝ))
            (H := fun _ _ _ => (0 : ℝ))
            (DpH := fun _ _ _ => (0 : Fin d → ℝ))
            (fun _ _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ))
            (fun i x => Dυ i x - (fun _ _ => (0 : ℝ)) i x)
            (μ - fun _ => (1 : ℝ)) (υ - fun _ => (0 : ℝ)) = 0 := by
      unfold mfgOperatorPair
      simp [StationaryMFG.Hamiltonian.euclideanDot]
    rw [hzero]

/-- The thin-input bundle is non-vacuous on the trivial data: there
exists `T : H4SimplePowerThinInputs …`. (This is independent of the
paper hypotheses `hmon`/`hpow`, which `H = 0` does not in general
satisfy — `HypothesisPowerGrowth.lower` fails for large `‖p‖`.) -/
example (d : ℕ) :
    Nonempty (H4SimplePowerThinInputs (d := d) (γBar := (2 : ℝ))
                (V := fun _ : Fin d → ℝ => (0 : ℝ))
                (H := fun _ _ _ => (0 : ℝ))
                (DpH := fun _ _ _ => (0 : Fin d → ℝ))
                (betaBar := (2 : ℝ≥0∞)) (gammaBar := (2 : ℝ≥0∞))) :=
  ⟨trivialThinInputs d⟩

/-- End-to-end sanity check: under the four paper hypotheses
`(hmon, hpow, hV, hHat0)` plus the authorised paper-residue bundle,
`thm_main_simplePowerGrowth_concrete` produces a strong solution.
The exponents are pinned to the paper formulas via
`Hamiltonian.betaBar`/`gammaBar`/`betaBar'`/`gammaBar'` of
`hpow.α, hpow.β`. -/
example {d : ℕ}
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hmon : HypothesisMonotone H DpH)
    (hpow : HypothesisPowerGrowth H DpH)
    (hV : Periodic.MemLpPer
            (ENNReal.ofReal (Hamiltonian.betaBar' hpow.β)) V)
    (hHat0 : StationaryMFG.Hamiltonian.HypothesisHat0 (d := d) H)
    (hFin : StationaryMFG.Hamiltonian.Hext_finite_at_zero (d := d) H)
    (hAgree : StationaryMFG.Hamiltonian.H_zero_eq_Hext (d := d) H)
    (hHextCont : StationaryMFG.Hamiltonian.HypothesisHextJointCont (d := d) H)
    (residues :
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
        V H DpH hpow) :
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
  thm_main_simplePowerGrowth_concrete (d := d)
    V H DpH hmon hpow hV hHat0 hFin hAgree hHextCont residues

/-! ### Phase D0 — diagnostic constructor for `T10PaperResidues`

`T10PaperResidues.of_paperHypotheses` exposes the *exact* dependency
shape of the residue bundle relative to the four paper hypotheses
`(hmon, hpow, hV, hHat0)` plus the surviving authorisation rider
`hAgree`. It is a refinement scaffold: every field of
`T10PaperResidues` is a `?placeholder` closed by `sorry`, and each
placeholder is annotated with the closure phase that will discharge
it. After Phase D7 lands, this constructor is sorry-free and
`thm_main_simplePowerGrowth_paper` will internally call it (Phase D8),
dropping the explicit `residues` parameter.

**Remaining closure gaps (one per `T10PaperResidues` field).**

* D1 (weak-pairings audit) — `h_weak_mOf`, `h_weak_uOf`,
  `h_weak_DuOf`.
* D2 (cheap scalar layer) — `epsSeq`, `epsSeq_pos`, `epsSeq_tendsto`,
  `Vbound`, `Vint_bound`, `Vβp_bound`, `hVint_nn`, `hVβp_nn`.
* D3 (measurability cascade) — `hu_measRaw`, `hDu_measRaw`.
* D4 (paperSol bundle + alignment) — `paperSol`, `cBundles`,
  `epsTerms_align`.
* D5 (strict positivity) — `hμ_posOf`.
* D6 (Minty residues) — `mintyResSetOf`, `mintyResSignedOf`,
  `mintyResTransportOf`.
-/

/-! ### Phase D2 helpers — cheap regularisation sequence.

`paperEpsSeq k := 1 / ((k : ℝ) + 1)` is the canonical paper
regularisation sequence: strictly positive (since `(k : ℝ) + 1 > 0`)
and tending to `0` at infinity (Mathlib
`tendsto_one_div_add_atTop_nhds_zero_nat`). Used by
`T10PaperResidues.of_paperHypotheses` to discharge the three
`epsSeq*` fields. -/

/-- Canonical paper regularisation sequence `1 / (k + 1)`. -/
noncomputable def paperEpsSeq : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)

/-- Strict positivity: `0 < 1 / (k + 1)` for every `k : ℕ`. -/
lemma paperEpsSeq_pos : ∀ k : ℕ, 0 < paperEpsSeq k := by
  intro k
  unfold paperEpsSeq
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  exact div_pos one_pos hk

/-- Convergence: `paperEpsSeq → 0` at infinity. -/
lemma paperEpsSeq_tendsto :
    Filter.Tendsto paperEpsSeq Filter.atTop (nhds 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-! ### Phase D4.1 — canonical paper `epsTerms` formula.

`paperEpsTerms` is the canonical paper-side regulariser residue
`ε · |Du|^(γ̄/2) + ε · u^γ̄` (paper §3 Legendre/regulariser block,
`Source/FGU-monotone_revised.tex`, transport-identity line 1212).
It is parameterised on the regulariser scale `ε`, the gradient-norm
exponent `γ̄`, and the bare regularised solution `sol` whose
`u`/`Du` components feed the formula.

This is the canonical witness used by
`T10PaperResidues.of_paperHypotheses` for the `cBundles k`
field's `epsTerms` slot, so that the residue-side alignment field
`epsTerms_align k` discharges via the bundled `epsTerms_eq`
certificate (`congrFun` on a function-level equation). Per iter
`infra-P5-T10-D4-1-canonical-paperEpsTerms`.
-/

/-- **Canonical paper `epsTerms` formula** (paper §3 regulariser
residue, `Source/FGU-monotone_revised.tex` lines 1212-1214):
`ε · |Du|^γ̄ + ε · |u|^γ̄`.

The dot-product `(fun i => sol.Du i x) ⬝ (fun i => sol.Du i x)`
realises `|Du(x)|²` in our `Fin d → ℝ` Euclidean layer, and the
half-power `^ (γ̄ / 2)` then yields `|Du(x)|^γ̄` (the dot-product
realisation is automatically non-negative, so no absolute value is
needed on the gradient term).

**Phase-0 transitional shape.** The paper formula is `ε|u_ε|^γ̄`
(with explicit absolute value on `u`); the absolute-value
migration is deferred to a follow-up task, because the Lean-side
chain consumes a fixed pointwise alignment formula in
`RegularizedPaperSolutionData.hTransport_identity` (and its
producer), which currently uses `sol.u x ^ γ̄` (no abs). Migrating
to `|u|^γ̄` requires updating that record and its producer chain
across `AssemblyContext.lean`, `AprioriUniform.lean`, and
`RegularizedSequence.lean`. Filed as the Phase-0 follow-up
**`infra-P5-T10-D4-4-paperEpsTerms-abs-u-migration`** (per
`infra-P5-T10-D4-4-PaperCBundleForK-fix-scaffolding`). -/
noncomputable def paperEpsTerms
    {d : ℕ} {ε : ℝ} {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {γBarReal βBarReal βBarReal' γBarReal' : ℝ}
    (eps γBar : ℝ)
    (sol : StationaryMFG.Theorems.SimplePower.Banach.RegularizedBareSolution
            d ε V H DpH γBarReal βBarReal βBarReal' γBarReal') :
    (Fin d → ℝ) → ℝ :=
  fun x =>
    eps *
        ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
          ^ (γBar / 2)
      + eps * |sol.u x| ^ γBar

/-- **D4.1 packaged C-class stub**: a per-`k` `AprioriUniformPerSolHypothesesC`
bundle together with the canonical-`epsTerms` identification certificate.

This packaged shape is what `T10PaperResidues.of_paperHypotheses`'s
`cBundles k` discharge consumes: projecting `.bundle` lands the C-class
record, and `.epsTerms_eq` discharges the residue-side
`epsTerms_align` field (via `congrFun` at each `x`).

Defined in this packaged form so the underlying analytic content
(strict positivity of `m`, integrability/non-negativity of the paper
regulariser residue, periodicity certificates, …) plus the canonical
`epsTerms = paperEpsTerms …` identification can be sourced from a
**single** `sorry` (instead of nine independent C-class field
sorries plus an extra alignment sorry). The discharge of this single
`sorry` is the body of D4.2/D4.3 (`infra-P5-T10-D4-2-…`). -/
structure CBundleD41Stub
    {d : ℕ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    {ε : ℝ} {βBarReal' γBarReal' : ℝ}
    (sol : StationaryMFG.Theorems.SimplePower.Banach.RegularizedBareSolution
            d ε V H DpH (Hamiltonian.gammaBar hpow.α hpow.β)
            (hpow.β + 1) βBarReal' γBarReal')
    (eps γBar : ℝ) where
  /-- The packaged C-class bundle. **Phase 1 sub-task 1c-b (v7 plan,
  D4.1c-b):** retyped to the integral V-data sibling
  `AprioriUniformPerSolHypothesesC_int` (`AprioriUniform.lean:2665`).
  **iter `infra-P5-T10-v7-drain-paperHVbndAuth`**: `Vbound` parameter
  and `hVbnd` field dropped from the C_int structure. -/
  bundle :
    StationaryMFG.Theorems.SimplePower.Banach.AprioriUniformPerSolHypothesesC_int
      (d := d) hpow sol
  /-- Canonical-`epsTerms` identification (function-level): the
  bundle's `epsTerms` field equals the paper-formula
  `paperEpsTerms eps γBar sol`. -/
  epsTerms_eq :
    bundle.epsTerms = paperEpsTerms (V := V) (H := H) (DpH := DpH) eps γBar sol

/-! ### Phase D6 step 1 — shared paper-scalar bundle

Per `infra-P5-T10-D6-shared-paper-scalars` (first child of the
iter-0534 D6 audit's seven-step plan), the three Minty residues
(`SetFamilyNarrowMintyResidue`, `SignedFamilyNarrowMintyResidue`,
`TransportFamilyNarrowMintyResidue`) all carry the same seven
**paper scalars** (Hamiltonian residues `hHat0`/`hAgree`, two
Hölder-conjugate certificates, the Gateaux strict lower bound
`1 < γ̄`, the exponent identification `γ̄ = γ̄`, and the conjugate-side
`MemLpPer β̄'` certificate for `V`). To avoid triplicating those
seven proofs across the three Minty residue producers, we package
them into a single shared structure `T10PaperScalars` here, alongside
a producer `T10PaperScalars_of_paperHypotheses` that derives all
seven from `(hpow, hV, hHat0, hAgree)` (the surviving paper
hypotheses + agreement rider).

This is **shared infrastructure only** — no D0 placeholder
discharges. The follow-up D6 children will consume
`T10PaperScalars_of_paperHypotheses` to discharge the three
`mintyRes*Of` residues without re-proving the seven scalars
inline. -/

/-- **Shared paper-scalar bundle** for the three Minty residues.

The three narrow Minty residues (`SetFamilyNarrowMintyResidue`,
`SignedFamilyNarrowMintyResidue`, `TransportFamilyNarrowMintyResidue`)
each carry the same seven scalars at the paper-canonical exponent
quadruple `(γ̄, β̄, β̄', γ̄')` with the Gateaux exponent pinned to
`γBar = γ̄`. We bundle them here so the three D6 producers can share
a single derivation.

The exponent quadruple is fixed by `hpow` via:
* `γBarReal := Hamiltonian.gammaBar hpow.α hpow.β`,
* `βBarReal := Hamiltonian.betaBar hpow.β`,
* `βBarReal' := Hamiltonian.betaBar' hpow.β`,
* `γBarReal' := Hamiltonian.gammaBar' hpow.α hpow.β`,
* `γBar := Hamiltonian.gammaBar hpow.α hpow.β`.
-/
structure T10PaperScalars
    {d : ℕ}
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH) where
  /-- Paper-Hamiltonian residue: `H` is finite at zero density. -/
  hHat0 : Hamiltonian.HypothesisHat0 (d := d) H
  /-- Paper-Hamiltonian residue: `H` agrees with `Hext` at zero density. -/
  hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H
  /-- Hölder-conjugacy of the `β`-exponent pair, in the residue's
  consumer-shape direction `β̄'.HolderConjugate β̄`. -/
  hβconj : (Hamiltonian.betaBar' hpow.β).HolderConjugate
              (Hamiltonian.betaBar hpow.β)
  /-- Hölder-conjugacy of the `γ`-exponent pair, in the residue's
  consumer-shape direction `γ̄'.HolderConjugate γ̄`. -/
  hγconj : (Hamiltonian.gammaBar' hpow.α hpow.β).HolderConjugate
              (Hamiltonian.gammaBar hpow.α hpow.β)
  /-- Strict lower bound `1 < γ̄` (paper Gateaux gradient hypothesis). -/
  hγ_one_lt : 1 < Hamiltonian.gammaBar hpow.α hpow.β
  /-- Identification of the chosen Gateaux exponent with `γBarReal`.
  Trivial at the paper-canonical pinning (`γBar = γBarReal = γ̄`),
  but kept as a field so the structure can be sliced into the three
  Minty residues without rewiring the consumer's `hγBar_eq` field. -/
  hγBar_eq : Hamiltonian.gammaBar hpow.α hpow.β =
              Hamiltonian.gammaBar hpow.α hpow.β
  /-- `V`-regularity at the conjugate exponent (consumed by the K0
  producer of each Minty residue). -/
  hV_conj : Periodic.MemLpPer (d := d)
              (ENNReal.ofReal (Hamiltonian.betaBar' hpow.β)) V

/-- **Producer for the shared paper-scalar bundle.** Given the four
paper hypotheses `(hpow, hV, hHat0, hAgree)`, derive all seven
shared paper scalars at the paper-canonical exponent quadruple.

* `hHat0`, `hAgree` are direct copies of the input.
* `hβconj` is `(hpqBeta_paper hpow).symm` (flip the Hölder direction
  to match the residue's consumer shape).
* `hγconj` is `(hpqGamma_paper hpow).symm`.
* `hγ_one_lt` is `Hamiltonian.one_lt_gammaBar hpow.hα hpow.hβ`.
* `hγBar_eq` is `rfl`.
* `hV_conj` is the input `hV` directly. -/
noncomputable def T10PaperScalars_of_paperHypotheses
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (hV : Periodic.MemLpPer (d := d)
            (ENNReal.ofReal (Hamiltonian.betaBar' hpow.β)) V)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H) :
    T10PaperScalars (d := d) V H DpH hpow where
  hHat0 := hHat0
  hAgree := hAgree
  hβconj :=
    (StationaryMFG.Theorems.SimplePower.Banach.hpqBeta_paper
      (d := d) hpow).symm
  hγconj :=
    (StationaryMFG.Theorems.SimplePower.Banach.hpqGamma_paper
      (d := d) hpow).symm
  hγ_one_lt :=
    Hamiltonian.one_lt_gammaBar hpow.α hpow.β hpow.hα hpow.hβ
  hγBar_eq := rfl
  hV_conj := hV

structure PaperSolForK
    {d : ℕ}
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (k : ℕ)
    [Fact (1 ≤ ENNReal.ofReal (hpow.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))] where
  /-- Paper §8 analytic residues at `(ε = paperEpsSeq k, V, H, DpH, hpow)`
  with the paper-canonical exponent quadruple.

  Iter 0609 (`paperSolFor-rewire-to-min`): retyped from the legacy
  13-conjunct `PaperSection8AnalyticResidues` to the paper-faithful
  11-conjunct `PaperSection8AnalyticResiduesMin`. The hemicontinuity
  feeder now routes through the `_min` chain rather than the legacy
  inline `hSegRes` chain. -/
  hAnalytic :
    StationaryMFG.Theorems.SimplePower.Banach.PaperSection8AnalyticResiduesMin
      (d := d)
      (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
      (βBarReal := hpow.β + 1)
      (βBarReal' := (hpow.β + 1) / hpow.β)
      (γBarReal' := (hpow.α * (hpow.β + 1) / hpow.β)
                      / (hpow.α * (hpow.β + 1) / hpow.β - 1))
      (paperEpsSeq k) V H DpH hpow
  /-- Set-family Minty/δ-limit premise at the specific Browder–Minty
  witness, universally quantified over the `ctx` to be built by
  `aepsiUniformContextK_of_paperHypotheses_closed_paper_min`. -/
  hMinty_set :
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
                (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) (Dυ i)) →
        (∀ i, Periodic.HasWeakDerivPer (d := d) i υ (Dυ i)) →
          0 ≤ mfgOperatorEpsPair
                (V := V) (H := H) (DpH := DpH)
                (hpow.α * (hpow.β + 1) / hpow.β) (paperEpsSeq k)
                Dυ (S.indicator ρ) υ
                (fun i x => Dυ i x -
                  StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
                (S.indicator ρ -
                  StationaryMFG.Theorems.SimplePower.Banach.mOf q)
                (υ - StationaryMFG.Theorems.SimplePower.Banach.uOf q)
  /-- Signed-family Minty/δ-limit premise at the specific Browder–Minty
  witness. -/
  hMinty_signed :
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
                (fun _ => (0 : ℝ))
  /-- Transport-family Minty/δ-limit premise at the specific
  Browder–Minty witness. -/
  hMinty_transport :
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
                (υ - StationaryMFG.Theorems.SimplePower.Banach.uOf q)
  /-- Signed-family **user-probe** Minty/δ-limit premise. -/
  hMinty_signed_user_probe :
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
                  StationaryMFG.Theorems.SimplePower.Banach.uOf q x)
  /-- Signed-family **user-triple** Minty/δ-limit premise. -/
  hMinty_signed_user_triple :
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
                  StationaryMFG.Theorems.SimplePower.Banach.uOf q x)
  /-- Per-`sol` paper-side input: ρ-perturbed primal `MemLpPer βBar` cert. -/
  hRhoMemLp :
    ∀ (sol : StationaryMFG.Theorems.SimplePower.Banach.RegularizedBareSolution
              d (paperEpsSeq k) V H DpH
              (hpow.α * (hpow.β + 1) / hpow.β)
              (hpow.β + 1)
              ((hpow.β + 1) / hpow.β)
              ((hpow.α * (hpow.β + 1) / hpow.β)
                / (hpow.α * (hpow.β + 1) / hpow.β - 1))),
    ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
    ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
      (MeasureTheory.volume.restrict (Periodic.UnitCube d)) S < ∞ →
    ∀ n : ℕ,
      Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1))
        (fun x => sol.m x + (1 / ((n : ℝ) + 1)) * σ *
                    (sol.m x * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
  /-- Per-`sol` paper-side input: σ-scaled primal indicator `MemLpPer` cert. -/
  hSigmaMIndicMemLp :
    ∀ (sol : StationaryMFG.Theorems.SimplePower.Banach.RegularizedBareSolution
              d (paperEpsSeq k) V H DpH
              (hpow.α * (hpow.β + 1) / hpow.β)
              (hpow.β + 1)
              ((hpow.β + 1) / hpow.β)
              ((hpow.α * (hpow.β + 1) / hpow.β)
                / (hpow.α * (hpow.β + 1) / hpow.β - 1))),
    ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
    ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
      (MeasureTheory.volume.restrict (Periodic.UnitCube d)) S < ∞ →
      Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1))
        (fun x => σ * sol.m x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
  /-- Per-`sol` paper-side input: signed-perturbed continuity. -/
  hCont_signed :
    ∀ (sol : StationaryMFG.Theorems.SimplePower.Banach.RegularizedBareSolution
              d (paperEpsSeq k) V H DpH
              (hpow.α * (hpow.β + 1) / hpow.β)
              (hpow.β + 1)
              ((hpow.β + 1) / hpow.β)
              ((hpow.α * (hpow.β + 1) / hpow.β)
                / (hpow.α * (hpow.β + 1) / hpow.β - 1))),
    ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
    ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
      (MeasureTheory.volume.restrict (Periodic.UnitCube d)) S < ∞ →
      Filter.Tendsto
        (fun n : ℕ =>
          mfgOperatorEpsPair
            (V := V) (H := H) (DpH := DpH)
            (hpow.α * (hpow.β + 1) / hpow.β) (paperEpsSeq k)
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
              (hpow.α * (hpow.β + 1) / hpow.β) (paperEpsSeq k)
              sol.Du sol.m sol.u
              (fun _ _ => (0 : ℝ))
              (fun x => σ * sol.m x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
              (fun _ => (0 : ℝ))))
  /-- Per-`sol` paper-side input: HJB-residual times `m` integrability. -/
  hResM :
    ∀ (sol : StationaryMFG.Theorems.SimplePower.Banach.RegularizedBareSolution
              d (paperEpsSeq k) V H DpH
              (hpow.α * (hpow.β + 1) / hpow.β)
              (hpow.β + 1)
              ((hpow.β + 1) / hpow.β)
              ((hpow.α * (hpow.β + 1) / hpow.β)
                / (hpow.α * (hpow.β + 1) / hpow.β - 1))),
    MeasureTheory.Integrable
      (fun x =>
        StationaryMFG.Theorems.SimplePower.hjbResidual V H sol.Du sol.m sol.u x
          * sol.m x)
      (MeasureTheory.volume.restrict (Periodic.UnitCube d))
  /-- Per-`sol` paper-side input: VI-positive direction lower bound. -/
  hVI_pos :
    ∀ (sol : StationaryMFG.Theorems.SimplePower.Banach.RegularizedBareSolution
              d (paperEpsSeq k) V H DpH
              (hpow.α * (hpow.β + 1) / hpow.β)
              (hpow.β + 1)
              ((hpow.β + 1) / hpow.β)
              ((hpow.α * (hpow.β + 1) / hpow.β)
                / (hpow.α * (hpow.β + 1) / hpow.β - 1))),
    (0 : ℝ) ≤
    ∫ x in Periodic.UnitCube d,
        (sol.m x * ((DpH x (fun i => sol.Du i x) (sol.m x))
                      ⬝ (fun i => sol.Du i x))
          + (sol.m x - 1) * sol.u x
          + (paperEpsSeq k) *
              ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
                ^ ((hpow.α * (hpow.β + 1) / hpow.β) / 2)
          + (paperEpsSeq k) * |sol.u x| ^ (hpow.α * (hpow.β + 1) / hpow.β))
        ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
  /-- Per-`sol` paper-side input: VI-negative direction upper bound. -/
  hVI_neg :
    ∀ (sol : StationaryMFG.Theorems.SimplePower.Banach.RegularizedBareSolution
              d (paperEpsSeq k) V H DpH
              (hpow.α * (hpow.β + 1) / hpow.β)
              (hpow.β + 1)
              ((hpow.β + 1) / hpow.β)
              ((hpow.α * (hpow.β + 1) / hpow.β)
                / (hpow.α * (hpow.β + 1) / hpow.β - 1))),
    ∫ x in Periodic.UnitCube d,
        (sol.m x * ((DpH x (fun i => sol.Du i x) (sol.m x))
                      ⬝ (fun i => sol.Du i x))
          + (sol.m x - 1) * sol.u x
          + (paperEpsSeq k) *
              ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
                ^ ((hpow.α * (hpow.β + 1) / hpow.β) / 2)
          + (paperEpsSeq k) * |sol.u x| ^ (hpow.α * (hpow.β + 1) / hpow.β))
        ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
      ≤ (0 : ℝ)
  /-- Per-`sol` paper-side input: `u` integrability. -/
  hu_int :
    ∀ (sol : StationaryMFG.Theorems.SimplePower.Banach.RegularizedBareSolution
              d (paperEpsSeq k) V H DpH
              (hpow.α * (hpow.β + 1) / hpow.β)
              (hpow.β + 1)
              ((hpow.β + 1) / hpow.β)
              ((hpow.α * (hpow.β + 1) / hpow.β)
                / (hpow.α * (hpow.β + 1) / hpow.β - 1))),
    MeasureTheory.Integrable sol.u
      (MeasureTheory.volume.restrict (Periodic.UnitCube d))
  /-- Per-`sol` paper-side input: `m * (u + H − V)` integrability. -/
  hMUH_int :
    ∀ (sol : StationaryMFG.Theorems.SimplePower.Banach.RegularizedBareSolution
              d (paperEpsSeq k) V H DpH
              (hpow.α * (hpow.β + 1) / hpow.β)
              (hpow.β + 1)
              ((hpow.β + 1) / hpow.β)
              ((hpow.α * (hpow.β + 1) / hpow.β)
                / (hpow.α * (hpow.β + 1) / hpow.β - 1))),
    MeasureTheory.Integrable
      (fun x => sol.m x *
        (sol.u x + H x (fun i => sol.Du i x) (sol.m x) - V x))
      (MeasureTheory.volume.restrict (Periodic.UnitCube d))
  /-- Per-`sol` paper-side input: paper-line-1212 RHS integrability. -/
  hRHS_int :
    ∀ (sol : StationaryMFG.Theorems.SimplePower.Banach.RegularizedBareSolution
              d (paperEpsSeq k) V H DpH
              (hpow.α * (hpow.β + 1) / hpow.β)
              (hpow.β + 1)
              ((hpow.β + 1) / hpow.β)
              ((hpow.α * (hpow.β + 1) / hpow.β)
                / (hpow.α * (hpow.β + 1) / hpow.β - 1))),
    MeasureTheory.Integrable
      (fun x =>
        sol.m x * (-H x (fun i => sol.Du i x) (sol.m x)
                  + (DpH x (fun i => sol.Du i x) (sol.m x))
                      ⬝ (fun i => sol.Du i x))
          + V x * sol.m x
          + (paperEpsSeq k) *
              ((fun i => sol.Du i x) ⬝ (fun i => sol.Du i x))
                ^ ((hpow.α * (hpow.β + 1) / hpow.β) / 2)
          + (paperEpsSeq k) * |sol.u x| ^ (hpow.α * (hpow.β + 1) / hpow.β))
      (MeasureTheory.volume.restrict (Periodic.UnitCube d))

/-! ### `paperSolFor-minty-set` — ε-level set-narrow Minty conclusion

The producer `paperSection8_hMinty_set_of_paperHypotheses` discharges
the `hMinty_set` field of `PaperSolForK V H DpH hpow k`. Per the
`infra-P5-T10-v7-paperSolFor-pre-scope` audit (Child #5,
`docs/PAPERSOLFOR_SCOPE.md` D-pre.4), the ε-level set-narrow Minty
conclusion at the specific Browder–Minty witness `q` extracted by
`exists_regularizedBareSolution_K` is delivered by the existing chain
```
mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses
  + hVIeps_set_of_KAepsi_VI
```
(both in `Banach/RegularizedSequence.lean`). The first builds the
operator-continuity `Tendsto` certificate at the strict-positive
perturbation `μ_n := S.indicator ρ + 1/(n+1)` from the per-query
residue dominator bundle `SetTendstoResidueOf`; the second uses that
`Tendsto` to upgrade the K_Aepsi-form weak VI (extracted internally
inside `exists_regularizedBareSolution_K` via
`exists_banachVI_at_eps_KAepsi` + `hemicont_upgrade`) to the strong
set-narrow VI at the bare-function endpoints.

This is the **ε-level layer** (`mfgOperatorEpsPair`), *not* the
δ-limit `setSegInputsAuth` layer; the two have distinct types and
domains (per `docs/PAPERSOLFOR_SCOPE.md` D-pre.4).

The producer takes the same six paper hypotheses as the existing
`regularizedSequenceData_of_paperHypotheses`
(`Banach/RegularizedSequence.lean:7378`) plus the per-query residue
supplier `residueOf_set : ∀ q hq_K0 S hS ρ υ Dυ …, SetTendstoResidueOf
…`. No new authorisation parameter is introduced. -/

/-- **ε-level set-narrow Minty producer.**

Given the paper hypotheses `(hpow, hRegH, hHat0, hFin, hAgree)` and a
per-query residue supplier `residueOf_set`, build the `hMinty_set`
field of `PaperSolForK V H DpH hpow k` at the paper-canonical
exponents.

The field body is universally quantified over `(ctx, q, hq_K0, hVI)`
and over the test-triple data `(S, ρ, υ, Dυ)` with their
membership/regularity certificates. The discharge dispatches to:

* `Banach.mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses`
  for the ε-level operator-continuity `Tendsto` along
  `μ_n := S.indicator ρ + 1/(n+1)`, fed by the residue's dominator
  bundle; and
* `Banach.hVIeps_set_of_KAepsi_VI` for the strong-VI upgrade from the
  K_Aepsi-form weak VI.

Reuse pattern: this is the per-`k` slice of the `hMinty_set` argument
to `exists_regularizedBareSolution_K` constructed inside
`regularizedSequenceData_of_paperHypotheses`
(`Banach/RegularizedSequence.lean:7167-7182`), specialised at
`ε := paperEpsSeq k` and the paper-canonical exponent quadruple. -/
noncomputable def paperSection8_hMinty_set_of_paperHypotheses
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
    -- Per-query residue supplier for the set family.
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
              hpow q S ρ υ Dυ) :
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
                (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) (Dυ i)) →
        (∀ i, Periodic.HasWeakDerivPer (d := d) i υ (Dυ i)) →
          0 ≤ mfgOperatorEpsPair
                (V := V) (H := H) (DpH := DpH)
                (hpow.α * (hpow.β + 1) / hpow.β) (paperEpsSeq k)
                Dυ (S.indicator ρ) υ
                (fun i x => Dυ i x -
                  StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
                (S.indicator ρ -
                  StationaryMFG.Theorems.SimplePower.Banach.mOf q)
                (υ - StationaryMFG.Theorems.SimplePower.Banach.uOf q) := by
  -- Derive the `SimplePowerExponentFacts` bundle at the paper exponents from
  -- `hpow`. This is the same cast used by
  -- `aepsiUniformContextK_of_paperHypotheses_closed_paper` (see
  -- `AssemblyContext.lean` around line 7345).
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
  -- Closure over the universal `(ctx, q, hq_K0, hVI)` and the test-triple.
  -- **Phase 5 step3d**: the `_hWeak_υ` hypothesis is consumed as a slot
  -- to match the W-form sibling's shape but is unused by the K-form
  -- analytic discharge (the K-form helper `hVIeps_set_of_KAepsi_VI`
  -- doesn't require a weak-derivative tie).
  intro ctx q hq_K0 hVI S hS ρ υ Dυ hρ_nn hSρ_memLp hυ_memSob hDυ_memLp _hWeak_υ
  -- Extract the per-query residue dominator bundle.
  set r :=
    residueOf_set q hq_K0 S hS ρ υ Dυ hρ_nn
      hSρ_memLp hυ_memSob hDυ_memLp with hr_def
  -- Build the ε-level operator-continuity `Tendsto` certificate along
  -- `μ_n := S.indicator ρ + 1/(n+1)`.
  have hCont :=
    StationaryMFG.Theorems.SimplePower.Banach.mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses_of_aestronglyMeasurable
      (ε := paperEpsSeq k)
      (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
      (βBarReal := hpow.β + 1)
      (βBarReal' := (hpow.β + 1) / hpow.β)
      (γBarReal' := (hpow.α * (hpow.β + 1) / hpow.β)
                      / (hpow.α * (hpow.β + 1) / hpow.β - 1))
      hpow hRegH hExp hHat0 hFin hAgree
      Dυ υ (StationaryMFG.Theorems.SimplePower.Banach.uOf q)
      (StationaryMFG.Theorems.SimplePower.Banach.DuOf q)
      (StationaryMFG.Theorems.SimplePower.Banach.mOf q) V S ρ
      hS r.hρ r.hm r.hV r.hυ r.hu r.hDυ r.hDu hρ_nn hSρ_memLp
      r.Gh r.Eh r.hGh_memLp r.hEh_memLp r.hGh_bd r.hEh_bd
      r.Gf r.Ef r.hGf_memLp r.hEf_memLp r.hGf_bd r.hEf_bd
      r.Gm r.Em r.hGm_memLp r.hEm_memLp r.hGm_bd r.hEm_bd
  -- Upgrade the K_Aepsi-form weak VI to the strong set-narrow VI at the
  -- bare-function endpoints.
  exact StationaryMFG.Theorems.SimplePower.Banach.hVIeps_set_of_KAepsi_VI
    ctx.auxHypsK q hVI S hS ρ υ Dυ hρ_nn
    hSρ_memLp hυ_memSob hDυ_memLp hCont

/-! ### Hext-free `_of_rc0` set Minty producer (T3 step 8)

ε-generic, `Hext_finite_at_zero`-free sibling of
`paperSection8_hMinty_set_of_paperHypotheses`. Two changes:

* takes the line-1821 right-continuity-at-0 certificate `hH_rc0`
  (accepted T3 rider) instead of `(hHat0, hFin, hAgree)`; and
* routes the ε-level operator-continuity `Tendsto` through the Hext-free
  `mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses_of_aestronglyMeasurable_of_rc0`
  bridge (step 6) instead of the Hext-pulling
  `_of_aestronglyMeasurable` aggregator.

`ε` is a free variable (the Hext-pulling sibling is fixed at
`paperEpsSeq k`); this is exactly what the substituted-pair wrapper at
`(Hdelta hweak ε, DpHepsilon hweak qE)` needs. The body is otherwise a
byte-for-byte copy of the sibling. -/
open StationaryMFG.Theorems.SimplePower.Banach in
noncomputable def paperSection8_hMinty_set_of_paperHypotheses_of_rc0
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
    -- Per-query residue supplier for the set family.
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
              hpow q S ρ υ Dυ) :
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
                (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) (Dυ i)) →
        (∀ i, Periodic.HasWeakDerivPer (d := d) i υ (Dυ i)) →
          0 ≤ mfgOperatorEpsPair
                (V := V) (H := H) (DpH := DpH)
                (hpow.α * (hpow.β + 1) / hpow.β) ε
                Dυ (S.indicator ρ) υ
                (fun i x => Dυ i x -
                  StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
                (S.indicator ρ -
                  StationaryMFG.Theorems.SimplePower.Banach.mOf q)
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
  intro ctx q hq_K0 hVI S hS ρ υ Dυ hρ_nn hSρ_memLp hυ_memSob hDυ_memLp _hWeak_υ
  set r :=
    residueOf_set q hq_K0 S hS ρ υ Dυ hρ_nn
      hSρ_memLp hυ_memSob hDυ_memLp with hr_def
  -- Hext-free `_of_rc0` set bridge (step 6) instead of the Hext-pulling
  -- `_of_aestronglyMeasurable` aggregator.
  have hCont :=
    StationaryMFG.Theorems.SimplePower.Banach.mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses_of_aestronglyMeasurable_of_rc0
      (ε := ε)
      (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
      (βBarReal := hpow.β + 1)
      (βBarReal' := (hpow.β + 1) / hpow.β)
      (γBarReal' := (hpow.α * (hpow.β + 1) / hpow.β)
                      / (hpow.α * (hpow.β + 1) / hpow.β - 1))
      hpow hRegH hExp hH_rc0
      Dυ υ (StationaryMFG.Theorems.SimplePower.Banach.uOf q)
      (StationaryMFG.Theorems.SimplePower.Banach.DuOf q)
      (StationaryMFG.Theorems.SimplePower.Banach.mOf q) V S ρ
      hS r.hρ r.hm r.hV r.hυ r.hu r.hDυ r.hDu hρ_nn hSρ_memLp
      r.Gh r.Eh r.hGh_memLp r.hEh_memLp r.hGh_bd r.hEh_bd
      r.Gf r.Ef r.hGf_memLp r.hEf_memLp r.hGf_bd r.hEf_bd
      r.Gm r.Em r.hGm_memLp r.hEm_memLp r.hGm_bd r.hEm_bd
  exact StationaryMFG.Theorems.SimplePower.Banach.hVIeps_set_of_KAepsi_VI
    ctx.auxHypsK q hVI S hS ρ υ Dυ hρ_nn
    hSρ_memLp hυ_memSob hDυ_memLp hCont

/-- **`measurable_H`-free set-family Minty producer** (D2b-1c-ii-c4).

`aeMeasH`-input sibling of
`paperSection8_hMinty_set_of_paperHypotheses_of_rc0`: it drops the
strict `RegularityH`/`HypothesisPowerGrowth` binders and instead consumes
the genuine individual H/DpH fields (bare exponents `α β`, `hDpH_meas`,
`hcont_H_pm`, `hcont_DpH_pm`, `hDpH_upper`), routing the inner operator
tendsto through the aesm-input `_of_aeMeasH` keystone
`mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses_of_aestronglyMeasurable_of_rc0_of_aeMeasH`,
which takes the boundary H AE composites (carried by the bare residue
bundle `SetTendstoResidueOfBare`) instead of `hRegH.measurable_H`.

This is instantiable at `H := HdeltaK0`: the H AE composites are supplied
by `aemeasurable_HdeltaK0_comp_of_rc0`. The strict `_of_rc0` producer
above is left byte-for-byte intact for T1/T2. -/
noncomputable def paperSection8_hMinty_set_of_paperHypotheses_of_rc0_of_aeMeasH
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
    -- Per-query bare-exponent residue supplier for the set family.
    (residueOf_set :
      ∀ (q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
                (β + 1)
                (α * (β + 1) / β)),
        q ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi d
              (β + 1)
              (α * (β + 1) / β) →
        ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
        ∀ (ρ υ : (Fin d → ℝ) → ℝ)
          (Dυ : Fin d → (Fin d → ℝ) → ℝ),
          (∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
              0 ≤ ρ x) →
          Periodic.MemLpPer (d := d)
            (ENNReal.ofReal (β + 1)) (S.indicator ρ) →
          Periodic.MemSobolevPer (d := d)
            (ENNReal.ofReal (α * (β + 1) / β)) υ →
          (∀ i, Periodic.MemLpPer (d := d)
                  (ENNReal.ofReal (α * (β + 1) / β))
                  (Dυ i)) →
            StationaryMFG.Theorems.SimplePower.Banach.SetTendstoResidueOfBare
              (d := d) (V := V) (H := H) (DpH := DpH)
              (βBarReal := β + 1)
              (γBarReal := α * (β + 1) / β)
              β q S ρ υ Dυ) :
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
      ∀ (S : Set (Fin d → ℝ)), MeasurableSet S →
      ∀ (ρ υ : (Fin d → ℝ) → ℝ)
        (Dυ : Fin d → (Fin d → ℝ) → ℝ),
        (∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
            0 ≤ ρ x) →
        Periodic.MemLpPer (d := d)
          (ENNReal.ofReal (β + 1)) (S.indicator ρ) →
        Periodic.MemSobolevPer (d := d)
          (ENNReal.ofReal (α * (β + 1) / β)) υ →
        (∀ i, Periodic.MemLpPer (d := d)
                (ENNReal.ofReal (α * (β + 1) / β)) (Dυ i)) →
        (∀ i, Periodic.HasWeakDerivPer (d := d) i υ (Dυ i)) →
          0 ≤ mfgOperatorEpsPair
                (V := V) (H := H) (DpH := DpH)
                (α * (β + 1) / β) ε
                Dυ (S.indicator ρ) υ
                (fun i x => Dυ i x -
                  StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
                (S.indicator ρ -
                  StationaryMFG.Theorems.SimplePower.Banach.mOf q)
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
  intro ctx q hq_K0 hVI S hS ρ υ Dυ hρ_nn hSρ_memLp hυ_memSob hDυ_memLp _hWeak_υ
  set r :=
    residueOf_set q hq_K0 S hS ρ υ Dυ hρ_nn
      hSρ_memLp hυ_memSob hDυ_memLp with hr_def
  -- `measurable_H`-free aesm-input keystone (D2b-1c-ii-c4).
  have hCont :=
    StationaryMFG.Theorems.SimplePower.Banach.mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses_of_aestronglyMeasurable_of_rc0_of_aeMeasH
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
      (StationaryMFG.Theorems.SimplePower.Banach.mOf q) V S ρ
      hS r.hρ r.hm r.hV r.hυ r.hu r.hDυ r.hDu hρ_nn hSρ_memLp
      r.hHcomp_ae_n r.hHcomp_ae_lim
      r.Gh r.Eh r.hGh_memLp r.hEh_memLp r.hGh_bd r.hEh_bd
      r.Gf r.Ef r.hGf_memLp r.hEf_memLp r.hGf_bd r.hEf_bd
      r.Gm r.Em r.hGm_memLp r.hEm_memLp r.hGm_bd r.hEm_bd
  exact StationaryMFG.Theorems.SimplePower.Banach.hVIeps_set_of_KAepsi_VI
    ctx.auxHypsK q hVI S hS ρ υ Dυ hρ_nn
    hSρ_memLp hυ_memSob hDυ_memLp hCont

/-! ### `paperSolFor-final-phase5-hWeakDeriv-step3b` — W-form set Minty
producer

Iter-0701 Phase 1 of the 6-phase `paperSolFor-final-phase5-hWeakDeriv`
plan. W-form sibling of `paperSection8_hMinty_set_of_paperHypotheses`
(immediately above), supplying the **refined-cone** Minty inequality
needed by `exists_regularizedBareSolution_K_W` (iter 0698).

Differences from the K-form sibling:

* Witness side: takes `q ∈ K0_Aepsi_W d βBar γBar` (refined non-negativity
  cone, iter 0687) instead of `K0_Aepsi`.
* VI side: takes `hVI` quantifying over `q' ∈ K_Aepsi_W d βBar γBar`
  (refined strict-positivity cone) instead of `K_Aepsi`.
* Context: takes `ctx : AepsiUniformContextK_W` instead of
  `AepsiUniformContextK`.
* Extra hypothesis: `hWeak_υ : ∀ i, HasWeakDerivPer i υ (Dυ i)`
  for the user-supplied test pair (per iter-0683 directive,
  retype the W-form statement to take the weak-derivative tie as a
  paper-faithful hypothesis, not as a new auth).
* Backing analytic lemma: dispatches to
  `Banach.hVIeps_set_of_KAepsi_W_VI` (iter 0701, just above
  `end Banach` in `Banach/RegularizedSequence.lean`) instead of
  `hVIeps_set_of_KAepsi_VI`.

No new authorisation parameter is introduced. -/

/-- **ε-level set-narrow W-form Minty producer.** Builds the
W-form `hMinty_set` field at the paper-canonical exponents. -/
noncomputable def paperSection8_hMinty_set_W_of_paperHypotheses
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
    -- Per-query residue supplier for the set family (identical to
    -- the K-form sibling's, since the residue is at the bare-function
    -- level).
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
              hpow q S ρ υ Dυ) :
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
                (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) (Dυ i)) →
        (∀ i, Periodic.HasWeakDerivPer (d := d) i υ (Dυ i)) →
          0 ≤ mfgOperatorEpsPair
                (V := V) (H := H) (DpH := DpH)
                (hpow.α * (hpow.β + 1) / hpow.β) (paperEpsSeq k)
                Dυ (S.indicator ρ) υ
                (fun i x => Dυ i x -
                  StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
                (S.indicator ρ -
                  StationaryMFG.Theorems.SimplePower.Banach.mOf q)
                (υ - StationaryMFG.Theorems.SimplePower.Banach.uOf q) := by
  -- Derive `SimplePowerExponentFacts` at the paper exponents (same cast
  -- as the K-form sibling).
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
  -- Closure: bind universal `(ctx, q, hq_K0_W, hVI)` and the test-triple
  -- with the W-form `hWeak_υ` hypothesis.
  intro ctx q hq_K0_W hVI S hS ρ υ Dυ hρ_nn hSρ_memLp hυ_memSob hDυ_memLp
        hWeak_υ
  -- Descend `q ∈ K0_Aepsi_W → q ∈ K0_Aepsi` for the residue supplier.
  have hq_K0 :
      q ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi d
            βBarReal γBarReal :=
    StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi_W_subset_K0_Aepsi
      d βBarReal γBarReal hq_K0_W
  -- Extract the per-query residue dominator bundle.
  set r :=
    residueOf_set q hq_K0 S hS ρ υ Dυ hρ_nn
      hSρ_memLp hυ_memSob hDυ_memLp with hr_def
  -- Build the ε-level operator-continuity `Tendsto` certificate along
  -- `μ_n := S.indicator ρ + 1/(n+1)`. Identical call as the K-form sibling.
  have hCont :=
    StationaryMFG.Theorems.SimplePower.Banach.mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses_of_aestronglyMeasurable
      (ε := paperEpsSeq k)
      (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
      (βBarReal := hpow.β + 1)
      (βBarReal' := (hpow.β + 1) / hpow.β)
      (γBarReal' := (hpow.α * (hpow.β + 1) / hpow.β)
                      / (hpow.α * (hpow.β + 1) / hpow.β - 1))
      hpow hRegH hExp hHat0 hFin hAgree
      Dυ υ (StationaryMFG.Theorems.SimplePower.Banach.uOf q)
      (StationaryMFG.Theorems.SimplePower.Banach.DuOf q)
      (StationaryMFG.Theorems.SimplePower.Banach.mOf q) V S ρ
      hS r.hρ r.hm r.hV r.hυ r.hu r.hDυ r.hDu hρ_nn hSρ_memLp
      r.Gh r.Eh r.hGh_memLp r.hEh_memLp r.hGh_bd r.hEh_bd
      r.Gf r.Ef r.hGf_memLp r.hEf_memLp r.hGf_bd r.hEf_bd
      r.Gm r.Em r.hGm_memLp r.hEm_memLp r.hGm_bd r.hEm_bd
  -- Upgrade via the W-form `hVIeps_set_of_KAepsi_W_VI`.
  exact StationaryMFG.Theorems.SimplePower.Banach.hVIeps_set_of_KAepsi_W_VI
    ctx.auxHypsK q hVI S hS ρ υ Dυ hρ_nn
    hSρ_memLp hυ_memSob hDυ_memLp hWeak_υ hCont

/-! ### `paperSolFor-supplier-set` — `SetTendstoResidueOf` field helpers

The four standalone lemmas below discharge the four "easy" dominator
fields of `SetTendstoResidueOf` directly from the paper hypotheses and
the per-query data. Each yields a `Periodic.MemLpPer` certificate for
the matching envelope; the pointwise a.e. bounds are already supplied
by the `set_perturbation_h{Eh,Gf,Gm,Em}_bd` lemmas in
`Banach/RegularizedSequence.lean`.

The two remaining envelope `MemLpPer` certificates (for the HJB-residual
`Gh` and the flux test factor `Ef`) are deeper analytic objects:

* `Gh` is the explicit envelope
  `(h.C + 1)·(‖Dυ‖^α + 1) + h.C·((|Sρ x|+1)^β + 1) + |υ| + |V|`
  which matches `Hamiltonian.g_dominator_memLp_betaBar'` at
  `μ := |Sρ| + 1` and `C' := h.C + 1`.
* `Ef` is the envelope `h.C·(‖Dυ‖^(α-1) + (|Sρ|+1)^(β-β/α) + 1)·∑|Dυ-Du|`
  whose natural Hölder exponent is `L^{(β+1)/β} = L^{β̄'}`, NOT
  `L^{γ̄}` as the structure expects. Reconciling this requires either
  a tighter test-data hypothesis (e.g. `Dυ ∈ L^∞`) or a rework of the
  consumer `mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses`
  to match the natural exponent.

Both are filed as sibling tasks
`paperSolFor-supplier-set-Gh-memLp` and
`paperSolFor-supplier-set-Ef-memLp` (see
`docs/TASKS/in_flight/paperSolFor-supplier-set.md`). -/

/-- **`hEh_envelope_memLp`** — the HJB pair-test envelope
`|Sρ| + 1 + |m|` lives in `L^{β+1}_per` whenever
`S.indicator ρ ∈ L^{β+1}_per` and `m ∈ L^{β+1}_per`.

Combined with `Banach.set_perturbation_hEh_bd`, this discharges the
`Eh, hEh_memLp, hEh_bd` triple of `SetTendstoResidueOf`. -/
theorem hEh_envelope_memLp_betaBar
    {d : ℕ} {S : Set (Fin d → ℝ)} {ρ m : (Fin d → ℝ) → ℝ}
    {βBarReal : ℝ}
    (hSρ_memLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal)
        (S.indicator ρ))
    (hm_memLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) m) :
    Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal)
      (fun x : (Fin d → ℝ) => |S.indicator ρ x| + 1 + |m x|) := by
  haveI : IsFiniteMeasure
      (MeasureTheory.Measure.restrict MeasureTheory.volume
        (Periodic.UnitCube (d := d))) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ]; simp⟩
  -- `|S.indicator ρ|` is in `L^βBar` via `MemLp.norm`.
  have hSρ_abs : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal)
      (fun x : (Fin d → ℝ) => |S.indicator ρ x|) := by
    have := hSρ_memLp.toMemLp.norm
    have heq : (fun x : (Fin d → ℝ) => ‖S.indicator ρ x‖)
              = (fun x : (Fin d → ℝ) => |S.indicator ρ x|) := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at this
    exact MemLp.toMemLpPer this
  -- `|m|` is in `L^βBar`.
  have hm_abs : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal)
      (fun x : (Fin d → ℝ) => |m x|) := by
    have := hm_memLp.toMemLp.norm
    have heq : (fun x : (Fin d → ℝ) => ‖m x‖)
              = (fun x : (Fin d → ℝ) => |m x|) := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at this
    exact MemLp.toMemLpPer this
  -- Constant `1 : ℝ` is in `L^βBar` on the finite-measure cube.
  have hone : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal)
      (fun _ : Fin d → ℝ => (1 : ℝ)) :=
    MemLp.toMemLpPer (MeasureTheory.memLp_const (1 : ℝ))
  -- Sum: `|Sρ| + 1 + |m|` via `MemLpPer.add` twice (with pointwise rewrites).
  have h1 :
      Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal)
        (fun x : (Fin d → ℝ) => |S.indicator ρ x| + 1) := by
    have := hSρ_abs.add hone
    have heq :
        ((fun x : (Fin d → ℝ) => |S.indicator ρ x|)
            + (fun _ : (Fin d → ℝ) => (1 : ℝ)))
          = (fun x : (Fin d → ℝ) => |S.indicator ρ x| + 1) := by
      funext x; simp [Pi.add_apply]
    rw [heq] at this
    exact this
  have h2 := h1.add hm_abs
  have heq2 :
      ((fun x : (Fin d → ℝ) => |S.indicator ρ x| + 1)
          + (fun x : (Fin d → ℝ) => |m x|))
        = (fun x : (Fin d → ℝ) => |S.indicator ρ x| + 1 + |m x|) := by
    funext x; simp [Pi.add_apply]
  rw [heq2] at h2
  exact h2

/-- **`hGf_envelope_memLp_gammaBarPrime`** — the flux μ-envelope
`|Sρ| + 1` lives in `L^{γ̄'}_per`. **DEPRECATED** under the iter 0617
flux-pair retype `(γ̄', γ̄) → (β̄, β̄')`: callers should now use
`hGf_envelope_memLp_betaBar` (below), which lands in the simpler
`L^{β+1}_per` slot without the `gammaBar'_le_betaBar` descent.

Kept for backwards compatibility / audit. -/
theorem hGf_envelope_memLp_gammaBarPrime
    {d : ℕ} {_V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    {S : Set (Fin d → ℝ)} {ρ : (Fin d → ℝ) → ℝ}
    (hSρ_memLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1))
        (S.indicator ρ)) :
    Periodic.MemLpPer (d := d)
      (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β /
        (hpow.α * (hpow.β + 1) / hpow.β - 1)))
      (fun x : (Fin d → ℝ) => |S.indicator ρ x| + 1) := by
  haveI : IsFiniteMeasure
      (MeasureTheory.Measure.restrict MeasureTheory.volume
        (Periodic.UnitCube (d := d))) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ]; simp⟩
  -- First build the envelope in `L^{β+1}_per`.
  have hSρ_abs : Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1))
      (fun x : (Fin d → ℝ) => |S.indicator ρ x|) := by
    have := hSρ_memLp.toMemLp.norm
    have heq : (fun x : (Fin d → ℝ) => ‖S.indicator ρ x‖)
              = (fun x : (Fin d → ℝ) => |S.indicator ρ x|) := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at this
    exact MemLp.toMemLpPer this
  have hone : Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1))
      (fun _ : Fin d → ℝ => (1 : ℝ)) :=
    MemLp.toMemLpPer (MeasureTheory.memLp_const (1 : ℝ))
  have henv_betaBar :
      Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1))
        (fun x : (Fin d → ℝ) => |S.indicator ρ x| + 1) := by
    have := hSρ_abs.add hone
    have heq :
        ((fun x : (Fin d → ℝ) => |S.indicator ρ x|)
            + (fun _ : (Fin d → ℝ) => (1 : ℝ)))
          = (fun x : (Fin d → ℝ) => |S.indicator ρ x| + 1) := by
      funext x; simp [Pi.add_apply]
    rw [heq] at this
    exact this
  -- Descend `L^{β+1} → L^{γ̄'}` via `γ̄' ≤ β+1` (paper `eq:gamma`).
  have hle : ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β /
        (hpow.α * (hpow.β + 1) / hpow.β - 1))
      ≤ ENNReal.ofReal (hpow.β + 1) :=
    ENNReal.ofReal_le_ofReal
      (Hamiltonian.gammaBar'_le_betaBar hpow.hα hpow.hβ)
  have hβTop : ENNReal.ofReal (hpow.β + 1) ≠ ⊤ := ENNReal.ofReal_ne_top
  exact Periodic.MemLpPer.mono_exponent_finite hle hβTop henv_betaBar

/-- **`hGf_envelope_memLp_betaBar`** — the flux μ-envelope `|Sρ| + 1`
lives in `L^{β+1}_per` whenever `S.indicator ρ ∈ L^{β+1}_per`.

Under the iter 0617 flux-pair retype `(γ̄', γ̄) → (β̄, β̄')`, the `Gf`
field of `SetTendstoResidueOf` lives in `L^{β̄} = L^{β+1}_per`. This
helper is the direct closed-form witness; no exponent descent is
needed. Combined with `Banach.set_perturbation_hGf_bd`, this
discharges the `Gf, hGf_memLp, hGf_bd` triple of
`SetTendstoResidueOf`. -/
theorem hGf_envelope_memLp_betaBar
    {d : ℕ} {S : Set (Fin d → ℝ)} {ρ : (Fin d → ℝ) → ℝ}
    {βBarReal : ℝ}
    (hSρ_memLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal)
        (S.indicator ρ)) :
    Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal)
      (fun x : (Fin d → ℝ) => |S.indicator ρ x| + 1) := by
  haveI : IsFiniteMeasure
      (MeasureTheory.Measure.restrict MeasureTheory.volume
        (Periodic.UnitCube (d := d))) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ]; simp⟩
  have hSρ_abs : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal)
      (fun x : (Fin d → ℝ) => |S.indicator ρ x|) := by
    have := hSρ_memLp.toMemLp.norm
    have heq : (fun x : (Fin d → ℝ) => ‖S.indicator ρ x‖)
              = (fun x : (Fin d → ℝ) => |S.indicator ρ x|) := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at this
    exact MemLp.toMemLpPer this
  have hone : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal)
      (fun _ : Fin d → ℝ => (1 : ℝ)) :=
    MemLp.toMemLpPer (MeasureTheory.memLp_const (1 : ℝ))
  have := hSρ_abs.add hone
  have heq :
      ((fun x : (Fin d → ℝ) => |S.indicator ρ x|)
          + (fun _ : (Fin d → ℝ) => (1 : ℝ)))
        = (fun x : (Fin d → ℝ) => |S.indicator ρ x| + 1) := by
    funext x; simp [Pi.add_apply]
  rw [heq] at this
  exact this

/-- **`hGm_envelope_memLp`** — the mass μ-envelope `|Sρ| + 2` lives in
`L^{β+1}_per` whenever `S.indicator ρ ∈ L^{β+1}_per`.

Combined with `Banach.set_perturbation_hGm_bd`, this discharges the
`Gm, hGm_memLp, hGm_bd` triple of `SetTendstoResidueOf`. -/
theorem hGm_envelope_memLp_betaBar
    {d : ℕ} {S : Set (Fin d → ℝ)} {ρ : (Fin d → ℝ) → ℝ}
    {βBarReal : ℝ}
    (hSρ_memLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal)
        (S.indicator ρ)) :
    Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal)
      (fun x : (Fin d → ℝ) => |S.indicator ρ x| + 2) := by
  haveI : IsFiniteMeasure
      (MeasureTheory.Measure.restrict MeasureTheory.volume
        (Periodic.UnitCube (d := d))) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ]; simp⟩
  have hSρ_abs : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal)
      (fun x : (Fin d → ℝ) => |S.indicator ρ x|) := by
    have := hSρ_memLp.toMemLp.norm
    have heq : (fun x : (Fin d → ℝ) => ‖S.indicator ρ x‖)
              = (fun x : (Fin d → ℝ) => |S.indicator ρ x|) := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at this
    exact MemLp.toMemLpPer this
  have htwo : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal)
      (fun _ : Fin d → ℝ => (2 : ℝ)) :=
    MemLp.toMemLpPer (MeasureTheory.memLp_const (2 : ℝ))
  have h := hSρ_abs.add htwo
  have heq :
      ((fun x : (Fin d → ℝ) => |S.indicator ρ x|)
          + (fun _ : (Fin d → ℝ) => (2 : ℝ)))
        = (fun x : (Fin d → ℝ) => |S.indicator ρ x| + 2) := by
    funext x; simp [Pi.add_apply]
  rw [heq] at h
  exact h

/-- **`hEm_envelope_memLp`** — the mass-pair test envelope `|υ - u|`
lives in `L^{β̄'}_per` whenever `υ, u ∈ L^{γ̄}_per`. The descent from
`L^{γ̄}` to `L^{β̄'}` uses `betaBar'_le_gammaBar` (paper `eq:gamma`,
shaped as `(β+1)/β ≤ α(β+1)/β`).

Combined with `Banach.set_perturbation_hEm_bd`, this discharges the
`Em, hEm_memLp, hEm_bd` triple of `SetTendstoResidueOf`. -/
theorem hEm_envelope_memLp_betaBarPrime
    {d : ℕ} {_V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    {υ u : (Fin d → ℝ) → ℝ}
    (hυ_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) υ)
    (hu_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) u) :
    Periodic.MemLpPer (d := d) (ENNReal.ofReal ((hpow.β + 1) / hpow.β))
      (fun x : (Fin d → ℝ) => |υ x - u x|) := by
  haveI : IsFiniteMeasure
      (MeasureTheory.Measure.restrict MeasureTheory.volume
        (Periodic.UnitCube (d := d))) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ]; simp⟩
  -- `υ - u` lives in `L^γ̄` via subtraction.
  have hsub : Periodic.MemLpPer (d := d)
      (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))
      (fun x : (Fin d → ℝ) => υ x - u x) := by
    have hneg := hu_memLp.const_smul (𝕜 := ℝ) (-1)
    have h := hυ_memLp.add hneg
    have heq :
        (υ + (-1 : ℝ) • u) = (fun x : (Fin d → ℝ) => υ x - u x) := by
      funext x; simp [Pi.add_apply, sub_eq_add_neg]
    rw [heq] at h
    exact h
  -- `|υ - u|` in `L^γ̄`.
  have habs_γ : Periodic.MemLpPer (d := d)
      (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))
      (fun x : (Fin d → ℝ) => |υ x - u x|) := by
    have := hsub.toMemLp.norm
    have heq : (fun x : (Fin d → ℝ) => ‖υ x - u x‖)
              = (fun x : (Fin d → ℝ) => |υ x - u x|) := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at this
    exact MemLp.toMemLpPer this
  -- Descend `L^γ̄ → L^{β̄'}` via `(β+1)/β ≤ α(β+1)/β` (paper `eq:gamma`).
  have hα_ge_one : 1 ≤ hpow.α := le_of_lt hpow.hα
  have hle_real : (hpow.β + 1) / hpow.β
      ≤ hpow.α * (hpow.β + 1) / hpow.β := by
    rw [div_le_div_iff_of_pos_right hpow.hβ]
    have : (1 : ℝ) * (hpow.β + 1) ≤ hpow.α * (hpow.β + 1) :=
      mul_le_mul_of_nonneg_right hα_ge_one
        (by linarith [hpow.hβ] : (0 : ℝ) ≤ hpow.β + 1)
    simpa using this
  have hle : ENNReal.ofReal ((hpow.β + 1) / hpow.β)
      ≤ ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β) :=
    ENNReal.ofReal_le_ofReal hle_real
  have hγTop : ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  exact Periodic.MemLpPer.mono_exponent_finite hle hγTop habs_γ

/-- **`hGh_envelope_memLp`** — the HJB residual envelope
`(h.C+1)·(‖Dυ‖^α + 1) + h.C·((|Sρ x|+1)^β + 1) + |υ x| + |V x|` lives
in `L^{β̄'} = L^{(β+1)/β}_per` whenever the inputs satisfy the
expected `MemLpPer` integrabilities.

The proof is a direct application of
`Hamiltonian.g_dominator_memLp_betaBar'` at the choices
`μ := |Sρ| + 1`, `C' := h.C + 1`. The hypothesis
`μ ∈ L^{β+1}_per` follows from `|Sρ| ∈ L^{β+1}_per` + constant.

Combined with `Banach.set_perturbation_hGh_bd`, this discharges the
`Gh, hGh_memLp, hGh_bd` triple of `SetTendstoResidueOf`. -/
theorem hGh_envelope_memLp_betaBarPrime
    {d : ℕ} {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    {S : Set (Fin d → ℝ)} {ρ υ : (Fin d → ℝ) → ℝ}
    {Dυ : Fin d → (Fin d → ℝ) → ℝ}
    (hSρ_memLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1))
        (S.indicator ρ))
    (hυ_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) υ)
    (hDυ_memLp : ∀ i, Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) (Dυ i))
    (hV_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) V) :
    Periodic.MemLpPer (d := d) (ENNReal.ofReal ((hpow.β + 1) / hpow.β))
      (fun x : (Fin d → ℝ) =>
        (hpow.C + 1) * (‖fun i => Dυ i x‖ ^ hpow.α + 1)
          + hpow.C * ((|S.indicator ρ x| + 1) ^ hpow.β + 1)
          + |υ x| + |V x|) := by
  haveI : IsFiniteMeasure
      (MeasureTheory.Measure.restrict MeasureTheory.volume
        (Periodic.UnitCube (d := d))) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ]; simp⟩
  -- Build `μ := |S.indicator ρ| + 1` in `L^{β+1}_per`.
  have hSρ_abs : Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1))
      (fun x : (Fin d → ℝ) => |S.indicator ρ x|) := by
    have := hSρ_memLp.toMemLp.norm
    have heq : (fun x : (Fin d → ℝ) => ‖S.indicator ρ x‖)
              = (fun x : (Fin d → ℝ) => |S.indicator ρ x|) := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at this
    exact MemLp.toMemLpPer this
  have hone : Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1))
      (fun _ : Fin d → ℝ => (1 : ℝ)) :=
    MemLp.toMemLpPer (MeasureTheory.memLp_const (1 : ℝ))
  have hμ_memLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1))
      (fun x : (Fin d → ℝ) => |S.indicator ρ x| + 1) := by
    have := hSρ_abs.add hone
    have heq :
        ((fun x : (Fin d → ℝ) => |S.indicator ρ x|)
            + (fun _ : (Fin d → ℝ) => (1 : ℝ)))
          = (fun x : (Fin d → ℝ) => |S.indicator ρ x| + 1) := by
      funext x; simp [Pi.add_apply]
    rw [heq] at this
    exact this
  -- Positivity of `C' := h.C + 1`.
  have hC'_pos : (0 : ℝ) < hpow.C + 1 := by linarith [hpow.hC]
  -- Apply `g_dominator_memLp_betaBar'` at `μ := |Sρ| + 1`, `C' := h.C + 1`.
  exact Hamiltonian.g_dominator_memLp_betaBar' hpow V υ
    (fun x => |S.indicator ρ x| + 1) Dυ
    hμ_memLp hυ_memLp hDυ_memLp hV_memLp hC'_pos

/-! ### `paperSolFor-supplier-set-Ef-envelope-betaBarPrime` — closed-form
`Ef ∈ L^β̄'` envelope for the set-supplier flux test factor.

The closed-form envelope from `set_perturbation_hEf_bd` is

```
Ef x := hpow.C * (‖fun i => Dυ i x‖^(α-1) + (|Sρ x|+1)^(β-β/α) + 1)
        * ∑ i, |Dυ i x - Du i x|
```

Distributing the outer multiplication gives three Hölder products:

* `‖Dυ‖^(α-1) · Δ` with Hölder triple `(γ̄/(α-1), γ̄, β̄')`, where
  `Δ x := ∑ i, |Dυ i x - Du i x|`. Identity:
  `(α-1)/γ̄ + 1/γ̄ = α/γ̄ = β/(β+1) = 1/β̄'`.
* `(|Sρ|+1)^(β-β/α) · Δ` with Hölder triple `(β̄/(β-β/α), γ̄, β̄')`.
  Identity: `(β-β/α)/(β+1) + β/(α(β+1)) = β(α-1+1)/(α(β+1)) = 1/β̄'`.
* `1 · Δ = Δ` lifts from `L^γ̄` to `L^β̄'` via `mono_exponent_finite`
  (`β̄' ≤ γ̄`).

Each piece lives in `L^β̄'`, so the sum and outer constant multiply
keep us in `L^β̄'`. Combined with `Banach.set_perturbation_hEf_bd`,
this discharges the `Ef, hEf_memLp, hEf_bd` triple of
`SetTendstoResidueOf` and lets `setTendstoResidueOf_of_paperHypotheses`
ship without the `_with_Ef` partial-input suffix. -/

/-- **Hölder triple `(γ̄/(α-1), γ̄, β̄')` on `ℝ`.** For `α > 1, β > 0`,
the real-valued exponents `(γ̄/(α-1), γ̄, β̄')` form a Hölder triple
with `γ̄ = α(β+1)/β`, `β̄' = (β+1)/β`. The identity is
`(α-1)/γ̄ + 1/γ̄ = α/γ̄ = β/(β+1) = 1/β̄'`. -/
private theorem holderTriple_gammaBarOverAlphaMinus1_gammaBar_betaBar'
    {α β : ℝ} (hα : 1 < α) (hβ : 0 < β) :
    Real.HolderTriple (α * (β + 1) / β / (α - 1))
      (α * (β + 1) / β)
      ((β + 1) / β) := by
  have hαpos : 0 < α := lt_trans one_pos hα
  have hαm1_pos : 0 < α - 1 := by linarith
  have hbb_pos : 0 < β + 1 := by linarith
  have hγb_pos : 0 < α * (β + 1) / β := by positivity
  have hγb_quot_pos : 0 < α * (β + 1) / β / (α - 1) :=
    div_pos hγb_pos hαm1_pos
  refine ⟨?_, hγb_quot_pos, hγb_pos⟩
  have hβne : β ≠ 0 := hβ.ne'
  have hαne : α ≠ 0 := hαpos.ne'
  have hαm1_ne : α - 1 ≠ 0 := hαm1_pos.ne'
  have hbb_ne : β + 1 ≠ 0 := hbb_pos.ne'
  have hγb_ne : α * (β + 1) / β ≠ 0 := hγb_pos.ne'
  field_simp
  ring

/-- **Hölder triple `(β̄/(β - β/α), γ̄, β̄')` on `ℝ`.** For `α > 1, β > 0`,
the exponents `(β̄/(β - β/α), γ̄, β̄')` form a Hölder triple with
`β̄ = β+1`. The identity is
`(β-β/α)/(β+1) + β/(α(β+1)) = β/(β+1) = 1/β̄'`. -/
private theorem holderTriple_betaBarOverBetaMinusBetaOverAlpha_gammaBar_betaBar'
    {α β : ℝ} (hα : 1 < α) (hβ : 0 < β) :
    Real.HolderTriple ((β + 1) / (β - β / α))
      (α * (β + 1) / β)
      ((β + 1) / β) := by
  have hαpos : 0 < α := lt_trans one_pos hα
  have hαm1_pos : 0 < α - 1 := by linarith
  have hbb_pos : 0 < β + 1 := by linarith
  have hγb_pos : 0 < α * (β + 1) / β := by positivity
  have hβ_div_α_pos : 0 < β / α := div_pos hβ hαpos
  have hβ_minus_pos : 0 < β - β / α := by
    have h1 : β / α < β := by
      rw [div_lt_iff₀ hαpos]
      have : β * 1 < β * α := by
        have hl : (1 : ℝ) < α := hα
        nlinarith
      linarith
    linarith
  have hr_pos : 0 < (β + 1) / (β - β / α) :=
    div_pos hbb_pos hβ_minus_pos
  refine ⟨?_, hr_pos, hγb_pos⟩
  have hβne : β ≠ 0 := hβ.ne'
  have hαne : α ≠ 0 := hαpos.ne'
  have hbb_ne : β + 1 ≠ 0 := hbb_pos.ne'
  have hβmβα_ne : β - β / α ≠ 0 := hβ_minus_pos.ne'
  have hγb_ne : α * (β + 1) / β ≠ 0 := hγb_pos.ne'
  field_simp
  ring

/-- **`hEf_envelope_memLp_betaBarPrime`** — the flux test-factor envelope
```
Ef x := hpow.C * (‖fun i => Dυ i x‖^(α-1) + (|Sρ x|+1)^(β-β/α) + 1)
        * ∑ i, |Dυ i x - Du i x|
```
lives in `L^{β̄'} = L^{(β+1)/β}_per` whenever
`S.indicator ρ ∈ L^{β+1}_per` and `Dυ i, Du i ∈ L^{γ̄}_per` for each `i`.

This is the exact closed-form upper bound proven in
`Banach.set_perturbation_hEf_bd`. Combined with that pointwise bound, it
discharges the `Ef, hEf_memLp, hEf_bd` triple of `SetTendstoResidueOf`
without needing `Ef` as an authorised parameter.

Proof structure: distribute the outer product into three Hölder terms,
each in `L^β̄'`:
* `‖Dυ‖^(α-1) · Δ` via `MemLp.mul'` at Hölder triple `(γ̄/(α-1), γ̄, β̄')`;
* `(|Sρ|+1)^(β-β/α) · Δ` via `MemLp.mul'` at `(β̄/(β-β/α), γ̄, β̄')`;
* `1 · Δ = Δ` via `mono_exponent_finite` (β̄' ≤ γ̄).
Here `Δ x := ∑ i, |Dυ i x - Du i x|`. -/
theorem hEf_envelope_memLp_betaBarPrime
    {d : ℕ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    {S : Set (Fin d → ℝ)} {ρ : (Fin d → ℝ) → ℝ}
    {Dυ Du : Fin d → (Fin d → ℝ) → ℝ}
    (hSρ_memLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1))
        (S.indicator ρ))
    (hDυ_memLp : ∀ i, Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) (Dυ i))
    (hDu_memLp : ∀ i, Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) (Du i)) :
    Periodic.MemLpPer (d := d) (ENNReal.ofReal ((hpow.β + 1) / hpow.β))
      (fun x : (Fin d → ℝ) =>
        hpow.C * (‖fun i => Dυ i x‖ ^ (hpow.α - 1)
                  + (|S.indicator ρ x| + 1) ^ (hpow.β - hpow.β / hpow.α)
                  + 1)
            * ∑ i, |Dυ i x - Du i x|) := by
  -- Standing positivity / nonnegativity facts.
  have hαpos : 0 < hpow.α := lt_trans one_pos hpow.hα
  have hαm1_pos : 0 < hpow.α - 1 := by linarith [hpow.hα]
  have hbb_pos : 0 < hpow.β + 1 := by linarith [hpow.hβ]
  have hβ_pos : 0 < hpow.β := hpow.hβ
  have hγb_pos : 0 < hpow.α * (hpow.β + 1) / hpow.β :=
    div_pos (mul_pos hαpos hbb_pos) hβ_pos
  have hβ_div_α_pos : 0 < hpow.β / hpow.α := div_pos hβ_pos hαpos
  have hβmβα_pos : 0 < hpow.β - hpow.β / hpow.α := by
    have h1 : hpow.β / hpow.α < hpow.β := by
      rw [div_lt_iff₀ hαpos]
      have : hpow.β * 1 < hpow.β * hpow.α := by
        nlinarith [hpow.hα, hpow.hβ]
      linarith
    linarith
  have hβb'_pos : 0 < (hpow.β + 1) / hpow.β := div_pos hbb_pos hβ_pos
  -- Finite-measure on the unit cube.
  haveI : IsFiniteMeasure
      (MeasureTheory.Measure.restrict MeasureTheory.volume
        (Periodic.UnitCube (d := d))) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ]; simp⟩
  -- Notation for the exponents (as ℝ≥0∞).
  set βBarE : ℝ≥0∞ := ENNReal.ofReal (hpow.β + 1) with hβBarE_def
  set γBarE : ℝ≥0∞ := ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)
    with hγBarE_def
  set βBar'E : ℝ≥0∞ := ENNReal.ofReal ((hpow.β + 1) / hpow.β)
    with hβBar'E_def
  -- ============================================================
  -- Step 1: build Δ := fun x => ∑ i, |Dυ i x - Du i x| ∈ L^γ̄.
  -- ============================================================
  have hDiff_memLp : ∀ i, Periodic.MemLpPer (d := d) γBarE
      (fun x : (Fin d → ℝ) => Dυ i x - Du i x) := by
    intro i
    have hneg := (hDu_memLp i).const_smul (𝕜 := ℝ) (-1)
    have h := (hDυ_memLp i).add hneg
    have heq :
        ((Dυ i) + (-1 : ℝ) • (Du i))
          = (fun x : (Fin d → ℝ) => Dυ i x - Du i x) := by
      funext x; simp [Pi.add_apply, sub_eq_add_neg]
    rw [heq] at h
    exact h
  have hDiff_abs_memLp : ∀ i, Periodic.MemLpPer (d := d) γBarE
      (fun x : (Fin d → ℝ) => |Dυ i x - Du i x|) := by
    intro i
    have := (hDiff_memLp i).toMemLp.norm
    have heq : (fun x : (Fin d → ℝ) => ‖Dυ i x - Du i x‖)
              = (fun x : (Fin d → ℝ) => |Dυ i x - Du i x|) := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at this
    exact MemLp.toMemLpPer this
  have hΔ_memLp : Periodic.MemLpPer (d := d) γBarE
      (fun x : (Fin d → ℝ) => ∑ i, |Dυ i x - Du i x|) := by
    have hsum :
        MemLp (fun x : (Fin d → ℝ) =>
            ∑ i : Fin d, (fun x => |Dυ i x - Du i x|) x) γBarE
          (MeasureTheory.Measure.restrict MeasureTheory.volume
            (Periodic.UnitCube d)) :=
      MeasureTheory.memLp_finset_sum (Finset.univ : Finset (Fin d))
        (fun i _ => (hDiff_abs_memLp i).toMemLp)
    exact MemLp.toMemLpPer hsum
  -- ============================================================
  -- Step 2: T1 := ‖fun i => Dυ i ·‖^(α-1) ∈ L^(γ̄/(α-1)).
  -- ============================================================
  -- Vector-valued `Dυ_vec` in `L^γ̄`.
  have hDυ_vec : Periodic.MemLpPer (d := d) γBarE
      (fun x : (Fin d → ℝ) => fun i : Fin d => Dυ i x) := by
    -- Build from per-coordinate via the sum-of-abs dominator.
    set Dom : (Fin d → ℝ) → ℝ := fun x => ∑ i : Fin d, |Dυ i x|
      with hDom_def
    have habs_memLp : ∀ i, Periodic.MemLpPer (d := d) γBarE
        (fun x => |Dυ i x|) := by
      intro i
      have := (hDυ_memLp i).toMemLp.norm
      have heq : (fun x : (Fin d → ℝ) => ‖Dυ i x‖)
                = (fun x : (Fin d → ℝ) => |Dυ i x|) := by
        funext x; exact Real.norm_eq_abs _
      rw [heq] at this
      exact MemLp.toMemLpPer this
    have hDom_memLp : Periodic.MemLpPer (d := d) γBarE Dom := by
      have hsum :
          MemLp (fun x : (Fin d → ℝ) =>
              ∑ i : Fin d, (fun x => |Dυ i x|) x) γBarE
            (MeasureTheory.Measure.restrict MeasureTheory.volume
              (Periodic.UnitCube d)) :=
        MeasureTheory.memLp_finset_sum (Finset.univ : Finset (Fin d))
          (fun i _ => (habs_memLp i).toMemLp)
      exact MemLp.toMemLpPer hsum
    have hbound :
        ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume
              (Periodic.UnitCube d)),
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
        AEStronglyMeasurable
          (fun x : (Fin d → ℝ) => fun i : Fin d => Dυ i x)
          (MeasureTheory.Measure.restrict MeasureTheory.volume
            (Periodic.UnitCube d)) := by
      have hAEm : AEMeasurable
          (fun x : (Fin d → ℝ) => fun i : Fin d => Dυ i x)
          (MeasureTheory.Measure.restrict MeasureTheory.volume
            (Periodic.UnitCube d)) :=
        aemeasurable_pi_iff.mpr fun i =>
          (hDυ_memLp i).aestronglyMeasurable.aemeasurable
      exact hAEm.aestronglyMeasurable
    exact MemLp.toMemLpPer
      (MeasureTheory.MemLp.of_le_mul hDom_memLp.toMemLp hmeas hbound)
  -- `‖Dυ_vec‖^(α-1) ∈ L^(γ̄/(α-1))` via `MemLp.norm_rpow_div`.
  set qE1 : ℝ≥0∞ := ENNReal.ofReal (hpow.α - 1) with hqE1_def
  have hqE1_top : qE1 ≠ ⊤ := by
    rw [hqE1_def]; exact ENNReal.ofReal_ne_top
  have hqE1_toReal : qE1.toReal = hpow.α - 1 := by
    rw [hqE1_def]; exact ENNReal.toReal_ofReal hαm1_pos.le
  have hT1_raw :
      MemLp (fun x : (Fin d → ℝ) =>
              ‖(fun j : Fin d => Dυ j x)‖ ^ qE1.toReal)
            (γBarE / qE1)
            (MeasureTheory.Measure.restrict MeasureTheory.volume
              (Periodic.UnitCube d)) :=
    MemLp.norm_rpow_div hDυ_vec.toMemLp qE1
  -- Identify `γBarE / qE1 = ENNReal.ofReal (γ̄/(α-1))`.
  have hdiv1 :
      γBarE / qE1
        = ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β / (hpow.α - 1)) := by
    rw [hγBarE_def, hqE1_def, ← ENNReal.ofReal_div_of_pos hαm1_pos]
  have hT1_memLp : Periodic.MemLpPer (d := d)
      (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β / (hpow.α - 1)))
      (fun x : (Fin d → ℝ) => ‖(fun j : Fin d => Dυ j x)‖ ^ (hpow.α - 1)) := by
    have heq :
        (fun x : (Fin d → ℝ) =>
          ‖(fun j : Fin d => Dυ j x)‖ ^ (hpow.α - 1))
        = (fun x : (Fin d → ℝ) =>
          ‖(fun j : Fin d => Dυ j x)‖ ^ qE1.toReal) := by
      funext x; rw [hqE1_toReal]
    rw [heq]
    have := MemLp.toMemLpPer hT1_raw
    rw [hdiv1] at this
    exact this
  -- ============================================================
  -- Step 3: T2 := (|Sρ|+1)^(β-β/α) ∈ L^(β̄/(β-β/α)).
  -- ============================================================
  -- Build `|S.indicator ρ| + 1 ∈ L^βBar`.
  have hSρ_abs : Periodic.MemLpPer (d := d) βBarE
      (fun x : (Fin d → ℝ) => |S.indicator ρ x|) := by
    have := hSρ_memLp.toMemLp.norm
    have heq : (fun x : (Fin d → ℝ) => ‖S.indicator ρ x‖)
              = (fun x : (Fin d → ℝ) => |S.indicator ρ x|) := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at this
    exact MemLp.toMemLpPer this
  have hone_βBar : Periodic.MemLpPer (d := d) βBarE
      (fun _ : Fin d → ℝ => (1 : ℝ)) :=
    MemLp.toMemLpPer (MeasureTheory.memLp_const (1 : ℝ))
  have hSρEnv_memLp : Periodic.MemLpPer (d := d) βBarE
      (fun x : (Fin d → ℝ) => |S.indicator ρ x| + 1) := by
    have := hSρ_abs.add hone_βBar
    have heq :
        ((fun x : (Fin d → ℝ) => |S.indicator ρ x|)
            + (fun _ : (Fin d → ℝ) => (1 : ℝ)))
          = (fun x : (Fin d → ℝ) => |S.indicator ρ x| + 1) := by
      funext x; simp [Pi.add_apply]
    rw [heq] at this
    exact this
  -- `(|Sρ|+1)^(β-β/α) ∈ L^(β̄/(β-β/α))` via `MemLp.norm_rpow_div`.
  set qE2 : ℝ≥0∞ := ENNReal.ofReal (hpow.β - hpow.β / hpow.α) with hqE2_def
  have hqE2_top : qE2 ≠ ⊤ := by
    rw [hqE2_def]; exact ENNReal.ofReal_ne_top
  have hqE2_toReal : qE2.toReal = hpow.β - hpow.β / hpow.α := by
    rw [hqE2_def]; exact ENNReal.toReal_ofReal hβmβα_pos.le
  -- The envelope `|Sρ|+1` is nonneg so `‖·‖ = ·`.
  have hT2_raw :
      MemLp (fun x : (Fin d → ℝ) =>
              ‖|S.indicator ρ x| + 1‖ ^ qE2.toReal)
            (βBarE / qE2)
            (MeasureTheory.Measure.restrict MeasureTheory.volume
              (Periodic.UnitCube d)) :=
    MemLp.norm_rpow_div hSρEnv_memLp.toMemLp qE2
  -- Identify `βBarE / qE2 = ENNReal.ofReal ((β+1)/(β-β/α))`.
  have hdiv2 :
      βBarE / qE2 = ENNReal.ofReal ((hpow.β + 1) / (hpow.β - hpow.β / hpow.α)) := by
    rw [hβBarE_def, hqE2_def, ← ENNReal.ofReal_div_of_pos hβmβα_pos]
  -- Rewrite `‖|Sρ|+1‖ = |Sρ|+1` and the exponent toReal.
  have hT2_memLp : Periodic.MemLpPer (d := d)
      (ENNReal.ofReal ((hpow.β + 1) / (hpow.β - hpow.β / hpow.α)))
      (fun x : (Fin d → ℝ) =>
        (|S.indicator ρ x| + 1) ^ (hpow.β - hpow.β / hpow.α)) := by
    have heq :
        (fun x : (Fin d → ℝ) =>
            (|S.indicator ρ x| + 1) ^ (hpow.β - hpow.β / hpow.α))
        = (fun x : (Fin d → ℝ) =>
            ‖|S.indicator ρ x| + 1‖ ^ qE2.toReal) := by
      funext x
      have hnn : 0 ≤ |S.indicator ρ x| + 1 := by
        have := abs_nonneg (S.indicator ρ x); linarith
      rw [Real.norm_eq_abs, abs_of_nonneg hnn, hqE2_toReal]
    rw [heq]
    have := MemLp.toMemLpPer hT2_raw
    rw [hdiv2] at this
    exact this
  -- ============================================================
  -- Step 4: T3 := Δ embedded in L^β̄'.
  -- ============================================================
  have hβBar'_le_γBar : βBar'E ≤ γBarE := by
    rw [hβBar'E_def, hγBarE_def]
    apply ENNReal.ofReal_le_ofReal
    rw [div_le_div_iff_of_pos_right hβ_pos]
    have h1 : (1 : ℝ) * (hpow.β + 1) ≤ hpow.α * (hpow.β + 1) :=
      mul_le_mul_of_nonneg_right hpow.hα.le hbb_pos.le
    linarith
  have hγBar_top : γBarE ≠ ⊤ := by
    rw [hγBarE_def]; exact ENNReal.ofReal_ne_top
  have hΔ_βBar' : Periodic.MemLpPer (d := d) βBar'E
      (fun x : (Fin d → ℝ) => ∑ i, |Dυ i x - Du i x|) :=
    Periodic.MemLpPer.mono_exponent_finite hβBar'_le_γBar hγBar_top hΔ_memLp
  -- ============================================================
  -- Step 5: Combine via Hölder products + sum.
  -- ============================================================
  -- Hölder triple 1: `(γ̄/(α-1), γ̄, β̄')`.
  have hHT1_real :
      Real.HolderTriple (hpow.α * (hpow.β + 1) / hpow.β / (hpow.α - 1))
        (hpow.α * (hpow.β + 1) / hpow.β)
        ((hpow.β + 1) / hpow.β) :=
    holderTriple_gammaBarOverAlphaMinus1_gammaBar_betaBar' hpow.hα hpow.hβ
  haveI hHT1_enn :
      ENNReal.HolderTriple
        (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β / (hpow.α - 1)))
        γBarE βBar'E := by
    have := hHT1_real.ennrealOfReal
    rw [hγBarE_def, hβBar'E_def]
    exact this
  -- Hölder triple 2: `(β̄/(β-β/α), γ̄, β̄')`.
  have hHT2_real :
      Real.HolderTriple ((hpow.β + 1) / (hpow.β - hpow.β / hpow.α))
        (hpow.α * (hpow.β + 1) / hpow.β)
        ((hpow.β + 1) / hpow.β) :=
    holderTriple_betaBarOverBetaMinusBetaOverAlpha_gammaBar_betaBar'
      hpow.hα hpow.hβ
  haveI hHT2_enn :
      ENNReal.HolderTriple
        (ENNReal.ofReal ((hpow.β + 1) / (hpow.β - hpow.β / hpow.α)))
        γBarE βBar'E := by
    have := hHT2_real.ennrealOfReal
    rw [hγBarE_def, hβBar'E_def]
    exact this
  -- Apply `MemLp.mul'`. Order: `φ * f` where φ-exponent first.
  -- Product 1: T1·Δ ∈ L^β̄'.
  have hProd1 :
      Periodic.MemLpPer (d := d) βBar'E
        (fun x : (Fin d → ℝ) =>
          ‖(fun j : Fin d => Dυ j x)‖ ^ (hpow.α - 1)
            * ∑ i, |Dυ i x - Du i x|) := by
    have h := (hT1_memLp.toMemLp).fun_mul
      (p := ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β / (hpow.α - 1))) (q := γBarE) (r := βBar'E) hΔ_memLp.toMemLp
    exact MemLp.toMemLpPer h
  -- Product 2: T2·Δ ∈ L^β̄'.
  have hProd2 :
      Periodic.MemLpPer (d := d) βBar'E
        (fun x : (Fin d → ℝ) =>
          (|S.indicator ρ x| + 1) ^ (hpow.β - hpow.β / hpow.α)
            * ∑ i, |Dυ i x - Du i x|) := by
    have h := (hT2_memLp.toMemLp).fun_mul
      (p := ENNReal.ofReal ((hpow.β + 1) / (hpow.β - hpow.β / hpow.α))) (q := γBarE) (r := βBar'E) hΔ_memLp.toMemLp
    exact MemLp.toMemLpPer h
  -- Step 5b: sum the three products.
  have hSum12 :
      Periodic.MemLpPer (d := d) βBar'E
        (fun x : (Fin d → ℝ) =>
          ‖(fun j : Fin d => Dυ j x)‖ ^ (hpow.α - 1)
            * ∑ i, |Dυ i x - Du i x|
          + (|S.indicator ρ x| + 1) ^ (hpow.β - hpow.β / hpow.α)
            * ∑ i, |Dυ i x - Du i x|) := by
    have := hProd1.add hProd2
    have heq :
        ((fun x : (Fin d → ℝ) =>
            ‖(fun j : Fin d => Dυ j x)‖ ^ (hpow.α - 1)
              * ∑ i, |Dυ i x - Du i x|)
          + (fun x : (Fin d → ℝ) =>
              (|S.indicator ρ x| + 1) ^ (hpow.β - hpow.β / hpow.α)
              * ∑ i, |Dυ i x - Du i x|))
        = (fun x : (Fin d → ℝ) =>
            ‖(fun j : Fin d => Dυ j x)‖ ^ (hpow.α - 1)
              * ∑ i, |Dυ i x - Du i x|
            + (|S.indicator ρ x| + 1) ^ (hpow.β - hpow.β / hpow.α)
              * ∑ i, |Dυ i x - Du i x|) := by
      funext x; simp [Pi.add_apply]
    rw [heq] at this
    exact this
  have hSum123 :
      Periodic.MemLpPer (d := d) βBar'E
        (fun x : (Fin d → ℝ) =>
          ‖(fun j : Fin d => Dυ j x)‖ ^ (hpow.α - 1)
            * ∑ i, |Dυ i x - Du i x|
          + (|S.indicator ρ x| + 1) ^ (hpow.β - hpow.β / hpow.α)
            * ∑ i, |Dυ i x - Du i x|
          + ∑ i, |Dυ i x - Du i x|) := by
    have := hSum12.add hΔ_βBar'
    have heq :
        ((fun x : (Fin d → ℝ) =>
            ‖(fun j : Fin d => Dυ j x)‖ ^ (hpow.α - 1)
              * ∑ i, |Dυ i x - Du i x|
            + (|S.indicator ρ x| + 1) ^ (hpow.β - hpow.β / hpow.α)
              * ∑ i, |Dυ i x - Du i x|)
          + (fun x : (Fin d → ℝ) => ∑ i, |Dυ i x - Du i x|))
        = (fun x : (Fin d → ℝ) =>
            ‖(fun j : Fin d => Dυ j x)‖ ^ (hpow.α - 1)
              * ∑ i, |Dυ i x - Du i x|
            + (|S.indicator ρ x| + 1) ^ (hpow.β - hpow.β / hpow.α)
              * ∑ i, |Dυ i x - Du i x|
            + ∑ i, |Dυ i x - Du i x|) := by
      funext x; simp [Pi.add_apply]
    rw [heq] at this
    exact this
  -- Step 5c: rewrite the explicit factored Ef in terms of the sum.
  -- Pointwise identity:
  --   `C * (a + b + 1) * Δ = C * a · Δ + C * b · Δ + C * 1 · Δ`
  --   which equals `C * (a·Δ + b·Δ + Δ)`.
  have hFinal :
      Periodic.MemLpPer (d := d) βBar'E
        (fun x : (Fin d → ℝ) =>
          hpow.C * (‖fun j : Fin d => Dυ j x‖ ^ (hpow.α - 1)
                    + (|S.indicator ρ x| + 1) ^ (hpow.β - hpow.β / hpow.α)
                    + 1)
              * ∑ i, |Dυ i x - Du i x|) := by
    have hSmul := hSum123.const_smul (𝕜 := ℝ) hpow.C
    have heq :
        ((hpow.C : ℝ) •
          (fun x : (Fin d → ℝ) =>
            ‖(fun j : Fin d => Dυ j x)‖ ^ (hpow.α - 1)
              * ∑ i, |Dυ i x - Du i x|
            + (|S.indicator ρ x| + 1) ^ (hpow.β - hpow.β / hpow.α)
              * ∑ i, |Dυ i x - Du i x|
            + ∑ i, |Dυ i x - Du i x|))
        = (fun x : (Fin d → ℝ) =>
            hpow.C * (‖fun j : Fin d => Dυ j x‖ ^ (hpow.α - 1)
                      + (|S.indicator ρ x| + 1) ^ (hpow.β - hpow.β / hpow.α)
                      + 1)
                * ∑ i, |Dυ i x - Du i x|) := by
      funext x
      simp [Pi.smul_apply, smul_eq_mul, add_mul, mul_add, one_mul, mul_assoc]
    rw [heq] at hSmul
    exact hSmul
  exact hFinal

/-! ### Bare-exponent envelope `MemLpPer` helpers (EXPERT RULING #4 retype,
D2c-2e-1 child A).

Bare-exponent siblings of `hGh/hEf/hEm_envelope_memLp_*` that take the
growth exponents `(β α C : ℝ)` + positivity `(hα : 1 < α) (hβ : 0 < β)`
[and `(hC : 0 < C)` where the constant `C` appears] INSTEAD of
`hpow : HypothesisPowerGrowth H' DpH`. The strict versions consume `hpow`
ONLY through `hpow.α/β/C` (values) and `hpow.hα/hβ/hC` (positivity) — never
through `RegularityH` or the analytic `upper/lower/DpH_upper/lagr` fields. So
these envelope `MemLpPer` dominator facts are a.e./value-level and need no
strict bundle; they are exactly the dominator fields the T3 `setTendstoResidue`
envelope consumes. -/

/-- Bare-exponent sibling of `hGh_envelope_memLp_betaBarPrime`.
Routes through `Hamiltonian.g_dominator_memLp_betaBar'_bare`. -/
theorem hGh_envelope_memLp_betaBarPrime_bare
    {d : ℕ} {V : (Fin d → ℝ) → ℝ}
    {β α C : ℝ} (hα : 1 < α) (hβ : 0 < β) (hC : 0 < C)
    {S : Set (Fin d → ℝ)} {ρ υ : (Fin d → ℝ) → ℝ}
    {Dυ : Fin d → (Fin d → ℝ) → ℝ}
    (hSρ_memLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal (β + 1))
        (S.indicator ρ))
    (hυ_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (α * (β + 1) / β)) υ)
    (hDυ_memLp : ∀ i, Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (α * (β + 1) / β)) (Dυ i))
    (hV_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal ((β + 1) / β)) V) :
    Periodic.MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
      (fun x : (Fin d → ℝ) =>
        (C + 1) * (‖fun i => Dυ i x‖ ^ α + 1)
          + C * ((|S.indicator ρ x| + 1) ^ β + 1)
          + |υ x| + |V x|) := by
  haveI : IsFiniteMeasure
      (MeasureTheory.Measure.restrict MeasureTheory.volume
        (Periodic.UnitCube (d := d))) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ]; simp⟩
  have hSρ_abs : Periodic.MemLpPer (d := d) (ENNReal.ofReal (β + 1))
      (fun x : (Fin d → ℝ) => |S.indicator ρ x|) := by
    have := hSρ_memLp.toMemLp.norm
    have heq : (fun x : (Fin d → ℝ) => ‖S.indicator ρ x‖)
              = (fun x : (Fin d → ℝ) => |S.indicator ρ x|) := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at this
    exact MemLp.toMemLpPer this
  have hone : Periodic.MemLpPer (d := d) (ENNReal.ofReal (β + 1))
      (fun _ : Fin d → ℝ => (1 : ℝ)) :=
    MemLp.toMemLpPer (MeasureTheory.memLp_const (1 : ℝ))
  have hμ_memLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal (β + 1))
      (fun x : (Fin d → ℝ) => |S.indicator ρ x| + 1) := by
    have := hSρ_abs.add hone
    have heq :
        ((fun x : (Fin d → ℝ) => |S.indicator ρ x|)
            + (fun _ : (Fin d → ℝ) => (1 : ℝ)))
          = (fun x : (Fin d → ℝ) => |S.indicator ρ x| + 1) := by
      funext x; simp [Pi.add_apply]
    rw [heq] at this
    exact this
  have hC'_pos : (0 : ℝ) < C + 1 := by linarith
  exact Hamiltonian.g_dominator_memLp_betaBar'_bare (β := β) (α := α) (C := C)
    hα hβ V υ
    (fun x => |S.indicator ρ x| + 1) Dυ
    hμ_memLp hυ_memLp hDυ_memLp hV_memLp hC'_pos

/-- Bare-exponent sibling of `hEf_envelope_memLp_betaBarPrime`. -/
theorem hEf_envelope_memLp_betaBarPrime_bare
    {d : ℕ}
    {β α C : ℝ} (hα : 1 < α) (hβ : 0 < β)
    {S : Set (Fin d → ℝ)} {ρ : (Fin d → ℝ) → ℝ}
    {Dυ Du : Fin d → (Fin d → ℝ) → ℝ}
    (hSρ_memLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal (β + 1))
        (S.indicator ρ))
    (hDυ_memLp : ∀ i, Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (α * (β + 1) / β)) (Dυ i))
    (hDu_memLp : ∀ i, Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (α * (β + 1) / β)) (Du i)) :
    Periodic.MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
      (fun x : (Fin d → ℝ) =>
        C * (‖fun i => Dυ i x‖ ^ (α - 1)
                  + (|S.indicator ρ x| + 1) ^ (β - β / α)
                  + 1)
            * ∑ i, |Dυ i x - Du i x|) := by
  have hαpos : 0 < α := lt_trans one_pos hα
  have hαm1_pos : 0 < α - 1 := by linarith
  have hbb_pos : 0 < β + 1 := by linarith
  have hβ_pos : 0 < β := hβ
  have hγb_pos : 0 < α * (β + 1) / β :=
    div_pos (mul_pos hαpos hbb_pos) hβ_pos
  have hβ_div_α_pos : 0 < β / α := div_pos hβ_pos hαpos
  have hβmβα_pos : 0 < β - β / α := by
    have h1 : β / α < β := by
      rw [div_lt_iff₀ hαpos]
      have : β * 1 < β * α := by nlinarith
      linarith
    linarith
  have hβb'_pos : 0 < (β + 1) / β := div_pos hbb_pos hβ_pos
  haveI : IsFiniteMeasure
      (MeasureTheory.Measure.restrict MeasureTheory.volume
        (Periodic.UnitCube (d := d))) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ]; simp⟩
  set βBarE : ℝ≥0∞ := ENNReal.ofReal (β + 1) with hβBarE_def
  set γBarE : ℝ≥0∞ := ENNReal.ofReal (α * (β + 1) / β)
    with hγBarE_def
  set βBar'E : ℝ≥0∞ := ENNReal.ofReal ((β + 1) / β)
    with hβBar'E_def
  have hDiff_memLp : ∀ i, Periodic.MemLpPer (d := d) γBarE
      (fun x : (Fin d → ℝ) => Dυ i x - Du i x) := by
    intro i
    have hneg := (hDu_memLp i).const_smul (𝕜 := ℝ) (-1)
    have h := (hDυ_memLp i).add hneg
    have heq :
        ((Dυ i) + (-1 : ℝ) • (Du i))
          = (fun x : (Fin d → ℝ) => Dυ i x - Du i x) := by
      funext x; simp [Pi.add_apply, sub_eq_add_neg]
    rw [heq] at h
    exact h
  have hDiff_abs_memLp : ∀ i, Periodic.MemLpPer (d := d) γBarE
      (fun x : (Fin d → ℝ) => |Dυ i x - Du i x|) := by
    intro i
    have := (hDiff_memLp i).toMemLp.norm
    have heq : (fun x : (Fin d → ℝ) => ‖Dυ i x - Du i x‖)
              = (fun x : (Fin d → ℝ) => |Dυ i x - Du i x|) := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at this
    exact MemLp.toMemLpPer this
  have hΔ_memLp : Periodic.MemLpPer (d := d) γBarE
      (fun x : (Fin d → ℝ) => ∑ i, |Dυ i x - Du i x|) := by
    have hsum :
        MemLp (fun x : (Fin d → ℝ) =>
            ∑ i : Fin d, (fun x => |Dυ i x - Du i x|) x) γBarE
          (MeasureTheory.Measure.restrict MeasureTheory.volume
            (Periodic.UnitCube d)) :=
      MeasureTheory.memLp_finset_sum (Finset.univ : Finset (Fin d))
        (fun i _ => (hDiff_abs_memLp i).toMemLp)
    exact MemLp.toMemLpPer hsum
  have hDυ_vec : Periodic.MemLpPer (d := d) γBarE
      (fun x : (Fin d → ℝ) => fun i : Fin d => Dυ i x) := by
    set Dom : (Fin d → ℝ) → ℝ := fun x => ∑ i : Fin d, |Dυ i x|
      with hDom_def
    have habs_memLp : ∀ i, Periodic.MemLpPer (d := d) γBarE
        (fun x => |Dυ i x|) := by
      intro i
      have := (hDυ_memLp i).toMemLp.norm
      have heq : (fun x : (Fin d → ℝ) => ‖Dυ i x‖)
                = (fun x : (Fin d → ℝ) => |Dυ i x|) := by
        funext x; exact Real.norm_eq_abs _
      rw [heq] at this
      exact MemLp.toMemLpPer this
    have hDom_memLp : Periodic.MemLpPer (d := d) γBarE Dom := by
      have hsum :
          MemLp (fun x : (Fin d → ℝ) =>
              ∑ i : Fin d, (fun x => |Dυ i x|) x) γBarE
            (MeasureTheory.Measure.restrict MeasureTheory.volume
              (Periodic.UnitCube d)) :=
        MeasureTheory.memLp_finset_sum (Finset.univ : Finset (Fin d))
          (fun i _ => (habs_memLp i).toMemLp)
      exact MemLp.toMemLpPer hsum
    have hbound :
        ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume
              (Periodic.UnitCube d)),
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
        AEStronglyMeasurable
          (fun x : (Fin d → ℝ) => fun i : Fin d => Dυ i x)
          (MeasureTheory.Measure.restrict MeasureTheory.volume
            (Periodic.UnitCube d)) := by
      have hAEm : AEMeasurable
          (fun x : (Fin d → ℝ) => fun i : Fin d => Dυ i x)
          (MeasureTheory.Measure.restrict MeasureTheory.volume
            (Periodic.UnitCube d)) :=
        aemeasurable_pi_iff.mpr fun i =>
          (hDυ_memLp i).aestronglyMeasurable.aemeasurable
      exact hAEm.aestronglyMeasurable
    exact MemLp.toMemLpPer
      (MeasureTheory.MemLp.of_le_mul hDom_memLp.toMemLp hmeas hbound)
  set qE1 : ℝ≥0∞ := ENNReal.ofReal (α - 1) with hqE1_def
  have hqE1_top : qE1 ≠ ⊤ := by
    rw [hqE1_def]; exact ENNReal.ofReal_ne_top
  have hqE1_toReal : qE1.toReal = α - 1 := by
    rw [hqE1_def]; exact ENNReal.toReal_ofReal hαm1_pos.le
  have hT1_raw :
      MemLp (fun x : (Fin d → ℝ) =>
              ‖(fun j : Fin d => Dυ j x)‖ ^ qE1.toReal)
            (γBarE / qE1)
            (MeasureTheory.Measure.restrict MeasureTheory.volume
              (Periodic.UnitCube d)) :=
    MemLp.norm_rpow_div hDυ_vec.toMemLp qE1
  have hdiv1 :
      γBarE / qE1
        = ENNReal.ofReal (α * (β + 1) / β / (α - 1)) := by
    rw [hγBarE_def, hqE1_def, ← ENNReal.ofReal_div_of_pos hαm1_pos]
  have hT1_memLp : Periodic.MemLpPer (d := d)
      (ENNReal.ofReal (α * (β + 1) / β / (α - 1)))
      (fun x : (Fin d → ℝ) => ‖(fun j : Fin d => Dυ j x)‖ ^ (α - 1)) := by
    have heq :
        (fun x : (Fin d → ℝ) =>
          ‖(fun j : Fin d => Dυ j x)‖ ^ (α - 1))
        = (fun x : (Fin d → ℝ) =>
          ‖(fun j : Fin d => Dυ j x)‖ ^ qE1.toReal) := by
      funext x; rw [hqE1_toReal]
    rw [heq]
    have := MemLp.toMemLpPer hT1_raw
    rw [hdiv1] at this
    exact this
  have hSρ_abs : Periodic.MemLpPer (d := d) βBarE
      (fun x : (Fin d → ℝ) => |S.indicator ρ x|) := by
    have := hSρ_memLp.toMemLp.norm
    have heq : (fun x : (Fin d → ℝ) => ‖S.indicator ρ x‖)
              = (fun x : (Fin d → ℝ) => |S.indicator ρ x|) := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at this
    exact MemLp.toMemLpPer this
  have hone_βBar : Periodic.MemLpPer (d := d) βBarE
      (fun _ : Fin d → ℝ => (1 : ℝ)) :=
    MemLp.toMemLpPer (MeasureTheory.memLp_const (1 : ℝ))
  have hSρEnv_memLp : Periodic.MemLpPer (d := d) βBarE
      (fun x : (Fin d → ℝ) => |S.indicator ρ x| + 1) := by
    have := hSρ_abs.add hone_βBar
    have heq :
        ((fun x : (Fin d → ℝ) => |S.indicator ρ x|)
            + (fun _ : (Fin d → ℝ) => (1 : ℝ)))
          = (fun x : (Fin d → ℝ) => |S.indicator ρ x| + 1) := by
      funext x; simp [Pi.add_apply]
    rw [heq] at this
    exact this
  set qE2 : ℝ≥0∞ := ENNReal.ofReal (β - β / α) with hqE2_def
  have hqE2_top : qE2 ≠ ⊤ := by
    rw [hqE2_def]; exact ENNReal.ofReal_ne_top
  have hqE2_toReal : qE2.toReal = β - β / α := by
    rw [hqE2_def]; exact ENNReal.toReal_ofReal hβmβα_pos.le
  have hT2_raw :
      MemLp (fun x : (Fin d → ℝ) =>
              ‖|S.indicator ρ x| + 1‖ ^ qE2.toReal)
            (βBarE / qE2)
            (MeasureTheory.Measure.restrict MeasureTheory.volume
              (Periodic.UnitCube d)) :=
    MemLp.norm_rpow_div hSρEnv_memLp.toMemLp qE2
  have hdiv2 :
      βBarE / qE2 = ENNReal.ofReal ((β + 1) / (β - β / α)) := by
    rw [hβBarE_def, hqE2_def, ← ENNReal.ofReal_div_of_pos hβmβα_pos]
  have hT2_memLp : Periodic.MemLpPer (d := d)
      (ENNReal.ofReal ((β + 1) / (β - β / α)))
      (fun x : (Fin d → ℝ) =>
        (|S.indicator ρ x| + 1) ^ (β - β / α)) := by
    have heq :
        (fun x : (Fin d → ℝ) =>
            (|S.indicator ρ x| + 1) ^ (β - β / α))
        = (fun x : (Fin d → ℝ) =>
            ‖|S.indicator ρ x| + 1‖ ^ qE2.toReal) := by
      funext x
      have hnn : 0 ≤ |S.indicator ρ x| + 1 := by
        have := abs_nonneg (S.indicator ρ x); linarith
      rw [Real.norm_eq_abs, abs_of_nonneg hnn, hqE2_toReal]
    rw [heq]
    have := MemLp.toMemLpPer hT2_raw
    rw [hdiv2] at this
    exact this
  have hβBar'_le_γBar : βBar'E ≤ γBarE := by
    rw [hβBar'E_def, hγBarE_def]
    apply ENNReal.ofReal_le_ofReal
    rw [div_le_div_iff_of_pos_right hβ_pos]
    have h1 : (1 : ℝ) * (β + 1) ≤ α * (β + 1) :=
      mul_le_mul_of_nonneg_right hα.le hbb_pos.le
    linarith
  have hγBar_top : γBarE ≠ ⊤ := by
    rw [hγBarE_def]; exact ENNReal.ofReal_ne_top
  have hΔ_βBar' : Periodic.MemLpPer (d := d) βBar'E
      (fun x : (Fin d → ℝ) => ∑ i, |Dυ i x - Du i x|) :=
    Periodic.MemLpPer.mono_exponent_finite hβBar'_le_γBar hγBar_top hΔ_memLp
  have hHT1_real :
      Real.HolderTriple (α * (β + 1) / β / (α - 1))
        (α * (β + 1) / β)
        ((β + 1) / β) :=
    holderTriple_gammaBarOverAlphaMinus1_gammaBar_betaBar' hα hβ
  haveI hHT1_enn :
      ENNReal.HolderTriple
        (ENNReal.ofReal (α * (β + 1) / β / (α - 1)))
        γBarE βBar'E := by
    have := hHT1_real.ennrealOfReal
    rw [hγBarE_def, hβBar'E_def]
    exact this
  have hHT2_real :
      Real.HolderTriple ((β + 1) / (β - β / α))
        (α * (β + 1) / β)
        ((β + 1) / β) :=
    holderTriple_betaBarOverBetaMinusBetaOverAlpha_gammaBar_betaBar' hα hβ
  haveI hHT2_enn :
      ENNReal.HolderTriple
        (ENNReal.ofReal ((β + 1) / (β - β / α)))
        γBarE βBar'E := by
    have := hHT2_real.ennrealOfReal
    rw [hγBarE_def, hβBar'E_def]
    exact this
  have hProd1 :
      Periodic.MemLpPer (d := d) βBar'E
        (fun x : (Fin d → ℝ) =>
          ‖(fun j : Fin d => Dυ j x)‖ ^ (α - 1)
            * ∑ i, |Dυ i x - Du i x|) := by
    have h := (hT1_memLp.toMemLp).fun_mul
      (p := ENNReal.ofReal (α * (β + 1) / β / (α - 1))) (q := γBarE) (r := βBar'E) hΔ_memLp.toMemLp
    exact MemLp.toMemLpPer h
  have hProd2 :
      Periodic.MemLpPer (d := d) βBar'E
        (fun x : (Fin d → ℝ) =>
          (|S.indicator ρ x| + 1) ^ (β - β / α)
            * ∑ i, |Dυ i x - Du i x|) := by
    have h := (hT2_memLp.toMemLp).fun_mul
      (p := ENNReal.ofReal ((β + 1) / (β - β / α))) (q := γBarE) (r := βBar'E) hΔ_memLp.toMemLp
    exact MemLp.toMemLpPer h
  have hSum12 :
      Periodic.MemLpPer (d := d) βBar'E
        (fun x : (Fin d → ℝ) =>
          ‖(fun j : Fin d => Dυ j x)‖ ^ (α - 1)
            * ∑ i, |Dυ i x - Du i x|
          + (|S.indicator ρ x| + 1) ^ (β - β / α)
            * ∑ i, |Dυ i x - Du i x|) := by
    have := hProd1.add hProd2
    have heq :
        ((fun x : (Fin d → ℝ) =>
            ‖(fun j : Fin d => Dυ j x)‖ ^ (α - 1)
              * ∑ i, |Dυ i x - Du i x|)
          + (fun x : (Fin d → ℝ) =>
              (|S.indicator ρ x| + 1) ^ (β - β / α)
              * ∑ i, |Dυ i x - Du i x|))
        = (fun x : (Fin d → ℝ) =>
            ‖(fun j : Fin d => Dυ j x)‖ ^ (α - 1)
              * ∑ i, |Dυ i x - Du i x|
            + (|S.indicator ρ x| + 1) ^ (β - β / α)
              * ∑ i, |Dυ i x - Du i x|) := by
      funext x; simp [Pi.add_apply]
    rw [heq] at this
    exact this
  have hSum123 :
      Periodic.MemLpPer (d := d) βBar'E
        (fun x : (Fin d → ℝ) =>
          ‖(fun j : Fin d => Dυ j x)‖ ^ (α - 1)
            * ∑ i, |Dυ i x - Du i x|
          + (|S.indicator ρ x| + 1) ^ (β - β / α)
            * ∑ i, |Dυ i x - Du i x|
          + ∑ i, |Dυ i x - Du i x|) := by
    have := hSum12.add hΔ_βBar'
    have heq :
        ((fun x : (Fin d → ℝ) =>
            ‖(fun j : Fin d => Dυ j x)‖ ^ (α - 1)
              * ∑ i, |Dυ i x - Du i x|
            + (|S.indicator ρ x| + 1) ^ (β - β / α)
              * ∑ i, |Dυ i x - Du i x|)
          + (fun x : (Fin d → ℝ) => ∑ i, |Dυ i x - Du i x|))
        = (fun x : (Fin d → ℝ) =>
            ‖(fun j : Fin d => Dυ j x)‖ ^ (α - 1)
              * ∑ i, |Dυ i x - Du i x|
            + (|S.indicator ρ x| + 1) ^ (β - β / α)
              * ∑ i, |Dυ i x - Du i x|
            + ∑ i, |Dυ i x - Du i x|) := by
      funext x; simp [Pi.add_apply]
    rw [heq] at this
    exact this
  have hFinal :
      Periodic.MemLpPer (d := d) βBar'E
        (fun x : (Fin d → ℝ) =>
          C * (‖fun j : Fin d => Dυ j x‖ ^ (α - 1)
                    + (|S.indicator ρ x| + 1) ^ (β - β / α)
                    + 1)
              * ∑ i, |Dυ i x - Du i x|) := by
    have hSmul := hSum123.const_smul (𝕜 := ℝ) C
    have heq :
        ((C : ℝ) •
          (fun x : (Fin d → ℝ) =>
            ‖(fun j : Fin d => Dυ j x)‖ ^ (α - 1)
              * ∑ i, |Dυ i x - Du i x|
            + (|S.indicator ρ x| + 1) ^ (β - β / α)
              * ∑ i, |Dυ i x - Du i x|
            + ∑ i, |Dυ i x - Du i x|))
        = (fun x : (Fin d → ℝ) =>
            C * (‖fun j : Fin d => Dυ j x‖ ^ (α - 1)
                      + (|S.indicator ρ x| + 1) ^ (β - β / α)
                      + 1)
                * ∑ i, |Dυ i x - Du i x|) := by
      funext x
      simp [Pi.smul_apply, smul_eq_mul, add_mul, mul_add, one_mul, mul_assoc]
    rw [heq] at hSmul
    exact hSmul
  exact hFinal

/-- Bare-exponent sibling of `hEm_envelope_memLp_betaBarPrime`. -/
theorem hEm_envelope_memLp_betaBarPrime_bare
    {d : ℕ}
    {β α : ℝ} (hα : 1 < α) (hβ : 0 < β)
    {υ u : (Fin d → ℝ) → ℝ}
    (hυ_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (α * (β + 1) / β)) υ)
    (hu_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (α * (β + 1) / β)) u) :
    Periodic.MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
      (fun x : (Fin d → ℝ) => |υ x - u x|) := by
  haveI : IsFiniteMeasure
      (MeasureTheory.Measure.restrict MeasureTheory.volume
        (Periodic.UnitCube (d := d))) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ]; simp⟩
  have hsub : Periodic.MemLpPer (d := d)
      (ENNReal.ofReal (α * (β + 1) / β))
      (fun x : (Fin d → ℝ) => υ x - u x) := by
    have hneg := hu_memLp.const_smul (𝕜 := ℝ) (-1)
    have h := hυ_memLp.add hneg
    have heq :
        (υ + (-1 : ℝ) • u) = (fun x : (Fin d → ℝ) => υ x - u x) := by
      funext x; simp [Pi.add_apply, sub_eq_add_neg]
    rw [heq] at h
    exact h
  have habs_γ : Periodic.MemLpPer (d := d)
      (ENNReal.ofReal (α * (β + 1) / β))
      (fun x : (Fin d → ℝ) => |υ x - u x|) := by
    have := hsub.toMemLp.norm
    have heq : (fun x : (Fin d → ℝ) => ‖υ x - u x‖)
              = (fun x : (Fin d → ℝ) => |υ x - u x|) := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at this
    exact MemLp.toMemLpPer this
  have hα_ge_one : 1 ≤ α := le_of_lt hα
  have hle_real : (β + 1) / β
      ≤ α * (β + 1) / β := by
    rw [div_le_div_iff_of_pos_right hβ]
    have : (1 : ℝ) * (β + 1) ≤ α * (β + 1) :=
      mul_le_mul_of_nonneg_right hα_ge_one
        (by linarith : (0 : ℝ) ≤ β + 1)
    simpa using this
  have hle : ENNReal.ofReal ((β + 1) / β)
      ≤ ENNReal.ofReal (α * (β + 1) / β) :=
    ENNReal.ofReal_le_ofReal hle_real
  have hγTop : ENNReal.ofReal (α * (β + 1) / β) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  exact Periodic.MemLpPer.mono_exponent_finite hle hγTop habs_γ

/-- **`hGh_envelope_memLp_betaBarPrime_signed_bare`** — bare-exponent
sibling of `hGh_envelope_memLp_betaBarPrime_signed` (D2c-2e-2b child C,
signed). The signed HJB-residual envelope
`(C+1)·(‖Du‖^α + 1) + C·((2·|m| + 1)^β + 1) + |u| + |V|` lives in
`L^{(β+1)/β}_per`. Reduces to `g_dominator_memLp_betaBar'_bare` at
`μ := 2·|m| + 1`, `C' := C + 1`. -/
theorem hGh_envelope_memLp_betaBarPrime_signed_bare
    {d : ℕ} {V : (Fin d → ℝ) → ℝ}
    {β α C : ℝ} (hα : 1 < α) (hβ : 0 < β) (hC : 0 < C)
    {m u : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm_memLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal (β + 1)) m)
    (hu_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (α * (β + 1) / β)) u)
    (hDu_memLp : ∀ i, Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (α * (β + 1) / β)) (Du i))
    (hV_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal ((β + 1) / β)) V) :
    Periodic.MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
      (fun x : (Fin d → ℝ) =>
        (C + 1) * (‖fun i => Du i x‖ ^ α + 1)
          + C * ((2 * |m x| + 1) ^ β + 1)
          + |u x| + |V x|) := by
  haveI : IsFiniteMeasure
      (MeasureTheory.Measure.restrict MeasureTheory.volume
        (Periodic.UnitCube (d := d))) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ]; simp⟩
  have hm_abs : Periodic.MemLpPer (d := d) (ENNReal.ofReal (β + 1))
      (fun x : (Fin d → ℝ) => |m x|) := by
    have := hm_memLp.toMemLp.norm
    have heq : (fun x : (Fin d → ℝ) => ‖m x‖)
              = (fun x : (Fin d → ℝ) => |m x|) := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at this
    exact MemLp.toMemLpPer this
  have hm_abs_2 :
      Periodic.MemLpPer (d := d) (ENNReal.ofReal (β + 1))
        (fun x : (Fin d → ℝ) => 2 * |m x|) := by
    have := hm_abs.const_smul (𝕜 := ℝ) (2 : ℝ)
    have heq : ((2 : ℝ) • (fun x : (Fin d → ℝ) => |m x|))
              = (fun x : (Fin d → ℝ) => 2 * |m x|) := by
      funext x; simp [Pi.smul_apply, smul_eq_mul]
    rw [heq] at this
    exact this
  have hone : Periodic.MemLpPer (d := d) (ENNReal.ofReal (β + 1))
      (fun _ : Fin d → ℝ => (1 : ℝ)) :=
    MemLp.toMemLpPer (MeasureTheory.memLp_const (1 : ℝ))
  have hμ_memLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal (β + 1))
      (fun x : (Fin d → ℝ) => 2 * |m x| + 1) := by
    have := hm_abs_2.add hone
    have heq :
        ((fun x : (Fin d → ℝ) => 2 * |m x|)
            + (fun _ : (Fin d → ℝ) => (1 : ℝ)))
          = (fun x : (Fin d → ℝ) => 2 * |m x| + 1) := by
      funext x; simp [Pi.add_apply]
    rw [heq] at this
    exact this
  have hC'_pos : (0 : ℝ) < C + 1 := by linarith
  exact Hamiltonian.g_dominator_memLp_betaBar'_bare (β := β) (α := α) (C := C)
    hα hβ V u
    (fun x => 2 * |m x| + 1) Du
    hμ_memLp hu_memLp hDu_memLp hV_memLp hC'_pos

/-- **`hGh_envelope_memLp_betaBarPrime_transport_bare`** — bare-exponent
sibling of `hGh_envelope_memLp_betaBarPrime_transport` (D2c-2e-2b child C,
transport). The transport HJB-residual envelope
`(C+1)·(‖φ‖^α + 1) + C·((|σ| + 1)^β + 1) + |υ| + |V|` lives in
`L^{(β+1)/β}_per`. Reduces to `hGh_envelope_memLp_betaBarPrime_bare` at
`S := Set.univ`, `ρ := σ`, `Dυ := φ` via `Set.univ.indicator σ = σ`. -/
theorem hGh_envelope_memLp_betaBarPrime_transport_bare
    {d : ℕ} {V : (Fin d → ℝ) → ℝ}
    {β α C : ℝ} (hα : 1 < α) (hβ : 0 < β) (hC : 0 < C)
    {σ υ : (Fin d → ℝ) → ℝ}
    {φ : Fin d → (Fin d → ℝ) → ℝ}
    (hσ_memLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal (β + 1)) σ)
    (hυ_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (α * (β + 1) / β)) υ)
    (hφ_memLp : ∀ i, Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (α * (β + 1) / β)) (φ i))
    (hV_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal ((β + 1) / β)) V) :
    Periodic.MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
      (fun x : (Fin d → ℝ) =>
        (C + 1) * (‖fun i => φ i x‖ ^ α + 1)
          + C * ((|σ x| + 1) ^ β + 1)
          + |υ x| + |V x|) := by
  have h_ind_univ : ∀ x : (Fin d → ℝ),
      (Set.univ : Set (Fin d → ℝ)).indicator σ x = σ x := by
    intro x; simp [Set.indicator_of_mem (Set.mem_univ x)]
  have hSσ_memLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal (β + 1))
      ((Set.univ : Set (Fin d → ℝ)).indicator σ) := by
    have heq : (Set.univ : Set (Fin d → ℝ)).indicator σ = σ := by
      funext x; exact h_ind_univ x
    rw [heq]; exact hσ_memLp
  have h_set := hGh_envelope_memLp_betaBarPrime_bare (V := V)
    (β := β) (α := α) (C := C) hα hβ hC
    (S := Set.univ) (ρ := σ) (υ := υ) (Dυ := φ)
    hSσ_memLp hυ_memLp hφ_memLp hV_memLp
  have heq :
      (fun x : (Fin d → ℝ) =>
          (C + 1) * (‖fun i => φ i x‖ ^ α + 1)
            + C * ((|(Set.univ : Set (Fin d → ℝ)).indicator σ x| + 1)
                          ^ β + 1)
            + |υ x| + |V x|)
        = (fun x : (Fin d → ℝ) =>
            (C + 1) * (‖fun i => φ i x‖ ^ α + 1)
              + C * ((|σ x| + 1) ^ β + 1)
              + |υ x| + |V x|) := by
    funext x; rw [h_ind_univ x]
  rw [heq] at h_set
  exact h_set

/-- **`hEf_envelope_memLp_betaBarPrime_transport_bare`** — bare-exponent
sibling of `hEf_envelope_memLp_betaBarPrime_transport` (D2c-2e-2b child C,
transport). The transport flux test-factor envelope lives in
`L^{(β+1)/β}_per`. Reduces to `hEf_envelope_memLp_betaBarPrime_bare` at
`S := Set.univ`, `ρ := σ`, `Dυ := φ` via `Set.univ.indicator σ = σ`. -/
theorem hEf_envelope_memLp_betaBarPrime_transport_bare
    {d : ℕ}
    {β α C : ℝ} (hα : 1 < α) (hβ : 0 < β)
    {σ : (Fin d → ℝ) → ℝ}
    {φ Du : Fin d → (Fin d → ℝ) → ℝ}
    (hσ_memLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal (β + 1)) σ)
    (hφ_memLp : ∀ i, Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (α * (β + 1) / β)) (φ i))
    (hDu_memLp : ∀ i, Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (α * (β + 1) / β)) (Du i)) :
    Periodic.MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
      (fun x : (Fin d → ℝ) =>
        C * (‖fun i => φ i x‖ ^ (α - 1)
                  + (|σ x| + 1) ^ (β - β / α)
                  + 1)
            * ∑ i, |φ i x - Du i x|) := by
  have h_ind_univ : ∀ x : (Fin d → ℝ),
      (Set.univ : Set (Fin d → ℝ)).indicator σ x = σ x := by
    intro x; simp [Set.indicator_of_mem (Set.mem_univ x)]
  have hSσ_memLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal (β + 1))
      ((Set.univ : Set (Fin d → ℝ)).indicator σ) := by
    have heq : (Set.univ : Set (Fin d → ℝ)).indicator σ = σ := by
      funext x; exact h_ind_univ x
    rw [heq]; exact hσ_memLp
  have h_set := hEf_envelope_memLp_betaBarPrime_bare
    (β := β) (α := α) (C := C) hα hβ
    (S := Set.univ) (ρ := σ) (Dυ := φ) (Du := Du)
    hSσ_memLp hφ_memLp hDu_memLp
  have heq :
      (fun x : (Fin d → ℝ) =>
          C * (‖fun i => φ i x‖ ^ (α - 1)
                    + (|(Set.univ : Set (Fin d → ℝ)).indicator σ x| + 1)
                        ^ (β - β / α)
                    + 1)
              * ∑ i, |φ i x - Du i x|)
        = (fun x : (Fin d → ℝ) =>
            C * (‖fun i => φ i x‖ ^ (α - 1)
                    + (|σ x| + 1) ^ (β - β / α)
                    + 1)
                * ∑ i, |φ i x - Du i x|) := by
    funext x; rw [h_ind_univ x]
  rw [heq] at h_set
  exact h_set

/-- **`setTendstoResidueOf_of_paperHypotheses_with_Ef`** — partial
producer for the per-query `SetTendstoResidueOf` bundle.

Given the paper hypotheses, the per-query Lp + measurability data, and
a **single** authorised input `(Ef, hEf_memLp, hEf_bd)` for the flux
test-factor envelope, build a `SetTendstoResidueOf`. The five other
fields `(Gh, Eh, Gf, Gm, Em)` are discharged in closed form via
`hGh_envelope_memLp_betaBarPrime`, `hEh_envelope_memLp_betaBar`,
`hGf_envelope_memLp_gammaBarPrime`, `hGm_envelope_memLp_betaBar`,
`hEm_envelope_memLp_betaBarPrime` plus the matching pointwise bound
lemmas `Banach.set_perturbation_h{Gh,Eh,Gf,Gm,Em}_bd`.

The `Ef` field remains an authorised input because the natural
envelope shape from `hpow.DpH_upper` lives in `L^{β̄'}` (Hölder
exponent `(β+1)/β`), NOT in `L^{γ̄}` as the structure's
`hEf_memLp` field requires. This exponent mismatch is filed as a
follow-up: see `paperSolFor-supplier-set-Ef-memLp` for the analytic
discharge that requires either tighter test-data hypotheses or a
restructuring of the consumer's Hölder pairing.

**Constraint preserved.** This producer is internal-only and never
added as an authorisation parameter to `T10PaperResidues.of_paperHypotheses`.
The caller is responsible for supplying `Ef` from a future fully
closed `setTendstoResidueOf_of_paperHypotheses` producer once the
analytic blocker on the `Ef` exponent is resolved. -/
noncomputable def setTendstoResidueOf_of_paperHypotheses_with_Ef
    {d : ℕ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    [Fact (1 ≤ ENNReal.ofReal (hpow.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))]
    (q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
            (hpow.β + 1) (hpow.α * (hpow.β + 1) / hpow.β))
    (S : Set (Fin d → ℝ)) (_hS : MeasurableSet S)
    (ρ υ : (Fin d → ℝ) → ℝ)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    -- Test-data AE-strong measurability inputs (iter post-0689 relax;
    -- replaces strict `Measurable ρ`, `Measurable υ`, `Measurable (Dυ i)`
    -- per `paperSolFor-final-phase5-aggregator-closed-testdata-meas-bridge-set`).
    -- Note: `_hS` is unused in the structure body but kept on the
    -- signature so the producer's input shape matches the consumer's
    -- `MeasurableSet S` requirement (e.g.
    -- `paperSection8_hMinty_set_of_paperHypotheses`'s `hS` param).
    -- **Iter-0713**: dropped the `hρ_aestrong` parameter (option b of
    -- `paperSolFor-final-phase5-aggregator-closed-set-rho-meas-supplier`);
    -- the `SetTendstoResidueOf.hρ` field now stores
    -- `AEStronglyMeasurable (S.indicator ρ)` and is built from
    -- `hSρ_memLp.aestronglyMeasurable`.
    (hυ_aestrong : AEStronglyMeasurable υ
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)))
    (hDυ_aestrong : ∀ i, AEStronglyMeasurable (Dυ i)
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)))
    -- Integrability inputs.
    (hSρ_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (hpow.β + 1)) (S.indicator ρ))
    (hυ_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) υ)
    (hDυ_memLp : ∀ i, Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) (Dυ i))
    (hV_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) V)
    -- Nonnegativity of `ρ` (for the bounds, particularly `Gh`/`Ef`).
    (hρ_nn :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)), 0 ≤ ρ x)
    -- iter 0617 flux-pair retype: `Ef` now lives at the natural
    -- envelope exponent `β̄' = (β+1)/β` (was `γ̄ = α(β+1)/β`).
    -- See `paperSolFor-supplier-flux-pairing-beta`.
    (Ef : (Fin d → ℝ) → ℝ)
    (hEf_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Ef)
    (hEf_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ‖DpH x (fun i => Dυ i x)
              (S.indicator ρ x + 1 / ((n : ℝ) + 1))
            ⬝ (fun i => Dυ i x
                        - StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)‖
          ≤ Ef x) :
    StationaryMFG.Theorems.SimplePower.Banach.SetTendstoResidueOf
      (d := d) (V := V) (H := H) (DpH := DpH)
      (βBarReal := hpow.β + 1)
      (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
      hpow q S ρ υ Dυ where
  -- Iter-0713 option-(b) refactor: the `hρ` field now stores
  -- `AEStronglyMeasurable (S.indicator ρ)` (rather than raw
  -- `AEStronglyMeasurable ρ`). Discharged directly from `hSρ_memLp`
  -- via `.aestronglyMeasurable`, eliminating the dependency on the
  -- `hρ_aestrong` parameter for this field.
  hρ := hSρ_memLp.aestronglyMeasurable
  hm := (MeasureTheory.Lp.stronglyMeasurable q.1).measurable
  hV := hV_memLp.aestronglyMeasurable
  hυ := hυ_aestrong
  hu := (MeasureTheory.Lp.stronglyMeasurable q.2.1).measurable
  hDυ := hDυ_aestrong
  hDu := fun i => (MeasureTheory.Lp.stronglyMeasurable (q.2.2 i)).measurable
  Gh := fun x : (Fin d → ℝ) =>
        (hpow.C + 1) * (‖fun i => Dυ i x‖ ^ hpow.α + 1)
          + hpow.C * ((|S.indicator ρ x| + 1) ^ hpow.β + 1)
          + |υ x| + |V x|
  Eh := fun x : (Fin d → ℝ) =>
        |S.indicator ρ x| + 1
          + |StationaryMFG.Theorems.SimplePower.Banach.mOf q x|
  hGh_memLp := hGh_envelope_memLp_betaBarPrime hpow
                hSρ_memLp hυ_memLp hDυ_memLp hV_memLp
  hEh_memLp :=
    hEh_envelope_memLp_betaBar (S := S) (ρ := ρ)
      (m := StationaryMFG.Theorems.SimplePower.Banach.mOf q)
      hSρ_memLp
      (StationaryMFG.Theorems.SimplePower.Banach.memLpPer_of_lpPer
        (d := d) q.1)
  hGh_bd := StationaryMFG.Theorems.SimplePower.Banach.set_perturbation_hGh_bd
              hpow (S := S) (ρ := ρ) (V := V) (υ := υ) hρ_nn (Dυ := Dυ)
  hEh_bd :=
    StationaryMFG.Theorems.SimplePower.Banach.set_perturbation_hEh_bd
      (S := S) (ρ := ρ)
      (m := StationaryMFG.Theorems.SimplePower.Banach.mOf q)
  Gf := fun x : (Fin d → ℝ) => |S.indicator ρ x| + 1
  Ef := Ef
  -- iter 0617 flux-pair retype: `Gf ∈ L^{β̄}` (was `L^{γ̄'}`).
  hGf_memLp := hGf_envelope_memLp_betaBar (S := S) (ρ := ρ) hSρ_memLp
  hEf_memLp := hEf_memLp
  hGf_bd :=
    StationaryMFG.Theorems.SimplePower.Banach.set_perturbation_hGf_bd
      (S := S) (ρ := ρ)
  hEf_bd := hEf_bd
  Gm := fun x : (Fin d → ℝ) => |S.indicator ρ x| + 2
  Em := fun x : (Fin d → ℝ) =>
        |υ x - StationaryMFG.Theorems.SimplePower.Banach.uOf q x|
  hGm_memLp := hGm_envelope_memLp_betaBar (S := S) (ρ := ρ) hSρ_memLp
  hEm_memLp :=
    hEm_envelope_memLp_betaBarPrime (_V := V) (H := H) (DpH := DpH)
      hpow (υ := υ) (u := StationaryMFG.Theorems.SimplePower.Banach.uOf q)
      hυ_memLp
      (StationaryMFG.Theorems.SimplePower.Banach.memLpPer_of_lpPer
        (d := d) q.2.1)
  hGm_bd :=
    StationaryMFG.Theorems.SimplePower.Banach.set_perturbation_hGm_bd
      (S := S) (ρ := ρ)
  hEm_bd :=
    StationaryMFG.Theorems.SimplePower.Banach.set_perturbation_hEm_bd
      (υ := υ) (u := StationaryMFG.Theorems.SimplePower.Banach.uOf q)

/-- **`setTendstoResidueOf_of_paperHypotheses`** — closed producer for the
per-query `SetTendstoResidueOf` bundle.

Given the paper hypotheses and the per-query Lp + measurability data,
build a complete `SetTendstoResidueOf` with **no** authorised inputs
beyond the paper data. The six envelope fields
`(Gh, Eh, Gf, Ef, Gm, Em)` are all discharged in closed form via

* `hGh_envelope_memLp_betaBarPrime`,
* `hEh_envelope_memLp_betaBar`,
* `hGf_envelope_memLp_betaBar`,
* `hEf_envelope_memLp_betaBarPrime`  ← iter 0618 (this task),
* `hGm_envelope_memLp_betaBar`,
* `hEm_envelope_memLp_betaBarPrime`

plus the matching pointwise bound lemmas
`Banach.set_perturbation_h{Gh,Eh,Gf,Ef,Gm,Em}_bd`.

The flux test-factor envelope `Ef` is instantiated inline to the exact
upper bound proven in `Banach.set_perturbation_hEf_bd`:
```
Ef x := hpow.C * (‖fun i => Dυ i x‖^(α-1)
                  + (|S.indicator ρ x| + 1)^(β - β/α) + 1)
        * ∑ i, |Dυ i x - DuOf q i x|
```
The corresponding `Ef ∈ L^{β̄'}_per` certificate is provided by
`hEf_envelope_memLp_betaBarPrime`.

**Constraint preserved.** This producer is internal-only and never
added as an authorisation parameter to `T10PaperResidues.of_paperHypotheses`.
It replaces the partial producer
`setTendstoResidueOf_of_paperHypotheses_with_Ef` (kept under
`@[deprecated]` for backwards compatibility — see below). -/
noncomputable def setTendstoResidueOf_of_paperHypotheses
    {d : ℕ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    [Fact (1 ≤ ENNReal.ofReal (hpow.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))]
    (q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
            (hpow.β + 1) (hpow.α * (hpow.β + 1) / hpow.β))
    (S : Set (Fin d → ℝ)) (_hS : MeasurableSet S)
    (ρ υ : (Fin d → ℝ) → ℝ)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    -- Test-data AE-strong measurability inputs (iter post-0689 relax;
    -- replaces strict `Measurable ρ`, `Measurable υ`, `Measurable (Dυ i)`
    -- per `paperSolFor-final-phase5-aggregator-closed-testdata-meas-bridge-set`).
    -- **Iter-0713 (this task)**: dropped the `hρ_aestrong` parameter; the
    -- `SetTendstoResidueOf.hρ` field now stores
    -- `AEStronglyMeasurable (S.indicator ρ)` (option b), which is derivable
    -- from `hSρ_memLp.aestronglyMeasurable` — eliminating the raw-`ρ`
    -- measurability gap that previously blocked closed callability from
    -- the partial supplier signature.
    (hυ_aestrong : AEStronglyMeasurable υ
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)))
    (hDυ_aestrong : ∀ i, AEStronglyMeasurable (Dυ i)
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)))
    (hSρ_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (hpow.β + 1)) (S.indicator ρ))
    (hυ_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) υ)
    (hDυ_memLp : ∀ i, Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) (Dυ i))
    (hV_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) V)
    (hρ_nn :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)), 0 ≤ ρ x) :
    StationaryMFG.Theorems.SimplePower.Banach.SetTendstoResidueOf
      (d := d) (V := V) (H := H) (DpH := DpH)
      (βBarReal := hpow.β + 1)
      (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
      hpow q S ρ υ Dυ :=
  let Du : Fin d → (Fin d → ℝ) → ℝ :=
    fun i => StationaryMFG.Theorems.SimplePower.Banach.DuOf q i
  let hDu_memLp : ∀ i, Periodic.MemLpPer (d := d)
      (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) (Du i) :=
    fun i =>
      StationaryMFG.Theorems.SimplePower.Banach.memLpPer_of_lpPer
        (d := d) (q.2.2 i)
  let Ef : (Fin d → ℝ) → ℝ := fun x : (Fin d → ℝ) =>
    hpow.C * (‖fun i => Dυ i x‖ ^ (hpow.α - 1)
              + (|S.indicator ρ x| + 1) ^ (hpow.β - hpow.β / hpow.α)
              + 1)
        * ∑ i, |Dυ i x - Du i x|
  let hEf_memLp : Periodic.MemLpPer (d := d)
      (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) Ef :=
    hEf_envelope_memLp_betaBarPrime hpow
      (Dυ := Dυ) (Du := Du) hSρ_memLp hDυ_memLp hDu_memLp
  let hEf_bd : ∀ n : ℕ,
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ‖DpH x (fun i => Dυ i x)
              (S.indicator ρ x + 1 / ((n : ℝ) + 1))
            ⬝ (fun i => Dυ i x - Du i x)‖ ≤ Ef x :=
    StationaryMFG.Theorems.SimplePower.Banach.set_perturbation_hEf_bd
      hpow (S := S) (ρ := ρ) hρ_nn (Dυ := Dυ) (Du := Du)
  setTendstoResidueOf_of_paperHypotheses_with_Ef
    (V := V) (H := H) (DpH := DpH)
    hpow q S _hS ρ υ Dυ hυ_aestrong hDυ_aestrong
    hSρ_memLp hυ_memLp hDυ_memLp hV_memLp hρ_nn
    Ef hEf_memLp hEf_bd

/-- **`setTendstoResidueOfBare_of_paperHypotheses_of_aeMeasH`** — bare-exponent,
`aeMeasH`-input set residue supplier (D2b-1c-ii-c4c-set).

Produces the `SetTendstoResidueOfBare` bundle (consumed by
`paperSection8_hMinty_set_of_paperHypotheses_of_rc0_of_aeMeasH`) at a target
carrier `H` whose dominator data is reused from a STRICT power-growth carrier
`H'` (with `hpow : HypothesisPowerGrowth H' DpH`) that AGREES with `H` on the
per-`n` positive slot `S.indicator ρ + 1/(n+1) > 0`. At `H := HdeltaK0`,
`H' := HdeltaPos` and the agreement is `HdeltaK0_eq_HdeltaPos_of_pos` (the two
carriers coincide on `{0 < m}`); the two extra H AE composites are supplied at
`HdeltaK0` by `aemeasurable_HdeltaK0_comp_of_rc0`.

The six envelope/dominator fields `(Gh, Eh, Gf, Ef, Gm, Em)` and all `_bd`
fields except `hGh_bd` are reused VERBATIM from
`setTendstoResidueOf_of_paperHypotheses` at `H'` (none of those mention the
target `H`). The single `hGh_bd` field — the only dominator field that
evaluates `H` — is transported across the a.e. agreement `hH_agree`. The two
H AE composites are taken as inputs (`hHcomp_ae_n`/`hHcomp_ae_lim`). -/
noncomputable def setTendstoResidueOfBare_of_paperHypotheses_of_aeMeasH
    {d : ℕ}
    {V : (Fin d → ℝ) → ℝ}
    {H H' : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H' DpH)
    [Fact (1 ≤ ENNReal.ofReal (hpow.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))]
    (q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
            (hpow.β + 1) (hpow.α * (hpow.β + 1) / hpow.β))
    (S : Set (Fin d → ℝ)) (hS : MeasurableSet S)
    (ρ υ : (Fin d → ℝ) → ℝ)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (hυ_aestrong : AEStronglyMeasurable υ
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)))
    (hDυ_aestrong : ∀ i, AEStronglyMeasurable (Dυ i)
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)))
    (hSρ_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (hpow.β + 1)) (S.indicator ρ))
    (hυ_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) υ)
    (hDυ_memLp : ∀ i, Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) (Dυ i))
    (hV_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) V)
    (hρ_nn :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)), 0 ≤ ρ x)
    -- A.e. agreement of the target carrier `H` with the strict carrier `H'`
    -- at the per-`n` positive slot (at `HdeltaK0`/`HdeltaPos`: the `{0<m}`
    -- coincidence `HdeltaK0_eq_HdeltaPos_of_pos`).
    (hH_agree : ∀ n : ℕ,
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        H x (fun i => Dυ i x) (S.indicator ρ x + 1 / ((n : ℝ) + 1))
          = H' x (fun i => Dυ i x) (S.indicator ρ x + 1 / ((n : ℝ) + 1)))
    -- The two H AE composites at the target carrier `H`.
    (hHcomp_ae_n : ∀ n : ℕ, AEMeasurable
      (fun x : (Fin d → ℝ) =>
        H x (fun i => Dυ i x) (S.indicator ρ x + 1 / ((n : ℝ) + 1)))
      (MeasureTheory.volume.restrict (Periodic.UnitCube d)))
    (hHcomp_ae_lim : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        H x (fun i => Dυ i x) (S.indicator ρ x))
      (MeasureTheory.volume.restrict (Periodic.UnitCube d))) :
    StationaryMFG.Theorems.SimplePower.Banach.SetTendstoResidueOfBare
      (d := d) (V := V) (H := H) (DpH := DpH)
      (βBarReal := hpow.β + 1)
      (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
      hpow.β q S ρ υ Dυ :=
  let strict :=
    setTendstoResidueOf_of_paperHypotheses
      (V := V) (H := H') (DpH := DpH)
      hpow q S hS ρ υ Dυ hυ_aestrong hDυ_aestrong
      hSρ_memLp hυ_memLp hDυ_memLp hV_memLp hρ_nn
  { hρ := strict.hρ
    hm := strict.hm
    hV := strict.hV
    hυ := strict.hυ
    hu := strict.hu
    hDυ := strict.hDυ
    hDu := strict.hDu
    hHcomp_ae_n := hHcomp_ae_n
    hHcomp_ae_lim := hHcomp_ae_lim
    Gh := strict.Gh
    Eh := strict.Eh
    hGh_memLp := strict.hGh_memLp
    hEh_memLp := strict.hEh_memLp
    hGh_bd := by
      intro n
      filter_upwards [strict.hGh_bd n, hH_agree n] with x hx hxAgree
      rw [hxAgree]; exact hx
    hEh_bd := strict.hEh_bd
    Gf := strict.Gf
    Ef := strict.Ef
    hGf_memLp := strict.hGf_memLp
    hEf_memLp := strict.hEf_memLp
    hGf_bd := strict.hGf_bd
    hEf_bd := strict.hEf_bd
    Gm := strict.Gm
    Em := strict.Em
    hGm_memLp := strict.hGm_memLp
    hEm_memLp := strict.hEm_memLp
    hGm_bd := strict.hGm_bd
    hEm_bd := strict.hEm_bd }

/-- **`setTendstoResidueOfBare_of_paperHypotheses_of_aeMeasH_ae`** — the
AE/bare-exponent sibling of `setTendstoResidueOfBare_of_paperHypotheses_of_aeMeasH`
(EXPERT RULING #4 retype, D2c-2e-1 child C).

Produces the `SetTendstoResidueOfBare` bundle DIRECTLY (inline structure literal,
**not** routed through `setTendstoResidueOf_of_paperHypotheses`, which would bind
`hpow : HypothesisPowerGrowth`). Instead of the strict power-growth carrier this
producer consumes:
* bare growth exponents `(β α C : ℝ)` with positivity `(hα : 1 < α) (hβ : 0 < β)
  (hC : 0 < C)` (the AE carrier's `Cdelta`/`hweak.α`/`hweak.β` values), and
* the three **a.e.** analytic estimates `hH_upper_pt` / `hlower` / `hDpH_upper`
  (general-`p`, `0 < m` shapes) sourced from `HdeltaAEPowerEpsData`
  (`H_upper_pointwise_ae` from child B + `lower_ae` + `DpH_upper_ae`).

The six dominator triples `(Gh,Eh,Gf,Ef,Gm,Em)` are discharged via the child-A
bare-exponent envelope `MemLpPer` helpers (`hGh_envelope_memLp_betaBarPrime_bare`,
`hEf_envelope_memLp_betaBarPrime_bare`, `hEm_envelope_memLp_betaBarPrime_bare`)
together with the already-bare envelope helpers (`hEh,hGf,hGm_envelope_memLp_betaBar`)
and the a.e./bare pointwise bounds (child-B `set_perturbation_h{Gh,Ef}_bd_ae`,
already-bare `set_perturbation_h{Eh,Gf,Gm,Em}_bd`). No `hpow`,
`RegularityH`, `hInj`/`hSurj`/`hFormPos`/`hqE_per` appears in the signature or
proof — the assembly is value/positivity + a.e.-bound-level only.

The two H AE composites are taken as inputs (`hHcomp_ae_n`/`hHcomp_ae_lim`),
exactly as in the strict sibling. -/
noncomputable def setTendstoResidueOfBare_of_paperHypotheses_of_aeMeasH_ae
    {d : ℕ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {β α C : ℝ} (hα : 1 < α) (hβ : 0 < β) (hC : 0 < C)
    [Fact (1 ≤ ENNReal.ofReal (β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (α * (β + 1) / β))]
    (q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
            (β + 1) (α * (β + 1) / β))
    (S : Set (Fin d → ℝ)) (_hS : MeasurableSet S)
    (ρ υ : (Fin d → ℝ) → ℝ)
    (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (hυ_aestrong : AEStronglyMeasurable υ
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)))
    (hDυ_aestrong : ∀ i, AEStronglyMeasurable (Dυ i)
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)))
    (hSρ_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (β + 1)) (S.indicator ρ))
    (hυ_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (α * (β + 1) / β)) υ)
    (hDυ_memLp : ∀ i, Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (α * (β + 1) / β)) (Dυ i))
    (hV_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal ((β + 1) / β)) V)
    (hρ_nn :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)), 0 ≤ ρ x)
    -- The three a.e. analytic estimates from the AE carrier
    -- `HdeltaAEPowerEpsData` (general-`p`, `0 < m` shapes), in place of the
    -- strict `hpow : HypothesisPowerGrowth`.
    (hH_upper_pt :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ∀ p m, 0 < m → H x p m ≤ C * (‖p‖ ^ α + 1) - (m ^ β) / C)
    (hlower :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ∀ p m, 0 < m → H x p m ≥ (‖p‖ ^ α) / C - C * (m ^ β + 1))
    (hDpH_upper :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ∀ p m, 0 < m →
          ‖DpH x p m‖ ≤ C * (‖p‖ ^ (α - 1) + m ^ (β - β / α) + 1))
    -- The two H AE composites at the target carrier `H`.
    (hHcomp_ae_n : ∀ n : ℕ, AEMeasurable
      (fun x : (Fin d → ℝ) =>
        H x (fun i => Dυ i x) (S.indicator ρ x + 1 / ((n : ℝ) + 1)))
      (MeasureTheory.volume.restrict (Periodic.UnitCube d)))
    (hHcomp_ae_lim : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        H x (fun i => Dυ i x) (S.indicator ρ x))
      (MeasureTheory.volume.restrict (Periodic.UnitCube d))) :
    StationaryMFG.Theorems.SimplePower.Banach.SetTendstoResidueOfBare
      (d := d) (V := V) (H := H) (DpH := DpH)
      (βBarReal := β + 1)
      (γBarReal := α * (β + 1) / β)
      β q S ρ υ Dυ :=
  let Du : Fin d → (Fin d → ℝ) → ℝ :=
    fun i => StationaryMFG.Theorems.SimplePower.Banach.DuOf q i
  let hDu_memLp : ∀ i, Periodic.MemLpPer (d := d)
      (ENNReal.ofReal (α * (β + 1) / β)) (Du i) :=
    fun i =>
      StationaryMFG.Theorems.SimplePower.Banach.memLpPer_of_lpPer
        (d := d) (q.2.2 i)
  { hρ := hSρ_memLp.aestronglyMeasurable
    hm := (MeasureTheory.Lp.stronglyMeasurable q.1).measurable
    hV := hV_memLp.aestronglyMeasurable
    hυ := hυ_aestrong
    hu := (MeasureTheory.Lp.stronglyMeasurable q.2.1).measurable
    hDυ := hDυ_aestrong
    hDu := fun i => (MeasureTheory.Lp.stronglyMeasurable (q.2.2 i)).measurable
    hHcomp_ae_n := hHcomp_ae_n
    hHcomp_ae_lim := hHcomp_ae_lim
    Gh := fun x : (Fin d → ℝ) =>
          (C + 1) * (‖fun i => Dυ i x‖ ^ α + 1)
            + C * ((|S.indicator ρ x| + 1) ^ β + 1)
            + |υ x| + |V x|
    Eh := fun x : (Fin d → ℝ) =>
          |S.indicator ρ x| + 1
            + |StationaryMFG.Theorems.SimplePower.Banach.mOf q x|
    hGh_memLp := hGh_envelope_memLp_betaBarPrime_bare hα hβ hC
                  hSρ_memLp hυ_memLp hDυ_memLp hV_memLp
    hEh_memLp :=
      hEh_envelope_memLp_betaBar (S := S) (ρ := ρ)
        (m := StationaryMFG.Theorems.SimplePower.Banach.mOf q)
        hSρ_memLp
        (StationaryMFG.Theorems.SimplePower.Banach.memLpPer_of_lpPer
          (d := d) q.1)
    hGh_bd :=
      StationaryMFG.Theorems.SimplePower.Banach.set_perturbation_hGh_bd_ae
        hα hβ hC (S := S) (ρ := ρ) (V := V) (υ := υ) hρ_nn (Dυ := Dυ)
        hH_upper_pt hlower
    hEh_bd :=
      StationaryMFG.Theorems.SimplePower.Banach.set_perturbation_hEh_bd
        (S := S) (ρ := ρ)
        (m := StationaryMFG.Theorems.SimplePower.Banach.mOf q)
    Gf := fun x : (Fin d → ℝ) => |S.indicator ρ x| + 1
    Ef := fun x : (Fin d → ℝ) =>
      C * (‖fun i => Dυ i x‖ ^ (α - 1)
                + (|S.indicator ρ x| + 1) ^ (β - β / α)
                + 1)
          * ∑ i, |Dυ i x - Du i x|
    hGf_memLp := hGf_envelope_memLp_betaBar (S := S) (ρ := ρ) hSρ_memLp
    hEf_memLp := hEf_envelope_memLp_betaBarPrime_bare hα hβ
                  (C := C) (S := S) (ρ := ρ) (Dυ := Dυ) (Du := Du)
                  hSρ_memLp hDυ_memLp hDu_memLp
    hGf_bd :=
      StationaryMFG.Theorems.SimplePower.Banach.set_perturbation_hGf_bd
        (S := S) (ρ := ρ)
    hEf_bd :=
      StationaryMFG.Theorems.SimplePower.Banach.set_perturbation_hEf_bd_ae
        hα hβ hC (S := S) (ρ := ρ) hρ_nn (Dυ := Dυ) (Du := Du) hDpH_upper
    Gm := fun x : (Fin d → ℝ) => |S.indicator ρ x| + 2
    Em := fun x : (Fin d → ℝ) =>
          |υ x - StationaryMFG.Theorems.SimplePower.Banach.uOf q x|
    hGm_memLp := hGm_envelope_memLp_betaBar (S := S) (ρ := ρ) hSρ_memLp
    hEm_memLp := hEm_envelope_memLp_betaBarPrime_bare hα hβ
                  (υ := υ) (u := StationaryMFG.Theorems.SimplePower.Banach.uOf q)
                  hυ_memLp
                  (StationaryMFG.Theorems.SimplePower.Banach.memLpPer_of_lpPer
                    (d := d) q.2.1)
    hGm_bd :=
      StationaryMFG.Theorems.SimplePower.Banach.set_perturbation_hGm_bd
        (S := S) (ρ := ρ)
    hEm_bd :=
      StationaryMFG.Theorems.SimplePower.Banach.set_perturbation_hEm_bd
        (υ := υ) (u := StationaryMFG.Theorems.SimplePower.Banach.uOf q) }

/-! ### `paperSolFor-supplier-transport-closed-Ef` — closed-form
transport-family supplier (iter 0619).

This block mirrors the set-family producer block above for the
transport family. The transport perturbation replaces `S.indicator ρ`
with a bare `σ` (no indicator wrapper), and the gradient slot uses
the independent test gradient `φ` rather than `Dυ`. The five
envelope helpers `hGh,Eh,Gf,Ef,Gm_envelope_memLp_*_transport` are
direct specialisations of the set analogues at `S := Set.univ`,
`ρ := σ`; the `Em` field reuses `hEm_envelope_memLp_betaBarPrime`
verbatim (no σ dependency). -/

/-- **`hGh_envelope_memLp_betaBarPrime_transport`** — the HJB residual
envelope for the transport family. Same shape as
`hGh_envelope_memLp_betaBarPrime` with `S.indicator ρ ↦ σ`. -/
theorem hGh_envelope_memLp_betaBarPrime_transport
    {d : ℕ} {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    {σ υ : (Fin d → ℝ) → ℝ}
    {φ : Fin d → (Fin d → ℝ) → ℝ}
    (hσ_memLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1)) σ)
    (hυ_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) υ)
    (hφ_memLp : ∀ i, Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) (φ i))
    (hV_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) V) :
    Periodic.MemLpPer (d := d) (ENNReal.ofReal ((hpow.β + 1) / hpow.β))
      (fun x : (Fin d → ℝ) =>
        (hpow.C + 1) * (‖fun i => φ i x‖ ^ hpow.α + 1)
          + hpow.C * ((|σ x| + 1) ^ hpow.β + 1)
          + |υ x| + |V x|) := by
  -- `Set.univ.indicator σ x = σ x` pointwise.
  have h_ind_univ : ∀ x : (Fin d → ℝ),
      (Set.univ : Set (Fin d → ℝ)).indicator σ x = σ x := by
    intro x; simp [Set.indicator_of_mem (Set.mem_univ x)]
  -- Reduce via the set version at `S := Set.univ, ρ := σ`.
  have hSσ_memLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1))
      ((Set.univ : Set (Fin d → ℝ)).indicator σ) := by
    have heq : (Set.univ : Set (Fin d → ℝ)).indicator σ = σ := by
      funext x; exact h_ind_univ x
    rw [heq]; exact hσ_memLp
  have h_set := hGh_envelope_memLp_betaBarPrime hpow
    (S := Set.univ) (ρ := σ) (υ := υ) (Dυ := φ)
    hSσ_memLp hυ_memLp hφ_memLp hV_memLp
  have heq :
      (fun x : (Fin d → ℝ) =>
          (hpow.C + 1) * (‖fun i => φ i x‖ ^ hpow.α + 1)
            + hpow.C * ((|(Set.univ : Set (Fin d → ℝ)).indicator σ x| + 1)
                          ^ hpow.β + 1)
            + |υ x| + |V x|)
        = (fun x : (Fin d → ℝ) =>
            (hpow.C + 1) * (‖fun i => φ i x‖ ^ hpow.α + 1)
              + hpow.C * ((|σ x| + 1) ^ hpow.β + 1)
              + |υ x| + |V x|) := by
    funext x; rw [h_ind_univ x]
  rw [heq] at h_set
  exact h_set

/-- **`hEh_envelope_memLp_betaBar_transport`** — the HJB pair-test
envelope for the transport family: `|σ| + 1 + |m|` lives in
`L^{β+1}_per`. -/
theorem hEh_envelope_memLp_betaBar_transport
    {d : ℕ} {σ m : (Fin d → ℝ) → ℝ}
    {βBarReal : ℝ}
    (hσ_memLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) σ)
    (hm_memLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) m) :
    Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal)
      (fun x : (Fin d → ℝ) => |σ x| + 1 + |m x|) := by
  have h_ind_univ : ∀ x : (Fin d → ℝ),
      (Set.univ : Set (Fin d → ℝ)).indicator σ x = σ x := by
    intro x; simp [Set.indicator_of_mem (Set.mem_univ x)]
  have hSσ_memLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal)
      ((Set.univ : Set (Fin d → ℝ)).indicator σ) := by
    have heq : (Set.univ : Set (Fin d → ℝ)).indicator σ = σ := by
      funext x; exact h_ind_univ x
    rw [heq]; exact hσ_memLp
  have h_set := hEh_envelope_memLp_betaBar
    (S := Set.univ) (ρ := σ) (m := m) hSσ_memLp hm_memLp
  have heq :
      (fun x : (Fin d → ℝ) =>
          |(Set.univ : Set (Fin d → ℝ)).indicator σ x| + 1 + |m x|)
        = (fun x : (Fin d → ℝ) => |σ x| + 1 + |m x|) := by
    funext x; rw [h_ind_univ x]
  rw [heq] at h_set
  exact h_set

/-- **`hGf_envelope_memLp_betaBar_transport`** — the flux μ-envelope
`|σ| + 1` lives in `L^{β+1}_per` for the transport family. -/
theorem hGf_envelope_memLp_betaBar_transport
    {d : ℕ} {σ : (Fin d → ℝ) → ℝ}
    {βBarReal : ℝ}
    (hσ_memLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) σ) :
    Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal)
      (fun x : (Fin d → ℝ) => |σ x| + 1) := by
  have h_ind_univ : ∀ x : (Fin d → ℝ),
      (Set.univ : Set (Fin d → ℝ)).indicator σ x = σ x := by
    intro x; simp [Set.indicator_of_mem (Set.mem_univ x)]
  have hSσ_memLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal)
      ((Set.univ : Set (Fin d → ℝ)).indicator σ) := by
    have heq : (Set.univ : Set (Fin d → ℝ)).indicator σ = σ := by
      funext x; exact h_ind_univ x
    rw [heq]; exact hσ_memLp
  have h_set := hGf_envelope_memLp_betaBar
    (S := Set.univ) (ρ := σ) hSσ_memLp
  have heq :
      (fun x : (Fin d → ℝ) =>
          |(Set.univ : Set (Fin d → ℝ)).indicator σ x| + 1)
        = (fun x : (Fin d → ℝ) => |σ x| + 1) := by
    funext x; rw [h_ind_univ x]
  rw [heq] at h_set
  exact h_set

/-- **`hGm_envelope_memLp_betaBar_transport`** — the mass μ-envelope
`|σ| + 2` lives in `L^{β+1}_per` for the transport family. -/
theorem hGm_envelope_memLp_betaBar_transport
    {d : ℕ} {σ : (Fin d → ℝ) → ℝ}
    {βBarReal : ℝ}
    (hσ_memLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal) σ) :
    Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal)
      (fun x : (Fin d → ℝ) => |σ x| + 2) := by
  have h_ind_univ : ∀ x : (Fin d → ℝ),
      (Set.univ : Set (Fin d → ℝ)).indicator σ x = σ x := by
    intro x; simp [Set.indicator_of_mem (Set.mem_univ x)]
  have hSσ_memLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal βBarReal)
      ((Set.univ : Set (Fin d → ℝ)).indicator σ) := by
    have heq : (Set.univ : Set (Fin d → ℝ)).indicator σ = σ := by
      funext x; exact h_ind_univ x
    rw [heq]; exact hσ_memLp
  have h_set := hGm_envelope_memLp_betaBar
    (S := Set.univ) (ρ := σ) hSσ_memLp
  have heq :
      (fun x : (Fin d → ℝ) =>
          |(Set.univ : Set (Fin d → ℝ)).indicator σ x| + 2)
        = (fun x : (Fin d → ℝ) => |σ x| + 2) := by
    funext x; rw [h_ind_univ x]
  rw [heq] at h_set
  exact h_set

/-- **`hEf_envelope_memLp_betaBarPrime_transport`** — the flux test-factor
envelope for the transport family. Same shape as the set version with
`S.indicator ρ ↦ σ` and `Dυ ↦ φ`. -/
theorem hEf_envelope_memLp_betaBarPrime_transport
    {d : ℕ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    {σ : (Fin d → ℝ) → ℝ}
    {φ Du : Fin d → (Fin d → ℝ) → ℝ}
    (hσ_memLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1)) σ)
    (hφ_memLp : ∀ i, Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) (φ i))
    (hDu_memLp : ∀ i, Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) (Du i)) :
    Periodic.MemLpPer (d := d) (ENNReal.ofReal ((hpow.β + 1) / hpow.β))
      (fun x : (Fin d → ℝ) =>
        hpow.C * (‖fun i => φ i x‖ ^ (hpow.α - 1)
                  + (|σ x| + 1) ^ (hpow.β - hpow.β / hpow.α)
                  + 1)
            * ∑ i, |φ i x - Du i x|) := by
  have h_ind_univ : ∀ x : (Fin d → ℝ),
      (Set.univ : Set (Fin d → ℝ)).indicator σ x = σ x := by
    intro x; simp [Set.indicator_of_mem (Set.mem_univ x)]
  have hSσ_memLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1))
      ((Set.univ : Set (Fin d → ℝ)).indicator σ) := by
    have heq : (Set.univ : Set (Fin d → ℝ)).indicator σ = σ := by
      funext x; exact h_ind_univ x
    rw [heq]; exact hσ_memLp
  have h_set := hEf_envelope_memLp_betaBarPrime hpow
    (S := Set.univ) (ρ := σ) (Dυ := φ) (Du := Du)
    hSσ_memLp hφ_memLp hDu_memLp
  have heq :
      (fun x : (Fin d → ℝ) =>
          hpow.C * (‖fun i => φ i x‖ ^ (hpow.α - 1)
                    + (|(Set.univ : Set (Fin d → ℝ)).indicator σ x| + 1)
                        ^ (hpow.β - hpow.β / hpow.α)
                    + 1)
              * ∑ i, |φ i x - Du i x|)
        = (fun x : (Fin d → ℝ) =>
            hpow.C * (‖fun i => φ i x‖ ^ (hpow.α - 1)
                    + (|σ x| + 1) ^ (hpow.β - hpow.β / hpow.α)
                    + 1)
                * ∑ i, |φ i x - Du i x|) := by
    funext x; rw [h_ind_univ x]
  rw [heq] at h_set
  exact h_set

/-- **`transportTendstoResidueOf_of_paperHypotheses`** — closed producer
for the per-query `TransportTendstoResidueOf` bundle.

Given the paper hypotheses and the per-query Lp + measurability data,
build a complete `TransportTendstoResidueOf` with **no** authorised
inputs beyond the paper data. All envelope fields
`(Gh, Eh, Gf, Ef, Gm, Em)` are discharged in closed form via the
`*_transport` envelope lemmas above (and `hEm_envelope_memLp_betaBarPrime`
which is shape-independent of σ), plus the matching pointwise bound
lemmas `Banach.transport_perturbation_h{Gh,Eh,Gf,Ef,Gm,Em}_bd`.

The flux test-factor envelope `Ef` is instantiated inline to the exact
upper bound proven in `Banach.transport_perturbation_hEf_bd`:
```
Ef x := hpow.C * (‖fun i => φ i x‖^(α-1)
                  + (|σ x| + 1)^(β - β/α) + 1)
        * ∑ i, |φ i x - DuOf q i x|
```
The corresponding `Ef ∈ L^{β̄'}_per` certificate is provided by
`hEf_envelope_memLp_betaBarPrime_transport`.

**Constraint preserved.** This producer is internal-only and never
added as an authorisation parameter to
`T10PaperResidues.of_paperHypotheses`. -/
noncomputable def transportTendstoResidueOf_of_paperHypotheses
    {d : ℕ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    [Fact (1 ≤ ENNReal.ofReal (hpow.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))]
    (q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
            (hpow.β + 1) (hpow.α * (hpow.β + 1) / hpow.β))
    (σ υ : (Fin d → ℝ) → ℝ)
    (φ : Fin d → (Fin d → ℝ) → ℝ)
    -- Test-data AE-strong measurability inputs (iter post-0690 relax;
    -- replaces strict `Measurable σ`, `Measurable υ`, `Measurable (φ i)`
    -- per `paperSolFor-final-phase5-aggregator-closed-testdata-meas-bridge-transport`).
    -- `hV` is now sourced from `hV_memLp.aestronglyMeasurable` rather
    -- than a strict-measurability witness.
    (hσ_aestrong : AEStronglyMeasurable σ
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)))
    (hυ_aestrong : AEStronglyMeasurable υ
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)))
    (hφ_aestrong : ∀ i, AEStronglyMeasurable (φ i)
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)))
    (hσ_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (hpow.β + 1)) σ)
    (hυ_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) υ)
    (hφ_memLp : ∀ i, Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) (φ i))
    (hV_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) V)
    (hσ_nn :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)), 0 ≤ σ x) :
    StationaryMFG.Theorems.SimplePower.Banach.TransportTendstoResidueOf
      (d := d) (V := V) (H := H) (DpH := DpH)
      (βBarReal := hpow.β + 1)
      (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
      hpow q σ υ φ :=
  let Du : Fin d → (Fin d → ℝ) → ℝ :=
    fun i => StationaryMFG.Theorems.SimplePower.Banach.DuOf q i
  let hDu_memLp : ∀ i, Periodic.MemLpPer (d := d)
      (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) (Du i) :=
    fun i =>
      StationaryMFG.Theorems.SimplePower.Banach.memLpPer_of_lpPer
        (d := d) (q.2.2 i)
  { hσ := hσ_aestrong
    hm := (MeasureTheory.Lp.stronglyMeasurable q.1).measurable
    hV := hV_memLp.aestronglyMeasurable
    hυ := hυ_aestrong
    hu := (MeasureTheory.Lp.stronglyMeasurable q.2.1).measurable
    hφ := hφ_aestrong
    hDu := fun i => (MeasureTheory.Lp.stronglyMeasurable (q.2.2 i)).measurable
    Gh := fun x : (Fin d → ℝ) =>
          (hpow.C + 1) * (‖fun i => φ i x‖ ^ hpow.α + 1)
            + hpow.C * ((|σ x| + 1) ^ hpow.β + 1)
            + |υ x| + |V x|
    Eh := fun x : (Fin d → ℝ) =>
          |σ x| + 1
            + |StationaryMFG.Theorems.SimplePower.Banach.mOf q x|
    hGh_memLp := hGh_envelope_memLp_betaBarPrime_transport hpow
                  hσ_memLp hυ_memLp hφ_memLp hV_memLp
    hEh_memLp :=
      hEh_envelope_memLp_betaBar_transport
        (σ := σ)
        (m := StationaryMFG.Theorems.SimplePower.Banach.mOf q)
        hσ_memLp
        (StationaryMFG.Theorems.SimplePower.Banach.memLpPer_of_lpPer
          (d := d) q.1)
    hGh_bd := StationaryMFG.Theorems.SimplePower.Banach.transport_perturbation_hGh_bd
                hpow (σ := σ) (V := V) (υ := υ) hσ_nn (φ := φ)
    hEh_bd :=
      StationaryMFG.Theorems.SimplePower.Banach.transport_perturbation_hEh_bd
        (σ := σ)
        (m := StationaryMFG.Theorems.SimplePower.Banach.mOf q)
    Gf := fun x : (Fin d → ℝ) => |σ x| + 1
    Ef := fun x : (Fin d → ℝ) =>
      hpow.C * (‖fun i => φ i x‖ ^ (hpow.α - 1)
                + (|σ x| + 1) ^ (hpow.β - hpow.β / hpow.α)
                + 1)
          * ∑ i, |φ i x - Du i x|
    hGf_memLp := hGf_envelope_memLp_betaBar_transport (σ := σ) hσ_memLp
    hEf_memLp := hEf_envelope_memLp_betaBarPrime_transport hpow
                  (σ := σ) (φ := φ) (Du := Du)
                  hσ_memLp hφ_memLp hDu_memLp
    hGf_bd :=
      StationaryMFG.Theorems.SimplePower.Banach.transport_perturbation_hGf_bd
        (σ := σ)
    hEf_bd :=
      StationaryMFG.Theorems.SimplePower.Banach.transport_perturbation_hEf_bd
        hpow (σ := σ) hσ_nn (φ := φ) (Du := Du)
    Gm := fun x : (Fin d → ℝ) => |σ x| + 2
    Em := fun x : (Fin d → ℝ) =>
          |υ x - StationaryMFG.Theorems.SimplePower.Banach.uOf q x|
    hGm_memLp := hGm_envelope_memLp_betaBar_transport (σ := σ) hσ_memLp
    hEm_memLp :=
      hEm_envelope_memLp_betaBarPrime (_V := V) (H := H) (DpH := DpH)
        hpow (υ := υ) (u := StationaryMFG.Theorems.SimplePower.Banach.uOf q)
        hυ_memLp
        (StationaryMFG.Theorems.SimplePower.Banach.memLpPer_of_lpPer
          (d := d) q.2.1)
    hGm_bd :=
      StationaryMFG.Theorems.SimplePower.Banach.transport_perturbation_hGm_bd
        (σ := σ)
    hEm_bd :=
      StationaryMFG.Theorems.SimplePower.Banach.transport_perturbation_hEm_bd
        (υ := υ) (u := StationaryMFG.Theorems.SimplePower.Banach.uOf q) }

/-! ### `paperSolFor-supplier-signed` — closed-form signed-family supplier
(iter 0620).

Closed-form producer for `SignedTendstoResidueOf`. Mirrors the set/
transport supplier blocks above but for the signed family. The
`SignedTendstoResidueOf` bundle is structurally smaller than the
set/transport bundles: it has only 9 fields, the only envelope being
the HJB residual `(Gh, hGh_memLp, hGh_bd)` (no `Eh`, `Gf`, `Ef`,
`Gm`, `Em`). The signed perturbation `μ_n := m + σ·m·1_S + 1/(n+1)`
multiplies the primal density by a sign-indicator, but preserves the
HJB-only test shape (no flux/mass test factors are needed by the
ε-level signed perturbation consumer).

The envelope used is
```
Gh x := (h.C+1) · (‖DuOf q‖^α + 1) + h.C · ((2·|mOf q x| + 1)^β + 1)
        + |uOf q x| + |V x|
```
which reduces to `g_dominator_memLp_betaBar'` at `μ := 2·|m| + 1`,
`C' := h.C + 1`. The pointwise bound is
`Banach.signed_perturbation_hGh_bd` (iter 0620 sibling lemma in
`Banach/RegularizedSequence.lean`). -/

/-- **`hGh_envelope_memLp_betaBarPrime_signed`** — the HJB residual
envelope for the **signed family**
`(h.C+1)·(‖Du‖^α + 1) + h.C·((2·|m| + 1)^β + 1) + |u| + |V|` lives in
`L^{β̄'} = L^{(β+1)/β}_per`.

Reduces to `g_dominator_memLp_betaBar'` at `μ := 2·|m| + 1`,
`C' := h.C + 1`. The hypothesis `μ ∈ L^{β+1}_per` follows from
`|m| ∈ L^{β+1}_per` (scaled by 2) plus the constant `1` on a finite
measure space.

Combined with `Banach.signed_perturbation_hGh_bd`, this discharges
the `Gh, hGh_memLp, hGh_bd` triple of `SignedTendstoResidueOf`. -/
theorem hGh_envelope_memLp_betaBarPrime_signed
    {d : ℕ} {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    {m u : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm_memLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1)) m)
    (hu_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) u)
    (hDu_memLp : ∀ i, Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) (Du i))
    (hV_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) V) :
    Periodic.MemLpPer (d := d) (ENNReal.ofReal ((hpow.β + 1) / hpow.β))
      (fun x : (Fin d → ℝ) =>
        (hpow.C + 1) * (‖fun i => Du i x‖ ^ hpow.α + 1)
          + hpow.C * ((2 * |m x| + 1) ^ hpow.β + 1)
          + |u x| + |V x|) := by
  haveI : IsFiniteMeasure
      (MeasureTheory.Measure.restrict MeasureTheory.volume
        (Periodic.UnitCube (d := d))) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ]; simp⟩
  -- Build `μ := 2·|m| + 1` in `L^{β+1}_per`.
  have hm_abs : Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1))
      (fun x : (Fin d → ℝ) => |m x|) := by
    have := hm_memLp.toMemLp.norm
    have heq : (fun x : (Fin d → ℝ) => ‖m x‖)
              = (fun x : (Fin d → ℝ) => |m x|) := by
      funext x; exact Real.norm_eq_abs _
    rw [heq] at this
    exact MemLp.toMemLpPer this
  -- `2·|m| ∈ L^{β+1}_per` via `const_smul` with scalar `2`.
  have hm_abs_2 :
      Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1))
        (fun x : (Fin d → ℝ) => 2 * |m x|) := by
    have := hm_abs.const_smul (𝕜 := ℝ) (2 : ℝ)
    have heq : ((2 : ℝ) • (fun x : (Fin d → ℝ) => |m x|))
              = (fun x : (Fin d → ℝ) => 2 * |m x|) := by
      funext x; simp [Pi.smul_apply, smul_eq_mul]
    rw [heq] at this
    exact this
  have hone : Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1))
      (fun _ : Fin d → ℝ => (1 : ℝ)) :=
    MemLp.toMemLpPer (MeasureTheory.memLp_const (1 : ℝ))
  have hμ_memLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1))
      (fun x : (Fin d → ℝ) => 2 * |m x| + 1) := by
    have := hm_abs_2.add hone
    have heq :
        ((fun x : (Fin d → ℝ) => 2 * |m x|)
            + (fun _ : (Fin d → ℝ) => (1 : ℝ)))
          = (fun x : (Fin d → ℝ) => 2 * |m x| + 1) := by
      funext x; simp [Pi.add_apply]
    rw [heq] at this
    exact this
  -- Positivity of `C' := h.C + 1`.
  have hC'_pos : (0 : ℝ) < hpow.C + 1 := by linarith [hpow.hC]
  -- Apply `g_dominator_memLp_betaBar'` at `μ := 2·|m| + 1`, `C' := h.C + 1`.
  exact Hamiltonian.g_dominator_memLp_betaBar' hpow V u
    (fun x => 2 * |m x| + 1) Du
    hμ_memLp hu_memLp hDu_memLp hV_memLp hC'_pos

/-- **`signedTendstoResidueOf_of_paperHypotheses`** — closed producer for
the per-query `SignedTendstoResidueOf` bundle.

Given the paper hypotheses and the per-query Lp + measurability data,
build a complete `SignedTendstoResidueOf` with **no** authorised inputs
beyond the paper data. The single envelope field
`(Gh, hGh_memLp, hGh_bd)` is discharged in closed form via
`hGh_envelope_memLp_betaBarPrime_signed` (above) and
`Banach.signed_perturbation_hGh_bd` (iter 0620 in
`Banach/RegularizedSequence.lean`).

The structure has only 9 fields total — much smaller than
`SetTendstoResidueOf` (24 fields) or `TransportTendstoResidueOf`
(24 fields) — because the signed-family ε-level continuity consumer
`mfgOperatorEpsPair_tendsto_signed_perturbation_of_paperHypotheses`
only requires the HJB residual envelope; the `Eh`, flux, and mass
envelopes are produced inline at the consumer site.

**Constraint preserved.** This producer is internal-only and never
added as an authorisation parameter to
`T10PaperResidues.of_paperHypotheses`. -/
noncomputable def signedTendstoResidueOf_of_paperHypotheses
    {d : ℕ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    [Fact (1 ≤ ENNReal.ofReal (hpow.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))]
    (q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
            (hpow.β + 1) (hpow.α * (hpow.β + 1) / hpow.β))
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (S : Set (Fin d → ℝ)) (_hS : MeasurableSet S)
    -- AE-strong measurability is derived from `hV_memLp` below; the
    -- strict `Measurable V` parameter has been removed
    -- (iter 0710, `paperSolFor-final-phase5-aggregator-closed-V-meas-bridge-signed-suppliers`).
    (hV_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) V)
    (hm_nn :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        0 ≤ StationaryMFG.Theorems.SimplePower.Banach.mOf q x) :
    StationaryMFG.Theorems.SimplePower.Banach.SignedTendstoResidueOf
      (d := d) (V := V) (H := H) (DpH := DpH)
      (βBarReal := hpow.β + 1)
      (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
      hpow q σ S :=
  let m : (Fin d → ℝ) → ℝ := StationaryMFG.Theorems.SimplePower.Banach.mOf q
  let u : (Fin d → ℝ) → ℝ := StationaryMFG.Theorems.SimplePower.Banach.uOf q
  let Du : Fin d → (Fin d → ℝ) → ℝ :=
    fun i => StationaryMFG.Theorems.SimplePower.Banach.DuOf q i
  let hm_memLp : Periodic.MemLpPer (d := d)
      (ENNReal.ofReal (hpow.β + 1)) m :=
    StationaryMFG.Theorems.SimplePower.Banach.memLpPer_of_lpPer
      (d := d) q.1
  let hu_memLp : Periodic.MemLpPer (d := d)
      (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) u :=
    StationaryMFG.Theorems.SimplePower.Banach.memLpPer_of_lpPer
      (d := d) q.2.1
  let hDu_memLp : ∀ i, Periodic.MemLpPer (d := d)
      (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) (Du i) :=
    fun i =>
      StationaryMFG.Theorems.SimplePower.Banach.memLpPer_of_lpPer
        (d := d) (q.2.2 i)
  { hm := (MeasureTheory.Lp.stronglyMeasurable q.1).measurable
    hV := hV_memLp.aestronglyMeasurable
    hu := (MeasureTheory.Lp.stronglyMeasurable q.2.1).measurable
    hDu := fun i => (MeasureTheory.Lp.stronglyMeasurable (q.2.2 i)).measurable
    hm_memLp := hm_memLp
    hm_nn := hm_nn
    Gh := fun x : (Fin d → ℝ) =>
          (hpow.C + 1) * (‖fun i => Du i x‖ ^ hpow.α + 1)
            + hpow.C * ((2 * |m x| + 1) ^ hpow.β + 1)
            + |u x| + |V x|
    hGh_memLp := hGh_envelope_memLp_betaBarPrime_signed hpow
                  (m := m) (u := u) (Du := Du)
                  hm_memLp hu_memLp hDu_memLp hV_memLp
    hGh_bd :=
      StationaryMFG.Theorems.SimplePower.Banach.signed_perturbation_hGh_bd
        hpow (S := S) (m := m) (V := V) (u := u) hm_nn (Du := Du) σ hσ }

/-- **`signedTendstoResidueOfBare_of_paperHypotheses_of_aeMeasH`** — bare-exponent,
`aeMeasH`-input signed residue supplier (D2b-1c-ii-c4c-signed).

Signed-family analogue of `setTendstoResidueOfBare_of_paperHypotheses_of_aeMeasH`.
Produces the `SignedTendstoResidueOfBare` bundle (consumed by
`paperSection8_hMinty_signed_of_paperHypotheses_of_rc0_of_aeMeasH`) at a target
carrier `H` whose dominator data is reused from a STRICT power-growth carrier
`H'` (with `hpow : HypothesisPowerGrowth H' DpH`) that AGREES with `H` on the
per-`n` positive signed slot `mOf q + σ·mOf q·𝟙_S + 1/(n+1) > 0`. At
`H := HdeltaK0`, `H' := HdeltaPos` and the agreement is
`HdeltaK0_eq_HdeltaPos_of_pos`; the two H AE composites are supplied at
`HdeltaK0` by `aemeasurable_HdeltaK0_comp_of_rc0`.

The signed bundle is structurally small (only the HJB-residual envelope
`(Gh, hGh_memLp, hGh_bd)`); the single field that evaluates `H` is `hGh_bd`,
transported across the a.e. agreement `hH_agree`. The two H AE composites are
taken as inputs (`hHcomp_ae_n`/`hHcomp_ae_lim`). -/
noncomputable def signedTendstoResidueOfBare_of_paperHypotheses_of_aeMeasH
    {d : ℕ}
    {V : (Fin d → ℝ) → ℝ}
    {H H' : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H' DpH)
    [Fact (1 ≤ ENNReal.ofReal (hpow.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))]
    (q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
            (hpow.β + 1) (hpow.α * (hpow.β + 1) / hpow.β))
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (S : Set (Fin d → ℝ)) (hS : MeasurableSet S)
    (hV_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) V)
    (hm_nn :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        0 ≤ StationaryMFG.Theorems.SimplePower.Banach.mOf q x)
    -- A.e. agreement of the target carrier `H` with the strict carrier `H'`
    -- at the per-`n` positive signed slot (at `HdeltaK0`/`HdeltaPos`: the
    -- `{0<m}` coincidence `HdeltaK0_eq_HdeltaPos_of_pos`).
    (hH_agree : ∀ n : ℕ,
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        H x (fun i => StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
              (StationaryMFG.Theorems.SimplePower.Banach.mOf q x
                + σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                + 1 / ((n : ℝ) + 1))
          = H' x (fun i => StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
              (StationaryMFG.Theorems.SimplePower.Banach.mOf q x
                + σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
                + 1 / ((n : ℝ) + 1)))
    -- The two H AE composites at the target carrier `H`.
    (hHcomp_ae_n : ∀ n : ℕ, AEMeasurable
      (fun x : (Fin d → ℝ) =>
        H x (fun i => StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
          (StationaryMFG.Theorems.SimplePower.Banach.mOf q x
            + σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
            + 1 / ((n : ℝ) + 1)))
      (MeasureTheory.volume.restrict (Periodic.UnitCube d)))
    (hHcomp_ae_lim : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        H x (fun i => StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
          (StationaryMFG.Theorems.SimplePower.Banach.mOf q x
            + σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
      (MeasureTheory.volume.restrict (Periodic.UnitCube d))) :
    StationaryMFG.Theorems.SimplePower.Banach.SignedTendstoResidueOfBare
      (d := d) (V := V) (H := H) (DpH := DpH)
      (βBarReal := hpow.β + 1)
      (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
      hpow.β q σ S :=
  let strict :=
    signedTendstoResidueOf_of_paperHypotheses
      (V := V) (H := H') (DpH := DpH)
      hpow q σ hσ S hS hV_memLp hm_nn
  { hm := strict.hm
    hV := strict.hV
    hu := strict.hu
    hDu := strict.hDu
    hm_memLp := strict.hm_memLp
    hm_nn := strict.hm_nn
    hHcomp_ae_n := hHcomp_ae_n
    hHcomp_ae_lim := hHcomp_ae_lim
    Gh := strict.Gh
    hGh_memLp := strict.hGh_memLp
    hGh_bd := by
      intro n
      filter_upwards [strict.hGh_bd n, hH_agree n] with x hx hxAgree
      rw [hxAgree]; exact hx }

/-- **`signedTendstoResidueOfBare_of_paperHypotheses_of_aeMeasH_ae`** — the
AE/bare-exponent sibling of `signedTendstoResidueOfBare_of_paperHypotheses_of_aeMeasH`
(D2c-2e-2b child C, signed).

Produces the `SignedTendstoResidueOfBare` bundle DIRECTLY (inline structure
literal, **not** routed through `signedTendstoResidueOf_of_paperHypotheses`,
which would bind `hpow : HypothesisPowerGrowth`). Instead of the strict
power-growth carrier this producer consumes bare growth exponents `(β α C : ℝ)`
with positivity `(hα : 1 < α) (hβ : 0 < β) (hC : 0 < C)` (the AE carrier's
`Cdelta`/`hweak.α`/`hweak.β` values), and the two **a.e.** analytic estimates
`hH_upper_pt` / `hlower` sourced from `HdeltaAEPowerEpsData`.

The single HJB-residual envelope `(Gh, hGh_memLp, hGh_bd)` is discharged via the
bare envelope helper `hGh_envelope_memLp_betaBarPrime_signed_bare` and the
a.e./bare pointwise bound `signed_perturbation_hGh_bd_ae`. The two H AE composites
are taken as inputs. No `hpow`, `RegularityH`, `hInj`/`hSurj`/`hFormPos`/`hqE_per`
appears in the signature or proof. -/
noncomputable def signedTendstoResidueOfBare_of_paperHypotheses_of_aeMeasH_ae
    {d : ℕ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {β α C : ℝ} (hα : 1 < α) (hβ : 0 < β) (hC : 0 < C)
    [Fact (1 ≤ ENNReal.ofReal (β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (α * (β + 1) / β))]
    (q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
            (β + 1) (α * (β + 1) / β))
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (S : Set (Fin d → ℝ)) (_hS : MeasurableSet S)
    (hV_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal ((β + 1) / β)) V)
    (hm_nn :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        0 ≤ StationaryMFG.Theorems.SimplePower.Banach.mOf q x)
    -- The two a.e. analytic estimates from the AE carrier
    -- `HdeltaAEPowerEpsData` (general-`p`, `0 < m` shapes).
    (hH_upper_pt :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ∀ p m, 0 < m → H x p m ≤ C * (‖p‖ ^ α + 1) - (m ^ β) / C)
    (hlower :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ∀ p m, 0 < m → H x p m ≥ (‖p‖ ^ α) / C - C * (m ^ β + 1))
    -- The two H AE composites at the target carrier `H`.
    (hHcomp_ae_n : ∀ n : ℕ, AEMeasurable
      (fun x : (Fin d → ℝ) =>
        H x (fun i => StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
          (StationaryMFG.Theorems.SimplePower.Banach.mOf q x
            + σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
            + 1 / ((n : ℝ) + 1)))
      (MeasureTheory.volume.restrict (Periodic.UnitCube d)))
    (hHcomp_ae_lim : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        H x (fun i => StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
          (StationaryMFG.Theorems.SimplePower.Banach.mOf q x
            + σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
      (MeasureTheory.volume.restrict (Periodic.UnitCube d))) :
    StationaryMFG.Theorems.SimplePower.Banach.SignedTendstoResidueOfBare
      (d := d) (V := V) (H := H) (DpH := DpH)
      (βBarReal := β + 1)
      (γBarReal := α * (β + 1) / β)
      β q σ S :=
  let m : (Fin d → ℝ) → ℝ := StationaryMFG.Theorems.SimplePower.Banach.mOf q
  let u : (Fin d → ℝ) → ℝ := StationaryMFG.Theorems.SimplePower.Banach.uOf q
  let Du : Fin d → (Fin d → ℝ) → ℝ :=
    fun i => StationaryMFG.Theorems.SimplePower.Banach.DuOf q i
  let hm_memLp : Periodic.MemLpPer (d := d)
      (ENNReal.ofReal (β + 1)) m :=
    StationaryMFG.Theorems.SimplePower.Banach.memLpPer_of_lpPer
      (d := d) q.1
  let hu_memLp : Periodic.MemLpPer (d := d)
      (ENNReal.ofReal (α * (β + 1) / β)) u :=
    StationaryMFG.Theorems.SimplePower.Banach.memLpPer_of_lpPer
      (d := d) q.2.1
  let hDu_memLp : ∀ i, Periodic.MemLpPer (d := d)
      (ENNReal.ofReal (α * (β + 1) / β)) (Du i) :=
    fun i =>
      StationaryMFG.Theorems.SimplePower.Banach.memLpPer_of_lpPer
        (d := d) (q.2.2 i)
  { hm := (MeasureTheory.Lp.stronglyMeasurable q.1).measurable
    hV := hV_memLp.aestronglyMeasurable
    hu := (MeasureTheory.Lp.stronglyMeasurable q.2.1).measurable
    hDu := fun i => (MeasureTheory.Lp.stronglyMeasurable (q.2.2 i)).measurable
    hm_memLp := hm_memLp
    hm_nn := hm_nn
    hHcomp_ae_n := hHcomp_ae_n
    hHcomp_ae_lim := hHcomp_ae_lim
    Gh := fun x : (Fin d → ℝ) =>
          (C + 1) * (‖fun i => Du i x‖ ^ α + 1)
            + C * ((2 * |m x| + 1) ^ β + 1)
            + |u x| + |V x|
    hGh_memLp := hGh_envelope_memLp_betaBarPrime_signed_bare hα hβ hC
                  (m := m) (u := u) (Du := Du)
                  hm_memLp hu_memLp hDu_memLp hV_memLp
    hGh_bd :=
      StationaryMFG.Theorems.SimplePower.Banach.signed_perturbation_hGh_bd_ae
        hβ hC (S := S) (m := m) (V := V) (u := u) hm_nn (Du := Du) σ hσ
        hH_upper_pt hlower }

/-- **`transportTendstoResidueOfBare_of_paperHypotheses_of_aeMeasH`** —
bare-exponent, `aeMeasH`-input transport residue supplier
(D2b-1c-ii-c4c-transport).

Transport-family analogue of `setTendstoResidueOfBare_of_paperHypotheses_of_aeMeasH`.
Produces the `TransportTendstoResidueOfBare` bundle (consumed by
`paperSection8_hMinty_transport_of_paperHypotheses_of_rc0_of_aeMeasH`) at a
target carrier `H` whose dominator data is reused from a STRICT power-growth
carrier `H'` that AGREES with `H` on the per-`n` positive transport slot
`σ + 1/(n+1) > 0`. At `H := HdeltaK0`, `H' := HdeltaPos` and the agreement is
`HdeltaK0_eq_HdeltaPos_of_pos`; the two H AE composites are supplied at
`HdeltaK0` by `aemeasurable_HdeltaK0_comp_of_rc0`.

The six envelope/dominator fields `(Gh, Eh, Gf, Ef, Gm, Em)` and all `_bd`
fields except `hGh_bd` are reused VERBATIM from
`transportTendstoResidueOf_of_paperHypotheses` at `H'` (`hEf_bd` evaluates
`DpH`, which is carrier-independent). The single `hGh_bd` field — the only
dominator field that evaluates `H` — is transported across the a.e. agreement
`hH_agree`. The two H AE composites are taken as inputs. -/
noncomputable def transportTendstoResidueOfBare_of_paperHypotheses_of_aeMeasH
    {d : ℕ}
    {V : (Fin d → ℝ) → ℝ}
    {H H' : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H' DpH)
    [Fact (1 ≤ ENNReal.ofReal (hpow.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))]
    (q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
            (hpow.β + 1) (hpow.α * (hpow.β + 1) / hpow.β))
    (σ υ : (Fin d → ℝ) → ℝ)
    (φ : Fin d → (Fin d → ℝ) → ℝ)
    (hσ_aestrong : AEStronglyMeasurable σ
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)))
    (hυ_aestrong : AEStronglyMeasurable υ
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)))
    (hφ_aestrong : ∀ i, AEStronglyMeasurable (φ i)
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)))
    (hσ_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (hpow.β + 1)) σ)
    (hυ_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) υ)
    (hφ_memLp : ∀ i, Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) (φ i))
    (hV_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) V)
    (hσ_nn :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)), 0 ≤ σ x)
    -- A.e. agreement of the target carrier `H` with the strict carrier `H'`
    -- at the per-`n` positive transport slot (at `HdeltaK0`/`HdeltaPos`: the
    -- `{0<m}` coincidence `HdeltaK0_eq_HdeltaPos_of_pos`).
    (hH_agree : ∀ n : ℕ,
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        H x (fun i => φ i x) (σ x + 1 / ((n : ℝ) + 1))
          = H' x (fun i => φ i x) (σ x + 1 / ((n : ℝ) + 1)))
    -- The two H AE composites at the target carrier `H`.
    (hHcomp_ae_n : ∀ n : ℕ, AEMeasurable
      (fun x : (Fin d → ℝ) =>
        H x (fun i => φ i x) (σ x + 1 / ((n : ℝ) + 1)))
      (MeasureTheory.volume.restrict (Periodic.UnitCube d)))
    (hHcomp_ae_lim : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        H x (fun i => φ i x) (σ x))
      (MeasureTheory.volume.restrict (Periodic.UnitCube d))) :
    StationaryMFG.Theorems.SimplePower.Banach.TransportTendstoResidueOfBare
      (d := d) (V := V) (H := H) (DpH := DpH)
      (βBarReal := hpow.β + 1)
      (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
      hpow.β q σ υ φ :=
  let strict :=
    transportTendstoResidueOf_of_paperHypotheses
      (V := V) (H := H') (DpH := DpH)
      hpow q σ υ φ hσ_aestrong hυ_aestrong hφ_aestrong
      hσ_memLp hυ_memLp hφ_memLp hV_memLp hσ_nn
  { hσ := strict.hσ
    hm := strict.hm
    hV := strict.hV
    hυ := strict.hυ
    hu := strict.hu
    hφ := strict.hφ
    hDu := strict.hDu
    hHcomp_ae_n := hHcomp_ae_n
    hHcomp_ae_lim := hHcomp_ae_lim
    Gh := strict.Gh
    Eh := strict.Eh
    hGh_memLp := strict.hGh_memLp
    hEh_memLp := strict.hEh_memLp
    hGh_bd := by
      intro n
      filter_upwards [strict.hGh_bd n, hH_agree n] with x hx hxAgree
      rw [hxAgree]; exact hx
    hEh_bd := strict.hEh_bd
    Gf := strict.Gf
    Ef := strict.Ef
    hGf_memLp := strict.hGf_memLp
    hEf_memLp := strict.hEf_memLp
    hGf_bd := strict.hGf_bd
    hEf_bd := strict.hEf_bd
    Gm := strict.Gm
    Em := strict.Em
    hGm_memLp := strict.hGm_memLp
    hEm_memLp := strict.hEm_memLp
    hGm_bd := strict.hGm_bd
    hEm_bd := strict.hEm_bd }

/-- **`transportTendstoResidueOfBare_of_paperHypotheses_of_aeMeasH_ae`** — the
AE/bare-exponent sibling of
`transportTendstoResidueOfBare_of_paperHypotheses_of_aeMeasH` (D2c-2e-2b child C,
transport).

Produces the `TransportTendstoResidueOfBare` bundle DIRECTLY (inline structure
literal, **not** routed through `transportTendstoResidueOf_of_paperHypotheses`,
which would bind `hpow : HypothesisPowerGrowth`). Instead of the strict
power-growth carrier this producer consumes bare growth exponents `(β α C : ℝ)`
with positivity `(hα : 1 < α) (hβ : 0 < β) (hC : 0 < C)` and the two **a.e.**
analytic estimates `hH_upper_pt` / `hlower` plus the `hDpH_upper` a.e. estimate,
sourced from `HdeltaAEPowerEpsData`.

The six dominator triples `(Gh,Eh,Gf,Ef,Gm,Em)` are discharged via the bare
transport envelope helpers (`hGh_envelope_memLp_betaBarPrime_transport_bare`,
`hEh/Gf/Gm_envelope_memLp_betaBar_transport`,
`hEf_envelope_memLp_betaBarPrime_transport_bare`,
`hEm_envelope_memLp_betaBarPrime_bare`) and the a.e./bare pointwise bounds
(`transport_perturbation_hGh_bd_ae`, `transport_perturbation_hEf_bd_ae`,
already-bare `transport_perturbation_h{Eh,Gf,Gm,Em}_bd`). No `hpow`,
`RegularityH`, `hInj`/`hSurj`/`hFormPos`/`hqE_per` appears in the signature or
proof. The two H AE composites are taken as inputs. -/
noncomputable def transportTendstoResidueOfBare_of_paperHypotheses_of_aeMeasH_ae
    {d : ℕ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {β α C : ℝ} (hα : 1 < α) (hβ : 0 < β) (hC : 0 < C)
    [Fact (1 ≤ ENNReal.ofReal (β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (α * (β + 1) / β))]
    (q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
            (β + 1) (α * (β + 1) / β))
    (σ υ : (Fin d → ℝ) → ℝ)
    (φ : Fin d → (Fin d → ℝ) → ℝ)
    (hσ_aestrong : AEStronglyMeasurable σ
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)))
    (hυ_aestrong : AEStronglyMeasurable υ
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)))
    (hφ_aestrong : ∀ i, AEStronglyMeasurable (φ i)
        (MeasureTheory.volume.restrict (Periodic.UnitCube d)))
    (hσ_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (β + 1)) σ)
    (hυ_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (α * (β + 1) / β)) υ)
    (hφ_memLp : ∀ i, Periodic.MemLpPer (d := d)
        (ENNReal.ofReal (α * (β + 1) / β)) (φ i))
    (hV_memLp : Periodic.MemLpPer (d := d)
        (ENNReal.ofReal ((β + 1) / β)) V)
    (hσ_nn :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)), 0 ≤ σ x)
    -- The three a.e. analytic estimates from the AE carrier
    -- `HdeltaAEPowerEpsData` (general-`p`, `0 < m` shapes).
    (hH_upper_pt :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ∀ p m, 0 < m → H x p m ≤ C * (‖p‖ ^ α + 1) - (m ^ β) / C)
    (hlower :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ∀ p m, 0 < m → H x p m ≥ (‖p‖ ^ α) / C - C * (m ^ β + 1))
    (hDpH_upper :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
        ∀ p m, 0 < m →
          ‖DpH x p m‖ ≤ C * (‖p‖ ^ (α - 1) + m ^ (β - β / α) + 1))
    -- The two H AE composites at the target carrier `H`.
    (hHcomp_ae_n : ∀ n : ℕ, AEMeasurable
      (fun x : (Fin d → ℝ) =>
        H x (fun i => φ i x) (σ x + 1 / ((n : ℝ) + 1)))
      (MeasureTheory.volume.restrict (Periodic.UnitCube d)))
    (hHcomp_ae_lim : AEMeasurable
      (fun x : (Fin d → ℝ) =>
        H x (fun i => φ i x) (σ x))
      (MeasureTheory.volume.restrict (Periodic.UnitCube d))) :
    StationaryMFG.Theorems.SimplePower.Banach.TransportTendstoResidueOfBare
      (d := d) (V := V) (H := H) (DpH := DpH)
      (βBarReal := β + 1)
      (γBarReal := α * (β + 1) / β)
      β q σ υ φ :=
  let Du : Fin d → (Fin d → ℝ) → ℝ :=
    fun i => StationaryMFG.Theorems.SimplePower.Banach.DuOf q i
  let hDu_memLp : ∀ i, Periodic.MemLpPer (d := d)
      (ENNReal.ofReal (α * (β + 1) / β)) (Du i) :=
    fun i =>
      StationaryMFG.Theorems.SimplePower.Banach.memLpPer_of_lpPer
        (d := d) (q.2.2 i)
  { hσ := hσ_aestrong
    hm := (MeasureTheory.Lp.stronglyMeasurable q.1).measurable
    hV := hV_memLp.aestronglyMeasurable
    hυ := hυ_aestrong
    hu := (MeasureTheory.Lp.stronglyMeasurable q.2.1).measurable
    hφ := hφ_aestrong
    hDu := fun i => (MeasureTheory.Lp.stronglyMeasurable (q.2.2 i)).measurable
    hHcomp_ae_n := hHcomp_ae_n
    hHcomp_ae_lim := hHcomp_ae_lim
    Gh := fun x : (Fin d → ℝ) =>
          (C + 1) * (‖fun i => φ i x‖ ^ α + 1)
            + C * ((|σ x| + 1) ^ β + 1)
            + |υ x| + |V x|
    Eh := fun x : (Fin d → ℝ) =>
          |σ x| + 1
            + |StationaryMFG.Theorems.SimplePower.Banach.mOf q x|
    hGh_memLp := hGh_envelope_memLp_betaBarPrime_transport_bare hα hβ hC
                  hσ_memLp hυ_memLp hφ_memLp hV_memLp
    hEh_memLp :=
      hEh_envelope_memLp_betaBar_transport
        (σ := σ)
        (m := StationaryMFG.Theorems.SimplePower.Banach.mOf q)
        hσ_memLp
        (StationaryMFG.Theorems.SimplePower.Banach.memLpPer_of_lpPer
          (d := d) q.1)
    hGh_bd :=
      StationaryMFG.Theorems.SimplePower.Banach.transport_perturbation_hGh_bd_ae
        hα hβ hC (σ := σ) (V := V) (υ := υ) hσ_nn (φ := φ)
        hH_upper_pt hlower
    hEh_bd :=
      StationaryMFG.Theorems.SimplePower.Banach.transport_perturbation_hEh_bd
        (σ := σ)
        (m := StationaryMFG.Theorems.SimplePower.Banach.mOf q)
    Gf := fun x : (Fin d → ℝ) => |σ x| + 1
    Ef := fun x : (Fin d → ℝ) =>
      C * (‖fun i => φ i x‖ ^ (α - 1)
                + (|σ x| + 1) ^ (β - β / α)
                + 1)
          * ∑ i, |φ i x - Du i x|
    hGf_memLp := hGf_envelope_memLp_betaBar_transport (σ := σ) hσ_memLp
    hEf_memLp := hEf_envelope_memLp_betaBarPrime_transport_bare hα hβ
                  (C := C) (σ := σ) (φ := φ) (Du := Du)
                  hσ_memLp hφ_memLp hDu_memLp
    hGf_bd :=
      StationaryMFG.Theorems.SimplePower.Banach.transport_perturbation_hGf_bd
        (σ := σ)
    hEf_bd :=
      StationaryMFG.Theorems.SimplePower.Banach.transport_perturbation_hEf_bd_ae
        hα hβ hC (σ := σ) hσ_nn (φ := φ) (Du := Du) hDpH_upper
    Gm := fun x : (Fin d → ℝ) => |σ x| + 2
    Em := fun x : (Fin d → ℝ) =>
          |υ x - StationaryMFG.Theorems.SimplePower.Banach.uOf q x|
    hGm_memLp := hGm_envelope_memLp_betaBar_transport (σ := σ) hσ_memLp
    hEm_memLp := hEm_envelope_memLp_betaBarPrime_bare hα hβ
                  (υ := υ) (u := StationaryMFG.Theorems.SimplePower.Banach.uOf q)
                  hυ_memLp
                  (StationaryMFG.Theorems.SimplePower.Banach.memLpPer_of_lpPer
                    (d := d) q.2.1)
    hGm_bd :=
      StationaryMFG.Theorems.SimplePower.Banach.transport_perturbation_hGm_bd
        (σ := σ)
    hEm_bd :=
      StationaryMFG.Theorems.SimplePower.Banach.transport_perturbation_hEm_bd
        (υ := υ) (u := StationaryMFG.Theorems.SimplePower.Banach.uOf q) }

/-! ### `paperSolFor-supplier-user-probe-cont` — closed-form
signed-family user-probe operator-continuity supplier (iter 0621).

Drains the `hSignedUserProbeCont` per-query parameter from the
iter-0612 `paperSection8_hMinty_signed_user_probe_of_paperHypotheses`
producer. The continuity certificate is the `Tendsto` of
`mfgOperatorEpsPair` along the strict-positive signed perturbation
`μ_n := mOf q + σ · mOf q · 1_S + 1/(n+1)` at a **user-supplied**
test probe `(Dυ, υ)`, with test direction `(Dυ - DuOf q, υ - uOf q)`.

**Reduction strategy.** The user-probe Tendsto matches the existing
set-family Tendsto
`mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses` at
the substitution
```
S' := Set.univ,
ρ' := mOf q + σ · mOf q · 1_S,
m := mOf q, u := uOf q, Du := DuOf q.
```
Indeed `Set.univ.indicator ρ' = ρ'` pointwise, so:
* the set sequence `S'.indicator ρ' + 1/(n+1) = mOf q + σ · mOf q · 1_S
  + 1/(n+1)` matches the user-probe sequence;
* the set test direction (constant `υ - u`, `Dυ - Du`) matches the
  user-probe test direction;
* the set η-factor `S'.indicator ρ' + 1/(n+1) - m = σ · mOf q · 1_S +
  1/(n+1)` matches the user-probe η-factor (after limit, `σ · mOf q ·
  1_S`).

The bridge is via `funext` on `Set.univ.indicator ρ' = ρ'`. The set
aggregator's six abstract dominators are discharged by
`setTendstoResidueOf_of_paperHypotheses` at the same substitution.

**`ρ' ≥ 0` a.e.** holds because `mOf q ≥ 0` a.e. (from
`q ∈ K0_Aepsi`) and `1 + σ · 1_S ∈ [0, 2]` for `σ ∈ {±1}`. -/

/-- **`signedUserProbeCont_of_paperHypotheses`** — closed producer for
the `hSignedUserProbeCont` per-query operator-continuity certificate.

Given the paper hypotheses `(hpow, hRegH, hHat0, hFin, hAgree)` and
the per-query Lp + measurability data on `q, υ, Dυ, V`, produce the
`Tendsto` of `mfgOperatorEpsPair` along the signed perturbation
`μ_n := mOf q + σ · mOf q · 1_S + 1/(n+1)` at the user probe
`(Dυ, υ)` and the user test direction `(Dυ - DuOf q, υ - uOf q)`.

The body reduces to the set-family aggregator
`mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses` at
`S := Set.univ, ρ := mOf q + σ · mOf q · 1_S`, then rewrites the
conclusion via `Set.univ.indicator ρ = ρ` (pointwise) to match the
user-probe shape. The six abstract dominators are produced by
`setTendstoResidueOf_of_paperHypotheses` at the same substitution.

**Constraint preserved.** This producer is internal-only and never
added as an authorisation parameter to
`T10PaperResidues.of_paperHypotheses`. -/
noncomputable def signedUserProbeCont_of_paperHypotheses
    {d : ℕ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (hRegH : Hamiltonian.RegularityH (d := d) H DpH)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hFin : Hamiltonian.Hext_finite_at_zero (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    [Fact (1 ≤ ENNReal.ofReal (hpow.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))]
    {ε : ℝ}
    (q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
            (hpow.β + 1) (hpow.α * (hpow.β + 1) / hpow.β))
    (hq_K0 : q ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi d
              (hpow.β + 1) (hpow.α * (hpow.β + 1) / hpow.β))
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (S : Set (Fin d → ℝ)) (hS : MeasurableSet S)
    (υ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    -- Per-query measurability data (υ, Dυ).
    -- Strict `V`-measurability removed (iter 0710,
    -- `paperSolFor-final-phase5-aggregator-closed-V-meas-bridge-signed-suppliers`);
    -- AE-strong-measurability of `V` is derived from `hV_memLp` below.
    (hυ_meas : Measurable υ)
    (hDυ_meas : ∀ i, Measurable (Dυ i))
    -- Per-query Lp data (υ, Dυ at γ̄; V at β̄').
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
            (hpow.α * (hpow.β + 1) / hpow.β) ε
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
              StationaryMFG.Theorems.SimplePower.Banach.uOf q x))) := by
  classical
  -- The "perturbed density without `1/(n+1)`":
  -- `ρ x := mOf q x + σ · mOf q x · 1_S(x)`.
  let ρ : (Fin d → ℝ) → ℝ :=
    fun x => StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
              σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
  -- Lp/measurability data on `mOf q, uOf q, DuOf q` from `q : XBanach`.
  have hm_memLp : Periodic.MemLpPer (d := d)
      (ENNReal.ofReal (hpow.β + 1))
      (StationaryMFG.Theorems.SimplePower.Banach.mOf q) :=
    StationaryMFG.Theorems.SimplePower.Banach.memLpPer_of_lpPer
      (d := d) q.1
  have hm_meas : Measurable
      (StationaryMFG.Theorems.SimplePower.Banach.mOf q) :=
    (MeasureTheory.Lp.stronglyMeasurable q.1).measurable
  -- `mOf q ≥ 0` a.e. (from `q ∈ K0_Aepsi`).
  have hm_nn : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
                  0 ≤ StationaryMFG.Theorems.SimplePower.Banach.mOf q x := hq_K0
  -- Measurability of `ρ`.
  have hInd_meas : Measurable
      (fun x : (Fin d → ℝ) =>
        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) :=
    measurable_const.indicator hS
  have hρ_meas : Measurable ρ := by
    have h1 : Measurable
        (fun x : (Fin d → ℝ) =>
          σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x) :=
      measurable_const.mul hm_meas
    have h2 : Measurable
        (fun x : (Fin d → ℝ) =>
          σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) :=
      h1.mul hInd_meas
    exact hm_meas.add h2
  -- Sign bounds.
  have hσ_lb : (-1 : ℝ) ≤ σ := by rcases hσ with hσ' | hσ' <;> simp [hσ']
  have hσ_ub : σ ≤ 1 := by rcases hσ with hσ' | hσ' <;> simp [hσ']
  -- `ρ ≥ 0` a.e.: `ρ x = m x * (1 + σ * 1_S x)`, and `m ≥ 0`, `(1 + σ · 1_S) ≥ 0`.
  have hρ_nn :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)), 0 ≤ ρ x := by
    filter_upwards [hm_nn] with x hx_mnn
    -- `0 ≤ 1_S x ≤ 1`.
    have hInd_bd : 0 ≤ S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x ∧
        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x ≤ 1 := by
      by_cases hxS : x ∈ S
      · refine ⟨?_, ?_⟩
        · simp [Set.indicator_of_mem hxS]
        · simp [Set.indicator_of_mem hxS]
      · refine ⟨?_, ?_⟩
        · simp [Set.indicator_of_notMem hxS]
        · simp [Set.indicator_of_notMem hxS]
    -- `1 + σ · 1_S x ≥ 0`.
    have hfactor_nn : 0 ≤ 1 + σ *
        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
      by_cases hxS : x ∈ S
      · rw [Set.indicator_of_mem hxS]
        simp only [mul_one]
        linarith
      · rw [Set.indicator_of_notMem hxS]
        simp
    -- `ρ x = mOf q x · (1 + σ · 1_S x) ≥ 0`.
    change 0 ≤ StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
              σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
    have h_eq :
        StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
            σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
          = StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
              (1 + σ * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by ring
    rw [h_eq]
    exact mul_nonneg hx_mnn hfactor_nn
  -- `ρ ∈ L^{β+1}_per`: `mOf q ∈ L^{β+1}_per` and `σ · mOf q · 1_S ∈ L^{β+1}_per`.
  have hσm_memLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1))
      (fun x => σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x) := by
    have hsmul := hm_memLp.const_smul (𝕜 := ℝ) σ
    have heq : (σ • (StationaryMFG.Theorems.SimplePower.Banach.mOf q :
                          (Fin d → ℝ) → ℝ))
                = fun x => σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x :=
      rfl
    rw [heq] at hsmul; exact hsmul
  have hSσm_memLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1))
      (S.indicator
        (fun x => σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x)) :=
    MemLp.toMemLpPer (MeasureTheory.MemLp.indicator hS.nullMeasurableSet hσm_memLp.toMemLp)
  have hSσm_funEq :
      (S.indicator
          (fun x => σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x) :
            (Fin d → ℝ) → ℝ)
        = fun x => σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
    funext x
    by_cases hx : x ∈ S
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have hSσm_memLp' : Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1))
      (fun x => σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
    rw [← hSσm_funEq]; exact hSσm_memLp
  have hρ_memLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1)) ρ := by
    have h := MemLpPer.add hm_memLp hSσm_memLp'
    have heq :
        ((StationaryMFG.Theorems.SimplePower.Banach.mOf q :
              (Fin d → ℝ) → ℝ)
            + (fun x => σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
          = ρ := by
      funext x; rfl
    rw [heq] at h; exact h
  -- The set version uses `S' := Set.univ, ρ' := ρ`. Then
  -- `Set.univ.indicator ρ x = ρ x` for every `x`.
  have h_ind_univ : ∀ x : (Fin d → ℝ),
      (Set.univ : Set (Fin d → ℝ)).indicator ρ x = ρ x := by
    intro x; simp
  have h_ind_univ_eq :
      (Set.univ : Set (Fin d → ℝ)).indicator ρ = ρ := by
    funext x; exact h_ind_univ x
  -- `Set.univ.indicator ρ ∈ L^{β+1}_per` (after rewriting via `h_ind_univ_eq`).
  have hSρ_memLp_univ : Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1))
      ((Set.univ : Set (Fin d → ℝ)).indicator ρ) := by
    rw [h_ind_univ_eq]; exact hρ_memLp
  -- `hExp` bundle at the paper-canonical quadruple.
  have hExp_paper :
      SimplePowerExponentFacts
          (SimplePowerExponentFacts.paperGammaBarReal hpow.α hpow.β)
          (SimplePowerExponentFacts.paperBetaBar hpow.β)
          (SimplePowerExponentFacts.paperGammaBar hpow.α hpow.β)
          (SimplePowerExponentFacts.paperBetaBarPrime hpow.β) :=
    SimplePowerExponentFacts.ofPowerGrowth hpow
  have hExp :
      SimplePowerExponentFacts (hpow.α * (hpow.β + 1) / hpow.β)
          (ENNReal.ofReal (hpow.β + 1))
          (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))
          (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) := by
    have h1 :
        (SimplePowerExponentFacts.paperBetaBar hpow.β)
          = ENNReal.ofReal (hpow.β + 1) := by
      simp [SimplePowerExponentFacts.paperBetaBar]
    have h2 :
        (SimplePowerExponentFacts.paperGammaBar hpow.α hpow.β)
          = ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β) := by
      simp [SimplePowerExponentFacts.paperGammaBar]
    have h3 :
        (SimplePowerExponentFacts.paperBetaBarPrime hpow.β)
          = ENNReal.ofReal ((hpow.β + 1) / hpow.β) := by
      simp [SimplePowerExponentFacts.paperBetaBarPrime]
    have h4 :
        (SimplePowerExponentFacts.paperGammaBarReal hpow.α hpow.β)
          = hpow.α * (hpow.β + 1) / hpow.β := by
      simp [SimplePowerExponentFacts.paperGammaBarReal]
    have := hExp_paper
    rw [h1, h2, h3, h4] at this
    exact this
  -- Build the per-query `SetTendstoResidueOf` bundle at the substitution
  -- `S := Set.univ, ρ := ρ, υ := υ, Dυ := Dυ`.
  let r : StationaryMFG.Theorems.SimplePower.Banach.SetTendstoResidueOf
            (d := d) (V := V) (H := H) (DpH := DpH)
            (βBarReal := hpow.β + 1)
            (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
            hpow q (Set.univ : Set (Fin d → ℝ)) ρ υ Dυ :=
    setTendstoResidueOf_of_paperHypotheses (V := V) (H := H) (DpH := DpH)
      hpow q (Set.univ : Set (Fin d → ℝ)) MeasurableSet.univ ρ υ Dυ
      hυ_meas.aestronglyMeasurable
      (fun i => (hDυ_meas i).aestronglyMeasurable)
      hSρ_memLp_univ hυ_memLp hDυ_memLp hV_memLp hρ_nn
  -- Apply the set-family aggregator (AE-V variant) to produce the
  -- set-form `Tendsto`. AE-strong measurability of `V` comes from
  -- `hV_memLp.aestronglyMeasurable`.
  have hSetTendsto :=
    StationaryMFG.Theorems.SimplePower.Banach.mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses_of_aestronglyMeasurable
      (ε := ε) (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
      (βBarReal := hpow.β + 1) (βBarReal' := (hpow.β + 1) / hpow.β)
      (γBarReal' := (hpow.α * (hpow.β + 1) / hpow.β) /
                      (hpow.α * (hpow.β + 1) / hpow.β - 1))
      hpow hRegH hExp hHat0 hFin hAgree
      Dυ υ (StationaryMFG.Theorems.SimplePower.Banach.uOf q)
      (fun i => StationaryMFG.Theorems.SimplePower.Banach.DuOf q i)
      (StationaryMFG.Theorems.SimplePower.Banach.mOf q) V
      (Set.univ : Set (Fin d → ℝ)) ρ
      MeasurableSet.univ (hρ_meas.indicator MeasurableSet.univ).aestronglyMeasurable
      ((MeasureTheory.Lp.stronglyMeasurable q.1).measurable)
      hV_memLp.aestronglyMeasurable hυ_meas.aestronglyMeasurable
      ((MeasureTheory.Lp.stronglyMeasurable q.2.1).measurable)
      (fun i => (hDυ_meas i).aestronglyMeasurable)
      (fun i => (MeasureTheory.Lp.stronglyMeasurable (q.2.2 i)).measurable)
      hρ_nn hSρ_memLp_univ
      r.Gh r.Eh r.hGh_memLp r.hEh_memLp r.hGh_bd r.hEh_bd
      r.Gf r.Ef r.hGf_memLp r.hEf_memLp r.hGf_bd r.hEf_bd
      r.Gm r.Em r.hGm_memLp r.hEm_memLp r.hGm_bd r.hEm_bd
  -- The set-form `Tendsto` uses `Set.univ.indicator ρ` (both in
  -- λ-bodies and as bare functions). Rewrite both forms:
  -- * `simp_rw [h_ind_univ]` handles `(Set.univ.indicator ρ) x → ρ x`
  --   inside λ-bodies.
  -- * `rw [h_ind_univ_eq]` handles bare function references.
  simp_rw [h_ind_univ] at hSetTendsto
  rw [h_ind_univ_eq] at hSetTendsto
  -- After both rewrites, the η-factor on the limit side becomes
  -- `ρ - Banach.mOf q` (function-level subtraction). Rewrite this
  -- to the explicit `σ · m · 1_S` form.
  have h_lim_sub_eq :
      ((ρ : (Fin d → ℝ) → ℝ) -
        StationaryMFG.Theorems.SimplePower.Banach.mOf q)
        = (fun x : (Fin d → ℝ) =>
            σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
    funext x
    change StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
            σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
          - StationaryMFG.Theorems.SimplePower.Banach.mOf q x = _
    ring
  rw [h_lim_sub_eq] at hSetTendsto
  -- Now `hSetTendsto` has the limit side in the user-probe shape.
  -- Use `Tendsto.congr` to align the sequence-side η-factor with the
  -- user-probe shape.
  refine hSetTendsto.congr (fun n => ?_)
  -- For each `n`, show the user-probe `mfgOperatorEpsPair` equals the
  -- set-form one (now with bare `ρ`). These are definitionally equal
  -- by `let`-unfolding of `ρ` and `Pi.sub_apply`.
  rfl

/-- **`signedUserProbeCont_of_paperHypotheses_of_aestronglyMeasurable`**
— AE-strong-measurable wrapper around the strict producer
`signedUserProbeCont_of_paperHypotheses`. The strict version requires
strict-`Measurable` witnesses on `υ, Dυ i`, but the partial aggregator
caller (the closed `hSignedUserProbeCont` supplier consumed by
`paperSection8_hMinty_signed_user_probe_of_paperHypotheses`) only has
`MemSobolevPer υ` + `MemLpPer (Dυ i)`. We bridge by extracting
measurable representatives via `MemLpPer.aestronglyMeasurable.mk` and
transporting the resulting `Tendsto` back via
`mfgOperatorEpsPair_congr_ae_primal` (for the primal `(Dυ, υ)` slot)
and `mfgOperatorEpsPair_congr_ae` (for the test slot `Dν := Dυ -
DuOf q`, `ν := υ - uOf q`).

This is the third of four `testdata-meas-bridge-*` siblings; mirrors
iter-0690 (set) and iter-0691 (transport), but the conclusion is a
bare `Tendsto`, not a struct field — no struct refactor needed. -/
noncomputable def signedUserProbeCont_of_paperHypotheses_of_aestronglyMeasurable
    {d : ℕ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (hRegH : Hamiltonian.RegularityH (d := d) H DpH)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hFin : Hamiltonian.Hext_finite_at_zero (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    [Fact (1 ≤ ENNReal.ofReal (hpow.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))]
    {ε : ℝ}
    (q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
            (hpow.β + 1) (hpow.α * (hpow.β + 1) / hpow.β))
    (hq_K0 : q ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi d
              (hpow.β + 1) (hpow.α * (hpow.β + 1) / hpow.β))
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (S : Set (Fin d → ℝ)) (hS : MeasurableSet S)
    (υ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    -- Per-query Lp data (υ, Dυ at γ̄; V at β̄'). Strict-`Measurable`
    -- inputs for `V, υ, Dυ i` have been replaced by AE-strong-measurable
    -- accessors derived from these Lp certificates (the strict
    -- `V`-measurability parameter was removed iter 0710,
    -- `paperSolFor-final-phase5-aggregator-closed-V-meas-bridge-signed-suppliers`).
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
            (hpow.α * (hpow.β + 1) / hpow.β) ε
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
              StationaryMFG.Theorems.SimplePower.Banach.uOf q x))) := by
  classical
  -- Measurable representatives of `υ, Dυ i` derived from their Lp
  -- certificates (each a.e.-equal to the original on the cube).
  set υ' : (Fin d → ℝ) → ℝ := hυ_memLp.aestronglyMeasurable.mk υ
    with hυ'_def
  set Dυ' : Fin d → (Fin d → ℝ) → ℝ :=
    fun i => (hDυ_memLp i).aestronglyMeasurable.mk (Dυ i)
    with hDυ'_def
  have hυ'_meas : Measurable υ' :=
    hυ_memLp.aestronglyMeasurable.measurable_mk
  have hDυ'_meas : ∀ i, Measurable (Dυ' i) := fun i =>
    (hDυ_memLp i).aestronglyMeasurable.measurable_mk
  have hυ'_ae :
      υ =ᵐ[MeasureTheory.volume.restrict (Periodic.UnitCube d)] υ' :=
    hυ_memLp.aestronglyMeasurable.ae_eq_mk
  have hDυ'_ae : ∀ i,
      Dυ i =ᵐ[MeasureTheory.volume.restrict (Periodic.UnitCube d)] Dυ' i :=
    fun i => (hDυ_memLp i).aestronglyMeasurable.ae_eq_mk
  -- Transport `MemLpPer` to the reps.
  have hυ'_memLp : Periodic.MemLpPer (d := d)
      (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) υ' :=
    hυ_memLp.congr_ae_unitCube hυ'_ae
  have hDυ'_memLp : ∀ i, Periodic.MemLpPer (d := d)
      (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) (Dυ' i) := fun i =>
    (hDυ_memLp i).congr_ae_unitCube (hDυ'_ae i)
  -- Apply the strict producer at the measurable reps.
  have h_prime :=
    signedUserProbeCont_of_paperHypotheses
      (V := V) (H := H) (DpH := DpH)
      hpow hRegH hHat0 hFin hAgree (ε := ε)
      q hq_K0 σ hσ S hS υ' Dυ'
      hυ'_meas hDυ'_meas
      hυ'_memLp hDυ'_memLp hV_memLp
  -- Build the `=ᵐ` equalities needed to bridge `(υ', Dυ') → (υ, Dυ)`
  -- inside each `mfgOperatorEpsPair` (both sequence and limit terms).
  -- Test direction `Dν` shape: `Dν i x = Dυ i x - DuOf q i x`.
  have hDνdiff_ae : ∀ i,
      (fun x : (Fin d → ℝ) =>
          Dυ' i x - StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
        =ᵐ[MeasureTheory.volume.restrict (Periodic.UnitCube d)]
      (fun x : (Fin d → ℝ) =>
          Dυ i x - StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x) := by
    intro i
    filter_upwards [hDυ'_ae i] with x hx
    rw [← hx]
  -- Test slot `ν` shape: `ν x = υ x - uOf q x`.
  have hνdiff_ae :
      (fun x : (Fin d → ℝ) =>
          υ' x - StationaryMFG.Theorems.SimplePower.Banach.uOf q x)
        =ᵐ[MeasureTheory.volume.restrict (Periodic.UnitCube d)]
      (fun x : (Fin d → ℝ) =>
          υ x - StationaryMFG.Theorems.SimplePower.Banach.uOf q x) := by
    filter_upwards [hυ'_ae] with x hx
    rw [← hx]
  -- Primal `Dυ` a.e. equality (slot 1 of `mfgOperatorEpsPair`).
  have hDυprim_ae : ∀ i,
      Dυ' i =ᵐ[MeasureTheory.volume.restrict (Periodic.UnitCube d)] Dυ i :=
    fun i => (hDυ'_ae i).symm
  -- Primal `υ` a.e. equality (slot 3 of `mfgOperatorEpsPair`).
  have hυprim_ae :
      υ' =ᵐ[MeasureTheory.volume.restrict (Periodic.UnitCube d)] υ :=
    hυ'_ae.symm
  -- For each `n`, the sequence term at `(υ', Dυ')` equals the one at
  -- `(υ, Dυ)`. Use primal-congr (slots 1, 2 [μ unchanged], 3) +
  -- test-congr (Dν, η unchanged, ν).
  have hSeq_eq : ∀ n : ℕ,
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
        (hpow.α * (hpow.β + 1) / hpow.β) ε
        Dυ'
        (fun x =>
          StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
            σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
            + 1 / ((n : ℝ) + 1))
        υ'
        (fun i x => Dυ' i x -
          StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
        (fun x =>
          (StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
            σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
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
          StationaryMFG.Theorems.SimplePower.Banach.uOf q x) := by
    intro n
    -- Primal swap: (Dυ', μ, υ') → (Dυ, μ, υ).
    rw [mfgOperatorEpsPair_congr_ae_primal (V := V) (H := H) (DpH := DpH)
          (γBar := hpow.α * (hpow.β + 1) / hpow.β) (ε := ε)
          Dυ' Dυ
          (fun x =>
            StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
              σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
              + 1 / ((n : ℝ) + 1))
          (fun x =>
            StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
              σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
              + 1 / ((n : ℝ) + 1))
          υ' υ
          (fun i x => Dυ' i x -
            StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
          (fun x =>
            (StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
              σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
              + 1 / ((n : ℝ) + 1)) -
            StationaryMFG.Theorems.SimplePower.Banach.mOf q x)
          (fun x => υ' x -
            StationaryMFG.Theorems.SimplePower.Banach.uOf q x)
          hDυprim_ae (Filter.EventuallyEq.refl _ _) hυprim_ae]
    -- Test swap: (Dυ' - DuOf, η unchanged, υ' - uOf) → (Dυ - DuOf, η, υ - uOf).
    rw [mfgOperatorEpsPair_congr_ae (V := V) (H := H) (DpH := DpH)
          (γBar := hpow.α * (hpow.β + 1) / hpow.β) (ε := ε)
          Dυ
          (fun x =>
            StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
              σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
              + 1 / ((n : ℝ) + 1))
          υ
          (fun i x => Dυ' i x -
            StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
          (fun i x => Dυ i x -
            StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
          (fun x =>
            (StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
              σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
              + 1 / ((n : ℝ) + 1)) -
            StationaryMFG.Theorems.SimplePower.Banach.mOf q x)
          (fun x =>
            (StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
              σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
              + 1 / ((n : ℝ) + 1)) -
            StationaryMFG.Theorems.SimplePower.Banach.mOf q x)
          (fun x => υ' x -
            StationaryMFG.Theorems.SimplePower.Banach.uOf q x)
          (fun x => υ x -
            StationaryMFG.Theorems.SimplePower.Banach.uOf q x)
          hDνdiff_ae (Filter.EventuallyEq.refl _ _) hνdiff_ae]
  -- The limit term at `(υ', Dυ')` equals the one at `(υ, Dυ)`.
  have hLim_eq :
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
        (hpow.α * (hpow.β + 1) / hpow.β) ε
        Dυ'
        (fun x =>
          StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
            σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
        υ'
        (fun i x => Dυ' i x -
          StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
        (fun x =>
          σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
        (fun x => υ' x -
          StationaryMFG.Theorems.SimplePower.Banach.uOf q x)
      =
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
        (hpow.α * (hpow.β + 1) / hpow.β) ε
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
          StationaryMFG.Theorems.SimplePower.Banach.uOf q x) := by
    rw [mfgOperatorEpsPair_congr_ae_primal (V := V) (H := H) (DpH := DpH)
          (γBar := hpow.α * (hpow.β + 1) / hpow.β) (ε := ε)
          Dυ' Dυ
          (fun x =>
            StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
              σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          (fun x =>
            StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
              σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          υ' υ
          (fun i x => Dυ' i x -
            StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
          (fun x =>
            σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          (fun x => υ' x -
            StationaryMFG.Theorems.SimplePower.Banach.uOf q x)
          hDυprim_ae (Filter.EventuallyEq.refl _ _) hυprim_ae]
    rw [mfgOperatorEpsPair_congr_ae (V := V) (H := H) (DpH := DpH)
          (γBar := hpow.α * (hpow.β + 1) / hpow.β) (ε := ε)
          Dυ
          (fun x =>
            StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
              σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          υ
          (fun i x => Dυ' i x -
            StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
          (fun i x => Dυ i x -
            StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
          (fun x =>
            σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          (fun x =>
            σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          (fun x => υ' x -
            StationaryMFG.Theorems.SimplePower.Banach.uOf q x)
          (fun x => υ x -
            StationaryMFG.Theorems.SimplePower.Banach.uOf q x)
          hDνdiff_ae (Filter.EventuallyEq.refl _ _) hνdiff_ae]
  -- Transport `h_prime` to the conclusion via the pointwise rewrites.
  have h_seq_funext :
      (fun n : ℕ =>
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          (hpow.α * (hpow.β + 1) / hpow.β) ε
          Dυ'
          (fun x =>
            StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
              σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
              + 1 / ((n : ℝ) + 1))
          υ'
          (fun i x => Dυ' i x -
            StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
          (fun x =>
            (StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
              σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
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
            StationaryMFG.Theorems.SimplePower.Banach.uOf q x)) := by
    funext n; exact hSeq_eq n
  rw [h_seq_funext, hLim_eq] at h_prime
  exact h_prime

/-! ### `paperSolFor-supplier-user-triple-cont` — closed-form
signed-family user-triple operator-continuity supplier (iter 0622).

Drains the `hSignedUserTripleCont` per-query parameter from the
iter-0614 `paperSection8_hMinty_signed_user_triple_of_paperHypotheses`
producer. The continuity certificate is the `Tendsto` of
`mfgOperatorEpsPair` along the strict-positive signed perturbation
`μ_n := μ + σ · μ · 1_S + 1/(n+1)` at a **user-supplied** primal
density `μ` and a **user-supplied** test probe `(Dυ, υ)`, with test
direction `(Dυ - DuOf q, υ - uOf q)` and bare-difference η-factor
`(μ + σ · μ · 1_S) - mOf q` (NOT simplified to `σ · μ · 1_S`, since
in general `μ ≠ mOf q`).

**Reduction strategy.** Mirrors iter-0621 (user-probe) line for line,
with the only substitution change `mOf q ↝ μ` in the perturbation
construction. The user-triple Tendsto matches the existing
set-family Tendsto
`mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses` at
```
S' := Set.univ,
ρ' := μ + σ · μ · 1_S,
m := mOf q, u := uOf q, Du := DuOf q.
```
Indeed `Set.univ.indicator ρ' = ρ'` pointwise, so:
* the set sequence `S'.indicator ρ' + 1/(n+1) = μ + σ · μ · 1_S
  + 1/(n+1)` matches the user-triple sequence;
* the set test direction (constant `υ - u`, `Dυ - Du`) matches the
  user-triple test direction;
* the set η-factor `S'.indicator ρ' + 1/(n+1) - m
  = (μ + σ · μ · 1_S + 1/(n+1)) - mOf q` matches the user-triple
  η-factor directly (no additional algebraic simplification needed
  on the limit side, unlike iter-0621 where the cancellation
  `mOf q + σ · mOf q · 1_S - mOf q = σ · mOf q · 1_S` was required).

The bridge is via `funext` on `Set.univ.indicator ρ' = ρ'`. The set
aggregator's six abstract dominators are discharged by
`setTendstoResidueOf_of_paperHypotheses` at the same substitution.

**`ρ' ≥ 0` a.e.** holds because `μ ≥ 0` a.e. (user-supplied input)
and `1 + σ · 1_S ∈ [0, 2]` for `σ ∈ {±1}`. -/

/-- **`signedUserTripleCont_of_paperHypotheses`** — closed producer for
the `hSignedUserTripleCont` per-query operator-continuity certificate.

Given the paper hypotheses `(hpow, hRegH, hHat0, hFin, hAgree)` and
the per-query Lp + measurability data on `q, μ, υ, Dυ, V`, produce
the `Tendsto` of `mfgOperatorEpsPair` along the signed perturbation
`μ_n := μ + σ · μ · 1_S + 1/(n+1)` at the user triple `(μ, Dυ, υ)`
and the user test direction `(Dυ - DuOf q, υ - uOf q)`.

The body reduces to the set-family aggregator
`mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses` at
`S := Set.univ, ρ := μ + σ · μ · 1_S`, then rewrites the conclusion
via `Set.univ.indicator ρ = ρ` (pointwise) to match the user-triple
shape. The six abstract dominators are produced by
`setTendstoResidueOf_of_paperHypotheses` at the same substitution.

**Constraint preserved.** This producer is internal-only and never
added as an authorisation parameter to
`T10PaperResidues.of_paperHypotheses`. -/
noncomputable def signedUserTripleCont_of_paperHypotheses
    {d : ℕ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (hRegH : Hamiltonian.RegularityH (d := d) H DpH)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hFin : Hamiltonian.Hext_finite_at_zero (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    [Fact (1 ≤ ENNReal.ofReal (hpow.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))]
    {ε : ℝ}
    (q : StationaryMFG.Theorems.SimplePower.Banach.XBanach d
            (hpow.β + 1) (hpow.α * (hpow.β + 1) / hpow.β))
    (_hq_K0 : q ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi d
              (hpow.β + 1) (hpow.α * (hpow.β + 1) / hpow.β))
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (S : Set (Fin d → ℝ)) (hS : MeasurableSet S)
    (μ υ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    -- Per-query measurability data (μ, υ, Dυ). Strict `V`-measurability
    -- was removed iter 0710 (AE-V is derived from `hV_memLp` below).
    (hμ_meas : Measurable μ)
    (hυ_meas : Measurable υ)
    (hDυ_meas : ∀ i, Measurable (Dυ i))
    -- Per-query non-negativity of the user primal density `μ`.
    (hμ_nn : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
                  0 ≤ μ x)
    -- Per-query Lp data (μ at β̄; υ, Dυ at γ̄; V at β̄').
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
  -- The "perturbed density without `1/(n+1)`":
  -- `ρ x := μ x + σ · μ x · 1_S(x)`.
  let ρ : (Fin d → ℝ) → ℝ :=
    fun x => μ x + σ * μ x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
  -- Measurability of `ρ`.
  have hInd_meas : Measurable
      (fun x : (Fin d → ℝ) =>
        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) :=
    measurable_const.indicator hS
  have hρ_meas : Measurable ρ := by
    have h1 : Measurable
        (fun x : (Fin d → ℝ) => σ * μ x) :=
      measurable_const.mul hμ_meas
    have h2 : Measurable
        (fun x : (Fin d → ℝ) =>
          σ * μ x *
            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) :=
      h1.mul hInd_meas
    exact hμ_meas.add h2
  -- Sign bounds.
  have hσ_lb : (-1 : ℝ) ≤ σ := by rcases hσ with hσ' | hσ' <;> simp [hσ']
  have hσ_ub : σ ≤ 1 := by rcases hσ with hσ' | hσ' <;> simp [hσ']
  -- `ρ ≥ 0` a.e.: `ρ x = μ x * (1 + σ * 1_S x)`, and `μ ≥ 0`, `(1 + σ · 1_S) ≥ 0`.
  have hρ_nn :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)), 0 ≤ ρ x := by
    filter_upwards [hμ_nn] with x hx_μnn
    -- `0 ≤ 1_S x ≤ 1`.
    have hInd_bd : 0 ≤ S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x ∧
        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x ≤ 1 := by
      by_cases hxS : x ∈ S
      · refine ⟨?_, ?_⟩
        · simp [Set.indicator_of_mem hxS]
        · simp [Set.indicator_of_mem hxS]
      · refine ⟨?_, ?_⟩
        · simp [Set.indicator_of_notMem hxS]
        · simp [Set.indicator_of_notMem hxS]
    -- `1 + σ · 1_S x ≥ 0`.
    have hfactor_nn : 0 ≤ 1 + σ *
        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
      by_cases hxS : x ∈ S
      · rw [Set.indicator_of_mem hxS]
        simp only [mul_one]
        linarith
      · rw [Set.indicator_of_notMem hxS]
        simp
    -- `ρ x = μ x · (1 + σ · 1_S x) ≥ 0`.
    change 0 ≤ μ x + σ * μ x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
    have h_eq :
        μ x + σ * μ x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
          = μ x *
              (1 + σ * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by ring
    rw [h_eq]
    exact mul_nonneg hx_μnn hfactor_nn
  -- `ρ ∈ L^{β+1}_per`: `μ ∈ L^{β+1}_per` and `σ · μ · 1_S ∈ L^{β+1}_per`.
  have hσμ_memLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1))
      (fun x => σ * μ x) := by
    have hsmul := hμ_memLp.const_smul (𝕜 := ℝ) σ
    have heq : (σ • (μ : (Fin d → ℝ) → ℝ))
                = fun x => σ * μ x :=
      rfl
    rw [heq] at hsmul; exact hsmul
  have hSσμ_memLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1))
      (S.indicator
        (fun x => σ * μ x)) :=
    MemLp.toMemLpPer (MeasureTheory.MemLp.indicator hS.nullMeasurableSet hσμ_memLp.toMemLp)
  have hSσμ_funEq :
      (S.indicator
          (fun x => σ * μ x) :
            (Fin d → ℝ) → ℝ)
        = fun x => σ * μ x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
    funext x
    by_cases hx : x ∈ S
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have hSσμ_memLp' : Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1))
      (fun x => σ * μ x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
    rw [← hSσμ_funEq]; exact hSσμ_memLp
  have hρ_memLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1)) ρ := by
    have h := MemLpPer.add hμ_memLp hSσμ_memLp'
    have heq :
        ((μ : (Fin d → ℝ) → ℝ)
            + (fun x => σ * μ x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
          = ρ := by
      funext x; rfl
    rw [heq] at h; exact h
  -- The set version uses `S' := Set.univ, ρ' := ρ`. Then
  -- `Set.univ.indicator ρ x = ρ x` for every `x`.
  have h_ind_univ : ∀ x : (Fin d → ℝ),
      (Set.univ : Set (Fin d → ℝ)).indicator ρ x = ρ x := by
    intro x; simp
  have h_ind_univ_eq :
      (Set.univ : Set (Fin d → ℝ)).indicator ρ = ρ := by
    funext x; exact h_ind_univ x
  -- `Set.univ.indicator ρ ∈ L^{β+1}_per` (after rewriting via `h_ind_univ_eq`).
  have hSρ_memLp_univ : Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1))
      ((Set.univ : Set (Fin d → ℝ)).indicator ρ) := by
    rw [h_ind_univ_eq]; exact hρ_memLp
  -- `hExp` bundle at the paper-canonical quadruple.
  have hExp_paper :
      SimplePowerExponentFacts
          (SimplePowerExponentFacts.paperGammaBarReal hpow.α hpow.β)
          (SimplePowerExponentFacts.paperBetaBar hpow.β)
          (SimplePowerExponentFacts.paperGammaBar hpow.α hpow.β)
          (SimplePowerExponentFacts.paperBetaBarPrime hpow.β) :=
    SimplePowerExponentFacts.ofPowerGrowth hpow
  have hExp :
      SimplePowerExponentFacts (hpow.α * (hpow.β + 1) / hpow.β)
          (ENNReal.ofReal (hpow.β + 1))
          (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))
          (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) := by
    have h1 :
        (SimplePowerExponentFacts.paperBetaBar hpow.β)
          = ENNReal.ofReal (hpow.β + 1) := by
      simp [SimplePowerExponentFacts.paperBetaBar]
    have h2 :
        (SimplePowerExponentFacts.paperGammaBar hpow.α hpow.β)
          = ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β) := by
      simp [SimplePowerExponentFacts.paperGammaBar]
    have h3 :
        (SimplePowerExponentFacts.paperBetaBarPrime hpow.β)
          = ENNReal.ofReal ((hpow.β + 1) / hpow.β) := by
      simp [SimplePowerExponentFacts.paperBetaBarPrime]
    have h4 :
        (SimplePowerExponentFacts.paperGammaBarReal hpow.α hpow.β)
          = hpow.α * (hpow.β + 1) / hpow.β := by
      simp [SimplePowerExponentFacts.paperGammaBarReal]
    have := hExp_paper
    rw [h1, h2, h3, h4] at this
    exact this
  -- Build the per-query `SetTendstoResidueOf` bundle at the substitution
  -- `S := Set.univ, ρ := ρ, υ := υ, Dυ := Dυ`.
  let r : StationaryMFG.Theorems.SimplePower.Banach.SetTendstoResidueOf
            (d := d) (V := V) (H := H) (DpH := DpH)
            (βBarReal := hpow.β + 1)
            (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
            hpow q (Set.univ : Set (Fin d → ℝ)) ρ υ Dυ :=
    setTendstoResidueOf_of_paperHypotheses (V := V) (H := H) (DpH := DpH)
      hpow q (Set.univ : Set (Fin d → ℝ)) MeasurableSet.univ ρ υ Dυ
      hυ_meas.aestronglyMeasurable
      (fun i => (hDυ_meas i).aestronglyMeasurable)
      hSρ_memLp_univ hυ_memLp hDυ_memLp hV_memLp hρ_nn
  -- Apply the set-family aggregator (AE-V variant) to produce the
  -- set-form `Tendsto`. AE-strong measurability of `V` comes from
  -- `hV_memLp.aestronglyMeasurable`.
  have hSetTendsto :=
    StationaryMFG.Theorems.SimplePower.Banach.mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses_of_aestronglyMeasurable
      (ε := ε) (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
      (βBarReal := hpow.β + 1) (βBarReal' := (hpow.β + 1) / hpow.β)
      (γBarReal' := (hpow.α * (hpow.β + 1) / hpow.β) /
                      (hpow.α * (hpow.β + 1) / hpow.β - 1))
      hpow hRegH hExp hHat0 hFin hAgree
      Dυ υ (StationaryMFG.Theorems.SimplePower.Banach.uOf q)
      (fun i => StationaryMFG.Theorems.SimplePower.Banach.DuOf q i)
      (StationaryMFG.Theorems.SimplePower.Banach.mOf q) V
      (Set.univ : Set (Fin d → ℝ)) ρ
      MeasurableSet.univ (hρ_meas.indicator MeasurableSet.univ).aestronglyMeasurable
      ((MeasureTheory.Lp.stronglyMeasurable q.1).measurable)
      hV_memLp.aestronglyMeasurable hυ_meas.aestronglyMeasurable
      ((MeasureTheory.Lp.stronglyMeasurable q.2.1).measurable)
      (fun i => (hDυ_meas i).aestronglyMeasurable)
      (fun i => (MeasureTheory.Lp.stronglyMeasurable (q.2.2 i)).measurable)
      hρ_nn hSρ_memLp_univ
      r.Gh r.Eh r.hGh_memLp r.hEh_memLp r.hGh_bd r.hEh_bd
      r.Gf r.Ef r.hGf_memLp r.hEf_memLp r.hGf_bd r.hEf_bd
      r.Gm r.Em r.hGm_memLp r.hEm_memLp r.hGm_bd r.hEm_bd
  -- The set-form `Tendsto` uses `Set.univ.indicator ρ` (both in
  -- λ-bodies and as bare functions). Rewrite both forms:
  -- * `simp_rw [h_ind_univ]` handles `(Set.univ.indicator ρ) x → ρ x`
  --   inside λ-bodies.
  -- * `rw [h_ind_univ_eq]` handles bare function references.
  simp_rw [h_ind_univ] at hSetTendsto
  rw [h_ind_univ_eq] at hSetTendsto
  -- For the user-triple shape, no additional algebraic simplification
  -- of the limit-side η-factor is needed: `ρ - mOf q` already matches
  -- `(μ + σ · μ · 1_S) - mOf q` definitionally (via `let`-unfolding of
  -- `ρ` and `Pi.sub_apply`). This is the key difference from
  -- iter-0621 (user-probe), where the cancellation `ρ - mOf q
  -- = σ · mOf q · 1_S` had to be proved by `funext + ring`.
  -- Use `Tendsto.congr` to align the sequence-side η-factor with the
  -- user-triple shape.
  refine hSetTendsto.congr (fun n => ?_)
  -- For each `n`, show the user-triple `mfgOperatorEpsPair` equals the
  -- set-form one (now with bare `ρ`). These are definitionally equal
  -- by `let`-unfolding of `ρ` and `Pi.sub_apply`.
  rfl

/-- **`signedUserTripleCont_of_paperHypotheses_of_aestronglyMeasurable`**
— AE-strong-measurable wrapper around the strict producer
`signedUserTripleCont_of_paperHypotheses`. The strict version requires
strict-`Measurable` witnesses on `μ, υ, Dυ i`, but the partial aggregator
caller only has `MemLpPer μ` + `MemSobolevPer υ` + `MemLpPer (Dυ i)`. We
bridge by extracting measurable representatives via
`MemLpPer.aestronglyMeasurable.mk` and transporting the resulting
`Tendsto` back via `mfgOperatorEpsPair_congr_ae_primal` (for the primal
`(Dυ, μ_seq, υ)` slot) and `mfgOperatorEpsPair_congr_ae` (for the test
slot `Dν, η, ν`).

This is the fourth and final `testdata-meas-bridge-*` sibling. Mirrors
iter-0692 (user-probe), with an additional `μ → μ'` bridge step in
both primal and test slots, since the user-triple consumer takes a
user-supplied primal density `μ`. -/
noncomputable def signedUserTripleCont_of_paperHypotheses_of_aestronglyMeasurable
    {d : ℕ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hpow : Hamiltonian.HypothesisPowerGrowth (d := d) H DpH)
    (hRegH : Hamiltonian.RegularityH (d := d) H DpH)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hFin : Hamiltonian.Hext_finite_at_zero (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
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
    -- Per-query non-negativity of the user primal density `μ`.
    (hμ_nn : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
                  0 ≤ μ x)
    -- Per-query Lp data (μ at β̄; υ, Dυ at γ̄; V at β̄'). Strict-`Measurable`
    -- inputs for `V, μ, υ, Dυ i` have been replaced by AE-strong-measurable
    -- accessors derived from these Lp certificates (strict `V`-measurability
    -- was removed iter 0710,
    -- `paperSolFor-final-phase5-aggregator-closed-V-meas-bridge-signed-suppliers`).
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
  -- Measurable representatives of `μ, υ, Dυ i` derived from their Lp
  -- certificates (each a.e.-equal to the original on the cube).
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
  -- Transport `MemLpPer` to the reps.
  have hμ'_memLp : Periodic.MemLpPer (d := d)
      (ENNReal.ofReal (hpow.β + 1)) μ' :=
    hμ_memLp.congr_ae_unitCube hμ'_ae
  have hυ'_memLp : Periodic.MemLpPer (d := d)
      (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) υ' :=
    hυ_memLp.congr_ae_unitCube hυ'_ae
  have hDυ'_memLp : ∀ i, Periodic.MemLpPer (d := d)
      (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) (Dυ' i) := fun i =>
    (hDυ_memLp i).congr_ae_unitCube (hDυ'_ae i)
  -- Transport `μ ≥ 0` a.e. to `μ' ≥ 0` a.e.
  have hμ'_nn : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
                  0 ≤ μ' x := by
    filter_upwards [hμ_nn, hμ'_ae] with x hxnn hxeq
    rw [← hxeq]; exact hxnn
  -- Apply the strict producer at the measurable reps.
  have h_prime :=
    signedUserTripleCont_of_paperHypotheses
      (V := V) (H := H) (DpH := DpH)
      hpow hRegH hHat0 hFin hAgree (ε := ε)
      q hq_K0 σ hσ S hS μ' υ' Dυ'
      hμ'_meas hυ'_meas hDυ'_meas
      hμ'_nn hμ'_memLp hυ'_memLp hDυ'_memLp hV_memLp
  -- Build the `=ᵐ` equalities needed to bridge `(μ', υ', Dυ') → (μ, υ, Dυ)`.
  -- Test direction `Dν` shape: `Dν i x = Dυ i x - DuOf q i x`.
  have hDνdiff_ae : ∀ i,
      (fun x : (Fin d → ℝ) =>
          Dυ' i x - StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
        =ᵐ[MeasureTheory.volume.restrict (Periodic.UnitCube d)]
      (fun x : (Fin d → ℝ) =>
          Dυ i x - StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x) := by
    intro i
    filter_upwards [hDυ'_ae i] with x hx
    rw [← hx]
  -- Test slot `ν` shape: `ν x = υ x - uOf q x`.
  have hνdiff_ae :
      (fun x : (Fin d → ℝ) =>
          υ' x - StationaryMFG.Theorems.SimplePower.Banach.uOf q x)
        =ᵐ[MeasureTheory.volume.restrict (Periodic.UnitCube d)]
      (fun x : (Fin d → ℝ) =>
          υ x - StationaryMFG.Theorems.SimplePower.Banach.uOf q x) := by
    filter_upwards [hυ'_ae] with x hx
    rw [← hx]
  -- Primal `Dυ` a.e. equality (slot 1 of `mfgOperatorEpsPair`).
  have hDυprim_ae : ∀ i,
      Dυ' i =ᵐ[MeasureTheory.volume.restrict (Periodic.UnitCube d)] Dυ i :=
    fun i => (hDυ'_ae i).symm
  -- Primal `υ` a.e. equality (slot 3 of `mfgOperatorEpsPair`).
  have hυprim_ae :
      υ' =ᵐ[MeasureTheory.volume.restrict (Periodic.UnitCube d)] υ :=
    hυ'_ae.symm
  -- Primal `μ_seq` a.e. equality (slot 2) — sequence form.
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
  -- Test slot `η` a.e. equality — sequence form (μ_seq - mOf).
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
  -- Primal `μ_seq` a.e. equality — limit form (drop `1/(n+1)`).
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
  -- Test slot `η` a.e. equality — limit form.
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
  -- For each `n`, the sequence term at `(μ', υ', Dυ')` equals the one at
  -- `(μ, υ, Dυ)`. Use primal-congr (slots 1, 2, 3) + test-congr (Dν, η, ν).
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
    -- Primal swap: (Dυ', μ'_seq, υ') → (Dυ, μ_seq, υ).
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
    -- Test swap: (Dυ' - DuOf, μ'_seq - mOf, υ' - uOf) → (Dυ - DuOf, μ_seq - mOf, υ - uOf).
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
  -- The limit term at `(μ', υ', Dυ')` equals the one at `(μ, υ, Dυ)`.
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
  -- Transport `h_prime` to the conclusion via the pointwise rewrites.
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

/-! ### Hext-free `_of_rc0` user-probe/triple continuity producers
(T3 step 8b)

ε-generic, `Hext_finite_at_zero`-free siblings of the strict
`signedUser{Probe,Triple}Cont_of_paperHypotheses` producers. Two
changes mirror the step-8 set/signed/transport `_of_rc0` producers:

* take the line-1821 right-continuity-at-0 certificate `hH_rc0`
  (accepted T3 rider) instead of `(hHat0, hFin, hAgree)`; and
* route the inner set-form `Tendsto` through the Hext-free step-6
  `mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses_of_aestronglyMeasurable_of_rc0`
  bridge instead of the Hext-pulling `_of_aestronglyMeasurable`
  aggregator.

The probe/triple cores already collapse to the SET core via the
`Set.univ` indicator reduction, so the bodies are byte-for-byte copies
of the strict siblings save for the aggregator-call swap. -/

/-- **`signedUserProbeCont_of_paperHypotheses_of_rc0`** — Hext-free
`_of_rc0` sibling of `signedUserProbeCont_of_paperHypotheses`. Takes
the right-continuity-at-0 rider `hH_rc0` in place of `(hHat0, hFin,
hAgree)` and routes the inner set-form `Tendsto` through the step-6
rc0 set bridge. -/
noncomputable def signedUserProbeCont_of_paperHypotheses_of_rc0
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
    (υ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (hυ_meas : Measurable υ)
    (hDυ_meas : ∀ i, Measurable (Dυ i))
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
            (hpow.α * (hpow.β + 1) / hpow.β) ε
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
              StationaryMFG.Theorems.SimplePower.Banach.uOf q x))) := by
  classical
  let ρ : (Fin d → ℝ) → ℝ :=
    fun x => StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
              σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
  have hm_memLp : Periodic.MemLpPer (d := d)
      (ENNReal.ofReal (hpow.β + 1))
      (StationaryMFG.Theorems.SimplePower.Banach.mOf q) :=
    StationaryMFG.Theorems.SimplePower.Banach.memLpPer_of_lpPer
      (d := d) q.1
  have hm_meas : Measurable
      (StationaryMFG.Theorems.SimplePower.Banach.mOf q) :=
    (MeasureTheory.Lp.stronglyMeasurable q.1).measurable
  have hm_nn : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)),
                  0 ≤ StationaryMFG.Theorems.SimplePower.Banach.mOf q x := hq_K0
  have hInd_meas : Measurable
      (fun x : (Fin d → ℝ) =>
        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) :=
    measurable_const.indicator hS
  have hρ_meas : Measurable ρ := by
    have h1 : Measurable
        (fun x : (Fin d → ℝ) =>
          σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x) :=
      measurable_const.mul hm_meas
    have h2 : Measurable
        (fun x : (Fin d → ℝ) =>
          σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) :=
      h1.mul hInd_meas
    exact hm_meas.add h2
  have hσ_lb : (-1 : ℝ) ≤ σ := by rcases hσ with hσ' | hσ' <;> simp [hσ']
  have hσ_ub : σ ≤ 1 := by rcases hσ with hσ' | hσ' <;> simp [hσ']
  have hρ_nn :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)), 0 ≤ ρ x := by
    filter_upwards [hm_nn] with x hx_mnn
    have hInd_bd : 0 ≤ S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x ∧
        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x ≤ 1 := by
      by_cases hxS : x ∈ S
      · refine ⟨?_, ?_⟩
        · simp [Set.indicator_of_mem hxS]
        · simp [Set.indicator_of_mem hxS]
      · refine ⟨?_, ?_⟩
        · simp [Set.indicator_of_notMem hxS]
        · simp [Set.indicator_of_notMem hxS]
    have hfactor_nn : 0 ≤ 1 + σ *
        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
      by_cases hxS : x ∈ S
      · rw [Set.indicator_of_mem hxS]
        simp only [mul_one]
        linarith
      · rw [Set.indicator_of_notMem hxS]
        simp
    change 0 ≤ StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
              σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
    have h_eq :
        StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
            σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
          = StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
              (1 + σ * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by ring
    rw [h_eq]
    exact mul_nonneg hx_mnn hfactor_nn
  have hσm_memLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1))
      (fun x => σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x) := by
    have hsmul := hm_memLp.const_smul (𝕜 := ℝ) σ
    have heq : (σ • (StationaryMFG.Theorems.SimplePower.Banach.mOf q :
                          (Fin d → ℝ) → ℝ))
                = fun x => σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x :=
      rfl
    rw [heq] at hsmul; exact hsmul
  have hSσm_memLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1))
      (S.indicator
        (fun x => σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x)) :=
    MemLp.toMemLpPer (MeasureTheory.MemLp.indicator hS.nullMeasurableSet hσm_memLp.toMemLp)
  have hSσm_funEq :
      (S.indicator
          (fun x => σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x) :
            (Fin d → ℝ) → ℝ)
        = fun x => σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
    funext x
    by_cases hx : x ∈ S
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have hSσm_memLp' : Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1))
      (fun x => σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
    rw [← hSσm_funEq]; exact hSσm_memLp
  have hρ_memLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1)) ρ := by
    have h := MemLpPer.add hm_memLp hSσm_memLp'
    have heq :
        ((StationaryMFG.Theorems.SimplePower.Banach.mOf q :
              (Fin d → ℝ) → ℝ)
            + (fun x => σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
          = ρ := by
      funext x; rfl
    rw [heq] at h; exact h
  have h_ind_univ : ∀ x : (Fin d → ℝ),
      (Set.univ : Set (Fin d → ℝ)).indicator ρ x = ρ x := by
    intro x; simp
  have h_ind_univ_eq :
      (Set.univ : Set (Fin d → ℝ)).indicator ρ = ρ := by
    funext x; exact h_ind_univ x
  have hSρ_memLp_univ : Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1))
      ((Set.univ : Set (Fin d → ℝ)).indicator ρ) := by
    rw [h_ind_univ_eq]; exact hρ_memLp
  have hExp_paper :
      SimplePowerExponentFacts
          (SimplePowerExponentFacts.paperGammaBarReal hpow.α hpow.β)
          (SimplePowerExponentFacts.paperBetaBar hpow.β)
          (SimplePowerExponentFacts.paperGammaBar hpow.α hpow.β)
          (SimplePowerExponentFacts.paperBetaBarPrime hpow.β) :=
    SimplePowerExponentFacts.ofPowerGrowth hpow
  have hExp :
      SimplePowerExponentFacts (hpow.α * (hpow.β + 1) / hpow.β)
          (ENNReal.ofReal (hpow.β + 1))
          (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))
          (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) := by
    have h1 :
        (SimplePowerExponentFacts.paperBetaBar hpow.β)
          = ENNReal.ofReal (hpow.β + 1) := by
      simp [SimplePowerExponentFacts.paperBetaBar]
    have h2 :
        (SimplePowerExponentFacts.paperGammaBar hpow.α hpow.β)
          = ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β) := by
      simp [SimplePowerExponentFacts.paperGammaBar]
    have h3 :
        (SimplePowerExponentFacts.paperBetaBarPrime hpow.β)
          = ENNReal.ofReal ((hpow.β + 1) / hpow.β) := by
      simp [SimplePowerExponentFacts.paperBetaBarPrime]
    have h4 :
        (SimplePowerExponentFacts.paperGammaBarReal hpow.α hpow.β)
          = hpow.α * (hpow.β + 1) / hpow.β := by
      simp [SimplePowerExponentFacts.paperGammaBarReal]
    have := hExp_paper
    rw [h1, h2, h3, h4] at this
    exact this
  let r : StationaryMFG.Theorems.SimplePower.Banach.SetTendstoResidueOf
            (d := d) (V := V) (H := H) (DpH := DpH)
            (βBarReal := hpow.β + 1)
            (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
            hpow q (Set.univ : Set (Fin d → ℝ)) ρ υ Dυ :=
    setTendstoResidueOf_of_paperHypotheses (V := V) (H := H) (DpH := DpH)
      hpow q (Set.univ : Set (Fin d → ℝ)) MeasurableSet.univ ρ υ Dυ
      hυ_meas.aestronglyMeasurable
      (fun i => (hDυ_meas i).aestronglyMeasurable)
      hSρ_memLp_univ hυ_memLp hDυ_memLp hV_memLp hρ_nn
  -- Hext-free `_of_rc0` set bridge (step 6) instead of the Hext-pulling
  -- `_of_aestronglyMeasurable` aggregator.
  have hSetTendsto :=
    StationaryMFG.Theorems.SimplePower.Banach.mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses_of_aestronglyMeasurable_of_rc0
      (ε := ε) (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
      (βBarReal := hpow.β + 1) (βBarReal' := (hpow.β + 1) / hpow.β)
      (γBarReal' := (hpow.α * (hpow.β + 1) / hpow.β) /
                      (hpow.α * (hpow.β + 1) / hpow.β - 1))
      hpow hRegH hExp hH_rc0
      Dυ υ (StationaryMFG.Theorems.SimplePower.Banach.uOf q)
      (fun i => StationaryMFG.Theorems.SimplePower.Banach.DuOf q i)
      (StationaryMFG.Theorems.SimplePower.Banach.mOf q) V
      (Set.univ : Set (Fin d → ℝ)) ρ
      MeasurableSet.univ (hρ_meas.indicator MeasurableSet.univ).aestronglyMeasurable
      ((MeasureTheory.Lp.stronglyMeasurable q.1).measurable)
      hV_memLp.aestronglyMeasurable hυ_meas.aestronglyMeasurable
      ((MeasureTheory.Lp.stronglyMeasurable q.2.1).measurable)
      (fun i => (hDυ_meas i).aestronglyMeasurable)
      (fun i => (MeasureTheory.Lp.stronglyMeasurable (q.2.2 i)).measurable)
      hρ_nn hSρ_memLp_univ
      r.Gh r.Eh r.hGh_memLp r.hEh_memLp r.hGh_bd r.hEh_bd
      r.Gf r.Ef r.hGf_memLp r.hEf_memLp r.hGf_bd r.hEf_bd
      r.Gm r.Em r.hGm_memLp r.hEm_memLp r.hGm_bd r.hEm_bd
  simp_rw [h_ind_univ] at hSetTendsto
  rw [h_ind_univ_eq] at hSetTendsto
  have h_lim_sub_eq :
      ((ρ : (Fin d → ℝ) → ℝ) -
        StationaryMFG.Theorems.SimplePower.Banach.mOf q)
        = (fun x : (Fin d → ℝ) =>
            σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
    funext x
    change StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
            σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
          - StationaryMFG.Theorems.SimplePower.Banach.mOf q x = _
    ring
  rw [h_lim_sub_eq] at hSetTendsto
  refine hSetTendsto.congr (fun n => ?_)
  rfl

/-- **`signedUserTripleCont_of_paperHypotheses_of_rc0`** — Hext-free
`_of_rc0` sibling of `signedUserTripleCont_of_paperHypotheses`. Takes
`hH_rc0` in place of `(hHat0, hFin, hAgree)` and routes the inner
set-form `Tendsto` through the step-6 rc0 set bridge. -/
noncomputable def signedUserTripleCont_of_paperHypotheses_of_rc0
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
    (_hq_K0 : q ∈ StationaryMFG.Theorems.SimplePower.Banach.K0_Aepsi d
              (hpow.β + 1) (hpow.α * (hpow.β + 1) / hpow.β))
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (S : Set (Fin d → ℝ)) (hS : MeasurableSet S)
    (μ υ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ)
    (hμ_meas : Measurable μ)
    (hυ_meas : Measurable υ)
    (hDυ_meas : ∀ i, Measurable (Dυ i))
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
  let ρ : (Fin d → ℝ) → ℝ :=
    fun x => μ x + σ * μ x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
  have hInd_meas : Measurable
      (fun x : (Fin d → ℝ) =>
        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) :=
    measurable_const.indicator hS
  have hρ_meas : Measurable ρ := by
    have h1 : Measurable
        (fun x : (Fin d → ℝ) => σ * μ x) :=
      measurable_const.mul hμ_meas
    have h2 : Measurable
        (fun x : (Fin d → ℝ) =>
          σ * μ x *
            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) :=
      h1.mul hInd_meas
    exact hμ_meas.add h2
  have hσ_lb : (-1 : ℝ) ≤ σ := by rcases hσ with hσ' | hσ' <;> simp [hσ']
  have hσ_ub : σ ≤ 1 := by rcases hσ with hσ' | hσ' <;> simp [hσ']
  have hρ_nn :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Periodic.UnitCube d)), 0 ≤ ρ x := by
    filter_upwards [hμ_nn] with x hx_μnn
    have hInd_bd : 0 ≤ S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x ∧
        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x ≤ 1 := by
      by_cases hxS : x ∈ S
      · refine ⟨?_, ?_⟩
        · simp [Set.indicator_of_mem hxS]
        · simp [Set.indicator_of_mem hxS]
      · refine ⟨?_, ?_⟩
        · simp [Set.indicator_of_notMem hxS]
        · simp [Set.indicator_of_notMem hxS]
    have hfactor_nn : 0 ≤ 1 + σ *
        S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
      by_cases hxS : x ∈ S
      · rw [Set.indicator_of_mem hxS]
        simp only [mul_one]
        linarith
      · rw [Set.indicator_of_notMem hxS]
        simp
    change 0 ≤ μ x + σ * μ x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
    have h_eq :
        μ x + σ * μ x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
          = μ x *
              (1 + σ * S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by ring
    rw [h_eq]
    exact mul_nonneg hx_μnn hfactor_nn
  have hσμ_memLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1))
      (fun x => σ * μ x) := by
    have hsmul := hμ_memLp.const_smul (𝕜 := ℝ) σ
    have heq : (σ • (μ : (Fin d → ℝ) → ℝ))
                = fun x => σ * μ x :=
      rfl
    rw [heq] at hsmul; exact hsmul
  have hSσμ_memLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1))
      (S.indicator
        (fun x => σ * μ x)) :=
    MemLp.toMemLpPer (MeasureTheory.MemLp.indicator hS.nullMeasurableSet hσμ_memLp.toMemLp)
  have hSσμ_funEq :
      (S.indicator
          (fun x => σ * μ x) :
            (Fin d → ℝ) → ℝ)
        = fun x => σ * μ x *
                    S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x := by
    funext x
    by_cases hx : x ∈ S
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have hSσμ_memLp' : Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1))
      (fun x => σ * μ x *
                  S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x) := by
    rw [← hSσμ_funEq]; exact hSσμ_memLp
  have hρ_memLp : Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1)) ρ := by
    have h := MemLpPer.add hμ_memLp hSσμ_memLp'
    have heq :
        ((μ : (Fin d → ℝ) → ℝ)
            + (fun x => σ * μ x *
                          S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x))
          = ρ := by
      funext x; rfl
    rw [heq] at h; exact h
  have h_ind_univ : ∀ x : (Fin d → ℝ),
      (Set.univ : Set (Fin d → ℝ)).indicator ρ x = ρ x := by
    intro x; simp
  have h_ind_univ_eq :
      (Set.univ : Set (Fin d → ℝ)).indicator ρ = ρ := by
    funext x; exact h_ind_univ x
  have hSρ_memLp_univ : Periodic.MemLpPer (d := d) (ENNReal.ofReal (hpow.β + 1))
      ((Set.univ : Set (Fin d → ℝ)).indicator ρ) := by
    rw [h_ind_univ_eq]; exact hρ_memLp
  have hExp_paper :
      SimplePowerExponentFacts
          (SimplePowerExponentFacts.paperGammaBarReal hpow.α hpow.β)
          (SimplePowerExponentFacts.paperBetaBar hpow.β)
          (SimplePowerExponentFacts.paperGammaBar hpow.α hpow.β)
          (SimplePowerExponentFacts.paperBetaBarPrime hpow.β) :=
    SimplePowerExponentFacts.ofPowerGrowth hpow
  have hExp :
      SimplePowerExponentFacts (hpow.α * (hpow.β + 1) / hpow.β)
          (ENNReal.ofReal (hpow.β + 1))
          (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β))
          (ENNReal.ofReal ((hpow.β + 1) / hpow.β)) := by
    have h1 :
        (SimplePowerExponentFacts.paperBetaBar hpow.β)
          = ENNReal.ofReal (hpow.β + 1) := by
      simp [SimplePowerExponentFacts.paperBetaBar]
    have h2 :
        (SimplePowerExponentFacts.paperGammaBar hpow.α hpow.β)
          = ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β) := by
      simp [SimplePowerExponentFacts.paperGammaBar]
    have h3 :
        (SimplePowerExponentFacts.paperBetaBarPrime hpow.β)
          = ENNReal.ofReal ((hpow.β + 1) / hpow.β) := by
      simp [SimplePowerExponentFacts.paperBetaBarPrime]
    have h4 :
        (SimplePowerExponentFacts.paperGammaBarReal hpow.α hpow.β)
          = hpow.α * (hpow.β + 1) / hpow.β := by
      simp [SimplePowerExponentFacts.paperGammaBarReal]
    have := hExp_paper
    rw [h1, h2, h3, h4] at this
    exact this
  let r : StationaryMFG.Theorems.SimplePower.Banach.SetTendstoResidueOf
            (d := d) (V := V) (H := H) (DpH := DpH)
            (βBarReal := hpow.β + 1)
            (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
            hpow q (Set.univ : Set (Fin d → ℝ)) ρ υ Dυ :=
    setTendstoResidueOf_of_paperHypotheses (V := V) (H := H) (DpH := DpH)
      hpow q (Set.univ : Set (Fin d → ℝ)) MeasurableSet.univ ρ υ Dυ
      hυ_meas.aestronglyMeasurable
      (fun i => (hDυ_meas i).aestronglyMeasurable)
      hSρ_memLp_univ hυ_memLp hDυ_memLp hV_memLp hρ_nn
  have hSetTendsto :=
    StationaryMFG.Theorems.SimplePower.Banach.mfgOperatorEpsPair_tendsto_set_perturbation_of_paperHypotheses_of_aestronglyMeasurable_of_rc0
      (ε := ε) (γBarReal := hpow.α * (hpow.β + 1) / hpow.β)
      (βBarReal := hpow.β + 1) (βBarReal' := (hpow.β + 1) / hpow.β)
      (γBarReal' := (hpow.α * (hpow.β + 1) / hpow.β) /
                      (hpow.α * (hpow.β + 1) / hpow.β - 1))
      hpow hRegH hExp hH_rc0
      Dυ υ (StationaryMFG.Theorems.SimplePower.Banach.uOf q)
      (fun i => StationaryMFG.Theorems.SimplePower.Banach.DuOf q i)
      (StationaryMFG.Theorems.SimplePower.Banach.mOf q) V
      (Set.univ : Set (Fin d → ℝ)) ρ
      MeasurableSet.univ (hρ_meas.indicator MeasurableSet.univ).aestronglyMeasurable
      ((MeasureTheory.Lp.stronglyMeasurable q.1).measurable)
      hV_memLp.aestronglyMeasurable hυ_meas.aestronglyMeasurable
      ((MeasureTheory.Lp.stronglyMeasurable q.2.1).measurable)
      (fun i => (hDυ_meas i).aestronglyMeasurable)
      (fun i => (MeasureTheory.Lp.stronglyMeasurable (q.2.2 i)).measurable)
      hρ_nn hSρ_memLp_univ
      r.Gh r.Eh r.hGh_memLp r.hEh_memLp r.hGh_bd r.hEh_bd
      r.Gf r.Ef r.hGf_memLp r.hEf_memLp r.hGf_bd r.hEf_bd
      r.Gm r.Em r.hGm_memLp r.hEm_memLp r.hGm_bd r.hEm_bd
  simp_rw [h_ind_univ] at hSetTendsto
  rw [h_ind_univ_eq] at hSetTendsto
  refine hSetTendsto.congr (fun n => ?_)
  rfl

/-- **`signedUserProbeCont_of_paperHypotheses_of_aestronglyMeasurable_of_rc0`**
— AE-strong-measurable, Hext-free `_of_rc0` wrapper around the strict
`signedUserProbeCont_of_paperHypotheses_of_rc0`. Mirrors the Hext-pulling
`signedUserProbeCont_of_paperHypotheses_of_aestronglyMeasurable`, swapping
`(hHat0,hFin,hAgree)` for `hH_rc0` and the inner strict call for the
`_of_rc0` strict producer. -/
noncomputable def signedUserProbeCont_of_paperHypotheses_of_aestronglyMeasurable_of_rc0
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
    (υ : (Fin d → ℝ) → ℝ) (Dυ : Fin d → (Fin d → ℝ) → ℝ)
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
            (hpow.α * (hpow.β + 1) / hpow.β) ε
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
              StationaryMFG.Theorems.SimplePower.Banach.uOf q x))) := by
  classical
  set υ' : (Fin d → ℝ) → ℝ := hυ_memLp.aestronglyMeasurable.mk υ
    with hυ'_def
  set Dυ' : Fin d → (Fin d → ℝ) → ℝ :=
    fun i => (hDυ_memLp i).aestronglyMeasurable.mk (Dυ i)
    with hDυ'_def
  have hυ'_meas : Measurable υ' :=
    hυ_memLp.aestronglyMeasurable.measurable_mk
  have hDυ'_meas : ∀ i, Measurable (Dυ' i) := fun i =>
    (hDυ_memLp i).aestronglyMeasurable.measurable_mk
  have hυ'_ae :
      υ =ᵐ[MeasureTheory.volume.restrict (Periodic.UnitCube d)] υ' :=
    hυ_memLp.aestronglyMeasurable.ae_eq_mk
  have hDυ'_ae : ∀ i,
      Dυ i =ᵐ[MeasureTheory.volume.restrict (Periodic.UnitCube d)] Dυ' i :=
    fun i => (hDυ_memLp i).aestronglyMeasurable.ae_eq_mk
  have hυ'_memLp : Periodic.MemLpPer (d := d)
      (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) υ' :=
    hυ_memLp.congr_ae_unitCube hυ'_ae
  have hDυ'_memLp : ∀ i, Periodic.MemLpPer (d := d)
      (ENNReal.ofReal (hpow.α * (hpow.β + 1) / hpow.β)) (Dυ' i) := fun i =>
    (hDυ_memLp i).congr_ae_unitCube (hDυ'_ae i)
  have h_prime :=
    signedUserProbeCont_of_paperHypotheses_of_rc0
      (V := V) (H := H) (DpH := DpH)
      hpow hRegH hH_rc0 (ε := ε)
      q hq_K0 σ hσ S hS υ' Dυ'
      hυ'_meas hDυ'_meas
      hυ'_memLp hDυ'_memLp hV_memLp
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
  have hSeq_eq : ∀ n : ℕ,
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
        (hpow.α * (hpow.β + 1) / hpow.β) ε
        Dυ'
        (fun x =>
          StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
            σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
            + 1 / ((n : ℝ) + 1))
        υ'
        (fun i x => Dυ' i x -
          StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
        (fun x =>
          (StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
            σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
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
          StationaryMFG.Theorems.SimplePower.Banach.uOf q x) := by
    intro n
    rw [mfgOperatorEpsPair_congr_ae_primal (V := V) (H := H) (DpH := DpH)
          (γBar := hpow.α * (hpow.β + 1) / hpow.β) (ε := ε)
          Dυ' Dυ
          (fun x =>
            StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
              σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
              + 1 / ((n : ℝ) + 1))
          (fun x =>
            StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
              σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
              + 1 / ((n : ℝ) + 1))
          υ' υ
          (fun i x => Dυ' i x -
            StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
          (fun x =>
            (StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
              σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
              + 1 / ((n : ℝ) + 1)) -
            StationaryMFG.Theorems.SimplePower.Banach.mOf q x)
          (fun x => υ' x -
            StationaryMFG.Theorems.SimplePower.Banach.uOf q x)
          hDυprim_ae (Filter.EventuallyEq.refl _ _) hυprim_ae]
    rw [mfgOperatorEpsPair_congr_ae (V := V) (H := H) (DpH := DpH)
          (γBar := hpow.α * (hpow.β + 1) / hpow.β) (ε := ε)
          Dυ
          (fun x =>
            StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
              σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
              + 1 / ((n : ℝ) + 1))
          υ
          (fun i x => Dυ' i x -
            StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
          (fun i x => Dυ i x -
            StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
          (fun x =>
            (StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
              σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
              + 1 / ((n : ℝ) + 1)) -
            StationaryMFG.Theorems.SimplePower.Banach.mOf q x)
          (fun x =>
            (StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
              σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
              + 1 / ((n : ℝ) + 1)) -
            StationaryMFG.Theorems.SimplePower.Banach.mOf q x)
          (fun x => υ' x -
            StationaryMFG.Theorems.SimplePower.Banach.uOf q x)
          (fun x => υ x -
            StationaryMFG.Theorems.SimplePower.Banach.uOf q x)
          hDνdiff_ae (Filter.EventuallyEq.refl _ _) hνdiff_ae]
  have hLim_eq :
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
        (hpow.α * (hpow.β + 1) / hpow.β) ε
        Dυ'
        (fun x =>
          StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
            σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
        υ'
        (fun i x => Dυ' i x -
          StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
        (fun x =>
          σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
            S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
        (fun x => υ' x -
          StationaryMFG.Theorems.SimplePower.Banach.uOf q x)
      =
      mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
        (hpow.α * (hpow.β + 1) / hpow.β) ε
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
          StationaryMFG.Theorems.SimplePower.Banach.uOf q x) := by
    rw [mfgOperatorEpsPair_congr_ae_primal (V := V) (H := H) (DpH := DpH)
          (γBar := hpow.α * (hpow.β + 1) / hpow.β) (ε := ε)
          Dυ' Dυ
          (fun x =>
            StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
              σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          (fun x =>
            StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
              σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          υ' υ
          (fun i x => Dυ' i x -
            StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
          (fun x =>
            σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          (fun x => υ' x -
            StationaryMFG.Theorems.SimplePower.Banach.uOf q x)
          hDυprim_ae (Filter.EventuallyEq.refl _ _) hυprim_ae]
    rw [mfgOperatorEpsPair_congr_ae (V := V) (H := H) (DpH := DpH)
          (γBar := hpow.α * (hpow.β + 1) / hpow.β) (ε := ε)
          Dυ
          (fun x =>
            StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
              σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          υ
          (fun i x => Dυ' i x -
            StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
          (fun i x => Dυ i x -
            StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
          (fun x =>
            σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          (fun x =>
            σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
              S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x)
          (fun x => υ' x -
            StationaryMFG.Theorems.SimplePower.Banach.uOf q x)
          (fun x => υ x -
            StationaryMFG.Theorems.SimplePower.Banach.uOf q x)
          hDνdiff_ae (Filter.EventuallyEq.refl _ _) hνdiff_ae]
  have h_seq_funext :
      (fun n : ℕ =>
        mfgOperatorEpsPair (V := V) (H := H) (DpH := DpH)
          (hpow.α * (hpow.β + 1) / hpow.β) ε
          Dυ'
          (fun x =>
            StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
              σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
                S.indicator (fun _ : Fin d → ℝ => (1 : ℝ)) x
              + 1 / ((n : ℝ) + 1))
          υ'
          (fun i x => Dυ' i x -
            StationaryMFG.Theorems.SimplePower.Banach.DuOf q i x)
          (fun x =>
            (StationaryMFG.Theorems.SimplePower.Banach.mOf q x +
              σ * StationaryMFG.Theorems.SimplePower.Banach.mOf q x *
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
            StationaryMFG.Theorems.SimplePower.Banach.uOf q x)) := by
    funext n; exact hSeq_eq n
  rw [h_seq_funext, hLim_eq] at h_prime
  exact h_prime

end SimplePower
end Theorems
end StationaryMFG
end
