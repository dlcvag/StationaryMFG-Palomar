module

public import StationaryMFG.Theorems.Congestion.MuAux
public import StationaryMFG.Theorems.Congestion.MuIntegrability
public import StationaryMFG.Theorems.Congestion.MuRe
public import StationaryMFG.Theorems.Congestion.Domain
public import StationaryMFG.Theorems.Congestion.Existence
public import StationaryMFG.Solutions.Weak
public import StationaryMFG.Solutions.Strong
public import StationaryMFG.Theorems.Congestion.StrongIsStrong.Part1
import all StationaryMFG.Theorems.Congestion.StrongIsStrong.Part1
public import StationaryMFG.Theorems.Congestion.StrongIsStrong.Part2
import all StationaryMFG.Theorems.Congestion.StrongIsStrong.Part2

@[expose] public section

noncomputable section
namespace StationaryMFG
namespace Congestion
open MeasureTheory
open StationaryMFG.Periodic
open StationaryMFG.Hamiltonian
open StationaryMFG.Solutions.Strong
open StationaryMFG.Solutions.MFG
open scoped ENNReal
variable {d : ℕ}


/-- **Local Hölder pairing bound on the torus.**
For real Hölder conjugates `p, q`, `f ∈ L^p_per` and `g ∈ L^q_per`,
`|∫ f·g| ≤ ‖f‖_{L^p} · ‖g‖_{L^q}`.

Adapted from `StationaryMFG.Theorems.SimplePower.Banach.abs_setIntegral_mul_le_lpNormPer_mul_lpNormPer`
(re-derived here so the Congestion module does not need to import the
Banach `WeakPairing` subtree). -/
private lemma congestion_abs_integral_mul_le_lpNormPer
    {p q : ℝ} (hpq : p.HolderConjugate q)
    {f g : (Fin d → ℝ) → ℝ}
    (hf : MemLpPer (d := d) (ENNReal.ofReal p) f)
    (hg : MemLpPer (d := d) (ENNReal.ofReal q) g) :
    |∫ x in UnitCube d, f x * g x|
      ≤ lpNormPer (ENNReal.ofReal p) f * lpNormPer (ENNReal.ofReal q) g := by
  set μ : Measure (Fin d → ℝ) :=
    Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d) with hμ
  have h_abs_le_int_abs :
      |∫ x in UnitCube d, f x * g x| ≤ ∫ x, ‖f x‖ * ‖g x‖ ∂μ := by
    have h₁ : |∫ x in UnitCube d, f x * g x| = ‖∫ x, f x * g x ∂μ‖ := by
      rw [Real.norm_eq_abs]
    have h₂ : ‖∫ x, f x * g x ∂μ‖ ≤ ∫ x, ‖f x * g x‖ ∂μ :=
      norm_integral_le_integral_norm _
    have h₃ : ∫ x, ‖f x * g x‖ ∂μ = ∫ x, ‖f x‖ * ‖g x‖ ∂μ := by
      refine integral_congr_ae ?_
      refine Filter.Eventually.of_forall (fun x => ?_)
      simp [Real.norm_eq_abs, abs_mul]
    rw [h₁]; exact h₂.trans h₃.le
  have h_holder :
      ∫ x, ‖f x‖ * ‖g x‖ ∂μ
        ≤ (∫ x, ‖f x‖ ^ p ∂μ) ^ (1 / p)
            * (∫ x, ‖g x‖ ^ q ∂μ) ^ (1 / q) :=
    integral_mul_norm_le_Lp_mul_Lq hpq hf.toMemLp hg.toMemLp
  have hp_pos : 0 < p := hpq.pos
  have hp_ne : (ENNReal.ofReal p) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hp_pos
  have hp_top : (ENNReal.ofReal p) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hp_toReal : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp_pos.le
  have hq_pos : 0 < q := hpq.symm.pos
  have hq_ne : (ENNReal.ofReal q) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hq_pos
  have hq_top : (ENNReal.ofReal q) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hq_toReal : (ENNReal.ofReal q).toReal = q := ENNReal.toReal_ofReal hq_pos.le
  have h_eLp_f :
      eLpNorm f (ENNReal.ofReal p) μ
        = ENNReal.ofReal
            ((∫ x, ‖f x‖ ^ (ENNReal.ofReal p).toReal ∂μ)
              ^ ((ENNReal.ofReal p).toReal⁻¹)) :=
    MemLp.eLpNorm_eq_integral_rpow_norm hp_ne hp_top hf.toMemLp
  have h_eLp_g :
      eLpNorm g (ENNReal.ofReal q) μ
        = ENNReal.ofReal
            ((∫ x, ‖g x‖ ^ (ENNReal.ofReal q).toReal ∂μ)
              ^ ((ENNReal.ofReal q).toReal⁻¹)) :=
    MemLp.eLpNorm_eq_integral_rpow_norm hq_ne hq_top hg.toMemLp
  have h_int_f_nn : 0 ≤ ∫ x, ‖f x‖ ^ p ∂μ :=
    integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _)
  have h_int_g_nn : 0 ≤ ∫ x, ‖g x‖ ^ q ∂μ :=
    integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _)
  have h_root_f_nn' : 0 ≤ (∫ x, ‖f x‖ ^ p ∂μ) ^ (p⁻¹) :=
    Real.rpow_nonneg h_int_f_nn _
  have h_root_g_nn' : 0 ≤ (∫ x, ‖g x‖ ^ q ∂μ) ^ (q⁻¹) :=
    Real.rpow_nonneg h_int_g_nn _
  have h_lpf : lpNormPer (ENNReal.ofReal p) f = (∫ x, ‖f x‖ ^ p ∂μ) ^ (1 / p) := by
    unfold lpNormPer eLpNormPer
    rw [h_eLp_f, hp_toReal, ENNReal.toReal_ofReal h_root_f_nn', one_div]
  have h_lpg : lpNormPer (ENNReal.ofReal q) g = (∫ x, ‖g x‖ ^ q ∂μ) ^ (1 / q) := by
    unfold lpNormPer eLpNormPer
    rw [h_eLp_g, hq_toReal, ENNReal.toReal_ofReal h_root_g_nn', one_div]
  calc |∫ x in UnitCube d, f x * g x|
      ≤ ∫ x, ‖f x‖ * ‖g x‖ ∂μ := h_abs_le_int_abs
    _ ≤ (∫ x, ‖f x‖ ^ p ∂μ) ^ (1 / p)
          * (∫ x, ‖g x‖ ^ q ∂μ) ^ (1 / q) := h_holder
    _ = lpNormPer (ENNReal.ofReal p) f
          * lpNormPer (ENNReal.ofReal q) g := by rw [h_lpf, h_lpg]

open StationaryMFG.Periodic Filter Topology in
/-- **Linear transport identity, extended from smooth tests to `φ = u` by
density (paper line 1526).**

At the Browder–Minty witness the transport functional is *linear* in the test
pair `(φ, ∇φ)`: it has the shape `T(φ) = ∫ A·φ + Σᵢ ∫ Bᵢ·∂ᵢφ` with fixed
coefficients `A ∈ L^{q}_per`, `Bᵢ ∈ L^{q}_per` (the Hölder dual exponent
`q = γ̄'`). The smooth-test identity `T(φ) = 0` (`congestion_transport_at_witness`,
regrouped) then extends to `φ = u ∈ W^{1,γ̄}_per` (`q`-dual data `u, Duᵢ ∈ L^{p}`,
`p = γ̄`) by smooth density.

Proof: pick smooth `φₙ` with `sobolevNormPer p (u−φₙ) (Du−∇φₙ) ≤ 1/(n+1)`
(`SmoothPeriodic.exists_sobolevPer_sub_le_of_memSobolevPer`); each `Lᵖ` piece
tends to `0`, so by the Hölder pairing bound
`|∫ A·u − ∫ A·φₙ| ≤ ‖A‖_q · ‖u−φₙ‖_p → 0` and likewise for each `Bᵢ`. The
constant-zero sequence `T(φₙ) = 0` passes to the limit `T(u) = 0`. -/
lemma transport_linear_at_u_of_smooth
    {pReal qReal : ℝ} (hpq : pReal.HolderConjugate qReal)
    {A : (Fin d → ℝ) → ℝ} {B : Fin d → ((Fin d → ℝ) → ℝ)}
    {u : (Fin d → ℝ) → ℝ} {Du : Fin d → ((Fin d → ℝ) → ℝ)}
    (hA : MemLpPer (d := d) (ENNReal.ofReal qReal) A)
    (hB : ∀ i, MemLpPer (d := d) (ENNReal.ofReal qReal) (B i))
    (hu_lp : MemLpPer (d := d) (ENNReal.ofReal pReal) u)
    (hDu_lp : ∀ i, MemLpPer (d := d) (ENNReal.ofReal pReal) (Du i))
    (hu_meas : MeasureTheory.AEStronglyMeasurable u
      (volume : Measure (Fin d → ℝ)))
    (hu_per : IsPeriodic u)
    (hu_loc : MeasureTheory.LocallyIntegrable u (volume : Measure (Fin d → ℝ)))
    (hDu_meas : ∀ i, MeasureTheory.AEStronglyMeasurable (Du i)
      (volume : Measure (Fin d → ℝ)))
    (hDu_per : ∀ i, IsPeriodic (Du i))
    (hDu_loc : ∀ i, MeasureTheory.LocallyIntegrable (Du i)
      (volume : Measure (Fin d → ℝ)))
    (hweak : ∀ i, Periodic.HasWeakDerivPer (d := d) i u (Du i))
    (hsmooth : ∀ φ : Periodic.SmoothPeriodic d,
      (∫ x in UnitCube d, A x * (φ : (Fin d → ℝ) → ℝ) x
        ∂(volume : Measure (Fin d → ℝ)))
      + ∑ i : Fin d, (∫ x in UnitCube d,
          B i x * (Periodic.SmoothPeriodic.partialDeriv i φ :
            (Fin d → ℝ) → ℝ) x
          ∂(volume : Measure (Fin d → ℝ))) = 0) :
    (∫ x in UnitCube d, A x * u x ∂(volume : Measure (Fin d → ℝ)))
      + ∑ i : Fin d, (∫ x in UnitCube d, B i x * Du i x
          ∂(volume : Measure (Fin d → ℝ))) = 0 := by
  classical
  have hp_pos : 0 < pReal := hpq.pos
  have hp1 : 1 ≤ pReal := hpq.lt.le
  have hp_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal pReal := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from (ENNReal.ofReal_one).symm]
    exact ENNReal.ofReal_le_ofReal hp1
  have hp_top : (ENNReal.ofReal pReal) ≠ (⊤ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  -- Smooth approximating sequence with `sobolevNormPer ≤ 1/(n+1)`.
  have hε : ∀ n : ℕ, (0 : ℝ) < 1 / (n + 1) := fun n => by positivity
  have hmemSob : MemSobolevPer (d := d) (ENNReal.ofReal pReal) u :=
    ⟨hu_lp, Du, hweak⟩
  choose φseq hφseq using
    (fun n : ℕ =>
      SmoothPeriodic.exists_sobolevPer_sub_le_of_memSobolevPer
        (p := ENNReal.ofReal pReal) hp_le hp_top hmemSob
        hu_meas hu_per hu_loc hu_lp
        hweak hDu_meas hDu_per hDu_loc hDu_lp (hε n))
  -- From the Sobolev-norm bound, extract `Lᵖ` convergence of each piece.
  -- `sobolevNormPer = lpNormPer (u−φ) + Σ lpNormPer (Du−∇φ)`, all summands ≥ 0.
  have hbound_to_zero : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  -- L^p tendsto of the scalar piece.
  have hu_conv : Tendsto
      (fun n => lpNormPer (ENNReal.ofReal pReal)
        ((u : (Fin d → ℝ) → ℝ) - (φseq n : (Fin d → ℝ) → ℝ)))
      atTop (𝓝 0) := by
    refine squeeze_zero (fun n => lpNormPer_nonneg _ _) (g := fun n : ℕ => (1 : ℝ) / (n + 1)) ?_ hbound_to_zero
    intro n
    have hle := hφseq n
    have hsplit : lpNormPer (ENNReal.ofReal pReal)
          ((u : (Fin d → ℝ) → ℝ) - (φseq n : (Fin d → ℝ) → ℝ))
        ≤ sobolevNormPer (ENNReal.ofReal pReal)
            ((u : (Fin d → ℝ) → ℝ) - (φseq n : (Fin d → ℝ) → ℝ))
            (fun i x => Du i x -
              ((SmoothPeriodic.partialDeriv i (φseq n) : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x) := by
      unfold sobolevNormPer
      have : 0 ≤ ∑ i : Fin d, lpNormPer (ENNReal.ofReal pReal)
          (fun x => Du i x -
            ((SmoothPeriodic.partialDeriv i (φseq n) : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x) :=
        Finset.sum_nonneg (fun i _ => lpNormPer_nonneg _ _)
      linarith
    exact le_trans hsplit hle
  -- L^p tendsto of each gradient piece.
  have hDu_conv : ∀ i : Fin d, Tendsto
      (fun n => lpNormPer (ENNReal.ofReal pReal)
        (fun x => Du i x -
          ((SmoothPeriodic.partialDeriv i (φseq n) : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) x))
      atTop (𝓝 0) := by
    intro i
    refine squeeze_zero (fun n => lpNormPer_nonneg _ _) (g := fun n : ℕ => (1 : ℝ) / (n + 1)) ?_ hbound_to_zero
    intro n
    have hle := hφseq n
    have hsplit : lpNormPer (ENNReal.ofReal pReal)
          (fun x => Du i x -
            ((SmoothPeriodic.partialDeriv i (φseq n) : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x)
        ≤ sobolevNormPer (ENNReal.ofReal pReal)
            ((u : (Fin d → ℝ) → ℝ) - (φseq n : (Fin d → ℝ) → ℝ))
            (fun i x => Du i x -
              ((SmoothPeriodic.partialDeriv i (φseq n) : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x) := by
      unfold sobolevNormPer
      have hmem : i ∈ (Finset.univ : Finset (Fin d)) := Finset.mem_univ i
      have hsum_ge : lpNormPer (ENNReal.ofReal pReal)
            (fun x => Du i x -
              ((SmoothPeriodic.partialDeriv i (φseq n) : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x)
          ≤ ∑ j : Fin d, lpNormPer (ENNReal.ofReal pReal)
              (fun x => Du j x -
                ((SmoothPeriodic.partialDeriv j (φseq n) : SmoothPeriodic d) :
                    (Fin d → ℝ) → ℝ) x) :=
        Finset.single_le_sum
          (f := fun j => lpNormPer (ENNReal.ofReal pReal)
            (fun x => Du j x -
              ((SmoothPeriodic.partialDeriv j (φseq n) : SmoothPeriodic d) :
                  (Fin d → ℝ) → ℝ) x))
          (fun j _ => lpNormPer_nonneg _ _) hmem
      have hnn : 0 ≤ lpNormPer (ENNReal.ofReal pReal)
          ((u : (Fin d → ℝ) → ℝ) - (φseq n : (Fin d → ℝ) → ℝ)) :=
        lpNormPer_nonneg _ _
      linarith
    exact le_trans hsplit hle
  -- Scalar pairing tendsto: `∫ A·φₙ → ∫ A·u`.
  have hA_pair : Tendsto
      (fun n => ∫ x in UnitCube d, A x * (φseq n : (Fin d → ℝ) → ℝ) x
        ∂(volume : Measure (Fin d → ℝ)))
      atTop
      (𝓝 (∫ x in UnitCube d, A x * u x ∂(volume : Measure (Fin d → ℝ)))) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg)
      (g := fun n => lpNormPer (ENNReal.ofReal qReal) A
        * lpNormPer (ENNReal.ofReal pReal)
          ((u : (Fin d → ℝ) → ℝ) - (φseq n : (Fin d → ℝ) → ℝ))) ?_ ?_
    · intro n
      have hφlp : MemLpPer (d := d) (ENNReal.ofReal pReal)
          (φseq n : (Fin d → ℝ) → ℝ) := by
        have := (Periodic.MemSobolevPer.of_smoothPeriodic
          (ENNReal.ofReal pReal) (φseq n)).1
        exact this
      have hint_u : IntegrableOn (fun x => A x * u x) (UnitCube d) :=
        MemLpPer.integrable_mul hpq.symm hA hu_lp
      have hint_φ : IntegrableOn (fun x => A x * (φseq n : (Fin d → ℝ) → ℝ) x)
          (UnitCube d) :=
        MemLpPer.integrable_mul hpq.symm hA hφlp
      have hdiff : dist
          (∫ x in UnitCube d, A x * (φseq n : (Fin d → ℝ) → ℝ) x
            ∂(volume : Measure (Fin d → ℝ)))
          (∫ x in UnitCube d, A x * u x ∂(volume : Measure (Fin d → ℝ)))
          = |∫ x in UnitCube d, A x *
              (u x - (φseq n : (Fin d → ℝ) → ℝ) x)
              ∂(volume : Measure (Fin d → ℝ))| := by
        rw [Real.dist_eq, abs_sub_comm]
        rw [← integral_sub hint_u hint_φ]
        refine congrArg _ ?_
        refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
        ring
      rw [hdiff]
      have hmul_lp : MemLpPer (d := d) (ENNReal.ofReal pReal)
          ((u : (Fin d → ℝ) → ℝ) - (φseq n : (Fin d → ℝ) → ℝ)) :=
        (hu_lp.toMemLp.sub hφlp.toMemLp)
      have := congestion_abs_integral_mul_le_lpNormPer
        (p := qReal) (q := pReal) hpq.symm hA hmul_lp
      simpa using this
    · have := hu_conv.const_mul (lpNormPer (ENNReal.ofReal qReal) A)
      simpa using this
  -- Gradient pairing tendsto for each `i`: `∫ Bᵢ·∂ᵢφₙ → ∫ Bᵢ·Duᵢ`.
  have hB_pair : ∀ i : Fin d, Tendsto
      (fun n => ∫ x in UnitCube d, B i x *
        (SmoothPeriodic.partialDeriv i (φseq n) : (Fin d → ℝ) → ℝ) x
        ∂(volume : Measure (Fin d → ℝ)))
      atTop
      (𝓝 (∫ x in UnitCube d, B i x * Du i x
        ∂(volume : Measure (Fin d → ℝ)))) := by
    intro i
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg)
      (g := fun n => lpNormPer (ENNReal.ofReal qReal) (B i)
        * lpNormPer (ENNReal.ofReal pReal)
          (fun x => Du i x -
            ((SmoothPeriodic.partialDeriv i (φseq n) : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x)) ?_ ?_
    · intro n
      have hψlp : MemLpPer (d := d) (ENNReal.ofReal pReal)
          (SmoothPeriodic.partialDeriv i (φseq n) : (Fin d → ℝ) → ℝ) :=
        (Periodic.MemSobolevPer.of_smoothPeriodic
          (ENNReal.ofReal pReal) (SmoothPeriodic.partialDeriv i (φseq n))).1
      have hint_u : IntegrableOn (fun x => B i x * Du i x) (UnitCube d) :=
        MemLpPer.integrable_mul hpq.symm (hB i) (hDu_lp i)
      have hint_φ : IntegrableOn (fun x => B i x *
          (SmoothPeriodic.partialDeriv i (φseq n) : (Fin d → ℝ) → ℝ) x)
          (UnitCube d) :=
        MemLpPer.integrable_mul hpq.symm (hB i) hψlp
      have hdiff : dist
          (∫ x in UnitCube d, B i x *
            (SmoothPeriodic.partialDeriv i (φseq n) : (Fin d → ℝ) → ℝ) x
            ∂(volume : Measure (Fin d → ℝ)))
          (∫ x in UnitCube d, B i x * Du i x
            ∂(volume : Measure (Fin d → ℝ)))
          = |∫ x in UnitCube d, B i x *
              (Du i x -
                (SmoothPeriodic.partialDeriv i (φseq n) : (Fin d → ℝ) → ℝ) x)
              ∂(volume : Measure (Fin d → ℝ))| := by
        rw [Real.dist_eq, abs_sub_comm]
        rw [← integral_sub hint_u hint_φ]
        refine congrArg _ ?_
        refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
        ring
      rw [hdiff]
      have hmul_lp : MemLpPer (d := d) (ENNReal.ofReal pReal)
          (fun x => Du i x -
            ((SmoothPeriodic.partialDeriv i (φseq n) : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x) :=
        ((hDu_lp i).toMemLp.sub hψlp.toMemLp)
      have := congestion_abs_integral_mul_le_lpNormPer
        (p := qReal) (q := pReal) hpq.symm (hB i) hmul_lp
      simpa using this
    · have := (hDu_conv i).const_mul (lpNormPer (ENNReal.ofReal qReal) (B i))
      simpa using this
  -- Sum the gradient pairings.
  have hBsum_pair : Tendsto
      (fun n => ∑ i : Fin d, ∫ x in UnitCube d, B i x *
        (SmoothPeriodic.partialDeriv i (φseq n) : (Fin d → ℝ) → ℝ) x
        ∂(volume : Measure (Fin d → ℝ)))
      atTop
      (𝓝 (∑ i : Fin d, ∫ x in UnitCube d, B i x * Du i x
        ∂(volume : Measure (Fin d → ℝ)))) :=
    tendsto_finset_sum (Finset.univ) (fun i _ => hB_pair i)
  -- Combine: `∫A·φₙ + ΣᵢBᵢ·∂ᵢφₙ → ∫A·u + ΣᵢBᵢ·Duᵢ`.
  have hsum_pair := hA_pair.add hBsum_pair
  -- The sequence is constantly `0` by `hsmooth`.
  have hzero : (fun n =>
      (∫ x in UnitCube d, A x * (φseq n : (Fin d → ℝ) → ℝ) x
        ∂(volume : Measure (Fin d → ℝ)))
      + ∑ i : Fin d, ∫ x in UnitCube d, B i x *
          (SmoothPeriodic.partialDeriv i (φseq n) : (Fin d → ℝ) → ℝ) x
          ∂(volume : Measure (Fin d → ℝ)))
      = fun _ => (0 : ℝ) := by
    funext n; exact hsmooth (φseq n)
  rw [hzero] at hsum_pair
  exact tendsto_nhds_unique hsum_pair tendsto_const_nhds

open StationaryMFG.Periodic Filter Topology in
/-- **AEPeriodicRep variant of `transport_linear_at_u_of_smooth`.**

Identical conclusion, but instead of demanding pointwise `IsPeriodic`/
`LocallyIntegrable` data on `u`/`Du i` (which is *not* derivable from the
quotient `Lp.coeFn` witnesses), it takes `Periodic.AEPeriodicRep` structures
`hu_rep`/`hDu_rep`. The proof transfers all data to the chosen periodic
representatives `uRep`/`DuRep i`, applies `transport_linear_at_u_of_smooth`,
and transports the conclusion back via `integral_congr_ae` (the integrands
`A·uRep` and `A·u`, resp. `B i·DuRep i` and `B i·Du i`, agree a.e. on the
cube). -/
lemma transport_linear_at_u_of_smooth_AEPeriodicRep
    {pReal qReal : ℝ} (hpq : pReal.HolderConjugate qReal)
    {A : (Fin d → ℝ) → ℝ} {B : Fin d → ((Fin d → ℝ) → ℝ)}
    {u : (Fin d → ℝ) → ℝ} {Du : Fin d → ((Fin d → ℝ) → ℝ)}
    (hA : MemLpPer (d := d) (ENNReal.ofReal qReal) A)
    (hB : ∀ i, MemLpPer (d := d) (ENNReal.ofReal qReal) (B i))
    (hu_lp : MemLpPer (d := d) (ENNReal.ofReal pReal) u)
    (hDu_lp : ∀ i, MemLpPer (d := d) (ENNReal.ofReal pReal) (Du i))
    (hu_rep : Periodic.AEPeriodicRep u)
    (hDu_rep : ∀ i, Periodic.AEPeriodicRep (Du i))
    (hweak : ∀ i, Periodic.HasWeakDerivPer (d := d) i u (Du i))
    (hsmooth : ∀ φ : Periodic.SmoothPeriodic d,
      (∫ x in UnitCube d, A x * (φ : (Fin d → ℝ) → ℝ) x
        ∂(volume : Measure (Fin d → ℝ)))
      + ∑ i : Fin d, (∫ x in UnitCube d,
          B i x * (Periodic.SmoothPeriodic.partialDeriv i φ :
            (Fin d → ℝ) → ℝ) x
          ∂(volume : Measure (Fin d → ℝ))) = 0) :
    (∫ x in UnitCube d, A x * u x ∂(volume : Measure (Fin d → ℝ)))
      + ∑ i : Fin d, (∫ x in UnitCube d, B i x * Du i x
          ∂(volume : Measure (Fin d → ℝ))) = 0 := by
  classical
  have hp1 : 1 ≤ pReal := hpq.lt.le
  have hp_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal pReal := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from (ENNReal.ofReal_one).symm]
    exact ENNReal.ofReal_le_ofReal hp1
  haveI hfin : IsFiniteMeasure
      (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  -- (a) The chosen periodic representatives.
  set uRep : (Fin d → ℝ) → ℝ := hu_rep.rep with huRepdef
  set DuRep : Fin d → ((Fin d → ℝ) → ℝ) := fun i => (hDu_rep i).rep with hDuRepdef
  -- a.e.-equalities on the cube: `uRep =ᵐ u`, `DuRep i =ᵐ Du i`.
  have hu_ae : uRep =ᵐ[Measure.restrict volume (UnitCube d)] u := hu_rep.ae_eq
  have hDu_ae : ∀ i, DuRep i =ᵐ[Measure.restrict volume (UnitCube d)] Du i :=
    fun i => (hDu_rep i).ae_eq
  -- (c) `MemLpPer` for the representatives (transfer across a.e.-equality).
  have hu_rep_lp : MemLpPer (d := d) (ENNReal.ofReal pReal) uRep :=
    MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq hu_ae.symm hu_lp.toMemLp)
  have hDu_rep_lp : ∀ i, MemLpPer (d := d) (ENNReal.ofReal pReal) (DuRep i) :=
    fun i => MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq (hDu_ae i).symm (hDu_lp i).toMemLp)
  -- `IsPeriodic` for the representatives (by definition of `AEPeriodicRep`).
  have hu_rep_per : IsPeriodic uRep := hu_rep.periodic
  have hDu_rep_per : ∀ i, IsPeriodic (DuRep i) := fun i => (hDu_rep i).periodic
  -- `LocallyIntegrable` for the representatives via the periodic bridge.
  have hu_rep_loc : MeasureTheory.LocallyIntegrable uRep
      (volume : Measure (Fin d → ℝ)) :=
    hu_rep_lp.locallyIntegrable_of_periodic hp_le hu_rep_per
  have hDu_rep_loc : ∀ i, MeasureTheory.LocallyIntegrable (DuRep i)
      (volume : Measure (Fin d → ℝ)) :=
    fun i => (hDu_rep_lp i).locallyIntegrable_of_periodic hp_le (hDu_rep_per i)
  -- `AEStronglyMeasurable` for the representatives (from local integrability).
  have hu_rep_meas : MeasureTheory.AEStronglyMeasurable uRep
      (volume : Measure (Fin d → ℝ)) := hu_rep_loc.aestronglyMeasurable
  have hDu_rep_meas : ∀ i, MeasureTheory.AEStronglyMeasurable (DuRep i)
      (volume : Measure (Fin d → ℝ)) := fun i => (hDu_rep_loc i).aestronglyMeasurable
  -- (b) Transfer weak derivatives from `u`/`Du i` to `uRep`/`DuRep i`.
  -- First move the derivative slot via `congr_ae`, then the primal slot inline.
  have hweak_rep : ∀ i, Periodic.HasWeakDerivPer (d := d) i uRep (DuRep i) := by
    intro i
    -- `congr_ae`: `Du i =ᵐ DuRep i` moves `g` to `DuRep i`.
    have hDuRep_one : MemLpPer (d := d) 1 (DuRep i) :=
      MemLp.toMemLpPer ((hDu_rep_lp i).toMemLp.mono_exponent hp_le)
    have hmid : Periodic.HasWeakDerivPer (d := d) i u (DuRep i) :=
      (hweak i).congr_ae hDuRep_one (hDu_ae i).symm
    -- Now move the primal slot `u → uRep`: the IBP identity only uses `f`
    -- inside `∫ f · ∂ᵢφ`, which is invariant under `u =ᵐ uRep` on the cube.
    refine ⟨hmid.1, ?_⟩
    intro φ
    have hpair : (fun x => u x *
          ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) x)
        =ᵐ[Measure.restrict volume (UnitCube d)]
          (fun x => uRep x *
            ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x) := by
      filter_upwards [hu_ae] with x hx
      simp [hx]
    have hint :
        periodicIntegral (fun x => u x *
            ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x) =
          periodicIntegral (fun x => uRep x *
            ((SmoothPeriodic.partialDeriv i φ : SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x) := by
      unfold periodicIntegral
      exact integral_congr_ae hpair
    rw [hmid.integral_eq φ, hint]
  -- (d) Apply the base lemma to the representatives.
  have hconc_rep :=
    transport_linear_at_u_of_smooth (pReal := pReal) (qReal := qReal) hpq
      (A := A) (B := B) (u := uRep) (Du := DuRep)
      hA hB hu_rep_lp hDu_rep_lp hu_rep_meas hu_rep_per hu_rep_loc
      hDu_rep_meas hDu_rep_per hDu_rep_loc hweak_rep hsmooth
  -- (e) Transport the conclusion back to `u`/`Du i` via `integral_congr_ae`.
  have hA_eq : (∫ x in UnitCube d, A x * uRep x ∂(volume : Measure (Fin d → ℝ)))
      = (∫ x in UnitCube d, A x * u x ∂(volume : Measure (Fin d → ℝ))) := by
    refine integral_congr_ae ?_
    filter_upwards [hu_ae] with x hx
    rw [hx]
  have hB_eq : ∀ i,
      (∫ x in UnitCube d, B i x * DuRep i x ∂(volume : Measure (Fin d → ℝ)))
      = (∫ x in UnitCube d, B i x * Du i x ∂(volume : Measure (Fin d → ℝ))) := by
    intro i
    refine integral_congr_ae ?_
    filter_upwards [hDu_ae i] with x hx
    rw [hx]
  rw [hA_eq, Finset.sum_congr rfl (fun i _ => hB_eq i)] at hconc_rep
  exact hconc_rep

open StationaryMFG.Periodic in
/-- **Witness-level transport identity `eq:congest.transport`**
(T2 phase6 BB VIid **child-5b-ii-B** — the deliverable of this task).

For every smooth periodic test `φ`, the first-variation transport identity

```
(∫ (m − 1)·φ + J(x, Du, m) ⬝ ∇φ) + (∫ ε·Gateaux) = 0
```

holds at the Browder–Minty witness `(m, u, Du)`. The proof is the `t → 0`
squeeze `iota_transport_smooth_assembled_J`, fed:

* `h_dir := congestion_VI_hdir_at_witness` (the per-direction `t · ι(t) ≥ 0`
  inequality, both signs, with all four `(s, ψ)`-indexed deferred hyps
  discharged in child-5b-ii-A2);
* `h_lim`, the DCT continuity at `t = 0`, assembled here from
  `iota_firstorder_h_lim_dct_J` and its four `5b` certs at `(φ, ∇φ)`:
  - `hcontA` from `iota_FA_continuous_at_zero_ae_J`
    (`hcong.mDpHat0.continuous_J` + `hm_nn`);
  - `hcontB` from `iota_FB_continuous_at_zero_ae` (`1 < γ̄`);
  - `gA`/`hgA_int`/`hboundA` from `iota_FA_uniform_dominator_J`;
  - `gB`/`hgB_int`/`hboundB` from `iota_FB_uniform_dominator`;
  - `hmeasA`: the J-flux mass + dot-product is a.e.-strongly-measurable, via
    `congestion_VI_Jflux_aemeasurable` at the perturbed gradient `Du + t·∇φ`;
  - `hmeasB`: the ε-Gateaux integrand rewrites (algebraically, as in
    `iota_FB_integrand_continuous`) to `ε·(vecSignedRpow γ̄ (Du+t∇φ) ⬝ ∇φ)
    + ε·(signedRpow γ̄ (u+tφ)·φ)`, a measurable composition of the continuous
    signed-power maps with the L^{γ̄} data.

No `0 < m` / power-growth / `Hext_finite_at_zero` crutch: the `{m = 0}`
boundary carries the genuine `J(x, ·, 0)` value throughout. -/
theorem congestion_transport_at_witness
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) m)
    (hm_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hu_memGamma : MemLpPer (d := d)
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) u)
    (hDu_mem : ∀ i,
      MemLpPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Du i))
    (hQuot_m_mem :
      MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (fun x : Fin d → ℝ =>
          ‖fun i => Du i x‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) /
            (m x ^ hcong.τ + 1)))
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    {ε : ℝ}
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
    (hw_m : (⇑w.1 : (Fin d → ℝ) → ℝ) = m)
    (hw_u : (⇑w.2.1 : (Fin d → ℝ) → ℝ) = u)
    (hw_Du : ∀ i, (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ) = Du i)
    (hcoeWeak_Du : ∀ i,
      Periodic.HasWeakDerivPer (d := d) i
        (⇑w.2.1 : (Fin d → ℝ) → ℝ) (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ))
    (φ : Periodic.SmoothPeriodic d) :
    (∫ x in UnitCube d,
        (m x - 1) * (φ : (Fin d → ℝ) → ℝ) x
          + (J x (fun i => Du i x) (m x)
              ⬝ (fun i => (Periodic.SmoothPeriodic.partialDeriv i φ :
                  (Fin d → ℝ) → ℝ) x))
        ∂(volume : Measure (Fin d → ℝ)))
    +
    (∫ x in UnitCube d,
        ε * vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
            (fun i => Du i x)
          * ((fun i => Du i x)
              ⬝ (fun i => (Periodic.SmoothPeriodic.partialDeriv i φ :
                  (Fin d → ℝ) → ℝ) x))
        + ε * absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β) (u x)
            * (u x * (φ : (Fin d → ℝ) → ℝ) x)
        ∂(volume : Measure (Fin d → ℝ))) = 0 := by
  classical
  set γBar : ℝ := hcong.α * (hcong.β + 1) / hcong.β with hγBardef
  set φf : (Fin d → ℝ) → ℝ := (φ : (Fin d → ℝ) → ℝ) with hφfdef
  set Dφf : Fin d → (Fin d → ℝ) → ℝ :=
    fun i => (Periodic.SmoothPeriodic.partialDeriv i φ : (Fin d → ℝ) → ℝ)
    with hDφfdef
  have hα : 1 < hcong.α := hcong.hα
  have hβ : 0 < hcong.β := hcong.hβ
  have hγ : 1 < γBar := by
    rw [hγBardef]
    exact StationaryMFG.Hamiltonian.one_lt_gammaBar hcong.α hcong.β hα hβ
  -- Smooth-test memberships in the relevant Lᵖ spaces.
  have hφf_betaP : MemLpPer (d := d)
      (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) φf :=
    (Periodic.MemSobolevPer.of_smoothPeriodic _ φ).1
  have hφf_gamma : MemLpPer (d := d) (ENNReal.ofReal γBar) φf := by
    rw [hγBardef]; exact (Periodic.MemSobolevPer.of_smoothPeriodic _ φ).1
  have hDφf_gamma : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBar) (Dφf i) := by
    intro i; rw [hγBardef, hDφfdef]
    exact (Periodic.MemSobolevPer.of_smoothPeriodic _
      (Periodic.SmoothPeriodic.partialDeriv i φ)).1
  have hDu_gamma : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBar) (Du i) := by
    intro i; rw [hγBardef]; exact hDu_mem i
  have hu_gamma : MemLpPer (d := d) (ENNReal.ofReal γBar) u := by
    rw [hγBardef]; exact hu_memGamma
  -- The integrands `FA`, `FB` of the DCT.
  set FA : ℝ → (Fin d → ℝ) → ℝ := fun t => fun x =>
    (m x - 1) * φf x
      + (J x (fun i => Du i x + t * Dφf i x) (m x) ⬝ (fun i => Dφf i x))
    with hFAdef
  set FB : ℝ → (Fin d → ℝ) → ℝ := fun t => fun x =>
    ε * vecAbsPowMinusTwo γBar (fun i => Du i x + t * Dφf i x)
        * ((fun i => Du i x + t * Dφf i x) ⬝ (fun i => Dφf i x))
      + ε * absPowMinusTwo γBar (u x + t * φf x)
          * ((u x + t * φf x) * φf x)
    with hFBdef
  -- ===== `hcontA`, `hcontB`. =====
  have hcontA : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      Filter.Tendsto (fun t => FA t x) (nhds (0 : ℝ)) (nhds (FA 0 x)) := by
    have := iota_FA_continuous_at_zero_ae_J (DpH := DpH) (J := J) (Du := Du)
      (m := m) hcong.mDpHat0.continuous_J hm_nn φf Dφf
    filter_upwards [this] with x hx
    simpa [hFAdef] using hx
  have hcontB : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      Filter.Tendsto (fun t => FB t x) (nhds (0 : ℝ)) (nhds (FB 0 x)) := by
    have := iota_FB_continuous_at_zero_ae (Du := Du) (u := u) (ε := ε)
      (γBar := γBar) hγ φf Dφf
    filter_upwards [this] with x hx
    simpa [hFBdef] using hx
  -- ===== `gA`, `gB` dominators. =====
  obtain ⟨gA, hgA_int, hboundA⟩ :=
    iota_FA_uniform_dominator_J (H := H) hcong hm_mem hm_nn hDu_gamma
      φf Dφf hφf_betaP hDφf_gamma FA (fun t => by rw [hFAdef])
  obtain ⟨gB, hgB_int, hboundB⟩ :=
    iota_FB_uniform_dominator (Du := Du) (u := u) (ε := ε) (γBar := γBar)
      hγ ((Theorems.SimplePower.SimplePowerExponentFacts.paper_holderConjugate_gammaBar
        hα hβ).symm)
      φf Dφf hu_gamma hφf_gamma hDu_gamma hDφf_gamma FB (fun t => by rw [hFBdef])
  -- ===== `hmeasA`, `hmeasB`. =====
  have hm_aem : AEMeasurable m (volume.restrict (UnitCube d)) :=
    aestronglyMeasurable_iff_aemeasurable.mp hm_mem.aestronglyMeasurable
  have hu_aem : AEMeasurable u (volume.restrict (UnitCube d)) :=
    aestronglyMeasurable_iff_aemeasurable.mp hu_gamma.aestronglyMeasurable
  have hφf_aem : AEMeasurable φf (volume.restrict (UnitCube d)) :=
    aestronglyMeasurable_iff_aemeasurable.mp hφf_betaP.aestronglyMeasurable
  have hDu_aem : ∀ i, AEMeasurable (Du i) (volume.restrict (UnitCube d)) :=
    fun i => aestronglyMeasurable_iff_aemeasurable.mp (hDu_gamma i).aestronglyMeasurable
  have hDφf_aem : ∀ i, AEMeasurable (Dφf i) (volume.restrict (UnitCube d)) :=
    fun i => aestronglyMeasurable_iff_aemeasurable.mp (hDφf_gamma i).aestronglyMeasurable
  have hmeasA : ∀ᶠ t in nhds (0 : ℝ),
      AEStronglyMeasurable (FA t) (volume.restrict (UnitCube d)) := by
    refine Filter.Eventually.of_forall (fun t => ?_)
    rw [hFAdef]
    have hmass : AEMeasurable (fun x => (m x - 1) * φf x)
        (volume.restrict (UnitCube d)) :=
      (hm_aem.sub_const 1).mul hφf_aem
    have hpert_aem : AEMeasurable
        (fun x => (fun i => Du i x + t * Dφf i x))
        (volume.restrict (UnitCube d)) := by
      rw [aemeasurable_pi_iff]; intro i
      exact (hDu_aem i).add (aemeasurable_const.mul (hDφf_aem i))
    have hflux : AEMeasurable
        (fun x => J x (fun i => Du i x + t * Dφf i x) (m x)
          ⬝ (fun i => Dφf i x))
        (volume.restrict (UnitCube d)) :=
      congestion_VI_Jflux_aemeasurable hcong.mDpHat0 hpert_aem hm_aem hDφf_aem
    exact (hmass.add hflux).aestronglyMeasurable
  have hmeasB : ∀ᶠ t in nhds (0 : ℝ),
      AEStronglyMeasurable (FB t) (volume.restrict (UnitCube d)) := by
    refine Filter.Eventually.of_forall (fun t => ?_)
    -- Measurability of the perturbed vector and scalar.
    have hpert_aem : AEMeasurable
        (fun x => (fun i => Du i x + t * Dφf i x))
        (volume.restrict (UnitCube d)) := by
      rw [aemeasurable_pi_iff]; intro i
      exact (hDu_aem i).add (aemeasurable_const.mul (hDφf_aem i))
    have hscal_aem : AEMeasurable (fun x => u x + t * φf x)
        (volume.restrict (UnitCube d)) :=
      hu_aem.add (aemeasurable_const.mul hφf_aem)
    -- Vector summand (signed-power form).
    have hvecRpow_aem : AEMeasurable
        (fun x => vecSignedRpow γBar (fun i => Du i x + t * Dφf i x))
        (volume.restrict (UnitCube d)) :=
      (continuous_vecSignedRpow hγ).measurable.comp_aemeasurable hpert_aem
    have hvecdot_aem : AEMeasurable
        (fun x => vecSignedRpow γBar (fun i => Du i x + t * Dφf i x)
          ⬝ (fun i => Dφf i x))
        (volume.restrict (UnitCube d)) := by
      set g : Fin d → (Fin d → ℝ) → ℝ :=
        fun i x => vecSignedRpow γBar (fun j => Du j x + t * Dφf j x) i * Dφf i x
        with hgdef
      have hsum : AEMeasurable (∑ i, g i) (volume.restrict (UnitCube d)) :=
        Finset.aemeasurable_sum Finset.univ (fun i _ => by
          rw [hgdef]
          exact ((measurable_pi_apply i).comp_aemeasurable hvecRpow_aem).mul
            (hDφf_aem i))
      have heq : (fun x => vecSignedRpow γBar (fun i => Du i x + t * Dφf i x)
            ⬝ (fun i => Dφf i x))
          = (∑ i, g i) := by
        funext x; rw [Finset.sum_apply]; unfold euclideanDot; rfl
      rw [heq]; exact hsum
    -- Scalar summand (signed-power form).
    have hscRpow_aem : AEMeasurable (fun x => signedRpow γBar (u x + t * φf x))
        (volume.restrict (UnitCube d)) :=
      (continuous_signedRpow hγ).measurable.comp_aemeasurable hscal_aem
    -- The signed-power form is AEMeasurable.
    have hAaem : AEMeasurable (fun x =>
        ε * (vecSignedRpow γBar (fun i => Du i x + t * Dφf i x)
            ⬝ (fun i => Dφf i x))
          + ε * (signedRpow γBar (u x + t * φf x) * φf x))
        (volume.restrict (UnitCube d)) :=
      (aemeasurable_const.mul hvecdot_aem).add
        (aemeasurable_const.mul (hscRpow_aem.mul hφf_aem))
    -- `FB t` equals (pointwise) the signed-power form (algebraic identity).
    refine (hAaem.aestronglyMeasurable).congr (Filter.Eventually.of_forall
      (fun x => ?_))
    change ε * (vecSignedRpow γBar (fun i => Du i x + t * Dφf i x)
          ⬝ (fun i => Dφf i x))
        + ε * (signedRpow γBar (u x + t * φf x) * φf x)
      = FB t x
    have hvec : vecSignedRpow γBar (fun i => Du i x + t * Dφf i x)
          ⬝ (fun i => Dφf i x)
        = vecAbsPowMinusTwo γBar (fun i => Du i x + t * Dφf i x)
            * ((fun i => Du i x + t * Dφf i x) ⬝ (fun i => Dφf i x)) := by
      unfold euclideanDot vecSignedRpow
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    have hsc : signedRpow γBar (u x + t * φf x) * φf x
        = absPowMinusTwo γBar (u x + t * φf x) * ((u x + t * φf x) * φf x) := by
      unfold signedRpow; ring
    rw [hvec, hsc, hFBdef]; ring
  -- ===== `h_lim` from `iota_firstorder_h_lim_dct_J`. =====
  have h_lim := iota_firstorder_h_lim_dct_J (DpH := DpH) (J := J) (Du := Du)
    (m := m) (u := u) (ε := ε) (γBar := γBar) φf Dφf FA FB
    (fun t => by rw [hFAdef]) (fun t => by rw [hFBdef])
    hcontA hcontB gA gB hgA_int hgB_int hboundA hboundB hmeasA hmeasB
  -- ===== `h_dir` from `congestion_VI_hdir_at_witness`. =====
  have h_dir := congestion_VI_hdir_at_witness hmon hcong hm_mem hm_nn
    hu_memGamma hDu_mem hQuot_m_mem hVmeas hV hAeq hKeq hVI hw_m hw_u hw_Du
    hcoeWeak_Du φ
  -- ===== Final transport call. =====
  exact iota_transport_smooth_assembled_J (_V := V) (DpH := DpH) (J := J)
    (Du := Du) (m := m) (u := u) (ε := ε) (γBar := γBar) φf Dφf FA FB
    (fun t => by rw [hFAdef]) (fun t => by rw [hFBdef]) h_dir h_lim

open StationaryMFG.Periodic in
/-- **VIid-5c child-E1: the three "easy" per-summand integrability
certificates at the Browder–Minty witness data.**

Three of the six integrability certificates that
`coeVI_identity_atWitness_of_closure` (Existence.lean) / its `_atPowerData`
wrapper (Coercivity.lean) consume are pure `Lᵖ`/Hölder facts on the
finite-measure cube, derivable directly from the witness `Lᵖ` data
(`m ∈ L^{β̄}`, `u ∈ L^{γ̄}`, `V ∈ L^{β̄'}`, with `β̄ = β+1`, `γ̄ = α(β+1)/β`,
`β̄' = (β+1)/β`):

* `hu_int`  — `u ∈ L¹` (finite-measure inclusion `L^{γ̄} ↪ L¹`, `1 ≤ γ̄`);
* `hmu_int` — `m·u ∈ L¹` (Hölder `(β̄, β̄')`, with `u ∈ L^{β̄'}` from
  `L^{γ̄} ↪ L^{β̄'}` since `β̄' ≤ γ̄`);
* `hVm_int` — `V·m ∈ L¹` (Hölder `(β̄', β̄)`).

These are phrased against bare functions `m u V` with the witness `MemLpPer`
hypotheses, so both the abstract `coeVI_identity_atWitness_of_closure` and the
`_atPowerData` wrapper can instantiate them at `data.weakVI.choose`'s
coercions. The remaining three certificates (the `m·D_pH·Du` flux summand,
the `m·H` summand, and the gap's `coe_epsTerms`) need the congestion-growth
envelope / the concrete gap and are produced separately (child E1b). -/
theorem congestion_VIid_easy_int_certs
    {α β : ℝ} (hα : 1 < α) (hβ : 0 < β)
    {m u V : (Fin d → ℝ) → ℝ}
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (β + 1)) m)
    (hu_memGamma : MemLpPer (d := d) (ENNReal.ofReal (α * (β + 1) / β)) u)
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β)) V) :
    MeasureTheory.Integrable u
        (MeasureTheory.volume.restrict (UnitCube d))
    ∧ MeasureTheory.Integrable (fun x => m x * u x)
        (MeasureTheory.volume.restrict (UnitCube d))
    ∧ MeasureTheory.Integrable (fun x => V x * m x)
        (MeasureTheory.volume.restrict (UnitCube d)) := by
  have hαpos : 0 < α := lt_trans one_pos hα
  have hβ1_pos : 0 < β + 1 := by linarith
  -- Abbreviations matching `gammaBar`/`betaBar'`.
  have hβbar' : (β + 1) / β = StationaryMFG.Hamiltonian.betaBar' β := rfl
  have hγbar : α * (β + 1) / β = StationaryMFG.Hamiltonian.gammaBar α β := by
    rw [StationaryMFG.Hamiltonian.gammaBar]
  -- `u ∈ L^{β̄'}` via the finite-measure inclusion `L^{γ̄} ↪ L^{β̄'}`.
  have hβ'_le_γ : ENNReal.ofReal ((β + 1) / β)
      ≤ ENNReal.ofReal (α * (β + 1) / β) := by
    apply ENNReal.ofReal_le_ofReal
    rw [hβbar', hγbar]
    exact StationaryMFG.Hamiltonian.betaBar'_le_gammaBar hα.le hβ
  have hu_β' : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β)) u :=
    MemLpPer.mono_exponent_finite hβ'_le_γ ENNReal.ofReal_ne_top hu_memGamma
  -- The real Hölder pair `(β̄, β̄') = (β+1, (β+1)/β)`.
  have hpq : (β + 1).HolderConjugate ((β + 1) / β) := by
    refine (Real.holderConjugate_iff).mpr ⟨by linarith, ?_⟩
    field_simp
    ring
  refine ⟨?_, ?_, ?_⟩
  · -- `hu_int`: `u ∈ L¹` via `L^{β̄'} ↪ L¹` (`1 ≤ β̄'`).
    have h1le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((β + 1) / β) := by
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
      apply ENNReal.ofReal_le_ofReal
      rw [le_div_iff₀ hβ]; linarith
    have hu_one : MemLpPer (d := d) (1 : ℝ≥0∞) u :=
      MemLpPer.mono_exponent_finite h1le ENNReal.ofReal_ne_top hu_β'
    exact (MeasureTheory.memLp_one_iff_integrable.mp hu_one)
  · -- `hmu_int`: `m·u ∈ L¹` (Hölder `(β̄, β̄')`).
    exact MemLpPer.integrable_mul hpq hm_mem hu_β'
  · -- `hVm_int`: `V·m ∈ L¹` (Hölder `(β̄', β̄)`).
    exact MemLpPer.integrable_mul hpq.symm hV hm_mem

open StationaryMFG.Periodic in
/-- **VIid-5c child E1b — the `m·(D_pH·Du)` flux integrability cert at the
witness, re-derived from raw witness data.**

`coeVI_identity_atWitness_of_closure` (Existence.lean) needs
`Integrable (m·(D_pH(x,Du,m)⬝Du))` on the cube. The `mDpHDu_int`
producer (Existence.lean ~4850) reads it off a
`CongestionBareRepresentatives` record whose `hVI_identity_coe` field is
exactly the identity we are producing (circular). This lemma re-derives
the same envelope from raw hypotheses, mirroring the `hJflux_γ'`/`hmflux_int`
block of `congestion_transport_at_u_witness` but applied **directly** to
`m·D_pH` (no `J = m·D_pH` substitution, hence no `hJat0` boundary datum):

* `m·D_pH(x,Du,m)ᵢ ∈ L^{γ̄'}` for each `i`, via the `m`-multiplied flux
  envelope (`hcong.DpH_upper`, dominated by
  `congestion_flux_dominator_memLp_gammaBar'_le`), with the `{m = 0}`
  boundary handled by `m·D_pH = 0` (no growth bound consumed there);
* Hölder `(γ̄, γ̄')` with `Duᵢ ∈ L^{γ̄}` gives the summand
  `m·D_pHᵢ·Duᵢ ∈ L¹`; summing over `i` gives the dotted flux.

No `0 < m` / power-growth / `Hext_finite_at_zero` crutch. -/
theorem congestion_VIid_mFlux_int
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    {m : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) m)
    (hm_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hDu_mem : ∀ i,
      MemLpPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Du i)) :
    MeasureTheory.Integrable
      (fun x => m x * ((DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x)))
      (volume.restrict (UnitCube d)) := by
  classical
  set α : ℝ := hcong.α with hαdef
  set β : ℝ := hcong.β with hβdef
  set τ : ℝ := hcong.τ with hτdef
  set γBar : ℝ := α * (β + 1) / β with hγBardef
  have hα : 1 < α := hcong.hα
  have hβ : 0 < β := hcong.hβ
  have hτ_nn : 0 ≤ τ := hcong.hτ.1
  have hτ_le : τ ≤ 1 := hcong.hτ.2
  have hαpos : 0 < α := lt_trans one_pos hα
  have hC_pos : 0 < hcong.C := hcong.hC
  have hγ : 1 < γBar := by
    rw [hγBardef]; exact StationaryMFG.Hamiltonian.one_lt_gammaBar α β hα hβ
  have hγpos : 0 < γBar := lt_trans one_pos hγ
  haveI hfin : IsFiniteMeasure
      (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  set γBar' : ℝ := γBar / (γBar - 1) with hγBar'def
  have hpq : γBar.HolderConjugate γBar' := by
    rw [hγBardef, hγBar'def, hγBardef]
    exact Theorems.SimplePower.SimplePowerExponentFacts.paper_holderConjugate_gammaBar
      hα hβ
  -- `Lᵖ` memberships of the witness data at `γ̄`.
  have hDu_gamma : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBar) (Du i) := by
    intro i; rw [hγBardef]; exact hDu_mem i
  have hm_aem : AEMeasurable m (volume.restrict (UnitCube d)) :=
    aestronglyMeasurable_iff_aemeasurable.mp hm_mem.aestronglyMeasurable
  have hDu_aem : ∀ i, AEMeasurable (Du i) (volume.restrict (UnitCube d)) :=
    fun i => aestronglyMeasurable_iff_aemeasurable.mp (hDu_gamma i).aestronglyMeasurable
  -- The J-flux dominator membership at the untruncated density.
  have hflux_dom : MemLpPer (d := d) (ENNReal.ofReal γBar')
      (fun x => hcong.C * (1 + m x ^ (1 - τ))
            * ‖fun j => Du j x‖ ^ (α * (1 + τ / β) - 1)
          + hcong.C * (m x ^ (β + 1 - β / α) + 1)) := by
    have h := congestion_flux_dominator_memLp_gammaBar'_le (d := d)
      (α := α) (β := β) (τ := τ) (K := hcong.C)
      hα hβ hτ_nn hτ_le (m := m) (Du := Du) hm_mem hm_nn
      (fun i => by rw [hαdef, hβdef]; exact hDu_mem i)
    have hexp : ENNReal.ofReal (α * (β + 1) / β / (α * (β + 1) / β - 1))
        = ENNReal.ofReal γBar' := by congr 1
    rwa [hexp] at h
  -- `m·D_pH(x,Du,m)ᵢ ∈ L^{γ̄'}` for each `i`, via the `m`-multiplied flux envelope.
  have hmDpH_γ' : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBar')
      (fun x => m x * DpH x (fun j => Du j x) (m x) i) := by
    intro i
    have hmDpH_meas : AEStronglyMeasurable
        (fun x => m x * DpH x (fun j => Du j x) (m x) i)
        (volume.restrict (UnitCube d)) := by
      have hDu' : AEMeasurable (fun x => (fun j => Du j x))
          (volume.restrict (UnitCube d)) := by
        rw [aemeasurable_pi_iff]; intro j; exact hDu_aem j
      have hprod : AEMeasurable
          (fun x : Fin d → ℝ => (x, (fun j => Du j x), m x))
          (volume.restrict (UnitCube d)) :=
        aemeasurable_id.prodMk (hDu'.prodMk hm_aem)
      have hvec : AEMeasurable (fun x => DpH x (fun j => Du j x) (m x))
          (volume.restrict (UnitCube d)) :=
        hcong.measurable_DpH.comp_aemeasurable hprod
      exact (hm_aem.mul
        ((measurable_pi_apply i).comp_aemeasurable hvec)).aestronglyMeasurable
    have hbound : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖m x * DpH x (fun j => Du j x) (m x) i‖
          ≤ hcong.C * (1 + m x ^ (1 - τ))
                * ‖fun j => Du j x‖ ^ (α * (1 + τ / β) - 1)
              + hcong.C * (m x ^ (β + 1 - β / α) + 1) := by
      filter_upwards [hcong.DpH_upper, hm_nn] with x hx hx_nn
      set px : Fin d → ℝ := fun j => Du j x with hpx
      rcases eq_or_lt_of_le hx_nn with hx0 | hxpos
      · have hm0 : m x = 0 := hx0.symm
        rw [hm0, zero_mul, norm_zero]
        have h1 : 0 ≤ hcong.C * (1 + (0:ℝ) ^ (1 - τ))
            * ‖fun j => Du j x‖ ^ (α * (1 + τ / β) - 1) := by positivity
        have h2 : 0 ≤ hcong.C * ((0:ℝ) ^ (β + 1 - β / α) + 1) := by positivity
        linarith
      · have hDpH_le := hx px (m x) hxpos
        have hcomp_le : |m x * DpH x px (m x) i| ≤ m x * ‖DpH x px (m x)‖ := by
          rw [abs_mul, abs_of_pos hxpos]
          apply mul_le_mul_of_nonneg_left _ hxpos.le
          have := norm_le_pi_norm (DpH x px (m x)) i
          simpa [Real.norm_eq_abs] using this
        have hmul : m x * ‖DpH x px (m x)‖
            ≤ hcong.C * (1 + m x ^ (1 - τ)) * ‖px‖ ^ (α * (1 + τ / β) - 1)
              + hcong.C * (m x ^ (β + 1 - β / α) + 1) := by
          have hstep := mul_le_mul_of_nonneg_left hDpH_le hxpos.le
          refine le_trans hstep (le_of_eq ?_)
          have e1 : m x * (1 / m x) = 1 := by field_simp
          have e2 : m x * (1 / m x ^ τ) = m x ^ (1 - τ) := by
            rw [mul_one_div, Real.rpow_sub hxpos, Real.rpow_one]
          have e3 : m x * m x ^ (β - β / α) = m x ^ (β + 1 - β / α) := by
            rw [show β + 1 - β / α = 1 + (β - β / α) by ring, Real.rpow_add hxpos,
              Real.rpow_one]
          calc m x * (hcong.C * (1 / m x + 1 / m x ^ τ) * ‖px‖ ^ (α*(1+τ/β)-1)
                  + hcong.C * (m x ^ (β - β/α) + 1 / m x))
              = hcong.C * (m x * (1/m x) + m x * (1/m x^τ))
                    * ‖px‖ ^ (α*(1+τ/β)-1)
                + hcong.C * (m x * m x ^ (β - β/α) + m x * (1/m x)) := by ring
            _ = hcong.C * (1 + m x ^ (1-τ)) * ‖px‖ ^ (α*(1+τ/β)-1)
                + hcong.C * (m x ^ (β+1-β/α) + 1) := by rw [e1, e2, e3]
        rw [Real.norm_eq_abs]; exact le_trans hcomp_le hmul
    apply MemLp.toMemLpPer
    refine MemLp.of_le_mul (c := 1) hflux_dom.toMemLp hmDpH_meas ?_
    filter_upwards [hbound] with x hx
    have hdom_nn : 0 ≤ hcong.C * (1 + m x ^ (1 - τ))
            * ‖fun j => Du j x‖ ^ (α * (1 + τ / β) - 1)
          + hcong.C * (m x ^ (β + 1 - β / α) + 1) :=
      le_trans (norm_nonneg _) hx
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg hdom_nn, one_mul]
    rw [Real.norm_eq_abs] at hx
    exact hx
  -- Each summand `m·D_pHᵢ·Duᵢ ∈ L¹` via Hölder `(γ̄, γ̄')`.
  have hsummand_int : ∀ i, IntegrableOn
      (fun x => m x * DpH x (fun j => Du j x) (m x) i * Du i x) (UnitCube d) := by
    intro i
    have := MemLpPer.integrable_mul hpq.symm (hmDpH_γ' i) (hDu_gamma i)
    simpa [mul_assoc] using this
  -- Sum the summands and rewrite as the dotted flux.
  have hsum := MeasureTheory.integrable_finset_sum
    (Finset.univ : Finset (Fin d)) (fun i _ => hsummand_int i)
  refine hsum.congr ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  change (∑ i, m x * DpH x (fun j => Du j x) (m x) i * Du i x)
    = m x * ((DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
  unfold euclideanDot
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

open StationaryMFG.Periodic in
/-- **VIid-5c child E1b — the `m·H` integrability cert at the witness,
re-derived from raw witness data.**

`coeVI_identity_atWitness_of_closure` (Existence.lean) needs
`Integrable (m·H(x,Du,m))` on the cube. The `mH_int` producer
(Existence.lean ~5425) reads its flux dominator off a
`CongestionBareRepresentatives` record whose `hVI_identity_coe` field is
the identity we are producing (circular). This lemma re-derives the
envelope from raw hypotheses via the two-sided `|H|` bound
`H_two_sided_congestion_of_hmon`:

  `|H(x,Du,m)| ≤ K·(1/m + 1/m^τ)·(‖Du‖^{αt} + 1) + K·(m^β + 1)`  (`m > 0`),

so multiplying by `m ≥ 0`,

  `m·|H| ≤ K·(1 + m^{1-τ})·(‖Du‖^{αt} + 1) + K·(m^{β+1} + m)`.

The single integrable dominator `Bnd` is built from:
* `‖Du‖^{αt} ∈ L¹` (`αt ≤ γ̄`, finite-measure inclusion);
* `m^{1-τ}·‖Du‖^{αt} ∈ L¹` (Hölder `((β+1)/(1-τ) , γ̄/αt)`, exponents
  summing to `1` exactly — the same `m·D_pH·Du` Young split);
* `m^{1-τ} ∈ L¹`, `m^{β+1} ∈ L¹`, `m ∈ L¹`, constants.

The `{m = 0}` set contributes `m·H = 0` (no growth bound consumed). No
`0 < m` / power-growth / `Hext_finite_at_zero` crutch. -/
theorem congestion_VIid_mH_int
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    {m : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) m)
    (hm_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hDu_mem : ∀ i,
      MemLpPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Du i)) :
    MeasureTheory.Integrable
      (fun x => m x * H x (fun i => Du i x) (m x))
      (volume.restrict (UnitCube d)) := by
  classical
  set α : ℝ := hcong.α with hαdef
  set β : ℝ := hcong.β with hβdef
  set τ : ℝ := hcong.τ with hτdef
  set γBar : ℝ := α * (β + 1) / β with hγBardef
  set αt : ℝ := α * (1 + τ / β) with hαtdef
  have hα : 1 < α := hcong.hα
  have hβ : 0 < β := hcong.hβ
  have hτ_nn : 0 ≤ τ := hcong.hτ.1
  have hτ_le : τ ≤ 1 := hcong.hτ.2
  have hαpos : 0 < α := lt_trans one_pos hα
  have hβp1_pos : 0 < β + 1 := by linarith
  have hγ : 1 < γBar := by
    rw [hγBardef]; exact StationaryMFG.Hamiltonian.one_lt_gammaBar α β hα hβ
  have hγpos : 0 < γBar := lt_trans one_pos hγ
  have hαt_pos : 0 < αt := by rw [hαtdef]; positivity
  have hαt_le_γ : αt ≤ γBar := by
    have hβne : (β : ℝ) ≠ 0 := ne_of_gt hβ
    have he1 : αt = α * (β + τ) / β := by
      rw [hαtdef]; field_simp
    have he2 : γBar = α * (β + 1) / β := hγBardef
    rw [he1, he2]
    rw [div_le_div_iff_of_pos_right hβ]
    apply mul_le_mul_of_nonneg_left _ hαpos.le
    linarith
  haveI hfin : IsFiniteMeasure
      (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  set μC : Measure (Fin d → ℝ) := volume.restrict (UnitCube d) with hμC
  -- `Lᵖ` memberships of `Du` at `γ̄`.
  have hDu_gamma : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBar) (Du i) := by
    intro i; rw [hγBardef]; exact hDu_mem i
  have hm_aem : AEMeasurable m μC :=
    aestronglyMeasurable_iff_aemeasurable.mp hm_mem.aestronglyMeasurable
  have hDu_aem : ∀ i, AEMeasurable (Du i) μC :=
    fun i => aestronglyMeasurable_iff_aemeasurable.mp (hDu_gamma i).aestronglyMeasurable
  -- AE-strong measurability of `m·H(·,Du,m)` (Carathéodory composition).
  have hDu' : AEMeasurable (fun x => (fun j => Du j x)) μC := by
    rw [aemeasurable_pi_iff]; intro j; exact hDu_aem j
  have hprod : AEMeasurable
      (fun x : Fin d → ℝ => (x, (fun j => Du j x), m x)) μC :=
    aemeasurable_id.prodMk (hDu'.prodMk hm_aem)
  have hH_comp_aem : AEMeasurable
      (fun x => H x (fun j => Du j x) (m x)) μC :=
    hcong.measurable_H.comp_aemeasurable hprod
  have hmH_aesm : AEStronglyMeasurable
      (fun x => m x * H x (fun i => Du i x) (m x)) μC :=
    (hm_aem.mul hH_comp_aem).aestronglyMeasurable
  -- `‖Du‖^{αt} ∈ L^{γ̄/αt}` and (finite measure) `∈ L¹`.
  have hDuVec_gamma : MemLpPer (d := d) (ENNReal.ofReal γBar)
      (fun x => ‖fun j => Du j x‖) := by
    have hvec : MemLpPer (d := d) (ENNReal.ofReal γBar)
        (fun x => (fun j => Du j x)) := by
      rw [Periodic.memLpPer_iff_memLp, MeasureTheory.memLp_pi_iff]
      intro i; exact (hDu_gamma i).toMemLp
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.norm hvec.toMemLp)
  -- `‖Du‖^{αt} ∈ L^{γ̄/αt}` via rpow-closure (`(γ̄/αt)·αt = γ̄`).
  have hDuPow_mem : MemLpPer (d := d) (ENNReal.ofReal (γBar / αt))
      (fun x => ‖fun j => Du j x‖ ^ αt) := by
    have hclose : ENNReal.ofReal (γBar / αt) * ENNReal.ofReal αt
        = ENNReal.ofReal γBar := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1; field_simp
    have h := Periodic.MemLpPer.rpow_closure (d := d)
      (s := ENNReal.ofReal (γBar / αt)) (r := αt) hαt_pos
      (f := fun x => ‖fun j => Du j x‖) (by rw [hclose]; exact hDuVec_gamma)
    -- `rpow_closure` produces `‖‖Du‖‖^{αt}`; collapse the double norm.
    refine h.congr_ae_unitCube ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    simp only [norm_norm]
  have hDuPow_one : MemLpPer (d := d) (1 : ℝ≥0∞)
      (fun x => ‖fun j => Du j x‖ ^ αt) := by
    have h1le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (γBar / αt) := by
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
      apply ENNReal.ofReal_le_ofReal
      rw [le_div_iff₀ hαt_pos, one_mul]; exact hαt_le_γ
    exact MemLpPer.mono_exponent_finite h1le ENNReal.ofReal_ne_top hDuPow_mem
  have hDuPow_int : MeasureTheory.Integrable
      (fun x => ‖fun j => Du j x‖ ^ αt) μC :=
    MeasureTheory.memLp_one_iff_integrable.mp hDuPow_one
  -- `m^{1-τ}·‖Du‖^{αt} ∈ L¹` via Hölder `((β+1)/(1-τ) , γ̄/αt)`.
  -- `m^{1-τ} ∈ L^{(β+1)/(1-τ)}` (rpow-closure if `τ < 1`; constant `1` if `τ = 1`).
  set p₁ : ℝ := (β + 1) / (1 - τ) with hp₁def
  have hmpow_int : MeasureTheory.Integrable
      (fun x => m x ^ (1 - τ) * ‖fun j => Du j x‖ ^ αt) μC := by
    rcases lt_or_eq_of_le hτ_le with hτ_lt | hτ_eq
    · -- `τ < 1`.
      have h1mτ_pos : 0 < 1 - τ := by linarith
      have hp₁_pos : 0 < p₁ := by rw [hp₁def]; positivity
      -- `m^{1-τ} ∈ L^{p₁}` via rpow-closure (`p₁·(1-τ) = β+1`).
      have hmpow_mem : MemLpPer (d := d) (ENNReal.ofReal p₁)
          (fun x => m x ^ (1 - τ)) := by
        have hclose : ENNReal.ofReal p₁ * ENNReal.ofReal (1 - τ)
            = ENNReal.ofReal (β + 1) := by
          rw [← ENNReal.ofReal_mul hp₁_pos.le]
          congr 1; rw [hp₁def]; field_simp
        have h := Periodic.MemLpPer.rpow_closure (d := d)
          (s := ENNReal.ofReal p₁) (r := 1 - τ) h1mτ_pos
          (f := fun x => |m x|) (by
            rw [hclose]; exact MemLp.toMemLpPer hm_mem.toMemLp.abs)
        -- `‖|m|‖^{1-τ} = m^{1-τ}` a.e. (using `m ≥ 0`).
        refine h.congr_ae_unitCube ?_
        filter_upwards [hm_nn] with x hx
        rw [Real.norm_eq_abs, abs_abs, abs_of_nonneg hx]
      -- Hölder conjugacy of `(p₁, γ̄/αt)`: `1/p₁ + αt/γ̄ = 1`.
      have hconj : p₁.HolderConjugate (γBar / αt) := by
        rw [Real.holderConjugate_iff]
        refine ⟨by rw [hp₁def]; rw [lt_div_iff₀ h1mτ_pos]; nlinarith, ?_⟩
        rw [hp₁def, hγBardef, hαtdef]
        field_simp
        ring
      have h := MemLpPer.integrable_mul hconj hmpow_mem hDuPow_mem
      exact h
    · -- `τ = 1`: `m^{1-τ} = m^0 = 1`, so reduce to `hDuPow_int`.
      refine hDuPow_int.congr ?_
      refine Filter.Eventually.of_forall (fun x => ?_)
      have h1mτ0 : (1 : ℝ) - τ = 0 := by rw [← hτ_eq]; ring
      simp only [h1mτ0, Real.rpow_zero, one_mul]
  -- The mass building blocks.
  -- `m^{β+1} ∈ L¹` via rpow-closure (`1·(β+1) = β+1`) and `m ≥ 0`.
  have hMβ1 : MeasureTheory.Integrable (fun x => m x ^ (β + 1)) μC := by
    have hclose : (1 : ℝ≥0∞) * ENNReal.ofReal (β + 1)
        = ENNReal.ofReal (β + 1) := by rw [one_mul]
    have h : MemLpPer (d := d) (1 : ℝ≥0∞) (fun x => ‖m x‖ ^ (β + 1)) :=
      Periodic.MemLpPer.rpow_closure (d := d) (s := (1 : ℝ≥0∞)) (r := β + 1)
        hβp1_pos (f := m) (by rw [hclose]; exact hm_mem)
    have hint := MeasureTheory.memLp_one_iff_integrable.mp h.toMemLp
    refine hint.congr ?_
    filter_upwards [hm_nn] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx]
  -- `m ∈ L¹` via the finite-measure inclusion `L^{β+1} ↪ L¹`.
  have hm_one_int : MeasureTheory.Integrable m μC := by
    have h1le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (β + 1) := by
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
      apply ENNReal.ofReal_le_ofReal; linarith
    exact MeasureTheory.memLp_one_iff_integrable.mp
      (MemLpPer.mono_exponent_finite h1le ENNReal.ofReal_ne_top hm_mem)
  -- `m^{1-τ} ∈ L¹` via the finite-measure inclusion `L^{β+1} ↪ L^{(β+1)/(1-τ)}…`.
  -- Simplest: dominate `m^{1-τ} ≤ m^{β+1} + 1` (Young at scale 1, `m > 0`).
  have hmpow_mass_int : MeasureTheory.Integrable
      (fun x => m x ^ (1 - τ)) μC := by
    have hone_int : MeasureTheory.Integrable (fun _ : (Fin d → ℝ) => (1 : ℝ)) μC :=
      MeasureTheory.integrable_const 1
    have hdom : MeasureTheory.Integrable (fun x => m x ^ (β + 1) + 1) μC :=
      hMβ1.add hone_int
    have h1mτ_nn : 0 ≤ 1 - τ := by linarith
    have hmeas : AEStronglyMeasurable (fun x => m x ^ (1 - τ)) μC :=
      (Real.continuous_rpow_const h1mτ_nn).comp_aestronglyMeasurable
        hm_mem.aestronglyMeasurable
    refine hdom.mono' hmeas ?_
    filter_upwards [hm_nn] with x hx
    have hnn : 0 ≤ m x ^ (β + 1) := Real.rpow_nonneg hx _
    have hbnd : m x ^ (1 - τ) ≤ m x ^ (β + 1) + 1 := by
      by_cases hm1 : 1 ≤ m x
      · have : m x ^ (1 - τ) ≤ m x ^ (β + 1) :=
          Real.rpow_le_rpow_of_exponent_le hm1 (by linarith)
        linarith
      · push_neg at hm1
        have hle1 : m x ^ (1 - τ) ≤ 1 :=
          Real.rpow_le_one hx hm1.le h1mτ_nn
        linarith
    have hlhs_nn : 0 ≤ m x ^ (1 - τ) := Real.rpow_nonneg hx _
    rw [Real.norm_eq_abs, abs_of_nonneg hlhs_nn]
    exact hbnd
  -- Two-sided `|H|` bound, valid for all `p, m > 0`.
  obtain ⟨K, hK_pos, hHbnd⟩ := H_two_sided_congestion_of_hmon hmon hcong
  -- The integrable dominator `Bnd`.
  set Bnd : (Fin d → ℝ) → ℝ :=
    fun x => K * (‖fun j => Du j x‖ ^ αt + 1)
            + K * (m x ^ (1 - τ) * (‖fun j => Du j x‖ ^ αt) + m x ^ (1 - τ))
            + (K * m x ^ (β + 1) + K * m x) with hBnd_def
  have hBnd_int : MeasureTheory.Integrable Bnd μC := by
    have hone_int : MeasureTheory.Integrable (fun _ : (Fin d → ℝ) => (1 : ℝ)) μC :=
      MeasureTheory.integrable_const 1
    have t1 : MeasureTheory.Integrable
        (fun x => K * (‖fun j => Du j x‖ ^ αt + 1)) μC :=
      (hDuPow_int.add hone_int).const_mul K
    have t2 : MeasureTheory.Integrable
        (fun x => K * (m x ^ (1 - τ) * (‖fun j => Du j x‖ ^ αt)
          + m x ^ (1 - τ))) μC :=
      (hmpow_int.add hmpow_mass_int).const_mul K
    have t3 : MeasureTheory.Integrable
        (fun x => K * m x ^ (β + 1) + K * m x) μC :=
      (hMβ1.const_mul K).add (hm_one_int.const_mul K)
    exact (t1.add t2).add t3
  -- Pointwise AE bound `‖m·H‖ ≤ Bnd`.
  have hPointwise : ∀ᵐ x ∂μC,
      ‖m x * H x (fun i => Du i x) (m x)‖ ≤ Bnd x := by
    filter_upwards [hHbnd, hm_nn] with x hx hx_nn
    set p : Fin d → ℝ := fun j => Du j x with hpdef
    have hαt_x : ‖p‖ ^ (α * (1 + τ / β)) = ‖p‖ ^ αt := by rw [hαtdef]
    rcases eq_or_lt_of_le hx_nn with hx0 | hxpos
    · -- `m x = 0`: the integrand vanishes; `Bnd x ≥ 0`.
      have hm0 : m x = 0 := hx0.symm
      rw [hm0, zero_mul, norm_zero]
      have hKnn : 0 ≤ K := hK_pos.le
      have hP_nn : 0 ≤ ‖fun j => Du j x‖ ^ αt := Real.rpow_nonneg (norm_nonneg _) _
      have hmτ_nn : 0 ≤ m x ^ (1 - τ) := Real.rpow_nonneg hx_nn _
      have hmβ_nn : 0 ≤ m x ^ (β + 1) := Real.rpow_nonneg hx_nn _
      simp only [hBnd_def]
      have e1 : 0 ≤ K * (‖fun j => Du j x‖ ^ αt + 1) := by positivity
      have e2 : 0 ≤ K * (m x ^ (1 - τ) * (‖fun j => Du j x‖ ^ αt) + m x ^ (1 - τ)) := by
        positivity
      have e3 : 0 ≤ K * m x ^ (β + 1) + K * m x := by
        have : 0 ≤ m x := hx_nn
        positivity
      linarith
    · -- `m x > 0`: multiply the two-sided bound by `m x`.
      have hHb := hx p (m x) hxpos
      rw [hαt_x] at hHb
      -- `m·|H| ≤ m·[K(1/m+1/m^τ)(‖p‖^{αt}+1) + K(m^β+1)]`.
      have hmH_le : m x * |H x p (m x)|
          ≤ m x * (K * ((1 / m x) + (1 / m x ^ τ)) * (‖p‖ ^ αt + 1)
              + K * (m x ^ β + 1)) :=
        mul_le_mul_of_nonneg_left hHb hxpos.le
      -- Simplify the RHS to the `Bnd` form.
      have e1 : m x * (1 / m x) = 1 := by field_simp
      have e2 : m x * (1 / m x ^ τ) = m x ^ (1 - τ) := by
        rw [mul_one_div, Real.rpow_sub hxpos, Real.rpow_one]
      have e3 : m x * m x ^ β = m x ^ (β + 1) := by
        rw [show β + 1 = 1 + β by ring, Real.rpow_add hxpos, Real.rpow_one]
      have hrhs_eq : m x * (K * ((1 / m x) + (1 / m x ^ τ)) * (‖p‖ ^ αt + 1)
              + K * (m x ^ β + 1))
          = K * (m x * (1 / m x) + m x * (1 / m x ^ τ)) * (‖p‖ ^ αt + 1)
            + K * (m x * m x ^ β + m x) := by ring
      rw [hrhs_eq, e1, e2, e3] at hmH_le
      -- Now `m·|H| ≤ K·(1 + m^{1-τ})·(‖p‖^{αt}+1) + K·(m^{β+1} + m)`.
      have hexpand : K * (1 + m x ^ (1 - τ)) * (‖p‖ ^ αt + 1)
            + K * (m x ^ (β + 1) + m x)
          = Bnd x := by
        rw [hBnd_def]; ring
      have hnorm_eq : ‖m x * H x p (m x)‖ = m x * |H x p (m x)| := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos hxpos]
      rw [hnorm_eq]
      calc m x * |H x p (m x)|
          ≤ K * (1 + m x ^ (1 - τ)) * (‖p‖ ^ αt + 1)
            + K * (m x ^ (β + 1) + m x) := by linarith
        _ = Bnd x := hexpand
  exact hBnd_int.mono' hmH_aesm hPointwise

open StationaryMFG.Periodic in
/-- **Witness-level transport identity at `φ = u` (`eq:congest.transport`
tested at `φ = u`).**  (T2 phase6 BB VIid **child-5c-B2** — the deliverable
of this task.)

The smooth-test transport identity `congestion_transport_at_witness`
(`∫[(m−1)φ + J(x,Du,m)⬝∇φ] + ∫ε·Gateaux = 0` for all smooth `φ`) is
*linear* in the test pair `(φ, ∇φ)`: it has the shape
`∫ A·φ + Σᵢ ∫ Bᵢ·∂ᵢφ = 0` with fixed `L^{γ̄'}` coefficients

* `A x = (m x − 1) + ε·|u x|^{γ̄−2}·u x`,
* `Bᵢ x = Jᵢ(x, Du, m) + ε·|Du x|^{γ̄−2}·Duᵢ x`.

The density passage `transport_linear_at_u_of_smooth` then extends the
identity to `φ = u` (`u, Duᵢ ∈ L^{γ̄}_per`). Substituting the flux
`J(x, Du, m)⬝Du = m·(D_pH(x, Du, m)⬝Du)` a.e. — by `hcong.mDpHat0.J_of_pos`
on `{0 < m}` and by the boundary witness datum `hJat0` (`J(x, Du, 0) = 0`)
on `{m = 0}` — yields the `m·(D_pH·Du)` flux form that child A
(`coeVI_identity_from_transport_and_HJ0`) consumes:

```
∫[(m−1)·u + m·(D_pH(x,Du,m)⬝Du)]
  + ∫[ε·|Du|^{γ̄−2}(Du⬝Du) + ε·|u|^{γ̄−2}(u·u)] = 0.
```

No `0 < m` / power-growth / `Hext_finite_at_zero` crutch: the `{m = 0}`
boundary carries the genuine `J(x, ·, 0)` value (here `= 0` via `hJat0`,
matching the `m·D_pH = 0` flux there). -/
theorem congestion_transport_at_u_witness_AEPeriodicRep
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) m)
    (hm_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hu_memGamma : MemLpPer (d := d)
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) u)
    (hDu_mem : ∀ i,
      MemLpPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Du i))
    (hQuot_m_mem :
      MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (fun x : Fin d → ℝ =>
          ‖fun i => Du i x‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) /
            (m x ^ hcong.τ + 1)))
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    {ε : ℝ}
    {Aop : congestionXBanach d
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
    (hAeq : Aop = congestionAepsiOpK hmon hcong hVmeas hV ε)
    (hKeq : K = congestionBanachK d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ)
    (hVI : ∀ v ∈ K, 0 ≤ Aop v (v - w))
    (hw_m : (⇑w.1 : (Fin d → ℝ) → ℝ) = m)
    (hw_u : (⇑w.2.1 : (Fin d → ℝ) → ℝ) = u)
    (hw_Du : ∀ i, (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ) = Du i)
    (hcoeWeak_Du : ∀ i,
      Periodic.HasWeakDerivPer (d := d) i
        (⇑w.2.1 : (Fin d → ℝ) → ℝ) (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ))
    (hu_rep : Periodic.AEPeriodicRep u)
    (hDu_rep : ∀ i, Periodic.AEPeriodicRep (Du i))
    (hJat0 : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      m x = 0 → J x (fun i => Du i x) 0 = 0) :
    (∫ x in UnitCube d,
        ((m x - 1) * u x
          + m x * ((DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x)))
        ∂(volume : Measure (Fin d → ℝ)))
    +
    (∫ x in UnitCube d,
        (ε * vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
            (fun i => Du i x)
            * ((fun i => Du i x) ⬝ (fun i => Du i x))
          + ε * absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β) (u x)
              * (u x * u x))
        ∂(volume : Measure (Fin d → ℝ))) = 0 := by
  classical
  set α : ℝ := hcong.α with hαdef
  set β : ℝ := hcong.β with hβdef
  set τ : ℝ := hcong.τ with hτdef
  set γBar : ℝ := α * (β + 1) / β with hγBardef
  have hα : 1 < α := hcong.hα
  have hβ : 0 < β := hcong.hβ
  have hτ_nn : 0 ≤ τ := hcong.hτ.1
  have hτ_le : τ ≤ 1 := hcong.hτ.2
  have hαpos : 0 < α := lt_trans one_pos hα
  have hC_pos : 0 < hcong.C := hcong.hC
  have hγ : 1 < γBar := by
    rw [hγBardef]
    exact StationaryMFG.Hamiltonian.one_lt_gammaBar α β hα hβ
  have hγpos : 0 < γBar := lt_trans one_pos hγ
  have hγm1_pos : 0 < γBar - 1 := by linarith
  haveI hfin : IsFiniteMeasure
      (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  -- The dual exponent `γ̄' = γ̄/(γ̄−1)`.
  set γBar' : ℝ := γBar / (γBar - 1) with hγBar'def
  have hpq : γBar.HolderConjugate γBar' := by
    rw [hγBardef, hγBar'def, hγBardef]
    exact Theorems.SimplePower.SimplePowerExponentFacts.paper_holderConjugate_gammaBar
      hα hβ
  have hγBar'_pos : 0 < γBar' := hpq.symm.pos
  -- `Lᵖ` memberships of the witness data at `γ̄`.
  have hu_gamma : MemLpPer (d := d) (ENNReal.ofReal γBar) u := by
    rw [hγBardef]; exact hu_memGamma
  have hDu_gamma : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBar) (Du i) := by
    intro i; rw [hγBardef]; exact hDu_mem i
  -- AE-measurability shortcuts.
  have hm_aem : AEMeasurable m (volume.restrict (UnitCube d)) :=
    aestronglyMeasurable_iff_aemeasurable.mp hm_mem.aestronglyMeasurable
  have hu_aem : AEMeasurable u (volume.restrict (UnitCube d)) :=
    aestronglyMeasurable_iff_aemeasurable.mp hu_gamma.aestronglyMeasurable
  have hDu_aem : ∀ i, AEMeasurable (Du i) (volume.restrict (UnitCube d)) :=
    fun i => aestronglyMeasurable_iff_aemeasurable.mp (hDu_gamma i).aestronglyMeasurable
  -- ============================================================
  -- The linear coefficients `A`, `B i`.
  -- ============================================================
  set A : (Fin d → ℝ) → ℝ :=
    fun x => (m x - 1) + ε * absPowMinusTwo γBar (u x) * u x with hAdef
  set B : Fin d → ((Fin d → ℝ) → ℝ) :=
    fun i x => J x (fun j => Du j x) (m x) i
      + ε * vecAbsPowMinusTwo γBar (fun j => Du j x) * Du i x with hBdef
  -- `m − 1 ∈ L^{γ̄'}` via the finite-measure inclusion `L^{β̄} ↪ L^{γ̄'}`.
  have hγBar'_le_βbar : ENNReal.ofReal γBar' ≤ ENNReal.ofReal (β + 1) := by
    apply ENNReal.ofReal_le_ofReal
    rw [hγBar'def, hγBardef]
    exact Hamiltonian.gammaBar'_le_betaBar hα hβ
  have hm_γ' : MemLpPer (d := d) (ENNReal.ofReal γBar') m :=
    MemLpPer.mono_exponent_finite hγBar'_le_βbar ENNReal.ofReal_ne_top hm_mem
  have hmsub1_γ' : MemLpPer (d := d) (ENNReal.ofReal γBar')
      (fun x => m x - 1) := by
    have := hm_γ'.add (MemLpPer.const (d := d)
      (p := ENNReal.ofReal γBar') (-1 : ℝ))
    have heq : (m + fun _ : Fin d → ℝ => (-1 : ℝ)) = (fun x => m x - 1) := by
      funext x; simp [sub_eq_add_neg]
    rwa [heq] at this
  -- `|u|^{γ̄−1} ∈ L^{γ̄'}` (rpow-closure, `γ̄'·(γ̄−1)=γ̄`).
  have hclose : ENNReal.ofReal γBar' * ENNReal.ofReal (γBar - 1)
      = ENNReal.ofReal γBar := by
    rw [← ENNReal.ofReal_mul hγBar'_pos.le]
    congr 1
    rw [hγBar'def]; field_simp
  have hu_pow : MemLpPer (d := d) (ENNReal.ofReal γBar')
      (fun x => |u x| ^ (γBar - 1)) := by
    have h := Periodic.MemLpPer.rpow_closure (d := d)
      (s := ENNReal.ofReal γBar') (r := γBar - 1) hγm1_pos
      (f := u) (by rw [hclose]; exact hu_gamma)
    have heq : (fun x => ‖u x‖ ^ (γBar - 1)) = (fun x => |u x| ^ (γBar - 1)) := by
      funext x; rw [Real.norm_eq_abs]
    rwa [heq] at h
  -- The ε-scalar term `ε·|u|^{γ̄−2}·u ∈ L^{γ̄'}` (dominated by `|ε|·|u|^{γ̄−1}`).
  have heps_scal_meas : AEStronglyMeasurable
      (fun x => ε * absPowMinusTwo γBar (u x) * u x)
      (volume.restrict (UnitCube d)) := by
    have habs : AEMeasurable (fun x => absPowMinusTwo γBar (u x))
        (volume.restrict (UnitCube d)) := by
      unfold absPowMinusTwo
      exact (hu_aem.abs.pow_const (γBar - 2))
    exact (((aemeasurable_const.mul habs).mul hu_aem)).aestronglyMeasurable
  have heps_scal_γ' : MemLpPer (d := d) (ENNReal.ofReal γBar')
      (fun x => ε * absPowMinusTwo γBar (u x) * u x) := by
    have hdom : MemLpPer (d := d) (ENNReal.ofReal γBar')
        (fun x => |ε| * |u x| ^ (γBar - 1)) := by
      have h := hu_pow.const_smul (𝕜 := ℝ) |ε|
      have heq : (|ε| • fun x => |u x| ^ (γBar - 1))
          = (fun x => |ε| * |u x| ^ (γBar - 1)) := by
        funext x; simp [Pi.smul_apply, smul_eq_mul]
      rwa [heq] at h
    apply MemLp.toMemLpPer
    refine MemLp.of_le_mul (c := 1) hdom.toMemLp heps_scal_meas
      (Filter.Eventually.of_forall (fun x => ?_))
    have hrhs_nn : 0 ≤ |ε| * |u x| ^ (γBar - 1) :=
      mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (abs_nonneg _) _)
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg hrhs_nn, one_mul]
    rw [show ε * absPowMinusTwo γBar (u x) * u x
        = ε * (absPowMinusTwo γBar (u x) * u x) by ring, abs_mul,
      Theorems.SimplePower.abs_absPowMinusTwo_mul_self hγ]
  have hA_γ' : MemLpPer (d := d) (ENNReal.ofReal γBar') A := by
    have := hmsub1_γ'.add heps_scal_γ'
    have heq : ((fun x => m x - 1)
          + fun x => ε * absPowMinusTwo γBar (u x) * u x) = A := by
      funext x; rw [hAdef, Pi.add_apply]
    rwa [heq] at this
  -- The J-flux dominator membership at the untruncated density.
  have hflux_dom : MemLpPer (d := d) (ENNReal.ofReal γBar')
      (fun x => hcong.C * (1 + m x ^ (1 - τ))
            * ‖fun j => Du j x‖ ^ (α * (1 + τ / β) - 1)
          + hcong.C * (m x ^ (β + 1 - β / α) + 1)) := by
    have h := congestion_flux_dominator_memLp_gammaBar'_le (d := d)
      (α := α) (β := β) (τ := τ) (K := hcong.C)
      hα hβ hτ_nn hτ_le (m := m) (Du := Du) hm_mem hm_nn
      (fun i => by rw [hαdef, hβdef]; exact hDu_mem i)
    have hexp : ENNReal.ofReal (α * (β + 1) / β / (α * (β + 1) / β - 1))
        = ENNReal.ofReal γBar' := by
      congr 1
    rwa [hexp] at h
  -- For each `i`, `J(x,Du,m)ᵢ = m·D_pH(x,Du,m)ᵢ` a.e.
  have hJ_eq_mDpH : ∀ i,
      (fun x => J x (fun j => Du j x) (m x) i)
        =ᵐ[volume.restrict (UnitCube d)]
      (fun x => m x * DpH x (fun j => Du j x) (m x) i) := by
    intro i
    filter_upwards [hm_nn, hJat0] with x hx_nn hx_zero
    rcases eq_or_lt_of_le hx_nn with hx0 | hxpos
    · have hm0 : m x = 0 := hx0.symm
      rw [hm0] at hx_zero ⊢
      rw [hx_zero (rfl), zero_mul, Pi.zero_apply]
    · have := hcong.mDpHat0.J_of_pos x (fun j => Du j x) (m x) hxpos
      rw [this, Pi.smul_apply, smul_eq_mul]
  -- J-flux ∈ L^{γ̄'} via the `m·D_pH` envelope.
  have hJflux_γ' : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBar')
      (fun x => J x (fun j => Du j x) (m x) i) := by
    intro i
    have hmDpH_meas : AEStronglyMeasurable
        (fun x => m x * DpH x (fun j => Du j x) (m x) i)
        (volume.restrict (UnitCube d)) := by
      have hDu' : AEMeasurable (fun x => (fun j => Du j x))
          (volume.restrict (UnitCube d)) := by
        rw [aemeasurable_pi_iff]; intro j; exact hDu_aem j
      have hprod : AEMeasurable
          (fun x : Fin d → ℝ => (x, (fun j => Du j x), m x))
          (volume.restrict (UnitCube d)) :=
        aemeasurable_id.prodMk (hDu'.prodMk hm_aem)
      have hvec : AEMeasurable (fun x => DpH x (fun j => Du j x) (m x))
          (volume.restrict (UnitCube d)) :=
        hcong.measurable_DpH.comp_aemeasurable hprod
      exact (hm_aem.mul
        ((measurable_pi_apply i).comp_aemeasurable hvec)).aestronglyMeasurable
    have hbound : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖m x * DpH x (fun j => Du j x) (m x) i‖
          ≤ hcong.C * (1 + m x ^ (1 - τ))
                * ‖fun j => Du j x‖ ^ (α * (1 + τ / β) - 1)
              + hcong.C * (m x ^ (β + 1 - β / α) + 1) := by
      filter_upwards [hcong.DpH_upper, hm_nn] with x hx hx_nn
      set px : Fin d → ℝ := fun j => Du j x with hpx
      rcases eq_or_lt_of_le hx_nn with hx0 | hxpos
      · have hm0 : m x = 0 := hx0.symm
        rw [hm0, zero_mul, norm_zero]
        have h1 : 0 ≤ hcong.C * (1 + (0:ℝ) ^ (1 - τ))
            * ‖fun j => Du j x‖ ^ (α * (1 + τ / β) - 1) := by positivity
        have h2 : 0 ≤ hcong.C * ((0:ℝ) ^ (β + 1 - β / α) + 1) := by positivity
        linarith
      · have hDpH_le := hx px (m x) hxpos
        have hcomp_le : |m x * DpH x px (m x) i| ≤ m x * ‖DpH x px (m x)‖ := by
          rw [abs_mul, abs_of_pos hxpos]
          apply mul_le_mul_of_nonneg_left _ hxpos.le
          have := norm_le_pi_norm (DpH x px (m x)) i
          simpa [Real.norm_eq_abs] using this
        have hmul : m x * ‖DpH x px (m x)‖
            ≤ hcong.C * (1 + m x ^ (1 - τ)) * ‖px‖ ^ (α * (1 + τ / β) - 1)
              + hcong.C * (m x ^ (β + 1 - β / α) + 1) := by
          have hstep := mul_le_mul_of_nonneg_left hDpH_le hxpos.le
          refine le_trans hstep (le_of_eq ?_)
          have e1 : m x * (1 / m x) = 1 := by field_simp
          have e2 : m x * (1 / m x ^ τ) = m x ^ (1 - τ) := by
            rw [mul_one_div, Real.rpow_sub hxpos, Real.rpow_one]
          have e3 : m x * m x ^ (β - β / α) = m x ^ (β + 1 - β / α) := by
            rw [show β + 1 - β / α = 1 + (β - β / α) by ring, Real.rpow_add hxpos,
              Real.rpow_one]
          calc m x * (hcong.C * (1 / m x + 1 / m x ^ τ) * ‖px‖ ^ (α*(1+τ/β)-1)
                  + hcong.C * (m x ^ (β - β/α) + 1 / m x))
              = hcong.C * (m x * (1/m x) + m x * (1/m x^τ))
                    * ‖px‖ ^ (α*(1+τ/β)-1)
                + hcong.C * (m x * m x ^ (β - β/α) + m x * (1/m x)) := by ring
            _ = hcong.C * (1 + m x ^ (1-τ)) * ‖px‖ ^ (α*(1+τ/β)-1)
                + hcong.C * (m x ^ (β+1-β/α) + 1) := by rw [e1, e2, e3]
        rw [Real.norm_eq_abs]; exact le_trans hcomp_le hmul
    have hmDpH_γ' : MemLpPer (d := d) (ENNReal.ofReal γBar')
        (fun x => m x * DpH x (fun j => Du j x) (m x) i) := by
      apply MemLp.toMemLpPer
      refine MemLp.of_le_mul (c := 1) hflux_dom.toMemLp hmDpH_meas ?_
      filter_upwards [hbound] with x hx
      have hdom_nn : 0 ≤ hcong.C * (1 + m x ^ (1 - τ))
              * ‖fun j => Du j x‖ ^ (α * (1 + τ / β) - 1)
            + hcong.C * (m x ^ (β + 1 - β / α) + 1) :=
        le_trans (norm_nonneg _) hx
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg hdom_nn, one_mul]
      rw [Real.norm_eq_abs] at hx
      exact hx
    -- Transfer back to J via the a.e. equality `J = m·D_pH`.
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq (hJ_eq_mDpH i).symm hmDpH_γ'.toMemLp)
  -- The ε-vector term `ε·|Du|^{γ̄−2}·Duᵢ ∈ L^{γ̄'}`.
  -- The Euclidean weight `(Du⬝Du)^{(γ̄−1)/2} ∈ L^{γ̄'}`, via the bound
  -- `(∑ Du_i²)^{(γ̄−1)/2} ≤ (∑ |Du_i|)^{γ̄−1}` and rpow-closure of `∑|Du_i| ∈ L^{γ̄}`.
  -- Adapted from the `hG_grad` block of `iota_FB_uniform_dominator`.
  have hDu_dot_pow : MemLpPer (d := d) (ENNReal.ofReal γBar')
      (fun x => ((fun j => Du j x) ⬝ (fun j => Du j x)) ^ ((γBar - 1) / 2)) := by
    -- `S := ∑ i, |Du i| ∈ L^{γ̄}`.
    have hWi : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBar)
        (fun x => |Du i x|) := fun i => MemLp.toMemLpPer (hDu_gamma i).toMemLp.abs
    have hS : MemLpPer (d := d) (ENNReal.ofReal γBar)
        (fun x => ∑ i, |Du i x|) :=
      MemLp.toMemLpPer (MeasureTheory.memLp_finset_sum (Finset.univ : Finset (Fin d))
        (f := fun i x => |Du i x|) (fun i _ => (hWi i).toMemLp) :
        MemLp _ _ _)
    -- `(∑ |Du i|)^{γ̄−1} ∈ L^{γ̄'}` by rpow-closure.
    have hSpow : MemLpPer (d := d) (ENNReal.ofReal γBar')
        (fun x => ‖∑ i, |Du i x|‖ ^ (γBar - 1)) :=
      Periodic.MemLpPer.rpow_closure (d := d) (s := ENNReal.ofReal γBar')
        (r := γBar - 1) hγm1_pos
        (f := fun x => ∑ i, |Du i x|) (by rw [hclose]; exact hS)
    -- Measurability of the Euclidean weight.
    have hmeas : AEStronglyMeasurable
        (fun x => ((fun j => Du j x) ⬝ (fun j => Du j x)) ^ ((γBar - 1) / 2))
        (volume.restrict (UnitCube d)) := by
      have hdot : AEMeasurable
          (fun x => (fun j => Du j x) ⬝ (fun j => Du j x))
          (volume.restrict (UnitCube d)) := by
        have h := Finset.aemeasurable_sum (Finset.univ : Finset (Fin d))
          (fun j (_ : j ∈ Finset.univ) => (hDu_aem j).mul (hDu_aem j))
        have heqfun : (∑ j, fun a => Du j a * Du j a)
            = (fun x => (fun j => Du j x) ⬝ (fun j => Du j x)) := by
          funext x; rw [Finset.sum_apply]; rfl
        simp only [Pi.mul_def] at h
        rwa [heqfun] at h
      exact (hdot.pow_const ((γBar - 1) / 2)).aestronglyMeasurable
    apply MemLp.toMemLpPer
    refine MemLp.of_le_mul (c := 1) hSpow.toMemLp hmeas
      (Filter.Eventually.of_forall (fun x => ?_))
    -- Pointwise: `(∑ Du_i²)^{(γ̄−1)/2} ≤ ‖∑ |Du_i|‖^{γ̄−1}`.
    set a : Fin d → ℝ := fun i => |Du i x| with ha
    have ha_nn : ∀ i, 0 ≤ a i := fun i => abs_nonneg _
    have hdot_eq : (fun j => Du j x) ⬝ (fun j => Du j x) = ∑ i, a i ^ (2 : ℕ) := by
      unfold euclideanDot
      exact Finset.sum_congr rfl (fun i _ => by rw [ha]; rw [sq_abs]; ring)
    have hsumsq_le : (∑ i, a i ^ (2 : ℕ)) ≤ (∑ i, a i) ^ (2 : ℕ) :=
      Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => ha_nn i)
    have hsum_nn : 0 ≤ ∑ i, a i := Finset.sum_nonneg (fun i _ => ha_nn i)
    have hsumsq_nn : 0 ≤ ∑ i, a i ^ (2 : ℕ) :=
      Finset.sum_nonneg (fun i _ => by positivity)
    have hbase : (∑ i, a i ^ (2 : ℕ)) ^ ((γBar - 1) / 2)
        ≤ ((∑ i, a i) ^ (2 : ℕ)) ^ ((γBar - 1) / 2) :=
      Real.rpow_le_rpow hsumsq_nn hsumsq_le (by linarith)
    have hrhs : ((∑ i, a i) ^ (2 : ℕ)) ^ ((γBar - 1) / 2)
        = ‖∑ i, a i‖ ^ (γBar - 1) := by
      rw [Real.norm_eq_abs, abs_of_nonneg hsum_nn,
        ← Real.rpow_natCast (∑ i, a i) 2, ← Real.rpow_mul hsum_nn]
      congr 1; push_cast; ring
    rw [Real.norm_eq_abs (((fun j => Du j x) ⬝ fun j => Du j x) ^ ((γBar - 1) / 2)),
      one_mul, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), hdot_eq]
    calc |(∑ i, a i ^ (2 : ℕ)) ^ ((γBar - 1) / 2)|
        = (∑ i, a i ^ (2 : ℕ)) ^ ((γBar - 1) / 2) :=
          abs_of_nonneg (Real.rpow_nonneg hsumsq_nn _)
      _ ≤ ((∑ i, a i) ^ (2 : ℕ)) ^ ((γBar - 1) / 2) := hbase
      _ = ‖∑ i, a i‖ ^ (γBar - 1) := hrhs
  have heps_vec_γ' : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBar')
      (fun x => ε * vecAbsPowMinusTwo γBar (fun j => Du j x) * Du i x) := by
    intro i
    have hmeas : AEStronglyMeasurable
        (fun x => ε * vecAbsPowMinusTwo γBar (fun j => Du j x) * Du i x)
        (volume.restrict (UnitCube d)) := by
      have hdot : AEMeasurable
          (fun x => (fun j => Du j x) ⬝ (fun j => Du j x))
          (volume.restrict (UnitCube d)) := by
        have h := Finset.aemeasurable_sum (Finset.univ : Finset (Fin d))
          (fun j (_ : j ∈ Finset.univ) => (hDu_aem j).mul (hDu_aem j))
        have heqfun : (∑ j, fun a => Du j a * Du j a)
            = (fun x => (fun j => Du j x) ⬝ (fun j => Du j x)) := by
          funext x; rw [Finset.sum_apply]; rfl
        simp only [Pi.mul_def] at h
        rwa [heqfun] at h
      have hvap : AEMeasurable (fun x => vecAbsPowMinusTwo γBar (fun j => Du j x))
          (volume.restrict (UnitCube d)) := by
        unfold vecAbsPowMinusTwo
        exact hdot.pow_const ((γBar - 2) / 2)
      exact ((aemeasurable_const.mul hvap).mul (hDu_aem i)).aestronglyMeasurable
    have hdom : MemLpPer (d := d) (ENNReal.ofReal γBar')
        (fun x => |ε| * ((fun j => Du j x) ⬝ (fun j => Du j x)) ^ ((γBar - 1) / 2)) := by
      have h := hDu_dot_pow.const_smul (𝕜 := ℝ) |ε|
      have heq : (|ε| • fun x =>
            ((fun j => Du j x) ⬝ (fun j => Du j x)) ^ ((γBar - 1) / 2))
          = (fun x =>
            |ε| * ((fun j => Du j x) ⬝ (fun j => Du j x)) ^ ((γBar - 1) / 2)) := by
        funext x; simp [Pi.smul_apply, smul_eq_mul]
      rwa [heq] at h
    apply MemLp.toMemLpPer
    refine MemLp.of_le_mul (c := 1) hdom.toMemLp hmeas
      (Filter.Eventually.of_forall (fun x => ?_))
    have hrhs_nn : 0 ≤ |ε|
        * ((fun j => Du j x) ⬝ (fun j => Du j x)) ^ ((γBar - 1) / 2) :=
      mul_nonneg (abs_nonneg _) (Real.rpow_nonneg
        (Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)) _)
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg hrhs_nn, one_mul]
    rw [show ε * vecAbsPowMinusTwo γBar (fun j => Du j x) * Du i x
        = ε * (vecAbsPowMinusTwo γBar (fun j => Du j x) * Du i x) by ring, abs_mul]
    exact mul_le_mul_of_nonneg_left
      (Theorems.SimplePower.abs_vecAbsPowMinusTwo_mul_coord_le hγ (fun j => Du j x) i)
      (abs_nonneg _)
  have hB_γ' : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBar') (B i) := by
    intro i
    have := (hJflux_γ' i).add (heps_vec_γ' i)
    have heq : ((fun x => J x (fun j => Du j x) (m x) i)
          + fun x => ε * vecAbsPowMinusTwo γBar (fun j => Du j x) * Du i x)
        = B i := by
      funext x; rw [hBdef, Pi.add_apply]
    rwa [heq] at this
  -- ============================================================
  -- `hsmooth`: regroup `congestion_transport_at_witness` into linear form.
  -- ============================================================
  have hsmooth : ∀ φ : Periodic.SmoothPeriodic d,
      (∫ x in UnitCube d, A x * (φ : (Fin d → ℝ) → ℝ) x
        ∂(volume : Measure (Fin d → ℝ)))
      + ∑ i : Fin d, (∫ x in UnitCube d,
          B i x * (Periodic.SmoothPeriodic.partialDeriv i φ :
            (Fin d → ℝ) → ℝ) x
          ∂(volume : Measure (Fin d → ℝ))) = 0 := by
    intro φ
    set φf : (Fin d → ℝ) → ℝ := (φ : (Fin d → ℝ) → ℝ) with hφfdef
    set Dφf : Fin d → (Fin d → ℝ) → ℝ :=
      fun i => (Periodic.SmoothPeriodic.partialDeriv i φ : (Fin d → ℝ) → ℝ)
      with hDφfdef
    have hφf_gamma : MemLpPer (d := d) (ENNReal.ofReal γBar) φf := by
      rw [hγBardef, hφfdef]
      exact (Periodic.MemSobolevPer.of_smoothPeriodic _ φ).1
    have hDφf_gamma : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBar) (Dφf i) := by
      intro i; rw [hγBardef, hDφfdef]
      exact (Periodic.MemSobolevPer.of_smoothPeriodic _
        (Periodic.SmoothPeriodic.partialDeriv i φ)).1
    have htrans := congestion_transport_at_witness hmon hcong hm_mem hm_nn
      hu_memGamma hDu_mem hQuot_m_mem hVmeas hV hAeq hKeq hVI hw_m hw_u hw_Du
      hcoeWeak_Du φ
    -- Regroup the witness `J⬝∇φ` integral as `Σᵢ ∫ Jᵢ·∂ᵢφ` (and the mass term).
    have hW1 : (∫ x in UnitCube d,
          (m x - 1) * φf x
            + (J x (fun i => Du i x) (m x) ⬝ (fun i => Dφf i x))
          ∂(volume : Measure (Fin d → ℝ)))
        = (∫ x in UnitCube d, (m x - 1) * φf x
              ∂(volume : Measure (Fin d → ℝ)))
          + ∑ i : Fin d, ∫ x in UnitCube d,
              J x (fun j => Du j x) (m x) i * Dφf i x
              ∂(volume : Measure (Fin d → ℝ)) := by
      have hmass_int : IntegrableOn (fun x => (m x - 1) * φf x) (UnitCube d) :=
        MemLpPer.integrable_mul hpq.symm hmsub1_γ' hφf_gamma
      have hcomp_int : ∀ i, IntegrableOn
          (fun x => J x (fun j => Du j x) (m x) i * Dφf i x) (UnitCube d) :=
        fun i => MemLpPer.integrable_mul hpq.symm (hJflux_γ' i) (hDφf_gamma i)
      rw [show (fun x => (m x - 1) * φf x
              + (J x (fun i => Du i x) (m x) ⬝ (fun i => Dφf i x)))
            = (fun x => (m x - 1) * φf x
              + ∑ i, J x (fun j => Du j x) (m x) i * Dφf i x) by
            funext x; rfl]
      rw [MeasureTheory.integral_add hmass_int
        (MeasureTheory.integrable_finset_sum _ (fun i _ => hcomp_int i))]
      congr 1
      exact MeasureTheory.integral_finset_sum _ (fun i _ => hcomp_int i)
    have hW2 : (∫ x in UnitCube d,
          ε * vecAbsPowMinusTwo γBar (fun i => Du i x)
              * ((fun i => Du i x) ⬝ (fun i => Dφf i x))
            + ε * absPowMinusTwo γBar (u x) * (u x * φf x)
          ∂(volume : Measure (Fin d → ℝ)))
        = (∑ i : Fin d, ∫ x in UnitCube d,
              ε * vecAbsPowMinusTwo γBar (fun j => Du j x) * Du i x * Dφf i x
              ∂(volume : Measure (Fin d → ℝ)))
          + ∫ x in UnitCube d,
              ε * absPowMinusTwo γBar (u x) * u x * φf x
              ∂(volume : Measure (Fin d → ℝ)) := by
      have hvec_int : ∀ i, IntegrableOn
          (fun x => ε * vecAbsPowMinusTwo γBar (fun j => Du j x) * Du i x * Dφf i x)
          (UnitCube d) := by
        intro i
        have := MemLpPer.integrable_mul hpq.symm (heps_vec_γ' i) (hDφf_gamma i)
        simpa [mul_assoc] using this
      have hscal_int : IntegrableOn
          (fun x => ε * absPowMinusTwo γBar (u x) * u x * φf x) (UnitCube d) := by
        have := MemLpPer.integrable_mul hpq.symm heps_scal_γ' hφf_gamma
        simpa [mul_assoc] using this
      have hvecdot_eq : (fun x => ε * vecAbsPowMinusTwo γBar (fun i => Du i x)
            * ((fun i => Du i x) ⬝ (fun i => Dφf i x)))
          = (fun x => ∑ i,
              ε * vecAbsPowMinusTwo γBar (fun j => Du j x) * Du i x * Dφf i x) := by
        funext x
        rw [show ε * vecAbsPowMinusTwo γBar (fun i => Du i x)
              * ((fun i => Du i x) ⬝ (fun i => Dφf i x))
            = ε * vecAbsPowMinusTwo γBar (fun i => Du i x)
              * (∑ i, Du i x * Dφf i x) by rfl,
          Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      have hscal_eq : (fun x => ε * absPowMinusTwo γBar (u x) * (u x * φf x))
          = (fun x => ε * absPowMinusTwo γBar (u x) * u x * φf x) := by
        funext x; ring
      rw [show (fun x => ε * vecAbsPowMinusTwo γBar (fun i => Du i x)
                * ((fun i => Du i x) ⬝ (fun i => Dφf i x))
              + ε * absPowMinusTwo γBar (u x) * (u x * φf x))
            = (fun x => (∑ i,
                ε * vecAbsPowMinusTwo γBar (fun j => Du j x) * Du i x * Dφf i x)
              + ε * absPowMinusTwo γBar (u x) * u x * φf x) by
            funext x
            have h1 := congrFun hvecdot_eq x
            have h2 := congrFun hscal_eq x
            simp only at h1 h2
            rw [h1, h2]]
      rw [MeasureTheory.integral_add
        (MeasureTheory.integrable_finset_sum _ (fun i _ => hvec_int i)) hscal_int]
      congr 1
      exact MeasureTheory.integral_finset_sum _ (fun i _ => hvec_int i)
    have hAφ_eq : (∫ x in UnitCube d, A x * φf x
            ∂(volume : Measure (Fin d → ℝ)))
        = (∫ x in UnitCube d, (m x - 1) * φf x
              ∂(volume : Measure (Fin d → ℝ)))
          + ∫ x in UnitCube d, ε * absPowMinusTwo γBar (u x) * u x * φf x
              ∂(volume : Measure (Fin d → ℝ)) := by
      have hmass_int : IntegrableOn (fun x => (m x - 1) * φf x) (UnitCube d) :=
        MemLpPer.integrable_mul hpq.symm hmsub1_γ' hφf_gamma
      have hscal_int : IntegrableOn
          (fun x => ε * absPowMinusTwo γBar (u x) * u x * φf x) (UnitCube d) := by
        have := MemLpPer.integrable_mul hpq.symm heps_scal_γ' hφf_gamma
        simpa [mul_assoc] using this
      rw [show (fun x => A x * φf x)
            = (fun x => (m x - 1) * φf x)
              + (fun x => ε * absPowMinusTwo γBar (u x) * u x * φf x) by
            funext x; rw [Pi.add_apply, hAdef]; ring]
      exact MeasureTheory.integral_add hmass_int hscal_int
    have hBφ_eq : ∀ i, (∫ x in UnitCube d, B i x * Dφf i x
            ∂(volume : Measure (Fin d → ℝ)))
        = (∫ x in UnitCube d, J x (fun j => Du j x) (m x) i * Dφf i x
              ∂(volume : Measure (Fin d → ℝ)))
          + ∫ x in UnitCube d,
              ε * vecAbsPowMinusTwo γBar (fun j => Du j x) * Du i x * Dφf i x
              ∂(volume : Measure (Fin d → ℝ)) := by
      intro i
      have hcomp_int : IntegrableOn
          (fun x => J x (fun j => Du j x) (m x) i * Dφf i x) (UnitCube d) :=
        MemLpPer.integrable_mul hpq.symm (hJflux_γ' i) (hDφf_gamma i)
      have hvec_int : IntegrableOn
          (fun x => ε * vecAbsPowMinusTwo γBar (fun j => Du j x) * Du i x * Dφf i x)
          (UnitCube d) := by
        have := MemLpPer.integrable_mul hpq.symm (heps_vec_γ' i) (hDφf_gamma i)
        simpa [mul_assoc] using this
      rw [show (fun x => B i x * Dφf i x)
            = (fun x => J x (fun j => Du j x) (m x) i * Dφf i x)
              + (fun x => ε * vecAbsPowMinusTwo γBar (fun j => Du j x)
                  * Du i x * Dφf i x) by
            funext x; rw [Pi.add_apply, hBdef]; ring]
      exact MeasureTheory.integral_add hcomp_int hvec_int
    rw [hAφ_eq, Finset.sum_congr rfl (fun i _ => hBφ_eq i), Finset.sum_add_distrib]
    rw [hW1, hW2] at htrans
    set IM : ℝ := ∫ x in UnitCube d, (m x - 1) * φf x
      ∂(volume : Measure (Fin d → ℝ)) with hIM
    set IS : ℝ := ∫ x in UnitCube d, ε * absPowMinusTwo γBar (u x) * u x * φf x
      ∂(volume : Measure (Fin d → ℝ)) with hIS
    set IJ : Fin d → ℝ := fun i => ∫ x in UnitCube d,
      J x (fun j => Du j x) (m x) i * Dφf i x
      ∂(volume : Measure (Fin d → ℝ)) with hIJ
    set IV : Fin d → ℝ := fun i => ∫ x in UnitCube d,
      ε * vecAbsPowMinusTwo γBar (fun j => Du j x) * Du i x * Dφf i x
      ∂(volume : Measure (Fin d → ℝ)) with hIV
    linarith [htrans]
  -- ============================================================
  -- Apply the density passage.
  -- ============================================================
  have hweak : ∀ i, Periodic.HasWeakDerivPer (d := d) i u (Du i) := by
    intro i
    have := hcoeWeak_Du i
    rw [hw_u, hw_Du i] at this
    exact this
  have htransU :=
    transport_linear_at_u_of_smooth_AEPeriodicRep (pReal := γBar) (qReal := γBar')
      hpq (A := A) (B := B) (u := u) (Du := Du)
      hA_γ' hB_γ' hu_gamma hDu_gamma hu_rep hDu_rep hweak hsmooth
  -- ============================================================
  -- Regroup the output and substitute `J⬝Du = m·(D_pH⬝Du)`.
  -- ============================================================
  have hmass_int : IntegrableOn (fun x => (m x - 1) * u x) (UnitCube d) :=
    MemLpPer.integrable_mul hpq.symm hmsub1_γ' hu_gamma
  have hscalU_int : IntegrableOn
      (fun x => ε * absPowMinusTwo γBar (u x) * u x * u x) (UnitCube d) := by
    have := MemLpPer.integrable_mul hpq.symm heps_scal_γ' hu_gamma
    simpa [mul_assoc] using this
  have hJU_int : ∀ i, IntegrableOn
      (fun x => J x (fun j => Du j x) (m x) i * Du i x) (UnitCube d) :=
    fun i => MemLpPer.integrable_mul hpq.symm (hJflux_γ' i) (hDu_gamma i)
  have hvecU_int : ∀ i, IntegrableOn
      (fun x => ε * vecAbsPowMinusTwo γBar (fun j => Du j x) * Du i x * Du i x)
      (UnitCube d) := by
    intro i
    have := MemLpPer.integrable_mul hpq.symm (heps_vec_γ' i) (hDu_gamma i)
    simpa [mul_assoc] using this
  have hAu_eq : (∫ x in UnitCube d, A x * u x ∂(volume : Measure (Fin d → ℝ)))
      = (∫ x in UnitCube d, (m x - 1) * u x ∂(volume : Measure (Fin d → ℝ)))
        + ∫ x in UnitCube d, ε * absPowMinusTwo γBar (u x) * u x * u x
            ∂(volume : Measure (Fin d → ℝ)) := by
    rw [show (fun x => A x * u x)
          = (fun x => (m x - 1) * u x)
            + (fun x => ε * absPowMinusTwo γBar (u x) * u x * u x) by
          funext x; rw [Pi.add_apply, hAdef]; ring]
    exact MeasureTheory.integral_add hmass_int hscalU_int
  have hBDu_eq : ∀ i, (∫ x in UnitCube d, B i x * Du i x
          ∂(volume : Measure (Fin d → ℝ)))
      = (∫ x in UnitCube d, J x (fun j => Du j x) (m x) i * Du i x
            ∂(volume : Measure (Fin d → ℝ)))
        + ∫ x in UnitCube d,
            ε * vecAbsPowMinusTwo γBar (fun j => Du j x) * Du i x * Du i x
            ∂(volume : Measure (Fin d → ℝ)) := by
    intro i
    rw [show (fun x => B i x * Du i x)
          = (fun x => J x (fun j => Du j x) (m x) i * Du i x)
            + (fun x => ε * vecAbsPowMinusTwo γBar (fun j => Du j x)
                * Du i x * Du i x) by
          funext x; rw [Pi.add_apply, hBdef]; ring]
    exact MeasureTheory.integral_add (hJU_int i) (hvecU_int i)
  rw [hAu_eq, Finset.sum_congr rfl (fun i _ => hBDu_eq i),
    Finset.sum_add_distrib] at htransU
  -- `Σᵢ ∫ Jᵢ·Duᵢ = ∫ m·(D_pH⬝Du)`.
  have hJsum_eq : (∑ i : Fin d, ∫ x in UnitCube d,
        J x (fun j => Du j x) (m x) i * Du i x
        ∂(volume : Measure (Fin d → ℝ)))
      = ∫ x in UnitCube d,
          m x * ((DpH x (fun j => Du j x) (m x)) ⬝ (fun j => Du j x))
          ∂(volume : Measure (Fin d → ℝ)) := by
    rw [← MeasureTheory.integral_finset_sum _ (fun i _ => hJU_int i)]
    refine integral_congr_ae ?_
    filter_upwards [hm_nn, hJat0] with x hx_nn hx_zero
    rcases eq_or_lt_of_le hx_nn with hx0 | hxpos
    · have hm0 : m x = 0 := hx0.symm
      rw [hm0] at hx_zero ⊢
      rw [hx_zero rfl, zero_mul]
      simp
    · have hJ := hcong.mDpHat0.J_of_pos x (fun j => Du j x) (m x) hxpos
      rw [Finset.sum_congr rfl
        (fun i _ => by rw [hJ, Pi.smul_apply, smul_eq_mul] :
          ∀ i ∈ (Finset.univ : Finset (Fin d)),
            J x (fun j => Du j x) (m x) i * Du i x
              = m x * DpH x (fun j => Du j x) (m x) i * Du i x)]
      unfold euclideanDot
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
  -- `Σᵢ ∫ ε·vecAbsPow·Duᵢ·Duᵢ = ∫ ε·vecAbsPow·(Du⬝Du)`.
  have hVsum_eq : (∑ i : Fin d, ∫ x in UnitCube d,
        ε * vecAbsPowMinusTwo γBar (fun j => Du j x) * Du i x * Du i x
        ∂(volume : Measure (Fin d → ℝ)))
      = ∫ x in UnitCube d,
          ε * vecAbsPowMinusTwo γBar (fun i => Du i x)
            * ((fun i => Du i x) ⬝ (fun i => Du i x))
          ∂(volume : Measure (Fin d → ℝ)) := by
    rw [← MeasureTheory.integral_finset_sum _ (fun i _ => hvecU_int i)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    change (∑ i, ε * vecAbsPowMinusTwo γBar (fun j => Du j x) * Du i x * Du i x)
      = ε * vecAbsPowMinusTwo γBar (fun i => Du i x)
        * ((fun i => Du i x) ⬝ (fun i => Du i x))
    unfold euclideanDot
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hJsum_eq, hVsum_eq] at htransU
  -- Split the goal's two integrals into the same four scalar integrals; `linarith`.
  have hgoal1 : (∫ x in UnitCube d,
        ((m x - 1) * u x
          + m x * ((DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x)))
        ∂(volume : Measure (Fin d → ℝ)))
      = (∫ x in UnitCube d, (m x - 1) * u x ∂(volume : Measure (Fin d → ℝ)))
        + ∫ x in UnitCube d,
            m x * ((DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))
            ∂(volume : Measure (Fin d → ℝ)) := by
    have hmflux_int : IntegrableOn
        (fun x => m x * ((DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x)))
        (UnitCube d) := by
      have h := MeasureTheory.integrable_finset_sum
        (Finset.univ : Finset (Fin d)) (fun i _ => hJU_int i)
      have heq : (fun x => ∑ i, J x (fun j => Du j x) (m x) i * Du i x)
          =ᵐ[volume.restrict (UnitCube d)]
          (fun x => m x * ((DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))) := by
        filter_upwards [hm_nn, hJat0] with x hx_nn hx_zero
        rcases eq_or_lt_of_le hx_nn with hx0 | hxpos
        · have hm0 : m x = 0 := hx0.symm
          rw [hm0] at hx_zero ⊢
          rw [hx_zero rfl, zero_mul]; simp
        · have hJ := hcong.mDpHat0.J_of_pos x (fun j => Du j x) (m x) hxpos
          rw [Finset.sum_congr rfl
            (fun i _ => by rw [hJ, Pi.smul_apply, smul_eq_mul] :
              ∀ i ∈ (Finset.univ : Finset (Fin d)),
                J x (fun j => Du j x) (m x) i * Du i x
                  = m x * DpH x (fun j => Du j x) (m x) i * Du i x)]
          unfold euclideanDot
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun i _ => by ring)
      exact h.congr heq
    rw [show (fun x => (m x - 1) * u x
            + m x * ((DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x)))
          = (fun x => (m x - 1) * u x)
            + (fun x => m x
                * ((DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x))) by
          funext x; rw [Pi.add_apply]]
    exact MeasureTheory.integral_add hmass_int hmflux_int
  have hgoal2 : (∫ x in UnitCube d,
        (ε * vecAbsPowMinusTwo γBar (fun i => Du i x)
            * ((fun i => Du i x) ⬝ (fun i => Du i x))
          + ε * absPowMinusTwo γBar (u x) * (u x * u x))
        ∂(volume : Measure (Fin d → ℝ)))
      = (∫ x in UnitCube d,
            ε * vecAbsPowMinusTwo γBar (fun i => Du i x)
              * ((fun i => Du i x) ⬝ (fun i => Du i x))
            ∂(volume : Measure (Fin d → ℝ)))
        + ∫ x in UnitCube d, ε * absPowMinusTwo γBar (u x) * u x * u x
            ∂(volume : Measure (Fin d → ℝ)) := by
    have hvflux_int : IntegrableOn
        (fun x => ε * vecAbsPowMinusTwo γBar (fun i => Du i x)
          * ((fun i => Du i x) ⬝ (fun i => Du i x))) (UnitCube d) := by
      have h := MeasureTheory.integrable_finset_sum
        (Finset.univ : Finset (Fin d)) (fun i _ => hvecU_int i)
      have heq : (fun x => ∑ i,
            ε * vecAbsPowMinusTwo γBar (fun j => Du j x) * Du i x * Du i x)
          =ᵐ[volume.restrict (UnitCube d)]
          (fun x => ε * vecAbsPowMinusTwo γBar (fun i => Du i x)
            * ((fun i => Du i x) ⬝ (fun i => Du i x))) := by
        refine Filter.Eventually.of_forall (fun x => ?_)
        change (∑ i, ε * vecAbsPowMinusTwo γBar (fun j => Du j x) * Du i x * Du i x)
          = ε * vecAbsPowMinusTwo γBar (fun i => Du i x)
            * ((fun i => Du i x) ⬝ (fun i => Du i x))
        unfold euclideanDot
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      exact h.congr heq
    rw [show (fun x => ε * vecAbsPowMinusTwo γBar (fun i => Du i x)
              * ((fun i => Du i x) ⬝ (fun i => Du i x))
            + ε * absPowMinusTwo γBar (u x) * (u x * u x))
          = (fun x => ε * vecAbsPowMinusTwo γBar (fun i => Du i x)
              * ((fun i => Du i x) ⬝ (fun i => Du i x)))
            + (fun x => ε * absPowMinusTwo γBar (u x) * u x * u x) by
          funext x; rw [Pi.add_apply]; ring]
    exact MeasureTheory.integral_add hvflux_int hscalU_int
  rw [hgoal1, hgoal2]
  linarith [htransU]

open StationaryMFG.Periodic in
/-- **Witness-level transport identity at `φ = u` — pointwise-periodicity
interface.** Thin wrapper over
`congestion_transport_at_u_witness_AEPeriodicRep`: it accepts the legacy
pointwise `IsPeriodic`/`LocallyIntegrable` data on `u`/`Du i` and feeds the
tautological representatives `AEPeriodicRep.ofPeriodic`. Sites that only hold
the raw `Lp.coeFn` witnesses (where `IsPeriodic` is *not* derivable) should
call the `_AEPeriodicRep` version directly with `bareCoeFnOfLpPer`. -/
theorem congestion_transport_at_u_witness
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) m)
    (hm_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hu_memGamma : MemLpPer (d := d)
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) u)
    (hDu_mem : ∀ i,
      MemLpPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Du i))
    (hQuot_m_mem :
      MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (fun x : Fin d → ℝ =>
          ‖fun i => Du i x‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) /
            (m x ^ hcong.τ + 1)))
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    {ε : ℝ}
    {Aop : congestionXBanach d
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
    (hAeq : Aop = congestionAepsiOpK hmon hcong hVmeas hV ε)
    (hKeq : K = congestionBanachK d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ)
    (hVI : ∀ v ∈ K, 0 ≤ Aop v (v - w))
    (hw_m : (⇑w.1 : (Fin d → ℝ) → ℝ) = m)
    (hw_u : (⇑w.2.1 : (Fin d → ℝ) → ℝ) = u)
    (hw_Du : ∀ i, (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ) = Du i)
    (hcoeWeak_Du : ∀ i,
      Periodic.HasWeakDerivPer (d := d) i
        (⇑w.2.1 : (Fin d → ℝ) → ℝ) (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ))
    (hu_per : IsPeriodic u)
    (hu_loc : MeasureTheory.LocallyIntegrable u (volume : Measure (Fin d → ℝ)))
    (hDu_per : ∀ i, IsPeriodic (Du i))
    (hDu_loc : ∀ i, MeasureTheory.LocallyIntegrable (Du i)
      (volume : Measure (Fin d → ℝ)))
    (hJat0 : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      m x = 0 → J x (fun i => Du i x) 0 = 0) :
    (∫ x in UnitCube d,
        ((m x - 1) * u x
          + m x * ((DpH x (fun i => Du i x) (m x)) ⬝ (fun i => Du i x)))
        ∂(volume : Measure (Fin d → ℝ)))
    +
    (∫ x in UnitCube d,
        (ε * vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
            (fun i => Du i x)
            * ((fun i => Du i x) ⬝ (fun i => Du i x))
          + ε * absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β) (u x)
              * (u x * u x))
        ∂(volume : Measure (Fin d → ℝ))) = 0 := by
  -- `hu_loc`/`hDu_loc` are subsumed by the periodic `MemLpPer` data carried by
  -- the tautological representatives; they remain in the signature only for
  -- backward compatibility of callers.
  have _ := hu_loc
  have _ := hDu_loc
  exact congestion_transport_at_u_witness_AEPeriodicRep
    hmon hcong hm_mem hm_nn hu_memGamma hDu_mem hQuot_m_mem hVmeas hV
    hAeq hKeq hVI hw_m hw_u hw_Du hcoeWeak_Du
    (Periodic.AEPeriodicRep.ofPeriodic hu_per)
    (fun i => Periodic.AEPeriodicRep.ofPeriodic (hDu_per i))
    hJat0

/-- **BB-VIid-5c-E2b-C1 witness `hQuot_m_mem` producer.**

The quotient dominator `‖Du‖^{α(1+τ/β)}/(m^τ+1) ∈ L^{β̄'}_per` at the
Browder–Minty closure witness density `m = ⇑data.weakVI.choose.1` and gradient
`Du i = ⇑(data.weakVI.choose.2.2 i)`, with the **witness density `m`** in the
denominator (NOT the auxiliary truncation `muAux`).

This is produced via the **HJB-interpolation route on `m`** (route 2 of the
task), not the unestablished closedness of the nonlinear ratio conjunct of
`congestionDomainK` (route 1). The witness density `m` itself satisfies the
HJB inequality (paper line 1397, `eq:congest.HJleq0`) and is a.e. non-negative
(E2a, `coeM_nonneg_atWitness_of_closure`), so it plays the role of `μ = muAux`
in the Young/lower-bound envelope of `witness_quotient_dominator_memLp` (with
`k := 0`). The free witness `MemLpPer` bundle
(`coeMemLpPer_witness_bundle_of_closure`) supplies `m ∈ L^{β̄}`, `u, Du ∈ L^{γ̄}`,
and the `V`-membership is the standing input from `hV`.

Two facts are honestly **bridge-threaded** as explicit hypotheses, exactly as
for `coeHJB_le_atWitness` and the standing `muAux` machinery (`h_cont` is an
upstream-threaded fact throughout MuAux/MuIntegrability — it is NOT derivable
from `RegularityH.continuous_H_pm`, which only gives continuity on `Ioi 0`):

* `hHJB` — the bare-coercion HJB inequality at the witness (paper line 1397);
* `h_cont` — on-`Ici 0` continuity of the section `μ₀ ↦ H(x, Du(x), μ₀)`,
  needed to close the `m x = 0` boundary of the lower bound by a limit `ν ↓ 0`.

No `0 < m` / power-growth / `Hext_finite_at_zero` crutch. -/
theorem coeQuot_atWitness_of_closure
    {γBar : ℝ}
    {betaBarPrime : ℝ≥0∞}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {ε : ℝ}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    (data : CongestionRegularizedSolutionData (d := d)
              (γBar := γBar)
              (betaBar := ENNReal.ofReal (hcong.β + 1))
              (betaBarPrime := betaBarPrime)
              (gammaBar := ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
              V H DpH J hcong.α hcong.β hcong.τ ε
              (Periodic.LpPer (ENNReal.ofReal (hcong.β + 1)) d
                × Periodic.SobolevPerLp 1
                    (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) d))
    (hKeq : data.K =
      congestionBanachK d (ENNReal.ofReal (hcong.β + 1)) betaBarPrime
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ)
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (hHJB :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        (data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ) x
          + H x (fun i => (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)
                ((data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x)
          - V x ≤ 0)
    (h_cont :
      ∀ x : Fin d → ℝ,
        ContinuousOn
          (fun μ₀ : ℝ =>
            H x (fun i => (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x) μ₀)
          (Set.Ici 0)) :
    MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
      (fun x : Fin d → ℝ =>
        ‖fun i => (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x‖
            ^ (hcong.α * (1 + hcong.τ / hcong.β))
          / ((data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x ^ hcong.τ + 1)) := by
  -- The free witness `MemLpPer` bundle: `m ∈ L^{β̄}`, `u, Du ∈ L^{γ̄}`.
  obtain ⟨hm_mem, _hu_mem, hDu_mem⟩ :=
    coeMemLpPer_witness_bundle_of_closure (d := d) data
  -- Witness a.e. non-negativity of the density (E2a).
  have hm_nn :
      0 ≤ᵐ[Measure.restrict volume (UnitCube d)]
        (data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) :=
    coeM_nonneg_atWitness_of_closure (d := d) data hKeq
  -- AE-measurability of the witness coercions (from `Lp`-membership).
  have hm_aem :
      AEMeasurable (data.weakVI.choose.1 : (Fin d → ℝ) → ℝ)
        (Measure.restrict volume (UnitCube d)) :=
    aestronglyMeasurable_iff_aemeasurable.mp hm_mem.aestronglyMeasurable
  have hDu_aem :
      ∀ i, AEMeasurable
        (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ)
        (Measure.restrict volume (UnitCube d)) :=
    fun i => aestronglyMeasurable_iff_aemeasurable.mp
      (hDu_mem i).aestronglyMeasurable
  -- The witness gradient lives in `L^{γ̄}` with the unfolded exponent.
  have hDu_mem' :
      ∀ i, MemLpPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) := hDu_mem
  -- The witness value `u ∈ L^{γ̄}`.
  have hu_mem' :
      MemLpPer (d := d)
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ) := by
    -- `L^{γ̄} ↪ L^{γ̄'}` is the wrong inclusion; instead route through the
    -- raw bundle fact `u ∈ L^{γ̄}` and the finite-measure monotonicity to
    -- `L^{(β+1)/β}` (the producer of `witness_quotient_dominator_memLp`
    -- consumes `u ∈ L^{(β+1)/β}`).
    haveI hcube_fin :
        IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
      ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
    have hβ : 0 < hcong.β := hcong.hβ
    have hα : 1 < hcong.α := hcong.hα
    have hle :
        ENNReal.ofReal ((hcong.β + 1) / hcong.β)
          ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β) := by
      apply ENNReal.ofReal_le_ofReal
      rw [mul_div_assoc]
      have hpos : 0 < (hcong.β + 1) / hcong.β :=
        div_pos (by linarith) hβ
      calc (hcong.β + 1) / hcong.β
          = 1 * ((hcong.β + 1) / hcong.β) := by ring
        _ ≤ hcong.α * ((hcong.β + 1) / hcong.β) :=
            mul_le_mul_of_nonneg_right hα.le hpos.le
    exact MemLpPer.mono_exponent_finite hle ENNReal.ofReal_ne_top _hu_mem
  exact witness_quotient_dominator_memLp (d := d) hmon hcong
    hm_aem hDu_aem hm_mem hu_mem' hV hm_nn hHJB h_cont

/-- **`(a:Hat0)` sibling of `coeQuot_atWitness_of_closure`.**

Identical conclusion (`hQuot_m_mem`), with the overstrong on-`Ici 0` continuity
hypothesis `h_cont` replaced by the two `m=0` boundary riders `hHat0`/`hAgree`
(the components of `CongestionRegularizedSequenceBuilderInputs.hH0`). Calls
`witness_quotient_dominator_memLp_hH0`; the rest of the preamble (free witness
`MemLpPer` bundle, witness non-negativity, `Lp`-monotonicity of `u`) is
unchanged. No `0 < m` / power-growth / `Hext_finite_at_zero` crutch. -/
theorem coeQuot_atWitness_of_closure_hH0
    {γBar : ℝ}
    {betaBarPrime : ℝ≥0∞}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {ε : ℝ}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    (data : CongestionRegularizedSolutionData (d := d)
              (γBar := γBar)
              (betaBar := ENNReal.ofReal (hcong.β + 1))
              (betaBarPrime := betaBarPrime)
              (gammaBar := ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
              V H DpH J hcong.α hcong.β hcong.τ ε
              (Periodic.LpPer (ENNReal.ofReal (hcong.β + 1)) d
                × Periodic.SobolevPerLp 1
                    (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) d))
    (hKeq : data.K =
      congestionBanachK d (ENNReal.ofReal (hcong.β + 1)) betaBarPrime
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ)
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (hHJB :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        (data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ) x
          + H x (fun i => (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)
                ((data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x)
          - V x ≤ 0) :
    MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
      (fun x : Fin d → ℝ =>
        ‖fun i => (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x‖
            ^ (hcong.α * (1 + hcong.τ / hcong.β))
          / ((data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x ^ hcong.τ + 1)) := by
  -- The free witness `MemLpPer` bundle: `m ∈ L^{β̄}`, `u, Du ∈ L^{γ̄}`.
  obtain ⟨hm_mem, _hu_mem, hDu_mem⟩ :=
    coeMemLpPer_witness_bundle_of_closure (d := d) data
  -- Witness a.e. non-negativity of the density (E2a).
  have hm_nn :
      0 ≤ᵐ[Measure.restrict volume (UnitCube d)]
        (data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) :=
    coeM_nonneg_atWitness_of_closure (d := d) data hKeq
  -- AE-measurability of the witness coercions (from `Lp`-membership).
  have hm_aem :
      AEMeasurable (data.weakVI.choose.1 : (Fin d → ℝ) → ℝ)
        (Measure.restrict volume (UnitCube d)) :=
    aestronglyMeasurable_iff_aemeasurable.mp hm_mem.aestronglyMeasurable
  have hDu_aem :
      ∀ i, AEMeasurable
        (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ)
        (Measure.restrict volume (UnitCube d)) :=
    fun i => aestronglyMeasurable_iff_aemeasurable.mp
      (hDu_mem i).aestronglyMeasurable
  have hDu_mem' :
      ∀ i, MemLpPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) := hDu_mem
  have hu_mem' :
      MemLpPer (d := d)
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ) := by
    haveI hcube_fin :
        IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
      ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
    have hβ : 0 < hcong.β := hcong.hβ
    have hα : 1 < hcong.α := hcong.hα
    have hle :
        ENNReal.ofReal ((hcong.β + 1) / hcong.β)
          ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β) := by
      apply ENNReal.ofReal_le_ofReal
      rw [mul_div_assoc]
      have hpos : 0 < (hcong.β + 1) / hcong.β :=
        div_pos (by linarith) hβ
      calc (hcong.β + 1) / hcong.β
          = 1 * ((hcong.β + 1) / hcong.β) := by ring
        _ ≤ hcong.α * ((hcong.β + 1) / hcong.β) :=
            mul_le_mul_of_nonneg_right hα.le hpos.le
    exact MemLpPer.mono_exponent_finite hle ENNReal.ofReal_ne_top _hu_mem
  exact witness_quotient_dominator_memLp_hH0 (d := d) hmon hcong hHat0 hAgree
    hm_aem hDu_aem hm_mem hu_mem' hV hm_nn hHJB

/-- **BB-VIid-5c-E2b-E1 witness `hJat0` producer.**

The boundary datum consumed by `congestion_transport_at_u_witness`:
the user's flux extension `J` vanishes on `{m = 0}` at the witness
gradient `Du i = ⇑(data.weakVI.choose.2.2 i)` and witness density
`m = ⇑data.weakVI.choose.1`:

    ∀ᵐ x, m x = 0 → J x (fun i => Du i x) 0 = 0.

This is **NOT** derivable from `data` alone, nor from
`CongestionGrowthCore` (`hcong.mDpHat0` bundles only the
`m → 0⁺` limit + on-`Ici 0` continuity of `m • DpH`, not the
*vanishing* of the user's abstract `J`-extension at `m = 0`; cf.
`WeakIsStrong.pack6_jZeroOracle` ~552–562). The honest source is the
bridge-deferred field `CongestionWeakIsStrongUpstreamPack.hJ_zero_eq`
(`WeakIsStrong` ~273), which states exactly this vanishing at the
weak-limit pair `lim`.

Same honest-bridge pattern as `coeHJB_le_atWitness` (Existence.lean
~3417): the abstract weak-VI conclusion at the chosen witness does not
itself pin the bare-coercion `J`-value, so the bridge hypothesis
`hBridge` — Path A's representation theorem specialised to
`hJ_zero_eq` at the witness pair — is taken as an explicit argument and
forwarded, while `Classical.choose_spec data.weakVI` (both the
closure-membership and the inequality-for-all-test-points parts) is
*materially threaded* into its premises. This keeps the producer
sham-free: it cannot be applied without first supplying the abstract
weak-VI conclusion.

No `0 < m` / power-growth / `Hext_finite_at_zero` crutch. -/
theorem coeJZero_atWitness_of_closure
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
    (hBridge :
      data.weakVI.choose ∈ closure data.K →
      (∀ v ∈ data.K, 0 ≤ data.A v (v - data.weakVI.choose)) →
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        (data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x = 0 →
          J x (fun i => (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x) 0
            = (0 : Fin d → ℝ)) :
    ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
      (data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x = 0 →
        J x (fun i => (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x) 0
          = (0 : Fin d → ℝ) := by
  -- Materially unpack `Classical.choose_spec data.weakVI`:
  -- closure-membership + the abstract VI inequality at the witness.
  obtain ⟨hMem, hVI⟩ := data.weakVI.choose_spec
  exact hBridge hMem hVI

open StationaryMFG.Periodic in
/-- **BB-VIid-5c-E2c witness transport assembly.**

Assemble the transport identity `hTransport` at the Browder–Minty closure
witness `data.weakVI.choose`, in the EXACT shape consumed by
`coeVI_identity_atWitness_of_closure` (Existence.lean) as its `hTransport`
parameter: the first integral is the `m·(D_pH·Du)` flux form, and the second
integral is `gap.coe_epsTerms data.weakVI.choose`.

This instantiates `congestion_transport_at_u_witness_AEPeriodicRep`
(StrongIsStrong) at the native pack (`data.A = congestionAepsiOpK …`,
`data.K = congestionBanachK …` by `rfl`), feeding the just-landed witness
analytic prerequisites:

* `hu_rep` / `hDu_rep` from `Periodic.bareCoeFnOfLpPer` (Periodic/Lp.lean) on
  the value/gradient `Lp` components;
* `hm_nn` from `coeM_nonneg_atWitness_of_closure` (E2a);
* `hQuot_m_mem` from `coeQuot_atWitness_of_closure` (C1), via the threaded
  `hHJB` / `h_cont` analytic facts;
* `hJat0` from `coeJZero_atWitness_of_closure` (E1), via the threaded
  `hJBridge`;
* the `MemLpPer` bundle from `coeMemLpPer_witness_bundle_of_closure` (E2);
* `hcoeWeak_Du` from `coeWeakDeriv_atWitness_of_closure`;
* `hVI` from `data.weakVI.choose_spec.2`.

The conclusion's explicit ε-residual integrand
`ε·vecAbsPowMinusTwo γ̄ (Du) · (Du⬝Du) + ε·absPowMinusTwo γ̄ u · (u·u)` is
reconciled with `gap.coe_epsTerms data.weakVI.choose` — which equals
`coeEpsTermsFn ε γ̄ data.weakVI.choose = ε·(vec… + abs…)` once
`γBarReal := γ̄ = α(β+1)/β` — via the supplied a.e.-equality `hEps_ae`
(`rfl` at the concrete `congestionRegularizedBuilderInputs_gap`) and a
`mul_add` distribution.

No `0 < m` / power-growth / `Hext_finite_at_zero` crutch. -/
theorem coeTransport_atWitness_of_closure
    {γBar : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {ε : ℝ}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    (data : CongestionRegularizedSolutionData (d := d)
              (γBar := γBar)
              (betaBar := ENNReal.ofReal (hcong.β + 1))
              (betaBarPrime := ENNReal.ofReal ((hcong.β + 1) / hcong.β))
              (gammaBar := ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
              V H DpH J hcong.α hcong.β hcong.τ ε
              (Periodic.LpPer (ENNReal.ofReal (hcong.β + 1)) d
                × Periodic.SobolevPerLp 1
                    (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) d))
    (gap : LpProductBareGap (d := d)
              (ENNReal.ofReal (hcong.β + 1))
              (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
              V H DpH ε)
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (hAeq : data.A = congestionAepsiOpK hmon hcong hVmeas hV ε)
    (hKeq : data.K =
      congestionBanachK d (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ)
    (hHJB :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        (data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ) x
          + H x (fun i => (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)
                ((data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x)
          - V x ≤ 0)
    (h_cont :
      ∀ x : Fin d → ℝ,
        ContinuousOn
          (fun μ₀ : ℝ =>
            H x (fun i => (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x) μ₀)
          (Set.Ici 0))
    (hJBridge :
      data.weakVI.choose ∈ closure data.K →
      (∀ v ∈ data.K, 0 ≤ data.A v (v - data.weakVI.choose)) →
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        (data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x = 0 →
          J x (fun i => (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x) 0
            = (0 : Fin d → ℝ))
    (hEps_ae :
      gap.coe_epsTerms data.weakVI.choose
        =ᵐ[Measure.restrict volume (UnitCube d)]
      coeEpsTermsFn (betaBar := ENNReal.ofReal (hcong.β + 1))
        (gammaBar := ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        ε (hcong.α * (hcong.β + 1) / hcong.β) data.weakVI.choose) :
    ∫ x in UnitCube d,
        (((data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x - 1)
            * (data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ) x
          + (data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x
            * ((DpH x (fun i =>
                    (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)
                  ((data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x))
                ⬝ (fun i =>
                    (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)))
        ∂(volume : Measure (Fin d → ℝ))
      + ∫ x in UnitCube d, gap.coe_epsTerms data.weakVI.choose x
          ∂(volume : Measure (Fin d → ℝ)) = 0 := by
  classical
  -- The free witness `MemLpPer` bundle (E2): `m ∈ L^{β̄}`, `u, Du ∈ L^{γ̄}`.
  obtain ⟨hm_mem, hu_mem, hDu_mem⟩ :=
    coeMemLpPer_witness_bundle_of_closure (d := d) data
  -- Witness a.e. non-negativity of the density (E2a).
  have hm_nn :
      0 ≤ᵐ[Measure.restrict volume (UnitCube d)]
        (data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) :=
    coeM_nonneg_atWitness_of_closure (d := d) data hKeq
  -- The quotient dominator membership (C1), via the threaded analytic facts.
  have hQuot_m_mem :
      MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (fun x : Fin d → ℝ =>
          ‖fun i => (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x‖
              ^ (hcong.α * (1 + hcong.τ / hcong.β))
            / ((data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x ^ hcong.τ + 1)) :=
    coeQuot_atWitness_of_closure (d := d) hmon hcong data hKeq hV hHJB h_cont
  -- Weak-derivative pairing of the witness value/gradient (E2b).
  have hcoeWeak_Du :
      ∀ i, Periodic.HasWeakDerivPer (d := d) i
        (data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ)
        (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) :=
    coeWeakDeriv_atWitness_of_closure (d := d) data hKeq
  -- The boundary datum `hJat0` (E1).
  have hJat0 :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        (data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x = 0 →
          J x (fun i => (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x) 0
            = (0 : Fin d → ℝ) :=
    coeJZero_atWitness_of_closure (d := d) data hJBridge
  -- Periodic a.e.-representatives of the value/gradient `Lp` coercions.
  have hu_rep :
      Periodic.AEPeriodicRep (data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ) :=
    Periodic.bareCoeFnOfLpPer (d := d) data.weakVI.choose.2.1
  have hDu_rep :
      ∀ i, Periodic.AEPeriodicRep
        (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) :=
    fun i => Periodic.bareCoeFnOfLpPer (d := d) (data.weakVI.choose.2.2 i)
  -- The abstract weak-VI inequality at the witness.
  have hVI : ∀ v ∈ data.K, 0 ≤ data.A v (v - data.weakVI.choose) :=
    data.weakVI.choose_spec.2
  -- Instantiate the AE-periodic-rep transport producer at the native pack.
  have hraw :
      (∫ x in UnitCube d,
          (((data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x - 1)
              * (data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ) x
            + (data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x
              * ((DpH x (fun i =>
                    (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)
                    ((data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x))
                  ⬝ (fun i =>
                    (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)))
          ∂(volume : Measure (Fin d → ℝ)))
      +
      (∫ x in UnitCube d,
          (ε * vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
              (fun i => (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)
              * ((fun i => (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)
                  ⬝ (fun i => (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x))
            + ε * absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
                ((data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ) x)
                * ((data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ) x
                    * (data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ) x))
          ∂(volume : Measure (Fin d → ℝ))) = 0 :=
    congestion_transport_at_u_witness_AEPeriodicRep
      hmon hcong hm_mem hm_nn hu_mem hDu_mem hQuot_m_mem hVmeas hV
      hAeq hKeq hVI rfl rfl (fun _ => rfl) hcoeWeak_Du hu_rep hDu_rep hJat0
  -- Reconcile the explicit ε-residual integral with `gap.coe_epsTerms`.
  have heps_int_eq :
      (∫ x in UnitCube d, gap.coe_epsTerms data.weakVI.choose x
          ∂(volume : Measure (Fin d → ℝ)))
      =
      (∫ x in UnitCube d,
          (ε * vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
              (fun i => (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)
              * ((fun i => (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)
                  ⬝ (fun i => (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x))
            + ε * absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
                ((data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ) x)
                * ((data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ) x
                    * (data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ) x))
          ∂(volume : Measure (Fin d → ℝ))) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hEps_ae] with x hx
    rw [hx]
    -- `coeEpsTermsFn ε γ̄ w x = ε·(vec… + abs…)`; distribute `ε`.
    unfold coeEpsTermsFn
    ring
  -- Conclude.
  rw [heps_int_eq]
  exact hraw

open StationaryMFG.Periodic in
/-- **`(a:Hat0)` sibling of `coeTransport_atWitness_of_closure`.**

Identical conclusion (the transport integral identity at the witness), with the
overstrong on-`Ici 0` continuity hypothesis `h_cont` replaced by
`hH0 : HypothesisHZeroExtension H` (the bundled `m=0` boundary riders threaded
through `CongestionRegularizedSequenceBuilderInputs.hH0`). The quotient dominator
membership is produced via `coeQuot_atWitness_of_closure_hH0` (feeding
`hH0.hHat0`/`hH0.hAgree`); every other premise is identical. No `0 < m` /
power-growth / `Hext_finite_at_zero` crutch. -/
theorem coeTransport_atWitness_of_closure_hH0
    {γBar : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {ε : ℝ}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    (hH0 : Hamiltonian.HypothesisHZeroExtension (d := d) H)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    (data : CongestionRegularizedSolutionData (d := d)
              (γBar := γBar)
              (betaBar := ENNReal.ofReal (hcong.β + 1))
              (betaBarPrime := ENNReal.ofReal ((hcong.β + 1) / hcong.β))
              (gammaBar := ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
              V H DpH J hcong.α hcong.β hcong.τ ε
              (Periodic.LpPer (ENNReal.ofReal (hcong.β + 1)) d
                × Periodic.SobolevPerLp 1
                    (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) d))
    (gap : LpProductBareGap (d := d)
              (ENNReal.ofReal (hcong.β + 1))
              (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
              V H DpH ε)
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (hAeq : data.A = congestionAepsiOpK hmon hcong hVmeas hV ε)
    (hKeq : data.K =
      congestionBanachK d (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ)
    (hHJB :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        (data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ) x
          + H x (fun i => (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)
                ((data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x)
          - V x ≤ 0)
    (hJBridge :
      data.weakVI.choose ∈ closure data.K →
      (∀ v ∈ data.K, 0 ≤ data.A v (v - data.weakVI.choose)) →
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        (data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x = 0 →
          J x (fun i => (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x) 0
            = (0 : Fin d → ℝ))
    (hEps_ae :
      gap.coe_epsTerms data.weakVI.choose
        =ᵐ[Measure.restrict volume (UnitCube d)]
      coeEpsTermsFn (betaBar := ENNReal.ofReal (hcong.β + 1))
        (gammaBar := ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        ε (hcong.α * (hcong.β + 1) / hcong.β) data.weakVI.choose) :
    ∫ x in UnitCube d,
        (((data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x - 1)
            * (data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ) x
          + (data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x
            * ((DpH x (fun i =>
                    (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)
                  ((data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x))
                ⬝ (fun i =>
                    (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)))
        ∂(volume : Measure (Fin d → ℝ))
      + ∫ x in UnitCube d, gap.coe_epsTerms data.weakVI.choose x
          ∂(volume : Measure (Fin d → ℝ)) = 0 := by
  classical
  -- The free witness `MemLpPer` bundle (E2): `m ∈ L^{β̄}`, `u, Du ∈ L^{γ̄}`.
  obtain ⟨hm_mem, hu_mem, hDu_mem⟩ :=
    coeMemLpPer_witness_bundle_of_closure (d := d) data
  -- Witness a.e. non-negativity of the density (E2a).
  have hm_nn :
      0 ≤ᵐ[Measure.restrict volume (UnitCube d)]
        (data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) :=
    coeM_nonneg_atWitness_of_closure (d := d) data hKeq
  -- The quotient dominator membership (C1), via the `(a:Hat0)` route.
  have hQuot_m_mem :
      MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (fun x : Fin d → ℝ =>
          ‖fun i => (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x‖
              ^ (hcong.α * (1 + hcong.τ / hcong.β))
            / ((data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x ^ hcong.τ + 1)) :=
    coeQuot_atWitness_of_closure_hH0 (d := d) hmon hcong hH0.hHat0 hH0.hAgree
      data hKeq hV hHJB
  -- Weak-derivative pairing of the witness value/gradient (E2b).
  have hcoeWeak_Du :
      ∀ i, Periodic.HasWeakDerivPer (d := d) i
        (data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ)
        (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) :=
    coeWeakDeriv_atWitness_of_closure (d := d) data hKeq
  -- The boundary datum `hJat0` (E1).
  have hJat0 :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        (data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x = 0 →
          J x (fun i => (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x) 0
            = (0 : Fin d → ℝ) :=
    coeJZero_atWitness_of_closure (d := d) data hJBridge
  -- Periodic a.e.-representatives of the value/gradient `Lp` coercions.
  have hu_rep :
      Periodic.AEPeriodicRep (data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ) :=
    Periodic.bareCoeFnOfLpPer (d := d) data.weakVI.choose.2.1
  have hDu_rep :
      ∀ i, Periodic.AEPeriodicRep
        (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) :=
    fun i => Periodic.bareCoeFnOfLpPer (d := d) (data.weakVI.choose.2.2 i)
  -- The abstract weak-VI inequality at the witness.
  have hVI : ∀ v ∈ data.K, 0 ≤ data.A v (v - data.weakVI.choose) :=
    data.weakVI.choose_spec.2
  -- Instantiate the AE-periodic-rep transport producer at the native pack.
  have hraw :
      (∫ x in UnitCube d,
          (((data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x - 1)
              * (data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ) x
            + (data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x
              * ((DpH x (fun i =>
                    (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)
                    ((data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x))
                  ⬝ (fun i =>
                    (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)))
          ∂(volume : Measure (Fin d → ℝ)))
      +
      (∫ x in UnitCube d,
          (ε * vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
              (fun i => (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)
              * ((fun i => (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)
                  ⬝ (fun i => (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x))
            + ε * absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
                ((data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ) x)
                * ((data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ) x
                    * (data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ) x))
          ∂(volume : Measure (Fin d → ℝ))) = 0 :=
    congestion_transport_at_u_witness_AEPeriodicRep
      hmon hcong hm_mem hm_nn hu_mem hDu_mem hQuot_m_mem hVmeas hV
      hAeq hKeq hVI rfl rfl (fun _ => rfl) hcoeWeak_Du hu_rep hDu_rep hJat0
  -- Reconcile the explicit ε-residual integral with `gap.coe_epsTerms`.
  have heps_int_eq :
      (∫ x in UnitCube d, gap.coe_epsTerms data.weakVI.choose x
          ∂(volume : Measure (Fin d → ℝ)))
      =
      (∫ x in UnitCube d,
          (ε * vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
              (fun i => (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)
              * ((fun i => (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)
                  ⬝ (fun i => (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x))
            + ε * absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
                ((data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ) x)
                * ((data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ) x
                    * (data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ) x))
          ∂(volume : Measure (Fin d → ℝ))) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hEps_ae] with x hx
    rw [hx]
    unfold coeEpsTermsFn
    ring
  rw [heps_int_eq]
  exact hraw

open StationaryMFG.Periodic in
/-- **BB-VIid-5c-E2d — fully-assembled `coeVI_identity` at the closure witness.**

This is the no-analytic-premise wrapper of `coeVI_identity_atWitness_of_closure`
(Existence.lean): the paper `eq:identity-congestion` integral identity at the
Browder–Minty closure witness `data.weakVI.choose`, produced entirely from
internal producers. There are NO standalone integrability or transport/HJ0
hypotheses left in the signature — only the same closure/bridge analytic facts
already consumed by `coeTransport_atWitness_of_closure_hH0` (its `hHJB`, the
`m=0` boundary bundle `hH0`, `hJBridge`, `hEps_ae`) plus the extra `h_perk`
lower-bound consumed by D2's
`congestion_HJ0_mass_atWitness_of_closure`.

Internally:

* the witness `MemLpPer` bundle (`coeMemLpPer_witness_bundle_of_closure`, E2):
  `m ∈ L^{β̄}`, `u, Du ∈ L^{γ̄}`;
* `hm_nn` (`coeM_nonneg_atWitness_of_closure`, E2a, via `hKeq`);
* the three "easy" certs (`congestion_VIid_easy_int_certs`): `hu_int`,
  `hmu_int`, `hVm_int`;
* the flux cert (`congestion_VIid_mFlux_int`): `hmFlux_int`;
* the `m·H` cert (`congestion_VIid_mH_int`): `hmH_int`;
* the gap's `coe_epsTerms` cert (`congestionRegularizedBuilderInputs_hEpsTerms_int`
  at the concrete `coeEpsTermsFn`, transferred to the supplied `gap` along
  `hEps_ae`): `heps_int`;
* `hTransport` (`coeTransport_atWitness_of_closure`, E2c);
* `hHJ0` (`congestion_HJ0_mass_atWitness_of_closure`, D2).

These are fed to `coeVI_identity_atWitness_of_closure` (child C). No
`0 < m` / power-growth / `Hext_finite_at_zero` crutch. -/
theorem coeVI_identity_atWitness_of_closure_full
    {γBar : ℝ}
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {ε : ℝ}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    (hH0 : Hamiltonian.HypothesisHZeroExtension (d := d) H)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    (data : CongestionRegularizedSolutionData (d := d)
              (γBar := γBar)
              (betaBar := ENNReal.ofReal (hcong.β + 1))
              (betaBarPrime := ENNReal.ofReal ((hcong.β + 1) / hcong.β))
              (gammaBar := ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
              V H DpH J hcong.α hcong.β hcong.τ ε
              (Periodic.LpPer (ENNReal.ofReal (hcong.β + 1)) d
                × Periodic.SobolevPerLp 1
                    (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) d))
    (gap : LpProductBareGap (d := d)
              (ENNReal.ofReal (hcong.β + 1))
              (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
              V H DpH ε)
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (hAeq : data.A = congestionAepsiOpK hmon hcong hVmeas hV ε)
    (hKeq : data.K =
      congestionBanachK d (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ)
    (hHJB :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        (data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ) x
          + H x (fun i => (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)
                ((data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x)
          - V x ≤ 0)
    (h_perk :
      ∀ k : ℝ, 0 < k →
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          0 < (data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x →
            -k ≤ (data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ) x
                  + H x (fun i => (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)
                      ((data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x)
                  - V x)
    (hJBridge :
      data.weakVI.choose ∈ closure data.K →
      (∀ v ∈ data.K, 0 ≤ data.A v (v - data.weakVI.choose)) →
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        (data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x = 0 →
          J x (fun i => (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x) 0
            = (0 : Fin d → ℝ))
    (hEps_ae :
      gap.coe_epsTerms data.weakVI.choose
        =ᵐ[Measure.restrict volume (UnitCube d)]
      coeEpsTermsFn (betaBar := ENNReal.ofReal (hcong.β + 1))
        (gammaBar := ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        ε (hcong.α * (hcong.β + 1) / hcong.β) data.weakVI.choose) :
    ∫ x in UnitCube d, (data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ) x
        ∂(volume : Measure (Fin d → ℝ))
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
          ∂(volume : Measure (Fin d → ℝ)) := by
  classical
  -- The witness `MemLpPer` bundle (E2): `m ∈ L^{β̄}`, `u, Du ∈ L^{γ̄}`.
  obtain ⟨hm_mem, hu_mem, hDu_mem⟩ :=
    coeMemLpPer_witness_bundle_of_closure (d := d) data
  -- Witness a.e. non-negativity of the density (E2a).
  have hm_nn :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        0 ≤ (data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x :=
    coeM_nonneg_atWitness_of_closure (d := d) data hKeq
  -- The three "easy" Hölder/inclusion certs (E1).
  obtain ⟨hu_int, hmu_int, hVm_int⟩ :=
    congestion_VIid_easy_int_certs (d := d) hcong.hα hcong.hβ
      hm_mem hu_mem hV
  -- The `m·(D_pH·Du)` flux cert (E1b).
  have hmFlux_int :
      MeasureTheory.Integrable
        (fun x => (data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x
          * ((DpH x (fun i => (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)
                ((data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x))
              ⬝ (fun i => (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)))
        (volume.restrict (UnitCube d)) :=
    congestion_VIid_mFlux_int (d := d) hmon hcong hm_mem hm_nn hDu_mem
  -- The `m·H` cert (E1b).
  have hmH_int :
      MeasureTheory.Integrable
        (fun x => (data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x
          * H x (fun i => (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)
                ((data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x))
        (volume.restrict (UnitCube d)) :=
    congestion_VIid_mH_int (d := d) hmon hcong hm_mem hm_nn hDu_mem
  -- The gap's `coe_epsTerms` cert (E1b): integrability of the concrete
  -- `coeEpsTermsFn`, transferred to the supplied `gap` along `hEps_ae`.
  have heps_int :
      MeasureTheory.Integrable
        (gap.coe_epsTerms data.weakVI.choose)
        (volume.restrict (UnitCube d)) := by
    have hconc :
        MeasureTheory.Integrable
          ((congestionRegularizedBuilderInputs_gap (d := d)
              (betaBar := ENNReal.ofReal (hcong.β + 1))
              (gammaBar := ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
              (V := V) (H := H) (DpH := DpH)
              ε (hcong.α * (hcong.β + 1) / hcong.β)).project_epsTerms
            data.weakVI.choose)
          (volume.restrict (UnitCube d)) :=
      congestionRegularizedBuilderInputs_hEpsTerms_int (d := d)
        (betaBar := ENNReal.ofReal (hcong.β + 1))
        (gammaBar := ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        (V := V) (H := H) (DpH := DpH)
        ε
        (γBarReal := hcong.α * (hcong.β + 1) / hcong.β)
        (StationaryMFG.Hamiltonian.one_lt_gammaBar hcong.α hcong.β
            hcong.hα hcong.hβ).le
        rfl data.weakVI.choose
    -- `project_epsTerms = coeEpsTermsFn` at the concrete gap.
    rw [congestionRegularizedBuilderInputs_gap_project_epsTerms] at hconc
    exact hconc.congr hEps_ae.symm
  -- `hTransport` at the witness (E2c).
  have hTransport :
      ∫ x in UnitCube d,
          (((data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x - 1)
              * (data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ) x
            + (data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x
              * ((DpH x (fun i =>
                      (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)
                    ((data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x))
                  ⬝ (fun i =>
                      (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)))
          ∂(volume : Measure (Fin d → ℝ))
        + ∫ x in UnitCube d, gap.coe_epsTerms data.weakVI.choose x
            ∂(volume : Measure (Fin d → ℝ)) = 0 :=
    coeTransport_atWitness_of_closure_hH0 (d := d) hmon hcong hH0 data gap
      hVmeas hV hAeq hKeq hHJB hJBridge hEps_ae
  -- `hHJ0` mass identity at the witness (D2).
  have hHJ0 :
      ∫ x in UnitCube d,
          (data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x
            * ((data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ) x
                + H x (fun i =>
                      (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)
                      ((data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x)
                - V x)
          ∂(volume : Measure (Fin d → ℝ)) = 0 :=
    congestion_HJ0_mass_atWitness_of_closure (d := d) data hHJB h_perk hm_nn
  -- Assemble via child C.
  exact coeVI_identity_atWitness_of_closure (d := d) data gap
    hu_int hmFlux_int hVm_int heps_int hmH_int hmu_int hTransport hHJ0

end Congestion

end StationaryMFG
