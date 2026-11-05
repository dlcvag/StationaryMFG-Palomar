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


/-- **Odd symmetry of the `ι`-family** under `(φ, t) ↦ (−φ, −t)`.

The `BigInt` integrand depends on the test only through `t·φ` and
`t·∇φ`, both invariant under `(φ, t) ↦ (−φ, −t)`; the prefactor `1/t`
is odd. Hence
`congestionIotaFamily … φ t = − congestionIotaFamily … (−φ) (−t)`. -/
theorem congestionIotaFamily_neg_neg
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (V m u : (Fin d → ℝ) → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (ε γEps δ : ℝ)
    (φ : Periodic.SmoothPeriodic d) (t : ℝ) :
    congestionIotaFamily H DpH V m u Du ε γEps δ φ t
      = - congestionIotaFamily H DpH V m u Du ε γEps δ (-φ) (-t) := by
  -- Under `φ ↦ -φ`, `∂ᵢ(-φ) = -∂ᵢφ` pointwise (linearity of `fderiv`).
  have hpd : ∀ (i : Fin d) (x : Fin d → ℝ),
      (Periodic.SmoothPeriodic.partialDeriv i (-φ) : (Fin d → ℝ) → ℝ) x
        = - (Periodic.SmoothPeriodic.partialDeriv i φ : (Fin d → ℝ) → ℝ) x := by
    intro i x
    simp only [Periodic.SmoothPeriodic.coe_partialDeriv,
      Periodic.SmoothPeriodic.coe_neg]
    rw [fderiv_neg]
    rfl
  -- `(-φ) x = - (φ x)`.
  have hφ : ∀ x, ((-φ : Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ) x
      = - (φ : (Fin d → ℝ) → ℝ) x := by
    intro x; rw [Periodic.SmoothPeriodic.coe_neg]; rfl
  -- The two integrand families coincide pointwise after the substitution
  -- `(φ, t) ↦ (-φ, -t)`: every test occurrence is `t·φ` resp. `t·∂ᵢφ`,
  -- which is even, so the arguments of `H`, `DpH`, the ε-functionals, and
  -- the prefactors `(m_δ - m)`, the dot products, and the `(m_δ-1)·tφ` term
  -- are all invariant.
  unfold congestionIotaFamily
  -- Rewrite the `(-φ, -t)` integrands to the `(φ, t)` integrands.
  have key1 :
      (∫ x in UnitCube d,
        (-(u x + (-t) * ((-φ : Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ) x)
            - H x
                (fun i => Du i x
                  + (-t) * (Periodic.SmoothPeriodic.partialDeriv i (-φ) :
                      (Fin d → ℝ) → ℝ) x)
                (max (m x) δ)
            + V x) * (max (m x) δ - m x)
          + max (m x) δ
              * (DpH x
                  (fun i => Du i x
                    + (-t) * (Periodic.SmoothPeriodic.partialDeriv i (-φ) :
                        (Fin d → ℝ) → ℝ) x)
                  (max (m x) δ)
                ⬝ (fun i => (-t) * (Periodic.SmoothPeriodic.partialDeriv i (-φ) :
                        (Fin d → ℝ) → ℝ) x))
          + (max (m x) δ - 1) * ((-t) * ((-φ : Periodic.SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x)
        ∂(volume : Measure (Fin d → ℝ)))
      =
      (∫ x in UnitCube d,
        (-(u x + t * (φ : (Fin d → ℝ) → ℝ) x)
            - H x
                (fun i => Du i x
                  + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                      (Fin d → ℝ) → ℝ) x)
                (max (m x) δ)
            + V x) * (max (m x) δ - m x)
          + max (m x) δ
              * (DpH x
                  (fun i => Du i x
                    + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                        (Fin d → ℝ) → ℝ) x)
                  (max (m x) δ)
                ⬝ (fun i => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                        (Fin d → ℝ) → ℝ) x))
          + (max (m x) δ - 1) * (t * (φ : (Fin d → ℝ) → ℝ) x)
        ∂(volume : Measure (Fin d → ℝ))) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x
    have e1 : (fun i => Du i x
        + (-t) * (Periodic.SmoothPeriodic.partialDeriv i (-φ) :
            (Fin d → ℝ) → ℝ) x)
        = (fun i => Du i x
          + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
              (Fin d → ℝ) → ℝ) x) := by
      funext i; rw [hpd i x]; ring
    have e2 : (fun i => (-t) * (Periodic.SmoothPeriodic.partialDeriv i (-φ) :
            (Fin d → ℝ) → ℝ) x)
        = (fun i => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
              (Fin d → ℝ) → ℝ) x) := by
      funext i; rw [hpd i x]; ring
    simp only []
    rw [e1, e2, hφ x]
    ring_nf
  have key2 :
      (∫ x in UnitCube d,
            vecAbsPowMinusTwo γEps
                (fun i => Du i x
                  + (-t) * (Periodic.SmoothPeriodic.partialDeriv i (-φ) :
                      (Fin d → ℝ) → ℝ) x)
              * ((fun i => Du i x
                    + (-t) * (Periodic.SmoothPeriodic.partialDeriv i (-φ) :
                        (Fin d → ℝ) → ℝ) x)
                  ⬝ (fun i => (-t) * (Periodic.SmoothPeriodic.partialDeriv i (-φ) :
                        (Fin d → ℝ) → ℝ) x))
            + absPowMinusTwo γEps
                (u x + (-t) * ((-φ : Periodic.SmoothPeriodic d) :
                    (Fin d → ℝ) → ℝ) x)
              * ((u x + (-t) * ((-φ : Periodic.SmoothPeriodic d) :
                    (Fin d → ℝ) → ℝ) x)
                  * ((-t) * ((-φ : Periodic.SmoothPeriodic d) :
                    (Fin d → ℝ) → ℝ) x))
          ∂(volume : Measure (Fin d → ℝ)))
      =
      (∫ x in UnitCube d,
            vecAbsPowMinusTwo γEps
                (fun i => Du i x
                  + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                      (Fin d → ℝ) → ℝ) x)
              * ((fun i => Du i x
                    + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                        (Fin d → ℝ) → ℝ) x)
                  ⬝ (fun i => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                        (Fin d → ℝ) → ℝ) x))
            + absPowMinusTwo γEps
                (u x + t * (φ : (Fin d → ℝ) → ℝ) x)
              * ((u x + t * (φ : (Fin d → ℝ) → ℝ) x)
                  * (t * (φ : (Fin d → ℝ) → ℝ) x))
          ∂(volume : Measure (Fin d → ℝ))) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x
    have e1 : (fun i => Du i x
        + (-t) * (Periodic.SmoothPeriodic.partialDeriv i (-φ) :
            (Fin d → ℝ) → ℝ) x)
        = (fun i => Du i x
          + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
              (Fin d → ℝ) → ℝ) x) := by
      funext i; rw [hpd i x]; ring
    have e2 : (fun i => (-t) * (Periodic.SmoothPeriodic.partialDeriv i (-φ) :
            (Fin d → ℝ) → ℝ) x)
        = (fun i => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
              (Fin d → ℝ) → ℝ) x) := by
      funext i; rw [hpd i x]; ring
    have e3 : u x + (-t) * ((-φ : Periodic.SmoothPeriodic d) :
        (Fin d → ℝ) → ℝ) x = u x + t * (φ : (Fin d → ℝ) → ℝ) x := by
      rw [hφ x]; ring
    have e4 : (-t) * ((-φ : Periodic.SmoothPeriodic d) : (Fin d → ℝ) → ℝ) x
        = t * (φ : (Fin d → ℝ) → ℝ) x := by rw [hφ x]; ring
    simp only []
    rw [e1, e2, e3, e4]
  rw [key1, key2]
  ring

/-- **The `t → 0` first-variation passage at fixed `δ`** (paper
`eq:identity-congestion`, lines 1556–1565; T2 phase6 BB VIid **child-4**).

The `±φ` squeeze: from child-3's first-variation inequality
`h_ineq` — `0 ≤ congestionIotaFamily … ψ s` for every smooth periodic
test direction `ψ` and every `s > 0` — and the DCT limit `h_lim`
(continuity of the `ι`-family in `t` at `t = 0`, with the uniform
`|t| ≤ 1` integrable dominator from `CongestionGrowthCore` and
`m_δ ≥ δ > 0`, bundled as a hypothesis), the limit value `ι0` equals `0`.

The two halves of the squeeze are produced internally:
* `t > 0`: `0 ≤ ι_δ(φ, t)` is `h_ineq φ t` directly;
* `t < 0`: `ι_δ(φ, t) = − ι_δ(−φ, −t) ≤ 0` by the odd symmetry
  `congestionIotaFamily_neg_neg` together with `h_ineq (−φ) (−t)`
  (since `−t > 0`).

The combinatorial squeeze itself is closed by `iota_firstorder_zero`. -/
theorem congestion_iota_tendsto_zero
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {V m u : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {ε γEps δ : ℝ}
    (φ : Periodic.SmoothPeriodic d)
    {ι0 : ℝ}
    (h_ineq : ∀ (ψ : Periodic.SmoothPeriodic d) (s : ℝ), 0 < s →
      0 ≤ congestionIotaFamily H DpH V m u Du ε γEps δ ψ s)
    (h_lim :
      Filter.Tendsto (congestionIotaFamily H DpH V m u Du ε γEps δ φ)
        (nhds (0 : ℝ)) (nhds ι0)) :
    ι0 = 0 := by
  -- `h_pos`: `0 ≤ ι_δ(φ, t)` for `t > 0` (child-3 at `φ`, `t`).
  have h_pos : ∀ t, 0 < t →
      0 ≤ congestionIotaFamily H DpH V m u Du ε γEps δ φ t :=
    fun t ht => h_ineq φ t ht
  -- `h_neg`: `ι_δ(φ, t) ≤ 0` for `t < 0` (odd symmetry + child-3 at `-φ`, `-t`).
  have h_neg : ∀ t, t < 0 →
      congestionIotaFamily H DpH V m u Du ε γEps δ φ t ≤ 0 := by
    intro t ht
    have hneg_t : 0 < -t := by linarith
    have hge : 0 ≤ congestionIotaFamily H DpH V m u Du ε γEps δ (-φ) (-t) :=
      h_ineq (-φ) (-t) hneg_t
    have hsym :
        congestionIotaFamily H DpH V m u Du ε γEps δ φ t
          = - congestionIotaFamily H DpH V m u Du ε γEps δ (-φ) (-t) :=
      congestionIotaFamily_neg_neg H DpH V m u Du ε γEps δ φ t
    rw [hsym]; linarith
  exact iota_firstorder_zero (ι := congestionIotaFamily H DpH V m u Du ε γEps δ φ)
    h_pos h_neg h_lim

/-! ## Step 2 of paper Lemma `lem:weak.is.strong` — HJB equality
`eq:congest.HJ0`

Paper `Source/FGU-monotone_revised.tex`, lines 1397, 1477–1511.

This is the dual of Step 1, formalised in `weak_is_strong_HJB_le` above.
After Step 1 yields `u + H(·, Du, m) - V ≤ 0` a.e., we now establish the
*opposite* inequality on `{m > 0}`:

```
-k ≤ u + H(·, Du, m) - V    a.e. on {m > 0}
```

for every `k > 0`, then send `k → 0⁺`. The argument uses the dual
auxiliary density `μ_re` from `MuRe.lean`, the product inequality
`muRe_inequality` (paper eq.~`eq:mu.redef-minus-m.bound`, line 1493),
and a *contradiction* step (paper line 1511): if
`u + H(·, Du, m) - V < -k` on a positive-measure set, continuity of
`H(x, Du x, ·)` would force `μ_re < m` on that set, contradicting
`μ_re = m` a.e. (the analogue of `μ = m` from Step 1).
-/

/-- **Step 2 per-`k` HJB lower bound on `{m > 0}`.** Given the *post-DCT*
and integrability conclusions of paper line 1507 packaged as hypotheses,
together with the structural facts about `muRe` from `MuRe.lean`,
deduce `-k ≤ u + H(·, Du, m) - V` a.e. on `{x : m x > 0}`.

Concretely (with `μ := muRe k m u V Du H`):

* `hk` — `k > 0` (paper line 1482).
* `hae_cont` (a.e.), `hae_ne` (a.e. non-emptiness of `muReSet`),
  `hae_m_nn` (a.e. `0 ≤ m`).
* `h_cont_all` — pointwise everywhere continuity of `H(x, Du x, ·)`
  (used in the contradiction step on a possibly-zero-measure set; we
  need it everywhere because the contradiction set is described
  pointwise).
* `h_diff_int` — `μ_re - m ∈ L¹_per`.
* `h_DCT` — `∫(u + H(·, Du, μ_re) - V)(μ_re - m) dx ≤ 0` (the analogue
  of `eq:hjb-test-mu.delta` after DCT in `δ → 0`, paper line 1507).

The conclusion `-k ≤ u + H(·, Du, m) - V` on `{m > 0}` (paper line
1511) follows from `μ_re = m` a.e. and the contradiction argument. -/
theorem weak_is_strong_HJB_ge_at_k
    {k : ℝ} (hk : 0 < k)
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    (hae_cont :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hae_ne :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        (muReSet k u V Du H x).Nonempty)
    (hae_HJB0 :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        muReInner k u V Du H x ≤ 0 →
          u x + H x (fun i => Du i x) 0 - V x ≤ -k)
    (h_diff_int :
      Integrable (fun x => muRe k m u V Du H x - m x)
        (volume.restrict (UnitCube d)))
    (h_prod_int :
      Integrable
        (fun x =>
          (u x + H x (fun i => Du i x) (muRe k m u V Du H x) - V x)
            * (muRe k m u V Du H x - m x))
        (volume.restrict (UnitCube d)))
    (h_DCT :
      ∫ x in UnitCube d,
          (u x + H x (fun i => Du i x) (muRe k m u V Du H x) - V x)
            * (muRe k m u V Du H x - m x)
          ∂(volume : Measure (Fin d → ℝ)) ≤ 0) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      0 < m x → -k ≤ u x + H x (fun i => Du i x) (m x) - V x := by
  -- Set μ := muRe k m u V Du H for readability.
  set μ : (Fin d → ℝ) → ℝ := muRe k m u V Du H with hμdef
  -- Step (a): the product inequality (paper eq. `eq:mu.redef-minus-m.bound`).
  have h_prod_ineq :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        0 ≤ (μ x - m x) *
              (k + u x + H x (fun i => Du i x) (μ x) - V x) :=
    muRe_inequality (k := k) (m := m) (u := u) (V := V)
      (Du := Du) (H := H) hae_cont hae_ne hae_HJB0
  -- Step (b): expand: `0 ≤ (μ - m)(k) + (μ - m)(u + H - V)`.
  -- Equivalently: `(u + H - V)(μ - m) ≥ -k(μ - m) = k(m - μ)`.
  have h_prod_rewrite :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        k * (m x - μ x)
          ≤ (u x + H x (fun i => Du i x) (μ x) - V x) * (μ x - m x) := by
    filter_upwards [h_prod_ineq] with x hx
    -- `hx : 0 ≤ (μ - m)(k + u + H - V)`. Expand.
    have h_expand :
        (μ x - m x) * (k + u x + H x (fun i => Du i x) (μ x) - V x)
          = (μ x - m x) * k
              + (μ x - m x) * (u x + H x (fun i => Du i x) (μ x) - V x) := by
      ring
    rw [h_expand] at hx
    -- `0 ≤ (μ - m)k + (μ - m)(u + H - V)`
    -- ⇒ `-(μ - m)k ≤ (μ - m)(u + H - V)`
    -- ⇒ `k(m - μ) ≤ (μ - m)(u + H - V)`
    have h1 : -(μ x - m x) * k ≤ (μ x - m x) *
                (u x + H x (fun i => Du i x) (μ x) - V x) := by linarith
    have h2 : -(μ x - m x) * k = k * (m x - μ x) := by ring
    have h3 : (μ x - m x) * (u x + H x (fun i => Du i x) (μ x) - V x)
                = (u x + H x (fun i => Du i x) (μ x) - V x) * (μ x - m x) := by
      ring
    linarith [h1, h2.symm, h3]
  -- Step (c): integrate `h_prod_rewrite` to get `k ∫(m - μ) ≤ ∫(u + H - V)(μ - m) ≤ 0`.
  -- We use `h_DCT` for the latter.
  have h_int_le :
      ∫ x in UnitCube d, k * (m x - muRe k m u V Du H x)
        ∂(volume : Measure (Fin d → ℝ)) ≤ 0 := by
    have h_le_dct :
        ∫ x in UnitCube d, k * (m x - muRe k m u V Du H x)
          ∂(volume : Measure (Fin d → ℝ))
          ≤ ∫ x in UnitCube d,
              (u x + H x (fun i => Du i x) (muRe k m u V Du H x) - V x)
                * (muRe k m u V Du H x - m x)
              ∂(volume : Measure (Fin d → ℝ)) := by
      -- We need integrability of both sides.
      -- For the LHS: `k * (m - μ_re) = -k * (μ_re - m)`, integrable from `h_diff_int`.
      have h_diff_int' :
          Integrable (fun x => k * (m x - muRe k m u V Du H x))
            (volume.restrict (UnitCube d)) := by
        have : Integrable (fun x => -k * (muRe k m u V Du H x - m x))
            (volume.restrict (UnitCube d)) :=
          h_diff_int.const_mul (-k)
        have heq : (fun x => -k * (muRe k m u V Du H x - m x))
            = (fun x => k * (m x - muRe k m u V Du H x)) := by
          funext x; ring
        rw [heq] at this; exact this
      -- For the RHS: it's the integrand of `h_DCT`. We need integrability.
      -- Actually for `integral_mono_ae` we need both sides integrable. We
      -- only have `h_DCT : ∫(u+H-V)(μ-m) ≤ 0` as a numerical bound. Since
      -- `h_DCT` exists, the integral is well-defined (could be `0` if not
      -- integrable, but `h_DCT` is a hypothesis — we treat it on faith
      -- and argue via integral_mono_ae provided we have integrability).
      -- The cleanest route: use `integral_le_integral_of_nonneg_ae`-style
      -- argument by noting `h_prod_rewrite` says LHS_integrand ≤ RHS_integrand
      -- a.e., and combining with the hypothesised bound on RHS integral.
      -- Concretely: if `f ≤ g` a.e. and both integrable, then `∫ f ≤ ∫ g`.
      -- We have integrability of `f`, and need integrability of `g`. From
      -- `h_prod_rewrite : f ≤ g` a.e. and `f, g - f ≥ 0` integrable... no,
      -- that's not given. We use a different angle: `h_DCT` is given, so
      -- treat it as-is.
      -- Alternative: since `h_DCT` involves the *value* of an integral
      -- (which Mathlib defines as 0 if the integrand is not integrable),
      -- we can apply `MeasureTheory.integral_mono_ae` provided we know
      -- both sides integrable. We assume both integrable as a separate
      -- hypothesis is unnecessary: `(u + H - V)(μ - m) = -k(μ - m) + …`
      -- via `h_prod_rewrite` (≤, not =), so we can't read off integrability
      -- directly. BUT: we have `0 ≤ (μ - m)(k + u + H - V)` a.e. from
      -- `h_prod_ineq`, and `(μ - m)(k + u + H - V) = k(μ - m) + (μ - m)(u + H - V)`,
      -- so `(u + H - V)(μ - m) = (μ - m)(u + H - V) ≥ -k(μ - m) = k(m - μ)`,
      -- which is integrable. The non-negative integrable lower bound is
      -- enough — we use it as a sandwich.
      -- Use `integral_mono_ae` directly: requires `f` integrable, `g`
      -- integrable, and `f ≤ g` a.e. We have `f = k*(m - μ_re)` integrable
      -- and `f ≤ g := (u+H-V)(μ_re-m)` a.e. We add `g`'s integrability as
      -- a *consequence* of `h_DCT` if `h_DCT`'s LHS is well-defined; but
      -- `∫ g ≤ 0` makes sense even if `g` is not integrable (Mathlib
      -- defaults the integral to 0). The cleanest workaround: introduce
      -- the integrability of `g` as an *additional* hypothesis. To avoid
      -- bloating signatures, use `h_DCT`'s structure: we instead prove
      -- the goal via the *non-negative* form and avoid `integral_mono_ae`.
      -- Concretely: define `r x := (μ_re x - m x)*(k + u + H - V)`, which
      -- is `≥ 0` a.e. by `h_prod_ineq`. Suppose `r` is integrable.
      -- Then `∫ r ≥ 0`. Expand: `∫ r = k ∫(μ_re - m) + ∫(μ_re - m)(u+H-V) =
      --     -k ∫(m - μ_re) + ∫(u+H-V)(μ_re - m)`. If both pieces are
      -- integrable, `0 ≤ -k ∫(m - μ_re) + h_DCT_value`, i.e.
      -- `k ∫(m - μ_re) ≤ h_DCT_value ≤ 0`. We need integrability of `r`
      -- and of the second piece. We have integrability of `μ_re - m`, so
      -- `k ∫(μ_re - m)` is well-defined. The second piece's integrability
      -- is what `h_DCT` implicitly relies on — Mathlib's `∫` defaults to
      -- 0 if not integrable, so `h_DCT` carries no information then. We
      -- assume integrability.
      -- For the formalization, we side-step `integral_mono_ae` and instead
      -- write the bound directly. Let's just use `integral_mono_ae`
      -- assuming integrability of the RHS is provided either via an
      -- additional hypothesis or via the structure of `h_DCT` (it is, in
      -- the consumer's chain, derived from `h_DCT`'s underlying DCT).
      -- Apply `integral_mono_ae`: both sides integrable, LHS ≤ RHS a.e.
      exact integral_mono_ae h_diff_int' h_prod_int h_prod_rewrite
    linarith
  -- Step (d): factor `k` out.
  have h_int_diff_le :
      ∫ x in UnitCube d, (m x - muRe k m u V Du H x)
        ∂(volume : Measure (Fin d → ℝ)) ≤ 0 := by
    have h_factor :
        ∫ x in UnitCube d, k * (m x - muRe k m u V Du H x)
          ∂(volume : Measure (Fin d → ℝ))
          = k * ∫ x in UnitCube d, (m x - muRe k m u V Du H x)
              ∂(volume : Measure (Fin d → ℝ)) :=
      integral_const_mul (μ := volume.restrict (UnitCube d)) k _
    rw [h_factor] at h_int_le
    by_contra hpos
    have hpos' : 0 < ∫ x in UnitCube d, (m x - muRe k m u V Du H x)
        ∂(volume : Measure (Fin d → ℝ)) := lt_of_not_ge hpos
    have : 0 < k * ∫ x in UnitCube d, (m x - muRe k m u V Du H x)
            ∂(volume : Measure (Fin d → ℝ)) :=
      mul_pos hk hpos'
    linarith
  -- Step (e): combine `m - μ_re ≥ 0` a.e. (from `muRe_le_m`) and
  -- `∫(m - μ_re) ≤ 0` to get `m = μ_re` a.e.
  have h_diff_nn :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        0 ≤ m x - muRe k m u V Du H x := by
    refine Filter.Eventually.of_forall ?_
    intro x
    have := muRe_le_m k m u V Du H x
    linarith
  have h_diff_int' :
      Integrable (fun x => m x - muRe k m u V Du H x)
        (volume.restrict (UnitCube d)) := by
    have : Integrable (fun x => -(muRe k m u V Du H x - m x))
        (volume.restrict (UnitCube d)) := h_diff_int.neg
    have heq : (fun x => -(muRe k m u V Du H x - m x))
        = (fun x => m x - muRe k m u V Du H x) := by
      funext x; ring
    rw [heq] at this; exact this
  have h_int_eq :
      ∫ x in UnitCube d, (m x - muRe k m u V Du H x)
        ∂(volume : Measure (Fin d → ℝ)) = 0 := by
    have h_int_nn :
        0 ≤ ∫ x in UnitCube d, (m x - muRe k m u V Du H x)
          ∂(volume : Measure (Fin d → ℝ)) :=
      integral_nonneg_of_ae h_diff_nn
    linarith
  have h_mu_eq_m :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        muRe k m u V Du H x = m x := by
    have h_diff_zero :
        (fun x => m x - muRe k m u V Du H x)
          =ᵐ[volume.restrict (UnitCube d)] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae h_diff_nn h_diff_int').mp h_int_eq
    filter_upwards [h_diff_zero] with x hx
    have : m x - muRe k m u V Du H x = 0 := hx
    linarith
  -- Step (f): contradiction. If, on a positive-measure subset of
  -- `{m > 0}`, `u + H(·, Du, m) - V < -k`, then continuity of
  -- `H(x, Du x, ·)` implies `m - ε ∈ muReSet` for small `ε > 0`, so
  -- `muReInner ≤ m - ε < m`, hence `μ_re < m`, contradicting `μ_re = m`.
  -- To stay measure-theoretically clean, we prove the contrapositive
  -- a.e.: on the set where `μ_re = m`, if `m > 0`, then
  -- `u + H(·, Du, m) - V ≥ -k`.
  filter_upwards [h_mu_eq_m, hae_cont] with x hxeq hx_cont h_m_pos
  -- Goal: `-k ≤ u x + H x (Du x) (m x) - V x`.
  -- We have `μ_re x = m x` and `m x > 0`.
  by_contra hlt
  push_neg at hlt
  -- `hlt : u x + H x (Du x) (m x) - V x < -k`.
  -- Continuity of `H(x, Du x, ·)` at the *positive* point `m x` (on `Ioi 0`):
  -- there's a neighborhood of `m x` (inside `Ioi 0`) where the bound is still
  -- `< -k`; pick `μ₀ < m x` close to `m x` with `0 < μ₀` and `f μ₀ < -k`.
  set f : ℝ → ℝ := fun μ₀ => u x + H x (fun i => Du i x) μ₀ - V x with hfdef
  -- `f` is `ContinuousOn (Ioi 0)`, and `m x ∈ Ioi 0` is interior, so
  -- `ContinuousAt f (m x)`.
  have hf_contOn : ContinuousOn f (Set.Ioi (0 : ℝ)) :=
    (continuousOn_const.add hx_cont).sub continuousOn_const
  have hm_mem_Ioi : m x ∈ Set.Ioi (0 : ℝ) := h_m_pos
  have hf_contAt : ContinuousAt f (m x) :=
    (hf_contOn _ hm_mem_Ioi).continuousAt (isOpen_Ioi.mem_nhds hm_mem_Ioi)
  have hf_lt : f (m x) < -k := by simpa [hfdef] using hlt
  -- `{y | f y < -k}` is a neighborhood of `m x`.
  have h_pre_nhds : f ⁻¹' Set.Iio (-k) ∈ nhds (m x) :=
    hf_contAt.preimage_mem_nhds (isOpen_Iio.mem_nhds hf_lt)
  rcases Metric.mem_nhds_iff.mp h_pre_nhds with ⟨δ', hδ'_pos, hball⟩
  -- We need a `μ₀` with `0 < μ₀`, `μ₀ < m x` (for the contradiction with
  -- `μ_re = m`), and `f μ₀ < -k` (so `μ₀ ∈ muReSet`).
  -- Pick `ε := min(δ'/2, m x / 2)`.
  set ε : ℝ := min (δ' / 2) (m x / 2) with hεdef
  have hε_pos : 0 < ε := by
    simp [hεdef]
    refine ⟨?_, ?_⟩
    · linarith
    · linarith
  have hε_lt_δ' : ε < δ' := by
    have h1 : ε ≤ δ' / 2 := min_le_left _ _
    linarith
  have hε_lt_m : ε ≤ m x / 2 := min_le_right _ _
  -- Define μ₀ := m x - ε.
  set μ₀ : ℝ := m x - ε with hμ₀def
  have hμ₀_lt_m : μ₀ < m x := by simp [hμ₀def]; linarith
  have hμ₀_nn : 0 ≤ μ₀ := by simp [hμ₀def]; linarith
  -- μ₀ ∈ ball (m x) δ'.
  have hμ₀_in_ball : μ₀ ∈ Metric.ball (m x) δ' := by
    rw [Metric.mem_ball]
    simp [hμ₀def, Real.dist_eq, abs_sub_comm]
    rw [abs_of_nonneg hε_pos.le]
    exact hε_lt_δ'
  -- f μ₀ < -k.
  have hf_at_μ₀ : f μ₀ < -k := hball hμ₀_in_ball
  -- μ₀ ∈ muReSet k u V Du H x.
  have hμ₀_in_set : μ₀ ∈ muReSet k u V Du H x := by
    refine ⟨hμ₀_nn, ?_⟩
    have : f μ₀ < -k := hf_at_μ₀
    have hf_eq : f μ₀ = u x + H x (fun i => Du i x) μ₀ - V x := rfl
    linarith
  -- Therefore muReInner k u V Du H x ≤ μ₀ < m x.
  have h_inner_le : muReInner k u V Du H x ≤ μ₀ :=
    muReInner_le_of_mem (k := k) (u := u) (V := V) (Du := Du) (H := H)
      (x := x) (a := μ₀) hμ₀_nn hμ₀_in_set.2
  have h_inner_lt_m : muReInner k u V Du H x < m x := by linarith
  -- Hence μ_re x = min(m x, muReInner) = muReInner < m x.
  have h_μre_eq_inner : muRe k m u V Du H x = muReInner k u V Du H x := by
    simp [muRe, min_eq_right h_inner_lt_m.le]
  have h_μre_lt_m : muRe k m u V Du H x < m x := by
    rw [h_μre_eq_inner]; exact h_inner_lt_m
  -- Contradiction: μ_re x < m x but `hxeq : μ_re x = m x`.
  exact absurd hxeq (ne_of_lt h_μre_lt_m)

/-- **Step 2 of paper `lem:weak.is.strong`** (`eq:congest.HJ0`,
paper line 1398).

Apply `weak_is_strong_HJB_ge_at_k` along a sequence `k_n := 1/(n+1) > 0`
and intersect the a.e. statements: for every `n`,
`-1/(n+1) ≤ u + H(·, Du, m) - V` a.e. on `{m > 0}`, hence
`0 ≤ u + H(·, Du, m) - V` a.e. on `{m > 0}`. Combined with Step 1
(`weak_is_strong_HJB_le`), this yields the equality
`u + H(·, Du, m) - V = 0` a.e. on `{m > 0}` (paper `eq:congest.HJ0`).

The per-`k` analytical hypotheses are quantified over `k > 0` to keep
the headline statement uniform (paper line 1482 fixes an arbitrary
`k > 0` for the construction). -/
theorem weak_is_strong_HJB_eq
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    (h_step1 :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_perk :
      ∀ k : ℝ, 0 < k →
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          0 < m x → -k ≤ u x + H x (fun i => Du i x) (m x) - V x) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      0 < m x → u x + H x (fun i => Du i x) (m x) - V x = 0 := by
  -- Build the sequence `k_n := 1/(n+1)`.
  set kSeq : ℕ → ℝ := fun n => (1 : ℝ) / (n + 1) with hkSeqdef
  have hk_pos : ∀ n, 0 < kSeq n := by
    intro n
    have : (0 : ℝ) < (n : ℝ) + 1 := by exact_mod_cast Nat.succ_pos n
    exact div_pos one_pos this
  -- For each n, get the a.e. statement at k_n.
  have h_each : ∀ n, ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      0 < m x → -kSeq n ≤ u x + H x (fun i => Du i x) (m x) - V x :=
    fun n => h_perk (kSeq n) (hk_pos n)
  -- Intersect over n via `ae_all_iff`.
  have h_all : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ n, 0 < m x → -kSeq n ≤ u x + H x (fun i => Du i x) (m x) - V x :=
    ae_all_iff.mpr h_each
  -- Combine with Step 1 and pass to the limit n → ∞.
  filter_upwards [h_all, h_step1] with x hx_lower hx_upper hm_pos
  -- Lower bound: `-kSeq n ≤ u + H - V` for every `n`. Since `kSeq → 0⁺`,
  -- conclude `0 ≤ u + H - V`.
  have hx_lower' : ∀ n, -kSeq n ≤ u x + H x (fun i => Du i x) (m x) - V x :=
    fun n => hx_lower n hm_pos
  have h_lim : Filter.Tendsto (fun n => -kSeq n) Filter.atTop (nhds (0 : ℝ)) := by
    have : Filter.Tendsto kSeq Filter.atTop (nhds (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using this.neg
  have h_const : Filter.Tendsto
      (fun _ : ℕ => u x + H x (fun i => Du i x) (m x) - V x)
      Filter.atTop (nhds (u x + H x (fun i => Du i x) (m x) - V x)) :=
    tendsto_const_nhds
  have h_ge : 0 ≤ u x + H x (fun i => Du i x) (m x) - V x :=
    le_of_tendsto_of_tendsto' h_lim h_const hx_lower'
  -- Combine with Step 1 (≤ 0) to get equality.
  linarith

/-- **`eq:congest.HJ0` mass identity from the pointwise `{m>0}` equality**
(VIid-5c child-D, integral-conversion seam).

Given the a.e. pointwise HJB equality on `{m > 0}` (the conclusion of
`weak_is_strong_HJB_eq`), a.e.-nonnegativity of `m`, and integrability of
the product `m·(u + H(·,Du,m) − V)`, the mass identity
`∫_{[0,1]^d} m·(u + H − V) = 0` (paper `eq:congest.HJ0`, line 1398) holds.

The integrand vanishes a.e.: on `{m x > 0}` the bracket `u + H − V = 0`
(from `hHJeq`), so the product is `0`; on `{m x = 0}` (the complement, a.e.
by `hm_nn`) the prefactor `m x = 0`, so the product is again `0`. Hence the
integrand is `0` a.e., and `MeasureTheory.integral_eq_zero_of_ae` gives the
result. -/
theorem weak_is_strong_HJ0_mass_of_HJeq
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    (hHJeq :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        0 < m x → u x + H x (fun i => Du i x) (m x) - V x = 0)
    (hm_nn :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x) :
    ∫ x in UnitCube d,
        m x * (u x + H x (fun i => Du i x) (m x) - V x)
        ∂(volume : Measure (Fin d → ℝ)) = 0 := by
  -- The integrand is `0` a.e.: split on `m x = 0` vs `0 < m x`.
  have hzero :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        m x * (u x + H x (fun i => Du i x) (m x) - V x) = 0 := by
    filter_upwards [hHJeq, hm_nn] with x hxeq hxnn
    rcases hxnn.lt_or_eq with hpos | hzero
    · -- `0 < m x`: the bracket vanishes.
      rw [hxeq hpos]; ring
    · -- `m x = 0`: the prefactor vanishes.
      rw [← hzero]; ring
  -- Integrate the a.e.-zero integrand.
  exact MeasureTheory.integral_eq_zero_of_ae hzero

/-! ## Step 3 of paper Lemma `lem:weak.is.strong` — headline transport
equation `eq:congest.transport`

Paper `Source/FGU-monotone_revised.tex`, line 1401:

```
∫_{𝕋^d} [(m - 1)φ + m·D_pH(x, Du, m)·Dφ
          + ε|Du|^{γ̄-2}Du·Dφ + ε|u|^{γ̄-2}u φ] dx = 0   for all φ ∈ W^{1,γ̄}(𝕋^d).
```

The proof bundles the four prerequisite combinatorial tasks:

* `infra:P5-mdelta-admissibility` (`mdelta_admissibility`): admissibility
  of the truncated pair `(m_δ, u + φ)` for each smooth `φ` and `δ > 0`.
* `infra:P5-transport-mdelta-limit` (`transport_mdelta_limit_concrete`):
  passing to the limit `δ → 0⁺` in the variational inequality tested
  against `(m_δ, u + φ)`, yielding `eq:transport-test-m.delta` (line 1546).
* `infra:P5-iota-firstorder` (`iota_firstorder_zero_concrete`): the
  first-order variation `ι(t) = 0` (line 1565), equivalent to
  `eq:congest.transport` evaluated at the smooth test `φ`.
* `infra:P5-density-Cinfty-W1gamma`: density of `C^∞(𝕋^d)` in
  `W^{1,γ̄}(𝕋^d)` extends the equation from smooth to Sobolev test
  functions; bundled here as a hypothesis-level extension closure since
  the underlying density argument is generic.

In the orchestrator below, the four prerequisite outputs are bundled as
the per-`φ` hypothesis `h_iota`: for every smooth periodic `φ`, the
integral identity `eq:congest.transport` evaluated at `φ` holds. The
extension to all `φ ∈ W^{1,γ̄}_per` is then provided by an explicit
`extend_to_W1gamma` hypothesis. The result is the integral identity for
all admissible test functions, which is precisely the conclusion of paper
Lemma `lem:weak.is.strong`(c). -/

/-- **Step 3 of paper `lem:weak.is.strong`** — the headline transport
equation `eq:congest.transport` (paper line 1401), in its smooth form.

Bundles the conclusion of `iota_firstorder_zero_concrete` over all smooth
test functions: for every `φ : SmoothPeriodic d` with weak gradient
witness `Dφ`, the integral identity holds. The hypothesis `h_iota` is
the per-`φ` output of `iota_firstorder_zero_concrete` — itself the
conclusion of the chain `mdelta_admissibility → transport_mdelta_limit
→ iota_firstorder_zero`, established for each individual smooth `φ`.

This headline statement matches paper `eq:congest.transport`
(line 1401) restricted to `C^∞(𝕋^d)` test functions. The extension to
`W^{1,γ̄}(𝕋^d)` test functions is the content of
`weak_is_strong_transport_W1gamma` below, via the density input. -/
theorem weak_is_strong_transport_smooth
    {_V : (Fin d → ℝ) → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    {ε γBar : ℝ}
    (h_iota :
      ∀ (φ : SmoothPeriodic d) (Dφ : Fin d → (Fin d → ℝ) → ℝ),
        (∫ x in UnitCube d,
            (m x - 1) * (φ : (Fin d → ℝ) → ℝ) x
              + m x
                * (DpH x (fun i => Du i x) (m x) ⬝ (fun i => Dφ i x))
            ∂(volume : Measure (Fin d → ℝ)))
        +
        (∫ x in UnitCube d,
            ε * vecAbsPowMinusTwo γBar (fun i => Du i x)
              * ((fun i => Du i x) ⬝ (fun i => Dφ i x))
            + ε * absPowMinusTwo γBar (u x) * (u x * (φ : (Fin d → ℝ) → ℝ) x)
            ∂(volume : Measure (Fin d → ℝ))) = 0) :
    ∀ (φ : SmoothPeriodic d) (Dφ : Fin d → (Fin d → ℝ) → ℝ),
      (∫ x in UnitCube d,
          (m x - 1) * (φ : (Fin d → ℝ) → ℝ) x
            + m x
              * (DpH x (fun i => Du i x) (m x) ⬝ (fun i => Dφ i x))
          ∂(volume : Measure (Fin d → ℝ)))
      +
      (∫ x in UnitCube d,
          ε * vecAbsPowMinusTwo γBar (fun i => Du i x)
            * ((fun i => Du i x) ⬝ (fun i => Dφ i x))
          + ε * absPowMinusTwo γBar (u x) * (u x * (φ : (Fin d → ℝ) → ℝ) x)
          ∂(volume : Measure (Fin d → ℝ))) = 0 :=
  h_iota

/-- **Headline `eq:congest.transport` over `W^{1,γ̄}(𝕋^d)` test
functions** (paper line 1401).

Lifts `weak_is_strong_transport_smooth` from `C^∞(𝕋^d)` to
`W^{1,γ̄}(𝕋^d)` via the density `infra:P5-density-Cinfty-W1gamma`,
bundled here as an explicit "extension closure" hypothesis
`h_extend`. Concretely, `h_extend` is the contract: if the bilinear
integral identity holds for every `φ ∈ C^∞(𝕋^d)`, it holds for every
`φ ∈ W^{1,γ̄}_per`. The density argument (paper line 1404, "for all
φ ∈ W^{1,γ̄}(𝕋^d)") supplies this closure once the smooth case is
established.

This is the orchestrator that lands paper `eq:congest.transport` as
formalised in `IsStrongSolution_Transport` (`Solutions/Strong.lean:205`),
with the only outstanding analytical input the per-`φ`
`iota_firstorder_zero_concrete` chain. -/
theorem weak_is_strong_transport
    {V : (Fin d → ℝ) → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    {ε γBar : ℝ}
    {TestPredicate : ((Fin d → ℝ) → ℝ) → (Fin d → (Fin d → ℝ) → ℝ) → Prop}
    (h_iota :
      ∀ (φ : SmoothPeriodic d) (Dφ : Fin d → (Fin d → ℝ) → ℝ),
        (∫ x in UnitCube d,
            (m x - 1) * (φ : (Fin d → ℝ) → ℝ) x
              + m x
                * (DpH x (fun i => Du i x) (m x) ⬝ (fun i => Dφ i x))
            ∂(volume : Measure (Fin d → ℝ)))
        +
        (∫ x in UnitCube d,
            ε * vecAbsPowMinusTwo γBar (fun i => Du i x)
              * ((fun i => Du i x) ⬝ (fun i => Dφ i x))
            + ε * absPowMinusTwo γBar (u x) * (u x * (φ : (Fin d → ℝ) → ℝ) x)
            ∂(volume : Measure (Fin d → ℝ))) = 0)
    (h_extend :
      (∀ (φ : SmoothPeriodic d) (Dφ : Fin d → (Fin d → ℝ) → ℝ),
          (∫ x in UnitCube d,
              (m x - 1) * (φ : (Fin d → ℝ) → ℝ) x
                + m x
                  * (DpH x (fun i => Du i x) (m x) ⬝ (fun i => Dφ i x))
              ∂(volume : Measure (Fin d → ℝ)))
          +
          (∫ x in UnitCube d,
              ε * vecAbsPowMinusTwo γBar (fun i => Du i x)
                * ((fun i => Du i x) ⬝ (fun i => Dφ i x))
              + ε * absPowMinusTwo γBar (u x) * (u x * (φ : (Fin d → ℝ) → ℝ) x)
              ∂(volume : Measure (Fin d → ℝ))) = 0) →
        ∀ (φ : (Fin d → ℝ) → ℝ) (Dφ : Fin d → (Fin d → ℝ) → ℝ),
          TestPredicate φ Dφ →
            (∫ x in UnitCube d,
                (m x - 1) * φ x
                  + m x
                    * (DpH x (fun i => Du i x) (m x) ⬝ (fun i => Dφ i x))
                ∂(volume : Measure (Fin d → ℝ)))
            +
            (∫ x in UnitCube d,
                ε * vecAbsPowMinusTwo γBar (fun i => Du i x)
                  * ((fun i => Du i x) ⬝ (fun i => Dφ i x))
                + ε * absPowMinusTwo γBar (u x) * (u x * φ x)
                ∂(volume : Measure (Fin d → ℝ))) = 0) :
    ∀ (φ : (Fin d → ℝ) → ℝ) (Dφ : Fin d → (Fin d → ℝ) → ℝ),
      TestPredicate φ Dφ →
        (∫ x in UnitCube d,
            (m x - 1) * φ x
              + m x
                * (DpH x (fun i => Du i x) (m x) ⬝ (fun i => Dφ i x))
            ∂(volume : Measure (Fin d → ℝ)))
        +
        (∫ x in UnitCube d,
            ε * vecAbsPowMinusTwo γBar (fun i => Du i x)
              * ((fun i => Du i x) ⬝ (fun i => Dφ i x))
            + ε * absPowMinusTwo γBar (u x) * (u x * φ x)
            ∂(volume : Measure (Fin d → ℝ))) = 0 :=
  h_extend (weak_is_strong_transport_smooth (_V := V) (DpH := DpH)
    (Du := Du) (m := m) (u := u) (ε := ε) (γBar := γBar) h_iota)

/-! ## Headline bundle of paper Lemma `lem:weak.is.strong`

Paper `Source/FGU-monotone_revised.tex`, line 1385, Lemma
`lem:weak.is.strong` (*Strong solution property*). Under the
assumptions of Theorem `thm:main-congestion.growth`, every
`(m, u) ∈ L^{β̄}_per × W^{1,γ̄}_per` solving `eq:weak.epsi.cong`
on `𝓚` at any `ε ≥ 0` enjoys:

* `eq:congest.HJleq0` — `u + H(x, Du, m) - V(x) ≤ 0` a.e.
  (paper line 1397, our `weak_is_strong_HJB_le`),
* `eq:congest.HJ0` — equality a.e. on `{m > 0}`
  (paper line 1398, our `weak_is_strong_HJB_eq`),
* `eq:congest.transport` — the integral identity over
  `W^{1,γ̄}` test functions (paper line 1401, our
  `weak_is_strong_transport`), retaining the
  `ε|Du|^{γ̄-2}Du·Dφ + ε|u|^{γ̄-2}u·φ` regularisation terms
  for general `ε ≥ 0`.

The orchestrator `weak_is_strong` packages these three outputs
(all already-formalised top-level theorems of this module) into
a single statement matching the structure of paper Lemma
`lem:weak.is.strong`. The HJB pair is exposed as
`IsStrongSolution_HJB` from `Solutions/Strong.lean:81`; the
transport identity is exposed as the integral equation in its
`ε`-regularised form, faithful to paper `eq:congest.transport`
across all `ε ≥ 0`.

A specialisation `weak_is_strong_at_zero_eps` lands the
`ε = 0` case directly as the predicate `IsStrongSolution`
(against the canonical flux extension `Hamiltonian.JsimpleExt
DpH`), bridging to `Solutions/Strong.lean:304`.

The hypotheses `h_HJB_le`, `h_HJB_eq`, `h_transport` are the
top-level conclusions of Steps 1–3 (clauses (a)–(c) of the
paper lemma). The intermediate analytical content
(constructions of `μ`, `μ_re`, `m_δ`; DCT discharges;
admissibility witnesses; density extension) is bundled inside
those three hypotheses, consistent with the modular discipline
followed in `WellDefined.lean`, `MuIntegrability.lean`, and the
per-`k` lemmas above.

Note: by the structural remark of `Source/FGU-monotone_revised.tex`,
line 1326 (and our task notes), the present route is the **only**
path to the strong-solution property in the congestion-growth
setting, because `(m_ε, u_ε)` is not guaranteed to lie in `𝓚`
(`essinf m_ε > 0` is not given), so the hemicontinuity upgrade
(`rmk:hemicontinuous-upgrade`) does not apply. -/

/-- **Headline `lem:weak.is.strong` (paper line 1385)** —
bundling of clauses (a)+(b) (HJB inequality / equality on
`{m > 0}`) and (c) (transport identity) of paper Lemma
`lem:weak.is.strong`.

Hypotheses:

* `h_HJB_le` — paper `eq:congest.HJleq0` (line 1397). The
  conclusion of `weak_is_strong_HJB_le`.
* `h_HJB_eq` — paper `eq:congest.HJ0` (line 1398). The
  conclusion of `weak_is_strong_HJB_eq`.
* `h_transport` — paper `eq:congest.transport` (line 1401)
  in its `ε`-regularised form for all admissible test
  functions, as produced by `weak_is_strong_transport`.

Conclusion:

* The HJB clause `IsStrongSolution_HJB V H Du m u`
  (`Solutions/Strong.lean:81`).
* The integral identity of `eq:congest.transport` over the
  same admissible test class (still `ε`-regularised). -/
theorem weak_is_strong
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    {ε γBar : ℝ}
    {TestPredicate : ((Fin d → ℝ) → ℝ) → (Fin d → (Fin d → ℝ) → ℝ) → Prop}
    (h_HJB_le :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_HJB_eq :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        0 < m x → u x + H x (fun i => Du i x) (m x) - V x = 0)
    (h_transport :
      ∀ (φ : (Fin d → ℝ) → ℝ) (Dφ : Fin d → (Fin d → ℝ) → ℝ),
        TestPredicate φ Dφ →
          (∫ x in UnitCube d,
              (m x - 1) * φ x
                + m x
                  * (DpH x (fun i => Du i x) (m x) ⬝ (fun i => Dφ i x))
              ∂(volume : Measure (Fin d → ℝ)))
          +
          (∫ x in UnitCube d,
              ε * ‖fun i => Du i x‖ ^ (γBar - 2)
                * ((fun i => Du i x) ⬝ (fun i => Dφ i x))
              + ε * |u x| ^ (γBar - 2) * u x * φ x
              ∂(volume : Measure (Fin d → ℝ))) = 0) :
    IsStrongSolution_HJB V H Du m u
      ∧
      ∀ (φ : (Fin d → ℝ) → ℝ) (Dφ : Fin d → (Fin d → ℝ) → ℝ),
        TestPredicate φ Dφ →
          (∫ x in UnitCube d,
              (m x - 1) * φ x
                + m x
                  * (DpH x (fun i => Du i x) (m x) ⬝ (fun i => Dφ i x))
              ∂(volume : Measure (Fin d → ℝ)))
          +
          (∫ x in UnitCube d,
              ε * ‖fun i => Du i x‖ ^ (γBar - 2)
                * ((fun i => Du i x) ⬝ (fun i => Dφ i x))
              + ε * |u x| ^ (γBar - 2) * u x * φ x
              ∂(volume : Measure (Fin d → ℝ))) = 0 :=
  ⟨⟨h_HJB_le, h_HJB_eq⟩, h_transport⟩

/-- **Specialisation of `weak_is_strong` at `ε = 0`** — produces
the bundled `IsStrongSolution` predicate (paper `def:strong`,
line 261; `Solutions/Strong.lean:304`) against the paper's flux
extension `J` (paper hypothesis `(a:mDpHat0)`).

At `ε = 0` the regularisation terms in `eq:congest.transport`
vanish, and the integrand reduces to the unregularised form
matching `IsStrongSolution_Transport` directly: the `h_transport`
hypothesis is now stated with the abstract extension `J` (rather
than the simple-power-case canonical extension `Hamiltonian.JsimpleExt`),
so no smul/mul rewriting bridge is required.

Hypotheses extend `weak_is_strong` with:

* `h_flux_int` — the integrability condition on
  `J(·, Du(·), m(·))` (paper line 261, part of the preamble of
  `def:strong`), supplying `IsStrongSolution_Transport.integrable`.
* `h_test` — the contract that every smooth periodic
  `φ : SmoothPeriodic d` (with its `partialDeriv` family as
  the test gradient) lies in the user-supplied admissible
  test class `TestPredicate`. -/
theorem weak_is_strong_at_zero_eps
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    {γBar : ℝ}
    {TestPredicate : ((Fin d → ℝ) → ℝ) → (Fin d → (Fin d → ℝ) → ℝ) → Prop}
    (h_HJB_le :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_HJB_eq :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        0 < m x → u x + H x (fun i => Du i x) (m x) - V x = 0)
    (h_transport :
      ∀ (φ : (Fin d → ℝ) → ℝ) (Dφ : Fin d → (Fin d → ℝ) → ℝ),
        TestPredicate φ Dφ →
          (∫ x in UnitCube d,
              (m x - 1) * φ x
                + J x (fun i => Du i x) (m x) ⬝ (fun i => Dφ i x)
              ∂(volume : Measure (Fin d → ℝ)))
          +
          (∫ x in UnitCube d,
              (0 : ℝ) * ‖fun i => Du i x‖ ^ (γBar - 2)
                * ((fun i => Du i x) ⬝ (fun i => Dφ i x))
              + (0 : ℝ) * |u x| ^ (γBar - 2) * u x * φ x
              ∂(volume : Measure (Fin d → ℝ))) = 0)
    (h_flux_int : mDpH_Integrable (d := d) J Du m)
    (h_test :
      ∀ φ : SmoothPeriodic d,
        TestPredicate (φ : (Fin d → ℝ) → ℝ)
          (fun i => (SmoothPeriodic.partialDeriv i φ : (Fin d → ℝ) → ℝ))) :
    IsStrongSolution V H J Du m u := by
  -- The hypothesis `DpH` is no longer needed in the proof body, but is
  -- retained in the signature for compatibility with consumers and to
  -- record the paper-level dependency.
  let _ := DpH
  refine ⟨⟨h_HJB_le, h_HJB_eq⟩, ?_, ?_⟩
  · exact h_flux_int
  · intro φ
    -- Specialise `h_transport` at `(φ, Dφ)` with
    -- `Dφ i := SmoothPeriodic.partialDeriv i φ`.
    have h_eq :=
      h_transport (φ : (Fin d → ℝ) → ℝ)
        (fun i => (SmoothPeriodic.partialDeriv i φ : (Fin d → ℝ) → ℝ))
        (h_test φ)
    -- The second integral vanishes pointwise (each summand has factor `0`),
    -- so `h_eq` reduces to the first integral being `0` — which already
    -- has the exact shape required by `IsStrongSolution_Transport`.
    have h_zero_int :
        ∫ x in UnitCube d,
          (0 : ℝ) * ‖fun i => Du i x‖ ^ (γBar - 2)
            * ((fun i => Du i x)
                ⬝ (fun i =>
                    (SmoothPeriodic.partialDeriv i φ : (Fin d → ℝ) → ℝ) x))
          + (0 : ℝ) * |u x| ^ (γBar - 2) * u x * (φ : (Fin d → ℝ) → ℝ) x
          ∂(volume : Measure (Fin d → ℝ)) = 0 := by
      simp
    rw [h_zero_int, add_zero] at h_eq
    exact h_eq

/-! ## Step 1 final wiring — bare HJB inequality at the Banach-VI witness
data (`infra-P7-sigfix-T2-phase6-hcoeHJB-le-child2c-final-wiring`)

This is the genuine producer of the bare-function HJB pointwise
inequality

```
u + H(·, Du, m) − V ≤ 0   a.e.
```

(paper `eq:congest.HJleq0`, line 1397) at the concrete weak-VI witness
`w`, with `m = w.1`, `u = w.2.1`, `Du i = w.2.2 i`. It replaces the
honest *bridge hypothesis* form of `coeHJB_le_atWitness`
(Existence.lean) with a real assembly: the per-`k` post-DCT integral
inequality is delivered by the now-self-contained `h_DCT_producer`
(no oracle), the structural `muAux` facts are derived from the standing
congestion hypotheses, and `weak_is_strong_HJB_le_of_perk_DCT` sends
`k → 0⁺` to produce the headline inequality.

The operator-identification facts (`hAeq`, `hKeq`, `hVI`) and the
witness-coercion identities (`hw_m`, `hw_u`, `hw_Du`, `hcoeWeak_Du`)
are threaded structurally exactly as `h_DCT_producer` requires; they
are the concrete realisation of `data.A = congestionAepsiOpK …`,
`data.K = congestionBanachK …`, and the abstract VI conclusion at the
chosen witness. No new proof-oracle is introduced: every premise is
either a paper hypothesis (`hmon`, `hcong`), a measurability/Lp datum
of the witness, or an operator-identity/VI fact dischargeable from the
concrete Banach realisation. -/
theorem weak_is_strong_HJB_le_of_witnessData
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm_meas : Measurable m)
    (hu_meas : Measurable u)
    (hV_meas : Measurable V)
    (hDu_meas : ∀ i, Measurable (Du i))
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) m)
    (hu_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) u)
    (hV_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (hDu_mem : ∀ i,
      MemLpPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Du i))
    (hae_m_nn :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hcont :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        Continuous (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀))
    (h_anti :
      ∀ x : Fin d → ℝ,
        AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ici 0))
    (h_cont :
      ∀ x : Fin d → ℝ,
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ici 0))
    (hne :
      ∀ k : ℝ, 0 < k →
        ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
          (muAuxSet k m u V Du H x).Nonempty)
    (h_ne_all :
      ∀ k : ℝ, 0 < k →
        ∀ x : Fin d → ℝ, (muAuxSet k m u V Du H x).Nonempty)
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
        (⇑w.2.1 : (Fin d → ℝ) → ℝ) (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ)) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      u x + H x (fun i => Du i x) (m x) - V x ≤ 0 := by
  -- Reduce to the per-`k` DCT assembler, supplying each structural field
  -- uniformly in `k > 0`.
  refine weak_is_strong_HJB_le_of_perk_DCT (V := V) (H := H) (Du := Du)
    (m := m) (u := u)
    hcont hae_m_nn (fun k hk => hne k hk) ?_ ?_ ?_ ?_
  · -- `h_mu_ge_m`: `m x ≤ μ x` from the defining infimum (every element of
    -- the constraint set dominates `m x`).
    intro k hk
    filter_upwards [hne k hk] with x hx_ne
    exact le_csInf hx_ne (fun b hb => hb.2.1)
  · -- `h_diff_int`: `μ − m ∈ L¹_per` via `muAux_diff_integrable`, using
    -- `μ ∈ L^{β+1}_per` (`muAux_mem_Lp_of_witnessData`) and `m ∈ L^{β+1}_per`.
    intro k hk
    have hβbar_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (hcong.β + 1) := by
      have : (1 : ℝ) ≤ hcong.β + 1 := by linarith [hcong.hβ]
      simpa using (ENNReal.one_le_ofReal.mpr this)
    have hβbar_top : ENNReal.ofReal (hcong.β + 1) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hμ_mem :
        MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) (muAux k m u V Du H) :=
      muAux_mem_Lp_of_witnessData hmon hcong hm_meas hu_meas hV_meas hDu_meas
        hm_mem hu_mem hV_mem hDu_mem hcont (hne k hk) h_anti h_cont (h_ne_all k hk)
    exact muAux_diff_integrable hβbar_one hβbar_top hμ_mem hm_mem
  · -- `h_DCT`: the per-`k` post-DCT integral inequality from `h_DCT_producer`.
    intro k hk
    exact h_DCT_producer hmon hcong hm_meas hu_meas hV_meas hDu_meas
      hm_mem hu_mem hV_mem hDu_mem hcont (hne k hk) h_anti h_cont (h_ne_all k hk)
      hVmeas hV hAeq hKeq hVI hw_m hw_u hw_Du hcoeWeak_Du
  · -- `h_HJB_at_mu`: extract `u + H(·,Du,μ) − V ≤ k` from `muAux_levelSet_ae`
    -- specialised at `a = μ x` (needs `0 ≤ μ x`, forward direction of the
    -- level-set iff with `μ x ≤ μ x`).
    intro k hk
    -- `μ ≥ 0` a.e. (infimum of a set of nonnegative reals).
    have hμ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        0 ≤ muAux k m u V Du H x :=
      Filter.Eventually.of_forall
        (fun x => le_csInf (h_ne_all k hk x) (fun b hb => hb.1))
    -- a.e. on-`Ici 0` antitonicity from the pointwise/standing facts.
    have hae_anti :
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ici 0) :=
      Filter.Eventually.of_forall h_anti
    -- Apply the on-`Ici 0` level-set characterisation at the (a.e.
    -- pointwise) `a = μ x` (`μ x ≥ 0`, so `a ∈ Ici 0`). The a.e. full-ℝ
    -- continuity `hcont` restricts to `ContinuousOn (Ici 0)`.
    filter_upwards [hμ_nn, hae_anti, hcont, hne k hk] with x hx_nn hx_anti hx_cont hx_ne
    have hiff :
        muAux k m u V Du H x ≤ muAux k m u V Du H x ↔
          m x ≤ muAux k m u V Du H x ∧
            u x + H x (fun i => Du i x) (muAux k m u V Du H x) - V x ≤ k :=
      muAux_le_iff_of_antitoneOn_of_nonempty hx_nn hx_cont.continuousOn hx_anti hx_ne
    exact (hiff.mp le_rfl).2

/-- **Positive-witness sibling of `weak_is_strong_HJB_le_of_witnessData`**
(on `{0 < m x}`). Same HJB-`≤ 0` conclusion, but the full-`ℝ` a.e. continuity
hypothesis is replaced by on-`(0,∞)` continuity of `H(x, Du x, ·)` together with
a.e. strict positivity `0 < m x` (the `hcoePos_m_witness` route). The four
structural fields of `weak_is_strong_HJB_le_of_perk_DCT_of_m_pos` are routed
through the `_of_m_pos` siblings; the `h_HJB_at_mu` field uses
`muAux_le_iff_of_antitoneOn_Ioi_of_nonempty_of_m_pos`. The on-`Ici 0` pointwise
facts `h_anti`/`h_cont` are still supplied (they feed the bound estimate / the
`muAux` measurability and restrict to `Ioi 0 ⊆ Ici 0`). The original is kept
untouched. -/
theorem weak_is_strong_HJB_le_of_witnessData_pos
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm_meas : Measurable m)
    (hu_meas : Measurable u)
    (hV_meas : Measurable V)
    (hDu_meas : ∀ i, Measurable (Du i))
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) m)
    (hu_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) u)
    (hV_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (hDu_mem : ∀ i,
      MemLpPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Du i))
    (hae_m_pos :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hcont :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (h_anti :
      ∀ x : Fin d → ℝ,
        AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ici 0))
    (h_cont :
      ∀ x : Fin d → ℝ,
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ici 0))
    (hne :
      ∀ k : ℝ, 0 < k →
        ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
          (muAuxSet k m u V Du H x).Nonempty)
    (h_ne_all :
      ∀ k : ℝ, 0 < k →
        ∀ x : Fin d → ℝ, (muAuxSet k m u V Du H x).Nonempty)
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
        (⇑w.2.1 : (Fin d → ℝ) → ℝ) (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ)) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      u x + H x (fun i => Du i x) (m x) - V x ≤ 0 := by
  refine weak_is_strong_HJB_le_of_perk_DCT_of_m_pos (V := V) (H := H) (Du := Du)
    (m := m) (u := u)
    hcont hae_m_pos (fun k hk => hne k hk) ?_ ?_ ?_ ?_
  · -- `h_mu_ge_m`.
    intro k hk
    filter_upwards [hne k hk] with x hx_ne
    exact le_csInf hx_ne (fun b hb => hb.2.1)
  · -- `h_diff_int`.
    intro k hk
    have hβbar_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (hcong.β + 1) := by
      have : (1 : ℝ) ≤ hcong.β + 1 := by linarith [hcong.hβ]
      simpa using (ENNReal.one_le_ofReal.mpr this)
    have hβbar_top : ENNReal.ofReal (hcong.β + 1) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hμ_mem :
        MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) (muAux k m u V Du H) :=
      muAux_mem_Lp_of_witnessData_pos hmon hcong hm_meas hu_meas hV_meas hDu_meas
        hm_mem hu_mem hV_mem hDu_mem hcont (hne k hk) hae_m_pos h_anti h_cont
        (h_ne_all k hk)
    exact muAux_diff_integrable hβbar_one hβbar_top hμ_mem hm_mem
  · -- `h_DCT` from `h_DCT_producer_of_m_pos`.
    intro k hk
    exact h_DCT_producer_of_m_pos hmon hcong hm_meas hu_meas hV_meas hDu_meas
      hm_mem hu_mem hV_mem hDu_mem hcont (hne k hk) hae_m_pos h_anti h_cont
      (h_ne_all k hk)
      hVmeas hV hAeq hKeq hVI hw_m hw_u hw_Du hcoeWeak_Du
  · -- `h_HJB_at_mu` via the on-`Ioi 0` level-set characterisation.
    intro k hk
    have hμ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        0 ≤ muAux k m u V Du H x :=
      Filter.Eventually.of_forall
        (fun x => le_csInf (h_ne_all k hk x) (fun b hb => hb.1))
    -- on-`Ioi 0` antitonicity from the on-`Ici 0` standing fact.
    have hae_anti :
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0) :=
      Filter.Eventually.of_forall
        (fun x => (h_anti x).mono Set.Ioi_subset_Ici_self)
    filter_upwards [hμ_nn, hae_anti, hcont, hae_m_pos, hne k hk]
      with x hx_nn hx_anti hx_cont hx_mpos hx_ne
    have hiff :
        muAux k m u V Du H x ≤ muAux k m u V Du H x ↔
          m x ≤ muAux k m u V Du H x ∧
            u x + H x (fun i => Du i x) (muAux k m u V Du H x) - V x ≤ k :=
      muAux_le_iff_of_antitoneOn_Ioi_of_nonempty_of_m_pos hx_mpos hx_nn hx_cont
        hx_anti hx_ne
    exact (hiff.mp le_rfl).2

/-- **Nonnegative-witness sibling of `weak_is_strong_HJB_le_of_witnessData`**
(STEP 5 of the δ-truncation route, paper `lem:weak.is.strong`, Step 1,
lines 1417–1506).

Same HJB-`≤ 0` conclusion as `weak_is_strong_HJB_le_of_witnessData_pos`, with
the full-`ℝ` a.e. continuity replaced by on-`(0,∞)` continuity of `H(x, Du x, ·)`
and *no positivity witness on `m`* — only `hae_m_nn : 0 ≤ m x` a.e. The four
structural fields of `weak_is_strong_HJB_le_of_perk_DCT_of_m_nonneg` are routed
through the nonneg-witness producer chain (`muAux_mem_Lp_of_witnessData_nonneg`,
`h_DCT_producer_of_m_nonneg`); the `h_HJB_at_mu` field reads the HJB inequality
straight off `μ x ∈ muAuxSet` via the on-`Ici 0` closedness
`muAuxSet_isClosed_of_continuousOn (h_cont x)` (no positivity needed). Strict
positivity is used only inside the producer chain for the truncated test density
`μ_δ = max(μ, δ)`, `δ > 0`, never for `m` or the witness. The `_pos`/`_pos'`/`_pos_aesm`
siblings are kept untouched. -/
theorem weak_is_strong_HJB_le_of_witnessData_nonneg
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm_meas : Measurable m)
    (hu_meas : Measurable u)
    (hV_meas : Measurable V)
    (hDu_meas : ∀ i, Measurable (Du i))
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) m)
    (hu_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) u)
    (hV_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (hDu_mem : ∀ i,
      MemLpPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Du i))
    (hae_m_nn :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hcont :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (h_anti :
      ∀ x : Fin d → ℝ,
        AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ici 0))
    (h_cont :
      ∀ x : Fin d → ℝ,
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ici 0))
    (hne :
      ∀ k : ℝ, 0 < k →
        ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
          (muAuxSet k m u V Du H x).Nonempty)
    (h_ne_all :
      ∀ k : ℝ, 0 < k →
        ∀ x : Fin d → ℝ, (muAuxSet k m u V Du H x).Nonempty)
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
        (⇑w.2.1 : (Fin d → ℝ) → ℝ) (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ)) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      u x + H x (fun i => Du i x) (m x) - V x ≤ 0 := by
  refine weak_is_strong_HJB_le_of_perk_DCT_of_m_nonneg (V := V) (H := H) (Du := Du)
    (m := m) (u := u)
    hcont hae_m_nn (fun k hk => hne k hk) ?_ ?_ ?_ ?_
  · -- `h_mu_ge_m`.
    intro k hk
    filter_upwards [hne k hk] with x hx_ne
    exact le_csInf hx_ne (fun b hb => hb.2.1)
  · -- `h_diff_int`.
    intro k hk
    have hβbar_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (hcong.β + 1) := by
      have : (1 : ℝ) ≤ hcong.β + 1 := by linarith [hcong.hβ]
      simpa using (ENNReal.one_le_ofReal.mpr this)
    have hβbar_top : ENNReal.ofReal (hcong.β + 1) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hμ_mem :
        MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) (muAux k m u V Du H) :=
      muAux_mem_Lp_of_witnessData_nonneg hmon hcong hm_meas hu_meas hV_meas hDu_meas
        hm_mem hu_mem hV_mem hDu_mem hcont (hne k hk) h_anti h_cont
        (h_ne_all k hk)
    exact muAux_diff_integrable hβbar_one hβbar_top hμ_mem hm_mem
  · -- `h_DCT` from `h_DCT_producer_of_m_nonneg`.
    intro k hk
    exact h_DCT_producer_of_m_nonneg hmon hcong hm_meas hu_meas hV_meas hDu_meas
      hm_mem hu_mem hV_mem hDu_mem hcont (hne k hk) hae_m_nn h_anti h_cont
      (h_ne_all k hk)
      hVmeas hV hAeq hKeq hVI hw_m hw_u hw_Du hcoeWeak_Du
  · -- `h_HJB_at_mu`: HJB at `μ x` read off `μ x ∈ muAuxSet` (Ici-0 closedness).
    intro k hk
    refine Filter.Eventually.of_forall (fun x => ?_)
    have h_closed : IsClosed (muAuxSet k m u V Du H x) :=
      muAuxSet_isClosed_of_continuousOn (h_cont x)
    have h_bdd : BddBelow (muAuxSet k m u V Du H x) :=
      muAuxSet_bddBelow k m u V Du H x
    have h_inf_mem : muAux k m u V Du H x ∈ muAuxSet k m u V Du H x :=
      h_closed.csInf_mem (h_ne_all k hk x) h_bdd
    exact h_inf_mem.2.2

/-- **a.e.-rider sibling of `weak_is_strong_HJB_le_of_witnessData_pos`**
(child-F, the producer-side fix that unblocks child-E).

The four pointwise closed-`Ici 0` / `∀ x` riders of the `_pos` entry point
(`h_anti`, `h_cont`, `h_ne_all`, and the boundary-dependent `hne`) are replaced
by the genuinely-available a.e.-on-`Ioi 0` data:

* `hae_anti : ∀ᵐ x, AntitoneOn (H x (Du x) ·) (Ioi 0)`
* `hae_ne   : ∀ k > 0, ∀ᵐ x, (muAuxSet k …).Nonempty`

threaded with `hae_m_pos`, so `muAux`/`muAuxSet` are only ever evaluated where
`0 < m x`. The discharge dispatches through the a.e.-rider producer chain
(`muAux_mem_Lp_of_witnessData_pos'`, `h_DCT_producer_of_m_pos'`), with `μ`
non-negativity from the unconditional `muAux_nonneg`. No public-bundle change,
no boundary (`m = 0`) data. The original `_pos` lemma is kept untouched. -/
theorem weak_is_strong_HJB_le_of_witnessData_pos'
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm_meas : Measurable m)
    (hu_meas : Measurable u)
    (hV_meas : Measurable V)
    (hDu_meas : ∀ i, Measurable (Du i))
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) m)
    (hu_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) u)
    (hV_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (hDu_mem : ∀ i,
      MemLpPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Du i))
    (hae_m_pos :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hcont :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hae_anti :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hae_ne :
      ∀ k : ℝ, 0 < k →
        ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
          (muAuxSet k m u V Du H x).Nonempty)
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
        (⇑w.2.1 : (Fin d → ℝ) → ℝ) (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ)) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      u x + H x (fun i => Du i x) (m x) - V x ≤ 0 := by
  refine weak_is_strong_HJB_le_of_perk_DCT_of_m_pos (V := V) (H := H) (Du := Du)
    (m := m) (u := u)
    hcont hae_m_pos (fun k hk => hae_ne k hk) ?_ ?_ ?_ ?_
  · -- `h_mu_ge_m`.
    intro k hk
    filter_upwards [hae_ne k hk] with x hx_ne
    exact le_csInf hx_ne (fun b hb => hb.2.1)
  · -- `h_diff_int`.
    intro k hk
    have hβbar_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (hcong.β + 1) := by
      have : (1 : ℝ) ≤ hcong.β + 1 := by linarith [hcong.hβ]
      simpa using (ENNReal.one_le_ofReal.mpr this)
    have hβbar_top : ENNReal.ofReal (hcong.β + 1) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hμ_mem :
        MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) (muAux k m u V Du H) :=
      muAux_mem_Lp_of_witnessData_pos' hmon hcong hm_meas hu_meas hV_meas hDu_meas
        hm_mem hu_mem hV_mem hDu_mem hcont (hae_ne k hk) hae_m_pos hae_anti
    exact muAux_diff_integrable hβbar_one hβbar_top hμ_mem hm_mem
  · -- `h_DCT` from `h_DCT_producer_of_m_pos'`.
    intro k hk
    exact h_DCT_producer_of_m_pos' hmon hcong hm_meas hu_meas hV_meas hDu_meas
      hm_mem hu_mem hV_mem hDu_mem hcont (hae_ne k hk) hae_m_pos hae_anti
      hVmeas hV hAeq hKeq hVI hw_m hw_u hw_Du hcoeWeak_Du
  · -- `h_HJB_at_mu` via the on-`Ioi 0` level-set characterisation.
    intro k hk
    have hμ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        0 ≤ muAux k m u V Du H x :=
      Filter.Eventually.of_forall (fun x => muAux_nonneg x)
    filter_upwards [hμ_nn, hae_anti, hcont, hae_m_pos, hae_ne k hk]
      with x hx_nn hx_anti hx_cont hx_mpos hx_ne
    have hiff :
        muAux k m u V Du H x ≤ muAux k m u V Du H x ↔
          m x ≤ muAux k m u V Du H x ∧
            u x + H x (fun i => Du i x) (muAux k m u V Du H x) - V x ≤ k :=
      muAux_le_iff_of_antitoneOn_Ioi_of_nonempty_of_m_pos hx_mpos hx_nn hx_cont
        hx_anti hx_ne
    exact (hiff.mp le_rfl).2

/-- **`AEStronglyMeasurable V` sibling of `weak_is_strong_HJB_le_of_witnessData_pos'`**
(child-G).

Identical to the primed version, but `V` is only `AEStronglyMeasurable` (`hV_aesm`).
The producer chain dispatches through the `_aesm` siblings
(`muAux_mem_Lp_of_witnessData_pos_aesm`, `h_DCT_producer_of_m_pos_aesm`). No
public-bundle change, no boundary (`m = 0`) data. The `_pos'` original is kept
untouched. -/
theorem weak_is_strong_HJB_le_of_witnessData_pos_aesm
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm_meas : Measurable m)
    (hu_meas : Measurable u)
    (hV_aesm : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hDu_meas : ∀ i, Measurable (Du i))
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) m)
    (hu_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) u)
    (hV_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (hDu_mem : ∀ i,
      MemLpPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Du i))
    (hae_m_pos :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hcont :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hae_anti :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hae_ne :
      ∀ k : ℝ, 0 < k →
        ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
          (muAuxSet k m u V Du H x).Nonempty)
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
        (⇑w.2.1 : (Fin d → ℝ) → ℝ) (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ)) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      u x + H x (fun i => Du i x) (m x) - V x ≤ 0 := by
  refine weak_is_strong_HJB_le_of_perk_DCT_of_m_pos (V := V) (H := H) (Du := Du)
    (m := m) (u := u)
    hcont hae_m_pos (fun k hk => hae_ne k hk) ?_ ?_ ?_ ?_
  · -- `h_mu_ge_m`.
    intro k hk
    filter_upwards [hae_ne k hk] with x hx_ne
    exact le_csInf hx_ne (fun b hb => hb.2.1)
  · -- `h_diff_int`.
    intro k hk
    have hβbar_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (hcong.β + 1) := by
      have : (1 : ℝ) ≤ hcong.β + 1 := by linarith [hcong.hβ]
      simpa using (ENNReal.one_le_ofReal.mpr this)
    have hβbar_top : ENNReal.ofReal (hcong.β + 1) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hμ_mem :
        MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) (muAux k m u V Du H) :=
      muAux_mem_Lp_of_witnessData_pos_aesm hmon hcong hm_meas hu_meas hV_aesm hDu_meas
        hm_mem hu_mem hV_mem hDu_mem hcont (hae_ne k hk) hae_m_pos hae_anti
    exact muAux_diff_integrable hβbar_one hβbar_top hμ_mem hm_mem
  · -- `h_DCT` from `h_DCT_producer_of_m_pos_aesm`.
    intro k hk
    exact h_DCT_producer_of_m_pos_aesm hmon hcong hm_meas hu_meas hV_aesm hDu_meas
      hm_mem hu_mem hV_mem hDu_mem hcont (hae_ne k hk) hae_m_pos hae_anti
      hVmeas hV hAeq hKeq hVI hw_m hw_u hw_Du hcoeWeak_Du
  · -- `h_HJB_at_mu` via the on-`Ioi 0` level-set characterisation.
    intro k hk
    have hμ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        0 ≤ muAux k m u V Du H x :=
      Filter.Eventually.of_forall (fun x => muAux_nonneg x)
    filter_upwards [hμ_nn, hae_anti, hcont, hae_m_pos, hae_ne k hk]
      with x hx_nn hx_anti hx_cont hx_mpos hx_ne
    have hiff :
        muAux k m u V Du H x ≤ muAux k m u V Du H x ↔
          m x ≤ muAux k m u V Du H x ∧
            u x + H x (fun i => Du i x) (muAux k m u V Du H x) - V x ≤ k :=
      muAux_le_iff_of_antitoneOn_Ioi_of_nonempty_of_m_pos hx_mpos hx_nn hx_cont
        hx_anti hx_ne
    exact (hiff.mp le_rfl).2

set_option maxHeartbeats 1600000 in
/-- **Nonneg-`delta` entry point: (a:Hat0) boundary HJB sibling of
`weak_is_strong_HJB_le_of_witnessData_pos_aesm`** (child-D2b).

Identical conclusion to the `_pos_aesm` entry point, but the a.e. strict
positivity `hae_m_pos` is replaced by mere a.e. non-negativity `hae_m_nn`, and
the boundary `{μ=0}` HJB inequality is routed through the (a:Hat0) extension
device (`hHat0 : HypothesisHat0 H`, `hAgree : H_zero_eq_Hext H` are the only new
public riders). The producer chain dispatches through the nonneg `_aesm`
siblings (`muAux_mem_Lp_of_witnessData_nonneg_aesm`,
`h_DCT_producer_of_m_nonneg_aesm`) and the per-`k` engine
`weak_is_strong_HJB_le_of_perk_DCT_of_m_nonneg`. The `h_HJB_at_mu` discharge uses
the boundary-free level-set lemma at `a = μ ≥ 0`: `le_rfl` gives
`HJB(μ) ≤ k ∨ μ ≤ 0`; on `μ = 0` the right-hand limit
`H(·) → Hext H x (Du x) 0` (from `hHat0`) plus the admissible-witness bound gives
`Hext ≤ (k−u+V : WithTop)`, finite (paper line 1435 — finiteness DERIVED, not
assumed), and `hAgree` transports back to raw `H(0)`. NO `0<m`, NO Ici-0
continuity, NO `Hext_finite_at_zero`. The `_pos_aesm` original is kept untouched. -/
theorem weak_is_strong_HJB_le_of_witnessData_nonneg_delta
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm_meas : Measurable m)
    (hu_meas : Measurable u)
    (hV_aesm : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hDu_meas : ∀ i, Measurable (Du i))
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) m)
    (hu_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) u)
    (hV_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (hDu_mem : ∀ i,
      MemLpPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Du i))
    (hae_m_nn :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hcont :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hae_anti :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hae_ne :
      ∀ k : ℝ, 0 < k →
        ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
          (muAuxSet k m u V Du H x).Nonempty)
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
        (⇑w.2.1 : (Fin d → ℝ) → ℝ) (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ)) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      u x + H x (fun i => Du i x) (m x) - V x ≤ 0 := by
  refine weak_is_strong_HJB_le_of_perk_DCT_of_m_nonneg (V := V) (H := H) (Du := Du)
    (m := m) (u := u)
    hcont hae_m_nn (fun k hk => hae_ne k hk) ?_ ?_ ?_ ?_
  · -- `h_mu_ge_m`.
    intro k hk
    filter_upwards [hae_ne k hk] with x hx_ne
    exact le_csInf hx_ne (fun b hb => hb.2.1)
  · -- `h_diff_int`.
    intro k hk
    have hβbar_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (hcong.β + 1) := by
      have : (1 : ℝ) ≤ hcong.β + 1 := by linarith [hcong.hβ]
      simpa using (ENNReal.one_le_ofReal.mpr this)
    have hβbar_top : ENNReal.ofReal (hcong.β + 1) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hμ_mem :
        MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) (muAux k m u V Du H) :=
      muAux_mem_Lp_of_witnessData_nonneg_aesm hmon hcong hm_meas hu_meas hV_aesm hDu_meas
        hm_mem hu_mem hV_mem hDu_mem hcont (hae_ne k hk) hae_m_nn hae_anti
    exact muAux_diff_integrable hβbar_one hβbar_top hμ_mem hm_mem
  · -- `h_DCT` from `h_DCT_producer_of_m_nonneg_aesm`.
    intro k hk
    exact h_DCT_producer_of_m_nonneg_aesm hmon hcong hHat0 hAgree hm_meas hu_meas
      hV_aesm hDu_meas
      hm_mem hu_mem hV_mem hDu_mem hcont (hae_ne k hk) hae_m_nn hae_anti
      hVmeas hV hAeq hKeq hVI hw_m hw_u hw_Du hcoeWeak_Du
  · -- `h_HJB_at_mu` via the boundary-free level-set characterisation at `a = μ`.
    intro k hk
    have hμ_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        0 ≤ muAux k m u V Du H x :=
      Filter.Eventually.of_forall (fun x => muAux_nonneg x)
    filter_upwards [hμ_nn, hae_anti, hcont, hae_m_nn, hae_ne k hk,
        hHat0.exists_limit_at_zero, hAgree]
      with x hx_nn hx_anti hx_cont hx_mnn hx_ne hx_limit hx_agree
    set μ : ℝ := muAux k m u V Du H x with hμ_def
    set b : ℝ := k - u x + V x with hb_def
    -- `H x (Du x) μ ≤ b`, hence the goal `u + H(μ) - V ≤ k`.
    have hHμ_le_b : H x (fun i => Du i x) μ ≤ b := by
      have hiff :=
        muAux_le_iff_of_antitoneOn_Ioi_of_nonempty_of_m_nonneg
          (k := k) (m := m) (u := u) (V := V) (Du := Du) (H := H) (x := x)
          (a := μ) hx_mnn hx_nn hx_cont hx_anti hx_ne
      rcases (hiff.mp (le_refl μ)).2 with hHJB | hμle0
      · -- `HJB(μ) ≤ k`.
        rw [hb_def]; linarith
      · -- `μ ≤ 0`, i.e. `μ = 0`: route the boundary value through `Hext`.
        have hμ0 : μ = 0 := le_antisymm hμle0 hx_nn
        have hwit := (muAux_le_zero_iff_of_antitoneOn_Ioi_of_m_nonneg
          (k := k) (m := m) (u := u) (V := V) (Du := Du) (H := H) (x := x)
          hx_mnn hx_anti hx_ne).mp hμle0
        have hraw_le' : H x (fun i => Du i x) 0 ≤ b := by
          by_cases hzero : ∃ n : ℕ, ∃ q : ℚ,
              (q : ℝ) = 0 ∧ m x ≤ (q : ℝ) ∧ 0 ≤ (q : ℝ) ∧
                (q : ℝ) < 1 / ((n : ℝ) + 1) ∧
                u x + H x (fun i => Du i x) (q : ℝ) - V x ≤ k
          · -- Case A: a `q = 0` witness ⇒ raw `H(0) ≤ b` directly.
            obtain ⟨_, _, hq_eq0, _, _, _, hHJB_q⟩ := hzero
            have hH0 : u x + H x (fun i => Du i x) (0 : ℝ) - V x ≤ k := by
              rw [← hq_eq0]; exact hHJB_q
            rw [hb_def]; linarith
          · -- Case B: every witness is positive ⇒ `H(ν) ≤ b` for all `ν > 0`,
            -- hence `Hext H x (Du x) 0 ≤ b`; transport to raw via `hAgree`.
            have hTendsto :
                Filter.Tendsto
                  (fun ν : ℝ => ((H x (fun i => Du i x) ν : ℝ) : WithTop ℝ))
                  (nhdsWithin 0 (Set.Ioi 0))
                  (nhds (Hamiltonian.H_at_zero H x (fun i => Du i x))) :=
              Hamiltonian.tendsto_Hext_zero_of_exists (hx_limit (fun i => Du i x))
            have hPointwise : ∀ ν : ℝ, 0 < ν → H x (fun i => Du i x) ν ≤ b := by
              intro ν hν
              obtain ⟨n, hn⟩ := exists_nat_one_div_lt hν
              obtain ⟨q, hq_ge_m, hq_nn, hq_hi, hHJB_q⟩ := hwit n
              have hq_lt_ν : (q : ℝ) < ν := by
                have h1 : (1 : ℝ) / ((n : ℝ) + 1) < ν := by
                  simpa only [one_div] using hn
                exact lt_trans hq_hi h1
              have hq_pos : 0 < (q : ℝ) := by
                rcases eq_or_lt_of_le hq_nn with hq0 | hq_pos
                · exact absurd
                    ⟨n, q, hq0.symm, hq_ge_m, hq_nn, hq_hi, hHJB_q⟩ hzero
                · exact hq_pos
              have hHq : H x (fun i => Du i x) (q : ℝ) ≤ b := by
                rw [hb_def]; linarith [hHJB_q]
              have hanti_le :
                  H x (fun i => Du i x) ν ≤ H x (fun i => Du i x) (q : ℝ) :=
                hx_anti hq_pos (lt_trans hq_pos hq_lt_ν) hq_lt_ν.le
              exact le_trans hanti_le hHq
            have hEv :
                ∀ᶠ ν in nhdsWithin 0 (Set.Ioi 0),
                  ((H x (fun i => Du i x) ν : ℝ) : WithTop ℝ)
                    ≤ ((b : ℝ) : WithTop ℝ) := by
              refine Filter.eventually_iff_exists_mem.mpr ⟨Set.Ioi (0 : ℝ),
                self_mem_nhdsWithin, fun ν hν => ?_⟩
              exact_mod_cast hPointwise ν hν
            have hHext_le :
                Hamiltonian.H_at_zero H x (fun i => Du i x)
                  ≤ ((b : ℝ) : WithTop ℝ) :=
              le_of_tendsto hTendsto hEv
            have hAgree_x :
                ((H x (fun i => Du i x) 0 : ℝ) : WithTop ℝ)
                  = Hamiltonian.H_at_zero H x (fun i => Du i x) := by
              rw [Hamiltonian.H_at_zero_def]; exact hx_agree (fun i => Du i x)
            have hraw_le :
                ((H x (fun i => Du i x) 0 : ℝ) : WithTop ℝ)
                  ≤ ((b : ℝ) : WithTop ℝ) := by
              rw [hAgree_x]; exact hHext_le
            exact_mod_cast hraw_le
        rw [hμ0]; exact hraw_le'
    rw [hb_def] at hHμ_le_b; linarith

/-! ## Step 1 prereq3 — exponent-transported witness producer
(`infra-P7-sigfix-T2-phase6-hcoeHJB-le-prereq3-transported-equalities`)

`weak_is_strong_HJB_le_of_witnessData` (above) fixes the Banach
exponents at `hcong.β`/`hcong.α`. The `hcoeHJB_le` discharge, however,
builds its weak-VI `data` (and hence the witness `data.weakVI.choose`,
the operators `data.A`/`data.K`) at the `h`-exponents of a SEPARATE
apriori power data `h : CongestionAprioriPowerData`, related to `hcong`
only by the abstract `Eq` proofs `inputs.hpowα_eq : hcong.α = h.α`,
`inputs.hpowβ_eq : hcong.β = h.β` (NOT `rfl` at the opaque `bareBridge`
Main call sites). Consequently the witness `congestionXBanach` type does
not definitionally unify with the producer's, and even the `Fact`
exponent instances fail to synthesise.

This wrapper makes the producer invokable for that GENERAL case. It
takes ABSTRACT reals `αh βh : ℝ` with equalities `hpowα_eq : hcong.α = αh`,
`hpowβ_eq : hcong.β = βh`, and accepts the witness `w`, operators `A`/`K`,
`Fact` instances and Lp-membership data all typed at the `αh`/`βh`
exponents — with the operator identifications `hAeq`/`hKeq` relating
`A`/`K` to `congestionAepsiOpK`/`congestionBanachK` (built at `hcong`)
TRANSPORTED across the two equalities. The body `subst`s the equalities
(both `αh`/`βh` are free variables, so `subst` rewrites every
`αh`/`βh`-typed hypothesis, including the `Fact` instances, back to the
`hcong`-exponents), then dispatches to the concrete producer. The HJB
conclusion `u + H(x,Du,m) − V ≤ 0` does not mention the Banach
exponents, so the transport is statement-invariant — no new oracle, no
`sorry`. -/
theorem weak_is_strong_HJB_le_of_witnessData_powTransport
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    {αh βh : ℝ}
    (hpowα_eq : hcong.α = αh)
    (hpowβ_eq : hcong.β = βh)
    [Fact (1 ≤ ENNReal.ofReal (βh + 1))]
    [Fact (1 ≤ ENNReal.ofReal (αh * (βh + 1) / βh))]
    -- The two `hcong`-exponent `Fact`s (so the bare `congestionAepsiOpK`/
    -- `congestionBanachK` elaborate) and the intermediate mixed `Fact` arising
    -- when the first `▸` has rewritten `hcong.α → αh` but `hcong.β` is still
    -- pending. All four are derivable from `hcong.hα`/`hcong.hβ`; the discharge
    -- supplies them by `haveI`. They collapse onto the `βh`-`Fact`s post-`subst`.
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    [Fact (1 ≤ ENNReal.ofReal (αh * (hcong.β + 1) / hcong.β))]
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm_meas : Measurable m)
    (hu_meas : Measurable u)
    (hV_meas : Measurable V)
    (hDu_meas : ∀ i, Measurable (Du i))
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (βh + 1)) m)
    (hu_mem : MemLpPer (d := d) (ENNReal.ofReal ((βh + 1) / βh)) u)
    (hV_mem : MemLpPer (d := d) (ENNReal.ofReal ((βh + 1) / βh)) V)
    (hDu_mem : ∀ i,
      MemLpPer (d := d)
        (ENNReal.ofReal (αh * (βh + 1) / βh)) (Du i))
    (hae_m_nn :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hcont :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        Continuous (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀))
    (h_anti :
      ∀ x : Fin d → ℝ,
        AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ici 0))
    (h_cont :
      ∀ x : Fin d → ℝ,
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ici 0))
    (hne :
      ∀ k : ℝ, 0 < k →
        ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
          (muAuxSet k m u V Du H x).Nonempty)
    (h_ne_all :
      ∀ k : ℝ, 0 < k →
        ∀ x : Fin d → ℝ, (muAuxSet k m u V Du H x).Nonempty)
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    -- The value-Lp hypothesis consumed by the operator and by the producer is
    -- stated at the `hcong`-exponents (post-`subst` it coincides with the
    -- `βh`-typed memberships above by proof irrelevance). Keeping it
    -- `hcong`-typed lets the operator term `congestionAepsiOpK hmon hcong …`
    -- elaborate before the `subst`, so the `▸` casts in `hAeq`/`hKeq` only
    -- transport the *type* of `A`/`K` (not the operator's own arguments).
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    {ε : ℝ}
    {A : congestionXBanach d
          (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh)) →
        StrongDual ℝ (congestionXBanach d
          (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh)))}
    {K : Set (congestionXBanach d
          (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh)))}
    {w : congestionXBanach d
          (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh))}
    -- Type equalities from the exponent equalities. They carry the transport
    -- of the operator/set TYPES from the `hcong`-exponents to the `βh`/`αh`
    -- exponents; the discharge proves them by `subst`/`congr` (no `▸` motive
    -- to infer). `cast` then moves the bare operators across them with no
    -- motive trouble — robust whether the equalities are `rfl` (Main special
    -- case) or abstract projections (`h.α`/`h.β`, the general case).
    (hAty :
      (congestionXBanach d (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) →
        StrongDual ℝ (congestionXBanach d (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))))
        =
      (congestionXBanach d (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh)) →
        StrongDual ℝ (congestionXBanach d (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh)))))
    (hKty :
      Set (congestionXBanach d (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))
        =
      Set (congestionXBanach d (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh))))
    (hAeq : A = cast hAty (congestionAepsiOpK hmon hcong hVmeas hV ε))
    (hKeq : K = cast hKty (congestionBanachK d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ))
    (hVI : ∀ v ∈ K, 0 ≤ A v (v - w))
    (hw_m : (⇑w.1 : (Fin d → ℝ) → ℝ) = m)
    (hw_u : (⇑w.2.1 : (Fin d → ℝ) → ℝ) = u)
    (hw_Du : ∀ i, (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ) = Du i)
    (hcoeWeak_Du : ∀ i,
      Periodic.HasWeakDerivPer (d := d) i
        (⇑w.2.1 : (Fin d → ℝ) → ℝ) (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ)) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      u x + H x (fun i => Du i x) (m x) - V x ≤ 0 := by
  -- Transport everything back to the `hcong`-exponents by substituting the
  -- abstract exponent variables. Both `αh` and `βh` are free, so `subst`
  -- rewrites every `αh`/`βh`-typed hypothesis (incl. the `Fact` instances, the
  -- witness/operators, and the type equalities `hAty`/`hKty`), reducing the
  -- goal to the concrete producer.
  subst hpowβ_eq
  subst hpowα_eq
  -- Post-`subst`, `hAty`/`hKty` are `rfl`-type equalities, so the `cast`s in
  -- `hAeq`/`hKeq` collapse (`cast_eq`); the producer then takes the witness
  -- data verbatim.
  rw [cast_eq] at hAeq hKeq
  exact weak_is_strong_HJB_le_of_witnessData hmon hcong hm_meas hu_meas
    hV_meas hDu_meas hm_mem hu_mem hV_mem hDu_mem hae_m_nn hcont h_anti h_cont
    hne h_ne_all hVmeas hV hAeq hKeq hVI hw_m hw_u hw_Du hcoeWeak_Du

/-- **Positive-witness exponent-transported sibling of
`weak_is_strong_HJB_le_of_witnessData_powTransport`** (on `{0 < m x}`).

Identical `subst`/`cast`-collapse skeleton to the original transport wrapper,
but the full-`ℝ` continuity hypothesis is replaced by on-`(0,∞)` continuity plus
a.e. strict positivity `0 < m x`, and the discharge dispatches to
`weak_is_strong_HJB_le_of_witnessData_pos`. The HJB conclusion is exponent-free,
so the transport remains statement-invariant. -/
theorem weak_is_strong_HJB_le_of_witnessData_powTransport_pos
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    {αh βh : ℝ}
    (hpowα_eq : hcong.α = αh)
    (hpowβ_eq : hcong.β = βh)
    [Fact (1 ≤ ENNReal.ofReal (βh + 1))]
    [Fact (1 ≤ ENNReal.ofReal (αh * (βh + 1) / βh))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    [Fact (1 ≤ ENNReal.ofReal (αh * (hcong.β + 1) / hcong.β))]
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm_meas : Measurable m)
    (hu_meas : Measurable u)
    (hV_meas : Measurable V)
    (hDu_meas : ∀ i, Measurable (Du i))
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (βh + 1)) m)
    (hu_mem : MemLpPer (d := d) (ENNReal.ofReal ((βh + 1) / βh)) u)
    (hV_mem : MemLpPer (d := d) (ENNReal.ofReal ((βh + 1) / βh)) V)
    (hDu_mem : ∀ i,
      MemLpPer (d := d)
        (ENNReal.ofReal (αh * (βh + 1) / βh)) (Du i))
    (hae_m_pos :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hcont :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (h_anti :
      ∀ x : Fin d → ℝ,
        AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ici 0))
    (h_cont :
      ∀ x : Fin d → ℝ,
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ici 0))
    (hne :
      ∀ k : ℝ, 0 < k →
        ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
          (muAuxSet k m u V Du H x).Nonempty)
    (h_ne_all :
      ∀ k : ℝ, 0 < k →
        ∀ x : Fin d → ℝ, (muAuxSet k m u V Du H x).Nonempty)
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    {ε : ℝ}
    {A : congestionXBanach d
          (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh)) →
        StrongDual ℝ (congestionXBanach d
          (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh)))}
    {K : Set (congestionXBanach d
          (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh)))}
    {w : congestionXBanach d
          (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh))}
    (hAty :
      (congestionXBanach d (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) →
        StrongDual ℝ (congestionXBanach d (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))))
        =
      (congestionXBanach d (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh)) →
        StrongDual ℝ (congestionXBanach d (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh)))))
    (hKty :
      Set (congestionXBanach d (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))
        =
      Set (congestionXBanach d (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh))))
    (hAeq : A = cast hAty (congestionAepsiOpK hmon hcong hVmeas hV ε))
    (hKeq : K = cast hKty (congestionBanachK d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ))
    (hVI : ∀ v ∈ K, 0 ≤ A v (v - w))
    (hw_m : (⇑w.1 : (Fin d → ℝ) → ℝ) = m)
    (hw_u : (⇑w.2.1 : (Fin d → ℝ) → ℝ) = u)
    (hw_Du : ∀ i, (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ) = Du i)
    (hcoeWeak_Du : ∀ i,
      Periodic.HasWeakDerivPer (d := d) i
        (⇑w.2.1 : (Fin d → ℝ) → ℝ) (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ)) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      u x + H x (fun i => Du i x) (m x) - V x ≤ 0 := by
  subst hpowβ_eq
  subst hpowα_eq
  rw [cast_eq] at hAeq hKeq
  exact weak_is_strong_HJB_le_of_witnessData_pos hmon hcong hm_meas hu_meas
    hV_meas hDu_meas hm_mem hu_mem hV_mem hDu_mem hae_m_pos hcont h_anti h_cont
    hne h_ne_all hVmeas hV hAeq hKeq hVI hw_m hw_u hw_Du hcoeWeak_Du

/-- **a.e.-rider exponent-transported sibling of
`weak_is_strong_HJB_le_of_witnessData_powTransport_pos`** (child-F).

Identical `subst`/`cast`-collapse skeleton, but the pointwise closed-`Ici 0` /
`∀ x` riders are replaced by the a.e.-on-`Ioi 0` forms `hae_anti`/`hae_ne`
(threaded with `hae_m_pos`), and the discharge dispatches to
`weak_is_strong_HJB_le_of_witnessData_pos'`. This is the primed entry point
child-E will call: no public-bundle change, no boundary (`m = 0`) data. -/
theorem weak_is_strong_HJB_le_of_witnessData_powTransport_pos'
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    {αh βh : ℝ}
    (hpowα_eq : hcong.α = αh)
    (hpowβ_eq : hcong.β = βh)
    [Fact (1 ≤ ENNReal.ofReal (βh + 1))]
    [Fact (1 ≤ ENNReal.ofReal (αh * (βh + 1) / βh))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    [Fact (1 ≤ ENNReal.ofReal (αh * (hcong.β + 1) / hcong.β))]
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm_meas : Measurable m)
    (hu_meas : Measurable u)
    (hV_meas : Measurable V)
    (hDu_meas : ∀ i, Measurable (Du i))
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (βh + 1)) m)
    (hu_mem : MemLpPer (d := d) (ENNReal.ofReal ((βh + 1) / βh)) u)
    (hV_mem : MemLpPer (d := d) (ENNReal.ofReal ((βh + 1) / βh)) V)
    (hDu_mem : ∀ i,
      MemLpPer (d := d)
        (ENNReal.ofReal (αh * (βh + 1) / βh)) (Du i))
    (hae_m_pos :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hcont :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hae_anti :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hae_ne :
      ∀ k : ℝ, 0 < k →
        ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
          (muAuxSet k m u V Du H x).Nonempty)
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    {ε : ℝ}
    {A : congestionXBanach d
          (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh)) →
        StrongDual ℝ (congestionXBanach d
          (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh)))}
    {K : Set (congestionXBanach d
          (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh)))}
    {w : congestionXBanach d
          (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh))}
    (hAty :
      (congestionXBanach d (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) →
        StrongDual ℝ (congestionXBanach d (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))))
        =
      (congestionXBanach d (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh)) →
        StrongDual ℝ (congestionXBanach d (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh)))))
    (hKty :
      Set (congestionXBanach d (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))
        =
      Set (congestionXBanach d (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh))))
    (hAeq : A = cast hAty (congestionAepsiOpK hmon hcong hVmeas hV ε))
    (hKeq : K = cast hKty (congestionBanachK d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ))
    (hVI : ∀ v ∈ K, 0 ≤ A v (v - w))
    (hw_m : (⇑w.1 : (Fin d → ℝ) → ℝ) = m)
    (hw_u : (⇑w.2.1 : (Fin d → ℝ) → ℝ) = u)
    (hw_Du : ∀ i, (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ) = Du i)
    (hcoeWeak_Du : ∀ i,
      Periodic.HasWeakDerivPer (d := d) i
        (⇑w.2.1 : (Fin d → ℝ) → ℝ) (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ)) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      u x + H x (fun i => Du i x) (m x) - V x ≤ 0 := by
  subst hpowβ_eq
  subst hpowα_eq
  rw [cast_eq] at hAeq hKeq
  exact weak_is_strong_HJB_le_of_witnessData_pos' hmon hcong hm_meas hu_meas
    hV_meas hDu_meas hm_mem hu_mem hV_mem hDu_mem hae_m_pos hcont hae_anti
    hae_ne hVmeas hV hAeq hKeq hVI hw_m hw_u hw_Du hcoeWeak_Du

/-- **`AEStronglyMeasurable V` sibling of
`weak_is_strong_HJB_le_of_witnessData_powTransport_pos'`** (child-G).

Identical `subst`/`cast`-collapse skeleton, but `V` is only `AEStronglyMeasurable`
(`hV_aesm`), so the discharge dispatches to `weak_is_strong_HJB_le_of_witnessData_pos_aesm`.
This is the entry point child-E will call: it passes `inputs.hVmeas`
(`AEStronglyMeasurable V`) directly for both `hV_aesm` and `hVmeas`, with no
public-bundle change and no boundary (`m = 0`) data. The `_pos'` original is kept
untouched. -/
theorem weak_is_strong_HJB_le_of_witnessData_powTransport_pos_aesm
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    {αh βh : ℝ}
    (hpowα_eq : hcong.α = αh)
    (hpowβ_eq : hcong.β = βh)
    [Fact (1 ≤ ENNReal.ofReal (βh + 1))]
    [Fact (1 ≤ ENNReal.ofReal (αh * (βh + 1) / βh))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    [Fact (1 ≤ ENNReal.ofReal (αh * (hcong.β + 1) / hcong.β))]
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm_meas : Measurable m)
    (hu_meas : Measurable u)
    (hV_aesm : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hDu_meas : ∀ i, Measurable (Du i))
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (βh + 1)) m)
    (hu_mem : MemLpPer (d := d) (ENNReal.ofReal ((βh + 1) / βh)) u)
    (hV_mem : MemLpPer (d := d) (ENNReal.ofReal ((βh + 1) / βh)) V)
    (hDu_mem : ∀ i,
      MemLpPer (d := d)
        (ENNReal.ofReal (αh * (βh + 1) / βh)) (Du i))
    (hae_m_pos :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hcont :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hae_anti :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hae_ne :
      ∀ k : ℝ, 0 < k →
        ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
          (muAuxSet k m u V Du H x).Nonempty)
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    {ε : ℝ}
    {A : congestionXBanach d
          (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh)) →
        StrongDual ℝ (congestionXBanach d
          (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh)))}
    {K : Set (congestionXBanach d
          (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh)))}
    {w : congestionXBanach d
          (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh))}
    (hAty :
      (congestionXBanach d (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) →
        StrongDual ℝ (congestionXBanach d (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))))
        =
      (congestionXBanach d (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh)) →
        StrongDual ℝ (congestionXBanach d (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh)))))
    (hKty :
      Set (congestionXBanach d (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))
        =
      Set (congestionXBanach d (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh))))
    (hAeq : A = cast hAty (congestionAepsiOpK hmon hcong hVmeas hV ε))
    (hKeq : K = cast hKty (congestionBanachK d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ))
    (hVI : ∀ v ∈ K, 0 ≤ A v (v - w))
    (hw_m : (⇑w.1 : (Fin d → ℝ) → ℝ) = m)
    (hw_u : (⇑w.2.1 : (Fin d → ℝ) → ℝ) = u)
    (hw_Du : ∀ i, (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ) = Du i)
    (hcoeWeak_Du : ∀ i,
      Periodic.HasWeakDerivPer (d := d) i
        (⇑w.2.1 : (Fin d → ℝ) → ℝ) (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ)) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      u x + H x (fun i => Du i x) (m x) - V x ≤ 0 := by
  subst hpowβ_eq
  subst hpowα_eq
  rw [cast_eq] at hAeq hKeq
  exact weak_is_strong_HJB_le_of_witnessData_pos_aesm hmon hcong hm_meas hu_meas
    hV_aesm hDu_meas hm_mem hu_mem hV_mem hDu_mem hae_m_pos hcont hae_anti
    hae_ne hVmeas hV hAeq hKeq hVI hw_m hw_u hw_Du hcoeWeak_Du

/-! ## Auto-rider sibling of the `_aesm` entry point (child-E)

`weak_is_strong_HJB_le_of_witnessData_powTransport_pos_aesm` still takes the
three a.e.-on-`Ioi 0` riders `hcont`/`hae_anti`/`hae_ne` as explicit
hypotheses. The `CongestionRegularizedSequenceBuilderInputs` bundle carries
only `hmon`/`hcong`, from which all three are derivable:

* `hcont` — restrict the joint a.e. continuity `hmon.continuous_H_pm` (on
  `{pm | 0 < pm.2}`, inherited from the `RegularityH` parent of
  `HypothesisMonotone`) to the section `μ₀ ↦ H x (Du · x) μ₀` on `Ioi 0`;
* `hae_anti` — specialise `antitone_in_m hmon` at `p := Du · x`;
* `hae_ne` — `muAux_nonempty_of_large_bound` with the static upper bound
  `H x (Du · x) μ₀ ≤ 2K·(‖Du x‖^{α(1+τ/β)} + 1) − δ·μ₀^β` (`μ₀ ≥ 1`),
  obtained from `H_upper_congestion_of_hmon` by dropping the `≤ 1` factors
  `1/μ₀ ≤ 1`, `1/μ₀^τ ≤ 1`.

None of these touches the boundary `m = 0`: they are all a.e.-on-`Ioi 0`
facts, exactly the form the `_aesm` chain consumes. This is the entry point
the Apriori `hcoeHJB_le` discharge calls. -/
theorem weak_is_strong_HJB_le_of_witnessData_powTransport_pos_aesm_autoRiders
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    {αh βh : ℝ}
    (hpowα_eq : hcong.α = αh)
    (hpowβ_eq : hcong.β = βh)
    [Fact (1 ≤ ENNReal.ofReal (βh + 1))]
    [Fact (1 ≤ ENNReal.ofReal (αh * (βh + 1) / βh))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    [Fact (1 ≤ ENNReal.ofReal (αh * (hcong.β + 1) / hcong.β))]
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm_meas : Measurable m)
    (hu_meas : Measurable u)
    (hV_aesm : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hDu_meas : ∀ i, Measurable (Du i))
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (βh + 1)) m)
    (hu_mem : MemLpPer (d := d) (ENNReal.ofReal ((βh + 1) / βh)) u)
    (hV_mem : MemLpPer (d := d) (ENNReal.ofReal ((βh + 1) / βh)) V)
    (hDu_mem : ∀ i,
      MemLpPer (d := d)
        (ENNReal.ofReal (αh * (βh + 1) / βh)) (Du i))
    (hae_m_pos :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    {ε : ℝ}
    {A : congestionXBanach d
          (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh)) →
        StrongDual ℝ (congestionXBanach d
          (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh)))}
    {K : Set (congestionXBanach d
          (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh)))}
    {w : congestionXBanach d
          (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh))}
    (hAty :
      (congestionXBanach d (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) →
        StrongDual ℝ (congestionXBanach d (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))))
        =
      (congestionXBanach d (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh)) →
        StrongDual ℝ (congestionXBanach d (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh)))))
    (hKty :
      Set (congestionXBanach d (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))
        =
      Set (congestionXBanach d (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh))))
    (hAeq : A = cast hAty (congestionAepsiOpK hmon hcong hVmeas hV ε))
    (hKeq : K = cast hKty (congestionBanachK d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ))
    (hVI : ∀ v ∈ K, 0 ≤ A v (v - w))
    (hw_m : (⇑w.1 : (Fin d → ℝ) → ℝ) = m)
    (hw_u : (⇑w.2.1 : (Fin d → ℝ) → ℝ) = u)
    (hw_Du : ∀ i, (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ) = Du i)
    (hcoeWeak_Du : ∀ i,
      Periodic.HasWeakDerivPer (d := d) i
        (⇑w.2.1 : (Fin d → ℝ) → ℝ) (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ)) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      u x + H x (fun i => Du i x) (m x) - V x ≤ 0 := by
  -- (1) `hcont`: section continuity on `Ioi 0` from joint a.e. continuity on
  -- `{pm | 0 < pm.2}` (inherited from `RegularityH`).
  have hcont :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0) := by
    filter_upwards [hmon.continuous_H_pm] with x hx
    have hg : Continuous (fun μ₀ : ℝ => ((fun i => Du i x), μ₀)) :=
      continuous_const.prodMk continuous_id
    have hmaps : Set.MapsTo (fun μ₀ : ℝ => ((fun i => Du i x), μ₀))
        (Set.Ioi (0 : ℝ)) {pm : (Fin d → ℝ) × ℝ | 0 < pm.2} := by
      intro μ₀ hμ₀
      exact hμ₀
    exact hx.comp hg.continuousOn hmaps
  -- (2) `hae_anti`: specialise `antitone_in_m hmon` at `p := Du · x`.
  have hae_anti :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0) := by
    filter_upwards [antitone_in_m hmon] with x hx
    exact hx (fun i => Du i x)
  -- (3) `hae_ne`: `muAux_nonempty_of_large_bound` with the static upper bound.
  obtain ⟨K₀, δ, hK₀_pos, hδ_pos, hUpper⟩ := H_upper_congestion_of_hmon hmon hcong
  have hae_ne :
      ∀ k : ℝ, 0 < k →
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          (muAuxSet k m u V Du H x).Nonempty := by
    intro k hk
    -- Static `μ₀ ≥ 1` bound `H ≤ f x - δ·μ₀^β` with
    -- `f x := 2·K₀·(‖Du x‖^{α(1+τ/β)} + 1)`.
    refine muAux_nonempty_of_large_bound (k := k) (m := m) (u := u) (V := V)
      (Du := Du) (H := H) (β := hcong.β) (δ := δ) hcong.hβ hδ_pos
      (f := fun x => 2 * K₀
        * (‖(fun i => Du i x)‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) + 1)) ?_
    filter_upwards [hUpper] with x hx
    intro μ₀ hμ₀
    have hμ₀_pos : 0 < μ₀ := lt_of_lt_of_le zero_lt_one hμ₀
    have hbnd := hx (fun i => Du i x) μ₀ hμ₀_pos
    -- `(1/μ₀ + 1/μ₀^τ) ≤ 2` on `μ₀ ≥ 1`.
    have hinv_le : (1 : ℝ) / μ₀ ≤ 1 := by
      rw [div_le_one hμ₀_pos]; exact hμ₀
    have hτ_nn : 0 ≤ hcong.τ := hcong.hτ.1
    have hμ₀τ_ge : (1 : ℝ) ≤ μ₀ ^ hcong.τ := Real.one_le_rpow hμ₀ hτ_nn
    have hμ₀τ_pos : 0 < μ₀ ^ hcong.τ :=
      Real.rpow_pos_of_pos hμ₀_pos hcong.τ
    have hinvτ_le : (1 : ℝ) / μ₀ ^ hcong.τ ≤ 1 := by
      rw [div_le_one hμ₀τ_pos]; exact hμ₀τ_ge
    have hsum_le : (1 / μ₀) + (1 / μ₀ ^ hcong.τ) ≤ 2 := by linarith
    have hP_nn : (0 : ℝ) ≤
        ‖(fun i => Du i x)‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) + 1 := by
      have : (0 : ℝ) ≤ ‖(fun i => Du i x)‖ ^
          (hcong.α * (1 + hcong.τ / hcong.β)) :=
        Real.rpow_nonneg (norm_nonneg _) _
      linarith
    have hsum_nn : (0 : ℝ) ≤ (1 / μ₀) + (1 / μ₀ ^ hcong.τ) := by
      have h1 : (0 : ℝ) ≤ 1 / μ₀ := by positivity
      have h2 : (0 : ℝ) ≤ 1 / μ₀ ^ hcong.τ := by positivity
      linarith
    -- `K₀·(1/μ₀ + 1/μ₀^τ)·(P+1) ≤ K₀·2·(P+1)`.
    have hmul_le :
        K₀ * ((1 / μ₀) + (1 / μ₀ ^ hcong.τ))
            * (‖(fun i => Du i x)‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) + 1)
          ≤ 2 * K₀
            * (‖(fun i => Du i x)‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) + 1) := by
      have hstep : K₀ * ((1 / μ₀) + (1 / μ₀ ^ hcong.τ)) ≤ K₀ * 2 :=
        mul_le_mul_of_nonneg_left hsum_le hK₀_pos.le
      calc K₀ * ((1 / μ₀) + (1 / μ₀ ^ hcong.τ))
              * (‖(fun i => Du i x)‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) + 1)
            ≤ (K₀ * 2)
              * (‖(fun i => Du i x)‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) + 1) :=
            mul_le_mul_of_nonneg_right hstep hP_nn
        _ = 2 * K₀
              * (‖(fun i => Du i x)‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) + 1) := by
            ring
    linarith
  -- Dispatch to the `_aesm` entry point with the derived riders.
  exact weak_is_strong_HJB_le_of_witnessData_powTransport_pos_aesm hmon hcong
    hpowα_eq hpowβ_eq hm_meas hu_meas hV_aesm hDu_meas hm_mem hu_mem hV_mem
    hDu_mem hae_m_pos hcont hae_anti hae_ne hVmeas hV hAty hKty hAeq hKeq hVI
    hw_m hw_u hw_Du hcoeWeak_Du

/-- **Nonneg-`delta` exponent-transported sibling of
`weak_is_strong_HJB_le_of_witnessData_powTransport_pos_aesm`** (child-D2b).

Identical `subst`/`cast`-collapse skeleton, but the a.e. strict positivity
`hae_m_pos` is replaced by mere non-negativity `hae_m_nn`, carrying the new
public riders `hHat0`/`hAgree`, and the discharge dispatches to
`weak_is_strong_HJB_le_of_witnessData_nonneg_delta`. The HJB conclusion is
exponent-free, so the transport remains statement-invariant. -/
theorem weak_is_strong_HJB_le_of_witnessData_powTransport_nonneg_delta
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    {αh βh : ℝ}
    (hpowα_eq : hcong.α = αh)
    (hpowβ_eq : hcong.β = βh)
    [Fact (1 ≤ ENNReal.ofReal (βh + 1))]
    [Fact (1 ≤ ENNReal.ofReal (αh * (βh + 1) / βh))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    [Fact (1 ≤ ENNReal.ofReal (αh * (hcong.β + 1) / hcong.β))]
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm_meas : Measurable m)
    (hu_meas : Measurable u)
    (hV_aesm : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hDu_meas : ∀ i, Measurable (Du i))
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (βh + 1)) m)
    (hu_mem : MemLpPer (d := d) (ENNReal.ofReal ((βh + 1) / βh)) u)
    (hV_mem : MemLpPer (d := d) (ENNReal.ofReal ((βh + 1) / βh)) V)
    (hDu_mem : ∀ i,
      MemLpPer (d := d)
        (ENNReal.ofReal (αh * (βh + 1) / βh)) (Du i))
    (hae_m_nn :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hcont :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hae_anti :
      ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
        AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0))
    (hae_ne :
      ∀ k : ℝ, 0 < k →
        ∀ᵐ x ∂(Measure.restrict volume (UnitCube d)),
          (muAuxSet k m u V Du H x).Nonempty)
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    {ε : ℝ}
    {A : congestionXBanach d
          (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh)) →
        StrongDual ℝ (congestionXBanach d
          (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh)))}
    {K : Set (congestionXBanach d
          (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh)))}
    {w : congestionXBanach d
          (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh))}
    (hAty :
      (congestionXBanach d (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) →
        StrongDual ℝ (congestionXBanach d (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))))
        =
      (congestionXBanach d (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh)) →
        StrongDual ℝ (congestionXBanach d (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh)))))
    (hKty :
      Set (congestionXBanach d (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))
        =
      Set (congestionXBanach d (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh))))
    (hAeq : A = cast hAty (congestionAepsiOpK hmon hcong hVmeas hV ε))
    (hKeq : K = cast hKty (congestionBanachK d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ))
    (hVI : ∀ v ∈ K, 0 ≤ A v (v - w))
    (hw_m : (⇑w.1 : (Fin d → ℝ) → ℝ) = m)
    (hw_u : (⇑w.2.1 : (Fin d → ℝ) → ℝ) = u)
    (hw_Du : ∀ i, (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ) = Du i)
    (hcoeWeak_Du : ∀ i,
      Periodic.HasWeakDerivPer (d := d) i
        (⇑w.2.1 : (Fin d → ℝ) → ℝ) (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ)) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      u x + H x (fun i => Du i x) (m x) - V x ≤ 0 := by
  subst hpowβ_eq
  subst hpowα_eq
  rw [cast_eq] at hAeq hKeq
  exact weak_is_strong_HJB_le_of_witnessData_nonneg_delta hmon hcong hHat0 hAgree
    hm_meas hu_meas hV_aesm hDu_meas hm_mem hu_mem hV_mem hDu_mem hae_m_nn hcont
    hae_anti hae_ne hVmeas hV hAeq hKeq hVI hw_m hw_u hw_Du hcoeWeak_Du

/-- **Auto-rider sibling of the `_nonneg_delta` entry point** (child-D2b).

Derives the three a.e.-on-`Ioi 0` riders `hcont`/`hae_anti`/`hae_ne` internally
from `hmon`/`hcong` (identical derivations to the `_pos_aesm_autoRiders`
sibling), then dispatches to
`weak_is_strong_HJB_le_of_witnessData_powTransport_nonneg_delta`, carrying the
new public riders `hHat0`/`hAgree` and the a.e. non-negativity `hae_m_nn`. -/
theorem weak_is_strong_HJB_le_of_witnessData_powTransport_nonneg_delta_autoRiders
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    {αh βh : ℝ}
    (hpowα_eq : hcong.α = αh)
    (hpowβ_eq : hcong.β = βh)
    [Fact (1 ≤ ENNReal.ofReal (βh + 1))]
    [Fact (1 ≤ ENNReal.ofReal (αh * (βh + 1) / βh))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    [Fact (1 ≤ ENNReal.ofReal (αh * (hcong.β + 1) / hcong.β))]
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm_meas : Measurable m)
    (hu_meas : Measurable u)
    (hV_aesm : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hDu_meas : ∀ i, Measurable (Du i))
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (βh + 1)) m)
    (hu_mem : MemLpPer (d := d) (ENNReal.ofReal ((βh + 1) / βh)) u)
    (hV_mem : MemLpPer (d := d) (ENNReal.ofReal ((βh + 1) / βh)) V)
    (hDu_mem : ∀ i,
      MemLpPer (d := d)
        (ENNReal.ofReal (αh * (βh + 1) / βh)) (Du i))
    (hae_m_nn :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hVmeas : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    {ε : ℝ}
    {A : congestionXBanach d
          (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh)) →
        StrongDual ℝ (congestionXBanach d
          (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh)))}
    {K : Set (congestionXBanach d
          (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh)))}
    {w : congestionXBanach d
          (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh))}
    (hAty :
      (congestionXBanach d (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) →
        StrongDual ℝ (congestionXBanach d (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))))
        =
      (congestionXBanach d (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh)) →
        StrongDual ℝ (congestionXBanach d (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh)))))
    (hKty :
      Set (congestionXBanach d (ENNReal.ofReal (hcong.β + 1))
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)))
        =
      Set (congestionXBanach d (ENNReal.ofReal (βh + 1))
          (ENNReal.ofReal (αh * (βh + 1) / βh))))
    (hAeq : A = cast hAty (congestionAepsiOpK hmon hcong hVmeas hV ε))
    (hKeq : K = cast hKty (congestionBanachK d
        (ENNReal.ofReal (hcong.β + 1))
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
        hcong.α hcong.β hcong.τ))
    (hVI : ∀ v ∈ K, 0 ≤ A v (v - w))
    (hw_m : (⇑w.1 : (Fin d → ℝ) → ℝ) = m)
    (hw_u : (⇑w.2.1 : (Fin d → ℝ) → ℝ) = u)
    (hw_Du : ∀ i, (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ) = Du i)
    (hcoeWeak_Du : ∀ i,
      Periodic.HasWeakDerivPer (d := d) i
        (⇑w.2.1 : (Fin d → ℝ) → ℝ) (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ)) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      u x + H x (fun i => Du i x) (m x) - V x ≤ 0 := by
  -- (1) `hcont`: section continuity on `Ioi 0` from joint a.e. continuity.
  have hcont :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0) := by
    filter_upwards [hmon.continuous_H_pm] with x hx
    have hg : Continuous (fun μ₀ : ℝ => ((fun i => Du i x), μ₀)) :=
      continuous_const.prodMk continuous_id
    have hmaps : Set.MapsTo (fun μ₀ : ℝ => ((fun i => Du i x), μ₀))
        (Set.Ioi (0 : ℝ)) {pm : (Fin d → ℝ) × ℝ | 0 < pm.2} := by
      intro μ₀ hμ₀
      exact hμ₀
    exact hx.comp hg.continuousOn hmaps
  -- (2) `hae_anti`: specialise `antitone_in_m hmon` at `p := Du · x`.
  have hae_anti :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0) := by
    filter_upwards [antitone_in_m hmon] with x hx
    exact hx (fun i => Du i x)
  -- (3) `hae_ne`: `muAux_nonempty_of_large_bound` with the static upper bound.
  obtain ⟨K₀, δ, hK₀_pos, hδ_pos, hUpper⟩ := H_upper_congestion_of_hmon hmon hcong
  have hae_ne :
      ∀ k : ℝ, 0 < k →
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          (muAuxSet k m u V Du H x).Nonempty := by
    intro k hk
    refine muAux_nonempty_of_large_bound (k := k) (m := m) (u := u) (V := V)
      (Du := Du) (H := H) (β := hcong.β) (δ := δ) hcong.hβ hδ_pos
      (f := fun x => 2 * K₀
        * (‖(fun i => Du i x)‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) + 1)) ?_
    filter_upwards [hUpper] with x hx
    intro μ₀ hμ₀
    have hμ₀_pos : 0 < μ₀ := lt_of_lt_of_le zero_lt_one hμ₀
    have hbnd := hx (fun i => Du i x) μ₀ hμ₀_pos
    have hinv_le : (1 : ℝ) / μ₀ ≤ 1 := by
      rw [div_le_one hμ₀_pos]; exact hμ₀
    have hτ_nn : 0 ≤ hcong.τ := hcong.hτ.1
    have hμ₀τ_ge : (1 : ℝ) ≤ μ₀ ^ hcong.τ := Real.one_le_rpow hμ₀ hτ_nn
    have hμ₀τ_pos : 0 < μ₀ ^ hcong.τ :=
      Real.rpow_pos_of_pos hμ₀_pos hcong.τ
    have hinvτ_le : (1 : ℝ) / μ₀ ^ hcong.τ ≤ 1 := by
      rw [div_le_one hμ₀τ_pos]; exact hμ₀τ_ge
    have hsum_le : (1 / μ₀) + (1 / μ₀ ^ hcong.τ) ≤ 2 := by linarith
    have hP_nn : (0 : ℝ) ≤
        ‖(fun i => Du i x)‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) + 1 := by
      have : (0 : ℝ) ≤ ‖(fun i => Du i x)‖ ^
          (hcong.α * (1 + hcong.τ / hcong.β)) :=
        Real.rpow_nonneg (norm_nonneg _) _
      linarith
    have hsum_nn : (0 : ℝ) ≤ (1 / μ₀) + (1 / μ₀ ^ hcong.τ) := by
      have h1 : (0 : ℝ) ≤ 1 / μ₀ := by positivity
      have h2 : (0 : ℝ) ≤ 1 / μ₀ ^ hcong.τ := by positivity
      linarith
    have hmul_le :
        K₀ * ((1 / μ₀) + (1 / μ₀ ^ hcong.τ))
            * (‖(fun i => Du i x)‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) + 1)
          ≤ 2 * K₀
            * (‖(fun i => Du i x)‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) + 1) := by
      have hstep : K₀ * ((1 / μ₀) + (1 / μ₀ ^ hcong.τ)) ≤ K₀ * 2 :=
        mul_le_mul_of_nonneg_left hsum_le hK₀_pos.le
      calc K₀ * ((1 / μ₀) + (1 / μ₀ ^ hcong.τ))
              * (‖(fun i => Du i x)‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) + 1)
            ≤ (K₀ * 2)
              * (‖(fun i => Du i x)‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) + 1) :=
            mul_le_mul_of_nonneg_right hstep hP_nn
        _ = 2 * K₀
              * (‖(fun i => Du i x)‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) + 1) := by
            ring
    linarith
  -- Dispatch to the `_nonneg_delta` transport wrapper with the derived riders.
  exact weak_is_strong_HJB_le_of_witnessData_powTransport_nonneg_delta hmon hcong
    hHat0 hAgree hpowα_eq hpowβ_eq hm_meas hu_meas hV_aesm hDu_meas hm_mem hu_mem
    hV_mem hDu_mem hae_m_nn hcont hae_anti hae_ne hVmeas hV hAty hKty hAeq hKeq hVI
    hw_m hw_u hw_Du hcoeWeak_Du

/-- **HJB-≥ witness wrapper** (`eq:congest.HJ0`, paper line 1398; T2 phase6
BB VIid-5c **child D1c**).

The `≥`-side analog of
`weak_is_strong_HJB_le_of_witnessData_powTransport_nonneg_delta_autoRiders`.
For every `k > 0`, it assembles the per-`k` riders that
`weak_is_strong_HJB_ge_at_k` (paper line 1511) consumes:

* the at-`k` analytical riders (`hae_cont`, `hae_ne`, `h_cont_all`) follow
  from the everywhere monotonicity / continuity / non-emptiness facts
  (`h_anti`, `h_cont_all`, `h_ne_all`) carried through the consumer chain;
* `h_diff_int` (`μ_re − m ∈ L¹`) is `muRe_sub_m_integrable`;
* `h_prod_int` (product integrability) is `muRe_prod_integrable`;
* `h_DCT` (`∫ (u+H(·,μ_re)−V)·(μ_re−m) ≤ 0`) is `h_DCT_producer_muRe`,
  which uses the δ-truncation transport passage (`h_step1` = the HJB-≤
  result) and the quotient dominator `muRe_quotient_dominator_memLp`.

The conclusion `h_perk : ∀ k > 0, ∀ᵐ x, 0 < m x → −k ≤ u + H(·,Du,m) − V`
is exactly the second argument `weak_is_strong_HJB_eq` consumes (alongside
the HJB-≤ result `h_step1`) to close the a.e. equality
`u + H(·,Du,m) − V = 0` on `{0 < m}`. -/
theorem weak_is_strong_HJB_ge_of_witnessData_powTransport_nonneg_delta_autoRiders
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    (hHat0 : Hamiltonian.HypothesisHat0 (d := d) H)
    (hAgree : Hamiltonian.H_zero_eq_Hext (d := d) H)
    [Fact (1 ≤ ENNReal.ofReal (hcong.β + 1))]
    [Fact (1 ≤ ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))]
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm_meas : Measurable m)
    (hu_meas : Measurable u)
    (hV_aesm : AEStronglyMeasurable V (volume.restrict (UnitCube d)))
    (hDu_meas : ∀ i, Measurable (Du i))
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) m)
    (hu_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) u)
    (hV_mem : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (hDu_mem : ∀ i,
      MemLpPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Du i))
    (hae_m_nn :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (h_step1 :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
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
        (⇑w.2.1 : (Fin d → ℝ) → ℝ) (⇑(w.2.2 i) : (Fin d → ℝ) → ℝ)) :
    ∀ k : ℝ, 0 < k →
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        0 < m x → -k ≤ u x + H x (fun i => Du i x) (m x) - V x := by
  intro k hk
  -- `Integrable m` (from `MemLpPer (β+1)`, `β+1 ≥ 1`, finite measure).
  have hm_int : Integrable m (volume.restrict (UnitCube d)) :=
    (hm_mem.toMemLp.mono_exponent
        (Fact.out : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (hcong.β + 1))).integrable le_rfl
  -- (1) `hae_cont`: section continuity on `Ioi 0` from joint a.e. continuity.
  have hae_cont :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ContinuousOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0) := by
    filter_upwards [hmon.continuous_H_pm] with x hx
    have hg : Continuous (fun μ₀ : ℝ => ((fun i => Du i x), μ₀)) :=
      continuous_const.prodMk continuous_id
    have hmaps : Set.MapsTo (fun μ₀ : ℝ => ((fun i => Du i x), μ₀))
        (Set.Ioi (0 : ℝ)) {pm : (Fin d → ℝ) × ℝ | 0 < pm.2} := fun μ₀ hμ₀ => hμ₀
    exact hx.comp hg.continuousOn hmaps
  -- (2) `hae_anti`: specialise `antitone_in_m hmon` at `p := Du · x`.
  have hae_anti :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        AntitoneOn (fun μ₀ : ℝ => H x (fun i => Du i x) μ₀) (Set.Ioi 0) := by
    filter_upwards [antitone_in_m hmon] with x hx
    exact hx (fun i => Du i x)
  -- (3) `hae_ne`: `muRe_nonempty_of_large_bound` with the static upper bound.
  obtain ⟨K₀, δ, hK₀_pos, hδ_pos, hUpper⟩ := H_upper_congestion_of_hmon hmon hcong
  have hae_ne :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        (muReSet k u V Du H x).Nonempty := by
    refine muRe_nonempty_of_large_bound (k := k) (u := u) (V := V)
      (Du := Du) (H := H) (β := hcong.β) (δ := δ) hcong.hβ hδ_pos
      (f := fun x => 2 * K₀
        * (‖(fun i => Du i x)‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) + 1)) ?_
    filter_upwards [hUpper] with x hx
    intro μ₀ hμ₀
    have hμ₀_pos : 0 < μ₀ := lt_of_lt_of_le zero_lt_one hμ₀
    have hbnd := hx (fun i => Du i x) μ₀ hμ₀_pos
    have hinv_le : (1 : ℝ) / μ₀ ≤ 1 := by
      rw [div_le_one hμ₀_pos]; exact hμ₀
    have hτ_nn : 0 ≤ hcong.τ := hcong.hτ.1
    have hμ₀τ_ge : (1 : ℝ) ≤ μ₀ ^ hcong.τ := Real.one_le_rpow hμ₀ hτ_nn
    have hμ₀τ_pos : 0 < μ₀ ^ hcong.τ := Real.rpow_pos_of_pos hμ₀_pos hcong.τ
    have hinvτ_le : (1 : ℝ) / μ₀ ^ hcong.τ ≤ 1 := by
      rw [div_le_one hμ₀τ_pos]; exact hμ₀τ_ge
    have hsum_le : (1 / μ₀) + (1 / μ₀ ^ hcong.τ) ≤ 2 := by linarith
    have hP_nn : (0 : ℝ) ≤
        ‖(fun i => Du i x)‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) + 1 := by
      have : (0 : ℝ) ≤ ‖(fun i => Du i x)‖ ^
          (hcong.α * (1 + hcong.τ / hcong.β)) :=
        Real.rpow_nonneg (norm_nonneg _) _
      linarith
    have hmul_le :
        K₀ * ((1 / μ₀) + (1 / μ₀ ^ hcong.τ))
            * (‖(fun i => Du i x)‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) + 1)
          ≤ 2 * K₀
            * (‖(fun i => Du i x)‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) + 1) := by
      have hstep : K₀ * ((1 / μ₀) + (1 / μ₀ ^ hcong.τ)) ≤ K₀ * 2 :=
        mul_le_mul_of_nonneg_left hsum_le hK₀_pos.le
      calc K₀ * ((1 / μ₀) + (1 / μ₀ ^ hcong.τ))
              * (‖(fun i => Du i x)‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) + 1)
            ≤ (K₀ * 2)
              * (‖(fun i => Du i x)‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) + 1) :=
            mul_le_mul_of_nonneg_right hstep hP_nn
        _ = 2 * K₀
              * (‖(fun i => Du i x)‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) + 1) := by
            ring
    linarith
  -- (4) `hae_HJB0`: boundary HJB-upper bound at `μ_re = 0` via (a:Hat0).
  have hae_HJB0 :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        muReInner k u V Du H x ≤ 0 →
          u x + H x (fun i => Du i x) 0 - V x ≤ -k := by
    filter_upwards [hae_anti, hae_ne, hHat0.exists_limit_at_zero, hAgree]
      with x hx_anti hx_ne hx_limit hx_agree hμle0
    have hwit := (muReInner_le_zero_iff_of_antitoneOn_Ioi hx_anti hx_ne).mp hμle0
    have hTendsto :
        Filter.Tendsto
          (fun ν : ℝ => ((H x (fun i => Du i x) ν : ℝ) : WithTop ℝ))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (Hamiltonian.H_at_zero H x (fun i => Du i x))) :=
      Hamiltonian.tendsto_Hext_zero_of_exists (hx_limit (fun i => Du i x))
    set b : ℝ := -k - u x + V x with hb_def
    by_cases hzero : ∃ n : ℕ, ∃ q : ℚ,
        (q : ℝ) = 0 ∧ 0 ≤ (q : ℝ) ∧ (q : ℝ) < 1 / ((n : ℝ) + 1) ∧
          u x + H x (fun i => Du i x) (q : ℝ) - V x ≤ -k
    · obtain ⟨_, _, hq_eq0, _, _, hHJB_q⟩ := hzero
      rw [hq_eq0] at hHJB_q; exact hHJB_q
    · have hPointwise : ∀ ν : ℝ, 0 < ν →
          u x + H x (fun i => Du i x) ν - V x ≤ -k := by
        intro ν hν
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hν
        obtain ⟨q, hq_nn, hq_hi, hHJB_q⟩ := hwit n
        have hq_lt_ν : (q : ℝ) < ν := by
          have h1 : (1 : ℝ) / ((n : ℝ) + 1) < ν := by
            simpa only [one_div] using hn
          exact lt_trans hq_hi h1
        have hq_pos : 0 < (q : ℝ) := by
          rcases eq_or_lt_of_le hq_nn with hq0 | hq_pos
          · exact absurd ⟨n, q, hq0.symm, hq_nn, hq_hi, hHJB_q⟩ hzero
          · exact hq_pos
        have hanti_le :
            H x (fun i => Du i x) ν ≤ H x (fun i => Du i x) (q : ℝ) :=
          hx_anti hq_pos (lt_trans hq_pos hq_lt_ν) hq_lt_ν.le
        linarith [hHJB_q]
      have hEv :
          ∀ᶠ ν in nhdsWithin 0 (Set.Ioi 0),
            ((H x (fun i => Du i x) ν : ℝ) : WithTop ℝ) ≤ ((b : ℝ) : WithTop ℝ) := by
        refine Filter.eventually_iff_exists_mem.mpr ⟨Set.Ioi (0 : ℝ),
          self_mem_nhdsWithin, fun ν hν => ?_⟩
        have := hPointwise ν hν
        have hle : H x (fun i => Du i x) ν ≤ b := by rw [hb_def]; linarith
        exact_mod_cast hle
      have hHext_le :
          Hamiltonian.H_at_zero H x (fun i => Du i x)
            ≤ ((b : ℝ) : WithTop ℝ) := le_of_tendsto hTendsto hEv
      have hAgree_x :
          ((H x (fun i => Du i x) 0 : ℝ) : WithTop ℝ)
            = Hamiltonian.H_at_zero H x (fun i => Du i x) := by
        rw [Hamiltonian.H_at_zero_def]; exact hx_agree (fun i => Du i x)
      have hraw_le :
          ((H x (fun i => Du i x) 0 : ℝ) : WithTop ℝ) ≤ ((b : ℝ) : WithTop ℝ) := by
        rw [hAgree_x]; exact hHext_le
      have hraw : H x (fun i => Du i x) 0 ≤ b := by exact_mod_cast hraw_le
      rw [hb_def] at hraw; linarith
  -- Null-measurability of the HJB level sets, then `AEMeasurable μ_re`.
  have hHJB_nmeas : ∀ a : ℝ,
      NullMeasurableSet { x : Fin d → ℝ |
        u x + H x (fun i => Du i x) a - V x ≤ -k }
        (volume.restrict (UnitCube d)) := by
    intro a
    have hDuvec : Measurable (fun x : Fin d → ℝ => fun i => Du i x) :=
      Measurable.of_eval hDu_meas
    have hprod : Measurable (fun x : Fin d → ℝ => (x, (fun i => Du i x), a)) :=
      measurable_id.prodMk (hDuvec.prodMk measurable_const)
    have hHcomp : Measurable (fun x : Fin d → ℝ => H x (fun i => Du i x) a) :=
      hmon.toRegularityH.measurable_H.comp hprod
    -- `V` is only a.e.-strongly-measurable, so build the sublevel set as a
    -- `NullMeasurableSet` of the a.e.-strongly-measurable HJB integrand.
    have hF_aesm : AEStronglyMeasurable
        (fun x : Fin d → ℝ => u x + H x (fun i => Du i x) a - V x)
        (volume.restrict (UnitCube d)) :=
      (hu_meas.aestronglyMeasurable.add hHcomp.aestronglyMeasurable).sub hV_aesm
    exact hF_aesm.nullMeasurableSet_le aestronglyMeasurable_const
  have hμre_aem : AEMeasurable (muRe k m u V Du H)
      (volume.restrict (UnitCube d)) :=
    muRe_measurable_of_Ioi0_of_m_nonneg_aesm hm_meas hHJB_nmeas hae_m_nn
      hae_anti hae_cont hae_ne
  have hμre_aesm : AEStronglyMeasurable (muRe k m u V Du H)
      (volume.restrict (UnitCube d)) := hμre_aem.aestronglyMeasurable
  -- `h_diff_int`: `μ_re − m ∈ L¹`.
  have h_diff_int :
      Integrable (fun x => muRe k m u V Du H x - m x)
        (volume.restrict (UnitCube d)) :=
    muRe_sub_m_integrable hμre_aesm hm_int hae_m_nn hae_ne
  -- `h_prod_int`: product integrability.
  have h_prod_int :
      Integrable
        (fun x =>
          (u x + H x (fun i => Du i x) (muRe k m u V Du H x) - V x)
            * (muRe k m u V Du H x - m x))
        (volume.restrict (UnitCube d)) :=
    muRe_prod_integrable hmon hcong hHat0 hAgree hk.le hm_meas hu_meas hV_aesm
      hDu_meas hm_mem hu_mem hV_mem hae_m_nn hae_anti hae_cont hae_ne
  -- `h_DCT`: the δ-truncation transport passage.
  have h_DCT :
      ∫ x in UnitCube d,
          (u x + H x (fun i => Du i x) (muRe k m u V Du H x) - V x)
            * (muRe k m u V Du H x - m x)
          ∂(volume : Measure (Fin d → ℝ)) ≤ 0 :=
    h_DCT_producer_muRe hmon hcong hHat0 hAgree hk hm_meas hu_meas hV_aesm
      hDu_meas hm_mem hu_mem hV_mem hDu_mem hae_m_nn hae_anti hae_cont hae_ne
      h_step1 hVmeas hV hAeq hKeq hVI hw_m hw_u hw_Du hcoeWeak_Du
  -- Dispatch to the per-`k` HJB lower bound.
  exact weak_is_strong_HJB_ge_at_k hk hae_cont hae_ne hae_HJB0 h_diff_int
    h_prod_int h_DCT

/-- **`eq:congest.HJ0` mass-identity assembly seam** (paper line 1398; T2
phase6 BB VIid-5c **child D2**).

The pure-assembly step that combines the two HJB half-bounds at the
Browder–Minty witness into the integrated `eq:congest.HJ0` identity. It
consumes:

* `h_step1` — the HJB-`≤ 0` a.e. inequality, the conclusion of the landed
  witness producer
  `weak_is_strong_HJB_le_of_witnessData_powTransport_nonneg_delta_autoRiders`
  (child E / the former `hcoeHJB_le` discharge);
* `h_perk` — the per-`k` HJB-`≥ −k` a.e. lower bound on `{m > 0}`, the
  conclusion of the landed witness producer
  `weak_is_strong_HJB_ge_of_witnessData_powTransport_nonneg_delta_autoRiders`
  (child D1c);
* `hm_nn` — a.e. nonnegativity of `m` (the witness's
  `(inputs.mε_pos_apriori …).mono (·.le)`, the same source the HJB-`≤`
  discharge uses).

It runs `weak_is_strong_HJB_eq h_step1 h_perk` to obtain the pointwise
`{m > 0}` equality `u + H(·,Du,m) − V = 0` a.e. (paper line 1398), then
`weak_is_strong_HJ0_mass_of_HJeq` to integrate it against the prefactor `m`
(which vanishes on the a.e. complement `{m = 0}`), yielding the mass
identity `∫_{[0,1]^d} m·(u + H(·,Du,m) − V) = 0`.

The conclusion is EXACTLY child C's `hHJ0` hypothesis shape
(`coeVI_identity_atWitness_of_closure`, Existence.lean ~3740) once the
witness data are plugged into the `m`/`u`/`Du` slots. -/
theorem weak_is_strong_HJ0_mass_of_step1_perk
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    (h_step1 :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        u x + H x (fun i => Du i x) (m x) - V x ≤ 0)
    (h_perk :
      ∀ k : ℝ, 0 < k →
        ∀ᵐ x ∂(volume.restrict (UnitCube d)),
          0 < m x → -k ≤ u x + H x (fun i => Du i x) (m x) - V x)
    (hm_nn :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x) :
    ∫ x in UnitCube d,
        m x * (u x + H x (fun i => Du i x) (m x) - V x)
        ∂(volume : Measure (Fin d → ℝ)) = 0 :=
  weak_is_strong_HJ0_mass_of_HJeq (weak_is_strong_HJB_eq h_step1 h_perk) hm_nn

/-- **`eq:congest.HJ0` mass identity at the Browder–Minty witness** (paper line
1398; T2 phase6 BB VIid-5c **child D2**, step 3).

The `_atWitness` specialisation of `weak_is_strong_HJ0_mass_of_step1_perk`: the
witness data `(m, u, Du) = (data.weakVI.choose.1, …2.1, …2.2)` are plugged into
the seam's `m`/`u`/`Du` slots, so the conclusion is EXACTLY the `hHJ0`
hypothesis shape consumed by `coeVI_identity_atWitness_of_closure`
(Existence.lean ~3740).

It takes, at the witness data slots:
* `h_step1` — the HJB-`≤ 0` a.e. inequality (conclusion of the landed witness
  producer
  `weak_is_strong_HJB_le_of_witnessData_powTransport_nonneg_delta_autoRiders`);
* `h_perk` — the per-`k` HJB-`≥ −k` a.e. lower bound on `{m > 0}` (conclusion
  of the landed witness producer
  `weak_is_strong_HJB_ge_of_witnessData_powTransport_nonneg_delta_autoRiders`);
* `hm_nn` — a.e. nonnegativity of `m` (the witness's
  `(inputs.mε_pos_apriori …).mono (·.le)`).

This is the landable deliverable of child D2; the discharge of child C's
`hHJ0` field inside the 5d field-removal is split out to child D3
(`…-D3-hcoeVI-field-removal`). -/
theorem congestion_HJ0_mass_atWitness_of_closure
    {γBar : ℝ}
    {betaBar betaBarPrime gammaBar : ℝ≥0∞}
    [Fact (1 ≤ betaBar)] [Fact (1 ≤ gammaBar)]
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {α β τ ε : ℝ}
    (data : Congestion.CongestionRegularizedSolutionData (d := d)
              (γBar := γBar) (betaBar := betaBar)
              (betaBarPrime := betaBarPrime) (gammaBar := gammaBar)
              V H DpH J α β τ ε
              (Periodic.LpPer betaBar d × Periodic.SobolevPerLp 1 gammaBar d))
    (h_step1 :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
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
    (hm_nn :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        0 ≤ (data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x) :
    ∫ x in UnitCube d,
        (data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x
          * ((data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ) x
              + H x (fun i =>
                    (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ) x)
                    ((data.weakVI.choose.1 : (Fin d → ℝ) → ℝ) x)
              - V x)
        ∂(volume : Measure (Fin d → ℝ)) = 0 :=
  weak_is_strong_HJ0_mass_of_step1_perk
    (V := V) (H := H)
    (Du := fun i => (data.weakVI.choose.2.2 i : (Fin d → ℝ) → ℝ))
    (m := (data.weakVI.choose.1 : (Fin d → ℝ) → ℝ))
    (u := (data.weakVI.choose.2.1 : (Fin d → ℝ) → ℝ))
    h_step1 h_perk hm_nn

/-! ## δ-truncation L¹ convergence toolkit (T2 phase6 BB VIid child-2)

DCT machinery for the `δ → 0` passage in the first-variation identity
(`eq:identity-congestion`, paper `lem:weak.is.strong`, lines 1524–1551). Working
with the generic truncation `m_δ = max(m, δ)` (= `mPerDelta m δ`, child-1) for the
*test* pair, we establish **L¹ convergence of the difference**
`∫ ‖f_{δ n} − f‖ → 0` for the `δ`-dependent integrands of the VI chain:

* `congestion_H_mdelta_tendsto_L1` — `H(x, p x, m_δ) → H(x, p x, m)` in `L¹`;
* `congestion_DpH_mdelta_tendsto_L1` — `D_pH(x, p x, m_δ) ⬝ q x → D_pH(x, p x, m) ⬝ q x`
  in `L¹`;
* `congestion_Vm_mdelta_tendsto_L1` — `V · m_δ → V · m` in `L¹` (Hölder dominator).

All three are phrased along an integer sequence `δSeq : ℕ → ℝ` with `δSeq → 0` (the
sequence form being what `MeasureTheory.tendsto_integral_of_dominated_convergence`
consumes, exactly as the `muAux_integral_tendsto` siblings above). The truncation
`m_δ ≥ δ > 0` keeps the limit point `m x > 0` interior to `Ioi 0`, so the on-`Ioi 0`
continuity of `H`/`D_pH` (`RegularityH.continuous_H_pm` / `continuous_DpH_pm`)
suffices; the `{m = 0}` boundary is *not* an issue here (that is the point of the
truncation). Each lemma takes an explicit integrable dominator hypothesis for the
difference (the `δ`-uniform growth bound `m_δ ≤ m + 1 ∈ L^β̄`, supplied downstream
by child-5 from `CongestionGrowthCore`).

The proof template is: apply `tendsto_integral_of_dominated_convergence` to the
nonnegative integrand `g n x := ‖f_{δ n} x − f x‖`, whose a.e. pointwise limit is
`0` (from `max (m x) (δSeq n) → m x` and continuity), with dominator `bound`; the
limiting integral `∫ 0 = 0` gives the L¹ statement. -/

/-- **L¹ convergence of `H` under δ-truncation** (paper lines 1545–1551, the DCT
passage `δ → 0`). For a fixed momentum field `p` and an a.e.-positive density `m`,
the truncated Hamiltonian `H(x, p x, m_δ)` converges to `H(x, p x, m)` in
`L¹(UnitCube d)` as `δ → 0⁺` (along any sequence `δSeq → 0`).

On `{0 < m x}` the limit point `m x` is interior to `Ioi 0` and the truncation
`max (m x) (δSeq n) ≥ m x > 0` stays in `Ioi 0`, so the on-`Ioi 0` continuity of
`H(x, p x, ·)` upgrades to `ContinuousAt` at `m x`, driving the pointwise limit.
The dominator for `‖H(x, p x, m_δ) − H(x, p x, m)‖` is supplied as a hypothesis
(downstream: the δ-uniform growth bound from `CongestionGrowthCore`). -/
theorem congestion_H_mdelta_tendsto_L1
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {m : (Fin d → ℝ) → ℝ}
    {p : (Fin d → ℝ) → (Fin d → ℝ)}
    {δSeq : ℕ → ℝ}
    (hδ_lim : Filter.Tendsto δSeq Filter.atTop (nhds (0 : ℝ)))
    (hm_pos : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hae_cont :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ContinuousOn (fun μ₀ : ℝ => H x (p x) μ₀) (Set.Ioi 0))
    (bound : (Fin d → ℝ) → ℝ)
    (hbound_int : Integrable bound (volume.restrict (UnitCube d)))
    (hmeas :
      ∀ n, AEStronglyMeasurable
        (fun x => ‖H x (p x) (mPerDelta m (δSeq n) x) - H x (p x) (m x)‖)
        (volume.restrict (UnitCube d)))
    (hbound :
      ∀ n, ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖‖H x (p x) (mPerDelta m (δSeq n) x) - H x (p x) (m x)‖‖ ≤ bound x) :
    Filter.Tendsto
      (fun n =>
        ∫ x in UnitCube d,
            ‖H x (p x) (mPerDelta m (δSeq n) x) - H x (p x) (m x)‖
            ∂(volume : Measure (Fin d → ℝ)))
      Filter.atTop (nhds (0 : ℝ)) := by
  -- Pointwise a.e. limit of `‖H(x, p x, m_δ) − H(x, p x, m)‖` to `0`.
  have h_lim :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        Filter.Tendsto
          (fun n => ‖H x (p x) (mPerDelta m (δSeq n) x) - H x (p x) (m x)‖)
          Filter.atTop (nhds (0 : ℝ)) := by
    filter_upwards [hm_pos, hae_cont] with x hx_mpos hx_cont
    have hmx_nn : (0 : ℝ) ≤ m x := hx_mpos.le
    -- `max (m x) (δSeq n) → m x` since `δSeq → 0` and `m x ≥ 0`.
    have h_max_lim :
        Filter.Tendsto (fun n => mPerDelta m (δSeq n) x) Filter.atTop
          (nhds (m x)) := by
      have h0 : max (m x) (0 : ℝ) = m x := max_eq_left hmx_nn
      have := (tendsto_const_nhds (x := m x)).max hδ_lim
      simpa [mPerDelta_def, h0] using this
    -- On-`Ioi 0` continuity upgrades to `ContinuousAt` at the interior point `m x`.
    have hmx_mem : m x ∈ Set.Ioi (0 : ℝ) := hx_mpos
    have h_cont_at : ContinuousAt (fun μ₀ : ℝ => H x (p x) μ₀) (m x) :=
      (hx_cont (m x) hmx_mem).continuousAt (isOpen_Ioi.mem_nhds hmx_mem)
    have h_H_lim :
        Filter.Tendsto
          (fun n => H x (p x) (mPerDelta m (δSeq n) x))
          Filter.atTop (nhds (H x (p x) (m x))) :=
      (h_cont_at.tendsto).comp h_max_lim
    have h_sub :
        Filter.Tendsto
          (fun n => H x (p x) (mPerDelta m (δSeq n) x) - H x (p x) (m x))
          Filter.atTop (nhds (0 : ℝ)) := by
      have := h_H_lim.sub (tendsto_const_nhds (x := H x (p x) (m x)))
      simpa using this
    have hc : Filter.Tendsto (fun y : ℝ => ‖y‖) (nhds 0) (nhds ‖(0 : ℝ)‖) :=
      (continuous_norm.tendsto 0)
    simpa using! hc.comp h_sub
  -- Apply DCT: the integral of the norm difference tends to `∫ 0 = 0`.
  have := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (UnitCube d))
    (F := fun n x => ‖H x (p x) (mPerDelta m (δSeq n) x) - H x (p x) (m x)‖)
    (f := fun _ => (0 : ℝ))
    bound hmeas hbound_int hbound h_lim
  simpa using this

/-- **L¹ convergence of `D_pH ⬝ q` under δ-truncation** (paper lines 1545–1551).
For a fixed momentum field `p` and test direction `q`, the truncated dot product
`D_pH(x, p x, m_δ) ⬝ q x` converges to `D_pH(x, p x, m) ⬝ q x` in `L¹(UnitCube d)`
as `δ → 0⁺`, on `{0 < m x}` (interior to `Ioi 0`), via on-`Ioi 0` continuity of
`D_pH(x, p x, ·)`. The dominator is supplied as a hypothesis. -/
theorem congestion_DpH_mdelta_tendsto_L1
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {m : (Fin d → ℝ) → ℝ}
    {p q : (Fin d → ℝ) → (Fin d → ℝ)}
    {δSeq : ℕ → ℝ}
    (hδ_lim : Filter.Tendsto δSeq Filter.atTop (nhds (0 : ℝ)))
    (hm_pos : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hae_cont :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ContinuousOn (fun μ₀ : ℝ => DpH x (p x) μ₀) (Set.Ioi 0))
    (bound : (Fin d → ℝ) → ℝ)
    (hbound_int : Integrable bound (volume.restrict (UnitCube d)))
    (hmeas :
      ∀ n, AEStronglyMeasurable
        (fun x =>
          ‖DpH x (p x) (mPerDelta m (δSeq n) x) ⬝ q x - DpH x (p x) (m x) ⬝ q x‖)
        (volume.restrict (UnitCube d)))
    (hbound :
      ∀ n, ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖‖DpH x (p x) (mPerDelta m (δSeq n) x) ⬝ q x
            - DpH x (p x) (m x) ⬝ q x‖‖ ≤ bound x) :
    Filter.Tendsto
      (fun n =>
        ∫ x in UnitCube d,
            ‖DpH x (p x) (mPerDelta m (δSeq n) x) ⬝ q x
              - DpH x (p x) (m x) ⬝ q x‖
            ∂(volume : Measure (Fin d → ℝ)))
      Filter.atTop (nhds (0 : ℝ)) := by
  have h_lim :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        Filter.Tendsto
          (fun n =>
            ‖DpH x (p x) (mPerDelta m (δSeq n) x) ⬝ q x
              - DpH x (p x) (m x) ⬝ q x‖)
          Filter.atTop (nhds (0 : ℝ)) := by
    filter_upwards [hm_pos, hae_cont] with x hx_mpos hx_cont
    have hmx_nn : (0 : ℝ) ≤ m x := hx_mpos.le
    have h_max_lim :
        Filter.Tendsto (fun n => mPerDelta m (δSeq n) x) Filter.atTop
          (nhds (m x)) := by
      have h0 : max (m x) (0 : ℝ) = m x := max_eq_left hmx_nn
      have := (tendsto_const_nhds (x := m x)).max hδ_lim
      simpa [mPerDelta_def, h0] using this
    have hmx_mem : m x ∈ Set.Ioi (0 : ℝ) := hx_mpos
    have h_cont_at : ContinuousAt (fun μ₀ : ℝ => DpH x (p x) μ₀) (m x) :=
      (hx_cont (m x) hmx_mem).continuousAt (isOpen_Ioi.mem_nhds hmx_mem)
    -- Each coordinate of `D_pH(x, p x, ·)` tends to its value at `m x`.
    have h_DpH_lim :
        Filter.Tendsto
          (fun n => DpH x (p x) (mPerDelta m (δSeq n) x))
          Filter.atTop (nhds (DpH x (p x) (m x))) :=
      (h_cont_at.tendsto).comp h_max_lim
    -- The dot product `· ⬝ q x = ∑ i, (·) i * q x i` is a finite sum of products,
    -- continuous in the first slot, so the dot products tend.
    have h_dot_lim :
        Filter.Tendsto
          (fun n => DpH x (p x) (mPerDelta m (δSeq n) x) ⬝ q x)
          Filter.atTop (nhds (DpH x (p x) (m x) ⬝ q x)) := by
      unfold StationaryMFG.Hamiltonian.euclideanDot
      apply tendsto_finset_sum
      intro i _
      have hi : Filter.Tendsto
          (fun n => (DpH x (p x) (mPerDelta m (δSeq n) x)) i)
          Filter.atTop (nhds ((DpH x (p x) (m x)) i)) :=
        (continuous_apply i).continuousAt.tendsto.comp h_DpH_lim
      exact hi.mul (tendsto_const_nhds (x := q x i))
    have h_sub :
        Filter.Tendsto
          (fun n => DpH x (p x) (mPerDelta m (δSeq n) x) ⬝ q x
            - DpH x (p x) (m x) ⬝ q x)
          Filter.atTop (nhds (0 : ℝ)) := by
      have := h_dot_lim.sub (tendsto_const_nhds (x := DpH x (p x) (m x) ⬝ q x))
      simpa using this
    have hc : Filter.Tendsto (fun y : ℝ => ‖y‖) (nhds 0) (nhds ‖(0 : ℝ)‖) :=
      (continuous_norm.tendsto 0)
    simpa using! hc.comp h_sub
  have := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (UnitCube d))
    (F := fun n x =>
      ‖DpH x (p x) (mPerDelta m (δSeq n) x) ⬝ q x - DpH x (p x) (m x) ⬝ q x‖)
    (f := fun _ => (0 : ℝ))
    bound hmeas hbound_int hbound h_lim
  simpa using this

/-- **L¹ convergence of `V · m_δ` under δ-truncation** (paper lines 1545–1551,
the `V·m_δ → V·m` term, controlled by Hölder `|V| ∈ L^{β̄'}`, `m_δ ∈ L^{β+1}`).

Here no continuity is needed: `‖V x · m_δ x − V x · m x‖ = |V x| · |m_δ x − m x|`
and for `0 ≤ δSeq n ≤ 1` (eventually, since `δSeq → 0`) with `0 ≤ m x` we have
`0 ≤ m_δ x − m x ≤ 1`, so the difference norm is dominated by `|V x|`, integrable
by hypothesis. The pointwise limit is `0` since `m_δ x − m x → 0` a.e. (child-1's
`mPerDelta_sub_tendsto_ae_pt`). -/
theorem congestion_Vm_mdelta_tendsto_L1
    {V : (Fin d → ℝ) → ℝ}
    {m : (Fin d → ℝ) → ℝ}
    {δSeq : ℕ → ℝ}
    (hδ_lim : Filter.Tendsto δSeq Filter.atTop (nhds (0 : ℝ)))
    (hδ_pos : ∀ n, 0 < δSeq n)
    (hm_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hV_int : Integrable V (volume.restrict (UnitCube d)))
    (hmeas :
      ∀ n, AEStronglyMeasurable
        (fun x => ‖V x * mPerDelta m (δSeq n) x - V x * m x‖)
        (volume.restrict (UnitCube d))) :
    Filter.Tendsto
      (fun n =>
        ∫ x in UnitCube d,
            ‖V x * mPerDelta m (δSeq n) x - V x * m x‖
            ∂(volume : Measure (Fin d → ℝ)))
      Filter.atTop (nhds (0 : ℝ)) := by
  -- Dominator `‖V‖`, integrable from `V ∈ L¹`.
  have hbound_int : Integrable (fun x => ‖V x‖) (volume.restrict (UnitCube d)) :=
    hV_int.norm
  -- The difference is eventually (for `δSeq n ≤ 1`) bounded by `‖V‖` a.e.;
  -- but we need the bound for *all* `n`, so split using a tail. We instead
  -- apply DCT after shifting to a tail where `δSeq n ≤ 1`.
  have hδ_le1 : ∀ᶠ n in Filter.atTop, δSeq n ≤ 1 := by
    have hmem : ∀ᶠ n in Filter.atTop, δSeq n ∈ Set.Iic (1 : ℝ) :=
      hδ_lim.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))
    simpa [Set.mem_Iic] using hmem
  obtain ⟨N, hN⟩ := hδ_le1.exists_forall_of_atTop
  -- Pointwise a.e. limit of `‖V·m_δ − V·m‖ → 0`.
  have h_lim :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        Filter.Tendsto
          (fun n => ‖V x * mPerDelta m (δSeq n) x - V x * m x‖)
          Filter.atTop (nhds (0 : ℝ)) := by
    filter_upwards [hm_nn] with x hmx
    -- `m_δ x − m x → 0`, so `V x · (m_δ − m) → 0`.
    have h_sub_ae := mPerDelta_sub_tendsto_ae_pt (m := m) (x := x) hmx
    have h_seq : Filter.Tendsto (fun n => mPerDelta m (δSeq n) x - m x)
        Filter.atTop (nhds (0 : ℝ)) := by
      have hδ_seq : Filter.Tendsto δSeq Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) := by
        rw [tendsto_nhdsWithin_iff]
        exact ⟨hδ_lim, Filter.Eventually.of_forall hδ_pos⟩
      exact h_sub_ae.comp hδ_seq
    have h_mul : Filter.Tendsto
        (fun n => V x * mPerDelta m (δSeq n) x - V x * m x)
        Filter.atTop (nhds (0 : ℝ)) := by
      have hmul := (tendsto_const_nhds (x := V x)).mul h_seq
      simp only [mul_zero] at hmul
      refine hmul.congr (fun n => ?_)
      rw [mul_sub]
    have hc : Filter.Tendsto (fun y : ℝ => ‖y‖) (nhds 0) (nhds ‖(0 : ℝ)‖) :=
      (continuous_norm.tendsto 0)
    have hnorm := hc.comp h_mul
    simpa [Function.comp] using! hnorm
  -- Domination on the tail `n ↦ n + N` (where `δSeq (n+N) ≤ 1`), then undo shift.
  rw [← Filter.tendsto_add_atTop_iff_nat N]
  have hbase :=
    MeasureTheory.tendsto_integral_of_dominated_convergence
      (μ := volume.restrict (UnitCube d))
      (F := fun n x => ‖V x * mPerDelta m (δSeq (n + N)) x - V x * m x‖)
      (f := fun _ => (0 : ℝ))
      (bound := fun x => ‖V x‖)
      (fun n => hmeas (n + N))
      hbound_int
      ?_ ?_
  · simpa using hbase
  · -- Domination: `‖‖V·m_δ − V·m‖‖ ≤ ‖V‖` on the tail.
    intro n
    have hle1 : δSeq (n + N) ≤ 1 := hN (n + N) (Nat.le_add_left N n)
    have hpos : 0 < δSeq (n + N) := hδ_pos (n + N)
    filter_upwards [hm_nn] with x hmx
    have h_diff_nn : 0 ≤ mPerDelta m (δSeq (n + N)) x - m x := by
      have := le_mPerDelta m (δSeq (n + N)) x; linarith
    have h_diff_le : mPerDelta m (δSeq (n + N)) x - m x ≤ 1 := by
      have := mPerDelta_le_add hpos.le hmx; linarith
    have h_eq : V x * mPerDelta m (δSeq (n + N)) x - V x * m x
        = V x * (mPerDelta m (δSeq (n + N)) x - m x) := by ring
    rw [norm_norm, h_eq, norm_mul]
    calc ‖V x‖ * ‖mPerDelta m (δSeq (n + N)) x - m x‖
        ≤ ‖V x‖ * 1 := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          rw [Real.norm_eq_abs, abs_of_nonneg h_diff_nn]
          exact h_diff_le
      _ = ‖V x‖ := by ring
  · -- A.e. pointwise convergence on the shifted tail.
    have hshift : Filter.Tendsto (fun n => δSeq (n + N)) Filter.atTop (nhds 0) :=
      hδ_lim.comp (Filter.tendsto_add_atTop_nat N)
    filter_upwards [hm_nn] with x hmx
    -- Reuse the (un-shifted) pointwise limit, restated for the shifted sequence.
    have h_sub_ae := mPerDelta_sub_tendsto_ae_pt (m := m) (x := x) hmx
    have hδ_seq : Filter.Tendsto (fun n => δSeq (n + N)) Filter.atTop
        (nhdsWithin 0 (Set.Ioi 0)) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨hshift, Filter.Eventually.of_forall (fun n => hδ_pos (n + N))⟩
    have h_seq : Filter.Tendsto (fun n => mPerDelta m (δSeq (n + N)) x - m x)
        Filter.atTop (nhds (0 : ℝ)) := h_sub_ae.comp hδ_seq
    have h_mul : Filter.Tendsto
        (fun n => V x * mPerDelta m (δSeq (n + N)) x - V x * m x)
        Filter.atTop (nhds (0 : ℝ)) := by
      have hmul := (tendsto_const_nhds (x := V x)).mul h_seq
      simp only [mul_zero] at hmul
      refine hmul.congr (fun n => ?_)
      rw [mul_sub]
    have hc : Filter.Tendsto (fun y : ℝ => ‖y‖) (nhds 0) (nhds ‖(0 : ℝ)‖) :=
      (continuous_norm.tendsto 0)
    have hnorm := hc.comp h_mul
    simpa [Function.comp] using! hnorm

/-- **L¹ convergence of the `m`-prefactored `D_pH ⬝ q` under δ-truncation**
(paper lines 1545–1551, child-4b-ii). For a fixed momentum field `p` and test
direction `q`, the truncated **mass-weighted** flux
`m_δ · (D_pH(x, p x, m_δ) ⬝ q x)` converges to `m · (D_pH(x, p x, m) ⬝ q x)` in
`L¹(UnitCube d)` as `δ → 0⁺`, on `{0 < m x}`.

This is a product convergence: `m_δ → m` a.e. (child-1's
`mPerDelta_sub_tendsto_ae_pt`) **and** the dot product
`D_pH(x, p x, m_δ) ⬝ q x → D_pH(x, p x, m) ⬝ q x` via on-`Ioi 0` continuity of
`D_pH(x, p x, ·)` (exactly the limit driving
`congestion_DpH_mdelta_tendsto_L1`). The product of the two convergent
sequences tends to `m · (D_pH(x, p x, m) ⬝ q x)`; the difference norm tends to
`0` and is dominated by the supplied integrable `bound` (downstream: the
`δ`-uniform `m_δ ≤ m + 1` bound times the `D_pH` growth bound). -/
theorem congestion_mDpH_mdelta_tendsto_L1
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {m : (Fin d → ℝ) → ℝ}
    {p q : (Fin d → ℝ) → (Fin d → ℝ)}
    {δSeq : ℕ → ℝ}
    (hδ_lim : Filter.Tendsto δSeq Filter.atTop (nhds (0 : ℝ)))
    (hδ_pos : ∀ n, 0 < δSeq n)
    (hm_pos : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 < m x)
    (hae_cont :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ContinuousOn (fun μ₀ : ℝ => DpH x (p x) μ₀) (Set.Ioi 0))
    (bound : (Fin d → ℝ) → ℝ)
    (hbound_int : Integrable bound (volume.restrict (UnitCube d)))
    (hmeas :
      ∀ n, AEStronglyMeasurable
        (fun x =>
          ‖mPerDelta m (δSeq n) x * (DpH x (p x) (mPerDelta m (δSeq n) x) ⬝ q x)
            - m x * (DpH x (p x) (m x) ⬝ q x)‖)
        (volume.restrict (UnitCube d)))
    (hbound :
      ∀ n, ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖‖mPerDelta m (δSeq n) x * (DpH x (p x) (mPerDelta m (δSeq n) x) ⬝ q x)
            - m x * (DpH x (p x) (m x) ⬝ q x)‖‖ ≤ bound x) :
    Filter.Tendsto
      (fun n =>
        ∫ x in UnitCube d,
            ‖mPerDelta m (δSeq n) x * (DpH x (p x) (mPerDelta m (δSeq n) x) ⬝ q x)
              - m x * (DpH x (p x) (m x) ⬝ q x)‖
            ∂(volume : Measure (Fin d → ℝ)))
      Filter.atTop (nhds (0 : ℝ)) := by
  have h_lim :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        Filter.Tendsto
          (fun n =>
            ‖mPerDelta m (δSeq n) x * (DpH x (p x) (mPerDelta m (δSeq n) x) ⬝ q x)
              - m x * (DpH x (p x) (m x) ⬝ q x)‖)
          Filter.atTop (nhds (0 : ℝ)) := by
    filter_upwards [hm_pos, hae_cont] with x hx_mpos hx_cont
    have hmx_nn : (0 : ℝ) ≤ m x := hx_mpos.le
    -- `m_δ → m` a.e. pointwise (child-1).
    have h_max_lim :
        Filter.Tendsto (fun n => mPerDelta m (δSeq n) x) Filter.atTop
          (nhds (m x)) := by
      have h0 : max (m x) (0 : ℝ) = m x := max_eq_left hmx_nn
      have := (tendsto_const_nhds (x := m x)).max hδ_lim
      simpa [mPerDelta_def, h0] using this
    -- On-`Ioi 0` continuity → `ContinuousAt` at the interior point `m x`.
    have hmx_mem : m x ∈ Set.Ioi (0 : ℝ) := hx_mpos
    have h_cont_at : ContinuousAt (fun μ₀ : ℝ => DpH x (p x) μ₀) (m x) :=
      (hx_cont (m x) hmx_mem).continuousAt (isOpen_Ioi.mem_nhds hmx_mem)
    have h_DpH_lim :
        Filter.Tendsto
          (fun n => DpH x (p x) (mPerDelta m (δSeq n) x))
          Filter.atTop (nhds (DpH x (p x) (m x))) :=
      (h_cont_at.tendsto).comp h_max_lim
    -- The dot product tends (finite sum of coordinatewise products).
    have h_dot_lim :
        Filter.Tendsto
          (fun n => DpH x (p x) (mPerDelta m (δSeq n) x) ⬝ q x)
          Filter.atTop (nhds (DpH x (p x) (m x) ⬝ q x)) := by
      unfold StationaryMFG.Hamiltonian.euclideanDot
      apply tendsto_finset_sum
      intro i _
      have hi : Filter.Tendsto
          (fun n => (DpH x (p x) (mPerDelta m (δSeq n) x)) i)
          Filter.atTop (nhds ((DpH x (p x) (m x)) i)) :=
        (continuous_apply i).continuousAt.tendsto.comp h_DpH_lim
      exact hi.mul (tendsto_const_nhds (x := q x i))
    -- Product of the two convergent sequences `m_δ` and `D_pH(…,m_δ) ⬝ q`.
    have h_prod_lim :
        Filter.Tendsto
          (fun n =>
            mPerDelta m (δSeq n) x * (DpH x (p x) (mPerDelta m (δSeq n) x) ⬝ q x))
          Filter.atTop (nhds (m x * (DpH x (p x) (m x) ⬝ q x))) :=
      h_max_lim.mul h_dot_lim
    have h_sub :
        Filter.Tendsto
          (fun n =>
            mPerDelta m (δSeq n) x * (DpH x (p x) (mPerDelta m (δSeq n) x) ⬝ q x)
              - m x * (DpH x (p x) (m x) ⬝ q x))
          Filter.atTop (nhds (0 : ℝ)) := by
      have := h_prod_lim.sub
        (tendsto_const_nhds (x := m x * (DpH x (p x) (m x) ⬝ q x)))
      simpa using this
    have hc : Filter.Tendsto (fun y : ℝ => ‖y‖) (nhds 0) (nhds ‖(0 : ℝ)‖) :=
      (continuous_norm.tendsto 0)
    simpa using! hc.comp h_sub
  have := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (UnitCube d))
    (F := fun n x =>
      ‖mPerDelta m (δSeq n) x * (DpH x (p x) (mPerDelta m (δSeq n) x) ⬝ q x)
        - m x * (DpH x (p x) (m x) ⬝ q x)‖)
    (f := fun _ => (0 : ℝ))
    bound hmeas hbound_int hbound h_lim
  simpa using this

/-- **L¹ convergence of the `m`-prefactored `D_pH ⬝ q` under δ-truncation, to
the closed-half-line extension `J = mD_pH`** (paper lines 1545–1551, child-5a-ii).

This is the `m ≥ 0` analogue of `congestion_mDpH_mdelta_tendsto_L1`. The latter
needs strict positivity `0 < m x` because it identifies the δ → 0 limit with the
product `m x · (D_pH(x, p x, m x) ⬝ q x)`, using on-`Ioi 0` continuity of
`D_pH(x, p x, ·)` at the interior point `m x`. At the boundary `m x = 0` that
product is `0`, but the *true* δ-limit of the mass-weighted flux is
`J(x, p x, 0) ⬝ q x` (the paper's `mD_pH` extension), which need not vanish.

So the honest, `m ≥ 0`-only statement targets the extension `J`: as `δ → 0⁺`,
`m_δ · (D_pH(x, p x, m_δ) ⬝ q x)` converges to `J(x, p x, m x) ⬝ q x` in
`L¹(UnitCube d)`, using **only** a.e. non-negativity `0 ≤ m x` and the bundled
`(a:mDpHat0)` data:
* `hJ_of_pos`: `J(x, p, m) = m • D_pH(x, p, m)` for `m > 0` — so for `δ > 0`,
  `m_δ ≥ δ > 0` gives `m_δ · D_pH(x, p x, m_δ) = J(x, p x, m_δ)`;
* `hae_cont_J`: a.e. joint continuity of `(p, m) ↦ J(x, p, m)` on `{m ≥ 0}`,
  which upgrades to one-variable continuity in `m` at the point `m x ≥ 0` (a
  boundary or interior point of `[0, ∞)`), so `J(x, p x, m_δ) → J(x, p x, m x)`.

The dominator is supplied as a hypothesis (downstream: the `δ`-uniform
`m_δ ≤ m + 1` flux growth bound). -/
theorem congestion_mDpH_mdelta_tendsto_L1_to_J
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {m : (Fin d → ℝ) → ℝ}
    {p q : (Fin d → ℝ) → (Fin d → ℝ)}
    {δSeq : ℕ → ℝ}
    (hδ_lim : Filter.Tendsto δSeq Filter.atTop (nhds (0 : ℝ)))
    (hδ_pos : ∀ n, 0 < δSeq n)
    (hm_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hJ_of_pos : ∀ x p m, 0 < m → J x p m = m • DpH x p m)
    (hae_cont_J :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ContinuousOn (fun pm : (Fin d → ℝ) × ℝ => J x pm.1 pm.2)
          {pm | 0 ≤ pm.2})
    (bound : (Fin d → ℝ) → ℝ)
    (hbound_int : Integrable bound (volume.restrict (UnitCube d)))
    (hmeas :
      ∀ n, AEStronglyMeasurable
        (fun x =>
          ‖mPerDelta m (δSeq n) x * (DpH x (p x) (mPerDelta m (δSeq n) x) ⬝ q x)
            - J x (p x) (m x) ⬝ q x‖)
        (volume.restrict (UnitCube d)))
    (hbound :
      ∀ n, ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖‖mPerDelta m (δSeq n) x * (DpH x (p x) (mPerDelta m (δSeq n) x) ⬝ q x)
            - J x (p x) (m x) ⬝ q x‖‖ ≤ bound x) :
    Filter.Tendsto
      (fun n =>
        ∫ x in UnitCube d,
            ‖mPerDelta m (δSeq n) x * (DpH x (p x) (mPerDelta m (δSeq n) x) ⬝ q x)
              - J x (p x) (m x) ⬝ q x‖
            ∂(volume : Measure (Fin d → ℝ)))
      Filter.atTop (nhds (0 : ℝ)) := by
  have h_lim :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        Filter.Tendsto
          (fun n =>
            ‖mPerDelta m (δSeq n) x * (DpH x (p x) (mPerDelta m (δSeq n) x) ⬝ q x)
              - J x (p x) (m x) ⬝ q x‖)
          Filter.atTop (nhds (0 : ℝ)) := by
    filter_upwards [hm_nn, hae_cont_J] with x hmx_nn hx_contJ
    -- `m_δ → m` a.e. pointwise (child-1), with `m_δ ≥ δ > 0`.
    have h_max_lim :
        Filter.Tendsto (fun n => mPerDelta m (δSeq n) x) Filter.atTop
          (nhds (m x)) := by
      have h0 : max (m x) (0 : ℝ) = m x := max_eq_left hmx_nn
      have := (tendsto_const_nhds (x := m x)).max hδ_lim
      simpa [mPerDelta_def, h0] using this
    -- The pair `(p x, m_δ) → (p x, m x)` stays in `{m ≥ 0}`.
    have h_pair_lim :
        Filter.Tendsto (fun n => ((p x), mPerDelta m (δSeq n) x))
          Filter.atTop (nhds ((p x), m x)) :=
      Filter.Tendsto.prodMk_nhds tendsto_const_nhds h_max_lim
    have h_pair_mem : ∀ n,
        ((p x), mPerDelta m (δSeq n) x) ∈ {pm : (Fin d → ℝ) × ℝ | 0 ≤ pm.2} := by
      intro n
      have := mPerDelta_pos (hδ_pos n) m x
      exact this.le
    have hx_mem : ((p x), m x) ∈ {pm : (Fin d → ℝ) × ℝ | 0 ≤ pm.2} := hmx_nn
    -- `J(x, p x, m_δ) → J(x, p x, m x)` by joint continuity on `{m ≥ 0}`.
    have h_J_lim :
        Filter.Tendsto
          (fun n => J x (p x) (mPerDelta m (δSeq n) x))
          Filter.atTop (nhds (J x (p x) (m x))) := by
      have hcontWithin :
          Filter.Tendsto (fun pm : (Fin d → ℝ) × ℝ => J x pm.1 pm.2)
            (nhdsWithin ((p x), m x) {pm | 0 ≤ pm.2})
            (nhds (J x (p x) (m x))) :=
        hx_contJ ((p x), m x) hx_mem
      have h_within :
          Filter.Tendsto (fun n => ((p x), mPerDelta m (δSeq n) x))
            Filter.atTop
            (nhdsWithin ((p x), m x) {pm | 0 ≤ pm.2}) :=
        tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
          h_pair_lim (Filter.Eventually.of_forall h_pair_mem)
      exact hcontWithin.comp h_within
    -- Rewrite `m_δ · D_pH(…, m_δ)` as `J(x, p x, m_δ)` (since `m_δ > 0`).
    have h_flux_eq : ∀ n,
        mPerDelta m (δSeq n) x * (DpH x (p x) (mPerDelta m (δSeq n) x) ⬝ q x)
          = (J x (p x) (mPerDelta m (δSeq n) x)) ⬝ q x := by
      intro n
      have hpos := mPerDelta_pos (hδ_pos n) m x
      rw [hJ_of_pos x (p x) (mPerDelta m (δSeq n) x) hpos]
      -- `(m_δ • D_pH) ⬝ q = m_δ * (D_pH ⬝ q)`.
      unfold StationaryMFG.Hamiltonian.euclideanDot
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp [Pi.smul_apply, smul_eq_mul]; ring
    -- The dot product `J(x, p x, ·) ⬝ q x` is continuous in `J`, so it tends.
    have h_dot_lim :
        Filter.Tendsto
          (fun n => (J x (p x) (mPerDelta m (δSeq n) x)) ⬝ q x)
          Filter.atTop (nhds ((J x (p x) (m x)) ⬝ q x)) := by
      unfold StationaryMFG.Hamiltonian.euclideanDot
      apply tendsto_finset_sum
      intro i _
      have hi : Filter.Tendsto
          (fun n => (J x (p x) (mPerDelta m (δSeq n) x)) i)
          Filter.atTop (nhds ((J x (p x) (m x)) i)) :=
        (continuous_apply i).continuousAt.tendsto.comp h_J_lim
      exact hi.mul (tendsto_const_nhds (x := q x i))
    have h_sub :
        Filter.Tendsto
          (fun n =>
            mPerDelta m (δSeq n) x * (DpH x (p x) (mPerDelta m (δSeq n) x) ⬝ q x)
              - J x (p x) (m x) ⬝ q x)
          Filter.atTop (nhds (0 : ℝ)) := by
      have h0 :
          Filter.Tendsto
            (fun n => (J x (p x) (mPerDelta m (δSeq n) x)) ⬝ q x
              - J x (p x) (m x) ⬝ q x)
            Filter.atTop (nhds (0 : ℝ)) := by
        have := h_dot_lim.sub (tendsto_const_nhds (x := (J x (p x) (m x)) ⬝ q x))
        simpa using this
      refine h0.congr (fun n => ?_)
      rw [h_flux_eq n]
    have hc : Filter.Tendsto (fun y : ℝ => ‖y‖) (nhds 0) (nhds ‖(0 : ℝ)‖) :=
      (continuous_norm.tendsto 0)
    simpa using! hc.comp h_sub
  have := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (UnitCube d))
    (F := fun n x =>
      ‖mPerDelta m (δSeq n) x * (DpH x (p x) (mPerDelta m (δSeq n) x) ⬝ q x)
        - J x (p x) (m x) ⬝ q x‖)
    (f := fun _ => (0 : ℝ))
    bound hmeas hbound_int hbound h_lim
  simpa using this

/-! ## δ → 0 DCT assembly bridge (T2 phase6 BB VIid child-4b)

The child-2 toolkit delivers *per-term* `L¹` convergences of the form
`∫ ‖f_{δ n} − f‖ → 0`. The connector `transport_mdelta_limit_concrete`
(paper line 1546, `eq:transport-test-m.delta`) consumes *integral*
convergences `∫ f_{δ n} → ∫ f`. The bridge below turns the former into the
latter: from `∫ ‖f_n − f‖ → 0` and integrability of `f_n`, `f`, we get
`∫ f_n → ∫ f` because

```
‖∫ f_n − ∫ f‖ = ‖∫ (f_n − f)‖ ≤ ∫ ‖f_n − f‖ → 0.
```

This is the genuine δ→0 dominated-convergence content the connector's
`h_LHS_tendsto` / `h_RHS_tendsto` hypotheses package; once the per-term
`L¹` differences (from child-2) are summed into a single LHS / RHS
integrand difference, the bridge discharges the connector inputs. -/

/-- **Generic `L¹`-difference → integral-convergence bridge.** If
`∫ ‖f_n − f‖ ∂μ → 0` and each `f_n`, together with `f`, is integrable, then
`∫ f_n ∂μ → ∫ f ∂μ`. The driver is
`MeasureTheory.norm_integral_le_integral_norm` applied to `f_n − f`, squeezed
to `0`. -/
theorem tendsto_integral_of_L1_diff
    {μ : Measure (Fin d → ℝ)}
    {f : (Fin d → ℝ) → ℝ} {fn : ℕ → (Fin d → ℝ) → ℝ}
    (hfn_int : ∀ n, Integrable (fn n) μ)
    (hf_int : Integrable f μ)
    (h_L1 :
      Filter.Tendsto (fun n => ∫ x, ‖fn n x - f x‖ ∂μ)
        Filter.atTop (nhds (0 : ℝ))) :
    Filter.Tendsto (fun n => ∫ x, fn n x ∂μ)
      Filter.atTop (nhds (∫ x, f x ∂μ)) := by
  -- Reduce to: `‖(∫ fn) − (∫ f)‖ → 0`.
  rw [tendsto_iff_norm_sub_tendsto_zero]
  -- `‖∫ fn − ∫ f‖ = ‖∫ (fn − f)‖ ≤ ∫ ‖fn − f‖`.
  have h_bound : ∀ n,
      ‖(∫ x, fn n x ∂μ) - ∫ x, f x ∂μ‖ ≤ ∫ x, ‖fn n x - f x‖ ∂μ := by
    intro n
    have h_sub : (∫ x, fn n x ∂μ) - ∫ x, f x ∂μ
        = ∫ x, (fn n x - f x) ∂μ :=
      (MeasureTheory.integral_sub (hfn_int n) hf_int).symm
    rw [h_sub]
    exact MeasureTheory.norm_integral_le_integral_norm _
  -- Squeeze: `0 ≤ ‖∫ fn − ∫ f‖ ≤ ∫‖fn − f‖ → 0`.
  exact squeeze_zero (fun n => norm_nonneg _) h_bound h_L1

/-- **Triangle assembly of two `L¹`-difference convergences** (child-4b-ii).
If `∫‖f₁ₙ − f₁‖ → 0` and `∫‖f₂ₙ − f₂‖ → 0`, with each term-difference
`fᵢₙ − fᵢ` integrable (so the two upper-bound integrals add), then the
`L¹`-difference of the sums converges:
`∫‖(f₁ₙ + f₂ₙ) − (f₁ + f₂)‖ → 0`.

The norm of the combined difference is bounded a.e. by the sum of the two
term-norms (`norm_add_le` after regrouping), so `integral_mono_of_nonneg`
(no integrability of the combined norm required) gives
`∫‖…‖ ≤ ∫‖f₁ₙ−f₁‖ + ∫‖f₂ₙ−f₂‖`, and the right-hand sum tends to `0`. -/
theorem tendsto_L1_diff_add
    {μ : Measure (Fin d → ℝ)}
    {f₁ f₂ : (Fin d → ℝ) → ℝ}
    {f₁n f₂n : ℕ → (Fin d → ℝ) → ℝ}
    (hf₁_diff_int : ∀ n, Integrable (fun x => f₁n n x - f₁ x) μ)
    (hf₂_diff_int : ∀ n, Integrable (fun x => f₂n n x - f₂ x) μ)
    (h₁ :
      Filter.Tendsto (fun n => ∫ x, ‖f₁n n x - f₁ x‖ ∂μ)
        Filter.atTop (nhds (0 : ℝ)))
    (h₂ :
      Filter.Tendsto (fun n => ∫ x, ‖f₂n n x - f₂ x‖ ∂μ)
        Filter.atTop (nhds (0 : ℝ))) :
    Filter.Tendsto
      (fun n => ∫ x, ‖(f₁n n x + f₂n n x) - (f₁ x + f₂ x)‖ ∂μ)
      Filter.atTop (nhds (0 : ℝ)) := by
  -- Upper bound: `∫‖(f₁ₙ+f₂ₙ)−(f₁+f₂)‖ ≤ ∫‖f₁ₙ−f₁‖ + ∫‖f₂ₙ−f₂‖`.
  have h_bound : ∀ n,
      (∫ x, ‖(f₁n n x + f₂n n x) - (f₁ x + f₂ x)‖ ∂μ)
        ≤ (∫ x, ‖f₁n n x - f₁ x‖ ∂μ) + (∫ x, ‖f₂n n x - f₂ x‖ ∂μ) := by
    intro n
    have h_int_sum :
        Integrable (fun x => ‖f₁n n x - f₁ x‖ + ‖f₂n n x - f₂ x‖) μ :=
      (hf₁_diff_int n).norm.add (hf₂_diff_int n).norm
    have h_le :
        (fun x => ‖(f₁n n x + f₂n n x) - (f₁ x + f₂ x)‖)
          ≤ᵐ[μ] (fun x => ‖f₁n n x - f₁ x‖ + ‖f₂n n x - f₂ x‖) := by
      filter_upwards with x
      have hrw : (f₁n n x + f₂n n x) - (f₁ x + f₂ x)
          = (f₁n n x - f₁ x) + (f₂n n x - f₂ x) := by ring
      rw [hrw]
      exact norm_add_le _ _
    have h_mono :=
      integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun x => norm_nonneg _)) h_int_sum h_le
    calc
      (∫ x, ‖(f₁n n x + f₂n n x) - (f₁ x + f₂ x)‖ ∂μ)
          ≤ ∫ x, (‖f₁n n x - f₁ x‖ + ‖f₂n n x - f₂ x‖) ∂μ := h_mono
      _ = (∫ x, ‖f₁n n x - f₁ x‖ ∂μ) + (∫ x, ‖f₂n n x - f₂ x‖ ∂μ) :=
          MeasureTheory.integral_add (hf₁_diff_int n).norm (hf₂_diff_int n).norm
  -- Squeeze between `0` and the convergent sum of upper bounds.
  have h_sum_tendsto :
      Filter.Tendsto
        (fun n => (∫ x, ‖f₁n n x - f₁ x‖ ∂μ) + (∫ x, ‖f₂n n x - f₂ x‖ ∂μ))
        Filter.atTop (nhds (0 : ℝ)) := by
    have := h₁.add h₂
    simpa using this
  exact squeeze_zero (fun n => integral_nonneg (fun x => norm_nonneg _))
    h_bound h_sum_tendsto

/-- **LHS `L¹`-difference assembly** (child-4b-ii). Produces the connector's
`hLHS_L1` hypothesis `∫‖LHSa n − LHSaLim‖ → 0` from the two per-term `L¹`
convergences:

* the `(m_δ−m)φ` mass term — child-2's `congestion_Vm_mdelta_tendsto_L1`
  applied with the bounded test function `φ` in the `V` slot;
* the mass-weighted flux term `m_δ·(D_pH(…,m_δ)⬝Dφ) − m·(D_pH(…,m)⬝Dφ)` —
  the new `congestion_mDpH_mdelta_tendsto_L1`.

The two are summed by `tendsto_L1_diff_add`; the `(m_δ−1)φ − (m−1)φ = φ·m_δ −
φ·m` identity rewrites the first term-difference into the Vm shape. -/
theorem lhs_L1_diff_tendsto
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {m : (Fin d → ℝ) → ℝ}
    {p : (Fin d → ℝ) → (Fin d → ℝ)}
    {δSeq : ℕ → ℝ}
    (φ : (Fin d → ℝ) → ℝ) (Dφ : (Fin d → ℝ) → (Fin d → ℝ))
    (LHSa : ℕ → (Fin d → ℝ) → ℝ) (LHSaLim : (Fin d → ℝ) → ℝ)
    (hLHSadef : ∀ n, LHSa n = fun x =>
      (mPerDelta m (δSeq n) x - 1) * φ x
        + mPerDelta m (δSeq n) x * (DpH x (p x) (mPerDelta m (δSeq n) x) ⬝ Dφ x))
    (hLHSaLimDef : LHSaLim = fun x =>
      (m x - 1) * φ x + m x * (DpH x (p x) (m x) ⬝ Dφ x))
    -- per-term diff integrability (for the `integral_add` in `tendsto_L1_diff_add`)
    (hMass_diff_int : ∀ n,
      Integrable (fun x =>
        ((mPerDelta m (δSeq n) x - 1) * φ x) - ((m x - 1) * φ x))
        (volume.restrict (UnitCube d)))
    (hFlux_diff_int : ∀ n,
      Integrable (fun x =>
        (mPerDelta m (δSeq n) x * (DpH x (p x) (mPerDelta m (δSeq n) x) ⬝ Dφ x))
          - (m x * (DpH x (p x) (m x) ⬝ Dφ x)))
        (volume.restrict (UnitCube d)))
    -- per-term `L¹` convergences (child-2 Vm with `V := φ`, and the new lemma)
    (hMass_L1 :
      Filter.Tendsto
        (fun n => ∫ x in UnitCube d,
            ‖φ x * mPerDelta m (δSeq n) x - φ x * m x‖
            ∂(volume : Measure (Fin d → ℝ)))
        Filter.atTop (nhds (0 : ℝ)))
    (hFlux_L1 :
      Filter.Tendsto
        (fun n => ∫ x in UnitCube d,
            ‖mPerDelta m (δSeq n) x * (DpH x (p x) (mPerDelta m (δSeq n) x) ⬝ Dφ x)
              - m x * (DpH x (p x) (m x) ⬝ Dφ x)‖
            ∂(volume : Measure (Fin d → ℝ)))
        Filter.atTop (nhds (0 : ℝ))) :
    Filter.Tendsto
      (fun n => ∫ x in UnitCube d, ‖LHSa n x - LHSaLim x‖
        ∂(volume : Measure (Fin d → ℝ)))
      Filter.atTop (nhds (0 : ℝ)) := by
  -- Recast the mass `L¹` convergence into the `(m_δ−1)φ − (m−1)φ` shape.
  have hMass_L1' :
      Filter.Tendsto
        (fun n => ∫ x in UnitCube d,
            ‖((mPerDelta m (δSeq n) x - 1) * φ x) - ((m x - 1) * φ x)‖
            ∂(volume : Measure (Fin d → ℝ)))
        Filter.atTop (nhds (0 : ℝ)) := by
    refine hMass_L1.congr (fun n => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    congr 1
    ring
  -- Sum the two per-term `L¹`-difference convergences.
  have h_add :=
    tendsto_L1_diff_add
      (μ := volume.restrict (UnitCube d))
      (f₁ := fun x => (m x - 1) * φ x)
      (f₂ := fun x => m x * (DpH x (p x) (m x) ⬝ Dφ x))
      (f₁n := fun n x => (mPerDelta m (δSeq n) x - 1) * φ x)
      (f₂n := fun n x =>
        mPerDelta m (δSeq n) x * (DpH x (p x) (mPerDelta m (δSeq n) x) ⬝ Dφ x))
      hMass_diff_int hFlux_diff_int hMass_L1' hFlux_L1
  -- Identify the summed integrand with `LHSa n − LHSaLim`.
  refine h_add.congr (fun n => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  rw [hLHSadef n, hLHSaLimDef]

/-- **LHS `L¹`-difference assembly, `J`-extension target** (T2 phase6 BB VIid
child-5a-ii-α).

This is the paper-faithful sibling of `lhs_L1_diff_tendsto`. The earlier version
states the limit integrand `LHSaLim` with the *product* `m x · (D_pH(x,p,m) ⬝ Dφ)`,
which at the boundary `{m x = 0}` equals `0` regardless of `D_pH`. But the honest
`δ → 0` limit of the mass-weighted flux is the paper's closed-half-line extension
`J(x, p x, m x) ⬝ Dφ x` (hypothesis `(a:mDpHat0)`), which need **not** vanish at
`m = 0`. The strict-positivity lemma `congestion_mDpH_mdelta_tendsto_L1` sidesteps
this only by assuming `0 < m x`, false at the Browder–Minty witness in general.

So this `J`-target version takes the *flux* `L¹` convergence to `J ⬝ Dφ` (supplied
by `congestion_VI_hFlux_L1_at_witness`, itself
`congestion_mDpH_mdelta_tendsto_L1_to_J` at `q := Dφ`) and the mass `L¹`
convergence, and assembles `∫‖LHSa n − LHSaLim_J‖ → 0` with
`LHSaLim_J x = (m x − 1) φ x + J(x, p x, m x) ⬝ Dφ x`. No `0 < m` is used. -/
theorem lhs_L1_diff_tendsto_J
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {m : (Fin d → ℝ) → ℝ}
    {p : (Fin d → ℝ) → (Fin d → ℝ)}
    {δSeq : ℕ → ℝ}
    (φ : (Fin d → ℝ) → ℝ) (Dφ : (Fin d → ℝ) → (Fin d → ℝ))
    (LHSa : ℕ → (Fin d → ℝ) → ℝ) (LHSaLim : (Fin d → ℝ) → ℝ)
    (hLHSadef : ∀ n, LHSa n = fun x =>
      (mPerDelta m (δSeq n) x - 1) * φ x
        + mPerDelta m (δSeq n) x * (DpH x (p x) (mPerDelta m (δSeq n) x) ⬝ Dφ x))
    (hLHSaLimDef : LHSaLim = fun x =>
      (m x - 1) * φ x + J x (p x) (m x) ⬝ Dφ x)
    -- per-term diff integrability (for the `integral_add` in `tendsto_L1_diff_add`)
    (hMass_diff_int : ∀ n,
      Integrable (fun x =>
        ((mPerDelta m (δSeq n) x - 1) * φ x) - ((m x - 1) * φ x))
        (volume.restrict (UnitCube d)))
    (hFlux_diff_int : ∀ n,
      Integrable (fun x =>
        (mPerDelta m (δSeq n) x * (DpH x (p x) (mPerDelta m (δSeq n) x) ⬝ Dφ x))
          - (J x (p x) (m x) ⬝ Dφ x))
        (volume.restrict (UnitCube d)))
    -- per-term `L¹` convergences (child-2 Vm with `V := φ`, and the `J`-target lemma)
    (hMass_L1 :
      Filter.Tendsto
        (fun n => ∫ x in UnitCube d,
            ‖φ x * mPerDelta m (δSeq n) x - φ x * m x‖
            ∂(volume : Measure (Fin d → ℝ)))
        Filter.atTop (nhds (0 : ℝ)))
    (hFlux_L1 :
      Filter.Tendsto
        (fun n => ∫ x in UnitCube d,
            ‖mPerDelta m (δSeq n) x * (DpH x (p x) (mPerDelta m (δSeq n) x) ⬝ Dφ x)
              - J x (p x) (m x) ⬝ Dφ x‖
            ∂(volume : Measure (Fin d → ℝ)))
        Filter.atTop (nhds (0 : ℝ))) :
    Filter.Tendsto
      (fun n => ∫ x in UnitCube d, ‖LHSa n x - LHSaLim x‖
        ∂(volume : Measure (Fin d → ℝ)))
      Filter.atTop (nhds (0 : ℝ)) := by
  -- Recast the mass `L¹` convergence into the `(m_δ−1)φ − (m−1)φ` shape.
  have hMass_L1' :
      Filter.Tendsto
        (fun n => ∫ x in UnitCube d,
            ‖((mPerDelta m (δSeq n) x - 1) * φ x) - ((m x - 1) * φ x)‖
            ∂(volume : Measure (Fin d → ℝ)))
        Filter.atTop (nhds (0 : ℝ)) := by
    refine hMass_L1.congr (fun n => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    congr 1
    ring
  -- Sum the two per-term `L¹`-difference convergences; the flux limit is `J ⬝ Dφ`.
  have h_add :=
    tendsto_L1_diff_add
      (μ := volume.restrict (UnitCube d))
      (f₁ := fun x => (m x - 1) * φ x)
      (f₂ := fun x => J x (p x) (m x) ⬝ Dφ x)
      (f₁n := fun n x => (mPerDelta m (δSeq n) x - 1) * φ x)
      (f₂n := fun n x =>
        mPerDelta m (δSeq n) x * (DpH x (p x) (mPerDelta m (δSeq n) x) ⬝ Dφ x))
      hMass_diff_int hFlux_diff_int hMass_L1' hFlux_L1
  -- Identify the summed integrand with `LHSa n − LHSaLim`.
  refine h_add.congr (fun n => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  rw [hLHSadef n, hLHSaLimDef]

/-- **Witness-level flux `L¹` cert, `J`-extension target** (T2 phase6 BB VIid
child-5a-ii-α — the deliverable of this task).

Produces, at the Browder–Minty closure-K witness, the `hFlux_L1` hypothesis that
the `J`-stated connector `lhs_L1_diff_tendsto_J` consumes: the mass-weighted flux
`m_δ · (D_pH(x, p x, m_δ) ⬝ Dφ x)` converges in `L¹(UnitCube d)` to the paper's
extension `J(x, p x, m x) ⬝ Dφ x` as `δ → 0⁺`.

This is exactly `congestion_mDpH_mdelta_tendsto_L1_to_J` specialised to the test
gradient `q := Dφ`, so it carries **no** `0 < m` / `hcoePos_m_witness` smuggling:
the boundary `{m x = 0}` contribution is the genuine extension value
`J(x, p x, 0) ⬝ Dφ x` (which the product form `m·D_pH` cannot represent), and the
limit uses only a.e. non-negativity `0 ≤ m x` plus the bundled `(a:mDpHat0)`
data (`hJ_of_pos` + a.e. joint continuity `hae_cont_J` of `J` on `{m ≥ 0}`). -/
theorem congestion_VI_hFlux_L1_at_witness
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {m : (Fin d → ℝ) → ℝ}
    {p : (Fin d → ℝ) → (Fin d → ℝ)}
    {δSeq : ℕ → ℝ}
    (Dφ : (Fin d → ℝ) → (Fin d → ℝ))
    (hδ_lim : Filter.Tendsto δSeq Filter.atTop (nhds (0 : ℝ)))
    (hδ_pos : ∀ n, 0 < δSeq n)
    (hm_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hJ_of_pos : ∀ x p m, 0 < m → J x p m = m • DpH x p m)
    (hae_cont_J :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ContinuousOn (fun pm : (Fin d → ℝ) × ℝ => J x pm.1 pm.2)
          {pm | 0 ≤ pm.2})
    (bound : (Fin d → ℝ) → ℝ)
    (hbound_int : Integrable bound (volume.restrict (UnitCube d)))
    (hmeas :
      ∀ n, AEStronglyMeasurable
        (fun x =>
          ‖mPerDelta m (δSeq n) x * (DpH x (p x) (mPerDelta m (δSeq n) x) ⬝ Dφ x)
            - J x (p x) (m x) ⬝ Dφ x‖)
        (volume.restrict (UnitCube d)))
    (hbound :
      ∀ n, ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖‖mPerDelta m (δSeq n) x * (DpH x (p x) (mPerDelta m (δSeq n) x) ⬝ Dφ x)
            - J x (p x) (m x) ⬝ Dφ x‖‖ ≤ bound x) :
    Filter.Tendsto
      (fun n => ∫ x in UnitCube d,
          ‖mPerDelta m (δSeq n) x * (DpH x (p x) (mPerDelta m (δSeq n) x) ⬝ Dφ x)
            - J x (p x) (m x) ⬝ Dφ x‖
          ∂(volume : Measure (Fin d → ℝ)))
      Filter.atTop (nhds (0 : ℝ)) :=
  congestion_mDpH_mdelta_tendsto_L1_to_J
    (DpH := DpH) (J := J) (m := m) (p := p) (q := Dφ) (δSeq := δSeq)
    hδ_lim hδ_pos hm_nn hJ_of_pos hae_cont_J bound hbound_int hmeas hbound

/-- **RHS `L¹`-difference assembly** (child-4b-ii, step 1). Produces the
connector's `hRHS_L1` hypothesis `∫‖RHSint n − 0‖ → 0`, where
`RHSint n x = Fac n x · (m_δ − m)` with `Fac n x` the
`(u+φ−C(m_δ^β+1)−V)` factor.

This adapts `congestion_Vm_mdelta_tendsto_L1`'s tail-shift DCT template,
generalised to a general factor `Fac` controlled by a `δ`-uniform integrable
dominator `g` (Hölder dominator from `CongestionGrowthCore` at the call
site). The mass test-difference `m_δ − m ∈ [0, 1]` (for `δ ≤ 1`, `m ≥ 0`) and
tends to `0` a.e. (`mPerDelta_sub_tendsto_ae_pt`); pointwise
`‖RHSint n x‖ ≤ g x · (m_δ − m) → 0`, and the dominator `g` (with `m_δ − m ≤ 1`)
controls the whole sequence — so DCT gives the `L¹` limit `0`. -/
theorem rhs_L1_diff_tendsto
    {m : (Fin d → ℝ) → ℝ}
    {δSeq : ℕ → ℝ}
    (Fac : ℕ → (Fin d → ℝ) → ℝ)
    (RHSint : ℕ → (Fin d → ℝ) → ℝ)
    (hδ_pos : ∀ n, 0 < δSeq n)
    (hδ_le_one : ∀ n, δSeq n ≤ 1)
    (hδ_lim : Filter.Tendsto δSeq Filter.atTop (nhds (0 : ℝ)))
    (hm_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hRHSdef : ∀ n, RHSint n = fun x =>
      Fac n x * (mPerDelta m (δSeq n) x - m x))
    (g : (Fin d → ℝ) → ℝ)
    (hg_int : Integrable g (volume.restrict (UnitCube d)))
    (hg_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ g x)
    (hFac_le : ∀ n, ∀ᵐ x ∂(volume.restrict (UnitCube d)), |Fac n x| ≤ g x)
    (hmeas : ∀ n, AEStronglyMeasurable
      (fun x => ‖RHSint n x - (0 : ℝ)‖) (volume.restrict (UnitCube d))) :
    Filter.Tendsto
      (fun n => ∫ x in UnitCube d, ‖RHSint n x - (0 : ℝ)‖
        ∂(volume : Measure (Fin d → ℝ)))
      Filter.atTop (nhds (0 : ℝ)) := by
  -- Collapse the per-`n` a.e. dominator bounds into a single a.e. statement.
  have hFac_le_all :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ n, |Fac n x| ≤ g x := by
    rw [MeasureTheory.ae_all_iff]
    exact hFac_le
  -- Pointwise a.e. limit `‖RHSint n x − 0‖ → 0`.
  have h_lim :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        Filter.Tendsto (fun n => ‖RHSint n x - (0 : ℝ)‖)
          Filter.atTop (nhds (0 : ℝ)) := by
    filter_upwards [hm_nn, hg_nn, hFac_le_all] with x hmx hgx hFacx
    -- `m_δ − m → 0` a.e. pointwise (child-1, with `δSeq → 0⁺`).
    have h_sub_ae := mPerDelta_sub_tendsto_ae_pt (m := m) (x := x) hmx
    have hδ_seq : Filter.Tendsto δSeq Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨hδ_lim, Filter.Eventually.of_forall hδ_pos⟩
    have h_seq : Filter.Tendsto (fun n => mPerDelta m (δSeq n) x - m x)
        Filter.atTop (nhds (0 : ℝ)) := h_sub_ae.comp hδ_seq
    -- Squeeze `0 ≤ ‖RHSint n x‖ ≤ g x · (m_δ − m)`, RHS → 0.
    have h_upper : Filter.Tendsto (fun n => g x * (mPerDelta m (δSeq n) x - m x))
        Filter.atTop (nhds (0 : ℝ)) := by
      have := (tendsto_const_nhds (x := g x)).mul h_seq
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_upper
      (Filter.Eventually.of_forall (fun n => norm_nonneg _)) ?_
    refine Filter.Eventually.of_forall (fun n => ?_)
    rw [sub_zero, hRHSdef n, norm_mul]
    have h_diff_nn : 0 ≤ mPerDelta m (δSeq n) x - m x := by
      have := le_mPerDelta m (δSeq n) x; linarith
    calc ‖Fac n x‖ * ‖mPerDelta m (δSeq n) x - m x‖
        ≤ g x * ‖mPerDelta m (δSeq n) x - m x‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          rw [Real.norm_eq_abs]; exact hFacx n
      _ = g x * (mPerDelta m (δSeq n) x - m x) := by
          rw [Real.norm_eq_abs, abs_of_nonneg h_diff_nn]
  -- Domination `‖RHSint n x − 0‖ ≤ g x` (uniformly in `n`, using `m_δ − m ≤ 1`).
  have hbound :
      ∀ n, ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ‖‖RHSint n x - (0 : ℝ)‖‖ ≤ g x := by
    intro n
    filter_upwards [hm_nn, hFac_le_all] with x hmx hFacx
    have h_diff_nn : 0 ≤ mPerDelta m (δSeq n) x - m x := by
      have := le_mPerDelta m (δSeq n) x; linarith
    have h_diff_le : mPerDelta m (δSeq n) x - m x ≤ 1 := by
      have h1 := mPerDelta_le_add (hδ_pos n).le hmx
      have h2 := hδ_le_one n; linarith
    rw [norm_norm, sub_zero, hRHSdef n, norm_mul]
    calc ‖Fac n x‖ * ‖mPerDelta m (δSeq n) x - m x‖
        ≤ g x * ‖mPerDelta m (δSeq n) x - m x‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          rw [Real.norm_eq_abs]; exact hFacx n
      _ ≤ g x * 1 := by
          apply mul_le_mul_of_nonneg_left _ (le_trans (abs_nonneg _) (hFacx 0))
          rw [Real.norm_eq_abs, abs_of_nonneg h_diff_nn]; exact h_diff_le
      _ = g x := mul_one _
  -- Apply DCT to the nonnegative norm sequence, limit `∫ 0 = 0`.
  have := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (UnitCube d))
    (F := fun n x => ‖RHSint n x - (0 : ℝ)‖)
    (f := fun _ => (0 : ℝ))
    g hmeas hg_int hbound h_lim
  simpa using this

/-- **δ → 0 DCT producing `eq:transport-test-m.delta`** (paper line 1546),
from the per-`δ` variational inequality and the per-term `L¹` convergences.

This is the in-`δ` dominated-convergence packaging: it discharges the two
integral-tendsto hypotheses of `transport_mdelta_limit_concrete` via the
generic bridge `tendsto_integral_of_L1_diff`.

The connector's LHS is split into two pieces (matching paper line 1538):

* `LHSa n` — the `δ`-dependent first integral
  `∫[(m_δ−1)φ + m_δ·D_pH(x,Du+Dφ,m_δ)·Dφ]`, whose limit is its `m`-evaluated
  counterpart; the `L¹` difference `∫‖LHSa n − LHSaLim‖ → 0` is supplied (from
  the child-2 toolkit summed across the two terms);
* `LHSb` — the `δ`-**independent** `ε`-Gateaux integral; its sequence is
  constant, so its limit is trivial.

The RHS integrand `RHSint n` is the `(u+φ−C(m_δ^β+1)−V)(m_δ−m)` term; its `L¹`
difference to `0` is supplied (the `m_δ−m` multiplier → 0 a.e.). The bridge
sends `∫ LHSa n → ∫ LHSaLim` and `∫ RHSint n → 0`, and then
`transport_mdelta_limit_concrete` closes `eq:transport-test-m.delta`. -/
theorem transport_mdelta_limit_of_L1
    {V : (Fin d → ℝ) → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    {ε γBar β C : ℝ}
    (φ Dφ_φ : (Fin d → ℝ) → ℝ)
    (Dφ : Fin d → (Fin d → ℝ) → ℝ)
    {δSeq : ℕ → ℝ}
    (hδ_pos : ∀ n, 0 < δSeq n)
    (hδ_le_one : ∀ n, δSeq n ≤ 1)
    (hδ_tendsto : Filter.Tendsto δSeq Filter.atTop (nhds (0 : ℝ)))
    -- Per-`n` variational inequality, lower-bounded form (paper line 1538).
    (h_VI_at_mdelta : ∀ n,
      (∫ x in UnitCube d,
          (u x + φ x - C * ((max (m x) (δSeq n)) ^ β + 1) - V x)
            * (max (m x) (δSeq n) - m x)
          ∂(volume : Measure (Fin d → ℝ)))
      ≤
      (∫ x in UnitCube d,
          (max (m x) (δSeq n) - 1) * φ x
            + max (m x) (δSeq n)
              * (DpH x (fun i => Du i x + Dφ i x) (max (m x) (δSeq n))
                  ⬝ (fun i => Dφ i x))
          ∂(volume : Measure (Fin d → ℝ)))
      +
      (∫ x in UnitCube d,
          ε * vecAbsPowMinusTwo γBar (fun i => Du i x + Dφ i x)
            * ((fun i => Du i x + Dφ i x) ⬝ (fun i => Dφ i x))
          + ε * absPowMinusTwo γBar (u x + φ x) * ((u x + φ x) * φ x)
          ∂(volume : Measure (Fin d → ℝ))))
    -- `δ`-dependent LHS integrand `LHSa n` and its `m`-limit `LHSaLim`,
    -- definitionally the first connector integral (paper line 1538).
    (LHSa : ℕ → (Fin d → ℝ) → ℝ)
    (LHSaLim : (Fin d → ℝ) → ℝ)
    (RHSint : ℕ → (Fin d → ℝ) → ℝ)
    (hLHSadef : ∀ n, LHSa n = fun x =>
      (max (m x) (δSeq n) - 1) * φ x
        + max (m x) (δSeq n)
          * (DpH x (fun i => Du i x + Dφ i x) (max (m x) (δSeq n))
              ⬝ (fun i => Dφ i x)))
    (hLHSaLimDef : LHSaLim = fun x =>
      (m x - 1) * φ x
        + m x
          * (DpH x (fun i => Du i x + Dφ i x) (m x)
              ⬝ (fun i => Dφ i x)))
    (hRHSdef : ∀ n, RHSint n = fun x =>
      (u x + φ x - C * ((max (m x) (δSeq n)) ^ β + 1) - V x)
        * (max (m x) (δSeq n) - m x))
    -- Integrability data for the bridge.
    (hLHSa_int : ∀ n, Integrable (LHSa n) (volume.restrict (UnitCube d)))
    (hLHSaLim_int : Integrable LHSaLim (volume.restrict (UnitCube d)))
    (hRHS_int : ∀ n, Integrable (RHSint n) (volume.restrict (UnitCube d)))
    -- `L¹` convergence of the whole-integrand differences (from child-2 summed).
    (hLHS_L1 :
      Filter.Tendsto
        (fun n => ∫ x in UnitCube d, ‖LHSa n x - LHSaLim x‖
          ∂(volume : Measure (Fin d → ℝ)))
        Filter.atTop (nhds (0 : ℝ)))
    (hRHS_L1 :
      Filter.Tendsto
        (fun n => ∫ x in UnitCube d, ‖RHSint n x - (0 : ℝ)‖
          ∂(volume : Measure (Fin d → ℝ)))
        Filter.atTop (nhds (0 : ℝ))) :
    0 ≤
      (∫ x in UnitCube d,
          (m x - 1) * φ x
            + m x
              * (DpH x (fun i => Du i x + Dφ i x) (m x)
                  ⬝ (fun i => Dφ i x))
          ∂(volume : Measure (Fin d → ℝ)))
      +
      (∫ x in UnitCube d,
          ε * vecAbsPowMinusTwo γBar (fun i => Du i x + Dφ i x)
            * ((fun i => Du i x + Dφ i x) ⬝ (fun i => Dφ i x))
          + ε * absPowMinusTwo γBar (u x + φ x) * ((u x + φ x) * φ x)
          ∂(volume : Measure (Fin d → ℝ))) := by
  -- The `δ`-dependent first integral converges to its `m`-counterpart (bridge).
  have h_LHSa_tendsto :
      Filter.Tendsto (fun n => ∫ x in UnitCube d, LHSa n x
          ∂(volume : Measure (Fin d → ℝ)))
        Filter.atTop
        (nhds (∫ x in UnitCube d, LHSaLim x
          ∂(volume : Measure (Fin d → ℝ)))) :=
    tendsto_integral_of_L1_diff hLHSa_int hLHSaLim_int hLHS_L1
  -- The `ε`-Gateaux integral `LHSb` is `δ`-independent: its sequence is constant.
  set LHSb : ℝ :=
    (∫ x in UnitCube d,
        ε * vecAbsPowMinusTwo γBar (fun i => Du i x + Dφ i x)
          * ((fun i => Du i x + Dφ i x) ⬝ (fun i => Dφ i x))
        + ε * absPowMinusTwo γBar (u x + φ x) * ((u x + φ x) * φ x)
        ∂(volume : Measure (Fin d → ℝ))) with hLHSb
  -- The full LHS sequence `∫ LHSa n + LHSb` converges to `∫ LHSaLim + LHSb`.
  have h_LHS_tendsto :
      Filter.Tendsto
        (fun n =>
          (∫ x in UnitCube d,
              (max (m x) (δSeq n) - 1) * φ x
                + max (m x) (δSeq n)
                  * (DpH x (fun i => Du i x + Dφ i x) (max (m x) (δSeq n))
                      ⬝ (fun i => Dφ i x))
              ∂(volume : Measure (Fin d → ℝ)))
          +
          (∫ x in UnitCube d,
              ε * vecAbsPowMinusTwo γBar (fun i => Du i x + Dφ i x)
                * ((fun i => Du i x + Dφ i x) ⬝ (fun i => Dφ i x))
              + ε * absPowMinusTwo γBar (u x + φ x) * ((u x + φ x) * φ x)
              ∂(volume : Measure (Fin d → ℝ))))
        Filter.atTop
        (nhds
          ((∫ x in UnitCube d,
              (m x - 1) * φ x
                + m x
                  * (DpH x (fun i => Du i x + Dφ i x) (m x)
                      ⬝ (fun i => Dφ i x))
              ∂(volume : Measure (Fin d → ℝ)))
          +
          (∫ x in UnitCube d,
              ε * vecAbsPowMinusTwo γBar (fun i => Du i x + Dφ i x)
                * ((fun i => Du i x + Dφ i x) ⬝ (fun i => Dφ i x))
              + ε * absPowMinusTwo γBar (u x + φ x) * ((u x + φ x) * φ x)
              ∂(volume : Measure (Fin d → ℝ))))) := by
    -- Rewrite the LHS-sequence first integral via `hLHSadef`, the limit via
    -- `hLHSaLimDef`, and add the constant `LHSb`.
    have h1 : (fun n =>
        (∫ x in UnitCube d,
            (max (m x) (δSeq n) - 1) * φ x
              + max (m x) (δSeq n)
                * (DpH x (fun i => Du i x + Dφ i x) (max (m x) (δSeq n))
                    ⬝ (fun i => Dφ i x))
            ∂(volume : Measure (Fin d → ℝ)))
        +
        (∫ x in UnitCube d,
            ε * vecAbsPowMinusTwo γBar (fun i => Du i x + Dφ i x)
              * ((fun i => Du i x + Dφ i x) ⬝ (fun i => Dφ i x))
            + ε * absPowMinusTwo γBar (u x + φ x) * ((u x + φ x) * φ x)
            ∂(volume : Measure (Fin d → ℝ))))
      = (fun n => (∫ x in UnitCube d, LHSa n x
            ∂(volume : Measure (Fin d → ℝ))) + LHSb) := by
      funext n
      rw [hLHSadef n, hLHSb]
    rw [h1]
    have h2 :
        (∫ x in UnitCube d,
            (m x - 1) * φ x
              + m x
                * (DpH x (fun i => Du i x + Dφ i x) (m x)
                    ⬝ (fun i => Dφ i x))
            ∂(volume : Measure (Fin d → ℝ)))
        +
        (∫ x in UnitCube d,
            ε * vecAbsPowMinusTwo γBar (fun i => Du i x + Dφ i x)
              * ((fun i => Du i x + Dφ i x) ⬝ (fun i => Dφ i x))
            + ε * absPowMinusTwo γBar (u x + φ x) * ((u x + φ x) * φ x)
            ∂(volume : Measure (Fin d → ℝ)))
        = (∫ x in UnitCube d, LHSaLim x ∂(volume : Measure (Fin d → ℝ))) + LHSb := by
      rw [hLHSaLimDef, hLHSb]
    rw [h2]
    exact h_LHSa_tendsto.add_const LHSb
  -- The RHS sequence `∫ RHSint n → 0` (bridge to the zero limit).
  have h_RHS_tendsto :
      Filter.Tendsto
        (fun n =>
          ∫ x in UnitCube d,
            (u x + φ x - C * ((max (m x) (δSeq n)) ^ β + 1) - V x)
              * (max (m x) (δSeq n) - m x)
            ∂(volume : Measure (Fin d → ℝ)))
        Filter.atTop
        (nhds (0 : ℝ)) := by
    have h0 :
        Filter.Tendsto (fun n => ∫ x in UnitCube d, RHSint n x
            ∂(volume : Measure (Fin d → ℝ)))
          Filter.atTop
          (nhds (∫ x in UnitCube d, (0 : ℝ)
            ∂(volume : Measure (Fin d → ℝ)))) :=
      tendsto_integral_of_L1_diff hRHS_int (integrable_zero _ _ _) hRHS_L1
    rw [MeasureTheory.integral_zero] at h0
    refine h0.congr (fun n => ?_)
    rw [hRHSdef n]
  -- Close with the existing connector.
  exact transport_mdelta_limit_concrete
    (V := V) (DpH := DpH) (Du := Du) (m := m) (u := u)
    (ε := ε) (γBar := γBar) (β := β) (C := C)
    φ Dφ_φ Dφ hδ_pos hδ_le_one hδ_tendsto
    h_VI_at_mdelta h_LHS_tendsto h_RHS_tendsto

/-- **`J`-extension sibling of `transport_mdelta_limit_of_L1`** (T2 phase6 BB VIid
child-5a-ii-β, connector J-reshape — the deliverable of this task).

The honest `δ → 0` passage producing `eq:transport-test-m.delta` with the
paper-faithful extension flux. The `δ`-dependent first integral `LHSa n` still
carries the product `m_δ·D_pH(x, Du+∇φ, m_δ)·∇φ` (true at `m_δ ≥ δ > 0`), but its
`δ → 0` limit `LHSaLim` is the closed-half-line extension
`(m−1)φ + J(x, Du+∇φ, m)⬝∇φ` (hypothesis `(a:mDpHat0)`), supplied through the
`L¹`-difference convergence `hLHS_L1` produced by `lhs_L1_diff_tendsto_J`
(itself fed by `congestion_VI_hFlux_L1_at_witness`). No `0 < m` is used: the
`{m = 0}` boundary contribution is the genuine `J(x, ·, 0)⬝∇φ`, which the product
form cannot represent.

The generic bridge `tendsto_integral_of_L1_diff` sends `∫ LHSa n → ∫ LHSaLim`
regardless of the limit's shape, so the proof mirrors the product-form original;
it closes via the `J`-stated `transport_mdelta_limit_concrete_J`. -/
theorem transport_mdelta_limit_of_L1_J
    {V : (Fin d → ℝ) → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    {ε γBar β C : ℝ}
    (φ Dφ_φ : (Fin d → ℝ) → ℝ)
    (Dφ : Fin d → (Fin d → ℝ) → ℝ)
    {δSeq : ℕ → ℝ}
    (hδ_pos : ∀ n, 0 < δSeq n)
    (hδ_le_one : ∀ n, δSeq n ≤ 1)
    (hδ_tendsto : Filter.Tendsto δSeq Filter.atTop (nhds (0 : ℝ)))
    (h_VI_at_mdelta : ∀ n,
      (∫ x in UnitCube d,
          (u x + φ x - C * ((max (m x) (δSeq n)) ^ β + 1) - V x)
            * (max (m x) (δSeq n) - m x)
          ∂(volume : Measure (Fin d → ℝ)))
      ≤
      (∫ x in UnitCube d,
          (max (m x) (δSeq n) - 1) * φ x
            + max (m x) (δSeq n)
              * (DpH x (fun i => Du i x + Dφ i x) (max (m x) (δSeq n))
                  ⬝ (fun i => Dφ i x))
          ∂(volume : Measure (Fin d → ℝ)))
      +
      (∫ x in UnitCube d,
          ε * vecAbsPowMinusTwo γBar (fun i => Du i x + Dφ i x)
            * ((fun i => Du i x + Dφ i x) ⬝ (fun i => Dφ i x))
          + ε * absPowMinusTwo γBar (u x + φ x) * ((u x + φ x) * φ x)
          ∂(volume : Measure (Fin d → ℝ))))
    (LHSa : ℕ → (Fin d → ℝ) → ℝ)
    (LHSaLim : (Fin d → ℝ) → ℝ)
    (RHSint : ℕ → (Fin d → ℝ) → ℝ)
    (hLHSadef : ∀ n, LHSa n = fun x =>
      (max (m x) (δSeq n) - 1) * φ x
        + max (m x) (δSeq n)
          * (DpH x (fun i => Du i x + Dφ i x) (max (m x) (δSeq n))
              ⬝ (fun i => Dφ i x)))
    -- The `δ → 0` limit integrand: the `J`-extension flux (paper `(a:mDpHat0)`).
    (hLHSaLimDef : LHSaLim = fun x =>
      (m x - 1) * φ x
        + (J x (fun i => Du i x + Dφ i x) (m x)
            ⬝ (fun i => Dφ i x)))
    (hRHSdef : ∀ n, RHSint n = fun x =>
      (u x + φ x - C * ((max (m x) (δSeq n)) ^ β + 1) - V x)
        * (max (m x) (δSeq n) - m x))
    (hLHSa_int : ∀ n, Integrable (LHSa n) (volume.restrict (UnitCube d)))
    (hLHSaLim_int : Integrable LHSaLim (volume.restrict (UnitCube d)))
    (hRHS_int : ∀ n, Integrable (RHSint n) (volume.restrict (UnitCube d)))
    (hLHS_L1 :
      Filter.Tendsto
        (fun n => ∫ x in UnitCube d, ‖LHSa n x - LHSaLim x‖
          ∂(volume : Measure (Fin d → ℝ)))
        Filter.atTop (nhds (0 : ℝ)))
    (hRHS_L1 :
      Filter.Tendsto
        (fun n => ∫ x in UnitCube d, ‖RHSint n x - (0 : ℝ)‖
          ∂(volume : Measure (Fin d → ℝ)))
        Filter.atTop (nhds (0 : ℝ))) :
    0 ≤
      (∫ x in UnitCube d,
          (m x - 1) * φ x
            + (J x (fun i => Du i x + Dφ i x) (m x)
                ⬝ (fun i => Dφ i x))
          ∂(volume : Measure (Fin d → ℝ)))
      +
      (∫ x in UnitCube d,
          ε * vecAbsPowMinusTwo γBar (fun i => Du i x + Dφ i x)
            * ((fun i => Du i x + Dφ i x) ⬝ (fun i => Dφ i x))
          + ε * absPowMinusTwo γBar (u x + φ x) * ((u x + φ x) * φ x)
          ∂(volume : Measure (Fin d → ℝ))) := by
  -- The `δ`-dependent first integral converges to its `J`-extension counterpart.
  have h_LHSa_tendsto :
      Filter.Tendsto (fun n => ∫ x in UnitCube d, LHSa n x
          ∂(volume : Measure (Fin d → ℝ)))
        Filter.atTop
        (nhds (∫ x in UnitCube d, LHSaLim x
          ∂(volume : Measure (Fin d → ℝ)))) :=
    tendsto_integral_of_L1_diff hLHSa_int hLHSaLim_int hLHS_L1
  set LHSb : ℝ :=
    (∫ x in UnitCube d,
        ε * vecAbsPowMinusTwo γBar (fun i => Du i x + Dφ i x)
          * ((fun i => Du i x + Dφ i x) ⬝ (fun i => Dφ i x))
        + ε * absPowMinusTwo γBar (u x + φ x) * ((u x + φ x) * φ x)
        ∂(volume : Measure (Fin d → ℝ))) with hLHSb
  have h_LHS_tendsto :
      Filter.Tendsto
        (fun n =>
          (∫ x in UnitCube d,
              (max (m x) (δSeq n) - 1) * φ x
                + max (m x) (δSeq n)
                  * (DpH x (fun i => Du i x + Dφ i x) (max (m x) (δSeq n))
                      ⬝ (fun i => Dφ i x))
              ∂(volume : Measure (Fin d → ℝ)))
          +
          (∫ x in UnitCube d,
              ε * vecAbsPowMinusTwo γBar (fun i => Du i x + Dφ i x)
                * ((fun i => Du i x + Dφ i x) ⬝ (fun i => Dφ i x))
              + ε * absPowMinusTwo γBar (u x + φ x) * ((u x + φ x) * φ x)
              ∂(volume : Measure (Fin d → ℝ))))
        Filter.atTop
        (nhds
          ((∫ x in UnitCube d,
              (m x - 1) * φ x
                + (J x (fun i => Du i x + Dφ i x) (m x)
                    ⬝ (fun i => Dφ i x))
              ∂(volume : Measure (Fin d → ℝ)))
          +
          (∫ x in UnitCube d,
              ε * vecAbsPowMinusTwo γBar (fun i => Du i x + Dφ i x)
                * ((fun i => Du i x + Dφ i x) ⬝ (fun i => Dφ i x))
              + ε * absPowMinusTwo γBar (u x + φ x) * ((u x + φ x) * φ x)
              ∂(volume : Measure (Fin d → ℝ))))) := by
    have h1 : (fun n =>
        (∫ x in UnitCube d,
            (max (m x) (δSeq n) - 1) * φ x
              + max (m x) (δSeq n)
                * (DpH x (fun i => Du i x + Dφ i x) (max (m x) (δSeq n))
                    ⬝ (fun i => Dφ i x))
            ∂(volume : Measure (Fin d → ℝ)))
        +
        (∫ x in UnitCube d,
            ε * vecAbsPowMinusTwo γBar (fun i => Du i x + Dφ i x)
              * ((fun i => Du i x + Dφ i x) ⬝ (fun i => Dφ i x))
            + ε * absPowMinusTwo γBar (u x + φ x) * ((u x + φ x) * φ x)
            ∂(volume : Measure (Fin d → ℝ))))
      = (fun n => (∫ x in UnitCube d, LHSa n x
            ∂(volume : Measure (Fin d → ℝ))) + LHSb) := by
      funext n
      rw [hLHSadef n, hLHSb]
    rw [h1]
    have h2 :
        (∫ x in UnitCube d,
            (m x - 1) * φ x
              + (J x (fun i => Du i x + Dφ i x) (m x)
                  ⬝ (fun i => Dφ i x))
            ∂(volume : Measure (Fin d → ℝ)))
        +
        (∫ x in UnitCube d,
            ε * vecAbsPowMinusTwo γBar (fun i => Du i x + Dφ i x)
              * ((fun i => Du i x + Dφ i x) ⬝ (fun i => Dφ i x))
            + ε * absPowMinusTwo γBar (u x + φ x) * ((u x + φ x) * φ x)
            ∂(volume : Measure (Fin d → ℝ)))
        = (∫ x in UnitCube d, LHSaLim x ∂(volume : Measure (Fin d → ℝ))) + LHSb := by
      rw [hLHSaLimDef, hLHSb]
    rw [h2]
    exact h_LHSa_tendsto.add_const LHSb
  have h_RHS_tendsto :
      Filter.Tendsto
        (fun n =>
          ∫ x in UnitCube d,
            (u x + φ x - C * ((max (m x) (δSeq n)) ^ β + 1) - V x)
              * (max (m x) (δSeq n) - m x)
            ∂(volume : Measure (Fin d → ℝ)))
        Filter.atTop
        (nhds (0 : ℝ)) := by
    have h0 :
        Filter.Tendsto (fun n => ∫ x in UnitCube d, RHSint n x
            ∂(volume : Measure (Fin d → ℝ)))
          Filter.atTop
          (nhds (∫ x in UnitCube d, (0 : ℝ)
            ∂(volume : Measure (Fin d → ℝ)))) :=
      tendsto_integral_of_L1_diff hRHS_int (integrable_zero _ _ _) hRHS_L1
    rw [MeasureTheory.integral_zero] at h0
    refine h0.congr (fun n => ?_)
    rw [hRHSdef n]
  exact transport_mdelta_limit_concrete_J
    (V := V) (DpH := DpH) (J := J) (Du := Du) (m := m) (u := u)
    (ε := ε) (γBar := γBar) (β := β) (C := C)
    φ Dφ_φ Dφ hδ_pos hδ_le_one hδ_tendsto
    h_VI_at_mdelta h_LHS_tendsto h_RHS_tendsto

/-! ## Integrability of the first-variation connector integrands at the
truncated density (T2 phase6 BB VIid child-4b-i prerequisite)

For fixed `t > 0`, `δ > 0`, the algebraic half of child-4b-i needs the
three connector integrands `LHSc`, `RHSc`, `Mterm` integrable on the
cube. These are operator well-definedness facts re-derived at the
**perturbed point** `(Du + t∇φ, m_δ)`, `m_δ = max(m, δ) ≥ δ > 0`.

The exponent bookkeeping: HJB / mass factors live in `L^{β̄'}` paired
with the test density `m_δ − m ∈ L^{β̄}` (Hölder `(β̄, β̄')`); the flux
factor `m_δ · D_pH ∈ L^{γ̄'}` paired with the smooth `Dφ_c ∈ L^{γ̄}`
(Hölder `(γ̄, γ̄')`).

The two keystone memberships re-derive operator well-definedness at the
perturbed argument:
* `H_at_perturbed_memLp_betaBar'` — the two-sided `|H|`-bound
  (`H_two_sided_congestion_of_hmon`) dominated by an `L^{β̄'}` envelope,
  via `MemLp.of_le_mul`;
* `mDpH_at_perturbed_memLp_gammaBar'` — the `D_pH` growth bound
  (`hcong.DpH_upper`) multiplied by `m_δ` and dominated by the
  `L^{γ̄'}` flux envelope (`congestion_flux_dominator_memLp_gammaBar'_le`).
-/

open StationaryMFG.Periodic in
/-- **Keystone A.** The HJB factor `−(u+φ_c) − H(·, Dg, m_δ) + V`
lies in `L^{β̄'}_per`, with `m_δ = max(m, δ) ≥ δ > 0` the truncated
density and `Dg` the perturbed gradient. Re-derives the HJB
well-definedness of `aEpsi_congestion_HJB_memLp` / `muAux_H_mem_Lp` at
the perturbed point, using the two-sided `|H|` bound
`H_two_sided_congestion_of_hmon`.

The perturbed-point ratio integrability `‖Dg‖^{αt}/(m_δ^τ+1) ∈ L^{β̄'}`
is a genuine certified residue (produced by `mdelta_admissibility` at the
call site — child-1's `mPerDelta_memLpPer` for `m_δ ∈ L^{β̄}` and the
smooth test gradient), threaded here per CONVENTIONS §8 rather than
re-derived from the `mdelta_admissibility` chain. -/
theorem H_at_perturbed_memLp_betaBar'
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    {m u V : (Fin d → ℝ) → ℝ}
    {Dg : Fin d → (Fin d → ℝ) → ℝ}
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) m)
    (hm_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hu_memBeta : MemLpPer (d := d)
      (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) u)
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (hDg_meas : ∀ i,
      AEStronglyMeasurable (Dg i) (volume.restrict (UnitCube d)))
    (φ_c : (Fin d → ℝ) → ℝ)
    (hφ_c : MemLpPer (d := d)
      (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) φ_c)
    {δ : ℝ} (hδ : 0 < δ)
    (hRatio_pert : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
      (fun x => ‖fun i => Dg i x‖ ^ (hcong.α * (1 + hcong.τ / hcong.β))
        / (max (m x) δ ^ hcong.τ + 1))) :
    MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
      (fun x => -(u x + φ_c x)
        - H x (fun i => Dg i x) (max (m x) δ) + V x) := by
  classical
  set α : ℝ := hcong.α with hαdef
  set β : ℝ := hcong.β with hβdef
  set τ : ℝ := hcong.τ with hτdef
  have hα : 1 < α := hcong.hα
  have hβ : 0 < β := hcong.hβ
  have hτ_nn : 0 ≤ τ := hcong.hτ.1
  have hβbar_pos : 0 < β + 1 := by linarith
  set βBar' : ℝ≥0∞ := ENNReal.ofReal ((β + 1) / β) with hβBar'def
  haveI hfin : IsFiniteMeasure
      (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  set mδ : (Fin d → ℝ) → ℝ := fun x => max (m x) δ with hmδdef
  have hmδ_pos : ∀ x, 0 < mδ x := fun x => lt_of_lt_of_le hδ (le_max_right _ _)
  have hmδ_mem : MemLpPer (d := d) (ENNReal.ofReal (β + 1)) mδ := by
    have := mPerDelta_memLpPer (d := d) (p := ENNReal.ofReal (β + 1))
      (δ := δ) hδ.le (m := m) (by rw [hβdef]; exact hm_mem) hm_nn
    simpa [mPerDelta, hmδdef] using! this
  set αt : ℝ := α * (1 + τ / β) with hαtdef
  -- Two-sided `|H|` bound, specialised to all `p, m > 0`.
  obtain ⟨K, hK_pos, hHbnd⟩ := H_two_sided_congestion_of_hmon hmon hcong
  -- AE-strong-measurability of `H(·, Dg, m_δ)` (Carathéodory composition).
  have hH_comp_meas : AEStronglyMeasurable
      (fun x => H x (fun i => Dg i x) (mδ x))
      (Measure.restrict volume (UnitCube d)) := by
    have hid : AEMeasurable (fun x : Fin d → ℝ => x)
        (volume.restrict (UnitCube d)) := aemeasurable_id
    have hDg' : AEMeasurable (fun x => (fun i => Dg i x))
        (volume.restrict (UnitCube d)) := by
      rw [aemeasurable_pi_iff]; intro i
      exact aestronglyMeasurable_iff_aemeasurable.mp (hDg_meas i)
    have hmδ' : AEMeasurable mδ (volume.restrict (UnitCube d)) :=
      aestronglyMeasurable_iff_aemeasurable.mp hmδ_mem.aestronglyMeasurable
    have hprod : AEMeasurable
        (fun x : Fin d → ℝ => (x, (fun i => Dg i x), mδ x))
        (volume.restrict (UnitCube d)) := hid.prodMk (hDg'.prodMk hmδ')
    have hcomp : AEMeasurable
        (fun x => H x (fun i => Dg i x) (mδ x))
        (volume.restrict (UnitCube d)) :=
      hcong.measurable_H.comp_aemeasurable hprod
    exact aestronglyMeasurable_iff_aemeasurable.mpr hcomp
  -- Summand `m_δ^β + 1 ∈ L^{β̄'}`.
  have hmδβ_dom : MemLpPer (d := d) βBar' (fun x => mδ x ^ β + 1) := by
    rw [hβBar'def]
    have hpow : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
        (fun x => mδ x ^ β) :=
      rpow_beta_memLp_betaBar' hβ hmδ_mem
        (Filter.Eventually.of_forall (fun x => (hmδ_pos x).le))
    have hone : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
        (fun _ : (Fin d → ℝ) => (1 : ℝ)) := MemLp.toMemLpPer (memLp_const 1)
    have := hpow.add hone
    simpa using! this
  -- Ratio-style summand `(1/m_δ + 1/m_δ^τ)·(‖Dg‖^{αt}+1) ∈ L^{β̄'}`, via
  -- the dominator `K_aux·(‖Dg‖^{αt}/(m_δ^τ+1) + 1)` (mirrors
  -- `WellDefined.ratio_full_memLp_betaBarPrime`).
  have hRatio_full : MemLpPer (d := d) βBar'
      (fun x => (1 / mδ x + 1 / mδ x ^ τ) * (‖fun i => Dg i x‖ ^ αt + 1)) := by
    set Kaux : ℝ := 1 / δ ^ (1 - τ) + 1 / δ + 1 + 1 / δ ^ τ with hKaux
    have hKaux_nn : 0 ≤ Kaux := by rw [hKaux]; positivity
    -- dominator membership.
    have hdom : MemLpPer (d := d) βBar'
        (fun x => Kaux * (‖fun i => Dg i x‖ ^ αt / (mδ x ^ τ + 1) + 1)) := by
      have hsmul : MemLpPer (d := d) βBar'
          (fun x => Kaux * (‖fun i => Dg i x‖ ^ αt / (mδ x ^ τ + 1))) := by
        have hh := hRatio_pert.const_smul (𝕜 := ℝ) Kaux
        have heq : (Kaux • fun x : Fin d → ℝ =>
              ‖fun i => Dg i x‖ ^ (hcong.α * (1 + hcong.τ / hcong.β))
                / (max (m x) δ ^ hcong.τ + 1))
            = (fun x => Kaux * (‖fun i => Dg i x‖ ^ αt / (mδ x ^ τ + 1))) := by
          funext x; simp only [Pi.smul_apply, smul_eq_mul, hmδdef, hαtdef,
            hαdef, hβdef, hτdef]
        rw [heq] at hh; exact hh
      have hconst : MemLpPer (d := d) βBar' (fun _ : (Fin d → ℝ) => Kaux) :=
        MemLp.toMemLpPer (memLp_const Kaux)
      have hsum := hsmul.add hconst
      have heq : ((fun x : Fin d → ℝ =>
            Kaux * (‖fun i => Dg i x‖ ^ αt / (mδ x ^ τ + 1)))
          + fun _ : Fin d → ℝ => Kaux)
          = (fun x => Kaux * (‖fun i => Dg i x‖ ^ αt / (mδ x ^ τ + 1) + 1)) := by
        funext x; simp only [Pi.add_apply]; ring
      rw [heq] at hsum; exact hsum
    -- AE-strong-measurability of the LHS.
    have hmeas_lhs : AEStronglyMeasurable
        (fun x => (1 / mδ x + 1 / mδ x ^ τ) * (‖fun i => Dg i x‖ ^ αt + 1))
        (Measure.restrict volume (UnitCube d)) := by
      have hmδ_meas := hmδ_mem.aestronglyMeasurable
      have hmδτ : AEStronglyMeasurable (fun x => mδ x ^ τ)
          (Measure.restrict volume (UnitCube d)) :=
        (Real.continuous_rpow_const hτ_nn).comp_aestronglyMeasurable hmδ_meas
      have hpre : AEStronglyMeasurable (fun x => 1 / mδ x + 1 / mδ x ^ τ)
          (Measure.restrict volume (UnitCube d)) :=
        (AEStronglyMeasurable.div₀ aestronglyMeasurable_const hmδ_meas).add
          (AEStronglyMeasurable.div₀ aestronglyMeasurable_const hmδτ)
      have hvec : AEStronglyMeasurable
          (fun x => ‖fun i => Dg i x‖) (Measure.restrict volume (UnitCube d)) := by
        apply AEStronglyMeasurable.norm
        rw [aestronglyMeasurable_iff_aemeasurable, aemeasurable_pi_iff]
        intro i; exact aestronglyMeasurable_iff_aemeasurable.mp (hDg_meas i)
      have hαt_nn : 0 ≤ αt := by
        rw [hαtdef]
        have : 0 ≤ 1 + τ / β := by positivity
        positivity
      have hnum : AEStronglyMeasurable (fun x => ‖fun i => Dg i x‖ ^ αt + 1)
          (Measure.restrict volume (UnitCube d)) :=
        ((Real.continuous_rpow_const hαt_nn).comp_aestronglyMeasurable
          hvec).add aestronglyMeasurable_const
      exact hpre.mul hnum
    -- pointwise domination.
    apply MemLp.toMemLpPer
    apply MemLp.of_le_mul (c := 1) hdom.toMemLp hmeas_lhs
    filter_upwards with x
    have hpos := hmδ_pos x
    have hmδτ_pos : 0 < mδ x ^ τ := Real.rpow_pos_of_pos hpos τ
    have hden_pos : 0 < mδ x ^ τ + 1 := by linarith
    have hnum_nn : 0 ≤ ‖fun i => Dg i x‖ ^ αt :=
      Real.rpow_nonneg (norm_nonneg _) _
    have hnum1_nn : 0 ≤ ‖fun i => Dg i x‖ ^ αt + 1 := by linarith
    have hpre_nn : 0 ≤ 1 / mδ x + 1 / mδ x ^ τ := by positivity
    have hLHS_nn : 0 ≤ (1 / mδ x + 1 / mδ x ^ τ) * (‖fun i => Dg i x‖ ^ αt + 1) :=
      mul_nonneg hpre_nn hnum1_nn
    have hratio_nn : 0 ≤ ‖fun i => Dg i x‖ ^ αt / (mδ x ^ τ + 1) :=
      div_nonneg hnum_nn hden_pos.le
    have hdom_nn : 0 ≤ Kaux * (‖fun i => Dg i x‖ ^ αt / (mδ x ^ τ + 1) + 1) :=
      mul_nonneg hKaux_nn (by linarith)
    have hden_ge_one : (1 : ℝ) ≤ mδ x ^ τ + 1 := by
      have := Real.rpow_nonneg hpos.le τ; linarith
    -- Key pointwise bound `(1/m_δ + 1/m_δ^τ)·(m_δ^τ+1) ≤ Kaux`.
    have h1τ_nn : 0 ≤ 1 - τ := by linarith [hcong.hτ.2]
    -- `m_δ^{τ}/m_δ = m_δ^{τ-1} = 1/m_δ^{1-τ} ≤ 1/δ^{1-τ}`.
    have hratio_pow : mδ x ^ τ / mδ x ≤ 1 / δ ^ (1 - τ) := by
      have hrw : mδ x ^ τ / mδ x = 1 / mδ x ^ (1 - τ) := by
        rw [div_eq_mul_inv, one_div, ← Real.rpow_neg hpos.le,
          ← Real.rpow_neg_one (mδ x), ← Real.rpow_add hpos]
        congr 1; ring
      rw [hrw]
      apply one_div_le_one_div_of_le (Real.rpow_pos_of_pos hδ _)
      exact Real.rpow_le_rpow hδ.le (le_max_right _ _) h1τ_nn
    have hkey : (1 / mδ x + 1 / mδ x ^ τ) * (mδ x ^ τ + 1) ≤ Kaux := by
      have hexp : (1 / mδ x + 1 / mδ x ^ τ) * (mδ x ^ τ + 1)
          = mδ x ^ τ / mδ x + 1 / mδ x + 1 + 1 / mδ x ^ τ := by
        field_simp; ring
      rw [hexp, hKaux]
      have ha : mδ x ^ τ / mδ x ≤ 1 / δ ^ (1 - τ) := hratio_pow
      have hb : 1 / mδ x ≤ 1 / δ := one_div_le_one_div_of_le hδ (le_max_right _ _)
      have hc : 1 / mδ x ^ τ ≤ 1 / δ ^ τ := by
        apply one_div_le_one_div_of_le (Real.rpow_pos_of_pos hδ τ)
        exact Real.rpow_le_rpow hδ.le (le_max_right _ _) hτ_nn
      linarith
    -- `(1/m_δ+1/m_δ^τ) ≤ Kaux/(m_δ^τ+1)`.
    have hpre_le : 1 / mδ x + 1 / mδ x ^ τ ≤ Kaux / (mδ x ^ τ + 1) := by
      rw [le_div_iff₀ hden_pos]; exact hkey
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hLHS_nn,
      abs_of_nonneg hdom_nn, one_mul]
    calc (1 / mδ x + 1 / mδ x ^ τ) * (‖fun i => Dg i x‖ ^ αt + 1)
        ≤ Kaux / (mδ x ^ τ + 1) * (‖fun i => Dg i x‖ ^ αt + 1) :=
          mul_le_mul_of_nonneg_right hpre_le hnum1_nn
      _ = Kaux * (‖fun i => Dg i x‖ ^ αt / (mδ x ^ τ + 1)
            + 1 / (mδ x ^ τ + 1)) := by
          rw [add_div]; ring
      _ ≤ Kaux * (‖fun i => Dg i x‖ ^ αt / (mδ x ^ τ + 1) + 1) := by
          apply mul_le_mul_of_nonneg_left _ hKaux_nn
          have : 1 / (mδ x ^ τ + 1) ≤ 1 := by
            rw [div_le_one hden_pos]; linarith
          linarith
  -- Scale the two pieces by `K` and assemble the full dominator.
  have hK_ratio : MemLpPer (d := d) βBar'
      (fun x => K * ((1 / mδ x + 1 / mδ x ^ τ) * (‖fun i => Dg i x‖ ^ αt + 1))) := by
    have hh := hRatio_full.const_smul (𝕜 := ℝ) K
    have heq : (K • fun x : Fin d → ℝ =>
          (1 / mδ x + 1 / mδ x ^ τ) * (‖fun i => Dg i x‖ ^ αt + 1))
        = (fun x => K * ((1 / mδ x + 1 / mδ x ^ τ)
            * (‖fun i => Dg i x‖ ^ αt + 1))) := by
      funext x; simp [Pi.smul_apply, smul_eq_mul]
    rw [heq] at hh; exact hh
  have hK_mβ : MemLpPer (d := d) βBar' (fun x => K * (mδ x ^ β + 1)) := by
    have hh := hmδβ_dom.const_smul (𝕜 := ℝ) K
    have heq : (K • fun x : Fin d → ℝ => mδ x ^ β + 1)
        = (fun x => K * (mδ x ^ β + 1)) := by
      funext x; simp [Pi.smul_apply, smul_eq_mul]
    rw [heq] at hh; exact hh
  -- `|u+φ_c| ∈ L^{β̄'}` and `|V| ∈ L^{β̄'}`.
  have huφ : MemLpPer (d := d) βBar' (fun x => u x + φ_c x) := by
    have := hu_memBeta.add hφ_c; simpa [hβBar'def] using! this
  have h_abs_uφ : MemLpPer (d := d) βBar' (fun x => |u x + φ_c x|) := by
    refine ⟨huφ.aestronglyMeasurable.norm.congr
      (Filter.Eventually.of_forall (fun x => (Real.norm_eq_abs _).symm)), ?_⟩
    have heq : eLpNormPer βBar' (fun x => |u x + φ_c x|)
        = eLpNormPer βBar' (fun x => u x + φ_c x) := by
      unfold eLpNormPer
      have : (fun x => ‖|u x + φ_c x|‖) = (fun x => ‖u x + φ_c x‖) := by
        funext x; rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_abs]
      rw [show (fun x => |u x + φ_c x|) = (fun x => ‖u x + φ_c x‖) from by
        funext x; rw [Real.norm_eq_abs]]
      rw [eLpNorm_norm _ huφ.aestronglyMeasurable]
    rw [heq]; exact huφ.eLpNormPer_lt_top
  have h_abs_V : MemLpPer (d := d) βBar' (fun x => |V x|) := by
    refine ⟨hV.aestronglyMeasurable.norm.congr
      (Filter.Eventually.of_forall (fun x => (Real.norm_eq_abs _).symm)), ?_⟩
    have heq : eLpNormPer βBar' (fun x => |V x|) = eLpNormPer βBar' V := by
      unfold eLpNormPer
      rw [show (fun x => |V x|) = (fun x => ‖V x‖) from by
        funext x; rw [Real.norm_eq_abs]]
      rw [eLpNorm_norm _ hV.aestronglyMeasurable]
    rw [heq]; exact hV.eLpNormPer_lt_top
  -- Combined dominator.
  have hdom : MemLpPer (d := d) βBar'
      (fun x => K * ((1 / mδ x + 1 / mδ x ^ τ) * (‖fun i => Dg i x‖ ^ αt + 1))
        + K * (mδ x ^ β + 1) + |u x + φ_c x| + |V x|) :=
    ((hK_ratio.add hK_mβ).add h_abs_uφ).add h_abs_V
  -- AE-strong-measurability of the target function.
  have hF_meas : AEStronglyMeasurable
      (fun x => -(u x + φ_c x) - H x (fun i => Dg i x) (mδ x) + V x)
      (Measure.restrict volume (UnitCube d)) :=
    ((huφ.aestronglyMeasurable.neg.sub hH_comp_meas).add
      hV.aestronglyMeasurable)
  -- The final domination.
  rw [hβBar'def] at hdom ⊢
  apply MemLp.toMemLpPer
  apply MemLp.of_le_mul (c := 1) hdom.toMemLp hF_meas
  filter_upwards [hHbnd] with x hxH
  set px : Fin d → ℝ := fun i => Dg i x with hpx
  have hxH' := hxH px (mδ x) (hmδ_pos x)
  -- Triangle inequality.
  have htri : |(-(u x + φ_c x) - H x px (mδ x) + V x)|
      ≤ |u x + φ_c x| + |H x px (mδ x)| + |V x| := by
    have hdecomp : -(u x + φ_c x) - H x px (mδ x) + V x
        = (-(u x + φ_c x)) + (-(H x px (mδ x))) + V x := by ring
    rw [hdecomp]
    calc |(-(u x + φ_c x)) + (-(H x px (mδ x))) + V x|
        ≤ |(-(u x + φ_c x)) + (-(H x px (mδ x)))| + |V x| := abs_add_le _ _
      _ ≤ (|(-(u x + φ_c x))| + |(-(H x px (mδ x)))|) + |V x| := by
          gcongr; exact abs_add_le _ _
      _ = |u x + φ_c x| + |H x px (mδ x)| + |V x| := by
          rw [abs_neg, abs_neg]
  -- Convert the H-bound `hxH'` to the local `αt` exponent.
  have hxH'' : |H x px (mδ x)|
      ≤ K * (1 / mδ x + 1 / mδ x ^ τ) * (‖px‖ ^ αt + 1)
        + K * (mδ x ^ β + 1) := by
    have := hxH'
    rw [hαtdef, hαdef, hβdef, hτdef]
    convert this using 3
  have hpre_nn : 0 ≤ 1 / mδ x + 1 / mδ x ^ τ := by
    have := hmδ_pos x; positivity
  have hnum1_nn : 0 ≤ ‖px‖ ^ αt + 1 := by positivity
  have hdom_nn : 0 ≤ K * ((1 / mδ x + 1 / mδ x ^ τ) * (‖px‖ ^ αt + 1))
        + K * (mδ x ^ β + 1) + |u x + φ_c x| + |V x| := by
    have h1 : 0 ≤ K * ((1 / mδ x + 1 / mδ x ^ τ) * (‖px‖ ^ αt + 1)) :=
      mul_nonneg hK_pos.le (mul_nonneg hpre_nn hnum1_nn)
    have h2 : 0 ≤ K * (mδ x ^ β + 1) :=
      mul_nonneg hK_pos.le (by positivity)
    linarith [abs_nonneg (u x + φ_c x), abs_nonneg (V x)]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hdom_nn, one_mul]
  have hKeq : K * (1 / mδ x + 1 / mδ x ^ τ) * (‖px‖ ^ αt + 1)
      = K * ((1 / mδ x + 1 / mδ x ^ τ) * (‖px‖ ^ αt + 1)) := by ring
  linarith [htri, hxH'', hKeq]

open StationaryMFG.Periodic in
/-- **Keystone B.** Each component `m_δ · D_pH(·, Dg, m_δ)ᵢ` of the flux
factor lies in `L^{γ̄'}_per`, with `m_δ = max(m, δ) ≥ δ > 0`. Re-derives
the flux well-definedness of the operator at the perturbed point, using
the `D_pH` growth bound `hcong.DpH_upper` and the flux dominator
membership `congestion_flux_dominator_memLp_gammaBar'_le`. -/
theorem mDpH_at_perturbed_memLp_gammaBar'
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    {m : (Fin d → ℝ) → ℝ}
    {Dg : Fin d → (Fin d → ℝ) → ℝ}
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) m)
    (hm_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hDg_memGamma : ∀ i,
      MemLpPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Dg i))
    {δ : ℝ} (hδ : 0 < δ) (i : Fin d) :
    MemLpPer (d := d)
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β
        / (hcong.α * (hcong.β + 1) / hcong.β - 1)))
      (fun x => max (m x) δ * DpH x (fun j => Dg j x) (max (m x) δ) i) := by
  classical
  set α : ℝ := hcong.α with hαdef
  set β : ℝ := hcong.β with hβdef
  set τ : ℝ := hcong.τ with hτdef
  have hα : 1 < α := hcong.hα
  have hβ : 0 < β := hcong.hβ
  have hτ_nn : 0 ≤ τ := hcong.hτ.1
  have hτ_le : τ ≤ 1 := hcong.hτ.2
  have hC_pos : 0 < hcong.C := hcong.hC
  haveI hfin : IsFiniteMeasure
      (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  set mδ : (Fin d → ℝ) → ℝ := fun x => max (m x) δ with hmδdef
  have hmδ_pos : ∀ x, 0 < mδ x := fun x => lt_of_lt_of_le hδ (le_max_right _ _)
  have hmδ_mem : MemLpPer (d := d) (ENNReal.ofReal (β + 1)) mδ := by
    have := mPerDelta_memLpPer (d := d) (p := ENNReal.ofReal (β + 1))
      (δ := δ) hδ.le (m := m) (by rw [hβdef]; exact hm_mem) hm_nn
    simpa [mPerDelta, hmδdef] using! this
  have hmδ_nn : 0 ≤ᵐ[Measure.restrict volume (UnitCube d)] mδ :=
    Filter.Eventually.of_forall (fun x => (hmδ_pos x).le)
  -- The flux dominator membership at `m = m_δ`, `Du = Dg`, `K = C`.
  have hflux_dom := congestion_flux_dominator_memLp_gammaBar'_le
    (d := d) (α := α) (β := β) (τ := τ) (K := hcong.C)
    hα hβ hτ_nn hτ_le (m := mδ) (Du := fun j x => Dg j x)
    hmδ_mem hmδ_nn (fun j => by rw [hαdef, hβdef]; exact hDg_memGamma j)
  -- AE-strong-measurability of `x ↦ m_δ · DpH(x, Dg, m_δ)ᵢ`.
  have hDpH_meas : AEStronglyMeasurable
      (fun x => mδ x * DpH x (fun j => Dg j x) (mδ x) i)
      (Measure.restrict volume (UnitCube d)) := by
    have hid : AEMeasurable (fun x : Fin d → ℝ => x)
        (volume.restrict (UnitCube d)) := aemeasurable_id
    have hDg' : AEMeasurable (fun x => (fun j => Dg j x))
        (volume.restrict (UnitCube d)) := by
      rw [aemeasurable_pi_iff]; intro j
      exact aestronglyMeasurable_iff_aemeasurable.mp (hDg_memGamma j).aestronglyMeasurable
    have hmδ' : AEMeasurable mδ (volume.restrict (UnitCube d)) :=
      aestronglyMeasurable_iff_aemeasurable.mp hmδ_mem.aestronglyMeasurable
    have hprod : AEMeasurable
        (fun x : Fin d → ℝ => (x, (fun j => Dg j x), mδ x))
        (volume.restrict (UnitCube d)) := hid.prodMk (hDg'.prodMk hmδ')
    have hvec : AEMeasurable (fun x => DpH x (fun j => Dg j x) (mδ x))
        (volume.restrict (UnitCube d)) :=
      hcong.measurable_DpH.comp_aemeasurable hprod
    have hcomp : AEMeasurable
        (fun x => DpH x (fun j => Dg j x) (mδ x) i)
        (volume.restrict (UnitCube d)) :=
      (measurable_pi_apply i).comp_aemeasurable hvec
    exact (hmδ'.mul hcomp).aestronglyMeasurable
  -- Pointwise domination `|m_δ·DpH_i| ≤ flux dominator`.
  have hbound : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ‖mδ x * DpH x (fun j => Dg j x) (mδ x) i‖
        ≤ hcong.C * (1 + mδ x ^ (1 - τ))
              * ‖fun j => Dg j x‖ ^ (α * (1 + τ / β) - 1)
            + hcong.C * (mδ x ^ (β + 1 - β / α) + 1) := by
    filter_upwards [hcong.DpH_upper] with x hx
    set px : Fin d → ℝ := fun j => Dg j x with hpx
    have hpos := hmδ_pos x
    have hDpH_le := hx px (mδ x) hpos
    -- `|m_δ·DpH_i| ≤ m_δ·‖DpH‖`.
    have hcomp_le : |mδ x * DpH x px (mδ x) i| ≤ mδ x * ‖DpH x px (mδ x)‖ := by
      rw [abs_mul, abs_of_pos hpos]
      apply mul_le_mul_of_nonneg_left _ hpos.le
      have := norm_le_pi_norm (DpH x px (mδ x)) i
      simpa [Real.norm_eq_abs] using this
    -- Multiply the `DpH` bound by `m_δ` and simplify the rpow algebra.
    have hmul : mδ x * ‖DpH x px (mδ x)‖
        ≤ hcong.C * (1 + mδ x ^ (1 - τ)) * ‖px‖ ^ (α * (1 + τ / β) - 1)
          + hcong.C * (mδ x ^ (β + 1 - β / α) + 1) := by
      have hstep := mul_le_mul_of_nonneg_left hDpH_le hpos.le
      refine le_trans hstep (le_of_eq ?_)
      -- `m_δ·[C(1/m_δ+1/m_δ^τ)‖p‖^{αt-1} + C(m_δ^{β-β/α}+1/m_δ)]`
      --   = C(1+m_δ^{1-τ})‖p‖^{αt-1} + C(m_δ^{β+1-β/α}+1).
      have hmne : mδ x ≠ 0 := ne_of_gt hpos
      have hmδ_one : mδ x = mδ x ^ (1 : ℝ) := (Real.rpow_one _).symm
      have e1 : mδ x * (1 / mδ x) = 1 := by field_simp
      have e2 : mδ x * (1 / mδ x ^ τ) = mδ x ^ (1 - τ) := by
        rw [mul_one_div, Real.rpow_sub hpos, Real.rpow_one]
      have e3 : mδ x * mδ x ^ (β - β / α) = mδ x ^ (β + 1 - β / α) := by
        rw [show β + 1 - β / α = 1 + (β - β / α) by ring, Real.rpow_add hpos,
          Real.rpow_one]
      calc mδ x * (hcong.C * (1 / mδ x + 1 / mδ x ^ τ) * ‖px‖ ^ (α*(1+τ/β)-1)
              + hcong.C * (mδ x ^ (β - β/α) + 1 / mδ x))
          = hcong.C * (mδ x * (1/mδ x) + mδ x * (1/mδ x^τ))
                * ‖px‖ ^ (α*(1+τ/β)-1)
            + hcong.C * (mδ x * mδ x ^ (β - β/α) + mδ x * (1/mδ x)) := by ring
        _ = hcong.C * (1 + mδ x ^ (1-τ)) * ‖px‖ ^ (α*(1+τ/β)-1)
            + hcong.C * (mδ x ^ (β+1-β/α) + 1) := by
              rw [e1, e2, e3]
    rw [Real.norm_eq_abs]; exact le_trans hcomp_le hmul
  -- Conclude via `MemLp.of_le_mul` against the flux dominator.
  have hgoal : MemLpPer (d := d)
      (ENNReal.ofReal (α * (β + 1) / β / (α * (β + 1) / β - 1)))
      (fun x => mδ x * DpH x (fun j => Dg j x) (mδ x) i) := by
    apply MemLp.toMemLpPer
    apply MemLp.of_le_mul (c := 1) hflux_dom.toMemLp hDpH_meas
    filter_upwards [hbound] with x hx
    have hdom_nn : 0 ≤ hcong.C * (1 + mδ x ^ (1 - τ))
              * ‖fun j => Dg j x‖ ^ (α * (1 + τ / β) - 1)
            + hcong.C * (mδ x ^ (β + 1 - β / α) + 1) := by
      have h1 : 0 ≤ hcong.C * (1 + mδ x ^ (1 - τ))
          * ‖fun j => Dg j x‖ ^ (α * (1 + τ / β) - 1) := by positivity
      have h2 : 0 ≤ hcong.C * (mδ x ^ (β + 1 - β / α) + 1) := by positivity
      linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hdom_nn, one_mul]
    rw [Real.norm_eq_abs] at hx
    exact hx
  rw [hαdef, hβdef]; exact hgoal

open StationaryMFG.Periodic in
/-- **First-variation connector integrands are integrable.**

For fixed `t > 0`, `δ > 0`, the three connector integrands at the
truncated density `m_δ = max(m, δ)` and the perturbed gradient
`Du + t∇φ` (`φ_c = t·φ`, `Dφ_c = t·∇φ`) are integrable on the cube. This
is the integrability prerequisite for the algebraic half of child-4b-i,
which then closes `h_VI_at_mdelta` by `integral_add`/`integral_sub`
+ `integral_mono_ae` + `linarith`.

The three certificates:
* `LHSc x := (u + φ_c − C·(m_δ^β+1) − V)·(m_δ − m)` — connector LHS;
* `RHSc x := (m_δ−1)·φ_c + m_δ·(D_pH(Du+Dφ_c, m_δ) ⬝ Dφ_c)` — connector RHS;
* `Mterm x := (−(u+φ_c) − H(Du+Dφ_c, m_δ) + V)·(m_δ−m)` — child-3 HJB term.

The HJB and mass factors pair against the test density `m_δ − m ∈ L^{β̄}`
in `L^{β̄'}` (`H_at_perturbed_memLp_betaBar'`, keystone A); the flux
components pair against the smooth `Dφ_c ∈ L^{γ̄}` in `L^{γ̄'}`
(`mDpH_at_perturbed_memLp_gammaBar'`, keystone B). -/
theorem firstvar_integrands_integrable
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) m)
    (hm_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hu_memGamma : MemLpPer (d := d)
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) u)
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (hDu_memGamma : ∀ i,
      MemLpPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Du i))
    (φ : Periodic.SmoothPeriodic d) {δ : ℝ} (hδ : 0 < δ) {t : ℝ}
    -- The perturbed-point ratio integrability (a certified residue from
    -- `mdelta_admissibility` at the call site).
    (hRatio_pert : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
      (fun x => ‖fun i => Du i x
            + t * (Periodic.SmoothPeriodic.partialDeriv i φ : (Fin d → ℝ) → ℝ) x‖
          ^ (hcong.α * (1 + hcong.τ / hcong.β))
        / (max (m x) δ ^ hcong.τ + 1))) :
    -- LHSc, RHSc, Mterm are integrable on the cube.
    (IntegrableOn (fun x =>
        (u x + t * (φ : (Fin d → ℝ) → ℝ) x
            - hcong.C * (max (m x) δ ^ hcong.β + 1) - V x)
          * (max (m x) δ - m x)) (UnitCube d))
    ∧ (IntegrableOn (fun x =>
        (max (m x) δ - 1) * (t * (φ : (Fin d → ℝ) → ℝ) x)
          + max (m x) δ * (DpH x
              (fun i => Du i x
                + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                    (Fin d → ℝ) → ℝ) x)
              (max (m x) δ)
            ⬝ (fun i => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                (Fin d → ℝ) → ℝ) x))) (UnitCube d))
    ∧ (IntegrableOn (fun x =>
        (-(u x + t * (φ : (Fin d → ℝ) → ℝ) x)
            - H x (fun i => Du i x
                + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                    (Fin d → ℝ) → ℝ) x)
              (max (m x) δ) + V x)
          * (max (m x) δ - m x)) (UnitCube d)) := by
  classical
  set α : ℝ := hcong.α with hαdef
  set β : ℝ := hcong.β with hβdef
  set τ : ℝ := hcong.τ with hτdef
  have hα : 1 < α := hcong.hα
  have hβ : 0 < β := hcong.hβ
  haveI hfin : IsFiniteMeasure
      (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  -- Abbreviations.
  set φ_c : (Fin d → ℝ) → ℝ := fun x => t * (φ : (Fin d → ℝ) → ℝ) x with hφc
  set Dg : Fin d → (Fin d → ℝ) → ℝ :=
    fun i x => Du i x
      + t * (Periodic.SmoothPeriodic.partialDeriv i φ : (Fin d → ℝ) → ℝ) x
    with hDg
  set mδ : (Fin d → ℝ) → ℝ := fun x => max (m x) δ with hmδdef
  -- Smooth-function memberships (`φ`, `∂ᵢφ` in every `L^p`).
  have hφ_betaP : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β)) φ_c := by
    have hraw : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
        ((φ : (Fin d → ℝ) → ℝ)) :=
      (Periodic.MemSobolevPer.of_smoothPeriodic _ φ).1
    have := hraw.const_smul (𝕜 := ℝ) t
    have heq : (t • (φ : (Fin d → ℝ) → ℝ)) = φ_c := by
      funext x; simp [hφc, Pi.smul_apply, smul_eq_mul]
    rwa [heq] at this
  have hφ_gamma : MemLpPer (d := d)
      (ENNReal.ofReal (α * (β + 1) / β)) φ_c := by
    have hraw : MemLpPer (d := d) (ENNReal.ofReal (α * (β + 1) / β))
        ((φ : (Fin d → ℝ) → ℝ)) :=
      (Periodic.MemSobolevPer.of_smoothPeriodic _ φ).1
    have := hraw.const_smul (𝕜 := ℝ) t
    have heq : (t • (φ : (Fin d → ℝ) → ℝ)) = φ_c := by
      funext x; simp [hφc, Pi.smul_apply, smul_eq_mul]
    rwa [heq] at this
  have hDφ_gamma : ∀ i, MemLpPer (d := d)
      (ENNReal.ofReal (α * (β + 1) / β))
      (fun x => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
          (Fin d → ℝ) → ℝ) x) := by
    intro i
    have hraw : MemLpPer (d := d) (ENNReal.ofReal (α * (β + 1) / β))
        ((Periodic.SmoothPeriodic.partialDeriv i φ : (Fin d → ℝ) → ℝ)) :=
      (Periodic.MemSobolevPer.of_smoothPeriodic _
        (Periodic.SmoothPeriodic.partialDeriv i φ)).1
    have := hraw.const_smul (𝕜 := ℝ) t
    have heq : (t • (Periodic.SmoothPeriodic.partialDeriv i φ : (Fin d → ℝ) → ℝ))
        = (fun x => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
            (Fin d → ℝ) → ℝ) x) := by
      funext x; simp [Pi.smul_apply, smul_eq_mul]
    rwa [heq] at this
  -- `Dg i ∈ L^{γ̄}` and measurable.
  have hDg_gamma : ∀ i, MemLpPer (d := d)
      (ENNReal.ofReal (α * (β + 1) / β)) (Dg i) := by
    intro i
    have := (by rw [hαdef, hβdef]; exact hDu_memGamma i : MemLpPer (d := d)
      (ENNReal.ofReal (α * (β + 1) / β)) (Du i)).add (hDφ_gamma i)
    have heq : (Du i + fun x => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
        (Fin d → ℝ) → ℝ) x) = Dg i := by
      funext x; simp [hDg, Pi.add_apply]
    rwa [heq] at this
  -- `m_δ ∈ L^{β̄}` and `m_δ − m ∈ L^{β̄}`.
  have hmδ_mem : MemLpPer (d := d) (ENNReal.ofReal (β + 1)) mδ := by
    have := mPerDelta_memLpPer (d := d) (p := ENNReal.ofReal (β + 1))
      (δ := δ) hδ.le (m := m) (by rw [hβdef]; exact hm_mem) hm_nn
    simpa [mPerDelta, hmδdef] using! this
  have hmδm : MemLpPer (d := d) (ENNReal.ofReal (β + 1))
      (fun x => mδ x - m x) := by
    have := hmδ_mem.add ((by rw [hβdef]; exact hm_mem :
      MemLpPer (d := d) (ENNReal.ofReal (β + 1)) m).const_smul (𝕜 := ℝ) (-1 : ℝ))
    have heq : (mδ + (-1 : ℝ) • m) = (fun x => mδ x - m x) := by
      funext x; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rwa [heq] at this
  -- `m_δ − 1 ∈ L^{β̄}` and `u ∈ L^{β̄'}`.
  have hmδ1 : MemLpPer (d := d) (ENNReal.ofReal (β + 1))
      (fun x => mδ x - 1) := by
    have := hmδ_mem.add_const (-1 : ℝ)
    have heq : (mδ + fun _ : Fin d → ℝ => (-1 : ℝ)) = (fun x => mδ x - 1) := by
      funext x; simp [Pi.add_apply]; ring
    rwa [heq] at this
  have hu_betaP : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β)) u :=
    u_memLp_betaBar' hα hβ (by rw [hαdef, hβdef]; exact hu_memGamma)
  -- Hölder conjugacies.
  have hβconj : Real.HolderConjugate (β + 1) ((β + 1) / β) :=
    Theorems.SimplePower.SimplePowerExponentFacts.paper_holderConjugate_betaBar hβ
  have hγconj : Real.HolderConjugate (α * (β + 1) / β)
      (α * (β + 1) / β / (α * (β + 1) / β - 1)) :=
    Theorems.SimplePower.SimplePowerExponentFacts.paper_holderConjugate_gammaBar hα hβ
  -- ===== Keystone memberships at the perturbed point. =====
  have hHfac : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
      (fun x => -(u x + φ_c x) - H x (fun i => Dg i x) (mδ x) + V x) := by
    have := H_at_perturbed_memLp_betaBar' (d := d) hmon hcong
      (m := m) (u := u) (V := V) (Dg := Dg) hm_mem hm_nn
      hu_betaP hV (fun i => (hDg_gamma i).aestronglyMeasurable)
      φ_c hφ_betaP hδ ?_
    · simpa [hαdef, hβdef, hτdef, hmδdef, hφc, hDg] using this
    · simpa [hαdef, hβdef, hτdef, hmδdef, hDg] using hRatio_pert
  have hflux : ∀ i, MemLpPer (d := d)
      (ENNReal.ofReal (α * (β + 1) / β / (α * (β + 1) / β - 1)))
      (fun x => mδ x * DpH x (fun j => Dg j x) (mδ x) i) := by
    intro i
    have := mDpH_at_perturbed_memLp_gammaBar' (d := d) hcong
      (m := m) (Dg := Dg) hm_mem hm_nn hDg_gamma hδ i
    simpa [hαdef, hβdef, hmδdef, hDg] using this
  -- ===== LHSc integrability. =====
  have hLHSfac : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
      (fun x => u x + φ_c x - hcong.C * (mδ x ^ β + 1) - V x) := by
    have hCmβ : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
        (fun x => hcong.C * (mδ x ^ β + 1)) := by
      have hpow : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
          (fun x => mδ x ^ β) :=
        rpow_beta_memLp_betaBar' hβ hmδ_mem
          (Filter.Eventually.of_forall (fun x =>
            (lt_of_lt_of_le hδ (le_max_right _ _)).le))
      have hone : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
          (fun _ : (Fin d → ℝ) => (1 : ℝ)) := MemLp.toMemLpPer (memLp_const 1)
      have := (hpow.add hone).const_smul (𝕜 := ℝ) hcong.C
      have heq : (hcong.C • ((fun x => mδ x ^ β) + fun _ : Fin d → ℝ => (1:ℝ)))
          = (fun x => hcong.C * (mδ x ^ β + 1)) := by
        funext x; simp [Pi.smul_apply, smul_eq_mul, Pi.add_apply]
      rwa [heq] at this
    have h1 := (hu_betaP.add hφ_betaP)
    have h2 := h1.add (hCmβ.const_smul (𝕜 := ℝ) (-1 : ℝ))
    have h3 := h2.add (hV.const_smul (𝕜 := ℝ) (-1 : ℝ))
    have heq : ((u + φ_c) + (-1 : ℝ) • (fun x => hcong.C * (mδ x ^ β + 1)))
          + (-1 : ℝ) • V
        = (fun x => u x + φ_c x - hcong.C * (mδ x ^ β + 1) - V x) := by
      funext x; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rwa [heq] at h3
  have hLHSc : IntegrableOn (fun x =>
      (u x + φ_c x - hcong.C * (mδ x ^ β + 1) - V x) * (mδ x - m x))
      (UnitCube d) :=
    MemLpPer.integrable_mul hβconj.symm hLHSfac hmδm
  -- ===== Mterm integrability. =====
  have hMterm : IntegrableOn (fun x =>
      (-(u x + φ_c x) - H x (fun i => Dg i x) (mδ x) + V x) * (mδ x - m x))
      (UnitCube d) :=
    MemLpPer.integrable_mul hβconj.symm hHfac hmδm
  -- ===== RHSc integrability. =====
  -- mass part `(m_δ − 1)·φ_c`.
  have hRHSmass : IntegrableOn (fun x => (mδ x - 1) * φ_c x) (UnitCube d) :=
    MemLpPer.integrable_mul hβconj hmδ1 hφ_betaP
  -- flux part: `m_δ·(DpH ⬝ Dφ_c) = Σᵢ (m_δ·DpH_i)·(Dφ_c i)`.
  have hRHSflux_i : ∀ i, IntegrableOn
      (fun x => (mδ x * DpH x (fun j => Dg j x) (mδ x) i)
        * (t * (Periodic.SmoothPeriodic.partialDeriv i φ : (Fin d → ℝ) → ℝ) x))
      (UnitCube d) :=
    fun i => MemLpPer.integrable_mul hγconj.symm (hflux i) (hDφ_gamma i)
  have hRHSflux : IntegrableOn
      (fun x => mδ x * (DpH x (fun j => Dg j x) (mδ x)
          ⬝ (fun i => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
              (Fin d → ℝ) → ℝ) x))) (UnitCube d) := by
    have hsum : IntegrableOn
        (fun x => ∑ i : Fin d, (mδ x * DpH x (fun j => Dg j x) (mδ x) i)
          * (t * (Periodic.SmoothPeriodic.partialDeriv i φ :
              (Fin d → ℝ) → ℝ) x)) (UnitCube d) :=
      MeasureTheory.integrable_finset_sum Finset.univ (fun i _ => hRHSflux_i i)
    refine hsum.congr (Filter.Eventually.of_forall (fun x => ?_))
    show ∑ i : Fin d, (mδ x * DpH x (fun j => Dg j x) (mδ x) i)
          * (t * (Periodic.SmoothPeriodic.partialDeriv i φ :
              (Fin d → ℝ) → ℝ) x)
        = mδ x * ∑ i : Fin d, DpH x (fun j => Dg j x) (mδ x) i
            * (t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                (Fin d → ℝ) → ℝ) x)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  have hRHSc : IntegrableOn (fun x =>
      (mδ x - 1) * φ_c x
        + mδ x * (DpH x (fun j => Dg j x) (mδ x)
            ⬝ (fun i => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                (Fin d → ℝ) → ℝ) x))) (UnitCube d) :=
    hRHSmass.add hRHSflux
  -- Assemble (rewriting the abbreviations back to the literal forms).
  refine ⟨?_, ?_, ?_⟩
  · simpa [hαdef, hβdef, hmδdef, hφc] using hLHSc
  · simpa [hαdef, hβdef, hmδdef, hφc, hDg] using hRHSc
  · simpa [hαdef, hβdef, hmδdef, hφc, hDg] using hMterm

/-! ## `t ∈ [−1, 1]`-uniform integrable dominators `gA`, `gB` for the
`t → 0` DCT (T2 phase6 BB VIid **child-4d-A**)

`iota_firstorder_h_lim_dct` consumes two `t`-uniform integrable dominators
`gA`, `gB` (with `‖FA t x‖ ≤ gA x`, `‖FB t x‖ ≤ gB x` eventually as `t → 0`,
i.e. for `|t| ≤ 1`). They are produced at the **limit** density `m`
(untruncated, `m ≥ 0` a.e.) and are independent of `t`, obtained by
replacing the perturbed momentum norm `‖Du + t∇φ‖` by its `|t| ≤ 1`-uniform
majorant `‖Du‖ + ‖∇φ‖` (triangle inequality + `|t| ≤ 1`) and using
`rpow`-monotonicity.

* `gB` (the `ε`-Gateaux dominator) reuses the natural-form Gateaux
  dominator `g_gat_natural` and its integrability producer
  `g_gat_natural_integrableOn`, with the pointwise `|t| ≤ 1`-uniform bound
  derived directly from `abs_vecAbsPowMinusTwo_mul_dot_le` /
  `abs_absPowMinusTwo_mul_self` (the perturbation `Du + t∇φ` is bounded by
  `|Du| + |∇φ|` componentwise for `|t| ≤ 1`).
* `gA` (the flux dominator) uses `CongestionGrowthCore.DpH_upper`
  multiplied by `m` (the keystone-B algebra of
  `mDpH_at_perturbed_memLp_gammaBar'`, at the limit density `m` rather than
  `m_δ`): on `{0 < m x}` the bound is the scalar flux dominator at
  `N = ‖Du‖ + ‖∇φ‖`, on `{m x = 0}` the `m`-prefactor annihilates the flux
  term (`0 ≤` the nonneg dominator). The scalar-`N` flux dominator
  `L^{γ̄'}` membership is `iota_flux_dominator_scalar_memLp_gammaBar'`
  (the scalar sibling of `congestion_flux_dominator_memLp_gammaBar'_le`).
-/

open StationaryMFG.Periodic in
/-- **Scalar `L^{γ̄'}` flux dominator** (scalar sibling of
`congestion_flux_dominator_memLp_gammaBar'_le`). For a nonneg scalar
`N ∈ L^{γ̄}_per` (with `γ̄ = α(β+1)/β`) and `m ∈ L^{β̄}_per`, `m ≥ 0` a.e.,
the explicit dominator
`K·(1+m^{1-τ})·N^{αt-1} + K·(m^{β+1-β/α}+1)`
(with `αt = α(1+τ/β)`) lies in `L^{γ̄'}_per`. Re-derives
`congestion_flux_dominator_memLp_gammaBar'` with the vector norm
`‖fun j => Du j x‖` replaced by the scalar `N x` (uses `N ≥ 0` so
`‖N x‖ = N x`). -/
theorem iota_flux_dominator_scalar_memLp_gammaBar'
    {α β τ K : ℝ} (hα : 1 < α) (hβ : 0 < β) (hτ_nn : 0 ≤ τ) (hτ_le : τ ≤ 1)
    {m N : (Fin d → ℝ) → ℝ}
    (hm : MemLpPer (d := d) (ENNReal.ofReal (β + 1)) m)
    (hm_nn : 0 ≤ᵐ[Measure.restrict volume (UnitCube d)] m)
    (hN : MemLpPer (d := d) (ENNReal.ofReal (α * (β + 1) / β)) N)
    (hN_nn : 0 ≤ᵐ[Measure.restrict volume (UnitCube d)] N) :
    MemLpPer (d := d)
      (ENNReal.ofReal ((α * (β + 1) / β) / (α * (β + 1) / β - 1)))
      (fun x =>
        K * (1 + m x ^ (1 - τ)) * N x ^ (α * (1 + τ / β) - 1)
            + K * (m x ^ (β + 1 - β / α) + 1)) := by
  classical
  haveI hfin : IsFiniteMeasure
      (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  set βbar : ℝ := β + 1 with hβbar
  set γbar : ℝ := α * (β + 1) / β with hγbar
  set γbar' : ℝ := γbar / (γbar - 1) with hγbar'
  set αt : ℝ := α * (1 + τ / β) with hαt
  have hαpos : 0 < α := lt_trans one_pos hα
  have hβbar_pos : 0 < βbar := by rw [hβbar]; linarith
  have hγbar_pos : 0 < γbar := by rw [hγbar]; positivity
  have hγbar_gt_one : 1 < γbar := by rw [hγbar, lt_div_iff₀ hβ]; nlinarith
  have hγbar'_pos : 0 < γbar' := by rw [hγbar']; apply div_pos hγbar_pos; linarith
  have hαt_gt_one : 1 < αt := by
    rw [hαt]
    have : 1 + τ / β ≥ 1 := by have := div_nonneg hτ_nn hβ.le; linarith
    nlinarith
  have hαtm1_pos : 0 < αt - 1 := by linarith
  -- `N` rewritten through its nonnegativity: `‖N x‖ = N x` a.e.
  have hN_norm : MemLpPer (d := d) (ENNReal.ofReal γbar)
      (fun x => ‖N x‖) := MemLp.toMemLpPer (MeasureTheory.MemLp.norm hN.toMemLp)
  -- Piece A: `‖N‖^{αt-1} ∈ L^{γ̄/(αt-1)}` by rpow-closure.
  set sN : ℝ≥0∞ := ENNReal.ofReal (γbar / (αt - 1)) with hsN
  have hsN_eq : sN * ENNReal.ofReal (αt - 1) = ENNReal.ofReal γbar := by
    rw [hsN, ← ENNReal.ofReal_mul (by positivity)]; congr 1; field_simp
  have hN_pow : MemLpPer (d := d) sN (fun x => ‖N x‖ ^ (αt - 1)) :=
    Periodic.MemLpPer.rpow_closure (d := d) (s := sN) (r := αt - 1)
      hαtm1_pos (f := N) (by rw [hsN_eq]; exact hN)
  -- Piece B: `m^{1-τ} ∈ L^{β̄/(1-τ)}` (split by `τ < 1` / `τ = 1`).
  -- Piece D: `m^{β+1-β/α} ∈ L^{γ̄'}` by rpow-closure.
  set e : ℝ := β + 1 - β / α with he
  have he_pos : 0 < e := by
    rw [he]
    have : β / α < β := by rw [div_lt_iff₀ hαpos]; nlinarith
    linarith
  set sme : ℝ≥0∞ := ENNReal.ofReal (βbar / e) with hsme
  have hsme_eq : sme * ENNReal.ofReal e = ENNReal.ofReal βbar := by
    rw [hsme, ← ENNReal.ofReal_mul (by positivity)]; congr 1; field_simp
  have hm_pow_e : MemLpPer (d := d) sme (fun x => ‖m x‖ ^ e) :=
    Periodic.MemLpPer.rpow_closure (d := d) (s := sme) (r := e)
      he_pos (f := m) (by rw [hsme_eq]; exact hm)
  have hsme_eq_γ' : sme = ENNReal.ofReal γbar' := by
    rw [hsme]; congr 1
    rw [hγbar', hγbar, hβbar, he]
    have hαne : α ≠ 0 := ne_of_gt hαpos
    have hβne : β ≠ 0 := ne_of_gt hβ
    field_simp
  have hm_pow_e' : MemLpPer (d := d) (ENNReal.ofReal γbar')
      (fun x => ‖m x‖ ^ e) := by rw [← hsme_eq_γ']; exact hm_pow_e
  -- The abs-version dominator, built as a sum of `L^{γ̄'}` pieces.
  -- `N`-power inclusion to `L^{γ̄'}` (Piece A↪γ̄', γ̄' ≤ sN by finite cube).
  have hγbar'_le_sN : ENNReal.ofReal γbar' ≤ sN := by
    rw [hsN]; apply ENNReal.ofReal_le_ofReal
    have hsN_pos : 0 < γbar / (αt - 1) := by positivity
    have hid : 1 / γbar' = (1 - τ) / βbar + (αt - 1) / γbar := by
      rw [hγbar', hγbar, hβbar, hαt]
      exact gammaBar'_holder_id_congestion (α := α) (β := β) (τ := τ) hα hβ
    refine (one_div_le_one_div hsN_pos hγbar'_pos).mp ?_
    rw [one_div_div]
    have hnn : 0 ≤ (1 - τ) / βbar := div_nonneg (by linarith) hβbar_pos.le
    linarith [hid]
  have hN_pow_γ' : MemLpPer (d := d) (ENNReal.ofReal γbar')
      (fun x => ‖N x‖ ^ (αt - 1)) :=
    Periodic.MemLpPer.mono_exponent_finite hγbar'_le_sN
      ENNReal.ofReal_ne_top hN_pow
  -- `m^{1-τ}·‖N‖^{αt-1} ∈ L^{γ̄'}`.
  have h1mτ_nn : 0 ≤ 1 - τ := by linarith
  rcases eq_or_lt_of_le hτ_le with hτ_eq | hτ_lt
  · -- `τ = 1`: `m^{1-τ} = m^0 = 1`, the `m`-factor collapses.
    have hτ1 : τ = 1 := hτ_eq
    have hdom_abs : MemLpPer (d := d) (ENNReal.ofReal γbar')
        (fun x => K * (1 + ‖m x‖ ^ (1 - τ)) * ‖N x‖ ^ (αt - 1)
            + K * (‖m x‖ ^ e + 1)) := by
      have hone : MemLpPer (d := d) (ENNReal.ofReal γbar')
          (fun _ : (Fin d → ℝ) => (1 : ℝ)) := MemLp.toMemLpPer (memLp_const 1)
      -- term1 = K·(1+m^0)·‖N‖^{αt-1} = K·2·‖N‖^{αt-1}.
      have hterm1 : MemLpPer (d := d) (ENNReal.ofReal γbar')
          (fun x => K * (1 + ‖m x‖ ^ (1 - τ)) * ‖N x‖ ^ (αt - 1)) := by
        have h := hN_pow_γ'.const_smul (𝕜 := ℝ) (K * 2)
        have heq : ((K * 2) • fun x => ‖N x‖ ^ (αt - 1))
            = (fun x => K * (1 + ‖m x‖ ^ (1 - τ)) * ‖N x‖ ^ (αt - 1)) := by
          funext x; simp only [Pi.smul_apply, smul_eq_mul, hτ1, sub_self,
            Real.rpow_zero]; ring
        rwa [heq] at h
      have hterm2 : MemLpPer (d := d) (ENNReal.ofReal γbar')
          (fun x => K * (‖m x‖ ^ e + 1)) := by
        have h := (hm_pow_e'.add hone).const_smul (𝕜 := ℝ) K
        have heq : (K • ((fun x => ‖m x‖ ^ e) + fun _ : Fin d → ℝ => (1:ℝ)))
            = (fun x => K * (‖m x‖ ^ e + 1)) := by
          funext x; simp [Pi.smul_apply, smul_eq_mul, Pi.add_apply]
        rwa [heq] at h
      have hsum := hterm1.add hterm2
      have heq : ((fun x => K * (1 + ‖m x‖ ^ (1 - τ)) * ‖N x‖ ^ (αt - 1))
            + fun x => K * (‖m x‖ ^ e + 1))
          = (fun x => K * (1 + ‖m x‖ ^ (1 - τ)) * ‖N x‖ ^ (αt - 1)
              + K * (‖m x‖ ^ e + 1)) := by
        funext x; simp only [Pi.add_apply]
      rw [heq] at hsum; exact hsum
    have hae : (fun x => K * (1 + ‖m x‖ ^ (1 - τ)) * ‖N x‖ ^ (αt - 1)
            + K * (‖m x‖ ^ e + 1))
        =ᵐ[Measure.restrict volume (UnitCube d)]
        (fun x => K * (1 + m x ^ (1 - τ)) * N x ^ (αt - 1)
            + K * (m x ^ (β + 1 - β / α) + 1)) := by
      filter_upwards [hm_nn, hN_nn] with x hmx hNx
      rw [Real.norm_eq_abs, abs_of_nonneg hmx, Real.norm_eq_abs,
        abs_of_nonneg hNx, ← he]
    have := MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq hae hdom_abs.toMemLp)
    simpa [hβbar, hγbar, hγbar', hαt] using this
  · -- `τ < 1`: the genuine Hölder-partition step (mirrors the vector lemma).
    have h1mτ_pos : 0 < 1 - τ := by linarith
    set sm : ℝ≥0∞ := ENNReal.ofReal (βbar / (1 - τ)) with hsm
    have hsm_eq : sm * ENNReal.ofReal (1 - τ) = ENNReal.ofReal βbar := by
      rw [hsm, ← ENNReal.ofReal_mul (by positivity)]; congr 1; field_simp
    have hm_pow : MemLpPer (d := d) sm (fun x => ‖m x‖ ^ (1 - τ)) :=
      Periodic.MemLpPer.rpow_closure (d := d) (s := sm) (r := 1 - τ)
        h1mτ_pos (f := m) (by rw [hsm_eq]; exact hm)
    -- Hölder triple `(sm, sN, ofReal γ̄')`.
    haveI hHolder : ENNReal.HolderTriple sm sN (ENNReal.ofReal γbar') := by
      rw [hsm, hsN]
      have hid := gammaBar'_holder_id_congestion (α := α) (β := β) (τ := τ) hα hβ
      -- `hid : 1/γ̄' = (1-τ)/β̄ + (αt-1)/γ̄` in the literal exponents.
      refine ⟨?_⟩
      rw [← ENNReal.ofReal_inv_of_pos (by positivity),
        ← ENNReal.ofReal_inv_of_pos (by positivity),
        ← ENNReal.ofReal_inv_of_pos hγbar'_pos,
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      have hid' : 1 / γbar' = (1 - τ) / βbar + (αt - 1) / γbar := by
        rw [hγbar', hγbar, hβbar, hαt]; exact hid
      rw [inv_div, inv_div, inv_eq_one_div, hid']
    have hprod : MemLpPer (d := d) (ENNReal.ofReal γbar')
        (fun x => ‖m x‖ ^ (1 - τ) * ‖N x‖ ^ (αt - 1)) :=
      Periodic.MemLpPer.mul_holderTriple (p := sm) (q := sN)
        (s := ENNReal.ofReal γbar') hm_pow hN_pow
    have hdom_abs : MemLpPer (d := d) (ENNReal.ofReal γbar')
        (fun x => K * (1 + ‖m x‖ ^ (1 - τ)) * ‖N x‖ ^ (αt - 1)
            + K * (‖m x‖ ^ e + 1)) := by
      have hsum1 : MemLpPer (d := d) (ENNReal.ofReal γbar')
          (fun x => ‖N x‖ ^ (αt - 1)
              + ‖m x‖ ^ (1 - τ) * ‖N x‖ ^ (αt - 1)) := by
        have := hN_pow_γ'.add hprod; simpa using! this
      have hterm1 : MemLpPer (d := d) (ENNReal.ofReal γbar')
          (fun x => K * (1 + ‖m x‖ ^ (1 - τ)) * ‖N x‖ ^ (αt - 1)) := by
        have hrw : (fun x => K * (1 + ‖m x‖ ^ (1 - τ)) * ‖N x‖ ^ (αt - 1))
            = (fun x => K • (‖N x‖ ^ (αt - 1)
                + ‖m x‖ ^ (1 - τ) * ‖N x‖ ^ (αt - 1))) := by
          funext x; simp only [smul_eq_mul]; ring
        rw [hrw]; exact hsum1.const_smul (𝕜 := ℝ) K
      have hone : MemLpPer (d := d) (ENNReal.ofReal γbar')
          (fun _ : (Fin d → ℝ) => (1 : ℝ)) := MemLp.toMemLpPer (memLp_const 1)
      have hterm2 : MemLpPer (d := d) (ENNReal.ofReal γbar')
          (fun x => K * (‖m x‖ ^ e + 1)) := by
        have h := (hm_pow_e'.add hone).const_smul (𝕜 := ℝ) K
        have heq : (K • ((fun x => ‖m x‖ ^ e) + fun _ : Fin d → ℝ => (1:ℝ)))
            = (fun x => K * (‖m x‖ ^ e + 1)) := by
          funext x; simp [Pi.smul_apply, smul_eq_mul, Pi.add_apply]
        rwa [heq] at h
      have hsum := hterm1.add hterm2
      have heq : ((fun x => K * (1 + ‖m x‖ ^ (1 - τ)) * ‖N x‖ ^ (αt - 1))
            + fun x => K * (‖m x‖ ^ e + 1))
          = (fun x => K * (1 + ‖m x‖ ^ (1 - τ)) * ‖N x‖ ^ (αt - 1)
              + K * (‖m x‖ ^ e + 1)) := by
        funext x; simp only [Pi.add_apply]
      rw [heq] at hsum; exact hsum
    have hae : (fun x => K * (1 + ‖m x‖ ^ (1 - τ)) * ‖N x‖ ^ (αt - 1)
            + K * (‖m x‖ ^ e + 1))
        =ᵐ[Measure.restrict volume (UnitCube d)]
        (fun x => K * (1 + m x ^ (1 - τ)) * N x ^ (αt - 1)
            + K * (m x ^ (β + 1 - β / α) + 1)) := by
      filter_upwards [hm_nn, hN_nn] with x hmx hNx
      rw [Real.norm_eq_abs, abs_of_nonneg hmx, Real.norm_eq_abs,
        abs_of_nonneg hNx, ← he]
    have := MemLp.toMemLpPer (MeasureTheory.MemLp.ae_eq hae hdom_abs.toMemLp)
    simpa [hβbar, hγbar, hγbar', hαt] using this

open StationaryMFG.Periodic in
/-- **`t ∈ [−1,1]`-uniform integrable dominator `gB` for the ε-Gateaux
integrand `FB`** (child-4d-A). For `1 < γ̄`, given `Du i, u ∈ L^{γ̄}_per`
and `Dφ i, φ ∈ L^{γ̄}_per`, the function

```
gB x = |ε| · g_gat_natural γ̄ Du Dφ u φ Dφ φ x
```

is integrable on the cube and bounds `‖FB t x‖` for every `|t| ≤ 1`. The
pointwise bound comes from `abs_vecAbsPowMinusTwo_mul_dot_le` /
`abs_absPowMinusTwo_mul_self`, with the perturbation `Du + t∇φ` majorised
componentwise by `|Du| + |∇φ|` (since `|t| ≤ 1`). The conclusion is in the
exact `(hgB_int, hboundB)` shape consumed by `iota_firstorder_h_lim_dct`. -/
theorem iota_FB_uniform_dominator
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {u : (Fin d → ℝ) → ℝ}
    {ε γBar γBar' : ℝ} (hγ : 1 < γBar)
    (hγconj : γBar'.HolderConjugate γBar)
    (φ : (Fin d → ℝ) → ℝ)
    (Dφ : Fin d → (Fin d → ℝ) → ℝ)
    (hu : MemLpPer (d := d) (ENNReal.ofReal γBar) u)
    (hφ : MemLpPer (d := d) (ENNReal.ofReal γBar) φ)
    (hDu : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBar) (Du i))
    (hDφ : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBar) (Dφ i))
    (FB : ℝ → (Fin d → ℝ) → ℝ)
    (hFBdef : ∀ t, FB t = fun x =>
      ε * vecAbsPowMinusTwo γBar (fun i => Du i x + t * Dφ i x)
          * ((fun i => Du i x + t * Dφ i x) ⬝ (fun i => Dφ i x))
        + ε * absPowMinusTwo γBar (u x + t * φ x)
            * ((u x + t * φ x) * φ x)) :
    ∃ gB : (Fin d → ℝ) → ℝ,
      Integrable gB (volume.restrict (UnitCube d))
      ∧ (∀ᶠ t in nhds (0 : ℝ),
          ∀ᵐ x ∂(volume.restrict (UnitCube d)), ‖FB t x‖ ≤ gB x) := by
  classical
  haveI hfin : IsFiniteMeasure
      (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  -- Hölder exponent facts: `γ̄' · (γ̄ − 1) = γ̄`, `γ̄' > 0`, `γ̄ − 1 > 0`.
  have hγm1_pos : 0 < γBar - 1 := by linarith
  have hγBar'_pos : 0 < γBar' := hγconj.pos
  have hγpos : 0 < γBar := lt_trans one_pos hγ
  have hconjmul : γBar' * (γBar - 1) = γBar := by
    have hinv := hγconj.inv_add_inv_eq_inv
    have hγne : γBar ≠ 0 := ne_of_gt hγpos
    have hγ'ne : γBar' ≠ 0 := ne_of_gt hγBar'_pos
    rw [inv_one] at hinv
    field_simp at hinv ⊢
    nlinarith [hinv]
  have hclose : ENNReal.ofReal γBar' * ENNReal.ofReal (γBar - 1)
      = ENNReal.ofReal γBar := by
    rw [← ENNReal.ofReal_mul hγBar'_pos.le, hconjmul]
  -- The natural-form Gateaux dominator, scaled by `|ε|`.
  set g0 : (Fin d → ℝ) → ℝ :=
    Theorems.SimplePower.Banach.g_gat_natural γBar Du Dφ u φ Dφ φ with hg0
  -- `|Dφ i| + |Du i| ∈ L^{γ̄}`; their sum `S ∈ L^{γ̄}`.
  have hWi : ∀ i, MemLpPer (d := d) (ENNReal.ofReal γBar)
      (fun x => |Dφ i x| + |Du i x|) := fun i =>
    (MemLp.toMemLpPer ((hDφ i).toMemLp.abs)).add (MemLp.toMemLpPer ((hDu i).toMemLp.abs))
  have hS : MemLpPer (d := d) (ENNReal.ofReal γBar)
      (fun x => ∑ i, (|Dφ i x| + |Du i x|)) :=
    MemLp.toMemLpPer (MeasureTheory.memLp_finset_sum (Finset.univ : Finset (Fin d))
      (f := fun i x => |Dφ i x| + |Du i x|) (fun i _ => (hWi i).toMemLp) :
      MemLp _ _ _)
  -- `T := |φ| + |u| ∈ L^{γ̄}`.
  have hT : MemLpPer (d := d) (ENNReal.ofReal γBar)
      (fun x => |φ x| + |u x|) :=
    (MemLp.toMemLpPer hφ.toMemLp.abs).add (MemLp.toMemLpPer hu.toMemLp.abs)
  refine ⟨fun x => |ε| * g0 x, ?_, ?_⟩
  · -- Integrability of `g0` via `g_gat_natural_integrableOn`, then scale.
    -- Grad block: `(∑ (|Dφ|+|Du|)²)^{(γ̄-1)/2} ≤ (∑(|Dφ|+|Du|))^{γ̄-1} ∈ L^{γ̄'}`.
    have hSpow : MemLpPer (d := d) (ENNReal.ofReal γBar')
        (fun x => ‖∑ i, (|Dφ i x| + |Du i x|)‖ ^ (γBar - 1)) :=
      Periodic.MemLpPer.rpow_closure (d := d) (s := ENNReal.ofReal γBar')
        (r := γBar - 1) hγm1_pos
        (f := fun x => ∑ i, (|Dφ i x| + |Du i x|)) (by rw [hclose]; exact hS)
    have hG_grad : MemLpPer (d := d) (ENNReal.ofReal γBar')
        (fun x => (∑ i, (|Dφ i x| + |Du i x|) ^ (2 : ℕ)) ^ ((γBar - 1) / 2)) := by
      have hmeas : AEStronglyMeasurable
          (fun x => (∑ i, (|Dφ i x| + |Du i x|) ^ (2 : ℕ)) ^ ((γBar - 1) / 2))
          (Measure.restrict volume (UnitCube d)) := by
        have hsum : AEStronglyMeasurable
            (fun x => ∑ i, (|Dφ i x| + |Du i x|) ^ (2 : ℕ))
            (Measure.restrict volume (UnitCube d)) := by
          refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
          have hi : AEStronglyMeasurable (fun x => |Dφ i x| + |Du i x|)
              (Measure.restrict volume (UnitCube d)) :=
            ((hDφ i).aestronglyMeasurable.norm.congr
              (Filter.Eventually.of_forall (fun _ => (Real.norm_eq_abs _).symm))).add
            ((hDu i).aestronglyMeasurable.norm.congr
              (Filter.Eventually.of_forall (fun _ => (Real.norm_eq_abs _).symm)))
          exact hi.pow 2
        exact (Real.continuous_rpow_const (by linarith)).comp_aestronglyMeasurable hsum
      refine MemLp.toMemLpPer (MemLp.of_le_mul (c := 1) hSpow.toMemLp hmeas
        (Filter.Eventually.of_forall (fun x => ?_)))
      -- Pointwise: `(∑aᵢ²)^{(γ̄-1)/2} ≤ ‖∑aᵢ‖^{γ̄-1}`.
      set a : Fin d → ℝ := fun i => |Dφ i x| + |Du i x| with ha
      have ha_nn : ∀ i, 0 ≤ a i := fun i => by positivity
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
      rw [Real.norm_eq_abs (((∑ i, a i ^ (2:ℕ)) ^ ((γBar-1)/2))), one_mul,
        Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      calc |(∑ i, a i ^ (2 : ℕ)) ^ ((γBar - 1) / 2)|
          = (∑ i, a i ^ (2 : ℕ)) ^ ((γBar - 1) / 2) :=
            abs_of_nonneg (Real.rpow_nonneg hsumsq_nn _)
        _ ≤ ((∑ i, a i) ^ (2 : ℕ)) ^ ((γBar - 1) / 2) := hbase
        _ = ‖∑ i, a i‖ ^ (γBar - 1) := hrhs
    -- Val block: `(|φ|+|u|)^{γ̄-1} ∈ L^{γ̄'}` directly via rpow_closure.
    have hG_val : MemLpPer (d := d) (ENNReal.ofReal γBar')
        (fun x => (|φ x| + |u x|) ^ (γBar - 1)) := by
      have h := Periodic.MemLpPer.rpow_closure (d := d) (s := ENNReal.ofReal γBar')
        (r := γBar - 1) hγm1_pos (f := fun x => |φ x| + |u x|)
        (by rw [hclose]; exact hT)
      have heq : (fun x => ‖|φ x| + |u x|‖ ^ (γBar - 1))
          = (fun x => (|φ x| + |u x|) ^ (γBar - 1)) := by
        funext x; rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rwa [heq] at h
    have hg0_int : IntegrableOn g0 (UnitCube d) :=
      Theorems.SimplePower.Banach.g_gat_natural_integrableOn
        (γBar := γBar) (γBar' := γBar') hγconj hDφ hφ hG_grad hG_val
    exact hg0_int.const_mul |ε|
  · -- Uniform bound for `|t| ≤ 1`.
    refine Filter.eventually_iff_exists_mem.mpr ⟨Metric.ball (0 : ℝ) 1,
      Metric.ball_mem_nhds 0 one_pos, fun t ht => ?_⟩
    have ht1 : |t| ≤ 1 := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht; linarith
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [hFBdef]
    set v : Fin d → ℝ := fun i => Du i x + t * Dφ i x with hv
    set w : Fin d → ℝ := fun i => Dφ i x with hw
    -- Vector term bound.
    have hvec : ‖ε * vecAbsPowMinusTwo γBar v * (v ⬝ w)‖
        ≤ |ε| * ((∑ i, (|Dφ i x| + |Du i x|) ^ (2 : ℕ)) ^ ((γBar - 1) / 2)
            * (∑ i, |Dφ i x|)) := by
      rw [show ε * vecAbsPowMinusTwo γBar v * (v ⬝ w)
          = ε * (vecAbsPowMinusTwo γBar v * (v ⬝ w)) by ring,
        norm_mul, Real.norm_eq_abs ε, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg ε)
      refine le_trans (Theorems.SimplePower.abs_vecAbsPowMinusTwo_mul_dot_le hγ v w) ?_
      -- base bound `v⬝v ≤ ∑(|Dφ|+|Du|)²` for `|t| ≤ 1`; `∑|wᵢ| = ∑|Dφᵢ|`.
      have hvv : v ⬝ v ≤ ∑ i, (|Dφ i x| + |Du i x|) ^ (2 : ℕ) := by
        unfold euclideanDot
        refine Finset.sum_le_sum (fun i _ => ?_)
        have hvi : |v i| ≤ |Dφ i x| + |Du i x| := by
          have : |v i| ≤ |Du i x| + |t| * |Dφ i x| := by
            rw [hv]; exact le_trans (abs_add_le _ _) (by rw [abs_mul])
          have h2 : |t| * |Dφ i x| ≤ |Dφ i x| := by
            rw [mul_comm]; exact mul_le_of_le_one_right (abs_nonneg _) ht1
          linarith [this, h2]
        have hvi_sq : v i * v i ≤ (|Dφ i x| + |Du i x|) ^ (2 : ℕ) := by
          have h0 : 0 ≤ |Dφ i x| + |Du i x| := by positivity
          have hself : v i * v i = |v i| * |v i| := (abs_mul_abs_self (v i)).symm
          rw [hself, pow_two]
          exact mul_le_mul hvi hvi (abs_nonneg _) h0
        exact hvi_sq
      have hexp_nn : 0 ≤ (γBar - 1) / 2 := by linarith
      have hbase : (v ⬝ v) ^ ((γBar - 1) / 2)
          ≤ (∑ i, (|Dφ i x| + |Du i x|) ^ (2 : ℕ)) ^ ((γBar - 1) / 2) :=
        Real.rpow_le_rpow (Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)) hvv hexp_nn
      have hsum_nn : 0 ≤ ∑ i, |Dφ i x| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      have hwsum : (∑ i, |w i|) = ∑ i, |Dφ i x| := rfl
      rw [hwsum]
      exact mul_le_mul_of_nonneg_right hbase hsum_nn
    -- Scalar term bound.
    have hsc : ‖ε * absPowMinusTwo γBar (u x + t * φ x) * ((u x + t * φ x) * φ x)‖
        ≤ |ε| * ((|φ x| + |u x|) ^ (γBar - 1) * |φ x|) := by
      rw [show ε * absPowMinusTwo γBar (u x + t * φ x) * ((u x + t * φ x) * φ x)
          = ε * (absPowMinusTwo γBar (u x + t * φ x) * ((u x + t * φ x) * φ x)) by ring,
        norm_mul, Real.norm_eq_abs ε, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg ε)
      rw [show absPowMinusTwo γBar (u x + t * φ x) * ((u x + t * φ x) * φ x)
          = (absPowMinusTwo γBar (u x + t * φ x) * (u x + t * φ x)) * φ x by ring,
        abs_mul, Theorems.SimplePower.abs_absPowMinusTwo_mul_self hγ]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      have hut : |u x + t * φ x| ≤ |φ x| + |u x| := by
        have : |u x + t * φ x| ≤ |u x| + |t| * |φ x| := by
          exact le_trans (abs_add_le _ _) (by rw [abs_mul])
        have h2 : |t| * |φ x| ≤ |φ x| := by
          rw [mul_comm]; exact mul_le_of_le_one_right (abs_nonneg _) ht1
        linarith
      exact Real.rpow_le_rpow (abs_nonneg _) hut (by linarith)
    -- Combine.
    refine le_trans (norm_add_le _ _) ?_
    show ‖ε * vecAbsPowMinusTwo γBar v * (v ⬝ w)‖
        + ‖ε * absPowMinusTwo γBar (u x + t * φ x) * ((u x + t * φ x) * φ x)‖
        ≤ |ε| * g0 x
    have hg0x : g0 x = (∑ i, (|Dφ i x| + |Du i x|) ^ (2 : ℕ)) ^ ((γBar - 1) / 2)
            * (∑ i, |Dφ i x|)
          + (|φ x| + |u x|) ^ (γBar - 1) * |φ x| := by
      rw [hg0]; rfl
    rw [hg0x, mul_add]
    exact add_le_add hvec hsc

open StationaryMFG.Periodic in
/-- **`t ∈ [−1,1]`-uniform integrable dominator `gA` for the flux
integrand `FA`** (child-4d-A). At the limit density `m` (untruncated,
`m ≥ 0` a.e.), with `Du i ∈ L^{γ̄}_per`, `m ∈ L^{β̄}_per`, `φ ∈ L^{β̄'}_per`
and the smooth test gradient `Dφ i ∈ L^{γ̄}_per`, the function

```
gA x = |m x − 1| · |φ x|
     + (C·(1+m^{1-τ})·N^{αt-1} + C·(m^{β+1-β/α}+1)) · (∑ i, |Dφ i x|)
```

with `N x = ‖Du · x‖ + ‖Dφ · x‖`, is integrable on the cube and bounds
`‖FA t x‖` for every `|t| ≤ 1`. The flux factor `m·‖D_pH(x, Du+t∇φ, m)‖` is
bounded via `CongestionGrowthCore.DpH_upper` (multiplied by `m`, the
keystone-B algebra) using `‖Du+t∇φ‖ ≤ N` for `|t| ≤ 1`; on `{m x = 0}` the
`m`-prefactor annihilates the flux term. Conclusion in the
`(hgA_int, hboundA)` shape of `iota_firstorder_h_lim_dct`. -/
theorem iota_FA_uniform_dominator
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    {m : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) m)
    (hm_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hDu_memGamma : ∀ i,
      MemLpPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Du i))
    (φ : (Fin d → ℝ) → ℝ)
    (Dφ : Fin d → (Fin d → ℝ) → ℝ)
    (hφ_betaP : MemLpPer (d := d)
      (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) φ)
    (hDφ_memGamma : ∀ i,
      MemLpPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Dφ i))
    (FA : ℝ → (Fin d → ℝ) → ℝ)
    (hFAdef : ∀ t, FA t = fun x =>
      (m x - 1) * φ x
        + m x * (DpH x (fun i => Du i x + t * Dφ i x) (m x)
            ⬝ (fun i => Dφ i x))) :
    ∃ gA : (Fin d → ℝ) → ℝ,
      Integrable gA (volume.restrict (UnitCube d))
      ∧ (∀ᶠ t in nhds (0 : ℝ),
          ∀ᵐ x ∂(volume.restrict (UnitCube d)), ‖FA t x‖ ≤ gA x) := by
  classical
  set α : ℝ := hcong.α with hαdef
  set β : ℝ := hcong.β with hβdef
  set τ : ℝ := hcong.τ with hτdef
  set C : ℝ := hcong.C with hCdef
  have hα : 1 < α := hcong.hα
  have hβ : 0 < β := hcong.hβ
  have hτ_nn : 0 ≤ τ := hcong.hτ.1
  have hτ_le : τ ≤ 1 := hcong.hτ.2
  have hC_pos : 0 < C := hcong.hC
  have hαpos : 0 < α := lt_trans one_pos hα
  haveI hfin : IsFiniteMeasure
      (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  -- The `|t| ≤ 1`-uniform majorant `N x = ‖Du·x‖ + ‖Dφ·x‖`.
  set N : (Fin d → ℝ) → ℝ :=
    fun x => ‖fun i => Du i x‖ + ‖fun i => Dφ i x‖ with hN
  have hN_nn : 0 ≤ᵐ[Measure.restrict volume (UnitCube d)] N :=
    Filter.Eventually.of_forall (fun x => by rw [hN]; positivity)
  -- `N ∈ L^{γ̄}`.
  have hDuvec : MemLpPer (d := d) (ENNReal.ofReal (α * (β + 1) / β))
      (fun x => ‖fun i => Du i x‖) := by
    have hvec : MemLpPer (d := d) (ENNReal.ofReal (α * (β + 1) / β))
        (fun x => (fun i => Du i x)) := by
      rw [Periodic.memLpPer_iff_memLp, MeasureTheory.memLp_pi_iff]
      intro i; rw [hαdef, hβdef]; exact (hDu_memGamma i).toMemLp
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.norm hvec.toMemLp)
  have hDφvec : MemLpPer (d := d) (ENNReal.ofReal (α * (β + 1) / β))
      (fun x => ‖fun i => Dφ i x‖) := by
    have hvec : MemLpPer (d := d) (ENNReal.ofReal (α * (β + 1) / β))
        (fun x => (fun i => Dφ i x)) := by
      rw [Periodic.memLpPer_iff_memLp, MeasureTheory.memLp_pi_iff]
      intro i; rw [hαdef, hβdef]; exact (hDφ_memGamma i).toMemLp
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.norm hvec.toMemLp)
  have hN_mem : MemLpPer (d := d) (ENNReal.ofReal (α * (β + 1) / β)) N :=
    hDuvec.add hDφvec
  -- The scalar flux dominator `∈ L^{γ̄'}`.
  have hflux_dom := iota_flux_dominator_scalar_memLp_gammaBar'
    (d := d) (α := α) (β := β) (τ := τ) (K := C)
    hα hβ hτ_nn hτ_le (m := m) (N := N)
    (by rw [hβdef]; exact hm_mem) hm_nn hN_mem hN_nn
  -- `∑ i, |Dφ i x| ∈ L^{γ̄}`.
  have hsumDφ : MemLpPer (d := d) (ENNReal.ofReal (α * (β + 1) / β))
      (fun x => ∑ i, |Dφ i x|) :=
    MemLp.toMemLpPer (MeasureTheory.memLp_finset_sum (Finset.univ : Finset (Fin d))
      (f := fun i x => |Dφ i x|)
      (fun i _ => (((by rw [hαdef, hβdef]; exact hDφ_memGamma i :
        MemLpPer (d := d) (ENNReal.ofReal (α * (β + 1) / β)) (Dφ i)).toMemLp.abs) :
        MemLp _ _ _)) : MemLp _ _ _)
  -- `m − 1 ∈ L^{β̄}`.
  have hm1 : MemLpPer (d := d) (ENNReal.ofReal (β + 1)) (fun x => m x - 1) := by
    have := (by rw [hβdef]; exact hm_mem :
      MemLpPer (d := d) (ENNReal.ofReal (β + 1)) m).add_const (-1 : ℝ)
    have heq : (m + fun _ : Fin d → ℝ => (-1 : ℝ)) = (fun x => m x - 1) := by
      funext x; simp [Pi.add_apply]; ring
    rwa [heq] at this
  -- Hölder conjugacies.
  have hβconj : Real.HolderConjugate (β + 1) ((β + 1) / β) :=
    Theorems.SimplePower.SimplePowerExponentFacts.paper_holderConjugate_betaBar hβ
  have hγconj : Real.HolderConjugate (α * (β + 1) / β)
      (α * (β + 1) / β / (α * (β + 1) / β - 1)) :=
    Theorems.SimplePower.SimplePowerExponentFacts.paper_holderConjugate_gammaBar hα hβ
  -- The dominator `gA`.
  refine ⟨fun x =>
      |m x - 1| * |φ x|
        + (C * (1 + m x ^ (1 - τ)) * N x ^ (α * (1 + τ / β) - 1)
            + C * (m x ^ (β + 1 - β / α) + 1)) * (∑ i, |Dφ i x|), ?_, ?_⟩
  · -- Integrability: mass term (β̄, β̄') + flux term (γ̄', γ̄).
    have hmass : IntegrableOn (fun x => |m x - 1| * |φ x|) (UnitCube d) := by
      have habs_m1 : MemLpPer (d := d) (ENNReal.ofReal (β + 1))
          (fun x => |m x - 1|) := MemLp.toMemLpPer hm1.toMemLp.abs
      have habs_φ : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
          (fun x => |φ x|) := MemLp.toMemLpPer hφ_betaP.toMemLp.abs
      exact MemLpPer.integrable_mul hβconj habs_m1 habs_φ
    have hfluxI : IntegrableOn (fun x =>
        (C * (1 + m x ^ (1 - τ)) * N x ^ (α * (1 + τ / β) - 1)
            + C * (m x ^ (β + 1 - β / α) + 1)) * (∑ i, |Dφ i x|)) (UnitCube d) :=
      MemLpPer.integrable_mul hγconj.symm hflux_dom hsumDφ
    exact hmass.add hfluxI
  · -- Uniform bound for `|t| ≤ 1`.
    refine Filter.eventually_iff_exists_mem.mpr ⟨Metric.ball (0 : ℝ) 1,
      Metric.ball_mem_nhds 0 one_pos, fun t ht => ?_⟩
    have ht1 : |t| ≤ 1 := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht; linarith
    rw [hFAdef]
    filter_upwards [hcong.DpH_upper, hm_nn] with x hxDpH hxm
    set p : Fin d → ℝ := fun i => Du i x + t * Dφ i x with hp
    -- `‖p‖ ≤ N x` for `|t| ≤ 1`.
    have hp_le_N : ‖p‖ ≤ N x := by
      rw [hN]
      have : ‖p‖ ≤ ‖fun i => Du i x‖ + ‖fun i => t * Dφ i x‖ := by
        have heq : p = (fun i => Du i x) + (fun i => t * Dφ i x) := by
          funext i; rw [hp]; simp [Pi.add_apply]
        rw [heq]; exact norm_add_le _ _
      have hsmul : ‖fun i => t * Dφ i x‖ ≤ ‖fun i => Dφ i x‖ := by
        have : (fun i => t * Dφ i x) = t • (fun i => Dφ i x) := by
          funext i; simp [Pi.smul_apply, smul_eq_mul]
        rw [this, norm_smul, Real.norm_eq_abs]
        exact mul_le_of_le_one_left (norm_nonneg _) ht1
      linarith
    -- Mass term: `|(m−1)·φ| = |m−1|·|φ|`.
    have hmass_eq : |(m x - 1) * φ x| = |m x - 1| * |φ x| := abs_mul _ _
    -- Flux dot bound: `|D_pH ⬝ Dφ| ≤ ‖D_pH‖·(∑|Dφᵢ|)`.
    have hdot_le : |DpH x p (m x) ⬝ (fun i => Dφ i x)|
        ≤ ‖DpH x p (m x)‖ * (∑ i, |Dφ i x|) := by
      unfold euclideanDot
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun i _ => ?_)
      rw [abs_mul]
      have hcoord : |DpH x p (m x) i| ≤ ‖DpH x p (m x)‖ := by
        have := norm_le_pi_norm (DpH x p (m x)) i
        simpa [Real.norm_eq_abs] using this
      exact mul_le_mul_of_nonneg_right hcoord (abs_nonneg _)
    -- Flux factor bound, split on `m x = 0` / `m x > 0`.
    set fluxDom : ℝ := C * (1 + m x ^ (1 - τ)) * N x ^ (α * (1 + τ / β) - 1)
        + C * (m x ^ (β + 1 - β / α) + 1) with hfluxDom
    have hfluxDom_nn : 0 ≤ fluxDom := by
      rw [hfluxDom]
      have h1 : 0 ≤ C * (1 + m x ^ (1 - τ)) * N x ^ (α * (1 + τ / β) - 1) := by
        have hNnn : 0 ≤ N x := by rw [hN]; positivity
        positivity
      have h2 : 0 ≤ C * (m x ^ (β + 1 - β / α) + 1) := by
        have hmnn := hxm; positivity
      linarith
    have hflux_le : |m x * (DpH x p (m x) ⬝ (fun i => Dφ i x))|
        ≤ fluxDom * (∑ i, |Dφ i x|) := by
      rcases eq_or_lt_of_le hxm with hm0 | hmpos
      · -- `m x = 0`: flux term vanishes.
        rw [← hm0]; simp only [zero_mul, abs_zero]
        have hsum_nn : 0 ≤ ∑ i, |Dφ i x| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
        exact mul_nonneg hfluxDom_nn hsum_nn
      · -- `0 < m x`: keystone-B algebra at the limit density.
        rw [abs_mul, abs_of_pos hmpos]
        -- `m·‖DpH‖ ≤ fluxDom` via DpH_upper + rpow-mono in `‖p‖ ≤ N`.
        have hDpH_le := hxDpH p (m x) hmpos
        have hmul : m x * ‖DpH x p (m x)‖
            ≤ C * (1 + m x ^ (1 - τ)) * ‖p‖ ^ (α * (1 + τ / β) - 1)
              + C * (m x ^ (β + 1 - β / α) + 1) := by
          have hstep := mul_le_mul_of_nonneg_left hDpH_le hmpos.le
          refine le_trans hstep (le_of_eq ?_)
          have hmne : m x ≠ 0 := ne_of_gt hmpos
          have e1 : m x * (1 / m x) = 1 := by field_simp
          have e2 : m x * (1 / m x ^ τ) = m x ^ (1 - τ) := by
            rw [mul_one_div, Real.rpow_sub hmpos, Real.rpow_one]
          have e3 : m x * m x ^ (β - β / α) = m x ^ (β + 1 - β / α) := by
            rw [show β + 1 - β / α = 1 + (β - β / α) by ring, Real.rpow_add hmpos,
              Real.rpow_one]
          calc m x * (C * (1 / m x + 1 / m x ^ τ) * ‖p‖ ^ (α*(1+τ/β)-1)
                  + C * (m x ^ (β - β/α) + 1 / m x))
              = C * (m x * (1/m x) + m x * (1/m x^τ)) * ‖p‖ ^ (α*(1+τ/β)-1)
                + C * (m x * m x ^ (β - β/α) + m x * (1/m x)) := by ring
            _ = C * (1 + m x ^ (1-τ)) * ‖p‖ ^ (α*(1+τ/β)-1)
                + C * (m x ^ (β+1-β/α) + 1) := by rw [e1, e2, e3]
        -- Replace `‖p‖^{αt-1}` by `N^{αt-1}` (rpow-mono, `αt-1 ≥ 0`).
        have hαt_gt_one : 1 < α * (1 + τ / β) := by
          have : 1 + τ / β ≥ 1 := by have := div_nonneg hτ_nn hβ.le; linarith
          nlinarith
        have hexp_nn : 0 ≤ α * (1 + τ / β) - 1 := by linarith
        have hpow_le : ‖p‖ ^ (α * (1 + τ / β) - 1) ≤ N x ^ (α * (1 + τ / β) - 1) :=
          Real.rpow_le_rpow (norm_nonneg _) hp_le_N hexp_nn
        have hmul' : m x * ‖DpH x p (m x)‖ ≤ fluxDom := by
          rw [hfluxDom]
          refine le_trans hmul (add_le_add ?_ le_rfl)
          rw [mul_assoc, mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ hC_pos.le
          have hfac_nn : 0 ≤ 1 + m x ^ (1 - τ) := by
            have : 0 ≤ m x ^ (1 - τ) := Real.rpow_nonneg hxm _; linarith
          exact mul_le_mul_of_nonneg_left hpow_le hfac_nn
        -- Combine with the dot bound.
        have hsum_nn : 0 ≤ ∑ i, |Dφ i x| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
        calc m x * |DpH x p (m x) ⬝ (fun i => Dφ i x)|
            ≤ m x * (‖DpH x p (m x)‖ * (∑ i, |Dφ i x|)) :=
              mul_le_mul_of_nonneg_left hdot_le hmpos.le
          _ = (m x * ‖DpH x p (m x)‖) * (∑ i, |Dφ i x|) := by ring
          _ ≤ fluxDom * (∑ i, |Dφ i x|) :=
              mul_le_mul_of_nonneg_right hmul' hsum_nn
    -- Assemble.
    rw [Real.norm_eq_abs]
    refine le_trans (abs_add_le _ _) ?_
    rw [hmass_eq]
    exact add_le_add le_rfl hflux_le

open StationaryMFG.Periodic in
/-- **`J`-extension `t ∈ [−1,1]`-uniform integrable dominator `gA`**
(T2 phase6 BB VIid **child-5b**, part (b)).

The `J`-form sibling of `iota_FA_uniform_dominator`: the flux integrand is the
paper extension `FA t x = (m x − 1)·φ x + J(x, Du+t∇φ, m x) ⬝ ∇φ`. The dominator

```
gA x = |m x − 1| · |φ x|
     + (C·(1+m^{1-τ})·N^{αt-1} + C·(m^{β+1-β/α}+1)) · (∑ i, |Dφ i x|)
```

is the same as in the product form, but the flux factor `‖J(x, Du+t∇φ, m)‖` is
now bounded **uniformly across `{m = 0}`** by the closed-half-line `J`-envelope
`CongestionGrowthCore.mDpH_extended_bound` (valid for every `m ≥ 0`, no
`m`-prefactor case split). With `‖Du+t∇φ‖ ≤ N` for `|t| ≤ 1` the bound is
`t`-uniform. Conclusion in the `(hgA_int, hboundA)` shape of
`iota_firstorder_h_lim_dct_J`. -/
theorem iota_FA_uniform_dominator_J
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    {m : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) m)
    (hm_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hDu_memGamma : ∀ i,
      MemLpPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Du i))
    (φ : (Fin d → ℝ) → ℝ)
    (Dφ : Fin d → (Fin d → ℝ) → ℝ)
    (hφ_betaP : MemLpPer (d := d)
      (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) φ)
    (hDφ_memGamma : ∀ i,
      MemLpPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Dφ i))
    (FA : ℝ → (Fin d → ℝ) → ℝ)
    (hFAdef : ∀ t, FA t = fun x =>
      (m x - 1) * φ x
        + (J x (fun i => Du i x + t * Dφ i x) (m x)
            ⬝ (fun i => Dφ i x))) :
    ∃ gA : (Fin d → ℝ) → ℝ,
      Integrable gA (volume.restrict (UnitCube d))
      ∧ (∀ᶠ t in nhds (0 : ℝ),
          ∀ᵐ x ∂(volume.restrict (UnitCube d)), ‖FA t x‖ ≤ gA x) := by
  classical
  set α : ℝ := hcong.α with hαdef
  set β : ℝ := hcong.β with hβdef
  set τ : ℝ := hcong.τ with hτdef
  set C : ℝ := hcong.C with hCdef
  have hα : 1 < α := hcong.hα
  have hβ : 0 < β := hcong.hβ
  have hτ_nn : 0 ≤ τ := hcong.hτ.1
  have hτ_le : τ ≤ 1 := hcong.hτ.2
  have hC_pos : 0 < C := hcong.hC
  have hαpos : 0 < α := lt_trans one_pos hα
  haveI hfin : IsFiniteMeasure
      (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  -- The `|t| ≤ 1`-uniform majorant `N x = ‖Du·x‖ + ‖Dφ·x‖`.
  set N : (Fin d → ℝ) → ℝ :=
    fun x => ‖fun i => Du i x‖ + ‖fun i => Dφ i x‖ with hN
  have hN_nn : 0 ≤ᵐ[Measure.restrict volume (UnitCube d)] N :=
    Filter.Eventually.of_forall (fun x => by rw [hN]; positivity)
  -- `N ∈ L^{γ̄}`.
  have hDuvec : MemLpPer (d := d) (ENNReal.ofReal (α * (β + 1) / β))
      (fun x => ‖fun i => Du i x‖) := by
    have hvec : MemLpPer (d := d) (ENNReal.ofReal (α * (β + 1) / β))
        (fun x => (fun i => Du i x)) := by
      rw [Periodic.memLpPer_iff_memLp, MeasureTheory.memLp_pi_iff]
      intro i; rw [hαdef, hβdef]; exact (hDu_memGamma i).toMemLp
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.norm hvec.toMemLp)
  have hDφvec : MemLpPer (d := d) (ENNReal.ofReal (α * (β + 1) / β))
      (fun x => ‖fun i => Dφ i x‖) := by
    have hvec : MemLpPer (d := d) (ENNReal.ofReal (α * (β + 1) / β))
        (fun x => (fun i => Dφ i x)) := by
      rw [Periodic.memLpPer_iff_memLp, MeasureTheory.memLp_pi_iff]
      intro i; rw [hαdef, hβdef]; exact (hDφ_memGamma i).toMemLp
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.norm hvec.toMemLp)
  have hN_mem : MemLpPer (d := d) (ENNReal.ofReal (α * (β + 1) / β)) N :=
    hDuvec.add hDφvec
  -- The scalar flux dominator `∈ L^{γ̄'}`.
  have hflux_dom := iota_flux_dominator_scalar_memLp_gammaBar'
    (d := d) (α := α) (β := β) (τ := τ) (K := C)
    hα hβ hτ_nn hτ_le (m := m) (N := N)
    (by rw [hβdef]; exact hm_mem) hm_nn hN_mem hN_nn
  -- `∑ i, |Dφ i x| ∈ L^{γ̄}`.
  have hsumDφ : MemLpPer (d := d) (ENNReal.ofReal (α * (β + 1) / β))
      (fun x => ∑ i, |Dφ i x|) :=
    MemLp.toMemLpPer (MeasureTheory.memLp_finset_sum (Finset.univ : Finset (Fin d))
      (f := fun i x => |Dφ i x|)
      (fun i _ => (((by rw [hαdef, hβdef]; exact hDφ_memGamma i :
        MemLpPer (d := d) (ENNReal.ofReal (α * (β + 1) / β)) (Dφ i)).toMemLp.abs) :
        MemLp _ _ _)) : MemLp _ _ _)
  -- `m − 1 ∈ L^{β̄}`.
  have hm1 : MemLpPer (d := d) (ENNReal.ofReal (β + 1)) (fun x => m x - 1) := by
    have := (by rw [hβdef]; exact hm_mem :
      MemLpPer (d := d) (ENNReal.ofReal (β + 1)) m).add_const (-1 : ℝ)
    have heq : (m + fun _ : Fin d → ℝ => (-1 : ℝ)) = (fun x => m x - 1) := by
      funext x; simp [Pi.add_apply]; ring
    rwa [heq] at this
  -- Hölder conjugacies.
  have hβconj : Real.HolderConjugate (β + 1) ((β + 1) / β) :=
    Theorems.SimplePower.SimplePowerExponentFacts.paper_holderConjugate_betaBar hβ
  have hγconj : Real.HolderConjugate (α * (β + 1) / β)
      (α * (β + 1) / β / (α * (β + 1) / β - 1)) :=
    Theorems.SimplePower.SimplePowerExponentFacts.paper_holderConjugate_gammaBar hα hβ
  -- The dominator `gA`.
  refine ⟨fun x =>
      |m x - 1| * |φ x|
        + (C * (1 + m x ^ (1 - τ)) * N x ^ (α * (1 + τ / β) - 1)
            + C * (m x ^ (β + 1 - β / α) + 1)) * (∑ i, |Dφ i x|), ?_, ?_⟩
  · -- Integrability: mass term (β̄, β̄') + flux term (γ̄', γ̄).
    have hmass : IntegrableOn (fun x => |m x - 1| * |φ x|) (UnitCube d) := by
      have habs_m1 : MemLpPer (d := d) (ENNReal.ofReal (β + 1))
          (fun x => |m x - 1|) := MemLp.toMemLpPer hm1.toMemLp.abs
      have habs_φ : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
          (fun x => |φ x|) := MemLp.toMemLpPer hφ_betaP.toMemLp.abs
      exact MemLpPer.integrable_mul hβconj habs_m1 habs_φ
    have hfluxI : IntegrableOn (fun x =>
        (C * (1 + m x ^ (1 - τ)) * N x ^ (α * (1 + τ / β) - 1)
            + C * (m x ^ (β + 1 - β / α) + 1)) * (∑ i, |Dφ i x|)) (UnitCube d) :=
      MemLpPer.integrable_mul hγconj.symm hflux_dom hsumDφ
    exact hmass.add hfluxI
  · -- Uniform bound for `|t| ≤ 1`.
    refine Filter.eventually_iff_exists_mem.mpr ⟨Metric.ball (0 : ℝ) 1,
      Metric.ball_mem_nhds 0 one_pos, fun t ht => ?_⟩
    have ht1 : |t| ≤ 1 := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht; linarith
    rw [hFAdef]
    filter_upwards [hcong.mDpH_extended_bound, hm_nn] with x hxJ hxm
    set p : Fin d → ℝ := fun i => Du i x + t * Dφ i x with hp
    -- `‖p‖ ≤ N x` for `|t| ≤ 1`.
    have hp_le_N : ‖p‖ ≤ N x := by
      rw [hN]
      have : ‖p‖ ≤ ‖fun i => Du i x‖ + ‖fun i => t * Dφ i x‖ := by
        have heq : p = (fun i => Du i x) + (fun i => t * Dφ i x) := by
          funext i; rw [hp]; simp [Pi.add_apply]
        rw [heq]; exact norm_add_le _ _
      have hsmul : ‖fun i => t * Dφ i x‖ ≤ ‖fun i => Dφ i x‖ := by
        have : (fun i => t * Dφ i x) = t • (fun i => Dφ i x) := by
          funext i; simp [Pi.smul_apply, smul_eq_mul]
        rw [this, norm_smul, Real.norm_eq_abs]
        exact mul_le_of_le_one_left (norm_nonneg _) ht1
      linarith
    -- Mass term: `|(m−1)·φ| = |m−1|·|φ|`.
    have hmass_eq : |(m x - 1) * φ x| = |m x - 1| * |φ x| := abs_mul _ _
    -- Flux dot bound: `|J ⬝ Dφ| ≤ ‖J‖·(∑|Dφᵢ|)`.
    have hdot_le : |J x p (m x) ⬝ (fun i => Dφ i x)|
        ≤ ‖J x p (m x)‖ * (∑ i, |Dφ i x|) := by
      unfold euclideanDot
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun i _ => ?_)
      rw [abs_mul]
      have hcoord : |J x p (m x) i| ≤ ‖J x p (m x)‖ := by
        have := norm_le_pi_norm (J x p (m x)) i
        simpa [Real.norm_eq_abs] using this
      exact mul_le_mul_of_nonneg_right hcoord (abs_nonneg _)
    -- Flux factor bound from the closed-half-line `J`-envelope (no `m=0` split).
    set fluxDom : ℝ := C * (1 + m x ^ (1 - τ)) * N x ^ (α * (1 + τ / β) - 1)
        + C * (m x ^ (β + 1 - β / α) + 1) with hfluxDom
    have hfluxDom_nn : 0 ≤ fluxDom := by
      rw [hfluxDom]
      have h1 : 0 ≤ C * (1 + m x ^ (1 - τ)) * N x ^ (α * (1 + τ / β) - 1) := by
        have hNnn : 0 ≤ N x := by rw [hN]; positivity
        positivity
      have h2 : 0 ≤ C * (m x ^ (β + 1 - β / α) + 1) := by
        have hmnn := hxm; positivity
      linarith
    have hflux_le : |J x p (m x) ⬝ (fun i => Dφ i x)|
        ≤ fluxDom * (∑ i, |Dφ i x|) := by
      -- `‖J‖ ≤ fluxDom` via `mDpH_extended_bound` + rpow-mono in `‖p‖ ≤ N`.
      have hJ_le := hxJ p (m x) hxm
      have hexp_nn : 0 ≤ α * (1 + τ / β) - 1 := by
        have hαt_gt_one : 1 < α * (1 + τ / β) := by
          have : 1 + τ / β ≥ 1 := by have := div_nonneg hτ_nn hβ.le; linarith
          nlinarith
        linarith
      have hpow_le : ‖p‖ ^ (α * (1 + τ / β) - 1) ≤ N x ^ (α * (1 + τ / β) - 1) :=
        Real.rpow_le_rpow (norm_nonneg _) hp_le_N hexp_nn
      have hJ_le' : ‖J x p (m x)‖ ≤ fluxDom := by
        rw [hfluxDom]
        refine le_trans hJ_le (add_le_add ?_ le_rfl)
        refine mul_le_mul_of_nonneg_left hpow_le ?_
        have hfac_nn : 0 ≤ 1 + m x ^ (1 - τ) := by
          have : 0 ≤ m x ^ (1 - τ) := Real.rpow_nonneg hxm _; linarith
        positivity
      have hsum_nn : 0 ≤ ∑ i, |Dφ i x| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      calc |J x p (m x) ⬝ (fun i => Dφ i x)|
          ≤ ‖J x p (m x)‖ * (∑ i, |Dφ i x|) := hdot_le
        _ ≤ fluxDom * (∑ i, |Dφ i x|) :=
            mul_le_mul_of_nonneg_right hJ_le' hsum_nn
    -- Assemble.
    rw [Real.norm_eq_abs]
    refine le_trans (abs_add_le _ _) ?_
    rw [hmass_eq]
    exact add_le_add le_rfl hflux_le

open StationaryMFG.Periodic in
/-- **child-3 raw first variation → connector `h_VI_at_mdelta`** (the
`(1/t)`-cancel + Hamiltonian-lower-bound algebra; paper line 1538).

For fixed `t > 0`, `δ > 0`, this turns child-3's raw first-variation
inequality
`0 ≤ (1/t)·(∫ Big1 + ε·∫ Big2)`
(`congestion_VI_firstvar_ineq`, where `Big1 = Mterm + RHSc`) into the
connector's per-`δ` variational inequality in lower-bounded form — the
literal `h_VI_at_mdelta` hypothesis that `transport_mdelta_limit_of_L1`
/ `transport_mdelta_limit_concrete` consume (with their `φ ↦ t·φ`,
`Dφ ↦ t·∇φ`, `γBar = γEps = α(β+1)/β`, `C = hcong.C`, `β = hcong.β`).

Algebra (steps 1–4 of the task):
1. `0 ≤ (1/t)·X`, `t > 0` ⟹ `0 ≤ X = ∫Big1 + ε·∫Big2`.
2. `∫Big1 = ∫Mterm + ∫RHSc` (`integral_add`, via the three integrability
   certificates from `firstvar_integrands_integrable`).
3. `∫Mterm ≤ −∫LHSc` (`integral_mono_ae`): pointwise a.e.
   `Mterm + LHSc = −(H(Du+t∇φ,m_δ)+C(m_δ^β+1))·(m_δ−m) ≤ 0`, using
   `m_δ − m ≥ 0` (`le_max_left`) and `H(Du+t∇φ,m_δ) ≥ −C(m_δ^β+1)`
   (`CongestionGrowthCore.lower` at `m_δ ≥ δ > 0`, dropping the
   nonneg leading term).
4. Recombine + `linarith` to `∫LHSc ≤ ∫RHSc + ε·∫Big2 = ∫LHSc ≤ … + ∫Gateaux`. -/
theorem congestion_VI_at_mdelta
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {ε : ℝ}
    (φ : Periodic.SmoothPeriodic d)
    {δ : ℝ} (hδ : 0 < δ) {t : ℝ} (ht : 0 < t)
    -- child-3's raw first-variation inequality `0 ≤ (1/t)·(∫Big1 + ε·∫Big2)`.
    (h_raw : 0 ≤ (1 / t) *
      ((∫ x in UnitCube d,
          (-(u x + t * (φ : (Fin d → ℝ) → ℝ) x)
              - H x
                  (fun i => Du i x
                    + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                        (Fin d → ℝ) → ℝ) x)
                  (max (m x) δ)
              + V x) * (max (m x) δ - m x)
            + max (m x) δ
                * (DpH x
                    (fun i => Du i x
                      + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                          (Fin d → ℝ) → ℝ) x)
                    (max (m x) δ)
                  ⬝ (fun i => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                          (Fin d → ℝ) → ℝ) x))
            + (max (m x) δ - 1) * (t * (φ : (Fin d → ℝ) → ℝ) x)
          ∂(volume : Measure (Fin d → ℝ)))
        + ε * (∫ x in UnitCube d,
              vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
                  (fun i => Du i x
                    + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                        (Fin d → ℝ) → ℝ) x)
                * ((fun i => Du i x
                      + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                          (Fin d → ℝ) → ℝ) x)
                    ⬝ (fun i => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                          (Fin d → ℝ) → ℝ) x))
              + absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
                  (u x + t * (φ : (Fin d → ℝ) → ℝ) x)
                * ((u x + t * (φ : (Fin d → ℝ) → ℝ) x)
                    * (t * (φ : (Fin d → ℝ) → ℝ) x))
            ∂(volume : Measure (Fin d → ℝ)))))
    -- The three connector-integrand integrability certificates
    -- (`firstvar_integrands_integrable`).
    (hLHSc_int : IntegrableOn (fun x =>
        (u x + t * (φ : (Fin d → ℝ) → ℝ) x
            - hcong.C * (max (m x) δ ^ hcong.β + 1) - V x)
          * (max (m x) δ - m x)) (UnitCube d))
    (hRHSc_int : IntegrableOn (fun x =>
        (max (m x) δ - 1) * (t * (φ : (Fin d → ℝ) → ℝ) x)
          + max (m x) δ * (DpH x
              (fun i => Du i x
                + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                    (Fin d → ℝ) → ℝ) x)
              (max (m x) δ)
            ⬝ (fun i => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                (Fin d → ℝ) → ℝ) x))) (UnitCube d))
    (hMterm_int : IntegrableOn (fun x =>
        (-(u x + t * (φ : (Fin d → ℝ) → ℝ) x)
            - H x (fun i => Du i x
                + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                    (Fin d → ℝ) → ℝ) x)
              (max (m x) δ) + V x)
          * (max (m x) δ - m x)) (UnitCube d)) :
    (∫ x in UnitCube d,
        (u x + t * (φ : (Fin d → ℝ) → ℝ) x
            - hcong.C * ((max (m x) δ) ^ hcong.β + 1) - V x)
          * (max (m x) δ - m x)
        ∂(volume : Measure (Fin d → ℝ)))
    ≤
    (∫ x in UnitCube d,
        (max (m x) δ - 1) * (t * (φ : (Fin d → ℝ) → ℝ) x)
          + max (m x) δ
            * (DpH x
                (fun i => Du i x
                  + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                      (Fin d → ℝ) → ℝ) x)
                (max (m x) δ)
                ⬝ (fun i => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                      (Fin d → ℝ) → ℝ) x))
        ∂(volume : Measure (Fin d → ℝ)))
    +
    (∫ x in UnitCube d,
        ε * vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
            (fun i => Du i x
              + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                  (Fin d → ℝ) → ℝ) x)
          * ((fun i => Du i x
                + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                    (Fin d → ℝ) → ℝ) x)
              ⬝ (fun i => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                  (Fin d → ℝ) → ℝ) x))
        + ε * absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
            (u x + t * (φ : (Fin d → ℝ) → ℝ) x)
          * ((u x + t * (φ : (Fin d → ℝ) → ℝ) x)
              * (t * (φ : (Fin d → ℝ) → ℝ) x))
        ∂(volume : Measure (Fin d → ℝ))) := by
  classical
  haveI hfin : IsFiniteMeasure
      (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  -- Abbreviations: `Dg i x = Du i x + t·∂ᵢφ x`, `mδ x = max (m x) δ`,
  -- `φ_c x = t·φ x`.
  set Dg : Fin d → (Fin d → ℝ) → ℝ :=
    fun i x => Du i x
      + t * (Periodic.SmoothPeriodic.partialDeriv i φ : (Fin d → ℝ) → ℝ) x
    with hDg
  set mδ : (Fin d → ℝ) → ℝ := fun x => max (m x) δ with hmδdef
  set φ_c : (Fin d → ℝ) → ℝ := fun x => t * (φ : (Fin d → ℝ) → ℝ) x with hφc
  -- Names for the four integrands.
  set LHSc : (Fin d → ℝ) → ℝ := fun x =>
    (u x + φ_c x - hcong.C * (mδ x ^ hcong.β + 1) - V x) * (mδ x - m x)
    with hLHScdef
  set RHSc : (Fin d → ℝ) → ℝ := fun x =>
    (mδ x - 1) * φ_c x
      + mδ x * (DpH x (fun i => Dg i x) (mδ x)
          ⬝ (fun i => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
              (Fin d → ℝ) → ℝ) x))
    with hRHScdef'
  set Mterm : (Fin d → ℝ) → ℝ := fun x =>
    (-(u x + φ_c x) - H x (fun i => Dg i x) (mδ x) + V x) * (mδ x - m x)
    with hMtermdef
  set Big2 : (Fin d → ℝ) → ℝ := fun x =>
    vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β) (fun i => Dg i x)
        * ((fun i => Dg i x) ⬝ (fun i => t *
            (Periodic.SmoothPeriodic.partialDeriv i φ : (Fin d → ℝ) → ℝ) x))
      + absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β) (u x + φ_c x)
        * ((u x + φ_c x) * φ_c x)
    with hBig2def
  -- Repackage the integrability certificates under the abbreviations.
  have hLHSci : IntegrableOn LHSc (UnitCube d) := by
    simpa [hLHScdef, hφc, hmδdef] using hLHSc_int
  have hRHSci : IntegrableOn RHSc (UnitCube d) := by
    simpa [hRHScdef', hφc, hmδdef, hDg] using hRHSc_int
  have hMtermi : IntegrableOn Mterm (UnitCube d) := by
    simpa [hMtermdef, hφc, hmδdef, hDg] using hMterm_int
  -- `Big1 = Mterm + RHSc` definitionally (after `ring`-normalising the sum).
  have hBig1_eq : (fun x =>
      (-(u x + φ_c x) - H x (fun i => Dg i x) (mδ x) + V x) * (mδ x - m x)
        + mδ x * (DpH x (fun i => Dg i x) (mδ x)
            ⬝ (fun i => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                (Fin d → ℝ) → ℝ) x))
        + (mδ x - 1) * φ_c x)
      = (fun x => Mterm x + RHSc x) := by
    funext x; simp only [hMtermdef, hRHScdef']; ring
  -- ===== Step 1: cancel the `1/t` prefactor. =====
  -- `0 ≤ (1/t)·X` and `t > 0` ⟹ `0 ≤ X`.
  have hX_nn : 0 ≤
      (∫ x in UnitCube d,
          (-(u x + φ_c x) - H x (fun i => Dg i x) (mδ x) + V x) * (mδ x - m x)
            + mδ x * (DpH x (fun i => Dg i x) (mδ x)
                ⬝ (fun i => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                    (Fin d → ℝ) → ℝ) x))
            + (mδ x - 1) * φ_c x
          ∂(volume : Measure (Fin d → ℝ)))
        + ε * (∫ x in UnitCube d, Big2 x
            ∂(volume : Measure (Fin d → ℝ))) := by
    have hraw' : 0 ≤ (1 / t) *
        ((∫ x in UnitCube d,
            (-(u x + φ_c x) - H x (fun i => Dg i x) (mδ x) + V x) * (mδ x - m x)
              + mδ x * (DpH x (fun i => Dg i x) (mδ x)
                  ⬝ (fun i => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                      (Fin d → ℝ) → ℝ) x))
              + (mδ x - 1) * φ_c x
            ∂(volume : Measure (Fin d → ℝ)))
          + ε * (∫ x in UnitCube d, Big2 x
              ∂(volume : Measure (Fin d → ℝ)))) := by
      simpa only [hφc, hmδdef, hDg, hBig2def] using h_raw
    -- `0 ≤ (1/t)·X` and `0 < 1/t` ⟹ `0 ≤ X`.
    have hinv_pos : 0 < 1 / t := by positivity
    nlinarith [mul_nonneg hinv_pos.le hraw', hinv_pos,
      mul_pos hinv_pos ht]
  -- ===== Step 2: split `∫Big1 = ∫Mterm + ∫RHSc`. =====
  have hBig1_split :
      (∫ x in UnitCube d,
          (-(u x + φ_c x) - H x (fun i => Dg i x) (mδ x) + V x) * (mδ x - m x)
            + mδ x * (DpH x (fun i => Dg i x) (mδ x)
                ⬝ (fun i => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                    (Fin d → ℝ) → ℝ) x))
            + (mδ x - 1) * φ_c x
          ∂(volume : Measure (Fin d → ℝ)))
        = (∫ x in UnitCube d, Mterm x ∂(volume : Measure (Fin d → ℝ)))
          + (∫ x in UnitCube d, RHSc x ∂(volume : Measure (Fin d → ℝ))) := by
    rw [show (fun x =>
        (-(u x + φ_c x) - H x (fun i => Dg i x) (mδ x) + V x) * (mδ x - m x)
          + mδ x * (DpH x (fun i => Dg i x) (mδ x)
              ⬝ (fun i => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                  (Fin d → ℝ) → ℝ) x))
          + (mδ x - 1) * φ_c x)
        = (fun x => Mterm x + RHSc x) from hBig1_eq]
    exact integral_add hMtermi hRHSci
  -- ===== Step 3: `∫Mterm ≤ −∫LHSc`. =====
  -- Pointwise a.e.: `Mterm + LHSc = −(H(Dg,mδ)+C(mδ^β+1))·(mδ−m) ≤ 0`.
  have hMterm_le : (∫ x in UnitCube d, Mterm x ∂(volume : Measure (Fin d → ℝ)))
      ≤ ∫ x in UnitCube d, (-LHSc x) ∂(volume : Measure (Fin d → ℝ)) := by
    have hae : Mterm ≤ᵐ[volume.restrict (UnitCube d)] (fun x => -LHSc x) := by
      filter_upwards [hcong.lower] with x hlow
      -- `mδ x = max (m x) δ ≥ δ > 0`, so the lower bound applies at `mδ x`.
      have hmδ_pos : 0 < mδ x := lt_of_lt_of_le hδ (le_max_right _ _)
      have hH_ge : H x (fun i => Dg i x) (mδ x)
          ≥ (1 / hcong.C) * (1 / (mδ x ^ hcong.τ + 1))
              * (‖fun i => Dg i x‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)))
            - hcong.C * (mδ x ^ hcong.β + 1) :=
        hlow (fun i => Dg i x) (mδ x) hmδ_pos
      -- The leading momentum term is `≥ 0`, so `H ≥ −C(mδ^β+1)`.
      have hlead_nn : 0 ≤ (1 / hcong.C) * (1 / (mδ x ^ hcong.τ + 1))
          * (‖fun i => Dg i x‖ ^ (hcong.α * (1 + hcong.τ / hcong.β))) := by
        have hC_pos : 0 < hcong.C := hcong.hC
        have hmτ_pos : 0 < mδ x ^ hcong.τ := Real.rpow_pos_of_pos hmδ_pos _
        have hmτ1_pos : 0 < mδ x ^ hcong.τ + 1 := by linarith
        have hpow_nn : 0 ≤ ‖fun i => Dg i x‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) :=
          Real.rpow_nonneg (norm_nonneg _) _
        positivity
      have hH_lb : H x (fun i => Dg i x) (mδ x)
          ≥ -(hcong.C * (mδ x ^ hcong.β + 1)) := by linarith
      -- `mδ − m ≥ 0`.
      have hdiff_nn : 0 ≤ mδ x - m x := by
        have : m x ≤ mδ x := le_max_left _ _
        linarith
      -- `Mterm x + LHSc x = −(H + C(mδ^β+1))·(mδ−m) ≤ 0`.
      change Mterm x ≤ -LHSc x
      simp only [hMtermdef, hLHScdef]
      have hfac_nn : 0 ≤ H x (fun i => Dg i x) (mδ x)
          + hcong.C * (mδ x ^ hcong.β + 1) := by linarith
      nlinarith [mul_nonneg hfac_nn hdiff_nn]
    have hneg_int : IntegrableOn (fun x => -LHSc x) (UnitCube d) := hLHSci.neg
    exact integral_mono_ae hMtermi hneg_int hae
  -- `∫(−LHSc) = −∫LHSc`.
  have hneg_eq : (∫ x in UnitCube d, (-LHSc x) ∂(volume : Measure (Fin d → ℝ)))
      = -(∫ x in UnitCube d, LHSc x ∂(volume : Measure (Fin d → ℝ))) := by
    rw [integral_neg]
  -- ===== Step 4: recombine. =====
  -- From `hX_nn` and `hBig1_split`:
  -- `0 ≤ ∫Mterm + ∫RHSc + ε·∫Big2 ≤ −∫LHSc + ∫RHSc + ε·∫Big2`,
  -- hence `∫LHSc ≤ ∫RHSc + ε·∫Big2`.
  rw [hBig1_split] at hX_nn
  -- Convert the goal's `ε·…` integral into `ε * ∫Big2`.
  have hGateaux_eq :
      (∫ x in UnitCube d,
          ε * vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
              (fun i => Du i x
                + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                    (Fin d → ℝ) → ℝ) x)
            * ((fun i => Du i x
                  + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                      (Fin d → ℝ) → ℝ) x)
                ⬝ (fun i => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                    (Fin d → ℝ) → ℝ) x))
          + ε * absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
              (u x + t * (φ : (Fin d → ℝ) → ℝ) x)
            * ((u x + t * (φ : (Fin d → ℝ) → ℝ) x)
                * (t * (φ : (Fin d → ℝ) → ℝ) x))
          ∂(volume : Measure (Fin d → ℝ)))
        = ε * (∫ x in UnitCube d, Big2 x ∂(volume : Measure (Fin d → ℝ))) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [hBig2def, hφc, hDg]; ring
  -- The goal's RHS first integral is `∫RHSc`.
  have hRHS_eq :
      (∫ x in UnitCube d,
          (max (m x) δ - 1) * (t * (φ : (Fin d → ℝ) → ℝ) x)
            + max (m x) δ
              * (DpH x
                  (fun i => Du i x
                    + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                        (Fin d → ℝ) → ℝ) x)
                  (max (m x) δ)
                  ⬝ (fun i => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                        (Fin d → ℝ) → ℝ) x))
          ∂(volume : Measure (Fin d → ℝ)))
        = ∫ x in UnitCube d, RHSc x ∂(volume : Measure (Fin d → ℝ)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [hRHScdef', hφc, hDg, hmδdef]
  -- The goal's LHS is `∫LHSc`.
  have hLHS_eq :
      (∫ x in UnitCube d,
          (u x + t * (φ : (Fin d → ℝ) → ℝ) x
              - hcong.C * ((max (m x) δ) ^ hcong.β + 1) - V x)
            * (max (m x) δ - m x)
          ∂(volume : Measure (Fin d → ℝ)))
        = ∫ x in UnitCube d, LHSc x ∂(volume : Measure (Fin d → ℝ)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [hLHScdef, hφc, hmδdef]
  rw [hGateaux_eq, hRHS_eq, hLHS_eq]
  rw [hneg_eq] at hMterm_le
  linarith [hX_nn, hMterm_le]

/-! ## Witness-level δ→0 cert suite (T2 phase6 BB VIid **child-5a-i**)

This is the VI-identity analogue of the HJB-le drain's
`weak_is_strong_HJB_le_of_witnessData` cert suite: it produces, at the
Browder–Minty witness, the per-`(δ, t)` inputs of the δ→0 connector
`transport_mdelta_limit_of_L1`. Specifically it lands two reusable
witness-level certificates:

* `congestion_VI_perturbed_ratio_memLp` — the perturbed-gradient ratio
  `‖Du + t∇φ‖^{αt} / (max(m, δ)^τ + 1) ∈ L^{β̄'}_per` (the `hRatio_pert`
  hypothesis of `firstvar_integrands_integrable` / `H_at_perturbed_memLp_betaBar'`),
  re-derived via `mdelta_pointwise_bound` + `MemLp.mono'` exactly as the
  `mdelta_admissibility` `?quot` block does — but here in the explicit
  `Du + t∇φ` shape the integrability certs consume;
* `congestion_VI_h_VI_at_mdelta_at_witness` — the per-`(δ, t)` connector
  hypothesis `h_VI_at_mdelta` itself (in the exact lower-bounded form
  `transport_mdelta_limit_of_L1` consumes with `φ ↦ t·φ`, `Dφ ↦ t·∇φ`,
  `γBar = α(β+1)/β`, `C = hcong.C`, `β = hcong.β`), assembled from
  `congestion_VI_firstvar_ineq` (child-3, `h_raw`) → `congestion_VI_at_mdelta`
  (child-4b-i), the latter's three integrability certs supplied via
  `firstvar_integrands_integrable` at the witness ratio above.

The remaining δ→0 plumbing — the per-term `L¹` convergences
(`lhs_L1_diff_tendsto` / `rhs_L1_diff_tendsto` at the witness from the child-2
DCT tools and the Hölder dominators) and the final `h_dir` assembly calling
`transport_mdelta_limit_of_L1` with the squeeze + `t = 0` / `t < 0` handling —
is the sibling child-5a-ii (depends on these certs). -/

/-- **Perturbed-gradient ratio `L^{β̄'}` membership at the witness**
(T2 phase6 BB VIid child-5a-i).

For the witness density `m` (in `L^{β̄}`, a.e. `≥ 0`), the witness quotient
dominator `‖Du‖^{αt}/(m^τ+1) ∈ L^{β̄'}` and a smooth test `φ`, the perturbed
ratio at the truncated density `m_δ = max(m, δ)` and the perturbed gradient
`Dg i = Du i + t·∂ᵢφ` lies in `L^{β̄'}_per`.

This is the `hRatio_pert` hypothesis of `firstvar_integrands_integrable` /
`H_at_perturbed_memLp_betaBar'`. Re-derived (not extracted from the existential
in `mdelta_admissibility`'s `congestionDomainK` membership) via the deterministic
pointwise bound `mdelta_pointwise_bound` + `MemLp.mono'`, mirroring the
`mdelta_admissibility` `?quot` block. -/
theorem congestion_VI_perturbed_ratio_memLp
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    {m : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) m)
    (hm_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hDu_mem : ∀ i,
      MemLpPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Du i))
    (hQuot_m_mem :
      MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (fun x : Fin d → ℝ =>
          ‖fun i => Du i x‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) /
            (m x ^ hcong.τ + 1)))
    (φ : Periodic.SmoothPeriodic d)
    {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
      (fun x => ‖fun i => Du i x
            + t * (Periodic.SmoothPeriodic.partialDeriv i φ : (Fin d → ℝ) → ℝ) x‖
          ^ (hcong.α * (1 + hcong.τ / hcong.β))
        / (max (m x) δ ^ hcong.τ + 1)) := by
  classical
  set α : ℝ := hcong.α with hαdef
  set β : ℝ := hcong.β with hβdef
  set τ : ℝ := hcong.τ with hτdef
  set αt : ℝ := α * (1 + τ / β) with hαtdef
  have hα : 1 < α := hcong.hα
  have hβ : 0 < β := hcong.hβ
  have hτ : 0 ≤ τ := hcong.hτ.1
  have hαt : 1 ≤ αt := by
    have hfrac : (0 : ℝ) ≤ τ / β := div_nonneg hτ hβ.le
    have h1 : (1 : ℝ) ≤ 1 + τ / β := by linarith
    rw [hαtdef]
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ α * (1 + τ / β) :=
          mul_le_mul hα.le h1 (by norm_num) (le_trans (by norm_num) hα.le)
  have hαt_nn : 0 ≤ αt := le_trans zero_le_one hαt
  haveI hcube_fin :
      IsFiniteMeasure (Measure.restrict volume (UnitCube (d := d))) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  -- The perturbation gradient `Dφ i := t·∂ᵢφ`.
  set Dφ : Fin d → (Fin d → ℝ) → ℝ :=
    fun i x => t * (Periodic.SmoothPeriodic.partialDeriv i φ : (Fin d → ℝ) → ℝ) x
    with hDφdef
  -- `‖Dφ‖^{αt} ∈ L^{β̄'}` (smooth ⇒ continuous bounded on the cube).
  have hDφ_Lp :
      MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
        (fun x : Fin d → ℝ => ‖fun i => Dφ i x‖ ^ αt) := by
    have hcont : ∀ i, Continuous (Dφ i) := by
      intro i; rw [hDφdef]
      exact continuous_const.mul
        (Periodic.SmoothPeriodic.partialDeriv i φ).smooth.continuous
    have hnorm_cont : Continuous (fun x : Fin d → ℝ => ‖fun i => Dφ i x‖) :=
      (continuous_pi hcont).norm
    have hcompact :
        IsCompact (Set.pi Set.univ (fun _ : Fin d => Set.Icc (0 : ℝ) 1)) :=
      isCompact_univ_pi (fun _ => isCompact_Icc)
    obtain ⟨C, hC⟩ := hcompact.bddAbove_image hnorm_cont.continuousOn
    have hpow_cont : Continuous (fun x : Fin d → ℝ => ‖fun i => Dφ i x‖ ^ αt) :=
      hnorm_cont.rpow_const (fun _ => Or.inr hαt_nn)
    refine MemLp.toMemLpPer ?_
    refine MeasureTheory.MemLp.of_bound hpow_cont.aestronglyMeasurable
      (C ^ αt) ?_
    refine (ae_restrict_iff' measurableSet_unitCube).2
      (Filter.Eventually.of_forall ?_)
    intro x hx
    have hx_cube : x ∈ Set.pi Set.univ (fun _ : Fin d => Set.Icc (0 : ℝ) 1) := by
      intro j _
      exact Set.Ico_subset_Icc_self (hx j (Set.mem_univ _))
    have hnorm_le : ‖fun i => Dφ i x‖ ≤ C := hC ⟨x, hx_cube, rfl⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact Real.rpow_le_rpow (norm_nonneg _) hnorm_le hαt_nn
  -- Dominator `RHS := 2^{αt-1}·(‖Du‖^{αt}/(m^τ+1) + ‖Dφ‖^{αt}) ∈ L^{β̄'}`.
  have hRHS_inner_mem :
      MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
        (fun x : Fin d → ℝ =>
          ‖fun i => Du i x‖ ^ αt / (m x ^ τ + 1) + ‖fun i => Dφ i x‖ ^ αt) := by
    have hQuot : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
        (fun x : Fin d → ℝ =>
          ‖fun i => Du i x‖ ^ αt / (m x ^ τ + 1)) := by
      rw [hαtdef, hαdef, hτdef]; rw [hβdef]; exact hQuot_m_mem
    exact hQuot.add hDφ_Lp
  have hRHS_mem :
      MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
        (fun x : Fin d → ℝ =>
          (2 : ℝ) ^ (αt - 1) *
            (‖fun i => Du i x‖ ^ αt / (m x ^ τ + 1) + ‖fun i => Dφ i x‖ ^ αt)) := by
    have := hRHS_inner_mem.const_smul ((2 : ℝ) ^ (αt - 1))
    have heq :
        ((2 : ℝ) ^ (αt - 1)) •
            (fun x : Fin d → ℝ =>
              ‖fun i => Du i x‖ ^ αt / (m x ^ τ + 1) + ‖fun i => Dφ i x‖ ^ αt)
          = (fun x : Fin d → ℝ =>
              (2 : ℝ) ^ (αt - 1) *
                (‖fun i => Du i x‖ ^ αt / (m x ^ τ + 1)
                  + ‖fun i => Dφ i x‖ ^ αt)) := by
      funext x; simp [Pi.smul_apply, smul_eq_mul]
    rwa [heq] at this
  -- Target membership via `MemLp.mono'` against the dominator.
  have hgoal :
      MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
        (fun x => ‖fun i => Du i x + Dφ i x‖ ^ αt / (max (m x) δ ^ τ + 1)) := by
    apply MemLp.toMemLpPer
    refine MemLp.mono' hRHS_mem.toMemLp ?_ ?_
    · -- AE strong measurability of the LHS, built from the components.
      have hcont_rpow_αt : Continuous (fun x : ℝ => x ^ αt) :=
        Real.continuous_rpow_const hαt_nn
      have hcont_rpow_τ : Continuous (fun x : ℝ => x ^ τ) :=
        Real.continuous_rpow_const hτ
      have h_Du_aem : ∀ i, AEMeasurable (Du i)
          (volume.restrict (UnitCube d)) := fun i =>
        (hDu_mem i).aestronglyMeasurable.aemeasurable
      have h_Dφ_aem : ∀ i, AEMeasurable (Dφ i)
          (volume.restrict (UnitCube d)) := fun i => by
        rw [hDφdef]
        exact (continuous_const.mul
          (Periodic.SmoothPeriodic.partialDeriv i φ).smooth.continuous).aemeasurable
      have h_sum_aem : ∀ i, AEMeasurable
          (fun x => Du i x + Dφ i x) (volume.restrict (UnitCube d)) :=
        fun i => (h_Du_aem i).add (h_Dφ_aem i)
      have h_vec_aesm : AEStronglyMeasurable
          (fun x : Fin d → ℝ => fun i => Du i x + Dφ i x)
          (volume.restrict (UnitCube d)) :=
        (aemeasurable_pi_iff.mpr h_sum_aem).aestronglyMeasurable
      have h_rpow_aesm : AEStronglyMeasurable
          (fun x : Fin d → ℝ => ‖fun i => Du i x + Dφ i x‖ ^ αt)
          (volume.restrict (UnitCube d)) :=
        hcont_rpow_αt.comp_aestronglyMeasurable h_vec_aesm.norm
      have h_m_aem : AEMeasurable m (volume.restrict (UnitCube d)) :=
        hm_mem.aestronglyMeasurable.aemeasurable
      have h_max_aesm : AEStronglyMeasurable
          (fun x : Fin d → ℝ => max (m x) δ) (volume.restrict (UnitCube d)) :=
        (h_m_aem.max aemeasurable_const).aestronglyMeasurable
      have h_den_aesm : AEStronglyMeasurable
          (fun x : Fin d → ℝ => max (m x) δ ^ τ + 1)
          (volume.restrict (UnitCube d)) :=
        (hcont_rpow_τ.comp_aestronglyMeasurable h_max_aesm).add
          aestronglyMeasurable_const
      exact (h_rpow_aesm.aemeasurable.div h_den_aesm.aemeasurable).aestronglyMeasurable
    · -- AE pointwise bound `‖LHS x‖ ≤ RHS x` from `mdelta_pointwise_bound`.
      filter_upwards [hm_nn] with x hx
      have hLHS_nn :
          0 ≤ ‖fun i => Du i x + Dφ i x‖ ^ αt / (max (m x) δ ^ τ + 1) := by
        have h2 : 0 ≤ max (m x) δ ^ τ + 1 := by
          have : 0 ≤ max (m x) δ ^ τ :=
            Real.rpow_nonneg (le_trans hδ.le (le_max_right _ _)) _
          linarith
        exact div_nonneg (Real.rpow_nonneg (norm_nonneg _) _) h2
      rw [Real.norm_eq_abs, abs_of_nonneg hLHS_nn]
      have hbound :=
        mdelta_pointwise_bound (m := m x) (δ := δ) (αt := αt) (τ := τ)
          (a := fun i => Du i x) (b := fun i => Dφ i x) hx hδ hτ hαt
      have hadd_eq :
          ((fun i => Du i x) + (fun i => Dφ i x)) = (fun i => Du i x + Dφ i x) := by
        funext i; rfl
      rw [hadd_eq] at hbound
      exact hbound
  -- Translate to the `αt`-displayed statement and back to `hcong.*` constants.
  have heqfun :
      (fun x => ‖fun i => Du i x + Dφ i x‖ ^ αt / (max (m x) δ ^ τ + 1))
        = (fun x => ‖fun i => Du i x
              + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                  (Fin d → ℝ) → ℝ) x‖
            ^ (hcong.α * (1 + hcong.τ / hcong.β))
          / (max (m x) δ ^ hcong.τ + 1)) := by
    funext x; rw [hαtdef, hαdef, hβdef, hτdef, hDφdef]
  rw [heqfun] at hgoal
  exact hgoal

/-- **Per-`(δ, t)` connector `h_VI_at_mdelta` at the witness**
(T2 phase6 BB VIid child-5a-i).

For each `δ > 0` and `t > 0`, produces the exact lower-bounded variational
inequality that `transport_mdelta_limit_of_L1` consumes as its
`h_VI_at_mdelta n` hypothesis (with the test direction `(t·φ, t·∇φ)`,
`γBar = α(β+1)/β`, `C = hcong.C`, `β = hcong.β`):

```
∫ (u + t·φ − C·(m_δ^β + 1) − V)·(m_δ − m)
  ≤ ∫ [(m_δ − 1)·t·φ + m_δ·D_pH(x, Du+t∇φ, m_δ)·(t∇φ)]
    + ∫ [ε·|Du+t∇φ|^{γ̄−2}(Du+t∇φ)·(t∇φ) + ε·|u+tφ|^{γ̄−2}(u+tφ)·(tφ)].
```

Assembled from `congestion_VI_firstvar_ineq` (child-3, the raw `1/t`-scaled
first-variation inequality) and `congestion_VI_at_mdelta` (child-4b-i), the
latter's three integrability certificates supplied via
`firstvar_integrands_integrable` at the perturbed ratio
`congestion_VI_perturbed_ratio_memLp`. -/
theorem congestion_VI_h_VI_at_mdelta_at_witness
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
    (φ : Periodic.SmoothPeriodic d)
    {δ : ℝ} (hδ : 0 < δ) {t : ℝ} (ht : 0 < t) :
    (∫ x in UnitCube d,
        (u x + t * (φ : (Fin d → ℝ) → ℝ) x
            - hcong.C * ((max (m x) δ) ^ hcong.β + 1) - V x)
          * (max (m x) δ - m x)
        ∂(volume : Measure (Fin d → ℝ)))
    ≤
    (∫ x in UnitCube d,
        (max (m x) δ - 1) * (t * (φ : (Fin d → ℝ) → ℝ) x)
          + max (m x) δ
            * (DpH x
                (fun i => Du i x
                  + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                      (Fin d → ℝ) → ℝ) x)
                (max (m x) δ)
                ⬝ (fun i => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                      (Fin d → ℝ) → ℝ) x))
        ∂(volume : Measure (Fin d → ℝ)))
    +
    (∫ x in UnitCube d,
        ε * vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
            (fun i => Du i x
              + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                  (Fin d → ℝ) → ℝ) x)
          * ((fun i => Du i x
                + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                    (Fin d → ℝ) → ℝ) x)
              ⬝ (fun i => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                  (Fin d → ℝ) → ℝ) x))
        + ε * absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
            (u x + t * (φ : (Fin d → ℝ) → ℝ) x)
          * ((u x + t * (φ : (Fin d → ℝ) → ℝ) x)
              * (t * (φ : (Fin d → ℝ) → ℝ) x))
        ∂(volume : Measure (Fin d → ℝ))) := by
  -- The perturbed ratio cert (`hRatio_pert`) for `firstvar_integrands_integrable`.
  have hRatio_pert :
      MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (fun x => ‖fun i => Du i x
              + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                  (Fin d → ℝ) → ℝ) x‖
            ^ (hcong.α * (1 + hcong.τ / hcong.β))
          / (max (m x) δ ^ hcong.τ + 1)) :=
    congestion_VI_perturbed_ratio_memLp hcong hm_mem hm_nn hDu_mem hQuot_m_mem
      φ hδ t
  -- The three connector-integrand integrability certs at the witness.
  obtain ⟨hLHSc_int, hRHSc_int, hMterm_int⟩ :=
    firstvar_integrands_integrable hmon hcong hm_mem hm_nn hu_memGamma hV
      hDu_mem φ hδ (t := t) hRatio_pert
  -- The raw `1/t`-scaled first-variation inequality (child-3) at the witness.
  have h_raw :=
    congestion_VI_firstvar_ineq hmon hcong hm_mem hm_nn hQuot_m_mem hVmeas hV
      hAeq hKeq hVI hw_m hw_u hw_Du hcoeWeak_Du φ hδ ht
  -- Discharge the per-`(δ, t)` connector inequality via child-4b-i.
  exact congestion_VI_at_mdelta hcong φ hδ ht h_raw hLHSc_int hRHSc_int hMterm_int

/-- **Witness-level mass-term `L¹` convergence** (T2 phase6 BB VIid
child-5a-ii-alpha-massrhs). For the truncated test density `m_δ = max(m, δSeq n)`
and the witness test `φ_c = t·φ`, the mass term `φ_c · m_δ → φ_c · m` in `L¹`:

```
∫ ‖(t·φ x)·m_δ − (t·φ x)·m‖ → 0.
```

This is the non-flux (mass) half of `lhs_L1_diff_tendsto`'s `hMass_L1`
hypothesis, instantiated at the witness with the `φ`-slot `= t·φ`. It is a thin
wrapper of child-2's `congestion_Vm_mdelta_tendsto_L1` with `V := t·φ` (smooth ⇒
`L¹` on the finite cube); only `hm_nn` is needed (the mass term carries no
continuity requirement); `hm_mem` supplies the measurability of `m`. -/
theorem congestion_VI_hMass_L1_at_witness
    {p : ℝ≥0∞}
    {m : (Fin d → ℝ) → ℝ}
    {δSeq : ℕ → ℝ}
    (hδ_pos : ∀ n, 0 < δSeq n)
    (hδ_tendsto : Filter.Tendsto δSeq Filter.atTop (nhds (0 : ℝ)))
    (hm_mem : MemLpPer (d := d) p m)
    (hm_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (φ : Periodic.SmoothPeriodic d) (t : ℝ) :
    Filter.Tendsto
      (fun n => ∫ x in UnitCube d,
          ‖(t * (φ : (Fin d → ℝ) → ℝ) x) * mPerDelta m (δSeq n) x
            - (t * (φ : (Fin d → ℝ) → ℝ) x) * m x‖
          ∂(volume : Measure (Fin d → ℝ)))
      Filter.atTop (nhds (0 : ℝ)) := by
  classical
  haveI hfin : IsFiniteMeasure
      (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  set V : (Fin d → ℝ) → ℝ := fun x => t * (φ : (Fin d → ℝ) → ℝ) x with hVdef
  -- `V = t·φ ∈ L¹_per` (smooth ⇒ in every `Lᵖ`), hence integrable on the cube.
  have hV_mem : MemLpPer (d := d) (1 : ℝ≥0∞) V := by
    have hraw : MemLpPer (d := d) (1 : ℝ≥0∞) ((φ : (Fin d → ℝ) → ℝ)) :=
      (Periodic.MemSobolevPer.of_smoothPeriodic (1 : ℝ≥0∞) φ).1
    have := hraw.const_smul (𝕜 := ℝ) t
    have heq : (t • (φ : (Fin d → ℝ) → ℝ)) = V := by
      funext x; simp [hVdef, Pi.smul_apply, smul_eq_mul]
    rwa [heq] at this
  have hV_int : Integrable V (volume.restrict (UnitCube d)) :=
    MeasureTheory.memLp_one_iff_integrable.mp hV_mem.toMemLp
  -- Measurability components.
  have hV_meas : AEStronglyMeasurable V (volume.restrict (UnitCube d)) :=
    hV_mem.aestronglyMeasurable
  have hm_meas : AEStronglyMeasurable m (volume.restrict (UnitCube d)) :=
    hm_mem.aestronglyMeasurable
  have hmδ_meas : ∀ n, AEStronglyMeasurable (mPerDelta m (δSeq n))
      (volume.restrict (UnitCube d)) := by
    intro n
    have := hm_meas.aemeasurable.max (aemeasurable_const (b := δSeq n))
    exact this.aestronglyMeasurable.congr (Filter.Eventually.of_forall (fun x => rfl))
  have hmeas : ∀ n, AEStronglyMeasurable
      (fun x => ‖V x * mPerDelta m (δSeq n) x - V x * m x‖)
      (volume.restrict (UnitCube d)) := by
    intro n
    exact ((hV_meas.mul (hmδ_meas n)).sub (hV_meas.mul hm_meas)).norm
  exact congestion_Vm_mdelta_tendsto_L1 (V := V) (m := m) (δSeq := δSeq)
    hδ_tendsto hδ_pos hm_nn hV_int hmeas

/-- **Witness-level RHS-term `L¹` convergence** (T2 phase6 BB VIid
child-5a-ii-alpha-massrhs). For the truncated test density `m_δ = max(m, δSeq n)`
and the witness test `φ_c = t·φ`, the RHS connector term
`(u + t·φ − C(m_δ^β + 1) − V)·(m_δ − m) → 0` in `L¹`:

```
∫ ‖RHSint n x − 0‖ → 0,  RHSint n x = Fac n x · (m_δ − m),
Fac n x = u x + t·φ x − C(m_δ^β + 1) − V x.
```

This is `rhs_L1_diff_tendsto`'s output at the witness. The `δ`-uniform Hölder
dominator `g x = |u x| + |t·φ x| + C((m x+1)^β + 1) + |V x| ∈ L^{β̄'} ⊆ L¹`
dominates `|Fac n x|` for all `n` via `m_δ ≤ m+1` (`δ ≤ 1`) ⇒ `m_δ^β ≤ (m+1)^β`
(`β > 0`, `rpow` monotone). Memberships: `u ∈ L^{β̄'}` (`u_memLp_betaBar'`),
`(m+1)^β ∈ L^{β̄'}` (`rpow_beta_memLp_betaBar'`), `V ∈ L^{β̄'}`, `t·φ` smooth. -/
theorem congestion_VI_hRHS_L1_at_witness
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    {m u V : (Fin d → ℝ) → ℝ}
    {δSeq : ℕ → ℝ}
    (hδ_pos : ∀ n, 0 < δSeq n)
    (hδ_le_one : ∀ n, δSeq n ≤ 1)
    (hδ_tendsto : Filter.Tendsto δSeq Filter.atTop (nhds (0 : ℝ)))
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) m)
    (hm_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hu_memGamma : MemLpPer (d := d)
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) u)
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (φ : Periodic.SmoothPeriodic d) (t : ℝ)
    (RHSint : ℕ → (Fin d → ℝ) → ℝ)
    (hRHSdef : ∀ n, RHSint n = fun x =>
      (u x + t * (φ : (Fin d → ℝ) → ℝ) x
          - hcong.C * ((max (m x) (δSeq n)) ^ hcong.β + 1) - V x)
        * (max (m x) (δSeq n) - m x)) :
    Filter.Tendsto
      (fun n => ∫ x in UnitCube d, ‖RHSint n x - (0 : ℝ)‖
        ∂(volume : Measure (Fin d → ℝ)))
      Filter.atTop (nhds (0 : ℝ)) := by
  classical
  set α : ℝ := hcong.α with hαdef
  set β : ℝ := hcong.β with hβdef
  have hα : 1 < α := hcong.hα
  have hβ : 0 < β := hcong.hβ
  haveI hfin : IsFiniteMeasure
      (Measure.restrict (volume : Measure (Fin d → ℝ)) (UnitCube d)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ]; simp⟩
  set φ_c : (Fin d → ℝ) → ℝ := fun x => t * (φ : (Fin d → ℝ) → ℝ) x with hφc
  -- The factor and its definitional `Fac`.
  set Fac : ℕ → (Fin d → ℝ) → ℝ := fun n x =>
    u x + φ_c x - hcong.C * (mPerDelta m (δSeq n) x ^ β + 1) - V x with hFacdef
  -- `hRHSdef` in `mPerDelta`/`Fac` form for `rhs_L1_diff_tendsto`.
  have hRHSdef' : ∀ n, RHSint n = fun x => Fac n x * (mPerDelta m (δSeq n) x - m x) := by
    intro n; rw [hRHSdef n]; funext x; rw [hFacdef]; simp [mPerDelta_def, hφc, hβdef]
  -- ===== Build the `δ`-uniform integrable dominator `g`. =====
  -- Witness memberships in `L^{β̄'}`.
  have hu_betaP : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β)) u :=
    u_memLp_betaBar' hα hβ (by rw [hαdef, hβdef]; exact hu_memGamma)
  have hφc_betaP : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β)) φ_c := by
    have hraw : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
        ((φ : (Fin d → ℝ) → ℝ)) :=
      (Periodic.MemSobolevPer.of_smoothPeriodic _ φ).1
    have := hraw.const_smul (𝕜 := ℝ) t
    have heq : (t • (φ : (Fin d → ℝ) → ℝ)) = φ_c := by
      funext x; simp [hφc, Pi.smul_apply, smul_eq_mul]
    rwa [heq] at this
  -- `(m+1)^β ∈ L^{β̄'}` (`m+1 ∈ L^{β+1}`, nonneg).
  have hm1_mem : MemLpPer (d := d) (ENNReal.ofReal (β + 1))
      (fun x => m x + 1) := by
    have := hm_mem.add_const (1 : ℝ)
    simpa using! this
  have hm1_nn : 0 ≤ᵐ[volume.restrict (UnitCube d)] (fun x => m x + 1) := by
    filter_upwards [hm_nn] with x hx
    show (0 : ℝ) ≤ m x + 1
    linarith
  have hm1pow_mem : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
      (fun x => (m x + 1) ^ β) :=
    rpow_beta_memLp_betaBar' hβ hm1_mem hm1_nn
  -- `g := |u| + |φ_c| + C·((m+1)^β + 1) + |V| ∈ L^{β̄'}`.
  set g : (Fin d → ℝ) → ℝ := fun x =>
    |u x| + |φ_c x| + hcong.C * ((m x + 1) ^ β + 1) + |V x| with hgdef
  have hC_mem : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
      (fun x => hcong.C * ((m x + 1) ^ β + 1)) := by
    have hone : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β))
        (fun _ : (Fin d → ℝ) => (1 : ℝ)) := MemLp.toMemLpPer (memLp_const 1)
    have := (hm1pow_mem.add hone).const_smul (𝕜 := ℝ) hcong.C
    have heq : (hcong.C • ((fun x => (m x + 1) ^ β) + fun _ : Fin d → ℝ => (1:ℝ)))
        = (fun x => hcong.C * ((m x + 1) ^ β + 1)) := by
      funext x; simp [Pi.smul_apply, smul_eq_mul, Pi.add_apply]
    rwa [heq] at this
  have hg_mem : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β)) g := by
    have h1 : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β)) (fun x => |u x|) :=
      MemLp.toMemLpPer hu_betaP.toMemLp.abs
    have h2 : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β)) (fun x => |φ_c x|) :=
      MemLp.toMemLpPer hφc_betaP.toMemLp.abs
    have h4 : MemLpPer (d := d) (ENNReal.ofReal ((β + 1) / β)) (fun x => |V x|) :=
      MemLp.toMemLpPer hV.toMemLp.abs
    have := ((h1.add h2).add hC_mem).add h4
    have heq : (((fun x => |u x|) + fun x => |φ_c x|)
          + (fun x => hcong.C * ((m x + 1) ^ β + 1))) + (fun x => |V x|) = g := by
      funext x; simp [hgdef, Pi.add_apply]
    rwa [heq] at this
  -- `g ∈ L¹` on the finite cube.
  have hβbar'_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((β + 1) / β) := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    apply ENNReal.ofReal_le_ofReal
    rw [le_div_iff₀ hβ]; linarith
  have hg_int : Integrable g (volume.restrict (UnitCube d)) :=
    MeasureTheory.memLp_one_iff_integrable.mp
      (hg_mem.mono_exponent_finite hβbar'_one ENNReal.ofReal_ne_top).toMemLp
  -- `g ≥ 0`.
  have hg_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ g x := by
    filter_upwards [hm_nn] with x hx
    have hpow_nn : 0 ≤ (m x + 1) ^ β :=
      Real.rpow_nonneg (by linarith) _
    have hC_nn : 0 ≤ hcong.C := hcong.hC.le
    have : 0 ≤ hcong.C * ((m x + 1) ^ β + 1) :=
      mul_nonneg hC_nn (by linarith)
    rw [hgdef]
    have := abs_nonneg (u x); have := abs_nonneg (φ_c x); have := abs_nonneg (V x)
    positivity
  -- Per-`n` dominator bound `|Fac n x| ≤ g x` (uniform in `n`).
  have hFac_le : ∀ n, ∀ᵐ x ∂(volume.restrict (UnitCube d)), |Fac n x| ≤ g x := by
    intro n
    filter_upwards [hm_nn] with x hx
    -- `m_δ^β ≤ (m+1)^β` from `m_δ ≤ m+1` and `β > 0`.
    have hmδ_le : mPerDelta m (δSeq n) x ≤ m x + 1 := by
      have := mPerDelta_le_add (hδ_pos n).le hx
      have h1 := hδ_le_one n; linarith
    have hmδ_nn : 0 ≤ mPerDelta m (δSeq n) x :=
      le_trans (hδ_pos n).le (mPerDelta_ge_delta m (δSeq n) x)
    have hpow_le : mPerDelta m (δSeq n) x ^ β ≤ (m x + 1) ^ β :=
      Real.rpow_le_rpow hmδ_nn hmδ_le hβ.le
    have hpow_nn : 0 ≤ mPerDelta m (δSeq n) x ^ β :=
      Real.rpow_nonneg hmδ_nn _
    have hC_nn : 0 ≤ hcong.C := hcong.hC.le
    have hCprod_nn : 0 ≤ hcong.C * (mPerDelta m (δSeq n) x ^ β + 1) :=
      mul_nonneg hC_nn (by linarith)
    -- `C·(m_δ^β+1) ≤ C·((m+1)^β+1)`.
    have hCprod_le : hcong.C * (mPerDelta m (δSeq n) x ^ β + 1)
        ≤ hcong.C * ((m x + 1) ^ β + 1) := by
      apply mul_le_mul_of_nonneg_left _ hC_nn; linarith
    -- bound each summand of `Fac` by its `g`-counterpart, then `abs_le`.
    have hu_le : -|u x| ≤ u x ∧ u x ≤ |u x| := ⟨neg_abs_le _, le_abs_self _⟩
    have hφ_le : -|φ_c x| ≤ φ_c x ∧ φ_c x ≤ |φ_c x| := ⟨neg_abs_le _, le_abs_self _⟩
    have hV_le : -|V x| ≤ V x ∧ V x ≤ |V x| := ⟨neg_abs_le _, le_abs_self _⟩
    rw [hFacdef, hgdef, abs_le]
    constructor
    · -- `-(g x) ≤ Fac n x`
      have : (0 : ℝ) ≤ hcong.C * ((m x + 1) ^ β + 1) :=
        mul_nonneg hC_nn (by linarith)
      nlinarith [hu_le.1, hφ_le.1, hV_le.1, hCprod_nn, this]
    · -- `Fac n x ≤ g x`
      nlinarith [hu_le.2, hφ_le.2, hV_le.2, hCprod_le, abs_nonneg (u x),
        abs_nonneg (φ_c x), abs_nonneg (V x)]
  -- AE strong measurability of `‖RHSint n − 0‖`.
  have hm_meas : AEStronglyMeasurable m (volume.restrict (UnitCube d)) :=
    hm_mem.aestronglyMeasurable
  have hu_meas : AEStronglyMeasurable u (volume.restrict (UnitCube d)) :=
    hu_memGamma.aestronglyMeasurable
  have hV_meas : AEStronglyMeasurable V (volume.restrict (UnitCube d)) :=
    hV.aestronglyMeasurable
  have hφc_meas : AEStronglyMeasurable φ_c (volume.restrict (UnitCube d)) :=
    hφc_betaP.aestronglyMeasurable
  have hmδ_meas : ∀ n, AEStronglyMeasurable (mPerDelta m (δSeq n))
      (volume.restrict (UnitCube d)) := by
    intro n
    have := hm_meas.aemeasurable.max (aemeasurable_const (b := δSeq n))
    exact this.aestronglyMeasurable.congr (Filter.Eventually.of_forall (fun x => rfl))
  have hcont_rpow : Continuous (fun y : ℝ => y ^ β) :=
    Real.continuous_rpow_const hβ.le
  have hmeas : ∀ n, AEStronglyMeasurable
      (fun x => ‖RHSint n x - (0 : ℝ)‖) (volume.restrict (UnitCube d)) := by
    intro n
    rw [hRHSdef' n]
    have hpow_meas : AEStronglyMeasurable
        (fun x => mPerDelta m (δSeq n) x ^ β) (volume.restrict (UnitCube d)) :=
      hcont_rpow.comp_aestronglyMeasurable (hmδ_meas n)
    have hFac_meas : AEStronglyMeasurable (Fac n) (volume.restrict (UnitCube d)) := by
      rw [hFacdef]
      have hCterm : AEStronglyMeasurable
          (fun x => hcong.C * (mPerDelta m (δSeq n) x ^ β + 1))
          (volume.restrict (UnitCube d)) :=
        aestronglyMeasurable_const.mul (hpow_meas.add aestronglyMeasurable_const)
      exact ((hu_meas.add hφc_meas).sub hCterm).sub hV_meas
    exact ((hFac_meas.mul ((hmδ_meas n).sub hm_meas)).sub
      aestronglyMeasurable_const).norm
  -- Apply the generic RHS DCT lemma.
  exact rhs_L1_diff_tendsto (m := m) (δSeq := δSeq) Fac RHSint
    hδ_pos hδ_le_one hδ_tendsto hm_nn hRHSdef' g hg_int hg_nn hFac_le hmeas

/-- **Witness-level per-`(δ,t)` connector-integrand integrability**
(T2 phase6 BB VIid child-5a-ii-alpha-massrhs). At the Browder–Minty witness,
the three connector integrands at the truncated density `m_δ = max(m, δ)` and
perturbed gradient `Du + t∇φ` are integrable on the cube:

* `LHSc x = (u + t·φ − C(m_δ^β+1) − V)·(m_δ − m)`,
* `RHSc x = (m_δ−1)·t·φ + m_δ·(D_pH(Du+t∇φ, m_δ) ⬝ t∇φ)`,
* `Mterm x = (−(u+t·φ) − H(Du+t∇φ, m_δ) + V)·(m_δ−m)`.

These are exactly the per-`n` `Integrable` inputs `transport_mdelta_limit_of_L1`
consumes (`hRHS_int`, `hLHSa_int`) and the child-4b-i HJB term. A thin wrapper
of `firstvar_integrands_integrable` at the witness ratio
`congestion_VI_perturbed_ratio_memLp` (reuse child-5a-i), mirroring the
`hRatio_pert`/`obtain` block of `congestion_VI_h_VI_at_mdelta_at_witness`. -/
theorem congestion_VI_firstvar_integrable_at_witness
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmon : HypothesisMonotone (d := d) H DpH)
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    {m u V : (Fin d → ℝ) → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) m)
    (hm_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hu_memGamma : MemLpPer (d := d)
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) u)
    (hV : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) V)
    (hDu_mem : ∀ i,
      MemLpPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Du i))
    (hQuot_m_mem :
      MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (fun x : Fin d → ℝ =>
          ‖fun i => Du i x‖ ^ (hcong.α * (1 + hcong.τ / hcong.β)) /
            (m x ^ hcong.τ + 1)))
    (φ : Periodic.SmoothPeriodic d) {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    (IntegrableOn (fun x =>
        (u x + t * (φ : (Fin d → ℝ) → ℝ) x
            - hcong.C * (max (m x) δ ^ hcong.β + 1) - V x)
          * (max (m x) δ - m x)) (UnitCube d))
    ∧ (IntegrableOn (fun x =>
        (max (m x) δ - 1) * (t * (φ : (Fin d → ℝ) → ℝ) x)
          + max (m x) δ * (DpH x
              (fun i => Du i x
                + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                    (Fin d → ℝ) → ℝ) x)
              (max (m x) δ)
            ⬝ (fun i => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                (Fin d → ℝ) → ℝ) x))) (UnitCube d))
    ∧ (IntegrableOn (fun x =>
        (-(u x + t * (φ : (Fin d → ℝ) → ℝ) x)
            - H x (fun i => Du i x
                + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                    (Fin d → ℝ) → ℝ) x)
              (max (m x) δ) + V x)
          * (max (m x) δ - m x)) (UnitCube d)) := by
  -- The perturbed ratio cert (`hRatio_pert`) at the witness (reuse child-5a-i).
  have hRatio_pert :
      MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
        (fun x => ‖fun i => Du i x
              + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                  (Fin d → ℝ) → ℝ) x‖
            ^ (hcong.α * (1 + hcong.τ / hcong.β))
          / (max (m x) δ ^ hcong.τ + 1)) :=
    congestion_VI_perturbed_ratio_memLp hcong hm_mem hm_nn hDu_mem hQuot_m_mem
      φ hδ t
  exact firstvar_integrands_integrable hmon hcong hm_mem hm_nn hu_memGamma hV
    hDu_mem φ hδ (t := t) hRatio_pert

/-- A.e.-measurability of the `J`-flux dot product `x ↦ J(x, p x, m x) ⬝ (q · x)`,
built from the joint `x`-measurability of `J` (via
`CongestionFluxCore.aemeasurable_J_comp`) and the coordinatewise measurability of
`p`, `m`, `q`. Used to discharge the `hmeas` certificate of
`congestion_VI_hFlux_L1_at_witness` and the J-summand measurability blocks. -/
theorem congestion_VI_Jflux_aemeasurable
    {DpH J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hJ : CongestionFluxCore (d := d) DpH J)
    {p : (Fin d → ℝ) → (Fin d → ℝ)} {m : (Fin d → ℝ) → ℝ}
    {q : Fin d → (Fin d → ℝ) → ℝ}
    (hp : AEMeasurable p (volume.restrict (UnitCube d)))
    (hm : AEMeasurable m (volume.restrict (UnitCube d)))
    (hq : ∀ i, AEMeasurable (q i) (volume.restrict (UnitCube d))) :
    AEMeasurable (fun x => J x (p x) (m x) ⬝ (fun i => q i x))
      (volume.restrict (UnitCube d)) := by
  have hJvec : AEMeasurable (fun x => J x (p x) (m x))
      (volume.restrict (UnitCube d)) := hJ.aemeasurable_J_comp hp hm
  -- `euclideanDot a b = ∑ i, a i * b i`; each summand is AEMeasurable.
  set g : Fin d → (Fin d → ℝ) → ℝ :=
    fun i x => (J x (p x) (m x)) i * q i x with hgdef
  have hsum : AEMeasurable (∑ i, g i) (volume.restrict (UnitCube d)) :=
    Finset.aemeasurable_sum Finset.univ (fun i _ => by
      rw [hgdef]
      exact ((measurable_pi_apply i).comp_aemeasurable hJvec).mul (hq i))
  have heq : (fun x => J x (p x) (m x) ⬝ (fun i => q i x)) = (∑ i, g i) := by
    funext x; rw [Finset.sum_apply]; rfl
  rw [heq]; exact hsum

/-- **Perturbed-witness flux `L¹` cert** (T2 phase6 BB VIid child-5b-ii-A2).
The `δ`-uniform flux-difference convergence
`∫ ‖m_δ·(D_pH(x, g, m_δ)⬝q) − J(x, g, m)⬝q‖ → 0` as `δ → 0⁺`, at a perturbed
gradient `g ∈ L^{γ̄}` and test gradient `q ∈ L^{γ̄}`. Discharges the `hFlux_L1`
hypothesis of `lhs_L1_diff_tendsto_J` at the Browder–Minty witness.

The `δ`-uniform dominator is `(env(·, m+1) + env(·, m))·∑ᵢ|qᵢ|`, where
`env(x, M) = C(1+M^{1-τ})‖g‖^{αt-1} + C(M^{β+1-β/α}+1)` is the closed-half-line
`J`-envelope (`mDpH_extended_bound`), monotone in `M ≥ 0`, applied at
`m_δ ≤ m+1` and at `m`. No `0 < m`: `m_δ·D_pH = J` for `m_δ > 0`, the limit
flux is the genuine extension `J(x, g, m)`. -/
theorem congestion_VI_Jflux_L1_diff_at
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hcong : CongestionGrowthCore (d := d) H DpH J)
    {m : (Fin d → ℝ) → ℝ}
    {g q : Fin d → (Fin d → ℝ) → ℝ}
    {δSeq : ℕ → ℝ}
    (hm_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1)) m)
    (hm_nn : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x)
    (hg_gamma : ∀ i, MemLpPer (d := d)
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (g i))
    (hq_gamma : ∀ i, MemLpPer (d := d)
      (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (q i))
    (hδ_pos : ∀ n, 0 < δSeq n)
    (hδ_le_one : ∀ n, δSeq n ≤ 1)
    (hδ_tendsto : Filter.Tendsto δSeq Filter.atTop (nhds (0 : ℝ))) :
    Filter.Tendsto
      (fun n => ∫ x in UnitCube d,
          ‖max (m x) (δSeq n)
              * (DpH x (fun i => g i x) (max (m x) (δSeq n))
                  ⬝ (fun i => q i x))
            - J x (fun i => g i x) (m x) ⬝ (fun i => q i x)‖
          ∂(volume : Measure (Fin d → ℝ)))
      Filter.atTop (nhds (0 : ℝ)) := by
  classical
  set α : ℝ := hcong.α with hαdef
  set β : ℝ := hcong.β with hβdef
  set τ : ℝ := hcong.τ with hτdef
  set C : ℝ := hcong.C with hCdef
  have hα : 1 < α := hcong.hα
  have hβ : 0 < β := hcong.hβ
  have hτ_nn : 0 ≤ τ := hcong.hτ.1
  have hτ_le : τ ≤ 1 := hcong.hτ.2
  have hC_pos : 0 < C := hcong.hC
  have hαpos : 0 < α := lt_trans one_pos hα
  have hm_aem : AEMeasurable m (volume.restrict (UnitCube d)) :=
    aestronglyMeasurable_iff_aemeasurable.mp hm_mem.aestronglyMeasurable
  have hg_aem : AEMeasurable (fun x => (fun i => g i x))
      (volume.restrict (UnitCube d)) := by
    rw [aemeasurable_pi_iff]; intro i
    exact aestronglyMeasurable_iff_aemeasurable.mp (hg_gamma i).aestronglyMeasurable
  -- Measurability of the flux difference (per `n`).
  have hmeas : ∀ n, AEStronglyMeasurable (fun x =>
      ‖mPerDelta m (δSeq n) x
          * (DpH x (fun i => g i x) (mPerDelta m (δSeq n) x)
              ⬝ (fun i => q i x))
        - J x (fun i => g i x) (m x) ⬝ (fun i => q i x)‖)
      (volume.restrict (UnitCube d)) := by
    intro n
    have hmδ_aem : AEMeasurable (fun x => mPerDelta m (δSeq n) x)
        (volume.restrict (UnitCube d)) := by
      simp only [mPerDelta_def]; exact hm_aem.max aemeasurable_const
    have hmDpH : AEMeasurable (fun x => mPerDelta m (δSeq n) x
        * (DpH x (fun i => g i x) (mPerDelta m (δSeq n) x)
            ⬝ (fun i => q i x))) (volume.restrict (UnitCube d)) := by
      have hvec : AEMeasurable
          (fun x => DpH x (fun i => g i x) (mPerDelta m (δSeq n) x))
          (volume.restrict (UnitCube d)) :=
        hcong.measurable_DpH.comp_aemeasurable
          (aemeasurable_id.prodMk (hg_aem.prodMk hmδ_aem))
      have hdot : AEMeasurable (fun x =>
          DpH x (fun i => g i x) (mPerDelta m (δSeq n) x)
            ⬝ (fun i => q i x)) (volume.restrict (UnitCube d)) := by
        set gg : Fin d → (Fin d → ℝ) → ℝ :=
          fun i x => (DpH x (fun j => g j x) (mPerDelta m (δSeq n) x)) i
            * q i x with hggdef
        have hsum : AEMeasurable (∑ i, gg i) (volume.restrict (UnitCube d)) :=
          Finset.aemeasurable_sum Finset.univ (fun i _ => by
            rw [hggdef]
            exact ((measurable_pi_apply i).comp_aemeasurable hvec).mul
              (aestronglyMeasurable_iff_aemeasurable.mp
                (hq_gamma i).aestronglyMeasurable))
        have heq : (fun x => DpH x (fun i => g i x) (mPerDelta m (δSeq n) x)
            ⬝ (fun i => q i x)) = (∑ i, gg i) := by
          funext x; rw [Finset.sum_apply]; rfl
        rw [heq]; exact hsum
      exact hmδ_aem.mul hdot
    have hJflux : AEMeasurable
        (fun x => J x (fun i => g i x) (m x) ⬝ (fun i => q i x))
        (volume.restrict (UnitCube d)) :=
      congestion_VI_Jflux_aemeasurable hcong.mDpHat0 hg_aem hm_aem
        (fun i => aestronglyMeasurable_iff_aemeasurable.mp
          (hq_gamma i).aestronglyMeasurable)
    exact (hmDpH.sub hJflux).norm.aestronglyMeasurable
  -- `N = ‖g·x‖ ∈ L^{γ̄}`.
  set N : (Fin d → ℝ) → ℝ := fun x => ‖fun i => g i x‖ with hNdef
  have hN_mem : MemLpPer (d := d) (ENNReal.ofReal (α * (β + 1) / β)) N := by
    have hvec : MemLpPer (d := d) (ENNReal.ofReal (α * (β + 1) / β))
        (fun x => (fun i => g i x)) := by
      rw [Periodic.memLpPer_iff_memLp, MeasureTheory.memLp_pi_iff]
      intro i; rw [hαdef, hβdef]; exact (hg_gamma i).toMemLp
    exact MemLp.toMemLpPer (MeasureTheory.MemLp.norm hvec.toMemLp)
  have hN_nn : 0 ≤ᵐ[Measure.restrict volume (UnitCube d)] N :=
    Filter.Eventually.of_forall (fun x => by rw [hNdef]; positivity)
  -- `m + 1 ∈ L^{β̄}`, nonneg.
  have hm1_mem : MemLpPer (d := d) (ENNReal.ofReal (β + 1)) (fun x => m x + 1) := by
    have := (by rw [hβdef]; exact hm_mem :
      MemLpPer (d := d) (ENNReal.ofReal (β + 1)) m).add_const (1 : ℝ)
    simpa [Pi.add_apply] using! this
  have hm1_nn : 0 ≤ᵐ[Measure.restrict volume (UnitCube d)] (fun x => m x + 1) := by
    filter_upwards [hm_nn] with x hx; change 0 ≤ m x + 1; linarith
  -- The two `J`-envelopes `∈ L^{γ̄'}`.
  have hEnvm := iota_flux_dominator_scalar_memLp_gammaBar'
    (d := d) (α := α) (β := β) (τ := τ) (K := C)
    hα hβ hτ_nn hτ_le (m := m) (N := N)
    (by rw [hβdef]; exact hm_mem) hm_nn hN_mem hN_nn
  have hEnvm1 := iota_flux_dominator_scalar_memLp_gammaBar'
    (d := d) (α := α) (β := β) (τ := τ) (K := C)
    hα hβ hτ_nn hτ_le (m := fun x => m x + 1) (N := N)
    hm1_mem hm1_nn hN_mem hN_nn
  -- `∑ i, |q i x| ∈ L^{γ̄}`.
  have hsumq : MemLpPer (d := d) (ENNReal.ofReal (α * (β + 1) / β))
      (fun x => ∑ i, |q i x|) :=
    MemLp.toMemLpPer (MeasureTheory.memLp_finset_sum (Finset.univ : Finset (Fin d))
      (f := fun i x => |q i x|)
      (fun i _ => (((by rw [hαdef, hβdef]; exact hq_gamma i :
        MemLpPer (d := d) (ENNReal.ofReal (α * (β + 1) / β))
          (q i)).toMemLp.abs) : MemLp _ _ _)) : MemLp _ _ _)
  -- Hölder conjugacy.
  have hγconj : Real.HolderConjugate (α * (β + 1) / β)
      (α * (β + 1) / β / (α * (β + 1) / β - 1)) :=
    Theorems.SimplePower.SimplePowerExponentFacts.paper_holderConjugate_gammaBar
      hα hβ
  -- The dominator and its integrability.
  set bound : (Fin d → ℝ) → ℝ := fun x =>
    ((C * (1 + (m x + 1) ^ (1 - τ)) * N x ^ (α * (1 + τ / β) - 1)
        + C * ((m x + 1) ^ (β + 1 - β / α) + 1))
      + (C * (1 + m x ^ (1 - τ)) * N x ^ (α * (1 + τ / β) - 1)
        + C * (m x ^ (β + 1 - β / α) + 1)))
    * (∑ i, |q i x|) with hbounddef
  have hbound_int : Integrable bound (volume.restrict (UnitCube d)) := by
    rw [hbounddef]
    exact MemLpPer.integrable_mul hγconj.symm (hEnvm1.add hEnvm) hsumq
  -- Exponent sign facts.
  have hexp1_nn : 0 ≤ 1 - τ := by linarith
  have hexp2_nn : 0 ≤ β + 1 - β / α := by
    have hdiv : β / α < β := by rw [div_lt_iff₀ hαpos]; nlinarith
    linarith
  -- The pointwise `δ`-uniform domination.
  have hbound : ∀ n, ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ‖‖mPerDelta m (δSeq n) x
            * (DpH x (fun i => g i x) (mPerDelta m (δSeq n) x)
                ⬝ (fun i => q i x))
          - J x (fun i => g i x) (m x) ⬝ (fun i => q i x)‖‖ ≤ bound x := by
    intro n
    filter_upwards [hcong.mDpH_extended_bound, hm_nn] with x hxJ hxm
    set p : Fin d → ℝ := fun i => g i x with hp
    have hmδ_pos : 0 < mPerDelta m (δSeq n) x := mPerDelta_pos (hδ_pos n) m x
    have hmδ_nn : 0 ≤ mPerDelta m (δSeq n) x := hmδ_pos.le
    have hmδ_le : mPerDelta m (δSeq n) x ≤ m x + 1 := by
      have h1 := mPerDelta_le_add (hδ_pos n).le hxm
      have h2 := hδ_le_one n; linarith
    have hNx_nn : 0 ≤ N x := by rw [hNdef]; positivity
    have hpN : ‖p‖ = N x := by rw [hNdef, hp]
    -- `m_δ · D_pH(x, p, m_δ) = J(x, p, m_δ)` (since `m_δ > 0`).
    have hJeq : mPerDelta m (δSeq n) x
        * (DpH x p (mPerDelta m (δSeq n) x) ⬝ (fun i => q i x))
        = J x p (mPerDelta m (δSeq n) x) ⬝ (fun i => q i x) := by
      rw [hcong.mDpHat0.J_of_pos x p (mPerDelta m (δSeq n) x) hmδ_pos]
      unfold euclideanDot
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp [Pi.smul_apply, smul_eq_mul]; ring
    -- Dot bound `|J ⬝ q| ≤ ‖J‖·∑|q|`.
    have hdot_le : ∀ M : ℝ, |J x p M ⬝ (fun i => q i x)|
        ≤ ‖J x p M‖ * (∑ i, |q i x|) := by
      intro M
      unfold euclideanDot
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun i _ => ?_)
      rw [abs_mul]
      have hcoord : |J x p M i| ≤ ‖J x p M‖ := by
        have := norm_le_pi_norm (J x p M) i
        simpa [Real.norm_eq_abs] using this
      exact mul_le_mul_of_nonneg_right hcoord (abs_nonneg _)
    -- Envelope monotonicity in `M` (for `0 ≤ M₁ ≤ M₂`).
    have henv_mono : ∀ M₁ M₂ : ℝ, 0 ≤ M₁ → M₁ ≤ M₂ →
        C * (1 + M₁ ^ (1 - τ)) * N x ^ (α * (1 + τ / β) - 1)
          + C * (M₁ ^ (β + 1 - β / α) + 1)
        ≤ C * (1 + M₂ ^ (1 - τ)) * N x ^ (α * (1 + τ / β) - 1)
          + C * (M₂ ^ (β + 1 - β / α) + 1) := by
      intro M₁ M₂ hM₁ hM₁₂
      have hpow1 : M₁ ^ (1 - τ) ≤ M₂ ^ (1 - τ) :=
        Real.rpow_le_rpow hM₁ hM₁₂ hexp1_nn
      have hpow2 : M₁ ^ (β + 1 - β / α) ≤ M₂ ^ (β + 1 - β / α) :=
        Real.rpow_le_rpow hM₁ hM₁₂ hexp2_nn
      have hNpow_nn : 0 ≤ N x ^ (α * (1 + τ / β) - 1) := Real.rpow_nonneg hNx_nn _
      have ht1 : C * (1 + M₁ ^ (1 - τ)) * N x ^ (α * (1 + τ / β) - 1)
          ≤ C * (1 + M₂ ^ (1 - τ)) * N x ^ (α * (1 + τ / β) - 1) := by
        have hfac : C * (1 + M₁ ^ (1 - τ)) ≤ C * (1 + M₂ ^ (1 - τ)) := by
          have : (1 : ℝ) + M₁ ^ (1 - τ) ≤ 1 + M₂ ^ (1 - τ) := by linarith
          exact mul_le_mul_of_nonneg_left this hC_pos.le
        exact mul_le_mul_of_nonneg_right hfac hNpow_nn
      have ht2 : C * (M₁ ^ (β + 1 - β / α) + 1)
          ≤ C * (M₂ ^ (β + 1 - β / α) + 1) := by
        have : M₁ ^ (β + 1 - β / α) + 1 ≤ M₂ ^ (β + 1 - β / α) + 1 := by linarith
        exact mul_le_mul_of_nonneg_left this hC_pos.le
      linarith
    -- `‖J(x, p, M)‖ ≤ env(x, M)` for `M ≥ 0`.
    have hJnorm_le : ∀ M : ℝ, 0 ≤ M → ‖J x p M‖
        ≤ C * (1 + M ^ (1 - τ)) * N x ^ (α * (1 + τ / β) - 1)
          + C * (M ^ (β + 1 - β / α) + 1) := by
      intro M hM
      have hb := hxJ p M hM
      rw [hpN] at hb
      exact hb
    have hsum_nn : 0 ≤ ∑ i, |q i x| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    rw [norm_norm, Real.norm_eq_abs, hJeq]
    refine le_trans (abs_sub _ _) ?_
    simp only [hbounddef]
    have hb1 : |J x p (mPerDelta m (δSeq n) x) ⬝ (fun i => q i x)|
        ≤ (C * (1 + (m x + 1) ^ (1 - τ)) * N x ^ (α * (1 + τ / β) - 1)
            + C * ((m x + 1) ^ (β + 1 - β / α) + 1)) * (∑ i, |q i x|) := by
      refine le_trans (hdot_le _) ?_
      refine mul_le_mul_of_nonneg_right ?_ hsum_nn
      refine le_trans (hJnorm_le _ hmδ_nn) ?_
      exact henv_mono _ _ hmδ_nn hmδ_le
    have hb2 : |J x p (m x) ⬝ (fun i => q i x)|
        ≤ (C * (1 + m x ^ (1 - τ)) * N x ^ (α * (1 + τ / β) - 1)
            + C * (m x ^ (β + 1 - β / α) + 1)) * (∑ i, |q i x|) := by
      refine le_trans (hdot_le _) ?_
      exact mul_le_mul_of_nonneg_right (hJnorm_le _ hxm) hsum_nn
    have hsplit : (((C * (1 + (m x + 1) ^ (1 - τ)) * N x ^ (α * (1 + τ / β) - 1)
            + C * ((m x + 1) ^ (β + 1 - β / α) + 1))
          + (C * (1 + m x ^ (1 - τ)) * N x ^ (α * (1 + τ / β) - 1)
            + C * (m x ^ (β + 1 - β / α) + 1)))
        * (∑ i, |q i x|))
        = (C * (1 + (m x + 1) ^ (1 - τ)) * N x ^ (α * (1 + τ / β) - 1)
            + C * ((m x + 1) ^ (β + 1 - β / α) + 1)) * (∑ i, |q i x|)
          + (C * (1 + m x ^ (1 - τ)) * N x ^ (α * (1 + τ / β) - 1)
            + C * (m x ^ (β + 1 - β / α) + 1)) * (∑ i, |q i x|) := by ring
    rw [hsplit]; exact add_le_add hb1 hb2
  -- Conclude via the flux `L¹` cert.
  exact congestion_VI_hFlux_L1_at_witness (DpH := DpH) (J := J) (m := m)
    (p := fun x => fun i => g i x) (δSeq := δSeq) (fun x => fun i => q i x)
    hδ_tendsto hδ_pos hm_nn hcong.mDpHat0.J_of_pos hcong.mDpHat0.continuous_J
    bound hbound_int hmeas hbound

/-! ## Witness-level full per-direction limit-density inequality
(T2 phase6 BB VIid **child-5a-ii-β** — the deliverable of this task)

Assembles the per-direction inequality `h_dir : ∀ t, 0 ≤ ∫[…tφ…] + ∫[…]`
(the `t · ι(t) ≥ 0` half, both signs) that the `t → 0` squeeze
`iota_transport_smooth_assembled_J` consumes, at the Browder–Minty witness.

For each fixed positive scale `s` and smooth test `ψ`, the `δ → 0⁺` connector
`transport_mdelta_limit_of_L1_J` (fed `δSeq n = 1/(n+1)`) produces the
`J`-extension transport inequality at `(s·ψ, s·∇ψ)`:

* `h_VI_at_mdelta` per `n` is `congestion_VI_h_VI_at_mdelta_at_witness` at
  `(δSeq n, s)`;
* the per-`n` integrabilities `hLHSa_int`/`hRHS_int` come from
  `congestion_VI_firstvar_integrable_at_witness`;
* `hMass_L1`/`hRHS_L1` come from `congestion_VI_hMass_L1_at_witness` /
  `congestion_VI_hRHS_L1_at_witness`; `hLHS_L1` is assembled from the mass
  `L¹` and the flux `L¹` cert via `lhs_L1_diff_tendsto_J`.

The genuinely `δ`-uniform-dominator-dependent flux data — the flux `L¹` cert,
the per-`n` diff integrabilities, and the `J`-limit integrand integrability —
are now **discharged internally** (child-5b-ii-A2) from the landed certs:
the flux `L¹` cert from `congestion_VI_Jflux_L1_diff_at` (its `δ`-uniform
`J`-envelope dominator + `congestion_VI_Jflux_aemeasurable` measurability),
the integrabilities from `iota_FA_uniform_dominator_J` / `_dominator` at the
base scale `t = 0` (perturbed gradient `Du + s·∇ψ`), the firstvar cert, and
`MemLpPer.integrable_mul`. No `(s, ψ)`-indexed free hypotheses remain.

The full `∀ t` statement is then: `t > 0` is the helper at `(t, φ)`; `t = 0`
is `0 ≤ 0` (every test occurrence is `0`, both integrands vanish); `t < 0` is
the helper at `(−t, −ψ)` whose `(−t)·(−φ)` test occurrences rewrite to `t·φ`
(`fderiv (-φ) = -fderiv φ` for the gradients). No `0 < m` / power-growth
crutch is used; the `{m = 0}` boundary value is the genuine `J(x, ·, 0)`. -/
theorem congestion_VI_hdir_at_witness
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
    ∀ t : ℝ,
      0 ≤
        (∫ x in UnitCube d,
            (m x - 1) * (t * (φ : (Fin d → ℝ) → ℝ) x)
              + (J x
                  (fun i => Du i x
                    + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                        (Fin d → ℝ) → ℝ) x)
                  (m x)
                ⬝ (fun i => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                    (Fin d → ℝ) → ℝ) x))
            ∂(volume : Measure (Fin d → ℝ)))
        +
        (∫ x in UnitCube d,
            ε * vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
                (fun i => Du i x
                  + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                      (Fin d → ℝ) → ℝ) x)
              * ((fun i => Du i x
                    + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                        (Fin d → ℝ) → ℝ) x)
                  ⬝ (fun i => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                      (Fin d → ℝ) → ℝ) x))
            + ε * absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
                (u x + t * (φ : (Fin d → ℝ) → ℝ) x)
              * ((u x + t * (φ : (Fin d → ℝ) → ℝ) x)
                  * (t * (φ : (Fin d → ℝ) → ℝ) x))
            ∂(volume : Measure (Fin d → ℝ))) := by
  classical
  -- `δSeq n = 1/(n+1)`.
  set δSeq : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ) with hδSeqdef
  have hδ_pos : ∀ n, 0 < δSeq n := by
    intro n; rw [hδSeqdef]
    exact div_pos one_pos (by positivity)
  have hδ_le_one : ∀ n, δSeq n ≤ 1 := by
    intro n; rw [hδSeqdef]
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hδ_tendsto : Filter.Tendsto δSeq Filter.atTop (nhds (0 : ℝ)) := by
    rw [hδSeqdef]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  -- The per-`(s, ψ)` connector conclusion at the positive scale `s`.
  have h_dir_at : ∀ (s : ℝ), 0 < s → ∀ (ψ : Periodic.SmoothPeriodic d),
      0 ≤
        (∫ x in UnitCube d,
            (m x - 1) * (s * (ψ : (Fin d → ℝ) → ℝ) x)
              + (J x
                  (fun i => Du i x
                    + s * (Periodic.SmoothPeriodic.partialDeriv i ψ :
                        (Fin d → ℝ) → ℝ) x)
                  (m x)
                ⬝ (fun i => s * (Periodic.SmoothPeriodic.partialDeriv i ψ :
                    (Fin d → ℝ) → ℝ) x))
            ∂(volume : Measure (Fin d → ℝ)))
        +
        (∫ x in UnitCube d,
            ε * vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
                (fun i => Du i x
                  + s * (Periodic.SmoothPeriodic.partialDeriv i ψ :
                      (Fin d → ℝ) → ℝ) x)
              * ((fun i => Du i x
                    + s * (Periodic.SmoothPeriodic.partialDeriv i ψ :
                        (Fin d → ℝ) → ℝ) x)
                  ⬝ (fun i => s * (Periodic.SmoothPeriodic.partialDeriv i ψ :
                      (Fin d → ℝ) → ℝ) x))
            + ε * absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
                (u x + s * (ψ : (Fin d → ℝ) → ℝ) x)
              * ((u x + s * (ψ : (Fin d → ℝ) → ℝ) x)
                  * (s * (ψ : (Fin d → ℝ) → ℝ) x))
            ∂(volume : Measure (Fin d → ℝ))) := by
    intro s hs ψ
    -- Abbreviations for the connector's `φ`/`Dφ` slots at `(s, ψ)`.
    set φc : (Fin d → ℝ) → ℝ := fun x => s * (ψ : (Fin d → ℝ) → ℝ) x with hφc
    set Dφc : Fin d → (Fin d → ℝ) → ℝ :=
      fun i x => s * (Periodic.SmoothPeriodic.partialDeriv i ψ :
        (Fin d → ℝ) → ℝ) x with hDφc
    -- The perturbed gradient `Du' = Du + s·∇ψ`.
    set Du' : Fin d → (Fin d → ℝ) → ℝ :=
      fun i x => Du i x + Dφc i x with hDu'def
    -- ===== `(s, ψ)`-flux-target discharge (child-5b-ii-A2). =====
    -- Smooth-function memberships: `φc ∈ L^{β̄'}`, `Dφc ∈ L^{γ̄}`.
    have hφc_betaP : MemLpPer (d := d)
        (ENNReal.ofReal ((hcong.β + 1) / hcong.β)) φc := by
      have hraw : MemLpPer (d := d) (ENNReal.ofReal ((hcong.β + 1) / hcong.β))
          ((ψ : (Fin d → ℝ) → ℝ)) :=
        (Periodic.MemSobolevPer.of_smoothPeriodic _ ψ).1
      have := hraw.const_smul (𝕜 := ℝ) s
      have heq : (s • (ψ : (Fin d → ℝ) → ℝ)) = φc := by
        funext x; simp [hφc, Pi.smul_apply, smul_eq_mul]
      rwa [heq] at this
    have hDφc_gamma : ∀ i, MemLpPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Dφc i) := by
      intro i
      have hraw : MemLpPer (d := d)
          (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β))
          ((Periodic.SmoothPeriodic.partialDeriv i ψ : (Fin d → ℝ) → ℝ)) :=
        (Periodic.MemSobolevPer.of_smoothPeriodic _
          (Periodic.SmoothPeriodic.partialDeriv i ψ)).1
      have := hraw.const_smul (𝕜 := ℝ) s
      have heq : (s • (Periodic.SmoothPeriodic.partialDeriv i ψ :
          (Fin d → ℝ) → ℝ)) = Dφc i := by
        funext x; simp [hDφc, Pi.smul_apply, smul_eq_mul]
      rwa [heq] at this
    have hDu'_gamma : ∀ i, MemLpPer (d := d)
        (ENNReal.ofReal (hcong.α * (hcong.β + 1) / hcong.β)) (Du' i) := by
      intro i
      have := (hDu_mem i).add (hDφc_gamma i)
      have heq : (Du i + Dφc i) = Du' i := by funext x; simp [hDu'def, Pi.add_apply]
      rwa [heq] at this
    -- Convenience AEMeasurable facts for `m`, `Du'`, `Dφc`.
    have hm_aem : AEMeasurable m (volume.restrict (UnitCube d)) :=
      aestronglyMeasurable_iff_aemeasurable.mp hm_mem.aestronglyMeasurable
    have hDu'_aem : AEMeasurable (fun x => (fun i => Du' i x))
        (volume.restrict (UnitCube d)) := by
      rw [aemeasurable_pi_iff]; intro i
      exact aestronglyMeasurable_iff_aemeasurable.mp (hDu'_gamma i).aestronglyMeasurable
    -- The `J`-flux dominator at the perturbed point (used at the base scale `t=0`).
    obtain ⟨gJ, hgJ_int, hgJ_bound⟩ :=
      iota_FA_uniform_dominator (H := H) hcong hm_mem hm_nn hDu'_gamma
        φc Dφc hφc_betaP hDφc_gamma
        (fun t => fun x => (m x - 1) * φc x
          + m x * (DpH x (fun i => Du' i x + t * Dφc i x) (m x)
              ⬝ (fun i => Dφc i x)))
        (fun t => rfl)
    obtain ⟨gJ', hgJ'_int, hgJ'_bound⟩ :=
      iota_FA_uniform_dominator_J (H := H) hcong hm_mem hm_nn hDu'_gamma
        φc Dφc hφc_betaP hDφc_gamma
        (fun t => fun x => (m x - 1) * φc x
          + (J x (fun i => Du' i x + t * Dφc i x) (m x)
              ⬝ (fun i => Dφc i x)))
        (fun t => rfl)
    -- Discharge 1: `hLHSaLim_int` (the `J`-limit integrand integrability).
    have hLHSaLim_int : Integrable (fun x =>
        (m x - 1) * φc x
          + (J x (fun i => Du' i x) (m x) ⬝ (fun i => Dφc i x)))
        (volume.restrict (UnitCube d)) := by
      have hbound0 := hgJ'_bound.self_of_nhds
      refine Integrable.mono' hgJ'_int ?_ ?_
      · -- AEStronglyMeasurable of the limit integrand.
        have hmass : AEMeasurable (fun x => (m x - 1) * φc x)
            (volume.restrict (UnitCube d)) :=
          (hm_aem.sub_const 1).mul
            (aestronglyMeasurable_iff_aemeasurable.mp hφc_betaP.aestronglyMeasurable)
        have hflux : AEMeasurable
            (fun x => J x (fun i => Du' i x) (m x) ⬝ (fun i => Dφc i x))
            (volume.restrict (UnitCube d)) :=
          congestion_VI_Jflux_aemeasurable hcong.mDpHat0 hDu'_aem hm_aem
            (fun i => aestronglyMeasurable_iff_aemeasurable.mp
              (hDφc_gamma i).aestronglyMeasurable)
        exact (hmass.add hflux).aestronglyMeasurable
      · -- Domination by `gJ'` at `t = 0`.
        filter_upwards [hbound0] with x hx
        simpa using hx
    -- Discharge 2: `hMass_diff_int` (per-`n` mass-difference integrability).
    have hMass_diff_int : ∀ (n : ℕ), Integrable (fun x =>
        ((max (m x) (δSeq n) - 1) * φc x) - ((m x - 1) * φc x))
        (volume.restrict (UnitCube d)) := by
      intro n
      have hβconj : Real.HolderConjugate (hcong.β + 1) ((hcong.β + 1) / hcong.β) :=
        Theorems.SimplePower.SimplePowerExponentFacts.paper_holderConjugate_betaBar
          hcong.hβ
      have hmδ_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1))
          (fun x => max (m x) (δSeq n)) := by
        have := mPerDelta_memLpPer (d := d) (p := ENNReal.ofReal (hcong.β + 1))
          (δ := δSeq n) (hδ_pos n).le (m := m) hm_mem hm_nn
        simpa [mPerDelta] using! this
      have hmδ1 : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1))
          (fun x => max (m x) (δSeq n) - 1) := by
        have := hmδ_mem.add_const (-1 : ℝ)
        have heq : ((fun x => max (m x) (δSeq n)) + fun _ : Fin d → ℝ => (-1 : ℝ))
            = (fun x => max (m x) (δSeq n) - 1) := by funext x; simp; ring
        rwa [heq] at this
      have hm1 : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1))
          (fun x => m x - 1) := by
        have := hm_mem.add_const (-1 : ℝ)
        have heq : (m + fun _ : Fin d → ℝ => (-1 : ℝ)) = (fun x => m x - 1) := by
          funext x; simp [Pi.add_apply]; ring
        rwa [heq] at this
      have h1 : IntegrableOn (fun x => (max (m x) (δSeq n) - 1) * φc x)
          (UnitCube d) := MemLpPer.integrable_mul hβconj hmδ1 hφc_betaP
      have h2 : IntegrableOn (fun x => (m x - 1) * φc x) (UnitCube d) :=
        MemLpPer.integrable_mul hβconj hm1 hφc_betaP
      exact h1.sub h2
    -- Discharge 3: `hFlux_diff_int` (per-`n` flux-difference integrability).
    have hFlux_diff_int : ∀ (n : ℕ), Integrable (fun x =>
        (max (m x) (δSeq n)
            * (DpH x (fun i => Du' i x) (max (m x) (δSeq n))
                ⬝ (fun i => Dφc i x)))
          - (J x (fun i => Du' i x) (m x) ⬝ (fun i => Dφc i x)))
        (volume.restrict (UnitCube d)) := by
      intro n
      -- `m_δ · D_pH ⬝ Dφc` summand: from the firstvar integrability cert.
      have hmDpH : Integrable (fun x =>
          (max (m x) (δSeq n) - 1) * φc x
            + max (m x) (δSeq n)
              * (DpH x (fun i => Du i x + Dφc i x) (max (m x) (δSeq n))
                  ⬝ (fun i => Dφc i x))) (volume.restrict (UnitCube d)) := by
        obtain ⟨_, h2, _⟩ :=
          congestion_VI_firstvar_integrable_at_witness hmon hcong hm_mem hm_nn
            hu_memGamma hV hDu_mem hQuot_m_mem ψ (hδ_pos n) s
        exact h2
      have hmDpHflux : Integrable (fun x =>
          max (m x) (δSeq n)
            * (DpH x (fun i => Du' i x) (max (m x) (δSeq n))
                ⬝ (fun i => Dφc i x))) (volume.restrict (UnitCube d)) := by
        -- subtract the mass part `(m_δ-1)·φc`, which is integrable.
        have hmass : Integrable (fun x => (max (m x) (δSeq n) - 1) * φc x)
            (volume.restrict (UnitCube d)) := by
          have hβconj : Real.HolderConjugate (hcong.β + 1)
              ((hcong.β + 1) / hcong.β) :=
            Theorems.SimplePower.SimplePowerExponentFacts.paper_holderConjugate_betaBar
              hcong.hβ
          have hmδ_mem : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1))
              (fun x => max (m x) (δSeq n)) := by
            have := mPerDelta_memLpPer (d := d) (p := ENNReal.ofReal (hcong.β + 1))
              (δ := δSeq n) (hδ_pos n).le (m := m) hm_mem hm_nn
            simpa [mPerDelta] using! this
          have hmδ1 : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1))
              (fun x => max (m x) (δSeq n) - 1) := by
            have := hmδ_mem.add_const (-1 : ℝ)
            have heq : ((fun x => max (m x) (δSeq n))
                + fun _ : Fin d → ℝ => (-1 : ℝ))
                = (fun x => max (m x) (δSeq n) - 1) := by funext x; simp; ring
            rwa [heq] at this
          exact MemLpPer.integrable_mul hβconj hmδ1 hφc_betaP
        refine (hmDpH.sub hmass).congr (Filter.Eventually.of_forall (fun x => ?_))
        simp only [Pi.sub_apply, hDu'def]; ring
      -- `J ⬝ Dφc` summand: dominate by `gJ'` at `t=0` (mass-subtracted).
      have hJflux : Integrable (fun x =>
          J x (fun i => Du' i x) (m x) ⬝ (fun i => Dφc i x))
          (volume.restrict (UnitCube d)) := by
        have hmass : Integrable (fun x => (m x - 1) * φc x)
            (volume.restrict (UnitCube d)) := by
          have hβconj : Real.HolderConjugate (hcong.β + 1)
              ((hcong.β + 1) / hcong.β) :=
            Theorems.SimplePower.SimplePowerExponentFacts.paper_holderConjugate_betaBar
              hcong.hβ
          have hm1 : MemLpPer (d := d) (ENNReal.ofReal (hcong.β + 1))
              (fun x => m x - 1) := by
            have := hm_mem.add_const (-1 : ℝ)
            have heq : (m + fun _ : Fin d → ℝ => (-1 : ℝ)) = (fun x => m x - 1) := by
              funext x; simp [Pi.add_apply]; ring
            rwa [heq] at this
          exact MemLpPer.integrable_mul hβconj hm1 hφc_betaP
        refine (hLHSaLim_int.sub hmass).congr
          (Filter.Eventually.of_forall (fun x => ?_))
        simp only [Pi.sub_apply]; ring
      exact hmDpHflux.sub hJflux
    -- Discharge 4: `hFlux_L1` (the `δ`-uniform flux `L¹` cert).
    have hFlux_L1 :
        Filter.Tendsto
          (fun n => ∫ x in UnitCube d,
              ‖max (m x) (δSeq n)
                  * (DpH x (fun i => Du' i x) (max (m x) (δSeq n))
                      ⬝ (fun i => Dφc i x))
                - J x (fun i => Du' i x) (m x) ⬝ (fun i => Dφc i x)‖
              ∂(volume : Measure (Fin d → ℝ)))
          Filter.atTop (nhds (0 : ℝ)) :=
      congestion_VI_Jflux_L1_diff_at (H := H) hcong hm_mem hm_nn
        hDu'_gamma hDφc_gamma hδ_pos hδ_le_one hδ_tendsto
    -- Per-`n` variational inequality at the witness (child-5a-i).
    have h_VI_at_mdelta : ∀ n,
        (∫ x in UnitCube d,
            (u x + φc x - hcong.C * ((max (m x) (δSeq n)) ^ hcong.β + 1) - V x)
              * (max (m x) (δSeq n) - m x)
            ∂(volume : Measure (Fin d → ℝ)))
        ≤
        (∫ x in UnitCube d,
            (max (m x) (δSeq n) - 1) * φc x
              + max (m x) (δSeq n)
                * (DpH x (fun i => Du i x + Dφc i x) (max (m x) (δSeq n))
                    ⬝ (fun i => Dφc i x))
            ∂(volume : Measure (Fin d → ℝ)))
        +
        (∫ x in UnitCube d,
            ε * vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
                (fun i => Du i x + Dφc i x)
              * ((fun i => Du i x + Dφc i x) ⬝ (fun i => Dφc i x))
            + ε * absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
                (u x + φc x) * ((u x + φc x) * φc x)
            ∂(volume : Measure (Fin d → ℝ))) := by
      intro n
      exact congestion_VI_h_VI_at_mdelta_at_witness hmon hcong hm_mem hm_nn
        hu_memGamma hDu_mem hQuot_m_mem hVmeas hV hAeq hKeq hVI hw_m hw_u hw_Du
        hcoeWeak_Du ψ (hδ_pos n) hs
    -- The per-`n` connector integrands and their integrability.
    set LHSa : ℕ → (Fin d → ℝ) → ℝ := fun n x =>
      (max (m x) (δSeq n) - 1) * φc x
        + max (m x) (δSeq n)
          * (DpH x (fun i => Du i x + Dφc i x) (max (m x) (δSeq n))
              ⬝ (fun i => Dφc i x)) with hLHSadef
    set LHSaLim : (Fin d → ℝ) → ℝ := fun x =>
      (m x - 1) * φc x
        + (J x (fun i => Du i x + Dφc i x) (m x) ⬝ (fun i => Dφc i x))
      with hLHSaLimdef
    set RHSint : ℕ → (Fin d → ℝ) → ℝ := fun n x =>
      (u x + φc x - hcong.C * ((max (m x) (δSeq n)) ^ hcong.β + 1) - V x)
        * (max (m x) (δSeq n) - m x) with hRHSdef
    -- Per-`n` integrabilities (child-5a-ii-α-massrhs, witness instantiation).
    have hInts : ∀ n,
        Integrable (RHSint n) (volume.restrict (UnitCube d))
        ∧ Integrable (LHSa n) (volume.restrict (UnitCube d)) := by
      intro n
      obtain ⟨h1, h2, _⟩ :=
        congestion_VI_firstvar_integrable_at_witness hmon hcong hm_mem hm_nn
          hu_memGamma hV hDu_mem hQuot_m_mem ψ (hδ_pos n) s
      exact ⟨h1, h2⟩
    have hRHS_int : ∀ n, Integrable (RHSint n) (volume.restrict (UnitCube d)) :=
      fun n => (hInts n).1
    have hLHSa_int : ∀ n, Integrable (LHSa n) (volume.restrict (UnitCube d)) :=
      fun n => (hInts n).2
    have hLHSaLim_int' : Integrable LHSaLim (volume.restrict (UnitCube d)) := by
      rw [hLHSaLimdef]; exact hLHSaLim_int
    -- Mass `L¹` cert (child-5a-ii-α-massrhs).
    have hMass_L1 :
        Filter.Tendsto
          (fun n => ∫ x in UnitCube d,
              ‖φc x * (max (m x) (δSeq n)) - φc x * m x‖
              ∂(volume : Measure (Fin d → ℝ)))
          Filter.atTop (nhds (0 : ℝ)) :=
      congestion_VI_hMass_L1_at_witness hδ_pos hδ_tendsto hm_mem hm_nn ψ s
    -- RHS `L¹` cert (child-5a-ii-α-massrhs).
    have hRHS_L1 :
        Filter.Tendsto
          (fun n => ∫ x in UnitCube d, ‖RHSint n x - (0 : ℝ)‖
            ∂(volume : Measure (Fin d → ℝ)))
          Filter.atTop (nhds (0 : ℝ)) :=
      congestion_VI_hRHS_L1_at_witness hcong hδ_pos hδ_le_one hδ_tendsto hm_mem
        hm_nn hu_memGamma hV ψ s RHSint (fun n => rfl)
    -- Assemble the LHS `L¹`-difference convergence.
    have hLHS_L1 :
        Filter.Tendsto
          (fun n => ∫ x in UnitCube d, ‖LHSa n x - LHSaLim x‖
            ∂(volume : Measure (Fin d → ℝ)))
          Filter.atTop (nhds (0 : ℝ)) :=
      lhs_L1_diff_tendsto_J (DpH := DpH) (J := J) (m := m)
        (p := fun x => fun i => Du i x + Dφc i x) (δSeq := δSeq)
        φc (fun x => fun i => Dφc i x) LHSa LHSaLim
        (fun n => rfl) rfl
        hMass_diff_int hFlux_diff_int
        hMass_L1 hFlux_L1
    -- Feed everything into the `δ → 0` connector.
    exact transport_mdelta_limit_of_L1_J (V := V) (DpH := DpH) (J := J)
      (Du := Du) (m := m) (u := u)
      (ε := ε) (γBar := hcong.α * (hcong.β + 1) / hcong.β)
      (β := hcong.β) (C := hcong.C)
      φc (0 : (Fin d → ℝ) → ℝ) (fun i x => Dφc i x)
      hδ_pos hδ_le_one hδ_tendsto h_VI_at_mdelta
      LHSa LHSaLim RHSint (fun n => rfl) rfl (fun n => rfl)
      hLHSa_int hLHSaLim_int' hRHS_int hLHS_L1 hRHS_L1
  -- The full `∀ t` statement: `t > 0`, `t = 0`, `t < 0`.
  intro t
  rcases lt_trichotomy t 0 with ht | ht | ht
  · -- `t < 0`: apply the helper at `(−t, −φ)` and rewrite `(−t)·(−φ) = t·φ`.
    have hposneg : 0 < -t := by linarith
    have hkey := h_dir_at (-t) hposneg (-φ)
    -- Pointwise gradient identity `∂ᵢ(−φ) = −∂ᵢφ`.
    have hpd : ∀ (i : Fin d) (x : Fin d → ℝ),
        (Periodic.SmoothPeriodic.partialDeriv i (-φ) : (Fin d → ℝ) → ℝ) x
          = -((Periodic.SmoothPeriodic.partialDeriv i φ : (Fin d → ℝ) → ℝ) x) := by
      intro i x
      simp only [Periodic.SmoothPeriodic.coe_partialDeriv,
        Periodic.SmoothPeriodic.coe_neg]
      rw [fderiv_neg]
      rfl
    -- Rewrite both integrals of `hkey` to the goal shape via a.e. (here pointwise)
    -- equality of the integrands.
    have hI1 :
        (∫ x in UnitCube d,
            (m x - 1) * (-t * ((-φ : Periodic.SmoothPeriodic d) :
                (Fin d → ℝ) → ℝ) x)
              + (J x
                  (fun i => Du i x
                    + -t * (Periodic.SmoothPeriodic.partialDeriv i (-φ) :
                        (Fin d → ℝ) → ℝ) x)
                  (m x)
                ⬝ (fun i => -t
                    * (Periodic.SmoothPeriodic.partialDeriv i (-φ) :
                        (Fin d → ℝ) → ℝ) x))
            ∂(volume : Measure (Fin d → ℝ)))
        =
        (∫ x in UnitCube d,
            (m x - 1) * (t * (φ : (Fin d → ℝ) → ℝ) x)
              + (J x
                  (fun i => Du i x
                    + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                        (Fin d → ℝ) → ℝ) x)
                  (m x)
                ⬝ (fun i => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                    (Fin d → ℝ) → ℝ) x))
            ∂(volume : Measure (Fin d → ℝ))) := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      simp only []
      have hgradf : (fun i => Du i x
            + -t * (Periodic.SmoothPeriodic.partialDeriv i (-φ) :
                (Fin d → ℝ) → ℝ) x)
          = (fun i => Du i x
            + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                (Fin d → ℝ) → ℝ) x) := by
        funext i; rw [hpd i x]; ring
      have hgrad2 : (fun i => -t
              * (Periodic.SmoothPeriodic.partialDeriv i (-φ) :
                  (Fin d → ℝ) → ℝ) x)
          = (fun i => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
              (Fin d → ℝ) → ℝ) x) := by
        funext i; rw [hpd i x]; ring
      have hφval : (-t * ((-φ : Periodic.SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) x)
          = t * (φ : (Fin d → ℝ) → ℝ) x := by
        simp only [Periodic.SmoothPeriodic.coe_neg, Pi.neg_apply]; ring
      rw [hφval, hgradf, hgrad2]
    have hI2 :
        (∫ x in UnitCube d,
            ε * vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
                (fun i => Du i x
                  + -t * (Periodic.SmoothPeriodic.partialDeriv i (-φ) :
                      (Fin d → ℝ) → ℝ) x)
              * ((fun i => Du i x
                    + -t * (Periodic.SmoothPeriodic.partialDeriv i (-φ) :
                        (Fin d → ℝ) → ℝ) x)
                  ⬝ (fun i => -t
                      * (Periodic.SmoothPeriodic.partialDeriv i (-φ) :
                          (Fin d → ℝ) → ℝ) x))
            + ε * absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
                (u x + -t * ((-φ : Periodic.SmoothPeriodic d) :
                    (Fin d → ℝ) → ℝ) x)
              * ((u x + -t * ((-φ : Periodic.SmoothPeriodic d) :
                    (Fin d → ℝ) → ℝ) x)
                  * (-t * ((-φ : Periodic.SmoothPeriodic d) :
                      (Fin d → ℝ) → ℝ) x))
            ∂(volume : Measure (Fin d → ℝ)))
        =
        (∫ x in UnitCube d,
            ε * vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
                (fun i => Du i x
                  + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                      (Fin d → ℝ) → ℝ) x)
              * ((fun i => Du i x
                    + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                        (Fin d → ℝ) → ℝ) x)
                  ⬝ (fun i => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                      (Fin d → ℝ) → ℝ) x))
            + ε * absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
                (u x + t * (φ : (Fin d → ℝ) → ℝ) x)
              * ((u x + t * (φ : (Fin d → ℝ) → ℝ) x)
                  * (t * (φ : (Fin d → ℝ) → ℝ) x))
            ∂(volume : Measure (Fin d → ℝ))) := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      simp only []
      have hgradf : (fun i => Du i x
            + -t * (Periodic.SmoothPeriodic.partialDeriv i (-φ) :
                (Fin d → ℝ) → ℝ) x)
          = (fun i => Du i x
            + t * (Periodic.SmoothPeriodic.partialDeriv i φ :
                (Fin d → ℝ) → ℝ) x) := by
        funext i; rw [hpd i x]; ring
      have hgrad2 : (fun i => -t
              * (Periodic.SmoothPeriodic.partialDeriv i (-φ) :
                  (Fin d → ℝ) → ℝ) x)
          = (fun i => t * (Periodic.SmoothPeriodic.partialDeriv i φ :
              (Fin d → ℝ) → ℝ) x) := by
        funext i; rw [hpd i x]; ring
      have hφval : (-t * ((-φ : Periodic.SmoothPeriodic d) :
              (Fin d → ℝ) → ℝ) x)
          = t * (φ : (Fin d → ℝ) → ℝ) x := by
        simp only [Periodic.SmoothPeriodic.coe_neg, Pi.neg_apply]; ring
      rw [hgradf, hgrad2, hφval]
    rw [hI1, hI2] at hkey
    exact hkey
  · -- `t = 0`: both integrands vanish.
    subst ht
    have h1 : (∫ x in UnitCube d,
          (m x - 1) * ((0 : ℝ) * (φ : (Fin d → ℝ) → ℝ) x)
            + (J x
                (fun i => Du i x
                  + (0 : ℝ) * (Periodic.SmoothPeriodic.partialDeriv i φ :
                      (Fin d → ℝ) → ℝ) x)
                (m x)
              ⬝ (fun i => (0 : ℝ)
                  * (Periodic.SmoothPeriodic.partialDeriv i φ :
                      (Fin d → ℝ) → ℝ) x))
          ∂(volume : Measure (Fin d → ℝ))) = 0 := by
      have hint : (fun x : Fin d → ℝ =>
          (m x - 1) * ((0 : ℝ) * (φ : (Fin d → ℝ) → ℝ) x)
            + (J x
                (fun i => Du i x
                  + (0 : ℝ) * (Periodic.SmoothPeriodic.partialDeriv i φ :
                      (Fin d → ℝ) → ℝ) x)
                (m x)
              ⬝ (fun i => (0 : ℝ)
                  * (Periodic.SmoothPeriodic.partialDeriv i φ :
                      (Fin d → ℝ) → ℝ) x)))
          = (fun _ => (0 : ℝ)) := by
        funext x
        have hz : (fun i => (0 : ℝ)
            * (Periodic.SmoothPeriodic.partialDeriv i φ :
                (Fin d → ℝ) → ℝ) x) = (fun _ => (0 : ℝ)) := by
          funext i; ring
        rw [hz]
        unfold euclideanDot
        simp
      rw [hint, MeasureTheory.integral_zero]
    have h2 : (∫ x in UnitCube d,
          ε * vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
              (fun i => Du i x
                + (0 : ℝ) * (Periodic.SmoothPeriodic.partialDeriv i φ :
                    (Fin d → ℝ) → ℝ) x)
            * ((fun i => Du i x
                  + (0 : ℝ) * (Periodic.SmoothPeriodic.partialDeriv i φ :
                      (Fin d → ℝ) → ℝ) x)
                ⬝ (fun i => (0 : ℝ)
                    * (Periodic.SmoothPeriodic.partialDeriv i φ :
                        (Fin d → ℝ) → ℝ) x))
          + ε * absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
              (u x + (0 : ℝ) * (φ : (Fin d → ℝ) → ℝ) x)
            * ((u x + (0 : ℝ) * (φ : (Fin d → ℝ) → ℝ) x)
                * ((0 : ℝ) * (φ : (Fin d → ℝ) → ℝ) x))
          ∂(volume : Measure (Fin d → ℝ))) = 0 := by
      have hint : (fun x : Fin d → ℝ =>
          ε * vecAbsPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
              (fun i => Du i x
                + (0 : ℝ) * (Periodic.SmoothPeriodic.partialDeriv i φ :
                    (Fin d → ℝ) → ℝ) x)
            * ((fun i => Du i x
                  + (0 : ℝ) * (Periodic.SmoothPeriodic.partialDeriv i φ :
                      (Fin d → ℝ) → ℝ) x)
                ⬝ (fun i => (0 : ℝ)
                    * (Periodic.SmoothPeriodic.partialDeriv i φ :
                        (Fin d → ℝ) → ℝ) x))
          + ε * absPowMinusTwo (hcong.α * (hcong.β + 1) / hcong.β)
              (u x + (0 : ℝ) * (φ : (Fin d → ℝ) → ℝ) x)
            * ((u x + (0 : ℝ) * (φ : (Fin d → ℝ) → ℝ) x)
                * ((0 : ℝ) * (φ : (Fin d → ℝ) → ℝ) x)))
          = (fun _ => (0 : ℝ)) := by
        funext x
        have hz : (fun i => (0 : ℝ)
            * (Periodic.SmoothPeriodic.partialDeriv i φ :
                (Fin d → ℝ) → ℝ) x) = (fun _ => (0 : ℝ)) := by
          funext i; ring
        rw [hz]
        unfold euclideanDot
        simp
      rw [hint, MeasureTheory.integral_zero]
    rw [h1, h2]; norm_num
  · -- `t > 0`: the helper at `(t, φ)`.
    exact h_dir_at t ht φ

end Congestion
end StationaryMFG
end
