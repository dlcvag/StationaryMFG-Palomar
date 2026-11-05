module

public import StationaryMFG.Hamiltonian.Assumptions

@[expose] public section

/-!
# Hamiltonian — algebraic consequences of `(onH.monotone)` (paper `rmk:cxty`)

This file derives the immediate algebraic consequences of the
Lasry–Lions monotonicity inequality `(hmon)` packaged in
`HypothesisMonotone`. These are the building blocks that the paper
introduces in Remark `rmk:cxty`
(`Source/FGU-monotone_revised.tex`, lines 432–438).

The two lemmas proved here are pure manipulations of the inequality

  `(-H(x, p₁, m₁) + H(x, p₂, m₂)) · (m₁ - m₂)`
  `+ (m₁ • D_pH(x, p₁, m₁) - m₂ • D_pH(x, p₂, m₂)) ⬝ (p₁ - p₂) ≥ 0`

with one of the slots collapsed:

* `antitone_in_m` — taking `p₁ = p₂` makes the dot-product summand
  vanish and yields `m ↦ H(x, p, m)` antitone on `(0, ∞)` for a.e. `x`
  and every `p`.
* `dpH_monotone_in_p` — taking `m₁ = m₂ = m > 0` makes the
  `(m₁ - m₂)` summand vanish and yields the (Euclidean) monotonicity
  of `p ↦ D_pH(x, p, m)` for a.e. `x` and every `m > 0`.

The paper goes one step further and concludes that `p ↦ H(x, p, m)`
is convex, but that step relies on the implicit identification of
`D_pH` with the `p`-gradient of `H`, which our `HypothesisMonotone`
bundle does not assert. The *gradient-monotonicity* statement
proved here is the exact algebraic content of `(hmon)` in the
`m₁ = m₂` slice and is what downstream lemmas will combine with a
`DpH = ∂_p H` hypothesis to recover convexity (tracked as a separate
task; see `docs/TASKS/backlog/paper-rmk-cxty-c.md`).

The third bullet of `rmk:cxty` — the sup-formula
`H(x, p, 0) = sup_{m > 0} H(x, p, m)` together with lower
semicontinuity and convexity of `p ↦ H(x, p, 0)` — is split out
into a child task `paper:rmk:cxty.c` because it combines this file's
antitone-in-`m` lemma with the `WithTop`-valued limit from
`(a:Hat0)` and the convexity step that this file does not establish.
-/

namespace StationaryMFG
namespace Hamiltonian

open MeasureTheory
open StationaryMFG.Periodic

variable {d : ℕ}

/-! ### Helper: dot product is bilinear in the obvious way -/

-- `euclideanDot_smul_left` is provided publicly by
-- `StationaryMFG.Hamiltonian` (Assumptions.lean); the former private
-- duplicate here was removed to avoid a name clash (P1c).

/-- Pulling a scalar through `m • v - m • w = m • (v - w)`. -/
private lemma smul_sub_smul_self (m : ℝ) (v w : Fin d → ℝ) :
    m • v - m • w = m • (v - w) := by
  funext i
  simp [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_sub]

/-! ### Lemma 1: `H(x, p, ·)` is nonincreasing on `ℝ⁺` -/

/--
**Paper `rmk:cxty`, first bullet** (line 434): under `(onH.monotone)`,
for almost every `x ∈ 𝕋^d` and every `p ∈ ℝ^d`, the section
`m ↦ H(x, p, m)` is nonincreasing on the open half-line `(0, ∞)`.

Proof: take `p₁ = p₂ = p` in the Lasry–Lions inequality `(hmon)`.
The `(p₁ - p₂)` factor in the second summand kills it, leaving
`(H(x, p, m₂) - H(x, p, m₁)) · (m₁ - m₂) ≥ 0`. A two-way case
split on `m₁ ≤ m₂` then yields the antitone conclusion.
-/
theorem antitone_in_m
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisMonotone H DpH) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p, AntitoneOn (fun m : ℝ => H x p m) (Set.Ioi (0 : ℝ)) := by
  refine h.monotone.mono ?_
  intro x hx p m₁ hm₁ m₂ hm₂ hle
  -- We want `H x p m₂ ≤ H x p m₁`.
  -- Apply `hx` at `(p₁, m₁) = (p, m₂)` and `(p₂, m₂) = (p, m₁)`.
  have hxm := hx p m₂ p m₁ (by exact hm₂) (by exact hm₁)
  -- Simplify: the `(p - p)`-dot summand vanishes.
  have hpp : (m₂ • DpH x p m₂ - m₁ • DpH x p m₁) ⬝ (p - p) = 0 := by
    simp
  rw [hpp, add_zero] at hxm
  -- `hxm : 0 ≤ (-H x p m₂ + H x p m₁) * (m₂ - m₁)`.
  -- Case `m₁ = m₂`: then `H x p m₂ = H x p m₁`, so `≤` is trivial.
  rcases lt_or_eq_of_le hle with hlt | heq
  · -- `m₁ < m₂`, so `m₂ - m₁ > 0`. Combined with `0 ≤ (…) * (m₂ - m₁)`,
    -- we get `0 ≤ -H x p m₂ + H x p m₁`.
    have hpos : 0 < m₂ - m₁ := sub_pos.mpr hlt
    have hge : 0 ≤ -H x p m₂ + H x p m₁ :=
      nonneg_of_mul_nonneg_left hxm hpos
    linarith
  · -- `m₁ = m₂` exactly; equality of the function.
    subst heq
    exact le_of_eq rfl

/-! ### Lemma 2: `D_pH(x, ·, m)` is monotone in `p` (Euclidean sense) -/

/--
**Paper `rmk:cxty`, second bullet** (line 434), gradient form: under
`(onH.monotone)`, for almost every `x ∈ 𝕋^d` and every `m > 0`, the
section `p ↦ D_pH(x, p, m)` is *Euclidean-monotone*:

  `(D_pH(x, p₁, m) - D_pH(x, p₂, m)) ⬝ (p₁ - p₂) ≥ 0` for all `p₁, p₂`.

Proof: take `m₁ = m₂ = m` in `(hmon)`. The `(m₁ - m₂)` factor kills
the first summand, so the inequality reduces to
`m · ((D_pH(x, p₁, m) - D_pH(x, p₂, m)) ⬝ (p₁ - p₂)) ≥ 0`, and
dividing by `m > 0` gives the claim.

The paper next concludes that `p ↦ H(x, p, m)` is convex; that step
silently uses that `D_pH` is the `p`-gradient of `H`, an identification
not present in our `HypothesisMonotone` bundle. We therefore stop at
the gradient-monotonicity statement, which is the exact algebraic
content of `(hmon)` in the `m₁ = m₂` slice. The convexity-of-`H`
step is tracked as a separate task; see the module docstring.
-/
theorem dpH_monotone_in_p
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (h : HypothesisMonotone H DpH) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ m : ℝ, 0 < m → ∀ p₁ p₂ : Fin d → ℝ,
        0 ≤ (DpH x p₁ m - DpH x p₂ m) ⬝ (p₁ - p₂) := by
  refine h.monotone.mono ?_
  intro x hx m hm p₁ p₂
  -- Apply `hx` at the same `m` for both slots.
  have hxm := hx p₁ m p₂ m hm hm
  -- The `(m - m) = 0` factor kills the first summand.
  have hzero : (-H x p₁ m + H x p₂ m) * (m - m) = 0 := by
    simp
  rw [hzero, zero_add] at hxm
  -- `hxm : 0 ≤ (m • DpH x p₁ m - m • DpH x p₂ m) ⬝ (p₁ - p₂)`.
  -- Pull the scalar through to obtain `0 ≤ m * ((D_pH p₁ - D_pH p₂) ⬝ (p₁ - p₂))`.
  rw [smul_sub_smul_self, euclideanDot_smul_left] at hxm
  -- `hxm : 0 ≤ m * ((D_pH x p₁ m - D_pH x p₂ m) ⬝ (p₁ - p₂))`.
  -- Divide by `m > 0`.
  exact (mul_nonneg_iff_of_pos_left hm).mp hxm

/-! ### Sup-formula at `m = 0` and lsc / convex consequences -/

section SupFormula

open Filter Topology Set

/--
**Auxiliary**: under `(onH.monotone)` and `(a:Hat0)`, for a.e. `x ∈ 𝕋^d`
and every `p ∈ ℝ^d`, the value `H_at_zero H x p` is the *least upper
bound* of the range of `m ↦ Hext H x p m` over `m > 0`.

Proof outline. Antitonicity of `m ↦ H(x, p, m)` on `(0, ∞)` (from
`antitone_in_m`) lifts to antitonicity in `WithTop ℝ`. Combined with
the limit selector from `(a:Hat0)`, both directions of `IsLUB` follow:
upper-bound from `Antitone.ge_of_tendsto`-style reasoning, least from
`le_of_tendsto'` against the filter `𝓝[>] (0:ℝ)` (which is `NeBot`
since `ℝ` has no maximum).
-/
theorem isLUB_Hext_pos
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmono : HypothesisMonotone H DpH) (hHat0 : HypothesisHat0 H) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p : Fin d → ℝ,
        IsLUB (Set.range (fun m : {m : ℝ // 0 < m} => Hext H x p m.1))
              (H_at_zero H x p) := by
  -- We combine the antitone-in-m result with the existence of a
  -- right-hand limit at `0`.
  have hAnti := antitone_in_m hmono
  filter_upwards [hAnti, hHat0.exists_limit_at_zero] with x hAntiX hLimX p
  -- Specialise to this `p`.
  have hAntiP : AntitoneOn (fun m : ℝ => H x p m) (Set.Ioi (0 : ℝ)) := hAntiX p
  have hLimP :
      Tendsto (fun m : ℝ => ((H x p m : ℝ) : WithTop ℝ))
        (𝓝[>] (0 : ℝ)) (𝓝 (H_at_zero H x p)) :=
    tendsto_Hext_zero_of_exists (hLimX p)
  -- Build `IsLUB` of the range.
  have hNeBot : (𝓝[>] (0 : ℝ)).NeBot := nhdsGT_neBot 0
  refine ⟨?_, ?_⟩
  · -- Upper-bound part: every `Hext_pos m₀` is `≤ H_at_zero`.
    rintro y ⟨m₀, rfl⟩
    change Hext H x p m₀.1 ≤ H_at_zero H x p
    -- Rewrite `Hext H x p m₀.1` to its coe form.
    rw [Hext_of_pos H x p m₀.2]
    -- Eventually in `𝓝[>] (0:ℝ)`, we have `m ≤ m₀.1`, hence by antitone
    -- `H x p m₀.1 ≤ H x p m`, hence the WithTop-cast inequality.
    have hev :
        ∀ᶠ m in 𝓝[>] (0 : ℝ),
          ((H x p m₀.1 : ℝ) : WithTop ℝ) ≤ ((H x p m : ℝ) : WithTop ℝ) := by
      have hIooMem : Set.Ioo (0 : ℝ) m₀.1 ∈ 𝓝[>] (0 : ℝ) :=
        Ioo_mem_nhdsGT m₀.2
      filter_upwards [hIooMem] with m hm
      have hm_pos : 0 < m := hm.1
      have hm_le : m ≤ m₀.1 := le_of_lt hm.2
      have hH : H x p m₀.1 ≤ H x p m :=
        hAntiP (Set.mem_Ioi.mpr hm_pos)
          (Set.mem_Ioi.mpr m₀.2)
          hm_le
      exact_mod_cast hH
    -- `ge_of_tendsto` against the (`NeBot`) filter `𝓝[>] (0 : ℝ)`.
    exact ge_of_tendsto hLimP hev
  · -- Least-upper-bound part: any upper bound `b` dominates `H_at_zero`.
    intro b hb
    -- For every `m > 0`, `Hext H x p m ≤ b`.
    have hev : ∀ᶠ m in 𝓝[>] (0 : ℝ), ((H x p m : ℝ) : WithTop ℝ) ≤ b := by
      filter_upwards [self_mem_nhdsWithin] with m hm
      have hm_pos : 0 < m := hm
      have hcoe : Hext H x p m = ((H x p m : ℝ) : WithTop ℝ) :=
        Hext_of_pos H x p hm_pos
      have hrange : Hext H x p m ∈
          Set.range (fun m : {m : ℝ // 0 < m} => Hext H x p m.1) :=
        ⟨⟨m, hm_pos⟩, rfl⟩
      have hbnd := hb hrange
      rw [hcoe] at hbnd
      exact hbnd
    exact le_of_tendsto hLimP hev

/--
**Paper `rmk:cxty`, third bullet — sup-formula at `m = 0`**
(`Source/FGU-monotone_revised.tex`, line 437): under `(onH.monotone)`
and `(a:Hat0)`, for almost every `x ∈ 𝕋^d` and every `p ∈ ℝ^d`,

  `H̃(x, p, 0) = sup_{m > 0} H(x, p, m)`

(where the sup is taken in `WithTop ℝ`).
-/
theorem H_at_zero_eq_sup
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmono : HypothesisMonotone H DpH) (hHat0 : HypothesisHat0 H) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p : Fin d → ℝ,
        H_at_zero H x p
          = sSup (Set.range (fun m : {m : ℝ // 0 < m} => Hext H x p m.1)) := by
  filter_upwards [isLUB_Hext_pos hmono hHat0] with x hx p
  -- `IsLUB.csSup_eq` requires nonemptiness of the range.
  have hne : (Set.range (fun m : {m : ℝ // 0 < m} => Hext H x p m.1)).Nonempty :=
    ⟨Hext H x p 1, ⟨⟨1, one_pos⟩, rfl⟩⟩
  exact ((hx p).csSup_eq hne).symm

/--
**Paper `rmk:cxty`, third bullet — lower semicontinuity of
`p ↦ H̃(x, p, 0)`** (`Source/FGU-monotone_revised.tex`, line 438): under
`(onH.monotone)` and `(a:Hat0)`, for almost every `x ∈ 𝕋^d` the map
`p ↦ H̃(x, p, 0)` is lower semicontinuous on `ℝ^d`.

Proof. By `H_at_zero_eq_sup`, the value at every `p` is the (extended)
supremum of the family `{p ↦ H(x, p, m)}_{m > 0}`. Each member of
the family is continuous in `p` (consequence of the joint continuity in
`(p, m)` from `(a:regularityH)` together with continuity of the
`WithTop`-coercion). Lower semicontinuity is then preserved by
extended-valued suprema, giving the claim.
-/
theorem lsc_H_at_zero
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hmono : HypothesisMonotone H DpH) (hHat0 : HypothesisHat0 H) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      LowerSemicontinuous (fun p : Fin d → ℝ => H_at_zero H x p) := by
  filter_upwards [H_at_zero_eq_sup hmono hHat0,
    hmono.toRegularityH.continuous_H_pm] with x hSupX hContX
  -- Rewrite `H_at_zero` pointwise as a supremum, then use the
  -- lsc-of-sup pattern.
  -- For `m₀ : {m // 0 < m}`, the section `p ↦ Hext H x p m₀.1` is
  -- continuous: it is the WithTop coercion of `p ↦ H(x, p, m₀.1)`,
  -- whose continuity in `p` follows from joint continuity in `(p, m)`
  -- on `{0 < m}`.
  -- Section continuity in `p` (real-valued).
  have hCtsR :
      ∀ m₀ : {m : ℝ // 0 < m},
        Continuous (fun p : Fin d → ℝ => H x p m₀.1) := by
    intro m₀
    refine continuous_iff_continuousAt.mpr (fun p => ?_)
    have hOpen : IsOpen ({pm : (Fin d → ℝ) × ℝ | 0 < pm.2}) :=
      isOpen_lt continuous_const continuous_snd
    have hmem : ((p, m₀.1) : (Fin d → ℝ) × ℝ) ∈ {pm | 0 < pm.2} := m₀.2
    have hCAt :
        ContinuousAt (fun pm : (Fin d → ℝ) × ℝ => H x pm.1 pm.2) (p, m₀.1) :=
      hContX.continuousAt (hOpen.mem_nhds hmem)
    -- Compose with the pair-with-constant map `q ↦ (q, m₀.1)`.
    have hId : ContinuousAt (id : (Fin d → ℝ) → (Fin d → ℝ)) p :=
      continuousAt_id
    have hConst : ContinuousAt (fun _ : Fin d → ℝ => m₀.1) p :=
      continuousAt_const
    exact hCAt.comp₂ hId hConst
  -- The pointwise iSup of the WithTop-coerced sections is lsc.
  -- Proved by hand: at each `p₀` and each `y < f p₀`, witness an `m₀`
  -- with `y < (H x p₀ m₀.1 : WithTop ℝ)`, then propagate the strict
  -- inequality by continuity of the section in `p`.
  have hLsc : LowerSemicontinuous
      (fun p : Fin d → ℝ =>
        ⨆ m₀ : {m : ℝ // 0 < m}, ((H x p m₀.1 : ℝ) : WithTop ℝ)) := by
    intro p₀ y hy
    -- `y < ⨆ m₀, …` over a (nonempty, bounded-above-by-⊤) family in
    -- `WithTop ℝ` exhibits a witness `m₀` with the strict inequality.
    have hbdd :
        BddAbove (Set.range
          (fun m₀ : {m : ℝ // 0 < m} => ((H x p₀ m₀.1 : ℝ) : WithTop ℝ))) :=
      OrderTop.bddAbove _
    have hExists : ∃ m₀ : {m : ℝ // 0 < m},
        y < ((H x p₀ m₀.1 : ℝ) : WithTop ℝ) := by
      by_contra hAll
      have hAll' : ∀ m₀ : {m : ℝ // 0 < m},
          ((H x p₀ m₀.1 : ℝ) : WithTop ℝ) ≤ y := by
        intro m₀
        exact not_lt.mp (fun h => hAll ⟨m₀, h⟩)
      have hUB : (⨆ m₀ : {m : ℝ // 0 < m},
          ((H x p₀ m₀.1 : ℝ) : WithTop ℝ)) ≤ y := ciSup_le hAll'
      exact (lt_irrefl _) (lt_of_lt_of_le hy hUB)
    obtain ⟨m₀, hWitness⟩ := hExists
    -- Continuity of the section gives an eventual strict inequality.
    have hCtsCoe :
        Continuous (fun p : Fin d → ℝ => ((H x p m₀.1 : ℝ) : WithTop ℝ)) :=
      WithTop.continuous_coe.comp (hCtsR m₀)
    have hLscSection :
        LowerSemicontinuousAt
          (fun p : Fin d → ℝ => ((H x p m₀.1 : ℝ) : WithTop ℝ)) p₀ :=
      hCtsCoe.lowerSemicontinuous p₀
    have hev := hLscSection y hWitness
    -- Lift the eventual section-inequality to the iSup.
    filter_upwards [hev] with p' hp'
    refine lt_of_lt_of_le hp' ?_
    have hbdd' :
        BddAbove (Set.range
          (fun m₀ : {m : ℝ // 0 < m} => ((H x p' m₀.1 : ℝ) : WithTop ℝ))) :=
      OrderTop.bddAbove _
    exact le_ciSup hbdd' m₀
  -- Reconcile `H_at_zero` (= `sSup` of range) with this `iSup`.
  have hrwP : ∀ q : Fin d → ℝ,
      H_at_zero H x q
        = ⨆ m₀ : {m : ℝ // 0 < m}, ((H x q m₀.1 : ℝ) : WithTop ℝ) := by
    intro q
    have h1 : H_at_zero H x q =
        sSup (Set.range (fun m₀ : {m : ℝ // 0 < m} => Hext H x q m₀.1)) :=
      hSupX q
    have h2 : ∀ m₀ : {m : ℝ // 0 < m},
        Hext H x q m₀.1 = ((H x q m₀.1 : ℝ) : WithTop ℝ) := fun m₀ =>
      Hext_of_pos H x q m₀.2
    have h3 :
        (fun m₀ : {m : ℝ // 0 < m} => Hext H x q m₀.1)
          = (fun m₀ : {m : ℝ // 0 < m} => ((H x q m₀.1 : ℝ) : WithTop ℝ)) := by
      funext m₀; exact h2 m₀
    rw [h1, h3, sSup_range]
  -- Pull the sup-form through `LowerSemicontinuous`.
  intro p₀ y hy
  -- `hy` is morally `y < H_at_zero H x p₀`; rewrite via the sup-form.
  have hyf : y < H_at_zero H x p₀ := hy
  have hy' : y < ⨆ m₀ : {m : ℝ // 0 < m}, ((H x p₀ m₀.1 : ℝ) : WithTop ℝ) := by
    rw [hrwP p₀] at hyf; exact hyf
  have hev := hLsc p₀ y hy'
  filter_upwards [hev] with p' hp'
  -- Convert back to `H_at_zero` form.
  have hyf' : y < H_at_zero H x p' := by
    rw [hrwP p']; exact hp'
  exact hyf'

/--
**Paper `rmk:cxty`, third bullet — convexity of `p ↦ H̃(x, p, 0)`**
(`Source/FGU-monotone_revised.tex`, line 438), conditional form.

In the paper, convexity of `p ↦ H̃(x, p, 0)` follows from convexity of
each section `p ↦ H(x, p, m)` for `m > 0`, which is itself a
consequence of `(onH.monotone)` once one identifies `D_pH` with `∂_p H`.
Our project does not currently bundle that identification, so we take
both section-convexity and finiteness of the supremum as external
hypotheses. The conclusion is convexity of the real-valued
representative `p ↦ ⨆ m₀ : {m // 0 < m}, H x p m₀.1`, which under
`hBdd` matches `H̃(x, p, 0)` via the WithTop coercion (cf.
`H_at_zero_eq_sup`).

* `hConvexEachM` — convexity of each section `p ↦ H(x, p, m)` for
  `m > 0`.
* `hBdd` — pointwise boundedness of the family
  `{m ↦ H(x, p, m) | m > 0}`, ensuring the supremum is finite.

The `hHat0` hypothesis is not technically required for this
conclusion — given `hBdd` and `hConvexEachM`, the real-valued sup is
already convex. We keep `hHat0` in the signature for symmetry with
the rest of `rmk:cxty`'s third bullet, and to mirror the paper.
-/
theorem convex_H_at_zero
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {DpH : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (_hmono : HypothesisMonotone H DpH) (_hHat0 : HypothesisHat0 H)
    (hConvexEachM :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ m : ℝ, 0 < m → ConvexOn ℝ Set.univ (fun p : Fin d → ℝ => H x p m))
    (hBdd :
      ∀ᵐ x ∂(volume.restrict (UnitCube d)),
        ∀ p : Fin d → ℝ,
          BddAbove (Set.range
            (fun m₀ : {m : ℝ // 0 < m} => H x p m₀.1))) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ConvexOn ℝ (Set.univ : Set (Fin d → ℝ))
        (fun p : Fin d → ℝ => ⨆ m₀ : {m : ℝ // 0 < m}, H x p m₀.1) := by
  filter_upwards [hConvexEachM, hBdd] with x hConvX hBddX
  refine ⟨convex_univ, ?_⟩
  intro p₁ _ p₂ _ a b ha hb hab
  -- Use `ciSup_le` against the BddAbove hypothesis at the midpoint.
  refine ciSup_le ?_
  intro m₀
  have hConvM : ConvexOn ℝ Set.univ (fun p : Fin d → ℝ => H x p m₀.1) :=
    hConvX m₀.1 m₀.2
  have hineq :
      H x (a • p₁ + b • p₂) m₀.1
        ≤ a * H x p₁ m₀.1 + b * H x p₂ m₀.1 := by
    have hMid := hConvM.2 (Set.mem_univ p₁) (Set.mem_univ p₂) ha hb hab
    simpa [smul_eq_mul] using hMid
  have hp1 : H x p₁ m₀.1 ≤ ⨆ m₀ : {m : ℝ // 0 < m}, H x p₁ m₀.1 :=
    le_ciSup (hBddX p₁) m₀
  have hp2 : H x p₂ m₀.1 ≤ ⨆ m₀ : {m : ℝ // 0 < m}, H x p₂ m₀.1 :=
    le_ciSup (hBddX p₂) m₀
  have hcomb : a * H x p₁ m₀.1 + b * H x p₂ m₀.1
      ≤ a * (⨆ m₀ : {m : ℝ // 0 < m}, H x p₁ m₀.1)
        + b * (⨆ m₀ : {m : ℝ // 0 < m}, H x p₂ m₀.1) := by
    have ha1 : a * H x p₁ m₀.1
        ≤ a * (⨆ m₀ : {m : ℝ // 0 < m}, H x p₁ m₀.1) :=
      mul_le_mul_of_nonneg_left hp1 ha
    have hb1 : b * H x p₂ m₀.1
        ≤ b * (⨆ m₀ : {m : ℝ // 0 < m}, H x p₂ m₀.1) :=
      mul_le_mul_of_nonneg_left hp2 hb
    linarith
  exact hineq.trans hcomb

end SupFormula

/-! ### Coherence checks: the trivial Hamiltonian -/

/-- The trivially-zero Hamiltonian is antitone in `m`. -/
example (d : ℕ) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ p : Fin d → ℝ,
        AntitoneOn (fun m : ℝ => (fun (_ : Fin d → ℝ) (_ : Fin d → ℝ) (_ : ℝ) => (0 : ℝ)) x p m)
          (Set.Ioi (0 : ℝ)) := by
  refine Filter.Eventually.of_forall ?_
  intro _ _ _ _ _ _ _
  exact le_rfl

/-- The trivially-zero `D_pH` is monotone in `p`. -/
example (d : ℕ) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      ∀ m : ℝ, 0 < m → ∀ p₁ p₂ : Fin d → ℝ,
        (0 : ℝ) ≤
          ((fun (_ : Fin d → ℝ) (_ : Fin d → ℝ) (_ : ℝ) => (0 : Fin d → ℝ)) x p₁ m -
              (fun (_ : Fin d → ℝ) (_ : Fin d → ℝ) (_ : ℝ) => (0 : Fin d → ℝ)) x p₂ m)
            ⬝ (p₁ - p₂) := by
  refine Filter.Eventually.of_forall ?_
  intro _ _ _ _ _
  simp

end Hamiltonian
end StationaryMFG
