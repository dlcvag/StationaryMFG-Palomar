module

public import StationaryMFG.Basic
public import StationaryMFG.Periodic.Reflexive

@[expose] public section

/-!
# Weak topology infrastructure for monotone-operator existence

This file collects three weak-topology facts consumed by
`paper:thm:monotone.abstract-weak` (cf. `docs/MONOTONE_PLAN.md` §1):

1. `isCompact_closure_weak_of_isBounded_reflexive` — for `X` a reflexive
   real Banach space, the weak closure of any norm-bounded set is weakly
   compact (Banach–Alaoglu transferred to `X` through reflexivity).

2. `isCompact_compactCoreW` — the "compact weak core"
   `compactCoreW R K := closure (toWeakSpace ℝ X '' (Metric.closedBall 0 R ∩ closure K))`
   is weakly compact; this is the convex closed bounded weak core extracted
   from the variational-inequality data `(R, K)`.

3. `isClosed_viHalfspaceW` — for any frozen `v : X` and bounded linear
   functional `Av : X →L[ℝ] ℝ`, the affine half-space
   `{u | 0 ≤ Av (v - u)}` is closed in the weak topology of `X`.

The reflexivity hypothesis is supplied via the project-local predicate
`StationaryMFG.Periodic.IsReflexiveNormedSpace` from
`StationaryMFG/Periodic/Reflexive.lean` (surjectivity of the canonical
double-dual inclusion). The third statement does not need reflexivity.

## References

- Mathlib: `NormedSpace.isCompact_closure_of_isBounded`
  (`Analysis/Normed/Module/DoubleDual.lean`), the Banach–Alaoglu transfer.
- Mathlib: `Convex.toWeakSpace_closure`
  (`Analysis/LocallyConvex/WeakSpace.lean`), Mazur's theorem (closures of
  convex sets coincide in norm and weak topologies).
- Mathlib: `WeakBilin.eval_continuous` for weak continuity of duality
  evaluation.
-/

noncomputable section

namespace StationaryMFG
namespace Monotone

open MeasureTheory NormedSpace
open scoped Topology

open StationaryMFG.Periodic (IsReflexiveNormedSpace)

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ## Surjectivity of the weak-topology double-dual inclusion -/

/-- If the strong-topology double-dual inclusion `X → X**` is surjective,
so is the weak-topology version `WeakSpace ℝ X → WeakDual ℝ (StrongDual ℝ X)`.

The latter has underlying linear map
`(toWeakSpace ℝ X).arrowCongr StrongDual.toWeakDual (inclusionInDoubleDual ℝ X)`,
which is surjective whenever `inclusionInDoubleDual` is, since it is the
composition of the strong inclusion with two linear isomorphisms. -/
theorem inclusionInDoubleDualWeak_surjective_of_reflexive
    (hX : IsReflexiveNormedSpace X) :
    Function.Surjective (NormedSpace.inclusionInDoubleDualWeak ℝ X) := by
  intro Φ
  -- `Φ : WeakDual ℝ (StrongDual ℝ X)`. Convert to `StrongDual ℝ (StrongDual ℝ X)`
  -- via the linear equivalence `WeakDual.toStrongDual`.
  let Ψ : StrongDual ℝ (StrongDual ℝ X) := WeakDual.toStrongDual Φ
  obtain ⟨x, hx⟩ := hX Ψ
  refine ⟨x, ?_⟩
  -- It suffices to check equality of the two `WeakDual` elements pointwise.
  apply ContinuousLinearMap.ext
  intro f
  -- The equality reduces to `f x = Φ f`.
  -- From `hx : inclusionInDoubleDual ℝ X x = Ψ`, applying both sides at `f`:
  --   `(inclusionInDoubleDual ℝ X x) f = Ψ f`, i.e. `f x = Ψ f`.
  -- And `Ψ f = WeakDual.toStrongDual Φ f = Φ f` by definition.
  have h1 : f x = Ψ f := by
    have := congr_arg (fun g : StrongDual ℝ (StrongDual ℝ X) => g f) hx
    simpa using this
  have h2 : Ψ f = Φ f := rfl
  -- Now goal `(inclusionInDoubleDualWeak ℝ X x) f = Φ f` is `f x = Φ f`.
  change f x = Φ f
  rw [h1, h2]

/-! ## Weak compactness of bounded sets in a reflexive Banach space -/

/-- **Banach–Alaoglu via reflexivity (closure form).** For a reflexive
real normed space `X` and any norm-bounded subset `S ⊆ X`, the weak closure
of `S` is weakly compact, i.e.
`IsCompact (closure (toWeakSpace ℝ X '' S))` in `WeakSpace ℝ X`.

This is the form actually delivered by Mathlib's
`NormedSpace.isCompact_closure_of_isBounded`: reflexivity makes the
side-condition `closure (… '' S) ⊆ Set.range (inclusionInDoubleDualWeak …)`
trivial, since the range is the whole codomain. -/
theorem isCompact_closure_weak_of_isBounded_reflexive
    (hX : IsReflexiveNormedSpace X) {S : Set X} (hS : Bornology.IsBounded S) :
    IsCompact (closure ((toWeakSpace ℝ X) '' S)) := by
  -- Apply Mathlib's `isCompact_closure_of_isBounded`.
  refine NormedSpace.isCompact_closure_of_isBounded
    (𝕜 := ℝ) (X := X) ((toWeakSpace ℝ X) '' S) ?_ ?_
  · -- `(toWeakSpace ℝ X) ⁻¹' (toWeakSpace ℝ X '' S) = S` (toWeakSpace is bijective).
    have hinj : Function.Injective (toWeakSpace ℝ X) := (toWeakSpace ℝ X).injective
    rw [Set.preimage_image_eq _ hinj]
    exact hS
  · -- The range condition is automatic by reflexivity.
    have hsurj := inclusionInDoubleDualWeak_surjective_of_reflexive hX
    rw [hsurj.range_eq]
    exact Set.subset_univ _

/-- **Mazur + Banach–Alaoglu.** For a reflexive real normed space `X`,
every norm-closed, convex, bounded subset is weakly compact (i.e. compact
in `WeakSpace ℝ X`).

Mazur's theorem gives `closure_of (T '' S) = T '' (closure S)` for `T =
toWeakSpace ℝ X` and convex `S`, so when `S` is also closed (in norm) the
weak closure of `T '' S` equals `T '' S`, and we apply
`isCompact_closure_weak_of_isBounded_reflexive`. -/
theorem isCompact_weak_of_closed_convex_bounded_reflexive
    (hX : IsReflexiveNormedSpace X) {S : Set X}
    (hS_closed : IsClosed S) (hS_conv : Convex ℝ S)
    (hS_bdd : Bornology.IsBounded S) :
    IsCompact ((toWeakSpace ℝ X) '' S) := by
  have hcl_compact :
      IsCompact (closure ((toWeakSpace ℝ X) '' S)) :=
    isCompact_closure_weak_of_isBounded_reflexive hX hS_bdd
  -- Mazur: `closure (toWeakSpace ℝ X '' S) = toWeakSpace ℝ X '' closure S`.
  have hMazur : (toWeakSpace ℝ X) '' closure S =
      closure ((toWeakSpace ℝ X) '' S) :=
    hS_conv.toWeakSpace_closure ℝ
  -- Since `S` is closed, `closure S = S`.
  have hclos : closure S = S := hS_closed.closure_eq
  rw [hclos] at hMazur
  rw [hMazur]
  exact hcl_compact

/-! ## Compact weak core of a bounded subset

The "compact weak core" of `(R, K)` is the weak closure of the norm-bounded
piece `Metric.closedBall 0 R ∩ closure K`. It is the natural compact set on
which the variational-inequality fixed-point argument runs. -/

/-- The compact weak core associated with radius `R ≥ 0` and a candidate
domain `K ⊆ X`: the weak closure of `Metric.closedBall 0 R ∩ closure K`. -/
def compactCoreW (R : ℝ) (K : Set X) : Set (WeakSpace ℝ X) :=
  closure ((toWeakSpace ℝ X) '' (Metric.closedBall (0 : X) R ∩ closure K))

/-- The compact weak core is weakly compact, for any `R` and any set `K`,
provided `X` is reflexive. -/
theorem isCompact_compactCoreW (hX : IsReflexiveNormedSpace X)
    (R : ℝ) (K : Set X) : IsCompact (compactCoreW R K : Set (WeakSpace ℝ X)) := by
  -- The seed set is bounded as a subset of the closed ball of radius `R`.
  have hbdd : Bornology.IsBounded
      (Metric.closedBall (0 : X) R ∩ closure K) :=
    (Metric.isBounded_closedBall.subset Set.inter_subset_left)
  exact isCompact_closure_weak_of_isBounded_reflexive (X := X) hX hbdd

/-! ## Weak closedness of variational-inequality half-spaces -/

/-- The affine half-space `{u | 0 ≤ Av (v - u)}` is closed in the weak
topology of `X`, for any continuous linear functional `Av : X →L[ℝ] ℝ` and
any frozen `v : X`.

The map `u : WeakSpace ℝ X ↦ Av u` is weakly continuous by
`WeakBilin.eval_continuous`, hence so is `u ↦ Av (v - u) = Av v - Av u`. The
half-space is then the preimage of the closed set `[0, ∞)` under a
continuous map. -/
theorem isClosed_viHalfspaceW (Av : X →L[ℝ] ℝ) (v : X) :
    IsClosed
      ({u : WeakSpace ℝ X | 0 ≤ Av (v - (toWeakSpace ℝ X).symm u)}) := by
  -- The evaluation `u ↦ Av u` is weakly continuous.
  have hAv_cont : Continuous fun u : WeakSpace ℝ X => Av ((toWeakSpace ℝ X).symm u) := by
    -- Unfold: this is exactly `WeakBilin.eval_continuous` applied to `Av`
    -- viewed as a member of `StrongDual ℝ X`.
    -- `(topDualPairing ℝ X).flip x Av = Av x`; the weak topology on `X`
    -- is induced by all such evaluations, so each is continuous.
    have := WeakBilin.eval_continuous (topDualPairing ℝ X).flip Av
    -- `WeakSpace ℝ X = WeakBilin (topDualPairing ℝ X).flip` definitionally.
    -- The function `fun x : WeakBilin _ => (topDualPairing ℝ X).flip x Av`
    -- is `fun x => Av x`. Through `(toWeakSpace ℝ X).symm` we have the
    -- definitional identity since `toWeakSpace = LinearEquiv.refl`.
    exact this
  -- Hence `u ↦ Av v - Av u = Av (v - u)` is continuous.
  have hsub_cont : Continuous fun u : WeakSpace ℝ X =>
      Av (v - (toWeakSpace ℝ X).symm u) := by
    have hconst : Continuous fun _ : WeakSpace ℝ X => Av v := continuous_const
    have hdiff : Continuous fun u : WeakSpace ℝ X => Av v - Av ((toWeakSpace ℝ X).symm u) :=
      hconst.sub hAv_cont
    -- `Av (v - u) = Av v - Av u` by `map_sub`.
    convert hdiff using 1
    funext u
    rw [map_sub]
  -- The half-space is `{u | 0 ≤ f u}` where `f u = Av (v - u)`; this is
  -- the preimage of `[0, ∞)`, a closed set.
  exact isClosed_le continuous_const hsub_cont

/-- Variant of `isClosed_viHalfspaceW` phrased directly in `X` (not in
`WeakSpace ℝ X`): the half-space is closed when `X` is given the *weak*
topology. Useful for clients that prefer to write the half-space in `X`
and then transport it via `toWeakSpace`. -/
theorem isClosed_viHalfspaceW' (Av : X →L[ℝ] ℝ) (v : X) :
    IsClosed
      ((toWeakSpace ℝ X) '' ({u : X | 0 ≤ Av (v - u)})) := by
  -- The image equals `{u : WeakSpace ℝ X | 0 ≤ Av (v - (toWeakSpace ℝ X).symm u)}`.
  -- Both `toWeakSpace` and its inverse act as the identity on the
  -- underlying set; this is a definitional rewriting.
  have hset :
      (toWeakSpace ℝ X) '' ({u : X | 0 ≤ Av (v - u)}) =
        {u : WeakSpace ℝ X | 0 ≤ Av (v - (toWeakSpace ℝ X).symm u)} := by
    ext u
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hu
      refine ⟨(toWeakSpace ℝ X).symm u, hu, ?_⟩
      simp
  rw [hset]
  exact isClosed_viHalfspaceW (X := X) Av v

/-! ## Sanity-check examples -/

/-- The half-space defined by the zero functional contains every point and
is therefore (trivially) closed. -/
example (v : X) :
    IsClosed
      ({u : WeakSpace ℝ X |
        0 ≤ (0 : X →L[ℝ] ℝ) (v - (toWeakSpace ℝ X).symm u)}) :=
  isClosed_viHalfspaceW (X := X) (0 : X →L[ℝ] ℝ) v

/-- The empty set is bounded, hence its weak closure is weakly compact in
any reflexive space. -/
example (hX : IsReflexiveNormedSpace X) :
    IsCompact (closure ((toWeakSpace ℝ X) '' (∅ : Set X))) :=
  isCompact_closure_weak_of_isBounded_reflexive hX Bornology.isBounded_empty

end Monotone
end StationaryMFG
