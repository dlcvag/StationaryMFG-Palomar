module

public import StationaryMFG.Periodic.WeakCompactness
public import StationaryMFG.Periodic.Reflexive

@[expose] public section

/-!
# Weak compactness extraction for `(m_ε, u_ε)` (paper `eq:compactness`)

This module formalizes the paper's compactness step at line 1292 of
`Source/FGU-monotone_revised.tex`, equation `eq:compactness`.

## Paper restatement

Under the ε-uniform a priori bound of `thm:apriori-simple.power.growth`, the
sequence `(m_{ε_k}, u_{ε_k})_k` is bounded in the reflexive product space
`L^{β̄}_per × W^{1,γ̄}_per`. Sequential weak compactness in a reflexive Banach
space (`weakSeqCompact_of_bounded_reflexive`, dependency
`infra:P4-weak-seq-compact-reflexive`) extracts a weakly convergent
subsequence
```
(m_{ε_k}, u_{ε_k}) ⇀ (m, u).
```
The constraint `m ≥ 0 a.e.` survives the limit because the set
`{m ∈ L^{β̄} | m ≥ 0 a.e.}` is a closed convex cone in the norm topology, and
hence (by the Hahn–Banach theorem) sequentially weakly closed; we package
this preservation as a hypothesis `IsSeqClosed S₁` on the constraint set so
the extraction lemma is reusable at every calibration of `p` (not just the
`p = 2` Hilbert calibration where the project currently has reflexivity in
hand).

## Main results

* `exists_weak_cluster_point` — the abstract extraction statement: a bounded
  sequence in a reflexive real normed space, all of whose terms lie in a
  sequentially weakly closed set `S`, admits a weakly convergent subsequence
  with limit again in `S`.
* `exists_weak_cluster_point_pair` — pair-shaped specialisation: when the
  ambient space is a product `Y × Z`, the first-component constraint set
  (encoding `m ≥ 0`) needs only be sequentially weakly closed in
  `WeakSpace ℝ Y`.

## References

* Paper: `Source/FGU-monotone_revised.tex`, line 1292, equation
  `eq:compactness`.
* Project dependencies:
  - `StationaryMFG.Periodic.WeakCompactness.weakSeqCompact_of_bounded_reflexive`
    (sequential Banach–Alaoglu / Eberlein–Smulian transfer).
  - `StationaryMFG.Periodic.Reflexive.IsReflexiveNormedSpace` (project-local
    reflexivity predicate).
-/

noncomputable section

namespace StationaryMFG
namespace Theorems
namespace SimplePower

open MeasureTheory NormedSpace
open Bornology Filter Topology
open StationaryMFG.Periodic
  (IsReflexiveNormedSpace weakSeqCompact_of_bounded_reflexive
    lpSobolev_product_isReflexive_two SobolevPerLp UnitCube)

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ## Abstract weak-cluster-point extraction -/

/-- **Weak cluster-point extraction with a sequentially-weakly-closed
constraint set.**

Given:
* a reflexive real normed space `X` with separable strong dual,
* a sequence `z_n : ℕ → X` whose range is norm-bounded,
* a sequentially weakly closed set
  `S : Set (WeakSpace ℝ X)` such that `(toWeakSpace ℝ X) (z_n n) ∈ S` for every `n`,

there exists a strictly increasing index function `φ` and a weak limit `z ∈ S`
with `(toWeakSpace ℝ X) (z_n (φ k)) → z` in `WeakSpace ℝ X`.

This is the abstract form of paper line 1292 (`eq:compactness`): the
constraint `m ≥ 0` survives under weak convergence because the cone
`{m ≥ 0 a.e.}` is sequentially weakly closed (a closed convex set is weakly
closed by Hahn–Banach). We accept that closedness as a hypothesis; concrete
applications in the paper supply it via the convex-cone argument. -/
theorem exists_weak_cluster_point
    [TopologicalSpace.SeparableSpace (StrongDual ℝ X)]
    (hX : IsReflexiveNormedSpace X)
    (z_n : ℕ → X) (hb : IsBounded (Set.range z_n))
    {S : Set (WeakSpace ℝ X)} (hS : IsSeqClosed S)
    (hmem : ∀ n, (toWeakSpace ℝ X) (z_n n) ∈ S) :
    ∃ (φ : ℕ → ℕ) (z : WeakSpace ℝ X),
      StrictMono φ ∧ z ∈ S ∧
        Tendsto (fun k => (toWeakSpace ℝ X) (z_n (φ k))) atTop (𝓝 z) := by
  obtain ⟨φ, hφ_mono, z, hz⟩ :=
    weakSeqCompact_of_bounded_reflexive hX z_n hb
  refine ⟨φ, z, hφ_mono, ?_, hz⟩
  -- The subsequence `(toWeakSpace ℝ X) (z_n (φ k))` lies in `S` for every `k`,
  -- and converges to `z`; sequential closedness gives `z ∈ S`.
  exact hS (fun k => hmem (φ k)) hz

/-! ## Pair-shaped specialisation

In the paper, the ambient reflexive space is the *product*
`L^{β̄}_per × W^{1,γ̄}_per`, and the cone constraint `m ≥ 0 a.e.` only
involves the first factor. The pair-shaped lemma below isolates that factor:
the user supplies a sequentially weakly closed subset `S₁ ⊆ WeakSpace ℝ Y`
controlling the `m_n` component, and we automatically lift it to a
sequentially weakly closed subset of `WeakSpace ℝ (Y × Z)` via the projection
`Prod.fst`.
-/

variable {Y Z : Type*}
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The first-coordinate projection `WeakSpace ℝ (Y × Z) → WeakSpace ℝ Y`,
defined as `WeakSpace.map (ContinuousLinearMap.fst ℝ Y Z)`. As `WeakSpace ℝ E`
is a type synonym for `E` carrying the weak topology, this is the underlying
projection `Prod.fst` viewed between weak spaces. -/
def weakProdFst :
    WeakSpace ℝ (Y × Z) → WeakSpace ℝ Y :=
  WeakSpace.map (ContinuousLinearMap.fst ℝ Y Z)

/-- Continuity of `weakProdFst` between weak topologies; immediate from
`WeakSpace.map` being a continuous linear map. -/
lemma continuous_weakProdFst :
    Continuous (weakProdFst (Y := Y) (Z := Z)) :=
  (WeakSpace.map (ContinuousLinearMap.fst ℝ Y Z)).continuous

/-- Pull back a sequentially closed subset of `WeakSpace ℝ Y` along the
first-coordinate projection to a sequentially closed subset of
`WeakSpace ℝ (Y × Z)`. -/
lemma isSeqClosed_preimage_weakProdFst
    {S₁ : Set (WeakSpace ℝ Y)} (hS₁ : IsSeqClosed S₁) :
    IsSeqClosed ((weakProdFst (Y := Y) (Z := Z)) ⁻¹' S₁) := by
  intro w wlim hmem hconv
  -- `weakProdFst` is continuous, so `weakProdFst ∘ w → weakProdFst wlim`.
  have hcont : Continuous (weakProdFst (Y := Y) (Z := Z)) :=
    continuous_weakProdFst
  have htend : Tendsto (fun n => weakProdFst (w n)) atTop
      (𝓝 (weakProdFst wlim)) := hcont.tendsto wlim |>.comp hconv
  exact hS₁ (fun n => hmem n) htend

/-- **Pair-shaped weak cluster-point extraction.**

Bounded sequence `(m_n, u_n)` in a reflexive product `Y × Z` (with separable
strong dual), with the first coordinate trapped in a sequentially weakly
closed set `S₁ ⊆ WeakSpace ℝ Y`: extract a weakly convergent subsequence
whose first-coordinate limit lies in `S₁`. -/
theorem exists_weak_cluster_point_pair
    [TopologicalSpace.SeparableSpace (StrongDual ℝ (Y × Z))]
    (hYZ : IsReflexiveNormedSpace (Y × Z))
    (z_n : ℕ → Y × Z) (hb : IsBounded (Set.range z_n))
    {S₁ : Set (WeakSpace ℝ Y)} (hS₁ : IsSeqClosed S₁)
    (hmem₁ : ∀ n, weakProdFst ((toWeakSpace ℝ (Y × Z)) (z_n n)) ∈ S₁) :
    ∃ (φ : ℕ → ℕ) (z : WeakSpace ℝ (Y × Z)),
      StrictMono φ ∧ weakProdFst z ∈ S₁ ∧
        Tendsto (fun k => (toWeakSpace ℝ (Y × Z)) (z_n (φ k))) atTop (𝓝 z) := by
  -- Lift `S₁` to a sequentially weakly closed subset of the product, and
  -- apply `exists_weak_cluster_point`.
  set S : Set (WeakSpace ℝ (Y × Z)) :=
    (weakProdFst (Y := Y) (Z := Z)) ⁻¹' S₁ with hS_def
  have hS_closed : IsSeqClosed S :=
    isSeqClosed_preimage_weakProdFst hS₁
  have hmem : ∀ n, (toWeakSpace ℝ (Y × Z)) (z_n n) ∈ S := fun n => hmem₁ n
  obtain ⟨φ, z, hmono, hzS, hzlim⟩ :=
    exists_weak_cluster_point hYZ z_n hb hS_closed hmem
  exact ⟨φ, z, hmono, hzS, hzlim⟩

/-! ## Sanity-check examples

The first example is a generic restatement; the second targets the paper's
calibration `Y = Lp ℝ 2 (volume.restrict (UnitCube d))`,
`Z = SobolevPerLp 1 2 d`, where reflexivity is supplied by
`lpSobolev_product_isReflexive_two`.
-/

/-- Generic restatement of `exists_weak_cluster_point`. -/
example {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [TopologicalSpace.SeparableSpace (StrongDual ℝ X)]
    (hX : IsReflexiveNormedSpace X)
    (z_n : ℕ → X) (hb : IsBounded (Set.range z_n))
    {S : Set (WeakSpace ℝ X)} (hS : IsSeqClosed S)
    (hmem : ∀ n, (toWeakSpace ℝ X) (z_n n) ∈ S) :
    ∃ (φ : ℕ → ℕ) (z : WeakSpace ℝ X),
      StrictMono φ ∧ z ∈ S ∧
        Tendsto (fun k => (toWeakSpace ℝ X) (z_n (φ k))) atTop (𝓝 z) :=
  exists_weak_cluster_point hX z_n hb hS hmem

/-- **Paper compactness target.** Given separability of the strong dual of
`L^2_per × W^{1,2}_per`, every bounded sequence `(m_n, u_n)` whose
first-coordinate weak images stay in a sequentially weakly closed set
admits a weakly convergent subsequence with first-coordinate limit in the
constraint set. This is the structural shape of paper `eq:compactness`. -/
example (d : ℕ)
    [TopologicalSpace.SeparableSpace
      (StrongDual ℝ
        ((MeasureTheory.Lp ℝ 2
            (MeasureTheory.Measure.restrict (volume) (UnitCube d))) ×
          SobolevPerLp 1 2 d))]
    (z_n : ℕ →
      ((MeasureTheory.Lp ℝ 2
          (MeasureTheory.Measure.restrict (volume) (UnitCube d))) ×
        SobolevPerLp 1 2 d))
    (hb : IsBounded (Set.range z_n))
    {S₁ : Set (WeakSpace ℝ
      (MeasureTheory.Lp ℝ 2
        (MeasureTheory.Measure.restrict (volume) (UnitCube d))))}
    (hS₁ : IsSeqClosed S₁)
    (hmem₁ : ∀ n,
      weakProdFst ((toWeakSpace ℝ _) (z_n n)) ∈ S₁) :
    ∃ (φ : ℕ → ℕ) (z : WeakSpace ℝ _),
      StrictMono φ ∧ weakProdFst z ∈ S₁ ∧
        Tendsto (fun k => (toWeakSpace ℝ _) (z_n (φ k))) atTop (𝓝 z) :=
  exists_weak_cluster_point_pair
    (lpSobolev_product_isReflexive_two (d := d)) z_n hb hS₁ hmem₁

end SimplePower
end Theorems
end StationaryMFG
