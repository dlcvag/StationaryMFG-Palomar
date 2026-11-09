module

public import StationaryMFG.Hamiltonian.FluxExtension
public import StationaryMFG.Hamiltonian.Differentiability

@[expose] public section

/-!
# Local boundary facts for the paper's congestion argument

The paper allows H(p,0)=+∞ and a nonzero limiting flux J(p,0).
The finite-value and zero-flux facts needed at an actual solution must
therefore be proved locally, rather than imposed for every momentum.
These local facts support the corrected paper-facing existence theorem.
-/

namespace StationaryMFG.Theorems.Congestion.Paper

open MeasureTheory Filter Set Topology
open StationaryMFG.Hamiltonian StationaryMFG.Periodic
open scoped StationaryMFG.Hamiltonian

variable {d : ℕ}

/-- Taking a positive-mass limit preserves the general limiting flux.
In particular the limit is J(p,0), not the raw product 0 • DpH(p,0). -/
theorem flux_tendsto_of_positive
    {ι : Type*} {l : Filter ι}
    {DpH J : (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hJ : ∀ p m, 0 < m → J p m = m • DpH p m)
    (hcont : ContinuousOn (fun pm : (Fin d → ℝ) × ℝ => J pm.1 pm.2)
      {pm | 0 ≤ pm.2})
    {p : ι → (Fin d → ℝ)} {m : ι → ℝ}
    {p₀ : Fin d → ℝ} {m₀ : ℝ}
    (hp : Tendsto p l (𝓝 p₀)) (hm : Tendsto m l (𝓝 m₀))
    (hmpos : ∀ᶠ i in l, 0 < m i) (hm₀ : 0 ≤ m₀) :
    Tendsto (fun i => m i • DpH (p i) (m i)) l (𝓝 (J p₀ m₀)) := by
  have hpair : Tendsto (fun i => (p i, m i)) l
      (𝓝[{pm : (Fin d → ℝ) × ℝ | 0 ≤ pm.2}] (p₀, m₀)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hp.prodMk_nhds hm, hmpos.mono fun i hi => hi.le⟩
  have hlim := (hcont (p₀, m₀) hm₀).tendsto.comp hpair
  apply hlim.congr'
  filter_upwards [hmpos] with i hi
  exact hJ (p i) (m i) hi

/-- The paper's positive truncations converge to J even at vacuum.
No zero-boundary-flux hypothesis is involved. -/
theorem flux_max_tendsto
    {ι : Type*} {l : Filter ι}
    {DpH J : (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    (hJ : ∀ p m, 0 < m → J p m = m • DpH p m)
    (hcont : ContinuousOn (fun pm : (Fin d → ℝ) × ℝ => J pm.1 pm.2)
      {pm | 0 ≤ pm.2})
    (p : Fin d → ℝ) {m : ℝ} (hm : 0 ≤ m)
    {δ : ι → ℝ} (hδ : Tendsto δ l (𝓝 0))
    (hδpos : ∀ᶠ i in l, 0 < δ i) :
    Tendsto (fun i => max m (δ i) • DpH p (max m (δ i)))
      l (𝓝 (J p m)) := by
  apply flux_tendsto_of_positive hJ hcont tendsto_const_nhds
  · have hmax : Tendsto (fun i => max m (δ i)) l (𝓝 (max m 0)) :=
      tendsto_const_nhds.max hδ
    simpa [max_eq_left hm] using hmax
  · exact hδpos.mono fun i hi => lt_of_lt_of_le hi (le_max_right _ _)
  · exact hm

private lemma dot_tendsto_right
    {ι : Type*} {l : Filter ι} {f : ι → (Fin d → ℝ)}
    {v : Fin d → ℝ} (hf : Tendsto f l (𝓝 v)) (w : Fin d → ℝ) :
    Tendsto (fun i => f i ⬝ w) l (𝓝 (v ⬝ w)) := by
  simp only [dotProduct]
  exact tendsto_finset_sum _ fun j _ =>
    ((continuous_apply j).tendsto _ |>.comp hf).mul_const (w j)

/-- A finite boundary value at p forces every limiting flux at q to point
away from p, using supporting hyperplanes and a local lower bound on H.
The lower bound may depend on q; no finite boundary value at q is assumed. -/
theorem boundary_flux_supports_finite_point
    {H : (Fin d → ℝ) → ℝ → ℝ}
    {DpH J : (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {p : Fin d → ℝ} {L : ℝ}
    (hfinite : Tendsto (H p) (𝓝[>] (0 : ℝ)) (𝓝 L))
    (hsupport : ∀ q m, 0 < m → H q m + DpH q m ⬝ (p - q) ≤ H p m)
    (hlower : ∀ q, ∃ C : ℝ, ∀ᶠ m in 𝓝[>] (0 : ℝ), -C ≤ H q m)
    (hJlim : ∀ q, Tendsto (fun m : ℝ => m • DpH q m)
      (𝓝[>] (0 : ℝ)) (𝓝 (J q 0))) :
    ∀ q, J q 0 ⬝ (p - q) ≤ 0 := by
  intro q
  obtain ⟨C, hC⟩ := hlower q
  have hm : Tendsto (fun m : ℝ => m) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hlim := dot_tendsto_right (hJlim q) (p - q)
  have hrhs : Tendsto (fun m => m * (H p m + C))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hm.mul (hfinite.add_const C)
  apply le_of_tendsto_of_tendsto hlim hrhs
  filter_upwards [hC, self_mem_nhdsWithin] with m hcm hmp
  have hs := mul_le_mul_of_nonneg_left (hsupport q m hmp) hmp.le
  rw [euclideanDot_smul_left]
  nlinarith [mul_le_mul_of_nonneg_left hcm hmp.le]

/-- At a finite Hamiltonian boundary point, the continuous limiting flux
vanishes. This is a local conclusion; J may be nonzero at other momenta
where the boundary Hamiltonian is infinite. -/
theorem boundary_flux_zero_at_finite_point
    {H : (Fin d → ℝ) → ℝ → ℝ}
    {DpH J : (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {p : Fin d → ℝ} {L : ℝ}
    (hfinite : Tendsto (H p) (𝓝[>] (0 : ℝ)) (𝓝 L))
    (hsupport : ∀ q m, 0 < m → H q m + DpH q m ⬝ (p - q) ≤ H p m)
    (hlower : ∀ q, ∃ C : ℝ, ∀ᶠ m in 𝓝[>] (0 : ℝ), -C ≤ H q m)
    (hJlim : ∀ q, Tendsto (fun m : ℝ => m • DpH q m)
      (𝓝[>] (0 : ℝ)) (𝓝 (J q 0)))
    (hcont : ContinuousAt (fun q => J q 0) p) :
    J p 0 = 0 := by
  have hs := boundary_flux_supports_finite_point hfinite hsupport hlower hJlim
  let v := J p 0
  have hm : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hq : Tendsto (fun t : ℝ => p - t • v)
      (𝓝[>] (0 : ℝ)) (𝓝 p) := by
    simpa using tendsto_const_nhds.sub (hm.smul_const v)
  have hj := hcont.tendsto.comp hq
  have hv : v ⬝ v ≤ 0 := by
    apply le_of_tendsto (dot_tendsto_right hj v)
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : 0 < t := ht
    have hx := hs (p - t • v)
    have he : p - (p - t • v) = t • v := by abel
    rw [he, euclideanDot_smul_right] at hx
    exact nonpos_of_mul_nonpos_right hx ht'
  funext i
  have hsum : v i * v i ≤ ∑ j, v j * v j :=
    Finset.single_le_sum (fun j _ => mul_self_nonneg (v j)) (Finset.mem_univ i)
  change v i = 0
  change (∑ j, v j * v j) ≤ 0 at hv
  nlinarith [mul_self_nonneg (v i)]

end StationaryMFG.Theorems.Congestion.Paper
