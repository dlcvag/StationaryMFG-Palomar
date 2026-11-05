module

public import StationaryMFG.Solutions.PaperStrong
public import StationaryMFG.Hamiltonian.PaperExtension

@[expose] public section

/-!
# Transport of strong solutions between Hamiltonian representatives

The PDE clauses depend only on positive-mass Hamiltonian data and the
limiting flux at the actual solution arguments. This allows the existence
machinery to use measurable representatives while retaining the paper's
original input functions in the final theorem.
-/

namespace StationaryMFG.Solutions.PaperStrong

open MeasureTheory StationaryMFG.Periodic StationaryMFG.Hamiltonian

variable {d : ℕ}
variable {V : (Fin d → ℝ) → ℝ}
variable {H G : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
variable {J K : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
variable {Du : Fin d → (Fin d → ℝ) → ℝ}
variable {m u : (Fin d → ℝ) → ℝ}

theorem IsStrongSolution_HJB.congr_positive
    (h : IsStrongSolution_HJB V H Du m u)
    (hHG : ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p t, 0 < t → H x p t = G x p t) :
    IsStrongSolution_HJB V G Du m u := by
  constructor
  · filter_upwards [h.1, hHG] with x hx hxe
    rwa [← Paper.Hext_congr_on_pos (hxe (fun i => Du i x)) (m x)]
  · filter_upwards [h.2, hHG] with x hx hxe hp
    rw [← Paper.Hext_congr_on_pos (hxe (fun i => Du i x)) (m x)]
    exact hx hp

theorem transport_congr_flux
    (h : Strong.IsStrongSolution_Transport V J Du m u)
    (hJK : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      J x (fun i => Du i x) (m x) = K x (fun i => Du i x) (m x)) :
    Strong.IsStrongSolution_Transport V K Du m u := by
  refine ⟨h.1.congr hJK, ?_⟩
  intro φ
  calc
    (∫ x in UnitCube d,
        (m x - 1) * (φ : (Fin d → ℝ) → ℝ) x +
          K x (fun i => Du i x) (m x) ⬝
            (fun i => (SmoothPeriodic.partialDeriv i φ : (Fin d → ℝ) → ℝ) x)) =
      ∫ x in UnitCube d,
        (m x - 1) * (φ : (Fin d → ℝ) → ℝ) x +
          J x (fun i => Du i x) (m x) ⬝
            (fun i => (SmoothPeriodic.partialDeriv i φ : (Fin d → ℝ) → ℝ) x) := by
      apply integral_congr_ae
      filter_upwards [hJK] with x hx
      rw [hx]
    _ = 0 := h.2 φ

theorem IsStrongSolution.congr_representatives
    (h : IsStrongSolution V H J Du m u)
    (hHG : ∀ᵐ x ∂(volume.restrict (UnitCube d)), ∀ p t, 0 < t → H x p t = G x p t)
    (hJK : ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      J x (fun i => Du i x) (m x) = K x (fun i => Du i x) (m x)) :
    IsStrongSolution V G K Du m u :=
  ⟨h.1.congr_positive hHG, transport_congr_flux h.2 hJK⟩

end StationaryMFG.Solutions.PaperStrong
