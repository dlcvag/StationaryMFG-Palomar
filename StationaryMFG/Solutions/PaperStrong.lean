module

public import StationaryMFG.Solutions.Strong

@[expose] public section

/-!
# Strong solutions allowing an infinite Hamiltonian boundary value

The inequality in Definition `def:strong` of the paper is interpreted
using the extended right-hand limit of H at zero mass. Writing it as
`Hext ≤ ↑(V-u)` avoids subtraction involving infinity. This requires
finiteness only at the arguments attained by a solution, not at every
momentum. The transport clause retains the supplied limiting flux J.

The existing real-valued predicate is a specialization under finite
boundary agreement. Its compatibility proofs below are migration
infrastructure, not a proof of the corrected existence theorems.
-/

namespace StationaryMFG.Solutions.PaperStrong

open MeasureTheory StationaryMFG.Periodic StationaryMFG.Hamiltonian

variable {d : ℕ}

/-- The extended-real HJB clause, with the original equation on positive mass. -/
def IsStrongSolution_HJB
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ) : Prop :=
  (∀ᵐ x ∂(volume.restrict (UnitCube d)),
    Hext H x (fun i => Du i x) (m x) ≤ ((V x - u x : ℝ) : WithTop ℝ)) ∧
  (∀ᵐ x ∂(volume.restrict (UnitCube d)),
    0 < m x →
      Hext H x (fun i => Du i x) (m x) = ((V x - u x : ℝ) : WithTop ℝ))

/-- The strong PDE clauses with a general boundary Hamiltonian and flux.
Nonnegativity, Sobolev membership, and the gradient tie remain explicit
conditions on the witnesses in the existence statements. -/
def IsStrongSolution
    (V : (Fin d → ℝ) → ℝ)
    (H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ))
    (Du : Fin d → (Fin d → ℝ) → ℝ)
    (m u : (Fin d → ℝ) → ℝ) : Prop :=
  IsStrongSolution_HJB V H Du m u ∧ Strong.IsStrongSolution_Transport V J Du m u

/-- The HJB inequality itself excludes infinity at solution arguments.
It does not imply a finite boundary value at arbitrary momenta. -/
theorem IsStrongSolution_HJB.ae_finite
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    (h : IsStrongSolution_HJB V H Du m u) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      Hext H x (fun i => Du i x) (m x) ≠ (⊤ : WithTop ℝ) := by
  filter_upwards [h.1] with x hx
  exact ne_top_of_le_ne_top (WithTop.coe_ne_top) hx

/-- On positive mass the extended equality is the ordinary real equation. -/
theorem IsStrongSolution_HJB.ae_real_eq_on_pos
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    (h : IsStrongSolution_HJB V H Du m u) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      0 < m x → u x + H x (fun i => Du i x) (m x) - V x = 0 := by
  filter_upwards [h.2] with x hx hp
  have he := hx hp
  rw [Hext_of_pos H x _ hp, WithTop.coe_inj] at he
  linarith

/-- At nonnegative arguments, finite boundary agreement identifies the
extended Hamiltonian with the supplied real-valued representative. -/
theorem ae_Hext_eq_of_agree
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m : (Fin d → ℝ) → ℝ}
    (hAgree : H_zero_eq_Hext H)
    (hm : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x) :
    ∀ᵐ x ∂(volume.restrict (UnitCube d)),
      Hext H x (fun i => Du i x) (m x) =
        ((H x (fun i => Du i x) (m x) : ℝ) : WithTop ℝ) := by
  filter_upwards [hAgree, hm] with x hx hmx
  rcases eq_or_lt_of_le hmx with hz | hp
  · rw [← hz]
    exact (hx _).symm
  · exact Hext_of_pos H x _ hp

/-- The old HJB clause and the extended-real clause agree on the finite
boundary specialization; no boundary-existence assumption is needed
separately for this compatibility result. -/
theorem hjb_iff_of_agree
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    (hAgree : H_zero_eq_Hext H)
    (hm : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x) :
    IsStrongSolution_HJB V H Du m u ↔ Strong.IsStrongSolution_HJB V H Du m u := by
  have he := ae_Hext_eq_of_agree (Du := Du) hAgree hm
  constructor
  · intro h
    refine ⟨?_, h.ae_real_eq_on_pos⟩
    have hle := h.1
    filter_upwards [hle, he] with x hx hex
    rw [hex, WithTop.coe_le_coe] at hx
    linarith
  · rintro ⟨hle, heq⟩
    constructor
    · filter_upwards [hle, he] with x hx hex
      rw [hex, WithTop.coe_le_coe]
      linarith
    · filter_upwards [heq] with x hx hp
      rw [Hext_of_pos H x _ hp, WithTop.coe_inj]
      linarith [hx hp]

/-- The transport equation is unchanged by the finite-boundary bridge. -/
theorem strong_iff_of_agree
    {V : (Fin d → ℝ) → ℝ}
    {H : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ}
    {J : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)}
    {Du : Fin d → (Fin d → ℝ) → ℝ}
    {m u : (Fin d → ℝ) → ℝ}
    (hAgree : H_zero_eq_Hext H)
    (hm : ∀ᵐ x ∂(volume.restrict (UnitCube d)), 0 ≤ m x) :
    IsStrongSolution V H J Du m u ↔ Strong.IsStrongSolution V H J Du m u :=
  and_congr (hjb_iff_of_agree hAgree hm) Iff.rfl

end StationaryMFG.Solutions.PaperStrong
