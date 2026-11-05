module

public import StationaryMFG.Basic

@[expose] public section

/-!
# Periodicity predicate on `(Fin d → ℝ) → X`

Per `docs/CONVENTIONS.md` §1, we never work with the quotient `ℝ^d / ℤ^d`.
Instead, a function `f : (Fin d → ℝ) → X` is *periodic* if it is invariant
under every integer-lattice translation. This file introduces the predicate
`StationaryMFG.Periodic.IsPeriodic` and the basic closure properties
(addition, subtraction, scalar multiplication, negation, constants, zero,
congruence) that the rest of Phase 1 relies on.

Integration over the torus and `Lᵖ`/`Wᵏ,ᵖ` infrastructure are defined in
sibling modules (`UnitCube.lean`, `Integral.lean`, `Lp.lean`, …) and are
**not** part of this task.
-/

namespace StationaryMFG
namespace Periodic

variable {d : ℕ} {X : Type*}

/-- `f : (Fin d → ℝ) → X` is periodic if it is invariant under every integer-
lattice translation. The translation vector is the pointwise coercion
`fun i => (k i : ℝ)` of an integer tuple `k : Fin d → ℤ`. -/
def IsPeriodic (f : (Fin d → ℝ) → X) : Prop :=
  ∀ k : Fin d → ℤ, ∀ x, f (x + fun i => (k i : ℝ)) = f x

/-- Periodicity transfers along pointwise equality. -/
lemma IsPeriodic.congr {f g : (Fin d → ℝ) → X}
    (hf : IsPeriodic f) (hfg : ∀ x, f x = g x) : IsPeriodic g := by
  intro k x
  have h1 := hf k x
  have h2 := hfg (x + fun i => (k i : ℝ))
  have h3 := hfg x
  -- f (x + k) = f x, and f = g pointwise, so g (x + k) = g x
  calc g (x + fun i => (k i : ℝ))
      = f (x + fun i => (k i : ℝ)) := (h2).symm
    _ = f x := h1
    _ = g x := h3

/-- Constant functions are periodic. -/
lemma IsPeriodic.const (c : X) : IsPeriodic (fun _ : (Fin d → ℝ) => c) := by
  intro _ _; rfl

/-- The zero function is periodic. -/
lemma IsPeriodic.zero [Zero X] : IsPeriodic (0 : (Fin d → ℝ) → X) := by
  intro _ _; rfl

/-- Sum of two periodic functions is periodic. -/
lemma IsPeriodic.add [Add X] {f g : (Fin d → ℝ) → X}
    (hf : IsPeriodic f) (hg : IsPeriodic g) : IsPeriodic (f + g) := by
  intro k x
  simp only [Pi.add_apply, hf k x, hg k x]

/-- Negation of a periodic function is periodic. -/
lemma IsPeriodic.neg [Neg X] {f : (Fin d → ℝ) → X}
    (hf : IsPeriodic f) : IsPeriodic (-f) := by
  intro k x
  simp only [Pi.neg_apply, hf k x]

/-- Difference of two periodic functions is periodic. -/
lemma IsPeriodic.sub [Sub X] {f g : (Fin d → ℝ) → X}
    (hf : IsPeriodic f) (hg : IsPeriodic g) : IsPeriodic (f - g) := by
  intro k x
  simp only [Pi.sub_apply, hf k x, hg k x]

/-- Scalar multiple of a periodic function (by a real scalar) is periodic. -/
lemma IsPeriodic.smul [SMul ℝ X] {f : (Fin d → ℝ) → X} (c : ℝ)
    (hf : IsPeriodic f) : IsPeriodic (c • f) := by
  intro k x
  simp only [Pi.smul_apply, hf k x]

/-! ### Concrete type-checking examples -/

example : IsPeriodic (fun _ : (Fin 1 → ℝ) => (0 : ℝ)) :=
  IsPeriodic.const (0 : ℝ)

example : IsPeriodic (0 : (Fin 2 → ℝ) → ℝ) := IsPeriodic.zero

example {f g : (Fin 3 → ℝ) → ℝ}
    (hf : IsPeriodic f) (hg : IsPeriodic g) : IsPeriodic (f + g) :=
  hf.add hg

example {f g : (Fin 3 → ℝ) → ℝ}
    (hf : IsPeriodic f) (hg : IsPeriodic g) : IsPeriodic (f - g) :=
  hf.sub hg

example {f : (Fin 2 → ℝ) → ℝ} (hf : IsPeriodic f) : IsPeriodic (-f) :=
  hf.neg

example {f : (Fin 2 → ℝ) → ℝ} (c : ℝ) (hf : IsPeriodic f) :
    IsPeriodic (c • f) :=
  hf.smul c

example {f g : (Fin 2 → ℝ) → ℝ}
    (hf : IsPeriodic f) (hfg : ∀ x, f x = g x) : IsPeriodic g :=
  hf.congr hfg

end Periodic
end StationaryMFG
