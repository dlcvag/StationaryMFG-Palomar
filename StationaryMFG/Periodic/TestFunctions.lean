module

public import StationaryMFG.Periodic.Basic

@[expose] public section

/-!
# Smooth periodic test functions `C^∞_per(𝕋^d)`

This file introduces the space of smooth periodic test functions on the torus
`𝕋^d`, modelled (per `docs/CONVENTIONS.md`) as functions `(Fin d → ℝ) → ℝ`
that are simultaneously `ContDiff ℝ ⊤` and satisfy the periodicity predicate
`StationaryMFG.Periodic.IsPeriodic`.

The space `SmoothPeriodic d` is shown to be a real vector space and to be
closed under pointwise multiplication and partial differentiation. These are
the raw closure properties needed by the weak-derivative definition in the
sibling file `WeakDerivative.lean`.

Note. We use `ContDiff ℝ ((⊤ : ℕ∞) : ℕ∞ω)` (i.e. `∞`, smooth) rather than
`ContDiff ℝ (⊤ : ℕ∞ω)` (i.e. `ω`, analytic). The closure properties under
sums, products, real scalar multiplication, and partial derivatives hold at
either smoothness level, but `∞` is what the bump-based mollifier in
`Mollifier.lean` can satisfy, so we use that level here as well.
-/

namespace StationaryMFG
namespace Periodic

open scoped ContDiff

variable {d : ℕ}

/-- A smooth periodic real-valued function on `𝕋^d`, packaged as a structure
carrying the function itself together with proofs of smoothness
(`ContDiff ℝ ⊤`) and periodicity (`IsPeriodic`). -/
structure SmoothPeriodic (d : ℕ) where
  /-- The underlying function. -/
  toFun : (Fin d → ℝ) → ℝ
  /-- The function is smooth (in the sense `ContDiff ℝ ∞`, i.e. infinitely
  differentiable; not necessarily analytic). -/
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : ℕ∞ω) toFun
  /-- The function is periodic with respect to the integer lattice. -/
  periodic : IsPeriodic toFun

namespace SmoothPeriodic

instance : CoeFun (SmoothPeriodic d) (fun _ => (Fin d → ℝ) → ℝ) where
  coe := SmoothPeriodic.toFun

@[simp] lemma coe_mk (f : (Fin d → ℝ) → ℝ)
    (hs : ContDiff ℝ ((⊤ : ℕ∞) : ℕ∞ω) f) (hp : IsPeriodic f) :
    ((⟨f, hs, hp⟩ : SmoothPeriodic d) : (Fin d → ℝ) → ℝ) = f := rfl

@[ext] lemma ext {φ ψ : SmoothPeriodic d}
    (h : ∀ x, (φ : (Fin d → ℝ) → ℝ) x = (ψ : (Fin d → ℝ) → ℝ) x) : φ = ψ := by
  cases φ with
  | mk f hs hp =>
    cases ψ with
    | mk g hs' hp' =>
      have : f = g := funext h
      subst this
      rfl

/-! ### Algebraic structure -/

/-- The zero test function. -/
instance : Zero (SmoothPeriodic d) where
  zero :=
    { toFun    := 0
      smooth   := contDiff_const
      periodic := IsPeriodic.zero }

@[simp] lemma coe_zero :
    ((0 : SmoothPeriodic d) : (Fin d → ℝ) → ℝ) = 0 := rfl

/-- Pointwise sum of two test functions. -/
instance : Add (SmoothPeriodic d) where
  add φ ψ :=
    { toFun    := (φ : (Fin d → ℝ) → ℝ) + (ψ : (Fin d → ℝ) → ℝ)
      smooth   := φ.smooth.add ψ.smooth
      periodic := φ.periodic.add ψ.periodic }

@[simp] lemma coe_add (φ ψ : SmoothPeriodic d) :
    ((φ + ψ : SmoothPeriodic d) : (Fin d → ℝ) → ℝ)
      = (φ : (Fin d → ℝ) → ℝ) + (ψ : (Fin d → ℝ) → ℝ) := rfl

/-- Pointwise negation. -/
instance : Neg (SmoothPeriodic d) where
  neg φ :=
    { toFun    := -(φ : (Fin d → ℝ) → ℝ)
      smooth   := φ.smooth.neg
      periodic := φ.periodic.neg }

@[simp] lemma coe_neg (φ : SmoothPeriodic d) :
    ((-φ : SmoothPeriodic d) : (Fin d → ℝ) → ℝ)
      = -((φ : (Fin d → ℝ) → ℝ)) := rfl

/-- Pointwise difference. -/
instance : Sub (SmoothPeriodic d) where
  sub φ ψ :=
    { toFun    := (φ : (Fin d → ℝ) → ℝ) - (ψ : (Fin d → ℝ) → ℝ)
      smooth   := φ.smooth.sub ψ.smooth
      periodic := φ.periodic.sub ψ.periodic }

@[simp] lemma coe_sub (φ ψ : SmoothPeriodic d) :
    ((φ - ψ : SmoothPeriodic d) : (Fin d → ℝ) → ℝ)
      = (φ : (Fin d → ℝ) → ℝ) - (ψ : (Fin d → ℝ) → ℝ) := rfl

/-- Real scalar multiplication. -/
instance : SMul ℝ (SmoothPeriodic d) where
  smul c φ :=
    { toFun    := c • (φ : (Fin d → ℝ) → ℝ)
      smooth   := φ.smooth.const_smul c
      periodic := φ.periodic.smul c }

@[simp] lemma coe_smul (c : ℝ) (φ : SmoothPeriodic d) :
    ((c • φ : SmoothPeriodic d) : (Fin d → ℝ) → ℝ)
      = c • ((φ : (Fin d → ℝ) → ℝ)) := rfl

/-- Natural-number scalar multiplication, defined via the underlying-function action. -/
instance : SMul ℕ (SmoothPeriodic d) where
  smul n φ :=
    { toFun    := (n : ℕ) • (φ : (Fin d → ℝ) → ℝ)
      smooth   := by
        -- `n • f = (n : ℝ) • f` pointwise, hence still smooth
        have h := φ.smooth.const_smul (n : ℝ)
        convert h using 1
        funext x; simp
      periodic := by
        intro k x
        simp [φ.periodic k x] }

@[simp] lemma coe_nsmul (n : ℕ) (φ : SmoothPeriodic d) :
    ((n • φ : SmoothPeriodic d) : (Fin d → ℝ) → ℝ)
      = n • ((φ : (Fin d → ℝ) → ℝ)) := rfl

/-- Integer scalar multiplication, defined via the underlying-function action. -/
instance : SMul ℤ (SmoothPeriodic d) where
  smul n φ :=
    { toFun    := (n : ℤ) • (φ : (Fin d → ℝ) → ℝ)
      smooth   := by
        have h := φ.smooth.const_smul (n : ℝ)
        convert h using 1
        funext x; simp
      periodic := by
        intro k x
        simp [φ.periodic k x] }

@[simp] lemma coe_zsmul (n : ℤ) (φ : SmoothPeriodic d) :
    ((n • φ : SmoothPeriodic d) : (Fin d → ℝ) → ℝ)
      = n • ((φ : (Fin d → ℝ) → ℝ)) := rfl

instance : AddCommGroup (SmoothPeriodic d) :=
  Function.Injective.addCommGroup
    (fun φ : SmoothPeriodic d => (φ : (Fin d → ℝ) → ℝ))
    (fun _ _ h => SmoothPeriodic.ext (fun x => congrFun h x))
    rfl
    (fun _ _ => rfl)
    (fun _ => rfl)
    (fun _ _ => rfl)
    (fun _ _ => rfl)
    (fun _ _ => rfl)

noncomputable instance : Module ℝ (SmoothPeriodic d) :=
  Function.Injective.module ℝ
    { toFun := fun φ : SmoothPeriodic d => (φ : (Fin d → ℝ) → ℝ)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
    (fun _ _ h => SmoothPeriodic.ext (fun x => congrFun h x))
    (fun _ _ => rfl)

/-! ### Multiplicative closure -/

/-- Pointwise product of two smooth periodic test functions is smooth periodic. -/
def mul (φ ψ : SmoothPeriodic d) : SmoothPeriodic d where
  toFun    := fun x => (φ : (Fin d → ℝ) → ℝ) x * (ψ : (Fin d → ℝ) → ℝ) x
  smooth   := φ.smooth.mul ψ.smooth
  periodic := by
    intro k x
    simp [φ.periodic k x, ψ.periodic k x]

@[simp] lemma coe_mul (φ ψ : SmoothPeriodic d) :
    ((mul φ ψ : SmoothPeriodic d) : (Fin d → ℝ) → ℝ)
      = fun x => (φ : (Fin d → ℝ) → ℝ) x * (ψ : (Fin d → ℝ) → ℝ) x := rfl

/-! ### Partial derivatives -/

/-- The partial derivative of a smooth periodic function in direction `e_i` is
again smooth and periodic. Smoothness uses `ContDiff.fderiv_right` together
with `ContDiff.clm_apply`; periodicity follows from the fact that translating
the input by an integer vector does not change `fderiv ℝ φ` (because the
periodicity of `φ` makes the translated function literally equal to `φ`). -/
noncomputable def partialDeriv (i : Fin d) (φ : SmoothPeriodic d) :
    SmoothPeriodic d where
  toFun := fun x =>
    fderiv ℝ (φ : (Fin d → ℝ) → ℝ) x (Pi.basisFun ℝ (Fin d) i)
  smooth := by
    -- `fderiv ℝ φ` is `ContDiff ℝ ∞` (since `∞ + 1 = ∞`).
    have hle : ((⊤ : ℕ∞) : ℕ∞ω) + 1 ≤ ((⊤ : ℕ∞) : ℕ∞ω) := by
      have h1 : ((⊤ : ℕ∞) : ℕ∞ω) + 1 = ((⊤ : ℕ∞) : ℕ∞ω) := by
        rw [show (1 : ℕ∞ω) = (((1 : ℕ∞) : ℕ∞ω)) from rfl,
            ← WithTop.coe_add]
        simp
      exact le_of_eq h1
    have h₁ : ContDiff ℝ ((⊤ : ℕ∞) : ℕ∞ω) (fderiv ℝ (φ : (Fin d → ℝ) → ℝ)) :=
      φ.smooth.fderiv_right (m := ((⊤ : ℕ∞) : ℕ∞ω)) hle
    -- Apply the constant continuous-linear-functional `evaluation at e_i`.
    exact h₁.clm_apply contDiff_const
  periodic := by
    intro k x
    -- Let `a := fun i => (k i : ℝ)` be the integer translation vector.
    set a : Fin d → ℝ := fun i => (k i : ℝ) with ha
    -- Periodicity says `φ (y + a) = φ y` for all `y`; i.e. `φ ∘ (· + a) = φ`.
    have hshift : (fun y => (φ : (Fin d → ℝ) → ℝ) (y + a))
        = (φ : (Fin d → ℝ) → ℝ) := by
      funext y
      exact φ.periodic k y
    -- `fderiv` of the translated function relates to `fderiv` of `φ` at the
    -- shifted point.
    have hfd : fderiv ℝ (fun y => (φ : (Fin d → ℝ) → ℝ) (y + a)) x
        = fderiv ℝ (φ : (Fin d → ℝ) → ℝ) (x + a) :=
      fderiv_comp_add_right (f := (φ : (Fin d → ℝ) → ℝ)) (a := a) (x := x)
    -- Combining the two displays gives `fderiv ℝ φ (x + a) = fderiv ℝ φ x`.
    have hxeq : fderiv ℝ (φ : (Fin d → ℝ) → ℝ) (x + a)
        = fderiv ℝ (φ : (Fin d → ℝ) → ℝ) x := by
      have h := hfd
      rw [hshift] at h
      -- now `h : fderiv ℝ φ x = fderiv ℝ φ (x + a)`
      exact h.symm
    -- Apply both sides to the basis vector `e_i`.
    change fderiv ℝ (φ : (Fin d → ℝ) → ℝ) (x + a) (Pi.basisFun ℝ (Fin d) i)
        = fderiv ℝ (φ : (Fin d → ℝ) → ℝ) x (Pi.basisFun ℝ (Fin d) i)
    rw [hxeq]

@[simp] lemma coe_partialDeriv (i : Fin d) (φ : SmoothPeriodic d) :
    ((partialDeriv i φ : SmoothPeriodic d) : (Fin d → ℝ) → ℝ)
      = fun x => fderiv ℝ (φ : (Fin d → ℝ) → ℝ) x (Pi.basisFun ℝ (Fin d) i) := rfl

/-! ### Constant test functions -/

/-- The constant function `c` packaged as a smooth periodic test function. -/
def const (c : ℝ) : SmoothPeriodic d where
  toFun    := fun _ => c
  smooth   := contDiff_const
  periodic := IsPeriodic.const c

@[simp] lemma coe_const (c : ℝ) :
    ((const c : SmoothPeriodic d) : (Fin d → ℝ) → ℝ) = fun _ => c := rfl

/-! ### Sample examples -/

example : ∃ φ : SmoothPeriodic 2, (φ : (Fin 2 → ℝ) → ℝ) = fun _ => (0 : ℝ) :=
  ⟨0, rfl⟩

example : ∃ φ : SmoothPeriodic 3, (φ : (Fin 3 → ℝ) → ℝ) = fun _ => (1 : ℝ) :=
  ⟨const 1, rfl⟩

example (φ ψ : SmoothPeriodic 2) :
    ((mul φ ψ) : (Fin 2 → ℝ) → ℝ) = fun x => (φ : _) x * (ψ : _) x := rfl

end SmoothPeriodic

end Periodic
end StationaryMFG
