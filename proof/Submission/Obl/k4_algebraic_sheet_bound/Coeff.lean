import Mathlib

/-!
# Coordinates for relations of bounded degree

Polynomials in `n + 1` variables of total degree at most `D` form a finite-dimensional space.
`polyOf c` is the polynomial with coordinates `c : Fin (polyDim n D) → ℂ` in a fixed basis of it.
Evaluation is jointly continuous in the coordinates and the point, and every nonzero relation of
degree at most `D` is a nonzero multiple of `polyOf c` for a unit vector `c` (sup norm).
-/

namespace Submission.Obl.k4_algebraic_sheet_bound

open MvPolynomial

/-- Polynomials in `n + 1` variables of total degree at most `D`. -/
noncomputable abbrev PolySpace (n D : ℕ) : Submodule ℂ (MvPolynomial (Fin (n + 1)) ℂ) :=
  restrictTotalDegree (Fin (n + 1)) ℂ D

/-- The dimension of `PolySpace n D`. -/
noncomputable abbrev polyDim (n D : ℕ) : ℕ := Module.finrank ℂ (PolySpace n D)

/-- A fixed basis of `PolySpace n D`. -/
noncomputable def polyBasis (n D : ℕ) : Module.Basis (Fin (polyDim n D)) ℂ (PolySpace n D) :=
  Module.finBasis ℂ (PolySpace n D)

/-- The polynomial with coordinates `c` in the basis `polyBasis n D`. -/
noncomputable def polyOf {n D : ℕ} (c : Fin (polyDim n D) → ℂ) :
    MvPolynomial (Fin (n + 1)) ℂ :=
  ((polyBasis n D).equivFun.symm c : PolySpace n D)

theorem eval_polyOf {n D : ℕ} (c : Fin (polyDim n D) → ℂ) (x : Fin (n + 1) → ℂ) :
    eval x (polyOf c) =
      ∑ i, c i * eval x ((polyBasis n D i : PolySpace n D) : MvPolynomial (Fin (n + 1)) ℂ) := by
  simp [polyOf, Module.Basis.equivFun_symm_apply, map_sum]

theorem continuous_eval_polyOf {n D : ℕ} {X : Type*} [TopologicalSpace X]
    {c : X → Fin (polyDim n D) → ℂ} {x : X → Fin (n + 1) → ℂ} (hc : Continuous c)
    (hx : Continuous x) :
    Continuous fun p => eval (x p) (polyOf (c p)) := by
  simp_rw [eval_polyOf]
  refine continuous_finsetSum _ fun i _ => ?_
  exact ((continuous_apply i).comp hc).mul ((MvPolynomial.continuous_eval _).comp hx)

theorem polyOf_ne_zero {n D : ℕ} {c : Fin (polyDim n D) → ℂ} (hc : c ≠ 0) : polyOf c ≠ 0 := by
  intro h
  apply hc
  have h0 : (polyBasis n D).equivFun.symm c = 0 := Subtype.ext h
  have h1 := congrArg (polyBasis n D).equivFun h0
  rwa [LinearEquiv.apply_symm_apply, map_zero] at h1

/-- Every nonzero polynomial of total degree at most `D` is a nonzero multiple of `polyOf c` for
a unit vector `c`. -/
theorem exists_unit_polyOf {n D : ℕ} {P : MvPolynomial (Fin (n + 1)) ℂ} (hP : P ≠ 0)
    (hdeg : P.totalDegree ≤ D) :
    ∃ c : Fin (polyDim n D) → ℂ, ‖c‖ = 1 ∧ ∃ a : ℂ, a ≠ 0 ∧
      ∀ x, eval x (polyOf c) = a * eval x P := by
  set p : PolySpace n D := ⟨P, (mem_restrictTotalDegree _ _ _).mpr hdeg⟩ with hp
  set c₀ := (polyBasis n D).equivFun p with hc₀def
  have hc₀ : c₀ ≠ 0 := by
    intro h
    apply hP
    have : p = 0 := by
      have := congrArg (polyBasis n D).equivFun.symm h
      simpa [c₀] using this
    exact congrArg Subtype.val this
  have hpos : 0 < ‖c₀‖ := norm_pos_iff.mpr hc₀
  refine ⟨((‖c₀‖⁻¹ : ℝ) : ℂ) • c₀, ?_, ((‖c₀‖⁻¹ : ℝ) : ℂ), ?_, ?_⟩
  · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
    exact inv_mul_cancel₀ hpos.ne'
  · exact_mod_cast (inv_ne_zero hpos.ne')
  · intro x
    have h1 : polyOf (((‖c₀‖⁻¹ : ℝ) : ℂ) • c₀) = ((‖c₀‖⁻¹ : ℝ) : ℂ) • P := by
      simp only [polyOf, map_smul, c₀, LinearEquiv.symm_apply_apply, p]
      rfl
    rw [h1, MvPolynomial.smul_eval]

end Submission.Obl.k4_algebraic_sheet_bound
