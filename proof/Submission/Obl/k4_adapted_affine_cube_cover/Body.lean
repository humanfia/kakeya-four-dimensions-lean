import Mathlib

namespace Submission.Obl.k4_adapted_affine_cube_cover

open MeasureTheory Set

/-- The seminorm unit body is compact because it lies in the Euclidean unit ball. -/
theorem isCompact_unit_body {n : ℕ}
    (V : Seminorm ℝ (EuclideanSpace ℝ (Fin n))) (hV : Continuous V)
    (hdom : ∀ x, ‖x‖ ≤ V x) :
    IsCompact {x : EuclideanSpace ℝ (Fin n) | V x ≤ 1} := by
  apply (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1).of_isClosed_subset
    (isClosed_le hV continuous_const)
  intro x hx
  exact mem_closedBall_zero_iff.mpr ((hdom x).trans hx)

/-- Continuity gives a nonempty open subset of the seminorm unit body. -/
theorem volume_unit_body_pos {n : ℕ}
    (V : Seminorm ℝ (EuclideanSpace ℝ (Fin n))) (hV : Continuous V) :
    0 < volume {x : EuclideanSpace ℝ (Fin n) | V x ≤ 1} := by
  have hpos : 0 < volume {x : EuclideanSpace ℝ (Fin n) | V x < 1} :=
    (isOpen_lt hV continuous_const).measure_pos volume ⟨0, by simp⟩
  apply hpos.trans_le
  apply measure_mono
  intro x hx
  change V x ≤ 1
  exact le_of_lt hx

/-- The real volume of the body is positive and finite. -/
theorem volume_unit_body_toReal_pos {n : ℕ}
    (V : Seminorm ℝ (EuclideanSpace ℝ (Fin n))) (hV : Continuous V)
    (hdom : ∀ x, ‖x‖ ≤ V x) :
    0 < (volume {x : EuclideanSpace ℝ (Fin n) | V x ≤ 1}).toReal :=
  ENNReal.toReal_pos (volume_unit_body_pos V hV).ne'
    (isCompact_unit_body V hV hdom).measure_ne_top

/-- Rescaling a basis supplies a basis in any seminorm unit body. -/
theorem exists_basis_in_unit_body {n : ℕ}
    (V : Seminorm ℝ (EuclideanSpace ℝ (Fin n))) :
    ∃ b : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)), ∀ i, V (b i) ≤ 1 := by
  classical
  let e := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hpos (i : Fin n) : 0 < 1 + V (e i) := by positivity
  let w : Fin n → ℝ := fun i => (1 + V (e i))⁻¹
  have hw (i : Fin n) : IsUnit (w i) :=
    isUnit_iff_ne_zero.mpr (inv_ne_zero (hpos i).ne')
  refine ⟨e.isUnitSMul hw, fun i => ?_⟩
  rw [Module.Basis.isUnitSMul_apply, map_smul_eq_mul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (hpos i))]
  exact (inv_mul_le_one₀ (hpos i)).mpr (by linarith)

end Submission.Obl.k4_adapted_affine_cube_cover
