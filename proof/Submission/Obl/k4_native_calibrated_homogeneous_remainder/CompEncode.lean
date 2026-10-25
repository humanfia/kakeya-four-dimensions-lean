/- Adapted from this LOT tree, obligation o119, session x0404, commit b1aa67e,
   Submission/Obl/k4_finite_width_critical_contradiction/CompEncode.lean. -/
import Mathlib

/-!
# Encoding finitely many worlds as one world

To homogenize a multi-world problem with the single-world homogenization theorem
(accepted o075), world `c` of `W` is placed in its own copy of trajectory space:
the internal index `i` becomes `W * i + c`, and the two hidden coefficients
`(l 2, l 5)` are scaled by `b` and the constant one is shifted by `o`.  With
`b = B σ` and `o = Λ c σ` the encoded hidden coordinate is `(B w + Λ c) σ`, so a
dyadic hidden bin of the encoded world at depth `ρ₀ + s` is a hidden bin of world
`c` at depth `s`, shifted by an integer that identifies `c`.

This file contains the coefficient maps, their inverses and Jacobians, and the
pushforward of piecewise-Lebesgue priors.
-/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder.Comp

open MeasureTheory

/-- Encoded coefficients: hidden coefficients `(l 2, l 5)` scaled by `b`, `l 2` shifted by `o`. -/
def encCoeff (b o : ℝ) (l : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![l 0, l 1, b * l 2 + o, l 3, l 4, b * l 5]

/-- The inverse of `encCoeff b o` for `b ≠ 0`. -/
noncomputable def decCoeff (b o : ℝ) (l : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![l 0, l 1, (l 2 - o) / b, l 3, l 4, l 5 / b]

theorem encCoeff_apply_hidden (b o : ℝ) (l : Fin 6 → ℝ) (t : ℝ) :
    encCoeff b o l 2 + t * encCoeff b o l 5 = b * (l 2 + t * l 5) + o := by
  simp [encCoeff]; ring

theorem encCoeff_zero (b o : ℝ) (l : Fin 6 → ℝ) : encCoeff b o l 0 = l 0 := rfl
theorem encCoeff_one (b o : ℝ) (l : Fin 6 → ℝ) : encCoeff b o l 1 = l 1 := rfl
theorem encCoeff_two (b o : ℝ) (l : Fin 6 → ℝ) : encCoeff b o l 2 = b * l 2 + o := rfl
theorem encCoeff_three (b o : ℝ) (l : Fin 6 → ℝ) : encCoeff b o l 3 = l 3 := rfl
theorem encCoeff_four (b o : ℝ) (l : Fin 6 → ℝ) : encCoeff b o l 4 = l 4 := rfl
theorem encCoeff_five (b o : ℝ) (l : Fin 6 → ℝ) : encCoeff b o l 5 = b * l 5 := rfl

attribute [local simp] encCoeff_zero encCoeff_one encCoeff_two encCoeff_three encCoeff_four encCoeff_five

theorem decCoeff_encCoeff {b : ℝ} (hb : b ≠ 0) (o : ℝ) (l : Fin 6 → ℝ) :
    decCoeff b o (encCoeff b o l) = l := by
  ext e
  fin_cases e <;> simp [decCoeff, encCoeff] <;> field_simp

theorem encCoeff_decCoeff {b : ℝ} (hb : b ≠ 0) (o : ℝ) (l : Fin 6 → ℝ) :
    encCoeff b o (decCoeff b o l) = l := by
  ext e
  fin_cases e <;> simp [decCoeff, encCoeff] <;> field_simp <;> ring

/-- The linear part of `encCoeff`. -/
def encMatrix (b : ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  Matrix.diagonal ![1, 1, b, 1, 1, b]

theorem encCoeff_eq (b o : ℝ) (l : Fin 6 → ℝ) :
    encCoeff b o l = (encMatrix b).mulVec l + ![0, 0, o, 0, 0, 0] := by
  ext i
  fin_cases i <;> simp [encCoeff, encMatrix, Matrix.mulVec_diagonal]

theorem det_encMatrix (b : ℝ) : (encMatrix b).det = b ^ 2 := by
  simp [encMatrix, Matrix.det_diagonal, Fin.prod_univ_succ]; ring

theorem continuous_encCoeff (b o : ℝ) : Continuous (encCoeff b o) := by
  refine continuous_pi fun e => ?_
  fin_cases e <;> simp only [encCoeff] <;> fun_prop

theorem continuous_decCoeff (b o : ℝ) : Continuous (decCoeff b o) := by
  refine continuous_pi fun e => ?_
  fin_cases e <;> simp only [decCoeff] <;> fun_prop

theorem measurable_encCoeff (b o : ℝ) : Measurable (encCoeff b o) :=
  (continuous_encCoeff b o).measurable

theorem measurable_decCoeff (b o : ℝ) : Measurable (decCoeff b o) :=
  (continuous_decCoeff b o).measurable

/-- `encCoeff b o` as a homeomorphism for `b ≠ 0`. -/
noncomputable def encHomeomorph {b : ℝ} (hb : b ≠ 0) (o : ℝ) :
    (Fin 6 → ℝ) ≃ₜ (Fin 6 → ℝ) where
  toFun := encCoeff b o
  invFun := decCoeff b o
  left_inv := decCoeff_encCoeff hb o
  right_inv := encCoeff_decCoeff hb o
  continuous_toFun := continuous_encCoeff b o
  continuous_invFun := continuous_decCoeff b o

theorem map_encCoeff_volume {b : ℝ} (hb : b ≠ 0) (o : ℝ) :
    Measure.map (encCoeff b o) volume = ENNReal.ofReal |(b ^ 2)|⁻¹ • volume := by
  have hdet : (encMatrix b).det ≠ 0 := by rw [det_encMatrix]; positivity
  have hfun : encCoeff b o = (fun x => x + ![0, 0, o, 0, 0, 0]) ∘ (Matrix.toLin' (encMatrix b)) := by
    funext l; simp [encCoeff_eq b o l, Matrix.toLin'_apply]
  rw [hfun, ← Measure.map_map (measurable_add_const _)
    (LinearMap.continuous_on_pi _).measurable,
    Real.map_matrix_volume_pi_eq_smul_volume_pi hdet,
    Measure.map_smul, map_add_right_eq_self, abs_inv, det_encMatrix]
  exact (measurable_add_const _).aemeasurable

theorem map_encCoeff_restrict {b : ℝ} (hb : b ≠ 0) (o : ℝ) (S : Set (Fin 6 → ℝ)) :
    Measure.map (encCoeff b o) (volume.restrict S) =
      ENNReal.ofReal |(b ^ 2)|⁻¹ • volume.restrict (decCoeff b o ⁻¹' S) := by
  set e := (encHomeomorph hb o).toMeasurableEquiv
  have he : (e : (Fin 6 → ℝ) → (Fin 6 → ℝ)) = encCoeff b o := rfl
  have hvol : Measure.map e volume = ENNReal.ofReal |(b ^ 2)|⁻¹ • volume := by
    rw [he]; exact map_encCoeff_volume hb o
  ext T hT
  have key : Measure.map e volume (T ∩ decCoeff b o ⁻¹' S) =
      (ENNReal.ofReal |(b ^ 2)|⁻¹ • volume) (T ∩ decCoeff b o ⁻¹' S) := by rw [hvol]
  rw [e.map_apply] at key
  have hpre : e ⁻¹' (T ∩ decCoeff b o ⁻¹' S) = e ⁻¹' T ∩ S := by
    ext x
    simp only [Set.mem_preimage, Set.mem_inter_iff]
    rw [he, decCoeff_encCoeff hb o]
  rw [hpre] at key
  rw [← he, e.map_apply, Measure.smul_apply, Measure.restrict_apply hT,
    Measure.restrict_apply (e.measurable hT), key, Measure.smul_apply]

end Submission.Obl.k4_native_calibrated_homogeneous_remainder.Comp
