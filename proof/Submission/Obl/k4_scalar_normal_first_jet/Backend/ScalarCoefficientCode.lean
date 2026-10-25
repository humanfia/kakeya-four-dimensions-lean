/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarCoefficientCode.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarCoefficientCode.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarMotion
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarGridGeometry
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-! The actual five displayed coefficient bins, in original coefficient order. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set

def scalarCoefficientVector {Λ : Type*} [MeasurableSpace Λ]
    (D : ScalarMotion Λ) (l : Λ) : Fin 5 → ℝ :=
  ![D.y₀ l, D.y₁ l, D.x₀ l, D.x₁ l, D.x₂ l]

noncomputable def scalarCoefficientCode {Λ : Type*} [MeasurableSpace Λ]
    (D : ScalarMotion Λ) (r : ℝ) (l : Λ) : Fin 5 → ℤ :=
  fun i => ⌊scalarCoefficientVector D l i / r⌋

theorem scalarCoefficientCode_measurable {Λ : Type*} [MeasurableSpace Λ]
    (D : ScalarMotion Λ) (r : ℝ) : Measurable (scalarCoefficientCode D r) := by
  apply measurable_pi_lambda
  intro i
  fin_cases i
  · exact (D.measurable_y₀.div_const r).floor
  · exact (D.measurable_y₁.div_const r).floor
  · exact (D.measurable_x₀.div_const r).floor
  · exact (D.measurable_x₁.div_const r).floor
  · exact (D.measurable_x₂.div_const r).floor

theorem scalarCoefficientCode_close {Λ : Type*} [MeasurableSpace Λ]
    (D : ScalarMotion Λ) {r : ℝ} (hr : 0 < r) {l l' : Λ}
    (he : scalarCoefficientCode D r l = scalarCoefficientCode D r l') :
    |D.y₀ l - D.y₀ l'| ≤ r ∧ |D.y₁ l - D.y₁ l'| ≤ r ∧
      |D.x₀ l - D.x₀ l'| ≤ r ∧ |D.x₁ l - D.x₁ l'| ≤ r ∧ |D.x₂ l - D.x₂ l'| ≤ r := by
  have hcoord i : |scalarCoefficientVector D l i - scalarCoefficientVector D l' i| ≤ r :=
    same_mesh_cell_close hr (congrFun he i)
  exact ⟨by simpa [scalarCoefficientVector] using hcoord 0,
    by simpa [scalarCoefficientVector] using hcoord 1,
    by simpa [scalarCoefficientVector] using hcoord 2,
    by simpa [scalarCoefficientVector] using hcoord 3,
    by simpa [scalarCoefficientVector] using hcoord 4⟩

theorem scalarCoefficientCode_position_close {Λ : Type*} [MeasurableSpace Λ]
    (D : ScalarMotion Λ) {r t : ℝ} (hr : 0 < r) (ht : t ∈ Icc (0 : ℝ) 1) {l l' : Λ}
    (he : scalarCoefficientCode D r l = scalarCoefficientCode D r l') :
    |D.x l t - D.x l' t| ≤ 3 * r ∧ |D.y l t - D.y l' t| ≤ 2 * r := by
  obtain ⟨hy₀, hy₁, hx₀, hx₁, hx₂⟩ := scalarCoefficientCode_close D hr he
  have ht1 : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  have ht2 : |t ^ 2| ≤ 1 := by rw [abs_of_nonneg (sq_nonneg t)]; nlinarith [ht.1, ht.2]
  have hxt : |(D.x₁ l - D.x₁ l') * t| ≤ r := by
    rw [abs_mul]
    exact (mul_le_mul hx₁ ht1 (abs_nonneg t) hr.le).trans_eq (mul_one _)
  have hxt₂ : |(D.x₂ l - D.x₂ l') * t ^ 2| ≤ r := by
    rw [abs_mul]
    exact (mul_le_mul hx₂ ht2 (abs_nonneg _) hr.le).trans_eq (mul_one _)
  have hyt : |(D.y₁ l - D.y₁ l') * t| ≤ r := by
    rw [abs_mul]
    exact (mul_le_mul hy₁ ht1 (abs_nonneg t) hr.le).trans_eq (mul_one _)
  constructor
  · have heq : D.x l t - D.x l' t = (D.x₀ l - D.x₀ l') +
        (D.x₁ l - D.x₁ l') * t + (D.x₂ l - D.x₂ l') * t ^ 2 := by dsimp [ScalarMotion.x]; ring
    rw [heq]
    exact ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans (by linarith)
  · have heq : D.y l t - D.y l' t = (D.y₀ l - D.y₀ l') + (D.y₁ l - D.y₁ l') * t := by
      dsimp [ScalarMotion.y]
      ring
    rw [heq]
    exact (abs_add_le _ _).trans (by linarith)

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
