/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarCoefficientObservations.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarCoefficientObservations.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarCoefficientCode
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarFirstJetValue

/-! Coefficient bins give fixed short scalar and first-jet output lists. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set

theorem scalarCoefficientCode_observations_close {Λ : Type*} [MeasurableSpace Λ]
    (D : ScalarMotion Λ) {F A : ℝ → ℝ} {r t K : ℝ} (hr : 0 < r)
    (ht : t ∈ Icc (0 : ℝ) 1) (hK : 1 ≤ K) (hF : |F t| ≤ K) (hA : |A t| ≤ K)
    {l l' : Λ} (he : scalarCoefficientCode D r l = scalarCoefficientCode D r l') :
    |D.scalar F l t - D.scalar F l' t| ≤ 5 * K * r ∧
      |scalarFirstJet D F A l t - scalarFirstJet D F A l' t| ≤ 6 * K * r := by
  obtain ⟨hy₀, hy₁, hx₀, hx₁, hx₂⟩ := scalarCoefficientCode_close D hr he
  obtain ⟨hx, hy⟩ := scalarCoefficientCode_position_close D hr ht he
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have ht1 : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  have hKr : r ≤ K * r := by nlinarith
  have hFy : |F t * (D.y l t - D.y l' t)| ≤ K * (2 * r) := by
    rw [abs_mul]
    exact mul_le_mul hF hy (abs_nonneg _) hK0
  have hFy₁ : |F t * (D.y₁ l - D.y₁ l')| ≤ K * r := by
    rw [abs_mul]
    exact mul_le_mul hF hy₁ (abs_nonneg _) hK0
  have hAy : |A t * (D.y l t - D.y l' t)| ≤ K * (2 * r) := by
    rw [abs_mul]
    exact mul_le_mul hA hy (abs_nonneg _) hK0
  have hx₂t : |2 * (D.x₂ l - D.x₂ l') * t| ≤ 2 * r := by
    have hh : |(D.x₂ l - D.x₂ l') * t| ≤ r := by
      rw [abs_mul]
      exact (mul_le_mul hx₂ ht1 (abs_nonneg t) hr.le).trans_eq (mul_one _)
    rw [mul_assoc, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left hh (by norm_num)
  constructor
  · have heq : D.scalar F l t - D.scalar F l' t =
        (D.x l t - D.x l' t) - F t * (D.y l t - D.y l' t) := by dsimp [ScalarMotion.scalar]; ring
    rw [heq]
    exact (abs_sub _ _).trans (by linarith)
  · have heq : scalarFirstJet D F A l t - scalarFirstJet D F A l' t =
        (D.x₁ l - D.x₁ l') + 2 * (D.x₂ l - D.x₂ l') * t -
          F t * (D.y₁ l - D.y₁ l') - A t * (D.y l t - D.y l' t) := by
      dsimp [scalarFirstJet, ScalarMotion.residual]
      ring
    rw [heq]
    have htri : |(D.x₁ l - D.x₁ l') + 2 * (D.x₂ l - D.x₂ l') * t -
        F t * (D.y₁ l - D.y₁ l') - A t * (D.y l t - D.y l' t)| ≤
        |D.x₁ l - D.x₁ l'| + |2 * (D.x₂ l - D.x₂ l') * t| +
          |F t * (D.y₁ l - D.y₁ l')| + |A t * (D.y l t - D.y l' t)| :=
      ((abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)).trans
        (add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl)
    exact htri.trans (by linarith)

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
