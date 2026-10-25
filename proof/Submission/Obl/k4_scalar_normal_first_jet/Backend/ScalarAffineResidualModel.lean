/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarAffineResidualModel.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarAffineResidualModel.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarCoefficientObservations
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarLocalModel

/-! Actual affine row fits give the normalized residual-slope model. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

theorem original_affine_row_residual_model {Λ : Type*} [MeasurableSpace Λ]
    (D : ScalarMotion Λ) (F : ℝ → ℝ) (l : Λ) (c base a slope : ℝ)
    {H p K u : ℝ} (hH : 0 < H) (hHp : H ≤ p) (hp1 : p ≤ 1) (hK : 1 ≤ K)
    (hu : |u| ≤ 1) (ha₂ : |D.x₂ l| ≤ K) (hb₁ : |D.y₁ l| ≤ K)
    (hY : |D.y l c| ≤ 2 * K) (hslope : |slope| ≤ K)
    (hrow₀ : |F c - (a + slope * c)| ≤ K * H * p)
    (hrow : |F (c + H * u) - (a + slope * (c + H * u))| ≤ K * H * p) :
    |(D.scalar F l (c + H * u) - base) / H -
      ((D.scalar F l c - base) / H + u * (D.residual F l c - slope * D.y l c))| ≤ 16 * K ^ 2 * p ∧
    |scalarFirstJet D F (fun _ => slope) l (c + H * u) -
      scalarFirstJet D F (fun _ => slope) l c| ≤ 6 * K ^ 2 * H := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hK0 : 0 ≤ K := hKpos.le
  have hp : 0 < p := hH.trans_le hHp
  have hKsq : K ≤ K ^ 2 := by nlinarith
  let φ := (F (c + H * u) - F c) / H
  have hrowdiff : |F (c + H * u) - F c - H * u * slope| ≤ 2 * K * H * p := by
    have he : F (c + H * u) - F c - H * u * slope =
        (F (c + H * u) - (a + slope * (c + H * u))) - (F c - (a + slope * c)) := by ring
    rw [he]
    exact (abs_sub _ _).trans (by linarith)
  have hφerror : |φ - u * slope| ≤ 2 * K * p := by
    have he : φ - u * slope = (F (c + H * u) - F c - H * u * slope) / H := by
      dsimp [φ]
      field_simp <;> ring
    rw [he, abs_div, abs_of_pos hH]
    apply (div_le_iff₀ hH).mpr
    nlinarith
  have huSlope : |u * slope| ≤ K := by
    rw [abs_mul]
    exact (mul_le_mul hu hslope (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hφ : |φ| ≤ 3 * K := by
    have hh := abs_sub_le φ (u * slope) 0
    rw [sub_zero, sub_zero] at hh
    have hpK := mul_le_mul_of_nonneg_left hp1 (show 0 ≤ 2 * K by positivity)
    linarith
  have hquad : (D.scalar F l (c + H * u) - base) / H =
      (D.scalar F l c - base) / H + u * D.residual F l c - φ * D.y l c +
        H * (u ^ 2 * D.x₂ l - u * φ * D.y₁ l) := by
    simpa only [ScalarMotion.scalar, ScalarMotion.x, ScalarMotion.y, ScalarMotion.residual, φ] using
      quadratic_local_identity (D.x₀ l) (D.x₁ l) (D.x₂ l) (D.y₀ l) (D.y₁ l)
        c H (F c) base u (F (c + H * u)) hH.ne'
  have hlocal : |H * (u ^ 2 * D.x₂ l - u * φ * D.y₁ l)| ≤ 12 * K ^ 2 * H := by
    have hh := quadratic_local_error hH.le (show 0 ≤ 3 * K by positivity) hu
      (ha₂.trans (by linarith)) (hb₁.trans (by linarith)) hφ
    have hmul := mul_le_mul_of_nonneg_left hKsq hH.le
    nlinarith
  have hφY : |(φ - u * slope) * D.y l c| ≤ 4 * K ^ 2 * p := by
    rw [abs_mul]
    have hh := mul_le_mul hφerror hY (abs_nonneg _) (by positivity : 0 ≤ 2 * K * p)
    nlinarith
  constructor
  · have he : (D.scalar F l (c + H * u) - base) / H -
        ((D.scalar F l c - base) / H + u * (D.residual F l c - slope * D.y l c)) =
        H * (u ^ 2 * D.x₂ l - u * φ * D.y₁ l) - (φ - u * slope) * D.y l c := by
      rw [hquad]
      ring
    rw [he]
    have hh := mul_le_mul_of_nonneg_left hHp (show 0 ≤ 12 * K ^ 2 by positivity)
    exact (abs_sub _ _).trans (by linarith)
  · have he : scalarFirstJet D F (fun _ => slope) l (c + H * u) -
        scalarFirstJet D F (fun _ => slope) l c =
        H * (2 * u * D.x₂ l - u * slope * D.y₁ l - φ * D.y₁ l) := by
      dsimp [scalarFirstJet, ScalarMotion.residual, ScalarMotion.y, φ]
      field_simp <;> ring
    have hx : |2 * u * D.x₂ l| ≤ 2 * K := by
      rw [mul_assoc, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact mul_le_mul_of_nonneg_left
        (by simpa only [abs_mul, one_mul] using mul_le_mul hu ha₂ (abs_nonneg _) zero_le_one) (by norm_num)
    have hsy : |u * slope * D.y₁ l| ≤ K ^ 2 := by
      rw [abs_mul]
      have hh := mul_le_mul huSlope hb₁ (abs_nonneg _) hK0
      nlinarith
    have hφy : |φ * D.y₁ l| ≤ 3 * K ^ 2 := by
      rw [abs_mul]
      have hh := mul_le_mul hφ hb₁ (abs_nonneg _) (show 0 ≤ 3 * K by positivity)
      nlinarith
    have hinside : |2 * u * D.x₂ l - u * slope * D.y₁ l - φ * D.y₁ l| ≤ 6 * K ^ 2 :=
      ((abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)).trans (by linarith)
    rw [he, abs_mul, abs_of_pos hH]
    have hh := mul_le_mul_of_nonneg_left hinside hH.le
    nlinarith

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
