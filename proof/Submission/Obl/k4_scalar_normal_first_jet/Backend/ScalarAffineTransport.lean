/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarAffineTransport.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarAffineTransport.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarBlockTime
import Submission.Obl.k4_scalar_normalized_exact_refinement.Transport
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Transport normalized scalar affine fits to their original time block. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set

theorem scalar_affine_image_volume {U : Set ℝ} (hU : MeasurableSet U)
    (c : ℝ) {H : ℝ} (hH : 0 < H) :
    MeasurableSet ((fun u => c + H * u) '' U) ∧
      volume ((fun u => c + H * u) '' U) = ENNReal.ofReal H * volume U := by
  let e := Submission.Obl.k4_scalar_normalized_exact_refinement.timeEquiv c H hH.ne'
  have heq : e ⁻¹' U = (fun u => c + H * u) '' U := by
    ext t
    rw [mem_preimage, Submission.Obl.k4_scalar_normalized_exact_refinement.timeEquiv_apply]
    constructor
    · intro ht
      refine ⟨(t - c) / H, ht, ?_⟩
      field_simp
      ring
    · rintro ⟨u, hu, rfl⟩
      simpa only [add_sub_cancel_left, mul_div_cancel_left₀ u hH.ne'] using hu
  refine ⟨by rw [← heq]; exact hU.preimage e.measurable, ?_⟩
  rw [← heq, ← Measure.map_apply e.measurable hU,
    Submission.Obl.k4_scalar_normalized_exact_refinement.map_timeEquiv c H hH,
    Measure.smul_apply]
  rfl

theorem original_affine_fit_transport {U : Set ℝ} (hU : MeasurableSet U)
    (F : ℝ → ℝ) (c a b : ℝ) {H L error ell : ℝ} (hH : 0 < H) (hL : 0 < L)
    (hvol : ENNReal.ofReal ell ≤ volume U)
    (hfit : ∀ u ∈ U, |(F (c + H * u) - F c) / (H * L) - (a + b * u)| ≤ error) :
    MeasurableSet ((fun u => c + H * u) '' U) ∧
      ENNReal.ofReal (H * ell) ≤ volume ((fun u => c + H * u) '' U) ∧
      ∀ t ∈ (fun u => c + H * u) '' U,
        |F t - ((F c + H * L * a - L * b * c) + (L * b) * t)| ≤ H * L * error := by
  obtain ⟨hVm, hVvol⟩ := scalar_affine_image_volume hU c hH
  refine ⟨hVm, ?_, ?_⟩
  · rw [hVvol, ENNReal.ofReal_mul hH.le]
    exact mul_le_mul_right hvol _
  · rintro t ⟨u, hu, rfl⟩
    have h := mul_le_mul_of_nonneg_left (hfit u hu) (mul_pos hH hL).le
    have he : F (c + H * u) - ((F c + H * L * a - L * b * c) + (L * b) * (c + H * u)) =
        (H * L) * ((F (c + H * u) - F c) / (H * L) - (a + b * u)) := by
      field_simp
      ring
    rw [he, abs_mul, abs_of_pos (mul_pos hH hL)]
    exact h

theorem original_affine_fit_coefficients {F₀ c a b H L K : ℝ}
    (hH : 0 ≤ H) (hH1 : H ≤ 1) (hL : 0 ≤ L) (hF : |F₀| ≤ K)
    (hc : |c| ≤ 1) (ha : |a| ≤ 9) (hb : |b| ≤ 4) :
    |L * b| ≤ 4 * L ∧ |F₀ + H * L * a - L * b * c| ≤ K + 13 * L := by
  have hslope : |L * b| ≤ 4 * L := by
    rw [abs_mul, abs_of_nonneg hL]
    nlinarith [mul_le_mul_of_nonneg_left hb hL]
  refine ⟨hslope, ?_⟩
  have haerr : |H * L * a| ≤ 9 * L := by
    rw [abs_mul, abs_of_nonneg (mul_nonneg hH hL)]
    have h₁ := mul_le_mul_of_nonneg_left ha (mul_nonneg hH hL)
    have h₂ := mul_le_mul_of_nonneg_right hH1 hL
    nlinarith
  have hberr : |L * b * c| ≤ 4 * L := by
    rw [abs_mul]
    exact (mul_le_mul hslope hc (abs_nonneg _) (by positivity)).trans_eq (mul_one _)
  exact ((abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans (by linarith)

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
