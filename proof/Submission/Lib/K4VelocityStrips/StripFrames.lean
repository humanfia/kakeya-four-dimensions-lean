/-
Adapted from: here:o116

Original heavy-strip packing and frame proofs by session x0644.
-/

import Submission.Lib.K4FinitePlankAtlases.PlankFrame

/-! A velocity strip and one midpoint bin give a narrower whole-block frame.
The old quadratic test is unchanged by this purely spatial construction. -/

noncomputable section

namespace Submission.Lib.K4VelocityStrips

open scoped RealInnerProductSpace BigOperators

abbrev StripPlane := EuclideanSpace ℝ (Fin 2)

def stripCenter (n : StripPlane) (s β : ℝ) : StripPlane := (s - β / 2) • n

def stripVelocity (n : StripPlane) (β : ℝ) : StripPlane := β • n

def stripLocalFrame (K D r : ℝ) (e n : StripPlane) : Matrix (Fin 2) (Fin 2) ℝ :=
  Submission.Lib.K4FinitePlankAtlases.plankFrame K ((1 + D) * r) e n

/-- A strip in velocity and a midpoint-position bin confine the entire affine
trajectory, with only the incoming size and strip slack as losses. -/
theorem strip_whole_block_fit {K D r s β : ℝ} {a v e n : StripPlane}
    (hK : 0 < K) (hD : 0 ≤ D) (hr : 0 < r)
    (he : ‖e‖ = 1) (hn : ‖n‖ = 1) (hen : inner ℝ e n = 0)
    (hfit : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖a + t • v‖ ≤ K)
    (hvel : |inner ℝ v n - β| ≤ D * r)
    (hmid : |inner ℝ (a + (1 / 2 : ℝ) • v) n - s| ≤ r)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖Matrix.toEuclideanLin (stripLocalFrame K D r e n)⁻¹
      (a + t • v - stripCenter n s β - t • stripVelocity n β)‖ ≤ 2 := by
  have hne : inner ℝ n e = 0 := by rw [real_inner_comm, hen]
  have hnn : inner ℝ n n = 1 := by rw [real_inner_self_eq_norm_sq, hn]; norm_num
  apply Submission.Lib.K4FinitePlankAtlases.plankFrame_fit hK (by positivity) he hn hen
  · simpa only [stripCenter, stripVelocity, inner_sub_left, inner_smul_left,
      starRingEnd_apply, star_trivial, hne, mul_zero, sub_zero] using
      ((abs_real_inner_le_norm (a + t • v) e).trans (by simpa only [he, mul_one] using hfit t ht))
  · have hid :
        inner ℝ (a + t • v - stripCenter n s β - t • stripVelocity n β) n =
          (inner ℝ (a + (1 / 2 : ℝ) • v) n - s) +
            (t - 1 / 2) * (inner ℝ v n - β) := by
      simp only [stripCenter, stripVelocity, inner_sub_left, inner_add_left,
        inner_smul_left, starRingEnd_apply, star_trivial, hnn, mul_one]
      ring
    have htime : |t - (1 / 2 : ℝ)| ≤ 1 / 2 := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    rw [hid]
    calc
      _ ≤ |inner ℝ (a + (1 / 2 : ℝ) • v) n - s| +
          |t - 1 / 2| * |inner ℝ v n - β| := by
        simpa only [abs_mul] using abs_add_le
          (inner ℝ (a + (1 / 2 : ℝ) • v) n - s) ((t - 1 / 2) * (inner ℝ v n - β))
      _ ≤ r + (1 / 2) * (D * r) :=
        add_le_add hmid (mul_le_mul htime hvel (abs_nonneg _) (by norm_num))
      _ ≤ (1 + D) * r := by nlinarith

theorem stripLocalFrame_abs_det {K D r : ℝ} {e n : StripPlane}
    (hK : 0 < K) (hD : 0 ≤ D) (hr : 0 < r)
    (he : ‖e‖ = 1) (hn : ‖n‖ = 1) (hen : inner ℝ e n = 0) :
    |Matrix.det (stripLocalFrame K D r e n)| = K * (1 + D) * r := by
  simpa only [stripLocalFrame, mul_assoc] using
    (Submission.Lib.K4FinitePlankAtlases.plankFrame_abs_det hK
      (show 0 < (1 + D) * r by positivity) he hn hen)

/-- The determinant saving is exactly the strip width times the actual
geometric losses; there is no change to the time block. -/
theorem strip_composite_determinant (Q : Matrix (Fin 2) (Fin 2) ℝ) (T : ℕ)
    {K D r : ℝ} {e n : StripPlane} (hK : 0 < K) (hD : 0 ≤ D) (hr : 0 < r)
    (he : ‖e‖ = 1) (hn : ‖n‖ = 1) (hen : inner ℝ e n = 0) :
    |Matrix.det (Q * stripLocalFrame K D r e n)| * (4 : ℝ) ^ T =
      (|Matrix.det Q| * (4 : ℝ) ^ T) * (K * (1 + D) * r) := by
  rw [Matrix.det_mul, abs_mul, stripLocalFrame_abs_det hK hD hr he hn hen]
  ring

/-- The narrowed frame has a polynomial entry and inverse-entry budget. -/
theorem stripLocalFrame_entry_budget {K D r : ℝ} {e n : StripPlane}
    (hK : 0 < K) (hD : 0 ≤ D) (hr : 0 < r)
    (he : ‖e‖ = 1) (hn : ‖n‖ = 1) (hen : inner ℝ e n = 0) :
    (∑ i : Fin 2, ∑ j : Fin 2,
      (|stripLocalFrame K D r e n i j| + |(stripLocalFrame K D r e n)⁻¹ i j|)) ≤
      2 * (K + (1 + D) * r + K⁻¹ + ((1 + D) * r)⁻¹) :=
  Submission.Lib.K4FinitePlankAtlases.plankFrame_entry_budget hK (by positivity) he hn hen

end Submission.Lib.K4VelocityStrips
