/- Adapted from this LOT tree, o197, session x0690, Packing/Geometry.lean,
   branch snapshot 9f1b6476; preserving original attributions below. -/
import Submission.Obl.k4_raw_localized_native_systems.Packing.BaseVolume
import Submission.Obl.k4_raw_localized_native_systems.Pairing.OperatorNorm

namespace Submission.Obl.k4_raw_localized_native_systems.Packing

open Submission.Obl.k4_finite_width_output_exclusion
open Pairing

noncomputable section

theorem abs_inner_of_projective_close {n m z : Plane} {θ B : ℝ}
    (hangle : min ‖n - m‖ ‖n + m‖ ≤ θ) (hz : |inner ℝ m z| ≤ B) :
    |inner ℝ n z| ≤ B + θ * ‖z‖ := by
  rcases min_le_iff.mp hangle with h | h
  · have he : inner ℝ n z = inner ℝ m z + inner ℝ (n - m) z := by
      rw [inner_sub_left]; ring
    rw [he]
    exact (abs_add_le _ _).trans (add_le_add hz
      ((abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right h (norm_nonneg _))))
  · have he : inner ℝ n z = -inner ℝ m z + inner ℝ (n + m) z := by
      rw [inner_add_left]; ring
    rw [he]
    exact (abs_add_le _ _).trans (add_le_add (by simpa only [abs_neg] using hz)
      ((abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right h (norm_nonneg _))))

theorem normal_image_aligned {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0)
    {n : Plane} {θ : ℝ}
    (hangle : min ‖n - minorNormal Q‖ ‖n + minorNormal Q‖ ≤ θ) (w : Plane) :
    |inner ℝ n (Matrix.toEuclideanLin Q w)| ≤
      (minorWidth Q + 2 * ‖longCol Q‖ * θ) * ‖w‖ := by
  have hθ : 0 ≤ θ := (le_min (norm_nonneg _) (norm_nonneg _)).trans hangle
  have h := abs_inner_of_projective_close hangle (abs_inner_minorNormal_le hQ w)
  calc
    _ ≤ minorWidth Q * ‖w‖ + θ * ‖Matrix.toEuclideanLin Q w‖ := h
    _ ≤ minorWidth Q * ‖w‖ + θ * (2 * ‖longCol Q‖ * ‖w‖) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (norm_toEuclideanLin_le_longCol Q w) hθ)
    _ = _ := by ring

/-- Every selected point of an earlier chart stays in a common enlargement of
the window touched by that chart. The enlargement charges full witness mass. -/
theorem earlier_frame_displacement {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0)
    {n z z₀ c u : Plane} {t t₀ α β κ q U V θ r₀ : ℝ}
    (hangle : min ‖n - minorNormal Q‖ ‖n + minorNormal Q‖ ≤ θ)
    (hfit : ‖Matrix.toEuclideanLin Q⁻¹ (z - c - t • u)‖ ≤ κ)
    (hfit₀ : ‖Matrix.toEuclideanLin Q⁻¹ (z₀ - c - t₀ • u)‖ ≤ κ)
    (ht : |t - t₀| ≤ q) (hU : ‖u‖ ≤ U)
    (hV : |inner ℝ (u - β • n) n| ≤ V)
    (h₀ : |inner ℝ (z₀ - α • n - t₀ • (β • n)) n| ≤ r₀) :
    ‖z - z₀‖ ≤ 4 * κ * ‖longCol Q‖ + q * U ∧
    |inner ℝ (z - α • n - t • (β • n)) n| ≤
      r₀ + 2 * κ * (minorWidth Q + 2 * ‖longCol Q‖ * θ) + q * V := by
  let d := (z - c - t • u) - (z₀ - c - t₀ • u)
  have hd : ‖Matrix.toEuclideanLin Q⁻¹ d‖ ≤ 2 * κ := by
    rw [show Matrix.toEuclideanLin Q⁻¹ d =
      Matrix.toEuclideanLin Q⁻¹ (z - c - t • u) -
        Matrix.toEuclideanLin Q⁻¹ (z₀ - c - t₀ • u) from map_sub _ _ _]
    exact (norm_sub_le _ _).trans (by linarith only [hfit, hfit₀])
  have hκ : 0 ≤ κ := (norm_nonneg _).trans hfit
  have hθ : 0 ≤ θ := (le_min (norm_nonneg _) (norm_nonneg _)).trans hangle
  have hf : 0 ≤ minorWidth Q + 2 * ‖longCol Q‖ * θ := by
    exact add_nonneg (minorWidth_nonneg Q) (by positivity)
  have he : d = Matrix.toEuclideanLin Q (Matrix.toEuclideanLin Q⁻¹ d) :=
    (Submission.Lib.K4XInterface.toEuclideanLin_inv_cancel Q hQ d).symm
  have hdspace : ‖d‖ ≤ 4 * κ * ‖longCol Q‖ := by
    rw [he]
    exact (norm_toEuclideanLin_le_longCol Q _).trans (by
      nlinarith [mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 2 * ‖longCol Q‖)])
  have hdnormal : |inner ℝ d n| ≤ 2 * κ *
      (minorWidth Q + 2 * ‖longCol Q‖ * θ) := by
    rw [real_inner_comm, he]
    exact (normal_image_aligned hQ hangle _).trans (by
      nlinarith [mul_le_mul_of_nonneg_left hd hf])
  have hdiff : z - z₀ = d + (t - t₀) • u := by dsimp [d]; module
  constructor
  · rw [hdiff]
    calc
      _ ≤ ‖d‖ + ‖(t - t₀) • u‖ := norm_add_le _ _
      _ = ‖d‖ + |t - t₀| * ‖u‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ _ := add_le_add hdspace (mul_le_mul ht hU (norm_nonneg _) ((abs_nonneg _).trans ht))
  · have hsplit : z - α • n - t • (β • n) =
        (z₀ - α • n - t₀ • (β • n)) + d + (t - t₀) • (u - β • n) := by
      dsimp [d]
      module
    rw [hsplit, inner_add_left, inner_add_left, real_inner_smul_left]
    calc
      _ ≤ |inner ℝ (z₀ - α • n - t₀ • (β • n)) n| + |inner ℝ d n| +
          |(t - t₀) * inner ℝ (u - β • n) n| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ _ := by
        rw [abs_mul]
        exact add_le_add (add_le_add h₀ hdnormal)
          (mul_le_mul ht hV (abs_nonneg _) ((abs_nonneg _).trans ht))

theorem earlier_base_mem_scalarWindowTube {Q : Matrix (Fin 2) (Fin 2) ℝ}
    (hQ : Q.det ≠ 0) {n c u : Plane} (hn : ‖n‖ = 1)
    {b b₀ : EuclideanSpace ℝ (Fin 3)} {α β κ q U V θ r₀ t y σ rt ry rn : ℝ}
    (hangle : min ‖n - minorNormal Q‖ ‖n + minorNormal Q‖ ≤ θ)
    (hfit : ‖Matrix.toEuclideanLin Q⁻¹ (basePlane b - c - b 0 • u)‖ ≤ κ)
    (hfit₀ : ‖Matrix.toEuclideanLin Q⁻¹ (basePlane b₀ - c - b₀ 0 • u)‖ ≤ κ)
    (ht : |b 0 - b₀ 0| ≤ q) (hU : ‖u‖ ≤ U)
    (hV : |inner ℝ (u - β • n) n| ≤ V)
    (h₀ : |inner ℝ (basePlane b₀ - α • n - b₀ 0 • (β • n)) n| ≤ r₀)
    (ht₀ : |b₀ 0 - t| ≤ σ)
    (hy₀ : |inner ℝ (basePlane b₀) (tangentOfNormal n) - y| ≤ σ)
    (htbudget : q + σ ≤ rt)
    (hybudget : σ + 4 * κ * ‖longCol Q‖ + q * U ≤ ry)
    (hnbudget : r₀ + 2 * κ * (minorWidth Q + 2 * ‖longCol Q‖ * θ) + q * V ≤ rn)
    (hry : 0 < ry) (hrn : 0 < rn) :
    b ∈ scalarWindowTube n t y α β rt ry rn := by
  obtain ⟨hspace, hnormal⟩ := earlier_frame_displacement hQ hangle hfit hfit₀ ht hU hV h₀
  apply mem_scalarWindowTube hn hry hrn
  · exact ((abs_sub_le (b 0) (b₀ 0) t).trans (add_le_add ht ht₀)).trans htbudget
  · have htan : |inner ℝ (basePlane b) (tangentOfNormal n) -
        inner ℝ (basePlane b₀) (tangentOfNormal n)| ≤
        4 * κ * ‖longCol Q‖ + q * U := by
      rw [← inner_sub_left]
      exact (abs_real_inner_le_norm _ _).trans (by
        simpa only [tangentOfNormal_norm, hn, mul_one] using hspace)
    apply ((abs_sub_le _ _ y).trans (add_le_add htan hy₀)).trans
    linarith only [hybudget]
  · exact hnormal.trans hnbudget

end
end Submission.Obl.k4_raw_localized_native_systems.Packing
