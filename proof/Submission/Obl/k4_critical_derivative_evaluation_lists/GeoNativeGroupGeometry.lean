import Submission.Obl.k4_critical_derivative_evaluation_lists.GeoContinuousJointCap
import Submission.Obl.k4_critical_derivative_evaluation_lists.GeoAffineDefs
import Submission.Obl.k4_scalar_coefficient_clustering.Evaluation

/- Adapted from this LOT tree, obligation o107, session x0353, commit 96bcaa7b51cc,
   file Submission/Obl/k4_finite_narrowness_path_improvement/NativeGroupGeometry.lean (namespace and imports renamed only). -/

/-! Fine velocity/initial-position groups lie in moving contact rectangles.
An occurring coefficient-ball center of an affine family is almost affine. -/

namespace Submission.Obl.k4_critical_derivative_evaluation_lists

noncomputable section

open Submission.Obl.k4_scalar_coefficient_clustering

theorem native_group_mem_contact_rectangle
    (b : Fin 6 → ℝ) (p : Fin 3 → ℝ) (m H D t : ℝ) (hD : 0 ≤ D)
    (hm : |m| ≤ 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) (htime : |t - m| ≤ H / 2)
    (hZ₀ : |b 0 - p 0| ≤ D) (hY₀ : |b 1 - p 1| ≤ D)
    (hvel : |b 3 - p 2| ≤ D) (hdef : |b 4 + b 0| ≤ D) :
    nativeHorizontalLine b t ∈ contactOuterBox m p H (2 * D) (5 * D) := by
  have ht1 : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
  have hZ : |(b 0 + t * b 3) - referenceZ p t| ≤ 2 * D := by
    calc
      _ = |(b 0 - p 0) + t * (b 3 - p 2)| := by unfold referenceZ; congr 1; ring
      _ ≤ |b 0 - p 0| + |t * (b 3 - p 2)| := abs_add_le _ _
      _ ≤ D + 1 * D := add_le_add hZ₀ (by
        rw [abs_mul]
        exact mul_le_mul ht1 hvel (abs_nonneg _) zero_le_one)
      _ = _ := by ring
  have hY : |(b 1 + t * b 4) - referenceY p t| ≤ 3 * D := by
    calc
      _ = |(b 1 - p 1) + t * ((b 4 + b 0) - (b 0 - p 0))| := by
        unfold referenceY; congr 1; ring
      _ ≤ |b 1 - p 1| + |t * ((b 4 + b 0) - (b 0 - p 0))| := abs_add_le _ _
      _ ≤ D + 1 * (D + D) := by
        apply add_le_add hY₀
        rw [abs_mul]
        exact mul_le_mul ht1 ((abs_sub _ _).trans (add_le_add hdef hZ₀))
          (abs_nonneg _) zero_le_one
      _ = _ := by ring
  apply (mem_contactOuterBox_iff _ _ _ _ _ _).mpr
  refine ⟨htime, hZ, ?_⟩
  change |(b 1 + t * b 4) - referenceY p t - m * ((b 0 + t * b 3) - referenceZ p t)| ≤ 5 * D
  calc
    _ ≤ |(b 1 + t * b 4) - referenceY p t| +
      |m * ((b 0 + t * b 3) - referenceZ p t)| := abs_sub _ _
    _ ≤ 3 * D + 1 * (2 * D) := add_le_add hY (by
      rw [abs_mul]
      exact mul_le_mul hm hZ (abs_nonneg _) zero_le_one)
    _ = _ := by ring

theorem affine_family_coefficient_ball_center
    {α : Type*} (a : α → Coeff) (c : Coeff) (K r : ℝ)
    (hnorm : ∀ l, ‖a l‖ ≤ K) (haffine : ∀ l, a l 2 = 0)
    (hex : ∃ l, a l ∈ Metric.ball c r) :
    ‖c‖ ≤ K + r ∧ |c 2| ≤ r := by
  obtain ⟨l, hl⟩ := hex
  have hdist : ‖a l - c‖ < r := by simpa only [Metric.mem_ball, dist_eq_norm] using hl
  constructor
  · calc
      _ = ‖(c - a l) + a l‖ := by rw [sub_add_cancel]
      _ ≤ ‖c - a l‖ + ‖a l‖ := norm_add_le _ _
      _ ≤ r + K := add_le_add (by rw [norm_sub_rev]; exact hdist.le) (hnorm l)
      _ = _ := by ring
  · have hh := PiLp.norm_apply_le (a l - c) 2
    simp only [Real.norm_eq_abs] at hh
    have heq : |(a l - c) 2| = |c 2| := by simp only [PiLp.sub_apply, haffine, zero_sub, abs_neg]
    rw [heq] at hh
    exact hh.trans hdist.le

theorem quadratic_band_to_affine_center (c : Coeff) (t x r : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hc : |c 2| ≤ r)
    (hband : |x - quadratic c t| ≤ 3 * r) :
    |x - (c 0 + t * c 1)| ≤ 4 * r := by
  have htsq : |t ^ 2| ≤ 1 := by rw [abs_of_nonneg (sq_nonneg _)]; nlinarith [ht.1, ht.2]
  have hgap : |quadratic c t - (c 0 + t * c 1)| ≤ r := by
    change |c 0 + t * c 1 + t ^ 2 * c 2 - (c 0 + t * c 1)| ≤ r
    rw [add_sub_cancel_left, abs_mul]
    simpa only [one_mul] using mul_le_mul htsq hc (abs_nonneg _) zero_le_one
  exact (abs_sub_le _ _ _).trans ((add_le_add hband hgap).trans_eq (by ring))

def shiftedNativeAffine (L : Fin 4 → ℝ) (c : Coeff) : Fin 4 → ℝ :=
  ![L 0 + c 0, L 1 + c 1, L 2, L 3]

theorem native_affine_band_residual_identity (L : Fin 4 → ℝ) (c : Coeff)
    (b : Fin 6 → ℝ) (t : ℝ) :
    (b 2 + t * b 5) - affineBaseEval (shiftedNativeAffine L c) (nativeHorizontalLine b t) =
      (affineResidualIntercept L b + t * affineResidualSlope L b) - (c 0 + t * c 1) := by
  dsimp [affineBaseEval, shiftedNativeAffine, nativeHorizontalLine,
    affineResidualIntercept, affineResidualSlope]
  ring

theorem shiftedNativeAffine_slope_bound (L : Fin 4 → ℝ) (c : Coeff) (K r : ℝ)
    (hK : 1 ≤ K) (hr : r ≤ 1) (hc : ‖c‖ ≤ K + r)
    (hL : ∀ i : Fin 3, |L i.succ| ≤ K) :
    ∀ i : Fin 3, |shiftedNativeAffine L c i.succ| ≤ 3 * K := by
  have hc1 : |c 1| ≤ K + 1 := (PiLp.norm_apply_le c 1).trans (hc.trans (by linarith))
  have hL1 : |L 1| ≤ K := hL 0
  have hL2 : |L 2| ≤ K := hL 1
  have hL3 : |L 3| ≤ K := hL 2
  intro i
  fin_cases i
  · change |L 1 + c 1| ≤ 3 * K
    exact (abs_add_le _ _).trans (by linarith)
  · change |L 2| ≤ 3 * K
    linarith
  · change |L 3| ≤ 3 * K
    linarith

end

end Submission.Obl.k4_critical_derivative_evaluation_lists
