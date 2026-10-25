-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.EStages
import Submission.Lib.K4XInterface.Charts

namespace Submission.Obl.k4_finite_affine_parent_sources

open Submission.Lib.K4XInterface

noncomputable section

/-- A true packet can be centered at any assigned representative. Its five
rows are then bounded using the parent coefficient bound and the relative
shear bound, without any bound on absolute old chart centers. -/
theorem tilted_label_from_relative_frame
    {α : Type} (b : α → Fin 6 → ℝ) (A : Set α) (l₀ : α) (hl₀ : l₀ ∈ A)
    (T : ℕ) (j : Fin (2 ^ T))
    (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : M.det ≠ 0)
    (center speed : EuclideanSpace ℝ (Fin 2)) (κ K K₀ Λ g : ℝ)
    (hκ : 0 ≤ κ) (hK₀ : 0 ≤ K₀) (hΛ : 0 ≤ Λ)
    (hrow : 0 < M 0 0 ^ 2 + M 0 1 ^ 2)
    (hfit : ∀ l ∈ A, ∀ t ∈ IS T j,
      ‖Matrix.toEuclideanLin M⁻¹ (gy (0, b l) t - center - t • speed)‖ ≤ κ)
    (hcoeff : |b l₀ 0| ≤ K₀ ∧ |b l₀ 1| ≤ K₀ ∧ |b l₀ 3| ≤ K₀ ∧ |b l₀ 4| ≤ K₀)
    (hlam : |(M 1 0 * M 0 0 + M 1 1 * M 0 1) /
      (M 0 0 ^ 2 + M 0 1 ^ 2)| ≤ Λ)
    (hK : K₀ * (1 + Λ) ≤ K) (hΛK : Λ ≤ K)
    (hmaj : 2 * κ * Real.sqrt (M 0 0 ^ 2 + M 0 1 ^ 2) ≤ K / (2 : ℝ) ^ T)
    (hmin : 4 * κ * Real.sqrt (M.det ^ 2 / (M 0 0 ^ 2 + M 0 1 ^ 2)) ≤
      K / (2 : ℝ) ^ T * g) :
    ∃ c : Fin 5 → ℝ, (∀ e, |c e| ≤ K) ∧
      ∀ l ∈ A,
        (∀ t ∈ IS T j,
          |(exS b l t) 1 - c 0 - t * c 1| ≤ K / (2 : ℝ) ^ T ∧
          |(exS b l t) 2 - c 2 - t * c 3 - c 4 * (exS b l t) 1| ≤
            K / (2 : ℝ) ^ T * g) ∧
        |b l 4 - c 3 - c 4 * b l 3| ≤ K * g := by
  let lam := (M 1 0 * M 0 0 + M 1 1 * M 0 1) / (M 0 0 ^ 2 + M 0 1 ^ 2)
  let c : Fin 5 → ℝ := ![b l₀ 0, b l₀ 3, b l₀ 1 - lam * b l₀ 0,
    b l₀ 4 - lam * b l₀ 3, lam]
  have hcoefK : K₀ ≤ K := by
    have h := mul_nonneg hK₀ hΛ
    nlinarith only [h, hK]
  have hdiff₀ : |b l₀ 1 - lam * b l₀ 0| ≤ K := by
    calc
      _ ≤ |b l₀ 1| + |lam| * |b l₀ 0| := by simpa only [abs_mul] using abs_sub (b l₀ 1) (lam * b l₀ 0)
      _ ≤ K₀ + Λ * K₀ := add_le_add hcoeff.2.1 (mul_le_mul hlam hcoeff.1 (abs_nonneg _) hΛ)
      _ ≤ K := by nlinarith only [hK]
  have hdiff₁ : |b l₀ 4 - lam * b l₀ 3| ≤ K := by
    calc
      _ ≤ |b l₀ 4| + |lam| * |b l₀ 3| := by simpa only [abs_mul] using abs_sub (b l₀ 4) (lam * b l₀ 3)
      _ ≤ K₀ + Λ * K₀ := add_le_add hcoeff.2.2.2 (mul_le_mul hlam hcoeff.2.2.1 (abs_nonneg _) hΛ)
      _ ≤ K := by nlinarith only [hK]
  refine ⟨c, ?_, fun l hl => ?_⟩
  · intro e
    fin_cases e
    · exact hcoeff.1.trans hcoefK
    · exact hcoeff.2.2.1.trans hcoefK
    · exact hdiff₀
    · exact hdiff₁
    · exact hlam.trans hΛK
  have hdiff (t : ℝ) (ht : t ∈ IS T j) :
      ‖Matrix.toEuclideanLin M⁻¹ (gy (0, b l) t - gy (0, b l₀) t)‖ ≤ 2 * κ := by
    have heq : gy (0, b l) t - gy (0, b l₀) t =
        (gy (0, b l) t - center - t • speed) -
          (gy (0, b l₀) t - center - t • speed) := by abel
    rw [heq, map_sub]
    exact (norm_sub_le _ _).trans ((add_le_add (hfit l hl t ht) (hfit l₀ hl₀ t ht)).trans_eq (by ring))
  have hvel (l : α) (hl : l ∈ A) :
      ‖Matrix.toEuclideanLin M⁻¹ (gv (0, b l) - speed)‖ ≤ 2 * κ * (2 : ℝ) ^ T := by
    have hq : (0 : ℝ) < (2 : ℝ) ^ T := by positivity
    have hlt : (j : ℝ) / (2 : ℝ) ^ T < ((j : ℝ) + 1) / (2 : ℝ) ^ T :=
      div_lt_div_of_pos_right (by linarith) hq
    have h := velocity_le_of_two_times M center speed (0, b l) hlt
      (hfit l hl _ ⟨le_rfl, hlt.le⟩) (hfit l hl _ ⟨hlt.le, le_rfl⟩)
    have heq : ((j : ℝ) + 1) / (2 : ℝ) ^ T - (j : ℝ) / (2 : ℝ) ^ T =
        ((2 : ℝ) ^ T)⁻¹ := by ring
    rw [heq] at h
    simpa only [div_inv_eq_mul] using h
  have hveldiff : ‖Matrix.toEuclideanLin M⁻¹ (gv (0, b l) - gv (0, b l₀))‖ ≤
      4 * κ * (2 : ℝ) ^ T := by
    have heq : gv (0, b l) - gv (0, b l₀) =
        (gv (0, b l) - speed) - (gv (0, b l₀) - speed) := by abel
    rw [heq, map_sub]
    exact (norm_sub_le _ _).trans ((add_le_add (hvel l hl) (hvel l₀ hl₀)).trans_eq (by ring))
  constructor
  · intro t ht
    have h := tilted_box_of_frame M hM (gy (0, b l) t - gy (0, b l₀) t) (hdiff t ht) hrow
    have hp₀ : |(exS b l t) 1 - c 0 - t * c 1| =
        |(gy (0, b l) t - gy (0, b l₀) t) 0| := by
      congr 1
      simp [exS, c, gy, gx, PiLp.sub_apply]
      ring
    have hp₁ : |(exS b l t) 2 - c 2 - t * c 3 - c 4 * (exS b l t) 1| =
        |(gy (0, b l) t - gy (0, b l₀) t) 1 - lam *
          (gy (0, b l) t - gy (0, b l₀) t) 0| := by
      congr 1
      simp [exS, c, gy, gx, PiLp.sub_apply]
      ring
    rw [hp₀, hp₁]
    refine ⟨h.1.trans hmaj, h.2.trans ?_⟩
    exact (mul_le_mul_of_nonneg_right (by linarith : 2 * κ ≤ 4 * κ) (Real.sqrt_nonneg _)).trans hmin
  · have h := tilted_box_of_frame M hM (gv (0, b l) - gv (0, b l₀)) hveldiff hrow
    have heq : |b l 4 - c 3 - c 4 * b l 3| =
        |(gv (0, b l) - gv (0, b l₀)) 1 - lam * (gv (0, b l) - gv (0, b l₀)) 0| := by
      congr 1
      simp [c, gv, PiLp.sub_apply]
      ring
    rw [heq]
    apply h.2.trans
    calc
      _ = (4 * κ * Real.sqrt (M.det ^ 2 / (M 0 0 ^ 2 + M 0 1 ^ 2))) * (2 : ℝ) ^ T := by ring
      _ ≤ (K / (2 : ℝ) ^ T * g) * (2 : ℝ) ^ T :=
        mul_le_mul_of_nonneg_right hmin (by positivity)
      _ = K * g := by field_simp

end

end Submission.Obl.k4_finite_affine_parent_sources
