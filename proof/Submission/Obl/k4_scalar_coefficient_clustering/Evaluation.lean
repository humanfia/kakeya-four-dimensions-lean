import Submission.Obl.k4_scalar_coefficient_clustering.Bins
import Submission.Obl.k4_scalar_coefficient_clustering.TimeBins

namespace Submission.Obl.k4_scalar_coefficient_clustering

open Submission.Lib.K4PlankGeometry (binTime)

noncomputable section

theorem quadratic_difference_le {a b : Coeff} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |quadratic a t - quadratic b t| ≤ 3 * ‖a - b‖ := by
  have h0 : |a 0 - b 0| ≤ ‖a - b‖ := PiLp.norm_apply_le (a - b) 0
  have h1 : |a 1 - b 1| ≤ ‖a - b‖ := PiLp.norm_apply_le (a - b) 1
  have h2 : |a 2 - b 2| ≤ ‖a - b‖ := PiLp.norm_apply_le (a - b) 2
  have htsq : |t ^ 2| ≤ 1 := by rw [abs_of_nonneg (sq_nonneg _)]; nlinarith [ht.1, ht.2]
  have ht1 : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
  have hm1 := mul_le_mul ht1 h1 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hm2 := mul_le_mul htsq h2 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have heq : quadratic a t - quadratic b t =
      (a 0 - b 0) + t * (a 1 - b 1) + t ^ 2 * (a 2 - b 2) := by dsimp [quadratic]; ring
  rw [heq]
  have hh := abs_add_three (a 0 - b 0) (t * (a 1 - b 1)) (t ^ 2 * (a 2 - b 2))
  simp only [abs_mul, one_mul] at hm1 hm2 hh
  linarith

theorem quadratic_time_lipschitz {a : Coeff} {B t s : ℝ} (ha : ‖a‖ ≤ B)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    |quadratic a t - quadratic a s| ≤ 3 * B * |t - s| := by
  have h1 : |a 1| ≤ B := (PiLp.norm_apply_le a 1).trans ha
  have h2 : |a 2| ≤ B := (PiLp.norm_apply_le a 2).trans ha
  have hsum : |t + s| ≤ 2 := by rw [abs_of_nonneg (add_nonneg ht.1 hs.1)]; linarith [ht.2, hs.2]
  have hcoef : |a 1 + (t + s) * a 2| ≤ 3 * B := by
    have hmul := mul_le_mul hsum h2 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    have hh := abs_add_le (a 1) ((t + s) * a 2)
    rw [abs_mul] at hh
    linarith
  have heq : quadratic a t - quadratic a s = (t - s) * (a 1 + (t + s) * a 2) := by
    dsimp [quadratic]
    ring
  rw [heq, abs_mul]
  nlinarith [mul_le_mul_of_nonneg_left hcoef (abs_nonneg (t - s))]

theorem floor_scaled_error {p : ℝ} (hp : 0 < p) (x : ℝ) :
    |x - p * (⌊x / p⌋ : ℝ)| ≤ p := by
  have hlo := (mul_le_mul_of_nonneg_left (Int.floor_le (x / p)) hp.le)
  have hhi := (mul_le_mul_of_nonneg_left (Int.lt_floor_add_one (x / p)).le hp.le)
  have hmul : p * (x / p) = x := by field_simp
  rw [hmul] at hlo hhi
  rw [abs_le]
  constructor <;> linarith

theorem marked_scalar_support {α : Type*} {D : ℕ} (hD : 1 ≤ D)
    {p R B : ℝ} (hp : 0 < p) (hR : 1 ≤ R) (hBR : 3 * B ≤ R)
    (hmesh : R ≤ (D : ℝ) * p) (a : α → Coeff) (G : Set α)
    (E : Set (α × ℝ)) (F : Finset (ℤ × ℤ))
    (hunit : E ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1)
    (hB : ∀ l ∈ G, ‖a l‖ ≤ B)
    (hF : ∀ l t, (l, t) ∈ E →
      (⌊t / p⌋, ⌊quadratic (a l) t / p⌋) ∈ F)
    {l₀ : α} (hl₀ : l₀ ∈ G) {j : Fin D}
    (hj : j ∈ labeledTimeMarks D a G E p (coefficientCode p (a l₀))) :
    ∃ f ∈ F, |binTime D j - p * (f.1 : ℝ)| ≤ 2 * p ∧
      |quadratic (a l₀) (binTime D j) - p * (f.2 : ℝ)| ≤ 12 * p := by
  classical
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  rcases (Finset.mem_filter.mp hj).2 with ⟨l, hl, hcode, t, htE, htcell⟩
  have ht := (hunit htE).2
  have hjt := timeCell_midpoint_dist hD j htcell
  have hjunit := Submission.Lib.K4PlankGeometry.binTime_mem_Icc hD j
  have hdt : 1 / (D : ℝ) ≤ p := (div_le_iff₀ hDpos).mpr (by nlinarith)
  have hBt : 3 * B / (D : ℝ) ≤ p := (div_le_iff₀ hDpos).mpr (by nlinarith)
  refine ⟨(⌊t / p⌋, ⌊quadratic (a l) t / p⌋), hF l t htE, ?_, ?_⟩
  · have hh := abs_add_le (binTime D j - t) (t - p * (⌊t / p⌋ : ℝ))
    have heq : binTime D j - t + (t - p * (⌊t / p⌋ : ℝ)) =
        binTime D j - p * (⌊t / p⌋ : ℝ) := by ring
    rw [heq] at hh
    linarith [floor_scaled_error hp t]
  · have htime := quadratic_time_lipschitz (hB l₀ hl₀) hjunit ht
    have htime' : |quadratic (a l₀) (binTime D j) - quadratic (a l₀) t| ≤ p := by
      have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB l₀ hl₀)
      have hh := mul_le_mul_of_nonneg_left hjt (by positivity : 0 ≤ 3 * B)
      have heq : 3 * B * (1 / (D : ℝ)) = 3 * B / (D : ℝ) := by ring
      rw [heq] at hh
      linarith
    have hdiff := quadratic_difference_le (a := a l₀) (b := a l) ht
    have hcoeff := coefficient_dist_of_code_eq hp hcode.symm
    have hh := abs_add_three
      (quadratic (a l₀) (binTime D j) - quadratic (a l₀) t)
      (quadratic (a l₀) t - quadratic (a l) t)
      (quadratic (a l) t - p * (⌊quadratic (a l) t / p⌋ : ℝ))
    have heq : quadratic (a l₀) (binTime D j) - quadratic (a l₀) t +
        (quadratic (a l₀) t - quadratic (a l) t) +
        (quadratic (a l) t - p * (⌊quadratic (a l) t / p⌋ : ℝ)) =
        quadratic (a l₀) (binTime D j) - p * (⌊quadratic (a l) t / p⌋ : ℝ) := by ring
    rw [heq] at hh
    linarith [floor_scaled_error hp (quadratic (a l) t)]

end
end Submission.Obl.k4_scalar_coefficient_clustering
