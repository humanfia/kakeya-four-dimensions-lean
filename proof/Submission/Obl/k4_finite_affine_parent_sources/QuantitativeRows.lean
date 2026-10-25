-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.RelativeRowGeometry
import Submission.Obl.k4_finite_affine_parent_sources.TiltedLabels
import Submission.Lib.K4ShearedTracking

/-!
Quantitative row budgets for actual relative child frames. The inputs separate
physical largest-axis fullness from the upper row bounds obtained in the
no-original-candidate branch. All losses are fixed powers of one slack `H`.
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open Submission.Lib.K4FinitePlankAtlases Submission.Lib.K4XInterface

noncomputable section

lemma frameRow_smul (a : ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ) (e : Fin 2) :
    frameRow (a • M) e = a • frameRow M e := by
  ext j
  rfl

lemma frameRow_norm_smul (a : ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ) (e : Fin 2) :
    ‖frameRow (a • M) e‖ = |a| * ‖frameRow M e‖ := by
  rw [frameRow_smul, norm_smul, Real.norm_eq_abs]

lemma firstRowLength_eq_frameRow (M : Matrix (Fin 2) (Fin 2) ℝ) :
    Submission.Lib.K4ShearedTracking.firstRowLength M = ‖frameRow M 0‖ := by
  rw [Submission.Lib.K4ShearedTracking.firstRowLength, ← frameRow_norm_sq M 0,
    Real.sqrt_sq (norm_nonneg _)]

/-- Physical fullness forces the major relative row to stay large once
the parent's transverse contribution is smaller than half that fullness. -/
theorem quantitative_major_row_lower
    (a b H : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hH : 1 ≤ H)
    (haH : a ≤ H) (hbH : b ≤ 1 / (2 * H ^ 2))
    (e n : EuclideanSpace ℝ (Fin 2)) (he : ‖e‖ = 1) (hn : ‖n‖ = 1)
    (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hfull : ∃ j : Fin 2, 1 / H ≤
      ‖WithLp.toLp 2 (fun i => (plankFrame a b e n * M) i j)‖)
    (hrow : ‖frameRow M 1‖ ≤ H) :
    1 / (2 * H ^ 2) ≤ ‖frameRow M 0‖ := by
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hminor : b * ‖frameRow M 1‖ ≤ (1 / H) / 2 := by
    calc
      _ ≤ (1 / (2 * H ^ 2)) * H :=
        mul_le_mul hbH hrow (norm_nonneg _) (by positivity)
      _ = _ := by field_simp <;> ring
  have hlower := relative_major_row_lower a b (1 / H) ha hb e n he hn M hfull hminor
  calc
    _ = (1 / H) / (2 * H) := by field_simp <;> ring
    _ ≤ (1 / H) / (2 * a) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    _ ≤ _ := hlower

/-- Bounds on the time-normalized relative velocity matrix give exactly
the position-frame widths at the child's native block length. -/
theorem rescale_relative_row_budgets
    (M : Matrix (Fin 2) (Fin 2) ℝ) (q H g : ℝ) (hq : 0 < q)
    (hlower : 1 / (2 * H ^ 2) ≤ ‖frameRow (q⁻¹ • M) 0‖)
    (hupper : ∀ e : Fin 2, ‖frameRow (q⁻¹ • M) e‖ ≤ H)
    (hdet : |(q⁻¹ • M).det| ≤ H * g) :
    q / (2 * H ^ 2) ≤ ‖frameRow M 0‖ ∧
      (∀ e : Fin 2, ‖frameRow M e‖ ≤ H * q) ∧
      |M.det| ≤ H * q ^ 2 * g := by
  have hnorm (e : Fin 2) : ‖frameRow (q⁻¹ • M) e‖ = ‖frameRow M e‖ / q := by
    rw [frameRow_norm_smul, abs_inv, abs_of_pos hq]
    ring
  have hdet_eq : |(q⁻¹ • M).det| = |M.det| / q ^ 2 := by
    rw [Matrix.det_smul]
    simp only [Fintype.card_fin, abs_mul, abs_pow, abs_inv, abs_of_pos hq]
    field_simp <;> ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hnorm] at hlower
    have h := (le_div_iff₀ hq).mp hlower
    simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using h
  · intro e
    exact (div_le_iff₀ hq).mp (by simpa only [hnorm] using hupper e)
  · rw [hdet_eq] at hdet
    have h := (div_le_iff₀ (sq_pos_of_pos hq)).mp hdet
    nlinarith only [h]

/-- One common slack budget controls every geometric row and all five
center/shear coefficients required by the frozen true-label hypothesis. -/
theorem quantitative_tilted_label
    {α : Type} (b : α → Fin 6 → ℝ) (A : Set α) (l₀ : α) (hl₀ : l₀ ∈ A)
    (T : ℕ) (j : Fin (2 ^ T))
    (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : M.det ≠ 0)
    (center speed : EuclideanSpace ℝ (Fin 2)) (κ H g : ℝ)
    (hκ : 0 ≤ κ) (hκH : κ ≤ H) (hH : 1 ≤ H) (hg : 0 ≤ g)
    (hfit : ∀ l ∈ A, ∀ t ∈ IS T j,
      ‖Matrix.toEuclideanLin M⁻¹ (gy (0, b l) t - center - t • speed)‖ ≤ κ)
    (hcoeff : |b l₀ 0| ≤ H ∧ |b l₀ 1| ≤ H ∧ |b l₀ 3| ≤ H ∧ |b l₀ 4| ≤ H)
    (hlower : ((2 : ℝ) ^ T)⁻¹ / (2 * H ^ 2) ≤ ‖frameRow M 0‖)
    (hupper : ∀ e : Fin 2, ‖frameRow M e‖ ≤ H * ((2 : ℝ) ^ T)⁻¹)
    (hdet : |M.det| ≤ H * (((2 : ℝ) ^ T)⁻¹) ^ 2 * g) :
    ∃ c : Fin 5 → ℝ, (∀ e, |c e| ≤ 16 * H ^ 4) ∧
      ∀ l ∈ A,
        (∀ t ∈ IS T j,
          |(exS b l t) 1 - c 0 - t * c 1| ≤ 16 * H ^ 4 / (2 : ℝ) ^ T ∧
          |(exS b l t) 2 - c 2 - t * c 3 - c 4 * (exS b l t) 1| ≤
            16 * H ^ 4 / (2 : ℝ) ^ T * g) ∧
        |b l 4 - c 3 - c 4 * b l 3| ≤ 16 * H ^ 4 * g := by
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  let q := ((2 : ℝ) ^ T)⁻¹
  have hq : 0 < q := by dsimp [q]; positivity
  have hlo : 0 < q / (2 * H ^ 2) := by positivity
  have hrow : 0 < M 0 0 ^ 2 + M 0 1 ^ 2 :=
    Real.sqrt_pos.mp (Submission.Lib.K4ShearedTracking.firstRowLength_pos M hM)
  have hrow_nonneg : 0 ≤ Submission.Lib.K4ShearedTracking.firstRowLength M :=
    (Submission.Lib.K4ShearedTracking.firstRowLength_pos M hM).le
  have hlam : |(M 1 0 * M 0 0 + M 1 1 * M 0 1) /
      (M 0 0 ^ 2 + M 0 1 ^ 2)| ≤ 2 * H ^ 3 := by
    have h := tilt_le_of_row_bounds M (q / (2 * H ^ 2)) (H * q) hlo hlower (hupper 1)
    have heq : H * q / (q / (2 * H ^ 2)) = 2 * H ^ 3 := by field_simp <;> ring
    simpa only [heq] using h
  have hminor : Real.sqrt (M.det ^ 2 / (M 0 0 ^ 2 + M 0 1 ^ 2)) ≤
      2 * H ^ 3 * q * g := by
    have h := minor_scale_le M (q / (2 * H ^ 2)) (H * q ^ 2 * g) hlo hlower hdet
    have heq : H * q ^ 2 * g / (q / (2 * H ^ 2)) = 2 * H ^ 3 * q * g := by
      field_simp <;> ring
    simpa only [heq] using h
  have hH2 : H ≤ H ^ 2 := by
    nlinarith [mul_nonneg hHpos.le (sub_nonneg.mpr hH)]
  have hHsq1 : 1 ≤ H ^ 2 := hH.trans hH2
  have hH24 : H ^ 2 ≤ H ^ 4 := by
    nlinarith [mul_nonneg (sq_nonneg H) (sub_nonneg.mpr hHsq1)]
  have hH34 : H ^ 3 ≤ H ^ 4 := by
    nlinarith [mul_nonneg (pow_nonneg hHpos.le 3) (sub_nonneg.mpr hH)]
  apply tilted_label_from_relative_frame b A l₀ hl₀ T j M hM center speed κ
    (16 * H ^ 4) H (2 * H ^ 3) g hκ hHpos.le (by positivity) hrow hfit hcoeff hlam
  · nlinarith only [hH2, hH24, pow_nonneg hHpos.le 4]
  · nlinarith only [hH34, pow_nonneg hHpos.le 4]
  · change 2 * κ * Submission.Lib.K4ShearedTracking.firstRowLength M ≤
      16 * H ^ 4 / (2 : ℝ) ^ T
    have hu : Submission.Lib.K4ShearedTracking.firstRowLength M ≤ H * q := by
      simpa only [firstRowLength_eq_frameRow] using hupper 0
    calc
      _ ≤ 2 * H * (H * q) :=
        mul_le_mul (by linarith only [hκH]) hu hrow_nonneg (by positivity)
      _ ≤ 16 * H ^ 4 / (2 : ℝ) ^ T := by
        change 2 * H * (H * q) ≤ 16 * H ^ 4 * q
        calc
          _ = 2 * H ^ 2 * q := by ring
          _ ≤ 2 * H ^ 4 * q := by gcongr
          _ ≤ _ := by gcongr; norm_num
  · calc
      _ ≤ 4 * H * (2 * H ^ 3 * q * g) :=
        mul_le_mul (by linarith only [hκH]) hminor (Real.sqrt_nonneg _) (by positivity)
      _ ≤ 16 * H ^ 4 / (2 : ℝ) ^ T * g := by
        change 4 * H * (2 * H ^ 3 * q * g) ≤ 16 * H ^ 4 * q * g
        calc
          _ = 8 * H ^ 4 * q * g := by ring
          _ ≤ _ := by gcongr; norm_num

end

end Submission.Obl.k4_finite_affine_parent_sources
