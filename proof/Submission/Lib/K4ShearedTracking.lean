-- Adapted from: here:o199
-- Session x0830, branch x0830, commit 61f4b163,
-- Submission/Obl/k4_finite_path_candidate_conversion/TrackingRows.lean.
import Submission.Lib.K4XInterface.Charts

/-!
# Sheared rows of a child frame

The accepted `K4XInterface.tilted_box_of_frame` supplies the two row estimates.
Here they are put into the position and velocity form used by `EH3`. Bounds on
the first row and determinant produce the required widths. Actual spread of
the first velocity coordinate, rather than the size of the enclosing matrix,
controls the slope of the shear.
-/

namespace Submission.Lib.K4ShearedTracking

open Submission.Lib.K4XInterface

noncomputable section

abbrev TrackingPlane := EuclideanSpace ℝ (Fin 2)

/-- Length of the first row of a planar frame. -/
def firstRowLength (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  Real.sqrt (M 0 0 ^ 2 + M 0 1 ^ 2)

/-- Orthogonal projection of the second row onto the first. -/
def rowShear (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  (M 1 0 * M 0 0 + M 1 1 * M 0 1) / (M 0 0 ^ 2 + M 0 1 ^ 2)

theorem firstRowLength_pos (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : M.det ≠ 0) :
    0 < firstRowLength M := by
  apply Real.sqrt_pos.mpr
  by_contra h
  have hs : M 0 0 ^ 2 + M 0 1 ^ 2 = 0 := le_antisymm (not_lt.mp h) (by positivity)
  have h00 : M 0 0 = 0 := by nlinarith [sq_nonneg (M 0 1)]
  have h01 : M 0 1 = 0 := by nlinarith [sq_nonneg (M 0 0)]
  apply hM
  simp [Matrix.det_fin_two, h00, h01]

/-- The transverse length is the determinant divided by the first-row length. -/
theorem transverseLength_eq (M : Matrix (Fin 2) (Fin 2) ℝ) :
    Real.sqrt (M.det ^ 2 / (M 0 0 ^ 2 + M 0 1 ^ 2)) = |M.det| / firstRowLength M := by
  rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq_eq_abs]
  rfl

/-- Position and velocity errors in a frame have the same sheared rows. -/
theorem row_bounds (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : M.det ≠ 0)
    (w : TrackingPlane) {κ : ℝ} (hw : ‖Matrix.toEuclideanLin M⁻¹ w‖ ≤ κ) :
    |w 0| ≤ κ * firstRowLength M ∧
      |w 1 - rowShear M * w 0| ≤ κ * |M.det| / firstRowLength M := by
  have hs : 0 < M 0 0 ^ 2 + M 0 1 ^ 2 :=
    Real.sqrt_pos.mp (firstRowLength_pos M hM)
  obtain ⟨h0, h1⟩ := tilted_box_of_frame M hM w hw hs
  refine ⟨h0, ?_⟩
  simpa only [rowShear, transverseLength_eq, mul_div_assoc] using h1

/-- Moving-center parameters after replacing the second row by its transverse part. -/
def shearedParameters (M : Matrix (Fin 2) (Fin 2) ℝ) (a b : TrackingPlane) : Fin 5 → ℝ :=
  ![a 0, b 0, a 1 - rowShear M * a 0, b 1 - rowShear M * b 0, rowShear M]

theorem position_rows (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : M.det ≠ 0)
    (y a b : TrackingPlane) (t : ℝ) {κ : ℝ}
    (hfit : ‖Matrix.toEuclideanLin M⁻¹ (y - a - t • b)‖ ≤ κ) :
    |y 0 - shearedParameters M a b 0 - t * shearedParameters M a b 1| ≤
        κ * firstRowLength M ∧
      |y 1 - shearedParameters M a b 2 - t * shearedParameters M a b 3 -
        shearedParameters M a b 4 * y 0| ≤ κ * |M.det| / firstRowLength M := by
  obtain ⟨h0, h1⟩ := row_bounds M hM (y - a - t • b) hfit
  constructor
  · simpa [shearedParameters] using h0
  · simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at h1
    convert h1 using 1
    simp only [shearedParameters, Matrix.cons_val, Fin.isValue]
    congr 1
    ring

theorem velocity_rows (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : M.det ≠ 0)
    (v a b : TrackingPlane) {κ q : ℝ}
    (hfit : ‖Matrix.toEuclideanLin M⁻¹ (v - b)‖ ≤ 2 * κ / q) :
    |v 1 - shearedParameters M a b 3 - shearedParameters M a b 4 * v 0| ≤
      (2 * κ / q) * |M.det| / firstRowLength M := by
  have h := (row_bounds M hM (v - b) hfit).2
  simp only [PiLp.sub_apply] at h
  convert h using 1
  simp only [shearedParameters, Matrix.cons_val, Fin.isValue]
  congr 1
  ring

/-- The determinant and the actual first-row lower bound give the thin width. -/
theorem transverseRatio_le (M : Matrix (Fin 2) (Fin 2) ℝ) {H q g : ℝ}
    (hH : 0 < H) (hq : 0 < q) (hg : 0 ≤ g)
    (hlower : q / H ≤ firstRowLength M) (hdet : |M.det| ≤ H * q ^ 2 * g) :
    |M.det| / firstRowLength M ≤ H ^ 2 * q * g := by
  have hr : 0 < firstRowLength M := (div_pos hq hH).trans_le hlower
  calc
    _ ≤ (H * q ^ 2 * g) / firstRowLength M :=
      div_le_div_of_nonneg_right hdet hr.le
    _ ≤ (H * q ^ 2 * g) / (q / H) :=
      div_le_div_of_nonneg_left (by positivity) (div_pos hq hH) hlower
    _ = H ^ 2 * q * g := by field_simp

/-- The three geometric tracking bounds required in the true-label hypothesis. -/
theorem tracking_rows (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : M.det ≠ 0)
    (y v a b : TrackingPlane) (t : ℝ) {κ H q g : ℝ}
    (hκ : 0 ≤ κ) (hH : 0 < H) (hq : 0 < q) (hg : 0 ≤ g)
    (hlower : q / H ≤ firstRowLength M) (hupper : firstRowLength M ≤ H * q)
    (hdet : |M.det| ≤ H * q ^ 2 * g)
    (hpos : ‖Matrix.toEuclideanLin M⁻¹ (y - a - t • b)‖ ≤ κ)
    (hvel : ‖Matrix.toEuclideanLin M⁻¹ (v - b)‖ ≤ 2 * κ / q) :
    |y 0 - shearedParameters M a b 0 - t * shearedParameters M a b 1| ≤ κ * H * q ∧
      |y 1 - shearedParameters M a b 2 - t * shearedParameters M a b 3 -
        shearedParameters M a b 4 * y 0| ≤ κ * H ^ 2 * q * g ∧
      |v 1 - shearedParameters M a b 3 - shearedParameters M a b 4 * v 0| ≤
        2 * κ * H ^ 2 * g := by
  have hratio := transverseRatio_le M hH hq hg hlower hdet
  obtain ⟨h0, h1⟩ := position_rows M hM y a b t hpos
  have h2 := velocity_rows M hM v a b hvel
  refine ⟨h0.trans ?_, h1.trans ?_, h2.trans ?_⟩
  · calc κ * firstRowLength M ≤ κ * (H * q) := mul_le_mul_of_nonneg_left hupper hκ
      _ = κ * H * q := by ring
  · calc κ * |M.det| / firstRowLength M = κ * (|M.det| / firstRowLength M) := by ring
      _ ≤ κ * (H ^ 2 * q * g) := mul_le_mul_of_nonneg_left hratio hκ
      _ = κ * H ^ 2 * q * g := by ring
  · calc (2 * κ / q) * |M.det| / firstRowLength M =
          (2 * κ / q) * (|M.det| / firstRowLength M) := by ring
      _ ≤ (2 * κ / q) * (H ^ 2 * q * g) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = 2 * κ * H ^ 2 * g := by field_simp

/-- Two separated actual first coordinates control an affine slope. -/
theorem slope_le_of_actual_spread {x₀ x₁ y₀ y₁ β lam K e δ : ℝ}
    (hδ : 0 < δ) (hgap : δ ≤ |x₁ - x₀|)
    (hy₀ : |y₀| ≤ K) (hy₁ : |y₁| ≤ K)
    (h₀ : |y₀ - β - lam * x₀| ≤ e) (h₁ : |y₁ - β - lam * x₁| ≤ e) :
    |lam| ≤ (2 * K + 2 * e) / δ := by
  have hmul : |lam| * |x₁ - x₀| ≤ 2 * K + 2 * e := by
    calc
      _ = |(y₁ - y₀) - ((y₁ - β - lam * x₁) - (y₀ - β - lam * x₀))| := by
        rw [← abs_mul]; congr 1; ring
      _ ≤ |y₁ - y₀| + |(y₁ - β - lam * x₁) - (y₀ - β - lam * x₀)| := abs_sub _ _
      _ ≤ (|y₁| + |y₀|) + (|y₁ - β - lam * x₁| + |y₀ - β - lam * x₀|) :=
        add_le_add (abs_sub _ _) (abs_sub _ _)
      _ ≤ 2 * K + 2 * e := by linarith
  apply (le_div_iff₀ hδ).mpr
  exact (mul_le_mul_of_nonneg_left hgap (abs_nonneg lam)).trans hmul

/-- Bounded native velocities and actual major-coordinate spread bound the shear. -/
theorem rowShear_le_of_velocity_spread (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : M.det ≠ 0)
    (v₀ v₁ b : TrackingPlane) {κ H q g K δ : ℝ}
    (hκ : 0 ≤ κ) (hH : 0 < H) (hq : 0 < q) (hg : 0 ≤ g)
    (hlower : q / H ≤ firstRowLength M) (hdet : |M.det| ≤ H * q ^ 2 * g)
    (hvel₀ : ‖Matrix.toEuclideanLin M⁻¹ (v₀ - b)‖ ≤ 2 * κ / q)
    (hvel₁ : ‖Matrix.toEuclideanLin M⁻¹ (v₁ - b)‖ ≤ 2 * κ / q)
    (hv₀ : |v₀ 1| ≤ K) (hv₁ : |v₁ 1| ≤ K)
    (hδ : 0 < δ) (hgap : δ ≤ |v₁ 0 - v₀ 0|) :
    |rowShear M| ≤ (2 * K + 4 * κ * H ^ 2 * g) / δ := by
  have hratio := transverseRatio_le M hH hq hg hlower hdet
  have hbound : (2 * κ / q) * |M.det| / firstRowLength M ≤ 2 * κ * H ^ 2 * g := by
    calc _ = (2 * κ / q) * (|M.det| / firstRowLength M) := by ring
         _ ≤ (2 * κ / q) * (H ^ 2 * q * g) :=
           mul_le_mul_of_nonneg_left hratio (by positivity)
         _ = 2 * κ * H ^ 2 * g := by field_simp
  have h₀ := (velocity_rows M hM v₀ 0 b hvel₀).trans hbound
  have h₁ := (velocity_rows M hM v₁ 0 b hvel₁).trans hbound
  have := slope_le_of_actual_spread hδ hgap hv₀ hv₁ h₀ h₁
  simpa [shearedParameters, show 2 * (2 * κ * H ^ 2 * g) = 4 * κ * H ^ 2 * g by ring] using this

/-- Actual first-coordinate velocity spread forces a lower bound on the first row. -/
theorem firstRowLength_lower_of_velocity_spread
    (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : M.det ≠ 0) (v₀ v₁ b : TrackingPlane) {κ q δ : ℝ}
    (hκ : 0 < κ) (hq : 0 < q)
    (hvel₀ : ‖Matrix.toEuclideanLin M⁻¹ (v₀ - b)‖ ≤ 2 * κ / q)
    (hvel₁ : ‖Matrix.toEuclideanLin M⁻¹ (v₁ - b)‖ ≤ 2 * κ / q)
    (hgap : δ ≤ |v₁ 0 - v₀ 0|) :
    δ * q / (4 * κ) ≤ firstRowLength M := by
  have h₀ := (row_bounds M hM (v₀ - b) hvel₀).1
  have h₁ := (row_bounds M hM (v₁ - b) hvel₁).1
  simp only [PiLp.sub_apply] at h₀ h₁
  have hdiff : |v₁ 0 - v₀ 0| ≤ (4 * κ * firstRowLength M) / q := by
    calc
      _ = |(v₁ 0 - b 0) - (v₀ 0 - b 0)| := by congr 1; ring
      _ ≤ |v₁ 0 - b 0| + |v₀ 0 - b 0| := abs_sub _ _
      _ ≤ (2 * κ / q) * firstRowLength M + (2 * κ / q) * firstRowLength M := add_le_add h₁ h₀
      _ = _ := by ring
  have hmul := (le_div_iff₀ hq).mp (hgap.trans hdiff)
  apply (div_le_iff₀ (by positivity : 0 < 4 * κ)).mpr
  nlinarith only [hmul]

/-- A single occupied trajectory bounds all the affine-center coefficients once
the shear and the geometric position/velocity errors are controlled. -/
theorem parameters_bound_of_witness (c : Fin 5 → ℝ) (y v : TrackingPlane) {t K L A B C D : ℝ}
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (ht : |t| ≤ 1) (hy₀ : |y 0| ≤ K) (hy₁ : |y 1| ≤ K)
    (hv₀ : |v 0| ≤ K) (hv₁ : |v 1| ≤ K) (hc₄ : |c 4| ≤ L)
    (hpos₀ : |y 0 - c 0 - t * c 1| ≤ A)
    (hpos₁ : |y 1 - c 2 - t * c 3 - c 4 * y 0| ≤ B)
    (hvel₀ : |v 0 - c 1| ≤ C) (hvel₁ : |v 1 - c 3 - c 4 * v 0| ≤ D) :
    ∀ i, |c i| ≤ L + 2 * (1 + L) * K + A + B + C + D := by
  have h1 : |c 1| ≤ K + C := by
    calc
      _ = |v 0 - (v 0 - c 1)| := by congr 1; ring
      _ ≤ |v 0| + |v 0 - c 1| := abs_sub _ _
      _ ≤ K + C := add_le_add hv₀ hvel₀
  have h3 : |c 3| ≤ (1 + L) * K + D := by
    calc
      _ = |(v 1 - c 4 * v 0) - (v 1 - c 3 - c 4 * v 0)| := by congr 1; ring
      _ ≤ |v 1 - c 4 * v 0| + |v 1 - c 3 - c 4 * v 0| := abs_sub _ _
      _ ≤ (|v 1| + |c 4| * |v 0|) + D := by
        exact add_le_add (by simpa [abs_mul] using abs_sub (v 1) (c 4 * v 0)) hvel₁
      _ ≤ (K + L * K) + D := by
        gcongr
      _ = _ := by ring
  have ht1 : |t * c 1| ≤ K + C := by
    rw [abs_mul]
    exact (mul_le_mul ht h1 (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have ht3 : |t * c 3| ≤ (1 + L) * K + D := by
    rw [abs_mul]
    exact (mul_le_mul ht h3 (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have h0 : |c 0| ≤ 2 * K + C + A := by
    calc
      _ = |(y 0 - t * c 1) - (y 0 - c 0 - t * c 1)| := by congr 1; ring
      _ ≤ |y 0 - t * c 1| + |y 0 - c 0 - t * c 1| := abs_sub _ _
      _ ≤ (|y 0| + |t * c 1|) + A := add_le_add (abs_sub _ _) hpos₀
      _ ≤ _ := by linarith
  have h2 : |c 2| ≤ 2 * (1 + L) * K + D + B := by
    calc
      _ = |(y 1 - t * c 3 - c 4 * y 0) - (y 1 - c 2 - t * c 3 - c 4 * y 0)| :=
        by congr 1; ring
      _ ≤ |y 1 - t * c 3 - c 4 * y 0| + |y 1 - c 2 - t * c 3 - c 4 * y 0| := abs_sub _ _
      _ ≤ ((|y 1| + |t * c 3|) + |c 4| * |y 0|) + B := by
        apply add_le_add _ hpos₁
        exact (abs_sub _ _).trans (by rw [abs_mul]; gcongr; exact abs_sub _ _)
      _ ≤ ((K + ((1 + L) * K + D)) + L * K) + B := by gcongr
      _ = _ := by ring
  intro i
  fin_cases i
  · change |c 0| ≤ _
    nlinarith [mul_nonneg hL hK]
  · change |c 1| ≤ _
    nlinarith [mul_nonneg hL hK]
  · change |c 2| ≤ _
    linarith
  · change |c 3| ≤ _
    nlinarith [mul_nonneg hL hK]
  · change |c 4| ≤ _
    have hLK : 0 ≤ (1 + L) * K := by positivity
    linarith

end

end Submission.Lib.K4ShearedTracking
