/- Adapted from this LOT tree: o199, session x0695, branch x0695,
   commit 9136fa89, Submission/Obl/k4_finite_path_candidate_conversion/DeepStrips.lean.
   This file retains the source's own provenance comments below. -/
import Submission.Obl.k4_finite_positive_mixed_cover_realization.ThinFrames

/-!
The true deeper chart supplies an observable unit-normal strip in the actual
normalized velocity coordinates of any ancestor. Its relative determinant
is the ratio of the two time-normalized frame determinants.
-/

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization

open Submission.Lib.K4XInterface
open scoped RealInnerProductSpace

noncomputable def relativeVelocityFrame (q₀ q₁ : ℝ) (Q₀ Q₁ : Frame) : Frame :=
  (q₀ / q₁) • (Q₀⁻¹ * Q₁)

theorem relativeVelocityFrame_apply (q₀ q₁ : ℝ) (Q₀ Q₁ : Frame) (w : Plane) :
    Matrix.toEuclideanLin (relativeVelocityFrame q₀ q₁ Q₀ Q₁) w =
      (q₀ / q₁) • Matrix.toEuclideanLin Q₀⁻¹ (Matrix.toEuclideanLin Q₁ w) := by
  change Matrix.toLpLin 2 2 ((q₀ / q₁) • (Q₀⁻¹ * Q₁)) w = _
  rw [map_smul, LinearMap.smul_apply, Matrix.toLpLin_mul_same, LinearMap.comp_apply]

theorem relativeVelocityFrame_det (q₀ q₁ : ℝ) (Q₀ Q₁ : Frame) :
    |(relativeVelocityFrame q₀ q₁ Q₀ Q₁).det| =
      (q₀ / q₁) ^ 2 * (|Q₁.det| / |Q₀.det|) := by
  rw [relativeVelocityFrame, Matrix.det_smul, Matrix.det_mul, det_inv_fin2]
  simp only [Fintype.card_fin, abs_mul, abs_pow, abs_inv, sq_abs]
  ring

theorem relativeVelocityFrame_det_ne_zero {q₀ q₁ : ℝ} {Q₀ Q₁ : Frame}
    (hq₀ : q₀ ≠ 0) (hq₁ : q₁ ≠ 0) (hQ₀ : Q₀.det ≠ 0) (hQ₁ : Q₁.det ≠ 0) :
    (relativeVelocityFrame q₀ q₁ Q₀ Q₁).det ≠ 0 := by
  rw [relativeVelocityFrame, Matrix.det_smul, Matrix.det_mul, det_inv_fin2]
  exact mul_ne_zero (pow_ne_zero _ (div_ne_zero hq₀ hq₁))
    (mul_ne_zero (inv_ne_zero hQ₀) hQ₁)

theorem relativeVelocityFrame_dyadic_det (T₀ T₁ : ℕ) (Q₀ Q₁ : Frame) :
    |(relativeVelocityFrame (((2 : ℝ) ^ T₀)⁻¹) (((2 : ℝ) ^ T₁)⁻¹) Q₀ Q₁).det| =
      (|Q₁.det| * (4 : ℝ) ^ T₁) / (|Q₀.det| * (4 : ℝ) ^ T₀) := by
  rw [relativeVelocityFrame_det]
  have hpow (T : ℕ) : (4 : ℝ) ^ T = ((2 : ℝ) ^ T) ^ 2 := by
    rw [← pow_mul, Nat.mul_comm T 2, pow_mul]
    norm_num
  rw [hpow T₀, hpow T₁]
  by_cases hQ₀ : Q₀.det = 0
  · simp [hQ₀]
  · have hQ₀' : |Q₀.det| ≠ 0 := abs_ne_zero.mpr hQ₀
    field_simp

/-- Two bounds of the supplied cumulative narrowness give the relative
determinant bound used by the deeper true strip. -/
theorem relativeVelocityFrame_narrowness_bound
    {N w₀ w₁ error : ℝ} {T₀ T₁ : ℕ} {Q₀ Q₁ : Frame}
    (hN : 0 < N)
    (h₀ : N ^ (-(w₀ + error)) ≤ |Q₀.det| * (4 : ℝ) ^ T₀)
    (h₁ : |Q₁.det| * (4 : ℝ) ^ T₁ ≤ N ^ (-(w₁ - error))) :
    |(relativeVelocityFrame (((2 : ℝ) ^ T₀)⁻¹) (((2 : ℝ) ^ T₁)⁻¹) Q₀ Q₁).det| ≤
      N ^ (-(w₁ - w₀ - 2 * error)) := by
  rw [relativeVelocityFrame_dyadic_det]
  calc
    _ ≤ N ^ (-(w₁ - error)) / N ^ (-(w₀ + error)) :=
      div_le_div₀ (by positivity) h₁ (by positivity) h₀
    _ = _ := by rw [← Real.rpow_sub hN]; congr 1; ring

theorem relativeVelocityFrame_identity {q₀ q₁ : ℝ} {Q₀ Q₁ : Frame}
    (hq₁ : q₁ ≠ 0) (hQ₁ : Q₁.det ≠ 0) (u₀ u₁ w : Plane) :
    q₀ • Matrix.toEuclideanLin Q₀⁻¹ (w - u₀) =
      q₀ • Matrix.toEuclideanLin Q₀⁻¹ (u₁ - u₀) +
        Matrix.toEuclideanLin (relativeVelocityFrame q₀ q₁ Q₀ Q₁)
          (q₁ • Matrix.toEuclideanLin Q₁⁻¹ (w - u₁)) := by
  rw [relativeVelocityFrame_apply, map_smul, toEuclideanLin_inv_cancel Q₁ hQ₁,
    map_smul, smul_smul, div_mul_cancel₀ _ hq₁, ← smul_add, ← map_add]
  congr 2
  abel

/-- A deeper true frame gives a thin strip in ancestor-normalized velocity
coordinates. The chosen normal and bias depend only on the two chart frames
and velocity centers, so the deeper original label knows them. -/
theorem gchart_relative_velocity_strip
    {Nk κ j r Bv a : ℝ} {M D T₀ T₁ : ℕ}
    {Ev : Set (Line × ℝ)} {c₁ u₀ u₁ : Plane} {Q₀ Q₁ : Frame}
    {R : MvPolynomial (Fin 4) ℝ} {A : Set Line} {F : Set (Line × ℝ)} {ex : Prop}
    (h : gchart Nk M D κ T₁ j r Bv Ev c₁ u₁ Q₁ R A F ex)
    (hQ₀ : Q₀.det ≠ 0) (ha : 0 < a)
    (hdet : |(relativeVelocityFrame (((2 : ℝ) ^ T₀)⁻¹)
      (((2 : ℝ) ^ T₁)⁻¹) Q₀ Q₁).det| ≤ a ^ 2) :
    ∃ (n : Plane) (β : ℝ), ‖n‖ = 1 ∧
      ∀ l ∈ A,
        |inner ℝ ((((2 : ℝ) ^ T₀)⁻¹) • Matrix.toEuclideanLin Q₀⁻¹ (gv l - u₀)) n - β| ≤
          2 * κ * a := by
  have hq₀ : (((2 : ℝ) ^ T₀)⁻¹) ≠ 0 := by positivity
  have hq₁ : (((2 : ℝ) ^ T₁)⁻¹) ≠ 0 := by positivity
  have hM := relativeVelocityFrame_det_ne_zero hq₀ hq₁ hQ₀ h.1
  have hw (l : Line) (hl : l ∈ A) :
      ‖(((2 : ℝ) ^ T₁)⁻¹) • Matrix.toEuclideanLin Q₁⁻¹ (gv l - u₁)‖ ≤ 2 * κ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < ((2 : ℝ) ^ T₁)⁻¹)]
    calc
      _ ≤ ((2 : ℝ) ^ T₁)⁻¹ * (2 * κ * (2 : ℝ) ^ T₁) :=
        mul_le_mul_of_nonneg_left (gchart_velocity h hl) (by positivity)
      _ = _ := by field_simp
  obtain ⟨n, β, hn, hfit⟩ := exists_thin_affine_frame_strip
    (relativeVelocityFrame (((2 : ℝ) ^ T₀)⁻¹) (((2 : ℝ) ^ T₁)⁻¹) Q₀ Q₁) hM
    ((((2 : ℝ) ^ T₀)⁻¹) • Matrix.toEuclideanLin Q₀⁻¹ (u₁ - u₀))
    (fun l : Line => (((2 : ℝ) ^ T₀)⁻¹) • Matrix.toEuclideanLin Q₀⁻¹ (gv l - u₀)) A ha hdet
    (fun l hl => ⟨_, hw l hl, relativeVelocityFrame_identity hq₁ h.1 u₀ u₁ (gv l)⟩)
  exact ⟨n, β, hn, fun l hl => (hfit l hl).trans_eq (by ring)⟩

/-- In particular, the original path's upper and lower cumulative determinant
bounds recover the deeper strip with half their exponent difference. -/
theorem gchart_relative_strip_of_narrowness
    {Nk κ j r Bv w₀ w₁ error : ℝ} {M D T₀ T₁ : ℕ}
    {Ev : Set (Line × ℝ)} {c₁ u₀ u₁ : Plane} {Q₀ Q₁ : Frame}
    {R : MvPolynomial (Fin 4) ℝ} {A : Set Line} {F : Set (Line × ℝ)} {ex : Prop}
    (h : gchart Nk M D κ T₁ j r Bv Ev c₁ u₁ Q₁ R A F ex)
    (hNk : 0 < Nk) (hQ₀ : Q₀.det ≠ 0)
    (h₀ : Nk ^ (-(w₀ + error)) ≤ |Q₀.det| * (4 : ℝ) ^ T₀)
    (h₁ : |Q₁.det| * (4 : ℝ) ^ T₁ ≤ Nk ^ (-(w₁ - error))) :
    ∃ (n : Plane) (β : ℝ), ‖n‖ = 1 ∧
      ∀ l ∈ A,
        |inner ℝ ((((2 : ℝ) ^ T₀)⁻¹) • Matrix.toEuclideanLin Q₀⁻¹ (gv l - u₀)) n - β| ≤
          2 * κ * Nk ^ (-(w₁ - w₀ - 2 * error) / 2) := by
  have hdet := relativeVelocityFrame_narrowness_bound hNk h₀ h₁
  have hpow : Nk ^ (-(w₁ - w₀ - 2 * error)) =
      (Nk ^ (-(w₁ - w₀ - 2 * error) / 2)) ^ 2 := by
    rw [← Real.rpow_mul_natCast hNk.le]
    congr 1
    push_cast
    ring
  rw [hpow] at hdet
  exact gchart_relative_velocity_strip h hQ₀ (Real.rpow_pos_of_pos hNk _) hdet

end Submission.Obl.k4_finite_positive_mixed_cover_realization
