/- Adapted from this LOT tree, o151, session x0508, commit 274d45f,
   Submission/Obl/k4_known_atlas_normalization_composition/FrameComposition.lean. Earlier provenance comments are retained. -/
import Submission.Obl.k4_native_finite_terminal_atlas_lift.Definitions
import Submission.Obl.k4_scalar_coefficient_clustering.Geometry

namespace Submission.Obl.k4_native_finite_terminal_atlas_lift

open scoped BigOperators

noncomputable def frameSize (Q : Frame) : ℝ := ∑ i, ∑ j, |Q i j|

theorem frameSize_nonneg (Q : Frame) : 0 ≤ frameSize Q :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem frameSize_row_le (Q : Frame) (i : Fin 2) :
    (∑ j, |Q i j|) ≤ frameSize Q :=
  Finset.single_le_sum (f := fun i : Fin 2 => ∑ j : Fin 2, |Q i j|)
    (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)

theorem frameSize_mul (Q R : Frame) : frameSize (Q * R) ≤ frameSize Q * frameSize R := by
  classical
  calc
    frameSize (Q * R) ≤ ∑ i, ∑ j, ∑ k, |Q i k| * |R k j| := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simpa only [Matrix.mul_apply, abs_mul] using
        (Finset.abs_sum_le_sum_abs (s := Finset.univ) (fun k => Q i k * R k j))
    _ = ∑ i, ∑ k, |Q i k| * (∑ j, |R k j|) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ ∑ i, ∑ k, |Q i k| * frameSize R := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_left (frameSize_row_le R k) (abs_nonneg _)
    _ = frameSize Q * frameSize R := by simp only [frameSize, Finset.sum_mul]

theorem frameSize_mul_time {Q R : Frame} {T U : ℕ} {κ κ' : ℝ}
    (hκ' : 0 ≤ κ') (hQ : frameSize Q ≤ κ / (2 : ℝ) ^ T)
    (hR : frameSize R ≤ κ' / (2 : ℝ) ^ U) :
    frameSize (Q * R) ≤ (κ * κ') / (2 : ℝ) ^ (T + U) := by
  have hn : 0 ≤ κ' / (2 : ℝ) ^ U := div_nonneg hκ' (by positivity)
  calc
    frameSize (Q * R) ≤ frameSize Q * frameSize R := frameSize_mul Q R
    _ ≤ (κ / (2 : ℝ) ^ T) * (κ' / (2 : ℝ) ^ U) :=
      mul_le_mul hQ hR (frameSize_nonneg R) (le_trans (frameSize_nonneg Q) hQ)
    _ = _ := by rw [pow_add]; ring

theorem determinant_time_mul (Q R : Frame) (T U : ℕ) :
    |Matrix.det (Q * R)| * (4 : ℝ) ^ (T + U) =
      (|Matrix.det Q| * (4 : ℝ) ^ T) * (|Matrix.det R| * (4 : ℝ) ^ U) := by
  rw [Matrix.det_mul, abs_mul, pow_add]
  ring

theorem determinant_time_mul_bound {Q R : Frame} {T U : ℕ} {N w w' ε ε' : ℝ}
    (hN : 0 < N)
    (hQ : |Matrix.det Q| * (4 : ℝ) ^ T ≤ N ^ (-w + ε))
    (hR : |Matrix.det R| * (4 : ℝ) ^ U ≤ N ^ (-w' + ε')) :
    |Matrix.det (Q * R)| * (4 : ℝ) ^ (T + U) ≤ N ^ (-(w + w') + (ε + ε')) := by
  rw [determinant_time_mul]
  calc
    _ ≤ N ^ (-w + ε) * N ^ (-w' + ε') :=
      mul_le_mul hQ hR (by positivity) (Real.rpow_nonneg hN.le _)
    _ = _ := by rw [← Real.rpow_add hN]; congr 1; ring

/-- The linear-map version of matrix multiplication in the frozen Euclidean
coordinates, convenient for the spatial part of a composite chart. -/
theorem euclideanLin_mul_apply (Q R : Frame) (z : Spatial) :
    Matrix.toEuclideanLin (Q * R) z =
      Matrix.toEuclideanLin Q (Matrix.toEuclideanLin R z) := by
  change Matrix.toLpLin 2 2 (Q * R) z = _
  rw [Matrix.toLpLin_mul 2 2 2]
  rfl

theorem euclideanLin_inv_cancel (Q : Frame) (hQ : Matrix.det Q ≠ 0) (z : Spatial) :
    Matrix.toEuclideanLin Q⁻¹ (Matrix.toEuclideanLin Q z) = z := by
  rw [← euclideanLin_mul_apply, Matrix.nonsing_inv_mul Q (isUnit_iff_ne_zero.mpr hQ)]
  change Matrix.toLpLin 2 2 (1 : Frame) z = z
  simp [Matrix.toLpLin]

noncomputable def compositeCenter (t₀ q : ℝ) (c e u d : Spatial) (Q : Frame) : Spatial :=
  c + Matrix.toEuclideanLin Q e - (t₀ / q) • Matrix.toEuclideanLin Q d

noncomputable def compositeVelocity (q : ℝ) (u d : Spatial) (Q : Frame) : Spatial :=
  u + q⁻¹ • Matrix.toEuclideanLin Q d

theorem composite_spatial_residual (t₀ q t : ℝ) (hq : q ≠ 0)
    (c e u d Y : Spatial) (Q : Frame) :
    Y - compositeCenter t₀ q c e u d Q - t • compositeVelocity q u d Q =
      Y - c - t • u - Matrix.toEuclideanLin Q (e + ((t - t₀) / q) • d) := by
  simp only [compositeCenter, compositeVelocity, map_add, map_smul, smul_add]
  module

theorem composite_frame_residual (t₀ q t : ℝ) (hq : q ≠ 0)
    (c e u d Y : Spatial) (Q R : Frame) (hQ : Matrix.det Q ≠ 0) :
    Matrix.toEuclideanLin (Q * R)⁻¹
      (Y - compositeCenter t₀ q c e u d Q - t • compositeVelocity q u d Q) =
    Matrix.toEuclideanLin R⁻¹
      (Matrix.toEuclideanLin Q⁻¹ (Y - c - t • u) - e - ((t - t₀) / q) • d) := by
  rw [composite_spatial_residual _ _ _ hq, Matrix.mul_inv_rev, euclideanLin_mul_apply]
  simp only [map_sub, euclideanLin_inv_cancel Q hQ, map_add, map_smul]
  module


theorem euclideanLin_norm_le (Q : Frame) (z : Spatial) :
    ‖Matrix.toEuclideanLin Q z‖ ≤ frameSize Q * ‖z‖ := by
  have hrow (i : Fin 2) :
      |(Matrix.toEuclideanLin Q z) i| ≤ (∑ j, |Q i j|) * ‖z‖ := by
    change |∑ j, Q i j * z j| ≤ _
    calc
      _ ≤ ∑ j, |Q i j * z j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, |Q i j| * ‖z‖ := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le z j) (abs_nonneg _)
      _ = _ := (Finset.sum_mul _ _ _).symm
  calc
    _ ≤ ∑ i : Fin 2, |(Matrix.toEuclideanLin Q z) i| := by
      simpa only [Fin.sum_univ_two] using
        Submission.Obl.k4_scalar_coefficient_clustering.plane_norm_le_abs_add
          (Matrix.toEuclideanLin Q z)
    _ ≤ ∑ i, (∑ j, |Q i j|) * ‖z‖ := Finset.sum_le_sum fun i _ => hrow i
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- Uniform control of the affine centers of a composed chart. -/
theorem composite_center_velocity_bound {t₀ q H H' : ℝ} {c e u d : Spatial} {Q : Frame}
    (hH : 1 ≤ H) (hH' : 1 ≤ H') (ht : |t₀| ≤ 1) (hq : |q⁻¹| ≤ H)
    (hcu : ‖c‖ + ‖u‖ ≤ H) (hed : ‖e‖ + ‖d‖ ≤ H') (hQ : frameSize Q ≤ H) :
    ‖compositeCenter t₀ q c e u d Q‖ + ‖compositeVelocity q u d Q‖ ≤ 4 * H ^ 2 * H' := by
  have hH0 : 0 ≤ H := le_trans zero_le_one hH
  have hH2 : H ≤ H ^ 2 := by nlinarith
  have htq : |t₀ / q| ≤ H := by
    rw [div_eq_mul_inv, abs_mul]
    exact (mul_le_mul ht hq (abs_nonneg _) zero_le_one).trans_eq (one_mul H)
  have hE : ‖Matrix.toEuclideanLin Q e‖ ≤ H * ‖e‖ :=
    (euclideanLin_norm_le Q e).trans (mul_le_mul_of_nonneg_right hQ (norm_nonneg _))
  have hD : ‖Matrix.toEuclideanLin Q d‖ ≤ H * ‖d‖ :=
    (euclideanLin_norm_le Q d).trans (mul_le_mul_of_nonneg_right hQ (norm_nonneg _))
  have hcent : ‖compositeCenter t₀ q c e u d Q‖ ≤
      ‖c‖ + H * ‖e‖ + H ^ 2 * ‖d‖ := by
    calc
      _ ≤ ‖c + Matrix.toEuclideanLin Q e‖ + ‖(t₀ / q) • Matrix.toEuclideanLin Q d‖ := norm_sub_le _ _
      _ ≤ (‖c‖ + ‖Matrix.toEuclideanLin Q e‖) + |t₀ / q| * ‖Matrix.toEuclideanLin Q d‖ := by
        rw [norm_smul, Real.norm_eq_abs]
        exact add_le_add (norm_add_le _ _) le_rfl
      _ ≤ ‖c‖ + H * ‖e‖ + H * (H * ‖d‖) :=
        add_le_add (add_le_add le_rfl hE) (mul_le_mul htq hD (norm_nonneg _) hH0)
      _ = _ := by ring
  have hvel : ‖compositeVelocity q u d Q‖ ≤ ‖u‖ + H ^ 2 * ‖d‖ := by
    calc
      _ ≤ ‖u‖ + ‖q⁻¹ • Matrix.toEuclideanLin Q d‖ := norm_add_le _ _
      _ = ‖u‖ + |q⁻¹| * ‖Matrix.toEuclideanLin Q d‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ‖u‖ + H * (H * ‖d‖) :=
        add_le_add le_rfl (mul_le_mul hq hD (norm_nonneg _) hH0)
      _ = _ := by ring
  have hHH' : H ≤ H ^ 2 * H' := by
    calc
      H ≤ H ^ 2 := hH2
      _ ≤ H ^ 2 * H' := by nlinarith [sq_nonneg H]
  calc
    _ ≤ (‖c‖ + ‖u‖) + H * ‖e‖ + 2 * H ^ 2 * ‖d‖ := by linarith [hcent, hvel]
    _ ≤ H + 2 * H ^ 2 * (‖e‖ + ‖d‖) := by
      have he : H * ‖e‖ ≤ H ^ 2 * ‖e‖ := mul_le_mul_of_nonneg_right hH2 (norm_nonneg _)
      nlinarith [mul_nonneg (sq_nonneg H) (norm_nonneg e)]
    _ ≤ H + 2 * H ^ 2 * H' := by gcongr
    _ ≤ _ := by nlinarith [sq_nonneg H]

end Submission.Obl.k4_native_finite_terminal_atlas_lift
