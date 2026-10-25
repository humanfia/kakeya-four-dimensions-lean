/-
Adapted from: here:o204
Original file: Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/Frames.lean.
Adapted there from LOT obligation o116, branch x0389, commit e3859a9b,
Submission/Obl/k4_isotropic_residual_candidates/Frames.lean.
-/
import Submission.Lib.K4NativePreparationNumerics.AffineStripTransfer
import Mathlib.Tactic.Module

/-! Generic two-dimensional inverse-frame, action and affine-motion bounds. -/

namespace Submission.Lib.K4NativePreparationNumerics

open scoped BigOperators

theorem euclidean_norm_le_sum_abs {ι : Type*} [Fintype ι] (w : EuclideanSpace ℝ ι) :
    ‖w‖ ≤ ∑ i, |w i| := by
  classical
  let f : ι → EuclideanSpace ℝ ι := fun i => PiLp.single 2 i (w i)
  have hsum : (∑ i, f i) = w := by
    ext j
    simp [f]
  calc
    _ = ‖∑ i, f i‖ := congrArg norm hsum.symm
    _ ≤ ∑ i, ‖f i‖ := norm_sum_le _ _
    _ = _ := by simp [f, PiLp.norm_single, Real.norm_eq_abs]

/-- An entry-sum frame bound controls its Euclidean action without a change
in the power of the frame size. -/
theorem matrix_action_norm_le_entry_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (Q : Matrix ι κ ℝ) (w : EuclideanSpace ℝ κ) :
    ‖Matrix.toEuclideanLin Q w‖ ≤ (∑ i, ∑ j, |Q i j|) * ‖w‖ := by
  have hcoord (i : ι) : |Matrix.toEuclideanLin Q w i| ≤ (∑ j, |Q i j|) * ‖w‖ := by
    change |∑ j, Q i j * w j| ≤ _
    calc
      _ ≤ ∑ j, |Q i j * w j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, |Q i j| * ‖w‖ := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le w j) (abs_nonneg _)
      _ = _ := (Finset.sum_mul _ _ _).symm
  calc
    _ ≤ ∑ i, |Matrix.toEuclideanLin Q w i| := euclidean_norm_le_sum_abs _
    _ ≤ ∑ i, (∑ j, |Q i j|) * ‖w‖ := Finset.sum_le_sum fun i _ => hcoord i
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- In two spatial dimensions the adjugate preserves the sum of absolute
entries, so this inverse bound loses no dimension-dependent exponent. -/
theorem inverse_entry_sum_two (Q : Matrix (Fin 2) (Fin 2) ℝ) :
    (∑ i, ∑ j, |Q⁻¹ i j|) = (∑ i, ∑ j, |Q i j|) / |Q.det| := by
  rw [Matrix.inv_def, Matrix.adjugate_fin_two]
  simp [Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv,
    abs_mul, abs_inv, div_eq_mul_inv]
  ring

/-- A normalized determinant floor controls the inverse of a small frame. -/
theorem normalized_inverse_frame_bound {Q : Matrix (Fin 2) (Fin 2) ℝ}
    {q κ a : ℝ} (hq : 0 < q) (hκ : 0 ≤ κ) (ha : 0 < a)
    (hsize : (∑ i, ∑ j, |Q i j|) ≤ κ * q) (hdet : a * q ^ 2 ≤ |Q.det|) :
    q * (∑ i, ∑ j, |Q⁻¹ i j|) ≤ κ / a := by
  have hdetpos : 0 < |Q.det| := lt_of_lt_of_le (by positivity) hdet
  rw [inverse_entry_sum_two, ← mul_div_assoc]
  apply (div_le_div_iff₀ hdetpos ha).mpr
  have hsize' := mul_le_mul_of_nonneg_left hsize (mul_nonneg hq.le ha.le)
  have hdet' := mul_le_mul_of_nonneg_left hdet hκ
  nlinarith

/-- An invertible frame converts a normalized fit back to physical size. -/
theorem physical_error_le_of_frame {q κ : ℝ} {Q : Matrix (Fin 2) (Fin 2) ℝ}
    (hQ : Q.det ≠ 0) (hκ : 0 ≤ κ) (hq : 0 < q)
    (hsize : (∑ i, ∑ j, |Q i j|) ≤ κ * q)
    {e : EuclideanSpace ℝ (Fin 2)} (hfit : ‖Matrix.toEuclideanLin Q⁻¹ e‖ ≤ κ) :
    ‖e‖ ≤ κ ^ 2 * q := by
  have hid : Matrix.toEuclideanLin Q (Matrix.toEuclideanLin Q⁻¹ e) = e := by
    have hmul := congrArg (fun L => L e) (Matrix.toLpLin_mul 2 2 2 Q Q⁻¹)
    rw [Matrix.mul_nonsing_inv Q (isUnit_iff_ne_zero.mpr hQ), Matrix.toLpLin_one] at hmul
    exact hmul.symm
  calc
    _ = ‖Matrix.toEuclideanLin Q (Matrix.toEuclideanLin Q⁻¹ e)‖ := congrArg norm hid.symm
    _ ≤ (∑ i, ∑ j, |Q i j|) * ‖Matrix.toEuclideanLin Q⁻¹ e‖ :=
      matrix_action_norm_le_entry_sum _ _
    _ ≤ (κ * q) * κ := mul_le_mul hsize hfit (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- The two endpoints of a fitted affine trajectory control its velocity
error in units of the block length. -/
theorem affine_velocity_bound {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a v c u : V) (t q K : ℝ) (hq : 0 < q)
    (hstart : ‖a + t • v - c - t • u‖ ≤ K * q)
    (hend : ‖a + (t + q) • v - c - (t + q) • u‖ ≤ K * q) :
    ‖v - u‖ ≤ 2 * K := by
  have hid : q • (v - u) =
      (a + (t + q) • v - c - (t + q) • u) - (a + t • v - c - t • u) := by
    module
  have hnorm : q * ‖v - u‖ ≤ 2 * K * q := by
    calc
      _ = ‖q • (v - u)‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hq]
      _ ≤ ‖a + (t + q) • v - c - (t + q) • u‖ + ‖a + t • v - c - t • u‖ := by
        rw [hid]
        exact norm_sub_le _ _
      _ ≤ K * q + K * q := add_le_add hend hstart
      _ = _ := by ring
  nlinarith

/-- An occupied whole-block chart has bounded center and velocity from the
actual physical trajectory bounds, irrespective of its format exponent. -/
theorem affine_center_velocity_bound {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (a v c u : V) (t q E K : ℝ)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hq : 0 < q) (hq1 : q ≤ 1) (hE : 0 ≤ E)
    (hstart : ‖a + t • v - c - t • u‖ ≤ E * q)
    (hend : ‖a + (t + q) • v - c - (t + q) • u‖ ≤ E * q)
    (hy : ‖a + t • v‖ ≤ K) (hv : ‖v‖ ≤ K) :
    ‖u‖ ≤ K + 2 * E ∧ ‖c‖ ≤ 2 * K + 3 * E ∧ ‖c‖ + ‖u‖ ≤ 3 * K + 5 * E := by
  have hvel := affine_velocity_bound a v c u t q E hq hstart hend
  have hu : ‖u‖ ≤ K + 2 * E := by
    calc
      _ = ‖v - (v - u)‖ := by congr 1; abel
      _ ≤ ‖v‖ + ‖v - u‖ := norm_sub_le _ _
      _ ≤ K + 2 * E := add_le_add hv hvel
  have hc : ‖c‖ ≤ 2 * K + 3 * E := by
    have hid : c = (a + t • v) - (a + t • v - c - t • u) - t • u := by abel
    calc
      _ ≤ ‖a + t • v‖ + ‖a + t • v - c - t • u‖ + ‖t • u‖ := by
        conv_lhs => rw [hid]
        exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ K + E * q + t * ‖u‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
        exact add_le_add (add_le_add hy hstart) le_rfl
      _ ≤ K + E + ‖u‖ := by
        have hEq := mul_le_mul_of_nonneg_left hq1 hE
        have htu := mul_le_mul_of_nonneg_right ht1 (norm_nonneg u)
        nlinarith
      _ ≤ 2 * K + 3 * E := by linarith
  exact ⟨hu, hc, by linarith⟩

end Submission.Lib.K4NativePreparationNumerics
