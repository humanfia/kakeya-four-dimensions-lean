-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.QuantitativeRows
import Submission.Obl.k4_finite_affine_parent_sources.NativeChildFrame
import Submission.Obl.k4_finite_affine_parent_sources.VelocityFrame
import Submission.Obl.k4_finite_affine_parent_sources.NativeOscillation
import Submission.Obl.k4_adapted_oscillation_tests.Glue

namespace Submission.Obl.k4_finite_affine_parent_sources

open Set Submission.Lib.K4XInterface

noncomputable section

/-- The three base coordinates in the chosen packet units. -/
def pointBaseS {α : Type} (b : α → Fin 6 → ℝ) (p : α × ℝ) :
    EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![p.2, b p.1 0 + p.2 * b p.1 3, b p.1 1 + p.2 * b p.1 4]

theorem nativeBase_pointS {α : Type} (b : α → Fin 6 → ℝ) (p : α × ℝ) :
    Submission.Obl.k4_stable_native_signal_oscillation.nativeBase (pointS b p) = pointBaseS b p := by
  ext e
  fin_cases e <;> rfl

lemma matrix_row_apply_abs_le (M : Matrix (Fin 2) (Fin 2) ℝ)
    (w : EuclideanSpace ℝ (Fin 2)) (e : Fin 2) :
    |(Matrix.toEuclideanLin M w) e| ≤ ‖frameRow M e‖ * ‖w‖ := by
  have heq : (Matrix.toEuclideanLin M w) e = inner ℝ (frameRow M e) w := by
    simp [toEuclideanLin_apply_fin2, frameRow, PiLp.inner_apply, Fin.sum_univ_two,
      RCLike.inner_apply, conj_trivial, mul_comm]
  rw [heq]
  exact abs_real_inner_le_norm _ _

lemma coordinate_le_of_inverse_frame
    (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : M.det ≠ 0)
    (w : EuclideanSpace ℝ (Fin 2)) (κ : ℝ)
    (hw : ‖Matrix.toEuclideanLin M⁻¹ w‖ ≤ κ) (e : Fin 2) :
    |w e| ≤ ‖frameRow M e‖ * κ := by
  have h := matrix_row_apply_abs_le M (Matrix.toEuclideanLin M⁻¹ w) e
  rw [toEuclideanLin_inv_cancel M hM] at h
  exact h.trans (mul_le_mul_of_nonneg_left hw (norm_nonneg _))

/-- An end label localizes the full three-dimensional base in the
earlier packet's units. Both relative rows are used, so no bound on a
raw hidden coordinate is assumed. -/
theorem pointBase_diameter_of_rows
    {α : Type} (b : α → Fin 6 → ℝ) (A : Set α)
    (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : M.det ≠ 0)
    (center speed : EuclideanSpace ℝ (Fin 2)) (a q κ H K : ℝ)
    (hq : 0 ≤ q) (hκ : 0 ≤ κ) (hH : 0 ≤ H) (hK : 0 ≤ K)
    (hrows : ∀ e : Fin 2, ‖frameRow M e‖ ≤ H * q)
    (hfit : ∀ l ∈ A, ∀ t ∈ Icc a (a + q),
      ‖Matrix.toEuclideanLin M⁻¹ (gy (0, b l) t - center - t • speed)‖ ≤ κ)
    (hvel : ∀ l ∈ A, ‖gv (0, b l)‖ ≤ K)
    (l : α) (hl : l ∈ A) (l' : α) (hl' : l' ∈ A)
    (t t' : ℝ) (ht : t ∈ Icc a (a + q)) (ht' : t' ∈ Icc a (a + q)) :
    ‖pointBaseS b (l, t) - pointBaseS b (l', t')‖ ≤ (1 + 4 * κ * H + 2 * K) * q := by
  have htime : |t - t'| ≤ q := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2, ht'.1, ht'.2]
  have hfixed : ∀ e : Fin 2,
      |(gy (0, b l) t - gy (0, b l') t) e| ≤ 2 * κ * H * q := by
    have heq : gy (0, b l) t - gy (0, b l') t =
        (gy (0, b l) t - center - t • speed) -
          (gy (0, b l') t - center - t • speed) := by abel
    have hdiff : ‖Matrix.toEuclideanLin M⁻¹ (gy (0, b l) t - gy (0, b l') t)‖ ≤ 2 * κ := by
      rw [heq, map_sub]
      exact (norm_sub_le _ _).trans ((add_le_add (hfit l hl t ht) (hfit l' hl' t ht)).trans_eq (by ring))
    intro e
    have h := coordinate_le_of_inverse_frame M hM _ (2 * κ) hdiff e
    exact h.trans ((mul_le_mul_of_nonneg_right (hrows e) (by positivity)).trans_eq (by ring))
  have hspatial : ∀ e : Fin 2,
      |(gy (0, b l) t - gy (0, b l') t') e| ≤ (2 * κ * H + K) * q := by
    intro e
    have heq : gy (0, b l) t - gy (0, b l') t' =
        (gy (0, b l) t - gy (0, b l') t) + (t - t') • gv (0, b l') := by
      rw [← gy_sub_gy (0, b l') t' t]
      abel
    have hv : |(gv (0, b l')) e| ≤ K := by
      simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le (gv (0, b l')) e).trans (hvel l' hl')
    rw [heq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    calc
      _ ≤ |(gy (0, b l) t - gy (0, b l') t) e| + |t - t'| * |gv (0, b l') e| := by
        simpa only [abs_mul] using abs_add_le ((gy (0, b l) t - gy (0, b l') t) e)
          ((t - t') * gv (0, b l') e)
      _ ≤ 2 * κ * H * q + q * K :=
        add_le_add (hfixed e) (mul_le_mul htime hv (abs_nonneg _) hq)
      _ = _ := by ring
  have hnorm : ∀ w : EuclideanSpace ℝ (Fin 3), ‖w‖ ≤ ∑ e : Fin 3, |w e| := by
    intro w
    simpa only [ContinuousLinearMap.id_apply] using
      Submission.Obl.k4_adapted_oscillation_tests.norm_apply_le_sum_abs
        (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3))) (by intro e; simp) w
  calc
    _ ≤ ∑ e : Fin 3, |(pointBaseS b (l, t) - pointBaseS b (l', t')) e| := hnorm _
    _ = |t - t'| + |(gy (0, b l) t - gy (0, b l') t') 0| +
        |(gy (0, b l) t - gy (0, b l') t') 1| := by
      simp [pointBaseS, Fin.sum_univ_succ, gy, gx, add_assoc]
    _ ≤ q + (2 * κ * H + K) * q + (2 * κ * H + K) * q :=
      add_le_add (add_le_add htime (hspatial 0)) (hspatial 1)
    _ = _ := by ring

/-- In the common geometric slack this is the requested `K*q_end/q_s`
localization, with the same `16H^4` budget as the tracking rows. -/
theorem pointBase_diameter_model_budget
    {α : Type} (b : α → Fin 6 → ℝ) (A : Set α)
    (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : M.det ≠ 0)
    (center speed : EuclideanSpace ℝ (Fin 2)) (a q κ H K : ℝ)
    (hq : 0 ≤ q) (hκ : 0 ≤ κ) (hK : 0 ≤ K)
    (hH : 1 ≤ H) (hκH : κ ≤ H) (hKH : K ≤ H)
    (hrows : ∀ e : Fin 2, ‖frameRow M e‖ ≤ H * q)
    (hfit : ∀ l ∈ A, ∀ t ∈ Icc a (a + q),
      ‖Matrix.toEuclideanLin M⁻¹ (gy (0, b l) t - center - t • speed)‖ ≤ κ)
    (hvel : ∀ l ∈ A, ‖gv (0, b l)‖ ≤ K)
    (l : α) (hl : l ∈ A) (l' : α) (hl' : l' ∈ A)
    (t t' : ℝ) (ht : t ∈ Icc a (a + q)) (ht' : t' ∈ Icc a (a + q)) :
    ‖pointBaseS b (l, t) - pointBaseS b (l', t')‖ ≤ 16 * H ^ 4 * q := by
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hH2 : H ≤ H ^ 2 := by nlinarith [mul_nonneg hH0 (sub_nonneg.mpr hH)]
  have hH24 : H ^ 2 ≤ H ^ 4 := by
    nlinarith [mul_nonneg (sq_nonneg H) (sub_nonneg.mpr (hH.trans hH2))]
  have hmul : κ * H ≤ H ^ 2 := by simpa only [pow_two] using mul_le_mul_of_nonneg_right hκH hH0
  have hbudget : 1 + 4 * κ * H + 2 * K ≤ 16 * H ^ 4 := by
    nlinarith only [hH, hH2, hH24, hmul, hKH, pow_nonneg hH0 4]
  exact (pointBase_diameter_of_rows b A M hM center speed a q κ H K hq hκ hH0 hK
    hrows hfit hvel l hl l' hl' t t' ht ht').trans (mul_le_mul_of_nonneg_right hbudget hq)

/-- The position-row upper bound includes the exact native time ratio. -/
theorem position_rows_of_relative_velocity_rows
    (M : Matrix (Fin 2) (Fin 2) ℝ) (q H : ℝ) (hq : 0 < q)
    (hrows : ∀ e : Fin 2, ‖frameRow (q⁻¹ • M) e‖ ≤ H) :
    ∀ e : Fin 2, ‖frameRow M e‖ ≤ H * q := by
  intro e
  have h := hrows e
  have heq : ‖frameRow (q⁻¹ • M) e‖ = ‖frameRow M e‖ / q := by
    rw [frameRow_norm_smul, abs_inv, abs_of_pos hq]
    ring
  rw [heq] at h
  exact (div_le_iff₀ hq).mp h

/-- An actual end label localizes the base in the earlier packet frame
by its exact relative time length. The earlier frame may be its original
chart frame: no orthogonal major-axis replacement is required here. -/
theorem PFrame.end_label_base_diameter
    (Φ : PFrame) (hq₀ : 0 < Φ.F.q) (hD : Φ.F.D.det ≠ 0)
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Q.det ≠ 0)
    (c u : EuclideanSpace ℝ (Fin 2)) (A : Set Trajectory)
    (t₁ q₁ κ H K : ℝ) (hq₁ : 0 < q₁) (hκ : 0 ≤ κ) (hK : 0 ≤ K)
    (hH : 1 ≤ H) (hκH : κ ≤ H) (hKH : K ≤ H)
    (hrows : ∀ e : Fin 2,
      ‖frameRow (relativeVelocityFrame Φ.F.q q₁ Φ.F.D Q) e‖ ≤ H)
    (hfit : ∀ l ∈ A, ∀ t ∈ Icc t₁ (t₁ + q₁),
      ‖Matrix.toEuclideanLin Q⁻¹ (gy l t - c - t • u)‖ ≤ κ)
    (hvel : ∀ l ∈ A, ‖gv (0, Φ.eb l)‖ ≤ K)
    (l : Trajectory) (hl : l ∈ A) (l' : Trajectory) (hl' : l' ∈ A)
    (t t' : ℝ) (ht : t ∈ Icc t₁ (t₁ + q₁)) (ht' : t' ∈ Icc t₁ (t₁ + q₁)) :
    ‖pointBaseS Φ.eb (l, (t - Φ.F.t₀) / Φ.F.q) -
        pointBaseS Φ.eb (l', (t' - Φ.F.t₀) / Φ.F.q)‖ ≤
      16 * H ^ 4 * (q₁ / Φ.F.q) := by
  let q := q₁ / Φ.F.q
  let a := (t₁ - Φ.F.t₀) / Φ.F.q
  have hq : 0 < q := div_pos hq₁ hq₀
  have ha : a + q = (t₁ + q₁ - Φ.F.t₀) / Φ.F.q := by dsimp [a, q]; ring
  have hI : ∀ s ∈ Icc a (a + q), Φ.F.t₀ + Φ.F.q * s ∈ Icc t₁ (t₁ + q₁) := by
    intro s hs
    have hlo : (t₁ - Φ.F.t₀) / Φ.F.q ≤ s := hs.1
    have hhi : s ≤ (t₁ + q₁ - Φ.F.t₀) / Φ.F.q := by simpa only [ha] using hs.2
    have h0 := (div_le_iff₀ hq₀).mp hlo
    have h1 := (le_div_iff₀ hq₀).mp hhi
    constructor <;> nlinarith only [h0, h1]
  have hmem : ∀ r ∈ Icc t₁ (t₁ + q₁), (r - Φ.F.t₀) / Φ.F.q ∈ Icc a (a + q) := by
    intro r hr
    constructor
    · exact div_le_div_of_nonneg_right (by linarith only [hr.1]) hq₀.le
    · rw [ha]
      exact div_le_div_of_nonneg_right (by linarith only [hr.2]) hq₀.le
  have hnativeFit := Φ.child_fit hq₀.ne' hD Q c u A (Icc t₁ (t₁ + q₁)) (Icc a (a + q))
    κ hI hfit
  have hnativeRows : ∀ e : Fin 2, ‖frameRow (Φ.childMatrix Q) e‖ ≤ H * q := by
    apply position_rows_of_relative_velocity_rows (Φ.childMatrix Q) q H hq
    simpa only [q, PFrame.childMatrix, relativeVelocityFrame, inv_div] using hrows
  exact pointBase_diameter_model_budget Φ.eb A (Φ.childMatrix Q)
    (Φ.childMatrix_det_ne_zero hD Q hQ) (Φ.childCenter c u) (Φ.childSpeed u)
    a q κ H K hq.le hκ hK hH hκH hKH hnativeRows hnativeFit hvel
    l hl l' hl' ((t - Φ.F.t₀) / Φ.F.q) ((t' - Φ.F.t₀) / Φ.F.q)
    (hmem t ht) (hmem t' ht')

end

end Submission.Obl.k4_finite_affine_parent_sources
