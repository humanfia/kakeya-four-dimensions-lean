/- Adapted from this LOT tree, o197, session x0690, Pairing/ChartStrips.lean,
   branch snapshot 9f1b6476; preserving original attributions below. -/
/- Adapted from this LOT tree, o178, session x0596, commit aff0309c5b5be9920172fe7e367c31d64a3a01e3;
   Submission/Obl/k4_unbounded_geometric_packet_reduction/ChartStrips.lean.
   The original file and its provenance are preserved below. -/
import Submission.Obl.k4_finite_width_output_exclusion.Interfaces
import Submission.Obl.k4_raw_localized_native_systems.Pairing.VelocityPinning
import Submission.Lib.K4XInterface.Charts

/-!
# Normal strips of a chart parallelogram

For a chart frame `(c, u, Q)` on a dyadic block, the unit normal to the longer
column of `Q` sees the parallelogram `Q (ball κ)` with width `√|det Q| κ`.
Hence every trajectory assigned to the chart satisfies, over the whole unit
time interval, the normal position and normal velocity constraints used by
paired full-time binning (o175), with thickness `κ √(|det Q| 4^T)` up to a
factor three.  No lower bound on the major axis is needed.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.Pairing

open MeasureTheory
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- The two columns of a planar matrix. -/
def col0 (Q : Matrix (Fin 2) (Fin 2) ℝ) : Plane := WithLp.toLp 2 ![Q 0 0, Q 1 0]
def col1 (Q : Matrix (Fin 2) (Fin 2) ℝ) : Plane := WithLp.toLp 2 ![Q 0 1, Q 1 1]

/-- Rotation by a quarter turn. -/
def rot90 (a : Plane) : Plane := WithLp.toLp 2 ![-a 1, a 0]

/-- The longer column. -/
def longCol (Q : Matrix (Fin 2) (Fin 2) ℝ) : Plane :=
  if ‖col1 Q‖ ≤ ‖col0 Q‖ then col0 Q else col1 Q

/-- The shorter column. -/
def shortCol (Q : Matrix (Fin 2) (Fin 2) ℝ) : Plane :=
  if ‖col1 Q‖ ≤ ‖col0 Q‖ then col1 Q else col0 Q

/-- The unit normal to the longer column (the minor-axis normal). -/
def minorNormal (Q : Matrix (Fin 2) (Fin 2) ℝ) : Plane :=
  ‖longCol Q‖⁻¹ • rot90 (longCol Q)

@[simp] theorem col0_apply0 (Q : Matrix (Fin 2) (Fin 2) ℝ) : col0 Q 0 = Q 0 0 := by simp [col0]
@[simp] theorem col0_apply1 (Q : Matrix (Fin 2) (Fin 2) ℝ) : col0 Q 1 = Q 1 0 := by simp [col0]
@[simp] theorem col1_apply0 (Q : Matrix (Fin 2) (Fin 2) ℝ) : col1 Q 0 = Q 0 1 := by simp [col1]
@[simp] theorem col1_apply1 (Q : Matrix (Fin 2) (Fin 2) ℝ) : col1 Q 1 = Q 1 1 := by simp [col1]
@[simp] theorem rot90_apply0 (a : Plane) : rot90 a 0 = -a 1 := by simp [rot90]
@[simp] theorem rot90_apply1 (a : Plane) : rot90 a 1 = a 0 := by simp [rot90]

theorem norm_rot90 (a : Plane) : ‖rot90 a‖ = ‖a‖ := by
  have h1 := norm_sq_fin2' (rot90 a)
  have h2 := norm_sq_fin2' a
  simp only [rot90_apply0, rot90_apply1] at h1
  have : ‖rot90 a‖ ^ 2 = ‖a‖ ^ 2 := by rw [h1, h2]; ring
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this

theorem inner_rot90_self (a : Plane) : inner ℝ (rot90 a) a = 0 := by
  rw [inner_fin2]; simp; ring

/-- The applied matrix is the column combination. -/
theorem toEuclideanLin_fin2_eq (Q : Matrix (Fin 2) (Fin 2) ℝ) (w : Plane) :
    Matrix.toEuclideanLin Q w = w 0 • col0 Q + w 1 • col1 Q := by
  ext i
  fin_cases i <;>
    simp [Matrix.toEuclideanLin, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

theorem det_eq_cross (Q : Matrix (Fin 2) (Fin 2) ℝ) :
    Q.det = cross2 (col0 Q) (col1 Q) := by
  rw [Matrix.det_fin_two, cross2]; simp; ring

theorem abs_det_le_mul_norm (Q : Matrix (Fin 2) (Fin 2) ℝ) :
    |Q.det| ≤ ‖col0 Q‖ * ‖col1 Q‖ := by
  rw [det_eq_cross, cross2]
  have h0 := norm_sq_fin2' (col0 Q)
  have h1 := norm_sq_fin2' (col1 Q)
  have key : (col0 Q 0 * col1 Q 1 - col0 Q 1 * col1 Q 0) ^ 2 ≤ (‖col0 Q‖ * ‖col1 Q‖) ^ 2 := by
    rw [mul_pow, h0, h1]
    nlinarith [sq_nonneg (col0 Q 0 * col1 Q 0 + col0 Q 1 * col1 Q 1)]
  exact abs_le_of_sq_le_sq key (by positivity)

/-- A ratio bounded by the larger factor is at most the square root. -/
theorem div_le_sqrt_of_le_sq {D a : ℝ} (hD : 0 ≤ D) (ha : 0 < a) (h : D ≤ a ^ 2) :
    D / a ≤ Real.sqrt D := by
  rw [div_le_iff₀ ha]
  have hs := Real.sq_sqrt hD
  have hs0 := Real.sqrt_nonneg D
  have : Real.sqrt D ≤ a := by
    rw [Real.sqrt_le_left]
    · exact h
    · exact ha.le
  nlinarith

theorem longCol_norm_ge (Q : Matrix (Fin 2) (Fin 2) ℝ) :
    ‖col0 Q‖ ≤ ‖longCol Q‖ ∧ ‖col1 Q‖ ≤ ‖longCol Q‖ := by
  unfold longCol
  split_ifs with h
  · exact ⟨le_rfl, h⟩
  · exact ⟨(lt_of_not_ge h).le, le_rfl⟩

theorem abs_det_le_longCol_sq (Q : Matrix (Fin 2) (Fin 2) ℝ) :
    |Q.det| ≤ ‖longCol Q‖ ^ 2 := by
  have h := abs_det_le_mul_norm Q
  obtain ⟨h0, h1⟩ := longCol_norm_ge Q
  calc |Q.det| ≤ ‖col0 Q‖ * ‖col1 Q‖ := h
    _ ≤ ‖longCol Q‖ * ‖longCol Q‖ := by gcongr
    _ = ‖longCol Q‖ ^ 2 := by ring

theorem longCol_norm_pos {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0) :
    0 < ‖longCol Q‖ := by
  have h := abs_det_le_longCol_sq Q
  have hpos : 0 < |Q.det| := abs_pos.mpr hQ
  by_contra hle
  push Not at hle
  have h0 : ‖longCol Q‖ = 0 := le_antisymm hle (norm_nonneg _)
  rw [h0] at h
  linarith

theorem norm_minorNormal {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0) :
    ‖minorNormal Q‖ = 1 := by
  have hpos := longCol_norm_pos hQ
  rw [minorNormal, norm_smul, norm_rot90, Real.norm_eq_abs, abs_inv,
    abs_of_pos hpos, inv_mul_cancel₀ hpos.ne']

/-- The minor width of a frame: `|det Q|` divided by its longer column. -/
def minorWidth (Q : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := |Q.det| / ‖longCol Q‖

theorem minorWidth_nonneg (Q : Matrix (Fin 2) (Fin 2) ℝ) : 0 ≤ minorWidth Q :=
  div_nonneg (abs_nonneg _) (norm_nonneg _)

theorem minorWidth_le_sqrt {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0) :
    minorWidth Q ≤ Real.sqrt |Q.det| :=
  div_le_sqrt_of_le_sq (abs_nonneg Q.det) (longCol_norm_pos hQ) (abs_det_le_longCol_sq Q)

/-- The minor-axis normal sees the image of a vector with the minor width. -/
theorem abs_inner_minorNormal_le {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0) (w : Plane) :
    |inner ℝ (minorNormal Q) (Matrix.toEuclideanLin Q w)| ≤ minorWidth Q * ‖w‖ := by
  have hpos := longCol_norm_pos hQ
  have hw0 := abs_coord_le_norm_fin2 w 0
  have hw1 := abs_coord_le_norm_fin2 w 1
  rw [toEuclideanLin_fin2_eq, minorNormal, inner_smul_left, inner_add_right,
    inner_smul_right, inner_smul_right]
  simp only [conj_trivial]
  unfold minorWidth
  unfold longCol at hpos ⊢
  split_ifs with h
  · rw [if_pos h] at hpos
    have hz : inner ℝ (rot90 (col0 Q)) (col0 Q) = 0 := inner_rot90_self _
    have hd : inner ℝ (rot90 (col0 Q)) (col1 Q) = Q.det := by
      rw [inner_fin2, det_eq_cross, cross2]; simp; ring
    rw [hz, hd, mul_zero, zero_add, abs_mul, abs_mul, abs_inv, abs_norm]
    calc ‖col0 Q‖⁻¹ * (|w 1| * |Q.det|) = (|Q.det| / ‖col0 Q‖) * |w 1| := by
          field_simp
      _ ≤ (|Q.det| / ‖col0 Q‖) * ‖w‖ := by gcongr
  · rw [if_neg h] at hpos
    have hz : inner ℝ (rot90 (col1 Q)) (col1 Q) = 0 := inner_rot90_self _
    have hd : inner ℝ (rot90 (col1 Q)) (col0 Q) = -Q.det := by
      rw [inner_fin2, det_eq_cross, cross2]; simp; ring
    rw [hz, hd, mul_zero, add_zero, abs_mul, abs_mul, abs_inv, abs_norm, abs_neg]
    calc ‖col1 Q‖⁻¹ * (|w 0| * |Q.det|) = (|Q.det| / ‖col1 Q‖) * |w 0| := by
          field_simp
      _ ≤ (|Q.det| / ‖col1 Q‖) * ‖w‖ := by gcongr

/-! ## Chart-level strips -/

theorem y_sub_y (l : Line) (s t : ℝ) : y l t - y l s = (t - s) • v l := by
  ext i
  fin_cases i <;> simp [y, x, v] <;> ring

theorem y_offset_eq (l : Line) (c u : Plane) (s t : ℝ) :
    y l t - c - t • u = (y l s - c - s • u) + (t - s) • (v l - u) := by
  have h := y_sub_y l s t
  rw [smul_sub, ← h, sub_smul]
  abel

/-- The normal position offset at a time where the parallelogram bound holds. -/
theorem abs_inner_offset_le {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0) {κ : ℝ}
    {w : Plane} (hw : ‖Matrix.toEuclideanLin Q⁻¹ w‖ ≤ κ) :
    |inner ℝ (minorNormal Q) w| ≤ minorWidth Q * κ := by
  have h := abs_inner_minorNormal_le hQ (Matrix.toEuclideanLin Q⁻¹ w)
  rw [Submission.Lib.K4XInterface.toEuclideanLin_inv_cancel Q hQ] at h
  exact h.trans (mul_le_mul_of_nonneg_left hw (minorWidth_nonneg Q))

/-- Two times of the block confine the normal velocity. -/
theorem abs_inner_velocity_le {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0)
    (c u : Plane) (l : Line) {t₁ t₂ κ : ℝ} (h12 : t₁ < t₂)
    (h₁ : ‖Matrix.toEuclideanLin Q⁻¹ (y l t₁ - c - t₁ • u)‖ ≤ κ)
    (h₂ : ‖Matrix.toEuclideanLin Q⁻¹ (y l t₂ - c - t₂ • u)‖ ≤ κ) :
    |inner ℝ (minorNormal Q) (v l - u)| ≤ minorWidth Q * (2 * κ / (t₂ - t₁)) := by
  have hpos : 0 < t₂ - t₁ := sub_pos.mpr h12
  have a1 := abs_inner_offset_le hQ h₁
  have a2 := abs_inner_offset_le hQ h₂
  have heq : y l t₂ - c - t₂ • u - (y l t₁ - c - t₁ • u) = (t₂ - t₁) • (v l - u) := by
    rw [y_offset_eq l c u t₁ t₂]; abel
  have hin : inner ℝ (minorNormal Q) (v l - u) =
      (inner ℝ (minorNormal Q) (y l t₂ - c - t₂ • u) -
        inner ℝ (minorNormal Q) (y l t₁ - c - t₁ • u)) / (t₂ - t₁) := by
    rw [← inner_sub_right, heq, inner_smul_right]
    field_simp
  rw [hin, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  have := abs_sub (inner ℝ (minorNormal Q) (y l t₂ - c - t₂ • u))
    (inner ℝ (minorNormal Q) (y l t₁ - c - t₁ • u))
  have hs : 0 ≤ minorWidth Q := minorWidth_nonneg Q
  calc _ ≤ minorWidth Q * κ + minorWidth Q * κ := this.trans (add_le_add a2 a1)
    _ = minorWidth Q * (2 * κ / (t₂ - t₁)) * (t₂ - t₁) := by field_simp; ring

/-- Normal strip data of a chart, valid over the whole unit interval: if the
parallelogram bound holds at the two ends of a block `[t₀, t₀ + q]`, then for
every `t ∈ [0, 1]` the normal offset is at most `√|det Q| κ (1 + 2/q)`. -/
theorem abs_inner_offset_extend {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0)
    (c u : Plane) (l : Line) {t₀ q κ : ℝ} (hq : 0 < q) (ht₀ : t₀ ∈ Set.Icc (0 : ℝ) 1)
    (h₁ : ‖Matrix.toEuclideanLin Q⁻¹ (y l t₀ - c - t₀ • u)‖ ≤ κ)
    (h₂ : ‖Matrix.toEuclideanLin Q⁻¹ (y l (t₀ + q) - c - (t₀ + q) • u)‖ ≤ κ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |inner ℝ (minorNormal Q) (y l t - c - t • u)| ≤ minorWidth Q * (κ * (1 + 2 / q)) := by
  have hv := abs_inner_velocity_le hQ c u l (by linarith : t₀ < t₀ + q) h₁ h₂
  rw [show t₀ + q - t₀ = q by ring] at hv
  have a1 := abs_inner_offset_le hQ h₁
  rw [y_offset_eq l c u t₀ t, inner_add_right, inner_smul_right]
  have htt : |t - t₀| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [ht.1, ht.2, ht₀.1, ht₀.2]
  have hs : 0 ≤ minorWidth Q := minorWidth_nonneg Q
  have hκ : 0 ≤ κ := (norm_nonneg _).trans h₁
  calc |inner ℝ (minorNormal Q) (y l t₀ - c - t₀ • u) +
        (t - t₀) * inner ℝ (minorNormal Q) (v l - u)|
      ≤ |inner ℝ (minorNormal Q) (y l t₀ - c - t₀ • u)| +
          |t - t₀| * |inner ℝ (minorNormal Q) (v l - u)| := by
        rw [← abs_mul]; exact abs_add_le _ _
    _ ≤ minorWidth Q * κ + 1 * (minorWidth Q * (2 * κ / q)) := by
        gcongr
    _ = minorWidth Q * (κ * (1 + 2 / q)) := by ring

end

end Submission.Obl.k4_raw_localized_native_systems.Pairing
