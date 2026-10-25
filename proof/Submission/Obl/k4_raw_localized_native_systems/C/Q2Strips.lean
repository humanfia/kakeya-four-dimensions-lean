import Submission.Obl.k4_raw_localized_native_systems.C.Q2Path

/-
Adapted from this LOT tree, o178, session x0596, `Q2Strips.lean` (commit ec5e1086),
renamed from `Submission.Obl.k4_unbounded_geometric_packet_reduction` into `Submission.Obl.k4_raw_localized_native_systems.C`.
-/

/-!
# Unit-interval strips of the charts along the good path

For a tagged incidence of the good path, its line stays in the chart
parallelogram enlarged by `s = 1 + 2 ⋅ 2^T` over the whole unit interval, and the
minor-axis normal position and velocity offsets are at most `√|det Q| κ s`.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.C

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- The unit-interval enlargement of a block of length `2^-T`. -/
def stripScale (T : ℕ) : ℝ := 1 + 2 * (2 : ℝ) ^ T

theorem stripScale_pos (T : ℕ) : 0 < stripScale T := by unfold stripScale; positivity

theorem stripScale_ge_one (T : ℕ) : 1 ≤ stripScale T := by
  unfold stripScale; have : (0 : ℝ) < (2 : ℝ) ^ T := by positivity
  linarith

theorem toEuclideanLin_smul_inv (Q : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Q.det ≠ 0) {s : ℝ}
    (hs : s ≠ 0) (w : Plane) :
    Matrix.toEuclideanLin (s • Q)⁻¹ w = s⁻¹ • Matrix.toEuclideanLin Q⁻¹ w := by
  letI : Invertible s := invertibleOfNonzero hs
  rw [Matrix.inv_smul Q s (isUnit_iff_ne_zero.mpr hQ), invOf_eq_inv, map_smul]
  simp

section

variable {p : Data} {k : ℕ} {a : Atlas p k} {M D : ℕ} {κ r : ℝ} {ex : Fin a.C → Prop}

/-- The parallelogram bound at both ends of the chart's block. -/
theorem ChartsHyp.ends (hc : ChartsHyp a M D κ r ex) (b : Fin a.C) {l : Line} (hl : l ∈ a.A b) :
    ‖Matrix.toEuclideanLin (a.Q b)⁻¹ (y l ((a.j b : ℕ) / (2 : ℝ) ^ a.T) - a.c b -
        ((a.j b : ℕ) / (2 : ℝ) ^ a.T) • a.u b)‖ ≤ κ ∧
      ‖Matrix.toEuclideanLin (a.Q b)⁻¹ (y l ((a.j b : ℕ) / (2 : ℝ) ^ a.T + 1 / (2 : ℝ) ^ a.T) -
        a.c b - ((a.j b : ℕ) / (2 : ℝ) ^ a.T + 1 / (2 : ℝ) ^ a.T) • a.u b)‖ ≤ κ := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ a.T := by positivity
  have hlt : ((a.j b : ℕ) : ℝ) / (2 : ℝ) ^ a.T ≤ (((a.j b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ a.T :=
    div_le_div_of_nonneg_right (by linarith) h2.le
  have hend : ((a.j b : ℕ) : ℝ) / (2 : ℝ) ^ a.T + 1 / (2 : ℝ) ^ a.T =
      (((a.j b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ a.T := by ring
  constructor
  · exact hc.frame b hl ⟨le_rfl, hlt⟩
  · rw [hend]; exact hc.frame b hl ⟨hlt, le_rfl⟩

theorem block_start_mem (a : Atlas p k) (b : Fin a.C) :
    ((a.j b : ℕ) : ℝ) / (2 : ℝ) ^ a.T ∈ Set.Icc (0 : ℝ) 1 := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ a.T := by positivity
  have hj : ((a.j b : ℕ) : ℝ) < (2 : ℝ) ^ a.T := by exact_mod_cast (a.j b).isLt
  constructor
  · positivity
  · rw [div_le_one h2]; linarith

/-- The enlarged frame contains the line over the whole unit interval. -/
theorem ChartsHyp.extend (hc : ChartsHyp a M D κ r ex) (b : Fin a.C) {l : Line} (hl : l ∈ a.A b)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖Matrix.toEuclideanLin (stripScale a.T • a.Q b)⁻¹ (y l t - a.c b - t • a.u b)‖ ≤ κ := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ a.T := by positivity
  obtain ⟨h₁, h₂⟩ := hc.ends b hl
  have hv := Submission.Lib.K4XInterface.velocity_le_of_two_times (a.Q b) (a.c b) (a.u b) l
    (show ((a.j b : ℕ) : ℝ) / (2 : ℝ) ^ a.T <
      ((a.j b : ℕ) : ℝ) / (2 : ℝ) ^ a.T + 1 / (2 : ℝ) ^ a.T by
        have : (0 : ℝ) < 1 / (2 : ℝ) ^ a.T := by positivity
        linarith) h₁ h₂
  rw [add_sub_cancel_left, div_div_eq_mul_div, div_one] at hv
  have hext := Submission.Lib.K4XInterface.gy_sub_extend_le (a.Q b) (a.c b) (a.u b) l h₁ hv t
  have htt : |t - ((a.j b : ℕ) : ℝ) / (2 : ℝ) ^ a.T| ≤ 1 := by
    have hm := block_start_mem a b
    rw [abs_le]; constructor <;> linarith [ht.1, ht.2, hm.1, hm.2]
  have hκ : 0 ≤ κ := (norm_nonneg _).trans h₁
  rw [toEuclideanLin_smul_inv _ (hc.det_ne b) (stripScale_pos a.T).ne', norm_smul,
    Real.norm_eq_abs, abs_inv, abs_of_pos (stripScale_pos a.T), inv_mul_le_iff₀ (stripScale_pos a.T)]
  calc ‖Matrix.toEuclideanLin (a.Q b)⁻¹ (y l t - a.c b - t • a.u b)‖
      ≤ κ + |t - ((a.j b : ℕ) : ℝ) / (2 : ℝ) ^ a.T| * (2 * κ * (2 : ℝ) ^ a.T) := hext
    _ ≤ κ + 1 * (2 * κ * (2 : ℝ) ^ a.T) := by gcongr
    _ = stripScale a.T * κ := by unfold stripScale; ring

/-- Minor-axis normal velocity offset. -/
theorem ChartsHyp.normal_velocity (hc : ChartsHyp a M D κ r ex) (b : Fin a.C) {l : Line}
    (hl : l ∈ a.A b) :
    |inner ℝ (minorNormal (a.Q b)) (v l - a.u b)| ≤
      minorWidth (a.Q b) * (κ * stripScale a.T) := by
  obtain ⟨h₁, h₂⟩ := hc.ends b hl
  have hq : (0 : ℝ) < 1 / (2 : ℝ) ^ a.T := by positivity
  have hv := abs_inner_velocity_le (hc.det_ne b) (a.c b) (a.u b) l
    (show ((a.j b : ℕ) : ℝ) / (2 : ℝ) ^ a.T <
      ((a.j b : ℕ) : ℝ) / (2 : ℝ) ^ a.T + 1 / (2 : ℝ) ^ a.T by linarith) h₁ h₂
  refine hv.trans ?_
  have hκ : 0 ≤ κ := (norm_nonneg _).trans h₁
  refine mul_le_mul_of_nonneg_left ?_ (minorWidth_nonneg _)
  rw [add_sub_cancel_left, div_div_eq_mul_div, div_one]
  unfold stripScale
  nlinarith [show (0 : ℝ) < (2 : ℝ) ^ a.T by positivity]

/-- Minor-axis normal position offset at time zero. -/
theorem ChartsHyp.normal_position_zero (hc : ChartsHyp a M D κ r ex) (b : Fin a.C) {l : Line}
    (hl : l ∈ a.A b) :
    |inner ℝ (minorNormal (a.Q b)) (y l 0 - a.c b)| ≤
      minorWidth (a.Q b) * (κ * stripScale a.T) := by
  obtain ⟨h₁, h₂⟩ := hc.ends b hl
  have hq : (0 : ℝ) < 1 / (2 : ℝ) ^ a.T := by positivity
  have h := abs_inner_offset_extend (hc.det_ne b) (a.c b) (a.u b) l hq (block_start_mem a b) h₁ h₂
    (t := 0) ⟨le_rfl, zero_le_one⟩
  rw [zero_smul, sub_zero] at h
  refine h.trans (le_of_eq ?_)
  unfold stripScale
  field_simp

end

end

end Submission.Obl.k4_raw_localized_native_systems.C
