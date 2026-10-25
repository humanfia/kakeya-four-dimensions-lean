/- Adapted from this LOT tree, obligation o201, session x0697, commit 74bd9a876bac,
   Submission/Obl/k4_horizontal_critical_rate_candidates/TrueBoxes.lean.
   Original source attributions below are preserved. -/
import Submission.Obl.k4_critical_intercept_concentration.OriginalMass
import Submission.Obl.k4_scalar_initial_true_horizon.Basic
import Submission.Obl.k4_critical_intercept_concentration.Inherited.ContactNormalization

namespace Submission.Obl.k4_critical_intercept_concentration

open Set MeasureTheory Inherited

noncomputable section

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

def midpoint (cfg : Data α) (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s)) : ℝ :=
  (((cfg.j k s i : ℕ) : ℝ) + 1 / 2) * cfg.timeLength k s

theorem timeLength_pos (cfg : Data α) (k : ℕ) (s : ℝ) : 0 < cfg.timeLength k s := by
  unfold timeLength
  positivity

theorem timeLength_le_one (cfg : Data α) (k : ℕ) (s : ℝ) : cfg.timeLength k s ≤ 1 := by
  unfold timeLength
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))

/-- The closed dyadic block has its exact midpoint and actual dyadic length. -/
theorem mem_I_time_gap (T : ℕ) (j : Fin (2 ^ T)) {t : ℝ} (ht : t ∈ I T j) :
    |t - (((j : ℕ) : ℝ) + 1 / 2) * ((2 : ℝ) ^ T)⁻¹| ≤ ((2 : ℝ) ^ T)⁻¹ / 2 := by
  change ((j : ℕ) : ℝ) / (2 : ℝ) ^ T ≤ t ∧
    t ≤ (((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T at ht
  simp only [div_eq_mul_inv] at ht
  apply abs_le.mpr
  constructor <;> nlinarith only [ht.1, ht.2]

/-- Every original full true assignment lies in its complete horizontal box.
The transverse ratio is converted to the actual time length using the same
squared slack that appears in the assignment count. -/
theorem AssignmentLevel.native_point_in_true_box (h : cfg.Valid) {k : ℕ} {s : ℝ}
    (a : cfg.AssignmentLevel k s) (i : Fin (cfg.n k s)) (l : α)
    (hl : l ∈ cfg.A k s i) {t : ℝ} (ht : t ∈ I (cfg.T k s) (cfg.j k s i)) :
    nativeHorizontalLine (cfg.b k l) t ∈ horizontalTrueBox (cfg.c k s i)
      (cfg.midpoint k s i) (cfg.timeLength k s) (cfg.K k ^ 2) := by
  have hK : 1 ≤ cfg.K k := h.subpower.1 k
  have hK0 : 0 ≤ cfg.K k := by linarith
  have hKpow : cfg.K k ≤ cfg.K k ^ 2 := by nlinarith
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hg := (time_length_comparison hN (by linarith : 0 < cfg.K k)
    a.time_lower a.time_upper).2
  change cfg.N k ^ (-cfg.κ * s) ≤ cfg.K k * cfg.timeLength k s at hg
  have hgeo := a.geometry i l hl t ht
  rw [h.horizontal_rate] at hgeo
  refine ⟨mem_I_time_gap _ _ ht, ?_, ?_⟩
  · exact hgeo.1.trans (mul_le_mul_of_nonneg_right hKpow (cfg.timeLength_pos k s).le)
  · have hscale : cfg.K k * cfg.timeLength k s * cfg.N k ^ (-cfg.κ * s) ≤
        cfg.K k ^ 2 * cfg.timeLength k s ^ 2 := by
      calc
        _ ≤ cfg.K k * cfg.timeLength k s * (cfg.K k * cfg.timeLength k s) :=
          mul_le_mul_of_nonneg_left hg (mul_nonneg hK0 (cfg.timeLength_pos k s).le)
        _ = _ := by ring
    exact hgeo.2.1.trans hscale

/-- The centered plane and tilt bounds apply to the same complete true box. -/
theorem AssignmentLevel.native_box_center_bounds (_h : cfg.Valid) {k : ℕ} {s : ℝ}
    (a : cfg.AssignmentLevel k s) (i : Fin (cfg.n k s)) :
    |cfg.c k s i 3 + cfg.c k s i 0 + cfg.midpoint k s i * cfg.c k s i 1| ≤
        cfg.K k * cfg.timeLength k s ∧
      |cfg.c k s i 4 - cfg.midpoint k s i| ≤ cfg.K k * cfg.timeLength k s := by
  have hsum := a.plane_center i
  constructor
  · exact (le_add_of_nonneg_right (abs_nonneg _)).trans hsum
  · exact (le_add_of_nonneg_left (abs_nonneg _)).trans hsum


/-- Complete true assignments have bounded base coordinates throughout their
actual time block. This uses the full geometric witness and no restriction
or renormalization of the trajectory prior. -/
theorem AssignmentLevel.native_base_bounds (h : cfg.Valid) {k : ℕ} {s : ℝ}
    (a : cfg.AssignmentLevel k s) (i : Fin (cfg.n k s)) (l : α)
    (hl : l ∈ cfg.A k s i) {t : ℝ} (ht : t ∈ I (cfg.T k s) (cfg.j k s i)) :
    |(cfg.x k l t) 1| ≤ 3 * cfg.K k ∧ |(cfg.x k l t) 2| ≤ 6 * cfg.K k ^ 2 := by
  have hK : 1 ≤ cfg.K k := h.subpower.1 k
  have hK0 : 0 ≤ cfg.K k := by linarith
  have hKsq : cfg.K k ≤ cfg.K k ^ 2 := by nlinarith
  have htime := Submission.Obl.k4_scalar_initial_true_horizon.I_subset_unit
    (cfg.T k s) (cfg.j k s i) ht
  have htabs : |t| ≤ 1 := by simpa only [abs_of_nonneg htime.1] using htime.2
  have hgeo := a.geometry i l hl t ht
  have hbox := a.native_point_in_true_box h i l hl ht
  have hq : cfg.timeLength k s ≤ 1 := cfg.timeLength_le_one k s
  have hq0 : 0 ≤ cfg.timeLength k s := (cfg.timeLength_pos k s).le
  have htcoeff (e : Fin 5) : |t * cfg.c k s i e| ≤ cfg.K k := by
    rw [abs_mul]
    exact (mul_le_mul htabs (a.coefficient_bound i e) (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hZ : |(cfg.x k l t) 1| ≤ 3 * cfg.K k := by
    calc
      _ = |((cfg.x k l t) 1 - cfg.c k s i 0 - t * cfg.c k s i 1) +
          cfg.c k s i 0 + t * cfg.c k s i 1| := by congr 1; ring
      _ ≤ |(cfg.x k l t) 1 - cfg.c k s i 0 - t * cfg.c k s i 1| +
          |cfg.c k s i 0| + |t * cfg.c k s i 1| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ cfg.K k * cfg.timeLength k s + cfg.K k + cfg.K k :=
        add_le_add (add_le_add hgeo.1 (a.coefficient_bound i 0)) (htcoeff 1)
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hq hK0]
  refine ⟨hZ, ?_⟩
  have herr : |(cfg.x k l t) 2 - cfg.c k s i 2 - t * cfg.c k s i 3 -
      cfg.c k s i 4 * (cfg.x k l t) 1| ≤ cfg.K k ^ 2 := by
    refine hbox.2.2.trans ?_
    have hq2 : cfg.timeLength k s ^ 2 ≤ 1 := by nlinarith
    exact (mul_le_mul_of_nonneg_left hq2 (sq_nonneg (cfg.K k))).trans_eq (mul_one _)
  calc
    _ = |((cfg.x k l t) 2 - cfg.c k s i 2 - t * cfg.c k s i 3 -
        cfg.c k s i 4 * (cfg.x k l t) 1) + cfg.c k s i 2 + t * cfg.c k s i 3 +
          cfg.c k s i 4 * (cfg.x k l t) 1| := by congr 1; ring
    _ ≤ |(cfg.x k l t) 2 - cfg.c k s i 2 - t * cfg.c k s i 3 -
          cfg.c k s i 4 * (cfg.x k l t) 1| + |cfg.c k s i 2| +
          |t * cfg.c k s i 3| + |cfg.c k s i 4 * (cfg.x k l t) 1| :=
      (abs_add_le _ _).trans
        (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
    _ ≤ cfg.K k ^ 2 + cfg.K k + cfg.K k + cfg.K k * (3 * cfg.K k) := by
      apply add_le_add (add_le_add (add_le_add herr (a.coefficient_bound i 2)) (htcoeff 3))
      rw [abs_mul]
      exact mul_le_mul (a.coefficient_bound i 4) hZ (abs_nonneg _) hK0
    _ ≤ _ := by nlinarith only [hKsq]

end Data

end

end Submission.Obl.k4_critical_intercept_concentration
