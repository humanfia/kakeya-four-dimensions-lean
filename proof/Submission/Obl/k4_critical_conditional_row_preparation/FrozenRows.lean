import Submission.Obl.k4_critical_conditional_row_preparation.AffineEntries
import Submission.Obl.k4_critical_conditional_row_preparation.NativeNormalization
import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.ShortSegments
import Submission.Obl.k4_profile_density_bounds.Asymptotics

namespace Submission.Obl.k4_critical_conditional_row_preparation
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal

namespace Data
variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- Empty fitted sets may use zero; every other entry has the original
whole-block fit and uniformly bounded nonconstant coefficients. -/
theorem AssignmentLevel.exists_bounded_entry (h : cfg.Valid) {k : ℕ} {s : ℝ}
    (a : cfg.AssignmentLevel k s) (hs : 0 ≤ s) (i : Fin (cfg.n k s)) :
    ∃ L : Fin 4 → ℝ, (∀ e : Fin 3, |L e.succ| ≤ 8 * cfg.K k ^ 4) ∧
      ∀ l ∈ cfg.B k s i, ∀ t ∈ I (cfg.T k s) (cfg.j k s i),
        |affineResidualIntercept L (cfg.b k l) + t * affineResidualSlope L (cfg.b k l)| ≤
          cfg.K k * cfg.N k ^ (-s) := by
  classical
  by_cases hB : (cfg.B k s i).Nonempty
  · obtain ⟨l, hl⟩ := hB
    obtain ⟨L, _, hL, hf⟩ := a.active_affine_entry h hs i l hl
      (cfg.leftTime k s i) (cfg.leftTime_mem k s i)
    exact ⟨L, hL, hf⟩
  · refine ⟨0, ?_, ?_⟩
    · intro e
      simp only [Pi.zero_apply, abs_zero]
      positivity
    · intro l hl
      exact (hB ⟨l, hl⟩).elim

def frozenRow (cfg : Data α) (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s))
    (L : Fin 4 → ℝ) : Fin 2 → ℝ :=
  ![L 1 - cfg.horizontalOrigin k s i * L 3, L 2 + cfg.leftTime k s i * L 3]

theorem AssignmentLevel.frozenRow_bound (h : cfg.Valid) {k : ℕ} {s : ℝ}
    (a : cfg.AssignmentLevel k s) (i : Fin (cfg.n k s)) (L : Fin 4 → ℝ)
    (hL : ∀ e : Fin 3, |L e.succ| ≤ 8 * cfg.K k ^ 4) :
    ∀ e, |cfg.frozenRow k s i L e| ≤ 32 * cfg.K k ^ 5 := by
  have hK : 1 ≤ cfg.K k := h.subpower.1 k
  have hK0 : 0 ≤ cfg.K k := by linarith
  have h45 : cfg.K k ^ 4 ≤ cfg.K k ^ 5 := pow_le_pow_right₀ hK (by norm_num)
  have h1 : |L 1| ≤ 8 * cfg.K k ^ 4 := hL 0
  have h2 : |L 2| ≤ 8 * cfg.K k ^ 4 := hL 1
  have h3 : |L 3| ≤ 8 * cfg.K k ^ 4 := hL 2
  intro e
  fin_cases e
  · change |L 1 - cfg.horizontalOrigin k s i * L 3| ≤ _
    have hm : |cfg.horizontalOrigin k s i * L 3| ≤ 16 * cfg.K k ^ 5 := by
      rw [abs_mul]
      calc
        _ ≤ (2 * cfg.K k) * (8 * cfg.K k ^ 4) :=
          mul_le_mul (a.horizontalOrigin_bound h i) h3 (abs_nonneg _) (by positivity)
        _ = _ := by ring
    exact (abs_sub _ _).trans (by nlinarith only [h1, hm, h45, pow_nonneg hK0 5])
  · change |L 2 + cfg.leftTime k s i * L 3| ≤ _
    have hm : |cfg.leftTime k s i * L 3| ≤ 8 * cfg.K k ^ 4 := by
      rw [abs_mul]
      exact (mul_le_mul (cfg.leftTime_abs_le_one k s i) h3 (abs_nonneg _)
        (by norm_num)).trans_eq (one_mul _)
    exact (abs_add_le _ _).trans (by nlinarith only [h2, hm, h45, pow_nonneg hK0 5])

theorem AssignmentLevel.horizontal_displacement {k : ℕ} {s : ℝ}
    (a : cfg.AssignmentLevel k s) (i : Fin (cfg.n k s)) (l : α)
    (hl : l ∈ cfg.A k s i) (t : ℝ) (ht : t ∈ I (cfg.T k s) (cfg.j k s i)) :
    |t - cfg.leftTime k s i| ≤ cfg.timeLength k s ∧
    |cfg.b k l 0 + t * cfg.b k l 3 - cfg.horizontalOrigin k s i| ≤
      2 * cfg.K k * cfg.timeLength k s := by
  have ht' := ht
  rw [cfg.true_block_eq] at ht'
  have htime : |t - cfg.leftTime k s i| ≤ cfg.timeLength k s := by
    rw [abs_of_nonneg (sub_nonneg.mpr ht'.1)]
    linarith only [ht'.2]
  refine ⟨htime, ?_⟩
  have hg := (a.geometry i l hl t ht).1
  have hc := a.coefficient_bound i 1
  have hm : |(t - cfg.leftTime k s i) * cfg.c k s i 1| ≤ cfg.K k * cfg.timeLength k s := by
    rw [abs_mul]
    exact (mul_le_mul htime hc (abs_nonneg _)
      (by unfold timeLength; positivity)).trans_eq (mul_comm _ _)
  calc
    _ = |((cfg.x k l t) 1 - cfg.c k s i 0 - t * cfg.c k s i 1) +
        (t - cfg.leftTime k s i) * cfg.c k s i 1| := by
      dsimp [x, horizontalOrigin]
      congr 1
      ring
    _ ≤ _ := abs_add_le _ _
    _ ≤ _ := by linarith only [hg, hm]

/-- Freezing the horizontal row on a deeper true label costs its actual
physical diameter, in addition to the fitted derivative and contact errors. -/
theorem AssignmentLevel.frozenRow_error (h : cfg.Valid) {k : ℕ} {s : ℝ}
    (a : cfg.AssignmentLevel k s) (i : Fin (cfg.n k s)) (L : Fin 4 → ℝ)
    (hL : ∀ e : Fin 3, |L e.succ| ≤ 8 * cfg.K k ^ 4)
    (hfit : ∀ l ∈ cfg.B k s i, ∀ t ∈ I (cfg.T k s) (cfg.j k s i),
      |affineResidualIntercept L (cfg.b k l) + t * affineResidualSlope L (cfg.b k l)| ≤
        cfg.K k * cfg.N k ^ (-s))
    (l : α) (hl : l ∈ cfg.B k s i) (t : ℝ) (ht : t ∈ I (cfg.T k s) (cfg.j k s i))
    (hv : |cfg.b k l 3| ≤ cfg.K k)
    (hdef : |cfg.b k l 4 + cfg.b k l 0| ≤ cfg.N k ^ (-cfg.e₀)) :
    |cfg.frozenRow k s i L 0 + cfg.b k l 3 * cfg.frozenRow k s i L 1 - cfg.b k l 5| ≤
      2 * cfg.K k * cfg.N k ^ (-s) / cfg.timeLength k s +
        24 * cfg.K k ^ 5 * cfg.timeLength k s + 8 * cfg.K k ^ 4 * cfg.N k ^ (-cfg.e₀) := by
  have hH : 0 < cfg.timeLength k s := by unfold timeLength; positivity
  have hK : 0 ≤ cfg.K k := by linarith [h.subpower.1 k]
  have hend : cfg.leftTime k s i + cfg.timeLength k s ∈ I (cfg.T k s) (cfg.j k s i) := by
    rw [cfg.true_block_eq]
    exact ⟨by linarith, le_rfl⟩
  have hsl := Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.affine_slope_bound
    (show cfg.leftTime k s i < cfg.leftTime k s i + cfg.timeLength k s by linarith)
    (show |affineResidualSlope L (cfg.b k l) * cfg.leftTime k s i +
      affineResidualIntercept L (cfg.b k l)| ≤ cfg.K k * cfg.N k ^ (-s) by
      simpa only [mul_comm, add_comm] using hfit l hl _ (cfg.leftTime_mem k s i))
    (show |affineResidualSlope L (cfg.b k l) * (cfg.leftTime k s i + cfg.timeLength k s) +
      affineResidualIntercept L (cfg.b k l)| ≤ cfg.K k * cfg.N k ^ (-s) by
      simpa only [mul_comm, add_comm] using hfit l hl _ hend)
  simp only [add_sub_cancel_left] at hsl
  rw [show 2 * (cfg.K k * cfg.N k ^ (-s)) / cfg.timeLength k s =
    2 * cfg.K k * cfg.N k ^ (-s) / cfg.timeLength k s by ring] at hsl
  have hd := a.horizontal_displacement i l (a.fitted_subset i hl) t ht
  have hd' : |(cfg.b k l 0 + t * cfg.b k l 3 - cfg.horizontalOrigin k s i) +
      cfg.b k l 3 * (cfg.leftTime k s i - t)| ≤ 3 * cfg.K k * cfg.timeLength k s := by
    have hm : |cfg.b k l 3 * (cfg.leftTime k s i - t)| ≤ cfg.K k * cfg.timeLength k s := by
      rw [abs_mul, abs_sub_comm]
      exact mul_le_mul hv hd.1 (abs_nonneg _) hK
    exact (abs_add_le _ _).trans (by linarith only [hd.2, hm])
  have h3 : |L 3| ≤ 8 * cfg.K k ^ 4 := hL 2
  have hcontact : |L 3 * (cfg.b k l 4 + cfg.b k l 0)| ≤
      8 * cfg.K k ^ 4 * cfg.N k ^ (-cfg.e₀) := by
    rw [abs_mul]
    exact mul_le_mul h3 hdef (abs_nonneg _) (by positivity)
  have hvar : |L 3 * ((cfg.b k l 0 + t * cfg.b k l 3 - cfg.horizontalOrigin k s i) +
      cfg.b k l 3 * (cfg.leftTime k s i - t))| ≤ 24 * cfg.K k ^ 5 * cfg.timeLength k s := by
    rw [abs_mul]
    exact (mul_le_mul h3 hd' (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have heq : cfg.frozenRow k s i L 0 + cfg.b k l 3 * cfg.frozenRow k s i L 1 - cfg.b k l 5 =
      -affineResidualSlope L (cfg.b k l) - L 3 * (cfg.b k l 4 + cfg.b k l 0) +
        L 3 * ((cfg.b k l 0 + t * cfg.b k l 3 - cfg.horizontalOrigin k s i) +
          cfg.b k l 3 * (cfg.leftTime k s i - t)) := by
    dsimp [frozenRow, affineResidualSlope]
    ring
  rw [heq]
  calc
    _ ≤ (|affineResidualSlope L (cfg.b k l)| + |L 3 * (cfg.b k l 4 + cfg.b k l 0)|) +
      |L 3 * ((cfg.b k l 0 + t * cfg.b k l 3 - cfg.horizontalOrigin k s i) +
          cfg.b k l 3 * (cfg.leftTime k s i - t))| := by
      exact (abs_add_le _ _).trans (add_le_add
        (by simpa only [abs_neg] using
          (abs_sub (-affineResidualSlope L (cfg.b k l)) (L 3 * (cfg.b k l 4 + cfg.b k l 0)))) le_rfl)
    _ ≤ _ := by linarith only [hsl, hcontact, hvar]

end Data
end
end Submission.Obl.k4_critical_conditional_row_preparation
