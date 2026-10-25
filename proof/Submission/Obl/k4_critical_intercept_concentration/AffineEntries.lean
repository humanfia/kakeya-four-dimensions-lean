/- Adapted from this LOT tree, obligation o201, session x0697, commit 74bd9a876bac,
   Submission/Obl/k4_horizontal_critical_rate_candidates/AffineEntries.lean.
   Original source attributions below are preserved. -/
import Submission.Obl.k4_critical_intercept_concentration.TrueBoxes
import Submission.Obl.k4_critical_intercept_concentration.Inherited.AffinePrimitive

namespace Submission.Obl.k4_critical_intercept_concentration

open Inherited MeasureTheory Set MvPolynomial

noncomputable section

/-- One actual fitted point bounds every slope of its true affine entry.
The horizontal derivative bounds, rather than any absolute intercept bound,
are the information used here. -/
theorem affine_entry_slopes_le (L : Fin 4 → ℝ) (K a q t Z : ℝ)
    (hK : 1 ≤ K) (haq : a / q ≤ K) (haq2 : a / q ^ 2 ≤ K ^ 2)
    (ht : |t| ≤ 1) (hZ : |Z| ≤ 3 * K)
    (hvertical : |L 3| ≤ K * (1 + a / q ^ 2))
    (hrow : |L 1 - Z * L 3| + |L 2 + t * L 3| ≤ K * (1 + a / q)) :
    ∀ i : Fin 3, |L i.succ| ≤ 8 * K ^ 4 := by
  have hK0 : 0 ≤ K := by linarith
  have h12 : K ≤ K ^ 2 := by nlinarith
  have h13 : K ≤ K ^ 3 := by simpa using pow_le_pow_right₀ hK (show 1 ≤ 3 by norm_num)
  have h24 : K ^ 2 ≤ K ^ 4 := pow_le_pow_right₀ hK (by norm_num)
  have h34 : K ^ 3 ≤ K ^ 4 := pow_le_pow_right₀ hK (by norm_num)
  have hv : |L 3| ≤ 2 * K ^ 3 := by
    refine hvertical.trans ?_
    have hh := mul_le_mul_of_nonneg_left (add_le_add_left haq2 1) hK0
    nlinarith only [hh, h13]
  have hr : |L 1 - Z * L 3| + |L 2 + t * L 3| ≤ 2 * K ^ 2 := by
    refine hrow.trans ?_
    have hh := mul_le_mul_of_nonneg_left (add_le_add_left haq 1) hK0
    nlinarith only [hh, h12]
  have hfirst : |L 1| ≤ 8 * K ^ 4 := by
    calc
      _ ≤ |L 1 - Z * L 3| + |Z * L 3| := by
        simpa only [sub_zero] using abs_sub_le (L 1) (Z * L 3) 0
      _ ≤ 2 * K ^ 2 + (3 * K) * (2 * K ^ 3) := by
        apply add_le_add (by linarith only [hr, abs_nonneg (L 2 + t * L 3)])
        rw [abs_mul]
        exact mul_le_mul hZ hv (abs_nonneg _) (by positivity)
      _ ≤ _ := by nlinarith only [h24]
  have hsecond : |L 2| ≤ 8 * K ^ 4 := by
    calc
      _ = |(L 2 + t * L 3) - t * L 3| := by congr 1; ring
      _ ≤ |L 2 + t * L 3| + |t * L 3| := abs_sub _ _
      _ ≤ 2 * K ^ 2 + 2 * K ^ 3 := by
        apply add_le_add (by linarith only [hr, abs_nonneg (L 1 - Z * L 3)])
        rw [abs_mul]
        exact (mul_le_mul ht hv (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
      _ ≤ _ := by nlinarith only [h24, h34]
  intro i
  fin_cases i
  · exact hfirst
  · exact hsecond
  · exact hv.trans (by nlinarith only [h34, pow_nonneg hK0 4])

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- Every active true affine entry has subpower bounded slopes and fits all
of its original assigned trajectories throughout the whole true block. -/
theorem AssignmentLevel.active_affine_entry (h : cfg.Valid) {k : ℕ} {s : ℝ}
    (a : cfg.AssignmentLevel k s) (hs : 0 ≤ s) (i : Fin (cfg.n k s))
    (l₀ : α) (hl₀ : l₀ ∈ cfg.B k s i) (t₀ : ℝ)
    (ht₀ : t₀ ∈ I (cfg.T k s) (cfg.j k s i)) :
    ∃ L : Fin 4 → ℝ,
      cfg.F k s i = X (3 : Fin 4) -
        (C (L 0) + C (L 1) * X (0 : Fin 4) + C (L 2) * X (1 : Fin 4) + C (L 3) * X (2 : Fin 4)) ∧
      (∀ e : Fin 3, |L e.succ| ≤ 8 * cfg.K k ^ 4) ∧
      ∀ l ∈ cfg.B k s i, ∀ t ∈ I (cfg.T k s) (cfg.j k s i),
        |affineResidualIntercept L (cfg.b k l) + t * affineResidualSlope L (cfg.b k l)| ≤
          cfg.K k * cfg.N k ^ (-s) := by
  obtain ⟨L, hF, hv, hrow⟩ := a.affine_entry i
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hN1 : 1 ≤ cfg.N k := by linarith [h.scale k]
  have hK : 0 < cfg.K k := by linarith [h.subpower.1 k]
  have hratios := critical_hidden_time_ratios hN1 hN hK h.rate_pos.le hs h.critical_rate
    a.time_lower a.time_upper
  have hbase := a.native_base_bounds h i l₀ (a.fitted_subset i hl₀) ht₀
  have htime := Submission.Obl.k4_scalar_initial_true_horizon.I_subset_unit
    (cfg.T k s) (cfg.j k s i) ht₀
  refine ⟨L, hF, ?_, ?_⟩
  · exact affine_entry_slopes_le L (cfg.K k) (cfg.N k ^ (-s)) (cfg.timeLength k s)
      t₀ ((cfg.x k l₀ t₀) 1) (h.subpower.1 k) hratios.1 hratios.2
      (by simpa only [abs_of_nonneg htime.1] using htime.2) hbase.1 hv (hrow l₀ hl₀ t₀ ht₀)
  · intro l hl t ht
    have hf := (a.fitted i l hl t ht).1
    have heq : eval (cfg.x k l t) (cfg.F k s i) =
        affineResidualIntercept L (cfg.b k l) + t * affineResidualSlope L (cfg.b k l) := by
      rw [hF]
      simp [x, affineResidualIntercept, affineResidualSlope]
      ring
    rwa [heq] at hf

end Data

end

end Submission.Obl.k4_critical_intercept_concentration
