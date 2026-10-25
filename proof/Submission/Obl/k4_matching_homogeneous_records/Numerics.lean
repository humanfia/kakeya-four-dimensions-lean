import Mathlib

namespace Submission.Obl.k4_matching_homogeneous_records

open Filter
open scoped Topology

lemma log_loss_threshold (q : ℕ) (A δ : ℝ) (hA : 0 ≤ A) (hδ : 0 < δ) :
    ∃ R : ℝ, 2 ≤ R ∧ ∀ N : ℝ, R ≤ N →
      (((A * Real.logb 2 N + 1) * 2) ^ q ≤ N ^ δ) := by
  let C : ℝ := (2 * (A + 1) / Real.log 2) ^ q
  have ho := (isLittleO_log_rpow_rpow_atTop (q : ℝ) hδ).const_mul_left C
  have hev : ∀ᶠ N : ℝ in atTop, ((A * Real.logb 2 N + 1) * 2) ^ q ≤ N ^ δ := by
    filter_upwards [ho.bound (show (0 : ℝ) < 1 by norm_num), eventually_ge_atTop (2 : ℝ)] with N hb hN
    have hNp : 0 < N := by linarith
    have hlog : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
    have hC : 0 ≤ C := by dsimp [C]; positivity
    have hnn : 0 ≤ C * (Real.log N) ^ q := by positivity
    have hbd : C * (Real.log N) ^ q ≤ N ^ δ := by
      simpa only [Real.rpow_natCast, Real.norm_eq_abs, abs_of_nonneg hnn,
        abs_of_pos (Real.rpow_pos_of_pos hNp δ), one_mul] using hb
    have hlogb : 1 ≤ Real.logb 2 N := by
      have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by norm_num : (0 : ℝ) < 2) hN
      norm_num at h ⊢
      exact h
    calc
      _ ≤ (((A + 1) * Real.logb 2 N) * 2) ^ q := by
        apply pow_le_pow_left₀ (by positivity) _
        nlinarith
      _ = C * (Real.log N) ^ q := by
        dsimp [C, Real.logb]
        rw [← mul_pow]
        congr 1
        field_simp
      _ ≤ _ := hbd
  obtain ⟨R, hR⟩ := eventually_atTop.1 hev
  exact ⟨max 2 R, le_max_left _ _, fun N hN => hR N ((le_max_right _ _).trans hN)⟩

end Submission.Obl.k4_matching_homogeneous_records
