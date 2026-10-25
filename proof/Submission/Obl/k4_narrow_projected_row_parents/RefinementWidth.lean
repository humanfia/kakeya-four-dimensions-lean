import Submission.Obl.k4_narrow_projected_row_parents.Model

namespace Submission.Obl.k4_narrow_projected_row_parents.MajorRefinement

open Filter

noncomputable section

/-- Integer subdivision chosen to reach a prescribed finer width. -/
def factor (χ ξ : ℝ) : ℕ := ⌈χ / ξ⌉₊

theorem width_bounds {χ ξ : ℝ} (hχ : 0 < χ) (hξ : 0 < ξ) (hξχ : ξ ≤ χ) :
    0 < factor χ ξ ∧ ξ / 2 ≤ χ / factor χ ξ ∧ χ / factor χ ξ ≤ ξ := by
  have hr : 0 < χ / ξ := div_pos hχ hξ
  have hJ : 0 < factor χ ξ := Nat.ceil_pos.mpr hr
  have hJr : (0 : ℝ) < factor χ ξ := by exact_mod_cast hJ
  have hratio : 1 ≤ χ / ξ := (le_div_iff₀ hξ).mpr (by simpa only [one_mul] using hξχ)
  have hlo : χ / ξ ≤ (factor χ ξ : ℝ) := Nat.le_ceil _
  have hup : (factor χ ξ : ℝ) < χ / ξ + 1 := Nat.ceil_lt_add_one hr.le
  refine ⟨hJ, ?_, ?_⟩
  · rw [le_div_iff₀ hJr]
    have hJbound : (factor χ ξ : ℝ) ≤ (2 * χ) / ξ := by
      calc (factor χ ξ : ℝ) ≤ χ / ξ + 1 := hup.le
           _ ≤ 2 * (χ / ξ) := by linarith
           _ = (2 * χ) / ξ := by ring
    have h := (le_div_iff₀ hξ).mp hJbound
    nlinarith
  · rw [div_le_iff₀ hJr]
    have h := (div_le_iff₀ hξ).mp hlo
    nlinarith

theorem power_width_bounds (N : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k)
    {m chiExp : ℝ} (hFine : m ≤ chiExp) (k : ℕ) :
    0 < factor (N k ^ (-m)) (N k ^ (-chiExp)) ∧
      N k ^ (-chiExp) / 2 ≤ N k ^ (-m) / factor (N k ^ (-m)) (N k ^ (-chiExp)) ∧
      N k ^ (-m) / factor (N k ^ (-m)) (N k ^ (-chiExp)) ≤ N k ^ (-chiExp) := by
  have hNp : 0 < N k := zero_lt_one.trans_le (hN k)
  exact width_bounds (Real.rpow_pos_of_pos hNp _) (Real.rpow_pos_of_pos hNp _)
    (Real.rpow_le_rpow_of_exponent_le (hN k) (by linarith))

/-- A constant-factor lower width gives every slightly weaker lower exponent. -/
theorem eventually_width_lower (N χ : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k)
    (hNt : Tendsto N atTop atTop) {fine lower : ℝ} (hgap : fine < lower)
    (hχ : ∀ k, N k ^ (-fine) / 2 ≤ χ k) :
    ∀ᶠ k in atTop, N k ^ (-lower) ≤ χ k := by
  have h2 : ∀ᶠ k in atTop, 2 ≤ N k ^ (lower - fine) :=
    ((tendsto_rpow_atTop (by linarith : 0 < lower - fine)).comp hNt).eventually_ge_atTop 2
  filter_upwards [h2] with k hk
  have hNp : 0 < N k := zero_lt_one.trans_le (hN k)
  have hmul : N k ^ (-lower) * 2 ≤ N k ^ (-fine) := by
    calc N k ^ (-lower) * 2 ≤ N k ^ (-lower) * N k ^ (lower - fine) :=
           mul_le_mul_of_nonneg_left hk (Real.rpow_nonneg hNp.le _)
         _ = N k ^ (-fine) := by rw [← Real.rpow_add hNp]; congr 1; ring
  exact (by linarith : N k ^ (-lower) ≤ N k ^ (-fine) / 2).trans (hχ k)

/-- Subdivide to a natural width divided by a loss. The resulting width is
small enough for stability and remains within twice that loss of the natural scale. -/
theorem natural_target_bounds {χ natural R : ℝ} (hχ : 0 < χ) (hnatural : 0 < natural)
    (hnχ : natural ≤ χ) (hR : 1 ≤ R) :
    0 < factor χ (natural / R) ∧
      natural ≤ (2 * R) * (χ / factor χ (natural / R)) ∧
      χ / factor χ (natural / R) ≤ natural / R := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hξ : 0 < natural / R := div_pos hnatural hRp
  have hξχ : natural / R ≤ χ := (div_le_self hnatural.le hR).trans hnχ
  obtain ⟨hJ, hlo, hup⟩ := width_bounds hχ hξ hξχ
  refine ⟨hJ, ?_, hup⟩
  have h := mul_le_mul_of_nonneg_right hlo (show 0 ≤ 2 * R by positivity)
  have hid : (natural / R / 2) * (2 * R) = natural := by field_simp
  rw [hid] at h
  simpa only [mul_comm] using h

end

end Submission.Obl.k4_narrow_projected_row_parents.MajorRefinement
