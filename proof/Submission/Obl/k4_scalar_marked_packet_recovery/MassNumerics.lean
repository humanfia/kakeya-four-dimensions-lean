import Submission.Obl.k4_scalar_marked_packet_recovery.Definitions

namespace Submission.Obl.k4_scalar_marked_packet_recovery

open scoped ENNReal

/-- The noisy packet count makes the desired pruning budget small. -/
theorem scaled_packet_budget {n : ℕ} {L E q K C : ℝ}
    (hL : 0 < L) (hE : 0 < E) (hK : 0 < K) (hq : L⁻¹ ≤ q)
    (hgap : 4 * K * L ^ 3 ≤ E)
    (hbudget : (n : ℝ≥0∞) * ENNReal.ofReal (q * C / L) ≤ 1) :
    (n : ℝ≥0∞) * ENNReal.ofReal (C / E) ≤ ENNReal.ofReal (L⁻¹ / (4 * K)) := by
  have hq0 : 0 < q := lt_of_lt_of_le (by positivity) hq
  have hqL : 1 ≤ q * L := by
    exact (div_le_iff₀ hL).mp (by simpa only [one_div] using hq)
  have hstep : 4 * K * L ^ 2 ≤ q * E := by
    calc
      _ = (4 * K * L ^ 2) * 1 := by ring
      _ ≤ (4 * K * L ^ 2) * (q * L) := by gcongr
      _ = q * (4 * K * L ^ 3) := by ring
      _ ≤ q * E := by gcongr
  have hr : L⁻¹ / (4 * K) = 1 / (4 * K * L) := by field_simp
  have hfac : L / (q * E) ≤ L⁻¹ / (4 * K) := by
    rw [hr, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hstep]
  have heq : C / E = (L / (q * E)) * (q * C / L) := by field_simp
  calc
    _ = ENNReal.ofReal (L / (q * E)) *
        ((n : ℝ≥0∞) * ENNReal.ofReal (q * C / L)) := by
      rw [heq, ENNReal.ofReal_mul (by positivity)]
      ring
    _ ≤ ENNReal.ofReal (L / (q * E)) * 1 := by gcongr
    _ = ENNReal.ofReal (L / (q * E)) := mul_one _
    _ ≤ _ := ENNReal.ofReal_le_ofReal hfac

/-- The same gap leaves the required lower bound for total retained mass. -/
theorem retained_mass_bound {L E K : ℝ} (hL : 1 ≤ L) (hK : 0 < K)
    (hgap : 4 * K * L ^ 3 ≤ E) : E⁻¹ ≤ L⁻¹ / (4 * K) := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hLL : L ≤ L ^ 3 := by nlinarith [sq_nonneg (L - 1)]
  have hE : 4 * K * L ≤ E := (by gcongr : 4 * K * L ≤ 4 * K * L ^ 3).trans hgap
  calc
    E⁻¹ ≤ (4 * K * L)⁻¹ := inv_anti₀ (by positivity) hE
    _ = L⁻¹ / (4 * K) := by field_simp

end Submission.Obl.k4_scalar_marked_packet_recovery
